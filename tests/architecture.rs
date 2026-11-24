//! The direction of dependencies between the modules of `src/`. A module may
//! use only modules in lower layers, so the graph has no cycles and the
//! runtime does not pull in the prover. Test code (`mod tests` at the end of
//! a file) is not checked: it may reach anything to set up a case.
//!
//! The check reads `crate::module` paths as text, so the crate keeps zero
//! dependencies. Name other modules by that path, not by `super::`.
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

/// Lowest layer first. A module may use the modules of the layers before its
/// own, never those of its own layer or later ones. `lib.rs` and `main.rs`
/// sit above all of them.
const LAYERS: &[&[&str]] = &[
    &["sexp", "builtin"],
    &["diag", "wisp", "profile"],
    &["ast"],
    &["types", "effects", "contracts"],
    &["smt"],
    &["solver"],
    &["vc", "cache"],
    &["verify"],
    &["specdiff", "ir"],
    &["value"],
    &["rt"],
    // The M1 interpreter, kept as the oracle of tests/runtime_diff.rs until M2-7.
    &["eval"],
];

#[test]
fn modules_use_only_lower_layers() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let found = check(&src, LAYERS);
    assert!(
        found.misplaced_tests.is_empty(),
        "Test code must be one `#[cfg(test)] mod tests` at the end of the file, which tests/architecture.rs skips: {:?}.\n\
         Move the test-only items into that module.",
        found.misplaced_tests
    );
    assert!(
        found.unknown.is_empty(),
        "These modules are not in LAYERS in tests/architecture.rs: {:?}.\n\
         Add each to LAYERS at the lowest layer that holds everything it uses, and to the module table in CLAUDE.md.",
        found.unknown
    );
    let new: Vec<&String> = found.violations.values().flatten().collect();
    assert!(
        new.is_empty(),
        "{} uses point up or sideways in the layers:\n  {}\n\n\
         A module may use only modules in lower layers (LAYERS in tests/architecture.rs).\n\
         Fix the design, not the check: move what both modules need into a lower module, or let the caller pass it in \
         (a value, a function, or a trait the lower module defines). Do not re-export the item from another module to \
         hide the use.",
        new.len(),
        new.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n  ")
    );
}

#[test]
fn the_check_reports_a_use_of_a_higher_layer_and_ignores_tests() {
    let src = Path::new(env!("CARGO_TARGET_TMPDIR")).join("architecture-src");
    let _ = std::fs::remove_dir_all(&src);
    std::fs::create_dir_all(&src).unwrap();
    let write = |name: &str, text: &str| std::fs::write(src.join(name), text).unwrap();
    write("lib.rs", "pub mod high;\npub mod low;\n");
    write("main.rs", "use warrant::high::Thing;\n");
    write("high.rs", "pub struct Thing;\nfn f() -> crate::low::Low { crate::low::Low }\n");
    write(
        "low.rs",
        "use crate::{sexp::Sexp, wisp};\npub struct Low;\n// crate::high in a comment\nfn up() -> crate::high::Thing { todo!() }\n\
         #[cfg(test)]\nmod tests {\n    use crate::high::Thing;\n}\n",
    );
    write("stray.rs", "#[cfg(test)]\nfn helper() {}\nfn g() {}\n");

    let found = check(&src, &[&["low"], &["high"]]);

    assert_eq!(found.unknown, BTreeSet::from(["sexp".to_string(), "stray".to_string(), "wisp".to_string()]));
    assert_eq!(found.misplaced_tests, ["stray.rs"]);
    let lines: Vec<&String> = found.violations.values().flatten().collect();
    assert_eq!(lines, ["src/low.rs:4: `low` uses `crate::high`, which is in a higher layer"]);
}

struct Found {
    /// Modules that are used or defined but missing from the layers.
    unknown: BTreeSet<String>,
    /// Files with a `#[cfg(test)]` that is not the final `mod tests`.
    misplaced_tests: Vec<String>,
    /// `(from, to)` -> each use as `src/file.rs:line: ...`.
    violations: BTreeMap<(String, String), Vec<String>>,
}

fn check(src: &Path, layers: &[&[&str]]) -> Found {
    let mut rank = BTreeMap::new();
    for (i, layer) in layers.iter().enumerate() {
        for m in *layer {
            assert!(rank.insert(m.to_string(), i).is_none(), "{} is in LAYERS twice", m);
        }
    }
    let mut files: Vec<_> = std::fs::read_dir(src).unwrap().map(|e| e.unwrap().path()).collect();
    files.sort();
    let mut found = Found { unknown: BTreeSet::new(), misplaced_tests: Vec::new(), violations: BTreeMap::new() };
    for path in files {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let Some(from) = name.strip_suffix(".rs") else { continue };
        if from == "lib" || from == "main" {
            continue;
        }
        if !rank.contains_key(from) {
            found.unknown.insert(from.to_string());
        }
        let text = std::fs::read_to_string(&path).unwrap();
        let production = match text.find("#[cfg(test)]") {
            Some(cut) if text[cut..].starts_with("#[cfg(test)]\nmod tests {") => &text[..cut],
            Some(cut) => {
                found.misplaced_tests.push(name.clone());
                &text[..cut]
            }
            None => &text[..],
        };
        for (i, line) in production.lines().enumerate() {
            let code = line.split("//").next().unwrap_or("");
            for to in used_modules(code) {
                if to == from {
                    continue;
                }
                let (Some(f), Some(t)) = (rank.get(from), rank.get(&to)) else {
                    if !rank.contains_key(&to) {
                        found.unknown.insert(to);
                    }
                    continue;
                };
                if t >= f {
                    let at = format!("src/{}:{}: `{}` uses `crate::{}`, which is in a higher layer", name, i + 1, from, to);
                    found.violations.entry((from.to_string(), to)).or_default().push(at);
                }
            }
        }
    }
    found
}

/// `crate::ast::lower(crate::sexp::flat(x))` -> `["ast", "sexp"]`, and
/// `use crate::{ast::Module, diag}` -> `["ast", "diag"]`.
fn used_modules(code: &str) -> Vec<String> {
    let ident = |s: &str| s.trim_start().chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect::<String>();
    let mut out = Vec::new();
    for (i, m) in code.match_indices("crate::") {
        if code[..i].ends_with(|c: char| c.is_alphanumeric() || c == '_') {
            continue;
        }
        let rest = &code[i + m.len()..];
        match rest.strip_prefix('{') {
            Some(group) => out.extend(group.split('}').next().unwrap_or("").split(',').map(ident)),
            None => out.push(ident(rest)),
        }
    }
    out.retain(|m| !m.is_empty());
    out
}
