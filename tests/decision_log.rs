//! The Decision Log in docs/DESIGN.md: numbered D1, D2, ... in order with no
//! gaps, so the next number is the row count plus one and nobody has to
//! remember it. Every dependency in Cargo.toml has a decision.

const DESIGN: &str = include_str!("../docs/DESIGN.md");
const CARGO: &str = include_str!("../Cargo.toml");

/// The rows of the Decision Log table: `(number, whole row)`.
fn decisions() -> Vec<(usize, &'static str)> {
    DESIGN
        .lines()
        .filter_map(|row| {
            let n = row.strip_prefix("| D")?.split(' ').next()?.parse().ok()?;
            Some((n, row))
        })
        .collect()
}

#[test]
fn decisions_are_numbered_in_order_without_gaps() {
    let numbers: Vec<usize> = decisions().iter().map(|(n, _)| *n).collect();
    let want: Vec<usize> = (1..=numbers.len()).collect();
    assert_eq!(
        numbers,
        want,
        "The Decision Log in docs/DESIGN.md must run D1, D2, ... in order. The next decision is D{}; append it at the end of the table.",
        numbers.len() + 1
    );
}

#[test]
fn every_dependency_has_a_decision() {
    let rows: Vec<&str> = decisions().iter().map(|(_, row)| *row).collect();
    let missing = undecided_dependencies(CARGO, &rows);
    assert!(
        missing.is_empty(),
        "{:?} in Cargo.toml have no decision. Warrant keeps zero dependencies unless there is a reason: \
         append a row that names each in backticks to the Decision Log in docs/DESIGN.md, or remove it.",
        missing
    );
}

#[test]
fn a_dependency_without_a_row_that_names_it_is_reported() {
    let cargo = "[package]\nname = \"warrant\"\n[dependencies]\nrayon = \"1\"\n[dev-dependencies]\nsyn = { version = \"2\" }\n";
    assert_eq!(undecided_dependencies(cargo, &["| D30 | fork-join uses `rayon` | ... |"]), ["syn"]);
}

/// Names under any `[...dependencies]` table that no row names in backticks.
fn undecided_dependencies(cargo: &str, rows: &[&str]) -> Vec<String> {
    let mut section = "";
    let mut missing = Vec::new();
    for line in cargo.lines().map(str::trim) {
        if line.starts_with('[') {
            section = line;
            continue;
        }
        let Some((name, _)) = line.split_once('=') else { continue };
        let name = name.trim();
        if section.ends_with("dependencies]") && !name.starts_with('#') && !rows.iter().any(|row| row.contains(&format!("`{}`", name))) {
            missing.push(name.to_string());
        }
    }
    missing
}
