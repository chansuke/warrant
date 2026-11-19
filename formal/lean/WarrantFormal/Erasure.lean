/-!
# Erasing proved preconditions

`contracts::levels` stops checking a function's `requires` at run time when

1. every syntactic call site of the function has a proved VC,
2. the function is never used as a value, and
3. it is not `main`.

This file proves that, under those three conditions, erasing the checks
never changes what a program does: the same result, the same contract
failure, or the same lack of an answer. The language is a small model of
Warrant's call structure: one-argument functions, direct calls, functions
as values, and calls through a value. A VC is modelled by what it means
when the solver proves it: whenever the caller's precondition holds and
the argument evaluates to `v`, the callee's precondition holds for `v`.

Evaluation takes fuel, so every run is a total function and non-termination
is "no answer" (`none`), the same in both programs.
-/

namespace Warrant

abbrev Fn := Nat

inductive Val where
  | int (n : Int)
  | fn (f : Fn)
  deriving DecidableEq

inductive Expr where
  | lit (n : Int)
  /-- The function's one parameter. -/
  | arg
  | add (a b : Expr)
  /-- `if c ≠ 0 then a else b` -/
  | ite (c a b : Expr)
  /-- A syntactic call site: the place a VC is generated. -/
  | call (f : Fn) (a : Expr)
  /-- `f` used as a value. -/
  | ref (f : Fn)
  /-- A call through a function value: no VC can see its target. -/
  | callv (g a : Expr)

inductive Res where
  | ok (v : Val)
  /-- A run-time contract failure. -/
  | fail
  deriving DecidableEq

structure Prog where
  body : Fn → Expr
  pre : Fn → Val → Bool

variable (P : Prog)

/-- Evaluates `e` with parameter `x`; `call` says what calling a function does. -/
def evalE (call : Fn → Val → Option Res) (x : Val) : Expr → Option Res
  | .lit n => some (.ok (.int n))
  | .arg => some (.ok x)
  | .add a b =>
    match evalE call x a, evalE call x b with
    | some (.ok (.int m)), some (.ok (.int n)) => some (.ok (.int (m + n)))
    | some .fail, _ => some .fail
    | some (.ok (.int _)), some .fail => some .fail
    | _, _ => none
  | .ite c a b =>
    match evalE call x c with
    | some (.ok (.int n)) => if n ≠ 0 then evalE call x a else evalE call x b
    | some .fail => some .fail
    | _ => none
  | .call f a =>
    match evalE call x a with
    | some (.ok v) => call f v
    | r => r
  | .ref f => some (.ok (.fn f))
  | .callv g a =>
    match evalE call x g with
    | some (.ok (.fn f)) =>
      match evalE call x a with
      | some (.ok v) => call f v
      | r => r
    | some .fail => some .fail
    | _ => none

/-- Calls `f` on `x`, checking its precondition when `checked f`. -/
def run (checked : Fn → Bool) : Nat → Fn → Val → Option Res
  | 0, _, _ => none
  | k + 1, f, x =>
    if checked f && !P.pre f x then some .fail
    else evalE (run checked k) x (P.body f)

/-- Does `e` use `f` as a value? -/
def refs (f : Fn) : Expr → Bool
  | .lit _ | .arg => false
  | .add a b => refs f a || refs f b
  | .ite c a b => refs f c || refs f a || refs f b
  | .call _ a => refs f a
  | .ref g => g == f
  | .callv g a => refs f g || refs f a

/-- Every call site in `e`, inside the body of `g`, to an erased function
has a valid VC: the caller's precondition implies the callee's. -/
def VCs (erased : Fn → Bool) (g : Fn) : Expr → Prop
  | .lit _ | .arg | .ref _ => True
  | .add a b => VCs erased g a ∧ VCs erased g b
  | .ite c a b => VCs erased g c ∧ VCs erased g a ∧ VCs erased g b
  | .call f a =>
    VCs erased g a ∧
    (erased f = true → ∀ k x v, P.pre g x = true →
      evalE (run P (fun h => !erased h) k) x a = some (.ok v) → P.pre f v = true)
  | .callv h a => VCs erased g h ∧ VCs erased g a

/-- A value is not an erased function. Only those could be called past a VC. -/
def ValOk (erased : Fn → Bool) : Val → Prop
  | .fn f => erased f = false
  | .int _ => True

def ResOk (erased : Fn → Bool) : Option Res → Prop
  | some (.ok v) => ValOk erased v
  | _ => True

section
variable (erased : Fn → Bool)

/-- The conditions `contracts::levels` checks, over the whole program. -/
structure Erasable (main : Fn) : Prop where
  not_main : erased main = false
  not_a_value : ∀ f g, erased f = true → refs f (P.body g) = false
  sites_proved : ∀ g, VCs P erased g (P.body g)

local notation "full" => run P (fun _ => true)
local notation "erasedRun" => run P (fun h => !erased h)

theorem evalE_agree (k : Nat)
    (ih : ∀ f x, ValOk erased x → (erased f = true → P.pre f x = true) →
      full k f x = erasedRun k f x ∧ ResOk erased (erasedRun k f x))
    (g : Fn) (x : Val) (hpre : P.pre g x = true) (hx : ValOk erased x) :
    ∀ e, VCs P erased g e → (∀ f, erased f = true → refs f e = false) →
      evalE (full k) x e = evalE (erasedRun k) x e ∧
      ResOk erased (evalE (erasedRun k) x e) := by
  intro e
  induction e with
  | lit n => intro _ _; exact ⟨rfl, trivial⟩
  | arg => intro _ _; exact ⟨rfl, hx⟩
  | ref f =>
    intro _ hr
    refine ⟨rfl, ?_⟩
    show erased f = false
    cases h : erased f
    · rfl
    · have := hr f h; simp [refs] at this
  | add a b iha ihb =>
    intro hv hr
    have ⟨ea, oka⟩ := iha hv.1 (fun f h => by have := hr f h; simp [refs] at this; exact this.1)
    have ⟨eb, okb⟩ := ihb hv.2 (fun f h => by have := hr f h; simp [refs] at this; exact this.2)
    refine ⟨by simp only [evalE, ea, eb], ?_⟩
    simp only [evalE]
    split <;> simp_all [ResOk, ValOk]
  | ite c a b ihc iha ihb =>
    intro hv hr
    have hr' := fun f h => by have := hr f h; simp [refs] at this; exact this
    have ⟨ec, okc⟩ := ihc hv.1 (fun f h => (hr' f h).1.1)
    have ⟨ea, oka⟩ := iha hv.2.1 (fun f h => (hr' f h).1.2)
    have ⟨eb, okb⟩ := ihb hv.2.2 (fun f h => (hr' f h).2)
    simp only [evalE]
    rw [ec, ea, eb]
    refine ⟨rfl, ?_⟩
    split
    · split <;> assumption
    · trivial
    · trivial
  | call f a iha =>
    intro hv hr
    have ⟨ea, oka⟩ := iha hv.1 (fun f h => by have := hr f h; simp [refs] at this; exact this)
    simp only [evalE, ea]
    cases hres : evalE (erasedRun k) x a with
    | none => exact ⟨rfl, trivial⟩
    | some r =>
      cases r with
      | fail => exact ⟨rfl, trivial⟩
      | ok v =>
        rw [hres] at oka
        exact ih f v oka (fun he => hv.2 he k x v hpre hres)
  | callv h a ihh iha =>
    intro hv hr
    have hr' := fun f h' => by have := hr f h'; simp [refs] at this; exact this
    have ⟨eh, okh⟩ := ihh hv.1 (fun f h' => (hr' f h').1)
    have ⟨ea, oka⟩ := iha hv.2 (fun f h' => (hr' f h').2)
    simp only [evalE, eh, ea]
    cases hh : evalE (erasedRun k) x h with
    | none => exact ⟨rfl, trivial⟩
    | some r =>
      cases r with
      | fail => exact ⟨rfl, trivial⟩
      | ok w =>
        cases w with
        | int _ => exact ⟨rfl, trivial⟩
        | fn f =>
          rw [hh] at okh
          cases hres : evalE (erasedRun k) x a with
          | none => exact ⟨rfl, trivial⟩
          | some r =>
            cases r with
            | fail => exact ⟨rfl, trivial⟩
            | ok v =>
              rw [hres] at oka
              exact ih f v oka (fun he => by simp [ResOk, ValOk] at okh; simp [okh] at he)

theorem run_agree {main : Fn} (h : Erasable P erased main) :
    ∀ n f x, ValOk erased x → (erased f = true → P.pre f x = true) →
      full n f x = erasedRun n f x ∧ ResOk erased (erasedRun n f x) := by
  intro n
  induction n with
  | zero => intro _ _ _ _; exact ⟨rfl, trivial⟩
  | succ k ih =>
    intro f x hx hpre
    by_cases hp : P.pre f x = true
    · simp only [run, hp, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
      exact evalE_agree P erased k ih f x hp hx (P.body f) (h.sites_proved f)
        (fun g hg => h.not_a_value g f hg)
    · have hf : erased f = false := by
        cases hE : erased f
        · rfl
        · exact absurd (hpre hE) hp
      have hp' : P.pre f x = false := by simpa using hp
      simp [run, hp', hf, ResOk]

/-- Erasing the preconditions `contracts::levels` marks proved changes nothing. -/
theorem erasure_sound {main : Fn} (h : Erasable P erased main) (n : Nat) (x : Val)
    (hx : ValOk erased x) : full n main x = erasedRun n main x :=
  (run_agree P erased h n main x hx (fun he => by simp [h.not_main] at he)).1

end

/-! Each condition is needed. In both programs below, function 1 requires a
positive argument and is called with 0, and erasing its check lets the call
through. -/

/-- 1 is called only through a value, so no VC covers the call. -/
def viaValue : Prog where
  body | 0 => .callv (.ref 1) (.lit 0) | _ => .arg
  pre f x := f != 1 || x != .int 0

example : run viaValue (fun _ => true) 3 0 (.int 0) = some .fail := by rfl
example : run viaValue (fun f => f != 1) 3 0 (.int 0) = some (.ok (.int 0)) := by rfl
example : (∀ g, VCs viaValue (· == 1) g (viaValue.body g)) := by
  intro g; cases g <;> simp [VCs, viaValue]

/-- 1 is `main`: the runtime calls it, and no call site in the program does. -/
def asMain : Prog where
  body _ := .arg
  pre f x := f != 1 || x != .int 0

example : run asMain (fun _ => true) 1 1 (.int 0) = some .fail := by rfl
example : run asMain (fun f => f != 1) 1 1 (.int 0) = some (.ok (.int 0)) := by rfl

end Warrant
