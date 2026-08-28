/-
# Monadic second-order logic on words

Formalisation of `sec:mso` (Monadic second-order logic on words) of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.

We give a concrete, intrinsically-scoped syntax for MSO formulas over finite
words and the satisfaction relation `Sat`.  Positions are natural numbers,
constrained to be `< w.length` by the quantifiers; first-order variables range
over positions and second-order variables over finite sets of positions.

This is a *definition* file — it fixes the object language `MSO.Formula` and its
semantics.  Deep results (e.g. Büchi–Elgot–Trakhtenbrot: regular ⇔ MSO-definable)
are not proved here; where the paper uses them they are taken as axioms.
-/
import Mathlib

namespace MSO

/-- **`sec:mso` (paper.tex).**  MSO formulas over words, *intrinsically
scoped*: `Formula Alpha nf ns` has `nf` free first-order (position) variables and `ns`
free second-order (set) variables, addressed by de Bruijn indices `Fin nf` and
`Fin ns`.  Under a quantifier the bound variable becomes index `0` and the
previously-free variables shift up by one (`Fin.cons` in the semantics). -/
inductive Formula (Alpha : Type*) : ℕ → ℕ → Type _
  /-- `x_i < x_j` (the linear order on positions). -/
  | lt {nf ns} (i j : Fin nf) : Formula Alpha nf ns
  /-- `Q_a(x_i)` — the letter at position `x_i` is `a`. -/
  | labelEq {nf ns} (i : Fin nf) (a : Alpha) : Formula Alpha nf ns
  /-- `x_i ∈ X_j` (membership in a set variable). -/
  | mem {nf ns} (i : Fin nf) (j : Fin ns) : Formula Alpha nf ns
  | tru {nf ns} : Formula Alpha nf ns
  | neg {nf ns} : Formula Alpha nf ns → Formula Alpha nf ns
  | and {nf ns} : Formula Alpha nf ns → Formula Alpha nf ns → Formula Alpha nf ns
  | or {nf ns} : Formula Alpha nf ns → Formula Alpha nf ns → Formula Alpha nf ns
  /-- `∃ x_0. φ`, a first-order quantifier (binds a fresh position variable). -/
  | exFO {nf ns} : Formula Alpha (nf + 1) ns → Formula Alpha nf ns
  /-- `∃ X_0. φ`, a second-order (set) quantifier. -/
  | exSO {nf ns} : Formula Alpha nf (ns + 1) → Formula Alpha nf ns

namespace Formula

variable {Alpha : Type*}

/-- **Satisfaction.**  `Sat w ρ σ φ` holds when the word `w` satisfies `φ` under
the first-order valuation `ρ : Fin nf → ℕ` (positions) and second-order valuation
`σ : Fin ns → Finset ℕ` (sets of positions).  Quantifiers range over the valid
positions `{p | p < w.length}`. -/
def Sat (w : List Alpha) : ∀ {nf ns : ℕ}, (Fin nf → ℕ) → (Fin ns → Finset ℕ) →
    Formula Alpha nf ns → Prop
  | _, _, ρ, _, .lt i j => ρ i < ρ j
  | _, _, ρ, _, .labelEq i a => w[ρ i]? = some a
  | _, _, ρ, σ, .mem i j => ρ i ∈ σ j
  | _, _, _, _, .tru => True
  | _, _, ρ, σ, .neg φ => ¬ Sat w ρ σ φ
  | _, _, ρ, σ, .and φ ψ => Sat w ρ σ φ ∧ Sat w ρ σ ψ
  | _, _, ρ, σ, .or φ ψ => Sat w ρ σ φ ∨ Sat w ρ σ ψ
  | _, _, ρ, σ, .exFO φ => ∃ p, p < w.length ∧ Sat w (Fin.cons p ρ) σ φ
  | _, _, ρ, σ, .exSO φ => ∃ S : Finset ℕ, (∀ x ∈ S, x < w.length) ∧ Sat w ρ (Fin.cons S σ) φ

/-- Derived universal first-order quantifier `∀ x_0. φ`. -/
def faFO {nf ns} (φ : Formula Alpha (nf + 1) ns) : Formula Alpha nf ns := .neg (.exFO (.neg φ))

/-- Derived universal second-order quantifier `∀ X_0. φ`. -/
def faSO {nf ns} (φ : Formula Alpha nf (ns + 1)) : Formula Alpha nf ns := .neg (.exSO (.neg φ))

/-- Derived implication. -/
def imp {nf ns} (φ ψ : Formula Alpha nf ns) : Formula Alpha nf ns := .or (.neg φ) ψ

/-- Derived equality of positions `x_i = x_j`. -/
def eqPos {nf ns} (i j : Fin nf) : Formula Alpha nf ns := .and (.neg (.lt i j)) (.neg (.lt j i))

@[simp] theorem sat_lt (w : List Alpha) {nf ns} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ)
    (i j : Fin nf) : Sat w ρ σ (.lt i j) ↔ ρ i < ρ j := Iff.rfl

@[simp] theorem sat_labelEq (w : List Alpha) {nf ns} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ)
    (i : Fin nf) (a : Alpha) : Sat w ρ σ (.labelEq i a) ↔ w[ρ i]? = some a := Iff.rfl

@[simp] theorem sat_mem (w : List Alpha) {nf ns} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ)
    (i : Fin nf) (j : Fin ns) : Sat w ρ σ (.mem i j) ↔ ρ i ∈ σ j := Iff.rfl

@[simp] theorem sat_tru (w : List Alpha) {nf ns} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ) :
    Sat w ρ σ (.tru : Formula Alpha nf ns) ↔ True := Iff.rfl

@[simp] theorem sat_neg (w : List Alpha) {nf ns} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ)
    (φ : Formula Alpha nf ns) : Sat w ρ σ (.neg φ) ↔ ¬ Sat w ρ σ φ := Iff.rfl

@[simp] theorem sat_and (w : List Alpha) {nf ns} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ)
    (φ ψ : Formula Alpha nf ns) : Sat w ρ σ (.and φ ψ) ↔ Sat w ρ σ φ ∧ Sat w ρ σ ψ := Iff.rfl

@[simp] theorem sat_or (w : List Alpha) {nf ns} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ)
    (φ ψ : Formula Alpha nf ns) : Sat w ρ σ (.or φ ψ) ↔ Sat w ρ σ φ ∨ Sat w ρ σ ψ := Iff.rfl

@[simp] theorem sat_exFO (w : List Alpha) {nf ns} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ)
    (φ : Formula Alpha (nf + 1) ns) :
    Sat w ρ σ (.exFO φ) ↔ ∃ p, p < w.length ∧ Sat w (Fin.cons p ρ) σ φ := Iff.rfl

@[simp] theorem sat_exSO (w : List Alpha) {nf ns} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ)
    (φ : Formula Alpha nf (ns + 1)) :
    Sat w ρ σ (.exSO φ) ↔
      ∃ S : Finset ℕ, (∀ x ∈ S, x < w.length) ∧ Sat w ρ (Fin.cons S σ) φ := Iff.rfl

theorem sat_eqPos (w : List Alpha) {nf ns} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ)
    (i j : Fin nf) : Sat w ρ σ (eqPos i j) ↔ ρ i = ρ j := by
  simp only [eqPos, sat_and, sat_neg, sat_lt]; omega

end Formula

/-- A *sentence* is a formula with no free variables. -/
abbrev Sentence (Alpha : Type*) := Formula Alpha 0 0

/-- The language defined by a sentence. -/
def Sentence.language {Alpha : Type*} (φ : Sentence Alpha) : Set (List Alpha) :=
  {w | φ.Sat w Fin.elim0 Fin.elim0}

/-- A `k`-ary position relation is MSO-definable when it is the satisfying-tuple
relation of some formula with `k` free first-order variables. -/
def MSODefinableRel {Alpha : Type*} (k : ℕ) (R : (w : List Alpha) → (Fin k → ℕ) → Prop) : Prop :=
  ∃ φ : Formula Alpha k 0, ∀ w ρ, R w ρ ↔ φ.Sat w ρ Fin.elim0

end MSO
