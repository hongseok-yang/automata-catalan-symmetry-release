/-
# Tuple-based MSO interpretations (ordinary polyregular functions)

Formalisation of `def:polyregular` (Tuple-based MSO interpretation; polyregular) of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.

A polyregular presentation has a finite set of *copies* (each with an arity
`k_c`); an *atom* is a pair `(c, ī)` of a copy and a `k_c`-tuple of input
positions.  The presentation is required to specify, by MSO formulas, a domain
sentence, a selection predicate, a label, and an ordering relation `χ`.  The
output `eval w` is the concatenation of the labels of the selected atoms, listed
in increasing `χ`-order.

We give `eval` *declaratively*: `out = eval w` iff `out` is the labels of the
`χ`-sorted list of selected atoms (`Sorted` + `Nodup` + exact membership pins
that list uniquely when `χ` is a strict total order).  This avoids committing to
a sorting algorithm and never needs `Classical.choose`.
-/
import RequestProject.MSO

open MSO

namespace Polyreg

variable {Alpha Gamma : Type*}

/-- **`def:polyregular` (paper.tex).**  A polyregular presentation:
copies `Fin K` with arities, an MSO-definable domain, selection predicate, label
function, and ordering relation `χ`.  Each component carries its MSO-definability
obligation as a field, which is what makes the class restrictive. -/
structure Presentation (Alpha Gamma : Type*) where
  /-- Number of copies. -/
  K : ℕ
  /-- Arity (number of position coordinates) of each copy. -/
  arity : Fin K → ℕ
  /-- The domain `{w : domain w}`. -/
  domain : List Alpha → Prop
  /-- … is MSO-definable by a sentence. -/
  domainDef : ∃ φ : Sentence Alpha, ∀ w, domain w ↔ φ.Sat w Fin.elim0 Fin.elim0
  /-- Selection predicate: which tuples of copy `c` are output atoms on `w`. -/
  sel : (c : Fin K) → List Alpha → (Fin (arity c) → ℕ) → Prop
  /-- … is MSO-definable (one formula with `arity c` free variables per copy). -/
  selDef : ∀ c, MSODefinableRel (arity c) (fun w ī => sel c w ī)
  /-- Label of each atom. -/
  label : (c : Fin K) → List Alpha → (Fin (arity c) → ℕ) → Gamma
  /-- … each label-class is MSO-definable. -/
  labelDef : ∀ (c : Fin K) (g : Gamma), MSODefinableRel (arity c) (fun w ī => label c w ī = g)
  /-- Ordering relation `χ` comparing an atom of copy `c` with one of copy `c'`. -/
  ord : (c c' : Fin K) → List Alpha → (Fin (arity c) → ℕ) → (Fin (arity c') → ℕ) → Prop
  /-- … is MSO-definable (one formula with `arity c + arity c'` free vars per pair). -/
  ordDef : ∀ c c', MSODefinableRel (arity c + arity c')
    (fun w ij => ord c c' w (fun t => ij (Fin.castAdd _ t)) (fun t => ij (Fin.natAdd _ t)))

namespace Presentation

variable (P : Presentation Alpha Gamma)

/-- An *atom*: a copy together with a tuple of input positions of its arity. -/
abbrev Atom := Σ c : Fin P.K, Fin (P.arity c) → ℕ

/-- The copy of an atom. -/
def Atom.copy {P : Presentation Alpha Gamma} (a : P.Atom) : Fin P.K := a.1

/-- An atom is *valid for `w`* when all of its positions are inside `w`. -/
def validAtom (w : List Alpha) (a : P.Atom) : Prop := ∀ t, a.2 t < w.length

/-- The *selected* atoms of `w`: valid atoms whose selection formula holds. -/
def selectedAtom (w : List Alpha) (a : P.Atom) : Prop :=
  P.validAtom w a ∧ P.sel a.1 w a.2

/-- The order relation `χ` lifted to atoms. -/
def atomOrd (w : List Alpha) (a b : P.Atom) : Prop := P.ord a.1 b.1 w a.2 b.2

/-- The label of an atom. -/
def labelOf (w : List Alpha) (a : P.Atom) : Gamma := P.label a.1 w a.2

/-- **Validity of a presentation.**  On every word, `χ` is a strict total order on
the selected atoms: irreflexive, transitive, and trichotomous.  (The paper builds
`χ` to linearly order the output atoms.) -/
structure Valid : Prop where
  irrefl : ∀ w a, P.selectedAtom w a → ¬ P.atomOrd w a a
  trans : ∀ w a b c, P.selectedAtom w a → P.selectedAtom w b → P.selectedAtom w c →
    P.atomOrd w a b → P.atomOrd w b c → P.atomOrd w a c
  trichot : ∀ w a b, P.selectedAtom w a → P.selectedAtom w b →
    P.atomOrd w a b ∨ a = b ∨ P.atomOrd w b a

/-- **Declarative output (`def:polyregular`).**  `out` is the output of `P` on `w` iff it is
the list of labels of the selected atoms, listed without repetition, in
increasing `χ`-order.  When `P` is `Valid`, this `out` is unique. -/
def IsOutput (w : List Alpha) (out : List Gamma) : Prop :=
  ∃ atoms : List P.Atom,
    atoms.Nodup ∧
    (∀ a, a ∈ atoms ↔ P.selectedAtom w a) ∧
    atoms.Pairwise (P.atomOrd w) ∧
    out = atoms.map (P.labelOf w)

/-- **Output uniqueness**: a valid polyregular presentation has at most one
declarative output per word.  (The `Polyreg.Presentation` analogue of the WRP
`isOutput_unique`.) -/
theorem isOutput_unique (hV : P.Valid) {w : List Alpha} {out₁ out₂ : List Gamma}
    (h₁ : P.IsOutput w out₁) (h₂ : P.IsOutput w out₂) : out₁ = out₂ := by
  obtain ⟨l₁, nd₁, mem₁, pw₁, rfl⟩ := h₁
  obtain ⟨l₂, nd₂, mem₂, pw₂, rfl⟩ := h₂
  have hperm : l₁.Perm l₂ :=
    (List.perm_ext_iff_of_nodup nd₁ nd₂).mpr (fun a => (mem₁ a).trans (mem₂ a).symm)
  have hl : l₁ = l₂ := by
    refine hperm.eq_of_pairwise ?_ pw₁ pw₂
    intro a b ha hb hab hba
    have sa' := (mem₁ a).mp ha
    have sb' := (mem₂ b).mp hb
    exact absurd (hV.trans w a b a sa' sb' sa' hab hba) (hV.irrefl w a sa')
  rw [hl]

end Presentation

/-- **`f` is an ordinary polyregular function** when it is realised by a valid
polyregular presentation: on its domain it returns the (unique) declarative
output, and off its domain it is undefined. -/
def IsPolyregular (f : List Alpha → Option (List Gamma)) : Prop :=
  ∃ P : Presentation Alpha Gamma, P.Valid ∧
    ∀ w out, f w = some out ↔ (P.domain w ∧ P.IsOutput w out)

/-- **`f` is a regular string transduction** (a deterministic MSO string
transduction; equivalently, by Engelfriet–Hoogeboom, a deterministic two-way
finite-state transduction / 2DFT) when it is realised by a valid polyregular
presentation all of whose copies have **arity 1**.  The arity-1 restriction makes
the presentation a *dimension-1* MSO interpretation: every output atom is a single
`(copy, input position)` pair, so the output length is linear in the input.  This
is the model meant by "deterministic MSO string transduction" / "2DFT" in the
paper's `cor:zeta-not-regular`. -/
def IsRegular (f : List Alpha → Option (List Gamma)) : Prop :=
  ∃ P : Presentation Alpha Gamma, P.Valid ∧ (∀ c, P.arity c = 1) ∧
    ∀ w out, f w = some out ↔ (P.domain w ∧ P.IsOutput w out)

/-- **Regular ⊆ polyregular**: a regular string transduction is in particular
ordinary polyregular (forget the arity-1 bound). -/
theorem IsRegular.isPolyregular {f : List Alpha → Option (List Gamma)}
    (h : IsRegular f) : IsPolyregular f := by
  obtain ⟨P, hv, _, hr⟩ := h
  exact ⟨P, hv, hr⟩

end Polyreg
