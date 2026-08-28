/-
# Existence of a selected atom with a given label on the slice is eventually periodic

This is the first genuine connection of the concrete `Polyreg`/`WRP` selection model
to the textbook Büchi axiom, *without any new axiom*.  For a polyregular presentation
`P` and an output letter `g`, the predicate

    "the word `w` has a selected atom whose label is `g`"

is the language of a single MSO **sentence** `existsSentence P g`: for each copy `c`
take the selection formula `∧` the label formula (both supplied by the presentation's
`selDef`/`labelDef` fields), close their `arity c` free first-order variables by
iterated `∃` (`closeAllFO`), and disjoin over the finitely many copies (`bigOrFin`).

Feeding that sentence to `SliceMSO.mso_slice_eventuallyPeriodic` (Büchi + the proved
automaton periodicity) shows the predicate is **eventually periodic** along the
wrapped-flat slice `W_n = U(UD)^n D`.  Taking `g = D` gives the "is there a selected
`D`-atom" dichotomy that the first-`D`-atom analysis of the rank-sort splits on.

Note this is an EXISTENCE statement; it deliberately does *not* count selected atoms
(per-position counting needs a marked alphabet / forward–backward product, not the
existential closure used here).  `#print axioms` of the results shows only
`[propext, Classical.choice, Quot.sound, SliceMSO.buchi]`.
-/
import RequestProject.Polyregular
import RequestProject.MSOClose
import RequestProject.SliceMSO
import RequestProject.DyckPath

open MSO Polyreg Step

namespace SliceSelect

variable {Gamma : Type*}

/-- The per-copy existential-closure sentence: "copy `c` contributes a valid selected
atom labelled `g`". -/
noncomputable def copySentence (P : Polyreg.Presentation Step Gamma) (g : Gamma)
    (c : Fin P.K) : MSO.Sentence Step :=
  Formula.closeAllFO
    (Formula.and (Classical.choose (P.selDef c)) (Classical.choose (P.labelDef c g)))

/-- The sentence whose language is "`w` has a selected atom labelled `g`". -/
noncomputable def existsSentence (P : Polyreg.Presentation Step Gamma) (g : Gamma) :
    MSO.Sentence Step :=
  Formula.bigOrFin (fun c => copySentence P g c)

/-- **Characterisation.**  The `existsSentence` holds on `w` iff `w` really has a
selected atom labelled `g`. -/
theorem sat_existsSentence (P : Polyreg.Presentation Step Gamma) (g : Gamma) (w : List Step) :
    (existsSentence P g).Sat w Fin.elim0 Fin.elim0 ↔
      ∃ a : P.Atom, P.selectedAtom w a ∧ P.labelOf w a = g := by
  rw [existsSentence, Formula.sat_bigOrFin]
  constructor
  · rintro ⟨c, hc⟩
    rw [copySentence, Formula.sat_closeAllFO] at hc
    obtain ⟨ρ, hρ, hsat⟩ := hc
    rw [Formula.sat_and] at hsat
    obtain ⟨hsel, hlab⟩ := hsat
    exact ⟨⟨c, ρ⟩, ⟨hρ, ((Classical.choose_spec (P.selDef c)) w ρ).mpr hsel⟩,
      ((Classical.choose_spec (P.labelDef c g)) w ρ).mpr hlab⟩
  · rintro ⟨⟨c, ρ⟩, ⟨hvalid, hsel⟩, hlab⟩
    refine ⟨c, ?_⟩
    rw [copySentence, Formula.sat_closeAllFO]
    refine ⟨ρ, hvalid, ?_⟩
    rw [Formula.sat_and]
    exact ⟨((Classical.choose_spec (P.selDef c)) w ρ).mp hsel,
      ((Classical.choose_spec (P.labelDef c g)) w ρ).mp hlab⟩

/-- **Existence of a selected `g`-atom is eventually periodic on the slice.**
For a polyregular presentation `P` and output letter `g`, whether `W_n = U(UD)^n D`
contains a selected atom labelled `g` is eventually periodic in `n`.  Proved from the
existing textbook Büchi axiom only — no new axiom. -/
theorem selectedLabel_exists_slice_eventuallyPeriodic
    (P : Polyreg.Presentation Step Gamma) (g : Gamma) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ n, m ≤ n →
      ((∃ a : P.Atom, P.selectedAtom (wrappedFlat (n + p)) a ∧
          P.labelOf (wrappedFlat (n + p)) a = g) ↔
       (∃ a : P.Atom, P.selectedAtom (wrappedFlat n) a ∧
          P.labelOf (wrappedFlat n) a = g)) := by
  obtain ⟨m, p, hp, hper⟩ :=
    SliceMSO.mso_slice_eventuallyPeriodic (existsSentence P g) [U] [U, D] [D]
  refine ⟨m, p, hp, fun n hn => ?_⟩
  rw [← sat_existsSentence P g (wrappedFlat (n + p)), ← sat_existsSentence P g (wrappedFlat n)]
  exact hper n hn

end SliceSelect
