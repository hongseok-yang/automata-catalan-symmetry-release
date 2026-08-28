/-
# Arity-1 atom-enumeration bridge: abstract atom counts ⇄ Finset `(copy, position)` sums

The output semantics (`SliceOutput.firstAscent_eq_countP`) expresses `firstAscent out` as a
`List.countP` over the abstract atom list (`atoms : List P.Atom`, `Atom = Σ c, Fin (arity c)→ℕ`).
The counting machinery (`SliceSelCount`, `countPeriodicInterval`) works with the finite double
Finset sum `∑_c ∑_{p<|w|}`.  This file bridges the two **for arity-1 presentations**, where every
coordinate function `Fin (arity c) → ℕ` is determined by its single value (so an atom is `(c, ·↦p)`)
and `validAtom` forces that value `< |w|`.

* `atom_countP_eq_finsetSum` — the general bridge: `atoms.countP Q = ∑_c ∑_{p<|w|}
  [sel c (·↦p) ∧ Q (c,·↦p)]`, via `List.toFinset_card_of_nodup` + `Finset.card_nbij'` with the
  arity-1 collapse (forward: read the single coordinate; inverse: the constant tuple `·↦p`).
* `count_U_eq_totalSelectedU` — corollary at `Q = (label = U)`: `out.count U` is the
  `totalSelectedU` summand (so `tailU = totalSelectedU − fas`, the former already affine-on-residues).

Pure counting identities — no `AffineOnResidues`, no `buchi`; axiom-clean
(`[propext, Classical.choice, Quot.sound]`).  Compose downstream with
`totalSelected_slice_affineOnResidues`; do not re-derive affineness here.
-/
import RequestProject.WRP
import RequestProject.SliceSelCount
import RequestProject.SliceOutput
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

open Step
open scoped Classical

namespace SliceBridge

/-- A transported single coordinate `0 : Fin (P.arity c)` (no `Fin.cast`). -/
def z (P : Polyreg.Presentation Step Step) (harity : ∀ c, P.arity c = 1) (c : Fin P.K) :
    Fin (P.arity c) := (harity c).symm ▸ (0 : Fin 1)

/-- The coordinate type is a subsingleton (the one place arity = 1 is essential). -/
theorem ss (P : Polyreg.Presentation Step Step) (harity : ∀ c, P.arity c = 1)
    (c : Fin P.K) : Subsingleton (Fin (P.arity c)) := by rw [harity c]; infer_instance

/-- Every coordinate function is constant. -/
theorem coord_det (P : Polyreg.Presentation Step Step) (harity : ∀ c, P.arity c = 1)
    (c : Fin P.K) (f : Fin (P.arity c) → ℕ) : f = fun _ => f (z P harity c) := by
  have := ss P harity c; funext t; congr 1; exact Subsingleton.elim _ _

/-- An atom equals its collapsed (constant-tuple) form. -/
theorem atom_eq (P : Polyreg.Presentation Step Step) (harity : ∀ c, P.arity c = 1)
    (a : P.Atom) : a = ⟨a.1, fun _ => a.2 (z P harity a.1)⟩ := by
  obtain ⟨c, f⟩ := a; exact Sigma.ext rfl (heq_of_eq (coord_det P harity c f))

/-- `validAtom` of a constant-tuple atom is just the position bound. -/
theorem valid_iff (P : Polyreg.Presentation Step Step) (harity : ∀ c, P.arity c = 1)
    (c : Fin P.K) (p : ℕ) (w : List Step) : P.validAtom w ⟨c, fun _ => p⟩ ↔ p < w.length := by
  unfold Polyreg.Presentation.validAtom
  have := ss P harity c
  constructor
  · exact fun h => h (z P harity c)
  · exact fun h t => h

/-- **The arity-1 atom-enumeration bridge.**  Counting an atom predicate `Q` over the nodup list
of selected atoms equals the finite double sum over copies and positions `< |w|`. -/
theorem atom_countP_eq_finsetSum (P : Polyreg.Presentation Step Step) (harity : ∀ c, P.arity c = 1)
    (w : List Step) (Q : P.Atom → Bool) (atoms : List P.Atom) (hnd : atoms.Nodup)
    (hmem : ∀ a, a ∈ atoms ↔ P.selectedAtom w a) :
    atoms.countP Q = ∑ c : Fin P.K, ∑ p ∈ Finset.range w.length,
      if (P.sel c w (fun _ => p) ∧ Q ⟨c, fun _ => p⟩) then 1 else 0 := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _)]
  have hRHS : (∑ c, ∑ p ∈ Finset.range w.length,
        if (P.sel c w (fun _ => p) ∧ Q ⟨c, fun _ => p⟩) then 1 else 0)
      = ∑ x ∈ (Finset.univ : Finset (Fin P.K)).sigma (fun _ => Finset.range w.length),
          if (P.sel x.1 w (fun _ => x.2) ∧ Q ⟨x.1, fun _ => x.2⟩) then 1 else 0 := by
    rw [Finset.sum_sigma']
  rw [hRHS, Finset.sum_boole]
  apply Finset.card_nbij' (i := fun a => (⟨a.1, a.2 (z P harity a.1)⟩ : Σ _ : Fin P.K, ℕ))
    (j := fun x => (⟨x.1, fun _ => x.2⟩ : P.Atom))
  · intro a ha
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter] at ha
    obtain ⟨hain, hQa⟩ := ha
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range]
    obtain ⟨hval, hs⟩ := (hmem a).mp hain
    refine ⟨⟨Finset.mem_univ _, hval _⟩, ?_, ?_⟩
    · have := hs; rw [coord_det P harity a.1 a.2] at this; exact this
    · rw [← atom_eq P harity a]; exact hQa
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range] at hx
    obtain ⟨⟨_, hxlt⟩, hsel, hQx⟩ := hx
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter]
    exact ⟨(hmem _).mpr ⟨(valid_iff P harity x.1 x.2 w).mpr hxlt, hsel⟩, hQx⟩
  · intro a ha; exact (atom_eq P harity a).symm
  · intro x hx; rfl

/-- **`out.count U` is the `totalSelectedU` summand.**  Corollary of the bridge at
`Q = (label = U)`. -/
theorem count_U_eq_totalSelectedU (P : Polyreg.Presentation Step Step) (harity : ∀ c, P.arity c = 1)
    (w : List Step) (out : List Step) (atoms : List P.Atom) (hnd : atoms.Nodup)
    (hmem : ∀ a, a ∈ atoms ↔ P.selectedAtom w a) (hout : out = atoms.map (P.labelOf w)) :
    out.count U = ∑ c : Fin P.K, ∑ p ∈ Finset.range w.length,
      if (P.sel c w (fun _ => p) ∧ P.label c w (fun _ => p) = U) then 1 else 0 := by
  rw [hout, List.count_eq_countP, List.countP_map]
  rw [atom_countP_eq_finsetSum P harity w ((· == U) ∘ P.labelOf w) atoms hnd hmem]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun p _ => ?_))
  congr 1
  simp only [Function.comp_apply, Polyreg.Presentation.labelOf, beq_iff_eq]

/-- **Capstone of the semantic bridge.**  `firstAscent` of a WRP output, as a fully
atoms-independent Finset count over `(copy, position)`: the selected `U`-atoms `(c,·↦p)`
that `≺`-precede every selected `D`-atom (`label = U ∨ wrpOrd`).  Combines
`SliceOutput.firstAscent_eq_countP` (the sorted-output characterisation) with the
arity-1 enumeration bridge.  This is the exact `fas(n)` spec the counting machinery
(`dstarRank`/`countPeriodicInterval`) must show affine-on-residues. -/
theorem firstAscent_eq_selectedCount (P : WRP.Presentation Step Step)
    (hV : P.Valid) (harity : ∀ c, P.toPoly.arity c = 1) (w : List Step) (out : List Step)
    (hout : P.IsOutput w out) :
    firstAscent out = ∑ c : Fin P.toPoly.K, ∑ p ∈ Finset.range w.length,
      if (P.toPoly.sel c w (fun _ => p) ∧ P.toPoly.label c w (fun _ => p) = U ∧
          ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom w b →
            (P.toPoly.label b.1 w b.2 = U ∨ P.wrpOrd w ⟨c, fun _ => p⟩ b)) then 1 else 0 := by
  obtain ⟨atoms, hnd, hmem, hfa⟩ := SliceOutput.firstAscent_eq_countP P hV w out hout
  rw [hfa, atom_countP_eq_finsetSum P.toPoly harity w
      (fun a => decide (P.toPoly.labelOf w a = U) &&
        atoms.all (fun b => decide (P.toPoly.labelOf w b = U) || decide (P.wrpOrd w a b)))
      atoms hnd hmem]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun p _ => ?_))
  refine if_congr ?_ rfl rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, hmem]
  simp only [Polyreg.Presentation.labelOf]

/-- **The D-absent branch of `fas`.**  When `W_n` has no selected `D`-atom (every selected
atom is `U`-labelled), the `∀`-condition in `firstAscent_eq_selectedCount` is vacuously
satisfied, so `firstAscent out` is exactly `totalSelectedU` (the count proved
affine-on-residues by `totalSelected_slice_affineOnResidues`). -/
theorem firstAscent_eq_totalSelectedU_of_noD (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1) (w : List Step) (out : List Step)
    (hout : P.IsOutput w out) (hnoD : ∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = U) :
    firstAscent out = ∑ c : Fin P.toPoly.K, ∑ p ∈ Finset.range w.length,
      if (P.toPoly.sel c w (fun _ => p) ∧ P.toPoly.label c w (fun _ => p) = U) then 1 else 0 := by
  rw [firstAscent_eq_selectedCount P hV harity w out hout]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun p _ => ?_))
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨hsel, hlab, _⟩; exact ⟨hsel, hlab⟩
  · rintro ⟨hsel, hlab⟩; exact ⟨hsel, hlab, fun b hb => Or.inl (hnoD b hb)⟩

end SliceBridge
