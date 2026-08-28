/-
# Total selected-with-label count on the slice is affine-on-residues (arity 1)

Combining the marked recogniser (`MSOMark.markedDFA_exists`) with the completed
slice count (`SliceCount.countAccept_slice_affineOnResidues`): for an **arity-1**
polyregular presentation `P` and an output letter `g`, the number of
selected-position atoms labelled `g` on the slice `W_n`,

    Σ_c #{ p < |W_n| : sel c W_n (·↦p) ∧ label c W_n (·↦p) = g },

is affine on residue classes of `n`.  Taking `g = U` this is `totalSelectedU` — the
count whose `fas`/`tailU` split is the remaining rank-sort target.

The only arity-specific ingredient is `mso_arity_one`: an arity-1 MSO-definable
relation has a single-free-variable defining formula (proved by `subst` on the
arity equation — no transport/cast).  `#print axioms` is
`[propext, Classical.choice, Quot.sound, SliceMSO.buchi]` (the count of an MSO
property needs Büchi).
-/
import RequestProject.SliceCountSlice
import RequestProject.SliceSelect

open MSO MSOMark SliceCount Step
open scoped Classical

/-- An arity-1 MSO-definable relation is defined by a single-free-variable formula,
evaluated at the constant tuple `· ↦ p`. -/
theorem mso_arity_one {Alpha : Type*} {k : ℕ} (h : k = 1)
    {R : List Alpha → (Fin k → ℕ) → Prop} (hR : MSO.MSODefinableRel k R) :
    ∃ φ : MSO.Formula Alpha 1 0, ∀ (w : List Alpha) (p : ℕ),
      R w (fun _ => p) ↔ φ.Sat w (fun _ => p) Fin.elim0 := by
  subst h
  obtain ⟨ψ, hψ⟩ := hR
  exact ⟨ψ, fun w p => hψ w (fun _ => p)⟩

/-- **`totalSelectedU` (arity 1) is affine-on-residues.**  For an arity-1
polyregular presentation, the slice count of selected positions labelled `g` is
affine on residue classes of `n`. -/
theorem totalSelected_slice_affineOnResidues
    (P : Polyreg.Presentation Step Step) (g : Step) (harity : ∀ c, P.arity c = 1) :
    SliceAffine.AffineOnResidues (fun n =>
      ∑ c : Fin P.K, ∑ p ∈ Finset.range (wrappedFlat n).length,
        if (P.sel c (wrappedFlat n) (fun _ => p) ∧ P.label c (wrappedFlat n) (fun _ => p) = g)
          then 1 else 0) := by
  apply SliceAffine.AffineOnResidues.finsetSum
  intro c _
  obtain ⟨φsel, hsel⟩ := mso_arity_one (harity c) (P.selDef c)
  obtain ⟨φlab, hlab⟩ := mso_arity_one (harity c) (P.labelDef c g)
  obtain ⟨Mc, hMc⟩ := markedDFA_exists (Formula.and φsel φlab)
  have hconv : (fun n => ∑ p ∈ Finset.range (wrappedFlat n).length,
      if (P.sel c (wrappedFlat n) (fun _ => p) ∧ P.label c (wrappedFlat n) (fun _ => p) = g)
        then 1 else 0) = (fun n => countAccept Mc (wrappedFlat n)) := by
    funext n
    unfold countAccept ind
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_range] at hp
    have hiff : (P.sel c (wrappedFlat n) (fun _ => p) ∧
        P.label c (wrappedFlat n) (fun _ => p) = g) ↔ Mc.accepts (markAt (wrappedFlat n) p) := by
      rw [hMc (wrappedFlat n) p hp, Formula.sat_and, hsel (wrappedFlat n) p, hlab (wrappedFlat n) p]
    rw [if_congr hiff rfl rfl]
  rw [hconv]
  exact countAccept_slice_affineOnResidues Mc
