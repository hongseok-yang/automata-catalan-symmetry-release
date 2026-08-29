/-
# Leaf bridges for the arity-1 `fas` discharge

Two small, foundational `AffineOnResidues`/`RankAffine` bridges that the §7 arity-1
discharge consumes downstream:

* `rankAffine_coord_affineOnResiduesZ` — a `RankAffine` `ℤ^d`-sequence is
  `AffineOnResiduesZ` in each coordinate (read the coordinate of the constant period
  vector `P` as the per-residue slope).  This is the bridge from the rank layer
  (`SliceRankAtom.RankAffine`) to the per-coordinate affine-on-residues layer that the
  `d*`-rank fold and the lex-below count need.
* `rankAffine_align_common_period` — align a finite list of `RankAffine` `ℤ^d`-sequences on
  one common period, which the `d*`-rank fold needs before comparing them.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import RequestProject.SliceRankAffine
import RequestProject.SliceThreshold

namespace SliceFasBridges

open SliceRankAtom SliceThreshold
open scoped Classical

/-- **`RankAffine` ⇒ per-coordinate `AffineOnResiduesZ`.**  Each coordinate of a
`RankAffine` vector sequence is affine on residues, with the residue-independent slope
`P i` (the `i`-th coordinate of the period vector). -/
theorem rankAffine_coord_affineOnResiduesZ {d : ℕ} {F : ℕ → Fin d → ℤ}
    (hF : RankAffine F) (i : Fin d) :
    AffineOnResiduesZ (fun j => F j i) := by
  obtain ⟨m, p, P, hp, hrec⟩ := hF
  refine ⟨m, p, fun _ => P i, hp, fun r k => ?_⟩
  have hit : F (m + r + p * k) = F (m + r) + k • P := RankAffine.iterate hrec (m + r) k (by omega)
  show F (m + r + p * k) i = F (m + r) i + (k : ℤ) * P i
  rw [hit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]

/-- **n-ary period aligner.**  A finite list of `RankAffine` vector families admits a
single common threshold `m` and period `p` on which every family satisfies the
period-`p` recurrence (with its own period vector).  This is what lets
`SliceOrder.lexLt_eventuallyPeriodic` (which needs a *shared* period across the
compared families) be applied pairwise across all of `Fs` — the prerequisite for the
cross-family `d*`-rank lex-min fold (`SliceDstarCore.lexMinList_coord_affineOnResiduesZ`). -/
theorem rankAffine_align_common_period {d : ℕ} (Fs : List (ℕ → Fin d → ℤ))
    (h : ∀ F ∈ Fs, RankAffine F) :
    ∃ (m p : ℕ), 1 ≤ p ∧ ∀ F ∈ Fs, ∃ P : Fin d → ℤ, ∀ n, m ≤ n → F (n + p) = F n + P := by
  induction Fs with
  | nil => exact ⟨0, 1, le_refl 1, fun F hF => absurd hF (by simp)⟩
  | cons F rest ih =>
      obtain ⟨mF, pF, PF, hpF, hFrec⟩ := h F (by simp)
      obtain ⟨m', p', hp', hrest⟩ := ih (fun G hG => h G (by simp [hG]))
      refine ⟨max mF m', pF * p', Nat.one_le_iff_ne_zero.mpr (by positivity), fun G hG => ?_⟩
      rcases List.mem_cons.mp hG with rfl | hGrest
      · exact ⟨p' • PF, fun n hn => RankAffine.iterate hFrec n p' (by omega)⟩
      · obtain ⟨PG, hGrec⟩ := hrest G hGrest
        refine ⟨pF • PG, fun n hn => ?_⟩
        rw [Nat.mul_comm pF p']
        exact RankAffine.iterate hGrec n pF (by omega)

end SliceFasBridges
