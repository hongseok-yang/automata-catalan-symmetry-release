/-
# Bridging the rank tower to the threshold-count kernel (fas assembly glue)

The `fas` count compares an atom's rank `rank_u(j)` (a `SliceRankAtom.RankAffine`
`ℤ^d`-vector in the loop-index `j`) against a moving threshold that is
`SliceThreshold.AffineOnResiduesZ` in `n`.  The lex comparison is done coordinate by
coordinate, so the first thing the assembly needs is: **each coordinate of a
`RankAffine` vector sequence is `AffineOnResiduesZ`**.  This file provides that bridge
(`rankAffine_coord_affineOnResiduesZ`) and the prefix-invariance repackaging
(`rank_block_prefix_invariant`) that lets the count read ranks at `W_{j+1}` instead of
`W_n`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import RequestProject.SliceRankRegions
import RequestProject.SliceThreshold

open WRP Step

namespace SliceRankAtom

/-- **Each coordinate of a `RankAffine` `ℤ^d`-vector sequence is `AffineOnResiduesZ`.**
The recurrence-form bridge from the rank tower (`F(j+p)=F j+P` for `j≥m`) to the
threshold algebra (`F'(m+r+p·k)=F'(m+r)+k·s r`). -/
theorem rankAffine_coord_affineOnResiduesZ {d : ℕ} {F : ℕ → Fin d → ℤ}
    (hF : RankAffine F) (i : Fin d) :
    SliceThreshold.AffineOnResiduesZ (fun j => F j i) := by
  obtain ⟨m, p, P, hp, hrec⟩ := hF
  refine ⟨m, p, fun _ => P i, hp, fun r k => ?_⟩
  have hit := RankAffine.iterate hrec (m + r) k (by omega)
  have hi := congrFun hit i
  simpa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] using hi

/-- **Block ranks on `W_n` agree with the `W_{j+1}` representatives.**  For `j < n`
the rank at the block-`U` (`1+2j`) and block-`D` (`1+2j+1`) positions of `W_n` equals
the rank at the same position of `W_{j+1}` — the `RankAffine`-in-`j` sequence the rank
tower works with.  (Ranks are prefix-determined and both words share the prefix
`U(UD)^{j+1}`.) -/
theorem rank_block_prefix_invariant {Gamma : Type*} (P : WRP.Presentation Step Gamma)
    (c : Fin P.toPoly.K) (n j : ℕ) (hj : j < n) :
    P.rank c (wrappedFlat n) (fun _ => 1 + 2 * j)
        = P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j)
    ∧ P.rank c (wrappedFlat n) (fun _ => 1 + 2 * j + 1)
        = P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1) := by
  have hbig : (wrappedFlat n).take (1 + 2 * j + 1 + 1)
      = (wrappedFlat (j + 1)).take (1 + 2 * j + 1 + 1) := by
    rw [show 1 + 2 * j + 1 + 1 = 1 + 2 * (j + 1) from by ring,
      SliceWords.wrappedFlat_take (j + 1) n (by omega),
      SliceWords.wrappedFlat_take (j + 1) (j + 1) (le_refl _)]
  have hsmall : (wrappedFlat n).take (1 + 2 * j + 1)
      = (wrappedFlat (j + 1)).take (1 + 2 * j + 1) := by
    have e : ∀ w : List Step,
        w.take (1 + 2 * j + 1) = (w.take (1 + 2 * j + 1 + 1)).take (1 + 2 * j + 1) :=
      fun w => by rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [e (wrappedFlat n), e (wrappedFlat (j + 1)), hbig]
  exact ⟨rank_const_prefix_stable P c _ _ (1 + 2 * j) hsmall,
    rank_const_prefix_stable P c _ _ (1 + 2 * j + 1) hbig⟩

end SliceRankAtom
