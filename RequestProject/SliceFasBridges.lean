/-
# Leaf bridges for the arity-1 `fas` discharge

Two small, foundational `AffineOnResidues`/`RankAffine` bridges that the §7 arity-1
discharge consumes downstream:

* `rankAffine_coord_affineOnResiduesZ` — a `RankAffine` `ℤ^d`-sequence is
  `AffineOnResiduesZ` in each coordinate (read the coordinate of the constant period
  vector `P` as the per-residue slope).  This is the bridge from the rank layer
  (`SliceRankAtom.RankAffine`) to the per-coordinate affine-on-residues layer that the
  `d*`-rank fold and the lex-below count need.
* `affineOnResidues_pair_to_affineInPeriod` — package two `AffineOnResidues` `ℕ`-sequences
  into the *paired* affine-in-period-index witness shape that the §7 theorem's conclusion
  (`wrp_slice_profile_affine`) demands of the slice profile `n ↦ (fas, tailU)`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import RequestProject.SliceRankAffine
import RequestProject.SliceThreshold
import RequestProject.SliceAffine

namespace SliceFasBridges

open SliceRankAtom SliceThreshold SliceAffine
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

/-- **`RankAffine` at a backward offset `n-1-l` is `AffineOnResiduesZ` per coord.**  (The
back / bulk-true `d*`-candidate values are `RB c (n-1-l)` for a fixed `l`; their coord is affine in
`n` with the rank's period vector as the global slope.) -/
theorem rankAffine_back_coord {d : ℕ} {F : ℕ → Fin d → ℤ} (hF : RankAffine F)
    (l : ℕ) (i : Fin d) : AffineOnResiduesZ (fun n => F (n - 1 - l) i) := by
  obtain ⟨m, p, P, hp, hrec⟩ := hF
  refine ⟨m + l + 1, p, fun _ => P i, hp, fun r k => ?_⟩
  simp only []
  rw [show m + l + 1 + r + p * k - 1 - l = (m + r) + p * k from by omega,
    show m + l + 1 + r - 1 - l = m + r from by omega,
    RankAffine.iterate hrec (m + r) k (by omega), Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]

/-- **Paired affine-in-period extraction.**  Two `AffineOnResidues` `ℕ`-sequences admit a
common threshold `m ≥ 1` and period `p ≥ 1` on which, for each residue `j < p`, both
sequences are simultaneously affine in the step count `k` — the exact witness shape of
`wrp_slice_profile_affine`'s conclusion. -/
theorem affineOnResidues_pair_to_affineInPeriod {f h : ℕ → ℕ}
    (hf : AffineOnResidues f) (hh : AffineOnResidues h) :
    ∃ (p m : ℕ), 1 ≤ p ∧ 1 ≤ m ∧ ∀ j, j < p →
      ∃ b₁ s₁ b₂ s₂ : ℕ, ∀ k,
        (f (m + j + p * k), h (m + j + p * k)) = (b₁ + k * s₁, b₂ + k * s₂) := by
  obtain ⟨mf, pf, sf, hpf, recf⟩ := hf
  obtain ⟨mh, ph, sh, hph, rech⟩ := hh
  refine ⟨pf * ph, max (max mf mh) 1, Nat.one_le_iff_ne_zero.mpr (by positivity),
    le_max_right _ _, fun j _ => ?_⟩
  set m := max (max mf mh) 1 with hm
  refine ⟨f (m + j), ph * sf (m + j - mf), h (m + j), pf * sh (m + j - mh), fun k => ?_⟩
  have ef : f (m + j + pf * ph * k) = f (m + j) + k * (ph * sf (m + j - mf)) := by
    have hb : m + j = mf + (m + j - mf) := by omega
    rw [show m + j + pf * ph * k = mf + (m + j - mf) + pf * (ph * k) from by rw [← hb]; ring,
      recf (m + j - mf) (ph * k), ← hb]
    ring
  have eg : h (m + j + pf * ph * k) = h (m + j) + k * (pf * sh (m + j - mh)) := by
    have hb : m + j = mh + (m + j - mh) := by omega
    rw [show m + j + pf * ph * k = mh + (m + j - mh) + ph * (pf * k) from by rw [← hb]; ring,
      rech (m + j - mh) (pf * k), ← hb]
    ring
  rw [ef, eg]

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
