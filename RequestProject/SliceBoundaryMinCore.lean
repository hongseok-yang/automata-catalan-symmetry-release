/-
# Boundary-min core (scalar version)

The DOMINANT new lemma behind the `d*`-rank construction: the running min of an
`AffineOnResiduesZ` scalar over an initial segment `[0, N)` is `AffineOnResiduesZ`
in `N`, attained at a per-residue boundary.  Part of the (WIP) arity-1 `fas`
discharge track (`SliceVectorLexMin` → `SliceDstarCore`); axiom-clean.
-/
import RequestProject.SliceThreshold

namespace SliceBoundaryMinCore

/-! ## Per-class representative count -/

noncomputable def numReps (m p r : ℕ) (N : ℕ) : ℕ :=
  if m + r < N then (N - (m + r) - 1) / p + 1 else 0

theorem mem_iff_lt_numReps (m p r N k : ℕ) (hp : 1 ≤ p) :
    m + r + p * k < N ↔ k < numReps m p r N := by
  unfold numReps
  by_cases hmr : m + r < N
  · rw [if_pos hmr]
    constructor
    · intro h
      have hkp : k ≤ (N - (m + r) - 1) / p :=
        (Nat.le_div_iff_mul_le hp).mpr (by rw [Nat.mul_comm]; omega)
      omega
    · intro h
      have hk : k ≤ (N - (m + r) - 1) / p := by omega
      have hle : p * k ≤ N - (m + r) - 1 :=
        calc p * k ≤ p * ((N - (m + r) - 1) / p) := Nat.mul_le_mul_left p hk
          _ = ((N - (m + r) - 1) / p) * p := by ring
          _ ≤ N - (m + r) - 1 := Nat.div_mul_le_self _ _
      omega
  · rw [if_neg hmr]; omega

end SliceBoundaryMinCore
