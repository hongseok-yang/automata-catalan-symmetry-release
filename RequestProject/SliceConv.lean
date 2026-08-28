/-
# Convolution of two purely-periodic sequences is affine on residue classes

The selection-*counting* construction of paper Lemma 6.4 reduces (after peeling the
forward/backward eventual-periodicity thresholds) to the following purely
combinatorial fact, which is its mathematical heart.

If `u : ℕ → α` is periodic with period `pu` and `v : ℕ → β` with period `pv`, then
for any `c : α → β → ℕ` the *convolution count*

    T(N) = Σ_{i < N} c (u i) (v (N-1-i))

is, on each residue class of `N` mod `P = pu·pv`, affine in the class index `k`:
`T(r + P·k) = T(r) + k · Δ_r`, with the per-class slope
`Δ_r = Σ_{s < P} c (u (r+s)) (v (P-1-s))`.

The point (and the reason the *purely* periodic case is the right core) is that
there is **no boundary term**: because `u`, `v` are periodic with no threshold,
shifting `N` by a full period `P` leaves every "old" summand unchanged
(`v((N-1-i)+P) = v(N-1-i)`) and simply appends one period's worth of new summands,
whose total is itself `P`-periodic in `N`.  This is proved directly, no `native`
anything; `#print axioms` shows only `[propext, Quot.sound]`.
-/
import Mathlib

namespace SliceConv

/-- **Convolution of two periodic sequences is affine on residue classes.**
With `P = pu·pv`, the convolution count `T(N) = Σ_{i<N} c (u i) (v (N-1-i))`
satisfies `T(r + P·k) = T(r) + k · Δ_r` for the per-class slope `Δ_r`. -/
theorem convolution_affineOnResidues {α β : Type*} (u : ℕ → α) (v : ℕ → β)
    (pu pv : ℕ) (hpu : 1 ≤ pu) (hpv : 1 ≤ pv)
    (hu : ∀ i, u (i + pu) = u i) (hv : ∀ j, v (j + pv) = v j) (c : α → β → ℕ) :
    ∃ P : ℕ, 1 ≤ P ∧ ∀ r k : ℕ,
      (∑ i ∈ Finset.range (r + P * k), c (u i) (v (r + P * k - 1 - i))) =
      (∑ i ∈ Finset.range r, c (u i) (v (r - 1 - i))) +
        k * (∑ s ∈ Finset.range (pu * pv), c (u (r + s)) (v (pu * pv - 1 - s))) := by
  set P := pu * pv with hPdef
  have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- period-`P` periodicity of `u` and `v`
  have hu_mul : ∀ (m i : ℕ), u (i + pu * m) = u i := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih => intro i; rw [Nat.mul_succ, ← Nat.add_assoc, hu, ih]
  have hv_mul : ∀ (m j : ℕ), v (j + pv * m) = v j := by
    intro m
    induction m with
    | zero => intro j; simp
    | succ m ih => intro j; rw [Nat.mul_succ, ← Nat.add_assoc, hv, ih]
  have huP : ∀ i, u (i + P) = u i := fun i => hu_mul pv i
  have hvP : ∀ j, v (j + P) = v j := fun j => by
    rw [hPdef, Nat.mul_comm pu pv]; exact hv_mul pu j
  have huP_mul : ∀ (k i : ℕ), u (i + P * k) = u i := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih => intro i; rw [Nat.mul_succ, ← Nat.add_assoc, huP, ih]
  -- one full period appends one period's worth of new summands; old ones unchanged
  have hsplit : ∀ N,
      (∑ i ∈ Finset.range (N + P), c (u i) (v (N + P - 1 - i))) =
      (∑ i ∈ Finset.range N, c (u i) (v (N - 1 - i))) +
        (∑ s ∈ Finset.range P, c (u (N + s)) (v (P - 1 - s))) := by
    intro N
    rw [Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show N + P - 1 - i = (N - 1 - i) + P from by omega, hvP]
    · apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_range] at hs
      rw [show N + P - 1 - (N + s) = P - 1 - s from by omega]
  -- the appended period's total is `P`-periodic in `N`
  have hIncPer : ∀ N k,
      (∑ s ∈ Finset.range P, c (u (N + P * k + s)) (v (P - 1 - s))) =
      (∑ s ∈ Finset.range P, c (u (N + s)) (v (P - 1 - s))) := by
    intro N k
    apply Finset.sum_congr rfl
    intro s _
    rw [show N + P * k + s = (N + s) + P * k from by ring, huP_mul k (N + s)]
  refine ⟨P, hP, fun r k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show r + P * (k + 1) = (r + P * k) + P from by ring, hsplit (r + P * k), ih,
        hIncPer r k]
      ring

end SliceConv
