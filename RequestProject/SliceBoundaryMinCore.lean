/-
# Boundary-min core (scalar version)

The DOMINANT new lemma behind the `d*`-rank construction: the running min of an
`AffineOnResiduesZ` scalar over an initial segment `[0, N)` is `AffineOnResiduesZ`
in `N`, attained at a per-residue boundary.  Part of the (WIP) arity-1 `fas`
discharge track (`SliceVectorLexMin` → `SliceDstarCore`); axiom-clean.
-/
import RequestProject.SliceThreshold

namespace SliceBoundaryMinCore

open SliceThreshold SliceAffine

/-! ## Running minimum and its lattice spec -/

/-- Running minimum over `[0, N)`; `runningMin F 0 = 0` is never read in the
application (guarded by the `D`-nonempty branch). -/
noncomputable def runningMin (F : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | N + 1 => if N = 0 then F 0 else min (runningMin F N) (F N)

/-! ## `AffineOnResiduesZ` closed under finite `Finset.inf'` -/

theorem finsetMin_affineOnResiduesZ {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (G : ι → ℕ → ℤ) (hG : ∀ i ∈ s, AffineOnResiduesZ (G i)) :
    AffineOnResiduesZ (fun N => s.inf' hs (fun i => G i N)) := by
  classical
  induction s using Finset.induction with
  | empty => exact absurd hs (by simp)
  | insert a s ha ih =>
      rcases s.eq_empty_or_nonempty with hse | hsne
      · subst hse
        refine (hG a (by simp)).congr (fun N => ?_); simp
      · have ihres : AffineOnResiduesZ (fun N => s.inf' hsne (fun i => G i N)) :=
          ih hsne (fun i hi => hG i (Finset.mem_insert_of_mem hi))
        have hga : AffineOnResiduesZ (G a) := hG a (by simp)
        refine (hga.min ihres).congr (fun N => ?_)
        rw [Finset.inf'_insert]

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

theorem numReps_affineOnResidues (m p r : ℕ) (hp : 1 ≤ p) :
    AffineOnResidues (numReps m p r) := by
  -- `numReps m p r N = #{k : m+r+p·k < N} = #{ j ∈ range N : (j-(m+r)) divisibility-free count }`;
  -- it is `AffineOnResidues` since it is the integer interval count `#{j<N : m+r ≤ j}` thinned by `p`.
  -- We obtain it as the `.toNat` of the `AffineOnResiduesZ` sequence `((N-(m+r)-1)/p + 1)` clamped.
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hZ : AffineOnResiduesZ (fun N => (numReps m p r N : ℤ)) := by
    -- eventually (for N > m+r) equal to `((N-(m+r)-1)/p) + 1`, an AffineOnResiduesZ sequence
    have hcore : AffineOnResiduesZ
        (fun N => (((N : ℤ) - (m + r) - 1) / (p : ℤ)) + 1) :=
      ((((AffineOnResiduesZ.id_cast).sub
        (AffineOnResiduesZ.const ((m + r : ℕ) : ℤ))).sub (AffineOnResiduesZ.const 1)).ediv
        (p : ℤ) hpZ).add (AffineOnResiduesZ.const 1)
    -- for small N (N ≤ m+r) numReps = 0; the AffineOnResiduesZ.toNat will absorb the transient.
    refine AffineOnResiduesZ.congr_eventually (N := m + r + 1) (fun N hN => ?_) hcore
    unfold numReps
    rw [if_pos (by omega)]
    have hdiv : (((N - (m + r) - 1 : ℕ) / p : ℕ) : ℤ)
        = ((N : ℤ) - (m + r) - 1) / (p : ℤ) := by
      rw [Int.natCast_div]
      congr 1
      have : m + r + 1 ≤ N := hN
      omega
    show ((((N - (m + r) - 1 : ℕ) / p + 1 : ℕ)) : ℤ) = ((N : ℤ) - (m + r) - 1) / (p : ℤ) + 1
    rw [Nat.cast_add, Nat.cast_one, hdiv]
  -- numReps is ℕ-valued, so it equals its own `.toNat`-recast
  have := hZ.toNat
  refine AffineOnResidues.congr_eventually (N := 0) (fun N _ => ?_) this
  simp

/-! ## Per-class boundary value -/

noncomputable def bvalue (F : ℕ → ℤ) (m r : ℕ) (s : ℕ → ℤ) (K : ℕ) : ℤ :=
  if 0 ≤ s r then F (m + r) else F (m + r) + ((K : ℤ) - 1) * s r

theorem bvalue_is_min (F : ℕ → ℤ) {m p : ℕ} {s : ℕ → ℤ}
    (hrec : ∀ r k : ℕ, F (m + r + p * k) = F (m + r) + k * s r) (r : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    (∀ k, k < K → bvalue F m r s K ≤ F (m + r + p * k)) ∧
      (∃ k, k < K ∧ bvalue F m r s K = F (m + r + p * k)) := by
  unfold bvalue
  by_cases hs : 0 ≤ s r
  · rw [if_pos hs]
    refine ⟨fun k _ => ?_, ⟨0, hK, by rw [hrec r 0]; simp⟩⟩
    rw [hrec r k]
    have : 0 ≤ (k : ℤ) * s r := mul_nonneg (Int.natCast_nonneg k) hs
    omega
  · rw [if_neg hs]; push Not at hs
    refine ⟨fun k hk => ?_, ⟨K - 1, by omega, ?_⟩⟩
    · rw [hrec r k]
      have hkK : (k : ℤ) ≤ (K : ℤ) - 1 := by omega
      nlinarith [mul_le_mul_of_nonpos_right hkK (le_of_lt hs)]
    · rw [hrec r (K - 1)]
      have : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
      rw [this]

theorem bvalue_numReps_affineOnResiduesZ (F : ℕ → ℤ) (m p : ℕ) (s : ℕ → ℤ) (r : ℕ)
    (hp : 1 ≤ p) :
    AffineOnResiduesZ (fun N => bvalue F m r s (numReps m p r N)) := by
  unfold bvalue
  by_cases hs : 0 ≤ s r
  · simp only [if_pos hs]; exact AffineOnResiduesZ.const _
  · simp only [if_neg hs]
    refine (AffineOnResiduesZ.const (F (m + r))).add ?_
    have hnZ : AffineOnResiduesZ (fun N => ((numReps m p r N : ℤ) - 1)) :=
      (AffineOnResiduesZ.of_natCast (numReps_affineOnResidues m p r hp)).sub
        (AffineOnResiduesZ.const 1)
    exact (hnZ.smul (s r)).congr (fun N => by ring)

/-! ## Capstone: the running min is `AffineOnResiduesZ`

`runningMin F N`, for `N ≥ m + p`, equals the `Finset.inf'` over `j ∈ [0, m+p)` of
a per-`j` `AffineOnResiduesZ` sequence:
  - for `j < m` (the transient): the constant `F j`;
  - for `m ≤ j < m+p` (representing residue class `r = j - m < p`): the per-class
    boundary value `bvalue F m r s (numReps m p r N)`.
Each summand is `AffineOnResiduesZ` (`const` / `bvalue_numReps_affineOnResiduesZ`),
and `finsetMin_affineOnResiduesZ` folds them; `congr_eventually` discards the
transient `N < m + p`. -/

/-- The per-`j` summand: transient value `F j` for `j < m`, else the class
boundary value of residue `j - m`. -/
noncomputable def summand (F : ℕ → ℤ) (m p : ℕ) (s : ℕ → ℤ) (j : ℕ) (N : ℕ) : ℤ :=
  if j < m then F j else bvalue F m (j - m) s (numReps m p (j - m) N)

/-! ## Vector lift: the per-residue lex-boundary coordinate

For a `RankAffine` vector `F : ℕ → Fin d → ℤ` with period vector `P` (the slope,
**residue-independent**), the lex order on the indices of a single residue class is
total with direction fixed by `P`: lex-min at `k = 0` if `P` is lex-non-negative,
at the last `k` if `P` is lex-negative.  Crucially the boundary choice is the SAME
for every coordinate `i` (it is decided by `P` alone), so the `i`-th coordinate of
the per-class lex-min vector is

    `F(m+r) i`                          if `P` is lex-≥ 0 (take first index),
    `F(m+r) i + (K-1)·(P i)`            if `P` is lex-< 0 (take last index).

Both are `AffineOnResiduesZ` in `N` (`K = numReps`).  This is the only genuinely
vector-specific computation; the cross-residue lex-min is then an
eventually-periodic tournament of `lexLt` comparisons among the `p` per-class
boundary vectors (each coordinate `AffineOnResiduesZ`), reducing to
`SliceOrder.lexLt_eventuallyPeriodic` + `affineOnResidues_indicator_of_EP`. -/

/-- **The per-class lex-boundary coordinate is `AffineOnResiduesZ`.**  With a single
global boundary flag `takeLast : Bool` (decided by the lex-sign of the period vector
`P`, the same for every residue and coordinate), the `i`-th coordinate of the
per-class lex-min is affine on residues of `N`. -/
theorem lexBoundaryCoord_affineOnResiduesZ (Fi : ℕ → ℤ) (m p : ℕ) (Pi : ℤ) (r : ℕ)
    (takeLast : Bool) (hp : 1 ≤ p) :
    AffineOnResiduesZ
      (fun N => if takeLast then Fi (m + r) + ((numReps m p r N : ℤ) - 1) * Pi
                else Fi (m + r)) := by
  cases takeLast with
  | false => simp only [Bool.false_eq_true, if_false]; exact AffineOnResiduesZ.const _
  | true =>
      simp only [if_true]
      refine (AffineOnResiduesZ.const (Fi (m + r))).add ?_
      have hnZ : AffineOnResiduesZ (fun N => ((numReps m p r N : ℤ) - 1)) :=
        (AffineOnResiduesZ.of_natCast (numReps_affineOnResidues m p r hp)).sub
          (AffineOnResiduesZ.const 1)
      exact (hnZ.smul Pi).congr (fun N => by ring)

/-! ## Per-class boundary INDEX (the argmin position)

The position analog of `bvalue`/`lexBoundaryCoord`: the loop-index in class `r` that
attains the class minimum over `[0, N)` — the first index `m + r` if `0 ≤ s r`, else
the last index `m + r + p·(K-1)` (`K = numReps`).  This is what `d*`'s position is
(per winning class); it is `AffineOnResidues` in `N`. -/

/-- The per-class boundary index attaining the class min over `[0,N)`. -/
noncomputable def bindex (m p r : ℕ) (s : ℕ → ℤ) (N : ℕ) : ℕ :=
  if 0 ≤ s r then m + r else m + r + p * (numReps m p r N - 1)

end SliceBoundaryMinCore
