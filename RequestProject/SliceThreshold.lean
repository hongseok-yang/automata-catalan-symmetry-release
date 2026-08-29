/-
# Lattice points under a moving affine threshold are affine-on-residues (fas piece (c) crux)

The genuinely new combinatorial lemma behind the arity-1 `fas` count.  On the slice,
an atom at loop-index `j` has a rank that is `RankAffine` (affine on residue classes
of `j`), and the moving threshold `d*`-rank is affine on residue classes of `n`.  The
lexicographic `≺`-comparison of the two becomes, per coordinate, a Boolean combination
of affine inequalities `α·j ⋚ (affine in n)`, and the `fas` count is a sum over `j`
of such a predicate.  Counting `j` therefore reduces to counting integers in an
interval whose endpoints are affine on residue classes of `n`.

This file builds that counting kernel from scratch:

* `AffineOnResiduesZ` — the `ℤ`-valued analogue of `SliceAffine.AffineOnResidues`,
  in recurrence form `F(m+r+p·k) = F(m+r) + k·s r`.  Closed under
  `const / + / − / ℤ-smul / id / ℕ-cast / ediv-by-a-positive-constant / min / max`.
* `AffineOnResiduesZ.toNat` — the workhorse: the `ℕ`-truncation of an
  `AffineOnResiduesZ` sequence is `SliceAffine.AffineOnResidues`.  (Per residue class
  the sequence is affine; `toNat` either keeps the affine part with its non-negative
  slope or collapses to `0`, after a finite sign-stabilising transient.)
* `card_range_filter_Ico` — `#{j ∈ range N : lo ≤ j < hi} = (min N hi − max 0 lo)⁺`.
* `countInterval` — `n ↦ #{ j < U n : lo n ≤ j < hi n }` is affine-on-residues when
  `lo, hi` are `AffineOnResiduesZ` and `U` is affine-on-residues.  This is the
  workhorse the lex assembly uses (the lex predicate carves out an interval in `j`).
* `countLtThreshold` (the paper's `countBelowAffineThreshold`) — `n ↦ #{ j < U n :
  α·j < T n }` is affine-on-residues for any fixed `α : ℤ` (any sign, incl. `0`).

Everything is elementary number theory; all axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/
import RequestProject.SliceAffine

namespace SliceThreshold

open SliceAffine

/-- A `ℤ`-valued sequence is **affine on residue classes** in recurrence form:
beyond a threshold `m`, on the progression `m+r, m+r+p, …` it is affine in the step
count with a residue-dependent slope `s r`. -/
def AffineOnResiduesZ (F : ℕ → ℤ) : Prop :=
  ∃ (m p : ℕ) (s : ℕ → ℤ), 1 ≤ p ∧ ∀ r k : ℕ, F (m + r + p * k) = F (m + r) + k * s r

namespace AffineOnResiduesZ

/-- Transfer along pointwise equality. -/
theorem congr {F G : ℕ → ℤ} (h : ∀ n, F n = G n) (hF : AffineOnResiduesZ F) :
    AffineOnResiduesZ G := by
  obtain ⟨m, p, s, hp, hF⟩ := hF
  exact ⟨m, p, s, hp, fun r k => by rw [← h, ← h]; exact hF r k⟩

theorem const (v : ℤ) : AffineOnResiduesZ (fun _ => v) :=
  ⟨0, 1, fun _ => 0, le_refl 1, fun r k => by simp⟩

theorem add {F G : ℕ → ℤ} (hF : AffineOnResiduesZ F) (hG : AffineOnResiduesZ G) :
    AffineOnResiduesZ (fun n => F n + G n) := by
  obtain ⟨mf, pf, sf, hpf, hf⟩ := hF
  obtain ⟨mg, pg, sg, hpg, hg⟩ := hG
  refine ⟨max mf mg, pf * pg, fun r => pg * sf (max mf mg + r - mf) + pf * sg (max mf mg + r - mg),
    Nat.one_le_iff_ne_zero.mpr (by positivity), fun r k => ?_⟩
  set m := max mf mg with hm
  have ef : F (m + r + pf * pg * k) = F (m + r) + k * (pg * sf (m + r - mf)) := by
    have hb : m + r = mf + (m + r - mf) := by omega
    rw [show m + r + pf * pg * k = mf + (m + r - mf) + pf * (pg * k) from by rw [← hb]; ring,
      hf (m + r - mf) (pg * k), ← hb]; push_cast; ring
  have eg : G (m + r + pf * pg * k) = G (m + r) + k * (pf * sg (m + r - mg)) := by
    have hb : m + r = mg + (m + r - mg) := by omega
    rw [show m + r + pf * pg * k = mg + (m + r - mg) + pg * (pf * k) from by rw [← hb]; ring,
      hg (m + r - mg) (pf * k), ← hb]; push_cast; ring
  show F (m + r + pf * pg * k) + G (m + r + pf * pg * k) = _
  rw [ef, eg]; ring

theorem neg {F : ℕ → ℤ} (hF : AffineOnResiduesZ F) : AffineOnResiduesZ (fun n => - F n) := by
  obtain ⟨m, p, s, hp, hF⟩ := hF
  exact ⟨m, p, fun r => - s r, hp, fun r k => by show - F (m + r + p * k) = _; rw [hF r k]; ring⟩

theorem sub {F G : ℕ → ℤ} (hF : AffineOnResiduesZ F) (hG : AffineOnResiduesZ G) :
    AffineOnResiduesZ (fun n => F n - G n) := by
  refine (hF.add hG.neg).congr (fun n => ?_); ring

theorem smul (c : ℤ) {F : ℕ → ℤ} (hF : AffineOnResiduesZ F) :
    AffineOnResiduesZ (fun n => c * F n) := by
  obtain ⟨m, p, s, hp, hF⟩ := hF
  exact ⟨m, p, fun r => c * s r, hp, fun r k => by show c * F (m + r + p * k) = _; rw [hF r k]; ring⟩

/-- The identity `n ↦ (n : ℤ)` is affine on residues (slope `1`). -/
theorem id_cast : AffineOnResiduesZ (fun n => (n : ℤ)) :=
  ⟨0, 1, fun _ => 1, le_refl 1, fun r k => by push_cast; ring⟩

/-- The `ℕ`-cast of a `SliceAffine.AffineOnResidues` sequence is `AffineOnResiduesZ`. -/
theorem of_natCast {f : ℕ → ℕ} (hf : AffineOnResidues f) :
    AffineOnResiduesZ (fun n => (f n : ℤ)) := by
  obtain ⟨m, p, s, hp, hf⟩ := hf
  refine ⟨m, p, fun r => (s r : ℤ), hp, fun r k => ?_⟩
  show (f (m + r + p * k) : ℤ) = (f (m + r) : ℤ) + (k : ℤ) * (s r : ℤ)
  rw [hf r k]; push_cast; ring

end AffineOnResiduesZ

/-- A `ℕ`-valued sequence whose period-`p` recurrence holds for the residues
`r < p` (with a `p`-periodic slope) is `AffineOnResidues`. -/
theorem affineOnResidues_of_period {G : ℕ → ℕ} {m p : ℕ} (σ : ℕ → ℕ) (hp : 1 ≤ p)
    (h : ∀ r, r < p → ∀ k, G (m + r + p * k) = G (m + r) + k * σ r) :
    AffineOnResidues G := by
  refine ⟨m, p, fun r => σ (r % p), hp, fun r k => ?_⟩
  show G (m + r + p * k) = G (m + r) + k * σ (r % p)
  have hr0 : r % p < p := Nat.mod_lt _ hp
  have hdm := Nat.div_add_mod r p
  have e1 : m + r + p * k = m + r % p + p * (r / p + k) := by rw [Nat.mul_add]; omega
  have e2 : m + r = m + r % p + p * (r / p) := by omega
  rw [e1, e2, h (r % p) hr0 (r / p + k), h (r % p) hr0 (r / p)]
  ring

namespace AffineOnResiduesZ

/-- **The workhorse.**  The `ℕ`-truncation of an `AffineOnResiduesZ` sequence is
`SliceAffine.AffineOnResidues`.  Per residue class the sequence is affine; pushing
the threshold past a finite sign-stabilising transient, `toNat` either keeps the
affine part (with non-negative slope) or collapses to `0`. -/
theorem toNat {F : ℕ → ℤ} (hF : AffineOnResiduesZ F) :
    AffineOnResidues (fun n => (F n).toNat) := by
  obtain ⟨m, p, s, hp, hF⟩ := hF
  classical
  set K : ℕ := (Finset.range p).sup (fun r => (F (m + r)).natAbs) + 1 with hKdef
  have hbound : ∀ r, r < p → (F (m + r)).natAbs < K := by
    intro r hr
    have hle : (F (m + r)).natAbs ≤ (Finset.range p).sup (fun r => (F (m + r)).natAbs) :=
      Finset.le_sup (f := fun r => (F (m + r)).natAbs) (Finset.mem_range.mpr hr)
    omega
  have hsign : ∀ r, r < p →
      (0 ≤ F (m + r) + K * s r → 0 ≤ s r) ∧ (F (m + r) + K * s r < 0 → s r ≤ 0) := by
    intro r hr
    have hb := hbound r hr
    have habs : |F (m + r)| < (K : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hb
    obtain ⟨hgt, hlt⟩ := abs_lt.mp habs
    have hK0 : (0 : ℤ) ≤ (K : ℤ) := Int.natCast_nonneg K
    refine ⟨fun hbase => ?_, fun hbase => ?_⟩
    · by_contra hneg; push Not at hneg
      have hsr1 : s r ≤ -1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left hsr1 hK0]
    · by_contra hpos; push Not at hpos
      have hsr1 : 1 ≤ s r := by omega
      nlinarith [mul_le_mul_of_nonneg_left hsr1 hK0]
  refine affineOnResidues_of_period (m := m + p * K)
    (fun r => if 0 ≤ F (m + r) + K * s r then (s r).toNat else 0) hp ?_
  intro r hr k
  have idx1 : m + p * K + r + p * k = m + r + p * (K + k) := by ring
  have idx2 : m + p * K + r = m + r + p * K := by ring
  show (F (m + p * K + r + p * k)).toNat =
      (F (m + p * K + r)).toNat + k * (if 0 ≤ F (m + r) + K * s r then (s r).toNat else 0)
  rw [idx1, idx2, hF r (K + k), hF r K]
  obtain ⟨hsr1, hsr2⟩ := hsign r hr
  by_cases hbase : 0 ≤ F (m + r) + K * s r
  · have hsr : 0 ≤ s r := hsr1 hbase
    rw [if_pos hbase]
    have hge : 0 ≤ F (m + r) + (↑(K + k)) * s r := by
      push_cast; nlinarith [mul_nonneg (Int.natCast_nonneg k) hsr, hbase]
    have key : ((F (m + r) + (↑(K + k)) * s r).toNat : ℤ)
        = (((F (m + r) + ↑K * s r).toNat + k * (s r).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hge]
      push_cast [Int.toNat_of_nonneg hbase, Int.toNat_of_nonneg hsr]
      ring
    exact_mod_cast key
  · push Not at hbase
    have hsr : s r ≤ 0 := hsr2 hbase
    rw [if_neg (not_le.mpr hbase)]
    have hle : F (m + r) + (↑(K + k)) * s r ≤ 0 := by
      push_cast; nlinarith [mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg k) hsr, hbase]
    rw [Int.toNat_eq_zero.mpr hle, Int.toNat_eq_zero.mpr (le_of_lt hbase)]
    simp

/-- The `ℤ`-recast of the `ℕ`-truncation is `AffineOnResiduesZ`. -/
theorem toNatCast {X : ℕ → ℤ} (hX : AffineOnResiduesZ X) :
    AffineOnResiduesZ (fun n => ((X n).toNat : ℤ)) :=
  of_natCast (toNat hX)

/-- Pointwise `max` of two `AffineOnResiduesZ` sequences is `AffineOnResiduesZ`. -/
theorem max {A B : ℕ → ℤ} (hA : AffineOnResiduesZ A) (hB : AffineOnResiduesZ B) :
    AffineOnResiduesZ (fun n => max (A n) (B n)) :=
  (hA.add (hB.sub hA).toNatCast).congr (fun n => by omega)

/-- Pointwise `min` of two `AffineOnResiduesZ` sequences is `AffineOnResiduesZ`. -/
theorem min {A B : ℕ → ℤ} (hA : AffineOnResiduesZ A) (hB : AffineOnResiduesZ B) :
    AffineOnResiduesZ (fun n => min (A n) (B n)) :=
  (hA.sub (hA.sub hB).toNatCast).congr (fun n => by omega)

/-- Euclidean division by a fixed positive constant preserves `AffineOnResiduesZ`. -/
theorem ediv_pos (α : ℤ) (hα : 0 < α) {F : ℕ → ℤ} (hF : AffineOnResiduesZ F) :
    AffineOnResiduesZ (fun n => F n / α) := by
  obtain ⟨m, p, s, hp, hF⟩ := hF
  have hαN : 1 ≤ α.toNat := by omega
  have hαcast : (α.toNat : ℤ) = α := Int.toNat_of_nonneg (le_of_lt hα)
  refine ⟨m, p * α.toNat, fun r => s r, Nat.mul_pos (by omega) (by omega), fun r k => ?_⟩
  show F (m + r + p * α.toNat * k) / α = F (m + r) / α + k * s r
  rw [show m + r + p * α.toNat * k = m + r + p * (α.toNat * k) from by ring, hF r (α.toNat * k)]
  rw [show F (m + r) + (↑(α.toNat * k)) * s r = F (m + r) + α * ((k : ℤ) * s r) from by
    push_cast; rw [hαcast]; ring]
  rw [Int.add_mul_ediv_left _ _ (ne_of_gt hα)]

/-- Euclidean division by any fixed nonzero constant preserves `AffineOnResiduesZ`. -/
theorem ediv (α : ℤ) (hα : α ≠ 0) {F : ℕ → ℤ} (hF : AffineOnResiduesZ F) :
    AffineOnResiduesZ (fun n => F n / α) := by
  obtain ⟨m, p, s, hp, hF⟩ := hF
  refine ⟨m, p * α.natAbs, fun r => if 0 < α then s r else - s r,
    Nat.mul_pos hp (by omega), fun r k => ?_⟩
  show F (m + r + p * α.natAbs * k) / α = F (m + r) / α + k * (if 0 < α then s r else - s r)
  rw [show m + r + p * α.natAbs * k = m + r + p * (α.natAbs * k) from by ring,
    hF r (α.natAbs * k)]
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · rw [if_neg (not_lt.mpr (le_of_lt hneg)),
      show F (m + r) + (↑(α.natAbs * k)) * s r = F (m + r) + α * ((k : ℤ) * (- s r)) from by
        push_cast; rw [abs_of_neg hneg]; ring,
      Int.add_mul_ediv_left _ _ hα]
  · rw [if_pos hpos,
      show F (m + r) + (↑(α.natAbs * k)) * s r = F (m + r) + α * ((k : ℤ) * s r) from by
        push_cast; rw [abs_of_pos hpos]; ring,
      Int.add_mul_ediv_left _ _ hα]

end AffineOnResiduesZ

/-- **The integer-interval count.**  `#{j ∈ [0,N) : lo ≤ j < hi}` equals the clamped
interval length `(min N hi − max 0 lo)⁺`. -/
theorem card_range_filter_Ico (N : ℕ) (lo hi : ℤ) :
    ((Finset.range N).filter (fun j : ℕ => lo ≤ (j : ℤ) ∧ (j : ℤ) < hi)).card
      = (min (N : ℤ) hi - max 0 lo).toNat := by
  have hset : (Finset.range N).filter (fun j : ℕ => lo ≤ (j : ℤ) ∧ (j : ℤ) < hi)
      = Finset.Ico (max 0 lo).toNat (min (N : ℤ) hi).toNat := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Nat.card_Ico]
  omega

/-- **`countInterval`.**  Counting `j ∈ [0, U n)` in an interval `[lo n, hi n)` whose
endpoints are affine on residue classes of `n` is itself affine on residue classes. -/
theorem countInterval {lo hi : ℕ → ℤ} {U : ℕ → ℕ}
    (hlo : AffineOnResiduesZ lo) (hhi : AffineOnResiduesZ hi) (hU : AffineOnResidues U) :
    AffineOnResidues (fun n => ((Finset.range (U n)).filter
      (fun j : ℕ => lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n)).card) := by
  have heq : (fun n => ((Finset.range (U n)).filter
        (fun j : ℕ => lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n)).card)
      = (fun n => (min ((U n : ℤ)) (hi n) - max 0 (lo n)).toNat) := by
    funext n; exact card_range_filter_Ico (U n) (lo n) (hi n)
  rw [heq]
  exact (((AffineOnResiduesZ.of_natCast hU).min hhi).sub
    ((AffineOnResiduesZ.const 0).max hlo)).toNat

/-- An `AffineOnResidues` sequence bounded by `1` has zero per-class slope, hence is
purely periodic beyond its threshold. -/
theorem affineOnResidues_bddOne_periodic {I : ℕ → ℕ} (hI : AffineOnResidues I)
    (hbd : ∀ n, I n ≤ 1) : ∃ mI pI : ℕ, 1 ≤ pI ∧ ∀ n, mI ≤ n → I (n + pI) = I n := by
  obtain ⟨mI, pI, sI, hpI, hIrec⟩ := hI
  refine ⟨mI, pI, hpI, fun n hn => ?_⟩
  obtain ⟨k, r, hr, hn'⟩ : ∃ k r, r < pI ∧ n = mI + r + pI * k :=
    ⟨(n - mI) / pI, (n - mI) % pI, Nat.mod_lt _ hpI, by
      have := Nat.div_add_mod (n - mI) pI; omega⟩
  have hs0 : sI r = 0 := by
    by_contra h
    have h2 := hIrec r 2
    have := hbd (mI + r + pI * 2)
    omega
  rw [hn', show mI + r + pI * k + pI = mI + r + pI * (k + 1) from by ring,
    hIrec r (k + 1), hIrec r k, hs0]
  ring

/-- The product of an `AffineOnResidues` sequence with a `{0,1}`-valued
`AffineOnResidues` indicator is `AffineOnResidues`. -/
theorem affineOnResidues_mul_bddOne {U I : ℕ → ℕ} (hU : AffineOnResidues U)
    (hI : AffineOnResidues I) (hbd : ∀ n, I n ≤ 1) :
    AffineOnResidues (fun n => U n * I n) := by
  obtain ⟨mU, pU, sU, hpU, hUrec⟩ := hU
  obtain ⟨mI, pI, hpI, hIper⟩ := affineOnResidues_bddOne_periodic hI hbd
  refine affineOnResidues_of_period (m := max mU mI) (p := pU * pI)
    (fun r => pI * sU (max mU mI + r - mU) * I (max mU mI + r)) (Nat.mul_pos hpU hpI) ?_
  intro r _ k
  set M := max mU mI with hMdef
  have hIeq : I (M + r + pU * pI * k) = I (M + r) := by
    have hgen : ∀ t, I (M + r + pI * t) = I (M + r) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
          rw [show M + r + pI * (t + 1) = (M + r + pI * t) + pI from by ring,
            hIper _ (by omega), ih]
    rw [show M + r + pU * pI * k = M + r + pI * (pU * k) from by ring]
    exact hgen (pU * k)
  have hUeq : U (M + r + pU * pI * k) = U (M + r) + k * (pI * sU (M + r - mU)) := by
    have hb : M + r = mU + (M + r - mU) := by omega
    rw [show M + r + pU * pI * k = mU + (M + r - mU) + pU * (pI * k) from by rw [← hb]; ring,
      hUrec (M + r - mU) (pI * k), ← hb]; ring
  show U (M + r + pU * pI * k) * I (M + r + pU * pI * k) =
      U (M + r) * I (M + r) + k * (pI * sU (M + r - mU) * I (M + r))
  rw [hIeq, hUeq]; ring

/-- **`countBelowAffineThreshold`.**  For any fixed `α : ℤ`, the count of
`j ∈ [0, U n)` with `α·j < T n` is affine on residue classes of `n`, whenever `U` is
`AffineOnResidues` and `T` is `AffineOnResiduesZ`.  This is the per-coordinate kernel
of the `fas` lex count; `α` is a rank slope (any sign, incl. `0`), `T` the threshold. -/
theorem countLtThreshold (α : ℤ) {T : ℕ → ℤ} {U : ℕ → ℕ}
    (hT : AffineOnResiduesZ T) (hU : AffineOnResidues U) :
    AffineOnResidues (fun n => ((Finset.range (U n)).filter
      (fun j : ℕ => α * (j : ℤ) < T n)).card) := by
  rcases lt_trichotomy α 0 with hneg | hzero | hpos
  · -- α < 0 : the solution set is a half-line `j ≥ lo` intersected with `[0, U n)`.
    set β : ℤ := -α with hβ
    have hβpos : 0 < β := by omega
    have hαβ : α = -β := by omega
    have hiff : ∀ n, ∀ j ∈ Finset.range (U n),
        (α * (j : ℤ) < T n) ↔ ((-(T n)) / β + 1 ≤ (j : ℤ) ∧ (j : ℤ) < (U n : ℤ)) := by
      intro n j hj
      rw [Finset.mem_range] at hj
      have hjU : (j : ℤ) < (U n : ℤ) := by exact_mod_cast hj
      constructor
      · intro h
        refine ⟨?_, hjU⟩
        rw [hαβ, neg_mul] at h
        have h2 : (-(T n)) / β < (j : ℤ) := by rw [Int.ediv_lt_iff_lt_mul hβpos]; nlinarith [h]
        omega
      · rintro ⟨h, _⟩
        have h2 : (-(T n)) / β < (j : ℤ) := by omega
        rw [Int.ediv_lt_iff_lt_mul hβpos] at h2
        rw [hαβ, neg_mul]; nlinarith [h2]
    have heq : (fun n => ((Finset.range (U n)).filter (fun j : ℕ => α * (j : ℤ) < T n)).card)
        = (fun n => ((Finset.range (U n)).filter
            (fun j : ℕ => (-(T n)) / β + 1 ≤ (j : ℤ) ∧ (j : ℤ) < (U n : ℤ))).card) := by
      funext n; rw [Finset.filter_congr (hiff n)]
    rw [heq]
    exact countInterval (((hT.neg).ediv_pos β hβpos).add (AffineOnResiduesZ.const 1))
      (AffineOnResiduesZ.of_natCast hU) hU
  · -- α = 0 : the predicate `0 < T n` is independent of `j`; count = U n · [0 < T n].
    subst hzero
    have heq : (fun n => ((Finset.range (U n)).filter (fun j : ℕ => (0 : ℤ) * (j : ℤ) < T n)).card)
        = (fun n => U n * (min 1 (T n)).toNat) := by
      funext n
      by_cases h : 0 < T n
      · rw [Finset.filter_true_of_mem (fun j _ => by simpa using h), Finset.card_range,
          show (min 1 (T n)).toNat = 1 from by omega, Nat.mul_one]
      · rw [Finset.filter_false_of_mem (fun j _ => by simpa using h), Finset.card_empty,
          show (min 1 (T n)).toNat = 0 from by omega, Nat.mul_zero]
    rw [heq]
    exact affineOnResidues_mul_bddOne hU (((AffineOnResiduesZ.const 1).min hT).toNat)
      (fun n => by omega)
  · -- α > 0 : the solution set is `j < c` intersected with `[0, U n)`.
    have hiff : ∀ n, ∀ j ∈ Finset.range (U n),
        (α * (j : ℤ) < T n) ↔ ((0 : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) < (T n - 1) / α + 1) := by
      intro n j _
      constructor
      · intro h
        refine ⟨Int.natCast_nonneg j, ?_⟩
        have h2 : (j : ℤ) ≤ (T n - 1) / α := by rw [Int.le_ediv_iff_mul_le hpos, mul_comm]; omega
        omega
      · rintro ⟨_, h⟩
        have h2 : (j : ℤ) ≤ (T n - 1) / α := by omega
        rw [Int.le_ediv_iff_mul_le hpos, mul_comm] at h2
        omega
    have heq : (fun n => ((Finset.range (U n)).filter (fun j : ℕ => α * (j : ℤ) < T n)).card)
        = (fun n => ((Finset.range (U n)).filter
            (fun j : ℕ => (0 : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) < (T n - 1) / α + 1)).card) := by
      funext n; rw [Finset.filter_congr (hiff n)]
    rw [heq]
    exact countInterval (AffineOnResiduesZ.const 0)
      (((hT.sub (AffineOnResiduesZ.const 1)).ediv_pos α hpos).add (AffineOnResiduesZ.const 1)) hU

end SliceThreshold
