/-
# The pinned counting kernels (§9 tower, Stage F3.1)

A genuine re-proof of the gated convolution kernels (`SliceGatedConv`) at
PINNED periods: the wrapped kernels return opaque existential periods; the
fibred chain needs the period to be an explicit function of the machine data,
fixed before the boundary width.  Spike S3's resolution: the residue-count's
period is exactly `P · m` because ediv-by-`m` of a `P`-pinned family is
`P·m`-pinned with the SAME slope (`(b + m·k·s)/m = b/m + k·s`, exact).

Layer 1 (this part): the pinned-arithmetic sublayer — `id_cast`, `neg`,
`min_at`/`max_at` (rebase past the finitely many class crossings), `toNat_at`
(rebase past the sign kinks), `ediv_nat` (period `P ↦ P·m`, slope preserved),
`congr_eventually`, `le_EP_at`, `mul_indicator_at` — then `countInterval_at`
(closed form `(min(hi,U) − max(lo,0))⁺`), `countIntervalResidue_at` (the
`j = a + m·t` bijection, transplanted verbatim), and the first kernel
`gatedConvolution_at` at period `P · (pu · pv)`.
-/
import RequestProject.CopiedAffineAt
import RequestProject.SliceLexCount
import RequestProject.SliceFasCount

namespace CopiedAffineAt.AffineOnResiduesAtZ

open SliceOrder SlicePeriodStar CopiedAffineAt

/-- The identity cast is pinned at every period (slope = the period). -/
theorem id_cast (P : ℕ) : AffineOnResiduesAtZ P (fun n => (n : ℤ)) :=
  ⟨0, fun j _ => ⟨(j : ℤ), (P : ℤ), fun k => by push_cast; ring⟩⟩

theorem neg {P : ℕ} {F : ℕ → ℤ} (h : AffineOnResiduesAtZ P F) :
    AffineOnResiduesAtZ P (fun n => -F n) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun j hj => ?_⟩
  obtain ⟨b, s, hbs⟩ := hm j hj
  refine ⟨-b, -s, fun k => ?_⟩
  show -F (m + j + P * k) = _
  rw [hbs k]
  ring

/-- Eventual agreement transfers pinned affineness (threshold absorbed). -/
theorem congr_eventually {P : ℕ} (hP : 1 ≤ P) {F G : ℕ → ℤ} (N : ℕ)
    (h : ∀ n, N ≤ n → F n = G n) (hF : AffineOnResiduesAtZ P F) :
    AffineOnResiduesAtZ P G := by
  obtain ⟨m, hm⟩ := hF.exists_rebase hP
  refine ⟨max m N, fun j hj => ?_⟩
  obtain ⟨b, s, hbs⟩ := hm (max m N) (le_max_left _ _) j hj
  refine ⟨b, s, fun k => ?_⟩
  rw [← h _ (le_trans (le_max_right m N)
    (le_trans (Nat.le_add_right _ j) (Nat.le_add_right _ _)))]
  exact hbs k

/-- Exact class data at the base shifted by `P · K` (same slopes, intercepts
shifted by `K` steps) — the rebase-past-kinks workhorse. -/
theorem class_shift {P : ℕ} {F : ℕ → ℤ} {m : ℕ} {b s : ℤ} {j : ℕ}
    (hbs : ∀ k : ℕ, F (m + j + P * k) = b + (k : ℤ) * s) (K : ℕ) :
    ∀ k : ℕ, F (m + P * K + j + P * k) = (b + (K : ℤ) * s) + (k : ℤ) * s := by
  intro k
  have harg : m + P * K + j + P * k = m + j + P * (K + k) := by
    have h1 : P * (K + k) = P * K + P * k := Nat.mul_add P K k
    generalize hA1 : P * K = A1 at h1 ⊢
    generalize hA2 : P * k = A2 at h1 ⊢
    generalize hA3 : P * (K + k) = A3 at h1 ⊢
    omega
  rw [harg, hbs (K + k)]
  push_cast
  ring

/-- **Pinned minimum**: rebase past the finitely many class crossings; per
class the winner is then fixed and exactly affine. -/
theorem min_at {P : ℕ} (hP : 1 ≤ P) {F G : ℕ → ℤ}
    (hF : AffineOnResiduesAtZ P F) (hG : AffineOnResiduesAtZ P G) :
    AffineOnResiduesAtZ P (fun n => min (F n) (G n)) := by
  classical
  obtain ⟨mF, hmF⟩ := hF.exists_rebase hP
  obtain ⟨mG, hmG⟩ := hG.exists_rebase hP
  choose bF sF hbsF using fun (j : Fin P) =>
    hmF (max mF mG) (le_max_left _ _) j.val j.isLt
  choose bG sG hbsG using fun (j : Fin P) =>
    hmG (max mF mG) (le_max_right _ _) j.val j.isLt
  set K : ℕ := Finset.univ.sup (fun j : Fin P => (bF j - bG j).natAbs + 1)
    with hK
  refine ⟨max mF mG + P * K, fun j hj => ?_⟩
  set jf : Fin P := ⟨j, hj⟩ with hjf
  have hKj : (bF jf - bG jf).natAbs + 1 ≤ K :=
    Finset.le_sup (f := fun j => (bF j - bG j).natAbs + 1) (Finset.mem_univ jf)
  have hF' := class_shift (hbsF jf) K
  have hG' := class_shift (hbsG jf) K
  have hKZ : ((bF jf - bG jf).natAbs : ℤ) + 1 ≤ (K : ℤ) := by exact_mod_cast hKj
  have habs1 : bF jf - bG jf ≤ ((bF jf - bG jf).natAbs : ℤ) := Int.le_natAbs
  have habs2 : bG jf - bF jf ≤ ((bF jf - bG jf).natAbs : ℤ) := by
    rw [← Int.natAbs_neg, neg_sub]
    exact Int.le_natAbs
  rcases lt_trichotomy (sF jf) (sG jf) with hs | hs | hs
  · -- F wins past the crossing
    refine ⟨bF jf + (K : ℤ) * sF jf, sF jf, fun k => ?_⟩
    show min (F _) (G _) = _
    rw [hF' k, hG' k, min_eq_left ?_]
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    have hs1 : sF jf + 1 ≤ sG jf := hs
    nlinarith [hKZ, habs1, habs2, hk0, hs1]
  · -- equal slopes: min distributes
    refine ⟨min (bF jf + (K : ℤ) * sF jf) (bG jf + (K : ℤ) * sG jf), sF jf,
      fun k => ?_⟩
    show min (F _) (G _) = _
    rw [hF' k, hG' k, ← hs, min_add_add_right]
  · -- G wins past the crossing
    refine ⟨bG jf + (K : ℤ) * sG jf, sG jf, fun k => ?_⟩
    show min (F _) (G _) = _
    rw [hF' k, hG' k, min_eq_right ?_]
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    have hs1 : sG jf + 1 ≤ sF jf := hs
    nlinarith [hKZ, habs1, habs2, hk0, hs1]

/-- **Pinned maximum**, via `min` and negation. -/
theorem max_at {P : ℕ} (hP : 1 ≤ P) {F G : ℕ → ℤ}
    (hF : AffineOnResiduesAtZ P F) (hG : AffineOnResiduesAtZ P G) :
    AffineOnResiduesAtZ P (fun n => max (F n) (G n)) := by
  refine (((min_at hP hF.neg hG.neg).neg).congr' (fun n => ?_))
  show -(min (-F n) (-G n)) = max (F n) (G n)
  rw [min_neg_neg, neg_neg]

/-- **Pinned `toNat`**: rebase past the sign kinks; per class the value is
then exactly `0` or exactly affine with nonnegative data. -/
theorem toNat_at {P : ℕ} (_hP : 1 ≤ P) {F : ℕ → ℤ}
    (h : AffineOnResiduesAtZ P F) :
    SlicePeriodStar.AffineOnResiduesAt P (fun n => (F n).toNat) := by
  classical
  obtain ⟨m, hm⟩ := h
  choose b s hbs using fun (j : Fin P) => hm j.val j.isLt
  set K : ℕ := Finset.univ.sup (fun j : Fin P => (b j).natAbs + 1) with hK
  refine ⟨m + P * K, fun j hj => ?_⟩
  set jf : Fin P := ⟨j, hj⟩ with hjf
  have hKj : (b jf).natAbs + 1 ≤ K :=
    Finset.le_sup (f := fun j => (b j).natAbs + 1) (Finset.mem_univ jf)
  have hF' := class_shift (hbs jf) K
  have hKZ : ((b jf).natAbs : ℤ) + 1 ≤ (K : ℤ) := by exact_mod_cast hKj
  have habs1 : b jf ≤ ((b jf).natAbs : ℤ) := Int.le_natAbs
  have habs2 : -(b jf) ≤ ((b jf).natAbs : ℤ) := by
    rw [← Int.natAbs_neg]
    exact Int.le_natAbs
  rcases lt_trichotomy (s jf) 0 with hs | hs | hs
  · -- negative slope: identically zero past the kink
    refine ⟨0, 0, fun k => ?_⟩
    show (F _).toNat = 0 + k * 0
    rw [hF' k]
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    have hs1 : s jf ≤ -1 := by omega
    have hneg : (b jf + (K : ℤ) * s jf) + (k : ℤ) * s jf < 0 := by
      nlinarith [hKZ, habs1, habs2, hk0, hs1]
    rw [Int.toNat_of_nonpos (le_of_lt hneg)]
    omega
  · -- zero slope: constant
    refine ⟨(b jf).toNat, 0, fun k => ?_⟩
    have hv : F (m + P * K + j + P * k) = b jf := by
      rw [hF' k, hs]
      ring
    show (F _).toNat = (b jf).toNat + k * 0
    rw [hv]
    omega
  · -- positive slope: exactly affine, nonnegative past the kink
    have hs1 : 1 ≤ s jf := hs
    have h0 : 0 ≤ b jf + (K : ℤ) * s jf := by
      nlinarith [hKZ, habs1, habs2, hs1]
    obtain ⟨sn, hsn⟩ : ∃ sn : ℕ, s jf = (sn : ℤ) :=
      ⟨(s jf).toNat, (Int.toNat_of_nonneg (le_of_lt hs)).symm⟩
    obtain ⟨bn, hbn⟩ : ∃ bn : ℕ, b jf + (K : ℤ) * s jf = (bn : ℤ) :=
      ⟨(b jf + (K : ℤ) * s jf).toNat, (Int.toNat_of_nonneg h0).symm⟩
    refine ⟨bn, sn, fun k => ?_⟩
    show (F _).toNat = bn + k * sn
    rw [hF' k, hbn, hsn,
      show ((bn : ℤ) + (k : ℤ) * (sn : ℤ)) = ((bn + k * sn : ℕ) : ℤ) from by
        push_cast; ring,
      Int.toNat_natCast]

/-- **Pinned ediv by a constant `m`** (the spike-S3 fact): period `P ↦ P·m`,
SAME slope — `(b + m·k·s)/m = b/m + k·s` exactly. -/
theorem ediv_nat {P : ℕ} (hP : 1 ≤ P) (m : ℕ) (hm : 1 ≤ m) {F : ℕ → ℤ}
    (hF : AffineOnResiduesAtZ P F) :
    AffineOnResiduesAtZ (P * m) (fun n => F n / (m : ℤ)) := by
  obtain ⟨mb, hmb⟩ := hF
  refine ⟨mb, fun j hj => ?_⟩
  obtain ⟨b, s, hbs⟩ := hmb (j % P) (Nat.mod_lt _ (by omega))
  refine ⟨(b + ((j / P : ℕ) : ℤ) * s) / (m : ℤ), s, fun k => ?_⟩
  have harg : mb + j + P * m * k = mb + j % P + P * (j / P + m * k) := by
    have hdm : P * (j / P) + j % P = j := Nat.div_add_mod j P
    have hsplit : P * (j / P + m * k) = P * (j / P) + P * (m * k) :=
      Nat.mul_add P _ _
    have hassoc : P * m * k = P * (m * k) := Nat.mul_assoc P m k
    generalize hA1 : P * (j / P) = A1 at hdm hsplit
    generalize hA2 : P * (m * k) = A2 at hsplit hassoc
    generalize hA3 : P * (j / P + m * k) = A3 at hsplit ⊢
    generalize hA0 : P * m * k = A0 at hassoc ⊢
    omega
  show F (mb + j + P * m * k) / (m : ℤ) = _
  rw [harg, hbs (j / P + m * k)]
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [show (b + ((j / P + m * k : ℕ) : ℤ) * s)
      = (b + ((j / P : ℕ) : ℤ) * s) + (m : ℤ) * ((k : ℤ) * s) from by
        push_cast; ring,
    Int.add_mul_ediv_left _ ((k : ℤ) * s) hm0]

end CopiedAffineAt.AffineOnResiduesAtZ

namespace SlicePeriodStar.AffineOnResiduesAt

/-- Eventual agreement transfers pinned affineness (ℕ side). -/
theorem congr_eventually {p : ℕ} (hp : 1 ≤ p) {f g : ℕ → ℕ} (N : ℕ)
    (h : ∀ n, N ≤ n → f n = g n) (hf : AffineOnResiduesAt p f) :
    AffineOnResiduesAt p g := by
  obtain ⟨m, hm⟩ := hf.exists_rebase hp
  refine ⟨max m N, fun j hj => ?_⟩
  obtain ⟨b, s, hbs⟩ := hm (max m N) (le_max_left _ _) j hj
  refine ⟨b, s, fun k => ?_⟩
  rw [← h _ (le_trans (le_max_right m N)
    (le_trans (Nat.le_add_right _ j) (Nat.le_add_right _ _)))]
  exact hbs k

end SlicePeriodStar.AffineOnResiduesAt

namespace CopiedKernels

open SliceOrder SlicePeriodStar CopiedAffineAt CopiedAffineAt.AffineOnResiduesAtZ
open scoped Classical

/-- Pinned `≤`-comparison is eventually periodic at the shared period. -/
theorem le_EP_at {P : ℕ} (hP : 1 ≤ P) {F G : ℕ → ℤ}
    (hF : AffineOnResiduesAtZ P F) (hG : AffineOnResiduesAtZ P G) :
    SliceOrder.EventuallyPeriodic (fun n => F n ≤ G n) P := by
  obtain ⟨M, hM⟩ := SliceDstarCore.EP_not (lt_EP_at hP hG hF)
  exact ⟨M, fun n hn => by
    have h2 := hM n hn
    simp only [] at h2
    rw [not_lt, not_lt] at h2
    exact h2⟩

/-- Multiplying a pinned count by an eventually-periodic `{0,1}` gate keeps
the pinned period (the gate is constant along every class tail). -/
theorem mul_indicator_at {p : ℕ} (hp : 1 ≤ p) {f : ℕ → ℕ}
    (hf : SlicePeriodStar.AffineOnResiduesAt p f) {Bit : ℕ → Prop}
    [DecidablePred Bit] (hEP : SliceOrder.EventuallyPeriodic Bit p) :
    SlicePeriodStar.AffineOnResiduesAt p
      (fun n => f n * (if Bit n then 1 else 0)) := by
  obtain ⟨M, hM⟩ := EP_class_const hEP
  obtain ⟨mf, hmf⟩ := hf.exists_rebase hp
  refine ⟨max mf M, fun j hj => ?_⟩
  obtain ⟨b, s, hbs⟩ := hmf _ (le_max_left _ _) j hj
  have hMle : M ≤ max mf M + j :=
    le_trans (le_max_right _ _) (Nat.le_add_right _ j)
  by_cases hbit : Bit (max mf M + j)
  · refine ⟨b, s, fun k => ?_⟩
    have hb := (hM (max mf M + j) hMle k).mpr hbit
    show f (max mf M + j + p * k)
        * (if Bit (max mf M + j + p * k) then 1 else 0) = b + k * s
    rw [if_pos hb, Nat.mul_one, hbs k]
  · refine ⟨0, 0, fun k => ?_⟩
    show f (max mf M + j + p * k)
        * (if Bit (max mf M + j + p * k) then 1 else 0) = 0 + k * 0
    rw [if_neg (fun hc => hbit ((hM (max mf M + j) hMle k).mp hc)),
      Nat.mul_zero]
    omega

/-- **The pinned interval count**: counting `t ∈ [0, U n)` with
`lo n ≤ t < hi n` is pinned at the endpoints' period (closed form
`(min(hi, U) − max(lo, 0))⁺`). -/
theorem countInterval_at {P : ℕ} (hP : 1 ≤ P) {lo hi : ℕ → ℤ}
    (hlo : AffineOnResiduesAtZ P lo) (hhi : AffineOnResiduesAtZ P hi)
    {U : ℕ → ℕ} (hU : SlicePeriodStar.AffineOnResiduesAt P U) :
    SlicePeriodStar.AffineOnResiduesAt P (fun n => ((Finset.range (U n)).filter
      (fun t : ℕ => lo n ≤ (t : ℤ) ∧ (t : ℤ) < hi n)).card) := by
  have hcard : ∀ n, ((Finset.range (U n)).filter
      (fun t : ℕ => lo n ≤ (t : ℤ) ∧ (t : ℤ) < hi n)).card
      = (min (hi n) ((U n : ℕ) : ℤ) - max (lo n) 0).toNat := by
    intro n
    have hset : (Finset.range (U n)).filter
        (fun t : ℕ => lo n ≤ (t : ℤ) ∧ (t : ℤ) < hi n)
        = Finset.Ico ((max (lo n) 0).toNat)
            ((min (hi n) ((U n : ℕ) : ℤ)).toNat) := by
      ext t
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨htU, htlo, hthi⟩
        omega
      · rintro ⟨h1, h2⟩
        omega
    rw [hset, Nat.card_Ico]
    omega
  refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => (hcard n).symm) ?_
  exact ((min_at hP hhi (natCast hU)).sub hP
    (max_at hP hlo (const P 0))).toNat_at hP

/-- **The pinned residue-interval count** (spike S3): counting
`j ∈ [0, N n)` with `j ≡ a [mod m]` and `lo n ≤ j < hi n` is pinned at
`P · m` — the `j = a + m·t` bijection back to `countInterval_at` on the
ediv-shifted endpoints. -/
theorem countIntervalResidue_at (a m : ℕ) (ha : a < m) {P : ℕ} (hP : 1 ≤ P)
    {lo hi : ℕ → ℤ} (hlo : AffineOnResiduesAtZ P lo)
    (hhi : AffineOnResiduesAtZ P hi)
    {N : ℕ → ℕ} (hN : SlicePeriodStar.AffineOnResiduesAt P N) :
    SlicePeriodStar.AffineOnResiduesAt (P * m)
      (fun n => ((Finset.range (N n)).filter
        (fun j : ℕ => j % m = a ∧ lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n)).card) := by
  have hm : 1 ≤ m := by omega
  have hPm : 1 ≤ P * m := Nat.mul_pos hP hm
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hmne : (m : ℤ) ≠ 0 := ne_of_gt hmZ
  -- the shifted endpoints, pinned at P·m
  set U' : ℕ → ℕ := fun n => ((((N n : ℕ) : ℤ) - a + m - 1) / m).toNat with hU'
  set lo' : ℕ → ℤ := fun n => (lo n - a + m - 1) / (m : ℤ) with hlo'def
  set hi' : ℕ → ℤ := fun n => (hi n - a - 1) / (m : ℤ) + 1 with hhi'def
  have hU'aff : SlicePeriodStar.AffineOnResiduesAt (P * m) U' :=
    (ediv_nat hP m hm ((((natCast hN).sub hP (const P (a : ℤ))).add hP
      (const P (m : ℤ))).sub hP (const P 1))).toNat_at hPm
  have hlo'aff : AffineOnResiduesAtZ (P * m) lo' :=
    ediv_nat hP m hm (((hlo.sub hP (const P (a : ℤ))).add hP
      (const P (m : ℤ))).sub hP (const P 1))
  have hhi'aff : AffineOnResiduesAtZ (P * m) hi' :=
    (ediv_nat hP m hm ((hhi.sub hP (const P (a : ℤ))).sub hP
      (const P 1))).add hPm (const (P * m) 1)
  refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_)
    (countInterval_at hPm hlo'aff hhi'aff hU'aff)
  -- pointwise: the j = a + m·t bijection (verbatim wrapped transplant)
  have hbound : ∀ t : ℕ, t < U' n ↔ a + m * t < N n := by
    intro t
    rw [hU', Int.lt_toNat]
    constructor
    · intro h
      have h2 : ((t : ℤ) + 1) * (m : ℤ) ≤ ((N n : ℕ) : ℤ) - (a : ℤ) + (m : ℤ) - 1 :=
        (Int.le_ediv_iff_mul_le hmZ).mp (by omega)
      have h3 : ((a + m * t : ℕ) : ℤ) < ((N n : ℕ) : ℤ) := by
        push_cast at h2 ⊢
        nlinarith [h2]
      exact_mod_cast h3
    · intro h
      have h3 : ((a + m * t : ℕ) : ℤ) < ((N n : ℕ) : ℤ) := by exact_mod_cast h
      have h2 : ((t : ℤ) + 1) * (m : ℤ) ≤ ((N n : ℕ) : ℤ) - (a : ℤ) + (m : ℤ) - 1 := by
        push_cast at h3 ⊢
        nlinarith [h3]
      exact (Int.le_ediv_iff_mul_le hmZ).mpr h2
  have hlobound : ∀ t : ℕ, lo' n ≤ (t : ℤ) ↔ lo n ≤ ((a + m * t : ℕ) : ℤ) := by
    intro t
    rw [hlo'def]
    show (lo n - a + m - 1) / (m : ℤ) ≤ (t : ℤ) ↔ _
    rw [← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hmZ]
    push_cast
    constructor <;> intro h <;> nlinarith [h]
  have hhibound : ∀ t : ℕ, (t : ℤ) < hi' n ↔ ((a + m * t : ℕ) : ℤ) < hi n := by
    intro t
    rw [hhi'def]
    show (t : ℤ) < (hi n - a - 1) / (m : ℤ) + 1 ↔ _
    rw [Int.lt_add_one_iff, Int.le_ediv_iff_mul_le hmZ]
    push_cast
    constructor <;> intro h <;> nlinarith [h]
  refine Finset.card_bij (fun t _ => a + m * t) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter, Finset.mem_range] at ht ⊢
    refine ⟨(hbound t).mp ht.1, ?_, ?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    · exact (hlobound t).mp ht.2.1
    · exact (hhibound t).mp ht.2.2
  · intro t1 _ t2 _ h
    exact Nat.eq_of_mul_eq_mul_left hm (Nat.add_left_cancel h)
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjN, hjmod, hjlo, hjhi⟩ := hj
    have hjeq : a + m * (j / m) = j := by
      have := Nat.div_add_mod j m
      omega
    refine ⟨j / m, ?_, hjeq⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨(hbound (j / m)).mpr (by rw [hjeq]; exact hjN),
      (hlobound (j / m)).mpr (by rw [hjeq]; exact hjlo),
      (hhibound (j / m)).mpr (by rw [hjeq]; exact hjhi)⟩

/-- **The pinned gated convolution kernel** (FIBRED_PORTMAP F3.1): for
eventually-periodic iterates `u`, `v` and ANY bit `b`, the count of
loop-indices `j < n` in a pinned affine interval whose convolution bit is on
is pinned at `P · (pu · pv)`.  `u`, `v`, `b` are abstract: per-`mS`-sized
conjunctions ride inside `b` at zero period cost. -/
theorem gatedConvolution_at {α β : Type*}
    (u : ℕ → α) (v : ℕ → β) (b : α → β → Prop)
    {mu pu : ℕ} (hpu : 1 ≤ pu) (hu : ∀ i, mu ≤ i → u (i + pu) = u i)
    {mv pv : ℕ} (hpv : 1 ≤ pv) (hv : ∀ j, mv ≤ j → v (j + pv) = v j)
    {P : ℕ} (hP : 1 ≤ P) (hdvd : pu * pv ∣ P)
    {lo hi : ℕ → ℤ} (hlo : AffineOnResiduesAtZ P lo)
    (hhi : AffineOnResiduesAtZ P hi) :
    SlicePeriodStar.AffineOnResiduesAt (P * (pu * pv))
      (fun n => ((Finset.range n).filter
        (fun j : ℕ => lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n
          ∧ b (u j) (v (n - 1 - j)))).card) := by
  classical
  have _hdvd_input : pu * pv ∣ P := hdvd
  set p := pu * pv with hpdef
  have hp : 1 ≤ p := Nat.mul_pos hpu hpv
  have hPtgt : 1 ≤ P * p := Nat.mul_pos hP hp
  have hdvd_p : p ∣ P * p := dvd_mul_left p P
  have hdvd_pu : pu ∣ P * p :=
    dvd_trans (Dvd.intro pv rfl) hdvd_p
  have hdvd_pv : pv ∣ P * p :=
    dvd_trans (Dvd.intro_left pu rfl) hdvd_p
  have hdvd_P : P ∣ P * p := dvd_mul_right P p
  -- periodicity helpers (verbatim transplant)
  have hu_iter : ∀ s t, mu ≤ s → u (s + pu * t) = u s := by
    intro s t hs
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hu _ (by omega), ih]
  have hv_iter : ∀ s t, mv ≤ s → v (s + pv * t) = v s := by
    intro s t hs
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hv _ (by omega), ih]
  have hu_p : ∀ s t, mu ≤ s → u (s + p * t) = u s := by
    intro s t hs
    rw [hpdef, show pu * pv * t = pu * (pv * t) from by ring]
    exact hu_iter s (pv * t) hs
  have hv_p : ∀ s t, mv ≤ s → v (s + p * t) = v s := by
    intro s t hs
    rw [hpdef, show pu * pv * t = pv * (pu * t) from by ring]
    exact hv_iter s (pu * t) hs
  -- the target-period endpoints and the gate-bit helper
  have hloT : AffineOnResiduesAtZ (P * p) lo := hlo.of_dvd hP hdvd_P hPtgt
  have hhiT : AffineOnResiduesAtZ (P * p) hi := hhi.of_dvd hP hdvd_P hPtgt
  have gated : ∀ (C : ℕ → ℤ), AffineOnResiduesAtZ (P * p) C →
      ∀ (Bit : ℕ → Prop), SliceOrder.EventuallyPeriodic Bit (P * p) →
      SlicePeriodStar.AffineOnResiduesAt (P * p)
        (fun n => if lo n ≤ C n ∧ C n < hi n ∧ Bit n then 1 else 0) := by
    intro C hC Bit hBit
    exact affineOnResiduesAt_indicator_of_EP hPtgt
      ((le_EP_at hPtgt hloT hC).and ((lt_EP_at hPtgt hC hhiT).and hBit))
  -- forward boundary `j < mu`
  have hFB : SlicePeriodStar.AffineOnResiduesAt (P * p)
      (fun n => ∑ j ∈ Finset.range mu,
        (if lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n
          ∧ b (u j) (v (n - 1 - j)) then 1 else 0)) := by
    apply SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hPtgt
    intro j _
    refine gated (fun _ => (j : ℤ))
      (CopiedAffineAt.AffineOnResiduesAtZ.const _ (j : ℤ))
      (fun n => b (u j) (v (n - 1 - j))) ?_
    refine SliceDstar.EP_of_dvd ?_ hdvd_pv
    refine ⟨mv + j + 1, fun n hn => ?_⟩
    show b (u j) (v (n + pv - 1 - j)) ↔ b (u j) (v (n - 1 - j))
    rw [show n + pv - 1 - j = (n - 1 - j) + pv from by omega, hv _ (by omega)]
  -- backward boundary, reindexed `j = n - mv + i`
  have hBB : SlicePeriodStar.AffineOnResiduesAt (P * p)
      (fun n => ∑ i ∈ Finset.range mv,
        (if lo n ≤ ((n - mv + i : ℕ) : ℤ) ∧ ((n - mv + i : ℕ) : ℤ) < hi n
          ∧ b (u (n - mv + i)) (v (n - 1 - (n - mv + i))) then 1 else 0)) := by
    apply SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hPtgt
    intro i hi_mem
    rw [Finset.mem_range] at hi_mem
    refine SlicePeriodStar.AffineOnResiduesAt.congr_eventually hPtgt
      (mv + i + 1) (fun n hn => ?_)
      (gated (fun n => (n : ℤ) - mv + i)
        (((CopiedAffineAt.AffineOnResiduesAtZ.id_cast (P * p)).sub hPtgt
            (CopiedAffineAt.AffineOnResiduesAtZ.const _ (mv : ℤ))).add hPtgt
          (CopiedAffineAt.AffineOnResiduesAtZ.const _ (i : ℤ)))
        (fun n => b (u (n - mv + i)) (v (mv - 1 - i))) ?_)
    · have e1 : ((n - mv + i : ℕ) : ℤ) = (n : ℤ) - mv + i := by omega
      have e2 : v (n - 1 - (n - mv + i)) = v (mv - 1 - i) := by
        rw [show n - 1 - (n - mv + i) = mv - 1 - i from by omega]
      rw [e1, e2]
    · refine SliceDstar.EP_of_dvd ?_ hdvd_pu
      refine ⟨mu + mv + i + 1, fun n hn => ?_⟩
      show b (u (n + pu - mv + i)) (v (mv - 1 - i))
        ↔ b (u (n - mv + i)) (v (mv - 1 - i))
      rw [show n + pu - mv + i = (n - mv + i) + pu from by omega,
        hu _ (by omega)]
  -- bulk pieces
  set Cr : ℕ → ℕ → ℕ := fun r n => ((Finset.range (n - mu - mv)).filter
    (fun i : ℕ => i % p = r ∧ lo n ≤ ((mu + i : ℕ) : ℤ)
      ∧ ((mu + i : ℕ) : ℤ) < hi n)).card with hCrdef
  set Ibeta : ℕ → ℕ → ℕ := fun r n =>
    if b (u (mu + r)) (v (mv + (n - mu - mv - 1 - r))) then 1 else 0
    with hIbetadef
  have hNaffP : SlicePeriodStar.AffineOnResiduesAt P (fun n => n - mu - mv) := by
    refine ⟨mu + mv, fun j hj => ⟨j, P, fun k => ?_⟩⟩
    show mu + mv + j + P * k - mu - mv = j + k * P
    rw [Nat.mul_comm P k]
    generalize k * P = A
    omega
  have hCr : ∀ r, r < p → SlicePeriodStar.AffineOnResiduesAt (P * p)
      (fun n => Cr r n) := by
    intro r hr
    have hlo2 : AffineOnResiduesAtZ P (fun n => lo n - (mu : ℤ)) :=
      (hlo.sub hP (CopiedAffineAt.AffineOnResiduesAtZ.const P (mu : ℤ))).congr'
        (fun n => rfl)
    have hhi2 : AffineOnResiduesAtZ P (fun n => hi n - (mu : ℤ)) :=
      (hhi.sub hP (CopiedAffineAt.AffineOnResiduesAtZ.const P (mu : ℤ))).congr'
        (fun n => rfl)
    have hbase := countIntervalResidue_at r p hr hP hlo2 hhi2 hNaffP
    refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_) hbase
    show ((Finset.range (n - mu - mv)).filter
        (fun i : ℕ => i % p = r ∧ lo n - (mu : ℤ) ≤ (i : ℤ)
          ∧ (i : ℤ) < hi n - (mu : ℤ))).card = Cr r n
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by push_cast at h2 ⊢; omega, by push_cast at h3 ⊢; omega⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by push_cast at h2 ⊢; omega, by push_cast at h3 ⊢; omega⟩
  have hBK : SlicePeriodStar.AffineOnResiduesAt (P * p)
      (fun n => ∑ r ∈ Finset.range p, Cr r n * Ibeta r n) := by
    apply SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hPtgt
    intro r hr_mem
    rw [Finset.mem_range] at hr_mem
    have hEPbit : SliceOrder.EventuallyPeriodic
        (fun n => b (u (mu + r)) (v (mv + (n - mu - mv - 1 - r)))) (P * p) := by
      refine SliceDstar.EP_of_dvd ?_ hdvd_p
      refine ⟨mu + mv + 1 + r, fun n hn => ?_⟩
      show b (u (mu + r)) (v (mv + (n + p - mu - mv - 1 - r)))
        ↔ b (u (mu + r)) (v (mv + (n - mu - mv - 1 - r)))
      rw [show mv + (n + p - mu - mv - 1 - r)
          = (mv + (n - mu - mv - 1 - r)) + p * 1 from by omega]
      rw [hv_p (mv + (n - mu - mv - 1 - r)) 1 (by omega)]
    exact mul_indicator_at hPtgt (hCr r hr_mem) hEPbit
  -- backward-boundary reindex identity (verbatim transplant)
  have eBB : ∀ n, mv ≤ n →
      (∑ j ∈ Finset.Ico (n - mv) n,
        (if lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n
          ∧ b (u j) (v (n - 1 - j)) then (1 : ℕ) else 0))
      = ∑ i ∈ Finset.range mv,
        (if lo n ≤ ((n - mv + i : ℕ) : ℤ) ∧ ((n - mv + i : ℕ) : ℤ) < hi n
          ∧ b (u (n - mv + i)) (v (n - 1 - (n - mv + i))) then 1 else 0) := by
    intro n _
    rw [Finset.sum_Ico_eq_sum_range, show n - (n - mv) = mv from by omega]
  -- bulk identity (verbatim transplant)
  have eBK : ∀ n, mu + mv ≤ n →
      (∑ j ∈ Finset.Ico mu (n - mv),
        (if lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n
          ∧ b (u j) (v (n - 1 - j)) then (1 : ℕ) else 0))
      = ∑ r ∈ Finset.range p, Cr r n * Ibeta r n := by
    intro n hn
    rw [Finset.sum_Ico_eq_sum_range, show n - mv - mu = n - mu - mv from by omega,
      ← Finset.sum_fiberwise_of_maps_to (t := Finset.range p) (g := fun i => i % p)
        (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hp))]
    apply Finset.sum_congr rfl
    intro r hr_mem
    rw [Finset.mem_range] at hr_mem
    have hconst : ∀ i ∈ (Finset.range (n - mu - mv)).filter (fun i => i % p = r),
        (b (u (mu + i)) (v (n - 1 - (mu + i)))
          ↔ b (u (mu + r)) (v (mv + (n - mu - mv - 1 - r)))) := by
      intro i hi_mem
      rw [Finset.mem_filter, Finset.mem_range] at hi_mem
      obtain ⟨hilt, himod⟩ := hi_mem
      have hu_eq : u (mu + i) = u (mu + r) := by
        have hidx : mu + i = (mu + r) + p * (i / p) := by
          have hdm : p * (i / p) + i % p = i := Nat.div_add_mod i p
          rw [himod] at hdm
          set pq := p * (i / p)
          omega
        rw [hidx]
        exact hu_p (mu + r) (i / p) (by omega)
      have hv_eq : v (n - 1 - (mu + i)) = v (mv + (n - mu - mv - 1 - r)) := by
        have hidx : mv + (n - mu - mv - 1 - r) = (n - 1 - (mu + i)) + p * (i / p) := by
          have hdm : p * (i / p) + i % p = i := Nat.div_add_mod i p
          rw [himod] at hdm
          set pq := p * (i / p)
          omega
        rw [hidx]
        exact (hv_p (n - 1 - (mu + i)) (i / p) (by omega)).symm
      rw [hu_eq, hv_eq]
    rw [Finset.sum_congr rfl (fun i hi => if_congr
      (and_congr_right (fun _ => and_congr_right (fun _ => hconst i hi))) rfl rfl)]
    have hpull : ∀ i, (if lo n ≤ ((mu + i : ℕ) : ℤ) ∧ ((mu + i : ℕ) : ℤ) < hi n
          ∧ b (u (mu + r)) (v (mv + (n - mu - mv - 1 - r))) then (1 : ℕ) else 0)
        = (if lo n ≤ ((mu + i : ℕ) : ℤ) ∧ ((mu + i : ℕ) : ℤ) < hi n then 1 else 0)
          * (if b (u (mu + r)) (v (mv + (n - mu - mv - 1 - r))) then 1 else 0) := by
      intro i
      rw [← SliceLexCount.ite_and_mul]
      exact if_congr and_assoc.symm rfl rfl
    rw [Finset.sum_congr rfl (fun i _ => hpull i), ← Finset.sum_mul]
    have hC_eq : (∑ i ∈ (Finset.range (n - mu - mv)).filter (fun i => i % p = r),
          (if lo n ≤ ((mu + i : ℕ) : ℤ) ∧ ((mu + i : ℕ) : ℤ) < hi n
            then (1 : ℕ) else 0))
        = Cr r n := by
      simp only [hCrdef]
      rw [Finset.card_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h1 : i % p = r
      · by_cases h2 : (lo n ≤ ((mu + i : ℕ) : ℤ) ∧ ((mu + i : ℕ) : ℤ) < hi n) <;>
          simp_all
      · simp [h1]
    rw [hC_eq]
  -- assemble
  refine SlicePeriodStar.AffineOnResiduesAt.congr_eventually hPtgt (mu + mv)
    (fun n hn => ?_) ((hFB.add hPtgt hBK).add hPtgt hBB)
  rw [Finset.card_filter,
    ← Finset.sum_range_add_sum_Ico _ (show mu ≤ n from by omega),
    ← Finset.sum_Ico_consecutive _ (show mu ≤ n - mv from by omega)
      (show n - mv ≤ n from by omega),
    eBK n hn, eBB n (by omega)]
  ring

/-! ## The lex layer (amendment D19: slope factors are explicit) -/

/-- The slope-magnitude product of a line list (`0`-slopes count as `1`). -/
def slopeProd (L : List (ℤ × ℤ)) : ℕ :=
  (L.map (fun bp => max bp.2.natAbs 1)).prod

theorem slopeProd_cons (bp : ℤ × ℤ) (L' : List (ℤ × ℤ)) :
    slopeProd (bp :: L') = max bp.2.natAbs 1 * slopeProd L' := by
  unfold slopeProd
  rw [List.map_cons, List.prod_cons]

/-- **Pinned signed ediv**: period `P ↦ P · |d|`, same slope. -/
theorem ediv_int {P : ℕ} (hP : 1 ≤ P) (dz : ℤ) (hd : dz ≠ 0) {F : ℕ → ℤ}
    (hF : AffineOnResiduesAtZ P F) :
    AffineOnResiduesAtZ (P * dz.natAbs) (fun n => F n / dz) := by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · -- dz < 0 : F / dz = -(F / (-dz))
    have hnat : dz.natAbs = (-dz).toNat := by omega
    have h1 := (ediv_nat hP (-dz).toNat (by omega) hF).neg
    rw [← hnat] at h1
    refine h1.congr' (fun n => ?_)
    show -(F n / ((dz.natAbs : ℕ) : ℤ)) = F n / dz
    have hcast : ((dz.natAbs : ℕ) : ℤ) = -dz := by omega
    rw [hcast, Int.ediv_neg, neg_neg]
  · -- dz > 0
    have hnat : dz.natAbs = dz.toNat := by omega
    have h1 := ediv_nat hP dz.toNat (by omega) hF
    rw [← hnat] at h1
    refine h1.congr' (fun n => ?_)
    show F n / ((dz.natAbs : ℕ) : ℤ) = F n / dz
    have hcast : ((dz.natAbs : ℕ) : ℤ) = dz := by omega
    rw [hcast]

/-- **Pinned divisibility bit**: `d ∣ F n` is eventually periodic at `P · |d|`
(along the refined classes the increment is divisible by `d`). -/
theorem dvd_EP_at {P : ℕ} (hP : 1 ≤ P) (dz : ℤ) (hd : dz ≠ 0) {F : ℕ → ℤ}
    (hF : AffineOnResiduesAtZ P F) :
    SliceOrder.EventuallyPeriodic (fun n => dz ∣ F n) (P * dz.natAbs) := by
  have hdn : 1 ≤ dz.natAbs := Int.natAbs_pos.mpr hd
  obtain ⟨m, hm⟩ := hF
  refine CopiedAffineAt.EP_of_classwise_eventually_const m (P * dz.natAbs)
    (Nat.mul_pos hP hdn) (fun j => ?_)
  obtain ⟨b, s, hbs⟩ := hm (j.val % P) (Nat.mod_lt _ (by omega))
  refine ⟨0, dz ∣ b + ((j.val / P : ℕ) : ℤ) * s, fun k _ => ?_⟩
  have harg : m + j.val + P * dz.natAbs * k
      = m + j.val % P + P * (j.val / P + dz.natAbs * k) := by
    have hdm : P * (j.val / P) + j.val % P = j.val := Nat.div_add_mod j.val P
    have hsplit : P * (j.val / P + dz.natAbs * k)
        = P * (j.val / P) + P * (dz.natAbs * k) := Nat.mul_add P _ _
    have hassoc : P * dz.natAbs * k = P * (dz.natAbs * k) :=
      Nat.mul_assoc P dz.natAbs k
    generalize hA1 : P * (j.val / P) = A1 at hdm hsplit
    generalize hA2 : P * (dz.natAbs * k) = A2 at hsplit hassoc
    generalize hA3 : P * (j.val / P + dz.natAbs * k) = A3 at hsplit ⊢
    generalize hA0 : P * dz.natAbs * k = A0 at hassoc ⊢
    omega
  show dz ∣ F (m + j.val + P * dz.natAbs * k) ↔ _
  rw [harg, hbs (j.val / P + dz.natAbs * k)]
  have hD : dz ∣ ((dz.natAbs : ℤ)) * ((k : ℤ) * s) :=
    Dvd.dvd.mul_right (Int.dvd_natAbs.mpr dvd_rfl) _
  have hsplit2 : b + ((j.val / P + dz.natAbs * k : ℕ) : ℤ) * s
      = (b + ((j.val / P : ℕ) : ℤ) * s) + (dz.natAbs : ℤ) * ((k : ℤ) * s) := by
    push_cast
    ring
  rw [hsplit2]
  constructor
  · intro h
    have := dvd_sub h hD
    simpa using this
  · intro h
    exact dvd_add h hD

/-- Pinned `lexLtL` comparison of two lists of pinned families is eventually
periodic at the shared period. -/
theorem lexLtL_EP_at {P : ℕ} (hP : 1 ≤ P) :
    ∀ (Fs Gs : List (ℕ → ℤ)), (∀ f ∈ Fs, AffineOnResiduesAtZ P f) →
    (∀ g ∈ Gs, AffineOnResiduesAtZ P g) →
    SliceOrder.EventuallyPeriodic (fun n =>
      SliceLexCount.lexLtL (Fs.map (fun f => f n)) (Gs.map (fun g => g n))) P := by
  intro Fs
  induction Fs with
  | nil =>
      intro Gs _ _
      exact ⟨0, fun n _ => by simp [SliceLexCount.lexLtL]⟩
  | cons f Fs' ih =>
      intro Gs hFs hGs
      cases Gs with
      | nil => exact ⟨0, fun n _ => by simp [SliceLexCount.lexLtL]⟩
      | cons g Gs' =>
          have hf := hFs f List.mem_cons_self
          have hg := hGs g List.mem_cons_self
          have hEP := (lt_EP_at hP hf hg).or ((eq_EP_at hP hf hg).and
            (ih Gs' (fun f' hf' => hFs f' (List.mem_cons_of_mem f hf'))
              (fun g' hg' => hGs g' (List.mem_cons_of_mem g hg'))))
          refine SliceOrder.EventuallyPeriodic.congr (fun n => ?_) hEP
          simp only [List.map_cons, SliceLexCount.lexLtL]

/-- Pinned ℕ-`<` comparison is eventually periodic at the shared period. -/
theorem nat_lt_EP_at {P : ℕ} (hP : 1 ≤ P) {f g : ℕ → ℕ}
    (hf : SlicePeriodStar.AffineOnResiduesAt P f)
    (hg : SlicePeriodStar.AffineOnResiduesAt P g) :
    SliceOrder.EventuallyPeriodic (fun n => f n < g n) P := by
  refine SliceOrder.EventuallyPeriodic.congr (fun n => ?_)
    (lt_EP_at hP (natCast hf) (natCast hg))
  exact Int.ofNat_lt

/-- **The pinned slope-threshold count**: counting `j < U n` with
`α·j < T n` is pinned at any multiple of `P · max |α| 1`. -/
theorem countLtThreshold_at (α : ℤ) {P : ℕ} (hP : 1 ≤ P) {T : ℕ → ℤ}
    {U : ℕ → ℕ} (hT : AffineOnResiduesAtZ P T)
    (hU : SlicePeriodStar.AffineOnResiduesAt P U)
    {Q : ℕ} (hQ : 1 ≤ Q) (hdvd : P * max α.natAbs 1 ∣ Q) :
    SlicePeriodStar.AffineOnResiduesAt Q (fun n => ((Finset.range (U n)).filter
      (fun j : ℕ => α * (j : ℤ) < T n)).card) := by
  classical
  have hPdvd : P ∣ Q := dvd_trans (Dvd.intro _ rfl) hdvd
  rcases lt_trichotomy α 0 with hneg | hzero | hpos
  · -- α < 0 : half-line `j ≥ lo` (verbatim wrapped identities)
    set β : ℤ := -α with hβ
    have hβpos : 0 < β := by omega
    have hαβ : α = -β := by omega
    have hanat : 1 ≤ α.natAbs := Int.natAbs_pos.mpr (by omega)
    have hPa : 1 ≤ P * α.natAbs := Nat.mul_pos hP hanat
    have hiff : ∀ n, ∀ j ∈ Finset.range (U n),
        (α * (j : ℤ) < T n)
          ↔ ((-(T n)) / β + 1 ≤ (j : ℤ) ∧ (j : ℤ) < ((U n : ℕ) : ℤ)) := by
      intro n j hj
      rw [Finset.mem_range] at hj
      have hjU : (j : ℤ) < ((U n : ℕ) : ℤ) := by exact_mod_cast hj
      constructor
      · intro h
        refine ⟨?_, hjU⟩
        rw [hαβ, neg_mul] at h
        have h2 : (-(T n)) / β < (j : ℤ) := by
          rw [Int.ediv_lt_iff_lt_mul hβpos]
          nlinarith [h]
        omega
      · rintro ⟨h, _⟩
        have h2 : (-(T n)) / β < (j : ℤ) := by omega
        rw [Int.ediv_lt_iff_lt_mul hβpos] at h2
        rw [hαβ, neg_mul]
        nlinarith [h2]
    have hβnat : β.natAbs = α.natAbs := by omega
    have hlo' : AffineOnResiduesAtZ (P * α.natAbs)
        (fun n => (-(T n)) / β + 1) := by
      have h1 := (ediv_int hP β (by omega) hT.neg).add
        (Nat.mul_pos hP (by omega)) (const _ 1)
      rw [hβnat] at h1
      exact h1
    have hUcast : AffineOnResiduesAtZ (P * α.natAbs)
        (fun n => ((U n : ℕ) : ℤ)) :=
      (natCast hU).of_dvd hP (Dvd.intro _ rfl) hPa
    have hUlift : SlicePeriodStar.AffineOnResiduesAt (P * α.natAbs) U :=
      hU.of_dvd hP (Dvd.intro _ rfl) hPa
    have hcnt := countInterval_at hPa hlo' hUcast hUlift
    have hshape : SlicePeriodStar.AffineOnResiduesAt (P * α.natAbs)
        (fun n => ((Finset.range (U n)).filter
          (fun j : ℕ => α * (j : ℤ) < T n)).card) := by
      refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_) hcnt
      show ((Finset.range (U n)).filter
          (fun j : ℕ => (-(T n)) / β + 1 ≤ (j : ℤ)
            ∧ (j : ℤ) < ((U n : ℕ) : ℤ))).card = _
      exact (congrArg Finset.card (Finset.filter_congr (hiff n))).symm
    refine hshape.of_dvd hPa ?_ hQ
    rwa [show max α.natAbs 1 = α.natAbs from by omega] at hdvd
  · -- α = 0 : count = U n · [0 < T n]
    subst hzero
    have hEPbit : SliceOrder.EventuallyPeriodic (fun n => (0 : ℤ) < T n) Q :=
      SliceDstar.EP_of_dvd (lt_EP_at hP (const P 0) hT) hPdvd
    have hUQ : SlicePeriodStar.AffineOnResiduesAt Q U := hU.of_dvd hP hPdvd hQ
    refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_)
      (mul_indicator_at hQ hUQ hEPbit)
    show U n * (if (0 : ℤ) < T n then 1 else 0) = _
    by_cases h : (0 : ℤ) < T n
    · rw [if_pos h, Nat.mul_one,
        Finset.filter_true_of_mem (fun j _ => by simpa using h),
        Finset.card_range]
    · rw [if_neg h, Nat.mul_zero,
        Finset.filter_false_of_mem (fun j _ => by simpa using h),
        Finset.card_empty]
  · -- α > 0 : `j < hi` (verbatim wrapped identities)
    have hanat : 1 ≤ α.natAbs := Int.natAbs_pos.mpr (by omega)
    have hPa : 1 ≤ P * α.natAbs := Nat.mul_pos hP hanat
    have hiff : ∀ n, ∀ j ∈ Finset.range (U n),
        (α * (j : ℤ) < T n)
          ↔ ((0 : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) < (T n - 1) / α + 1) := by
      intro n j _
      constructor
      · intro h
        refine ⟨Int.natCast_nonneg j, ?_⟩
        have h2 : (j : ℤ) ≤ (T n - 1) / α := by
          rw [Int.le_ediv_iff_mul_le hpos, mul_comm]
          omega
        omega
      · rintro ⟨_, h⟩
        have h2 : (j : ℤ) ≤ (T n - 1) / α := by omega
        rw [Int.le_ediv_iff_mul_le hpos, mul_comm] at h2
        omega
    have hhi' : AffineOnResiduesAtZ (P * α.natAbs)
        (fun n => (T n - 1) / α + 1) :=
      (ediv_int hP α (by omega) (hT.sub hP (const P 1))).add hPa (const _ 1)
    have hUlift : SlicePeriodStar.AffineOnResiduesAt (P * α.natAbs) U :=
      hU.of_dvd hP (Dvd.intro _ rfl) hPa
    have hcnt := countInterval_at hPa
      (const (P * α.natAbs) 0) hhi' hUlift
    have hshape : SlicePeriodStar.AffineOnResiduesAt (P * α.natAbs)
        (fun n => ((Finset.range (U n)).filter
          (fun j : ℕ => α * (j : ℤ) < T n)).card) := by
      refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_) hcnt
      show ((Finset.range (U n)).filter
          (fun j : ℕ => (0 : ℤ) ≤ (j : ℤ)
            ∧ (j : ℤ) < (T n - 1) / α + 1)).card = _
      exact (congrArg Finset.card (Finset.filter_congr (hiff n))).symm
    refine hshape.of_dvd hPa ?_ hQ
    rwa [show max α.natAbs 1 = α.natAbs from by omega] at hdvd

/-- **The pinned lex-below count** (amendment D19): counting `t < U n` whose
affine line is `lexLtL`-below the pinned threshold list is pinned at any
multiple of `P · slopeProd L`.  Induction on the line list: the head-strict
term is `countLtThreshold_at`; the `p ≠ 0` tie term is ONE indicator of an
eventually-periodic four-way conjunction (`pinned_count`); the `p = 0` tie
term is the gated tail count. -/
theorem countLexL_at (L : List (ℤ × ℤ)) :
    ∀ (T : List (ℕ → ℤ)) (P : ℕ), 1 ≤ P →
    (∀ f ∈ T, AffineOnResiduesAtZ P f) →
    ∀ (U : ℕ → ℕ), SlicePeriodStar.AffineOnResiduesAt P U →
    ∀ (Q : ℕ), 1 ≤ Q → P * slopeProd L ∣ Q →
    SlicePeriodStar.AffineOnResiduesAt Q (fun n => ((Finset.range (U n)).filter
      (fun t : ℕ => SliceLexCount.lexLtL
        (L.map (fun bp => bp.1 + (t : ℤ) * bp.2))
        (T.map (fun f => f n)))).card) := by
  classical
  induction L with
  | nil =>
      intro T P hP hT U hU Q hQ hdvd
      refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_)
        (SlicePeriodStar.AffineOnResiduesAt.const Q 0)
      show 0 = _
      rw [Finset.filter_false_of_mem
        (fun t _ => by simp [SliceLexCount.lexLtL]), Finset.card_empty]
  | cons bp L' ih =>
      intro T P hP hT U hU Q hQ hdvd
      obtain ⟨b, p⟩ := bp
      have hPQ : P ∣ Q := dvd_trans (Dvd.intro _ rfl) hdvd
      have hsprod : P * slopeProd L' ∣ Q := by
        refine dvd_trans ?_ hdvd
        rw [slopeProd_cons,
          show P * (max p.natAbs 1 * slopeProd L')
            = P * slopeProd L' * max p.natAbs 1 from by ring]
        exact dvd_mul_right _ _
      cases T with
      | nil =>
          refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_)
            (SlicePeriodStar.AffineOnResiduesAt.const Q 0)
          show 0 = _
          rw [Finset.filter_false_of_mem
            (fun t _ => by simp [SliceLexCount.lexLtL]), Finset.card_empty]
      | cons c T' =>
          have hc : AffineOnResiduesAtZ P c := hT c List.mem_cons_self
          have hT' : ∀ f ∈ T', AffineOnResiduesAtZ P f :=
            fun f hf => hT f (List.mem_cons_of_mem c hf)
          -- split the head disjunction into strict + tie (verbatim wrapped)
          have hsplit : (fun n => ((Finset.range (U n)).filter (fun t : ℕ =>
                SliceLexCount.lexLtL
                  (((b, p) :: L').map (fun bp => bp.1 + (t : ℤ) * bp.2))
                  ((c :: T').map (fun f => f n)))).card)
              = (fun n => ((Finset.range (U n)).filter
                    (fun t : ℕ => b + (t : ℤ) * p < c n)).card
                  + ((Finset.range (U n)).filter
                    (fun t : ℕ => b + (t : ℤ) * p = c n ∧
                      SliceLexCount.lexLtL
                        (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                        (T'.map (fun f => f n)))).card) := by
            funext n
            have hfc : (Finset.range (U n)).filter (fun t : ℕ =>
                  SliceLexCount.lexLtL
                    (((b, p) :: L').map (fun bp => bp.1 + (t : ℤ) * bp.2))
                    ((c :: T').map (fun f => f n)))
                = (Finset.range (U n)).filter
                    (fun t : ℕ => (b + (t : ℤ) * p < c n) ∨
                      (b + (t : ℤ) * p = c n ∧ SliceLexCount.lexLtL
                        (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                        (T'.map (fun f => f n)))) :=
              Finset.filter_congr (fun t _ => by
                simp only [List.map_cons, SliceLexCount.lexLtL])
            have hdisj : Disjoint
                ((Finset.range (U n)).filter
                  (fun t : ℕ => b + (t : ℤ) * p < c n))
                ((Finset.range (U n)).filter
                  (fun t : ℕ => b + (t : ℤ) * p = c n ∧
                    SliceLexCount.lexLtL
                      (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                      (T'.map (fun f => f n)))) := by
              apply Finset.disjoint_left.mpr
              intro t h1 h2
              rw [Finset.mem_filter] at h1 h2
              exact absurd h2.2.1 (ne_of_lt h1.2)
            rw [hfc, Finset.filter_or, Finset.card_union_of_disjoint hdisj]
          rw [hsplit]
          refine SlicePeriodStar.AffineOnResiduesAt.add hQ ?_ ?_
          · -- strict head
            have hmax : P * max p.natAbs 1 ∣ Q := by
              refine dvd_trans ?_ hdvd
              rw [slopeProd_cons, ← Nat.mul_assoc]
              exact dvd_mul_right _ _
            refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_)
              (countLtThreshold_at p hP (hc.sub hP (const P b)) hU hQ hmax)
            show ((Finset.range (U n)).filter
                (fun j : ℕ => p * (j : ℤ) < c n - b)).card = _
            apply congrArg Finset.card
            apply Finset.filter_congr
            intro t _
            rw [mul_comm p ((t : ℕ) : ℤ)]
            generalize ((t : ℕ) : ℤ) * p = X
            omega
          · -- tie
            by_cases hp0 : p = 0
            · -- zero slope: gated tail count
              subst hp0
              have heq : (fun n => ((Finset.range (U n)).filter (fun t : ℕ =>
                    b + (t : ℤ) * 0 = c n ∧ SliceLexCount.lexLtL
                      (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                      (T'.map (fun f => f n)))).card)
                  = (fun n => ((Finset.range (U n)).filter (fun t : ℕ =>
                      SliceLexCount.lexLtL
                        (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                        (T'.map (fun f => f n)))).card
                      * (if b = c n then 1 else 0)) := by
                funext n
                by_cases hbc : b = c n
                · rw [if_pos hbc, Nat.mul_one]
                  apply congrArg Finset.card
                  apply Finset.filter_congr
                  intro t _
                  constructor
                  · rintro ⟨-, hr⟩
                    exact hr
                  · intro hr
                    exact ⟨by rw [← hbc]; ring, hr⟩
                · rw [if_neg hbc, Nat.mul_zero, Finset.card_eq_zero,
                    Finset.filter_eq_empty_iff]
                  rintro t - ⟨he, -⟩
                  exact hbc (by simpa using he)
              rw [heq]
              have hEPeq : SliceOrder.EventuallyPeriodic (fun n => b = c n) Q :=
                SliceDstar.EP_of_dvd (eq_EP_at hP (const P b) hc) hPQ
              exact mul_indicator_at hQ (ih T' P hP hT' U hU Q hQ hsprod) hEPeq
            · -- nonzero slope: pinned_count gives ONE indicator
              have hpnat : 1 ≤ p.natAbs := Int.natAbs_pos.mpr hp0
              have hPp1 : 1 ≤ P * p.natAbs := Nat.mul_pos hP hpnat
              have hPp : P * p.natAbs ∣ Q := by
                refine dvd_trans ?_ hdvd
                rw [slopeProd_cons, ← Nat.mul_assoc,
                  show max p.natAbs 1 = p.natAbs from by omega]
                exact dvd_mul_right _ _
              have hediv : AffineOnResiduesAtZ (P * p.natAbs)
                  (fun n => (c n - b) / p) :=
                ediv_int hP p hp0 (hc.sub hP (const P b))
              have bitA : SliceOrder.EventuallyPeriodic
                  (fun n => p ∣ (c n - b)) Q :=
                SliceDstar.EP_of_dvd (dvd_EP_at hP p hp0
                  (hc.sub hP (const P b))) hPp
              have bitB : SliceOrder.EventuallyPeriodic
                  (fun n => 0 ≤ (c n - b) / p) Q :=
                SliceDstar.EP_of_dvd (le_EP_at hPp1 (const _ 0) hediv) hPp
              have bitC : SliceOrder.EventuallyPeriodic
                  (fun n => ((c n - b) / p).toNat < U n) Q :=
                SliceDstar.EP_of_dvd (nat_lt_EP_at hPp1 (hediv.toNat_at hPp1)
                  (hU.of_dvd hP (Dvd.intro _ rfl) hPp1)) hPp
              have bitD : SliceOrder.EventuallyPeriodic (fun n =>
                  SliceLexCount.lexLtL
                    (L'.map (fun bp => bp.1 + ((c n - b) / p) * bp.2))
                    (T'.map (fun f => f n))) Q := by
                have hlines : ∀ f ∈ L'.map (fun bp =>
                    (fun n => bp.1 + ((c n - b) / p) * bp.2)),
                    AffineOnResiduesAtZ (P * p.natAbs) f := by
                  intro f hf
                  rw [List.mem_map] at hf
                  obtain ⟨bp', -, rfl⟩ := hf
                  exact (const _ bp'.1).add hPp1
                    ((hediv.smul bp'.2).congr'
                      (fun n => mul_comm bp'.2 ((c n - b) / p)))
                have hT'lift : ∀ f ∈ T', AffineOnResiduesAtZ (P * p.natAbs) f :=
                  fun f hf => (hT' f hf).of_dvd hP (Dvd.intro _ rfl) hPp1
                have h := lexLtL_EP_at hPp1
                  (L'.map (fun bp => (fun n => bp.1 + ((c n - b) / p) * bp.2)))
                  T' hlines hT'lift
                refine SliceDstar.EP_of_dvd
                  (SliceOrder.EventuallyPeriodic.congr (fun n => ?_) h) hPp
                simp only [List.map_map, Function.comp_def]
              refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_)
                (CopiedAffineAt.affineOnResiduesAt_indicator_of_EP hQ
                  (bitA.and (bitB.and (bitC.and bitD))))
              show (if (p ∣ (c n - b) ∧ 0 ≤ (c n - b) / p
                  ∧ ((c n - b) / p).toNat < U n
                  ∧ SliceLexCount.lexLtL
                      (L'.map (fun bp => bp.1 + ((c n - b) / p) * bp.2))
                      (T'.map (fun f => f n))) then 1 else 0) = _
              rw [SliceLexCount.pinned_count b p (c n) hp0 (U n)
                (fun t => SliceLexCount.lexLtL
                  (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                  (T'.map (fun f => f n)))]
              refine if_congr ?_ rfl rfl
              constructor
              · rintro ⟨h1, h2, h3, h4⟩
                refine ⟨h1, h2, h3, ?_⟩
                rwa [show (L'.map (fun bp =>
                    bp.1 + ((((c n - b) / p).toNat : ℕ) : ℤ) * bp.2))
                    = L'.map (fun bp => bp.1 + ((c n - b) / p) * bp.2) from
                  List.map_congr_left (fun bp' _ => by
                    rw [Int.toNat_of_nonneg h2])]
              · rintro ⟨h1, h2, h3, h4⟩
                refine ⟨h1, h2, h3, ?_⟩
                rwa [show (L'.map (fun bp =>
                    bp.1 + ((((c n - b) / p).toNat : ℕ) : ℤ) * bp.2))
                    = L'.map (fun bp => bp.1 + ((c n - b) / p) * bp.2) from
                  List.map_congr_left (fun bp' _ => by
                    rw [Int.toNat_of_nonneg h2])] at h4

/-- **The pinned residue-index lex count**: counting `i < N n` with
`i ≡ a [mod m]` whose period-index line is `lexLtL`-below the threshold is
pinned at any multiple of `P · m · slopeProd L`. -/
theorem countLexL_residueIndex_at (a m : ℕ) (ha : a < m) (L : List (ℤ × ℤ))
    (T : List (ℕ → ℤ)) {P : ℕ} (hP : 1 ≤ P)
    (hT : ∀ f ∈ T, AffineOnResiduesAtZ P f)
    {N : ℕ → ℕ} (hN : SlicePeriodStar.AffineOnResiduesAt P N)
    {Q : ℕ} (hQ : 1 ≤ Q) (hdvd : P * m * slopeProd L ∣ Q) :
    SlicePeriodStar.AffineOnResiduesAt Q (fun n => ((Finset.range (N n)).filter
      (fun i : ℕ => i % m = a ∧ SliceLexCount.lexLtL
        (L.map (fun bp => bp.1 + (((i - a) / m : ℕ) : ℤ) * bp.2))
        (T.map (fun f => f n)))).card) := by
  have hm : 1 ≤ m := by omega
  have hPm : 1 ≤ P * m := Nat.mul_pos hP hm
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hU'aff : SlicePeriodStar.AffineOnResiduesAt (P * m)
      (fun n => ((((N n : ℕ) : ℤ) - a + m - 1) / (m : ℤ)).toNat) :=
    (ediv_nat hP m hm ((((natCast hN).sub hP (const P (a : ℤ))).add hP
      (const P (m : ℤ))).sub hP (const P 1))).toNat_at hPm
  have hTm : ∀ f ∈ T, AffineOnResiduesAtZ (P * m) f :=
    fun f hf => (hT f hf).of_dvd hP (Dvd.intro _ rfl) hPm
  have hcnt := countLexL_at L T (P * m) hPm hTm _ hU'aff Q hQ hdvd
  refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_) hcnt
  show ((Finset.range (((((N n : ℕ) : ℤ) - a + m - 1) / (m : ℤ)).toNat)).filter
      (fun t : ℕ => SliceLexCount.lexLtL
        (L.map (fun bp => bp.1 + (t : ℤ) * bp.2))
        (T.map (fun f => f n)))).card = _
  have hbound : ∀ t : ℕ,
      t < ((((N n : ℕ) : ℤ) - a + m - 1) / (m : ℤ)).toNat
        ↔ a + m * t < N n := by
    intro t
    rw [Int.lt_toNat]
    constructor
    · intro h
      have h2 : ((t : ℤ) + 1) * (m : ℤ)
          ≤ ((N n : ℕ) : ℤ) - (a : ℤ) + (m : ℤ) - 1 :=
        (Int.le_ediv_iff_mul_le hmZ).mp (by omega)
      have h3 : ((a + m * t : ℕ) : ℤ) < ((N n : ℕ) : ℤ) := by
        push_cast at h2 ⊢
        nlinarith [h2]
      exact_mod_cast h3
    · intro h
      have h3 : ((a + m * t : ℕ) : ℤ) < ((N n : ℕ) : ℤ) := by exact_mod_cast h
      have h2 : ((t : ℤ) + 1) * (m : ℤ)
          ≤ ((N n : ℕ) : ℤ) - (a : ℤ) + (m : ℤ) - 1 := by
        push_cast at h3 ⊢
        nlinarith [h3]
      exact (Int.le_ediv_iff_mul_le hmZ).mpr h2
  refine Finset.card_bij (fun t _ => a + m * t) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter, Finset.mem_range] at ht ⊢
    refine ⟨(hbound t).mp ht.1, ?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    · rw [show (a + m * t - a) / m = t from by
        rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hm]]
      exact ht.2
  · intro t1 _ t2 _ h
    exact Nat.eq_of_mul_eq_mul_left hm (Nat.add_left_cancel h)
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hiN, himod, hilex⟩ := hi
    have hdm := Nat.div_add_mod i m
    have hieq : a + m * (i / m) = i := by omega
    have hia : (i - a) / m = i / m := by
      rw [show i - a = m * (i / m) from by omega,
        Nat.mul_div_cancel_left _ hm]
    refine ⟨i / m, ?_, hieq⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨(hbound (i / m)).mpr (by rw [hieq]; exact hiN), ?_⟩
    rw [← hia]
    exact hilex

/-- **The pinned gated lex-convolution kernel** (FIBRED_PORTMAP F3.1 + D19):
the count of loop-indices `j < n` with `lexLt (R j) (T n)` and convolution
bit on is pinned at any multiple of
`P · (pu·pv·pR) · ∏ max |(pu·pv)·PR c| 1`. -/
theorem gatedLexConvolution_at {α β : Type*} {d : ℕ}
    (u : ℕ → α) (v : ℕ → β) (b : α → β → Prop)
    {mu pu : ℕ} (hpu : 1 ≤ pu) (hu : ∀ i, mu ≤ i → u (i + pu) = u i)
    {mv pv : ℕ} (hpv : 1 ≤ pv) (hv : ∀ j, mv ≤ j → v (j + pv) = v j)
    (R : ℕ → Fin d → ℤ) {mR pR : ℕ} (PR : Fin d → ℤ) (hpR : 1 ≤ pR)
    (hR : ∀ j, mR ≤ j → R (j + pR) = R j + PR)
    (T : ℕ → Fin d → ℤ) {P : ℕ} (hP : 1 ≤ P)
    (hT : ∀ i, AffineOnResiduesAtZ P (fun n => T n i))
    {Q : ℕ} (hQ : 1 ≤ Q)
    (hdvdQ : P * (pu * pv * pR)
      * (∏ c : Fin d, max ((((pu * pv : ℕ) : ℤ) * PR c).natAbs) 1) ∣ Q) :
    SlicePeriodStar.AffineOnResiduesAt Q (fun n => ((Finset.range n).filter
      (fun j : ℕ => WRP.lexLt (R j) (T n)
        ∧ b (u j) (v (n - 1 - j)))).card) := by
  classical
  -- periodicity helpers (verbatim transplants)
  have hu_iter : ∀ s t, mu ≤ s → u (s + pu * t) = u s := by
    intro s t hs
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hu _ (by omega), ih]
  have hv_iter : ∀ s t, mv ≤ s → v (s + pv * t) = v s := by
    intro s t hs
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hv _ (by omega), ih]
  have hR_iter : ∀ s t, mR ≤ s → R (s + pR * t) = R s + t • PR := by
    intro s t hs
    induction t with
    | zero => simp
    | succ t ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc, hR _ (by omega), ih, succ_nsmul]
        abel
  set p := pu * pv * pR with hpdef
  have hp : 1 ≤ p := Nat.mul_pos (Nat.mul_pos hpu hpv) hpR
  set M0 := max mu mR with hM0def
  have hu_p : ∀ s t, mu ≤ s → u (s + p * t) = u s := by
    intro s t hs
    rw [hpdef, show pu * pv * pR * t = pu * (pv * pR * t) from by ring]
    exact hu_iter s (pv * pR * t) hs
  have hv_p : ∀ s t, mv ≤ s → v (s + p * t) = v s := by
    intro s t hs
    rw [hpdef, show pu * pv * pR * t = pv * (pu * pR * t) from by ring]
    exact hv_iter s (pu * pR * t) hs
  set sl : Fin d → ℤ := fun c => ((pu * pv : ℕ) : ℤ) * PR c with hsldef
  have hR_p : ∀ s t, mR ≤ s → R (s + p * t) = R s + t • sl := by
    intro s t hs
    rw [hpdef, show pu * pv * pR * t = pR * (pu * pv * t) from by ring,
      hR_iter s (pu * pv * t) hs]
    congr 1
    funext c
    show ((pu * pv * t : ℕ)) • PR c = t • sl c
    rw [hsldef]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  -- divisibilities
  have hdvd_full : P * p
      * (∏ c : Fin d, max ((((pu * pv : ℕ) : ℤ) * PR c).natAbs) 1) ∣ Q :=
    hdvdQ
  have hdvd_p : p ∣ Q := by
    refine dvd_trans ?_ hdvd_full
    rw [show P * p * (∏ c : Fin d, max ((((pu * pv : ℕ) : ℤ) * PR c).natAbs) 1)
        = p * (P * (∏ c : Fin d, max ((((pu * pv : ℕ) : ℤ) * PR c).natAbs) 1))
      from by ring]
    exact Dvd.intro _ rfl
  have hPQ : P ∣ Q := by
    refine dvd_trans ?_ hdvd_full
    rw [show P * p * (∏ c : Fin d, max ((((pu * pv : ℕ) : ℤ) * PR c).natAbs) 1)
        = P * (p * (∏ c : Fin d, max ((((pu * pv : ℕ) : ℤ) * PR c).natAbs) 1))
      from by ring]
    exact Dvd.intro _ rfl
  have hdvd_pu : pu ∣ Q :=
    dvd_trans (dvd_trans (dvd_mul_right pu pv)
      (dvd_mul_right (pu * pv) pR)) hdvd_p
  have hdvd_pv : pv ∣ Q :=
    dvd_trans (dvd_trans (dvd_mul_left pv pu)
      (dvd_mul_right (pu * pv) pR)) hdvd_p
  have hdvd_pR : pR ∣ Q := dvd_trans (dvd_mul_left pR (pu * pv)) hdvd_p
  -- the gated lex indicator
  have hTQ : ∀ i, AffineOnResiduesAtZ Q (fun n => T n i) :=
    fun i => (hT i).of_dvd hP hPQ hQ
  have gatedLex : ∀ (C : ℕ → Fin d → ℤ),
      (∀ i, AffineOnResiduesAtZ Q (fun n => C n i)) →
      ∀ (Bit : ℕ → Prop), SliceOrder.EventuallyPeriodic Bit Q →
      SlicePeriodStar.AffineOnResiduesAt Q
        (fun n => if WRP.lexLt (C n) (T n) ∧ Bit n then 1 else 0) := by
    intro C hC Bit hBit
    exact CopiedAffineAt.affineOnResiduesAt_indicator_of_EP hQ
      ((CopiedAffineAt.lexLt_EP_at hQ hC hTQ).and hBit)
  -- forward boundary `j < M0`
  have hFB : SlicePeriodStar.AffineOnResiduesAt Q
      (fun n => ∑ j ∈ Finset.range M0,
        (if WRP.lexLt (R j) (T n)
          ∧ b (u j) (v (n - 1 - j)) then 1 else 0)) := by
    apply SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hQ
    intro j _
    refine gatedLex (fun _ => R j) (fun i => const Q _)
      (fun n => b (u j) (v (n - 1 - j))) ?_
    refine SliceDstar.EP_of_dvd ?_ hdvd_pv
    refine ⟨mv + j + 1, fun n hn => ?_⟩
    show b (u j) (v (n + pv - 1 - j)) ↔ b (u j) (v (n - 1 - j))
    rw [show n + pv - 1 - j = (n - 1 - j) + pv from by omega, hv _ (by omega)]
  -- backward boundary, reindexed `j = n - mv + i`
  have hBB : SlicePeriodStar.AffineOnResiduesAt Q
      (fun n => ∑ i ∈ Finset.range mv,
        (if WRP.lexLt (R (n - mv + i)) (T n)
          ∧ b (u (n - mv + i)) (v (n - 1 - (n - mv + i))) then 1 else 0)) := by
    apply SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hQ
    intro i hi_mem
    rw [Finset.mem_range] at hi_mem
    refine SlicePeriodStar.AffineOnResiduesAt.congr_eventually hQ
      (mR + mv + i + 1) (fun n hn => ?_)
      (gatedLex (fun n => R (n - mv + i)) ?_
        (fun n => b (u (n - mv + i)) (v (mv - 1 - i))) ?_)
    · have e2 : v (n - 1 - (n - mv + i)) = v (mv - 1 - i) := by
        rw [show n - 1 - (n - mv + i) = mv - 1 - i from by omega]
      rw [e2]
    · intro cc
      refine AffineOnResiduesAtZ.of_recurrence hQ (m := mR + mv)
        (S := ((Q / pR : ℕ) : ℤ) * PR cc) ?_
      intro n hn
      show R (n + Q - mv + i) cc = R (n - mv + i) cc + _
      rw [show n + Q - mv + i = (n - mv + i) + pR * (Q / pR) from by
        rw [Nat.mul_div_cancel' hdvd_pR]
        omega]
      rw [hR_iter (n - mv + i) (Q / pR) (by omega)]
      simp only [Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    · refine SliceDstar.EP_of_dvd ?_ hdvd_pu
      refine ⟨mu + mv + i + 1, fun n hn => ?_⟩
      show b (u (n + pu - mv + i)) (v (mv - 1 - i))
        ↔ b (u (n - mv + i)) (v (mv - 1 - i))
      rw [show n + pu - mv + i = (n - mv + i) + pu from by omega,
        hu _ (by omega)]
  -- bulk pieces
  set Lr : ℕ → List (ℤ × ℤ) :=
    fun r => List.ofFn (fun c : Fin d => (R (M0 + r) c, sl c)) with hLrdef
  set Tlist : List (ℕ → ℤ) :=
    List.ofFn (fun c : Fin d => (fun n => T n c)) with hTlistdef
  have hTlistA : ∀ f ∈ Tlist, AffineOnResiduesAtZ P f := by
    intro f hf
    rw [hTlistdef, List.mem_ofFn] at hf
    obtain ⟨c, rfl⟩ := hf
    exact hT c
  set Cr : ℕ → ℕ → ℕ := fun r n => ((Finset.range (n - M0 - mv)).filter
    (fun i : ℕ => i % p = r ∧ SliceLexCount.lexLtL
      ((Lr r).map (fun bp => bp.1 + (((i - r) / p : ℕ) : ℤ) * bp.2))
      (Tlist.map (fun f => f n)))).card with hCrdef
  set Ibeta : ℕ → ℕ → ℕ := fun r n =>
    if b (u (M0 + r)) (v (mv + (n - M0 - mv - 1 - r))) then 1 else 0
    with hIbetadef
  have hNaffP : SlicePeriodStar.AffineOnResiduesAt P
      (fun n => n - M0 - mv) := by
    refine ⟨M0 + mv, fun j hj => ⟨j, P, fun k => ?_⟩⟩
    show M0 + mv + j + P * k - M0 - mv = j + k * P
    rw [Nat.mul_comm P k]
    generalize k * P = A
    omega
  have hsprodLr : ∀ r, slopeProd (Lr r)
      = ∏ c : Fin d, max ((((pu * pv : ℕ) : ℤ) * PR c).natAbs) 1 := by
    intro r
    rw [hLrdef]
    unfold slopeProd
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  have hCr : ∀ r, r < p → SlicePeriodStar.AffineOnResiduesAt Q
      (fun n => Cr r n) := by
    intro r hr
    refine countLexL_residueIndex_at r p hr (Lr r) Tlist hP hTlistA hNaffP hQ ?_
    rw [hsprodLr r]
    exact hdvd_full
  have hBK : SlicePeriodStar.AffineOnResiduesAt Q
      (fun n => ∑ r ∈ Finset.range p, Cr r n * Ibeta r n) := by
    apply SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hQ
    intro r hr_mem
    rw [Finset.mem_range] at hr_mem
    have hEPbit : SliceOrder.EventuallyPeriodic
        (fun n => b (u (M0 + r)) (v (mv + (n - M0 - mv - 1 - r)))) Q := by
      refine SliceDstar.EP_of_dvd ?_ hdvd_p
      refine ⟨M0 + mv + 1 + r, fun n hn => ?_⟩
      show b (u (M0 + r)) (v (mv + (n + p - M0 - mv - 1 - r)))
        ↔ b (u (M0 + r)) (v (mv + (n - M0 - mv - 1 - r)))
      rw [show mv + (n + p - M0 - mv - 1 - r)
          = (mv + (n - M0 - mv - 1 - r)) + p * 1 from by omega]
      rw [hv_p (mv + (n - M0 - mv - 1 - r)) 1 (by omega)]
    exact mul_indicator_at hQ (hCr r hr_mem) hEPbit
  -- backward-boundary reindex identity (verbatim transplant)
  have eBB : ∀ n, mv ≤ n →
      (∑ j ∈ Finset.Ico (n - mv) n,
        (if WRP.lexLt (R j) (T n)
          ∧ b (u j) (v (n - 1 - j)) then (1 : ℕ) else 0))
      = ∑ i ∈ Finset.range mv,
        (if WRP.lexLt (R (n - mv + i)) (T n)
          ∧ b (u (n - mv + i)) (v (n - 1 - (n - mv + i))) then 1 else 0) := by
    intro n _
    rw [Finset.sum_Ico_eq_sum_range, show n - (n - mv) = mv from by omega]
  -- bulk identity (verbatim transplant)
  have eBK : ∀ n, M0 + mv ≤ n →
      (∑ j ∈ Finset.Ico M0 (n - mv),
        (if WRP.lexLt (R j) (T n)
          ∧ b (u j) (v (n - 1 - j)) then (1 : ℕ) else 0))
      = ∑ r ∈ Finset.range p, Cr r n * Ibeta r n := by
    intro n hn
    rw [Finset.sum_Ico_eq_sum_range,
      show n - mv - M0 = n - M0 - mv from by omega,
      ← Finset.sum_fiberwise_of_maps_to (t := Finset.range p)
        (g := fun i => i % p)
        (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hp))]
    apply Finset.sum_congr rfl
    intro r hr_mem
    rw [Finset.mem_range] at hr_mem
    have hbody : ∀ i ∈ (Finset.range (n - M0 - mv)).filter
        (fun i => i % p = r),
        (if WRP.lexLt (R (M0 + i)) (T n)
          ∧ b (u (M0 + i)) (v (n - 1 - (M0 + i))) then (1 : ℕ) else 0)
        = (if SliceLexCount.lexLtL
              ((Lr r).map (fun bp => bp.1 + (((i - r) / p : ℕ) : ℤ) * bp.2))
              (Tlist.map (fun f => f n)) then 1 else 0)
          * (if b (u (M0 + r)) (v (mv + (n - M0 - mv - 1 - r)))
              then 1 else 0) := by
      intro i hi_mem
      rw [Finset.mem_filter, Finset.mem_range] at hi_mem
      obtain ⟨hilt, himod⟩ := hi_mem
      have hik : (i - r) / p = i / p := by
        have hdm := Nat.div_add_mod i p
        rw [show i - r = p * (i / p) from by omega,
          Nat.mul_div_cancel_left _ hp]
      have hidx : M0 + i = (M0 + r) + p * (i / p) := by
        have hdm := Nat.div_add_mod i p
        omega
      have hlexeq : WRP.lexLt (R (M0 + i)) (T n)
          ↔ SliceLexCount.lexLtL
              ((Lr r).map (fun bp => bp.1 + (((i - r) / p : ℕ) : ℤ) * bp.2))
              (Tlist.map (fun f => f n)) := by
        rw [SliceLexCount.lexLt_iff_lexLtL, hLrdef, hTlistdef,
          List.map_ofFn, List.map_ofFn]
        refine Iff.of_eq (congrArg₂ SliceLexCount.lexLtL
          (congrArg List.ofFn (funext fun c => ?_)) rfl)
        show R (M0 + i) c = R (M0 + r) c + (((i - r) / p : ℕ) : ℤ) * sl c
        rw [hidx, hR_p (M0 + r) (i / p) (by omega), hik]
        simp only [Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
      have hu_eq : u (M0 + i) = u (M0 + r) := by
        rw [hidx]
        exact hu_p (M0 + r) (i / p) (by omega)
      have hv_eq : v (n - 1 - (M0 + i)) = v (mv + (n - M0 - mv - 1 - r)) := by
        have hidx2 : mv + (n - M0 - mv - 1 - r)
            = (n - 1 - (M0 + i)) + p * (i / p) := by
          have hdm := Nat.div_add_mod i p
          omega
        rw [hidx2]
        exact (hv_p (n - 1 - (M0 + i)) (i / p) (by omega)).symm
      rw [hu_eq, hv_eq, ← SliceLexCount.ite_and_mul]
      exact if_congr (and_congr_left (fun _ => hlexeq)) rfl rfl
    rw [Finset.sum_congr rfl hbody, ← Finset.sum_mul]
    refine congrArg₂ (· * ·) ?_ rfl
    simp only [hCrdef]
    rw [← Finset.filter_filter, Finset.card_filter]
  -- assemble
  refine SlicePeriodStar.AffineOnResiduesAt.congr_eventually hQ (M0 + mv)
    (fun n hn => ?_) ((hFB.add hQ hBK).add hQ hBB)
  rw [Finset.card_filter,
    ← Finset.sum_range_add_sum_Ico _ (show M0 ≤ n from by omega),
    ← Finset.sum_Ico_consecutive _ (show M0 ≤ n - mv from by omega)
      (show n - mv ≤ n from by omega),
    eBK n hn, eBB n (by omega)]
  ring

/-- **Pinned partition subtraction**: if `A = B + C` pointwise with `A`, `B`
pinned at `Q`, so is `C` (slopes subtract; nonnegativity forces the order). -/
theorem sub_of_partition_at {Q : ℕ} (hQ : 1 ≤ Q) {A B C : ℕ → ℕ}
    (hA : SlicePeriodStar.AffineOnResiduesAt Q A)
    (hB : SlicePeriodStar.AffineOnResiduesAt Q B)
    (h : ∀ n, A n = B n + C n) :
    SlicePeriodStar.AffineOnResiduesAt Q C := by
  obtain ⟨mA, hmA⟩ := hA.exists_rebase hQ
  obtain ⟨mB, hmB⟩ := hB.exists_rebase hQ
  refine ⟨max mA mB, fun j hj => ?_⟩
  obtain ⟨bA, sA, hbsA⟩ := hmA _ (le_max_left _ _) j hj
  obtain ⟨bB, sB, hbsB⟩ := hmB _ (le_max_right _ _) j hj
  -- the slopes are ordered (else A − B would go negative)
  have hs : sB ≤ sA := by
    by_contra hcon
    push Not at hcon
    have h1 := h (max mA mB + j + Q * (bA + 1))
    rw [hbsA (bA + 1), hbsB (bA + 1)] at h1
    have hZ : (bA + 1) * sB ≥ (bA + 1) * sA + (bA + 1) :=
      by calc (bA + 1) * sB ≥ (bA + 1) * (sA + 1) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = (bA + 1) * sA + (bA + 1) := by ring
    generalize hX : (bA + 1) * sA = X at h1 hZ
    generalize hY : (bA + 1) * sB = Y at h1 hZ
    omega
  have hb : bB ≤ bA := by
    have h0 := h (max mA mB + j + Q * 0)
    rw [hbsA 0, hbsB 0] at h0
    omega
  refine ⟨bA - bB, sA - sB, fun k => ?_⟩
  have h1 := h (max mA mB + j + Q * k)
  rw [hbsA k, hbsB k] at h1
  have hZ : k * (sA - sB) + k * sB = k * sA := by
    rw [← Nat.mul_add]
    congr 1
    omega
  generalize hX : k * sA = X at h1 hZ
  generalize hY : k * sB = Y at h1 hZ
  generalize hW : k * (sA - sB) = W at hZ ⊢
  omega

/-- **The pinned gated eq-convolution kernel**: rank EQUALITY against the
threshold, via the `Fin.snoc` sentinel trick — two lex kernels at the same
data and the pinned partition subtraction. -/
theorem gatedEqConvolution_at {α β : Type*} {d : ℕ}
    (u : ℕ → α) (v : ℕ → β) (b : α → β → Prop)
    {mu pu : ℕ} (hpu : 1 ≤ pu) (hu : ∀ i, mu ≤ i → u (i + pu) = u i)
    {mv pv : ℕ} (hpv : 1 ≤ pv) (hv : ∀ j, mv ≤ j → v (j + pv) = v j)
    (R : ℕ → Fin d → ℤ) {mR pR : ℕ} (PR : Fin d → ℤ) (hpR : 1 ≤ pR)
    (hR : ∀ j, mR ≤ j → R (j + pR) = R j + PR)
    (T : ℕ → Fin d → ℤ) {P : ℕ} (hP : 1 ≤ P)
    (hT : ∀ i, AffineOnResiduesAtZ P (fun n => T n i))
    {Q : ℕ} (hQ : 1 ≤ Q)
    (hdvdQ : P * (pu * pv * pR)
      * (∏ c : Fin d, max ((((pu * pv : ℕ) : ℤ) * PR c).natAbs) 1) ∣ Q) :
    SlicePeriodStar.AffineOnResiduesAt Q (fun n => ((Finset.range n).filter
      (fun j : ℕ => R j = T n ∧ b (u j) (v (n - 1 - j)))).card) := by
  classical
  set Rle : ℕ → Fin (d + 1) → ℤ := fun j => Fin.snoc (R j) (0 : ℤ) with hRledef
  set Rlt : ℕ → Fin (d + 1) → ℤ := fun j => Fin.snoc (R j) (1 : ℤ) with hRltdef
  set Tle : ℕ → Fin (d + 1) → ℤ := fun n => Fin.snoc (T n) (1 : ℤ) with hTledef
  set Tlt : ℕ → Fin (d + 1) → ℤ := fun n => Fin.snoc (T n) (0 : ℤ) with hTltdef
  have hRle : ∀ j, mR ≤ j → Rle (j + pR) = Rle j + Fin.snoc PR (0 : ℤ) := by
    intro j hj
    funext c
    refine Fin.lastCases ?_ ?_ c
    · simp only [hRledef, Pi.add_apply, Fin.snoc_last, add_zero]
    · intro i
      simp only [hRledef, Pi.add_apply, Fin.snoc_castSucc]
      rw [hR j hj]
      simp only [Pi.add_apply]
  have hRlt : ∀ j, mR ≤ j → Rlt (j + pR) = Rlt j + Fin.snoc PR (0 : ℤ) := by
    intro j hj
    funext c
    refine Fin.lastCases ?_ ?_ c
    · simp only [hRltdef, Pi.add_apply, Fin.snoc_last, add_zero]
    · intro i
      simp only [hRltdef, Pi.add_apply, Fin.snoc_castSucc]
      rw [hR j hj]
      simp only [Pi.add_apply]
  have hTle : ∀ i, AffineOnResiduesAtZ P (fun n => Tle n i) := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · simpa only [hTledef, Fin.snoc_last] using const P (1 : ℤ)
    · intro i
      simpa only [hTledef, Fin.snoc_castSucc] using hT i
  have hTlt : ∀ i, AffineOnResiduesAtZ P (fun n => Tlt n i) := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · simpa only [hTltdef, Fin.snoc_last] using const P (0 : ℤ)
    · intro i
      simpa only [hTltdef, Fin.snoc_castSucc] using hT i
  -- the snoc slope product equals the base product (the last factor is 1)
  have hdvdQ' : P * (pu * pv * pR)
      * (∏ c : Fin (d + 1),
          max ((((pu * pv : ℕ) : ℤ)
            * (Fin.snoc PR (0 : ℤ) : Fin (d + 1) → ℤ) c).natAbs) 1) ∣ Q := by
    have hprod : (∏ c : Fin (d + 1),
        max ((((pu * pv : ℕ) : ℤ)
          * (Fin.snoc PR (0 : ℤ) : Fin (d + 1) → ℤ) c).natAbs) 1)
        = ∏ c : Fin d, max ((((pu * pv : ℕ) : ℤ) * PR c).natAbs) 1 := by
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, Int.natAbs_zero]
      simp
    rwa [hprod]
  have Ale := gatedLexConvolution_at u v b hpu hu hpv hv
    Rle (Fin.snoc PR (0 : ℤ)) hpR hRle Tle hP hTle hQ hdvdQ'
  have Alt := gatedLexConvolution_at u v b hpu hu hpv hv
    Rlt (Fin.snoc PR (0 : ℤ)) hpR hRlt Tlt hP hTlt hQ hdvdQ'
  refine sub_of_partition_at hQ Ale Alt (fun n => ?_)
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hle : WRP.lexLt (Rle j) (Tle n)
      ↔ (WRP.lexLt (R j) (T n) ∨ R j = T n) := by
    rw [hRledef, hTledef]
    exact SliceFasCount.lexLt_snoc_le (R j) (T n)
  have hlt : WRP.lexLt (Rlt j) (Tlt n) ↔ WRP.lexLt (R j) (T n) := by
    rw [hRltdef, hTltdef]
    exact SliceFasCount.lexLt_snoc_lt (R j) (T n)
  by_cases hb : b (u j) (v (n - 1 - j))
  · by_cases heq : R j = T n
    · have hlexF : ¬ WRP.lexLt (R j) (T n) :=
        fun hh => SliceFasCount.lexLt_ne hh heq
      rw [if_pos ⟨hle.mpr (Or.inr heq), hb⟩,
        if_neg (fun hh => hlexF (hlt.mp hh.1)), if_pos ⟨heq, hb⟩]
    · by_cases hlex : WRP.lexLt (R j) (T n)
      · rw [if_pos ⟨hle.mpr (Or.inl hlex), hb⟩, if_pos ⟨hlt.mpr hlex, hb⟩,
          if_neg (fun hh => heq hh.1)]
      · rw [if_neg (fun hh => (hle.mp hh.1).elim hlex heq),
          if_neg (fun hh => hlex (hlt.mp hh.1)),
          if_neg (fun hh => heq hh.1)]
  · rw [if_neg (fun hh => hb hh.2), if_neg (fun hh => hb hh.2),
      if_neg (fun hh => hb hh.2)]

end CopiedKernels
