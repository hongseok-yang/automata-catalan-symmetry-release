/-
# The gated convolution kernel: counting loop-indices in a moving interval whose MSO bit is on

`countAccept_slice_affineOnResidues` (SliceCountSlice) counts *all* slice positions whose
marked-DFA gate is on; `countInterval` (SliceThreshold) counts loop-indices in an affine
interval `[lo n, hi n)`.  The arity-1 `fas` count needs **both at once**: the loop-indices
`j` in an affine interval whose per-position `{0,1}` MSO bit is on.  The bit, on the slice,
has the forward/backward convolution shape (`b (u j) (v (n-1-j))` for eventually-periodic
iterates `u`, `v`), and the interval rides on top of it.

This file builds that join abstractly (`affineOnResidues_gatedConvolution`) over an abstract
bit `b : α → β → Prop` with eventually-periodic `u : ℕ → α`, `v : ℕ → β`, plus the supporting
residue-restricted interval count `countIntervalResidue`.  Specialising `u`,`v`,`b` to the
slice forward/backward iterates yields `countPeriodicInterval` (in `SliceFasCount`).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`): purely arithmetic; the MSO/Büchi
content lives in the marked DFA that is later plugged in for `b`.
-/
import RequestProject.SliceLexCount

namespace SliceGatedConv

open SliceThreshold SliceAffine SliceLexCount
open scoped Classical

/-- **Residue-restricted interval count.**  Counting `j ∈ [0, N n)` with `j ≡ a [mod m]`
and `lo n ≤ j < hi n` is `AffineOnResidues` in `n` — reparametrise `j = a + m·t` (a bijection
onto the residue class) back to `countInterval` on the shifted endpoints. -/
theorem countIntervalResidue (a m : ℕ) (ha : a < m) {lo hi : ℕ → ℤ}
    (hlo : AffineOnResiduesZ lo) (hhi : AffineOnResiduesZ hi) {N : ℕ → ℕ}
    (hN : AffineOnResidues N) :
    AffineOnResidues (fun n => ((Finset.range (N n)).filter
      (fun j : ℕ => j % m = a ∧ lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n)).card) := by
  have hm : 1 ≤ m := by omega
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hmne : (m : ℤ) ≠ 0 := ne_of_gt hmZ
  -- the t-bound and shifted endpoints
  set U' : ℕ → ℕ := fun n => (((N n : ℤ) - a + m - 1) / m).toNat with hU'
  set lo' : ℕ → ℤ := fun n => (lo n - a + m - 1) / m with hlo'def
  set hi' : ℕ → ℤ := fun n => (hi n - a - 1) / m + 1 with hhi'def
  have hU'aff : AffineOnResidues U' :=
    (((((AffineOnResiduesZ.of_natCast hN).sub (AffineOnResiduesZ.const (a : ℤ))).add
      (AffineOnResiduesZ.const (m : ℤ))).sub (AffineOnResiduesZ.const 1)).ediv (m : ℤ) hmne).toNat
  have hlo'aff : AffineOnResiduesZ lo' :=
    (((hlo.sub (AffineOnResiduesZ.const (a : ℤ))).add (AffineOnResiduesZ.const (m : ℤ))).sub
      (AffineOnResiduesZ.const 1)).ediv (m : ℤ) hmne
  have hhi'aff : AffineOnResiduesZ hi' :=
    (((hhi.sub (AffineOnResiduesZ.const (a : ℤ))).sub (AffineOnResiduesZ.const 1)).ediv
      (m : ℤ) hmne).add (AffineOnResiduesZ.const 1)
  refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_)
    (countInterval hlo'aff hhi'aff hU'aff)
  -- bound equivalence: t < U' n ↔ a + m·t < N n
  have hbound : ∀ t : ℕ, t < U' n ↔ a + m * t < N n := by
    intro t
    rw [hU', Int.lt_toNat]
    constructor
    · intro h
      have h2 : ((t : ℤ) + 1) * (m : ℤ) ≤ (N n : ℤ) - (a : ℤ) + (m : ℤ) - 1 :=
        (Int.le_ediv_iff_mul_le hmZ).mp (by omega)
      have h3 : ((a + m * t : ℕ) : ℤ) < (N n : ℤ) := by push_cast at h2 ⊢; nlinarith [h2]
      exact_mod_cast h3
    · intro h
      have h3 : ((a + m * t : ℕ) : ℤ) < (N n : ℤ) := by exact_mod_cast h
      have h2 : ((t : ℤ) + 1) * (m : ℤ) ≤ (N n : ℤ) - (a : ℤ) + (m : ℤ) - 1 := by
        push_cast at h3 ⊢; nlinarith [h3]
      exact (Int.le_ediv_iff_mul_le hmZ).mpr h2
  -- lower-endpoint equivalence: lo' n ≤ t ↔ lo n ≤ a + m·t
  have hlobound : ∀ t : ℕ, lo' n ≤ (t : ℤ) ↔ lo n ≤ ((a + m * t : ℕ) : ℤ) := by
    intro t
    rw [hlo'def, ← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hmZ]
    push_cast; constructor <;> intro h <;> nlinarith [h]
  -- upper-endpoint equivalence: t < hi' n ↔ a + m·t < hi n
  have hhibound : ∀ t : ℕ, (t : ℤ) < hi' n ↔ ((a + m * t : ℕ) : ℤ) < hi n := by
    intro t
    rw [hhi'def, Int.lt_add_one_iff, Int.le_ediv_iff_mul_le hmZ]
    push_cast; constructor <;> intro h <;> nlinarith [h]
  -- bijection j = a + m·t
  refine (Finset.card_bij (fun t _ => a + m * t) ?_ ?_ ?_).symm
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
    have hjeq : a + m * (j / m) = j := by have := Nat.div_add_mod j m; omega
    refine ⟨j / m, ?_, hjeq⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨(hbound (j / m)).mpr (by rw [hjeq]; exact hjN),
      (hlobound (j / m)).mpr (by rw [hjeq]; exact hjlo),
      (hhibound (j / m)).mpr (by rw [hjeq]; exact hjhi)⟩

/-- **Residue-restricted period-index lex count.**  The lex analogue of `countIntervalResidue`:
counting `i ∈ [0, N n)` with `i ≡ a [mod m]` and a lex condition whose rank list is affine in
the **period index** `(i-a)/m` is `AffineOnResidues` in `n` — reparametrise `i = a + m·t`
(a bijection onto the residue class, with `(i-a)/m = t`) back to `countLexL`. -/
theorem countLexL_residueIndex (a m : ℕ) (ha : a < m) (L : List (ℤ × ℤ)) (T : List (ℕ → ℤ))
    (hT : ∀ f ∈ T, AffineOnResiduesZ f) {N : ℕ → ℕ} (hN : AffineOnResidues N) :
    AffineOnResidues (fun n => ((Finset.range (N n)).filter
      (fun i : ℕ => i % m = a ∧ lexLtL (L.map (fun bp => bp.1 + (((i - a) / m : ℕ) : ℤ) * bp.2))
        (T.map (fun f => f n)))).card) := by
  have hm : 1 ≤ m := by omega
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  set U' : ℕ → ℕ := fun n => (((N n : ℤ) - a + m - 1) / m).toNat with hU'
  have hU'aff : AffineOnResidues U' :=
    (((((AffineOnResiduesZ.of_natCast hN).sub (AffineOnResiduesZ.const (a : ℤ))).add
      (AffineOnResiduesZ.const (m : ℤ))).sub (AffineOnResiduesZ.const 1)).ediv (m : ℤ) hmZ).toNat
  refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_) (countLexL L T hT U' hU'aff)
  have hbound : ∀ t : ℕ, t < U' n ↔ a + m * t < N n := by
    intro t
    rw [hU', Int.lt_toNat]
    constructor
    · intro h
      have h2 : ((t : ℤ) + 1) * (m : ℤ) ≤ (N n : ℤ) - (a : ℤ) + (m : ℤ) - 1 :=
        (Int.le_ediv_iff_mul_le (by omega : (0 : ℤ) < m)).mp (by omega)
      have h3 : ((a + m * t : ℕ) : ℤ) < (N n : ℤ) := by push_cast at h2 ⊢; nlinarith [h2]
      exact_mod_cast h3
    · intro h
      have h3 : ((a + m * t : ℕ) : ℤ) < (N n : ℤ) := by exact_mod_cast h
      have h2 : ((t : ℤ) + 1) * (m : ℤ) ≤ (N n : ℤ) - (a : ℤ) + (m : ℤ) - 1 := by
        push_cast at h3 ⊢; nlinarith [h3]
      exact (Int.le_ediv_iff_mul_le (by omega : (0 : ℤ) < m)).mpr h2
  refine (Finset.card_bij (fun t _ => a + m * t) ?_ ?_ ?_).symm
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
      rw [show i - a = m * (i / m) from by omega, Nat.mul_div_cancel_left _ hm]
    refine ⟨i / m, ?_, hieq⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨(hbound (i / m)).mpr (by rw [hieq]; exact hiN), ?_⟩
    rw [← hia]; exact hilex

/-- The identity sequence `n ↦ n` is affine on residues (slope `1`). -/
theorem affineOnResidues_id : AffineOnResidues (fun n => n) :=
  ⟨0, 1, fun _ => 1, le_refl 1, fun r k => by simp⟩

/-- **The gated convolution kernel (abstract).**  For eventually-periodic iterates
`u : ℕ → α`, `v : ℕ → β` and any bit `b : α → β → Prop`, the count of loop-indices
`j < n` in an affine interval `[lo n, hi n)` whose bit `b (u j) (v (n-1-j))` is on is
`AffineOnResidues` in `n`.  The interval rides on top of the forward/backward
convolution: the proof peels the forward boundary (`j < mu`) and backward boundary
(`j > n-1-mv`) as finite sums of per-index affine terms, and on the bulk regroups by
residue mod `p = pu·pv`, on which the bit is *constant* (purely-periodic iterates) and
the interval count is `countIntervalResidue`. -/
theorem affineOnResidues_gatedConvolution {α β : Type*}
    (u : ℕ → α) (v : ℕ → β) (b : α → β → Prop)
    {mu pu : ℕ} (hpu : 1 ≤ pu) (hu : ∀ i, mu ≤ i → u (i + pu) = u i)
    {mv pv : ℕ} (hpv : 1 ≤ pv) (hv : ∀ j, mv ≤ j → v (j + pv) = v j)
    {lo hi : ℕ → ℤ} (hlo : AffineOnResiduesZ lo) (hhi : AffineOnResiduesZ hi) :
    AffineOnResidues (fun n => ((Finset.range n).filter
      (fun j : ℕ => lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n ∧ b (u j) (v (n - 1 - j)))).card) := by
  classical
  -- periodicity helpers
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
  set p := pu * pv with hpdef
  have hp : 1 ≤ p := Nat.mul_pos hpu hpv
  have hu_p : ∀ s t, mu ≤ s → u (s + p * t) = u s := by
    intro s t hs
    rw [hpdef, show pu * pv * t = pu * (pv * t) from by ring]
    exact hu_iter s (pv * t) hs
  have hv_p : ∀ s t, mv ≤ s → v (s + p * t) = v s := by
    intro s t hs
    rw [hpdef, show pu * pv * t = pv * (pu * t) from by ring]
    exact hv_iter s (pu * t) hs
  -- gate-bit helper
  have gated : ∀ (C : ℕ → ℤ), AffineOnResiduesZ C → ∀ (Bit : ℕ → Prop),
      AffineOnResidues (fun n => if Bit n then 1 else 0) →
      AffineOnResidues (fun n => if lo n ≤ C n ∧ C n < hi n ∧ Bit n then 1 else 0) := by
    intro C hC Bit hBit
    have heq : (fun n => if lo n ≤ C n ∧ C n < hi n ∧ Bit n then (1 : ℕ) else 0)
        = (fun n => (if lo n ≤ C n then 1 else 0)
            * ((if C n < hi n then 1 else 0) * (if Bit n then 1 else 0))) := by
      funext n
      rw [ite_and_mul (lo n ≤ C n) (C n < hi n ∧ Bit n), ite_and_mul (C n < hi n) (Bit n)]
    rw [heq]
    exact affineOnResidues_mul_bddOne (indicator_le hlo hC)
      (affineOnResidues_mul_bddOne (indicator_lt hC hhi) hBit (fun n => by split <;> simp))
      (fun n => by split_ifs <;> omega)
  -- forward boundary `j < mu`
  have hFB : AffineOnResidues (fun n => ∑ j ∈ Finset.range mu,
      (if lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n ∧ b (u j) (v (n - 1 - j)) then 1 else 0)) := by
    apply AffineOnResidues.finsetSum
    intro j _
    refine gated (fun _ => (j : ℤ)) (AffineOnResiduesZ.const _) (fun n => b (u j) (v (n - 1 - j))) ?_
    refine affineOnResidues_of_eventuallyPeriodic (m := mv + j + 1) (p := pv) hpv (fun n hn => ?_)
    have he : v (n + pv - 1 - j) = v (n - 1 - j) := by
      rw [show n + pv - 1 - j = (n - 1 - j) + pv from by omega]; exact hv _ (by omega)
    exact if_congr (by simp only [he]) rfl rfl
  -- backward boundary `j > n-1-mv`, reindexed `j = n-mv+i`
  have hBB : AffineOnResidues (fun n => ∑ i ∈ Finset.range mv,
      (if lo n ≤ ((n - mv + i : ℕ) : ℤ) ∧ ((n - mv + i : ℕ) : ℤ) < hi n
        ∧ b (u (n - mv + i)) (v (n - 1 - (n - mv + i))) then 1 else 0)) := by
    apply AffineOnResidues.finsetSum
    intro i hi_mem
    rw [Finset.mem_range] at hi_mem
    refine AffineOnResidues.congr_eventually (N := mv + i + 1) (fun n hn => ?_)
      (gated (fun n => (n : ℤ) - mv + i)
        ((AffineOnResiduesZ.id_cast.sub (AffineOnResiduesZ.const (mv : ℤ))).add
          (AffineOnResiduesZ.const (i : ℤ)))
        (fun n => b (u (n - mv + i)) (v (mv - 1 - i))) ?_)
    · have e1 : ((n - mv + i : ℕ) : ℤ) = (n : ℤ) - mv + i := by
        have : mv ≤ n := by omega
        omega
      have e2 : v (n - 1 - (n - mv + i)) = v (mv - 1 - i) := by
        rw [show n - 1 - (n - mv + i) = mv - 1 - i from by omega]
      rw [e1, e2]
    · refine affineOnResidues_of_eventuallyPeriodic (m := mu + mv + i + 1) (p := pu) hpu
        (fun n hn => ?_)
      have he : u (n + pu - mv + i) = u (n - mv + i) := by
        rw [show n + pu - mv + i = (n - mv + i) + pu from by omega]; exact hu _ (by omega)
      exact if_congr (by simp only [he]) rfl rfl
  -- bulk pieces
  set Cr : ℕ → ℕ → ℕ := fun r n => ((Finset.range (n - mu - mv)).filter
    (fun i : ℕ => i % p = r ∧ lo n ≤ ((mu + i : ℕ) : ℤ) ∧ ((mu + i : ℕ) : ℤ) < hi n)).card
    with hCrdef
  set Ibeta : ℕ → ℕ → ℕ := fun r n =>
    if b (u (mu + r)) (v (mv + (n - mu - mv - 1 - r))) then 1 else 0 with hIbetadef
  have hNaff : AffineOnResidues (fun n => n - mu - mv) := by
    have heq : (fun n => n - mu - mv) = (fun n => n - (mu + mv)) := by funext n; rw [Nat.sub_sub]
    rw [heq]; exact affineOnResidues_id.shift (mu + mv)
  have hCr : ∀ r, r < p → AffineOnResidues (fun n => Cr r n) := by
    intro r hr
    refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_)
      (countIntervalResidue r p hr (hlo.sub (AffineOnResiduesZ.const (mu : ℤ)))
        (hhi.sub (AffineOnResiduesZ.const (mu : ℤ))) hNaff)
    rw [hCrdef]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by push_cast at h2 ⊢; omega, by push_cast at h3 ⊢; omega⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by push_cast at h2 ⊢; omega, by push_cast at h3 ⊢; omega⟩
  have hBK : AffineOnResidues (fun n => ∑ r ∈ Finset.range p, Cr r n * Ibeta r n) := by
    apply AffineOnResidues.finsetSum
    intro r hr_mem
    rw [Finset.mem_range] at hr_mem
    refine affineOnResidues_mul_bddOne (hCr r hr_mem) ?_ (fun n => by simp only [hIbetadef]; split_ifs <;> omega)
    rw [hIbetadef]
    refine affineOnResidues_of_eventuallyPeriodic (m := mu + mv + 1 + r) (p := p) hp (fun n hn => ?_)
    have key : v (mv + (n + p - mu - mv - 1 - r)) = v (mv + (n - mu - mv - 1 - r)) := by
      rw [show mv + (n + p - mu - mv - 1 - r) = (mv + (n - mu - mv - 1 - r)) + p * 1 from by omega]
      exact hv_p (mv + (n - mu - mv - 1 - r)) 1 (by omega)
    exact if_congr (by rw [key]) rfl rfl
  -- backward-boundary reindex identity
  have eBB : ∀ n, mv ≤ n →
      (∑ j ∈ Finset.Ico (n - mv) n,
        (if lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n ∧ b (u j) (v (n - 1 - j)) then (1 : ℕ) else 0))
      = ∑ i ∈ Finset.range mv,
        (if lo n ≤ ((n - mv + i : ℕ) : ℤ) ∧ ((n - mv + i : ℕ) : ℤ) < hi n
          ∧ b (u (n - mv + i)) (v (n - 1 - (n - mv + i))) then 1 else 0) := by
    intro n _
    rw [Finset.sum_Ico_eq_sum_range, show n - (n - mv) = mv from by omega]
  -- bulk identity
  have eBK : ∀ n, mu + mv ≤ n →
      (∑ j ∈ Finset.Ico mu (n - mv),
        (if lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n ∧ b (u j) (v (n - 1 - j)) then (1 : ℕ) else 0))
      = ∑ r ∈ Finset.range p, Cr r n * Ibeta r n := by
    intro n hn
    rw [Finset.sum_Ico_eq_sum_range, show n - mv - mu = n - mu - mv from by omega,
      ← Finset.sum_fiberwise_of_maps_to (t := Finset.range p) (g := fun i => i % p)
        (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hp))]
    apply Finset.sum_congr rfl
    intro r hr_mem
    rw [Finset.mem_range] at hr_mem
    -- constancy of the bit on the fiber
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
          set pq := p * (i / p); omega
        rw [hidx]; exact hu_p (mu + r) (i / p) (by omega)
      have hv_eq : v (n - 1 - (mu + i)) = v (mv + (n - mu - mv - 1 - r)) := by
        have hidx : mv + (n - mu - mv - 1 - r) = (n - 1 - (mu + i)) + p * (i / p) := by
          have hdm : p * (i / p) + i % p = i := Nat.div_add_mod i p
          rw [himod] at hdm
          set pq := p * (i / p); omega
        rw [hidx]; exact (hv_p (n - 1 - (mu + i)) (i / p) (by omega)).symm
      rw [hu_eq, hv_eq]
    -- replace bit by the constant; factor it out
    rw [Finset.sum_congr rfl (fun i hi => if_congr
      (and_congr_right (fun _ => and_congr_right (fun _ => hconst i hi))) rfl rfl)]
    have hpull : ∀ i, (if lo n ≤ ((mu + i : ℕ) : ℤ) ∧ ((mu + i : ℕ) : ℤ) < hi n
          ∧ b (u (mu + r)) (v (mv + (n - mu - mv - 1 - r))) then (1 : ℕ) else 0)
        = (if lo n ≤ ((mu + i : ℕ) : ℤ) ∧ ((mu + i : ℕ) : ℤ) < hi n then 1 else 0)
          * (if b (u (mu + r)) (v (mv + (n - mu - mv - 1 - r))) then 1 else 0) := by
      intro i
      rw [← ite_and_mul]
      exact if_congr and_assoc.symm rfl rfl
    rw [Finset.sum_congr rfl (fun i _ => hpull i), ← Finset.sum_mul]
    have hC_eq : (∑ i ∈ (Finset.range (n - mu - mv)).filter (fun i => i % p = r),
          (if lo n ≤ ((mu + i : ℕ) : ℤ) ∧ ((mu + i : ℕ) : ℤ) < hi n then (1 : ℕ) else 0))
        = Cr r n := by
      simp only [hCrdef]
      rw [Finset.card_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h1 : i % p = r
      · by_cases h2 : (lo n ≤ ((mu + i : ℕ) : ℤ) ∧ ((mu + i : ℕ) : ℤ) < hi n) <;> simp_all
      · simp [h1]
    rw [hC_eq]
  -- assemble
  refine AffineOnResidues.congr_eventually (N := mu + mv) (fun n hn => ?_)
    ((hFB.add hBK).add hBB)
  rw [Finset.card_filter,
    ← Finset.sum_range_add_sum_Ico _ (show mu ≤ n from by omega),
    ← Finset.sum_Ico_consecutive _ (show mu ≤ n - mv from by omega) (show n - mv ≤ n from by omega),
    eBK n hn, eBB n (by omega)]
  ring

set_option maxHeartbeats 1000000 in
/-- **The gated lex-convolution kernel (abstract).**  The lex analogue of
`affineOnResidues_gatedConvolution`: for eventually-periodic iterates `u`, `v`, a bit
`b`, a rank `R : ℕ → Fin d → ℤ` satisfying a period-`pR` recurrence (slope `PR`), and a
threshold `T : ℕ → Fin d → ℤ` affine-on-residues per coordinate, the count of loop-indices
`j < n` with `lexLt (R j) (T n)` and bit `b (u j) (v (n-1-j))` on is `AffineOnResidues` in
`n`.  Same skeleton as the interval kernel — peel the forward boundary `j < M0` and backward
boundary `j > n-1-mv` as finite per-index affine terms (lex indicators), and on the bulk
regroup by residue mod `p = pu·pv·pR`, on which the bit is constant and the per-fibre lex
count (the rank is then affine in the period index) is `countLexL_residueIndex`. -/
theorem affineOnResidues_gatedLexConvolution {α β : Type*} {d : ℕ}
    (u : ℕ → α) (v : ℕ → β) (b : α → β → Prop)
    {mu pu : ℕ} (hpu : 1 ≤ pu) (hu : ∀ i, mu ≤ i → u (i + pu) = u i)
    {mv pv : ℕ} (hpv : 1 ≤ pv) (hv : ∀ j, mv ≤ j → v (j + pv) = v j)
    (R : ℕ → Fin d → ℤ) {mR pR : ℕ} (PR : Fin d → ℤ) (hpR : 1 ≤ pR)
    (hR : ∀ j, mR ≤ j → R (j + pR) = R j + PR)
    (T : ℕ → Fin d → ℤ) (hT : ∀ i, AffineOnResiduesZ (fun n => T n i)) :
    AffineOnResidues (fun n => ((Finset.range n).filter
      (fun j : ℕ => WRP.lexLt (R j) (T n) ∧ b (u j) (v (n - 1 - j)))).card) := by
  classical
  -- periodicity helpers for u, v
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
  -- the rank slope per residue at period p
  set sl : Fin d → ℤ := (pu * pv) • PR with hsldef
  have hR_p : ∀ s t, mR ≤ s → R (s + p * t) = R s + t • sl := by
    intro s t hs
    rw [hpdef, show pu * pv * pR * t = pR * (pu * pv * t) from by ring, hR_iter s (pu * pv * t) hs,
      hsldef, smul_smul, Nat.mul_comm]
  -- the general lex indicator: lexLt (C n) (T n) for an AffineOnResiduesZ-per-coord C
  have hlexIndV : ∀ (C : ℕ → Fin d → ℤ), (∀ i, AffineOnResiduesZ (fun n => C n i)) →
      AffineOnResidues (fun n => if WRP.lexLt (C n) (T n) then 1 else 0) := by
    intro C hC
    have hAs : ∀ f ∈ List.ofFn (fun i : Fin d => (fun n => C n i)),
        AffineOnResiduesZ f := by
      intro f hf; rw [List.mem_ofFn] at hf; obtain ⟨i, rfl⟩ := hf; exact hC i
    have hBs : ∀ f ∈ List.ofFn (fun i : Fin d => (fun n => T n i)),
        AffineOnResiduesZ f := by
      intro f hf; rw [List.mem_ofFn] at hf; obtain ⟨i, rfl⟩ := hf; exact hT i
    refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_)
      (lexLtL_indicator (List.ofFn (fun i : Fin d => (fun n => C n i)))
        (List.ofFn (fun i : Fin d => (fun n => T n i))) hAs hBs)
    refine if_congr ?_ rfl rfl
    rw [List.map_ofFn, List.map_ofFn, ← lexLt_iff_lexLtL]
    rfl
  -- the gated lex indicator (lex ∧ bit)
  have gatedLex : ∀ (C : ℕ → Fin d → ℤ), (∀ i, AffineOnResiduesZ (fun n => C n i)) →
      ∀ (Bit : ℕ → Prop), AffineOnResidues (fun n => if Bit n then 1 else 0) →
      AffineOnResidues (fun n => if WRP.lexLt (C n) (T n) ∧ Bit n then 1 else 0) := by
    intro C hC Bit hBit
    have heq : (fun n => if WRP.lexLt (C n) (T n) ∧ Bit n then (1 : ℕ) else 0)
        = (fun n => (if WRP.lexLt (C n) (T n) then 1 else 0) * (if Bit n then 1 else 0)) := by
      funext n; rw [ite_and_mul]
    rw [heq]
    exact affineOnResidues_mul_bddOne (hlexIndV C hC) hBit (fun n => by split <;> simp)
  -- forward boundary `j < M0`
  have hFB : AffineOnResidues (fun n => ∑ j ∈ Finset.range M0,
      (if WRP.lexLt (R j) (T n) ∧ b (u j) (v (n - 1 - j)) then 1 else 0)) := by
    apply AffineOnResidues.finsetSum
    intro j _
    refine gatedLex (fun _ => R j) (fun i => AffineOnResiduesZ.const _)
      (fun n => b (u j) (v (n - 1 - j))) ?_
    refine affineOnResidues_of_eventuallyPeriodic (m := mv + j + 1) (p := pv) hpv (fun n hn => ?_)
    have he : v (n + pv - 1 - j) = v (n - 1 - j) := by
      rw [show n + pv - 1 - j = (n - 1 - j) + pv from by omega]; exact hv _ (by omega)
    exact if_congr (by simp only [he]) rfl rfl
  -- backward boundary `j > n-1-mv`, reindexed `j = n-mv+i`
  have hBB : AffineOnResidues (fun n => ∑ i ∈ Finset.range mv,
      (if WRP.lexLt (R (n - mv + i)) (T n)
        ∧ b (u (n - mv + i)) (v (n - 1 - (n - mv + i))) then 1 else 0)) := by
    apply AffineOnResidues.finsetSum
    intro i hi_mem
    rw [Finset.mem_range] at hi_mem
    refine AffineOnResidues.congr_eventually (N := mR + mv + i + 1) (fun n hn => ?_)
      (gatedLex (fun n => R (n - mv + i)) ?_
        (fun n => b (u (n - mv + i)) (v (mv - 1 - i))) ?_)
    · have e2 : v (n - 1 - (n - mv + i)) = v (mv - 1 - i) := by
        rw [show n - 1 - (n - mv + i) = mv - 1 - i from by omega]
      rw [e2]
    · -- R (n - mv + i) is AffineOnResiduesZ per coord (recurrence at pR)
      intro c
      refine ⟨mR + mv, pR, fun _ => PR c, hpR, fun r k => ?_⟩
      show R (mR + mv + r + pR * k - mv + i) c = R (mR + mv + r - mv + i) c + k * PR c
      rw [show mR + mv + r + pR * k - mv + i = (mR + r + i) + pR * k from by omega,
        hR_iter (mR + r + i) k (by omega),
        show mR + mv + r - mv + i = mR + r + i from by omega]
      simp [Pi.add_apply, nsmul_eq_mul, mul_comm]
    · refine affineOnResidues_of_eventuallyPeriodic (m := mu + mv + i + 1) (p := pu) hpu
        (fun n hn => ?_)
      have he : u (n + pu - mv + i) = u (n - mv + i) := by
        rw [show n + pu - mv + i = (n - mv + i) + pu from by omega]; exact hu _ (by omega)
      exact if_congr (by simp only [he]) rfl rfl
  -- bulk pieces
  set Lr : ℕ → List (ℤ × ℤ) := fun r => List.ofFn (fun c : Fin d => (R (M0 + r) c, sl c))
    with hLrdef
  set Tlist : List (ℕ → ℤ) := List.ofFn (fun c : Fin d => (fun n => T n c)) with hTlistdef
  have hTlistA : ∀ f ∈ Tlist, AffineOnResiduesZ f := by
    intro f hf; rw [hTlistdef, List.mem_ofFn] at hf; obtain ⟨c, rfl⟩ := hf; exact hT c
  set Cr : ℕ → ℕ → ℕ := fun r n => ((Finset.range (n - M0 - mv)).filter
    (fun i : ℕ => i % p = r ∧ lexLtL ((Lr r).map (fun bp => bp.1 + (((i - r) / p : ℕ) : ℤ) * bp.2))
      (Tlist.map (fun f => f n)))).card with hCrdef
  set Ibeta : ℕ → ℕ → ℕ := fun r n =>
    if b (u (M0 + r)) (v (mv + (n - M0 - mv - 1 - r))) then 1 else 0 with hIbetadef
  have hNaff : AffineOnResidues (fun n => n - M0 - mv) := by
    have heq : (fun n => n - M0 - mv) = (fun n => n - (M0 + mv)) := by funext n; rw [Nat.sub_sub]
    rw [heq]; exact affineOnResidues_id.shift (M0 + mv)
  have hCr : ∀ r, r < p → AffineOnResidues (fun n => Cr r n) := by
    intro r hr
    exact countLexL_residueIndex r p hr (Lr r) Tlist hTlistA hNaff
  have hBK : AffineOnResidues (fun n => ∑ r ∈ Finset.range p, Cr r n * Ibeta r n) := by
    apply AffineOnResidues.finsetSum
    intro r hr_mem
    rw [Finset.mem_range] at hr_mem
    refine affineOnResidues_mul_bddOne (hCr r hr_mem) ?_ (fun n => by simp only [hIbetadef]; split_ifs <;> omega)
    rw [hIbetadef]
    refine affineOnResidues_of_eventuallyPeriodic (m := M0 + mv + 1 + r) (p := p) hp (fun n hn => ?_)
    have key : v (mv + (n + p - M0 - mv - 1 - r)) = v (mv + (n - M0 - mv - 1 - r)) := by
      rw [show mv + (n + p - M0 - mv - 1 - r) = (mv + (n - M0 - mv - 1 - r)) + p * 1 from by omega]
      exact hv_p (mv + (n - M0 - mv - 1 - r)) 1 (by omega)
    exact if_congr (by rw [key]) rfl rfl
  -- backward-boundary reindex identity
  have eBB : ∀ n, mv ≤ n →
      (∑ j ∈ Finset.Ico (n - mv) n,
        (if WRP.lexLt (R j) (T n) ∧ b (u j) (v (n - 1 - j)) then (1 : ℕ) else 0))
      = ∑ i ∈ Finset.range mv,
        (if WRP.lexLt (R (n - mv + i)) (T n)
          ∧ b (u (n - mv + i)) (v (n - 1 - (n - mv + i))) then 1 else 0) := by
    intro n _
    rw [Finset.sum_Ico_eq_sum_range, show n - (n - mv) = mv from by omega]
  -- bulk identity
  have eBK : ∀ n, M0 + mv ≤ n →
      (∑ j ∈ Finset.Ico M0 (n - mv),
        (if WRP.lexLt (R j) (T n) ∧ b (u j) (v (n - 1 - j)) then (1 : ℕ) else 0))
      = ∑ r ∈ Finset.range p, Cr r n * Ibeta r n := by
    intro n hn
    rw [Finset.sum_Ico_eq_sum_range, show n - mv - M0 = n - M0 - mv from by omega,
      ← Finset.sum_fiberwise_of_maps_to (t := Finset.range p) (g := fun i => i % p)
        (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hp))]
    apply Finset.sum_congr rfl
    intro r hr_mem
    rw [Finset.mem_range] at hr_mem
    -- rewrite the per-i term: lex(R(M0+i)) via the residue reindex, bit constant on the fibre
    have hbody : ∀ i ∈ (Finset.range (n - M0 - mv)).filter (fun i => i % p = r),
        (if WRP.lexLt (R (M0 + i)) (T n) ∧ b (u (M0 + i)) (v (n - 1 - (M0 + i))) then (1 : ℕ) else 0)
        = (if lexLtL ((Lr r).map (fun bp => bp.1 + (((i - r) / p : ℕ) : ℤ) * bp.2))
              (Tlist.map (fun f => f n)) then 1 else 0)
          * (if b (u (M0 + r)) (v (mv + (n - M0 - mv - 1 - r))) then 1 else 0) := by
      intro i hi_mem
      rw [Finset.mem_filter, Finset.mem_range] at hi_mem
      obtain ⟨hilt, himod⟩ := hi_mem
      have hik : (i - r) / p = i / p := by
        have hdm := Nat.div_add_mod i p; rw [show i - r = p * (i / p) from by omega,
          Nat.mul_div_cancel_left _ hp]
      have hidx : M0 + i = (M0 + r) + p * (i / p) := by
        have hdm := Nat.div_add_mod i p; omega
      -- lex equivalence
      have hlexeq : WRP.lexLt (R (M0 + i)) (T n)
          ↔ lexLtL ((Lr r).map (fun bp => bp.1 + (((i - r) / p : ℕ) : ℤ) * bp.2))
              (Tlist.map (fun f => f n)) := by
        rw [lexLt_iff_lexLtL, hLrdef, hTlistdef, List.map_ofFn, List.map_ofFn]
        refine Iff.of_eq (congrArg₂ lexLtL (congrArg List.ofFn (funext fun c => ?_)) rfl)
        show R (M0 + i) c = R (M0 + r) c + (((i - r) / p : ℕ) : ℤ) * sl c
        rw [hidx, hR_p (M0 + r) (i / p) (by omega), hik]
        simp [Pi.add_apply, nsmul_eq_mul, mul_comm]
      -- bit constancy on the fibre
      have hu_eq : u (M0 + i) = u (M0 + r) := by
        rw [hidx]; exact hu_p (M0 + r) (i / p) (by omega)
      have hv_eq : v (n - 1 - (M0 + i)) = v (mv + (n - M0 - mv - 1 - r)) := by
        have hidx2 : mv + (n - M0 - mv - 1 - r) = (n - 1 - (M0 + i)) + p * (i / p) := by
          have hdm := Nat.div_add_mod i p; omega
        rw [hidx2]; exact (hv_p (n - 1 - (M0 + i)) (i / p) (by omega)).symm
      rw [hu_eq, hv_eq, ← ite_and_mul]
      exact if_congr (and_congr_left (fun _ => hlexeq)) rfl rfl
    rw [Finset.sum_congr rfl hbody, ← Finset.sum_mul]
    refine congrArg₂ (· * ·) ?_ rfl
    simp only [hCrdef]
    rw [← Finset.filter_filter, Finset.card_filter]
  -- assemble
  refine AffineOnResidues.congr_eventually (N := M0 + mv) (fun n hn => ?_)
    ((hFB.add hBK).add hBB)
  rw [Finset.card_filter,
    ← Finset.sum_range_add_sum_Ico _ (show M0 ≤ n from by omega),
    ← Finset.sum_Ico_consecutive _ (show M0 ≤ n - mv from by omega) (show n - mv ≤ n from by omega),
    eBK n hn, eBB n (by omega)]
  ring

end SliceGatedConv
