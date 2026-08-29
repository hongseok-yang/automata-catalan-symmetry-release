/-
# The bounded fibred rank slopes (§9 tower, F3.9 prep)

The bounded variants of the rank-decomposition chain: the rank slope `PR`/`PBn`
is bounded by an `mS`-FREE constant (the block-cycle weight bound from
`SlicePeriodStar.affineOnResidues_of_blockIterate_func_bounded`).  This is what
lets the strict/tie counts pin at the `mS`-free period `RowAffine` demands.

This file currently lands `summand_copied_families_recurrence_bounded` (level 1
of the propagation): all four family slopes are `s.coeff • (p₂ • Pw)` with the
SAME `Pw` (the block-cycle slope), bounded by `s.coeff.natAbs * p₂ * SPw`.
-/
import RequestProject.CopiedSetup
import RequestProject.CopiedSlopeBound

namespace CopiedSetup

open WRP Step SliceRankAtom SliceRank SliceFamilyRank SliceFamilyCell CopiedCells CopiedRank
  CopiedDstar MSOMarkN SliceMarkN
open scoped Classical

variable {d : ℕ}

/-- **The bounded family recurrence** (level 1): the same four block families as
`summand_copied_families_recurrence`, with each slope `Pv` bounded per-coordinate
by the `mS`-FREE `SP` (all four share the block-cycle slope `s.coeff • (p₂ • Pw)`,
bounded via the atomic `affineOnResidues_of_blockIterate_func_bounded`). -/
theorem summand_copied_families_recurrence_bounded {k : ℕ} (s : Summand Step d k) :
    ∃ (m p : ℕ) (SP : Fin d → ℕ), 1 ≤ p ∧ ∀ mS, 1 ≤ mS →
      (∃ Pv : Fin d → ℤ, (∀ j, m ≤ j →
        s.eval (copiedSlice mS (j + p + 1)) (fun _ => mS + 2 * (j + p))
          = s.eval (copiedSlice mS (j + 1)) (fun _ => mS + 2 * j) + Pv)
        ∧ ∀ c, (Pv c).natAbs ≤ SP c) ∧
      (∃ Pv : Fin d → ℤ, (∀ j, m ≤ j →
        s.eval (copiedSlice mS (j + p + 1)) (fun _ => mS + 2 * (j + p) + 1)
          = s.eval (copiedSlice mS (j + 1)) (fun _ => mS + 2 * j + 1) + Pv)
        ∧ ∀ c, (Pv c).natAbs ≤ SP c) ∧
      (∃ Pv : Fin d → ℤ, (∀ n, m ≤ n →
        s.eval (copiedSlice mS (n + p)) (fun _ => mS + 2 * (n + p))
          = s.eval (copiedSlice mS n) (fun _ => mS + 2 * n) + Pv)
        ∧ ∀ c, (Pv c).natAbs ≤ SP c) ∧
      (∀ l, l < mS - 1 → ∃ Pv : Fin d → ℤ, (∀ n, m ≤ n →
        s.eval (copiedSlice mS (n + p)) (fun _ => mS + 2 * (n + p) + 1 + l)
          = s.eval (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l) + Pv)
        ∧ ∀ c, (Pv c).natAbs ≤ SP c) := by
  have := s.A.fintypeQ
  obtain ⟨m₁, p₁, SPw, hp₁, htwin⟩ :=
    SlicePeriodStar.affineOnResidues_of_blockIterate_func_bounded
      (fun q => List.foldl s.A.δ q [U, D])
      (fun q => (List.foldl (SliceRank.rankStep s.A) (q, 0) [U, D]).2)
  obtain ⟨m₂, p₂, hp₂, hEPf⟩ := func_iterate_EP (fun q => List.foldl s.A.δ q [U, D])
  refine ⟨max m₁ m₂, p₁ * p₂, fun c => s.coeff.natAbs * p₂ * SPw c,
    Nat.one_le_iff_ne_zero.mpr (by positivity), fun mS hm => ?_⟩
  set q₁ : s.A.Q := List.foldl s.A.δ s.A.q0 (List.replicate mS U) with hq₁
  have hrank : ∀ j, s.A.prefixRank
      (List.replicate mS U ++ (List.replicate j [U, D]).flatten)
      (List.replicate mS U ++ (List.replicate j [U, D]).flatten).length
      = (List.foldl (SliceRank.rankStep s.A) (s.A.q0, 0)
          (List.replicate mS U)).2
        + ∑ i ∈ Finset.range j,
            (fun q => (List.foldl (SliceRank.rankStep s.A) (q, 0) [U, D]).2)
              ((fun q => List.foldl s.A.δ q [U, D])^[i] q₁) := by
    intro j
    rw [SliceRank.prefixRank_eq_foldl, List.foldl_append,
      SliceRank.foldl_rankStep_replicate_snd,
      show (List.foldl (SliceRank.rankStep s.A) (s.A.q0, 0)
        (List.replicate mS U)).1 = q₁ from
        SliceRank.rankStep_fst s.A s.A.q0 0 _]
    rfl
  obtain ⟨Pw, hPw, hPwb⟩ := htwin q₁
  have hS : ∀ j, m₁ ≤ j →
      (∑ i ∈ Finset.range (j + p₁),
        (fun q => (List.foldl (SliceRank.rankStep s.A) (q, 0) [U, D]).2)
          ((fun q => List.foldl s.A.δ q [U, D])^[i] q₁))
      = (∑ i ∈ Finset.range j,
          (fun q => (List.foldl (SliceRank.rankStep s.A) (q, 0) [U, D]).2)
            ((fun q => List.foldl s.A.δ q [U, D])^[i] q₁)) + Pw :=
    recurrence_of_pre_blocks' (S := fun n => ∑ i ∈ Finset.range n,
      (fun q => (List.foldl (SliceRank.rankStep s.A) (q, 0) [U, D]).2)
        ((fun q => List.foldl s.A.δ q [U, D])^[i] q₁)) hp₁ hPw
  have hSmul : ∀ j, m₁ ≤ j →
      (∑ i ∈ Finset.range (j + p₁ * p₂),
        (fun q => (List.foldl (SliceRank.rankStep s.A) (q, 0) [U, D]).2)
          ((fun q => List.foldl s.A.δ q [U, D])^[i] q₁))
      = (∑ i ∈ Finset.range j,
          (fun q => (List.foldl (SliceRank.rankStep s.A) (q, 0) [U, D]).2)
            ((fun q => List.foldl s.A.δ q [U, D])^[i] q₁)) + p₂ • Pw :=
    fun j hj => RankAffine.iterate (F := fun n => ∑ i ∈ Finset.range n,
      (fun q => (List.foldl (SliceRank.rankStep s.A) (q, 0) [U, D]).2)
        ((fun q => List.foldl s.A.δ q [U, D])^[i] q₁)) hS j p₂ hj
  have hPF : ∀ j, m₁ ≤ j →
      s.A.prefixRank (List.replicate mS U
          ++ (List.replicate (j + p₁ * p₂) [U, D]).flatten)
        (List.replicate mS U
          ++ (List.replicate (j + p₁ * p₂) [U, D]).flatten).length
      = s.A.prefixRank (List.replicate mS U ++ (List.replicate j [U, D]).flatten)
          (List.replicate mS U ++ (List.replicate j [U, D]).flatten).length
        + p₂ • Pw := by
    intro j hj
    rw [hrank, hrank, hSmul j hj]
    abel
  have hit : ∀ j, m₂ ≤ j →
      (fun q => List.foldl s.A.δ q [U, D])^[j + p₁ * p₂]
        = (fun q => List.foldl s.A.δ q [U, D])^[j] := by
    intro j hj
    have h := func_EP_mul hEPf p₁ j hj
    rwa [Nat.mul_comm p₂ p₁] at h
  -- the shared slope bound
  have hslopebound : ∀ c, ((s.coeff • (p₂ • Pw)) c).natAbs ≤ s.coeff.natAbs * p₂ * SPw c := by
    intro c
    show (s.coeff * ((p₂ : ℤ) * Pw c)).natAbs ≤ s.coeff.natAbs * p₂ * SPw c
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
    have := hPwb c
    calc s.coeff.natAbs * (p₂ * (Pw c).natAbs)
        ≤ s.coeff.natAbs * (p₂ * SPw c) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
      _ = s.coeff.natAbs * p₂ * SPw c := by ring
  refine ⟨⟨s.coeff • (p₂ • Pw), fun j hj => ?_, hslopebound⟩,
    ⟨s.coeff • (p₂ • Pw), fun j hj => ?_, hslopebound⟩,
    ⟨s.coeff • (p₂ • Pw), fun n hn => ?_, hslopebound⟩,
    fun l hl => ⟨s.coeff • (p₂ • Pw), fun n hn => ?_, hslopebound⟩⟩
  · rw [CopiedRank.summand_copied_block_eq s mS (j + p₁ * p₂) hm,
      CopiedRank.summand_copied_block_eq s mS j hm, hPF j (by omega),
      hit j (by omega), smul_add]
    abel
  · rw [CopiedRank.summand_copied_blockD_eq s mS (j + p₁ * p₂) hm,
      CopiedRank.summand_copied_blockD_eq s mS j hm, hPF j (by omega),
      hit j (by omega), add_right_comm, smul_add]
    abel
  · rw [CopiedRank.summand_copied_suf_eq s mS (n + p₁ * p₂) hm,
      CopiedRank.summand_copied_suf_eq s mS n hm, hPF n (by omega),
      hit n (by omega), smul_add]
    abel
  · rw [CopiedRank.summand_copied_sufStretch_eq s mS l hl (n + p₁ * p₂),
      CopiedRank.summand_copied_sufStretch_eq s mS l hl n,
      prefixRank_tail_split s.A (List.replicate mS U) [U, D]
        (List.replicate (l + 1) D) (n + p₁ * p₂),
      prefixRank_tail_split s.A (List.replicate mS U) [U, D]
        (List.replicate (l + 1) D) n,
      hPF n (by omega), hit n (by omega)]
    simp only [smul_add]
    abel

/-! ## Level 2: the bounded region decomposition -/

/-- **Bounded region decomposition** (level 2): same as
`summand_region_decomp_fibred_uniform`, with both region slopes `PRs`, `PBs`
bounded per-coordinate by the `mS`-FREE `SP` of the bounded family recurrence
(each slope is `0` or one of the four family slopes, all `≤ SP`). -/
theorem summand_region_decomp_fibred_uniform_bounded {B k : ℕ} (s : Summand Step d k) :
    ∃ (m p : ℕ) (SP : Fin d → ℕ), 1 ≤ p ∧ B + 1 ≤ m ∧
      ∀ mS, 1 ≤ mS → ∀ r : RegionSpecF B, r.valid mS →
      ∃ (Rs Bs : ℕ → Fin d → ℤ) (PRs PBs : Fin d → ℤ),
        (∀ t, m ≤ t → Rs (t + p) = Rs t + PRs) ∧
        (∀ n, m ≤ n → Bs (n + p) = Bs n + PBs) ∧
        (∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
          s.eval (copiedSlice mS n) (fun _ => r.posAt mS t n)
            = fun c => Rs t c + Bs n c) ∧
        (∀ c, (PRs c).natAbs ≤ SP c) ∧ (∀ c, (PBs c).natAbs ≤ SP c) := by
  obtain ⟨m₀, p₀, SP, hp₀, hfam⟩ :=
    summand_copied_families_recurrence_bounded (k := k) s
  refine ⟨m₀ + B + 1, p₀, SP, hp₀, by omega, fun mS hm r hv => ?_⟩
  obtain ⟨⟨PU, hU, hUb⟩, ⟨PD, hD, hDb⟩, ⟨PS, hSuf, hSb⟩, hStr⟩ := hfam mS hm
  have hzero : ∀ c, ((0 : Fin d → ℤ) c).natAbs ≤ SP c := fun c => by simp
  rcases r with r | q | l
  case prefIdx =>
    have hq : q < mS - 1 := hv
    refine ⟨fun _ => s.eval (copiedSlice mS 0) (fun _ => q), fun _ => 0, 0, 0,
      (by intro t _; simp), (by intro n _; simp), fun t n _ _ => ?_, hzero, hzero⟩
    show s.eval (copiedSlice mS n) (fun _ => q) = _
    rw [CopiedRank.summand_copied_pref_stable s mS q n 0 hm (by omega)]
    funext c
    simp
  case sufIdx =>
    have hlv : l < mS - 1 := hv
    obtain ⟨PSl, hSl, hSlb⟩ := hStr l hlv
    refine ⟨fun _ => 0,
      fun n => s.eval (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l),
      0, PSl, (by intro t _; simp), fun n hn => hSl n (by omega),
      fun t n _ _ => ?_, hzero, hSlb⟩
    show s.eval (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l) = _
    funext c
    simp
  case core =>
    rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
    · -- pre
      refine ⟨fun _ => s.eval (copiedSlice mS 0) (fun _ => mS - 1 + 0),
        fun _ => 0, 0, 0, (by intro t _; simp), (by intro n _; simp),
        fun t n _ _ => ?_, hzero, hzero⟩
      show s.eval (copiedSlice mS n) (fun _ => mS - 1 + 0) = _
      rw [CopiedRank.summand_copied_mid_stable s mS 0 n 0 hm (by omega) (by omega)]
      funext c
      simp
    · -- suf
      refine ⟨fun _ => 0,
        fun n => s.eval (copiedSlice mS n) (fun _ => mS + 2 * n),
        0, PS, (by intro t _; simp), fun n hn => hSuf n (by omega),
        fun t n _ _ => ?_, hzero, hSb⟩
      have hpos : mS - 1 + (1 + 2 * n) = mS + 2 * n := by omega
      show s.eval (copiedSlice mS n) (fun _ => mS - 1 + (1 + 2 * n)) = _
      rw [hpos]
      funext c
      simp
    · -- front-pinned
      rcases e with _ | _
      · refine ⟨fun _ => s.eval (copiedSlice mS (f.val + 1))
            (fun _ => mS - 1 + (1 + 2 * f.val)),
          fun _ => 0, 0, 0, (by intro t _; simp), (by intro n _; simp),
          fun t n ht htn => ?_, hzero, hzero⟩
        have hf := f.isLt
        show s.eval (copiedSlice mS n) (fun _ => mS - 1 + (1 + 2 * f.val)) = _
        rw [CopiedRank.summand_copied_mid_stable s mS (1 + 2 * f.val) n (f.val + 1) hm
          (by omega) (by omega)]
        funext c
        simp
      · refine ⟨fun _ => s.eval (copiedSlice mS (f.val + 1))
            (fun _ => mS - 1 + (1 + 2 * f.val + 1)),
          fun _ => 0, 0, 0, (by intro t _; simp), (by intro n _; simp),
          fun t n ht htn => ?_, hzero, hzero⟩
        have hf := f.isLt
        show s.eval (copiedSlice mS n)
          (fun _ => mS - 1 + (1 + 2 * f.val + 1)) = _
        rw [CopiedRank.summand_copied_mid_stable s mS (1 + 2 * f.val + 1) n (f.val + 1) hm
          (by omega) (by omega)]
        funext c
        simp
    · -- back-pinned
      rcases e with _ | _
      · refine ⟨fun _ => 0,
          fun n => s.eval (copiedSlice mS (n - (1 + l.val) + 1))
            (fun _ => mS + 2 * (n - (1 + l.val))),
          0, PU, (by intro t _; simp), ?_, fun t n ht htn => ?_, hzero, hUb⟩
        · intro n hn
          have hlB := l.isLt
          have harg : n + p₀ - (1 + l.val) = (n - (1 + l.val)) + p₀ := by omega
          show s.eval (copiedSlice mS (n + p₀ - (1 + l.val) + 1))
            (fun _ => mS + 2 * (n + p₀ - (1 + l.val))) = _
          rw [harg]
          exact hU (n - (1 + l.val)) (by omega)
        · have hlB := l.isLt
          have harg : n - 1 - l.val = n - (1 + l.val) := by omega
          have hpos : mS - 1 + (1 + 2 * (n - (1 + l.val)))
              = mS + 2 * (n - (1 + l.val)) := by omega
          show s.eval (copiedSlice mS n)
            (fun _ => mS - 1 + (1 + 2 * (n - 1 - l.val))) = _
          rw [harg, CopiedRank.summand_copied_mid_stable s mS (1 + 2 * (n - (1 + l.val)))
            n (n - (1 + l.val) + 1) hm (by omega) (by omega), hpos]
          funext c
          simp
      · refine ⟨fun _ => 0,
          fun n => s.eval (copiedSlice mS (n - (1 + l.val) + 1))
            (fun _ => mS + 2 * (n - (1 + l.val)) + 1),
          0, PD, (by intro t _; simp), ?_, fun t n ht htn => ?_, hzero, hDb⟩
        · intro n hn
          have hlB := l.isLt
          have harg : n + p₀ - (1 + l.val) = (n - (1 + l.val)) + p₀ := by omega
          show s.eval (copiedSlice mS (n + p₀ - (1 + l.val) + 1))
            (fun _ => mS + 2 * (n + p₀ - (1 + l.val)) + 1) = _
          rw [harg]
          exact hD (n - (1 + l.val)) (by omega)
        · have hlB := l.isLt
          have harg : n - 1 - l.val = n - (1 + l.val) := by omega
          have hpos : mS - 1 + (1 + 2 * (n - (1 + l.val)) + 1)
              = mS + 2 * (n - (1 + l.val)) + 1 := by omega
          show s.eval (copiedSlice mS n)
            (fun _ => mS - 1 + (1 + 2 * (n - 1 - l.val) + 1)) = _
          rw [harg, CopiedRank.summand_copied_mid_stable s mS
            (1 + 2 * (n - (1 + l.val)) + 1) n (n - (1 + l.val) + 1) hm
            (by omega) (by omega), hpos]
          funext c
          simp
    · -- cluster
      rcases e with _ | _
      · refine ⟨fun t => s.eval (copiedSlice mS (t + δ.val + 1))
            (fun _ => mS + 2 * (t + δ.val)),
          fun _ => 0, PU, 0, ?_, (by intro n _; simp),
          fun t n ht htn => ?_, hUb, hzero⟩
        · intro t ht
          have harg : t + p₀ + δ.val = (t + δ.val) + p₀ := by omega
          show s.eval (copiedSlice mS (t + p₀ + δ.val + 1))
            (fun _ => mS + 2 * (t + p₀ + δ.val)) = _
          rw [harg]
          exact hU (t + δ.val) (by omega)
        · have hδ := δ.isLt
          have hpos : mS - 1 + (1 + 2 * (t + δ.val))
              = mS + 2 * (t + δ.val) := by omega
          show s.eval (copiedSlice mS n)
            (fun _ => mS - 1 + (1 + 2 * (t + δ.val))) = _
          rw [CopiedRank.summand_copied_mid_stable s mS (1 + 2 * (t + δ.val)) n
            (t + δ.val + 1) hm (by omega) (by omega), hpos]
          funext c
          simp
      · refine ⟨fun t => s.eval (copiedSlice mS (t + δ.val + 1))
            (fun _ => mS + 2 * (t + δ.val) + 1),
          fun _ => 0, PD, 0, ?_, (by intro n _; simp),
          fun t n ht htn => ?_, hDb, hzero⟩
        · intro t ht
          have harg : t + p₀ + δ.val = (t + δ.val) + p₀ := by omega
          show s.eval (copiedSlice mS (t + p₀ + δ.val + 1))
            (fun _ => mS + 2 * (t + p₀ + δ.val) + 1) = _
          rw [harg]
          exact hD (t + δ.val) (by omega)
        · have hδ := δ.isLt
          have hpos : mS - 1 + (1 + 2 * (t + δ.val) + 1)
              = mS + 2 * (t + δ.val) + 1 := by omega
          show s.eval (copiedSlice mS n)
            (fun _ => mS - 1 + (1 + 2 * (t + δ.val) + 1)) = _
          rw [CopiedRank.summand_copied_mid_stable s mS (1 + 2 * (t + δ.val) + 1) n
            (t + δ.val + 1) hm (by omega) (by omega), hpos]
          funext c
          simp

/-! ## Level 3: the bounded rank-term decomposition -/

/-- Triangle bound for a list sum of integers: if each term is bounded in
`natAbs` by `h s`, the `natAbs` of the sum is bounded by `∑ h s`. -/
private theorem list_natAbs_sum_bound {ι : Type*} (l : List ι) (f : ι → ℤ)
    (h : ι → ℕ) (hb : ∀ s ∈ l, (f s).natAbs ≤ h s) :
    ((l.map f).sum).natAbs ≤ (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    refine le_trans (Int.natAbs_add_le _ _) ?_
    exact Nat.add_le_add (hb a (List.mem_cons.mpr (Or.inl rfl)))
      (ih (fun s hs => hb s (List.mem_cons.mpr (Or.inr hs))))

/-- Per-coordinate distribution of a list-sum recurrence (local copy of the
file-private `CopiedSetup.pi_list_sum_recurrence`). -/
private theorem pi_list_sum_recurrence {ι : Type*} (l : List ι)
    (F G H : ι → Fin d → ℤ) (h : ∀ s ∈ l, F s = G s + H s) :
    (l.map F).sum = (l.map G).sum + (l.map H).sum := by
  funext c
  show ((l.map F).sum) c = ((l.map G).sum + (l.map H).sum) c
  rw [Pi.add_apply, list_sum_pi_apply l F c, list_sum_pi_apply l G c,
    list_sum_pi_apply l H c, ← list_sum_map_add]
  refine congrArg List.sum (List.map_congr_left (fun s hs => ?_))
  rw [h s hs]
  rfl

/-- **Bounded rank-term decomposition** (level 3): both rank-term slopes `PR`,
`PBn` (sums of the rescaled region slopes) are bounded per-coordinate by the
`mS`-FREE `SP c = ∑_s (p₀ / ps s) · SPs s c`, via the triangle bound and the
level-2 region bounds. -/
theorem rankTerm_cell_decomp_fibred_uniform_bounded {B k : ℕ} (κ : RankTerm Step d k) :
    ∃ (m p : ℕ) (SP : Fin d → ℕ), 1 ≤ p ∧ B + 1 ≤ m ∧
      ∀ mS, 1 ≤ mS → ∀ rs : Fin k → RegionSpecF B, (∀ i, (rs i).valid mS) →
      ∃ (R Bn : ℕ → Fin d → ℤ) (PR PBn : Fin d → ℤ),
        (∀ t, m ≤ t → R (t + p) = R t + PR) ∧
        (∀ n, m ≤ n → Bn (n + p) = Bn n + PBn) ∧
        (∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
          κ.eval (copiedSlice mS n) (fun i => (rs i).posAt mS t n)
            = fun c => R t c + Bn n c) ∧
        (∀ c, (PR c).natAbs ≤ SP c) ∧ (∀ c, (PBn c).natAbs ≤ SP c) := by
  classical
  choose ms ps SPs hps hmsB huni using
    fun s : Summand Step d k => summand_region_decomp_fibred_uniform_bounded (B := B) s
  obtain ⟨m₀, p₀, hp₀, halign⟩ :=
    uniform_list_align κ.summands ms ps (fun s _ => hps s)
  refine ⟨max m₀ (B + 1), p₀,
    fun c => (κ.summands.map (fun s => (p₀ / ps s) * SPs s c)).sum,
    hp₀, le_max_right _ _, fun mS hm rs hv => ?_⟩
  choose Rs Bs PRs PBs hRrec hBrec heq hPRsb hPBsb using
    fun s : Summand Step d k => huni s mS hm (rs s.π) (hv s.π)
  have hresc : ∀ s ∈ κ.summands, ∀ t, max m₀ (B + 1) ≤ t →
      Rs s (t + p₀) = Rs s t + (p₀ / ps s) • PRs s := by
    intro s hs t ht
    obtain ⟨q, hq⟩ := (halign s hs).2
    rw [hq, Nat.mul_div_cancel_left q (hps s)]
    exact RankAffine.iterate (hRrec s) t q
      (le_trans (le_trans (halign s hs).1 (le_max_left _ _)) ht)
  have hrescB : ∀ s ∈ κ.summands, ∀ n, max m₀ (B + 1) ≤ n →
      Bs s (n + p₀) = Bs s n + (p₀ / ps s) • PBs s := by
    intro s hs n hn
    obtain ⟨q, hq⟩ := (halign s hs).2
    rw [hq, Nat.mul_div_cancel_left q (hps s)]
    exact RankAffine.iterate (hBrec s) n q
      (le_trans (le_trans (halign s hs).1 (le_max_left _ _)) hn)
  refine ⟨fun t => κ.c0 + (κ.summands.map (fun s => Rs s t)).sum,
    fun n => (κ.summands.map (fun s => Bs s n)).sum,
    (κ.summands.map (fun s => (p₀ / ps s) • PRs s)).sum,
    (κ.summands.map (fun s => (p₀ / ps s) • PBs s)).sum, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have h := pi_list_sum_recurrence κ.summands (fun s => Rs s (t + p₀))
      (fun s => Rs s t) (fun s => (p₀ / ps s) • PRs s)
      (fun s hs => hresc s hs t ht)
    show κ.c0 + (κ.summands.map (fun s => Rs s (t + p₀))).sum
      = κ.c0 + (κ.summands.map (fun s => Rs s t)).sum
        + (κ.summands.map (fun s => (p₀ / ps s) • PRs s)).sum
    rw [h]
    abel
  · intro n hn
    exact pi_list_sum_recurrence κ.summands (fun s => Bs s (n + p₀))
      (fun s => Bs s n) (fun s => (p₀ / ps s) • PBs s)
      (fun s hs => hrescB s hs n hn)
  · intro t n ht htn
    rw [rankTerm_eval_proj]
    funext c
    have hsummand : ∀ s ∈ κ.summands,
        s.eval (copiedSlice mS n)
          (fun _ => (fun i => (rs i).posAt mS t n) s.π) c
          = Rs s t c + Bs s n c := by
      intro s _
      rw [heq s t n ht htn]
    calc κ.c0 c + (κ.summands.map (fun s =>
          s.eval (copiedSlice mS n)
            (fun _ => (fun i => (rs i).posAt mS t n) s.π) c)).sum
        = κ.c0 c + (κ.summands.map (fun s => Rs s t c + Bs s n c)).sum := by
          rw [congrArg List.sum (List.map_congr_left hsummand)]
      _ = κ.c0 c + ((κ.summands.map (fun s => Rs s t c)).sum
            + (κ.summands.map (fun s => Bs s n c)).sum) := by
          rw [list_sum_map_add]
      _ = (κ.c0 c + ((κ.summands.map (fun s => Rs s t)).sum) c)
            + ((κ.summands.map (fun s => Bs s n)).sum) c := by
          rw [list_sum_pi_apply, list_sum_pi_apply]
          ring
  · intro c
    rw [list_sum_pi_apply]
    refine list_natAbs_sum_bound κ.summands _ _ (fun s _ => ?_)
    simp only [Pi.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul le_rfl (hPRsb s c)
  · intro c
    rw [list_sum_pi_apply]
    refine list_natAbs_sum_bound κ.summands _ _ (fun s _ => ?_)
    simp only [Pi.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul le_rfl (hPBsb s c)

/-! ## Level 4a: the bounded presentation-level rank decomposition -/

/-- **Bounded presentation-level rank decomposition** (level 4a): the slopes
`PR`, `PBn` are bounded per-coordinate by the `mS`-FREE `SP` inherited from the
bounded rank-term decomposition (the region-graph is just rewritten). -/
theorem rank_cell_decomp_fibred_uniform_bounded {B : ℕ}
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    ∃ (m p : ℕ) (SP : Fin P.d → ℕ), 1 ≤ p ∧ B + 1 ≤ m ∧
      ∀ mS, 1 ≤ mS →
      ∀ rs : Fin (P.toPoly.arity c) → RegionSpecF B, (∀ i, (rs i).valid mS) →
      ∃ (R Bn : ℕ → Fin P.d → ℤ) (PR PBn : Fin P.d → ℤ),
        (∀ t, m ≤ t → R (t + p) = R t + PR) ∧
        (∀ n, m ≤ n → Bn (n + p) = Bn n + PBn) ∧
        (∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
          P.rank c (copiedSlice mS n) (cellTupleF rs mS t n)
            = fun i => R t i + Bn n i) ∧
        (∀ i, (PR i).natAbs ≤ SP i) ∧ (∀ i, (PBn i).natAbs ≤ SP i) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  obtain ⟨m, p, SP, hp, hmB, hterm⟩ :=
    rankTerm_cell_decomp_fibred_uniform_bounded (B := B) κ
  refine ⟨m, p, SP, hp, hmB, fun mS hm rs hv => ?_⟩
  obtain ⟨R, Bn, PR, PBn, h1, h2, h3, hPRb, hPBnb⟩ := hterm mS hm rs hv
  exact ⟨R, Bn, PR, PBn, h1, h2,
    fun t n ht htn => by rw [hκ]; exact h3 t n ht htn, hPRb, hPBnb⟩

/-! ## Level 4b: the bounded fibred setup fold -/

/-- **Bounded fibred stage-1 setup** (level 4b, the F3.9 capstone of the
propagation): identical to `dstar_setup_fibred` but with an `mS`-FREE
per-coordinate bound `SP c rs = (p / pr c) · SPr c` on BOTH cell slopes
`PR c rs`, `PBn c rs`.  This is the bound the strict/tie counts need to pin the
slope-product at the `mS`-free period `RowAffine` demands. -/
theorem dstar_setup_fibred_bounded (P : WRP.Presentation Step Step) (B : ℕ) :
    ∃ (m p : ℕ)
      (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (SP : (c : Fin P.toPoly.K) → Fin P.d → ℕ),
      1 ≤ p ∧ B + 1 ≤ m ∧
      (∀ (c : Fin P.toPoly.K) (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
        (∀ i, ī i < w.length) →
        ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D))) ∧
      (∀ (c : Fin P.toPoly.K) (g : ℕ), m ≤ g →
        (bFN (Mc c))^[g + p] = (bFN (Mc c))^[g]) ∧
      ∀ mS, 1 ≤ mS →
        ∃ (Rcell Bcell : (c : Fin P.toPoly.K) →
            (Fin (P.toPoly.arity c) → RegionSpecF B) → ℕ → Fin P.d → ℤ)
          (PR PBn : (c : Fin P.toPoly.K) →
            (Fin (P.toPoly.arity c) → RegionSpecF B) → Fin P.d → ℤ),
          (∀ (c : Fin P.toPoly.K)
              (rs : Fin (P.toPoly.arity c) → RegionSpecF B),
            (∀ i, (rs i).valid mS) → ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
            P.rank c (copiedSlice mS n) (cellTupleF rs mS t n)
              = fun i => Rcell c rs t i + Bcell c rs n i) ∧
          (∀ c rs t, m ≤ t → Rcell c rs (t + p) = Rcell c rs t + PR c rs) ∧
          (∀ c rs n, m ≤ n → Bcell c rs (n + p) = Bcell c rs n + PBn c rs) ∧
          (∀ c rs i, (PR c rs i).natAbs ≤ SP c i) ∧
          (∀ c rs i, (PBn c rs i).natAbs ≤ SP c i) := by
  classical
  choose mr pr SPr hpr hmrB hrank using
    fun c : Fin P.toPoly.K => rank_cell_decomp_fibred_uniform_bounded (B := B) P c
  have hdata : ∀ c : Fin P.toPoly.K,
      ∃ (M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (mv pv : ℕ),
        1 ≤ pv ∧
        (∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
          (∀ i, ī i < w.length) →
          (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
            (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D))) ∧
        (∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g]) := by
    intro c
    obtain ⟨M, hM⟩ := SliceDstarGA.exists_selDDFA P c
    obtain ⟨mv, pv, hpv, hEP⟩ := SliceMarkN.bFN_func_iterate_eventuallyPeriodic M
    exact ⟨M, mv, pv, hpv, hM, hEP⟩
  choose Mc mvc pvc hpvc hMc hEPc using hdata
  set p : ℕ := (∏ c : Fin P.toPoly.K, pr c) * (∏ c : Fin P.toPoly.K, pvc c)
    with hpdef
  have hprpos : 0 < ∏ c : Fin P.toPoly.K, pr c :=
    Finset.prod_pos (fun c _ => hpr c)
  have hpvpos : 0 < ∏ c : Fin P.toPoly.K, pvc c :=
    Finset.prod_pos (fun c _ => hpvc c)
  have hp : 1 ≤ p := by
    rw [hpdef]
    exact Nat.mul_pos hprpos hpvpos
  have hprdvd : ∀ c, pr c ∣ p := by
    intro c
    rw [hpdef]
    exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ c)) _
  have hpvcdvd : ∀ c, pvc c ∣ p := by
    intro c
    rw [hpdef]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ c)) _
  set m : ℕ := (Finset.univ.sup (fun c => mr c)
      ⊔ Finset.univ.sup (fun c => mvc c)) ⊔ (B + 1) with hmdef
  have hmB : B + 1 ≤ m := by
    rw [hmdef]
    exact le_max_right _ _
  have hmmr : ∀ c, mr c ≤ m := by
    intro c
    rw [hmdef]
    exact le_trans (le_trans (Finset.le_sup (f := fun c => mr c)
      (Finset.mem_univ c)) (le_max_left _ _)) (le_max_left _ _)
  have hmmvc : ∀ c, mvc c ≤ m := by
    intro c
    rw [hmdef]
    exact le_trans (le_trans (Finset.le_sup (f := fun c => mvc c)
      (Finset.mem_univ c)) (le_max_right _ _)) (le_max_left _ _)
  refine ⟨m, p, Mc, fun c i => (p / pr c) * SPr c i, hp, hmB, hMc, ?_, ?_⟩
  · -- bFN function-iterate periodicity at (m, p)
    intro c g hg
    obtain ⟨t, ht⟩ := hpvcdvd c
    rw [ht, Nat.mul_comm]
    exact SliceGrowthCollapse.bFN_iterate_period_mul (Mc c) (mvc c) (pvc c)
      (hEPc c) t g (le_trans (hmmvc c) hg)
  · -- the per-width cell families, rescaled to (m, p), now bounded
    intro mS hm
    have hfam : ∀ (c : Fin P.toPoly.K)
        (rs : Fin (P.toPoly.arity c) → RegionSpecF B),
        ∃ (R Bn : ℕ → Fin P.d → ℤ) (PRv PBv : Fin P.d → ℤ),
          ((∀ i, (rs i).valid mS) → ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
            P.rank c (copiedSlice mS n) (cellTupleF rs mS t n)
              = fun i => R t i + Bn n i) ∧
          (∀ t, m ≤ t → R (t + p) = R t + PRv) ∧
          (∀ n, m ≤ n → Bn (n + p) = Bn n + PBv) ∧
          (∀ i, (PRv i).natAbs ≤ (p / pr c) * SPr c i) ∧
          (∀ i, (PBv i).natAbs ≤ (p / pr c) * SPr c i) := by
      intro c rs
      by_cases hv : ∀ i, (rs i).valid mS
      · obtain ⟨R, Bn, PRv, PBv, h1, h2, h3, hPRvb, hPBvb⟩ := hrank c mS hm rs hv
        obtain ⟨q, hq⟩ := hprdvd c
        refine ⟨R, Bn, (p / pr c) • PRv, (p / pr c) • PBv,
          fun _ => h3, ?_, ?_, ?_, ?_⟩
        · intro t ht
          rw [hq, Nat.mul_div_cancel_left q (hpr c)]
          exact RankAffine.iterate h1 t q (le_trans (hmmr c) ht)
        · intro n hn
          rw [hq, Nat.mul_div_cancel_left q (hpr c)]
          exact RankAffine.iterate h2 n q (le_trans (hmmr c) hn)
        · intro i
          rw [Pi.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
          exact Nat.mul_le_mul le_rfl (hPRvb i)
        · intro i
          rw [Pi.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
          exact Nat.mul_le_mul le_rfl (hPBvb i)
      · exact ⟨0, 0, 0, 0, fun hcon => absurd hcon hv,
          (by intro t _; simp), (by intro n _; simp),
          (fun i => by simp), (fun i => by simp)⟩
    choose Rcell Bcell PRc PBc h1 h2 h3 hPRcb hPBcb using hfam
    exact ⟨Rcell, Bcell, PRc, PBc, h1, h2, h3, hPRcb, hPBcb⟩

end CopiedSetup
