/-
# The fibred setup fold (§9 tower, Stage F.2)

The wrapped-flat `dstar_setup_GA` aligned rank periods over the per-slice cell
list; on the copied slice that list grows with `mS`, so the periods must come
from the FUNCTION-LEVEL engines instead (Stage C's `SlicePeriodStar`):

* `func_iterate_EP` — iterate periodicity of any finite-state map, uniform in
  the start point (the `(f ∘ ·)`-at-`id` trick);
* `summand_copied_families_recurrence` — one machine-level `(m, p)` per
  summand serving its block-U/block-D/suf families and EVERY suffix-stretch
  family across ALL boundary widths `mS` (slopes per-width: they read the
  post-prefix state `δ^*(q0, U^mS)`);
* `summand_region_decomp_fibred_uniform` /
  `rank_cell_decomp_fibred_uniform` — the Stage E decomposition with the
  recurrence thresholds and periods hoisted BEFORE `mS`;
* `dstar_setup_fibred` — the fibred stage-1 fold: `(m, p)` and the per-copy
  selected-`D` DFAs chosen before `mS`; per-`mS` cell families with global
  slopes at the pinned `p`.
-/
import RequestProject.CopiedRank
import RequestProject.CopiedDstar
import RequestProject.SlicePeriodStar
import RequestProject.SliceDstarBridgeGA

namespace CopiedSetup

open WRP Step SliceRankAtom SliceRank SliceFamilyRank SliceFamilyCell CopiedCells CopiedRank
  CopiedDstar MSOMarkN SliceMarkN
open scoped Classical

variable {d : ℕ}

/-! ## The machine-level engines -/

/-- **Function-space iterate periodicity, uniform in the start point**: the
`(f ∘ ·)`-at-`id` trick gives one `(m, p)` with `f^[j+p] = f^[j]` as FUNCTIONS. -/
theorem func_iterate_EP {Q : Type*} [Finite Q] (f : Q → Q) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ j, m ≤ j → f^[j + p] = f^[j] := by
  obtain ⟨m, p, hp, hper⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic (fun g : Q → Q => f ∘ g) id
  have key : ∀ k, (fun g : Q → Q => f ∘ g)^[k] id = f^[k] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, ← Function.iterate_succ']
  exact ⟨m, p, hp, fun j hj => by rw [← key, ← key]; exact hper j hj⟩

/-- Function-level EP extends to multiples of the period. -/
theorem func_EP_mul {Q : Type*} {f : Q → Q} {m p : ℕ}
    (h : ∀ j, m ≤ j → f^[j + p] = f^[j]) :
    ∀ q j, m ≤ j → f^[j + p * q] = f^[j] := by
  intro q
  induction q with
  | zero => intro j _; simp
  | succ q ih =>
      intro j hj
      rw [Nat.mul_succ, ← Nat.add_assoc, h _ (by omega), ih j hj]

/-- The pre-blocks shape yields the recurrence at the SAME `(m, p)`. -/
theorem recurrence_of_pre_blocks' {S : ℕ → Fin d → ℤ} {m p : ℕ}
    {P : Fin d → ℤ} (hp : 1 ≤ p)
    (h : ∀ k r, S (m + p * k + r) = S (m + r) + k • P) :
    ∀ j, m ≤ j → S (j + p) = S j + P := by
  intro j hj
  obtain ⟨k, r, -, hjeq⟩ : ∃ k r, r < p ∧ j = m + p * k + r := by
    refine ⟨(j - m) / p, (j - m) % p, Nat.mod_lt _ hp, ?_⟩
    have := Nat.div_add_mod (j - m) p
    omega
  have e1 : S j = S (m + r) + k • P := by rw [hjeq]; exact h k r
  have e2 : S (j + p) = S (m + r) + (k + 1) • P := by
    rw [show j + p = m + p * (k + 1) + r from by rw [Nat.mul_succ]; omega]
    exact h (k + 1) r
  rw [e1, e2, succ_nsmul]
  abel

/-- The tail split of the copied prefix-rank (the `hval` of the tail engine,
exposed): reading `pre ++ loop^n ++ tail` adds a tail correction read off the
post-loop state. -/
theorem prefixRank_tail_split (A : RankSource Step d)
    (pre loop tail : List Step) (n : ℕ) :
    A.prefixRank (pre ++ (List.replicate n loop).flatten ++ tail)
      (pre ++ (List.replicate n loop).flatten ++ tail).length
    = A.prefixRank (pre ++ (List.replicate n loop).flatten)
        (pre ++ (List.replicate n loop).flatten).length
      + (List.foldl (SliceRank.rankStep A)
          ((fun q => List.foldl A.δ q loop)^[n] (List.foldl A.δ A.q0 pre), 0)
          tail).2 := by
  have hsnd : ∀ z : A.Q × (Fin d → ℤ),
      (List.foldl (SliceRank.rankStep A) z tail).2
        = z.2 + (List.foldl (SliceRank.rankStep A) (z.1, 0) tail).2 := by
    rintro ⟨q, acc⟩
    exact SliceRank.rankStep_snd_add A q acc tail
  have hY1 : (List.foldl (SliceRank.rankStep A) (A.q0, 0)
      (pre ++ (List.replicate n loop).flatten)).1
      = (fun q => List.foldl A.δ q loop)^[n] (List.foldl A.δ A.q0 pre) := by
    rw [SliceRank.rankStep_fst, List.foldl_append,
      SliceMSO.foldl_replicate_flatten]
  rw [SliceRank.prefixRank_eq_foldl, SliceRank.prefixRank_eq_foldl,
    List.foldl_append, hsnd, hY1]

/-! ## The uniform copied-family recurrences -/

/-- **One machine-level `(m, p)` per summand** serving the block-U, block-D
and suf families and every suffix-stretch family, across ALL boundary widths
(slopes per-width — they read `δ^*(q0, U^mS)`). -/
theorem summand_copied_families_recurrence {k : ℕ} (s : Summand Step d k) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ mS, 1 ≤ mS →
      (∃ Pv : Fin d → ℤ, ∀ j, m ≤ j →
        s.eval (copiedSlice mS (j + p + 1)) (fun _ => mS + 2 * (j + p))
          = s.eval (copiedSlice mS (j + 1)) (fun _ => mS + 2 * j) + Pv) ∧
      (∃ Pv : Fin d → ℤ, ∀ j, m ≤ j →
        s.eval (copiedSlice mS (j + p + 1)) (fun _ => mS + 2 * (j + p) + 1)
          = s.eval (copiedSlice mS (j + 1)) (fun _ => mS + 2 * j + 1) + Pv) ∧
      (∃ Pv : Fin d → ℤ, ∀ n, m ≤ n →
        s.eval (copiedSlice mS (n + p)) (fun _ => mS + 2 * (n + p))
          = s.eval (copiedSlice mS n) (fun _ => mS + 2 * n) + Pv) ∧
      (∀ l, l < mS - 1 → ∃ Pv : Fin d → ℤ, ∀ n, m ≤ n →
        s.eval (copiedSlice mS (n + p)) (fun _ => mS + 2 * (n + p) + 1 + l)
          = s.eval (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l) + Pv) := by
  have := s.A.fintypeQ
  obtain ⟨m₁, p₁, hp₁, htwin⟩ :=
    SlicePeriodStar.affineOnResidues_of_blockIterate_func
      (fun q => List.foldl s.A.δ q [U, D])
      (fun q => (List.foldl (SliceRank.rankStep s.A) (q, 0) [U, D]).2)
  obtain ⟨m₂, p₂, hp₂, hEPf⟩ := func_iterate_EP (fun q => List.foldl s.A.δ q [U, D])
  refine ⟨max m₁ m₂, p₁ * p₂,
    Nat.one_le_iff_ne_zero.mpr (by positivity), fun mS hm => ?_⟩
  set q₁ : s.A.Q := List.foldl s.A.δ s.A.q0 (List.replicate mS U) with hq₁
  -- the prefix-rank decomposition at this boundary width
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
  -- the summed-weight recurrence at the combined period
  obtain ⟨Pw, hPw⟩ := htwin q₁
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
  -- the prefix-rank recurrence (the per-width constant cancels)
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
  -- the iterate equality at the combined period
  have hit : ∀ j, m₂ ≤ j →
      (fun q => List.foldl s.A.δ q [U, D])^[j + p₁ * p₂]
        = (fun q => List.foldl s.A.δ q [U, D])^[j] := by
    intro j hj
    have h := func_EP_mul hEPf p₁ j hj
    rwa [Nat.mul_comm p₂ p₁] at h
  refine ⟨⟨s.coeff • (p₂ • Pw), fun j hj => ?_⟩,
    ⟨s.coeff • (p₂ • Pw), fun j hj => ?_⟩,
    ⟨s.coeff • (p₂ • Pw), fun n hn => ?_⟩,
    fun l hl => ⟨s.coeff • (p₂ • Pw), fun n hn => ?_⟩⟩
  · -- block-U
    rw [summand_copied_block_eq s mS (j + p₁ * p₂) hm,
      summand_copied_block_eq s mS j hm, hPF j (by omega),
      hit j (by omega), smul_add]
    abel
  · -- block-D
    rw [summand_copied_blockD_eq s mS (j + p₁ * p₂) hm,
      summand_copied_blockD_eq s mS j hm, hPF j (by omega),
      hit j (by omega), add_right_comm, smul_add]
    abel
  · -- suf
    rw [summand_copied_suf_eq s mS (n + p₁ * p₂) hm,
      summand_copied_suf_eq s mS n hm, hPF n (by omega),
      hit n (by omega), smul_add]
    abel
  · -- suffix stretch at offset l
    rw [summand_copied_sufStretch_eq s mS l hl (n + p₁ * p₂),
      summand_copied_sufStretch_eq s mS l hl n,
      prefixRank_tail_split s.A (List.replicate mS U) [U, D]
        (List.replicate (l + 1) D) (n + p₁ * p₂),
      prefixRank_tail_split s.A (List.replicate mS U) [U, D]
        (List.replicate (l + 1) D) n,
      hPF n (by omega), hit n (by omega)]
    simp only [smul_add]
    abel

/-! ## The uniform fibred region decomposition -/

/-- **The Stage E region decomposition with `(m, p)` hoisted before `mS`**:
one machine-level threshold and period per summand; families and slopes
per-width. -/
theorem summand_region_decomp_fibred_uniform {B k : ℕ} (s : Summand Step d k) :
    ∃ m p : ℕ, 1 ≤ p ∧ B + 1 ≤ m ∧
      ∀ mS, 1 ≤ mS → ∀ r : RegionSpecF B, r.valid mS →
      ∃ (Rs Bs : ℕ → Fin d → ℤ) (PRs PBs : Fin d → ℤ),
        (∀ t, m ≤ t → Rs (t + p) = Rs t + PRs) ∧
        (∀ n, m ≤ n → Bs (n + p) = Bs n + PBs) ∧
        ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
          s.eval (copiedSlice mS n) (fun _ => r.posAt mS t n)
            = fun c => Rs t c + Bs n c := by
  obtain ⟨m₀, p₀, hp₀, hfam⟩ := summand_copied_families_recurrence (k := k) s
  refine ⟨m₀ + B + 1, p₀, hp₀, by omega, fun mS hm r hv => ?_⟩
  obtain ⟨⟨PU, hU⟩, ⟨PD, hD⟩, ⟨PS, hSuf⟩, hStr⟩ := hfam mS hm
  rcases r with r | q | l
  case prefIdx =>
    have hq : q < mS - 1 := hv
    refine ⟨fun _ => s.eval (copiedSlice mS 0) (fun _ => q), fun _ => 0, 0, 0,
      (by intro t _; simp), (by intro n _; simp), fun t n _ _ => ?_⟩
    show s.eval (copiedSlice mS n) (fun _ => q) = _
    rw [summand_copied_pref_stable s mS q n 0 hm (by omega)]
    funext c
    simp
  case sufIdx =>
    have hlv : l < mS - 1 := hv
    obtain ⟨PSl, hSl⟩ := hStr l hlv
    refine ⟨fun _ => 0,
      fun n => s.eval (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l),
      0, PSl, (by intro t _; simp), fun n hn => hSl n (by omega),
      fun t n _ _ => ?_⟩
    show s.eval (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l) = _
    funext c
    simp
  case core =>
    rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
    · -- pre
      refine ⟨fun _ => s.eval (copiedSlice mS 0) (fun _ => mS - 1 + 0),
        fun _ => 0, 0, 0, (by intro t _; simp), (by intro n _; simp),
        fun t n _ _ => ?_⟩
      show s.eval (copiedSlice mS n) (fun _ => mS - 1 + 0) = _
      rw [summand_copied_mid_stable s mS 0 n 0 hm (by omega) (by omega)]
      funext c
      simp
    · -- suf
      refine ⟨fun _ => 0,
        fun n => s.eval (copiedSlice mS n) (fun _ => mS + 2 * n),
        0, PS, (by intro t _; simp), fun n hn => hSuf n (by omega),
        fun t n _ _ => ?_⟩
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
          fun t n ht htn => ?_⟩
        have hf := f.isLt
        show s.eval (copiedSlice mS n) (fun _ => mS - 1 + (1 + 2 * f.val)) = _
        rw [summand_copied_mid_stable s mS (1 + 2 * f.val) n (f.val + 1) hm
          (by omega) (by omega)]
        funext c
        simp
      · refine ⟨fun _ => s.eval (copiedSlice mS (f.val + 1))
            (fun _ => mS - 1 + (1 + 2 * f.val + 1)),
          fun _ => 0, 0, 0, (by intro t _; simp), (by intro n _; simp),
          fun t n ht htn => ?_⟩
        have hf := f.isLt
        show s.eval (copiedSlice mS n)
          (fun _ => mS - 1 + (1 + 2 * f.val + 1)) = _
        rw [summand_copied_mid_stable s mS (1 + 2 * f.val + 1) n (f.val + 1) hm
          (by omega) (by omega)]
        funext c
        simp
    · -- back-pinned
      rcases e with _ | _
      · refine ⟨fun _ => 0,
          fun n => s.eval (copiedSlice mS (n - (1 + l.val) + 1))
            (fun _ => mS + 2 * (n - (1 + l.val))),
          0, PU, (by intro t _; simp), ?_, fun t n ht htn => ?_⟩
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
          rw [harg, summand_copied_mid_stable s mS (1 + 2 * (n - (1 + l.val)))
            n (n - (1 + l.val) + 1) hm (by omega) (by omega), hpos]
          funext c
          simp
      · refine ⟨fun _ => 0,
          fun n => s.eval (copiedSlice mS (n - (1 + l.val) + 1))
            (fun _ => mS + 2 * (n - (1 + l.val)) + 1),
          0, PD, (by intro t _; simp), ?_, fun t n ht htn => ?_⟩
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
          rw [harg, summand_copied_mid_stable s mS
            (1 + 2 * (n - (1 + l.val)) + 1) n (n - (1 + l.val) + 1) hm
            (by omega) (by omega), hpos]
          funext c
          simp
    · -- cluster
      rcases e with _ | _
      · refine ⟨fun t => s.eval (copiedSlice mS (t + δ.val + 1))
            (fun _ => mS + 2 * (t + δ.val)),
          fun _ => 0, PU, 0, ?_, (by intro n _; simp), fun t n ht htn => ?_⟩
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
          rw [summand_copied_mid_stable s mS (1 + 2 * (t + δ.val)) n
            (t + δ.val + 1) hm (by omega) (by omega), hpos]
          funext c
          simp
      · refine ⟨fun t => s.eval (copiedSlice mS (t + δ.val + 1))
            (fun _ => mS + 2 * (t + δ.val) + 1),
          fun _ => 0, PD, 0, ?_, (by intro n _; simp), fun t n ht htn => ?_⟩
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
          rw [summand_copied_mid_stable s mS (1 + 2 * (t + δ.val) + 1) n
            (t + δ.val + 1) hm (by omega) (by omega), hpos]
          funext c
          simp

/-! ## The rank-term and presentation levels -/

/-- Align machine-level thresholds and periods over a list. -/
theorem uniform_list_align {α : Type*} (l : List α) (ms ps : α → ℕ)
    (hps : ∀ a ∈ l, 1 ≤ ps a) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ a ∈ l, ms a ≤ m ∧ ps a ∣ p := by
  induction l with
  | nil => exact ⟨0, 1, le_rfl, by simp⟩
  | cons a rest ih =>
      obtain ⟨m', p', hp', h'⟩ :=
        ih (fun b hb => hps b (List.mem_cons.mpr (Or.inr hb)))
      have hpa := hps a (List.mem_cons.mpr (Or.inl rfl))
      refine ⟨max (ms a) m', ps a * p',
        Nat.one_le_iff_ne_zero.mpr (by positivity), fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨le_max_left _ _, dvd_mul_right _ _⟩
      · exact ⟨le_trans (h' b hb).1 (le_max_right _ _),
          Dvd.dvd.mul_left (h' b hb).2 (ps a)⟩

private theorem pi_list_sum_recurrence {ι : Type*} (l : List ι)
    (F G H : ι → Fin d → ℤ) (h : ∀ s ∈ l, F s = G s + H s) :
    (l.map F).sum = (l.map G).sum + (l.map H).sum := by
  funext c
  show ((l.map F).sum) c = ((l.map G).sum + (l.map H).sum) c
  rw [Pi.add_apply, SliceFamilyRank.list_sum_pi_apply l F c,
    SliceFamilyRank.list_sum_pi_apply l G c,
    SliceFamilyRank.list_sum_pi_apply l H c,
    ← SliceFamilyRank.list_sum_map_add]
  refine congrArg List.sum (List.map_congr_left (fun s hs => ?_))
  rw [h s hs]
  rfl

/-- The fibred rank-term decomposition with `(m, p)` hoisted before `mS`. -/
theorem rankTerm_cell_decomp_fibred_uniform {B k : ℕ} (κ : RankTerm Step d k) :
    ∃ m p : ℕ, 1 ≤ p ∧ B + 1 ≤ m ∧
      ∀ mS, 1 ≤ mS → ∀ rs : Fin k → RegionSpecF B, (∀ i, (rs i).valid mS) →
      ∃ (R Bn : ℕ → Fin d → ℤ) (PR PBn : Fin d → ℤ),
        (∀ t, m ≤ t → R (t + p) = R t + PR) ∧
        (∀ n, m ≤ n → Bn (n + p) = Bn n + PBn) ∧
        ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
          κ.eval (copiedSlice mS n) (fun i => (rs i).posAt mS t n)
            = fun c => R t c + Bn n c := by
  classical
  choose ms ps hps hmsB huni using fun s : Summand Step d k =>
    summand_region_decomp_fibred_uniform (B := B) s
  obtain ⟨m₀, p₀, hp₀, halign⟩ :=
    uniform_list_align κ.summands ms ps (fun s _ => hps s)
  refine ⟨max m₀ (B + 1), p₀, hp₀, le_max_right _ _, fun mS hm rs hv => ?_⟩
  choose Rs Bs PRs PBs hRrec hBrec heq using
    fun s : Summand Step d k => huni s mS hm (rs s.π) (hv s.π)
  -- per-member recurrences rescaled to the aligned period
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
    (κ.summands.map (fun s => (p₀ / ps s) • PBs s)).sum, ?_, ?_, ?_⟩
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

/-- The fibred presentation-level rank decomposition, `(m, p)` before `mS`. -/
theorem rank_cell_decomp_fibred_uniform {B : ℕ} (P : WRP.Presentation Step Step)
    (c : Fin P.toPoly.K) :
    ∃ m p : ℕ, 1 ≤ p ∧ B + 1 ≤ m ∧
      ∀ mS, 1 ≤ mS →
      ∀ rs : Fin (P.toPoly.arity c) → RegionSpecF B, (∀ i, (rs i).valid mS) →
      ∃ (R Bn : ℕ → Fin P.d → ℤ) (PR PBn : Fin P.d → ℤ),
        (∀ t, m ≤ t → R (t + p) = R t + PR) ∧
        (∀ n, m ≤ n → Bn (n + p) = Bn n + PBn) ∧
        ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
          P.rank c (copiedSlice mS n) (cellTupleF rs mS t n)
            = fun i => R t i + Bn n i := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  obtain ⟨m, p, hp, hmB, hterm⟩ := rankTerm_cell_decomp_fibred_uniform (B := B) κ
  refine ⟨m, p, hp, hmB, fun mS hm rs hv => ?_⟩
  obtain ⟨R, Bn, PR, PBn, h1, h2, h3⟩ := hterm mS hm rs hv
  exact ⟨R, Bn, PR, PBn, h1, h2,
    fun t n ht htn => by rw [hκ]; exact h3 t n ht htn⟩

/-! ## The fibred setup fold -/

/-- **The fibred stage-1 setup** (CS-5.2): `(m, p)` and the per-copy
selected-`D` DFAs chosen BEFORE the boundary width; per-width cell families
with global slopes at the pinned period. -/
theorem dstar_setup_fibred (P : WRP.Presentation Step Step) (B : ℕ) :
    ∃ (m p : ℕ)
      (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))),
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
          (∀ c rs n, m ≤ n → Bcell c rs (n + p) = Bcell c rs n + PBn c rs) := by
  classical
  -- the per-copy uniform rank data and selected-D DFAs
  choose mr pr hpr hmrB hrank using
    fun c : Fin P.toPoly.K => rank_cell_decomp_fibred_uniform (B := B) P c
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
  -- the global period and threshold (all machine-level, width-free)
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
  refine ⟨m, p, Mc, hp, hmB, hMc, ?_, ?_⟩
  · -- bFN function-iterate periodicity at (m, p)
    intro c g hg
    obtain ⟨t, ht⟩ := hpvcdvd c
    rw [ht, Nat.mul_comm]
    exact SliceGrowthCollapse.bFN_iterate_period_mul (Mc c) (mvc c) (pvc c)
      (hEPc c) t g (le_trans (hmmvc c) hg)
  · -- the per-width cell families, rescaled to (m, p)
    intro mS hm
    have hfam : ∀ (c : Fin P.toPoly.K)
        (rs : Fin (P.toPoly.arity c) → RegionSpecF B),
        ∃ (R Bn : ℕ → Fin P.d → ℤ) (PRv PBv : Fin P.d → ℤ),
          ((∀ i, (rs i).valid mS) → ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
            P.rank c (copiedSlice mS n) (cellTupleF rs mS t n)
              = fun i => R t i + Bn n i) ∧
          (∀ t, m ≤ t → R (t + p) = R t + PRv) ∧
          (∀ n, m ≤ n → Bn (n + p) = Bn n + PBv) := by
      intro c rs
      by_cases hv : ∀ i, (rs i).valid mS
      · obtain ⟨R, Bn, PRv, PBv, h1, h2, h3⟩ := hrank c mS hm rs hv
        obtain ⟨q, hq⟩ := hprdvd c
        refine ⟨R, Bn, (p / pr c) • PRv, (p / pr c) • PBv,
          fun _ => h3, ?_, ?_⟩
        · intro t ht
          rw [hq, Nat.mul_div_cancel_left q (hpr c)]
          exact RankAffine.iterate h1 t q (le_trans (hmmr c) ht)
        · intro n hn
          rw [hq, Nat.mul_div_cancel_left q (hpr c)]
          exact RankAffine.iterate h2 n q (le_trans (hmmr c) hn)
      · exact ⟨0, 0, 0, 0, fun hcon => absurd hcon hv,
          (by intro t _; simp), (by intro n _; simp)⟩
    choose Rcell Bcell PRc PBc h1 h2 h3 using hfam
    exact ⟨Rcell, Bcell, PRc, PBc, h1, h2, h3⟩

end CopiedSetup
