/-
# Block-iterate facts for the slice selection count

The automaton-side foundation of the slice-specific count reduction.  For a
deterministic automaton `M` over `Step × Bool`, the forward unmarked run `fwd`
reaches the start of loop-block `j` of `W_n` in state `bF^[j] q_pre`, where
`bF q = foldl fStep q [U,D]` is the one-block transition and `q_pre = fStep q0 U`.
The forward state iterate `bF^[j] q_pre` and the iterate *function* `bF^[m]` are
both eventually periodic (`M.Q`, hence `M.Q → M.Q`, is finite), which is what feeds
the convolution.  All axiom-clean.
-/
import RequestProject.SliceCount
import RequestProject.SliceWords
import RequestProject.SliceMSO
import RequestProject.SliceAutomata
import RequestProject.SliceAffine
import RequestProject.WrappedFlat

open MSOMark SliceMSO Step
open scoped Classical

namespace SliceCount

variable (M : DetAuto (Step × Bool))

/-- The one-block (`UD`) forward transition. -/
def bF (q : M.Q) : M.Q := List.foldl (fStep M) q [U, D]

/-- The forward state after the slice's leading `U`. -/
def qpre : M.Q := fStep M M.q0 U

/-- **Forward state at a block boundary.**  The unmarked forward run reaches the
start of loop-block `j` of `W_n` in state `bF^[j] q_pre`. -/
theorem fwd_blockStart (n j : ℕ) (h : j ≤ n) :
    fwd M (wrappedFlat n) (1 + 2 * j) = (bF M)^[j] (qpre M) := by
  unfold fwd
  rw [SliceWords.wrappedFlat_take j n h, List.foldl_append,
    show List.foldl (fStep M) M.q0 [U] = qpre M from rfl, foldl_replicate_flatten]
  rfl

/-- The forward state iterate `bF^[j] q_pre` is eventually periodic in `j`. -/
theorem bF_iterate_eventuallyPeriodic :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ j, m ≤ j → (bF M)^[j + p] (qpre M) = (bF M)^[j] (qpre M) := by
  have := M.fintypeQ
  exact SliceAutomata.iterate_eventuallyPeriodic (bF M) (qpre M)

/-- The iterate *function* `bF^[m]` is eventually periodic in `m` (`M.Q → M.Q` is
finite). -/
theorem bF_func_iterate_eventuallyPeriodic :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ j, m ≤ j → (bF M)^[j + p] = (bF M)^[j] := by
  have := M.fintypeQ
  obtain ⟨m, p, hp, hper⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic (fun g : M.Q → M.Q => bF M ∘ g) id
  have key : ∀ k, (fun g : M.Q → M.Q => bF M ∘ g)^[k] id = (bF M)^[k] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, ← Function.iterate_succ']
  exact ⟨m, p, hp, fun j hj => by rw [← key, ← key]; exact hper j hj⟩

/-- The slice suffix at a loop-block, exposing the block's `U`, `D` and the rest. -/
theorem wrappedFlat_drop_block (n j : ℕ) (h : j < n) :
    (wrappedFlat n).drop (1 + 2 * j) =
      U :: D :: ((List.replicate (n - 1 - j) [U, D]).flatten ++ [D]) := by
  rw [SliceWords.wrappedFlat_drop j n (le_of_lt h), show n - j = (n - 1 - j) + 1 from by omega,
    List.replicate_succ, List.flatten_cons]
  rfl

theorem wrappedFlat_getElem_U (n j : ℕ) (h : j < n) (hb : 1 + 2 * j < (wrappedFlat n).length) :
    (wrappedFlat n)[1 + 2 * j] = U := by
  have hd := @List.getElem?_drop _ (wrappedFlat n) (1 + 2 * j) 0
  rw [wrappedFlat_drop_block n j h, Nat.add_zero, List.getElem?_eq_getElem hb] at hd
  simpa using hd.symm

theorem wrappedFlat_getElem_D (n j : ℕ) (h : j < n)
    (hb : 1 + 2 * j + 1 < (wrappedFlat n).length) : (wrappedFlat n)[1 + 2 * j + 1] = D := by
  have hd := @List.getElem?_drop _ (wrappedFlat n) (1 + 2 * j) 1
  rw [wrappedFlat_drop_block n j h, List.getElem?_eq_getElem hb] at hd
  simpa using hd.symm

/-- Backward type just after the block's `U` (at its `D`). -/
theorem tau_blockU (n j : ℕ) (h : j < n) (q : M.Q) :
    tau M (wrappedFlat n) (1 + 2 * j + 1) q =
      M.accept (fStep M ((bF M)^[n - 1 - j] (fStep M q D)) D) := by
  unfold tau
  rw [show 1 + 2 * j + 1 = (1 + 2 * j) + 1 from rfl, ← List.drop_drop, wrappedFlat_drop_block n j h,
    List.drop_one, List.tail_cons, List.foldl_cons, List.foldl_append, foldl_replicate_flatten]
  rfl

/-- Backward type just after the block's `D` (at the next block start). -/
theorem tau_blockD (n j : ℕ) (h : j < n) (q : M.Q) :
    tau M (wrappedFlat n) (1 + 2 * j + 2) q =
      M.accept (fStep M ((bF M)^[n - 1 - j] q) D) := by
  unfold tau
  rw [show 1 + 2 * j + 2 = 1 + 2 * (j + 1) from by ring,
    SliceWords.wrappedFlat_drop (j + 1) n (by omega), show n - (j + 1) = n - 1 - j from by omega,
    List.foldl_append, foldl_replicate_flatten]
  rfl

/-- One forward step: `fwd` at `p+1` extends `fwd` at `p` by the letter `w[p]`. -/
theorem fwd_succ (w : List Step) (p : ℕ) (hp : p < w.length) :
    fwd M w (p + 1) = fStep M (fwd M w p) (w[p]) := by
  unfold fwd
  rw [List.take_add_one, List.getElem?_eq_getElem hp, Option.toList_some, List.foldl_append]
  rfl

/-- Forward state just after the block's `U`. -/
theorem fwd_blockU (n j : ℕ) (h : j < n) :
    fwd M (wrappedFlat n) (1 + 2 * j + 1) = fStep M ((bF M)^[j] (qpre M)) U := by
  have hb : 1 + 2 * j < (wrappedFlat n).length := by rw [length_wrappedFlat]; omega
  rw [fwd_succ M (wrappedFlat n) (1 + 2 * j) hb, fwd_blockStart M n j (le_of_lt h),
    wrappedFlat_getElem_U n j h hb]

open scoped Classical in
/-- Per-position contribution: `1` if the single-mark word at `p` is accepted. -/
noncomputable def ind (w : List Step) (p : ℕ) : ℕ := if M.accepts (markAt w p) then 1 else 0

open scoped Classical in
/-- The number of accepted single-mark positions of `w`. -/
noncomputable def countAccept (w : List Step) : ℕ := ∑ p ∈ Finset.range w.length, ind M w p

open scoped Classical in
/-- The contribution of one loop-block, as a function of the forward state `q`
entering the block and the backward iterate `g = bF^[n-1-j]`. -/
noncomputable def blockC (q : M.Q) (g : M.Q → M.Q) : ℕ :=
  (if M.accept (fStep M (g (fStep M (M.δ q (U, true)) D)) D) then 1 else 0) +
  (if M.accept (fStep M (g (M.δ (fStep M q U) (D, true))) D) then 1 else 0)

/-- The two indicators of loop-block `j` sum to `blockC` of its forward/backward
iterates. -/
theorem ind_block (n j : ℕ) (h : j < n) :
    ind M (wrappedFlat n) (1 + 2 * j) + ind M (wrappedFlat n) (1 + 2 * j + 1)
      = blockC M ((bF M)^[j] (qpre M)) ((bF M)^[n - 1 - j]) := by
  have hb1 : 1 + 2 * j < (wrappedFlat n).length := by rw [length_wrappedFlat]; omega
  have hb2 : 1 + 2 * j + 1 < (wrappedFlat n).length := by rw [length_wrappedFlat]; omega
  have e1 : M.accepts (markAt (wrappedFlat n) (1 + 2 * j)) ↔
      M.accept (fStep M ((bF M)^[n - 1 - j]
        (fStep M (M.δ ((bF M)^[j] (qpre M)) (U, true)) D)) D) := by
    rw [accepts_markAt M (wrappedFlat n) (1 + 2 * j) hb1, fwd_blockStart M n j (le_of_lt h),
      wrappedFlat_getElem_U n j h hb1, tau_blockU M n j h]
  have e2 : M.accepts (markAt (wrappedFlat n) (1 + 2 * j + 1)) ↔
      M.accept (fStep M ((bF M)^[n - 1 - j]
        (M.δ (fStep M ((bF M)^[j] (qpre M)) U) (D, true))) D) := by
    rw [accepts_markAt M (wrappedFlat n) (1 + 2 * j + 1) hb2, fwd_blockU M n j h,
      wrappedFlat_getElem_D n j h hb2, tau_blockD M n j h]
  unfold ind blockC
  rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]

/-- Pairing reindex: a sum over `2n` indices is a sum over `n` consecutive pairs. -/
theorem sum_pairs (g : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), g i = ∑ j ∈ Finset.range n, (g (2 * j) + g (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, show 2 * (n + 1) = 2 * n + 1 + 1 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
      ring

/-- Backward type just before the first loop (used by `ind` at position `0`). -/
theorem tau_pre (n : ℕ) (q : M.Q) :
    tau M (wrappedFlat n) 1 q = M.accept (fStep M ((bF M)^[n] q) D) := by
  unfold tau
  rw [show (1 : ℕ) = 1 + 2 * 0 from rfl, SliceWords.wrappedFlat_drop 0 n (Nat.zero_le n),
    Nat.sub_zero, List.foldl_append, foldl_replicate_flatten]
  rfl

theorem wrappedFlat_getElem_zero (n : ℕ) (hb : 0 < (wrappedFlat n).length) :
    (wrappedFlat n)[0] = U := by
  have h0 : (wrappedFlat n)[0]? = some U := by unfold wrappedFlat; rfl
  rw [List.getElem?_eq_getElem hb] at h0
  exact Option.some.inj h0

/-- Backward type after the whole slice (used by `ind` at the last position). -/
theorem tau_suf (n : ℕ) (q : M.Q) : tau M (wrappedFlat n) (2 * n + 2) q = M.accept q := by
  unfold tau
  rw [List.drop_eq_nil_of_le (by rw [length_wrappedFlat]; omega)]
  rfl

theorem wrappedFlat_getElem_last (n : ℕ) (hb : 2 * n + 1 < (wrappedFlat n).length) :
    (wrappedFlat n)[2 * n + 1] = D := by
  have hd := @List.getElem?_drop _ (wrappedFlat n) (1 + 2 * n) 0
  rw [SliceWords.wrappedFlat_drop n n (le_refl n), Nat.sub_self, Nat.add_zero,
    show 1 + 2 * n = 2 * n + 1 from by ring, List.getElem?_eq_getElem hb] at hd
  simpa using hd.symm

theorem ind_pre (n : ℕ) :
    ind M (wrappedFlat n) 0 =
      if M.accept (fStep M ((bF M)^[n] (M.δ M.q0 (U, true))) D) then 1 else 0 := by
  have hb : 0 < (wrappedFlat n).length := by rw [length_wrappedFlat]; omega
  have e : M.accepts (markAt (wrappedFlat n) 0) ↔
      M.accept (fStep M ((bF M)^[n] (M.δ M.q0 (U, true))) D) := by
    rw [accepts_markAt M (wrappedFlat n) 0 hb,
      show fwd M (wrappedFlat n) 0 = M.q0 from rfl, wrappedFlat_getElem_zero n hb,
      show (0 : ℕ) + 1 = 1 from rfl, tau_pre M n]
  unfold ind
  rw [if_congr e rfl rfl]

theorem ind_suf (n : ℕ) :
    ind M (wrappedFlat n) (2 * n + 1) =
      if M.accept (M.δ ((bF M)^[n] (qpre M)) (D, true)) then 1 else 0 := by
  have hb : 2 * n + 1 < (wrappedFlat n).length := by rw [length_wrappedFlat]; omega
  have e : M.accepts (markAt (wrappedFlat n) (2 * n + 1)) ↔
      M.accept (M.δ ((bF M)^[n] (qpre M)) (D, true)) := by
    rw [accepts_markAt M (wrappedFlat n) (2 * n + 1) hb,
      show fwd M (wrappedFlat n) (2 * n + 1) = (bF M)^[n] (qpre M) from by
        rw [show 2 * n + 1 = 1 + 2 * n from by ring]; exact fwd_blockStart M n n (le_refl n),
      wrappedFlat_getElem_last n hb, show 2 * n + 1 + 1 = 2 * n + 2 from by ring, tau_suf M n]
  unfold ind
  rw [if_congr e rfl rfl]

/-- **Count decomposition.**  The slice count splits into the two boundary
indicators and the per-block convolution sum. -/
theorem countAccept_wrappedFlat (n : ℕ) :
    countAccept M (wrappedFlat n) =
      ind M (wrappedFlat n) 0
      + (∑ j ∈ Finset.range n, blockC M ((bF M)^[j] (qpre M)) ((bF M)^[n - 1 - j]))
      + ind M (wrappedFlat n) (2 * n + 1) := by
  have hmid : (∑ i ∈ Finset.range (2 * n), ind M (wrappedFlat n) (i + 1))
      = ∑ j ∈ Finset.range n, blockC M ((bF M)^[j] (qpre M)) ((bF M)^[n - 1 - j]) := by
    rw [sum_pairs (fun i => ind M (wrappedFlat n) (i + 1)) n]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    show ind M (wrappedFlat n) (2 * j + 1) + ind M (wrappedFlat n) (2 * j + 1 + 1) = _
    rw [show 2 * j + 1 = 1 + 2 * j from by ring]
    exact ind_block M n j hj
  have hlen : (wrappedFlat n).length = 2 * n + 1 + 1 := by rw [length_wrappedFlat]; ring
  unfold countAccept
  rw [hlen, Finset.sum_range_succ', Finset.sum_range_succ]
  show (∑ i ∈ Finset.range (2 * n), ind M (wrappedFlat n) (i + 1))
      + ind M (wrappedFlat n) (2 * n + 1) + ind M (wrappedFlat n) 0 = _
  rw [hmid]
  ring

theorem ind_pre_affine : SliceAffine.AffineOnResidues (fun n => ind M (wrappedFlat n) 0) := by
  have := M.fintypeQ
  obtain ⟨m, p, hp, hper⟩ := SliceAutomata.iterate_eventuallyPeriodic (bF M) (M.δ M.q0 (U, true))
  refine SliceAffine.affineOnResidues_of_eventuallyPeriodic (m := m) (p := p) hp (fun n hn => ?_)
  rw [ind_pre M (n + p), ind_pre M n, hper n hn]

theorem ind_suf_affine :
    SliceAffine.AffineOnResidues (fun n => ind M (wrappedFlat n) (2 * n + 1)) := by
  have := M.fintypeQ
  obtain ⟨m, p, hp, hper⟩ := SliceAutomata.iterate_eventuallyPeriodic (bF M) (qpre M)
  refine SliceAffine.affineOnResidues_of_eventuallyPeriodic (m := m) (p := p) hp (fun n hn => ?_)
  rw [ind_suf M (n + p), ind_suf M n, hper n hn]

/-- **The slice selection count is affine on residue classes.**  For any
deterministic automaton `M` over `Step × Bool`, the number of positions `p` whose
single-mark word `markAt (W_n) p` is accepted is affine on residue classes of `n`. -/
theorem countAccept_slice_affineOnResidues :
    SliceAffine.AffineOnResidues (fun n => countAccept M (wrappedFlat n)) := by
  have hmid : SliceAffine.AffineOnResidues
      (fun n => ∑ j ∈ Finset.range n, blockC M ((bF M)^[j] (qpre M)) ((bF M)^[n - 1 - j])) := by
    obtain ⟨mu, pu, hpu, hu⟩ := bF_iterate_eventuallyPeriodic M
    obtain ⟨mv, pv, hpv, hv⟩ := bF_func_iterate_eventuallyPeriodic M
    exact SliceAffine.affineOnResidues_convolution_eventuallyPeriodic
      (fun j => (bF M)^[j] (qpre M)) (fun m => (bF M)^[m]) (blockC M)
      mu pu hpu hu mv pv hpv hv
  refine SliceAffine.AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_)
    (((ind_pre_affine M).add hmid).add (ind_suf_affine M))
  exact countAccept_wrappedFlat M n

end SliceCount
