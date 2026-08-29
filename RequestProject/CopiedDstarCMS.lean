import RequestProject.CopiedSetupMS
import RequestProject.CopiedDstarC

/-!
# d3.4 bridge — threshold- and period-EXPOSED depth recurrences (the §9 Stage F-mS linchpin)

The mS-direction tie-count route needs the suffix/prefix *depth* recurrences of a cell rank with
their period **and** their threshold exposed as parameters, uniformly in `(mS, n, t)`.  The
n-direction analogue can leave both hidden inside an `∃`, because there `dstar_setup_fibred` hands the
machine product back directly at the binder; in the mS direction `mS` couples both growing runs
through the automaton, so a hidden `∃ p` would be `mS,n`-dependent and no fixed period would divide it.

The file has three layers.

* **The mark-slide linchpin** (`iterate_mark_slide`, `foldl_window_slide`,
  `accepts_copiedSlice_suf_shift` / `accepts_copiedSlice_pref_shift`).  The depth collapse moves one
  boundary coordinate of a cell, not the whole base, so a naive move could slide one coordinate's mark
  across another's.  The move is therefore confined to a CLEAR sub-window `[s,e)` of the growing run
  that holds only the moving coordinate, and shifts its depth by a multiple of the unmarked machine
  cycle `p` while every in-window gap stays `≥ m`; then the marked-DFA gate is preserved.

* **`RankAffineAtFrom M Q F`** — affine-on-residues at period `Q` with the recurrence valid from the
  EXPOSED threshold `M` — together with its combinators (`const`, `mono`, `add`, `of_dvd`, `listSum`)
  and the two cell-level recurrences `rank_cell_sufStretch_threshold_uniform` /
  `rank_cell_prefStretch_threshold_uniform`, whose period and threshold are products/maxima over
  `κ.summands` of `endofunction_EP_mul`-derived per-summand data, hence `mS,n,ī0`-free.

* **The boundary collapse** (`coordCands_cycle_lengths`, `CoordCandRealizes`,
  `sufStretch_boundary_eq_coordCand`): per coordinate `(c, j0)` a single collapse period
  `pc` (gate cycle × rank period) and a single threshold `T = max(rank, gate)` with `T + pc < q_D`, and
  then the collapse of a suffix depth onto a boundary depth whose descriptor is a member of the
  `mS`-free candidate set `coordCands B q_U q_D`.
-/

namespace CopiedDstarCMS

open WRP Step CopiedRank CopiedCells SliceFamilyCell CopiedDstar SliceMarkN CopiedMark SliceMSO
  MSOMarkN SliceDstar CopiedSetupMS

/-! ## d3.4 content core — step 1: the uniform `l`-direction (depth) rank recurrence

The boundary collapse (`sufStretch_boundary_eq_coordCand`) runs `selBvec_le_member` in the DEPTH
direction at a period `lcm(depth-recurrence, gate-cycle)`.  For that `lcm` to be `mS`-FREE (so the
shallow/deep `coordCands` band width `q_D` is `mS`-free), the depth-recurrence period must itself be
`mS,n`-free.  A period obtained from `iterate_eventuallyPeriodic` on the start word `U^mS (UD)^n` would
be `mS,n`-DEPENDENT, so the suffix recurrence is re-derived here with the start-FREE
`endofunction_EP_mul` on the `D`-step: one `p_D`, depending only on `s.A`, serves every `mS, n` — the
slope may move with `mS,n`, the period may not.  (The prefix `p_U` is already `mS,n`-free via
`CopiedSetupMS.prefStretch_formula_rankAffine_q`.) -/

/-- **Tail-run decomposition**: the prefix-rank of `pre ++ x^N` over its whole length is the rank read
over `pre` plus the partial sum of block-weights of the `x`-block iterate started at the post-`pre`
state.  The tail-side mirror of the per-summand run decomposition. -/
theorem prefixRank_tail_decomp {Alpha : Type*} {d : ℕ} (A : RankSource Alpha d) (x : Alpha)
    (pre : List Alpha) (N : ℕ) :
    A.prefixRank (pre ++ List.replicate N x) (pre ++ List.replicate N x).length
      = (List.foldl (SliceRank.rankStep A) (A.q0, 0) pre).2
        + ∑ i ∈ Finset.range N,
            SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i] (List.foldl A.δ A.q0 pre)) := by
  rw [SliceRank.prefixRank_eq_foldl, List.foldl_append]
  obtain ⟨st, rk, hpr⟩ :
      ∃ st rk, List.foldl (SliceRank.rankStep A) (A.q0, 0) pre = (st, rk) := ⟨_, _, rfl⟩
  have hst : st = List.foldl A.δ A.q0 pre := by
    rw [← SliceRank.rankStep_fst A A.q0 0 pre, hpr]
  rw [hpr, SliceRank.rankStep_snd_add]
  have hflat : List.replicate N x = (List.replicate N [x]).flatten :=
    (CopiedRank.flatten_replicate_singleton x N).symm
  rw [hflat, SliceRank.foldl_rankStep_replicate_snd A [x] st 0 N, zero_add, hst]

/-! ## d3.4 step 2 — the LINCHPIN: gate invariance under a depth slide of one boundary coord

The mS-direction collapse must move a cell's MIDDLE-band suffix (resp. prefix) coordinates onto a
bounded representative without changing the gate.  Unlike the n-direction (a uniform whole-base group
shift), the depth collapse is per-coordinate, so a naive move could slide one coord's mark across
another's and change the foldl.  The resolution: each move stays inside a CLEAR sub-window `[s,e)` of
the growing run holding only the moving coord, and shifts its depth by a multiple of the unmarked
machine cycle `p` while every in-window gap stays `≥ m`.  Then the gate is preserved.

The whole argument collapses to a 4-line abstract identity, `iterate_mark_slide`: a marked step `g`
between two unmarked-`f` runs whose gaps differ by `p*κ` (both `≥ m`) is invariant
(`f^[R] (g (f^[A] q)) = f^[R'] (g (f^[A'] q))`).  `foldl_window_slide` lifts it to one clear `markSeg`
window; the two capstones (`accepts_copiedSlice_suf_shift` / `_pref_shift`) wrap it with
`markAtN_copiedSlice` + `markSeg_congr_outside` (the untouched U-prefix / middle / D-suffix segments are
identical between the source and target tuples). -/

/-- **Abstract single-mark slide.**  A marked transition `g` sandwiched between two unmarked-`f` runs
whose left/right gaps differ by a common multiple `p*κ` of the period (and stay `≥ m`) leaves the
composite state unchanged. -/
theorem iterate_mark_slide {Q : Type*} (f g : Q → Q) (m p : ℕ)
    (hper : ∀ κ b, m ≤ b → f^[b + p * κ] = f^[b])
    {A R A' R' κ : ℕ}
    (hA' : A' = A + p * κ) (hR : R = R' + p * κ) (hA : m ≤ A) (hR' : m ≤ R')
    (q : Q) :
    f^[R] (g (f^[A] q)) = f^[R'] (g (f^[A'] q)) := by
  have e1 : f^[A'] q = f^[A] q := by rw [hA', hper κ A hA]
  have e2 : f^[R] = f^[R'] := by rw [hR, hper κ R' hR']
  rw [e1, e2]

/-- **Single-mark clear-window decomposition of `markSeg`.**  Over a `len`-letter run of `x`s at offset
`off` in which the ONLY in-window mark is coord `j0` (at relative depth `a`), the marked segment factors
as an unmarked left run, the single marked letter (bit `j0` only), and an unmarked right run. -/
theorem markSeg_single_window {k : ℕ} (x : Step) (ī : Fin k → ℕ) (j0 : Fin k)
    (off a len : ℕ) (ha : a < len) (hj0 : ī j0 = off + a)
    (hclear : ∀ i, i ≠ j0 → ī i < off ∨ off + len ≤ ī i) :
    markSeg k (List.replicate len x) ī off
      = unmark k (List.replicate a x)
        ++ (mkLetter k x (fun i => decide (i = j0))
              :: unmark k (List.replicate (len - a - 1) x)) := by
  have hsplit : List.replicate len x
      = List.replicate a x ++ (x :: List.replicate (len - a - 1) x) := by
    rw [← List.replicate_succ, ← List.replicate_add]
    congr 1; omega
  rw [hsplit, markSeg_append, List.length_replicate]
  congr 1
  · -- left part is unmarked
    apply markSeg_unmarked
    intro i
    rw [List.length_replicate]
    by_cases hi : i = j0
    · subst hi; right; omega
    · rcases hclear i hi with h | h
      · left; exact h
      · right; omega
  · -- marked letter :: right part
    rw [markSeg_cons]
    congr 1
    · -- the marked letter's bit vector is exactly `{j0}`
      congr 1
      funext i
      simp only [bitsAt]
      by_cases hi : i = j0
      · subst hi; rw [hj0]; simp
      · rw [decide_eq_false (by
          rcases hclear i hi with h | h
          · omega
          · omega), decide_eq_false hi]
    · -- right part is unmarked
      apply markSeg_unmarked
      intro i
      rw [List.length_replicate]
      by_cases hi : i = j0
      · subst hi; left; omega
      · rcases hclear i hi with h | h
        · left; omega
        · right; omega

/-- The foldl over a single-mark clear window, in the `f^[R] (g (f^[A] q))` slide shape. -/
theorem foldl_markSeg_single_window {k : ℕ} (M : DetAuto (MarkedN k)) (x : Step) (ī : Fin k → ℕ)
    (j0 : Fin k) (off a len : ℕ) (ha : a < len) (hj0 : ī j0 = off + a)
    (hclear : ∀ i, i ≠ j0 → ī i < off ∨ off + len ≤ ī i) (q : M.Q) :
    List.foldl M.δ q (markSeg k (List.replicate len x) ī off)
      = (fun s => M.δ s (mkLetter k x (fun _ => false)))^[len - a - 1]
          (M.δ ((fun s => M.δ s (mkLetter k x (fun _ => false)))^[a] q)
               (mkLetter k x (fun i => decide (i = j0)))) := by
  rw [markSeg_single_window x ī j0 off a len ha hj0 hclear, List.foldl_append, List.foldl_cons]
  have hunmark : ∀ (b : ℕ), unmark k (List.replicate b x)
      = List.replicate b (mkLetter k x (fun _ => false)) := by
    intro b; rw [unmark, List.map_replicate]
  rw [hunmark, hunmark, CopiedRank.foldl_replicate_iterate,
    CopiedRank.foldl_replicate_iterate]

/-- **The window slide workhorse.**  Within a clear window `x^winLen` at offset `winStart` holding only
coord `j0`, sliding `j0` from relative depth `a` to `a'` (differing by `p*κ`, all in-window gaps `≥ m`)
leaves the foldl from any start state unchanged. -/
theorem foldl_window_slide {k : ℕ} (M : DetAuto (MarkedN k)) (x : Step)
    (ī ī' : Fin k → ℕ) (j0 : Fin k) (winStart winLen a a' κ m p : ℕ)
    (hper : ∀ κ b, m ≤ b → (fun s => M.δ s (mkLetter k x (fun _ => false)))^[b + p * κ]
                          = (fun s => M.δ s (mkLetter k x (fun _ => false)))^[b])
    (hsame : ∀ i, i ≠ j0 → ī i = ī' i)
    (hj0 : ī j0 = winStart + a) (hj0' : ī' j0 = winStart + a')
    (ha : a < winLen) (ha' : a' < winLen)
    (hclear : ∀ i, i ≠ j0 → ī i < winStart ∨ winStart + winLen ≤ ī i)
    (hgapA : m ≤ a) (hgapA' : m ≤ a') (hgapR : m ≤ winLen - 1 - a) (hgapR' : m ≤ winLen - 1 - a')
    (hshift : a' = a + p * κ ∨ a = a' + p * κ) (qstart : M.Q) :
    List.foldl M.δ qstart (markSeg k (List.replicate winLen x) ī winStart)
      = List.foldl M.δ qstart (markSeg k (List.replicate winLen x) ī' winStart) := by
  have hclear' : ∀ i, i ≠ j0 → ī' i < winStart ∨ winStart + winLen ≤ ī' i := by
    intro i hi; rw [← hsame i hi]; exact hclear i hi
  rw [foldl_markSeg_single_window M x ī j0 winStart a winLen ha hj0 hclear,
      foldl_markSeg_single_window M x ī' j0 winStart a' winLen ha' hj0' hclear']
  rcases hshift with h | h
  · exact iterate_mark_slide (fun s => M.δ s (mkLetter k x (fun _ => false)))
      (fun s => M.δ s (mkLetter k x (fun i => decide (i = j0)))) m p hper
      (A := a) (R := winLen - a - 1) (A' := a') (R' := winLen - a' - 1) (κ := κ)
      h (by omega) hgapA (by omega) qstart
  · exact (iterate_mark_slide (fun s => M.δ s (mkLetter k x (fun _ => false)))
      (fun s => M.δ s (mkLetter k x (fun i => decide (i = j0)))) m p hper
      (A := a') (R := winLen - a' - 1) (A' := a) (R' := winLen - a - 1) (κ := κ)
      h (by omega) hgapA' (by omega) qstart).symm

/-- **Gate invariance under a suffix-coord depth slide (the linchpin, suffix side).**  Moving coord
`j0` (a D-suffix coord at depth `a`) to depth `a'` inside a clear sub-window `[s,e)` of the D-suffix,
with the depths differing by `p*κ` (`p` = the unmarked-D machine cycle) and all in-window gaps `≥ m`,
preserves cell acceptance on the copied slice. -/
theorem accepts_copiedSlice_suf_shift {k : ℕ} (M : DetAuto (MarkedN k)) (mS n : ℕ) (hm : 1 ≤ mS)
    (ī ī' : Fin k → ℕ) (j0 : Fin k) (s e a a' κ m p : ℕ)
    (hper : ∀ κ b, m ≤ b → (fun st => M.δ st (mkLetter k D (fun _ => false)))^[b + p * κ]
                          = (fun st => M.δ st (mkLetter k D (fun _ => false)))^[b])
    (hsame : ∀ i, i ≠ j0 → ī i = ī' i)
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hj0 : ī j0 = mS + 2 * n + 1 + a) (hj0' : ī' j0 = mS + 2 * n + 1 + a')
    (hclear : ∀ i, i ≠ j0 → ī i < mS + 2 * n + 1 + s ∨ mS + 2 * n + 1 + e ≤ ī i)
    (hgapA : m ≤ a - s) (hgapA' : m ≤ a' - s) (hgapR : m ≤ e - 1 - a) (hgapR' : m ≤ e - 1 - a')
    (hshift : a' = a + p * κ ∨ a = a' + p * κ) :
    M.accepts (markAtN k (copiedSlice mS n) ī) ↔ M.accepts (markAtN k (copiedSlice mS n) ī') := by
  -- boundary segments (U-prefix, middle) are identical: j0 lives in the D-suffix
  have hUpre : markSeg k (List.replicate (mS - 1) U) ī 0
      = markSeg k (List.replicate (mS - 1) U) ī' 0 := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; rw [List.length_replicate]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    · exact Or.inl (hsame i hi)
  have hMid : markSeg k (wrappedFlat n) ī (mS - 1) = markSeg k (wrappedFlat n) ī' (mS - 1) := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; rw [length_wrappedFlat]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    · exact Or.inl (hsame i hi)
  -- D-suffix split: Dleft (clear) ++ Dwin (the slide window) ++ Dright (clear)
  have hDsplit : ∀ (j : Fin k → ℕ),
      markSeg k (List.replicate (mS - 1) D) j (mS + 2 * n + 1)
      = markSeg k (List.replicate s D) j (mS + 2 * n + 1)
        ++ markSeg k (List.replicate (e - s) D) j (mS + 2 * n + 1 + s)
        ++ markSeg k (List.replicate (mS - 1 - e) D) j (mS + 2 * n + 1 + e) := by
    intro j
    have hrep : List.replicate (mS - 1) D
        = (List.replicate s D ++ List.replicate (e - s) D) ++ List.replicate (mS - 1 - e) D := by
      rw [List.append_assoc, ← List.replicate_add, ← List.replicate_add]; congr 1; omega
    rw [hrep, markSeg_append, markSeg_append, List.length_replicate, List.length_append,
      List.length_replicate, List.length_replicate]
    congr 2
    omega
  have hDleft : markSeg k (List.replicate s D) ī (mS + 2 * n + 1)
      = markSeg k (List.replicate s D) ī' (mS + 2 * n + 1) := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; rw [List.length_replicate]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    · exact Or.inl (hsame i hi)
  have hDright : markSeg k (List.replicate (mS - 1 - e) D) ī (mS + 2 * n + 1 + e)
      = markSeg k (List.replicate (mS - 1 - e) D) ī' (mS + 2 * n + 1 + e) := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · exact Or.inl (hsame i hi)
  -- the window slide
  have hwin : List.foldl M.δ
        (List.foldl M.δ M.q0
          (markSeg k (List.replicate (mS - 1) U) ī' 0 ++ markSeg k (wrappedFlat n) ī' (mS - 1)
            ++ markSeg k (List.replicate s D) ī' (mS + 2 * n + 1)))
        (markSeg k (List.replicate (e - s) D) ī (mS + 2 * n + 1 + s))
      = List.foldl M.δ
        (List.foldl M.δ M.q0
          (markSeg k (List.replicate (mS - 1) U) ī' 0 ++ markSeg k (wrappedFlat n) ī' (mS - 1)
            ++ markSeg k (List.replicate s D) ī' (mS + 2 * n + 1)))
        (markSeg k (List.replicate (e - s) D) ī' (mS + 2 * n + 1 + s)) := by
    apply foldl_window_slide M D ī ī' j0 (mS + 2 * n + 1 + s) (e - s) (a - s) (a' - s) κ m p hper hsame
    · rw [hj0]; omega
    · rw [hj0']; omega
    · omega
    · omega
    · intro i hi; rcases hclear i hi with h | h
      · left; omega
      · right; omega
    · exact hgapA
    · exact hgapA'
    · omega
    · omega
    · rcases hshift with h | h
      · left; omega
      · right; omega
  -- assemble
  have key : List.foldl M.δ M.q0 (markAtN k (copiedSlice mS n) ī)
      = List.foldl M.δ M.q0 (markAtN k (copiedSlice mS n) ī') := by
    rw [markAtN_copiedSlice k mS n hm, markAtN_copiedSlice k mS n hm, hUpre, hMid,
      hDsplit ī, hDsplit ī', hDleft, hDright]
    have hL : ∀ (W : List (MarkedN k)),
        List.foldl M.δ M.q0 (markSeg k (List.replicate (mS - 1) U) ī' 0
            ++ markSeg k (wrappedFlat n) ī' (mS - 1)
            ++ (markSeg k (List.replicate s D) ī' (mS + 2 * n + 1) ++ W
                ++ markSeg k (List.replicate (mS - 1 - e) D) ī' (mS + 2 * n + 1 + e)))
          = List.foldl M.δ (List.foldl M.δ
              (List.foldl M.δ M.q0 (markSeg k (List.replicate (mS - 1) U) ī' 0
                ++ markSeg k (wrappedFlat n) ī' (mS - 1)
                ++ markSeg k (List.replicate s D) ī' (mS + 2 * n + 1))) W)
              (markSeg k (List.replicate (mS - 1 - e) D) ī' (mS + 2 * n + 1 + e)) := by
      intro W
      rw [← List.append_assoc, ← List.append_assoc, List.foldl_append, List.foldl_append]
    rw [hL, hL]
    exact congrArg
      (fun st => List.foldl M.δ st (markSeg k (List.replicate (mS - 1 - e) D) ī' (mS + 2 * n + 1 + e)))
      hwin
  have hacc : M.accepts (markAtN k (copiedSlice mS n) ī)
      = M.accepts (markAtN k (copiedSlice mS n) ī') := by
    unfold DetAuto.accepts; rw [key]
  rw [hacc]

/-- Updating a descriptor coordinate to `sufIdx l` updates the corresponding
cell-tuple position to the copied-slice suffix position. -/
theorem cellTupleF_update_sufIdx {B k : ℕ} (rs : Fin k → RegionSpecF B)
    (j0 : Fin k) (mS t n l : ℕ) :
    cellTupleF (Function.update rs j0 (RegionSpecF.sufIdx l)) mS t n =
      Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l) := by
  funext i
  by_cases hi : i = j0
  · subst hi
    simp only [cellTupleF, Function.update_self, RegionSpecF.posAt]
  · simp only [cellTupleF, Function.update_of_ne hi]

/-- **Gate invariance under a prefix-coord depth slide (the linchpin, prefix side).**  Moving coord
`j0` (a U-prefix coord at depth `a`) to depth `a'` inside a clear sub-window `[s,e)` of the U-prefix,
with the depths differing by `p*κ` (`p` = the unmarked-U machine cycle) and all in-window gaps `≥ m`,
preserves cell acceptance on the copied slice. -/
theorem accepts_copiedSlice_pref_shift {k : ℕ} (M : DetAuto (MarkedN k)) (mS n : ℕ) (hm : 1 ≤ mS)
    (ī ī' : Fin k → ℕ) (j0 : Fin k) (s e a a' κ m p : ℕ)
    (hper : ∀ κ b, m ≤ b → (fun st => M.δ st (mkLetter k U (fun _ => false)))^[b + p * κ]
                          = (fun st => M.δ st (mkLetter k U (fun _ => false)))^[b])
    (hsame : ∀ i, i ≠ j0 → ī i = ī' i)
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hj0 : ī j0 = a) (hj0' : ī' j0 = a')
    (hclear : ∀ i, i ≠ j0 → ī i < s ∨ e ≤ ī i)
    (hgapA : m ≤ a - s) (hgapA' : m ≤ a' - s) (hgapR : m ≤ e - 1 - a) (hgapR' : m ≤ e - 1 - a')
    (hshift : a' = a + p * κ ∨ a = a' + p * κ) :
    M.accepts (markAtN k (copiedSlice mS n) ī) ↔ M.accepts (markAtN k (copiedSlice mS n) ī') := by
  -- middle and D-suffix segments are identical: j0 lives in the U-prefix
  have hMid : markSeg k (wrappedFlat n) ī (mS - 1) = markSeg k (wrappedFlat n) ī' (mS - 1) := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · exact Or.inl (hsame i hi)
  have hDsuf : markSeg k (List.replicate (mS - 1) D) ī (mS + 2 * n + 1)
      = markSeg k (List.replicate (mS - 1) D) ī' (mS + 2 * n + 1) := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · exact Or.inl (hsame i hi)
  -- U-prefix split: Uleft (clear) ++ Uwin (the slide window) ++ Uright (clear)
  have hUsplit : ∀ (j : Fin k → ℕ),
      markSeg k (List.replicate (mS - 1) U) j 0
      = markSeg k (List.replicate s U) j 0
        ++ markSeg k (List.replicate (e - s) U) j s
        ++ markSeg k (List.replicate (mS - 1 - e) U) j e := by
    intro j
    have hrep : List.replicate (mS - 1) U
        = (List.replicate s U ++ List.replicate (e - s) U) ++ List.replicate (mS - 1 - e) U := by
      rw [List.append_assoc, ← List.replicate_add, ← List.replicate_add]; congr 1; omega
    rw [hrep, markSeg_append, markSeg_append]
    simp only [List.length_append, List.length_replicate, Nat.zero_add]
    congr 2
    omega
  have hUleft : markSeg k (List.replicate s U) ī 0 = markSeg k (List.replicate s U) ī' 0 := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; rw [List.length_replicate]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    · exact Or.inl (hsame i hi)
  have hUright : markSeg k (List.replicate (mS - 1 - e) U) ī e
      = markSeg k (List.replicate (mS - 1 - e) U) ī' e := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · exact Or.inl (hsame i hi)
  -- the window slide
  have hwin : List.foldl M.δ (List.foldl M.δ M.q0 (markSeg k (List.replicate s U) ī' 0))
        (markSeg k (List.replicate (e - s) U) ī s)
      = List.foldl M.δ (List.foldl M.δ M.q0 (markSeg k (List.replicate s U) ī' 0))
        (markSeg k (List.replicate (e - s) U) ī' s) := by
    apply foldl_window_slide M U ī ī' j0 s (e - s) (a - s) (a' - s) κ m p hper hsame
    · rw [hj0]; omega
    · rw [hj0']; omega
    · omega
    · omega
    · intro i hi; rcases hclear i hi with h | h
      · left; omega
      · right; omega
    · exact hgapA
    · exact hgapA'
    · omega
    · omega
    · rcases hshift with h | h
      · left; omega
      · right; omega
  -- assemble
  have key : List.foldl M.δ M.q0 (markAtN k (copiedSlice mS n) ī)
      = List.foldl M.δ M.q0 (markAtN k (copiedSlice mS n) ī') := by
    rw [markAtN_copiedSlice k mS n hm, markAtN_copiedSlice k mS n hm, hMid, hDsuf,
      hUsplit ī, hUsplit ī', hUleft, hUright]
    simp only [List.foldl_append]
    rw [hwin]
  have hacc : M.accepts (markAtN k (copiedSlice mS n) ī)
      = M.accepts (markAtN k (copiedSlice mS n) ī') := by
    unfold DetAuto.accepts; rw [key]
  rw [hacc]

/-- Updating a descriptor coordinate to `prefIdx q` updates the corresponding
cell-tuple position to the copied-slice prefix position. -/
theorem cellTupleF_update_prefIdx {B k : ℕ} (rs : Fin k → RegionSpecF B)
    (j0 : Fin k) (mS t n q : ℕ) :
    cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q)) mS t n =
      Function.update (cellTupleF rs mS t n) j0 q := by
  funext i
  by_cases hi : i = j0
  · subst hi
    simp only [cellTupleF, Function.update_self, RegionSpecF.posAt]
  · simp only [cellTupleF, Function.update_of_ne hi]

-- Threshold-EXPOSING per-summand depth recurrence: the `∃ p_D mD` is hoisted outside `∀ mS n`,
-- so both the period `p_D` and the threshold `mD` are `mS,n`-free.
theorem sufStretch_formula_rankAffine_l_uniform' {k : ℕ} (s : Summand Step d k) :
    ∃ p_D mD, 1 ≤ p_D ∧ ∀ mS n, ∃ (P : Fin d → ℤ), ∀ l, mD ≤ l →
      ( s.coeff • s.A.prefixRank
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1 + p_D) D)
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten
            ++ List.replicate (l + 1 + p_D) D).length
        + s.β (List.foldl s.A.δ
            ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
            (List.replicate (l + 1 + p_D) D)) D )
      = ( s.coeff • s.A.prefixRank
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten
            ++ List.replicate (l + 1) D).length
        + s.β (List.foldl s.A.δ
            ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
            (List.replicate (l + 1) D)) D )
      + P := by
  have := s.A.fintypeQ
  obtain ⟨mD, pD, hpD, hcyc⟩ := endofunction_EP_mul (fun q => s.A.δ q D)
  refine ⟨pD, mD, hpD, fun mS n => ?_⟩
  set pre : List Step := List.replicate mS U ++ (List.replicate n [U, D]).flatten with hpre
  have hstpre : (fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U))
      = List.foldl s.A.δ s.A.q0 pre := by
    rw [hpre, List.foldl_append, SliceMSO.foldl_replicate_flatten]
  set stpre : s.A.Q := List.foldl s.A.δ s.A.q0 pre with hstdef
  have hbsD : SliceRank.blockStep s.A [D] = fun q => s.A.δ q D := by funext q; rfl
  have hgper : ∀ i, mD ≤ i →
      SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[i + pD] stpre)
        = SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[i] stpre) := by
    intro i hi
    rw [hbsD]
    have := hcyc 1 i hi
    rw [show i + pD * 1 = i + pD by ring] at this
    rw [this]
  set Δ : Fin d → ℤ := ∑ j ∈ Finset.Ico mD (mD + pD),
    SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[j] stpre) with hΔ
  refine ⟨s.coeff • Δ, fun l hl => ?_⟩
  have hPA : s.A.prefixRank
      (pre ++ List.replicate (l + 1 + pD) D) (pre ++ List.replicate (l + 1 + pD) D).length
      = s.A.prefixRank (pre ++ List.replicate (l + 1) D) (pre ++ List.replicate (l + 1) D).length
        + Δ := by
    rw [prefixRank_tail_decomp s.A D pre (l + 1 + pD), prefixRank_tail_decomp s.A D pre (l + 1),
      SliceAutomata.partialSum_recurrence'
        (fun i => SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[i] stpre)) mD pD hgper
        (l + 1) (by omega), ← hΔ]
    abel
  have hPB : s.β (List.foldl s.A.δ stpre (List.replicate (l + 1 + pD) D)) D
      = s.β (List.foldl s.A.δ stpre (List.replicate (l + 1) D)) D := by
    rw [CopiedRank.foldl_replicate_iterate s.A.δ D stpre (l + 1 + pD),
      CopiedRank.foldl_replicate_iterate s.A.δ D stpre (l + 1)]
    have hc := hcyc 1 (l + 1) (by omega)
    rw [Nat.mul_one] at hc
    rw [hc]
  rw [hstpre, hPB, hPA, smul_add]
  abel

/-! ### RankAffineAtFrom: threshold-EXPOSED affine-on-residues (period AND threshold parameters). -/

/-- `F` is affine-on-residues at period `Q` with the recurrence valid from the EXPOSED threshold `M`.
Exposing `M` as a parameter (rather than hiding it in an `∃ m`) is what lets the d3.4 boundary collapse
bound the shallow endpoint depth `M + r` against the `mS`-free band width `q_D`. -/
def RankAffineAtFrom (M Q : ℕ) (F : ℕ → Fin d → ℤ) : Prop :=
  ∃ P : Fin d → ℤ, ∀ l, M ≤ l → F (l + Q) = F l + P

theorem RankAffineAtFrom.const (M Q : ℕ) (v : Fin d → ℤ) : RankAffineAtFrom M Q (fun _ => v) :=
  ⟨0, fun _ _ => by simp⟩

theorem RankAffineAtFrom.mono {M M' Q : ℕ} {F : ℕ → Fin d → ℤ}
    (h : RankAffineAtFrom M Q F) (hMM' : M ≤ M') : RankAffineAtFrom M' Q F := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun l hl => hP l (le_trans hMM' hl)⟩

theorem RankAffineAtFrom.add {M Q : ℕ} {F G : ℕ → Fin d → ℤ}
    (hF : RankAffineAtFrom M Q F) (hG : RankAffineAtFrom M Q G) :
    RankAffineAtFrom M Q (fun l => F l + G l) := by
  obtain ⟨PF, hF⟩ := hF
  obtain ⟨PG, hG⟩ := hG
  refine ⟨PF + PG, fun l hl => ?_⟩
  show F (l + Q) + G (l + Q) = (F l + G l) + (PF + PG)
  rw [hF l hl, hG l hl]; abel

/-- Lift the period of a `RankAffineAtFrom` to any multiple (threshold unchanged). -/
theorem RankAffineAtFrom.of_dvd {M Q : ℕ} {F : ℕ → Fin d → ℤ} {p : ℕ}
    (h : RankAffineAtFrom M p F) (hpQ : p ∣ Q) : RankAffineAtFrom M Q F := by
  obtain ⟨P, hrec⟩ := h
  obtain ⟨k, rfl⟩ := hpQ
  exact ⟨k • P, fun l hl => SliceRankAtom.RankAffine.iterate hrec l k hl⟩

/-- A list-sum at a COMMON exposed threshold `M` and period `Q`. -/
theorem RankAffineAtFrom.listSum {ι : Type*} (L : List ι) (M Q : ℕ) (g : ι → ℕ → Fin d → ℤ)
    (h : ∀ i ∈ L, RankAffineAtFrom M Q (g i)) :
    RankAffineAtFrom M Q (fun l => (L.map (fun i => g i l)).sum) := by
  induction L with
  | nil => simpa using RankAffineAtFrom.const M Q (0 : Fin d → ℤ)
  | cons a L' ih =>
      have ha := h a (List.mem_cons.mpr (Or.inl rfl))
      have ih' := ih (fun i hi => h i (List.mem_cons.mpr (Or.inr hi)))
      obtain ⟨P, hrec⟩ := ha.add ih'
      exact ⟨P, fun l hl => by simpa [List.map_cons, List.sum_cons] using hrec l hl⟩

/-! ### Cell-level threshold-exposed recurrences (suffix + prefix). -/

/-- **Suffix cell rank, threshold EXPOSED** (Option-B of d3.4 step 3): the cell rank as a function of
suffix depth `l` is `RankAffineAtFrom M Q` at one `mS,n,ī0`-FREE period `Q` AND threshold `M` (both =
products / maxes over `κ.summands` of the `endofunction_EP_mul`-derived per-summand period / threshold). -/
theorem rank_cell_sufStretch_threshold_uniform (P : WRP.Presentation Step Step)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) :
    ∃ Q M, 1 ≤ Q ∧ ∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n : ℕ),
      ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom M Q F ∧
        (∀ l, l < mS - 1 → P.rank c (copiedSlice mS n)
          (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  choose pf mDf hpf using fun s : Summand Step P.d (P.toPoly.arity c) =>
    sufStretch_formula_rankAffine_l_uniform' s
  refine ⟨(κ.summands.map pf).prod, (κ.summands.map mDf).sum, ?_, fun ī0 mS n => ?_⟩
  · exact List.one_le_prod_of_one_le (by
      intro x hx; obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx; exact (hpf s).1)
  · set M := (κ.summands.map mDf).sum with hMdef
    refine ⟨fun l => κ.c0 + (κ.summands.map (fun s =>
        if s.π = j0 then
          s.coeff • s.A.prefixRank
              (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
              (List.replicate mS U ++ (List.replicate n [U, D]).flatten
                ++ List.replicate (l + 1) D).length
            + s.β (List.foldl s.A.δ
                ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
                (List.replicate (l + 1) D)) D
        else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π)))).sum, ?_, ?_⟩
    · -- period+threshold leg
      refine (RankAffineAtFrom.const M _ κ.c0).add
        (RankAffineAtFrom.listSum κ.summands M _ _ (fun s hs => ?_))
      by_cases hπ : s.π = j0
      · have hpQ : pf s ∣ (κ.summands.map pf).prod := List.dvd_prod (by
          exact List.mem_map.mpr ⟨s, hs, rfl⟩)
        obtain ⟨Pv, hrec⟩ := (hpf s).2 mS n
        have hform : RankAffineAtFrom (mDf s) (pf s)
            (fun l => if s.π = j0 then
              s.coeff • s.A.prefixRank
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten
                    ++ List.replicate (l + 1) D).length
                + s.β (List.foldl s.A.δ
                    ((fun q => List.foldl s.A.δ q [U, D])^[n]
                      (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
                    (List.replicate (l + 1) D)) D
              else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π))) := by
          refine ⟨Pv, fun l hl => ?_⟩
          simp only [if_pos hπ]
          rw [show l + pf s + 1 = l + 1 + pf s from by omega]
          exact hrec l hl
        exact ((hform.of_dvd hpQ).mono
          (by rw [hMdef]; exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem (f := mDf) hs)))
      · have heq : (fun l => if s.π = j0 then
              s.coeff • s.A.prefixRank
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten
                    ++ List.replicate (l + 1) D).length
                + s.β (List.foldl s.A.δ
                    ((fun q => List.foldl s.A.δ q [U, D])^[n]
                      (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
                    (List.replicate (l + 1) D)) D
              else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π)))
            = (fun _ => s.eval (copiedSlice mS n) (fun _ => ī0 (s.π))) := by
          funext l; simp only [if_neg hπ]
        rw [heq]; exact RankAffineAtFrom.const _ _ _
    · -- agreement leg (verbatim rank_cell_sufStretch_rankAffine_l_uniform)
      intro l hl
      rw [hκ (copiedSlice mS n) _, SliceFamilyRank.rankTerm_eval_proj]
      funext c'
      simp only [Pi.add_apply]
      rw [SliceFamilyRank.list_sum_pi_apply]
      refine congrArg (κ.c0 c' + ·) (congrArg List.sum (List.map_congr_left (fun s _ => ?_)))
      by_cases hπ : s.π = j0
      · rw [if_pos hπ, hπ, Function.update_self]
        exact congrFun (summand_copied_sufStretch_eq s mS l hl n) c'
      · rw [if_neg hπ, Function.update_of_ne hπ]

/-- **Prefix cell rank, threshold EXPOSED** (Option-B of d3.4 step 3): mirror of the suffix, but the
underlying `prefStretch_formula_rankAffine_q` is already `mS,n`-free so its threshold `mf s` is exposed
directly — no primed per-summand lemma needed. -/
theorem rank_cell_prefStretch_threshold_uniform (P : WRP.Presentation Step Step)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) :
    ∃ Q M, 1 ≤ Q ∧ ∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n : ℕ),
      ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom M Q F ∧
        (∀ q, q < mS - 1 → P.rank c (copiedSlice mS n) (Function.update ī0 j0 q) = F q) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  choose mf pf Pf hf using fun s : Summand Step P.d (P.toPoly.arity c) =>
    prefStretch_formula_rankAffine_q s
  refine ⟨(κ.summands.map pf).prod, (κ.summands.map mf).sum, ?_, fun ī0 mS n => ?_⟩
  · exact List.one_le_prod_of_one_le (by
      intro x hx; obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx; exact (hf s).1)
  · set M := (κ.summands.map mf).sum with hMdef
    refine ⟨fun q => κ.c0 + (κ.summands.map (fun s =>
        if s.π = j0 then
          s.coeff • s.A.prefixRank (List.replicate q U) (List.replicate q U).length
            + s.β (List.foldl s.A.δ s.A.q0 (List.replicate q U)) U
        else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π)))).sum, ?_, ?_⟩
    · refine (RankAffineAtFrom.const M _ κ.c0).add
        (RankAffineAtFrom.listSum κ.summands M _ _ (fun s hs => ?_))
      by_cases hπ : s.π = j0
      · have hpQ : pf s ∣ (κ.summands.map pf).prod := List.dvd_prod (by
          exact List.mem_map.mpr ⟨s, hs, rfl⟩)
        have hform : RankAffineAtFrom (mf s) (pf s)
            (fun q => if s.π = j0 then
              s.coeff • s.A.prefixRank (List.replicate q U) (List.replicate q U).length
                + s.β (List.foldl s.A.δ s.A.q0 (List.replicate q U)) U
              else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π))) := by
          refine ⟨Pf s, fun q hq => ?_⟩
          simp only [if_pos hπ]
          exact (hf s).2 q hq
        exact ((hform.of_dvd hpQ).mono
          (by rw [hMdef]; exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem (f := mf) hs)))
      · have heq : (fun q => if s.π = j0 then
              s.coeff • s.A.prefixRank (List.replicate q U) (List.replicate q U).length
                + s.β (List.foldl s.A.δ s.A.q0 (List.replicate q U)) U
              else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π)))
            = (fun _ => s.eval (copiedSlice mS n) (fun _ => ī0 (s.π))) := by
          funext q; simp only [if_neg hπ]
        rw [heq]; exact RankAffineAtFrom.const _ _ _
    · intro q hq
      rw [hκ (copiedSlice mS n) _, SliceFamilyRank.rankTerm_eval_proj]
      funext c'
      simp only [Pi.add_apply]
      rw [SliceFamilyRank.list_sum_pi_apply]
      refine congrArg (κ.c0 c' + ·) (congrArg List.sum (List.map_congr_left (fun s _ => ?_)))
      by_cases hπ : s.π = j0
      · rw [if_pos hπ, hπ, Function.update_self]
        exact congrFun (summand_copied_prefStretch_eq s mS q hq n) c'
      · rw [if_neg hπ, Function.update_of_ne hπ]

/-! ### d3.4 step 3 (Option B'', single threshold) + step 4 boundary collapse.
Step 3 exposes, per coordinate `(c,j0)`, a combined period `pc = pg·Q` and a SINGLE threshold
`T = max(rank threshold, gate threshold)` with `T + pc < q_D`: the bundled `T` is what step 5 needs so
the SHALLOW collapse endpoint `T + r ≥ T ≥ mg` clears the gate before-gap.  Step 4 takes a band bound `N`
(step-5 passes `mS-1-T`) so the DEEP endpoint stays `≥ T` from the suffix end (after-gap), outputs
`M ≤ l_bd` / `l_bd < N` (before/after gaps for step 5), the gate shift (a multiple of `pc`), and the
value domination.  (Arity-1 has one coordinate per cell, so step 5 = step 4 with vacuous clear-window;
the general-arity collapse is blocked by coordinate crossing.) -/

/-- **Revised step 3 (Option B'', single threshold).**  For each suffix/prefix coordinate `(c, j0)`,
exposes a SINGLE collapse period `pc` (= gate cycle × rank period) AND a SINGLE threshold
`T = max(rank threshold, gate threshold)` with `T + pc < q_D`, the gate cyclicity from `T`, and the rank
recurrence `RankAffineAtFrom T pc`.  Bundling the gate threshold `mg` into `T` is what step 5 needs: the
SHALLOW collapse endpoint `T + r ≥ T ≥ mg` clears the gate before-gap, and `T + pc < q_D` keeps it inside
the band.  `q_D`/`q_U` is the additive budget. -/
theorem coordCands_cycle_lengths (P : WRP.Presentation Step Step)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (lo : ℕ) :
    ∃ q_U q_D : ℕ, lo < q_U ∧ lo < q_D ∧
      (∀ c (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
        (∀ κ b, T ≤ b →
          (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
            = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
        (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
          RankAffineAtFrom T pc F ∧
          (∀ l, l < mS - 1 → P.rank c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l))) ∧
      (∀ c (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
        (∀ κ b, T ≤ b →
          (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
            = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
        (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
          RankAffineAtFrom T pc F ∧
          (∀ q, q < mS - 1 → P.rank c (copiedSlice mS n) (Function.update ī0 j0 q) = F q))) := by
  classical
  choose mgD gateDcyc hgD using fun c => by
    have := (Mc c).fintypeQ
    exact endofunction_EP_mul (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))
  choose mgU gateUcyc hgU using fun c => by
    have := (Mc c).fintypeQ
    exact endofunction_EP_mul (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))
  choose Qsuf Msuf hsuf using fun c j0 => rank_cell_sufStretch_threshold_uniform P c j0
  choose Qpref Mpref hpref using fun c j0 => rank_cell_prefStretch_threshold_uniform P c j0
  refine ⟨lo + 1 + (∑ c, mgU c) + (∑ c, ∑ j0, (Mpref c j0 + gateUcyc c * Qpref c j0)),
          lo + 1 + (∑ c, mgD c) + (∑ c, ∑ j0, (Msuf c j0 + gateDcyc c * Qsuf c j0)),
          by omega, by omega, ?_, ?_⟩
  · intro c j0
    refine ⟨gateDcyc c * Qsuf c j0, max (Msuf c j0) (mgD c),
      Nat.mul_pos (hgD c).1 (hsuf c j0).1, ?_, ?_, ?_⟩
    · have hin : Msuf c j0 + gateDcyc c * Qsuf c j0
          ≤ ∑ j0, (Msuf c j0 + gateDcyc c * Qsuf c j0) :=
        Finset.single_le_sum (f := fun j0 => Msuf c j0 + gateDcyc c * Qsuf c j0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j0)
      have hout : (∑ j0, (Msuf c j0 + gateDcyc c * Qsuf c j0))
          ≤ ∑ c, ∑ j0, (Msuf c j0 + gateDcyc c * Qsuf c j0) :=
        Finset.single_le_sum (f := fun c => ∑ j0, (Msuf c j0 + gateDcyc c * Qsuf c j0))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      have h1 : mgD c ≤ ∑ c, mgD c :=
        Finset.single_le_sum (f := fun c => mgD c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
    · intro κ b hb
      rw [show b + gateDcyc c * Qsuf c j0 * κ = b + gateDcyc c * (Qsuf c j0 * κ) by ring]
      exact (hgD c).2 (Qsuf c j0 * κ) b (le_trans (le_max_right _ _) hb)
    · intro ī0 mS n
      obtain ⟨F, hRA, hag⟩ := (hsuf c j0).2 ī0 mS n
      exact ⟨F, (hRA.of_dvd (dvd_mul_left (Qsuf c j0) (gateDcyc c))).mono (le_max_left _ _), hag⟩
  · intro c j0
    refine ⟨gateUcyc c * Qpref c j0, max (Mpref c j0) (mgU c),
      Nat.mul_pos (hgU c).1 (hpref c j0).1, ?_, ?_, ?_⟩
    · have hin : Mpref c j0 + gateUcyc c * Qpref c j0
          ≤ ∑ j0, (Mpref c j0 + gateUcyc c * Qpref c j0) :=
        Finset.single_le_sum (f := fun j0 => Mpref c j0 + gateUcyc c * Qpref c j0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j0)
      have hout : (∑ j0, (Mpref c j0 + gateUcyc c * Qpref c j0))
          ≤ ∑ c, ∑ j0, (Mpref c j0 + gateUcyc c * Qpref c j0) :=
        Finset.single_le_sum (f := fun c => ∑ j0, (Mpref c j0 + gateUcyc c * Qpref c j0))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      have h1 : mgU c ≤ ∑ c, mgU c :=
        Finset.single_le_sum (f := fun c => mgU c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
    · intro κ b hb
      rw [show b + gateUcyc c * Qpref c j0 * κ = b + gateUcyc c * (Qpref c j0 * κ) by ring]
      exact (hgU c).2 (Qpref c j0 * κ) b (le_trans (le_max_right _ _) hb)
    · intro ī0 mS n
      obtain ⟨F, hRA, hag⟩ := (hpref c j0).2 ī0 mS n
      exact ⟨F, (hRA.of_dvd (dvd_mul_left (Qpref c j0) (gateUcyc c))).mono (le_max_left _ _), hag⟩

/-- A finite coordinate candidate `x` realises the row-dependent descriptor `r`
when it is in `coordCands` and its interpretation at row `mS` — from-end offsets read as
`sufIdx (mS-1-i)` / `prefIdx (mS-1-i)` — is exactly `r`. -/
def CoordCandRealizes {B : ℕ} (q_U q_D mS : ℕ)
    (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (r : RegionSpecF B) : Prop :=
  x ∈ coordCands B q_U q_D ∧
    (match x with
      | Sum.inl r' => r'
      | Sum.inr (Sum.inl i_off) => RegionSpecF.sufIdx (mS - 1 - i_off)
      | Sum.inr (Sum.inr i_off) => RegionSpecF.prefIdx (mS - 1 - i_off)) = r

open SliceBoundaryMinCore

/-- **d3.4 step 4 (suffix): the selBvec boundary endpoint is a `coordCands` member, and lex-dominates
the cell value.**  A suffix coordinate `j0` at depth `l` (`M ≤ l < N`) collapses, at the combined period
`pc`, to a boundary depth `l_bd` whose descriptor `x` lies in `coordCands B q_U q_D`: SHALLOW
`Sum.inl (sufIdx l_bd)` with `l_bd < q_D` (slope ≥ 0), or DEEP `Sum.inr (Sum.inl (mS-1-l_bd))` with offset
in `[1,q_D]` (slope < 0).  The band bound `N` (caller passes `mS-1-T`) keeps the deep endpoint `T` away
from the suffix end (step-5 after-gap), and the outputs `M ≤ l_bd` / `l_bd < N` give step-5's before/after
gaps.  Shift `l - l_bd` (or `l_bd - l`) is a multiple of `pc` (gate); rank at `l_bd` lex-dominates rank at
`l` (value). -/
theorem sufStretch_boundary_eq_coordCand
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    {B : ℕ} (q_U q_D : ℕ) (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n t l N : ℕ)
    (pc M : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pc) (hMpc : M + pc < q_D) (hF : RankAffineAtFrom M pc F)
    (hag : ∀ l', l' < mS - 1 → P.rank c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : M ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1) (hNM : mS - 1 ≤ N + M) (hMpcN : M + pc ≤ N) :
    ∃ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      x ∈ coordCands B q_U q_D ∧
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx l_bd) ∧
      mixedPosAt x mS t n = mS + 2 * n + 1 + l_bd ∧
      M ≤ l_bd ∧ l_bd < N ∧
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) ∧
      ¬ WRP.lexLt (P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l)))
                  (P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l_bd))) := by
  obtain ⟨PR, hPR⟩ := hF
  have hrec : ∀ (i : Fin P.d) (r' k : ℕ), F (M + r' + pc * k) i = F (M + r') i + k * PR i := by
    intro i r' k
    have hit := congrFun (SliceRankAtom.RankAffine.iterate hPR (M + r') k (by omega)) i
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
    exact hit
  obtain ⟨r, hrdef⟩ : ∃ rr : ℕ, rr = (l - M) % pc := ⟨_, rfl⟩
  obtain ⟨kd, hkddef⟩ : ∃ kk : ℕ, kk = (l - M) / pc := ⟨_, rfl⟩
  have hrlt : r < pc := by rw [hrdef]; exact Nat.mod_lt _ hpc
  have hjeq : M + r + pc * kd = l := by
    rw [hrdef, hkddef]; have := Nat.mod_add_div (l - M) pc; omega
  have hkd : kd < numReps M pc r N :=
    (mem_iff_lt_numReps M pc r N kd hpc).mp (by rw [hjeq]; exact hlN)
  by_cases hslope : WRP.lexLt PR (fun _ => 0)
  · -- DEEP: slope < 0, F decreasing; collapse UP to the deep endpoint
    have hdom := SliceDstarBridge.selBvec_le_member F PR true hrec
      (iff_of_true rfl hslope) r N kd hkd
    set l_bd := M + r + pc * (numReps M pc r N - 1) with hlbd
    have hnr1 : 1 ≤ numReps M pc r N := by omega
    have hlbdN : l_bd < N := by
      rw [hlbd]
      exact (mem_iff_lt_numReps M pc r N (numReps M pc r N - 1) hpc).mpr (by omega)
    have hlbd_mS : l_bd < mS - 1 := by omega
    have hMlbd : M ≤ l_bd := by rw [hlbd]; omega
    have hge : N ≤ M + r + pc * numReps M pc r N := by
      by_contra h; push Not at h
      exact absurd ((mem_iff_lt_numReps M pc r N (numReps M pc r N) hpc).mp h) (lt_irrefl _)
    have hmuleq : pc * (numReps M pc r N - 1) + pc = pc * numReps M pc r N := by
      rw [← Nat.mul_succ]; congr 1; omega
    have hge' : N ≤ l_bd + pc := by rw [hlbd]; omega
    have hbnd : selBvecVal F M r PR true 0 (numReps M pc r N - 1) = F l_bd := by
      funext i
      rw [hlbd, hrec i r (numReps M pc r N - 1)]
      simp only [selBvecVal, if_true]
    have hxmem : Sum.inr (Sum.inl (mS - 1 - l_bd)) ∈ coordCands B q_U q_D := by
      rw [mem_coordCands]
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨mS - 1 - l_bd, by omega, ?_, rfl⟩)))
      -- i_off = mS-1-l_bd ≤ M+pc < q_D (deep band reaches within M+pc of the end)
      omega
    refine ⟨l_bd, Sum.inr (Sum.inl (mS - 1 - l_bd)), hxmem, ?_, ?_, hMlbd, hlbdN, ?_, ?_⟩
    · refine ⟨hxmem, ?_⟩
      exact congrArg RegionSpecF.sufIdx (by omega)
    · show mixedPosAt (Sum.inr (Sum.inl (mS - 1 - l_bd))) mS t n = mS + 2 * n + 1 + l_bd
      simp only [mixedPosAt]; omega
    · refine Or.inr ⟨numReps M pc r N - 1 - kd, ?_⟩
      have hkdle : kd ≤ numReps M pc r N - 1 := by omega
      have hsplit : pc * (numReps M pc r N - 1)
          = pc * kd + pc * (numReps M pc r N - 1 - kd) := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' hkdle]
      rw [hlbd]; omega
    · rw [hjeq] at hdom; rw [hbnd] at hdom
      rw [hag l (by omega), hag l_bd hlbd_mS]; exact hdom
  · -- SHALLOW: slope ≥ 0, F nondecreasing; collapse DOWN to the shallow endpoint M+r
    have hdom := SliceDstarBridge.selBvec_le_member F PR false hrec
      (iff_of_false Bool.false_ne_true hslope) r N kd hkd
    have hlbdN : M + r < N := by omega
    have hlbd_mS : M + r < mS - 1 := by omega
    have hbnd : selBvecVal F M r PR false 0 (numReps M pc r N - 1) = F (M + r) := by
      funext i; simp only [selBvecVal, Bool.false_eq_true, if_false, Nat.cast_zero, zero_mul, add_zero]
    have hxmem : Sum.inl (RegionSpecF.sufIdx (B := B) (M + r)) ∈ coordCands B q_U q_D := by
      rw [mem_coordCands]; exact Or.inr (Or.inr (Or.inl ⟨M + r, by omega, rfl⟩))
    refine ⟨M + r, Sum.inl (RegionSpecF.sufIdx (M + r)), hxmem, ?_, ?_,
      Nat.le_add_right _ _, hlbdN, ?_, ?_⟩
    · exact ⟨hxmem, rfl⟩
    · show mixedPosAt (Sum.inl (RegionSpecF.sufIdx (M + r))) mS t n = mS + 2 * n + 1 + (M + r)
      simp only [mixedPosAt, RegionSpecF.posAt]
    · exact Or.inl ⟨kd, hjeq.symm⟩
    · rw [hjeq] at hdom; rw [hbnd] at hdom
      rw [hag l (by omega), hag (M + r) hlbd_mS]; exact hdom

end CopiedDstarCMS
