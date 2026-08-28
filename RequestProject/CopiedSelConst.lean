/-
# Selection-constancy on a residue class (§9 d4a, gap G2 — the slice wrapper)

Wraps the abstract heart `CopiedSufRunGate.accepts_single_mark_run_period` into the concrete claim that
gate acceptance (= selectedAtom ∧ label D, via `Mc`) is constant on each residue class of the
homogeneous `D^mS` suffix run (and the `U^mS` prefix run) of `copiedSlice mS n`.  This is what makes
the per-class uniformity `hsufUniform`/`hpreUniform` (feeding `gate_semantic_split`) provable: a run
atom achieving d* forces its whole class to achieve d* only because the class endpoint is SELECTED,
which is exactly this constancy.

The workhorses are stated at ARBITRARY arity `k` (constant mark tuple `fun _ => p`) so they apply
directly to the arity-`(arity c)` D-selector gate `exists_selDDFA` with NO `MarkedN (arity c) → MarkedN 1`
coercion; the arity-1 names are kept as one-line corollaries.

  `markSeg_single_split` (gap G2-C) — the single-mark run split that exposes the marked letter inside a
  homogeneous run; `gateAccepts_run_shift`/`gateAccepts_pre_run_shift` — the suffix/prefix slice wrappers.
-/
import RequestProject.CopiedSufRunGate
import RequestProject.CopiedDstarCMS

namespace CopiedSelConst

open WRP Step MSOMarkN SliceMarkN SliceMSO CopiedMark CopiedSufRunGate SliceReRoot

/-- **Single-mark run split (arity `k`).**  A marked run `x^L` with the single mark of `(fun _ => off+l)`
at relative offset `l` (`l < L`) factors as `(x,unmarked)^l ++ [(x,marked)] ++ (x,unmarked)^(L-1-l)`.
The constant tuple `fun _ => off+l` marks position `off+l` in every coordinate, so the exposed letter has
all `k` bits `true`.  Built from `markSeg_replicate_decomp_end` (peel front `l` unmarked) + `markSeg_cons`
(expose the mark) + `markSeg_replicate_decomp` (tail unmarked) + `unmark_replicate`. -/
theorem markSeg_single_split_k (k : ℕ) (x : Step) (off l L : ℕ) (hl : l < L) :
    markSeg k (List.replicate L x) (fun _ => off + l) off
      = List.replicate l (mkLetter k x (fun _ => false))
        ++ [mkLetter k x (fun _ => true)]
        ++ List.replicate (L - l - 1) (mkLetter k x (fun _ => false)) := by
  rw [CopiedSetupMS.markSeg_replicate_decomp_end x (fun _ => off + l) off (L - l) L (by omega)
      (fun _ => Or.inr (show off + (L - (L - l)) ≤ off + l by omega))]
  have hLl : L - (L - l) = l := by omega
  rw [hLl, CopiedSetupMS.unmark_replicate]
  have hrep : L - l = (L - l - 1) + 1 := by omega
  rw [hrep, List.replicate_succ, markSeg_cons]
  have hbit : bitsAt k (fun _ => off + l) (off + l) = (fun _ => true) := by
    funext i; simp [bitsAt]
  rw [hbit]
  have htail : markSeg k (List.replicate (L - l - 1) x) (fun _ => off + l) (off + l + 1)
      = List.replicate (L - l - 1) (mkLetter k x (fun _ => false)) := by
    rw [CopiedSetupMS.markSeg_replicate_decomp x (fun _ => off + l) (off + l + 1) 0 (L - l - 1)
        (by omega) (fun _ => Or.inl (show off + l < off + l + 1 + 0 by omega))]
    simp [CopiedSetupMS.unmark_replicate]
  rw [htail, show L - l - 1 + 1 - 1 = L - l - 1 from by omega, List.append_assoc,
    List.singleton_append]

/-- Arity-1 corollary of `markSeg_single_split_k`. -/
theorem markSeg_single_split (x : Step) (off l L : ℕ) (hl : l < L) :
    markSeg 1 (List.replicate L x) (fun _ => off + l) off
      = List.replicate l (mkLetter 1 x (fun _ => false))
        ++ [mkLetter 1 x (fun _ => true)]
        ++ List.replicate (L - l - 1) (mkLetter 1 x (fun _ => false)) :=
  markSeg_single_split_k 1 x off l L hl

/-- **G2 wrapper (suffix run, arity `k`).**  For a fixed marked DFA `M`, gate acceptance at the
suffix-run mark position `p = mS+2n+1+l` (inside the final `D^mS` run, with the constant mark tuple
`fun _ => p`) is invariant under the mark shift `l ↦ l+pc`, given the unmarked-`D` iterate is
`pc`-periodic past `T` (the `coordCands_cycle_lengths` gate cycle) and the deep margin `T+pc+l+2 ≤ mS`.
This is the selection-constancy that makes per-class uniformity provable: a run atom achieving d* forces
its whole residue class to, because the class endpoint is selected exactly by this periodicity.
Decomposes via `accepts_copied_arity_reduced` (`k'=0`, `ι=Fin.elim0`) → `accepts_pullback` →
`markAtN_zero` → `accepts_reRoot`, makes the U-prefix unmarked, splits the D-suffix
(`markSeg_single_split_k`), then applies `accepts_single_mark_run_period`. -/
theorem gateAccepts_run_shift_k (k : ℕ) (M : DetAuto (MarkedN k)) (mS n l pc T : ℕ) (hm1 : 1 ≤ mS)
    (hper : ∀ a, T ≤ a →
      (fun q => M.δ q (mkLetter k D (fun _ => false)))^[a + pc]
        = (fun q => M.δ q (mkLetter k D (fun _ => false)))^[a])
    (hl : T ≤ l) (hsuf : T + pc + l + 2 ≤ mS) :
    M.accepts (markAtN k (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l))
      ↔ M.accepts (markAtN k (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + (l + pc))) := by
  rw [accepts_copied_arity_reduced M Fin.elim0 mS n hm1 (fun _ => mS + 2 * n + 1 + l)
        (fun i => i.elim0) (fun i _ => Or.inr (show mS + 2 * n + 1 ≤ mS + 2 * n + 1 + l by omega)),
      accepts_copied_arity_reduced M Fin.elim0 mS n hm1 (fun _ => mS + 2 * n + 1 + (l + pc))
        (fun i => i.elim0)
        (fun i _ => Or.inr (show mS + 2 * n + 1 ≤ mS + 2 * n + 1 + (l + pc) by omega)),
    accepts_pullback, accepts_pullback, markAtN_zero, markAtN_zero,
    accepts_reRoot, accepts_reRoot]
  -- U-prefix is unmarked (mark p ≥ mS-1) on both sides
  have hUpre : ∀ q, mS - 1 ≤ q → markSeg k (List.replicate (mS - 1) U) (fun _ => q) 0
      = unmark k (List.replicate (mS - 1) U) := by
    intro q hq
    exact markSeg_unmarked k (List.replicate (mS - 1) U) (fun _ => q) 0
      (fun i => Or.inr (by simp only [List.length_replicate]; omega))
  -- D-suffix split via markSeg_single_split_k (off = mS+2n+1, L = mS-1)
  rw [hUpre _ (by omega), hUpre _ (by omega),
    markSeg_single_split_k k D (mS + 2 * n + 1) l (mS - 1) (by omega),
    markSeg_single_split_k k D (mS + 2 * n + 1) (l + pc) (mS - 1) (by omega)]
  -- apply the abstract heart
  have heart := accepts_single_mark_run_period M (mkLetter k D (fun _ => false))
    (mkLetter k D (fun _ => true))
    (unmark k (List.replicate (mS - 1) U) ++ (wrappedFlat n).map (mapBits (Fin.elim0)))
    [] pc T hper l (mS - 1 - l - 1) hl (by omega)
  simp only [List.append_nil, List.append_assoc] at heart ⊢
  rw [show mS - 1 - (l + pc) - 1 = mS - 1 - l - 1 - pc from by omega]
  exact heart

/-- Arity-1 corollary of `gateAccepts_run_shift_k`. -/
theorem gateAccepts_run_shift (M : DetAuto (MarkedN 1)) (mS n l pc T : ℕ) (hm1 : 1 ≤ mS)
    (hper : ∀ a, T ≤ a →
      (fun q => M.δ q (mkLetter 1 D (fun _ => false)))^[a + pc]
        = (fun q => M.δ q (mkLetter 1 D (fun _ => false)))^[a])
    (hl : T ≤ l) (hsuf : T + pc + l + 2 ≤ mS) :
    M.accepts (markAtN 1 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l))
      ↔ M.accepts (markAtN 1 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + (l + pc))) :=
  gateAccepts_run_shift_k 1 M mS n l pc T hm1 hper hl hsuf

/-- **G2 prefix twin (arity `k`).**  Gate acceptance at the prefix-run mark position `p = l` (inside the
initial `U^mS` run) is invariant under `l ↦ l+pc`, given the unmarked-`U` iterate is `pc`-periodic past `T`.
Mirror of `gateAccepts_run_shift_k`: here the D-suffix is unmarked, the U-prefix is split, `pre = []`,
`suf = mid ++ unmark(D)`.  The extra `0 + l` normalisation lets `markSeg_single_split_k` (offset 0) fire. -/
theorem gateAccepts_pre_run_shift_k (k : ℕ) (M : DetAuto (MarkedN k)) (mS n l pc T : ℕ) (hm1 : 1 ≤ mS)
    (hper : ∀ a, T ≤ a →
      (fun q => M.δ q (mkLetter k U (fun _ => false)))^[a + pc]
        = (fun q => M.δ q (mkLetter k U (fun _ => false)))^[a])
    (hl : T ≤ l) (hpre : T + pc + l + 2 ≤ mS) :
    M.accepts (markAtN k (copiedSlice mS n) (fun _ => l))
      ↔ M.accepts (markAtN k (copiedSlice mS n) (fun _ => l + pc)) := by
  rw [accepts_copied_arity_reduced M Fin.elim0 mS n hm1 (fun _ => l)
        (fun i => i.elim0) (fun i _ => Or.inl (show l < mS - 1 by omega)),
      accepts_copied_arity_reduced M Fin.elim0 mS n hm1 (fun _ => l + pc)
        (fun i => i.elim0) (fun i _ => Or.inl (show l + pc < mS - 1 by omega)),
    accepts_pullback, accepts_pullback, markAtN_zero, markAtN_zero,
    accepts_reRoot, accepts_reRoot]
  -- D-suffix is unmarked (mark l < mS-1 ≤ mS+2n+1) on both sides
  have hDsuf : ∀ q, q < mS + 2 * n + 1 →
      markSeg k (List.replicate (mS - 1) D) (fun _ => q) (mS + 2 * n + 1)
        = unmark k (List.replicate (mS - 1) D) := by
    intro q hq
    exact markSeg_unmarked k (List.replicate (mS - 1) D) (fun _ => q) (mS + 2 * n + 1)
      (fun i => Or.inl (by simpa using hq))
  rw [hDsuf _ (by omega), hDsuf _ (by omega)]
  -- normalise the prefix mark `l` to `0 + l` so markSeg_single_split_k (off=0) fires
  rw [show (fun (_ : Fin k) => l) = (fun _ => 0 + l) from by funext _; rw [Nat.zero_add],
    show (fun (_ : Fin k) => l + pc) = (fun _ => 0 + (l + pc)) from by funext _; rw [Nat.zero_add],
    markSeg_single_split_k k U 0 l (mS - 1) (by omega),
    markSeg_single_split_k k U 0 (l + pc) (mS - 1) (by omega)]
  -- apply the abstract heart with pre=[], suf = mid ++ unmark(D)
  have heart := accepts_single_mark_run_period M (mkLetter k U (fun _ => false))
    (mkLetter k U (fun _ => true))
    []
    ((wrappedFlat n).map (mapBits (Fin.elim0)) ++ unmark k (List.replicate (mS - 1) D))
    pc T hper l (mS - 1 - l - 1) hl (by omega)
  simp only [List.nil_append, List.append_assoc] at heart ⊢
  rw [show mS - 1 - (l + pc) - 1 = mS - 1 - l - 1 - pc from by omega]
  exact heart

/-- Arity-1 corollary of `gateAccepts_pre_run_shift_k`. -/
theorem gateAccepts_pre_run_shift (M : DetAuto (MarkedN 1)) (mS n l pc T : ℕ) (hm1 : 1 ≤ mS)
    (hper : ∀ a, T ≤ a →
      (fun q => M.δ q (mkLetter 1 U (fun _ => false)))^[a + pc]
        = (fun q => M.δ q (mkLetter 1 U (fun _ => false)))^[a])
    (hl : T ≤ l) (hpre : T + pc + l + 2 ≤ mS) :
    M.accepts (markAtN 1 (copiedSlice mS n) (fun _ => l))
      ↔ M.accepts (markAtN 1 (copiedSlice mS n) (fun _ => l + pc)) :=
  gateAccepts_pre_run_shift_k 1 M mS n l pc T hm1 hper hl hpre

/-! ## (4a-1) Selection-constancy at the slice — the keystone connecting G2 to per-class uniformity -/

/-- **Selection-constancy on the suffix D-run.**  If `M` decides "`sel ∧ label = D`" on `markAtN`
(the `SliceDstarGA.exists_selDDFA` gate) and its unmarked-`D` iterate is `pc`-cyclic past `T` (a
`CopiedDstarCMS.coordCands_cycle_lengths` gate cycle, here at the multiple `pc·κ`), then "selected and
labelled D" at the deep suffix-run position `mS+2n+1+l` agrees with that at `mS+2n+1+(l+pc·κ)`.  This is
exactly what forces the per-class ENDPOINT to be selected (so `dstarRankGA'_lex_min` applies to it),
which is the `hglob` hypothesis of `CopiedSufRunGate.class_uniform_of_dom`. -/
theorem selRun_suf_const
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hM : ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (mS n l pc T κ : ℕ) (hm1 : 1 ≤ mS)
    (hgate : ∀ b, T ≤ b →
      (fun q => M.δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun q => M.δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hl : T ≤ l) (hmargin : T + pc * κ + l + 2 ≤ mS) :
    (P.toPoly.sel c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l)
        ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l) = D)
      ↔ (P.toPoly.sel c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + (l + pc * κ))
        ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + (l + pc * κ)) = D) := by
  have hlen : (copiedSlice mS n).length = 2 * (mS + n) := length_copiedSlice mS n
  have hval1 : ∀ i : Fin (P.toPoly.arity c),
      (fun _ : Fin (P.toPoly.arity c) => mS + 2 * n + 1 + l) i < (copiedSlice mS n).length := by
    intro i; show mS + 2 * n + 1 + l < (copiedSlice mS n).length; rw [hlen]; omega
  have hval2 : ∀ i : Fin (P.toPoly.arity c),
      (fun _ : Fin (P.toPoly.arity c) => mS + 2 * n + 1 + (l + pc * κ)) i
        < (copiedSlice mS n).length := by
    intro i; show mS + 2 * n + 1 + (l + pc * κ) < (copiedSlice mS n).length; rw [hlen]; omega
  rw [← hM (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l) hval1,
      ← hM (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + (l + pc * κ)) hval2]
  exact gateAccepts_run_shift_k (P.toPoly.arity c) M mS n l (pc * κ) T hm1 hgate hl hmargin

/-- **Selection-constancy on the prefix U-run.**  Prefix twin of `selRun_suf_const`: "selected and
labelled D" at the prefix-run position `l` agrees with that at `l+pc·κ`, given the unmarked-`U` iterate
is `pc`-cyclic past `T`. -/
theorem selRun_pre_const
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hM : ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (mS n l pc T κ : ℕ) (hm1 : 1 ≤ mS)
    (hgate : ∀ b, T ≤ b →
      (fun q => M.δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun q => M.δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hl : T ≤ l) (hmargin : T + pc * κ + l + 2 ≤ mS) :
    (P.toPoly.sel c (copiedSlice mS n) (fun _ => l)
        ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => l) = D)
      ↔ (P.toPoly.sel c (copiedSlice mS n) (fun _ => l + pc * κ)
        ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => l + pc * κ) = D) := by
  have hlen : (copiedSlice mS n).length = 2 * (mS + n) := length_copiedSlice mS n
  have hval1 : ∀ i : Fin (P.toPoly.arity c),
      (fun _ : Fin (P.toPoly.arity c) => l) i < (copiedSlice mS n).length := by
    intro i; show l < (copiedSlice mS n).length; rw [hlen]; omega
  have hval2 : ∀ i : Fin (P.toPoly.arity c),
      (fun _ : Fin (P.toPoly.arity c) => l + pc * κ) i < (copiedSlice mS n).length := by
    intro i; show l + pc * κ < (copiedSlice mS n).length; rw [hlen]; omega
  rw [← hM (copiedSlice mS n) (fun _ => l) hval1,
      ← hM (copiedSlice mS n) (fun _ => l + pc * κ) hval2]
  exact gateAccepts_pre_run_shift_k (P.toPoly.arity c) M mS n l (pc * κ) T hm1 hgate hl hmargin

/-- Selection-constancy for one moving suffix coordinate in arbitrary arity.
This is the selector-facing wrapper around
`CopiedDstarCMS.accepts_copiedSlice_suf_shift`: if two tuples differ only by
sliding coordinate `j0` inside a clear final-`D` sub-window, and the unmarked
`D` transition is periodic across that slide, then the selected-`D` predicate is
unchanged. -/
theorem selRun_suf_update_shift
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hM : ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (mS n : ℕ) (hm1 : 1 ≤ mS)
    (ī ī' : Fin (P.toPoly.arity c) → ℕ) (j0 : Fin (P.toPoly.arity c))
    (s e a a' κ T pc : ℕ)
    (hper : ∀ κ b, T ≤ b →
      (fun q => M.δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun q => M.δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hval : ∀ i, ī i < (copiedSlice mS n).length)
    (hval' : ∀ i, ī' i < (copiedSlice mS n).length)
    (hsame : ∀ i, i ≠ j0 → ī i = ī' i)
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hj0 : ī j0 = mS + 2 * n + 1 + a)
    (hj0' : ī' j0 = mS + 2 * n + 1 + a')
    (hclear : ∀ i, i ≠ j0 →
      ī i < mS + 2 * n + 1 + s ∨ mS + 2 * n + 1 + e ≤ ī i)
    (hgapA : T ≤ a - s) (hgapA' : T ≤ a' - s)
    (hgapR : T ≤ e - 1 - a) (hgapR' : T ≤ e - 1 - a')
    (hshift : a' = a + pc * κ ∨ a = a' + pc * κ) :
    (P.toPoly.sel c (copiedSlice mS n) ī
        ∧ P.toPoly.label c (copiedSlice mS n) ī = D)
      ↔ (P.toPoly.sel c (copiedSlice mS n) ī'
        ∧ P.toPoly.label c (copiedSlice mS n) ī' = D) := by
  rw [← hM (copiedSlice mS n) ī hval, ← hM (copiedSlice mS n) ī' hval']
  exact CopiedDstarCMS.accepts_copiedSlice_suf_shift M mS n hm1 ī ī' j0 s e a a' κ T pc
    hper hsame hse heL hsa hae hsa' hae' hj0 hj0' hclear hgapA hgapA' hgapR hgapR'
    hshift

/-- Prefix twin of `selRun_suf_update_shift`: one moving coordinate slides
inside a clear initial-`U` sub-window, preserving the selected-`D` predicate. -/
theorem selRun_pre_update_shift
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hM : ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (mS n : ℕ) (hm1 : 1 ≤ mS)
    (ī ī' : Fin (P.toPoly.arity c) → ℕ) (j0 : Fin (P.toPoly.arity c))
    (s e a a' κ T pc : ℕ)
    (hper : ∀ κ b, T ≤ b →
      (fun q => M.δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun q => M.δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hval : ∀ i, ī i < (copiedSlice mS n).length)
    (hval' : ∀ i, ī' i < (copiedSlice mS n).length)
    (hsame : ∀ i, i ≠ j0 → ī i = ī' i)
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hj0 : ī j0 = a) (hj0' : ī' j0 = a')
    (hclear : ∀ i, i ≠ j0 → ī i < s ∨ e ≤ ī i)
    (hgapA : T ≤ a - s) (hgapA' : T ≤ a' - s)
    (hgapR : T ≤ e - 1 - a) (hgapR' : T ≤ e - 1 - a')
    (hshift : a' = a + pc * κ ∨ a = a' + pc * κ) :
    (P.toPoly.sel c (copiedSlice mS n) ī
        ∧ P.toPoly.label c (copiedSlice mS n) ī = D)
      ↔ (P.toPoly.sel c (copiedSlice mS n) ī'
        ∧ P.toPoly.label c (copiedSlice mS n) ī' = D) := by
  rw [← hM (copiedSlice mS n) ī hval, ← hM (copiedSlice mS n) ī' hval']
  exact CopiedDstarCMS.accepts_copiedSlice_pref_shift M mS n hm1 ī ī' j0 s e a a' κ T pc
    hper hsame hse heL hsa hae hsa' hae' hj0 hj0' hclear hgapA hgapA' hgapR hgapR'
    hshift

end CopiedSelConst
