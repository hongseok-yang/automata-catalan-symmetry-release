/-
# The fibred gate machines and their EPs (§9 tower, Stage F3.3)

The fixed-machine design (FIBRED_PORTMAP D8): acceptance of a fibred cell
tuple on the copied slice reduces, for ALL `n` at once, to ONE pulled-back
re-rooted machine — because the marked boundary stretches of a valid cell
tuple are `n`-independent.  That hinge is `cellTupleF_seg_congr_n` (spike S1):

* the `U`-stretch segments agree by `markSeg_congr_outside` at the shared
  offset `0` (prefix-stretch coordinates are `n`-free; everything else is out
  of the window);
* the `D`-stretch segments live at DIFFERENT offsets (`mS + 2n + 1`), so per
  side we first junk the out-of-window coordinates onto the shifted relative
  tuple (`markSeg_congr_outside`), then strip the offset with `markSeg_shift`
  — both sides land on the `n`-free relative tuple (`sufIdx l ↦ l`,
  everything else `↦ mS − 1`, just past the window) at offset `0`.
-/
import RequestProject.CopiedRegionF
import RequestProject.SliceCellConvGA

namespace CopiedGateEP

open WRP Step SliceFamilyCell MSOMarkN SliceMarkN SliceMSO SliceReRoot
  SliceDstarGA CopiedMark CopiedCells CopiedDstar CopiedRegionF

/-- The `n`-free relative `D`-stretch tuple: suffix-stretch offsets verbatim,
everything else parked just past the window. -/
def relDAtF {B : ℕ} (mS : ℕ) : RegionSpecF B → ℕ
  | .sufIdx l => l
  | _ => mS - 1

/-- One side of the `D`-segment normalization: the marked `D`-stretch of a
valid fibred cell tuple is the `n`-free relative segment. -/
theorem markSegD_eq_rel {B k : ℕ} (rs : Fin k → RegionSpecF B) (mS t n : ℕ)
    (hm : 1 ≤ mS) (hv : ∀ i, (rs i).valid mS) (hw : t + B ≤ n) :
    markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t n)
        (mS + 2 * n + 1)
      = markSeg k (List.replicate (mS - 1) D)
          (fun i => relDAtF mS (rs i)) 0 := by
  have h1 : markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t n)
      (mS + 2 * n + 1)
      = markSeg k (List.replicate (mS - 1) D)
          (fun i => relDAtF mS (rs i) + (mS + 2 * n + 1)) (mS + 2 * n + 1) := by
    apply markSeg_congr_outside
    intro i
    rw [List.length_replicate]
    rcases hri : rs i with r | q | l
    · -- core: original strictly left of the window; relative side parked right
      right
      constructor
      · left
        show (rs i).posAt mS t n < mS + 2 * n + 1
        rw [hri]
        rcases r with _ | _ | ⟨f, e⟩ | ⟨l', e⟩ | ⟨δ, e⟩ <;>
          simp only [RegionSpecF.posAt, RegionSpec.posAt]
        · omega
        · omega
        · have := f.isLt
          rcases e with _ | _ <;>
            simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
        · have := l'.isLt
          rcases e with _ | _ <;>
            simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
        · have := δ.isLt
          rcases e with _ | _ <;>
            simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
      · right
        show mS + 2 * n + 1 + (mS - 1) ≤ (mS - 1) + (mS + 2 * n + 1)
        omega
    · -- prefix stretch: original left of the window; relative side parked right
      have hq : q < mS - 1 := by
        have := hv i
        rwa [hri] at this
      right
      constructor
      · left
        show (rs i).posAt mS t n < mS + 2 * n + 1
        rw [hri]
        show q < mS + 2 * n + 1
        omega
      · right
        show mS + 2 * n + 1 + (mS - 1) ≤ (mS - 1) + (mS + 2 * n + 1)
        omega
    · -- suffix stretch: positions agree
      left
      show (rs i).posAt mS t n = l + (mS + 2 * n + 1)
      rw [hri]
      show mS + 2 * n + 1 + l = l + (mS + 2 * n + 1)
      omega
  have h2 := markSeg_shift k (List.replicate (mS - 1) D)
    (fun i => relDAtF mS (rs i)) (mS + 2 * n + 1) 0
  rw [Nat.zero_add] at h2
  exact h1.trans h2

/-- **SPIKE S1 (the hinge of the fixed-machine gate design)**: the marked
boundary stretches of a valid fibred cell tuple are `n`-INDEPENDENT. -/
theorem cellTupleF_seg_congr_n {B k : ℕ} (rs : Fin k → RegionSpecF B)
    (mS t : ℕ) (hm : 1 ≤ mS) (hv : ∀ i, (rs i).valid mS) (n n' : ℕ)
    (hw : t + B ≤ n) (hw' : t + B ≤ n') :
    markSeg k (List.replicate (mS - 1) U) (cellTupleF rs mS t n) 0
        = markSeg k (List.replicate (mS - 1) U) (cellTupleF rs mS t n') 0
    ∧ markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t n)
          (mS + 2 * n + 1)
        = markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t n')
          (mS + 2 * n' + 1) := by
  constructor
  · apply markSeg_congr_outside
    intro i
    rw [List.length_replicate]
    rcases hri : rs i with r | q | l
    · -- core: both sides at or past the window end
      right
      constructor
      · right
        show 0 + (mS - 1) ≤ (rs i).posAt mS t n
        rw [hri]
        show 0 + (mS - 1) ≤ mS - 1 + RegionSpec.posAt r t n
        omega
      · right
        show 0 + (mS - 1) ≤ (rs i).posAt mS t n'
        rw [hri]
        show 0 + (mS - 1) ≤ mS - 1 + RegionSpec.posAt r t n'
        omega
    · -- prefix stretch: `n`-free positions agree
      left
      show (rs i).posAt mS t n = (rs i).posAt mS t n'
      rw [hri]
      rfl
    · -- suffix stretch: both sides past the window end
      right
      constructor
      · right
        show 0 + (mS - 1) ≤ (rs i).posAt mS t n
        rw [hri]
        show 0 + (mS - 1) ≤ mS + 2 * n + 1 + l
        omega
      · right
        show 0 + (mS - 1) ≤ (rs i).posAt mS t n'
        rw [hri]
        show 0 + (mS - 1) ≤ mS + 2 * n' + 1 + l
        omega
  · rw [markSegD_eq_rel rs mS t n hm hv hw,
      markSegD_eq_rel rs mS t n' hm hv hw']

/-! ## The fixed reduced machine -/

/-- **The reduced gate machine**: the pullback of `M` re-rooted through the
(`n`-independent) marked boundary stretches of the cell, evaluated at the
dummy slice `n₀ := t + B`.  By S1 this ONE machine serves every `n`. -/
noncomputable def redM {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k)) (mS : ℕ)
    (rs : Fin k → RegionSpecF B) (t : ℕ) :
    SliceMSO.DetAuto (MarkedN (coreSet rs).card) :=
  pullback (reRoot M
    (markSeg k (List.replicate (mS - 1) U) (cellTupleF rs mS t (t + B)) 0)
    (markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t (t + B))
      (mS + 2 * (t + B) + 1)))
    (mapBits (coreEmb rs))

/-- The reduced machine's block map is literally `bFN M` — every machine
period transfers. -/
theorem bFN_redM {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k)) (mS : ℕ)
    (rs : Fin k → RegionSpecF B) (t : ℕ) :
    SliceMarkN.bFN (redM M mS rs t) = SliceMarkN.bFN M :=
  (bFN_pullback (reRoot M _ _) (coreEmb rs)).trans (bFN_reRoot M _ _)

/-- The reduced machine does not depend on the base. -/
theorem redM_t_congr {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k)) (mS : ℕ)
    (hm : 1 ≤ mS) (rs : Fin k → RegionSpecF B)
    (hv : ∀ i, (rs i).valid mS) (t t' : ℕ) :
    redM M mS rs t = redM M mS rs t' := by
  unfold redM
  obtain ⟨hU1, hD1⟩ := cellTupleF_seg_congr_n rs mS t hm hv (t + B)
    (max (t + B) (t' + B)) le_rfl (le_max_left _ _)
  obtain ⟨hU2, hD2⟩ := CopiedDstar.cellTupleF_seg_congr rs mS t t'
    (max (t + B) (t' + B)) hm (le_max_left _ _) (le_max_right _ _)
  obtain ⟨hU3, hD3⟩ := cellTupleF_seg_congr_n rs mS t' hm hv (t' + B)
    (max (t + B) (t' + B)) le_rfl (le_max_right _ _)
  rw [hU1, hD1, hU2, hD2, ← hU3, ← hD3]

/-! ## The gate and its reduction -/

/-- The fibred cell gate: marked acceptance of the cell tuple on the copied
slice. -/
def gateF {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k))
    (rs : Fin k → RegionSpecF B) (mS t0 n : ℕ) : Prop :=
  M.accepts (markAtN k (copiedSlice mS n) (cellTupleF rs mS t0 n))

/-- **The gate reduction**: on the window, the fibred gate is acceptance of
the underlying wrapped-flat cell tuple at the FIXED reduced machine. -/
theorem gateF_reduced {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k)) (mS : ℕ)
    (hm : 1 ≤ mS) (rs : Fin k → RegionSpecF B)
    (hv : ∀ i, (rs i).valid mS) (t0 n : ℕ) (hwin : t0 + B ≤ n) :
    gateF M rs mS t0 n ↔ (redM M mS rs t0).accepts
      (markAtN (coreSet rs).card (wrappedFlat n)
        (cellTuple (coreSpec rs) t0 n)) := by
  unfold gateF
  rw [accepts_copied_arity_reduced M (coreEmb rs) mS n hm _
    (cellTupleF_mid rs mS t0 n hm hwin) (cellTupleF_out rs mS t0 n hv)]
  obtain ⟨hU, hD⟩ := cellTupleF_seg_congr_n rs mS t0 hm hv n (t0 + B)
    hwin le_rfl
  rw [hU, hD, cellTupleF_reduced rs mS t0 n hm]
  rfl

/-! ## The eventual periodicities (machine periods only — zero Büchi calls) -/

/-- Wrapped cell acceptance at a fixed base is eventually periodic in `n` at
the machine's `bFN` function period. -/
theorem acceptsN_cellTuple_EP_at {Z k : ℕ} (M : SliceMSO.DetAuto (MarkedN k))
    (rs : Fin k → RegionSpec Z) (t0 : ℕ) (hZt : Z ≤ t0) (mv pv : ℕ)
    (hpv : 1 ≤ pv) (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g]) :
    ∃ N, ∀ n, N ≤ n →
      (M.accepts (markAtN k (wrappedFlat (n + pv)) (cellTuple rs t0 (n + pv)))
        ↔ M.accepts (markAtN k (wrappedFlat n) (cellTuple rs t0 n))) := by
  refine ⟨mv + t0 + SliceFasCountGA.clusterWidth rs + Z + 1, fun n hn => ?_⟩
  rw [SliceFasCountGA.acceptsN_cellTuple_convW M rs t0 (n + pv) hZt (by omega),
    SliceFasCountGA.acceptsN_cellTuple_convW M rs t0 n hZt (by omega)]
  have harg : n + pv - Z - SliceFasCountGA.clusterWidth rs - t0
      = (n - Z - SliceFasCountGA.clusterWidth rs - t0) + pv := by omega
  rw [harg, hEP (n - Z - SliceFasCountGA.clusterWidth rs - t0) (by omega)]

/-- **The fibred gate EP** (replaces `anchorGate_EP` — zero Büchi calls): the
gate at a fixed base is eventually periodic in `n` at the machine's `bFN`
function period; the threshold is per-`(mS, rs, t0)`. -/
theorem gateF_EP {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k)) (mv pv : ℕ)
    (hpv : 1 ≤ pv) (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g])
    (mS : ℕ) (hm : 1 ≤ mS) (rs : Fin k → RegionSpecF B)
    (hv : ∀ i, (rs i).valid mS) (t0 : ℕ) (hBt : B ≤ t0) :
    ∃ N, ∀ n, N ≤ n → (gateF M rs mS t0 (n + pv) ↔ gateF M rs mS t0 n) := by
  have hEPred : ∀ g, mv ≤ g →
      (bFN (redM M mS rs t0))^[g + pv] = (bFN (redM M mS rs t0))^[g] := by
    intro g hg
    rw [bFN_redM]
    exact hEP g hg
  obtain ⟨N, hN⟩ := acceptsN_cellTuple_EP_at (redM M mS rs t0) (coreSpec rs)
    t0 hBt mv pv hpv hEPred
  refine ⟨max N (t0 + B), fun n hn => ?_⟩
  rw [gateF_reduced M mS hm rs hv t0 (n + pv) (by omega),
    gateF_reduced M mS hm rs hv t0 n (by omega)]
  exact hN n (by omega)

/-- Packaging: the gate is `EventuallyPeriodic` at the machine period. -/
theorem gateF_EP' {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k)) (mv pv : ℕ)
    (hpv : 1 ≤ pv) (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g])
    (mS : ℕ) (hm : 1 ≤ mS) (rs : Fin k → RegionSpecF B)
    (hv : ∀ i, (rs i).valid mS) (t0 : ℕ) (hBt : B ≤ t0) :
    SliceOrder.EventuallyPeriodic (fun n => gateF M rs mS t0 n) pv :=
  gateF_EP M mv pv hpv hEP mS hm rs hv t0 hBt

/-! ## The kernel (convolution) form -/

/-- The fibred bulk width agrees with the wrapped width of the core part. -/
theorem clusterWidthF_eq_coreSpec {B k : ℕ} (rs : Fin k → RegionSpecF B) :
    clusterWidthF rs = SliceFasCountGA.clusterWidth (coreSpec rs) := by
  classical
  apply le_antisymm
  · refine Finset.sup_le (fun i _ => ?_)
    show widthAtF (rs i) ≤ _
    by_cases hcore : ∃ i', coreEmb rs i' = i
    · obtain ⟨i', rfl⟩ := hcore
      have hr := rs_coreEmb rs i'
      rw [hr]
      rcases hs : coreSpec rs i' with _ | _ | ⟨f, e⟩ | ⟨l', e⟩ | ⟨δ, e⟩
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · have hlt := SliceFasCountGA.cluster_lt_width (coreSpec rs) i' δ e hs
        show δ.val + 1 ≤ _
        omega
    · push Not at hcore
      rcases noncore_of_out rs i hcore with ⟨q, hq⟩ | ⟨l, hl⟩
      · rw [hq]
        exact Nat.zero_le _
      · rw [hl]
        exact Nat.zero_le _
  · refine Finset.sup_le (fun i' _ => ?_)
    rcases hs : coreSpec rs i' with _ | _ | ⟨f, e⟩ | ⟨l', e⟩ | ⟨δ, e⟩
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · have hr := rs_coreEmb rs i'
      rw [hs] at hr
      have hlt := cluster_lt_widthF rs (coreEmb rs i') δ e hr
      show δ.val + 1 ≤ _
      omega

/-- **The fibred kernel form** (what every F3.9 bulk arm consumes): on the
full canonical window, fibred cell acceptance is the fixed boundary data of
the FIXED reduced machine around two `bFN M`-iterate gaps — ONE step function
for all count kernels. -/
theorem acceptsF_cellTuple_convW {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k))
    (mS : ℕ) (hm : 1 ≤ mS) (rs : Fin k → RegionSpecF B)
    (hv : ∀ i, (rs i).valid mS) (t n : ℕ) (hZt : B ≤ t)
    (htn : t + SliceFasCountGA.clusterWidth (coreSpec rs) + B ≤ n) :
    M.accepts (markAtN k (copiedSlice mS n) (cellTupleF rs mS t n)) ↔
      SliceFasCountGA.cellAcc (redM M mS rs B) (coreSpec rs)
        ((bFN M)^[n - B - SliceFasCountGA.clusterWidth (coreSpec rs) - t]
          (SliceFasCountGA.cellGclW (redM M mS rs B) (coreSpec rs)
            ((bFN M)^[t - B]
              (SliceFasCountGA.cellQ0 (redM M mS rs B) (coreSpec rs))))) := by
  have hgr := gateF_reduced M mS hm rs hv t n (by omega)
  rw [show M.accepts (markAtN k (copiedSlice mS n) (cellTupleF rs mS t n))
      = gateF M rs mS t n from rfl, hgr, redM_t_congr M mS hm rs hv t B,
    SliceFasCountGA.acceptsN_cellTuple_convW (redM M mS rs B) (coreSpec rs)
      t n hZt htn, bFN_redM]
  rfl

end CopiedGateEP
