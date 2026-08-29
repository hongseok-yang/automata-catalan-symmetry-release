/-
# The budgeted semantic bridge `TiePointBridgeBudgetedIndexed` (§9 d4c, item 4 — the capstone
  integration)

The row-indexed gate family `GdfaF idx (n % pG)` whose acceptance (∧ rank = d*) characterises the TIE
membership condition consumed by `CopiedCounts.tie_count_fibred_of_gate_budgeted_indexed`.  Built from
the BANDED update-deep gate
`CopiedBoundedGateBand.fasU_atomOrd_full_gate_bounded_band_updateDeep`, instantiated with the
budgeted selector emitters and finite activation sets recorded in `BridgeRowIndex`.  The exported
capstone is `tie_point_bridge_budgeted_indexed_of_update_zero_bundle`, which takes the
`BridgeUpdateZeroSupplierBundle` of obligations and produces `TiePointBridgeBudgetedIndexed`.

Stated at `Mbr ≤ mS` (not `1 ≤ mS`): the selector / dstar machinery only holds past the rep-config
pre-period threshold `Mbr`; the downstream D4 chain is threaded with this floor.  The selected-atom
budget `C` is fixed before the row period is chosen, which lets the bridge pick a finite row index after
seeing the concrete row and its budget proof.
-/
import RequestProject.CopiedAchSetFold2
import RequestProject.CopiedAchieverLocus
import RequestProject.CopiedBoundedGateBand
import RequestProject.CopiedDstarCMS
import RequestProject.CopiedSelUniform
import RequestProject.CopiedSelector
import RequestProject.CopiedTie2b

namespace CopiedTieSlice

open WRP Step SliceMSO MSOMarkN CopiedSetupMS

/-- Forget the `Fin` bound of a finite set of bounded natural indices. -/
def finVals {N : ℕ} (s : Finset (Fin N)) : Finset ℕ :=
  s.image (fun x => x.1)

theorem mem_finVals_lt {N : ℕ} {s : Finset (Fin N)} {x : ℕ} (hx : x ∈ finVals s) :
    x < N := by
  rw [finVals] at hx
  obtain ⟨y, _hy, hyx⟩ := Finset.mem_image.mp hx
  rw [← hyx]
  exact y.2

/-- Pack a finite set of naturals into `Fin N`, using a pointwise bound. -/
def finPack {N : ℕ} (s : Finset ℕ) (h : ∀ x ∈ s, x < N) : Finset (Fin N) :=
  s.attach.image (fun x => (⟨x.1, h x.1 x.2⟩ : Fin N))

theorem mem_finVals_finPack {N : ℕ} (s : Finset ℕ) (h : ∀ x ∈ s, x < N) (x : ℕ) :
    x ∈ finVals (finPack s h) ↔ x ∈ s := by
  constructor
  · intro hx
    rw [finVals, finPack] at hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    subst y
    simp only at hyx
    rw [← hyx]
    exact z.2
  · intro hx
    rw [finVals, finPack]
    refine Finset.mem_image.mpr ⟨⟨x, h x hx⟩, ?_, rfl⟩
    refine Finset.mem_image.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
    exact Finset.mem_attach _ _

theorem finVals_finPack {N : ℕ} (s : Finset ℕ) (h : ∀ x ∈ s, x < N) :
    finVals (finPack s h) = s := by
  ext x
  exact mem_finVals_finPack s h x

/-- Abstract tuple-fibre scalarization used by the current arity-1 bridge.  The
general-arity route should replace callers of this package by descriptor-level
coverage rather than by proving this scalarization. -/
def TupleFiberScalarization (P : WRP.Presentation Step Step) : Prop :=
    ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (xb : Fin (P.toPoly.arity c) → ℕ),
      xb = fun _ : Fin (P.toPoly.arity c) => xb j0

/-- Arity-1 supplier for `TupleFiberScalarization`. -/
theorem tupleFiberScalarization_of_arity_one
    (P : WRP.Presentation Step Step) (harity1 : ∀ c, P.toPoly.arity c = 1) :
    TupleFiberScalarization P := by
  intro c j0 xb
  have hsub : Subsingleton (Fin (P.toPoly.arity c)) := by rw [harity1 c]; infer_instance
  funext i
  rw [@Subsingleton.elim _ hsub i j0]

/-- Under tuple-fibre scalarization, updating one distinguished coordinate
collapses to the corresponding constant tuple. -/
theorem update_eq_const_of_tupleFiberScalarization
    (P : WRP.Presentation Step Step) (hTuple : TupleFiberScalarization P)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (v : ℕ) :
    Function.update ī0 j0 v = fun _ : Fin (P.toPoly.arity c) => v := by
  have h := hTuple c j0 (Function.update ī0 j0 v)
  simpa [Function.update] using h

/-- Abstract coverage for the CORE/shallow/deep-boundary part of the semantic
split.  It is a descriptor-level obligation, so an arbitrary-arity bridge can
supply it directly (no tuple-fibre scalarisation is needed). -/
def CoreBoundaryCoverage (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    ∀ {B Bh M mthr qB Q mS n Nc mx : ℕ}
      {pcF Ts Tp : Fin P.toPoly.K → ℕ}
      (_j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c))
      {S1 : (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ}
      {F2 : (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ}
      {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ},
      1 ≤ mS →
      qB < mS →
      1 ≤ Q →
      qB = mx + Q + 1 →
      (∀ c' : Fin P.toPoly.K, pcF c' ∣ Q) →
      (∀ c' : Fin P.toPoly.K, Ts c' ≤ mx) →
      (∀ c' : Fin P.toPoly.K, Tp c' ≤ mx) →
      mS ≤ Nc + mx →
      (∀ (b : P.toPoly.Atom),
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        CopiedTieGate.cfgCellGAFL B Bh M mthr S1
          (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
          mS n b →
        (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF B) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          b.2 = CopiedDstar.cellTupleF rs mS t n →
          CopiedTieGate.cfgPosL M mthr (S1 b.1 rs) ∅ ∅
            (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
          rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity b.1) qB qB) →
        (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF Bh) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          b.2 = CopiedDstar.cellTupleF rs mS t n →
          CopiedTieGate.cfgPosL M mthr ∅ (F2 b.1 rs) ∅
            (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
          rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity b.1) qB qB) →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b) →
      (∀ (c' : Fin P.toPoly.K) (l : ℕ),
        l < mS - 1 → qB ≤ l → ¬ l + pcF c' < Nc →
        (P.toPoly.sel c' (copiedSlice mS n)
            (fun _ : Fin (P.toPoly.arity c') => mS + 2 * n + 1 + l)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (fun _ : Fin (P.toPoly.arity c') => mS + 2 * n + 1 + l) = D) →
        P.rank c' (copiedSlice mS n)
            (fun _ : Fin (P.toPoly.arity c') => mS + 2 * n + 1 + l)
          = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
          (⟨c', fun _ : Fin (P.toPoly.arity c') => mS + 2 * n + 1 + l⟩ :
            P.toPoly.Atom)) →
      (∀ (c' : Fin P.toPoly.K) (l : ℕ),
        l < mS - 1 → qB ≤ l → ¬ l + pcF c' < Nc →
        (P.toPoly.sel c' (copiedSlice mS n)
            (fun _ : Fin (P.toPoly.arity c') => l)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (fun _ : Fin (P.toPoly.arity c') => l) = D) →
        P.rank c' (copiedSlice mS n)
            (fun _ : Fin (P.toPoly.arity c') => l)
          = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
          (⟨c', fun _ : Fin (P.toPoly.arity c') => l⟩ : P.toPoly.Atom)) →
      (∀ b : P.toPoly.Atom,
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
        CopiedTieGate.cfgCellGAFL B Bh M mthr S1
          (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
          mS n b) →
      ∀ b : P.toPoly.Atom,
        ¬ (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
          b.2 = fun _ => mS + 2 * n + 1 + l) →
        ¬ (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
          b.2 = fun _ => l) →
        (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
          P.toPoly.labelOf (copiedSlice mS n) b = D) →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b

/-- Update-shaped CORE/shallow/deep-boundary coverage.  This is the first
component needed by `tieSemanticUpdateSplitAt`: the suffix/prefix middle-run
classes are distinguished-coordinate update tuples rather than constant
tuples. -/
def CoreBoundaryUpdateCoverage (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    ∀ {B Bh M mthr qB Q mS n Nc mx : ℕ}
      {pcF Ts Tp : Fin P.toPoly.K → ℕ}
      (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
      (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c))
      {S1 : (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ}
      {F2 : (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ}
      {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ},
      1 ≤ mS →
      qB < mS →
      1 ≤ Q →
      qB = mx + Q + 1 →
      (∀ c' : Fin P.toPoly.K, pcF c' ∣ Q) →
      (∀ c' : Fin P.toPoly.K, Ts c' ≤ mx) →
      (∀ c' : Fin P.toPoly.K, Tp c' ≤ mx) →
      mS ≤ Nc + mx →
      (∀ (b : P.toPoly.Atom),
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        CopiedTieGate.cfgCellGAFL B Bh M mthr S1
          (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
          mS n b →
        (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF B) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          b.2 = CopiedDstar.cellTupleF rs mS t n →
          CopiedTieGate.cfgPosL M mthr (S1 b.1 rs) ∅ ∅
            (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
          rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity b.1) qB qB) →
        (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF Bh) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          b.2 = CopiedDstar.cellTupleF rs mS t n →
          CopiedTieGate.cfgPosL M mthr ∅ (F2 b.1 rs) ∅
            (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
          rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity b.1) qB qB) →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b) →
      (∀ (c' : Fin P.toPoly.K) (l : ℕ),
        l < mS - 1 → qB ≤ l → ¬ l + pcF c' < Nc →
        (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l)) = D) →
        P.rank c' (copiedSlice mS n)
            (Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l))
          = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
          (⟨c', Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l)⟩ :
            P.toPoly.Atom)) →
      (∀ (c' : Fin P.toPoly.K) (l : ℕ),
        l < mS - 1 → qB ≤ l → ¬ l + pcF c' < Nc →
        (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (ī0F c') (j0F c') l)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (ī0F c') (j0F c') l) = D) →
        P.rank c' (copiedSlice mS n)
            (Function.update (ī0F c') (j0F c') l)
          = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
          (⟨c', Function.update (ī0F c') (j0F c') l⟩ : P.toPoly.Atom)) →
      (∀ b : P.toPoly.Atom,
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
        CopiedTieGate.cfgCellGAFL B Bh M mthr S1
          (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
          mS n b) →
      ∀ b : P.toPoly.Atom,
        ¬ (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
          b.2 = Function.update (ī0F b.1) (j0F b.1) (mS + 2 * n + 1 + l)) →
        ¬ (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
          b.2 = Function.update (ī0F b.1) (j0F b.1) l) →
        (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
          P.toPoly.labelOf (copiedSlice mS n) b = D) →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b

/-- Zero-base update-shaped CORE/shallow/deep-boundary coverage.  This is the
canonical specialization used by `mkBridgeUpdateRowIndex`: every non-moving
coordinate is the shared zero base tuple, while `j0F` chooses the distinguished
updated coordinate. -/
def CoreBoundaryUpdateZeroCoverage (P : WRP.Presentation Step Step) (hV : P.Valid) :
    Prop :=
    ∀ {B Bh M mthr qB Q mS n Nc mx : ℕ}
      {pcF Ts Tp : Fin P.toPoly.K → ℕ}
      (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c))
      {S1 : (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ}
      {F2 : (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ}
      {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ},
      1 ≤ mS →
      qB < mS →
      1 ≤ Q →
      qB = mx + Q + 1 →
      (∀ c' : Fin P.toPoly.K, pcF c' ∣ Q) →
      (∀ c' : Fin P.toPoly.K, Ts c' ≤ mx) →
      (∀ c' : Fin P.toPoly.K, Tp c' ≤ mx) →
      mS ≤ Nc + mx →
      (∀ (b : P.toPoly.Atom),
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        CopiedTieGate.cfgCellGAFL B Bh M mthr S1
          (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
          mS n b →
        (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF B) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          b.2 = CopiedDstar.cellTupleF rs mS t n →
          CopiedTieGate.cfgPosL M mthr (S1 b.1 rs) ∅ ∅
            (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
          rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity b.1) qB qB) →
        (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF Bh) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          b.2 = CopiedDstar.cellTupleF rs mS t n →
          CopiedTieGate.cfgPosL M mthr ∅ (F2 b.1 rs) ∅
            (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
          rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity b.1) qB qB) →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b) →
      (∀ (c' : Fin P.toPoly.K) (l : ℕ),
        l < mS - 1 → qB ≤ l → ¬ l + pcF c' < Nc →
        (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l)) = D) →
        P.rank c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l))
          = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
          (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mS + 2 * n + 1 + l)⟩ : P.toPoly.Atom)) →
      (∀ (c' : Fin P.toPoly.K) (l : ℕ),
        l < mS - 1 → qB ≤ l → ¬ l + pcF c' < Nc →
        (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = D) →
        P.rank c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
          = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
          (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l⟩ :
            P.toPoly.Atom)) →
      (∀ b : P.toPoly.Atom,
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
        CopiedTieGate.cfgCellGAFL B Bh M mthr S1
          (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
          mS n b) →
      ∀ b : P.toPoly.Atom,
        ¬ (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
          b.2 = Function.update (fun _ : Fin (P.toPoly.arity b.1) => 0)
            (j0F b.1) (mS + 2 * n + 1 + l)) →
        ¬ (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
          b.2 = Function.update (fun _ : Fin (P.toPoly.arity b.1) => 0)
            (j0F b.1) l) →
        (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
          P.toPoly.labelOf (copiedSlice mS n) b = D) →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b

/-- The old fully-parametric update boundary predicate supplies the canonical
zero-base boundary predicate by specializing the base tuple to zero. -/
theorem coreBoundaryUpdateZeroCoverage_of_updateCoverage
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hCore : CoreBoundaryUpdateCoverage P hV) :
    CoreBoundaryUpdateZeroCoverage P hV := by
  intro B Bh M mthr qB Q mS n Nc mx pcF Ts Tp j0F S1 F2 c ī
    hm hqB_lt hQ1 hqB_def hpcF_dvd_Q hTs_le_mx hTp_le_mx hNcmx
    hcore_from_cfg hdeep_suf_order hdeep_pre_order hcfg_of_rank
    b hnotS hnotP hselD hbach
  exact hCore (fun c' (_ : Fin (P.toPoly.arity c')) => 0) j0F
    hm hqB_lt hQ1 hqB_def hpcF_dvd_Q hTs_le_mx hTp_le_mx hNcmx
    hcore_from_cfg hdeep_suf_order hdeep_pre_order hcfg_of_rank
    b hnotS hnotP hselD hbach

/-- Consume the update-shaped semantic split to recover the whole `D`-competitor
order obligation.  This is the proof-body seam for replacing the current
legacy constant-tuple split in the bridge with descriptor/update branches. -/
theorem whole_order_of_update_split
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    {mS n Nc : ℕ} {pcF Ts Tp : Fin P.toPoly.K → ℕ}
    {ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ}
    {j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c)}
    {c0 : Fin P.toPoly.K} {ī0m : Fin (P.toPoly.arity c0) → ℕ}
    (hsplit :
      CopiedSelUniform.tieSemanticUpdateSplitAt P hV mS n c0 ī0m pcF Ts Tp Nc ī0F j0F)
    (hcore : ∀ b : P.toPoly.Atom,
      ¬ (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (ī0F b.1) (j0F b.1) (mS + 2 * n + 1 + l)) →
      ¬ (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (ī0F b.1) (j0F b.1) l) →
      (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b)
    (hsuf : ∀ r : ℕ,
      (∀ b : P.toPoly.Atom,
        (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
          b.2 = Function.update (ī0F b.1) (j0F b.1) (mS + 2 * n + 1 + l)) →
        Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
        (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
          P.toPoly.labelOf (copiedSlice mS n) b = D) →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n) →
      ∀ b : P.toPoly.Atom,
        (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
          b.2 = Function.update (ī0F b.1) (j0F b.1) (mS + 2 * n + 1 + l)) →
        Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
        (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
          P.toPoly.labelOf (copiedSlice mS n) b = D) →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b)
    (hpre : ∀ r : ℕ,
      (∀ b : P.toPoly.Atom,
        (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
          b.2 = Function.update (ī0F b.1) (j0F b.1) l) →
        Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
        (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
          P.toPoly.labelOf (copiedSlice mS n) b = D) →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n) →
      ∀ b : P.toPoly.Atom,
        (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
          b.2 = Function.update (ī0F b.1) (j0F b.1) l) →
        Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
        (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
          P.toPoly.labelOf (copiedSlice mS n) b = D) →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b) :
    ∀ b : P.toPoly.Atom,
      (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b :=
  hsplit.mpr ⟨hcore, hsuf, hpre⟩

/-- Core-branch atom order from the update-shaped boundary coverage, at the zero
base tuple — matching the canonical bridge row index whose untouched coordinates
are all zero. -/
theorem core_order_of_update_zero_boundary
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hCoreBoundary : CoreBoundaryUpdateZeroCoverage P hV)
    {B Bh M mthr qB Q mS n Nc mx : ℕ}
    {pcF Ts Tp : Fin P.toPoly.K → ℕ}
    (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c))
    {S1 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ}
    {F2 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ}
    {c0 : Fin P.toPoly.K} {ī0m : Fin (P.toPoly.arity c0) → ℕ}
    (hm : 1 ≤ mS) (hqB_lt : qB < mS) (hQ1 : 1 ≤ Q)
    (hqB_def : qB = mx + Q + 1)
    (hpcF_dvd_Q : ∀ c' : Fin P.toPoly.K, pcF c' ∣ Q)
    (hTs_le_mx : ∀ c' : Fin P.toPoly.K, Ts c' ≤ mx)
    (hTp_le_mx : ∀ c' : Fin P.toPoly.K, Tp c' ≤ mx)
    (hNcmx : mS ≤ Nc + mx)
    (hcore_from_cfg : ∀ (b : P.toPoly.Atom),
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      CopiedTieGate.cfgCellGAFL B Bh M mthr S1
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
        mS n b →
      (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF B) (t : ℕ),
        (∀ i, (rs i).valid mS) → t < n →
        b.2 = CopiedDstar.cellTupleF rs mS t n →
        CopiedTieGate.cfgPosL M mthr (S1 b.1 rs) ∅ ∅
          (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
        rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity b.1) qB qB) →
      (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF Bh) (t : ℕ),
        (∀ i, (rs i).valid mS) → t < n →
        b.2 = CopiedDstar.cellTupleF rs mS t n →
        CopiedTieGate.cfgPosL M mthr ∅ (F2 b.1 rs) ∅
          (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
        rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity b.1) qB qB) →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b)
    (hdeep_suf_order : ∀ (c' : Fin P.toPoly.K) (l : ℕ),
      l < mS - 1 → qB ≤ l → ¬ l + pcF c' < Nc →
      (P.toPoly.sel c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mS + 2 * n + 1 + l))
        ∧ P.toPoly.label c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mS + 2 * n + 1 + l)) = D) →
      P.rank c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mS + 2 * n + 1 + l))
        = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩
        (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)⟩ : P.toPoly.Atom))
    (hdeep_pre_order : ∀ (c' : Fin P.toPoly.K) (l : ℕ),
      l < mS - 1 → qB ≤ l → ¬ l + pcF c' < Nc →
      (P.toPoly.sel c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
        ∧ P.toPoly.label c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = D) →
      P.rank c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
        = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩
        (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l⟩ :
          P.toPoly.Atom))
    (hcfg_of_rank : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      CopiedTieGate.cfgCellGAFL B Bh M mthr S1
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
        mS n b) :
    ∀ b : P.toPoly.Atom,
      ¬ (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (fun _ : Fin (P.toPoly.arity b.1) => 0)
          (j0F b.1) (mS + 2 * n + 1 + l)) →
      ¬ (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (fun _ : Fin (P.toPoly.arity b.1) => 0)
          (j0F b.1) l) →
      (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b :=
  hCoreBoundary j0F hm hqB_lt hQ1 hqB_def hpcF_dvd_Q hTs_le_mx
    hTp_le_mx hNcmx hcore_from_cfg hdeep_suf_order hdeep_pre_order hcfg_of_rank

/-- Turn the suffix class hypothesis from `tieSemanticUpdateSplitAt` into the
rank equality for the distinguished-coordinate update tuple. -/
theorem rank_update_suffix_of_split_class
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    {mS n Nc r : ℕ} {pcF Ts : Fin P.toPoly.K → ℕ}
    {ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ}
    {j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c)}
    {c' : Fin P.toPoly.K} {xb : Fin (P.toPoly.arity c') → ℕ} {l : ℕ}
    (hclass : ∀ b : P.toPoly.Atom,
      (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (ī0F b.1) (j0F b.1) (mS + 2 * n + 1 + l)) →
      Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
      (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n)
    (hlo : Ts c' + pcF c' ≤ l) (hhi : l + pcF c' < Nc)
    (hxbeq : xb = Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l))
    (hcls : Nat.pair c'.val ((xb (j0F c')) % pcF c') = r)
    (hselD : P.toPoly.selectedAtom (copiedSlice mS n) (⟨c', xb⟩ : P.toPoly.Atom) ∧
      P.toPoly.labelOf (copiedSlice mS n) (⟨c', xb⟩ : P.toPoly.Atom) = D) :
    P.rank c' (copiedSlice mS n)
        (Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l))
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  have hcls_update :
      Nat.pair c'.val (((Function.update (ī0F c') (j0F c')
        (mS + 2 * n + 1 + l)) (j0F c')) % pcF c') = r := by
    simpa [hxbeq] using hcls
  have hselD_update :
      P.toPoly.selectedAtom (copiedSlice mS n)
          (⟨c', Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l)⟩ :
            P.toPoly.Atom) ∧
        P.toPoly.labelOf (copiedSlice mS n)
          (⟨c', Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l)⟩ :
            P.toPoly.Atom) = D := by
    simpa [hxbeq] using hselD
  simpa [WRP.Presentation.rankOf] using
    hclass
      (⟨c', Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l)⟩ :
        P.toPoly.Atom)
      ⟨l, hlo, hhi, rfl⟩ hcls_update hselD_update

/-- Prefix twin of `rank_update_suffix_of_split_class`. -/
theorem rank_update_prefix_of_split_class
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    {mS n Nc r : ℕ} {pcF Tp : Fin P.toPoly.K → ℕ}
    {ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ}
    {j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c)}
    {c' : Fin P.toPoly.K} {xb : Fin (P.toPoly.arity c') → ℕ} {l : ℕ}
    (hclass : ∀ b : P.toPoly.Atom,
      (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (ī0F b.1) (j0F b.1) l) →
      Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
      (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n)
    (hlo : Tp c' + pcF c' ≤ l) (hhi : l + pcF c' < Nc)
    (hxbeq : xb = Function.update (ī0F c') (j0F c') l)
    (hcls : Nat.pair c'.val ((xb (j0F c')) % pcF c') = r)
    (hselD : P.toPoly.selectedAtom (copiedSlice mS n) (⟨c', xb⟩ : P.toPoly.Atom) ∧
      P.toPoly.labelOf (copiedSlice mS n) (⟨c', xb⟩ : P.toPoly.Atom) = D) :
    P.rank c' (copiedSlice mS n) (Function.update (ī0F c') (j0F c') l)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  have hcls_update :
      Nat.pair c'.val (((Function.update (ī0F c') (j0F c') l) (j0F c')) % pcF c') = r := by
    simpa [hxbeq] using hcls
  have hselD_update :
      P.toPoly.selectedAtom (copiedSlice mS n)
          (⟨c', Function.update (ī0F c') (j0F c') l⟩ : P.toPoly.Atom) ∧
        P.toPoly.labelOf (copiedSlice mS n)
          (⟨c', Function.update (ī0F c') (j0F c') l⟩ : P.toPoly.Atom) = D := by
    simpa [hxbeq] using hselD
  simpa [WRP.Presentation.rankOf] using
    hclass (⟨c', Function.update (ī0F c') (j0F c') l⟩ : P.toPoly.Atom)
      ⟨l, hlo, hhi, rfl⟩ hcls_update hselD_update

/-- The current arity-1 scalarization supplies the descriptor-level
CORE/boundary coverage package. -/
theorem coreBoundaryCoverage_of_tupleFiberScalarization
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hTupleScalar : TupleFiberScalarization P) :
    CoreBoundaryCoverage P hV := by
  intro B Bh M mthr qB Q mS n Nc mx pcF Ts Tp j0F S1 F2 c ī
    hm hqB_lt hQ1 hqB_def hpcF_dvd_Q hTs_le_mx hTp_le_mx hNcmx
    hcore_from_cfg hdeep_suf_order hdeep_pre_order hcfg_of_rank
    b hnotS hnotP hselD hbach
  rcases b with ⟨c', xb⟩
  let p0 : ℕ := xb (j0F c')
  have hbconst : xb = fun _ : Fin (P.toPoly.arity c') => p0 := by
    dsimp [p0]
    exact hTupleScalar c' (j0F c') xb
  have hp0val : p0 < (copiedSlice mS n).length := by
    dsimp [p0]
    exact hselD.1.1 (j0F c')
  have hp0lt : p0 < 2 * (mS + n) := by
    simpa [length_copiedSlice] using hp0val
  have hrawcfg :
      CopiedTieGate.cfgCellGAFL B Bh M mthr S1
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
        mS n (⟨c', xb⟩ : P.toPoly.Atom) :=
    hcfg_of_rank (⟨c', xb⟩ : P.toPoly.Atom) hselD.1 hselD.2 hbach
  have hbounded_coreish :
      ∀ {B0 : ℕ}, (¬ p0 < mS - 1) → (¬ mS + 2 * n + 1 ≤ p0) →
        ∀ (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B0) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          xb = CopiedDstar.cellTupleF rs mS t n →
          rs ∈ CopiedBoundedGate.boundedTuplesF B0 (P.toPoly.arity c') qB qB := by
    intro B0 hnotPre hnotSuf rs t hvalid _htn hcell
    rw [CopiedBoundedGate.mem_boundedTuplesF]
    intro i
    have hcelli := congrFun hcell i
    have hxi : xb i = p0 := by rw [hbconst]
    cases hrs : rs i with
    | core r0 =>
        simp
    | prefIdx q =>
        exfalso
        have hvalidi := hvalid i
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs] at hcelli
        simp [CopiedCells.RegionSpecF.valid, hrs] at hvalidi
        exact hnotPre (by omega)
    | sufIdx l =>
        exfalso
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs] at hcelli
        exact hnotSuf (by omega)
  have hbounded_pref :
      ∀ {B0 : ℕ}, p0 < qB →
        ∀ (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B0) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          xb = CopiedDstar.cellTupleF rs mS t n →
          rs ∈ CopiedBoundedGate.boundedTuplesF B0 (P.toPoly.arity c') qB qB := by
    intro B0 hpq rs t hvalid _htn hcell
    rw [CopiedBoundedGate.mem_boundedTuplesF]
    intro i
    have hcelli := congrFun hcell i
    have hxi : xb i = p0 := by rw [hbconst]
    cases hrs : rs i with
    | core r0 =>
        simp
    | prefIdx q =>
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs] at hcelli
        simp
        omega
    | sufIdx l =>
        exfalso
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs] at hcelli
        have := hqB_lt
        omega
  have hbounded_suf :
      ∀ {B0 : ℕ} (l : ℕ), p0 = mS + 2 * n + 1 + l → l < qB →
        ∀ (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B0) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          xb = CopiedDstar.cellTupleF rs mS t n →
          rs ∈ CopiedBoundedGate.boundedTuplesF B0 (P.toPoly.arity c') qB qB := by
    intro B0 l hpEq hlq rs t hvalid _htn hcell
    rw [CopiedBoundedGate.mem_boundedTuplesF]
    intro i
    have hcelli := congrFun hcell i
    have hxi : xb i = p0 := by rw [hbconst]
    cases hrs : rs i with
    | core r0 =>
        simp
    | prefIdx q =>
        exfalso
        have hvalidi := hvalid i
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs] at hcelli
        simp [CopiedCells.RegionSpecF.valid, hrs] at hvalidi
        omega
    | sufIdx l' =>
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs] at hcelli
        simp
        omega
  have hcore_by_coreish (hnotPre : ¬ p0 < mS - 1)
      (hnotSuf : ¬ mS + 2 * n + 1 ≤ p0) :
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
        (⟨c', xb⟩ : P.toPoly.Atom) :=
    hcore_from_cfg (⟨c', xb⟩ : P.toPoly.Atom) hselD.1 hselD.2 hrawcfg
      (by
        intro rs t hvalid htn hcell _hpos
        exact hbounded_coreish hnotPre hnotSuf rs t hvalid htn hcell)
      (by
        intro rs t hvalid htn hcell _hpos
        exact hbounded_coreish hnotPre hnotSuf rs t hvalid htn hcell)
  rcases CopiedCells.position_cases_copied mS p0 n hm hp0lt with
  hpref | hpreBoundary | hmid | hsufBoundary | hsuf
  · by_cases hpq : p0 < qB
    · exact hcore_from_cfg (⟨c', xb⟩ : P.toPoly.Atom) hselD.1 hselD.2 hrawcfg
        (by
          intro rs t hvalid htn hcell _hpos
          exact hbounded_pref hpq rs t hvalid htn hcell)
        (by
          intro rs t hvalid htn hcell _hpos
          exact hbounded_pref hpq rs t hvalid htn hcell)
    · have hqBp : qB ≤ p0 := by omega
      have hTqP : Tp c' + pcF c' < qB := by
        have hpcQ : pcF c' ≤ Q :=
          Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ1) (hpcF_dvd_Q c')
        have hTp := hTp_le_mx c'
        rw [hqB_def]
        omega
      have hnotHi : ¬ p0 + pcF c' < Nc := by
        intro hhi
        have hlower : Tp c' + pcF c' ≤ p0 := by omega
        exact hnotP ⟨p0, hlower, hhi, hbconst⟩
      have hselRun :
          P.toPoly.sel c' (copiedSlice mS n)
              (fun _ : Fin (P.toPoly.arity c') => p0)
            ∧ P.toPoly.label c' (copiedSlice mS n)
              (fun _ : Fin (P.toPoly.arity c') => p0) = D := by
        rw [← hbconst]
        exact ⟨hselD.1.2, hselD.2⟩
      have hachRun :
          P.rank c' (copiedSlice mS n)
              (fun _ : Fin (P.toPoly.arity c') => p0)
            = CopiedDstar.dstarRankGA_m P hV mS n := by
        rw [← hbconst]
        exact hbach
      rw [hbconst]
      exact hdeep_pre_order c' p0 hpref hqBp hnotHi hselRun hachRun
  · exact hcore_by_coreish (by omega) (by omega)
  · rcases hmid with ⟨hj, hpEven | hpOdd⟩
    · exact hcore_by_coreish (by omega) (by omega)
    · exact hcore_by_coreish (by omega) (by omega)
  · exact hcore_by_coreish (by omega) (by omega)
  · set l : ℕ := p0 - (mS + 2 * n + 1) with hl_def
    have hpEq : p0 = mS + 2 * n + 1 + l := by
      rw [hl_def]
      omega
    have hlm : l < mS - 1 := by
      rw [length_copiedSlice] at hp0val
      omega
    by_cases hlq : l < qB
    · exact hcore_from_cfg (⟨c', xb⟩ : P.toPoly.Atom) hselD.1 hselD.2 hrawcfg
        (by
          intro rs t hvalid htn hcell _hpos
          exact hbounded_suf l hpEq hlq rs t hvalid htn hcell)
        (by
          intro rs t hvalid htn hcell _hpos
          exact hbounded_suf l hpEq hlq rs t hvalid htn hcell)
    · have hqBl : qB ≤ l := by omega
      have hTqS : Ts c' + pcF c' < qB := by
        have hpcQ : pcF c' ≤ Q :=
          Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ1) (hpcF_dvd_Q c')
        have hTs := hTs_le_mx c'
        rw [hqB_def]
        omega
      have htuple :
          xb = fun _ : Fin (P.toPoly.arity c') => mS + 2 * n + 1 + l := by
        rw [hbconst]
        funext i
        exact hpEq
      have hnotHi : ¬ l + pcF c' < Nc := by
        intro hhi
        have hlower : Ts c' + pcF c' ≤ l := by omega
        exact hnotS ⟨l, hlower, hhi, htuple⟩
      have hselRun :
          P.toPoly.sel c' (copiedSlice mS n)
              (fun _ : Fin (P.toPoly.arity c') => mS + 2 * n + 1 + l)
            ∧ P.toPoly.label c' (copiedSlice mS n)
              (fun _ : Fin (P.toPoly.arity c') => mS + 2 * n + 1 + l) = D := by
        rw [← htuple]
        exact ⟨hselD.1.2, hselD.2⟩
      have hachRun :
          P.rank c' (copiedSlice mS n)
              (fun _ : Fin (P.toPoly.arity c') => mS + 2 * n + 1 + l)
            = CopiedDstar.dstarRankGA_m P hV mS n := by
        rw [← htuple]
        exact hbach
      rw [htuple]
      exact hdeep_suf_order c' l hlm hqBl hnotHi hselRun hachRun

/-- Legacy core-boundary coverage yields the update-shaped core-boundary
interface under tuple-fibre scalarization. -/
theorem coreBoundaryUpdateCoverage_of_coreBoundaryCoverage_of_tupleFiberScalarization
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hCore : CoreBoundaryCoverage P hV)
    (hTuple : TupleFiberScalarization P) :
    CoreBoundaryUpdateCoverage P hV := by
  intro B Bh M mthr qB Q mS n Nc mx pcF Ts Tp ī0F j0F S1 F2 c ī
    hm hqB_lt hQ1 hqB_def hpcF_dvd_Q hTs_le_mx hTp_le_mx hNcmx
    hcore_from_cfg hdeep_suf_update hdeep_pre_update hcfg_of_rank
    b hnotS hnotP hselD hbach
  exact hCore j0F hm hqB_lt hQ1 hqB_def hpcF_dvd_Q hTs_le_mx hTp_le_mx hNcmx
    hcore_from_cfg
    (by
      intro c' l hl hqBl hnotHi hselRun hachRun
      have hupd :=
        update_eq_const_of_tupleFiberScalarization P hTuple c' (j0F c') (ī0F c')
          (mS + 2 * n + 1 + l)
      have hselRunU :
          P.toPoly.sel c' (copiedSlice mS n)
              (Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l))
            ∧ P.toPoly.label c' (copiedSlice mS n)
              (Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l)) = D := by
        simpa [hupd] using hselRun
      have hachRunU :
          P.rank c' (copiedSlice mS n)
              (Function.update (ī0F c') (j0F c') (mS + 2 * n + 1 + l))
            = CopiedDstar.dstarRankGA_m P hV mS n := by
        simpa [hupd] using hachRun
      have hord :=
        hdeep_suf_update c' l hl hqBl hnotHi hselRunU hachRunU
      simpa [hupd] using hord)
    (by
      intro c' l hl hqBl hnotHi hselRun hachRun
      have hupd :=
        update_eq_const_of_tupleFiberScalarization P hTuple c' (j0F c') (ī0F c') l
      have hselRunU :
          P.toPoly.sel c' (copiedSlice mS n)
              (Function.update (ī0F c') (j0F c') l)
            ∧ P.toPoly.label c' (copiedSlice mS n)
              (Function.update (ī0F c') (j0F c') l) = D := by
        simpa [hupd] using hselRun
      have hachRunU :
          P.rank c' (copiedSlice mS n) (Function.update (ī0F c') (j0F c') l)
            = CopiedDstar.dstarRankGA_m P hV mS n := by
        simpa [hupd] using hachRun
      have hord := hdeep_pre_update c' l hl hqBl hnotHi hselRunU hachRunU
      simpa [hupd] using hord)
    hcfg_of_rank b
    (by
      intro hsuf
      apply hnotS
      rcases hsuf with ⟨l, hlo, hhi, hbeq⟩
      refine ⟨l, hlo, hhi, ?_⟩
      have hupd :=
        update_eq_const_of_tupleFiberScalarization P hTuple b.1 (j0F b.1) (ī0F b.1)
          (mS + 2 * n + 1 + l)
      simpa [hupd] using hbeq)
    (by
      intro hpre
      apply hnotP
      rcases hpre with ⟨l, hlo, hhi, hbeq⟩
      refine ⟨l, hlo, hhi, ?_⟩
      have hupd :=
        update_eq_const_of_tupleFiberScalarization P hTuple b.1 (j0F b.1) (ī0F b.1) l
      simpa [hupd] using hbeq)
    hselD hbach

/-- Descriptor-facing run-residue coverage.  Both halves are phrased in the
update-tuple language used by arbitrary-arity descriptor rows: d*-achiever
coverage for updated selected witnesses, and band/deep rank soundness for
updated run-band callbacks. -/
def RunResidueUpdateCoverage (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    CopiedAchieverLocus.DstarAchieverUpdateLocus P hV ∧
    CopiedBoundedGateBand.BandedUpdateRankSoundness P hV

/-- Public arity-free supplier for descriptor-facing run-residue coverage. -/
theorem runResidueUpdateCoverage
    (P : WRP.Presentation Step Step) (hV : P.Valid) :
    RunResidueUpdateCoverage P hV :=
  ⟨CopiedAchieverLocus.dstarAchieverUpdateLocus P hV,
    CopiedBoundedGateBand.bandedUpdateRankSoundness P hV⟩

/-- Zero-base update supplier bundle for the canonical arbitrary-arity bridge
route.  This refinement keeps the distinguished-coordinate update split aligned
with `mkBridgeUpdateRowIndex`, whose non-moving coordinates use the shared
zero tuple. -/
def BridgeUpdateZeroSupplierBundle (P : WRP.Presentation Step Step) (hV : P.Valid) :
    Prop :=
    CopiedSelUniform.TieSemanticUpdateZeroSplitData P hV ∧
    CopiedSelUniform.RunClassUpdateUniformCoverage P hV ∧
    (∃ CbudN : ℕ,
      ∀ (mS : ℕ), 1 ≤ mS →
        ∀ n, P.toPoly.domain (copiedSlice mS n) →
          ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
            (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
            l.length ≤ CbudN * (mS + n + 1)) ∧
    RunResidueUpdateCoverage P hV ∧
    CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV ∧
    CoreBoundaryUpdateCoverage P hV

/-- Zero-base update supplier bundle with the boundary component already
specialized to the canonical zero base tuple.  This is the direct arbitrary-
arity bridge interface; the older `BridgeUpdateZeroSupplierBundle` remains as
a compatibility package when callers still have fully-parametric update
boundary coverage. -/
def BridgeUpdateZeroBoundarySupplierBundle
    (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    CopiedSelUniform.TieSemanticUpdateZeroSplitData P hV ∧
    CopiedSelUniform.RunClassUpdateUniformCoverage P hV ∧
    (∃ CbudN : ℕ,
      ∀ (mS : ℕ), 1 ≤ mS →
        ∀ n, P.toPoly.domain (copiedSlice mS n) →
          ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
            (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
            l.length ≤ CbudN * (mS + n + 1)) ∧
    RunResidueUpdateCoverage P hV ∧
    CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV ∧
    CoreBoundaryUpdateZeroCoverage P hV

/-- A fully-parametric zero-base supplier bundle forgets to the zero-boundary
bundle by specializing its boundary component to the shared zero base tuple. -/
theorem bridgeUpdateZeroBoundarySupplierBundle_of_zeroSupplierBundle
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hZero : BridgeUpdateZeroSupplierBundle P hV) :
    BridgeUpdateZeroBoundarySupplierBundle P hV := by
  rcases hZero with
    ⟨hZeroSplit, hRunClassUpdate, hBudget, hRunResidueUpdate, hBandActiveUpdate,
      hCoreBoundaryUpdate⟩
  exact ⟨hZeroSplit, hRunClassUpdate, hBudget, hRunResidueUpdate, hBandActiveUpdate,
    coreBoundaryUpdateZeroCoverage_of_updateCoverage P hV hCoreBoundaryUpdate⟩

/-- Build the update-shaped bridge supplier bundle from a chosen distinguished
coordinate in every copy.  The semantic split component is the general-arity
zero-base update split; no tuple-fibre scalarisation is used for that part. -/
theorem bridgeUpdateZeroSupplierBundle_of_coordChoice
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c))
    (CbudN : ℕ)
    (hbudCN : ∀ (mS : ℕ), 1 ≤ mS →
      ∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ CbudN * (mS + n + 1))
    (hCoreBoundary : CoreBoundaryUpdateCoverage P hV) :
    BridgeUpdateZeroSupplierBundle P hV :=
  ⟨CopiedSelUniform.tieSemanticUpdateZeroSplitData_of_coordChoice P hV
      (CopiedSelUniform.runClassUpdateUniformCoverage P hV) j0F,
    CopiedSelUniform.runClassUpdateUniformCoverage P hV,
    ⟨CbudN, hbudCN⟩,
    runResidueUpdateCoverage P hV,
    CopiedBoundedGateBand.bandedUpdateActivationCompleteness P hV,
    hCoreBoundary⟩

/-- Arity-1 supplier for `BridgeUpdateZeroSupplierBundle`. -/
theorem bridgeUpdateZeroSupplierBundle_of_arity_one
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity1 : ∀ c, P.toPoly.arity c = 1) :
    BridgeUpdateZeroSupplierBundle P hV := by
  obtain ⟨CbudN, hbudCN⟩ := CopiedTie2b.arity_one_hbud P harity1
  exact bridgeUpdateZeroSupplierBundle_of_coordChoice P hV
    (fun c => ⟨0, by have := harity1 c; omega⟩)
    CbudN hbudCN
    (coreBoundaryUpdateCoverage_of_coreBoundaryCoverage_of_tupleFiberScalarization P hV
      (coreBoundaryCoverage_of_tupleFiberScalarization P hV
        (tupleFiberScalarization_of_arity_one P harity1))
      (tupleFiberScalarization_of_arity_one P harity1))

/-- Bounded bulk-cell keys used in the finite row-index bridge. -/
def S1Key (P : WRP.Presentation Step Step) (B q_U q_D : ℕ) :=
  Σ c' : Fin P.toPoly.K,
    (CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity c') q_U q_D :
      Finset (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B))

/-- Bounded frozen-cell keys used in the finite row-index bridge. -/
def F2Key (P : WRP.Presentation Step Step) (Bh q_U q_D : ℕ) :=
  Σ c' : Fin P.toPoly.K,
    (CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity c') q_U q_D :
      Finset (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh))

noncomputable instance s1KeyFintype (P : WRP.Presentation Step Step) (B q_U q_D : ℕ) :
    Fintype (S1Key P B q_U q_D) := by
  dsimp [S1Key]
  infer_instance

noncomputable instance f2KeyFintype (P : WRP.Presentation Step Step) (Bh q_U q_D : ℕ) :
    Fintype (F2Key P Bh q_U q_D) := by
  dsimp [F2Key]
  infer_instance

noncomputable instance s1KeyDecidableEq (P : WRP.Presentation Step Step) (B q_U q_D : ℕ) :
    DecidableEq (S1Key P B q_U q_D) := by
  classical
  dsimp [S1Key]
  infer_instance

noncomputable instance f2KeyDecidableEq (P : WRP.Presentation Step Step) (Bh q_U q_D : ℕ) :
    DecidableEq (F2Key P Bh q_U q_D) := by
  classical
  dsimp [F2Key]
  infer_instance

/-- Finite row data for the budgeted bridge.  For each `n % pG` class it stores:
bounded bulk/frozen selector emitters, suffix/prefix run activation residues, and
deep suffix/prefix offsets.  The unpacking functions below turn these bounded
`Fin` tables back into the `Finset ℕ` inputs expected by the DFA gate. -/
abbrev BridgeRowIndex (P : WRP.Presentation Step Step)
    (B Bh M pG q_U q_D Q : ℕ) (Ndeep : Fin P.toPoly.K → ℕ) :=
  (Fin pG → S1Key P B q_U q_D → Finset (Fin M)) ×
  (Fin pG → F2Key P Bh q_U q_D → Finset (Fin (2 * Bh + 2))) ×
  (Fin pG → (c' : Fin P.toPoly.K) → Finset (Fin Q)) ×
  (Fin pG → (c' : Fin P.toPoly.K) → Finset (Fin Q)) ×
  (Fin pG → (c' : Fin P.toPoly.K) → Finset (Fin (Ndeep c' + 3))) ×
  (Fin pG → (c' : Fin P.toPoly.K) → Finset (Fin (Ndeep c' + 3)))

noncomputable instance bridgeRowIndexFintype (P : WRP.Presentation Step Step)
    (B Bh M pG q_U q_D Q : ℕ) (Ndeep : Fin P.toPoly.K → ℕ) :
    Fintype (BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep) := by
  dsimp [BridgeRowIndex]
  infer_instance

noncomputable instance bridgeRowIndexDecidableEq (P : WRP.Presentation Step Step)
    (B Bh M pG q_U q_D Q : ℕ) (Ndeep : Fin P.toPoly.K → ℕ) :
    DecidableEq (BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep) := by
  classical
  dsimp [BridgeRowIndex]
  infer_instance

def rowClass {pG : ℕ} (hpG : 1 ≤ pG) (rN : ℕ) : Fin pG :=
  ⟨rN % pG, Nat.mod_lt rN hpG⟩

/-- Canonical representative of each row class above a chosen floor. -/
def rowRep (pG Nfloor : ℕ) : Fin pG → ℕ :=
  fun r => r.1 + pG * Nfloor

theorem rowRep_modEq {pG Nfloor : ℕ} (r : Fin pG) :
    Nat.ModEq pG (rowRep pG Nfloor r) r.1 := by
  dsimp [rowRep]
  have h := (Nat.mod_modEq (r.1 + pG * Nfloor) pG)
  rw [Nat.add_mul_mod_self_left] at h
  rw [Nat.mod_eq_of_lt r.2] at h
  exact h.symm

theorem rowRep_ge_floor {pG Nfloor : ℕ} (hpG : 1 ≤ pG) (r : Fin pG) :
    Nfloor ≤ rowRep pG Nfloor r := by
  dsimp [rowRep]
  have hmul : Nfloor ≤ pG * Nfloor := by
    simpa [one_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_right Nfloor hpG
  omega

theorem rowClass_mod_of_dvd {pG q : ℕ} (hpG : 1 ≤ pG) (hdvd : q ∣ pG)
    (n : ℕ) :
    (rowClass hpG (n % pG)).1 % q = n % q := by
  dsimp [rowClass]
  rw [Nat.mod_mod]
  exact Nat.ModEq.of_dvd hdvd (Nat.mod_modEq n pG : Nat.ModEq pG (n % pG) n)

theorem repN_rowClass_mod_of_dvd {pG q : ℕ} (hpG : 1 ≤ pG) (hdvd : q ∣ pG)
    {repN : Fin pG → ℕ}
    (hrep : ∀ r : Fin pG, Nat.ModEq pG (repN r) r.1) (n : ℕ) :
    repN (rowClass hpG (n % pG)) % q = n % q := by
  trans (rowClass hpG (n % pG)).1 % q
  · exact Nat.ModEq.of_dvd hdvd (hrep (rowClass hpG (n % pG)))
  · exact rowClass_mod_of_dvd hpG hdvd n

theorem updateSuffixShift_rowClass_mod_of_dvd {pG Q : ℕ} (hpG : 1 ≤ pG)
    (hQdvd : Q ∣ pG) {repN : Fin pG → ℕ}
    (hrep : ∀ r : Fin pG, Nat.ModEq pG (repN r) r.1)
    (mS n T : ℕ) :
    (mS + 2 * n + 1 + T) % Q =
      (mS + 2 * repN (rowClass hpG (n % pG)) + 1 + T) % Q := by
  change (mS + 2 * n + 1 + T) ≡
    (mS + 2 * repN (rowClass hpG (n % pG)) + 1 + T) [MOD Q]
  have hnrep : n ≡ repN (rowClass hpG (n % pG)) [MOD Q] :=
    (repN_rowClass_mod_of_dvd hpG hQdvd hrep n).symm
  exact (((Nat.ModEq.rfl.add (hnrep.mul_left 2)).add Nat.ModEq.rfl).add Nat.ModEq.rfl)

theorem bridgeGlobalPeriod_five
    (pSel pN pDomN pDpN Q : ℕ)
    (hpSel : 1 ≤ pSel) (hpN : 1 ≤ pN)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN) (hQ : 1 ≤ Q) :
    ∃ pG : ℕ, 1 ≤ pG ∧ pSel ∣ pG ∧ pN ∣ pG ∧ pDomN ∣ pG ∧ pDpN ∣ pG ∧ Q ∣ pG := by
  set pG : ℕ := (((pSel * pN) * pDomN) * pDpN) * Q with hpGdef
  refine ⟨pG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpGdef]
    exact Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hpSel)
            (Nat.lt_of_lt_of_le Nat.zero_lt_one hpN))
          (Nat.lt_of_lt_of_le Nat.zero_lt_one hpDomN))
        (Nat.lt_of_lt_of_le Nat.zero_lt_one hpDpN))
      (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ)
  · rw [hpGdef]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (dvd_mul_right pSel pN) pDomN) pDpN) Q
  · rw [hpGdef]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (dvd_mul_left pN pSel) pDomN) pDpN) Q
  · rw [hpGdef]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left pDomN (pSel * pN)) pDpN) Q
  · rw [hpGdef]
    exact dvd_mul_of_dvd_left (dvd_mul_left pDpN ((pSel * pN) * pDomN)) Q
  · rw [hpGdef]
    exact dvd_mul_left Q (((pSel * pN) * pDomN) * pDpN)

/-- Transport the copied-slice domain and D-present guard from the actual
column `n` to the row representative selected by `rowClass`. -/
theorem domDp_rowClass_rep_of_actual
    (P : WRP.Presentation Step Step)
    {pG pDomN pDpN NDomN NDpN mS n : ℕ} (hpG : 1 ≤ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    {repN : Fin pG → ℕ}
    (hrep : ∀ r : Fin pG, Nat.ModEq pG (repN r) r.1)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hm : 1 ≤ mS)
    (hDom_n : NDomN ≤ n)
    (hDom_rep : NDomN ≤ repN (rowClass hpG (n % pG)))
    (hDp_n : NDpN ≤ n)
    (hDp_rep : NDpN ≤ repN (rowClass hpG (n % pG)))
    (hG : CopiedAchSetFold.domDp P mS n) :
    CopiedAchSetFold.domDp P mS (repN (rowClass hpG (n % pG))) := by
  constructor
  · have hmod : n % pDomN = repN (rowClass hpG (n % pG)) % pDomN :=
      (repN_rowClass_mod_of_dvd hpG hpDomN_dvd hrep n).symm
    exact (SliceFasSelector.iff_on_class
      (Pr := fun x => P.toPoly.domain (copiedSlice mS x))
      hpDomN (hDomN mS hm) hDom_n hDom_rep hmod).mp hG.1
  · have hmod : n % pDpN = repN (rowClass hpG (n % pG)) % pDpN :=
      (repN_rowClass_mod_of_dvd hpG hpDpN_dvd hrep n).symm
    exact (SliceFasSelector.iff_on_class
      (Pr := fun x => ∃ a, P.toPoly.selectedAtom (copiedSlice mS x) a ∧
        P.toPoly.labelOf (copiedSlice mS x) a = D)
      hpDpN (hDpN mS hm) hDp_n hDp_rep hmod).mp hG.2

def rowS1 {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) : Finset ℕ :=
  if h : rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity c') q_U q_D then
    finVals (idx.1 (rowClass hpG rN) ⟨c', ⟨rs, h⟩⟩)
  else ∅

def rowF2 {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) : Finset ℕ :=
  if h : rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity c') q_U q_D then
    finVals (idx.2.1 (rowClass hpG rN) ⟨c', ⟨rs, h⟩⟩)
  else ∅

def rowSsuf {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep) (rN : ℕ)
    (c' : Fin P.toPoly.K) : Finset ℕ :=
  finVals (idx.2.2.1 (rowClass hpG rN) c')

def rowSpre {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep) (rN : ℕ)
    (c' : Fin P.toPoly.K) : Finset ℕ :=
  finVals (idx.2.2.2.1 (rowClass hpG rN) c')

def rowDsuf {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep) (rN : ℕ)
    (c' : Fin P.toPoly.K) : Finset ℕ :=
  finVals (idx.2.2.2.2.1 (rowClass hpG rN) c')

def rowDpre {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep) (rN : ℕ)
    (c' : Fin P.toPoly.K) : Finset ℕ :=
  finVals (idx.2.2.2.2.2 (rowClass hpG rN) c')

/-- Totalized bulk emitters for arbitrary row indices: bad parity entries are ignored. -/
def rowS1Odd {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) : Finset ℕ :=
  (rowS1 hpG idx rN c' rs).filter (fun r => r % 2 = 1)

/-- Totalized frozen emitters for arbitrary row indices: bad parity entries are ignored. -/
def rowF2Odd {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) : Finset ℕ :=
  (rowF2 hpG idx rN c' rs).filter (fun r => r % 2 = 1)

/-- Update-shaped suffix run-residue row table for a representative `n` in
each row class.  This is the row-index version of
`CopiedBoundedGateBand.updateSufAbsTieSet`. -/
noncomputable def updateSsufRowTable
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG : ℕ}
    (pcF Ts : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ) (Q : ℕ) :
    Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ :=
  fun r c' =>
    CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c') (fun _ => 0)
      mS (repN r) (pcF c') (Ts c') Q

/-- Prefix twin of `updateSsufRowTable`. -/
noncomputable def updateSpreRowTable
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG : ℕ}
    (pcF Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ) (Q : ℕ) :
    Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ :=
  fun r c' =>
    CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c') (fun _ => 0)
      mS (repN r) (pcF c') (Tp c') Q

/-- Deep-suffix row table for genuine update-tuple deep clauses: the
representative rank is measured on the tuple with only the distinguished
coordinate moved into the deep suffix position. -/
noncomputable def updateDeepDsufRowTable
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG B : ℕ}
    (Ndeep : Fin P.toPoly.K → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ) :
    Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ :=
  fun r c' =>
    (Finset.range (Ndeep c')).filter (fun k =>
      P.rank c' (copiedSlice mS (repN r))
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mixedPosAt
              (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
              mS (B + 1) (repN r)))
        = CopiedDstar.dstarRankGA_m P hV mS (repN r))

/-- Deep-prefix twin of `updateDeepDsufRowTable`.  The stored gate offset is
shifted by `+3`, matching `updateDeepPreOrdClauseAt`. -/
noncomputable def updateDeepDpreRowTable
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG B : ℕ}
    (Ndeep : Fin P.toPoly.K → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ) :
    Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ :=
  fun r c' =>
    ((Finset.range (Ndeep c')).filter (fun k =>
      P.rank c' (copiedSlice mS (repN r))
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mixedPosAt
              (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
              mS (B + 1) (repN r)))
        = CopiedDstar.dstarRankGA_m P hV mS (repN r))).image (fun k => k + 3)

theorem mem_updateSsufRowTable
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG : ℕ}
    (pcF Ts : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ) (Q : ℕ)
    (r : Fin pG) (c' : Fin P.toPoly.K) (ρ : ℕ) :
    ρ ∈ updateSsufRowTable P hV pcF Ts j0F mS repN Q r c' ↔
      ρ < Q ∧
        ((ρ + Q - ((mS + 2 * repN r + 1 + Ts c') % Q)) % pcF c') ∈
          CopiedBoundedGateBand.updateSufTieSet P hV c' (j0F c') (fun _ => 0)
            mS (repN r) (pcF c') (Ts c') := by
  simpa [updateSsufRowTable] using
    CopiedBoundedGateBand.mem_updateSufAbsTieSet P hV c' (j0F c') (fun _ => 0)
      mS (repN r) (pcF c') (Ts c') Q ρ

theorem mem_updateSpreRowTable
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG : ℕ}
    (pcF Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ) (Q : ℕ)
    (r : Fin pG) (c' : Fin P.toPoly.K) (ρ : ℕ) :
    ρ ∈ updateSpreRowTable P hV pcF Tp j0F mS repN Q r c' ↔
      ρ < Q ∧
        ((ρ + Q - ((Tp c') % Q)) % pcF c') ∈
          CopiedBoundedGateBand.updatePreTieSet P hV c' (j0F c') (fun _ => 0)
            mS (repN r) (pcF c') (Tp c') := by
  simpa [updateSpreRowTable] using
    CopiedBoundedGateBand.mem_updatePreAbsTieSet P hV c' (j0F c') (fun _ => 0)
      mS (repN r) (pcF c') (Tp c') Q ρ

theorem updateSsufRowTable_mem_lt
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG : ℕ}
    (pcF Ts : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ) (Q : ℕ)
    {r : Fin pG} {c' : Fin P.toPoly.K} {ρ : ℕ}
    (hρ : ρ ∈ updateSsufRowTable P hV pcF Ts j0F mS repN Q r c') :
    ρ < Q :=
  (mem_updateSsufRowTable P hV pcF Ts j0F mS repN Q r c' ρ).mp hρ |>.1

theorem updateSpreRowTable_mem_lt
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG : ℕ}
    (pcF Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ) (Q : ℕ)
    {r : Fin pG} {c' : Fin P.toPoly.K} {ρ : ℕ}
    (hρ : ρ ∈ updateSpreRowTable P hV pcF Tp j0F mS repN Q r c') :
    ρ < Q :=
  (mem_updateSpreRowTable P hV pcF Tp j0F mS repN Q r c' ρ).mp hρ |>.1

theorem updateDeepDsufRowTable_mem_lt
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG B : ℕ}
    (Ndeep : Fin P.toPoly.K → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    {r : Fin pG} {c' : Fin P.toPoly.K} {k : ℕ}
    (hk : k ∈ updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS repN r c') :
    k < Ndeep c' + 3 := by
  rw [updateDeepDsufRowTable] at hk
  have hkN : k < Ndeep c' := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  omega

theorem updateDeepDpreRowTable_mem_lt
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG B : ℕ}
    (Ndeep : Fin P.toPoly.K → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    {r : Fin pG} {c' : Fin P.toPoly.K} {k : ℕ}
    (hk : k ∈ updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS repN r c') :
    k < Ndeep c' + 3 := by
  rw [updateDeepDpreRowTable] at hk
  obtain ⟨k0, hk0, rfl⟩ := Finset.mem_image.mp hk
  have hk0N : k0 < Ndeep c' := Finset.mem_range.mp (Finset.mem_filter.mp hk0).1
  omega

/-- Budgeted fixed-period n-fold for the zero-base update absolute suffix and
prefix residue tables.  This is the row-table-facing wrapper around
`CopiedAchSetFold.updateZero_achievesDstar_iff_on_n_class_of_budget` plus the
two-representative update folds. -/
theorem updateAbsTieSet_zero_fold_n_actual_fixed_period_of_budget
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (Cbud : ℕ)
    (hbudC : ∀ (mS : ℕ), 1 ≤ mS →
      ∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ Cbud * (mS + n + 1)) :
    ∃ (p0 : ℕ), 1 ≤ p0 ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (Ts pcF mS Q : ℕ), 1 ≤ mS → Ts + 2 * pcF ≤ mS - 1 →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
          (mS + 2 * n + 1 + Ts) % Q = (mS + 2 * n' + 1 + Ts) % Q →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          CopiedBoundedGateBand.updateSufAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n pcF Ts Q =
            CopiedBoundedGateBand.updateSufAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n' pcF Ts Q) ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (Tp pcF mS Q : ℕ), 1 ≤ mS → Tp + 2 * pcF ≤ mS - 1 →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          CopiedBoundedGateBand.updatePreAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n pcF Tp Q =
            CopiedBoundedGateBand.updatePreAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n' pcF Tp Q) := by
  obtain ⟨p0, hp0, hsuf, hpre⟩ :=
    CopiedAchSetFold.updateZero_achievesDstar_iff_on_n_class_of_budget
      P hV Cbud hbudC
  refine ⟨p0, hp0, ?_, ?_⟩
  · intro c' j0 Ts pcF mS Q hm hmval
    obtain ⟨N, hN⟩ :=
      CopiedAchSetFold.tyingSuf2_update_zero_fold_n_actual_fixed_period
        P hV p0 hsuf c' j0 Ts pcF mS hm hmval
    refine ⟨N, fun n n' hn hn' hmod hshift hG hG' => ?_⟩
    have hlocal := hN n n' hn hn' hmod hG hG'
    have hset :
        CopiedBoundedGateBand.updateSufTieSet P hV c' j0
            (fun _ : Fin (P.toPoly.arity c') => 0) mS n pcF Ts =
          CopiedBoundedGateBand.updateSufTieSet P hV c' j0
            (fun _ : Fin (P.toPoly.arity c') => 0) mS n' pcF Ts := by
      simpa [CopiedBoundedGateBand.updateSufTieSet] using hlocal
    exact CopiedBoundedGateBand.updateSufAbsTieSet_eq_of_tieSet_eq
      P hV c' j0 (fun _ : Fin (P.toPoly.arity c') => 0)
      mS n n' pcF Ts Q hshift hset
  · intro c' j0 Tp pcF mS Q hm hmval
    obtain ⟨N, hN⟩ :=
      CopiedAchSetFold.tyingPre2_update_zero_fold_n_actual_fixed_period
        P hV p0 hpre c' j0 Tp pcF mS hm hmval
    refine ⟨N, fun n n' hn hn' hmod hG hG' => ?_⟩
    have hlocal := hN n n' hn hn' hmod hG hG'
    have hset :
        CopiedBoundedGateBand.updatePreTieSet P hV c' j0
            (fun _ : Fin (P.toPoly.arity c') => 0) mS n pcF Tp =
          CopiedBoundedGateBand.updatePreTieSet P hV c' j0
            (fun _ : Fin (P.toPoly.arity c') => 0) mS n' pcF Tp := by
      simpa [CopiedBoundedGateBand.updatePreTieSet] using hlocal
    exact CopiedBoundedGateBand.updatePreAbsTieSet_eq_of_tieSet_eq
      P hV c' j0 (fun _ : Fin (P.toPoly.arity c') => 0)
      mS n n' pcF Tp Q hset

/-- Budgeted fixed-period n-fold for the zero-base update deep suffix/prefix
offset tables.  This is the deep analogue of
`updateAbsTieSet_zero_fold_n_actual_fixed_period_of_budget`: the finite filter
over offsets is folded from the single-coordinate update-zero transport. -/
theorem updateDeepRows_zero_fold_n_actual_fixed_period_of_budget
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (Cbud : ℕ)
    (hbudC : ∀ (mS : ℕ), 1 ≤ mS →
      ∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ Cbud * (mS + n + 1)) :
    ∃ (p0 : ℕ), 1 ≤ p0 ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (B mS NdeepC : ℕ), 1 ≤ mS → NdeepC + 2 ≤ mS →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' →
          B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
          n % p0 = n' % p0 →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n)
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n))
                = CopiedDstar.dstarRankGA_m P hV mS n)
            =
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n')
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n'))
                = CopiedDstar.dstarRankGA_m P hV mS n')) ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (B mS NdeepC : ℕ), 1 ≤ mS → NdeepC + 2 ≤ mS →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' →
          B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
          n % p0 = n' % p0 →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n)
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n))
                = CopiedDstar.dstarRankGA_m P hV mS n)
            =
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n')
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n'))
                = CopiedDstar.dstarRankGA_m P hV mS n')) := by
  classical
  obtain ⟨p0, hp0, hsuf, hpre⟩ :=
    CopiedAchSetFold.updateZero_achievesDstar_iff_on_n_class_of_budget
      P hV Cbud hbudC
  refine ⟨p0, hp0, ?_, ?_⟩
  · intro c' j0 B mS NdeepC hm hNdeep
    have key : ∀ k, ∃ N, k < NdeepC → ∀ n n', N ≤ n → N ≤ n' →
        n % p0 = n' % p0 → CopiedAchSetFold.domDp P mS n →
        CopiedAchSetFold.domDp P mS n' →
        ((P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n) ↔
          (P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n')) := by
      intro k
      by_cases hk : k < NdeepC
      · let q := mS - 1 - (k + 1)
        have hq : q < mS - 1 := by
          dsimp [q]
          omega
        obtain ⟨N, hN⟩ := hsuf c' j0 mS q hm hq
        refine ⟨N, fun _ n n' hn hn' hmod hG hG' => ?_⟩
        have hstep := hN n n' hn hn' hmod hG hG'
        simpa [mixedPosAt, q] using hstep
      · exact ⟨0, fun h => absurd h hk⟩
    choose Nf hNf using key
    refine ⟨(Finset.range NdeepC).sup Nf, fun n n' hn hn' _hB _hB' hmod hG hG' => ?_⟩
    apply Finset.filter_congr
    intro k hk
    exact hNf k (Finset.mem_range.mp hk) n n'
      (le_trans (Finset.le_sup hk) hn) (le_trans (Finset.le_sup hk) hn')
      hmod hG hG'
  · intro c' j0 B mS NdeepC hm hNdeep
    have key : ∀ k, ∃ N, k < NdeepC → ∀ n n', N ≤ n → N ≤ n' →
        n % p0 = n' % p0 → CopiedAchSetFold.domDp P mS n →
        CopiedAchSetFold.domDp P mS n' →
        ((P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n) ↔
          (P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n')) := by
      intro k
      by_cases hk : k < NdeepC
      · let q := mS - 1 - (k + 1)
        have hq : q < mS - 1 := by
          dsimp [q]
          omega
        obtain ⟨N, hN⟩ := hpre c' j0 mS q hm hq
        refine ⟨N, fun _ n n' hn hn' hmod hG hG' => ?_⟩
        have hstep := hN n n' hn hn' hmod hG hG'
        simpa [mixedPosAt, q] using hstep
      · exact ⟨0, fun h => absurd h hk⟩
    choose Nf hNf using key
    refine ⟨(Finset.range NdeepC).sup Nf, fun n n' hn hn' _hB _hB' hmod hG hG' => ?_⟩
    apply Finset.filter_congr
    intro k hk
    exact hNf k (Finset.mem_range.mp hk) n n'
      (le_trans (Finset.le_sup hk) hn) (le_trans (Finset.le_sup hk) hn')
      hmod hG hG'

/-- Bundle the n-period suppliers needed by the direct update bridge:
zero-base update suffix/prefix row-table folds, copied-slice domain, and
D-present.  The eventual bridge adds selector and residue-table periods on top
of these. -/
theorem updateBridgePeriodSuppliers_of_budget
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (Cbud : ℕ)
    (hbudC : ∀ (mS : ℕ), 1 ≤ mS →
      ∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ Cbud * (mS + n + 1)) :
    ∃ (p0 NDomN pDomN NDpN pDpN : ℕ),
      1 ≤ p0 ∧ 1 ≤ pDomN ∧ 1 ≤ pDpN ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (Ts pcF mS Q : ℕ), 1 ≤ mS → Ts + 2 * pcF ≤ mS - 1 →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
          (mS + 2 * n + 1 + Ts) % Q = (mS + 2 * n' + 1 + Ts) % Q →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          CopiedBoundedGateBand.updateSufAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n pcF Ts Q =
            CopiedBoundedGateBand.updateSufAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n' pcF Ts Q) ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (Tp pcF mS Q : ℕ), 1 ≤ mS → Tp + 2 * pcF ≤ mS - 1 →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          CopiedBoundedGateBand.updatePreAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n pcF Tp Q =
            CopiedBoundedGateBand.updatePreAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n' pcF Tp Q) ∧
      (∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
        (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
         P.toPoly.domain (copiedSlice mS n))) ∧
      (∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
        ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
            ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
         (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
            ∧ P.toPoly.labelOf (copiedSlice mS n) a = D))) := by
  obtain ⟨p0, hp0, hsuf, hpre⟩ :=
    updateAbsTieSet_zero_fold_n_actual_fixed_period_of_budget P hV Cbud hbudC
  obtain ⟨NDomN, pDomN, hpDomN, hDomN⟩ := CopiedGates.domain_EP_fibred P
  obtain ⟨NDpN, pDpN, hpDpN, hDpN⟩ := CopiedGates.Dpresent_EP_fibred P
  exact ⟨p0, NDomN, pDomN, NDpN, pDpN, hp0, hpDomN, hpDpN,
    hsuf, hpre, hDomN, hDpN⟩

/-- Period suppliers for the fully update-shaped bridge.  This extends
`updateBridgePeriodSuppliers_of_budget` with the update-tuple deep suffix and
prefix folds, lifted to one common period. -/
theorem updateDeepBridgePeriodSuppliers_of_budget
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (Cbud : ℕ)
    (hbudC : ∀ (mS : ℕ), 1 ≤ mS →
      ∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ Cbud * (mS + n + 1)) :
    ∃ (p0 NDomN pDomN NDpN pDpN : ℕ),
      1 ≤ p0 ∧ 1 ≤ pDomN ∧ 1 ≤ pDpN ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (Ts pcF mS Q : ℕ), 1 ≤ mS → Ts + 2 * pcF ≤ mS - 1 →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
          (mS + 2 * n + 1 + Ts) % Q =
            (mS + 2 * n' + 1 + Ts) % Q →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          CopiedBoundedGateBand.updateSufAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n pcF Ts Q =
            CopiedBoundedGateBand.updateSufAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n' pcF Ts Q) ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (Tp pcF mS Q : ℕ), 1 ≤ mS → Tp + 2 * pcF ≤ mS - 1 →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          CopiedBoundedGateBand.updatePreAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n pcF Tp Q =
            CopiedBoundedGateBand.updatePreAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n' pcF Tp Q) ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (B mS NdeepC : ℕ), 1 ≤ mS → NdeepC + 2 ≤ mS →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' →
          B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
          n % p0 = n' % p0 →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n)
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n))
                = CopiedDstar.dstarRankGA_m P hV mS n)
            =
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n')
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n'))
                = CopiedDstar.dstarRankGA_m P hV mS n')) ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (B mS NdeepC : ℕ), 1 ≤ mS → NdeepC + 2 ≤ mS →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' →
          B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
          n % p0 = n' % p0 →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n)
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n))
                = CopiedDstar.dstarRankGA_m P hV mS n)
            =
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n')
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n'))
                = CopiedDstar.dstarRankGA_m P hV mS n')) ∧
      (∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
        (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
         P.toPoly.domain (copiedSlice mS n))) ∧
      (∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
        ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
            ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
         (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
            ∧ P.toPoly.labelOf (copiedSlice mS n) a = D))) := by
  obtain ⟨pAbs, NDomN, pDomN, NDpN, pDpN, hpAbs, hpDomN, hpDpN,
    hsuf, hpre, hDomN, hDpN⟩ :=
    updateBridgePeriodSuppliers_of_budget P hV Cbud hbudC
  obtain ⟨pDeep, hpDeep, hdsuf, hdpre⟩ :=
    updateDeepRows_zero_fold_n_actual_fixed_period_of_budget P hV Cbud hbudC
  let p0 := pAbs * pDeep
  have hp0 : 1 ≤ p0 := by
    dsimp [p0]
    exact Nat.mul_pos hpAbs hpDeep
  have hpAbs_dvd : pAbs ∣ p0 := by
    dsimp [p0]
    exact Nat.dvd_mul_right pAbs pDeep
  have hpDeep_dvd : pDeep ∣ p0 := by
    dsimp [p0]
    exact Nat.dvd_mul_left pDeep pAbs
  refine ⟨p0, NDomN, pDomN, NDpN, pDpN, hp0, hpDomN, hpDpN, ?_, ?_, ?_, ?_,
    hDomN, hDpN⟩
  · intro c' j0 Ts pcF mS Q hm hband
    obtain ⟨N, hN⟩ := hsuf c' j0 Ts pcF mS Q hm hband
    refine ⟨N, fun n n' hn hn' hmod hshift hG hG' => ?_⟩
    exact hN n n' hn hn' (Nat.ModEq.of_dvd hpAbs_dvd hmod) hshift hG hG'
  · intro c' j0 Tp pcF mS Q hm hband
    obtain ⟨N, hN⟩ := hpre c' j0 Tp pcF mS Q hm hband
    refine ⟨N, fun n n' hn hn' hmod hG hG' => ?_⟩
    exact hN n n' hn hn' (Nat.ModEq.of_dvd hpAbs_dvd hmod) hG hG'
  · intro c' j0 B mS NdeepC hm hdeep
    obtain ⟨N, hN⟩ := hdsuf c' j0 B mS NdeepC hm hdeep
    refine ⟨N, fun n n' hn hn' hB hB' hmod hG hG' => ?_⟩
    exact hN n n' hn hn' hB hB' (Nat.ModEq.of_dvd hpDeep_dvd hmod) hG hG'
  · intro c' j0 B mS NdeepC hm hdeep
    obtain ⟨N, hN⟩ := hdpre c' j0 B mS NdeepC hm hdeep
    refine ⟨N, fun n n' hn hn' hB hB' hmod hG hG' => ?_⟩
    exact hN n n' hn hn' hB hB' (Nat.ModEq.of_dvd hpDeep_dvd hmod) hG hG'

/-- Global row-period package for the fully update-shaped bridge. -/
def BridgeUpdateDeepGlobalPeriodSuppliers
    (P : WRP.Presentation Step Step) (hV : P.Valid) (pSel Q : ℕ) : Prop :=
    ∃ (p0 NDomN pDomN NDpN pDpN pG : ℕ),
      1 ≤ p0 ∧ 1 ≤ pDomN ∧ 1 ≤ pDpN ∧ 1 ≤ pG ∧
      pSel ∣ pG ∧ p0 ∣ pG ∧ pDomN ∣ pG ∧ pDpN ∣ pG ∧ Q ∣ pG ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (Ts pcF mS Q : ℕ), 1 ≤ mS → Ts + 2 * pcF ≤ mS - 1 →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
          (mS + 2 * n + 1 + Ts) % Q = (mS + 2 * n' + 1 + Ts) % Q →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          CopiedBoundedGateBand.updateSufAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n pcF Ts Q =
            CopiedBoundedGateBand.updateSufAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n' pcF Ts Q) ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (Tp pcF mS Q : ℕ), 1 ≤ mS → Tp + 2 * pcF ≤ mS - 1 →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          CopiedBoundedGateBand.updatePreAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n pcF Tp Q =
            CopiedBoundedGateBand.updatePreAbsTieSet P hV c' j0
              (fun _ : Fin (P.toPoly.arity c') => 0) mS n' pcF Tp Q) ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (B mS NdeepC : ℕ), 1 ≤ mS → NdeepC + 2 ≤ mS →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' →
          B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
          n % p0 = n' % p0 →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n)
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n))
                = CopiedDstar.dstarRankGA_m P hV mS n)
            =
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n')
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n'))
                = CopiedDstar.dstarRankGA_m P hV mS n')) ∧
      (∀ (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
          (B mS NdeepC : ℕ), 1 ≤ mS → NdeepC + 2 ≤ mS →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' →
          B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
          n % p0 = n' % p0 →
          CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n)
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n))
                = CopiedDstar.dstarRankGA_m P hV mS n)
            =
          (Finset.range NdeepC).filter (fun k =>
              P.rank c' (copiedSlice mS n')
                  (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                    (mixedPosAt
                      (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                      mS (B + 1) n'))
                = CopiedDstar.dstarRankGA_m P hV mS n')) ∧
      (∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
        (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
         P.toPoly.domain (copiedSlice mS n))) ∧
      (∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
        ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
            ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
         (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
            ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))

/-- Budgeted selected-atom growth supplies the fully update-shaped bridge's
global row-period package. -/
theorem bridgeUpdateDeepGlobalPeriodSuppliers_of_budget
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (Cbud : ℕ)
    (hbudC : ∀ (mS : ℕ), 1 ≤ mS →
      ∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ Cbud * (mS + n + 1))
    (pSel Q : ℕ) (hpSel : 1 ≤ pSel) (hQ : 1 ≤ Q) :
    BridgeUpdateDeepGlobalPeriodSuppliers P hV pSel Q := by
  obtain ⟨p0, NDomN, pDomN, NDpN, pDpN, hp0, hpDomN, hpDpN,
    hsuf, hpre, hdsuf, hdpre, hDomN, hDpN⟩ :=
    updateDeepBridgePeriodSuppliers_of_budget P hV Cbud hbudC
  obtain ⟨pG, hpG, hpSel_dvd, hp0_dvd, hpDomN_dvd, hpDpN_dvd, hQ_dvd⟩ :=
    bridgeGlobalPeriod_five pSel p0 pDomN pDpN Q hpSel hp0 hpDomN hpDpN hQ
  exact ⟨p0, NDomN, pDomN, NDpN, pDpN, pG,
    hp0, hpDomN, hpDpN, hpG,
    hpSel_dvd, hp0_dvd, hpDomN_dvd, hpDpN_dvd, hQ_dvd,
    hsuf, hpre, hdsuf, hdpre, hDomN, hDpN⟩

/-- Explicit-threshold row-class specialization of a zero-base suffix absolute
table n-fold.  This version avoids choosing a fresh existential threshold after
`repN` has been fixed, which is useful when the bridge representative floor
must already dominate all table-fold thresholds. -/
theorem updateSsufRowTable_eq_of_zero_fold_n_actual_rowClass_at
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG p0 Q : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hQdvd : Q ∣ pG)
    {repN : Fin pG → ℕ}
    (hrep : ∀ r : Fin pG, Nat.ModEq pG (repN r) r.1)
    (pcF Ts : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q) :
    ∀ n, N ≤ n → N ≤ repN (rowClass hpG (n % pG)) →
      CopiedAchSetFold.domDp P mS n →
      CopiedAchSetFold.domDp P mS (repN (rowClass hpG (n % pG))) →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        updateSsufRowTable P hV pcF Ts j0F mS repN Q (rowClass hpG (n % pG)) c' := by
  intro n hn hrepN hG hGrep
  let rcls : Fin pG := rowClass hpG (n % pG)
  have hmod : n % p0 = repN rcls % p0 := by
    exact (repN_rowClass_mod_of_dvd hpG hp0dvd hrep n).symm
  have hshift :
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * repN rcls + 1 + Ts c') % Q := by
    simpa [rcls] using updateSuffixShift_rowClass_mod_of_dvd hpG hQdvd hrep mS n (Ts c')
  have hAbs := hN n (repN rcls) hn hrepN hmod hshift hG hGrep
  simpa [rcls, updateSsufRowTable] using hAbs

/-- Prefix twin of
`updateSsufRowTable_eq_of_zero_fold_n_actual_rowClass_at`. -/
theorem updateSpreRowTable_eq_of_zero_fold_n_actual_rowClass_at
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG p0 Q : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    {repN : Fin pG → ℕ}
    (hrep : ∀ r : Fin pG, Nat.ModEq pG (repN r) r.1)
    (pcF Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q) :
    ∀ n, N ≤ n → N ≤ repN (rowClass hpG (n % pG)) →
      CopiedAchSetFold.domDp P mS n →
      CopiedAchSetFold.domDp P mS (repN (rowClass hpG (n % pG))) →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        updateSpreRowTable P hV pcF Tp j0F mS repN Q (rowClass hpG (n % pG)) c' := by
  intro n hn hrepN hG hGrep
  let rcls : Fin pG := rowClass hpG (n % pG)
  have hmod : n % p0 = repN rcls % p0 := by
    exact (repN_rowClass_mod_of_dvd hpG hp0dvd hrep n).symm
  have hAbs := hN n (repN rcls) hn hrepN hmod hG hGrep
  simpa [rcls, updateSpreRowTable] using hAbs

/-- Domain/D-present transport to the canonical `rowRep` representative from a
single global floor dominating both copied-slice guard thresholds. -/
theorem domDp_rowClass_rowRep_of_actual_of_floor
    (P : WRP.Presentation Step Step)
    {pG pDomN pDpN NDomN NDpN Nfloor mS n : ℕ}
    (hpG : 1 ≤ pG) (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hm : 1 ≤ mS)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n) :
    CopiedAchSetFold.domDp P mS (rowRep pG Nfloor (rowClass hpG (n % pG))) := by
  exact domDp_rowClass_rep_of_actual P hpG hpDomN hpDpN hpDomN_dvd hpDpN_dvd
    (fun r : Fin pG => rowRep_modEq r)
    hDomN hDpN hm
    (le_trans hNDom_floor hn_floor)
    (le_trans hNDom_floor (rowRep_ge_floor hpG (rowClass hpG (n % pG))))
    (le_trans hNDp_floor hn_floor)
    (le_trans hNDp_floor (rowRep_ge_floor hpG (rowClass hpG (n % pG))))
    hG

/-- Suffix absolute-table row transport for canonical `rowRep`, with all
threshold obligations discharged from one global floor. -/
theorem updateSsufRowTable_eq_of_zero_fold_n_actual_rowClass_rowRep_of_floor
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG p0 pDomN pDpN Q : ℕ}
    {NDomN NDpN Nfloor mS n : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hQdvd : Q ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hm : 1 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n) :
    CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
        (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
      updateSsufRowTable P hV pcF Ts j0F mS (rowRep pG Nfloor) Q
        (rowClass hpG (n % pG)) c' := by
  have hGrep :
      CopiedAchSetFold.domDp P mS (rowRep pG Nfloor (rowClass hpG (n % pG))) :=
    domDp_rowClass_rowRep_of_actual_of_floor P hpG hpDomN hpDpN hpDomN_dvd hpDpN_dvd
      hDomN hDpN hm hNDom_floor hNDp_floor hn_floor hG
  exact updateSsufRowTable_eq_of_zero_fold_n_actual_rowClass_at P hV hpG hp0dvd hQdvd
    (fun r : Fin pG => rowRep_modEq r) pcF Ts j0F mS c' N hN n
    (le_trans hN_floor hn_floor)
    (le_trans hN_floor (rowRep_ge_floor hpG (rowClass hpG (n % pG))))
    hG hGrep

/-- Prefix twin of
`updateSsufRowTable_eq_of_zero_fold_n_actual_rowClass_rowRep_of_floor`. -/
theorem updateSpreRowTable_eq_of_zero_fold_n_actual_rowClass_rowRep_of_floor
    (P : WRP.Presentation Step Step) (hV : P.Valid) {pG p0 pDomN pDpN Q : ℕ}
    {NDomN NDpN Nfloor mS n : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hm : 1 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n) :
    CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
        (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
      updateSpreRowTable P hV pcF Tp j0F mS (rowRep pG Nfloor) Q
        (rowClass hpG (n % pG)) c' := by
  have hGrep :
      CopiedAchSetFold.domDp P mS (rowRep pG Nfloor (rowClass hpG (n % pG))) :=
    domDp_rowClass_rowRep_of_actual_of_floor P hpG hpDomN hpDpN hpDomN_dvd hpDpN_dvd
      hDomN hDpN hm hNDom_floor hNDp_floor hn_floor hG
  exact updateSpreRowTable_eq_of_zero_fold_n_actual_rowClass_at P hV hpG hp0dvd
    (fun r : Fin pG => rowRep_modEq r) pcF Tp j0F mS c' N hN n
    (le_trans hN_floor hn_floor)
    (le_trans hN_floor (rowRep_ge_floor hpG (rowClass hpG (n % pG))))
    hG hGrep

theorem rowS1_mem_lt {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) {x : ℕ}
    (hx : x ∈ rowS1 hpG idx rN c' rs) : x < M := by
  rw [rowS1] at hx
  split at hx
  · exact mem_finVals_lt hx
  · exact absurd hx (Finset.notMem_empty x)

theorem rowSsuf_mem_lt {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep)
    (rN : ℕ) (c' : Fin P.toPoly.K) {x : ℕ}
    (hx : x ∈ rowSsuf hpG idx rN c') : x < Q :=
  mem_finVals_lt hx

theorem rowSpre_mem_lt {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep)
    (rN : ℕ) (c' : Fin P.toPoly.K) {x : ℕ}
    (hx : x ∈ rowSpre hpG idx rN c') : x < Q :=
  mem_finVals_lt hx

/-- Pack ordinary natural-valued row tables into the finite row-index universe. -/
def mkBridgeRowIndex {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ}
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hSsuf : ∀ r c' x, x ∈ Ssuf r c' → x < Q)
    (hSpre : ∀ r c' x, x ∈ Spre r c' → x < Q)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3) :
    BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep :=
  (fun r key => finPack (S1 r key) (hS1 r key),
   fun r key => finPack (F2 r key) (hF2 r key),
   fun r c' => finPack (Ssuf r c') (hSsuf r c'),
   fun r c' => finPack (Spre r c') (hSpre r c'),
   fun r c' => finPack (Dsuf r c') (hDsuf r c'),
   fun r c' => finPack (Dpre r c') (hDpre r c'))

/-- Pack row data using update-shaped suffix/prefix run-residue tables and
ordinary core/deep row tables. -/
noncomputable def mkBridgeUpdateRowIndex
    {P : WRP.Presentation Step Step} (hV : P.Valid)
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3) :
    BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep :=
  mkBridgeRowIndex S1 F2
    (updateSsufRowTable P hV pcF Ts j0F mS repN Q)
    (updateSpreRowTable P hV pcF Tp j0F mS repN Q)
    Dsuf Dpre hS1 hF2
    (fun _ _ _ hx => updateSsufRowTable_mem_lt P hV pcF Ts j0F mS repN Q hx)
    (fun _ _ _ hx => updateSpreRowTable_mem_lt P hV pcF Tp j0F mS repN Q hx)
    hDsuf hDpre

theorem rowS1_mkBridgeRowIndex {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hSsuf : ∀ r c' x, x ∈ Ssuf r c' → x < Q)
    (hSpre : ∀ r c' x, x ∈ Spre r c' → x < Q)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B)
    (hmem : rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity c') q_U q_D) :
    rowS1 hpG
        (mkBridgeRowIndex (M := M) (Q := Q) (Ndeep := Ndeep) S1 F2 Ssuf Spre Dsuf Dpre
          hS1 hF2 hSsuf hSpre hDsuf hDpre) rN c' rs
      = S1 (rowClass hpG rN) ⟨c', ⟨rs, hmem⟩⟩ := by
  simp [rowS1, mkBridgeRowIndex, hmem, finVals_finPack]

theorem rowS1_mkBridgeRowIndex_notMem {P : WRP.Presentation Step Step}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hSsuf : ∀ r c' x, x ∈ Ssuf r c' → x < Q)
    (hSpre : ∀ r c' x, x ∈ Spre r c' → x < Q)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B)
    (hmem : rs ∉ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity c') q_U q_D) :
    rowS1 hpG
        (mkBridgeRowIndex (M := M) (Q := Q) (Ndeep := Ndeep) S1 F2 Ssuf Spre Dsuf Dpre
          hS1 hF2 hSsuf hSpre hDsuf hDpre) rN c' rs = ∅ := by
  simp [rowS1, hmem]

theorem rowF2_mkBridgeRowIndex {P : WRP.Presentation Step Step} {B Bh M pG q_U q_D Q : ℕ}
    {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hSsuf : ∀ r c' x, x ∈ Ssuf r c' → x < Q)
    (hSpre : ∀ r c' x, x ∈ Spre r c' → x < Q)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh)
    (hmem : rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity c') q_U q_D) :
    rowF2 hpG
        (mkBridgeRowIndex (M := M) (Q := Q) (Ndeep := Ndeep) S1 F2 Ssuf Spre Dsuf Dpre
          hS1 hF2 hSsuf hSpre hDsuf hDpre) rN c' rs
      = F2 (rowClass hpG rN) ⟨c', ⟨rs, hmem⟩⟩ := by
  simp [rowF2, mkBridgeRowIndex, hmem, finVals_finPack]

theorem rowF2_mkBridgeRowIndex_notMem {P : WRP.Presentation Step Step}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hSsuf : ∀ r c' x, x ∈ Ssuf r c' → x < Q)
    (hSpre : ∀ r c' x, x ∈ Spre r c' → x < Q)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh)
    (hmem : rs ∉ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity c') q_U q_D) :
    rowF2 hpG
        (mkBridgeRowIndex (M := M) (Q := Q) (Ndeep := Ndeep) S1 F2 Ssuf Spre Dsuf Dpre
          hS1 hF2 hSsuf hSpre hDsuf hDpre) rN c' rs = ∅ := by
  simp [rowF2, hmem]

theorem rowSsuf_mkBridgeRowIndex {P : WRP.Presentation Step Step}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hSsuf : ∀ r c' x, x ∈ Ssuf r c' → x < Q)
    (hSpre : ∀ r c' x, x ∈ Spre r c' → x < Q)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K) :
    rowSsuf hpG
        (mkBridgeRowIndex (M := M) (Q := Q) (Ndeep := Ndeep) S1 F2 Ssuf Spre Dsuf Dpre
          hS1 hF2 hSsuf hSpre hDsuf hDpre) rN c'
      = Ssuf (rowClass hpG rN) c' := by
  simp [rowSsuf, mkBridgeRowIndex, finVals_finPack]

theorem rowSpre_mkBridgeRowIndex {P : WRP.Presentation Step Step}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hSsuf : ∀ r c' x, x ∈ Ssuf r c' → x < Q)
    (hSpre : ∀ r c' x, x ∈ Spre r c' → x < Q)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K) :
    rowSpre hpG
        (mkBridgeRowIndex (M := M) (Q := Q) (Ndeep := Ndeep) S1 F2 Ssuf Spre Dsuf Dpre
          hS1 hF2 hSsuf hSpre hDsuf hDpre) rN c'
      = Spre (rowClass hpG rN) c' := by
  simp [rowSpre, mkBridgeRowIndex, finVals_finPack]

theorem rowDsuf_mkBridgeRowIndex {P : WRP.Presentation Step Step}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hSsuf : ∀ r c' x, x ∈ Ssuf r c' → x < Q)
    (hSpre : ∀ r c' x, x ∈ Spre r c' → x < Q)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K) :
    rowDsuf hpG
        (mkBridgeRowIndex (M := M) (Q := Q) (Ndeep := Ndeep) S1 F2 Ssuf Spre Dsuf Dpre
          hS1 hF2 hSsuf hSpre hDsuf hDpre) rN c'
      = Dsuf (rowClass hpG rN) c' := by
  simp [rowDsuf, mkBridgeRowIndex, finVals_finPack]

theorem rowDpre_mkBridgeRowIndex {P : WRP.Presentation Step Step}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hSsuf : ∀ r c' x, x ∈ Ssuf r c' → x < Q)
    (hSpre : ∀ r c' x, x ∈ Spre r c' → x < Q)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K) :
    rowDpre hpG
        (mkBridgeRowIndex (M := M) (Q := Q) (Ndeep := Ndeep) S1 F2 Ssuf Spre Dsuf Dpre
          hS1 hF2 hSsuf hSpre hDsuf hDpre) rN c'
      = Dpre (rowClass hpG rN) c' := by
  simp [rowDpre, mkBridgeRowIndex, finVals_finPack]

theorem rowS1_mkBridgeUpdateRowIndex {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B)
    (hmem : rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity c') q_U q_D) :
    rowS1 (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c' rs
      = S1 (rowClass hpG rN) ⟨c', ⟨rs, hmem⟩⟩ := by
  simpa [mkBridgeUpdateRowIndex] using
    rowS1_mkBridgeRowIndex (Q := Q) hpG S1 F2
      (updateSsufRowTable P hV pcF Ts j0F mS repN Q)
      (updateSpreRowTable P hV pcF Tp j0F mS repN Q)
      Dsuf Dpre hS1 hF2
      (fun _ _ _ hx => updateSsufRowTable_mem_lt P hV pcF Ts j0F mS repN Q hx)
      (fun _ _ _ hx => updateSpreRowTable_mem_lt P hV pcF Tp j0F mS repN Q hx)
      hDsuf hDpre rN c' rs hmem

theorem rowS1_mkBridgeUpdateRowIndex_notMem
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B)
    (hmem : rs ∉ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity c') q_U q_D) :
    rowS1 (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c' rs = ∅ := by
  simpa [mkBridgeUpdateRowIndex] using
    rowS1_mkBridgeRowIndex_notMem (Q := Q) hpG S1 F2
      (updateSsufRowTable P hV pcF Ts j0F mS repN Q)
      (updateSpreRowTable P hV pcF Tp j0F mS repN Q)
      Dsuf Dpre hS1 hF2
      (fun _ _ _ hx => updateSsufRowTable_mem_lt P hV pcF Ts j0F mS repN Q hx)
      (fun _ _ _ hx => updateSpreRowTable_mem_lt P hV pcF Tp j0F mS repN Q hx)
      hDsuf hDpre rN c' rs hmem

theorem rowF2_mkBridgeUpdateRowIndex {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh)
    (hmem : rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity c') q_U q_D) :
    rowF2 (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c' rs
      = F2 (rowClass hpG rN) ⟨c', ⟨rs, hmem⟩⟩ := by
  simpa [mkBridgeUpdateRowIndex] using
    rowF2_mkBridgeRowIndex (Q := Q) hpG S1 F2
      (updateSsufRowTable P hV pcF Ts j0F mS repN Q)
      (updateSpreRowTable P hV pcF Tp j0F mS repN Q)
      Dsuf Dpre hS1 hF2
      (fun _ _ _ hx => updateSsufRowTable_mem_lt P hV pcF Ts j0F mS repN Q hx)
      (fun _ _ _ hx => updateSpreRowTable_mem_lt P hV pcF Tp j0F mS repN Q hx)
      hDsuf hDpre rN c' rs hmem

theorem rowF2_mkBridgeUpdateRowIndex_notMem
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh)
    (hmem : rs ∉ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity c') q_U q_D) :
    rowF2 (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c' rs = ∅ := by
  simpa [mkBridgeUpdateRowIndex] using
    rowF2_mkBridgeRowIndex_notMem (Q := Q) hpG S1 F2
      (updateSsufRowTable P hV pcF Ts j0F mS repN Q)
      (updateSpreRowTable P hV pcF Tp j0F mS repN Q)
      Dsuf Dpre hS1 hF2
      (fun _ _ _ hx => updateSsufRowTable_mem_lt P hV pcF Ts j0F mS repN Q hx)
      (fun _ _ _ hx => updateSpreRowTable_mem_lt P hV pcF Tp j0F mS repN Q hx)
      hDsuf hDpre rN c' rs hmem

theorem rowS1Odd_mkBridgeUpdateRowIndex {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (hS1odd : ∀ r key x, x ∈ S1 r key → x % 2 = 1)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B)
    (hmem : rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity c') q_U q_D) :
    rowS1Odd (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c' rs
      = S1 (rowClass hpG rN) ⟨c', ⟨rs, hmem⟩⟩ := by
  rw [rowS1Odd,
    rowS1_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp j0F mS repN
      S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre rN c' rs hmem]
  exact Finset.filter_true_of_mem (fun x hx => hS1odd (rowClass hpG rN) ⟨c', ⟨rs, hmem⟩⟩ x hx)

theorem rowS1Odd_mkBridgeUpdateRowIndex_notMem
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B)
    (hmem : rs ∉ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity c') q_U q_D) :
    rowS1Odd (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c' rs = ∅ := by
  rw [rowS1Odd,
    rowS1_mkBridgeUpdateRowIndex_notMem (hV := hV) (Q := Q) hpG pcF Ts Tp j0F mS
      repN S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre rN c' rs hmem]
  simp

theorem rowF2Odd_mkBridgeUpdateRowIndex {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (hF2odd : ∀ r key x, x ∈ F2 r key → x % 2 = 1)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh)
    (hmem : rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity c') q_U q_D) :
    rowF2Odd (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c' rs
      = F2 (rowClass hpG rN) ⟨c', ⟨rs, hmem⟩⟩ := by
  rw [rowF2Odd,
    rowF2_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp j0F mS repN
      S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre rN c' rs hmem]
  exact Finset.filter_true_of_mem (fun x hx => hF2odd (rowClass hpG rN) ⟨c', ⟨rs, hmem⟩⟩ x hx)

theorem rowF2Odd_mkBridgeUpdateRowIndex_notMem
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh)
    (hmem : rs ∉ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity c') q_U q_D) :
    rowF2Odd (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c' rs = ∅ := by
  rw [rowF2Odd,
    rowF2_mkBridgeUpdateRowIndex_notMem (hV := hV) (Q := Q) hpG pcF Ts Tp j0F mS
      repN S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre rN c' rs hmem]
  simp

theorem rowSsuf_mkBridgeUpdateRowIndex {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K) :
    rowSsuf (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c'
      = updateSsufRowTable P hV pcF Ts j0F mS repN Q (rowClass hpG rN) c' := by
  simpa [mkBridgeUpdateRowIndex] using
    rowSsuf_mkBridgeRowIndex (Q := Q) hpG S1 F2
      (updateSsufRowTable P hV pcF Ts j0F mS repN Q)
      (updateSpreRowTable P hV pcF Tp j0F mS repN Q)
      Dsuf Dpre hS1 hF2
      (fun _ _ _ hx => updateSsufRowTable_mem_lt P hV pcF Ts j0F mS repN Q hx)
      (fun _ _ _ hx => updateSpreRowTable_mem_lt P hV pcF Tp j0F mS repN Q hx)
      hDsuf hDpre rN c'

theorem rowSpre_mkBridgeUpdateRowIndex {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K) :
    rowSpre (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c'
      = updateSpreRowTable P hV pcF Tp j0F mS repN Q (rowClass hpG rN) c' := by
  simpa [mkBridgeUpdateRowIndex] using
    rowSpre_mkBridgeRowIndex (Q := Q) hpG S1 F2
      (updateSsufRowTable P hV pcF Ts j0F mS repN Q)
      (updateSpreRowTable P hV pcF Tp j0F mS repN Q)
      Dsuf Dpre hS1 hF2
      (fun _ _ _ hx => updateSsufRowTable_mem_lt P hV pcF Ts j0F mS repN Q hx)
      (fun _ _ _ hx => updateSpreRowTable_mem_lt P hV pcF Tp j0F mS repN Q hx)
      hDsuf hDpre rN c'

/-- Push an actual suffix activation into the update row index when the caller
has already transported the actual absolute table to the row representative.
This is the non-existential version used by the direct bridge after all row
floors have been chosen. -/
theorem rowSsuf_mkBridgeUpdateRowIndex_mem_of_activation_table_eq
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    (hpG : 1 ≤ pG)
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (c' : Fin P.toPoly.K)
    (hpc : 1 ≤ pcF c') (hmval : Ts c' + 2 * pcF c' ≤ mS - 1)
    (n ρ : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hρ : ρ < Q)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = F l)
    (h0F :
      F (Ts c' + ((ρ + Q - ((mS + 2 * n + 1 + Ts c') % Q)) % pcF c'))
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1F :
      F (Ts c' + ((ρ + Q - ((mS + 2 * n + 1 + Ts c') % Q)) % pcF c') +
          pcF c') = CopiedDstar.dstarRankGA_m P hV mS n)
    (htable :
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        updateSsufRowTable P hV pcF Ts j0F mS repN Q (rowClass hpG (n % pG)) c') :
    ρ ∈ rowSsuf (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
        hS1 hF2 hDsuf hDpre) (n % pG) c' := by
  have hAbs :=
    CopiedBoundedGateBand.mem_updateSufAbsTieSet_of_activation P hV hActive
      c' (j0F c') (fun _ : Fin (P.toPoly.arity c') => 0)
      mS n (pcF c') (Ts c') Q ρ F hpc hρ hmval hag h0F h1F
  have hrow :=
    rowSsuf_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp j0F mS repN
      S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre (n % pG) c'
  rw [hrow, ← htable]
  exact hAbs

/-- Prefix twin of
`rowSsuf_mkBridgeUpdateRowIndex_mem_of_activation_table_eq`. -/
theorem rowSpre_mkBridgeUpdateRowIndex_mem_of_activation_table_eq
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    (hpG : 1 ≤ pG)
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (c' : Fin P.toPoly.K)
    (hpc : 1 ≤ pcF c') (hmval : Tp c' + 2 * pcF c' ≤ mS - 1)
    (n ρ : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hρ : ρ < Q)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = F l)
    (h0F :
      F (Tp c' + ((ρ + Q - ((Tp c') % Q)) % pcF c'))
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1F :
      F (Tp c' + ((ρ + Q - ((Tp c') % Q)) % pcF c') + pcF c')
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (htable :
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        updateSpreRowTable P hV pcF Tp j0F mS repN Q (rowClass hpG (n % pG)) c') :
    ρ ∈ rowSpre (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
        hS1 hF2 hDsuf hDpre) (n % pG) c' := by
  have hAbs :=
    CopiedBoundedGateBand.mem_updatePreAbsTieSet_of_activation P hV hActive
      c' (j0F c') (fun _ : Fin (P.toPoly.arity c') => 0)
      mS n (pcF c') (Tp c') Q ρ F hpc hρ hmval hag h0F h1F
  have hrow :=
    rowSpre_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp j0F mS repN
      S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre (n % pG) c'
  rw [hrow, ← htable]
  exact hAbs

/-- Fully composed suffix activation hook for canonical `rowRep`: a single
floor dominating the row-fold and copied-slice guard thresholds is enough to
push an actual activation residue into the finite update row index. -/
theorem rowSsuf_mkBridgeUpdateRowIndex_mem_of_activation_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hQdvd : Q ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hpc : 1 ≤ pcF c') (hm : 1 ≤ mS)
    (hmval : Ts c' + 2 * pcF c' ≤ mS - 1)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (n ρ : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hρ : ρ < Q)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = F l)
    (h0F :
      F (Ts c' + ((ρ + Q - ((mS + 2 * n + 1 + Ts c') % Q)) % pcF c'))
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1F :
      F (Ts c' + ((ρ + Q - ((mS + 2 * n + 1 + Ts c') % Q)) % pcF c') +
          pcF c') = CopiedDstar.dstarRankGA_m P hV mS n) :
    ρ ∈ rowSsuf (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c' := by
  have htable :=
    updateSsufRowTable_eq_of_zero_fold_n_actual_rowClass_rowRep_of_floor
      P hV hpG hp0dvd hQdvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts j0F c' N hN hm hN_floor hNDom_floor hNDp_floor hn_floor hG
  exact rowSsuf_mkBridgeUpdateRowIndex_mem_of_activation_table_eq (hV := hV)
    (Q := Q) hpG hActive pcF Ts Tp j0F mS (rowRep pG Nfloor)
    S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre c' hpc hmval n ρ F hρ hag h0F h1F htable

/-- Prefix twin of
`rowSsuf_mkBridgeUpdateRowIndex_mem_of_activation_rowRep_floor`. -/
theorem rowSpre_mkBridgeUpdateRowIndex_mem_of_activation_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hpc : 1 ≤ pcF c') (hm : 1 ≤ mS)
    (hmval : Tp c' + 2 * pcF c' ≤ mS - 1)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (n ρ : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hρ : ρ < Q)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = F l)
    (h0F :
      F (Tp c' + ((ρ + Q - ((Tp c') % Q)) % pcF c'))
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1F :
      F (Tp c' + ((ρ + Q - ((Tp c') % Q)) % pcF c') + pcF c')
        = CopiedDstar.dstarRankGA_m P hV mS n) :
    ρ ∈ rowSpre (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c' := by
  have htable :=
    updateSpreRowTable_eq_of_zero_fold_n_actual_rowClass_rowRep_of_floor
      P hV (Q := Q) hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Tp j0F c' N hN hm hN_floor hNDom_floor hNDp_floor hn_floor hG
  exact rowSpre_mkBridgeUpdateRowIndex_mem_of_activation_table_eq (hV := hV)
    (Q := Q) hpG hActive pcF Ts Tp j0F mS (rowRep pG Nfloor)
    S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre c' hpc hmval n ρ F hρ hag h0F h1F htable

/-- Updating a zero base tuple at an in-bounds position keeps every coordinate
in bounds.  This is the zero-base validity fact used by the direct update
bridge's run-band obligations. -/
theorem update_zero_valid_of_position_lt {α : Type*} [DecidableEq α]
    {j0 : α} {p L : ℕ} (hp : p < L) :
    ∀ i, Function.update (fun _ : α => 0) j0 p i < L := by
  intro i
  by_cases hi : i = j0
  · subst i
    simpa [Function.update] using hp
  · have hL : 0 < L := Nat.lt_of_le_of_lt (Nat.zero_le p) hp
    simpa [Function.update, hi] using hL

/-- Convert a tie-side `hall` ordering hypothesis plus a freshly proved
`d*` rank equality into the raw `ord` clause expected by the update bridge
gate. -/
theorem ord_of_tie_hall_rank
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {mS n : ℕ} {c c' : Fin P.toPoly.K}
    {ī : Fin (P.toPoly.arity c) → ℕ}
    {xb : Fin (P.toPoly.arity c') → ℕ}
    (hall : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    (hxbval : ∀ i, xb i < (copiedSlice mS n).length)
    (hsel : P.toPoly.sel c' (copiedSlice mS n) xb)
    (hlabel : P.toPoly.label c' (copiedSlice mS n) xb = D)
    (hrank : P.rank c' (copiedSlice mS n) xb =
      CopiedDstar.dstarRankGA_m P hV mS n) :
    P.toPoly.ord c c' (copiedSlice mS n) ī xb := by
  have hbsel :
      P.toPoly.selectedAtom (copiedSlice mS n) (⟨c', xb⟩ : P.toPoly.Atom) :=
    ⟨hxbval, hsel⟩
  have hbD :
      P.toPoly.labelOf (copiedSlice mS n) (⟨c', xb⟩ : P.toPoly.Atom) = D := by
    simpa [Polyreg.Presentation.labelOf] using hlabel
  have hbrank :
      P.rankOf (copiedSlice mS n) (⟨c', xb⟩ : P.toPoly.Atom) =
        CopiedDstar.dstarRankGA_m P hV mS n := by
    simpa [WRP.Presentation.rankOf] using hrank
  simpa [Polyreg.Presentation.atomOrd] using
    hall (⟨c', xb⟩ : P.toPoly.Atom) hbsel hbD hbrank

/-- Decode a suffix run-residue stored in the canonical update row index and
use update band soundness to prove the moving-coordinate update tuple has rank
`d*` at the actual slice. -/
theorem rank_update_suffix_of_rowSsuf_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hQdvd : Q ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hSound : CopiedBoundedGateBand.BandedUpdateRankSoundness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hpc : 1 ≤ pcF c') (hQpos : 0 < Q) (hpcQ : pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hmval : Ts c' + 2 * pcF c' ≤ mS - 1)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (n k ρ p : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hk : 2 ≤ k) (hTk : Ts c' ≤ k - 2)
    (hF : CopiedDstarCMS.RankAffineAtFrom (Ts c') (pcF c') F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = F l)
    (hrmem : ρ ∈ rowSsuf (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c')
    (hp : p < (copiedSlice mS n).length)
    (hguard : CopiedBandRunGate.updateSufBandGuard (copiedSlice mS n) Q ρ k p) :
    P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  have htable :=
    updateSsufRowTable_eq_of_zero_fold_n_actual_rowClass_rowRep_of_floor
      P hV hpG hp0dvd hQdvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts j0F c' N hN hm hN_floor hNDom_floor hNDp_floor hn_floor hG
  have hrow :=
    rowSsuf_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp j0F mS
      (rowRep pG Nfloor) S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre (n % pG) c'
  have hAbs :
      ρ ∈ CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
        (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q := by
    rw [hrow] at hrmem
    rwa [htable]
  have hAbsData :=
    (CopiedBoundedGateBand.mem_updateSufAbsTieSet P hV c' (j0F c')
      (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q ρ).mp hAbs
  set ρact : ℕ := (ρ + Q - ((mS + 2 * n + 1 + Ts c') % Q)) % pcF c' with hρact_def
  have hlocal :
      ρact ∈ CopiedBoundedGateBand.updateSufTieSet P hV c' (j0F c')
        (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') := by
    simpa [ρact, hρact_def] using hAbsData.2
  have hRanks := (Finset.mem_filter.mp hlocal).2
  have hρact_lt : ρact < pcF c' := by
    rw [hρact_def]
    exact Nat.mod_lt _ (by omega)
  have h0F : F (Ts c' + ρact) = CopiedDstar.dstarRankGA_m P hV mS n := by
    exact (hag (Ts c' + ρact) (by omega)).symm.trans hRanks.1
  have h1F :
      F (Ts c' + ρact + pcF c') = CopiedDstar.dstarRankGA_m P hV mS n := by
    exact (hag (Ts c' + ρact + pcF c') (by omega)).symm.trans hRanks.2
  exact hSound.1 c' (j0F c') (fun _ : Fin (P.toPoly.arity c') => 0) (_B := B)
    mS n (pcF c') (Ts c') Q k F hm hn hpc hQpos hpcQ hk hTk hmval hF hag
    hAbsData.1 hρact_def h0F h1F p hp hguard.2 hguard.1.2

/-- Prefix twin of `rank_update_suffix_of_rowSsuf_rowRep_floor`. -/
theorem rank_update_prefix_of_rowSpre_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hSound : CopiedBoundedGateBand.BandedUpdateRankSoundness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hpc : 1 ≤ pcF c') (hQpos : 0 < Q) (hpcQ : pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hmval : Tp c' + 2 * pcF c' ≤ mS - 1)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (n k ρ p : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hTk : Tp c' ≤ k)
    (hF : CopiedDstarCMS.RankAffineAtFrom (Tp c') (pcF c') F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = F l)
    (hrmem : ρ ∈ rowSpre (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c')
    (hguard : CopiedBandRunGate.preBandStrictGuard (copiedSlice mS n) Q ρ k p) :
    P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  have htable :=
    updateSpreRowTable_eq_of_zero_fold_n_actual_rowClass_rowRep_of_floor
      P hV (Q := Q) hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Tp j0F c' N hN hm hN_floor hNDom_floor hNDp_floor hn_floor hG
  have hrow :=
    rowSpre_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp j0F mS
      (rowRep pG Nfloor) S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre (n % pG) c'
  have hAbs :
      ρ ∈ CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
        (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q := by
    rw [hrow] at hrmem
    rwa [htable]
  have hAbsData :=
    (CopiedBoundedGateBand.mem_updatePreAbsTieSet P hV c' (j0F c')
      (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q ρ).mp hAbs
  set ρact : ℕ := (ρ + Q - ((Tp c') % Q)) % pcF c' with hρact_def
  have hlocal :
      ρact ∈ CopiedBoundedGateBand.updatePreTieSet P hV c' (j0F c')
        (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') := by
    simpa [ρact, hρact_def] using hAbsData.2
  have hRanks := (Finset.mem_filter.mp hlocal).2
  have hρact_lt : ρact < pcF c' := by
    rw [hρact_def]
    exact Nat.mod_lt _ (by omega)
  have h0F : F (Tp c' + ρact) = CopiedDstar.dstarRankGA_m P hV mS n := by
    exact (hag (Tp c' + ρact) (by omega)).symm.trans hRanks.1
  have h1F :
      F (Tp c' + ρact + pcF c') = CopiedDstar.dstarRankGA_m P hV mS n := by
    exact (hag (Tp c' + ρact + pcF c') (by omega)).symm.trans hRanks.2
  have hpref : p < mS - 1 := by
    rcases hguard.2.2 with ⟨z, _hzlen, hpz, hzD, hzNoD⟩
    have hzfirst := CopiedBoundedGateBand.firstD_of_no_previous_D_copiedSlice
      mS n (z + 2) hm hn hzD hzNoD
    omega
  exact hSound.2.1 c' (j0F c') (fun _ : Fin (P.toPoly.arity c') => 0) (_B := B)
    mS n (pcF c') (Tp c') Q k F hm hn hpc hQpos hpcQ hTk hmval hF hag
    hAbsData.1 hρact_def h0F h1F p hguard.1.1 hguard.2.1 hpref hguard.1.2

/-- Forward bridge hook for the update suffix-row clause: row membership and
the suffix band guard prove the competitor is a selected `D` atom of rank `d*`,
so the tie-side ordering hypothesis supplies the gate's raw `ord` conclusion. -/
theorem ord_update_suffix_of_rowSsuf_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hQdvd : Q ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hSound : CopiedBoundedGateBand.BandedUpdateRankSoundness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    {c : Fin P.toPoly.K} (ī : Fin (P.toPoly.arity c) → ℕ)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hpc : 1 ≤ pcF c') (hQpos : 0 < Q) (hpcQ : pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hmval : Ts c' + 2 * pcF c' ≤ mS - 1)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (n k ρ p : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hk : 2 ≤ k) (hTk : Ts c' ≤ k - 2)
    (hF : CopiedDstarCMS.RankAffineAtFrom (Ts c') (pcF c') F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = F l)
    (hall : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    (hrmem : ρ ∈ rowSsuf (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c')
    (hp : p < (copiedSlice mS n).length)
    (hguard : CopiedBandRunGate.updateSufBandGuard (copiedSlice mS n) Q ρ k p)
    (hsel : P.toPoly.sel c' (copiedSlice mS n)
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p))
    (hlabel : P.toPoly.label c' (copiedSlice mS n)
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p) = D) :
    P.toPoly.ord c c' (copiedSlice mS n) ī
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p) := by
  have hrank :=
    rank_update_suffix_of_rowSsuf_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN) (NDomN := NDomN)
      (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hQdvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN hSound
      pcF Ts Tp j0F mS S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre c' N hN hpc hQpos
      hpcQ hm hmval hN_floor hNDom_floor hNDp_floor n k ρ p F hn hn_floor hG hk
      hTk hF hag hrmem hp hguard
  exact ord_of_tie_hall_rank (P := P) (hV := hV) hall
    (update_zero_valid_of_position_lt (α := Fin (P.toPoly.arity c')) hp) hsel hlabel hrank

/-- Prefix twin of `ord_update_suffix_of_rowSsuf_rowRep_floor`. -/
theorem ord_update_prefix_of_rowSpre_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hSound : CopiedBoundedGateBand.BandedUpdateRankSoundness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    {c : Fin P.toPoly.K} (ī : Fin (P.toPoly.arity c) → ℕ)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hpc : 1 ≤ pcF c') (hQpos : 0 < Q) (hpcQ : pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hmval : Tp c' + 2 * pcF c' ≤ mS - 1)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (n k ρ p : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hTk : Tp c' ≤ k)
    (hF : CopiedDstarCMS.RankAffineAtFrom (Tp c') (pcF c') F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = F l)
    (hall : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    (hrmem : ρ ∈ rowSpre (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c')
    (hp : p < (copiedSlice mS n).length)
    (hguard : CopiedBandRunGate.preBandStrictGuard (copiedSlice mS n) Q ρ k p)
    (hsel : P.toPoly.sel c' (copiedSlice mS n)
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p))
    (hlabel : P.toPoly.label c' (copiedSlice mS n)
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p) = D) :
    P.toPoly.ord c c' (copiedSlice mS n) ī
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p) := by
  have hrank :=
    rank_update_prefix_of_rowSpre_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN) (NDomN := NDomN)
      (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN hSound
      pcF Ts Tp j0F mS S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre c' N hN hpc hQpos
      hpcQ hm hmval hN_floor hNDom_floor hNDp_floor n k ρ p F hn hn_floor hG hTk
      hF hag hrmem hguard
  exact ord_of_tie_hall_rank (P := P) (hV := hV) hall
    (update_zero_valid_of_position_lt (α := Fin (P.toPoly.arity c')) hp) hsel hlabel hrank

theorem rowDsuf_mkBridgeUpdateRowIndex {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K) :
    rowDsuf (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c'
      = Dsuf (rowClass hpG rN) c' := by
  simpa [mkBridgeUpdateRowIndex] using
    rowDsuf_mkBridgeRowIndex (Q := Q) hpG S1 F2
      (updateSsufRowTable P hV pcF Ts j0F mS repN Q)
      (updateSpreRowTable P hV pcF Tp j0F mS repN Q)
      Dsuf Dpre hS1 hF2
      (fun _ _ _ hx => updateSsufRowTable_mem_lt P hV pcF Ts j0F mS repN Q hx)
      (fun _ _ _ hx => updateSpreRowTable_mem_lt P hV pcF Tp j0F mS repN Q hx)
      hDsuf hDpre rN c'

theorem rowDpre_mkBridgeUpdateRowIndex {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (rN : ℕ) (c' : Fin P.toPoly.K) :
    rowDpre (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2 Dsuf Dpre
          hS1 hF2 hDsuf hDpre) rN c'
      = Dpre (rowClass hpG rN) c' := by
  simpa [mkBridgeUpdateRowIndex] using
    rowDpre_mkBridgeRowIndex (Q := Q) hpG S1 F2
      (updateSsufRowTable P hV pcF Ts j0F mS repN Q)
      (updateSpreRowTable P hV pcF Tp j0F mS repN Q)
      Dsuf Dpre hS1 hF2
      (fun _ _ _ hx => updateSsufRowTable_mem_lt P hV pcF Ts j0F mS repN Q hx)
      (fun _ _ _ hx => updateSpreRowTable_mem_lt P hV pcF Tp j0F mS repN Q hx)
      hDsuf hDpre rN c'

/-- Deep-suffix row rewrite for update row indices built from the genuine
update-tuple deep tables. -/
theorem rowDsuf_mkBridgeUpdateRowIndex_updateDeepRows
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (rN : ℕ) (c' : Fin P.toPoly.K) :
    rowDsuf (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2
          (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS repN)
          (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS repN)
          hS1 hF2
          (fun r c' x hx => updateDeepDsufRowTable_mem_lt
            (B := B) P hV Ndeep j0F mS repN (r := r) (c' := c') (k := x) hx)
          (fun r c' x hx => updateDeepDpreRowTable_mem_lt
            (B := B) P hV Ndeep j0F mS repN (r := r) (c' := c') (k := x) hx))
        rN c'
      = updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS repN (rowClass hpG rN) c' := by
  exact rowDsuf_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp j0F mS repN
    S1 F2
    (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS repN)
    (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS repN)
    hS1 hF2
    (fun r c' x hx => updateDeepDsufRowTable_mem_lt
      (B := B) P hV Ndeep j0F mS repN (r := r) (c' := c') (k := x) hx)
    (fun r c' x hx => updateDeepDpreRowTable_mem_lt
      (B := B) P hV Ndeep j0F mS repN (r := r) (c' := c') (k := x) hx)
    rN c'

/-- Deep-prefix twin of `rowDsuf_mkBridgeUpdateRowIndex_updateDeepRows`. -/
theorem rowDpre_mkBridgeUpdateRowIndex_updateDeepRows
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ} (hpG : 1 ≤ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (rN : ℕ) (c' : Fin P.toPoly.K) :
    rowDpre (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN S1 F2
          (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS repN)
          (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS repN)
          hS1 hF2
          (fun r c' x hx => updateDeepDsufRowTable_mem_lt
            (B := B) P hV Ndeep j0F mS repN (r := r) (c' := c') (k := x) hx)
          (fun r c' x hx => updateDeepDpreRowTable_mem_lt
            (B := B) P hV Ndeep j0F mS repN (r := r) (c' := c') (k := x) hx))
        rN c'
      = updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS repN (rowClass hpG rN) c' := by
  exact rowDpre_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp j0F mS repN
    S1 F2
    (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS repN)
    (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS repN)
    hS1 hF2
    (fun r c' x hx => updateDeepDsufRowTable_mem_lt
      (B := B) P hV Ndeep j0F mS repN (r := r) (c' := c') (k := x) hx)
    (fun r c' x hx => updateDeepDpreRowTable_mem_lt
      (B := B) P hV Ndeep j0F mS repN (r := r) (c' := c') (k := x) hx)
    rN c'

/-- Push an actual update-tuple deep-suffix activation into the canonical
update-deep row index. -/
theorem rowDsuf_mkBridgeUpdateRowIndex_mem_of_updateDeep_active_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hm : 1 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (n k : ℕ)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hkN : k < Ndeep c')
    (hactive : P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mixedPosAt
            (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
            mS (B + 1) n))
      = CopiedDstar.dstarRankGA_m P hV mS n) :
    k ∈ rowDsuf (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)) (n % pG) c' := by
  let rcls : Fin pG := rowClass hpG (n % pG)
  have hGrep :
      CopiedAchSetFold.domDp P mS (rowRep pG Nfloor rcls) :=
    domDp_rowClass_rowRep_of_actual_of_floor P hpG hpDomN hpDpN hpDomN_dvd hpDpN_dvd
      hDomN hDpN hm hNDom_floor hNDp_floor hn_floor hG
  have hmod : n % p0 = rowRep pG Nfloor rcls % p0 :=
    (repN_rowClass_mod_of_dvd hpG hp0dvd (fun r : Fin pG => rowRep_modEq r) n).symm
  have hsets := hN n (rowRep pG Nfloor rcls)
    (le_trans hN_floor hn_floor)
    (le_trans hN_floor (rowRep_ge_floor hpG rcls))
    (le_trans hB_floor hn_floor)
    (le_trans hB_floor (rowRep_ge_floor hpG rcls))
    hmod hG hGrep
  have hactive_mem :
      k ∈ (Finset.range (Ndeep c')).filter (fun k =>
        P.rank c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mixedPosAt
                (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                mS (B + 1) n))
          = CopiedDstar.dstarRankGA_m P hV mS n) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkN, hactive⟩
  have hactive_rep :
      k ∈ updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          rcls c' := by
    rw [updateDeepDsufRowTable, ← hsets]
    exact hactive_mem
  have hrow :=
    rowDsuf_mkBridgeUpdateRowIndex_updateDeepRows (hV := hV) (B := B) (Q := Q)
      (Ndeep := Ndeep)
      hpG pcF Ts Tp j0F mS (rowRep pG Nfloor) S1 F2 hS1 hF2 (n % pG) c'
  rw [hrow]
  exact hactive_rep

/-- Push an actual update-tuple deep-prefix activation into the canonical
update-deep row index. -/
theorem rowDpre_mkBridgeUpdateRowIndex_mem_of_updateDeep_active_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hm : 1 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (n k : ℕ)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hkN : k < Ndeep c')
    (hactive : P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mixedPosAt
            (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
            mS (B + 1) n))
      = CopiedDstar.dstarRankGA_m P hV mS n) :
    k + 3 ∈ rowDpre (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)) (n % pG) c' := by
  let rcls : Fin pG := rowClass hpG (n % pG)
  have hGrep :
      CopiedAchSetFold.domDp P mS (rowRep pG Nfloor rcls) :=
    domDp_rowClass_rowRep_of_actual_of_floor P hpG hpDomN hpDpN hpDomN_dvd hpDpN_dvd
      hDomN hDpN hm hNDom_floor hNDp_floor hn_floor hG
  have hmod : n % p0 = rowRep pG Nfloor rcls % p0 :=
    (repN_rowClass_mod_of_dvd hpG hp0dvd (fun r : Fin pG => rowRep_modEq r) n).symm
  have hsets := hN n (rowRep pG Nfloor rcls)
    (le_trans hN_floor hn_floor)
    (le_trans hN_floor (rowRep_ge_floor hpG rcls))
    (le_trans hB_floor hn_floor)
    (le_trans hB_floor (rowRep_ge_floor hpG rcls))
    hmod hG hGrep
  have hactive_mem :
      k ∈ (Finset.range (Ndeep c')).filter (fun k =>
        P.rank c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mixedPosAt
                (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                mS (B + 1) n))
          = CopiedDstar.dstarRankGA_m P hV mS n) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkN, hactive⟩
  have hactive_rep :
      k + 3 ∈ updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS
          (rowRep pG Nfloor) rcls c' := by
    rw [updateDeepDpreRowTable]
    exact Finset.mem_image.mpr ⟨k, by rwa [← hsets], rfl⟩
  have hrow :=
    rowDpre_mkBridgeUpdateRowIndex_updateDeepRows (hV := hV) (B := B) (Q := Q)
      (Ndeep := Ndeep)
      hpG pcF Ts Tp j0F mS (rowRep pG Nfloor) S1 F2 hS1 hF2 (n % pG) c'
  rw [hrow]
  exact hactive_rep

/-- Decode a deep-suffix row stored in the genuine update-tuple table and
transport it from the row representative back to the actual `n`. -/
theorem rank_update_deep_suffix_of_rowDsuf_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (hDsufRow : ∀ r c',
      Dsuf r c' =
        (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS (rowRep pG Nfloor r))
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) (rowRep pG Nfloor r)))
            = CopiedDstar.dstarRankGA_m P hV mS (rowRep pG Nfloor r)))
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hm : 1 ≤ mS) (hNdeep_add2 : Ndeep c' + 2 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (n k p : ℕ)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hrmem : k ∈ rowDsuf (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c')
    (hguard : ((copiedSlice mS n)[p]? = some D
        ∧ ∀ q, q < (copiedSlice mS n).length → p < q →
            (copiedSlice mS n)[q]? = some D)
      ∧ p + 1 + k = (copiedSlice mS n).length) :
    P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  let rcls : Fin pG := rowClass hpG (n % pG)
  have hGrep :
      CopiedAchSetFold.domDp P mS (rowRep pG Nfloor rcls) :=
    domDp_rowClass_rowRep_of_actual_of_floor P hpG hpDomN hpDpN hpDomN_dvd hpDpN_dvd
      hDomN hDpN hm hNDom_floor hNDp_floor hn_floor hG
  have hmod : n % p0 = rowRep pG Nfloor rcls % p0 :=
    (repN_rowClass_mod_of_dvd hpG hp0dvd (fun r : Fin pG => rowRep_modEq r) n).symm
  have hsets := hN n (rowRep pG Nfloor rcls)
    (le_trans hN_floor hn_floor)
    (le_trans hN_floor (rowRep_ge_floor hpG rcls))
    (le_trans hB_floor hn_floor)
    (le_trans hB_floor (rowRep_ge_floor hpG rcls))
    hmod hG hGrep
  have hrow :
      rowDsuf (Q := Q) hpG
          (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
            S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c'
        = Dsuf rcls c' := by
    dsimp [rcls]
    exact rowDsuf_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp
      j0F mS (rowRep pG Nfloor) S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre (n % pG) c'
  have hactive_rep :
      k ∈ (Finset.range (Ndeep c')).filter (fun k =>
        P.rank c' (copiedSlice mS (rowRep pG Nfloor rcls))
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mixedPosAt
                (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                mS (B + 1) (rowRep pG Nfloor rcls)))
          = CopiedDstar.dstarRankGA_m P hV mS (rowRep pG Nfloor rcls)) := by
    rw [hrow, hDsufRow rcls c'] at hrmem
    exact hrmem
  have hactive_mem :
      k ∈ (Finset.range (Ndeep c')).filter (fun k =>
        P.rank c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mixedPosAt
                (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                mS (B + 1) n))
          = CopiedDstar.dstarRankGA_m P hV mS n) := by
    rw [hsets]
    exact hactive_rep
  have hkN : k < Ndeep c' := Finset.mem_range.mp (Finset.mem_filter.mp hactive_mem).1
  have hk : k + 2 ≤ mS := by omega
  have hp_eq :
      p = mixedPosAt (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
          mS (B + 1) n :=
    CopiedBoundedGateBand.deepSuf_fromEnd_mixedPosAt (B := B) mS n (B + 1) p k hk
      hguard.2
  rw [hp_eq]
  exact (Finset.mem_filter.mp hactive_mem).2

/-- Prefix twin of `rank_update_deep_suffix_of_rowDsuf_rowRep_floor`. -/
theorem rank_update_deep_prefix_of_rowDpre_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (hDpreRow : ∀ r c',
      Dpre r c' =
        ((Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS (rowRep pG Nfloor r))
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) (rowRep pG Nfloor r)))
            = CopiedDstar.dstarRankGA_m P hV mS (rowRep pG Nfloor r))).image
          (fun k => k + 3))
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hm : 1 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (n k p : ℕ) (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hrmem : k ∈ rowDpre (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c')
    (hguard : ((copiedSlice mS n)[p]? = some U
        ∧ ∀ q, q < (copiedSlice mS n).length → q < p →
            (copiedSlice mS n)[q]? = some U)
      ∧ ((copiedSlice mS n)[p + k]? = some D
        ∧ ∀ q, q < p + k → (copiedSlice mS n)[q]? ≠ some D)) :
    P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  let rcls : Fin pG := rowClass hpG (n % pG)
  have hGrep :
      CopiedAchSetFold.domDp P mS (rowRep pG Nfloor rcls) :=
    domDp_rowClass_rowRep_of_actual_of_floor P hpG hpDomN hpDpN hpDomN_dvd hpDpN_dvd
      hDomN hDpN hm hNDom_floor hNDp_floor hn_floor hG
  have hmod : n % p0 = rowRep pG Nfloor rcls % p0 :=
    (repN_rowClass_mod_of_dvd hpG hp0dvd (fun r : Fin pG => rowRep_modEq r) n).symm
  have hsets := hN n (rowRep pG Nfloor rcls)
    (le_trans hN_floor hn_floor)
    (le_trans hN_floor (rowRep_ge_floor hpG rcls))
    (le_trans hB_floor hn_floor)
    (le_trans hB_floor (rowRep_ge_floor hpG rcls))
    hmod hG hGrep
  have hrow :
      rowDpre (Q := Q) hpG
          (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
            S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c'
        = Dpre rcls c' := by
    dsimp [rcls]
    exact rowDpre_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp
      j0F mS (rowRep pG Nfloor) S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre (n % pG) c'
  have hk_rep :
      k ∈ ((Finset.range (Ndeep c')).filter (fun k =>
        P.rank c' (copiedSlice mS (rowRep pG Nfloor rcls))
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mixedPosAt
                (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                mS (B + 1) (rowRep pG Nfloor rcls)))
          = CopiedDstar.dstarRankGA_m P hV mS (rowRep pG Nfloor rcls))).image
        (fun k => k + 3) := by
    rw [hrow, hDpreRow rcls c'] at hrmem
    exact hrmem
  obtain ⟨k0, hk0rep, hk0eq⟩ := Finset.mem_image.mp hk_rep
  subst k
  have hk0_mem :
      k0 ∈ (Finset.range (Ndeep c')).filter (fun k =>
        P.rank c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mixedPosAt
                (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                mS (B + 1) n))
          = CopiedDstar.dstarRankGA_m P hV mS n) := by
    rw [hsets]
    exact hk0rep
  have hactive0 := (Finset.mem_filter.mp hk0_mem).2
  have hshift : k0 + 3 - 2 = k0 + 1 := by omega
  have hp_eq :
      p = mixedPosAt (Sum.inr (Sum.inr (k0 + 3 - 2)) :
          CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS (B + 1) n :=
    CopiedBoundedGateBand.deepPre_beforeFirstD_mixedPosAt (B := B) mS n (B + 1)
      p (k0 + 3) hm hn (by omega) hguard.2
  rw [hp_eq]
  simpa [hshift] using hactive0

/-- Forward bridge hook for a genuine update-tuple deep-suffix row. -/
theorem ord_update_deep_suffix_of_rowDsuf_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (hDsufRow : ∀ r c',
      Dsuf r c' =
        (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS (rowRep pG Nfloor r))
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) (rowRep pG Nfloor r)))
            = CopiedDstar.dstarRankGA_m P hV mS (rowRep pG Nfloor r)))
    {c : Fin P.toPoly.K} (ī : Fin (P.toPoly.arity c) → ℕ)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hm : 1 ≤ mS) (hNdeep_add2 : Ndeep c' + 2 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (n k p : ℕ)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hall : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    (hrmem : k ∈ rowDsuf (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c')
    (hp : p < (copiedSlice mS n).length)
    (hguard : ((copiedSlice mS n)[p]? = some D
        ∧ ∀ q, q < (copiedSlice mS n).length → p < q →
            (copiedSlice mS n)[q]? = some D)
      ∧ p + 1 + k = (copiedSlice mS n).length)
    (hsel : P.toPoly.sel c' (copiedSlice mS n)
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p))
    (hlabel : P.toPoly.label c' (copiedSlice mS n)
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p) = D) :
    P.toPoly.ord c c' (copiedSlice mS n) ī
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p) := by
  have hrank :=
    rank_update_deep_suffix_of_rowDsuf_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN) (NDomN := NDomN)
      (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts Tp j0F mS S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre hDsufRow c' N hN
      hm hNdeep_add2 hN_floor hNDom_floor hNDp_floor hB_floor n k p hn_floor hG
      hrmem hguard
  have hxbval :
      ∀ i, (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p) i
        < (copiedSlice mS n).length := by
    intro i
    by_cases hi : i = j0F c'
    · subst i
      simp [Function.update, hp]
    · simp [Function.update, hi]
      rw [length_copiedSlice]
      omega
  exact ord_of_tie_hall_rank (P := P) (hV := hV) hall hxbval hsel hlabel hrank

/-- Prefix twin of `ord_update_deep_suffix_of_rowDsuf_rowRep_floor`. -/
theorem ord_update_deep_prefix_of_rowDpre_rowRep_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (hDpreRow : ∀ r c',
      Dpre r c' =
        ((Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS (rowRep pG Nfloor r))
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) (rowRep pG Nfloor r)))
            = CopiedDstar.dstarRankGA_m P hV mS (rowRep pG Nfloor r))).image
          (fun k => k + 3))
    {c : Fin P.toPoly.K} (ī : Fin (P.toPoly.arity c) → ℕ)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hm : 1 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (n k p : ℕ) (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hall : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    (hrmem : k ∈ rowDpre (Q := Q) hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG) c')
    (hp : p < (copiedSlice mS n).length)
    (hguard : ((copiedSlice mS n)[p]? = some U
        ∧ ∀ q, q < (copiedSlice mS n).length → q < p →
            (copiedSlice mS n)[q]? = some U)
      ∧ ((copiedSlice mS n)[p + k]? = some D
        ∧ ∀ q, q < p + k → (copiedSlice mS n)[q]? ≠ some D))
    (hsel : P.toPoly.sel c' (copiedSlice mS n)
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p))
    (hlabel : P.toPoly.label c' (copiedSlice mS n)
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p) = D) :
    P.toPoly.ord c c' (copiedSlice mS n) ī
      (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p) := by
  have hrank :=
    rank_update_deep_prefix_of_rowDpre_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN) (NDomN := NDomN)
      (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts Tp j0F mS S1 F2 Dsuf Dpre hS1 hF2 hDsuf hDpre hDpreRow c' N hN
      hm hN_floor hNDom_floor hNDp_floor hB_floor n k p hn hn_floor hG hrmem hguard
  have hxbval :
      ∀ i, (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') p) i
        < (copiedSlice mS n).length := by
    intro i
    by_cases hi : i = j0F c'
    · subst i
      simp [Function.update, hp]
    · simp [Function.update, hi]
      rw [length_copiedSlice]
      omega
  exact ord_of_tie_hall_rank (P := P) (hV := hV) hall hxbval hsel hlabel hrank

/-- Fully update-shaped semantic condition recognized by the finite row-index
bridge gate.  Both run-band and deep-boundary clauses range over one moving
distinguished coordinate of the fixed base tuple. -/
def bridgeUpdateDeepGateCond (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (B Bh M mthr pG q_U q_D Q : ℕ) (Ndeep : Fin P.toPoly.K → ℕ)
    (hpG : 1 ≤ pG) (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (ī0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c') → ℕ)
    (rN mS n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ) : Prop :=
  P.toPoly.sel c (copiedSlice mS n) ī
    ∧ P.toPoly.label c (copiedSlice mS n) ī = U
    ∧ (∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        CopiedTieGate.cfgCellGAFL B Bh M mthr
          (rowS1Odd hpG idx rN) (fun _ _ => ∅) (fun _ _ => ∅)
          (fun _ _ => ∅) (rowF2Odd hpG idx rN) (fun _ _ => ∅) mS n b →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    ∧ (∀ (c' : Fin P.toPoly.K) (r : ℕ), r ∈ rowSsuf hpG idx rN c' →
        ∀ p, p < (copiedSlice mS n).length →
          (CopiedBandRunGate.updateSufBandGuard (copiedSlice mS n) Q r (q_D + 2) p
            ∧ P.toPoly.sel c' (copiedSlice mS n)
                (Function.update (ī0F c') (j0F c') p)
            ∧ P.toPoly.label c' (copiedSlice mS n)
                (Function.update (ī0F c') (j0F c') p) = D) →
          P.toPoly.ord c c' (copiedSlice mS n) ī
            (Function.update (ī0F c') (j0F c') p))
    ∧ (∀ (c' : Fin P.toPoly.K) (r : ℕ), r ∈ rowSpre hpG idx rN c' →
        ∀ p, p < (copiedSlice mS n).length →
          (CopiedBandRunGate.preBandStrictGuard (copiedSlice mS n) Q r q_U p
            ∧ P.toPoly.sel c' (copiedSlice mS n)
                (Function.update (ī0F c') (j0F c') p)
            ∧ P.toPoly.label c' (copiedSlice mS n)
                (Function.update (ī0F c') (j0F c') p) = D) →
          P.toPoly.ord c c' (copiedSlice mS n) ī
            (Function.update (ī0F c') (j0F c') p))
    ∧ (∀ (c' : Fin P.toPoly.K) (k : ℕ), k ∈ rowDsuf hpG idx rN c' →
        ∀ p, p < (copiedSlice mS n).length →
          ((((copiedSlice mS n)[p]? = some D
                ∧ ∀ q, q < (copiedSlice mS n).length → p < q →
                    (copiedSlice mS n)[q]? = some D)
              ∧ p + 1 + k = (copiedSlice mS n).length)
            ∧ P.toPoly.sel c' (copiedSlice mS n)
                (Function.update (ī0F c') (j0F c') p)
            ∧ P.toPoly.label c' (copiedSlice mS n)
                (Function.update (ī0F c') (j0F c') p) = D) →
          P.toPoly.ord c c' (copiedSlice mS n) ī
            (Function.update (ī0F c') (j0F c') p))
    ∧ (∀ (c' : Fin P.toPoly.K) (k : ℕ), k ∈ rowDpre hpG idx rN c' →
        ∀ p, p < (copiedSlice mS n).length →
          ((((copiedSlice mS n)[p]? = some U
                ∧ ∀ q, q < (copiedSlice mS n).length → q < p →
                    (copiedSlice mS n)[q]? = some U)
              ∧ ((copiedSlice mS n)[p + k]? = some D
                ∧ ∀ q, q < p + k → (copiedSlice mS n)[q]? ≠ some D))
            ∧ P.toPoly.sel c' (copiedSlice mS n)
                (Function.update (ī0F c') (j0F c') p)
            ∧ P.toPoly.label c' (copiedSlice mS n)
                (Function.update (ī0F c') (j0F c') p) = D) →
          P.toPoly.ord c c' (copiedSlice mS n) ī
            (Function.update (ī0F c') (j0F c') p))

/-- Fully update-shaped row-indexed bridge gate family.  This version uses
update-tuple clauses for both middle run bands and deep boundary offsets. -/
theorem bridgeUpdateDeepRowIndex_gate_family (P : WRP.Presentation Step Step)
    (B Bh M mthr pG q_U q_D Q : ℕ) (Ndeep : Fin P.toPoly.K → ℕ)
    (hpG : 1 ≤ pG) (hQ : 0 < Q) (hBB : B ≤ Bh) (hBh1 : 1 ≤ Bh)
    (hM2 : M % 2 = 0)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (ī0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c') → ℕ) :
    ∃ (GdfaF : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep → ℕ →
        (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))),
      ∀ (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep) (rN : ℕ)
        (c : Fin P.toPoly.K) (mS n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ),
        q_U < mS → q_D < mS → Bh ≤ n →
        (∀ i, ī i < (copiedSlice mS n).length) →
        (∀ c' i, ī0F c' i < (copiedSlice mS n).length) →
        (bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG idx j0F ī0F
            rN mS n ī
          ↔ (GdfaF idx rN c).accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)) := by
  classical
  choose GdfaF hGdfa using fun
      (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep) (rN : ℕ)
      (c : Fin P.toPoly.K) =>
    CopiedBoundedGateBand.fasU_atomOrd_full_gate_bounded_band_updateDeep P c B Bh M mthr q_U q_D
      (q_D + 2) q_U
      (rowS1Odd hpG idx rN) (fun _ _ => ∅) (fun _ _ => ∅)
      (fun _ _ => ∅) (rowF2Odd hpG idx rN) (fun _ _ => ∅)
      (rowSsuf hpG idx rN) (rowSpre hpG idx rN)
      (rowDsuf hpG idx rN) (rowDpre hpG idx rN) j0F ī0F Q hQ
      (fun c' r hr => rowSsuf_mem_lt hpG idx rN c' hr)
      (fun c' r hr => rowSpre_mem_lt hpG idx rN c' hr)
      hBB hBh1 hM2
      (by
        intro c' rs r hr
        rw [rowS1Odd] at hr
        exact ⟨rowS1_mem_lt hpG idx rN c' rs (Finset.mem_filter.mp hr).1,
          (Finset.mem_filter.mp hr).2⟩)
      (fun c' rs r hr => absurd hr (Finset.notMem_empty r))
      (fun c' rs f hf => absurd hf (Finset.notMem_empty f))
      (by
        intro c' rs f hf
        rw [rowF2Odd] at hf
        exact (Finset.mem_filter.mp hf).2)
      (fun c' rs k hk => absurd hk (Finset.notMem_empty k))
      (fun c' rs k hk => absurd hk (Finset.notMem_empty k))
      (by intro c' rs hb; simp [rowS1Odd, rowS1, hb])
      (fun c' rs _ => rfl)
      (fun c' rs _ => rfl)
      (fun c' rs _ => rfl)
      (by intro c' rs hb; simp [rowF2Odd, rowF2, hb])
      (fun c' rs _ => rfl)
  refine ⟨GdfaF, ?_⟩
  intro idx rN c mS n ī hqU hqD hBh hval hbase
  exact hGdfa idx rN c mS n ī hqU hqD hBh hval hbase

/-- Zero-base specialization of `bridgeUpdateDeepRowIndex_gate_family`. -/
theorem bridgeUpdateDeepRowIndex_gate_family_zeroBase (P : WRP.Presentation Step Step)
    (B Bh M mthr pG q_U q_D Q : ℕ) (Ndeep : Fin P.toPoly.K → ℕ)
    (hpG : 1 ≤ pG) (hQ : 0 < Q) (hBB : B ≤ Bh) (hBh1 : 1 ≤ Bh)
    (hM2 : M % 2 = 0)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c')) :
    ∃ (GdfaF : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep → ℕ →
        (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))),
      ∀ (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep) (rN : ℕ)
        (c : Fin P.toPoly.K) (mS n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ),
        q_U < mS → q_D < mS → Bh ≤ n →
        (∀ i, ī i < (copiedSlice mS n).length) →
        (bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG idx j0F
            (fun _ _ => 0) rN mS n ī
          ↔ (GdfaF idx rN c).accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)) := by
  classical
  obtain ⟨GdfaF, hGdfa⟩ :=
    bridgeUpdateDeepRowIndex_gate_family P B Bh M mthr pG q_U q_D Q Ndeep
      hpG hQ hBB hBh1 hM2 j0F (fun _ _ => 0)
  refine ⟨GdfaF, ?_⟩
  intro idx rN c mS n ī hqU hqD hBh hval
  refine hGdfa idx rN c mS n ī hqU hqD hBh hval ?_
  intro c' i
  rw [length_copiedSlice]
  omega

/-- Transport a core/frozen cfg fact from an update row index back to the
selector tables at the actual residue.  The run/deep tables are empty in this
cfg shape, so only the bounded bulk/frozen rows need rewriting. -/
theorem selector_cfgCellGAFL_of_updateRow_cfgCellGAFL
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG pSel q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    (hpG : 1 ≤ pG) (hpSel_dvd : pSel ∣ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1tab : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2tab : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1tab r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (hS1odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1)
    (hF2odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1)
    (S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1)
    (hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1)
    {n : ℕ} {b : P.toPoly.Atom}
    (hcfg : CopiedTieGate.cfgCellGAFL B Bh M mthr
      (rowS1Odd (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
          S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG))
      (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅)
      (rowF2Odd (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
          S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG))
      (fun _ _ => ∅) mS n b) :
    CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
      (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
      (fun _ _ => ∅) mS n b := by
  classical
  have hrowClass_mod_pSel :
      (rowClass hpG (n % pG)).1 % pSel = n % pSel :=
    rowClass_mod_of_dvd hpG hpSel_dvd n
  rcases hcfg with hbulk | hfrozen
  · left
    rcases hbulk with ⟨rs, t, hvalid, htn, hcell, hpos⟩
    refine ⟨rs, t, hvalid, htn, hcell, ?_⟩
    rcases hpos with ⟨hwin, hinner⟩
    refine ⟨hwin, ?_⟩
    rcases hinner with hres | hfront | hback
    · rcases hres with ⟨hlo, hhi, r, hr, hmod⟩
      left
      refine ⟨hlo, hhi, r, ?_, hmod⟩
      by_cases hbnd :
          rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity b.1) q_U q_D
      · have hrow :
            rowS1Odd (Q := Q) hpG
                (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
                  S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre)
                (n % pG) b.1 rs =
              S1tab (rowClass hpG (n % pG)) ⟨b.1, ⟨rs, hbnd⟩⟩ :=
          rowS1Odd_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp
            j0F mS repN S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre hS1odd
            (n % pG) b.1 rs hbnd
        rw [hrow] at hr
        rw [hS1tab_eq (rowClass hpG (n % pG)) ⟨b.1, ⟨rs, hbnd⟩⟩] at hr
        simpa [hrowClass_mod_pSel] using hr
      · exfalso
        have hrow :
            rowS1Odd (Q := Q) hpG
                (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
                  S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre)
                (n % pG) b.1 rs = ∅ :=
          rowS1Odd_mkBridgeUpdateRowIndex_notMem (hV := hV) (Q := Q) hpG pcF Ts Tp
            j0F mS repN S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre
            (n % pG) b.1 rs hbnd
        rw [hrow] at hr
        exact Finset.notMem_empty r hr
    · exfalso
      rcases hfront with ⟨f, hf, _⟩
      exact Finset.notMem_empty f hf
    · exfalso
      rcases hback with ⟨k, hk, _⟩
      exact Finset.notMem_empty k hk
  · right
    rcases hfrozen with ⟨rs, t, hvalid, htn, hcell, hpos⟩
    refine ⟨rs, t, hvalid, htn, hcell, ?_⟩
    rcases hpos with ⟨hwin, hinner⟩
    refine ⟨hwin, ?_⟩
    rcases hinner with hres | hfront | hback
    · exfalso
      rcases hres with ⟨_, _, r, hr, _⟩
      exact Finset.notMem_empty r hr
    · rcases hfront with ⟨f, hf, hcase⟩
      right
      left
      refine ⟨f, ?_, hcase⟩
      by_cases hbnd :
          rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity b.1) q_U q_D
      · have hrow :
            rowF2Odd (Q := Q) hpG
                (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
                  S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre)
                (n % pG) b.1 rs =
              F2tab (rowClass hpG (n % pG)) ⟨b.1, ⟨rs, hbnd⟩⟩ :=
          rowF2Odd_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp
            j0F mS repN S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre hF2odd
            (n % pG) b.1 rs hbnd
        rw [hrow] at hf
        rw [hF2tab_eq (rowClass hpG (n % pG)) ⟨b.1, ⟨rs, hbnd⟩⟩] at hf
        simpa [hrowClass_mod_pSel] using hf
      · exfalso
        have hrow :
            rowF2Odd (Q := Q) hpG
                (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
                  S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre)
                (n % pG) b.1 rs = ∅ :=
          rowF2Odd_mkBridgeUpdateRowIndex_notMem (hV := hV) (Q := Q) hpG pcF Ts Tp
            j0F mS repN S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre
            (n % pG) b.1 rs hbnd
        rw [hrow] at hf
        exact Finset.notMem_empty f hf
    · exfalso
      rcases hback with ⟨k, hk, _⟩
      exact Finset.notMem_empty k hk

/-- Forward core/frozen gate hook for the direct update bridge: transport the
cfg fact from the update row index back to selector tables, use the selector
callback to recover rank `d*`, then discharge the order goal with `hall`. -/
theorem ord_core_of_updateRow_cfgCellGAFL
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG pSel q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    (hpG : 1 ≤ pG) (hpSel_dvd : pSel ∣ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1tab : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2tab : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1tab r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (hS1odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1)
    (hF2odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1)
    (S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1)
    (hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    {b : P.toPoly.Atom}
    (hall : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    (hcfgRank : P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
        (fun _ _ => ∅) mS n b →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n)
    (hbsel : P.toPoly.selectedAtom (copiedSlice mS n) b)
    (hbD : P.toPoly.labelOf (copiedSlice mS n) b = D)
    (hcfg : CopiedTieGate.cfgCellGAFL B Bh M mthr
      (rowS1Odd (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
          S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG))
      (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅)
      (rowF2Odd (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
          S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG))
      (fun _ _ => ∅) mS n b) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b := by
  have hcfgSel :
      CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
        (fun _ _ => ∅) mS n b :=
    selector_cfgCellGAFL_of_updateRow_cfgCellGAFL (hV := hV) (Q := Q)
      hpG hpSel_dvd pcF Ts Tp j0F mS repN S1tab F2tab Dsuf Dpre
      hS1 hF2 hDsuf hDpre hS1odd hF2odd S1L F2L hS1tab_eq hF2tab_eq hcfg
  exact hall b hbsel hbD (hcfgRank hbsel hbD hcfgSel)

/-- The fully update-shaped bridge gate condition from a canonical row: the deep
rows and deep periodicity hypotheses are measured on the one-coordinate update
tuples. -/
theorem bridgeUpdateDeepGateCond_of_updateDeepRow_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG pSel q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hQdvd : Q ∣ pG)
    (hpSel_dvd : pSel ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hSound : CopiedBoundedGateBand.BandedUpdateRankSoundness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1tab : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2tab : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1tab r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (hS1odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1)
    (hF2odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1)
    (hDsufRow : ∀ r c',
      Dsuf r c' =
        (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS (rowRep pG Nfloor r))
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) (rowRep pG Nfloor r)))
            = CopiedDstar.dstarRankGA_m P hV mS (rowRep pG Nfloor r)))
    (hDpreRow : ∀ r c',
      Dpre r c' =
        ((Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS (rowRep pG Nfloor r))
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) (rowRep pG Nfloor r)))
            = CopiedDstar.dstarRankGA_m P hV mS (rowRep pG Nfloor r))).image
          (fun k => k + 3))
    (S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1)
    (hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1)
    (NSuf NPre NDSuf NDPre : Fin P.toPoly.K → ℕ)
    (hNSuf : ∀ c' n n', NSuf c' ≤ n → NSuf c' ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hNPre : ∀ c' n n', NPre c' ≤ n → NPre c' ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hNDSuf : ∀ c' n n', NDSuf c' ≤ n → NDSuf c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hNDPre : ∀ c' n n', NDPre c' ≤ n → NDPre c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (Fs Fp : (c' : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hselU : P.toPoly.sel c (copiedSlice mS n) ī)
    (hlabelU : P.toPoly.label c (copiedSlice mS n) ī = U)
    (hall : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    (hcfgRank : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
        (fun _ _ => ∅) mS n b →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n)
    (hpcF : ∀ c' : Fin P.toPoly.K, 1 ≤ pcF c')
    (hQpos : 0 < Q) (hpcQ : ∀ c' : Fin P.toPoly.K, pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hTs_le_qD : ∀ c' : Fin P.toPoly.K, Ts c' ≤ q_D)
    (hTp_le_qU : ∀ c' : Fin P.toPoly.K, Tp c' ≤ q_U)
    (hSufBand : ∀ c' : Fin P.toPoly.K, Ts c' + 2 * pcF c' ≤ mS - 1)
    (hPreBand : ∀ c' : Fin P.toPoly.K, Tp c' + 2 * pcF c' ≤ mS - 1)
    (hNdeep_add2 : ∀ c' : Fin P.toPoly.K, Ndeep c' + 2 ≤ mS)
    (hNSuf_floor : ∀ c' : Fin P.toPoly.K, NSuf c' ≤ Nfloor)
    (hNPre_floor : ∀ c' : Fin P.toPoly.K, NPre c' ≤ Nfloor)
    (hNDSuf_floor : ∀ c' : Fin P.toPoly.K, NDSuf c' ≤ Nfloor)
    (hNDPre_floor : ∀ c' : Fin P.toPoly.K, NDPre c' ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hFs : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Ts c') (pcF c') (Fs c'))
    (hFp : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Tp c') (pcF c') (Fp c'))
    (hags : ∀ c' l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = Fs c' l)
    (hagp : ∀ c' l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
          = Fp c' l) :
    bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre)
      j0F (fun _ _ => 0) (n % pG) mS n ī := by
  refine ⟨hselU, hlabelU, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hbsel hbD hcfg
    exact ord_core_of_updateRow_cfgCellGAFL (hV := hV) (mthr := mthr) (Q := Q)
      hpG hpSel_dvd pcF Ts Tp j0F mS (rowRep pG Nfloor)
      S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre hS1odd hF2odd
      S1L F2L hS1tab_eq hF2tab_eq (n := n) (c := c) (ī := ī) (b := b)
      hall (hcfgRank b) hbsel hbD hcfg
  · intro c' r hrmem p hp hcond
    rcases hcond with ⟨hguard, hselD, hlabelD⟩
    exact ord_update_suffix_of_rowSsuf_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN) (NDomN := NDomN)
      (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hQdvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN hSound
      pcF Ts Tp j0F mS S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre
      (c := c) ī c' (NSuf c') (hNSuf c') (hpcF c') hQpos (hpcQ c')
      hm (hSufBand c') (hNSuf_floor c') hNDom_floor hNDp_floor
      n (q_D + 2) r p (Fs c') hn hn_floor hG (by omega)
      (by have := hTs_le_qD c'; omega) (hFs c') (hags c') hall hrmem hp
      hguard hselD hlabelD
  · intro c' r hrmem p hp hcond
    rcases hcond with ⟨hguard, hselD, hlabelD⟩
    exact ord_update_prefix_of_rowSpre_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN) (NDomN := NDomN)
      (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN hSound
      pcF Ts Tp j0F mS S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre
      (c := c) ī c' (NPre c') (hNPre c') (hpcF c') hQpos (hpcQ c')
      hm (hPreBand c') (hNPre_floor c') hNDom_floor hNDp_floor
      n q_U r p (Fp c') hn hn_floor hG (hTp_le_qU c') (hFp c') (hagp c') hall
      hrmem hp hguard hselD hlabelD
  · intro c' k hkmem p hp hcond
    rcases hcond with ⟨hguard, hselD, hlabelD⟩
    exact ord_update_deep_suffix_of_rowDsuf_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN) (NDomN := NDomN)
      (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts Tp j0F mS S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre
      hDsufRow (c := c) ī c' (NDSuf c') (hNDSuf c')
      hm (hNdeep_add2 c') (hNDSuf_floor c') hNDom_floor hNDp_floor hB_floor
      n k p hn_floor hG hall hkmem hp hguard hselD hlabelD
  · intro c' k hkmem p hp hcond
    rcases hcond with ⟨hguard, hselD, hlabelD⟩
    exact ord_update_deep_prefix_of_rowDpre_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN) (NDomN := NDomN)
      (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts Tp j0F mS S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre
      hDpreRow (c := c) ī c' (NDPre c') (hNDPre c')
      hm (hNDPre_floor c') hNDom_floor hNDp_floor hB_floor n k p hn hn_floor hG
      hall hkmem hp hguard hselD hlabelD

/-- Canonical deep-row specialization of
`bridgeUpdateDeepGateCond_of_updateDeepRow_floor`.  The row index stores the
named update-tuple deep tables. -/
theorem bridgeUpdateDeepGateCond_of_updateDeepRow_floor_canonicalRows
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG pSel q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hQdvd : Q ∣ pG)
    (hpSel_dvd : pSel ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hSound : CopiedBoundedGateBand.BandedUpdateRankSoundness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1tab : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2tab : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1tab r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2)
    (hS1odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1)
    (hF2odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1)
    (S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1)
    (hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1)
    (NSuf NPre NDSuf NDPre : Fin P.toPoly.K → ℕ)
    (hNSuf : ∀ c' n n', NSuf c' ≤ n → NSuf c' ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hNPre : ∀ c' n n', NPre c' ≤ n → NPre c' ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hNDSuf : ∀ c' n n', NDSuf c' ≤ n → NDSuf c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hNDPre : ∀ c' n n', NDPre c' ≤ n → NDPre c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (Fs Fp : (c' : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hselU : P.toPoly.sel c (copiedSlice mS n) ī)
    (hlabelU : P.toPoly.label c (copiedSlice mS n) ī = U)
    (hall : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    (hcfgRank : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
        (fun _ _ => ∅) mS n b →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n)
    (hpcF : ∀ c' : Fin P.toPoly.K, 1 ≤ pcF c')
    (hQpos : 0 < Q) (hpcQ : ∀ c' : Fin P.toPoly.K, pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hTs_le_qD : ∀ c' : Fin P.toPoly.K, Ts c' ≤ q_D)
    (hTp_le_qU : ∀ c' : Fin P.toPoly.K, Tp c' ≤ q_U)
    (hSufBand : ∀ c' : Fin P.toPoly.K, Ts c' + 2 * pcF c' ≤ mS - 1)
    (hPreBand : ∀ c' : Fin P.toPoly.K, Tp c' + 2 * pcF c' ≤ mS - 1)
    (hNdeep_add2 : ∀ c' : Fin P.toPoly.K, Ndeep c' + 2 ≤ mS)
    (hNSuf_floor : ∀ c' : Fin P.toPoly.K, NSuf c' ≤ Nfloor)
    (hNPre_floor : ∀ c' : Fin P.toPoly.K, NPre c' ≤ Nfloor)
    (hNDSuf_floor : ∀ c' : Fin P.toPoly.K, NDSuf c' ≤ Nfloor)
    (hNDPre_floor : ∀ c' : Fin P.toPoly.K, NDPre c' ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hFs : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Ts c') (pcF c') (Fs c'))
    (hFp : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Tp c') (pcF c') (Fp c'))
    (hags : ∀ c' l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = Fs c' l)
    (hagp : ∀ c' l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
          = Fp c' l) :
    bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1tab F2tab
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor) (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor) (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī := by
  exact bridgeUpdateDeepGateCond_of_updateDeepRow_floor
    (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
    (pG := pG) (pSel := pSel) (q_U := q_U) (q_D := q_D) (Q := Q)
    (Ndeep := Ndeep) (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
    (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
    hpG hp0dvd hQdvd hpSel_dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN hSound
    pcF Ts Tp j0F mS S1tab F2tab
    (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
    (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
    hS1 hF2
    (fun r c' x hx => updateDeepDsufRowTable_mem_lt
      (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor) (r := r) (c' := c') (k := x) hx)
    (fun r c' x hx => updateDeepDpreRowTable_mem_lt
      (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor) (r := r) (c' := c') (k := x) hx)
    hS1odd hF2odd (by intro r c'; rfl) (by intro r c'; rfl)
    S1L F2L hS1tab_eq hF2tab_eq NSuf NPre NDSuf NDPre hNSuf hNPre hNDSuf hNDPre
    Fs Fp hselU hlabelU hall hcfgRank hpcF hQpos hpcQ hm hn hn_floor hG
    hTs_le_qD hTp_le_qU hSufBand hPreBand hNdeep_add2
    hNSuf_floor hNPre_floor hNDSuf_floor hNDPre_floor hNDom_floor hNDp_floor hB_floor
    hFs hFp hags hagp

/-- Forward automaton hook for the fully update-shaped canonical rows.  This
packages the common composition of
`bridgeUpdateDeepGateCond_of_updateDeepRow_floor_canonicalRows` with the
zero-base update-deep gate family: once the row-representative tables discharge
all semantic row clauses, the finite DFA accepts the marked copied slice. -/
theorem bridgeUpdateDeep_accepts_rank_of_updateDeepRow_floor_canonicalRows
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG pSel q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hQdvd : Q ∣ pG)
    (hpSel_dvd : pSel ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hSound : CopiedBoundedGateBand.BandedUpdateRankSoundness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1tab : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2tab : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1tab r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2)
    (hS1odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1)
    (hF2odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1)
    (S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1)
    (hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1)
    (NSuf NPre NDSuf NDPre : Fin P.toPoly.K → ℕ)
    (hNSuf : ∀ c' n n', NSuf c' ≤ n → NSuf c' ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hNPre : ∀ c' n n', NPre c' ≤ n → NPre c' ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hNDSuf : ∀ c' n n', NDSuf c' ≤ n → NDSuf c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hNDPre : ∀ c' n n', NDPre c' ≤ n → NDPre c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (Fs Fp : (c' : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (GdfaF : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep → ℕ →
      (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hGdfa : ∀ (idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep) (rN : ℕ)
        (c : Fin P.toPoly.K) (mS n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ),
        q_U < mS → q_D < mS → Bh ≤ n →
        (∀ i, ī i < (copiedSlice mS n).length) →
        (bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG idx j0F
            (fun _ _ => 0) rN mS n ī
          ↔ (GdfaF idx rN c).accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)))
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hselU : P.toPoly.sel c (copiedSlice mS n) ī)
    (hlabelU : P.toPoly.label c (copiedSlice mS n) ī = U)
    (hrank : P.rankOf (copiedSlice mS n) ⟨c, ī⟩ =
      CopiedDstar.dstarRankGA_m P hV mS n)
    (hall : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    (hcfgRank : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
        (fun _ _ => ∅) mS n b →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n)
    (hpcF : ∀ c' : Fin P.toPoly.K, 1 ≤ pcF c')
    (hQpos : 0 < Q) (hpcQ : ∀ c' : Fin P.toPoly.K, pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hTs_le_qD : ∀ c' : Fin P.toPoly.K, Ts c' ≤ q_D)
    (hTp_le_qU : ∀ c' : Fin P.toPoly.K, Tp c' ≤ q_U)
    (hSufBand : ∀ c' : Fin P.toPoly.K, Ts c' + 2 * pcF c' ≤ mS - 1)
    (hPreBand : ∀ c' : Fin P.toPoly.K, Tp c' + 2 * pcF c' ≤ mS - 1)
    (hNdeep_add2 : ∀ c' : Fin P.toPoly.K, Ndeep c' + 2 ≤ mS)
    (hNSuf_floor : ∀ c' : Fin P.toPoly.K, NSuf c' ≤ Nfloor)
    (hNPre_floor : ∀ c' : Fin P.toPoly.K, NPre c' ≤ Nfloor)
    (hNDSuf_floor : ∀ c' : Fin P.toPoly.K, NDSuf c' ≤ Nfloor)
    (hNDPre_floor : ∀ c' : Fin P.toPoly.K, NDPre c' ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hFs : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Ts c') (pcF c') (Fs c'))
    (hFp : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Tp c') (pcF c') (Fp c'))
    (hags : ∀ c' l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = Fs c' l)
    (hagp : ∀ c' l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
          = Fp c' l)
    (hqU_lt : q_U < mS) (hqD_lt : q_D < mS) (hBh_n : Bh ≤ n)
    (hval : ∀ i, ī i < (copiedSlice mS n).length) :
    (GdfaF
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
          S1tab F2tab
          (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
          (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
          hS1 hF2
          (fun r c' x hx => updateDeepDsufRowTable_mem_lt
            (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
            (r := r) (c' := c') (k := x) hx)
          (fun r c' x hx => updateDeepDpreRowTable_mem_lt
            (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
            (r := r) (c' := c') (k := x) hx))
        (n % pG) c).accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)
      ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ =
          CopiedDstar.dstarRankGA_m P hV mS n := by
  have hgate :
      bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
          S1tab F2tab
          (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
          (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
          hS1 hF2
          (fun r c' x hx => updateDeepDsufRowTable_mem_lt
            (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
            (r := r) (c' := c') (k := x) hx)
          (fun r c' x hx => updateDeepDpreRowTable_mem_lt
            (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
            (r := r) (c' := c') (k := x) hx))
        j0F (fun _ _ => 0) (n % pG) mS n ī :=
    bridgeUpdateDeepGateCond_of_updateDeepRow_floor_canonicalRows
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
      (pG := pG) (pSel := pSel) (q_U := q_U) (q_D := q_D) (Q := Q)
      (Ndeep := Ndeep) (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hQdvd hpSel_dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd
      hDomN hDpN hSound pcF Ts Tp j0F mS S1tab F2tab hS1 hF2 hS1odd hF2odd
      S1L F2L hS1tab_eq hF2tab_eq NSuf NPre NDSuf NDPre
      hNSuf hNPre hNDSuf hNDPre Fs Fp hselU hlabelU hall hcfgRank
      hpcF hQpos hpcQ hm hn hn_floor hG hTs_le_qD hTp_le_qU hSufBand hPreBand
      hNdeep_add2 hNSuf_floor hNPre_floor hNDSuf_floor hNDPre_floor
      hNDom_floor hNDp_floor hB_floor hFs hFp hags hagp
  refine ⟨?_, hrank⟩
  exact (hGdfa
    (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
      S1tab F2tab
      (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
      (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
      hS1 hF2
      (fun r c' x hx => updateDeepDsufRowTable_mem_lt
        (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
        (r := r) (c' := c') (k := x) hx)
      (fun r c' x hx => updateDeepDpreRowTable_mem_lt
        (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
        (r := r) (c' := c') (k := x) hx))
    (n % pG) c mS n ī hqU_lt hqD_lt hBh_n hval).mp hgate

/-- Reverse transport for the core/frozen cfg branch: a selector-table cfg fact
can be replayed against an update row index whenever the supplied boundedness
callbacks show that the tuple rows are present in the finite row index. -/
theorem updateRow_cfgCellGAFL_of_selector_cfgCellGAFL
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG pSel q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    (hpG : 1 ≤ pG) (hpSel_dvd : pSel ∣ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1tab : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2tab : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1tab r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (hS1odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1)
    (hF2odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1)
    (S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1)
    (hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1)
    {n : ℕ} {b : P.toPoly.Atom}
    (hcfg : CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
      (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
      (fun _ _ => ∅) mS n b)
    (hbndB : ∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF B) (t : ℕ),
      (∀ i, (rs i).valid mS) → t < n →
      b.2 = CopiedDstar.cellTupleF rs mS t n →
      CopiedTieGate.cfgPosL M mthr (S1L (n % pSel) b.1 rs) ∅ ∅
        (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
      rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity b.1) q_U q_D)
    (hbndH : ∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF Bh) (t : ℕ),
      (∀ i, (rs i).valid mS) → t < n →
      b.2 = CopiedDstar.cellTupleF rs mS t n →
      CopiedTieGate.cfgPosL M mthr ∅ (F2L (n % pSel) b.1 rs) ∅
        (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
      rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity b.1) q_U q_D) :
    CopiedTieGate.cfgCellGAFL B Bh M mthr
      (rowS1Odd (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
          S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG))
      (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅)
      (rowF2Odd (Q := Q) hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
          S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre) (n % pG))
      (fun _ _ => ∅) mS n b := by
  classical
  have hrowClass_mod_pSel :
      (rowClass hpG (n % pG)).1 % pSel = n % pSel :=
    rowClass_mod_of_dvd hpG hpSel_dvd n
  rcases hcfg with hbulk | hfrozen
  · left
    rcases hbulk with ⟨rs, t, hvalid, htn, hcell, hpos⟩
    have hbnd : rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity b.1) q_U q_D :=
      hbndB rs t hvalid htn hcell hpos
    refine ⟨rs, t, hvalid, htn, hcell, ?_⟩
    rcases hpos with ⟨hwin, hinner⟩
    refine ⟨hwin, ?_⟩
    rcases hinner with hres | hfront | hback
    · rcases hres with ⟨hlo, hhi, r, hrmem, hmod⟩
      left
      refine ⟨hlo, hhi, r, ?_, hmod⟩
      have hrow :
          rowS1Odd (Q := Q) hpG
              (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
                S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre)
              (n % pG) b.1 rs =
            S1tab (rowClass hpG (n % pG)) ⟨b.1, ⟨rs, hbnd⟩⟩ :=
        rowS1Odd_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp
          j0F mS repN S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre hS1odd
          (n % pG) b.1 rs hbnd
      rw [hrow, hS1tab_eq (rowClass hpG (n % pG)) ⟨b.1, ⟨rs, hbnd⟩⟩]
      simpa [hrowClass_mod_pSel] using hrmem
    · exfalso
      rcases hfront with ⟨f, hf, _⟩
      exact Finset.notMem_empty f hf
    · exfalso
      rcases hback with ⟨k, hk, _⟩
      exact Finset.notMem_empty k hk
  · right
    rcases hfrozen with ⟨rs, t, hvalid, htn, hcell, hpos⟩
    have hbnd : rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity b.1) q_U q_D :=
      hbndH rs t hvalid htn hcell hpos
    refine ⟨rs, t, hvalid, htn, hcell, ?_⟩
    rcases hpos with ⟨hwin, hinner⟩
    refine ⟨hwin, ?_⟩
    rcases hinner with hres | hfront | hback
    · exfalso
      rcases hres with ⟨_, _, r, hrmem, _⟩
      exact Finset.notMem_empty r hrmem
    · rcases hfront with ⟨f, hfmem, hcase⟩
      right
      left
      refine ⟨f, ?_, hcase⟩
      have hrow :
          rowF2Odd (Q := Q) hpG
              (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
                S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre)
              (n % pG) b.1 rs =
            F2tab (rowClass hpG (n % pG)) ⟨b.1, ⟨rs, hbnd⟩⟩ :=
        rowF2Odd_mkBridgeUpdateRowIndex (hV := hV) (Q := Q) hpG pcF Ts Tp
          j0F mS repN S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre hF2odd
          (n % pG) b.1 rs hbnd
      rw [hrow, hF2tab_eq (rowClass hpG (n % pG)) ⟨b.1, ⟨rs, hbnd⟩⟩]
      simpa [hrowClass_mod_pSel] using hfmem
    · exfalso
      rcases hback with ⟨k, hk, _⟩
      exact Finset.notMem_empty k hk

/-- Core branch consumer for the fully update-shaped bridge condition: the
core/frozen cfg branch is untouched by the deep rows, so the selector-table
replay discharges the atom order obligation directly. -/
theorem atomOrd_of_bridgeUpdateDeepGateCond_selector_cfg
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG pSel q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    (hpG : 1 ≤ pG) (hpSel_dvd : pSel ∣ pG)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (ī0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c') → ℕ)
    (mS : ℕ) (repN : Fin pG → ℕ)
    (S1tab : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2tab : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (Dsuf Dpre : Fin pG → (c' : Fin P.toPoly.K) → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1tab r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2)
    (hDsuf : ∀ r c' x, x ∈ Dsuf r c' → x < Ndeep c' + 3)
    (hDpre : ∀ r c' x, x ∈ Dpre r c' → x < Ndeep c' + 3)
    (hS1odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1)
    (hF2odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1)
    (S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1)
    (hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    {b : P.toPoly.Atom}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS repN
        S1tab F2tab Dsuf Dpre hS1 hF2 hDsuf hDpre)
      j0F ī0F (n % pG) mS n ī)
    (hbsel : P.toPoly.selectedAtom (copiedSlice mS n) b)
    (hbD : P.toPoly.labelOf (copiedSlice mS n) b = D)
    (hcfg : CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
      (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
      (fun _ _ => ∅) mS n b)
    (hbndB : ∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF B) (t : ℕ),
      (∀ i, (rs i).valid mS) → t < n →
      b.2 = CopiedDstar.cellTupleF rs mS t n →
      CopiedTieGate.cfgPosL M mthr (S1L (n % pSel) b.1 rs) ∅ ∅
        (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
      rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity b.1) q_U q_D)
    (hbndH : ∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF Bh) (t : ℕ),
      (∀ i, (rs i).valid mS) → t < n →
      b.2 = CopiedDstar.cellTupleF rs mS t n →
      CopiedTieGate.cfgPosL M mthr ∅ (F2L (n % pSel) b.1 rs) ∅
        (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
      rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity b.1) q_U q_D) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b := by
  refine hgate.2.2.1 b hbsel hbD ?_
  exact updateRow_cfgCellGAFL_of_selector_cfgCellGAFL (hV := hV) (Q := Q)
    hpG hpSel_dvd pcF Ts Tp j0F mS repN S1tab F2tab Dsuf Dpre
    hS1 hF2 hDsuf hDpre hS1odd hF2odd S1L F2L hS1tab_eq hF2tab_eq
    hcfg hbndB hbndH

/-- Suffix-run slope callback for the fully update-shaped bridge.  The affine
locus supplies the two adjacent activation ranks for the absolute row residue;
activation completeness stores that residue in the canonical update row, and
the suffix clause of `bridgeUpdateDeepGateCond` gives the desired order. -/
theorem atomOrd_update_suffix_slope_of_bridgeUpdateDeepGateCond_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hQdvd : Q ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    {l : ℕ} (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pcF c') (hQpos : 0 < Q) (hpcQ : pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hband : Ts c' + 2 * pcF c' ≤ mS - 1)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = F l)
    (hTs_l : Ts c' ≤ l) (hlm : l < mS - 1) (hqD_l : q_D ≤ l)
    (hslope : ∀ l', Ts c' ≤ l' → l' < mS - 1 →
      (l' - Ts c') % pcF c' = (l - Ts c') % pcF c' →
      F l' = CopiedDstar.dstarRankGA_m P hV mS n)
    (hselD : P.toPoly.sel c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l))
      ∧ P.toPoly.label c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = D) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
      (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)⟩ : P.toPoly.Atom) := by
  set rAbs : ℕ := (mS + 2 * n + 1 + l) % Q with hrAbs_def
  have hrAbsQ : rAbs < Q := by
    rw [hrAbs_def]
    exact Nat.mod_lt _ hQpos
  set ρact : ℕ :=
    (rAbs + Q - ((mS + 2 * n + 1 + Ts c') % Q)) % pcF c' with hρact_def
  have hρact_lt : ρact < pcF c' := by
    rw [hρact_def]
    exact Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hpc)
  have hresloc : ρact = (l - Ts c') % pcF c' := by
    have hres := CopiedSelUniform.runLocalResidue_of_abs_mod
      (Q := Q) (pc := pcF c') (shift := mS + 2 * n + 1)
      (T := Ts c') (l := l) (ρ := rAbs)
      hQpos hpcQ hrAbsQ (by rw [hrAbs_def]) hTs_l
    simpa [ρact, hρact_def] using hres
  have h0F : F (Ts c' + ρact) = CopiedDstar.dstarRankGA_m P hV mS n := by
    apply hslope
    · omega
    · omega
    · rw [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt hρact_lt]
      exact hresloc
  have h1F :
      F (Ts c' + ρact + pcF c') = CopiedDstar.dstarRankGA_m P hV mS n := by
    apply hslope
    · omega
    · omega
    · have hmod :
          (Ts c' + ρact + pcF c' - Ts c') % pcF c' = ρact := by
        rw [show Ts c' + ρact + pcF c' - Ts c' = ρact + pcF c' by omega]
        rw [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
        exact Nat.mod_eq_of_lt hρact_lt
      rw [hmod]
      exact hresloc
  have hrmem :=
    rowSsuf_mkBridgeUpdateRowIndex_mem_of_activation_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hQdvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN hActive
      pcF Ts Tp j0F mS S1 F2
      (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
      (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
      hS1 hF2
      (fun r c' x hx => updateDeepDsufRowTable_mem_lt
        (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
        (r := r) (c' := c') (k := x) hx)
      (fun r c' x hx => updateDeepDpreRowTable_mem_lt
        (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
        (r := r) (c' := c') (k := x) hx)
      c' N hN hpc hm hband hN_floor hNDom_floor hNDp_floor
      n rAbs F hn_floor hG hrAbsQ hag h0F h1F
  have hp : mS + 2 * n + 1 + l < (copiedSlice mS n).length := by
    rw [length_copiedSlice]
    omega
  have hguard :
      CopiedBandRunGate.updateSufBandGuard (copiedSlice mS n) Q rAbs (q_D + 2)
        (mS + 2 * n + 1 + l) := by
    have hrunBand :=
      CopiedBandRunGate.suffixBandGuard_copiedSlice mS n q_D l hm hn hlm hqD_l
    have hpmod : (mS + 2 * n + 1 + l) % Q = rAbs := by rw [hrAbs_def]
    exact ⟨⟨hrunBand.1, hpmod⟩, hrunBand.2⟩
  have hord :=
    hgate.2.2.2.1 c' rAbs hrmem (mS + 2 * n + 1 + l) hp
      ⟨hguard, hselD.1, hselD.2⟩
  simpa [Polyreg.Presentation.atomOrd] using hord

/-- Prefix-run slope callback for the fully update-shaped bridge. -/
theorem atomOrd_update_prefix_slope_of_bridgeUpdateDeepGateCond_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    {l : ℕ} (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pcF c') (hQpos : 0 < Q) (hpcQ : pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hband : Tp c' + 2 * pcF c' ≤ mS - 1)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = F l)
    (hTp_l : Tp c' ≤ l) (hlm : l < mS - 1) (hqU_l : q_U ≤ l)
    (hslope : ∀ l', Tp c' ≤ l' → l' < mS - 1 →
      (l' - Tp c') % pcF c' = (l - Tp c') % pcF c' →
      F l' = CopiedDstar.dstarRankGA_m P hV mS n)
    (hselD : P.toPoly.sel c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
      ∧ P.toPoly.label c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = D) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
      (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l⟩ :
        P.toPoly.Atom) := by
  set rAbs : ℕ := l % Q with hrAbs_def
  have hrAbsQ : rAbs < Q := by
    rw [hrAbs_def]
    exact Nat.mod_lt _ hQpos
  set ρact : ℕ := (rAbs + Q - ((Tp c') % Q)) % pcF c' with hρact_def
  have hρact_lt : ρact < pcF c' := by
    rw [hρact_def]
    exact Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hpc)
  have hresloc : ρact = (l - Tp c') % pcF c' := by
    have hres := CopiedSelUniform.runLocalResidue_of_abs_mod
      (Q := Q) (pc := pcF c') (shift := 0)
      (T := Tp c') (l := l) (ρ := rAbs)
      hQpos hpcQ hrAbsQ (by simp [hrAbs_def]) hTp_l
    simpa [ρact, hρact_def] using hres
  have h0F : F (Tp c' + ρact) = CopiedDstar.dstarRankGA_m P hV mS n := by
    apply hslope
    · omega
    · omega
    · rw [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt hρact_lt]
      exact hresloc
  have h1F :
      F (Tp c' + ρact + pcF c') = CopiedDstar.dstarRankGA_m P hV mS n := by
    apply hslope
    · omega
    · omega
    · have hmod :
          (Tp c' + ρact + pcF c' - Tp c') % pcF c' = ρact := by
        rw [show Tp c' + ρact + pcF c' - Tp c' = ρact + pcF c' by omega]
        rw [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
        exact Nat.mod_eq_of_lt hρact_lt
      rw [hmod]
      exact hresloc
  have hrmem :=
    rowSpre_mkBridgeUpdateRowIndex_mem_of_activation_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN hActive
      pcF Ts Tp j0F mS S1 F2
      (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
      (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
      hS1 hF2
      (fun r c' x hx => updateDeepDsufRowTable_mem_lt
        (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
        (r := r) (c' := c') (k := x) hx)
      (fun r c' x hx => updateDeepDpreRowTable_mem_lt
        (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
        (r := r) (c' := c') (k := x) hx)
      c' N hN hpc hm hband hN_floor hNDom_floor hNDp_floor
      n rAbs F hn_floor hG hrAbsQ hag h0F h1F
  have hp : l < (copiedSlice mS n).length := by
    rw [length_copiedSlice]
    omega
  have hguard :
      CopiedBandRunGate.preBandStrictGuard (copiedSlice mS n) Q rAbs q_U l := by
    simpa [hrAbs_def] using
      CopiedBandRunGate.preBandStrictGuard_copiedSlice mS n Q q_U l hm hn hlm hqU_l
  have hord := hgate.2.2.2.2.1 c' rAbs hrmem l hp ⟨hguard, hselD.1, hselD.2⟩
  simpa [Polyreg.Presentation.atomOrd] using hord

/-- Deep-suffix callback for the update-shaped bridge when the achiever-locus
already supplies the deep offset bound. -/
theorem atomOrd_update_deep_suffix_locus_of_bridgeUpdateDeepGateCond_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    {l : ℕ}
    (hm : 1 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hlm : l < mS - 1)
    (hdeep : 1 ≤ mS - 1 - l ∧ mS - 1 - l < Ndeep c')
    (hselD : P.toPoly.sel c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l))
      ∧ P.toPoly.label c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = D)
    (hach : P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l))
      = CopiedDstar.dstarRankGA_m P hV mS n) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
      (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)⟩ : P.toPoly.Atom) := by
  set k : ℕ := mS - 2 - l with hk_def
  have htailOff : mS - 1 - (k + 1) = l := by
    rw [hk_def]
    omega
  have hkN : k < Ndeep c' := by
    rw [hk_def]
    omega
  have hpos :
      mixedPosAt
          (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
          mS (B + 1) n
        = mS + 2 * n + 1 + l := by
    simp only [mixedPosAt]
    rw [htailOff]
  have hactive :
      P.rank c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mixedPosAt
              (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
              mS (B + 1) n))
        = CopiedDstar.dstarRankGA_m P hV mS n := by
    simpa [hpos] using hach
  have hrmem :=
    rowDsuf_mkBridgeUpdateRowIndex_mem_of_updateDeep_active_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts Tp j0F mS S1 F2 hS1 hF2 c' N hN hm hN_floor
      hNDom_floor hNDp_floor hB_floor n k hn_floor hG hkN hactive
  have hp : mS + 2 * n + 1 + l < (copiedSlice mS n).length := by
    rw [length_copiedSlice]
    omega
  have hcond :
      ((((copiedSlice mS n)[mS + 2 * n + 1 + l]? = some D
            ∧ ∀ q, q < (copiedSlice mS n).length → mS + 2 * n + 1 + l < q →
                (copiedSlice mS n)[q]? = some D)
          ∧ mS + 2 * n + 1 + l + 1 + k = (copiedSlice mS n).length)
        ∧ P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l))
        ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l)) = D) := by
    have hrunTail :=
      (CopiedBandRunGate.suffixBandGuard_copiedSlice mS n 0 l hm (by omega)
        hlm (Nat.zero_le l)).1
    refine ⟨⟨hrunTail, ?_⟩, hselD.1, hselD.2⟩
    rw [length_copiedSlice]
    omega
  have hord :=
    hgate.2.2.2.2.2.1 c' k hrmem (mS + 2 * n + 1 + l) hp hcond
  simpa [Polyreg.Presentation.atomOrd] using hord

/-- Deep-prefix callback for the update-shaped bridge when the achiever-locus
already supplies the deep offset bound. -/
theorem atomOrd_update_deep_prefix_locus_of_bridgeUpdateDeepGateCond_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    {l : ℕ}
    (hm : 1 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hlm : l < mS - 1) (hqU_l : q_U ≤ l)
    (hdeep : 1 ≤ mS - 1 - l ∧ mS - 1 - l < Ndeep c')
    (hselD : P.toPoly.sel c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
      ∧ P.toPoly.label c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = D)
    (hach : P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
      = CopiedDstar.dstarRankGA_m P hV mS n) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
      (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l⟩ :
        P.toPoly.Atom) := by
  set k0 : ℕ := mS - 2 - l with hk0_def
  have hpreOff : mS - 1 - (k0 + 1) = l := by
    rw [hk0_def]
    omega
  have hk0N : k0 < Ndeep c' := by
    rw [hk0_def]
    omega
  have hpos :
      mixedPosAt
          (Sum.inr (Sum.inr (k0 + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
          mS (B + 1) n
        = l := by
    simp only [mixedPosAt]
    rw [hpreOff]
  have hactive :
      P.rank c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mixedPosAt
              (Sum.inr (Sum.inr (k0 + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
              mS (B + 1) n))
        = CopiedDstar.dstarRankGA_m P hV mS n := by
    simpa [hpos] using hach
  have hrmem :=
    rowDpre_mkBridgeUpdateRowIndex_mem_of_updateDeep_active_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts Tp j0F mS S1 F2 hS1 hF2 c' N hN hm hN_floor
      hNDom_floor hNDp_floor hB_floor n k0 hn_floor hG hk0N hactive
  have hp : l < (copiedSlice mS n).length := by
    rw [length_copiedSlice]
    omega
  have hcond :
      ((((copiedSlice mS n)[l]? = some U
            ∧ ∀ q, q < (copiedSlice mS n).length → q < l →
                (copiedSlice mS n)[q]? = some U)
          ∧ ((copiedSlice mS n)[l + (k0 + 3)]? = some D
            ∧ ∀ q, q < l + (k0 + 3) → (copiedSlice mS n)[q]? ≠ some D))
        ∧ P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
        ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = D) := by
    have hpreGuard :=
      CopiedBandRunGate.preBandStrictGuard_copiedSlice mS n Q q_U l hm hn hlm hqU_l
    have hfirst := CopiedBandRunGate.firstDGuard_copiedSlice mS n hm hn
    refine ⟨⟨hpreGuard.1.1, ?_⟩, hselD.1, hselD.2⟩
    have hpin : l + (k0 + 3) = mS + 1 := by
      rw [hk0_def]
      omega
    constructor
    · rw [hpin]
      exact hfirst.1
    · intro q hq
      rw [hpin] at hq
      exact hfirst.2 q hq
  have hord := hgate.2.2.2.2.2.2 c' (k0 + 3) hrmem l hp hcond
  simpa [Polyreg.Presentation.atomOrd] using hord

/-- Suffix split-branch callback for the fully update-shaped bridge.  The
update achiever-locus reduces the branch to either the shallow slope row or the
deep-locus row; the explicit lower-band premise rules out the tiny shallow
case. -/
theorem atomOrd_update_suffix_branch_of_bridgeUpdateDeepGateCond_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hQdvd : Q ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (hAch : CopiedAchieverLocus.DstarAchieverUpdateLocus P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (c' : Fin P.toPoly.K)
    (NSuf NDSuf : ℕ)
    (hNSuf : ∀ n n', NSuf ≤ n → NSuf ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hNDSuf : ∀ n n', NDSuf ≤ n → NDSuf ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    {Nc mx l : ℕ} (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pcF c') (hQpos : 0 < Q) (hpcQ : pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hNcmS : Nc ≤ mS - 1) (hNcmx : mS ≤ Nc + mx)
    (hTq : Ts c' + pcF c' < q_D)
    (hband : Ts c' + 2 * pcF c' ≤ mS - 1)
    (hNSuf_floor : NSuf ≤ Nfloor)
    (hNDSuf_floor : NDSuf ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hF : CopiedDstarCMS.RankAffineAtFrom (Ts c') (pcF c') F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = F l)
    (hselconst : ∀ l₁ l₂, Ts c' ≤ l₁ → l₁ < Nc → Ts c' ≤ l₂ → l₂ < Nc →
      (l₁ - Ts c') % pcF c' = (l₂ - Ts c') % pcF c' →
      ((P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₁))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₁)) = D)
        ↔ (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₂))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₂)) = D)))
    (hNdeep_eq : Ndeep c' = mx + pcF c')
    (hTs_l : Ts c' ≤ l) (hlm : l < mS - 1) (hqD_l : q_D ≤ l)
    (hselD : P.toPoly.sel c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l))
      ∧ P.toPoly.label c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = D)
    (hach : P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l))
      = CopiedDstar.dstarRankGA_m P hV mS n) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
      (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)⟩ : P.toPoly.Atom) := by
  have hupdval : ∀ l', l' < mS - 1 →
      ∀ i, Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l') i < (copiedSlice mS n).length := by
    intro l' hl' i
    have hp : mS + 2 * n + 1 + l' < (copiedSlice mS n).length := by
      rw [length_copiedSlice]
      omega
    exact update_zero_valid_of_position_lt (α := Fin (P.toPoly.arity c')) hp i
  have hachF : F l = CopiedDstar.dstarRankGA_m P hV mS n := by
    exact (hag l hlm).symm.trans hach
  have hlocus :=
    hAch.1 c' (j0F c') (fun _ : Fin (P.toPoly.arity c') => 0)
      mS n (pcF c') (Ts c') Nc q_D mx F hpc hTq hF
      hupdval hag hselconst hNcmS hNcmx l hlm hselD hachF
  rcases hlocus with hsh | hslope | hdeep
  · exfalso
    omega
  · exact atomOrd_update_suffix_slope_of_bridgeUpdateDeepGateCond_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
      (pG := pG) (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hQdvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      hActive pcF Ts Tp j0F mS S1 F2 hS1 hF2 hgate c' NSuf hNSuf F
      hpc hQpos hpcQ hm hn hband hNSuf_floor hNDom_floor hNDp_floor hn_floor hG
      hag hTs_l hlm hqD_l hslope hselD
  · have hdeepN : 1 ≤ mS - 1 - l ∧ mS - 1 - l < Ndeep c' := by
      refine ⟨hdeep.1, ?_⟩
      rw [hNdeep_eq]
      exact hdeep.2
    exact atomOrd_update_deep_suffix_locus_of_bridgeUpdateDeepGateCond_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
      (pG := pG) (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts Tp j0F mS S1 F2 hS1 hF2 hgate c' NDSuf hNDSuf
      hm hNDSuf_floor hNDom_floor hNDp_floor hB_floor hn_floor hG
      hlm hdeepN hselD hach

/-- Prefix split-branch twin of
`atomOrd_update_suffix_branch_of_bridgeUpdateDeepGateCond_floor`. -/
theorem atomOrd_update_prefix_branch_of_bridgeUpdateDeepGateCond_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (hAch : CopiedAchieverLocus.DstarAchieverUpdateLocus P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (c' : Fin P.toPoly.K)
    (NPre NDPre : ℕ)
    (hNPre : ∀ n n', NPre ≤ n → NPre ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hNDPre : ∀ n n', NDPre ≤ n → NDPre ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    {Nc mx l : ℕ} (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pcF c') (hQpos : 0 < Q) (hpcQ : pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hNcmS : Nc ≤ mS - 1) (hNcmx : mS ≤ Nc + mx)
    (hTq : Tp c' + pcF c' < q_U)
    (hband : Tp c' + 2 * pcF c' ≤ mS - 1)
    (hNPre_floor : NPre ≤ Nfloor)
    (hNDPre_floor : NDPre ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hF : CopiedDstarCMS.RankAffineAtFrom (Tp c') (pcF c') F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = F l)
    (hselconst : ∀ l₁ l₂, Tp c' ≤ l₁ → l₁ < Nc → Tp c' ≤ l₂ → l₂ < Nc →
      (l₁ - Tp c') % pcF c' = (l₂ - Tp c') % pcF c' →
      ((P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₁)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₁) = D)
        ↔ (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₂)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₂) = D)))
    (hNdeep_eq : Ndeep c' = mx + pcF c')
    (hTp_l : Tp c' ≤ l) (hlm : l < mS - 1) (hqU_l : q_U ≤ l)
    (hselD : P.toPoly.sel c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
      ∧ P.toPoly.label c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = D)
    (hach : P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
      = CopiedDstar.dstarRankGA_m P hV mS n) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
      (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l⟩ :
        P.toPoly.Atom) := by
  have hupdval : ∀ l', l' < mS - 1 →
      ∀ i, Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l' i
        < (copiedSlice mS n).length := by
    intro l' hl' i
    have hp : l' < (copiedSlice mS n).length := by
      rw [length_copiedSlice]
      omega
    exact update_zero_valid_of_position_lt (α := Fin (P.toPoly.arity c')) hp i
  have hachF : F l = CopiedDstar.dstarRankGA_m P hV mS n := by
    exact (hag l hlm).symm.trans hach
  have hlocus :=
    hAch.2 c' (j0F c') (fun _ : Fin (P.toPoly.arity c') => 0)
      mS n (pcF c') (Tp c') Nc q_U mx F hpc hTq hF
      hupdval hag hselconst hNcmS hNcmx l hlm hselD hachF
  rcases hlocus with hsh | hslope | hdeep
  · exfalso
    omega
  · exact atomOrd_update_prefix_slope_of_bridgeUpdateDeepGateCond_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
      (pG := pG) (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      hActive pcF Ts Tp j0F mS S1 F2 hS1 hF2 hgate c' NPre hNPre F
      hpc hQpos hpcQ hm hn hband hNPre_floor hNDom_floor hNDp_floor hn_floor hG
      hag hTp_l hlm hqU_l hslope hselD
  · have hdeepN : 1 ≤ mS - 1 - l ∧ mS - 1 - l < Ndeep c' := by
      refine ⟨hdeep.1, ?_⟩
      rw [hNdeep_eq]
      exact hdeep.2
    exact atomOrd_update_deep_prefix_locus_of_bridgeUpdateDeepGateCond_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
      (pG := pG) (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts Tp j0F mS S1 F2 hS1 hF2 hgate c' NDPre hNDPre
      hm hNDPre_floor hNDom_floor hNDp_floor hB_floor hn hn_floor hG
      hlm hqU_l hdeepN hselD hach

/-- Turn a suffix branch from `tieSemanticUpdateSplitAt` into the canonical
update-deep suffix branch callback.  The caller supplies the small-band branch,
usually by replaying the selector cfg through the core gate. -/
theorem atomOrd_update_suffix_split_branch_of_bridgeUpdateDeepGateCond_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hQdvd : Q ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (hAch : CopiedAchieverLocus.DstarAchieverUpdateLocus P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (NSuf NDSuf : Fin P.toPoly.K → ℕ)
    (hNSuf : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NSuf c' ≤ n → NSuf c' ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hNDSuf : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NDSuf c' ≤ n → NDSuf c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    {Nc mx r : ℕ} (Fs : (c' : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (hpc : ∀ c' : Fin P.toPoly.K, 1 ≤ pcF c')
    (hQpos : 0 < Q) (hpcQ : ∀ c' : Fin P.toPoly.K, pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hNcmS : Nc ≤ mS - 1) (hNcmx : mS ≤ Nc + mx)
    (hTq : ∀ c' : Fin P.toPoly.K, Ts c' + pcF c' < q_D)
    (hband : ∀ c' : Fin P.toPoly.K, Ts c' + 2 * pcF c' ≤ mS - 1)
    (hNSuf_floor : ∀ c' : Fin P.toPoly.K, NSuf c' ≤ Nfloor)
    (hNDSuf_floor : ∀ c' : Fin P.toPoly.K, NDSuf c' ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hFs : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Ts c') (pcF c') (Fs c'))
    (hags : ∀ c' : Fin P.toPoly.K, ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = Fs c' l)
    (hselconst : ∀ c' : Fin P.toPoly.K, ∀ l₁ l₂,
      Ts c' ≤ l₁ → l₁ < Nc → Ts c' ≤ l₂ → l₂ < Nc →
      (l₁ - Ts c') % pcF c' = (l₂ - Ts c') % pcF c' →
      ((P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₁))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₁)) = D)
        ↔ (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₂))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₂)) = D)))
    (hNdeep_eq : ∀ c' : Fin P.toPoly.K, Ndeep c' = mx + pcF c')
    (hsmall : ∀ (c' : Fin P.toPoly.K) (l : ℕ),
      Ts c' + pcF c' ≤ l → l + pcF c' < Nc → l < q_D →
      (P.toPoly.sel c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mS + 2 * n + 1 + l))
        ∧ P.toPoly.label c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mS + 2 * n + 1 + l)) = D) →
      P.rank c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mS + 2 * n + 1 + l))
        = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
        (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mS + 2 * n + 1 + l)⟩ : P.toPoly.Atom))
    (hclass : ∀ b : P.toPoly.Atom,
      (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (fun _ : Fin (P.toPoly.arity b.1) => 0)
          (j0F b.1) (mS + 2 * n + 1 + l)) →
      Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
      (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n) :
    ∀ b : P.toPoly.Atom,
      (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (fun _ : Fin (P.toPoly.arity b.1) => 0)
          (j0F b.1) (mS + 2 * n + 1 + l)) →
      Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
      (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b := by
  intro b hsuf hcls hselD
  rcases b with ⟨c', xb⟩
  rcases hsuf with ⟨l, hlo, hhi, hxbeq⟩
  have hxbeq' :
      xb = Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
        (mS + 2 * n + 1 + l) := by
    simpa using hxbeq
  subst xb
  have hlo' : Ts c' + pcF c' ≤ l := by
    simpa using hlo
  have hhi' : l + pcF c' < Nc := by
    simpa using hhi
  have hach :
      P.rank c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mS + 2 * n + 1 + l))
        = CopiedDstar.dstarRankGA_m P hV mS n :=
    rank_update_suffix_of_split_class P hV
      (mS := mS) (n := n) (Nc := Nc) (r := r)
      (pcF := pcF) (Ts := Ts) (ī0F := fun c' _ => 0) (j0F := j0F)
      (c' := c') (l := l) hclass hlo' hhi' rfl hcls hselD
  have hselRun :
      P.toPoly.sel c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mS + 2 * n + 1 + l))
        ∧ P.toPoly.label c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mS + 2 * n + 1 + l)) = D :=
    ⟨hselD.1.2, hselD.2⟩
  have hlm : l < mS - 1 := by
    have := hpc c'
    omega
  by_cases hsmall_l : l < q_D
  · exact hsmall c' l hlo' hhi' hsmall_l hselRun hach
  · have hqD_l : q_D ≤ l := by omega
    have hTs_l : Ts c' ≤ l := by omega
    exact atomOrd_update_suffix_branch_of_bridgeUpdateDeepGateCond_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
      (pG := pG) (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hQdvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      hActive hAch pcF Ts Tp j0F mS S1 F2 hS1 hF2 hgate c'
      (NSuf c') (NDSuf c') (hNSuf c') (hNDSuf c') (Fs c')
      (hpc c') hQpos (hpcQ c') hm hn hNcmS hNcmx (hTq c') (hband c')
      (hNSuf_floor c') (hNDSuf_floor c') hNDom_floor hNDp_floor hB_floor hn_floor
      hG (hFs c') (hags c') (hselconst c') (hNdeep_eq c')
      hTs_l hlm hqD_l hselRun hach

/-- Prefix twin of
`atomOrd_update_suffix_split_branch_of_bridgeUpdateDeepGateCond_floor`. -/
theorem atomOrd_update_prefix_split_branch_of_bridgeUpdateDeepGateCond_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (hAch : CopiedAchieverLocus.DstarAchieverUpdateLocus P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (NPre NDPre : Fin P.toPoly.K → ℕ)
    (hNPre : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NPre c' ≤ n → NPre c' ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hNDPre : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NDPre c' ≤ n → NDPre c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    {Nc mx r : ℕ} (Fp : (c' : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (hpc : ∀ c' : Fin P.toPoly.K, 1 ≤ pcF c')
    (hQpos : 0 < Q) (hpcQ : ∀ c' : Fin P.toPoly.K, pcF c' ∣ Q)
    (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hNcmS : Nc ≤ mS - 1) (hNcmx : mS ≤ Nc + mx)
    (hTq : ∀ c' : Fin P.toPoly.K, Tp c' + pcF c' < q_U)
    (hband : ∀ c' : Fin P.toPoly.K, Tp c' + 2 * pcF c' ≤ mS - 1)
    (hNPre_floor : ∀ c' : Fin P.toPoly.K, NPre c' ≤ Nfloor)
    (hNDPre_floor : ∀ c' : Fin P.toPoly.K, NDPre c' ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hFp : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Tp c') (pcF c') (Fp c'))
    (hagp : ∀ c' : Fin P.toPoly.K, ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) =
          Fp c' l)
    (hselconst : ∀ c' : Fin P.toPoly.K, ∀ l₁ l₂,
      Tp c' ≤ l₁ → l₁ < Nc → Tp c' ≤ l₂ → l₂ < Nc →
      (l₁ - Tp c') % pcF c' = (l₂ - Tp c') % pcF c' →
      ((P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₁)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₁) = D)
        ↔ (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₂)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₂) = D)))
    (hNdeep_eq : ∀ c' : Fin P.toPoly.K, Ndeep c' = mx + pcF c')
    (hsmall : ∀ (c' : Fin P.toPoly.K) (l : ℕ),
      Tp c' + pcF c' ≤ l → l + pcF c' < Nc → l < q_U →
      (P.toPoly.sel c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
        ∧ P.toPoly.label c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = D) →
      P.rank c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
        = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
        (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l⟩ :
          P.toPoly.Atom))
    (hclass : ∀ b : P.toPoly.Atom,
      (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (fun _ : Fin (P.toPoly.arity b.1) => 0)
          (j0F b.1) l) →
      Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
      (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n) :
    ∀ b : P.toPoly.Atom,
      (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (fun _ : Fin (P.toPoly.arity b.1) => 0)
          (j0F b.1) l) →
      Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
      (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b := by
  intro b hpre hcls hselD
  rcases b with ⟨c', xb⟩
  rcases hpre with ⟨l, hlo, hhi, hxbeq⟩
  have hxbeq' :
      xb = Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l := by
    simpa using hxbeq
  subst xb
  have hlo' : Tp c' + pcF c' ≤ l := by
    simpa using hlo
  have hhi' : l + pcF c' < Nc := by
    simpa using hhi
  have hach :
      P.rank c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
        = CopiedDstar.dstarRankGA_m P hV mS n :=
    rank_update_prefix_of_split_class P hV
      (mS := mS) (n := n) (Nc := Nc) (r := r)
      (pcF := pcF) (Tp := Tp) (ī0F := fun c' _ => 0) (j0F := j0F)
      (c' := c') (l := l) hclass hlo' hhi' rfl hcls hselD
  have hselRun :
      P.toPoly.sel c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
        ∧ P.toPoly.label c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = D :=
    ⟨hselD.1.2, hselD.2⟩
  have hlm : l < mS - 1 := by
    have := hpc c'
    omega
  by_cases hsmall_l : l < q_U
  · exact hsmall c' l hlo' hhi' hsmall_l hselRun hach
  · have hqU_l : q_U ≤ l := by omega
    have hTp_l : Tp c' ≤ l := by omega
    exact atomOrd_update_prefix_branch_of_bridgeUpdateDeepGateCond_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
      (pG := pG) (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      hActive hAch pcF Ts Tp j0F mS S1 F2 hS1 hF2 hgate c'
      (NPre c') (NDPre c') (hNPre c') (hNDPre c') (Fp c')
      (hpc c') hQpos (hpcQ c') hm hn hNcmS hNcmx (hTq c') (hband c')
      (hNPre_floor c') (hNDPre_floor c') hNDom_floor hNDp_floor hB_floor hn_floor
      hG (hFp c') (hagp c') (hselconst c') (hNdeep_eq c')
      hTp_l hlm hqU_l hselRun hach

/-- A zero-base tuple with one distinguished suffix-coordinate update is a
bounded descriptor tuple whenever that update lies in the shallow suffix band. -/
theorem update_zero_suffix_boundedTuplesF_of_cellTupleF
    {B k qB mS n l : ℕ} {j0 : Fin k}
    {rs : Fin k → CopiedCells.RegionSpecF B} {t : ℕ}
    (hlq : l < qB)
    (hvalid : ∀ i, (rs i).valid mS)
    (hcell : Function.update (fun _ : Fin k => 0) j0 (mS + 2 * n + 1 + l) =
      CopiedDstar.cellTupleF rs mS t n) :
    rs ∈ CopiedBoundedGate.boundedTuplesF B k qB qB := by
  rw [CopiedBoundedGate.mem_boundedTuplesF]
  intro i
  have hcelli := congrFun hcell i
  by_cases hij : i = j0
  · subst i
    cases hrs : rs j0 with
    | core r0 =>
        simp
    | prefIdx q =>
        exfalso
        have hvalidi := hvalid j0
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs] at hcelli
        simp [CopiedCells.RegionSpecF.valid, hrs] at hvalidi
        omega
    | sufIdx l' =>
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs] at hcelli
        simp
        omega
  · cases hrs : rs i with
    | core r0 =>
        simp
    | prefIdx q =>
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs, Function.update,
          hij] at hcelli
        simp
        omega
    | sufIdx l' =>
        exfalso
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs, Function.update,
          hij] at hcelli
        omega

/-- Prefix-band twin of `update_zero_suffix_boundedTuplesF_of_cellTupleF`. -/
theorem update_zero_prefix_boundedTuplesF_of_cellTupleF
    {B k qB mS n l : ℕ} {j0 : Fin k}
    {rs : Fin k → CopiedCells.RegionSpecF B} {t : ℕ}
    (hlm : l < mS - 1) (hlq : l < qB)
    (hcell : Function.update (fun _ : Fin k => 0) j0 l =
      CopiedDstar.cellTupleF rs mS t n) :
    rs ∈ CopiedBoundedGate.boundedTuplesF B k qB qB := by
  rw [CopiedBoundedGate.mem_boundedTuplesF]
  intro i
  have hcelli := congrFun hcell i
  by_cases hij : i = j0
  · subst i
    cases hrs : rs j0 with
    | core r0 =>
        simp
    | prefIdx q =>
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs] at hcelli
        simp
        omega
    | sufIdx l' =>
        exfalso
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs] at hcelli
        omega
  · cases hrs : rs i with
    | core r0 =>
        simp
    | prefIdx q =>
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs, Function.update,
          hij] at hcelli
        simp
        omega
    | sufIdx l' =>
        exfalso
        simp [CopiedDstar.cellTupleF, CopiedCells.RegionSpecF.posAt, hrs, Function.update,
          hij] at hcelli
        omega

/-- Small suffix updates are handled by replaying the selector cfg through the
core branch: the distinguished coordinate lies in a suffix cell with offset
below `qB`, while all unchanged coordinates are at position zero and therefore
also bounded. -/
theorem atomOrd_update_suffix_small_of_core_from_cfg
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr qB mS n Nc : ℕ}
    {pcF Ts : Fin P.toPoly.K → ℕ}
    {j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c')}
    {S1 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ}
    {F2 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ}
    {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hcore_from_cfg : ∀ (b : P.toPoly.Atom),
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      CopiedTieGate.cfgCellGAFL B Bh M mthr S1
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
        mS n b →
      (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF B) (t : ℕ),
        (∀ i, (rs i).valid mS) → t < n →
        b.2 = CopiedDstar.cellTupleF rs mS t n →
        CopiedTieGate.cfgPosL M mthr (S1 b.1 rs) ∅ ∅
          (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
        rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity b.1) qB qB) →
      (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF Bh) (t : ℕ),
        (∀ i, (rs i).valid mS) → t < n →
        b.2 = CopiedDstar.cellTupleF rs mS t n →
        CopiedTieGate.cfgPosL M mthr ∅ (F2 b.1 rs) ∅
          (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
        rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity b.1) qB qB) →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    (hcfg_of_rank : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      CopiedTieGate.cfgCellGAFL B Bh M mthr S1
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
        mS n b)
    (c' : Fin P.toPoly.K) (l : ℕ)
    (hpc : 1 ≤ pcF c') (hNcmS : Nc ≤ mS - 1)
    (_hlo : Ts c' + pcF c' ≤ l) (hhi : l + pcF c' < Nc) (hlq : l < qB)
    (hselD : P.toPoly.sel c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l))
      ∧ P.toPoly.label c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = D)
    (hach : P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l))
      = CopiedDstar.dstarRankGA_m P hV mS n) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
      (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)⟩ : P.toPoly.Atom) := by
  have hlm : l < mS - 1 := by omega
  have hp : mS + 2 * n + 1 + l < (copiedSlice mS n).length := by
    rw [length_copiedSlice]
    omega
  let b : P.toPoly.Atom :=
    ⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
      (mS + 2 * n + 1 + l)⟩
  have hbsel : P.toPoly.selectedAtom (copiedSlice mS n) b :=
    ⟨update_zero_valid_of_position_lt (α := Fin (P.toPoly.arity c')) hp, hselD.1⟩
  have hbD : P.toPoly.labelOf (copiedSlice mS n) b = D := hselD.2
  have hbrank : P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n := by
    simpa [b, WRP.Presentation.rankOf] using hach
  have hcfg := hcfg_of_rank b hbsel hbD hbrank
  have hbounded :
      ∀ {B0 : ℕ}
        (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B0) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l)) =
            CopiedDstar.cellTupleF rs mS t n →
          rs ∈ CopiedBoundedGate.boundedTuplesF B0 (P.toPoly.arity c') qB qB := by
    intro B0 rs t hvalid _htn hcell
    exact update_zero_suffix_boundedTuplesF_of_cellTupleF (j0 := j0F c') hlq hvalid hcell
  exact hcore_from_cfg b hbsel hbD hcfg
    (by
      intro rs t hvalid htn hcell _hpos
      exact hbounded rs t hvalid htn hcell)
    (by
      intro rs t hvalid htn hcell _hpos
      exact hbounded rs t hvalid htn hcell)

/-- Prefix small-band twin of
`atomOrd_update_suffix_small_of_core_from_cfg`. -/
theorem atomOrd_update_prefix_small_of_core_from_cfg
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr qB mS n Nc : ℕ}
    {pcF Tp : Fin P.toPoly.K → ℕ}
    {j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c')}
    {S1 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ}
    {F2 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ}
    {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hcore_from_cfg : ∀ (b : P.toPoly.Atom),
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      CopiedTieGate.cfgCellGAFL B Bh M mthr S1
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
        mS n b →
      (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF B) (t : ℕ),
        (∀ i, (rs i).valid mS) → t < n →
        b.2 = CopiedDstar.cellTupleF rs mS t n →
        CopiedTieGate.cfgPosL M mthr (S1 b.1 rs) ∅ ∅
          (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
        rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity b.1) qB qB) →
      (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF Bh) (t : ℕ),
        (∀ i, (rs i).valid mS) → t < n →
        b.2 = CopiedDstar.cellTupleF rs mS t n →
        CopiedTieGate.cfgPosL M mthr ∅ (F2 b.1 rs) ∅
          (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
        rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity b.1) qB qB) →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
    (hcfg_of_rank : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      CopiedTieGate.cfgCellGAFL B Bh M mthr S1
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) F2 (fun _ _ => ∅)
        mS n b)
    (c' : Fin P.toPoly.K) (l : ℕ)
    (hpc : 1 ≤ pcF c') (hNcmS : Nc ≤ mS - 1)
    (_hlo : Tp c' + pcF c' ≤ l) (hhi : l + pcF c' < Nc) (hlq : l < qB)
    (hselD : P.toPoly.sel c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
      ∧ P.toPoly.label c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = D)
    (hach : P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
      = CopiedDstar.dstarRankGA_m P hV mS n) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
      (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l⟩ :
        P.toPoly.Atom) := by
  have hlm : l < mS - 1 := by omega
  have hp : l < (copiedSlice mS n).length := by
    rw [length_copiedSlice]
    omega
  let b : P.toPoly.Atom :=
    ⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l⟩
  have hbsel : P.toPoly.selectedAtom (copiedSlice mS n) b :=
    ⟨update_zero_valid_of_position_lt (α := Fin (P.toPoly.arity c')) hp, hselD.1⟩
  have hbD : P.toPoly.labelOf (copiedSlice mS n) b = D := hselD.2
  have hbrank : P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n := by
    simpa [b, WRP.Presentation.rankOf] using hach
  have hcfg := hcfg_of_rank b hbsel hbD hbrank
  have hbounded :
      ∀ {B0 : ℕ}
        (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B0) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) =
            CopiedDstar.cellTupleF rs mS t n →
          rs ∈ CopiedBoundedGate.boundedTuplesF B0 (P.toPoly.arity c') qB qB := by
    intro B0 rs t _hvalid _htn hcell
    exact update_zero_prefix_boundedTuplesF_of_cellTupleF (j0 := j0F c') hlm hlq hcell
  exact hcore_from_cfg b hbsel hbD hcfg
    (by
      intro rs t hvalid htn hcell _hpos
      exact hbounded rs t hvalid htn hcell)
    (by
      intro rs t hvalid htn hcell _hpos
      exact hbounded rs t hvalid htn hcell)

/-- Deep-suffix boundary callback for the fully update-shaped bridge.  An
actual deep-suffix rank at a distinguished-coordinate update tuple is first
transported into the canonical update-deep row table, then consumed by the
deep-suffix clause of `bridgeUpdateDeepGateCond`. -/
theorem atomOrd_update_deep_suffix_of_bridgeUpdateDeepGateCond_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    {Nc mx l : ℕ}
    (hm : 1 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hNcmx : mS ≤ Nc + mx)
    (hNdeep_eq : Ndeep c' = mx + pcF c')
    (hlm : l < mS - 1)
    (hnotHi : ¬ l + pcF c' < Nc)
    (hselD : P.toPoly.sel c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l))
      ∧ P.toPoly.label c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = D)
    (hach : P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l))
      = CopiedDstar.dstarRankGA_m P hV mS n) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
      (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)⟩ : P.toPoly.Atom) := by
  set k : ℕ := mS - 2 - l with hk_def
  have hgeNc : Nc ≤ l + pcF c' := by
    by_contra hlt
    exact hnotHi (by omega)
  have htailOff : mS - 1 - (k + 1) = l := by
    rw [hk_def]
    omega
  have hk_le_from_locus : k ≤ mS - 1 - l := by
    rw [hk_def]
    omega
  have hoff_lt : mS - 1 - l < Ndeep c' := by
    have hm_le_lN : mS ≤ l + Ndeep c' := by
      rw [hNdeep_eq]
      calc
        mS ≤ Nc + mx := hNcmx
        _ ≤ (l + pcF c') + mx := Nat.add_le_add_right hgeNc mx
        _ = l + (mx + pcF c') := by omega
    omega
  have hkN : k < Ndeep c' := lt_of_le_of_lt hk_le_from_locus hoff_lt
  have hpos :
      mixedPosAt
          (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
          mS (B + 1) n
        = mS + 2 * n + 1 + l := by
    simp only [mixedPosAt]
    rw [htailOff]
  have hactive :
      P.rank c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mixedPosAt
              (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
              mS (B + 1) n))
        = CopiedDstar.dstarRankGA_m P hV mS n := by
    simpa [hpos] using hach
  have hrmem :=
    rowDsuf_mkBridgeUpdateRowIndex_mem_of_updateDeep_active_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts Tp j0F mS S1 F2 hS1 hF2 c' N hN hm hN_floor
      hNDom_floor hNDp_floor hB_floor n k hn_floor hG hkN hactive
  have hp : mS + 2 * n + 1 + l < (copiedSlice mS n).length := by
    rw [length_copiedSlice]
    omega
  have hcond :
      ((((copiedSlice mS n)[mS + 2 * n + 1 + l]? = some D
            ∧ ∀ q, q < (copiedSlice mS n).length → mS + 2 * n + 1 + l < q →
                (copiedSlice mS n)[q]? = some D)
          ∧ mS + 2 * n + 1 + l + 1 + k = (copiedSlice mS n).length)
        ∧ P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l))
        ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l)) = D) := by
    have hrunTail :=
      (CopiedBandRunGate.suffixBandGuard_copiedSlice mS n 0 l hm (by omega)
        hlm (Nat.zero_le l)).1
    refine ⟨⟨hrunTail, ?_⟩, hselD.1, hselD.2⟩
    rw [length_copiedSlice]
    omega
  have hord :=
    hgate.2.2.2.2.2.1 c' k hrmem (mS + 2 * n + 1 + l) hp hcond
  simpa [Polyreg.Presentation.atomOrd] using hord

/-- Deep-prefix boundary callback for the fully update-shaped bridge. -/
theorem atomOrd_update_deep_prefix_of_bridgeUpdateDeepGateCond_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    {B Bh M mthr pG q_U q_D Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1 : Fin pG → S1Key P B q_U q_D → Finset ℕ)
    (F2 : Fin pG → F2Key P Bh q_U q_D → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1 r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2 r key → x < 2 * Bh + 2)
    {n : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG q_U q_D Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1 F2
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (c' : Fin P.toPoly.K) (N : ℕ)
    (hN : ∀ n n', N ≤ n → N ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    {Nc mx l : ℕ}
    (hm : 1 ≤ mS)
    (hN_floor : N ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hNcmx : mS ≤ Nc + mx)
    (hNdeep_eq : Ndeep c' = mx + pcF c')
    (hlm : l < mS - 1) (hqU_l : q_U ≤ l)
    (hnotHi : ¬ l + pcF c' < Nc)
    (hselD : P.toPoly.sel c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
      ∧ P.toPoly.label c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = D)
    (hach : P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
      = CopiedDstar.dstarRankGA_m P hV mS n) :
    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩
      (⟨c', Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l⟩ :
        P.toPoly.Atom) := by
  set k0 : ℕ := mS - 2 - l with hk0_def
  have hgeNc : Nc ≤ l + pcF c' := by
    by_contra hlt
    exact hnotHi (by omega)
  have hpreOff : mS - 1 - (k0 + 1) = l := by
    rw [hk0_def]
    omega
  have hk0_le_from_locus : k0 ≤ mS - 1 - l := by
    rw [hk0_def]
    omega
  have hoff_lt : mS - 1 - l < Ndeep c' := by
    have hm_le_lN : mS ≤ l + Ndeep c' := by
      rw [hNdeep_eq]
      calc
        mS ≤ Nc + mx := hNcmx
        _ ≤ (l + pcF c') + mx := Nat.add_le_add_right hgeNc mx
        _ = l + (mx + pcF c') := by omega
    omega
  have hk0N : k0 < Ndeep c' := lt_of_le_of_lt hk0_le_from_locus hoff_lt
  have hpos :
      mixedPosAt
          (Sum.inr (Sum.inr (k0 + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
          mS (B + 1) n
        = l := by
    simp only [mixedPosAt]
    rw [hpreOff]
  have hactive :
      P.rank c' (copiedSlice mS n)
          (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
            (mixedPosAt
              (Sum.inr (Sum.inr (k0 + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
              mS (B + 1) n))
        = CopiedDstar.dstarRankGA_m P hV mS n := by
    simpa [hpos] using hach
  have hrmem :=
    rowDpre_mkBridgeUpdateRowIndex_mem_of_updateDeep_active_rowRep_floor
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (pG := pG)
      (q_U := q_U) (q_D := q_D) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts Tp j0F mS S1 F2 hS1 hF2 c' N hN hm hN_floor
      hNDom_floor hNDp_floor hB_floor n k0 hn_floor hG hk0N hactive
  have hp : l < (copiedSlice mS n).length := by
    rw [length_copiedSlice]
    omega
  have hcond :
      ((((copiedSlice mS n)[l]? = some U
            ∧ ∀ q, q < (copiedSlice mS n).length → q < l →
                (copiedSlice mS n)[q]? = some U)
          ∧ ((copiedSlice mS n)[l + (k0 + 3)]? = some D
            ∧ ∀ q, q < l + (k0 + 3) → (copiedSlice mS n)[q]? ≠ some D))
        ∧ P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l)
        ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) = D) := by
    have hpreGuard :=
      CopiedBandRunGate.preBandStrictGuard_copiedSlice mS n Q q_U l hm (by omega)
        hlm hqU_l
    have hfirst := CopiedBandRunGate.firstDGuard_copiedSlice mS n hm (by omega)
    refine ⟨⟨hpreGuard.1.1, ?_⟩, hselD.1, hselD.2⟩
    have hpin : l + (k0 + 3) = mS + 1 := by
      rw [hk0_def]
      omega
    constructor
    · rw [hpin]
      exact hfirst.1
    · intro q hq
      rw [hpin] at hq
      exact hfirst.2 q hq
  have hord :=
    hgate.2.2.2.2.2.2 c' (k0 + 3) hrmem l hp hcond
  simpa [Polyreg.Presentation.atomOrd] using hord

/-- Core branch consumer for the canonical fully update-shaped bridge row.  It
packages selector-table replay together with the update-deep suffix/prefix
boundary callbacks in the exact shape required by
`whole_order_of_update_split`. -/
theorem core_order_of_bridgeUpdateDeepGateCond_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    (hCoreBoundary : CoreBoundaryUpdateZeroCoverage P hV)
    {B Bh M mthr pG pSel qB Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hpSel_dvd : pSel ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1tab : Fin pG → S1Key P B qB qB → Finset ℕ)
    (F2tab : Fin pG → F2Key P Bh qB qB → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1tab r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2)
    (hS1odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1)
    (hF2odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1)
    (S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1)
    (hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1)
    {n Nc mx : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG qB qB Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1tab F2tab
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (hm : 1 ≤ mS) (hqB_lt : qB < mS) (hQ1 : 1 ≤ Q)
    (hqB_def : qB = mx + Q + 1)
    (hpcF_dvd_Q : ∀ c' : Fin P.toPoly.K, pcF c' ∣ Q)
    (hTs_le_mx : ∀ c' : Fin P.toPoly.K, Ts c' ≤ mx)
    (hTp_le_mx : ∀ c' : Fin P.toPoly.K, Tp c' ≤ mx)
    (hNcmx : mS ≤ Nc + mx)
    (hNdeep_eq : ∀ c' : Fin P.toPoly.K, Ndeep c' = mx + pcF c')
    (NDSuf NDPre : Fin P.toPoly.K → ℕ)
    (hNDSuf : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NDSuf c' ≤ n → NDSuf c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hNDPre : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NDPre c' ≤ n → NDPre c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hNDSuf_floor : ∀ c' : Fin P.toPoly.K, NDSuf c' ≤ Nfloor)
    (hNDPre_floor : ∀ c' : Fin P.toPoly.K, NDPre c' ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (hcfg_of_rank : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
        (fun _ _ => ∅) mS n b) :
    ∀ b : P.toPoly.Atom,
      ¬ (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (fun _ : Fin (P.toPoly.arity b.1) => 0)
          (j0F b.1) (mS + 2 * n + 1 + l)) →
      ¬ (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (fun _ : Fin (P.toPoly.arity b.1) => 0)
          (j0F b.1) l) →
      (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b :=
  core_order_of_update_zero_boundary P hV hCoreBoundary j0F
    (B := B) (Bh := Bh) (M := M) (mthr := mthr) (qB := qB) (Q := Q)
    (mS := mS) (n := n) (Nc := Nc) (mx := mx)
    (pcF := pcF) (Ts := Ts) (Tp := Tp)
    (S1 := S1L (n % pSel)) (F2 := F2L (n % pSel)) (c0 := c) (ī0m := ī)
    hm hqB_lt hQ1 hqB_def hpcF_dvd_Q hTs_le_mx hTp_le_mx hNcmx
    (by
      intro b hbsel hbD hcfg hbndB hbndH
      exact atomOrd_of_bridgeUpdateDeepGateCond_selector_cfg
        (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
        (pG := pG) (pSel := pSel) (q_U := qB) (q_D := qB) (Q := Q)
        (Ndeep := Ndeep) hpG hpSel_dvd pcF Ts Tp j0F (fun c' _ => 0)
        mS (rowRep pG Nfloor) S1tab F2tab
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        hS1odd hF2odd S1L F2L hS1tab_eq hF2tab_eq hgate
        hbsel hbD hcfg hbndB hbndH)
    (by
      intro c' l hlm hqBl hnotHi hselD hach
      exact atomOrd_update_deep_suffix_of_bridgeUpdateDeepGateCond_floor
        (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
        (pG := pG) (q_U := qB) (q_D := qB) (Q := Q) (Ndeep := Ndeep)
        (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
        (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
        hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
        pcF Ts Tp j0F mS S1tab F2tab hS1 hF2 hgate c' (NDSuf c') (hNDSuf c')
        hm (hNDSuf_floor c') hNDom_floor hNDp_floor hB_floor hn_floor hG
        hNcmx (hNdeep_eq c') hlm hnotHi hselD hach)
    (by
      intro c' l hlm hqBl hnotHi hselD hach
      exact atomOrd_update_deep_prefix_of_bridgeUpdateDeepGateCond_floor
        (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
        (pG := pG) (q_U := qB) (q_D := qB) (Q := Q) (Ndeep := Ndeep)
        (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
        (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
        hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
        pcF Ts Tp j0F mS S1tab F2tab hS1 hF2 hgate c' (NDPre c') (hNDPre c')
        hm (hNDPre_floor c') hNDom_floor hNDp_floor hB_floor hn hn_floor hG
        hNcmx (hNdeep_eq c') hlm hqBl hnotHi hselD hach)
    hcfg_of_rank

/-- Whole-order consumer for the canonical fully update-shaped bridge row.  The
core branch is discharged by `core_order_of_bridgeUpdateDeepGateCond_floor`;
suffix/prefix split branches are routed through the update-deep branch
callbacks, with the shallow small-band cases supplied explicitly. -/
theorem whole_order_of_bridgeUpdateDeepGateCond_updateSplit_floor
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    (hCoreBoundary : CoreBoundaryUpdateZeroCoverage P hV)
    {B Bh M mthr pG pSel qB Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hpSel_dvd : pSel ∣ pG) (hQdvd : Q ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (hAch : CopiedAchieverLocus.DstarAchieverUpdateLocus P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1tab : Fin pG → S1Key P B qB qB → Finset ℕ)
    (F2tab : Fin pG → F2Key P Bh qB qB → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1tab r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2)
    (hS1odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1)
    (hF2odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1)
    (S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1)
    (hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1)
    {n Nc mx : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hsplit :
      CopiedSelUniform.tieSemanticUpdateSplitAt P hV mS n c ī pcF Ts Tp Nc
        (fun _ _ => 0) j0F)
    (hgate : bridgeUpdateDeepGateCond P c B Bh M mthr pG qB qB Q Ndeep hpG
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1tab F2tab
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      j0F (fun _ _ => 0) (n % pG) mS n ī)
    (hm : 1 ≤ mS) (hqB_lt : qB < mS) (hQ1 : 1 ≤ Q)
    (hqB_def : qB = mx + Q + 1)
    (hpc : ∀ c' : Fin P.toPoly.K, 1 ≤ pcF c')
    (hpcF_dvd_Q : ∀ c' : Fin P.toPoly.K, pcF c' ∣ Q)
    (hTs_le_mx : ∀ c' : Fin P.toPoly.K, Ts c' ≤ mx)
    (hTp_le_mx : ∀ c' : Fin P.toPoly.K, Tp c' ≤ mx)
    (hNcmS : Nc ≤ mS - 1) (hNcmx : mS ≤ Nc + mx)
    (hbandSuf : ∀ c' : Fin P.toPoly.K, Ts c' + 2 * pcF c' ≤ mS - 1)
    (hbandPre : ∀ c' : Fin P.toPoly.K, Tp c' + 2 * pcF c' ≤ mS - 1)
    (hNdeep_eq : ∀ c' : Fin P.toPoly.K, Ndeep c' = mx + pcF c')
    (NSuf NPre NDSuf NDPre : Fin P.toPoly.K → ℕ)
    (hNSuf : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NSuf c' ≤ n → NSuf c' ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hNPre : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NPre c' ≤ n → NPre c' ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hNDSuf : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NDSuf c' ≤ n → NDSuf c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hNDPre : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NDPre c' ≤ n → NDPre c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hNSuf_floor : ∀ c' : Fin P.toPoly.K, NSuf c' ≤ Nfloor)
    (hNPre_floor : ∀ c' : Fin P.toPoly.K, NPre c' ≤ Nfloor)
    (hNDSuf_floor : ∀ c' : Fin P.toPoly.K, NDSuf c' ≤ Nfloor)
    (hNDPre_floor : ∀ c' : Fin P.toPoly.K, NDPre c' ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (Fs Fp : (c' : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (hFs : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Ts c') (pcF c') (Fs c'))
    (hFp : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Tp c') (pcF c') (Fp c'))
    (hags : ∀ c' : Fin P.toPoly.K, ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = Fs c' l)
    (hagp : ∀ c' : Fin P.toPoly.K, ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) =
          Fp c' l)
    (hselconstS : ∀ c' : Fin P.toPoly.K, ∀ l₁ l₂,
      Ts c' ≤ l₁ → l₁ < Nc → Ts c' ≤ l₂ → l₂ < Nc →
      (l₁ - Ts c') % pcF c' = (l₂ - Ts c') % pcF c' →
      ((P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₁))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₁)) = D)
        ↔ (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₂))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₂)) = D)))
    (hselconstP : ∀ c' : Fin P.toPoly.K, ∀ l₁ l₂,
      Tp c' ≤ l₁ → l₁ < Nc → Tp c' ≤ l₂ → l₂ < Nc →
      (l₁ - Tp c') % pcF c' = (l₂ - Tp c') % pcF c' →
      ((P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₁)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₁) = D)
        ↔ (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₂)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₂) = D)))
    (hcfg_of_rank : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
        (fun _ _ => ∅) mS n b) :
    ∀ b : P.toPoly.Atom,
      (P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b := by
  have hcore_from_cfg :
      ∀ (b : P.toPoly.Atom),
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
          (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
          (fun _ _ => ∅) mS n b →
        (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF B) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          b.2 = CopiedDstar.cellTupleF rs mS t n →
          CopiedTieGate.cfgPosL M mthr (S1L (n % pSel) b.1 rs) ∅ ∅
            (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
          rs ∈ CopiedBoundedGate.boundedTuplesF B (P.toPoly.arity b.1) qB qB) →
        (∀ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF Bh) (t : ℕ),
          (∀ i, (rs i).valid mS) → t < n →
          b.2 = CopiedDstar.cellTupleF rs mS t n →
          CopiedTieGate.cfgPosL M mthr ∅ (F2L (n % pSel) b.1 rs) ∅
            (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
          rs ∈ CopiedBoundedGate.boundedTuplesF Bh (P.toPoly.arity b.1) qB qB) →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b := by
    intro b hbsel hbD hcfg hbndB hbndH
    exact atomOrd_of_bridgeUpdateDeepGateCond_selector_cfg
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
      (pG := pG) (pSel := pSel) (q_U := qB) (q_D := qB) (Q := Q)
      (Ndeep := Ndeep) hpG hpSel_dvd pcF Ts Tp j0F (fun c' _ => 0)
      mS (rowRep pG Nfloor) S1tab F2tab
      (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
      (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
      hS1 hF2
      (fun r c' x hx => updateDeepDsufRowTable_mem_lt
        (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
        (r := r) (c' := c') (k := x) hx)
      (fun r c' x hx => updateDeepDpreRowTable_mem_lt
        (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
        (r := r) (c' := c') (k := x) hx)
      hS1odd hF2odd S1L F2L hS1tab_eq hF2tab_eq hgate
      hbsel hbD hcfg hbndB hbndH
  exact whole_order_of_update_split P hV hsplit
    (core_order_of_bridgeUpdateDeepGateCond_floor hCoreBoundary
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
      (pG := pG) (pSel := pSel) (qB := qB) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hpSel_dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
      pcF Ts Tp j0F mS S1tab F2tab hS1 hF2 hS1odd hF2odd
      S1L F2L hS1tab_eq hF2tab_eq hgate
      hm hqB_lt hQ1 hqB_def hpcF_dvd_Q hTs_le_mx hTp_le_mx hNcmx hNdeep_eq
      NDSuf NDPre hNDSuf hNDPre hNDSuf_floor hNDPre_floor hNDom_floor hNDp_floor
      hB_floor hn hn_floor hG hcfg_of_rank)
    (by
      intro r hclass
      exact atomOrd_update_suffix_split_branch_of_bridgeUpdateDeepGateCond_floor
        (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
        (pG := pG) (q_U := qB) (q_D := qB) (Q := Q) (Ndeep := Ndeep)
        (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
        (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
        hpG hp0dvd hQdvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
        hActive hAch pcF Ts Tp j0F mS S1tab F2tab hS1 hF2 hgate
        NSuf NDSuf hNSuf hNDSuf Fs hpc
        (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ1) hpcF_dvd_Q hm hn hNcmS hNcmx
        (by
          intro c'
          have hpcQ_le : pcF c' ≤ Q :=
            Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ1) (hpcF_dvd_Q c')
          have hTs := hTs_le_mx c'
          rw [hqB_def]
          omega)
        hbandSuf
        hNSuf_floor hNDSuf_floor hNDom_floor hNDp_floor hB_floor hn_floor hG
        hFs hags hselconstS hNdeep_eq
        (by
          intro c' l hlo hhi hlq hselD hach
          exact atomOrd_update_suffix_small_of_core_from_cfg
            (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
            (qB := qB) (mS := mS) (n := n) (Nc := Nc)
            (pcF := pcF) (Ts := Ts) (j0F := j0F)
            (S1 := S1L (n % pSel)) (F2 := F2L (n % pSel))
            (c := c) (ī := ī) hcore_from_cfg hcfg_of_rank c' l
            (hpc c') hNcmS hlo hhi hlq hselD hach)
        hclass)
    (by
      intro r hclass
      exact atomOrd_update_prefix_split_branch_of_bridgeUpdateDeepGateCond_floor
        (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
        (pG := pG) (q_U := qB) (q_D := qB) (Q := Q) (Ndeep := Ndeep)
        (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
        (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
        hpG hp0dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
        hActive hAch pcF Ts Tp j0F mS S1tab F2tab hS1 hF2 hgate
        NPre NDPre hNPre hNDPre Fp hpc
        (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ1) hpcF_dvd_Q hm hn hNcmS hNcmx
        (by
          intro c'
          have hpcQ_le : pcF c' ≤ Q :=
            Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ1) (hpcF_dvd_Q c')
          have hTp := hTp_le_mx c'
          rw [hqB_def]
          omega)
        hbandPre
        hNPre_floor hNDPre_floor hNDom_floor hNDp_floor hB_floor hn_floor hG
        hFp hagp hselconstP hNdeep_eq
        (by
          intro c' l hlo hhi hlq hselD hach
          exact atomOrd_update_prefix_small_of_core_from_cfg
            (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
            (qB := qB) (mS := mS) (n := n) (Nc := Nc)
            (pcF := pcF) (Tp := Tp) (j0F := j0F)
            (S1 := S1L (n % pSel)) (F2 := F2L (n % pSel))
            (c := c) (ī := ī) hcore_from_cfg hcfg_of_rank c' l
            (hpc c') hNcmS hlo hhi hlq hselD hach)
        hclass)

/-- Reverse automaton hook for the fully update-shaped canonical rows.  This
packages the common composition of DFA acceptance, the zero-base update-deep
gate family, and the update-split whole-order theorem. -/
theorem bridgeUpdateDeep_semantic_of_accepts_rank_updateSplit_floor_canonicalRows
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    (hCoreBoundary : CoreBoundaryUpdateZeroCoverage P hV)
    {B Bh M mthr pG pSel qB Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hpSel_dvd : pSel ∣ pG)
    (hQdvd : Q ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (hAch : CopiedAchieverLocus.DstarAchieverUpdateLocus P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1tab : Fin pG → S1Key P B qB qB → Finset ℕ)
    (F2tab : Fin pG → F2Key P Bh qB qB → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1tab r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2)
    (hS1odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1)
    (hF2odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1)
    (S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1)
    (hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1)
    (GdfaF : BridgeRowIndex P B Bh M pG qB qB Q Ndeep → ℕ →
      (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hGdfa : ∀ (idx : BridgeRowIndex P B Bh M pG qB qB Q Ndeep) (rN : ℕ)
        (c : Fin P.toPoly.K) (mS n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ),
        qB < mS → qB < mS → Bh ≤ n →
        (∀ i, ī i < (copiedSlice mS n).length) →
        (bridgeUpdateDeepGateCond P c B Bh M mthr pG qB qB Q Ndeep hpG idx j0F
            (fun _ _ => 0) rN mS n ī
          ↔ (GdfaF idx rN c).accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)))
    {n Nc mx : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hsplit :
      CopiedSelUniform.tieSemanticUpdateSplitAt P hV mS n c ī pcF Ts Tp Nc
        (fun _ _ => 0) j0F)
    (hacc :
      (GdfaF
          (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
            S1tab F2tab
            (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
            (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
            hS1 hF2
            (fun r c' x hx => updateDeepDsufRowTable_mem_lt
              (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
              (r := r) (c' := c') (k := x) hx)
            (fun r c' x hx => updateDeepDpreRowTable_mem_lt
              (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
              (r := r) (c' := c') (k := x) hx))
          (n % pG) c).accepts
        (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī))
    (hrank : P.rankOf (copiedSlice mS n) ⟨c, ī⟩ =
      CopiedDstar.dstarRankGA_m P hV mS n)
    (hm : 1 ≤ mS) (hqB_lt : qB < mS) (hQ1 : 1 ≤ Q)
    (hqB_def : qB = mx + Q + 1)
    (hpc : ∀ c' : Fin P.toPoly.K, 1 ≤ pcF c')
    (hpcF_dvd_Q : ∀ c' : Fin P.toPoly.K, pcF c' ∣ Q)
    (hTs_le_mx : ∀ c' : Fin P.toPoly.K, Ts c' ≤ mx)
    (hTp_le_mx : ∀ c' : Fin P.toPoly.K, Tp c' ≤ mx)
    (hNcmS : Nc ≤ mS - 1) (hNcmx : mS ≤ Nc + mx)
    (hbandSuf : ∀ c' : Fin P.toPoly.K, Ts c' + 2 * pcF c' ≤ mS - 1)
    (hbandPre : ∀ c' : Fin P.toPoly.K, Tp c' + 2 * pcF c' ≤ mS - 1)
    (hNdeep_eq : ∀ c' : Fin P.toPoly.K, Ndeep c' = mx + pcF c')
    (NSuf NPre NDSuf NDPre : Fin P.toPoly.K → ℕ)
    (hNSuf : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NSuf c' ≤ n → NSuf c' ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hNPre : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NPre c' ≤ n → NPre c' ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hNDSuf : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NDSuf c' ≤ n → NDSuf c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hNDPre : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NDPre c' ≤ n → NDPre c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hNSuf_floor : ∀ c' : Fin P.toPoly.K, NSuf c' ≤ Nfloor)
    (hNPre_floor : ∀ c' : Fin P.toPoly.K, NPre c' ≤ Nfloor)
    (hNDSuf_floor : ∀ c' : Fin P.toPoly.K, NDSuf c' ≤ Nfloor)
    (hNDPre_floor : ∀ c' : Fin P.toPoly.K, NDPre c' ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (Fs Fp : (c' : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (hFs : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Ts c') (pcF c') (Fs c'))
    (hFp : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Tp c') (pcF c') (Fp c'))
    (hags : ∀ c' : Fin P.toPoly.K, ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = Fs c' l)
    (hagp : ∀ c' : Fin P.toPoly.K, ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) =
          Fp c' l)
    (hselconstS : ∀ c' : Fin P.toPoly.K, ∀ l₁ l₂,
      Ts c' ≤ l₁ → l₁ < Nc → Ts c' ≤ l₂ → l₂ < Nc →
      (l₁ - Ts c') % pcF c' = (l₂ - Ts c') % pcF c' →
      ((P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₁))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₁)) = D)
        ↔ (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₂))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₂)) = D)))
    (hselconstP : ∀ c' : Fin P.toPoly.K, ∀ l₁ l₂,
      Tp c' ≤ l₁ → l₁ < Nc → Tp c' ≤ l₂ → l₂ < Nc →
      (l₁ - Tp c') % pcF c' = (l₂ - Tp c') % pcF c' →
      ((P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₁)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₁) = D)
        ↔ (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₂)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₂) = D)))
    (hcfg_of_rank : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
        (fun _ _ => ∅) mS n b)
    (hBh_n : Bh ≤ n) (hval : ∀ i, ī i < (copiedSlice mS n).length) :
    P.toPoly.sel c (copiedSlice mS n) ī
      ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
      ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ =
          CopiedDstar.dstarRankGA_m P hV mS n
      ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
          P.toPoly.labelOf (copiedSlice mS n) b = D →
          P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
          P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b := by
  have hgate :
      bridgeUpdateDeepGateCond P c B Bh M mthr pG qB qB Q Ndeep hpG
        (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
          S1tab F2tab
          (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
          (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
          hS1 hF2
          (fun r c' x hx => updateDeepDsufRowTable_mem_lt
            (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
            (r := r) (c' := c') (k := x) hx)
          (fun r c' x hx => updateDeepDpreRowTable_mem_lt
            (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
            (r := r) (c' := c') (k := x) hx))
        j0F (fun _ _ => 0) (n % pG) mS n ī := by
    exact (hGdfa
      (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1tab F2tab
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1 hF2
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx))
      (n % pG) c mS n ī hqB_lt hqB_lt hBh_n hval).mpr hacc
  refine ⟨hgate.1, hgate.2.1, hrank, ?_⟩
  intro b hbsel hbD hbrank
  exact whole_order_of_bridgeUpdateDeepGateCond_updateSplit_floor hCoreBoundary
    hpG hp0dvd hpSel_dvd hQdvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd hDomN hDpN
    hActive hAch pcF Ts Tp j0F mS S1tab F2tab hS1 hF2 hS1odd hF2odd
    S1L F2L hS1tab_eq hF2tab_eq hsplit hgate hm hqB_lt hQ1 hqB_def
    hpc hpcF_dvd_Q hTs_le_mx hTp_le_mx hNcmS hNcmx hbandSuf hbandPre
    hNdeep_eq NSuf NPre NDSuf NDPre hNSuf hNPre hNDSuf hNDPre
    hNSuf_floor hNPre_floor hNDSuf_floor hNDPre_floor hNDom_floor hNDp_floor
    hB_floor hn hn_floor hG Fs Fp hFs hFp hags hagp hselconstS hselconstP
    hcfg_of_rank b ⟨hbsel, hbD⟩ hbrank

/-- Combined semantic iff for the fully update-shaped canonical rows.  This is
the bridge-body core: the forward direction packages selector/rank soundness
into DFA acceptance, while the reverse direction replays DFA acceptance through
the update split and whole-order theorem. -/
theorem bridgeUpdateDeep_accepts_rank_iff_updateSplit_floor_canonicalRows
    {P : WRP.Presentation Step Step} {hV : P.Valid}
    (hCoreBoundary : CoreBoundaryUpdateZeroCoverage P hV)
    {B Bh M mthr pG pSel qB Q : ℕ} {Ndeep : Fin P.toPoly.K → ℕ}
    {p0 pDomN pDpN NDomN NDpN Nfloor : ℕ}
    (hpG : 1 ≤ pG) (hp0dvd : p0 ∣ pG) (hpSel_dvd : pSel ∣ pG)
    (hQdvd : Q ∣ pG)
    (hpDomN : 1 ≤ pDomN) (hpDpN : 1 ≤ pDpN)
    (hpDomN_dvd : pDomN ∣ pG) (hpDpN_dvd : pDpN ∣ pG)
    (hDomN : ∀ mS, 1 ≤ mS → ∀ n, NDomN ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + pDomN)) ↔
       P.toPoly.domain (copiedSlice mS n)))
    (hDpN : ∀ mS, 1 ≤ mS → ∀ n, NDpN ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + pDpN)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + pDpN)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)))
    (hSound : CopiedBoundedGateBand.BandedUpdateRankSoundness P hV)
    (hActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (hAch : CopiedAchieverLocus.DstarAchieverUpdateLocus P hV)
    (pcF Ts Tp : (c' : Fin P.toPoly.K) → ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (mS : ℕ)
    (S1tab : Fin pG → S1Key P B qB qB → Finset ℕ)
    (F2tab : Fin pG → F2Key P Bh qB qB → Finset ℕ)
    (hS1 : ∀ r key x, x ∈ S1tab r key → x < M)
    (hF2 : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2)
    (hS1odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1)
    (hF2odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1)
    (S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1)
    (hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1)
    (GdfaF : BridgeRowIndex P B Bh M pG qB qB Q Ndeep → ℕ →
      (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hGdfa : ∀ (idx : BridgeRowIndex P B Bh M pG qB qB Q Ndeep) (rN : ℕ)
        (c : Fin P.toPoly.K) (mS n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ),
        qB < mS → qB < mS → Bh ≤ n →
        (∀ i, ī i < (copiedSlice mS n).length) →
        (bridgeUpdateDeepGateCond P c B Bh M mthr pG qB qB Q Ndeep hpG idx j0F
            (fun _ _ => 0) rN mS n ī
          ↔ (GdfaF idx rN c).accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)))
    {n Nc mx : ℕ} {c : Fin P.toPoly.K} {ī : Fin (P.toPoly.arity c) → ℕ}
    (hsplit :
      CopiedSelUniform.tieSemanticUpdateSplitAt P hV mS n c ī pcF Ts Tp Nc
        (fun _ _ => 0) j0F)
    (hm : 1 ≤ mS) (hqB_lt : qB < mS) (hQ1 : 1 ≤ Q)
    (hqB_def : qB = mx + Q + 1)
    (hpc : ∀ c' : Fin P.toPoly.K, 1 ≤ pcF c')
    (hpcF_dvd_Q : ∀ c' : Fin P.toPoly.K, pcF c' ∣ Q)
    (hTs_le_mx : ∀ c' : Fin P.toPoly.K, Ts c' ≤ mx)
    (hTp_le_mx : ∀ c' : Fin P.toPoly.K, Tp c' ≤ mx)
    (hNcmS : Nc ≤ mS - 1) (hNcmx : mS ≤ Nc + mx)
    (hbandSuf : ∀ c' : Fin P.toPoly.K, Ts c' + 2 * pcF c' ≤ mS - 1)
    (hbandPre : ∀ c' : Fin P.toPoly.K, Tp c' + 2 * pcF c' ≤ mS - 1)
    (hNdeep_eq : ∀ c' : Fin P.toPoly.K, Ndeep c' = mx + pcF c')
    (hNdeep_add2 : ∀ c' : Fin P.toPoly.K, Ndeep c' + 2 ≤ mS)
    (NSuf NPre NDSuf NDPre : Fin P.toPoly.K → ℕ)
    (hNSuf : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NSuf c' ≤ n → NSuf c' ≤ n' → n % p0 = n' % p0 →
      (mS + 2 * n + 1 + Ts c') % Q =
        (mS + 2 * n' + 1 + Ts c') % Q →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Ts c') Q =
        CopiedBoundedGateBand.updateSufAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Ts c') Q)
    (hNPre : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NPre c' ≤ n → NPre c' ≤ n' → n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n (pcF c') (Tp c') Q =
        CopiedBoundedGateBand.updatePreAbsTieSet P hV c' (j0F c')
          (fun _ : Fin (P.toPoly.arity c') => 0) mS n' (pcF c') (Tp c') Q)
    (hNDSuf : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NDSuf c' ≤ n → NDSuf c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inl (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hNDPre : ∀ c' : Fin P.toPoly.K, ∀ n n',
      NDPre c' ≤ n → NDPre c' ≤ n' →
      B + 1 + B + 1 ≤ n → B + 1 + B + 1 ≤ n' →
      n % p0 = n' % p0 →
      CopiedAchSetFold.domDp P mS n → CopiedAchSetFold.domDp P mS n' →
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n))
            = CopiedDstar.dstarRankGA_m P hV mS n)
        =
      (Finset.range (Ndeep c')).filter (fun k =>
          P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
                (mixedPosAt
                  (Sum.inr (Sum.inr (k + 1)) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
                  mS (B + 1) n'))
            = CopiedDstar.dstarRankGA_m P hV mS n'))
    (hNSuf_floor : ∀ c' : Fin P.toPoly.K, NSuf c' ≤ Nfloor)
    (hNPre_floor : ∀ c' : Fin P.toPoly.K, NPre c' ≤ Nfloor)
    (hNDSuf_floor : ∀ c' : Fin P.toPoly.K, NDSuf c' ≤ Nfloor)
    (hNDPre_floor : ∀ c' : Fin P.toPoly.K, NDPre c' ≤ Nfloor)
    (hNDom_floor : NDomN ≤ Nfloor) (hNDp_floor : NDpN ≤ Nfloor)
    (hB_floor : B + 1 + B + 1 ≤ Nfloor)
    (hn : 1 ≤ n) (hn_floor : Nfloor ≤ n)
    (hG : CopiedAchSetFold.domDp P mS n)
    (Fs Fp : (c' : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (hFs : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Ts c') (pcF c') (Fs c'))
    (hFp : ∀ c' : Fin P.toPoly.K,
      CopiedDstarCMS.RankAffineAtFrom (Tp c') (pcF c') (Fp c'))
    (hags : ∀ c' : Fin P.toPoly.K, ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
          (mS + 2 * n + 1 + l)) = Fs c' l)
    (hagp : ∀ c' : Fin P.toPoly.K, ∀ l, l < mS - 1 →
      P.rank c' (copiedSlice mS n)
        (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l) =
          Fp c' l)
    (hselconstS : ∀ c' : Fin P.toPoly.K, ∀ l₁ l₂,
      Ts c' ≤ l₁ → l₁ < Nc → Ts c' ≤ l₂ → l₂ < Nc →
      (l₁ - Ts c') % pcF c' = (l₂ - Ts c') % pcF c' →
      ((P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₁))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₁)) = D)
        ↔ (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₂))
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c')
              (mS + 2 * n + 1 + l₂)) = D)))
    (hselconstP : ∀ c' : Fin P.toPoly.K, ∀ l₁ l₂,
      Tp c' ≤ l₁ → l₁ < Nc → Tp c' ≤ l₂ → l₂ < Nc →
      (l₁ - Tp c') % pcF c' = (l₂ - Tp c') % pcF c' →
      ((P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₁)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₁) = D)
        ↔ (P.toPoly.sel c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₂)
          ∧ P.toPoly.label c' (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) (j0F c') l₂) = D)))
    (hcfgRank : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
        (fun _ _ => ∅) mS n b →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n)
    (hcfg_of_rank : ∀ b : P.toPoly.Atom,
      P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
        (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
        (fun _ _ => ∅) mS n b)
    (hBh_n : Bh ≤ n) (hval : ∀ i, ī i < (copiedSlice mS n).length) :
    ((P.toPoly.sel c (copiedSlice mS n) ī
        ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
        ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ =
            CopiedDstar.dstarRankGA_m P hV mS n
        ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
            P.toPoly.labelOf (copiedSlice mS n) b = D →
            P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
            P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
      ↔ ((GdfaF
          (mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
            S1tab F2tab
            (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
            (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
            hS1 hF2
            (fun r c' x hx => updateDeepDsufRowTable_mem_lt
              (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
              (r := r) (c' := c') (k := x) hx)
            (fun r c' x hx => updateDeepDpreRowTable_mem_lt
              (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
              (r := r) (c' := c') (k := x) hx))
          (n % pG) c).accepts
            (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)
        ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ =
            CopiedDstar.dstarRankGA_m P hV mS n)) := by
  constructor
  · rintro ⟨hselU, hlabelU, hrank, hall⟩
    exact bridgeUpdateDeep_accepts_rank_of_updateDeepRow_floor_canonicalRows
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
      (pG := pG) (pSel := pSel) (q_U := qB) (q_D := qB) (Q := Q)
      (Ndeep := Ndeep) (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hpG hp0dvd hQdvd hpSel_dvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd
      hDomN hDpN hSound pcF Ts Tp j0F mS S1tab F2tab hS1 hF2 hS1odd hF2odd
      S1L F2L hS1tab_eq hF2tab_eq NSuf NPre NDSuf NDPre
      hNSuf hNPre hNDSuf hNDPre Fs Fp GdfaF hGdfa
      hselU hlabelU hrank hall hcfgRank hpc
      (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ1) hpcF_dvd_Q hm hn hn_floor hG
      (by
        intro c'
        rw [hqB_def]
        have := hTs_le_mx c'
        omega)
      (by
        intro c'
        rw [hqB_def]
        have := hTp_le_mx c'
        omega)
      hbandSuf hbandPre hNdeep_add2 hNSuf_floor hNPre_floor hNDSuf_floor
      hNDPre_floor hNDom_floor hNDp_floor hB_floor hFs hFp hags hagp
      hqB_lt hqB_lt hBh_n hval
  · rintro ⟨hacc, hrank⟩
    exact bridgeUpdateDeep_semantic_of_accepts_rank_updateSplit_floor_canonicalRows
      hCoreBoundary hpG hp0dvd hpSel_dvd hQdvd hpDomN hpDpN hpDomN_dvd hpDpN_dvd
      hDomN hDpN hActive hAch pcF Ts Tp j0F mS S1tab F2tab hS1 hF2 hS1odd hF2odd
      S1L F2L hS1tab_eq hF2tab_eq GdfaF hGdfa hsplit hacc hrank
      hm hqB_lt hQ1 hqB_def hpc hpcF_dvd_Q hTs_le_mx hTp_le_mx hNcmS hNcmx
      hbandSuf hbandPre hNdeep_eq NSuf NPre NDSuf NDPre hNSuf hNPre hNDSuf hNDPre
      hNSuf_floor hNPre_floor hNDSuf_floor hNDPre_floor hNDom_floor hNDp_floor
      hB_floor hn hn_floor hG Fs Fp hFs hFp hags hagp hselconstS hselconstP
      hcfg_of_rank hBh_n hval

/-- Abstract package for the budgeted row-indexed tie bridge.  The arity-1 proof
above is one supplier; the arbitrary-arity route should supply the same package
without using `harity1`. -/
def TiePointBridgeBudgetedIndexed (P : WRP.Presentation Step Step) (hV : P.Valid)
    (C : ℕ) : Prop :=
    ∃ (B Bh M _mthr pG q_U q_D Q : ℕ) (Ndeep : Fin P.toPoly.K → ℕ) (Mbr : ℕ),
      1 ≤ pG ∧ 1 ≤ Mbr ∧
      ∃ (GdfaF : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep → ℕ →
          (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))),
        ∀ (mS : ℕ), Mbr ≤ mS →
          (∀ n, P.toPoly.domain (copiedSlice mS n) →
            ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
              (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
              l.length ≤ C * (mS + n + 1)) →
          ∃ idx : BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep, ∃ Nbr,
            ∀ n, Nbr ≤ n → P.toPoly.domain (copiedSlice mS n) →
              (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
                P.toPoly.labelOf (copiedSlice mS n) a = D) →
              ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
                (∀ i, ī i < (copiedSlice mS n).length) →
                ((P.toPoly.sel c (copiedSlice mS n) ī
                    ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
                    ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩
                        = CopiedDstar.dstarRankGA_m P hV mS n
                    ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
                        P.toPoly.labelOf (copiedSlice mS n) b = D →
                        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
                        P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
                 ↔ ((GdfaF idx (n % pG) c).accepts
                        (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)
                    ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩
                        = CopiedDstar.dstarRankGA_m P hV mS n))

/-- Direct budgeted bridge from canonical zero-base update suppliers.  This is
the arbitrary-arity bridge route up to the remaining supplier construction:
the row index is the update-shaped `mkBridgeUpdateRowIndex`, and the inner
semantic equivalence is delegated to
`bridgeUpdateDeep_accepts_rank_iff_updateSplit_floor_canonicalRows`. -/
theorem tie_point_bridge_budgeted_indexed_of_update_zero_suppliers
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (C : ℕ)
    (hSplitZero : CopiedSelUniform.TieSemanticUpdateZeroSplitData P hV)
    (CbudN : ℕ)
    (hbudCN : ∀ (mS : ℕ), 1 ≤ mS →
      ∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ CbudN * (mS + n + 1))
    (hRunResidue : RunResidueUpdateCoverage P hV)
    (hBandActive : CopiedBoundedGateBand.BandedUpdateActivationCompleteness P hV)
    (hCoreBoundary : CoreBoundaryUpdateZeroCoverage P hV) :
    TiePointBridgeBudgetedIndexed P hV C := by
  classical
  rcases hSplitZero with
    ⟨Mc, pcF, Ts, Tp, ī0F, j0F, mx, hzero, hmx1, hpcF1, hTs_le_mx, hTp_le_mx,
      _hMc, _hsufcyc, _hprefcyc, hsplitData⟩
  subst ī0F
  obtain ⟨B, Bh, M, mthr, _pstar, pSel, _hpstar, _hpstardvd, hpSel, hBB, hM2, hBh1,
    _hB1, hselBudget⟩ := CopiedSelector.eqRankD_cell_selector_fibred P hV
  have hAch : CopiedAchieverLocus.DstarAchieverUpdateLocus P hV := hRunResidue.1
  have hSound : CopiedBoundedGateBand.BandedUpdateRankSoundness P hV := hRunResidue.2
  set Q : ℕ := ∏ c' : Fin P.toPoly.K, pcF c' with hQdef
  have hQ1 : 1 ≤ Q := by
    rw [hQdef]
    exact Finset.prod_pos (fun c' _ => Nat.lt_of_lt_of_le Nat.zero_lt_one (hpcF1 c'))
  have hpcF_dvd_Q : ∀ c' : Fin P.toPoly.K, pcF c' ∣ Q := by
    intro c'
    rw [hQdef]
    exact Finset.dvd_prod_of_mem pcF (Finset.mem_univ c')
  obtain ⟨p0, NDomN, pDomN, NDpN, pDpN, pG, hp0, hpDomN, hpDpN, hpG,
      hpSel_dvd_pG, hp0_dvd_pG, hpDomN_dvd_pG, hpDpN_dvd_pG, hQ_dvd_pG,
      hNSufPeriod, hNPrePeriod, hNDSufPeriod, hNDPrePeriod, hDomN, hDpN⟩ :=
    bridgeUpdateDeepGlobalPeriodSuppliers_of_budget P hV CbudN hbudCN pSel Q hpSel hQ1
  set qB : ℕ := mx + Q + 1 with hqB_def
  set Ndeep : Fin P.toPoly.K → ℕ := fun c' => mx + pcF c' with hNdeep_def
  obtain ⟨GdfaF, hGdfa⟩ :=
    bridgeUpdateDeepRowIndex_gate_family_zeroBase P B Bh M mthr pG qB qB Q Ndeep hpG
      (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ1) hBB hBh1 hM2 j0F
  set Mbr : ℕ := max (max (max 1 (qB + 1)) (2 * Bh + 2))
    ((Finset.univ.sup fun c' : Fin P.toPoly.K =>
      max (max (Ts c' + 2 * pcF c' + 3) (Tp c' + 2 * pcF c' + 3)) (Ndeep c' + 2)))
    with hMbrdef
  refine ⟨B, Bh, M, mthr, pG, qB, qB, Q, Ndeep, Mbr, hpG, ?_, GdfaF, ?_⟩
  · exact le_trans (le_max_left 1 (qB + 1))
      (le_trans (le_max_left _ (2 * Bh + 2)) (le_max_left _ _))
  · intro mS hMbrle hbud
    have hm : 1 ≤ mS := by
      have h1Mbr : 1 ≤ Mbr := by
        rw [hMbrdef]
        exact le_trans (le_max_left 1 (qB + 1))
          (le_trans (le_max_left _ (2 * Bh + 2)) (le_max_left _ _))
      exact le_trans h1Mbr hMbrle
    have hqB_lt : qB < mS := by
      have hqBs : qB + 1 ≤ Mbr := by
        rw [hMbrdef]
        exact le_trans (le_max_right 1 (qB + 1))
          (le_trans (le_max_left _ (2 * Bh + 2)) (le_max_left _ _))
      have := le_trans hqBs hMbrle
      omega
    have hmx_lt : mx < mS := by
      have hqBmx : mx < qB := by rw [hqB_def]; omega
      omega
    have hactBandSuf : ∀ c' : Fin P.toPoly.K, Ts c' + 2 * pcF c' ≤ mS - 1 := by
      intro c'
      have hsup :
          max (max (Ts c' + 2 * pcF c' + 3) (Tp c' + 2 * pcF c' + 3))
              (Ndeep c' + 2)
            ≤ Finset.univ.sup (fun c' : Fin P.toPoly.K =>
              max (max (Ts c' + 2 * pcF c' + 3) (Tp c' + 2 * pcF c' + 3))
                (Ndeep c' + 2)) :=
        Finset.le_sup
          (f := fun c' : Fin P.toPoly.K =>
            max (max (Ts c' + 2 * pcF c' + 3) (Tp c' + 2 * pcF c' + 3))
              (Ndeep c' + 2))
          (Finset.mem_univ c')
      have hterm : Ts c' + 2 * pcF c' + 3 ≤ Mbr := by
        rw [hMbrdef]
        exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsup)
          (le_max_right _ _)
      have := le_trans hterm hMbrle
      omega
    have hactBandPre : ∀ c' : Fin P.toPoly.K, Tp c' + 2 * pcF c' ≤ mS - 1 := by
      intro c'
      have hsup :
          max (max (Ts c' + 2 * pcF c' + 3) (Tp c' + 2 * pcF c' + 3))
              (Ndeep c' + 2)
            ≤ Finset.univ.sup (fun c' : Fin P.toPoly.K =>
              max (max (Ts c' + 2 * pcF c' + 3) (Tp c' + 2 * pcF c' + 3))
                (Ndeep c' + 2)) :=
        Finset.le_sup
          (f := fun c' : Fin P.toPoly.K =>
            max (max (Ts c' + 2 * pcF c' + 3) (Tp c' + 2 * pcF c' + 3))
              (Ndeep c' + 2))
          (Finset.mem_univ c')
      have hterm : Tp c' + 2 * pcF c' + 3 ≤ Mbr := by
        rw [hMbrdef]
        exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsup)
          (le_max_right _ _)
      have := le_trans hterm hMbrle
      omega
    have hNdeep_add2_le_mS : ∀ c' : Fin P.toPoly.K, Ndeep c' + 2 ≤ mS := by
      intro c'
      have hsup :
          max (max (Ts c' + 2 * pcF c' + 3) (Tp c' + 2 * pcF c' + 3))
              (Ndeep c' + 2)
            ≤ Finset.univ.sup (fun c' : Fin P.toPoly.K =>
              max (max (Ts c' + 2 * pcF c' + 3) (Tp c' + 2 * pcF c' + 3))
                (Ndeep c' + 2)) :=
        Finset.le_sup
          (f := fun c' : Fin P.toPoly.K =>
            max (max (Ts c' + 2 * pcF c' + 3) (Tp c' + 2 * pcF c' + 3))
              (Ndeep c' + 2))
          (Finset.mem_univ c')
      have hterm : Ndeep c' + 2 ≤ Mbr := by
        rw [hMbrdef]
        exact le_trans (le_trans (le_max_right _ _) hsup) (le_max_right _ _)
      exact le_trans hterm hMbrle
    obtain ⟨Nsel, S1L, F2L, hNselGeo, hS1hyg, hF2hyg, hsel⟩ :=
      hselBudget C mS hm hbud
    choose NSuf hNSuf using fun c' : Fin P.toPoly.K =>
      hNSufPeriod c' (j0F c') (Ts c') (pcF c') mS Q hm (hactBandSuf c')
    choose NPre hNPre using fun c' : Fin P.toPoly.K =>
      hNPrePeriod c' (j0F c') (Tp c') (pcF c') mS Q hm (hactBandPre c')
    choose NDSuf hNDSuf using fun c' : Fin P.toPoly.K =>
      hNDSufPeriod c' (j0F c') B mS (Ndeep c') hm (hNdeep_add2_le_mS c')
    choose NDPre hNDPre using fun c' : Fin P.toPoly.K =>
      hNDPrePeriod c' (j0F c') B mS (Ndeep c') hm (hNdeep_add2_le_mS c')
    set Nact : ℕ := max (max NDomN NDpN) (Finset.univ.sup fun c' : Fin P.toPoly.K =>
      max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c'))) with hNact_def
    set Nfloor : ℕ := max (max Nsel (2 * Bh + 2)) Nact with hNfloor_def
    have hNsel_le_floor : Nsel ≤ Nfloor := by
      rw [hNfloor_def]
      exact le_trans (le_max_left Nsel (2 * Bh + 2)) (le_max_left _ Nact)
    have hBh_floor : 2 * Bh + 2 ≤ Nfloor := by
      rw [hNfloor_def]
      exact le_trans (le_max_right Nsel (2 * Bh + 2)) (le_max_left _ Nact)
    have hB_floor : B + 1 + B + 1 ≤ Nfloor := by
      have := hBh_floor
      have hBB' : B + 1 + B + 1 ≤ 2 * Bh + 2 := by omega
      omega
    have hNDomN_floor : NDomN ≤ Nfloor := by
      rw [hNfloor_def, hNact_def]
      exact le_trans (le_trans (le_max_left NDomN NDpN) (le_max_left _ _))
        (le_max_right _ _)
    have hNDpN_floor : NDpN ≤ Nfloor := by
      rw [hNfloor_def, hNact_def]
      exact le_trans (le_trans (le_max_right NDomN NDpN) (le_max_left _ _))
        (le_max_right _ _)
    have hNSuf_floor : ∀ c' : Fin P.toPoly.K, NSuf c' ≤ Nfloor := by
      intro c'
      rw [hNfloor_def, hNact_def]
      have hsup :
          max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c'))
            ≤ Finset.univ.sup (fun c' : Fin P.toPoly.K =>
              max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c'))) :=
        Finset.le_sup
          (f := fun c' : Fin P.toPoly.K =>
            max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c')))
          (Finset.mem_univ c')
      exact le_trans
        (le_trans (le_trans (le_max_left (NSuf c') (NPre c')) (le_max_left _ _)) hsup)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    have hNPre_floor : ∀ c' : Fin P.toPoly.K, NPre c' ≤ Nfloor := by
      intro c'
      rw [hNfloor_def, hNact_def]
      have hsup :
          max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c'))
            ≤ Finset.univ.sup (fun c' : Fin P.toPoly.K =>
              max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c'))) :=
        Finset.le_sup
          (f := fun c' : Fin P.toPoly.K =>
            max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c')))
          (Finset.mem_univ c')
      exact le_trans
        (le_trans (le_trans (le_max_right (NSuf c') (NPre c')) (le_max_left _ _)) hsup)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    have hNDSuf_floor : ∀ c' : Fin P.toPoly.K, NDSuf c' ≤ Nfloor := by
      intro c'
      rw [hNfloor_def, hNact_def]
      have hsup :
          max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c'))
            ≤ Finset.univ.sup (fun c' : Fin P.toPoly.K =>
              max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c'))) :=
        Finset.le_sup
          (f := fun c' : Fin P.toPoly.K =>
            max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c')))
          (Finset.mem_univ c')
      exact le_trans
        (le_trans (le_trans (le_max_left (NDSuf c') (NDPre c')) (le_max_right _ _)) hsup)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    have hNDPre_floor : ∀ c' : Fin P.toPoly.K, NDPre c' ≤ Nfloor := by
      intro c'
      rw [hNfloor_def, hNact_def]
      have hsup :
          max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c'))
            ≤ Finset.univ.sup (fun c' : Fin P.toPoly.K =>
              max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c'))) :=
        Finset.le_sup
          (f := fun c' : Fin P.toPoly.K =>
            max (max (NSuf c') (NPre c')) (max (NDSuf c') (NDPre c')))
          (Finset.mem_univ c')
      exact le_trans
        (le_trans (le_trans (le_max_right (NDSuf c') (NDPre c')) (le_max_right _ _)) hsup)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    set S1tab : Fin pG → S1Key P B qB qB → Finset ℕ :=
      fun r key => S1L (r.1 % pSel) key.1 key.2.1 with hS1tab_def
    set F2tab : Fin pG → F2Key P Bh qB qB → Finset ℕ :=
      fun r key => F2L (r.1 % pSel) key.1 key.2.1 with hF2tab_def
    have hS1tab_bound : ∀ r key x, x ∈ S1tab r key → x < M := by
      intro r key x hx
      rw [hS1tab_def] at hx
      exact (hS1hyg (r.1 % pSel) key.1 key.2.1 x hx).1
    have hS1tab_odd : ∀ r key x, x ∈ S1tab r key → x % 2 = 1 := by
      intro r key x hx
      rw [hS1tab_def] at hx
      exact (hS1hyg (r.1 % pSel) key.1 key.2.1 x hx).2
    have hF2tab_bound : ∀ r key x, x ∈ F2tab r key → x < 2 * Bh + 2 := by
      intro r key x hx
      rw [hF2tab_def] at hx
      exact (hF2hyg (r.1 % pSel) key.1 key.2.1 x hx).1
    have hF2tab_odd : ∀ r key x, x ∈ F2tab r key → x % 2 = 1 := by
      intro r key x hx
      rw [hF2tab_def] at hx
      exact (hF2hyg (r.1 % pSel) key.1 key.2.1 x hx).2
    have hS1tab_eq : ∀ r key, S1tab r key = S1L (r.1 % pSel) key.1 key.2.1 := by
      intro r key
      rw [hS1tab_def]
    have hF2tab_eq : ∀ r key, F2tab r key = F2L (r.1 % pSel) key.1 key.2.1 := by
      intro r key
      rw [hF2tab_def]
    let idx : BridgeRowIndex P B Bh M pG qB qB Q Ndeep :=
      mkBridgeUpdateRowIndex (Q := Q) hV pcF Ts Tp j0F mS (rowRep pG Nfloor)
        S1tab F2tab
        (updateDeepDsufRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        (updateDeepDpreRowTable (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor))
        hS1tab_bound hF2tab_bound
        (fun r c' x hx => updateDeepDsufRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
        (fun r c' x hx => updateDeepDpreRowTable_mem_lt
          (B := B) P hV Ndeep j0F mS (rowRep pG Nfloor)
          (r := r) (c' := c') (k := x) hx)
    refine ⟨idx, Nfloor, ?_⟩
    intro n hn hdom hDpres c ī hval
    obtain ⟨FFs, FFp, Nc, hNcmS, hNcmx, _hNcs, _hNcp, hFs, hFp, hags, hagp,
      _hupdvals, _hupdvalp, hselconstS, hselconstP, hsplitAll⟩ :=
      hsplitData mS (le_of_lt hmx_lt) n
    have hNsel_n : Nsel ≤ n := le_trans hNsel_le_floor hn
    have hn1 : 1 ≤ n := by
      have := le_trans hBh_floor hn
      omega
    have hBh_n : Bh ≤ n := by
      have := le_trans hBh_floor hn
      omega
    have hG : CopiedAchSetFold.domDp P mS n := ⟨hdom, hDpres⟩
    have hNdeep_eq : ∀ c' : Fin P.toPoly.K, Ndeep c' = mx + pcF c' := by
      intro c'
      rw [hNdeep_def]
    have hcfgRank : ∀ b : P.toPoly.Atom,
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
          (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
          (fun _ _ => ∅) mS n b →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n := by
      intro b hbsel hbD hcfg
      exact (hsel n hNsel_n hdom hDpres b hbsel hbD).mpr hcfg
    have hcfg_of_rank : ∀ b : P.toPoly.Atom,
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
        CopiedTieGate.cfgCellGAFL B Bh M mthr (S1L (n % pSel))
          (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % pSel))
          (fun _ _ => ∅) mS n b := by
      intro b hbsel hbD hrank
      exact (hsel n hNsel_n hdom hDpres b hbsel hbD).mp hrank
    dsimp [idx]
    exact bridgeUpdateDeep_accepts_rank_iff_updateSplit_floor_canonicalRows
      (P := P) (hV := hV) (B := B) (Bh := Bh) (M := M) (mthr := mthr)
      (pG := pG) (pSel := pSel) (qB := qB) (Q := Q) (Ndeep := Ndeep)
      (p0 := p0) (pDomN := pDomN) (pDpN := pDpN)
      (NDomN := NDomN) (NDpN := NDpN) (Nfloor := Nfloor)
      hCoreBoundary hpG hp0_dvd_pG hpSel_dvd_pG hQ_dvd_pG hpDomN hpDpN
      hpDomN_dvd_pG hpDpN_dvd_pG hDomN hDpN hSound hBandActive hAch
      pcF Ts Tp j0F mS S1tab F2tab hS1tab_bound hF2tab_bound hS1tab_odd hF2tab_odd
      S1L F2L hS1tab_eq hF2tab_eq GdfaF hGdfa (hsplitAll c ī)
      hm hqB_lt hQ1 hqB_def hpcF1 hpcF_dvd_Q hTs_le_mx hTp_le_mx hNcmS hNcmx
      hactBandSuf hactBandPre hNdeep_eq hNdeep_add2_le_mS
      NSuf NPre NDSuf NDPre hNSuf hNPre hNDSuf hNDPre
      hNSuf_floor hNPre_floor hNDSuf_floor hNDPre_floor hNDomN_floor hNDpN_floor
      hB_floor hn1 hn hG FFs FFp hFs hFp hags hagp hselconstS hselconstP
      hcfgRank hcfg_of_rank hBh_n hval

/-- Canonical zero-base suppliers with zero-boundary coverage feed the
row-indexed bridge directly, without tuple-fibre scalarization. -/
theorem tie_point_bridge_budgeted_indexed_of_update_zero_boundary_bundle
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (C : ℕ) (hUpdate : BridgeUpdateZeroBoundarySupplierBundle P hV) :
    TiePointBridgeBudgetedIndexed P hV C := by
  rcases hUpdate with
    ⟨hSplitZero, _hRunClassUpdate, ⟨CbudN, hbudCN⟩, hRunResidueUpdate,
      hBandActiveUpdate, hCoreBoundaryUpdate⟩
  exact tie_point_bridge_budgeted_indexed_of_update_zero_suppliers P hV C hSplitZero
    CbudN hbudCN hRunResidueUpdate hBandActiveUpdate
    hCoreBoundaryUpdate

/-- Canonical zero-base update suppliers feed the row-indexed bridge directly,
without tuple-fibre scalarization. -/
theorem tie_point_bridge_budgeted_indexed_of_update_zero_bundle
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (C : ℕ) (hUpdate : BridgeUpdateZeroSupplierBundle P hV) :
    TiePointBridgeBudgetedIndexed P hV C :=
  tie_point_bridge_budgeted_indexed_of_update_zero_boundary_bundle P hV C
    (bridgeUpdateZeroBoundarySupplierBundle_of_zeroSupplierBundle P hV hUpdate)

end CopiedTieSlice
