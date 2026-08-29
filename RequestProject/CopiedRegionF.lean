/-
# Fibred descriptor algebra (§9 tower, Stage F3.2)

The `RegionSpecF` analogues of the wrapped descriptor toolkit
(`SliceDstarGateGA` / `SliceFasSelectorGA` / `SliceCellConvGA`), per
Stage F3.2.  Boundary (stretch) constructors are base-independent
positions, so every map treats them as identities; `core` constructors defer
to the wrapped lemmas under the `mS − 1` shift:

* `clusterFreeF` (Bool-valued — decision D10) with base-independence;
* `regionLiftF` — bound enlargement (positions, validity, cluster-freedom
  preserved);
* `refreezeFrontF` / `refreezeBackF` — the zone re-descriptions, and the
  bundled `freeze_front_descrF` / `freeze_back_descrF` (any front/back-zone
  cell is a cluster-free cell over the enlarged bound at the dummy base
  `Bh + 1`, validity preserved);
* `cellTupleF_valid` — cell tuples are in-slice on the window;
* `clusterWidthF` — the bulk width, with the member bound and `≤ Z`.
-/
import RequestProject.CopiedDstar
import RequestProject.SliceDstarGateGA

namespace CopiedRegionF

open SliceFamilyCell SliceDstarGateGA CopiedCells CopiedDstar

/-! ## Cluster-freedom (Bool-valued) -/

/-- A fibred descriptor is cluster-free when it does not ride the mobile
window; stretch descriptors never do. -/
def clusterFreeF {B : ℕ} : RegionSpecF B → Bool
  | .core (.cluster _ _) => false
  | _ => true

theorem clusterFreeF_core {B : ℕ} (r : RegionSpec B) :
    clusterFreeF (RegionSpecF.core r) = true ↔ clusterFree r := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp [clusterFreeF, clusterFree]

/-- Cluster-free fibred descriptors ignore the base. -/
theorem clusterFreeF_posAt_base {B : ℕ} (r : RegionSpecF B)
    (hcf : clusterFreeF r = true) (mS t t' n : ℕ) :
    r.posAt mS t n = r.posAt mS t' n := by
  rcases r with r | q | l
  · rcases r with _ | _ | ⟨f, e⟩ | ⟨l', e⟩ | ⟨δ, e⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [clusterFreeF] at hcf
  · rfl
  · rfl

/-- Cluster-free cell tuples ignore the base entirely. -/
theorem cellTupleF_clusterFree_base {B k : ℕ} (rs : Fin k → RegionSpecF B)
    (hcf : ∀ i, clusterFreeF (rs i) = true) (mS t t' n : ℕ) :
    cellTupleF rs mS t n = cellTupleF rs mS t' n :=
  funext fun i => clusterFreeF_posAt_base (rs i) (hcf i) mS t t' n

/-! ## Bound enlargement -/

/-- Lift a fibred descriptor along an enlargement of the pin/offset bound. -/
def regionLiftF {B B' : ℕ} (h : B ≤ B') : RegionSpecF B → RegionSpecF B'
  | .core r => .core (regionLift h r)
  | .prefIdx q => .prefIdx q
  | .sufIdx l => .sufIdx l

theorem regionLiftF_posAt {B B' : ℕ} (h : B ≤ B') (r : RegionSpecF B)
    (mS t n : ℕ) : (regionLiftF h r).posAt mS t n = r.posAt mS t n := by
  rcases r with r | q | l
  · show mS - 1 + (regionLift h r).posAt t n = mS - 1 + r.posAt t n
    rw [regionLift_posAt]
  · rfl
  · rfl

theorem regionLiftF_valid {B B' : ℕ} (h : B ≤ B') (r : RegionSpecF B)
    (mS : ℕ) : (regionLiftF h r).valid mS ↔ r.valid mS := by
  rcases r with r | q | l <;> exact Iff.rfl

theorem clusterFreeF_regionLiftF {B B' : ℕ} (h : B ≤ B') (r : RegionSpecF B) :
    clusterFreeF (regionLiftF h r) = clusterFreeF r := by
  rcases r with r | q | l
  · rcases r with _ | _ | ⟨f, e⟩ | ⟨l', e⟩ | ⟨δ, e⟩ <;> rfl
  · rfl
  · rfl

theorem cellTupleF_regionLiftF {B B' k : ℕ} (h : B ≤ B')
    (rs : Fin k → RegionSpecF B) (mS t n : ℕ) :
    cellTupleF (fun i => regionLiftF h (rs i)) mS t n = cellTupleF rs mS t n :=
  funext fun i => regionLiftF_posAt h (rs i) mS t n

/-! ## Zone re-descriptions -/

/-- The fibred front-zone re-freeze: core clusters re-pin as fronts at
`t + δ`; stretch descriptors pass through. -/
def refreezeFrontF {B B' : ℕ} (hBB' : B ≤ B') (t : ℕ) (htB : t + B ≤ B') :
    RegionSpecF B → RegionSpecF B'
  | .core r => .core (refreezeFront hBB' t htB r)
  | .prefIdx q => .prefIdx q
  | .sufIdx l => .sufIdx l

theorem clusterFreeF_refreezeFrontF {B B' : ℕ} (hBB' : B ≤ B') (t : ℕ)
    (htB : t + B ≤ B') (r : RegionSpecF B) :
    clusterFreeF (refreezeFrontF hBB' t htB r) = true := by
  rcases r with r | q | l
  · exact (clusterFreeF_core _).mpr (clusterFree_refreezeFront hBB' t htB r)
  · rfl
  · rfl

theorem refreezeFrontF_posAt {B B' : ℕ} (hBB' : B ≤ B') (t : ℕ)
    (htB : t + B ≤ B') (r : RegionSpecF B) (mS b n : ℕ) :
    (refreezeFrontF hBB' t htB r).posAt mS b n = r.posAt mS t n := by
  rcases r with r | q | l
  · show mS - 1 + (refreezeFront hBB' t htB r).posAt b n
      = mS - 1 + r.posAt t n
    rw [refreezeFront_posAt]
  · rfl
  · rfl

theorem refreezeFrontF_valid {B B' : ℕ} (hBB' : B ≤ B') (t : ℕ)
    (htB : t + B ≤ B') (r : RegionSpecF B) (mS : ℕ) (hv : r.valid mS) :
    (refreezeFrontF hBB' t htB r).valid mS := by
  rcases r with r | q | l
  · trivial
  · exact hv
  · exact hv

/-- The fibred back-zone re-freeze: core clusters re-pin as backs at
`n − 1 − (t + δ)`; stretch descriptors pass through. -/
def refreezeBackF {B B' : ℕ} (hBB' : B ≤ B') (hB'1 : 1 ≤ B') (t n : ℕ)
    (hback : n ≤ t + B') : RegionSpecF B → RegionSpecF B'
  | .core r => .core (refreezeBack hBB' hB'1 t n hback r)
  | .prefIdx q => .prefIdx q
  | .sufIdx l => .sufIdx l

theorem clusterFreeF_refreezeBackF {B B' : ℕ} (hBB' : B ≤ B') (hB'1 : 1 ≤ B')
    (t n : ℕ) (hback : n ≤ t + B') (r : RegionSpecF B) :
    clusterFreeF (refreezeBackF hBB' hB'1 t n hback r) = true := by
  rcases r with r | q | l
  · exact (clusterFreeF_core _).mpr
      (clusterFree_refreezeBack hBB' hB'1 t n hback r)
  · rfl
  · rfl

theorem refreezeBackF_posAt {B B' : ℕ} (hBB' : B ≤ B') (hB'1 : 1 ≤ B')
    (t n : ℕ) (hback : n ≤ t + B') (htn : t + B ≤ n) (r : RegionSpecF B)
    (mS b : ℕ) :
    (refreezeBackF hBB' hB'1 t n hback r).posAt mS b n = r.posAt mS t n := by
  rcases r with r | q | l
  · show mS - 1 + (refreezeBack hBB' hB'1 t n hback r).posAt b n
      = mS - 1 + r.posAt t n
    rw [refreezeBack_posAt hBB' hB'1 t n hback htn]
  · rfl
  · rfl

theorem refreezeBackF_valid {B B' : ℕ} (hBB' : B ≤ B') (hB'1 : 1 ≤ B')
    (t n : ℕ) (hback : n ≤ t + B') (r : RegionSpecF B) (mS : ℕ)
    (hv : r.valid mS) :
    (refreezeBackF hBB' hB'1 t n hback r).valid mS := by
  rcases r with r | q | l
  · trivial
  · exact hv
  · exact hv

/-! ## Cell-tuple validity on the window -/

/-- Fibred cell tuples are in-slice on the window. -/
theorem cellTupleF_valid {B k : ℕ} (rs : Fin k → RegionSpecF B)
    (mS t₀ n : ℕ) (hm : 1 ≤ mS) (hv : ∀ i, (rs i).valid mS)
    (hwin : t₀ + B ≤ n) :
    ∀ i, cellTupleF rs mS t₀ n i < (copiedSlice mS n).length := by
  intro i
  rw [length_copiedSlice]
  show (rs i).posAt mS t₀ n < 2 * (mS + n)
  rcases hri : rs i with r | q | l
  · rcases r with _ | _ | ⟨f, e⟩ | ⟨l', e⟩ | ⟨δ, e⟩ <;>
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
  · have hq : q < mS - 1 := by
      have := hv i
      rwa [hri] at this
    show q < 2 * (mS + n)
    omega
  · have hl : l < mS - 1 := by
      have := hv i
      rwa [hri] at this
    show mS + 2 * n + 1 + l < 2 * (mS + n)
    omega

/-! ## The bundled re-freezes -/

/-- A fibred cell whose base sits in the front zone is a cluster-free cell
over the enlarged bound, at the dummy base `Bh + 1` (validity preserved). -/
theorem freeze_front_descrF {B Bh k : ℕ} (hBB : B ≤ Bh)
    (rs : Fin k → RegionSpecF B) (mS t n : ℕ) (htB : t + B ≤ Bh) :
    ∃ rs' : Fin k → RegionSpecF Bh,
      (∀ i, clusterFreeF (rs' i) = true) ∧
      (∀ i, (rs i).valid mS → (rs' i).valid mS) ∧
      cellTupleF rs mS t n = cellTupleF rs' mS (Bh + 1) n :=
  ⟨fun i => refreezeFrontF hBB t htB (rs i),
   fun i => clusterFreeF_refreezeFrontF hBB t htB (rs i),
   fun i hv => refreezeFrontF_valid hBB t htB (rs i) mS hv,
   funext (fun i => (refreezeFrontF_posAt hBB t htB (rs i) mS (Bh + 1) n).symm)⟩

/-- A fibred cell whose base sits in the back zone is a cluster-free cell
over the enlarged bound, at the dummy base `Bh + 1` (validity preserved). -/
theorem freeze_back_descrF {B Bh k : ℕ} (hBB : B ≤ Bh) (hBh1 : 1 ≤ Bh)
    (rs : Fin k → RegionSpecF B) (mS t n : ℕ) (hback : n ≤ t + Bh)
    (htn : t + B ≤ n) :
    ∃ rs' : Fin k → RegionSpecF Bh,
      (∀ i, clusterFreeF (rs' i) = true) ∧
      (∀ i, (rs i).valid mS → (rs' i).valid mS) ∧
      cellTupleF rs mS t n = cellTupleF rs' mS (Bh + 1) n :=
  ⟨fun i => refreezeBackF hBB hBh1 t n hback (rs i),
   fun i => clusterFreeF_refreezeBackF hBB hBh1 t n hback (rs i),
   fun i hv => refreezeBackF_valid hBB hBh1 t n hback (rs i) mS hv,
   funext (fun i =>
     (refreezeBackF_posAt hBB hBh1 t n hback htn (rs i) mS (Bh + 1)).symm)⟩

/-! ## The bulk width -/

/-- The width contribution of one fibred coordinate. -/
def widthAtF {Z : ℕ} : RegionSpecF Z → ℕ
  | .core (.cluster δ _) => δ.val + 1
  | _ => 0

/-- The bulk width of a fibred cell: the largest core cluster offset plus one
(stretch and pinned coordinates contribute `0`). -/
noncomputable def clusterWidthF {Z k : ℕ} (rs : Fin k → RegionSpecF Z) : ℕ :=
  Finset.univ.sup (fun i => widthAtF (rs i))

theorem cluster_lt_widthF {Z k : ℕ} (rs : Fin k → RegionSpecF Z) (i : Fin k)
    (δ : Fin Z) (e : Bool) (h : rs i = .core (.cluster δ e)) :
    δ.val < clusterWidthF rs := by
  have hle : widthAtF (rs i) ≤ clusterWidthF rs :=
    Finset.le_sup (f := fun i => widthAtF (rs i)) (Finset.mem_univ i)
  rw [h] at hle
  exact hle

end CopiedRegionF
