/-
# `d*` for general arity — region enumeration and zone re-description (GA-5.7–5.8)

The adjudicated GA-5 gate-layer prerequisites (see `GA58_ADJUDICATION.json`):

* `regionTuples` — the finite enumeration of cell descriptors (via the derived
  `Fintype (RegionSpec B)` and `Fintype.piFinset`), with total membership;
* `regionLift` / `regionLift_posAt` — descriptors lift along `B ≤ B'` preserving
  positions (`Fin.castLE` on the pin/offset fields);
* `clusterFree` / `clusterFree_posAt_base` — pinned descriptors ignore the base;
* `cell_refreeze_front` / `cell_refreeze_back` — the ZONE RE-DESCRIPTION: an atom in
  cell form at a base in the front (resp. back) zone is also a CLUSTER-FREE cell over
  the enlarged bound `B̂` (the cluster coordinates re-pin as fronts `t+δ` resp. backs
  `n−1−(t+δ)`).  These feed the heterogeneous-candidate design: frozen candidates at
  `B̂`, bulk candidates at the original `B`.

Axiom-clean: pure descriptor algebra.
-/
import RequestProject.SliceDstarGA
import RequestProject.SliceFasGates

namespace SliceDstarGateGA

open WRP Step SliceFamilyCell SliceDstarGA
open scoped Classical

/-! ## GA-5.7: enumeration and lifting -/

/-- The (total) enumeration of cell descriptors at bound `B` and arity `k`. -/
noncomputable def regionTuples (B k : ℕ) : List (Fin k → RegionSpec B) :=
  (Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset (RegionSpec B)))).toList

theorem mem_regionTuples (B k : ℕ) (rs : Fin k → RegionSpec B) :
    rs ∈ regionTuples B k := by
  rw [regionTuples, Finset.mem_toList, Fintype.mem_piFinset]
  intro i
  exact Finset.mem_univ _

/-- Lift a descriptor along an enlargement of the pin/offset bound. -/
def regionLift {B B' : ℕ} (h : B ≤ B') : RegionSpec B → RegionSpec B'
  | .pre => .pre
  | .suf => .suf
  | .front f e => .front (Fin.castLE h f) e
  | .back l e => .back (Fin.castLE h l) e
  | .cluster δ e => .cluster (Fin.castLE h δ) e

/-- Lifting preserves the described position. -/
theorem regionLift_posAt {B B' : ℕ} (h : B ≤ B') (r : RegionSpec B) (t n : ℕ) :
    (regionLift h r).posAt t n = r.posAt t n := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;> rfl

/-- A descriptor is cluster-free when it does not ride the mobile window. -/
def clusterFree {B : ℕ} : RegionSpec B → Prop
  | .cluster _ _ => False
  | _ => True

/-- Cluster-free descriptors ignore the base. -/
theorem clusterFree_posAt_base {B : ℕ} (r : RegionSpec B) (hcf : clusterFree r)
    (t t' n : ℕ) : r.posAt t n = r.posAt t' n := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd hcf (by simp [clusterFree])

/-! ## GA-5.8: zone re-description -/

/-- The front-zone re-freeze map: cluster coordinates re-pin as fronts at `t + δ`. -/
def refreezeFront {B B' : ℕ} (hBB' : B ≤ B') (t : ℕ) (htB : t + B ≤ B') :
    RegionSpec B → RegionSpec B'
  | .pre => .pre
  | .suf => .suf
  | .front f e => .front (Fin.castLE hBB' f) e
  | .back l e => .back (Fin.castLE hBB' l) e
  | .cluster δ e => .front ⟨t + δ.val, by have := δ.isLt; omega⟩ e

theorem clusterFree_refreezeFront {B B' : ℕ} (hBB' : B ≤ B') (t : ℕ)
    (htB : t + B ≤ B') (r : RegionSpec B) :
    clusterFree (refreezeFront hBB' t htB r) := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [refreezeFront, clusterFree]

/-- **Front-zone re-description**: the re-frozen descriptor describes the same
position at ANY base. -/
theorem refreezeFront_posAt {B B' : ℕ} (hBB' : B ≤ B') (t : ℕ) (htB : t + B ≤ B')
    (r : RegionSpec B) (b n : ℕ) :
    (refreezeFront hBB' t htB r).posAt b n = r.posAt t n := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [refreezeFront, RegionSpec.posAt, Fin.val_castLE]

/-- The back-zone re-freeze map: cluster coordinates re-pin as backs at
`n − 1 − (t + δ)`. -/
def refreezeBack {B B' : ℕ} (hBB' : B ≤ B') (hB'1 : 1 ≤ B') (t n : ℕ)
    (hback : n ≤ t + B') : RegionSpec B → RegionSpec B'
  | .pre => .pre
  | .suf => .suf
  | .front f e => .front (Fin.castLE hBB' f) e
  | .back l e => .back (Fin.castLE hBB' l) e
  | .cluster δ e => .back ⟨n - 1 - (t + δ.val), by omega⟩ e

theorem clusterFree_refreezeBack {B B' : ℕ} (hBB' : B ≤ B') (hB'1 : 1 ≤ B')
    (t n : ℕ) (hback : n ≤ t + B') (r : RegionSpec B) :
    clusterFree (refreezeBack hBB' hB'1 t n hback r) := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [refreezeBack, clusterFree]

/-- **Back-zone re-description**: the re-frozen descriptor describes the same
position at ANY base, provided the window sits inside the slice (`t + B ≤ n`). -/
theorem refreezeBack_posAt {B B' : ℕ} (hBB' : B ≤ B') (hB'1 : 1 ≤ B') (t n : ℕ)
    (hback : n ≤ t + B') (htn : t + B ≤ n) (r : RegionSpec B) (b : ℕ) :
    (refreezeBack hBB' hB'1 t n hback r).posAt b n = r.posAt t n := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [refreezeBack, RegionSpec.posAt, Fin.val_castLE]
  have hδ := δ.isLt
  have harg : n - 1 - (n - 1 - (t + δ.val)) = t + δ.val := by omega
  rw [harg]

/-! ## GA-5.9: the per-cell anchor gate sentences -/

/-- Validity of the cell tuple inside the slice. -/
theorem cellTuple_valid {B k : ℕ} (rs : Fin k → RegionSpec B) (t₀ n : ℕ)
    (hwin : t₀ + B ≤ n) :
    ∀ i, cellTuple rs t₀ n i < (wrappedFlat n).length := by
  intro i
  rw [length_wrappedFlat]
  show (rs i).posAt t₀ n < 2 * (n + 1)
  rcases rs i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;> simp only [RegionSpec.posAt]
  · omega
  · omega
  · have := f.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · have := l.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · have := δ.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- The per-coordinate position decode at a CONSTANT anchor base `t₀`: front-anchored
regions decode by `mso_position_eq` at their literal positions, end-anchored ones by
`mso_position_fromEnd` at their literal end-offsets. -/
noncomputable def regionDecode (t₀ : ℕ) {B : ℕ} : RegionSpec B → MSO.Formula Step 1 0
  | .pre => (SliceFasGates.mso_position_eq (Alpha := Step) 0).choose
  | .suf => (SliceFasGates.mso_position_fromEnd (Alpha := Step) 0).choose
  | .front f e =>
      (SliceFasGates.mso_position_eq (Alpha := Step) (1 + 2 * f.val + e.toNat)).choose
  | .back l e =>
      (SliceFasGates.mso_position_fromEnd (Alpha := Step)
        (2 * l.val + 2 - e.toNat)).choose
  | .cluster δ e =>
      (SliceFasGates.mso_position_eq (Alpha := Step)
        (1 + 2 * (t₀ + δ.val) + e.toNat)).choose

/-- **The decode pins the position**: on the slice, the decode of region `r` holds of
`p` exactly when `p` is the position `r` describes at the anchor. -/
theorem regionDecode_sat (t₀ : ℕ) {B : ℕ} (r : RegionSpec B) (n p : ℕ)
    (hp : p < (wrappedFlat n).length) (hwin : t₀ + B ≤ n) :
    ((regionDecode t₀ r).Sat (wrappedFlat n) (fun _ => p) Fin.elim0 ↔
      p = r.posAt t₀ n) := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
  · exact ((SliceFasGates.mso_position_eq (Alpha := Step) 0).choose_spec
      (wrappedFlat n) p hp).trans (by simp only [RegionSpec.posAt])
  · refine ((SliceFasGates.mso_position_fromEnd (Alpha := Step) 0).choose_spec
      (wrappedFlat n) p hp).trans ?_
    rw [length_wrappedFlat]
    simp only [RegionSpec.posAt]
    omega
  · exact ((SliceFasGates.mso_position_eq (Alpha := Step)
      (1 + 2 * f.val + e.toNat)).choose_spec (wrappedFlat n) p hp).trans
      (by simp only [RegionSpec.posAt])
  · refine ((SliceFasGates.mso_position_fromEnd (Alpha := Step)
      (2 * l.val + 2 - e.toNat)).choose_spec (wrappedFlat n) p hp).trans ?_
    rw [length_wrappedFlat]
    simp only [RegionSpec.posAt]
    have := l.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · exact ((SliceFasGates.mso_position_eq (Alpha := Step)
      (1 + 2 * (t₀ + δ.val) + e.toNat)).choose_spec (wrappedFlat n) p hp).trans
      (by simp only [RegionSpec.posAt])

/-- **The anchor gate sentence**: "the atom of copy `c` at the cell positions with
anchor base `t₀` is selected and labelled `D`" — the per-coordinate decodes pin the
existentially closed variables to the cell tuple, then the selection and label
formulas fire at it. -/
noncomputable def anchorGate (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    {B : ℕ} (rs : Fin (P.toPoly.arity c) → RegionSpec B) (t₀ : ℕ) :
    MSO.Sentence Step :=
  MSOMarkN.closeAllFO (MSO.Formula.and
    (MSOMarkN.andList ((List.finRange (P.toPoly.arity c)).map (fun i =>
      SliceFasGates.relabelFO (fun _ : Fin 1 => i) (regionDecode t₀ (rs i)))))
    (MSO.Formula.and (P.toPoly.selDef c).choose ((P.toPoly.labelDef c D).choose)))

/-- **The gate characterization**: on the window, the anchor gate holds on `W_n`
exactly when the anchored cell atom is selected with label `D`. -/
theorem sat_anchorGate (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    {B : ℕ} (rs : Fin (P.toPoly.arity c) → RegionSpec B) (t₀ n : ℕ)
    (hwin : t₀ + B ≤ n) :
    ((anchorGate P c rs t₀).Sat (wrappedFlat n) Fin.elim0 Fin.elim0 ↔
      (P.toPoly.sel c (wrappedFlat n) (cellTuple rs t₀ n)
        ∧ P.toPoly.label c (wrappedFlat n) (cellTuple rs t₀ n) = D)) := by
  rw [anchorGate, MSOMarkN.sat_closeAllFO]
  constructor
  · rintro ⟨ρ, hbound, hsat⟩
    rw [MSO.Formula.sat_and, MSO.Formula.sat_and] at hsat
    obtain ⟨hdec, hsel, hlab⟩ := hsat
    have hρ : ρ = cellTuple rs t₀ n := by
      funext i
      have hd := (MSOMarkN.sat_andList _ _ _ _).mp hdec _
        (List.mem_map_of_mem (List.mem_finRange i))
      rw [SliceFasGates.sat_relabelFO] at hd
      exact (regionDecode_sat t₀ (rs i) n (ρ i) (hbound i) hwin).mp hd
    rw [hρ] at hsel hlab
    exact ⟨((P.toPoly.selDef c).choose_spec (wrappedFlat n) (cellTuple rs t₀ n)).mpr hsel,
      ((P.toPoly.labelDef c D).choose_spec (wrappedFlat n) (cellTuple rs t₀ n)).mpr hlab⟩
  · rintro ⟨hsel, hlab⟩
    refine ⟨cellTuple rs t₀ n, cellTuple_valid rs t₀ n hwin, ?_⟩
    rw [MSO.Formula.sat_and, MSO.Formula.sat_and]
    refine ⟨?_,
      ((P.toPoly.selDef c).choose_spec (wrappedFlat n) (cellTuple rs t₀ n)).mp hsel,
      ((P.toPoly.labelDef c D).choose_spec (wrappedFlat n) (cellTuple rs t₀ n)).mp hlab⟩
    rw [MSOMarkN.sat_andList]
    intro ψ hψ
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hψ
    rw [SliceFasGates.sat_relabelFO]
    exact (regionDecode_sat t₀ (rs i) n (cellTuple rs t₀ n i)
      (cellTuple_valid rs t₀ n hwin i) hwin).mpr rfl

/-- **Gate slice-EP**: the anchor gate's truth is eventually periodic in `n`. -/
theorem anchorGate_EP (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    {B : ℕ} (rs : Fin (P.toPoly.arity c) → RegionSpec B) (t₀ : ℕ) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ n, m ≤ n →
      ((anchorGate P c rs t₀).Sat (wrappedFlat (n + p)) Fin.elim0 Fin.elim0 ↔
       (anchorGate P c rs t₀).Sat (wrappedFlat n) Fin.elim0 Fin.elim0) := by
  obtain ⟨m, p, hp, hper⟩ := SliceMSO.mso_slice_eventuallyPeriodic
    (anchorGate P c rs t₀) [U] [U, D] [D]
  refine ⟨m, p, hp, fun n hn => ?_⟩
  unfold wrappedFlat
  exact hper n hn

/-- **The gate–DFA glue**: on the window, the anchor gate agrees with the per-copy
selected-`D` DFA's acceptance of the marked cell tuple (`exists_selDDFA`'s `M`). -/
theorem anchorGate_iff_accepts (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    {B : ℕ} (rs : Fin (P.toPoly.arity c) → RegionSpec B) (t₀ n : ℕ)
    (hwin : t₀ + B ≤ n)
    (M : SliceMSO.DetAuto (MSOMarkN.MarkedN (P.toPoly.arity c)))
    (hM : ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
      (M.accepts (MSOMarkN.markAtN (P.toPoly.arity c) w ī) ↔
        (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D))) :
    ((anchorGate P c rs t₀).Sat (wrappedFlat n) Fin.elim0 Fin.elim0 ↔
      M.accepts (MSOMarkN.markAtN (P.toPoly.arity c) (wrappedFlat n)
        (cellTuple rs t₀ n))) :=
  (sat_anchorGate P c rs t₀ n hwin).trans
    (hM (wrappedFlat n) (cellTuple rs t₀ n) (cellTuple_valid rs t₀ n hwin)).symm


end SliceDstarGateGA
