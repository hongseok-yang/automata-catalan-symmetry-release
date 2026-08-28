/-
# `d*` for general arity — the semantic layer and the cell transport (GA-5.1–5.6)

The GA-5 mechanical layer:

* `selDListGA` / `mem_selDListGA` — the selected-`D`-atom list of `W_n` over all
  copies and tuples (`Sigma.eta` replaces the arity-1 `atom_eq` machinery);
* `exists_min_selDAtomGA` / `dstarRankGA` / `dstarRankGA_spec` — verbatim ports of
  the arity-1 `SliceDstar` block minus the arity hypothesis.  `dstarRankGA` is
  SEMANTIC and `C`-free; its sole downstream consumer
  (`SliceOutput.fas_inner_collapse`) is already arity-free;
* `exists_selDDFA` — the per-copy selected-`D` DFA (`sel ∧ label = D` conjunction
  through `markedDFAN_exists`);
* `cellTuple` / `cellTuple_classify` — the cell position tuple and its three-way
  position split, discharging the move lemmas' `hclass` with
  `a := B, b := t, c := t + B, d := n − B`;
* `cellTuple_shift_right` / `cellTuple_shift_left` — window shifts move the base;
* `cell_base_transport` — acceptance of the cell tuple is invariant under moving the
  base by any period multiple inside the window: ONE `acceptsN_moveGroup_multi`
  (resp. `_left`) application — the whole hI/hII transport, no chains.

Axiom-clean except the DFA layer (+`SliceMSO.buchi`).
-/
import RequestProject.SliceDstar
import RequestProject.SliceGrowthCollapse
import RequestProject.SliceFamilyCell

namespace SliceDstarGA

open WRP Step SliceFamilyCell SliceGrowthCollapse MSOMarkN SliceMarkN
open scoped Classical

/-! ## GA-5.1: the selected-`D` list -/

/-- The selected `D`-atoms of `W_n`, over all copies and tuples. -/
noncomputable def selDListGA (P : WRP.Presentation Step Step) (n : ℕ) :
    List P.toPoly.Atom :=
  ((List.finRange P.toPoly.K).flatMap (fun c =>
    (Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
      Finset.range (wrappedFlat n).length)).toList.map
      (fun ī => (⟨c, ī⟩ : P.toPoly.Atom)))).filter
    (fun a => decide (P.toPoly.selectedAtom (wrappedFlat n) a ∧
      P.toPoly.labelOf (wrappedFlat n) a = D))

theorem mem_selDListGA (P : WRP.Presentation Step Step) (n : ℕ) (a : P.toPoly.Atom) :
    a ∈ selDListGA P n ↔
      (P.toPoly.selectedAtom (wrappedFlat n) a
        ∧ P.toPoly.labelOf (wrappedFlat n) a = D) := by
  rw [selDListGA, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hsel, hlab⟩
    exact ⟨hsel, hlab⟩
  · rintro ⟨hsel, hlab⟩
    refine ⟨?_, hsel, hlab⟩
    rw [List.mem_flatMap]
    refine ⟨a.1, List.mem_finRange _, ?_⟩
    rw [List.mem_map]
    refine ⟨a.2, ?_, rfl⟩
    rw [Finset.mem_toList, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact hsel.1 i

/-! ## GA-5.2: the minimal selected `D`-atom and `dstarRankGA` -/

/-- **Existence of the `≺`-minimal selected `D`-atom**, general arity. -/
theorem exists_min_selDAtomGA (P : WRP.Presentation Step Step) (hV : P.Valid) (n : ℕ)
    (h : ∃ a, P.toPoly.selectedAtom (wrappedFlat n) a
      ∧ P.toPoly.labelOf (wrappedFlat n) a = D) :
    ∃ dstar, P.toPoly.selectedAtom (wrappedFlat n) dstar ∧
      P.toPoly.labelOf (wrappedFlat n) dstar = D ∧
      ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
        P.toPoly.labelOf (wrappedFlat n) b = D →
        dstar = b ∨ P.wrpOrd (wrappedFlat n) dstar b := by
  obtain ⟨a0, ha0⟩ := h
  have hmemiff := mem_selDListGA P n
  have hlne : selDListGA P n ≠ [] := fun hcon => by
    have := (hmemiff a0).mpr ha0
    rw [hcon] at this
    exact absurd this (by simp)
  obtain ⟨dstar, hdmem, hdmin⟩ := SliceDstar.exists_min_of_list
    (P.wrpOrd (wrappedFlat n)) (selDListGA P n) hlne
    (fun a ha b hb => hV.trichot (wrappedFlat n) a b ((hmemiff a).mp ha).1
      ((hmemiff b).mp hb).1)
    (fun a ha b hb c hc => hV.trans (wrappedFlat n) a b c
      ((hmemiff a).mp ha).1 ((hmemiff b).mp hb).1 ((hmemiff c).mp hc).1)
  obtain ⟨hdsel, hdD⟩ := (hmemiff dstar).mp hdmem
  exact ⟨dstar, hdsel, hdD, fun b hbsel hbD => hdmin b ((hmemiff b).mpr ⟨hbsel, hbD⟩)⟩

/-- **`d*`-rank(n), general arity**: the rank vector of the `≺`-minimal selected
`D`-atom of `W_n` (`0` when `D`-absent).  SEMANTIC and `C`-free. -/
noncomputable def dstarRankGA (P : WRP.Presentation Step Step) (hV : P.Valid)
    (n : ℕ) : Fin P.d → ℤ :=
  if h : ∃ a, P.toPoly.selectedAtom (wrappedFlat n) a
      ∧ P.toPoly.labelOf (wrappedFlat n) a = D
  then P.rankOf (wrappedFlat n) (Classical.choose (exists_min_selDAtomGA P hV n h))
  else fun _ => 0

/-- **The consumer interface**: on a `D`-present slice, `dstarRankGA n` is `rankOf`
of an actual `≺`-minimal selected `D`-atom — what `fas_inner_collapse` consumes. -/
theorem dstarRankGA_spec (P : WRP.Presentation Step Step) (hV : P.Valid) (n : ℕ)
    (h : ∃ a, P.toPoly.selectedAtom (wrappedFlat n) a
      ∧ P.toPoly.labelOf (wrappedFlat n) a = D) :
    ∃ dstar, P.toPoly.selectedAtom (wrappedFlat n) dstar ∧
      P.toPoly.labelOf (wrappedFlat n) dstar = D ∧
      (∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
        P.toPoly.labelOf (wrappedFlat n) b = D →
        dstar = b ∨ P.wrpOrd (wrappedFlat n) dstar b) ∧
      dstarRankGA P hV n = P.rankOf (wrappedFlat n) dstar := by
  refine ⟨Classical.choose (exists_min_selDAtomGA P hV n h), ?_⟩
  obtain ⟨hsel, hD, hmin⟩ := Classical.choose_spec (exists_min_selDAtomGA P hV n h)
  refine ⟨hsel, hD, hmin, ?_⟩
  unfold dstarRankGA
  rw [dif_pos h]

/-! ## GA-5.3: the per-copy selected-`D` DFA -/

/-- **The per-copy selected-`D` recogniser**: on valid tuples, an `arity c`-mark DFA
decides `sel ∧ label = D` (the conjunction of the two defining formulas through
`markedDFAN_exists`). -/
theorem exists_selDDFA (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    ∃ M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)) := by
  obtain ⟨φs, hφs⟩ := P.toPoly.selDef c
  obtain ⟨φl, hφl⟩ := P.toPoly.labelDef c D
  obtain ⟨M, hM⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c) (MSO.Formula.and φs φl)
  refine ⟨M, fun w ī hval => ?_⟩
  rw [hM w ī hval, MSO.Formula.sat_and, ← hφs w ī, ← hφl w ī]

/-! ## GA-5.4: the cell tuple and its position split -/

/-- The position tuple a cell descriptor describes at base `t` on `W_n`. -/
def cellTuple {B : ℕ} {k : ℕ} (rs : Fin k → RegionSpec B) (t n : ℕ) : Fin k → ℕ :=
  fun i => (rs i).posAt t n

/-- **The three-way position split**: on the window `B ≤ t`, `t + 2B ≤ n`, every
cell-tuple coordinate is in the front zone (`< 1+2B`), the cluster window
(`[1+2t, 1+2(t+B))`), or the back zone (`≥ 1+2(n−B)`) — the move lemmas' `hclass`
with `a := B, b := t, c := t + B, d := n − B`. -/
theorem cellTuple_classify {B k : ℕ} (rs : Fin k → RegionSpec B) (t n : ℕ)
    (htB : B ≤ t) (htn : t + 2 * B ≤ n) :
    ∀ i, cellTuple rs t n i < 1 + 2 * B
      ∨ (1 + 2 * t ≤ cellTuple rs t n i ∧ cellTuple rs t n i < 1 + 2 * (t + B))
      ∨ 1 + 2 * (n - B) ≤ cellTuple rs t n i := by
  intro i
  unfold cellTuple
  rcases hri : rs i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [RegionSpec.posAt]
  · left; omega
  · right; right; omega
  · left
    have := f.isLt
    rcases e with _ | _
    · simp [Bool.toNat]
    · simp [Bool.toNat]
      omega
  · right; right
    have := l.isLt
    rcases e with _ | _ <;> (simp [Bool.toNat]; omega)
  · right; left
    have := δ.isLt
    rcases e with _ | _ <;> (constructor <;> simp [Bool.toNat] <;> omega)

/-! ## GA-5.5: window shifts move the base -/

/-- Shifting the cluster window right by `δ` moves the cell base right. -/
theorem cellTuple_shift_right {B k : ℕ} (rs : Fin k → RegionSpec B) (t n δ : ℕ)
    (htB : B ≤ t) (htn : t + δ + 2 * B ≤ n) :
    shiftGroup k (cellTuple rs t n) t (t + B) δ = cellTuple rs (t + δ) n := by
  funext i
  show shiftGroup k (cellTuple rs t n) t (t + B) δ i = (rs i).posAt (t + δ) n
  rcases hri : rs i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ', e⟩
  · rw [shiftGroup_apply_out (cellTuple rs t n) t (t + B) δ i
      (by unfold cellTuple; rw [hri]; simp only [RegionSpec.posAt]; omega)]
    unfold cellTuple
    rw [hri]
    simp only [RegionSpec.posAt]
  · rw [shiftGroup_apply_out (cellTuple rs t n) t (t + B) δ i
      (by unfold cellTuple; rw [hri]; simp only [RegionSpec.posAt]; omega)]
    unfold cellTuple
    rw [hri]
    simp only [RegionSpec.posAt]
  · have hf := f.isLt
    rw [shiftGroup_apply_out (cellTuple rs t n) t (t + B) δ i
      (by unfold cellTuple; rw [hri]; simp only [RegionSpec.posAt]
          rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)]
    unfold cellTuple
    rw [hri]
    simp only [RegionSpec.posAt]
  · have hl := l.isLt
    rw [shiftGroup_apply_out (cellTuple rs t n) t (t + B) δ i
      (by unfold cellTuple; rw [hri]; simp only [RegionSpec.posAt]
          rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)]
    unfold cellTuple
    rw [hri]
    simp only [RegionSpec.posAt]
  · have hδ' := δ'.isLt
    rw [shiftGroup_apply_in (cellTuple rs t n) t (t + B) δ i
      (by unfold cellTuple; rw [hri]; simp only [RegionSpec.posAt]
          rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> constructor <;> omega)]
    unfold cellTuple
    rw [hri]
    simp only [RegionSpec.posAt]
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Shifting the cluster window left by `δ` moves the cell base left. -/
theorem cellTuple_shift_left {B k : ℕ} (rs : Fin k → RegionSpec B) (t n δ : ℕ)
    (htB : B ≤ t) (hδt : δ ≤ t) (htn : t + 2 * B ≤ n) :
    shiftGroupLeft k (cellTuple rs t n) t (t + B) δ = cellTuple rs (t - δ) n := by
  funext i
  show shiftGroupLeft k (cellTuple rs t n) t (t + B) δ i = (rs i).posAt (t - δ) n
  rcases hri : rs i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ', e⟩
  · rw [shiftGroupLeft_apply_out (cellTuple rs t n) t (t + B) δ i
      (by unfold cellTuple; rw [hri]; simp only [RegionSpec.posAt]; omega)]
    unfold cellTuple
    rw [hri]
    simp only [RegionSpec.posAt]
  · rw [shiftGroupLeft_apply_out (cellTuple rs t n) t (t + B) δ i
      (by unfold cellTuple; rw [hri]; simp only [RegionSpec.posAt]; omega)]
    unfold cellTuple
    rw [hri]
    simp only [RegionSpec.posAt]
  · have hf := f.isLt
    rw [shiftGroupLeft_apply_out (cellTuple rs t n) t (t + B) δ i
      (by unfold cellTuple; rw [hri]; simp only [RegionSpec.posAt]
          rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)]
    unfold cellTuple
    rw [hri]
    simp only [RegionSpec.posAt]
  · have hl := l.isLt
    rw [shiftGroupLeft_apply_out (cellTuple rs t n) t (t + B) δ i
      (by unfold cellTuple; rw [hri]; simp only [RegionSpec.posAt]
          rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)]
    unfold cellTuple
    rw [hri]
    simp only [RegionSpec.posAt]
  · have hδ' := δ'.isLt
    rw [shiftGroupLeft_apply_in (cellTuple rs t n) t (t + B) δ i
      (by unfold cellTuple; rw [hri]; simp only [RegionSpec.posAt]
          rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> constructor <;> omega)]
    unfold cellTuple
    rw [hri]
    simp only [RegionSpec.posAt]
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-! ## GA-5.6: the cell base transport -/

/-- **Rightward base transport**: a per-cell DFA's acceptance of the cell tuple is
invariant under moving the base right by any period multiple inside the window —
ONE `acceptsN_moveGroup_multi` application. -/
theorem cell_base_transport_right {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k))
    (mv pv : ℕ) (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g])
    (rs : Fin k → RegionSpec B) (t n j : ℕ)
    (htB : B + mv ≤ t) (htn : t + j * pv + 2 * B + mv ≤ n - B) (hBn : B ≤ n) :
    M.accepts (markAtN k (wrappedFlat n) (cellTuple rs (t + j * pv) n))
      ↔ M.accepts (markAtN k (wrappedFlat n) (cellTuple rs t n)) := by
  have hshift := cellTuple_shift_right rs t n (j * pv) (by omega) (by omega)
  rw [← hshift]
  exact acceptsN_moveGroup_multi M mv pv hEP n (cellTuple rs t n) B t (t + B) (n - B) j
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (cellTuple_classify rs t n (by omega) (by omega))

/-- **Leftward base transport**: the `acceptsN_moveGroup_left` twin. -/
theorem cell_base_transport_left {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k))
    (mv pv : ℕ) (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g])
    (rs : Fin k → RegionSpec B) (t n j : ℕ)
    (htB : B + mv + j * pv ≤ t) (htn : t + 2 * B + mv ≤ n - B) (hBn : B ≤ n) :
    M.accepts (markAtN k (wrappedFlat n) (cellTuple rs (t - j * pv) n))
      ↔ M.accepts (markAtN k (wrappedFlat n) (cellTuple rs t n)) := by
  have hshift := cellTuple_shift_left rs t n (j * pv) (by omega) (by omega) (by omega)
  rw [← hshift]
  exact acceptsN_moveGroup_left M mv pv hEP n (cellTuple rs t n) B t (t + B) (n - B) j
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (cellTuple_classify rs t n (by omega) (by omega))

end SliceDstarGA
