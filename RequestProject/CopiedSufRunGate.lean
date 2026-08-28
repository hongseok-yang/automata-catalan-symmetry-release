/-
# The suffix-run atomOrd gate (§9 single-gate selector-mS, slope-0 boundary)

When the boundary `D^mS` suffix run ties the minimal rank `d*` (the slope-0 all-tie case), it
contributes `~mS` equal-rank selected `D`-atoms.  The tie gate's competitor quantifier
`∀b sel-D (rank b = d* → atomOrd(a,b))` over them collapses to ONE MSO clause
"∀ p in the final maximal D-run, sel-D(p) → ordDef(a, p)" — `atomOrd = ordDef` is MSO, so a single
universal-over-positions clause realises it (no per-shape config; the mS-growing boundary shapes are
folded into one DFA whose acceptance is EP-in-mS by run periodicity).

* `inFinalDRun` — the MSO "position in the final maximal D-run" guard + its sat lemma.
* `gordNB` — the `ordDef` address map with NO base slot (the no-`z` twin of `SliceFasGatesGA.gord`).
* `sufOrdClause` — the universal-over-the-competitor-coord atomOrd clause (the `cellClause` shape with
  `inFinalDRun` in place of the cell-config decode).
* `sufOrdClause_gate` — its DFA realisation, spec ∀-word.

Mirrors `CopiedTieGate.boundary_pair_component` (the single-atom version) and
`SliceFasGatesGA.cellClause` (the universal-over-config version).
-/
import RequestProject.CopiedTieGate

namespace CopiedSufRunGate

open WRP Step MSO MSOMarkN SliceMarkN

/-- **"position `x_0` lies in the final maximal D-run."**  MSO formula with one free FO variable:
the letter at `x_0` is `D`, and every later valid position is also `D`. -/
def inFinalDRun : MSO.Formula Step 1 0 :=
  MSO.Formula.and (MSO.Formula.labelEq 0 D)
    (MSO.Formula.faFO (MSO.Formula.imp (MSO.Formula.lt 1 0) (MSO.Formula.labelEq 0 D)))

theorem sat_inFinalDRun (w : List Step) (ρ : Fin 1 → ℕ) (σ : Fin 0 → Finset ℕ) :
    (inFinalDRun).Sat w ρ σ ↔
      (w[ρ 0]? = some D ∧ ∀ q, q < w.length → ρ 0 < q → w[q]? = some D) := by
  have hc0 : ∀ q : ℕ, (Fin.cons q ρ : Fin 2 → ℕ) 0 = q := fun q => rfl
  have hc1 : ∀ q : ℕ, (Fin.cons q ρ : Fin 2 → ℕ) 1 = ρ 0 := fun q => rfl
  unfold inFinalDRun
  simp only [MSO.Formula.sat_and, SliceFasGates.sat_faFO, SliceFasGates.sat_imp,
    MSO.Formula.sat_lt, MSO.Formula.sat_labelEq, hc0, hc1]

/-- The `ordDef` address map WITHOUT a base slot (the no-`z` twin of `SliceFasGatesGA.gord`):
the `c`-atom (`ordDef`'s first block) maps to the HIGH mark block `arity c' + ·`, the `c'`-atom
(second block) to the LOW bound block `·`. -/
def gordNB (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) :
    Fin (P.toPoly.arity c + P.toPoly.arity c') →
    Fin (P.toPoly.arity c + P.toPoly.arity c') :=
  fun idx => if h : idx.1 < P.toPoly.arity c
    then ⟨P.toPoly.arity c' + idx.1, by omega⟩
    else ⟨idx.1 - P.toPoly.arity c, by have := idx.2; omega⟩

/-- **The suffix-run atomOrd clause.**  For the marked `c`-atom `a`: every `c'`-tuple `xb` all of
whose coordinates lie in the final D-run and which is a selected `D`-atom is `ordDef`-preceded by `a`.
This is the `cellClause` shape with NO base slot and `inFinalDRun` in place of the cell-config decode;
it folds the (slope-0 all-tie) boundary competitors into ONE clause. -/
noncomputable def sufOrdClause (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  SliceFasGatesGA.faFOs (P.toPoly.arity c') (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        SliceFasGates.relabelFO
          (fun _ : Fin 1 =>
            (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          inFinalDRun)))
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          (P.toPoly.selDef c').choose)
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          (P.toPoly.labelDef c' D).choose)))
    (SliceFasGates.relabelFO (gordNB P c c') (P.toPoly.ordDef c c').choose))

/-- Composition: the low embedding reads the bound tuple `pb`. -/
theorem comp_embNB (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (pb : Fin (P.toPoly.arity c') → ℕ) (ī : Fin (P.toPoly.arity c) → ℕ) :
    (SliceFasGatesGA.appFO pb ī) ∘ (fun t : Fin (P.toPoly.arity c') =>
        (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c'))) = pb := by
  funext t
  exact SliceFasGatesGA.appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)

/-- Composition: the `gordNB` relabel reads `(ī, pb)` in `ordDef`'s block convention. -/
theorem comp_gordNB (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (pb : Fin (P.toPoly.arity c') → ℕ) (ī : Fin (P.toPoly.arity c) → ℕ) :
    ((fun t => ((SliceFasGatesGA.appFO pb ī) ∘ gordNB P c c') (Fin.castAdd (P.toPoly.arity c') t))
        = ī)
    ∧ ((fun t => ((SliceFasGatesGA.appFO pb ī) ∘ gordNB P c c') (Fin.natAdd (P.toPoly.arity c) t))
        = pb) := by
  constructor
  · funext t
    show SliceFasGatesGA.appFO pb ī (gordNB P c c' (Fin.castAdd _ t)) = ī t
    have hg : gordNB P c c' (Fin.castAdd (P.toPoly.arity c') t)
        = ⟨P.toPoly.arity c' + t.1, by have := t.2; omega⟩ := by
      unfold gordNB
      rw [dif_pos (show ((Fin.castAdd (P.toPoly.arity c') t) : ℕ) < P.toPoly.arity c from t.2)]
      rfl
    rw [hg, SliceFasGatesGA.appFO_high pb ī t.1 t.2 (by have := t.2; omega)]
  · funext t
    show SliceFasGatesGA.appFO pb ī (gordNB P c c' (Fin.natAdd _ t)) = pb t
    have hg : gordNB P c c' (Fin.natAdd (P.toPoly.arity c) t) = ⟨t.1, by have := t.2; omega⟩ := by
      unfold gordNB
      rw [dif_neg (show ¬(((Fin.natAdd (P.toPoly.arity c) t) : ℕ) < P.toPoly.arity c) from by
        have hv : ((Fin.natAdd (P.toPoly.arity c) t) : ℕ) = P.toPoly.arity c + t.1 := rfl
        omega)]
      congr 1
      show ((Fin.natAdd (P.toPoly.arity c) t) : ℕ) - P.toPoly.arity c = (t : ℕ)
      have hv : ((Fin.natAdd (P.toPoly.arity c) t) : ℕ) = P.toPoly.arity c + t.1 := rfl
      omega
    rw [hg]
    exact SliceFasGatesGA.appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)

/-- **The suffix-run atomOrd gate** (DFA realisation of `sufOrdClause`), spec ∀-word.
`A.accepts(markAtN a) ↔ ∀ xb (in-slice), (all coords of xb in the final D-run ∧ xb a selected
`D`-atom) → ord c c' a xb`. -/
theorem sufOrdClause_gate (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) :
    ∃ A : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ),
        (∀ i, i_marks i < w.length) →
        (A.accepts (markAtN _ w i_marks) ↔
          ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < w.length) →
            ((∀ i, w[xb i]? = some D ∧ ∀ q, q < w.length → xb i < q → w[q]? = some D)
              ∧ P.toPoly.sel c' w xb ∧ P.toPoly.label c' w xb = D) →
            P.toPoly.ord c c' w i_marks xb) := by
  obtain ⟨A, hA⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c) (sufOrdClause P c c')
  refine ⟨A, fun w i_marks hi => ?_⟩
  rw [hA w i_marks hi, sufOrdClause, SliceFasGatesGA.sat_faFOs]
  -- guard-decode helper: the inFinalDRun relabel valuation at coord i reads xb i
  have hguarddec : ∀ (xb : Fin (P.toPoly.arity c') → ℕ) (i : Fin (P.toPoly.arity c')),
      (SliceFasGates.relabelFO
          (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          inFinalDRun).Sat w (SliceFasGatesGA.appFO xb i_marks) Fin.elim0 ↔
        (w[xb i]? = some D ∧ ∀ q, q < w.length → xb i < q → w[q]? = some D) := by
    intro xb i
    rw [SliceFasGates.sat_relabelFO, sat_inFinalDRun]
    have hv0 : ((SliceFasGatesGA.appFO xb i_marks) ∘
        (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ :
          Fin (P.toPoly.arity c + P.toPoly.arity c')))) 0 = xb i :=
      SliceFasGatesGA.appFO_low xb i_marks i.1 (by have := i.2; omega) (by have := i.2; omega)
    rw [hv0]
  constructor
  · -- raw → semantic
    intro h xb hxbv hcond
    obtain ⟨hguard, hsel, hlab⟩ := hcond
    have hsat := h xb hxbv
    rw [SliceFasGates.sat_imp] at hsat
    have hord := hsat (by
      rw [MSO.Formula.sat_and]
      refine ⟨?_, ?_⟩
      · rw [MSOMarkN.sat_andList]
        intro ψ hψ
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hψ
        exact (hguarddec xb i).mpr (hguard i)
      · rw [MSO.Formula.sat_and]
        refine ⟨?_, ?_⟩
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.selDef c').choose_spec w xb).mp hsel
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.labelDef c' D).choose_spec w xb).mp hlab)
    rw [SliceFasGates.sat_relabelFO] at hord
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' xb i_marks
    have hfinal := ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO xb i_marks) ∘ gordNB P c c')).mpr hord
    simp only [hg1, hg2] at hfinal
    exact hfinal
  · -- semantic → raw
    intro h pb hpbv
    rw [SliceFasGates.sat_imp]
    intro hprem
    rw [MSO.Formula.sat_and] at hprem
    obtain ⟨hdec, hsl⟩ := hprem
    rw [MSO.Formula.sat_and] at hsl
    obtain ⟨hsel1, hlab1⟩ := hsl
    have hguard : ∀ i, w[pb i]? = some D ∧ ∀ q, q < w.length → pb i < q → w[q]? = some D := by
      intro i
      rw [MSOMarkN.sat_andList] at hdec
      exact (hguarddec pb i).mp (hdec _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
    have hsel : P.toPoly.sel c' w pb := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hsel1
      exact ((P.toPoly.selDef c').choose_spec w pb).mpr hsel1
    have hlab : P.toPoly.label c' w pb = D := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hlab1
      exact ((P.toPoly.labelDef c' D).choose_spec w pb).mpr hlab1
    have hord := h pb hpbv ⟨hguard, hsel, hlab⟩
    rw [SliceFasGates.sat_relabelFO]
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' pb i_marks
    refine ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO pb i_marks) ∘ gordNB P c c')).mp ?_
    simp only [hg1, hg2]
    exact hord

/-! ## The PREFIX twin (the `U^mS` initial run) -/

/-- **"position `x_0` lies in the initial maximal U-run."**  MSO: the letter at `x_0` is `U`, and
every earlier valid position is also `U`. -/
def inInitialURun : MSO.Formula Step 1 0 :=
  MSO.Formula.and (MSO.Formula.labelEq 0 U)
    (MSO.Formula.faFO (MSO.Formula.imp (MSO.Formula.lt 0 1) (MSO.Formula.labelEq 0 U)))

theorem sat_inInitialURun (w : List Step) (ρ : Fin 1 → ℕ) (σ : Fin 0 → Finset ℕ) :
    (inInitialURun).Sat w ρ σ ↔
      (w[ρ 0]? = some U ∧ ∀ q, q < w.length → q < ρ 0 → w[q]? = some U) := by
  have hc0 : ∀ q : ℕ, (Fin.cons q ρ : Fin 2 → ℕ) 0 = q := fun q => rfl
  have hc1 : ∀ q : ℕ, (Fin.cons q ρ : Fin 2 → ℕ) 1 = ρ 0 := fun q => rfl
  unfold inInitialURun
  simp only [MSO.Formula.sat_and, SliceFasGates.sat_faFO, SliceFasGates.sat_imp,
    MSO.Formula.sat_lt, MSO.Formula.sat_labelEq, hc0, hc1]

/-- **The prefix-run atomOrd clause** (the `inInitialURun` twin of `sufOrdClause`; same `gordNB`/
selectedness/label structure, with `inInitialURun` in place of `inFinalDRun`). -/
noncomputable def prefOrdClause (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  SliceFasGatesGA.faFOs (P.toPoly.arity c') (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        SliceFasGates.relabelFO
          (fun _ : Fin 1 =>
            (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          inInitialURun)))
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          (P.toPoly.selDef c').choose)
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          (P.toPoly.labelDef c' D).choose)))
    (SliceFasGates.relabelFO (gordNB P c c') (P.toPoly.ordDef c c').choose))

/-! ## Per-residue-class refinement (the integration uses ONE clause per tying class `r < Q`)

The boundary run rank is affine at a machine period `Q`; only the residue classes `r` whose
constant equals d* actually tie, so the gate activates one clause per tying `r`.  These add a
`position ≡ r [Q]` guard (`SliceFasGates.mso_position_mod`) to the run clauses. -/

/-- **Per-residue-class suffix-run atomOrd clause.** -/
noncomputable def sufOrdClauseAt (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  SliceFasGatesGA.faFOs (P.toPoly.arity c') (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        MSO.Formula.and
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 =>
              (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            inFinalDRun)
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 =>
              (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            (SliceFasGates.mso_position_mod Q r hr).choose))))
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          (P.toPoly.selDef c').choose)
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          (P.toPoly.labelDef c' D).choose)))
    (SliceFasGates.relabelFO (gordNB P c c') (P.toPoly.ordDef c c').choose))

/-- **Per-residue-class suffix-run atomOrd gate.** -/
theorem sufOrdClauseAt_gate (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) :
    ∃ A : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ),
        (∀ i, i_marks i < w.length) →
        (A.accepts (markAtN _ w i_marks) ↔
          ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < w.length) →
            ((∀ i, (w[xb i]? = some D ∧ ∀ q, q < w.length → xb i < q → w[q]? = some D)
                ∧ xb i % Q = r)
              ∧ P.toPoly.sel c' w xb ∧ P.toPoly.label c' w xb = D) →
            P.toPoly.ord c c' w i_marks xb) := by
  obtain ⟨A, hA⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c) (sufOrdClauseAt P c c' Q r hr)
  refine ⟨A, fun w i_marks hi => ?_⟩
  rw [hA w i_marks hi, sufOrdClauseAt, SliceFasGatesGA.sat_faFOs]
  have hguarddec : ∀ (xb : Fin (P.toPoly.arity c') → ℕ) (i : Fin (P.toPoly.arity c')),
      xb i < w.length →
      ((MSO.Formula.and
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            inFinalDRun)
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            (SliceFasGates.mso_position_mod Q r hr).choose)).Sat w
        (SliceFasGatesGA.appFO xb i_marks) Fin.elim0 ↔
        ((w[xb i]? = some D ∧ ∀ q, q < w.length → xb i < q → w[q]? = some D) ∧ xb i % Q = r)) := by
    intro xb i hxv
    have hv0 : ((SliceFasGatesGA.appFO xb i_marks) ∘
        (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ :
          Fin (P.toPoly.arity c + P.toPoly.arity c')))) = fun _ => xb i := by
      funext _
      exact SliceFasGatesGA.appFO_low xb i_marks i.1 (by have := i.2; omega) (by have := i.2; omega)
    rw [MSO.Formula.sat_and, SliceFasGates.sat_relabelFO, SliceFasGates.sat_relabelFO,
      sat_inFinalDRun, hv0,
      (SliceFasGates.mso_position_mod Q r hr).choose_spec w (xb i) hxv]
  constructor
  · intro h xb hxbv hcond
    obtain ⟨hguard, hsel, hlab⟩ := hcond
    have hsat := h xb hxbv
    rw [SliceFasGates.sat_imp] at hsat
    have hord := hsat (by
      rw [MSO.Formula.sat_and]
      refine ⟨?_, ?_⟩
      · rw [MSOMarkN.sat_andList]
        intro ψ hψ
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hψ
        exact (hguarddec xb i (hxbv i)).mpr (hguard i)
      · rw [MSO.Formula.sat_and]
        refine ⟨?_, ?_⟩
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.selDef c').choose_spec w xb).mp hsel
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.labelDef c' D).choose_spec w xb).mp hlab)
    rw [SliceFasGates.sat_relabelFO] at hord
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' xb i_marks
    have hfinal := ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO xb i_marks) ∘ gordNB P c c')).mpr hord
    simp only [hg1, hg2] at hfinal
    exact hfinal
  · intro h pb hpbv
    rw [SliceFasGates.sat_imp]
    intro hprem
    rw [MSO.Formula.sat_and] at hprem
    obtain ⟨hdec, hsl⟩ := hprem
    rw [MSO.Formula.sat_and] at hsl
    obtain ⟨hsel1, hlab1⟩ := hsl
    have hguard : ∀ i, (w[pb i]? = some D ∧ ∀ q, q < w.length → pb i < q → w[q]? = some D)
        ∧ pb i % Q = r := by
      intro i
      rw [MSOMarkN.sat_andList] at hdec
      exact (hguarddec pb i (hpbv i)).mp (hdec _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
    have hsel : P.toPoly.sel c' w pb := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hsel1
      exact ((P.toPoly.selDef c').choose_spec w pb).mpr hsel1
    have hlab : P.toPoly.label c' w pb = D := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hlab1
      exact ((P.toPoly.labelDef c' D).choose_spec w pb).mpr hlab1
    have hord := h pb hpbv ⟨hguard, hsel, hlab⟩
    rw [SliceFasGates.sat_relabelFO]
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' pb i_marks
    refine ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO pb i_marks) ∘ gordNB P c c')).mp ?_
    simp only [hg1, hg2]
    exact hord

/-- **Per-residue-class prefix-run atomOrd clause.** -/
noncomputable def prefOrdClauseAt (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  SliceFasGatesGA.faFOs (P.toPoly.arity c') (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        MSO.Formula.and
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 =>
              (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            inInitialURun)
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 =>
              (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            (SliceFasGates.mso_position_mod Q r hr).choose))))
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          (P.toPoly.selDef c').choose)
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          (P.toPoly.labelDef c' D).choose)))
    (SliceFasGates.relabelFO (gordNB P c c') (P.toPoly.ordDef c c').choose))

/-! ## The integration semantic core: the gate-semantic `∀b` split -/

/-- **The gate-semantic `∀b` SPLIT** (the logical core of the single-gate integration, step 4).
The tie competitor quantifier `∀b sel-D, achieves-d* → atomOrd` over ALL atoms is equivalent to: the
CORE part (competitors in neither boundary run), plus, PER RESIDUE CLASS `r`, the suffix-run and
prefix-run parts — each gated by "class `r` ties d*".  The forward direction is pure logic; the backward
direction uses the per-class UNIFORMITY facts `hsufUniform`/`hpreUniform` (a run atom achieving d* forces
its whole residue class to achieve d* — the slope-0 structure; these are the next sub-lemmas, from the
committed lex-extreme infra).  Generic in the atom type; instantiated at the copied slice with
`inSuf` = in the final D-run, `inPre` = in the initial U-run, `cls b` = b's position mod the rank period.
The suffix/prefix per-class parts are realised by `sufOrdClauseAt`/`prefOrdClauseAt`; the core part by the
bounded-shape `cfgCellGAFL` selector. -/
theorem gate_semantic_split {Atom : Type*}
    (selD ach atOrd inSuf inPre : Atom → Prop) (cls : Atom → ℕ)
    (hsufUniform : ∀ b, inSuf b → selD b → ach b →
      ∀ b', inSuf b' → cls b' = cls b → selD b' → ach b')
    (hpreUniform : ∀ b, inPre b → selD b → ach b →
      ∀ b', inPre b' → cls b' = cls b → selD b' → ach b') :
    (∀ b, selD b → ach b → atOrd b) ↔
      ((∀ b, ¬ inSuf b → ¬ inPre b → selD b → ach b → atOrd b)
        ∧ (∀ r, (∀ b, inSuf b → cls b = r → selD b → ach b) →
            (∀ b, inSuf b → cls b = r → selD b → atOrd b))
        ∧ (∀ r, (∀ b, inPre b → cls b = r → selD b → ach b) →
            (∀ b, inPre b → cls b = r → selD b → atOrd b))) := by
  classical
  constructor
  · intro hL
    refine ⟨?_, ?_, ?_⟩
    · intro b _ _ hsel hach; exact hL b hsel hach
    · intro r hclass b hsuf hcls hsel
      exact hL b hsel (hclass b hsuf hcls hsel)
    · intro r hclass b hpre hcls hsel
      exact hL b hsel (hclass b hpre hcls hsel)
  · rintro ⟨hcore, hsuf, hpre⟩ b hsel hach
    by_cases hb : inSuf b
    · exact hsuf (cls b)
        (fun b' hsuf' hcls' hsel' => hsufUniform b hb hsel hach b' hsuf' hcls' hsel')
        b hb rfl hsel
    · by_cases hb' : inPre b
      · exact hpre (cls b)
          (fun b'' hpre'' hcls'' hsel'' => hpreUniform b hb' hsel hach b'' hpre'' hcls'' hsel'')
          b hb' rfl hsel
      · exact hcore b hb hb' hsel hach

/-- **Affine-on-a-class uniformity (arithmetic core of step 4a).**  A boundary-run rank restricted to
one residue class is affine in the class-index: `G k i = G 0 i + k * P i`.  If two DISTINCT class
indices have equal value, the slope `P` vanishes and `G` is constant on the class.  This converts "a
strictly-deep run atom achieving the class-min, with the class-endpoint also achieving it" into "the
WHOLE class achieves d*" — the `hsufUniform`/`hpreUniform` hypotheses of `gate_semantic_split`.

⚠ The full per-class uniformity ALSO needs (the next sub-lemmas): selection is CONSTANT on each class
(take the class period `Q = lcm(rank period, selection period)`, both periodic on the homogeneous run),
so the sel-D class members are the whole class; and the endpoint (class-min) value = d* via
`SliceDstarBridge.selBvec_le_member` (domination) + the global-min sandwich. -/
theorem affine_class_uniform {d : ℕ} (G : ℕ → Fin d → ℤ) (P : Fin d → ℤ)
    (hrec : ∀ k i, G k i = G 0 i + (k : ℤ) * P i)
    {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) (heq : G k₁ = G k₂) :
    ∀ k, G k = G 0 := by
  have hP : P = 0 := by
    funext i
    have h1 := hrec k₁ i
    have h2 := hrec k₂ i
    have hgi : G k₁ i = G k₂ i := congrFun heq i
    rw [h1, h2] at hgi
    have hmul : ((k₁ : ℤ) - (k₂ : ℤ)) * P i = 0 := by ring_nf; linarith
    have hk : ((k₁ : ℤ) - (k₂ : ℤ)) ≠ 0 := by
      have : (k₁ : ℤ) ≠ (k₂ : ℤ) := by exact_mod_cast hne
      omega
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hk
    · simpa using h
  intro k
  funext i
  rw [hrec k i, hP]
  simp

/-- **(4a) domination-sandwich uniformity.**  An affine class (`F k = F 0 + k•P`) whose ENDPOINT
`k_e` lex-dominates the class (`hdom : ¬ lexLt (F k_b) (F k_e)`, i.e. `F k_e ≤ F k_b`; from
`SliceDstarBridge.selBvec_le_member`), with `dstar` the GLOBAL min over selected atoms so
`dstar ≤ F k_e` (`hglob`, the endpoint being selected — automatic since the class period absorbs the
gate cycle), and a strictly-interior achiever `k_b` (`F k_b = dstar`, `k_b ≠ k_e`): the whole class
equals `dstar`.  This is `hsufUniform`/`hpreUniform` of `gate_semantic_split` once instantiated at the
boundary run via `coordCands_cycle_lengths` (gives `hrec` AND selection-uniformity). -/
theorem class_uniform_of_dom {d : ℕ} (F : ℕ → Fin d → ℤ) (P dstar : Fin d → ℤ)
    (hrec : ∀ k i, F k i = F 0 i + (k : ℤ) * P i)
    {k_e k_b : ℕ} (hne : k_e ≠ k_b)
    (hdom : ¬ WRP.lexLt (F k_b) (F k_e))
    (hglob : ¬ WRP.lexLt (F k_e) dstar)
    (hb : F k_b = dstar) :
    ∀ k, F k = dstar := by
  have hae : F k_e = F k_b := by
    rcases SliceLexOrder.lexLt_not_lt (F k_b) (F k_e) hdom with h | h
    · exact h
    · rw [hb] at h; exact absurd h hglob
  have hconst := affine_class_uniform F P hrec hne hae
  have h0 : F 0 = dstar := by rw [← hconst k_b]; exact hb
  intro k; rw [hconst k, h0]

/-! ## G2: selection-constant-on-class — the abstract heart -/

private theorem foldl_rep_iter {α Q : Type*} (δ : Q → α → Q) (x : α) (a : Q) (k : ℕ) :
    List.foldl δ a (List.replicate k x) = (fun q => δ q x)^[k] a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.foldl_cons, Function.iterate_succ_apply, ih]

/-- **G2 heart (abstract): single-mark acceptance is `pc`-periodic in the mark position on a
homogeneous run.**  A DFA reading `pre ++ x^l ++ [y] ++ x^m ++ suf` (one marked letter `y` flanked by
runs of the homogeneous letter `x`): if the single-step `x`-iterate is `pc`-periodic past `T`, then the
length-conserving mark shift `(l,m) ↦ (l+pc, m-pc)` preserves acceptance, for deep margins
(`T ≤ l`, `T+pc ≤ m`).  Both run-iterates (prefix and suffix) move by `pc` and are fixed by `hper`.
Instantiated at `x` = unmarked-D, `y` = marked-D, `hper` = the `coordCands_cycle_lengths` gate D-cycle,
this gives selection-constancy on a `pc`-class of the `D^mS` run (integration step 4a, gap G2) — and the
mirror with `x` = U for the prefix run. -/
theorem accepts_single_mark_run_period {α : Type*} (M : SliceMSO.DetAuto α) (x y : α)
    (pre suf : List α) (pc T : ℕ)
    (hper : ∀ a, T ≤ a → (fun q => M.δ q x)^[a + pc] = (fun q => M.δ q x)^[a])
    (l m : ℕ) (hl : T ≤ l) (hm : T + pc ≤ m) :
    M.accepts (pre ++ List.replicate l x ++ [y] ++ List.replicate m x ++ suf)
      ↔ M.accepts (pre ++ List.replicate (l + pc) x ++ [y] ++ List.replicate (m - pc) x ++ suf) := by
  unfold SliceMSO.DetAuto.accepts
  have key : List.foldl M.δ M.q0
        (pre ++ List.replicate l x ++ [y] ++ List.replicate m x ++ suf)
      = List.foldl M.δ M.q0
        (pre ++ List.replicate (l + pc) x ++ [y] ++ List.replicate (m - pc) x ++ suf) := by
    simp only [List.foldl_append, foldl_rep_iter, List.foldl_cons, List.foldl_nil]
    have hpre : (fun q => M.δ q x)^[l + pc] (List.foldl M.δ M.q0 pre)
        = (fun q => M.δ q x)^[l] (List.foldl M.δ M.q0 pre) := congrFun (hper l hl) _
    have hsuf : (fun q => M.δ q x)^[m] = (fun q => M.δ q x)^[m - pc] := by
      have h := hper (m - pc) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at h
    rw [hpre, hsuf]
  rw [key]

end CopiedSufRunGate
