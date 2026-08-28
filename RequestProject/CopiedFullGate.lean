/-
# The conjoined full gate (§9 mS-direction direct bridge, step 3a)

The direct `hbr` bridge needs ONE marked DFA whose acceptance characterizes the TIE competitor
quantifier over ALL selected-`D` `d*`-achievers — covered (by COVERAGE, `CopiedAchieverLocus`) by the
CORE cell gate (`CopiedTieGate.cfgCellGAFL`) ∧ the boundary run-clauses ∧ the deep from-end clauses.

This file first FACTORS the per-clause `.Sat` characterizations out of the `…_gate` lemmas (whose
proofs build a `markedDFAN_exists` wrapper around exactly these `.Sat ↔ condition` bodies), so the
conjoined gate can include the clauses as sub-formulas of ONE `markedDFAN`.

* `deepSufOrdClauseAt_sat` / `deepPreOrdClauseAt_sat` — the deep clause `.Sat` characterizations
  (the bodies of `CopiedDeepRunGate.deepSufOrdClauseAt_gate` / `deepPreOrdClauseAt_gate` minus the
  `markedDFAN_exists` wrapper).
-/
import RequestProject.CopiedDeepRunGate
import RequestProject.CopiedTieGateF

namespace CopiedFullGate

open WRP Step MSO MSOMarkN SliceMarkN CopiedSufRunGate CopiedDeepRunGate CopiedTieGate CopiedRank

/-- **`deepSufOrdClauseAt` satisfaction** (the body of `deepSufOrdClauseAt_gate` after the
`markedDFAN_exists`/`rw [hA]` wrapper): the formula's `.Sat` at the mark valuation `i_marks` is the
deep-suffix-offset-`k` atomOrd condition. -/
theorem deepSufOrdClauseAt_sat (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) (k : ℕ)
    (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ) (_hi : ∀ i, i_marks i < w.length) :
    (deepSufOrdClauseAt P c c' k).Sat w i_marks Fin.elim0 ↔
      ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < w.length) →
        ((∀ i, (w[xb i]? = some D ∧ ∀ q, q < w.length → xb i < q → w[q]? = some D)
            ∧ xb i + 1 + k = w.length)
          ∧ P.toPoly.sel c' w xb ∧ P.toPoly.label c' w xb = D) →
        P.toPoly.ord c c' w i_marks xb := by
  rw [deepSufOrdClauseAt, SliceFasGatesGA.sat_faFOs]
  have hguarddec : ∀ (xb : Fin (P.toPoly.arity c') → ℕ) (i : Fin (P.toPoly.arity c')),
      xb i < w.length →
      ((MSO.Formula.and
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            inFinalDRun)
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            (SliceFasGates.mso_position_fromEnd k).choose)).Sat w
        (SliceFasGatesGA.appFO xb i_marks) Fin.elim0 ↔
        ((w[xb i]? = some D ∧ ∀ q, q < w.length → xb i < q → w[q]? = some D) ∧ xb i + 1 + k = w.length)) := by
    intro xb i hxv
    have hv0 : ((SliceFasGatesGA.appFO xb i_marks) ∘
        (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ :
          Fin (P.toPoly.arity c + P.toPoly.arity c')))) = fun _ => xb i := by
      funext _
      exact SliceFasGatesGA.appFO_low xb i_marks i.1 (by have := i.2; omega) (by have := i.2; omega)
    rw [MSO.Formula.sat_and, SliceFasGates.sat_relabelFO, SliceFasGates.sat_relabelFO,
      sat_inFinalDRun, hv0,
      (SliceFasGates.mso_position_fromEnd k).choose_spec w (xb i) hxv]
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
        ∧ pb i + 1 + k = w.length := by
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

/-- **`deepPreOrdClauseAt` satisfaction** (the prefix twin). -/
theorem deepPreOrdClauseAt_sat (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) (k : ℕ)
    (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ) (_hi : ∀ i, i_marks i < w.length) :
    (deepPreOrdClauseAt P c c' k).Sat w i_marks Fin.elim0 ↔
      ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < w.length) →
        ((∀ i, (w[xb i]? = some U ∧ ∀ q, q < w.length → q < xb i → w[q]? = some U)
            ∧ (w[xb i + k]? = some D ∧ ∀ q, q < xb i + k → w[q]? ≠ some D))
          ∧ P.toPoly.sel c' w xb ∧ P.toPoly.label c' w xb = D) →
        P.toPoly.ord c c' w i_marks xb := by
  rw [deepPreOrdClauseAt, SliceFasGatesGA.sat_faFOs]
  have hguarddec : ∀ (xb : Fin (P.toPoly.arity c') → ℕ) (i : Fin (P.toPoly.arity c')),
      xb i < w.length →
      ((MSO.Formula.and
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            inInitialURun)
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            (mso_position_beforeFirstD k).choose)).Sat w
        (SliceFasGatesGA.appFO xb i_marks) Fin.elim0 ↔
        ((w[xb i]? = some U ∧ ∀ q, q < w.length → q < xb i → w[q]? = some U)
          ∧ (w[xb i + k]? = some D ∧ ∀ q, q < xb i + k → w[q]? ≠ some D))) := by
    intro xb i hxv
    have hv0 : ((SliceFasGatesGA.appFO xb i_marks) ∘
        (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ :
          Fin (P.toPoly.arity c + P.toPoly.arity c')))) = fun _ => xb i := by
      funext _
      exact SliceFasGatesGA.appFO_low xb i_marks i.1 (by have := i.2; omega) (by have := i.2; omega)
    rw [MSO.Formula.sat_and, SliceFasGates.sat_relabelFO, SliceFasGates.sat_relabelFO,
      sat_inInitialURun, hv0,
      (mso_position_beforeFirstD k).choose_spec w (xb i) hxv]
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
    have hguard : ∀ i, (w[pb i]? = some U ∧ ∀ q, q < w.length → q < pb i → w[q]? = some U)
        ∧ (w[pb i + k]? = some D ∧ ∀ q, q < pb i + k → w[q]? ≠ some D) := by
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

/-- **`sufOrdClauseAt` satisfaction** (the per-residue-class suffix run clause; the body of
`CopiedSufRunGate.sufOrdClauseAt_gate` minus the `markedDFAN_exists` wrapper). -/
theorem sufOrdClauseAt_sat (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) (Q r : ℕ) (hr : r < Q)
    (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ) (_hi : ∀ i, i_marks i < w.length) :
    (sufOrdClauseAt P c c' Q r hr).Sat w i_marks Fin.elim0 ↔
      ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < w.length) →
        ((∀ i, (w[xb i]? = some D ∧ ∀ q, q < w.length → xb i < q → w[q]? = some D)
            ∧ xb i % Q = r)
          ∧ P.toPoly.sel c' w xb ∧ P.toPoly.label c' w xb = D) →
        P.toPoly.ord c c' w i_marks xb := by
  rw [sufOrdClauseAt, SliceFasGatesGA.sat_faFOs]
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

/-- **`prefOrdClauseAt` satisfaction** (the per-residue-class prefix run clause). -/
theorem prefOrdClauseAt_sat (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) (Q r : ℕ) (hr : r < Q)
    (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ) (_hi : ∀ i, i_marks i < w.length) :
    (prefOrdClauseAt P c c' Q r hr).Sat w i_marks Fin.elim0 ↔
      ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < w.length) →
        ((∀ i, (w[xb i]? = some U ∧ ∀ q, q < w.length → q < xb i → w[q]? = some U)
            ∧ xb i % Q = r)
          ∧ P.toPoly.sel c' w xb ∧ P.toPoly.label c' w xb = D) →
        P.toPoly.ord c c' w i_marks xb := by
  rw [prefOrdClauseAt, SliceFasGatesGA.sat_faFOs]
  have hguarddec : ∀ (xb : Fin (P.toPoly.arity c') → ℕ) (i : Fin (P.toPoly.arity c')),
      xb i < w.length →
      ((MSO.Formula.and
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            inInitialURun)
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            (SliceFasGates.mso_position_mod Q r hr).choose)).Sat w
        (SliceFasGatesGA.appFO xb i_marks) Fin.elim0 ↔
        ((w[xb i]? = some U ∧ ∀ q, q < w.length → q < xb i → w[q]? = some U) ∧ xb i % Q = r)) := by
    intro xb i hxv
    have hv0 : ((SliceFasGatesGA.appFO xb i_marks) ∘
        (fun _ : Fin 1 => (⟨i.1, by have := i.2; omega⟩ :
          Fin (P.toPoly.arity c + P.toPoly.arity c')))) = fun _ => xb i := by
      funext _
      exact SliceFasGatesGA.appFO_low xb i_marks i.1 (by have := i.2; omega) (by have := i.2; omega)
    rw [MSO.Formula.sat_and, SliceFasGates.sat_relabelFO, SliceFasGates.sat_relabelFO,
      sat_inInitialURun, hv0,
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
    have hguard : ∀ i, (w[pb i]? = some U ∧ ∀ q, q < w.length → q < pb i → w[q]? = some U)
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

/-! ## The conjoined gate: CORE cell gate ∧ deep from-end clauses -/

/-- **The CORE+deep conjoined gate.**  Extends `CopiedTieGate.fasU_atomOrd_cellCfg_gate_fibred` by
conjoining the deep-suffix / deep-prefix from-end clauses (over offset sets `Dsuf`/`Dpre`) as further
`andList` sub-formulas of the ONE `markedDFAN`.  Acceptance ⟺ (the CORE gate condition) ∧ (every
deep-suffix offset `k ∈ Dsuf c'` atom is `ord`-preceded) ∧ (every deep-prefix offset). -/
theorem fasU_atomOrd_cell_deep_gate_fibred (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (B Bh M mthr : ℕ)
    (S₁ F₁ K₁ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (S₂ F₂ K₂ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (Dsuf Dpre : (c' : Fin P.toPoly.K) → Finset ℕ)
    (mS : ℕ) (hm : 1 ≤ mS) (hBB : B ≤ Bh) (hBh1 : 1 ≤ Bh) (hM2 : M % 2 = 0)
    (hS₁ : ∀ c' rs, ∀ r ∈ S₁ c' rs, r < M ∧ r % 2 = 1)
    (hS₂ : ∀ c' rs, ∀ r ∈ S₂ c' rs, r < M ∧ r % 2 = 1)
    (hF₁ : ∀ c' rs, ∀ f ∈ F₁ c' rs, f % 2 = 1)
    (hF₂ : ∀ c' rs, ∀ f ∈ F₂ c' rs, f % 2 = 1)
    (hK₁ : ∀ c' rs, ∀ k ∈ K₁ c' rs, k % 2 = 0)
    (hK₂ : ∀ c' rs, ∀ k ∈ K₂ c' rs, k % 2 = 0) :
    ∃ Mdfa : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ), Bh ≤ n →
        (∀ i, ī i < (copiedSlice mS n).length) →
        ((P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.label c (copiedSlice mS n) ī = U
          ∧ (∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
              P.toPoly.labelOf (copiedSlice mS n) b = D →
              CopiedTieGate.cfgCellGAFL B Bh M mthr S₁ F₁ K₁ S₂ F₂ K₂ mS n b →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
          ∧ (∀ (c' : Fin P.toPoly.K) (k : ℕ), k ∈ Dsuf c' →
              ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < (copiedSlice mS n).length) →
                ((∀ i, (((copiedSlice mS n)[xb i]? = some D
                      ∧ ∀ q, q < (copiedSlice mS n).length → xb i < q → (copiedSlice mS n)[q]? = some D)
                    ∧ xb i + 1 + k = (copiedSlice mS n).length))
                  ∧ P.toPoly.sel c' (copiedSlice mS n) xb ∧ P.toPoly.label c' (copiedSlice mS n) xb = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī xb)
          ∧ (∀ (c' : Fin P.toPoly.K) (k : ℕ), k ∈ Dpre c' →
              ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < (copiedSlice mS n).length) →
                ((∀ i, ((copiedSlice mS n)[xb i]? = some U
                      ∧ ∀ q, q < (copiedSlice mS n).length → q < xb i → (copiedSlice mS n)[q]? = some U)
                    ∧ ((copiedSlice mS n)[xb i + k]? = some D
                      ∧ ∀ q, q < xb i + k → (copiedSlice mS n)[q]? ≠ some D))
                  ∧ P.toPoly.sel c' (copiedSlice mS n) xb ∧ P.toPoly.label c' (copiedSlice mS n) xb = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī xb))
         ↔ Mdfa.accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)) := by
  obtain ⟨Mdfa, hM⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c)
    (MSO.Formula.and (P.toPoly.selDef c).choose
      (MSO.Formula.and (P.toPoly.labelDef c U).choose
        (MSO.Formula.and
          (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
            ((CopiedRank.regionTuplesF B (P.toPoly.arity c') mS).toList).map
              (fun rs => CopiedTieGate.cellClauseF P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
                (fun r hr => (hS₁ c' rs r hr).1) rs))))
          (MSO.Formula.and
            (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
              ((CopiedRank.regionTuplesF Bh (P.toPoly.arity c') mS).toList).map
                (fun rs => CopiedTieGate.cellClauseF P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
                  (fun r hr => (hS₂ c' rs r hr).1) rs))))
            (MSO.Formula.and
              (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                ((Dsuf c').toList).map (fun k => deepSufOrdClauseAt P c c' k))))
              (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                ((Dpre c').toList).map (fun k => deepPreOrdClauseAt P c c' k)))))))))
  refine ⟨Mdfa, fun n ī hBhn hval => ?_⟩
  have hBn : B ≤ n := le_trans hBB hBhn
  have hn : 1 ≤ n := le_trans hBh1 hBhn
  rw [hM (copiedSlice mS n) ī hval, MSO.Formula.sat_and, MSO.Formula.sat_and,
    MSO.Formula.sat_and, MSO.Formula.sat_and, MSO.Formula.sat_and]
  constructor
  · rintro ⟨hsel, hlab, hord, hdsuf, hdpre⟩
    refine ⟨((P.toPoly.selDef c).choose_spec (copiedSlice mS n) ī).mp hsel,
      ((P.toPoly.labelDef c U).choose_spec (copiedSlice mS n) ī).mp hlab, ?_, ?_, ?_, ?_⟩
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨rs, hrsmem, rfl⟩ := hψ
      have hrsv : ∀ i, (rs i).valid mS :=
        (CopiedRank.mem_regionTuplesF rs).mp (Finset.mem_toList.mp hrsmem)
      rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
        (fun r hr => (hS₁ c' rs r hr).1) rs mS n ī hm hn hBn hM2
        (fun r hr => (hS₁ c' rs r hr).2) (hF₁ c' rs) (hK₁ c' rs) hrsv hval]
      intro t xb hz hxv hcell hsel' hlab' hcfg
      exact hord ⟨c', xb⟩ ⟨hxv, hsel'⟩ hlab' (Or.inl ⟨rs, t, hrsv, hz, hcell, hcfg⟩)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨rs, hrsmem, rfl⟩ := hψ
      have hrsv : ∀ i, (rs i).valid mS :=
        (CopiedRank.mem_regionTuplesF rs).mp (Finset.mem_toList.mp hrsmem)
      rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
        (fun r hr => (hS₂ c' rs r hr).1) rs mS n ī hm hn hBhn hM2
        (fun r hr => (hS₂ c' rs r hr).2) (hF₂ c' rs) (hK₂ c' rs) hrsv hval]
      intro t xb hz hxv hcell hsel' hlab' hcfg
      exact hord ⟨c', xb⟩ ⟨hxv, hsel'⟩ hlab' (Or.inr ⟨rs, t, hrsv, hz, hcell, hcfg⟩)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨k, hkmem, rfl⟩ := hψ
      rw [deepSufOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval]
      exact hdsuf c' k (Finset.mem_toList.mp hkmem)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨k, hkmem, rfl⟩ := hψ
      rw [deepPreOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval]
      exact hdpre c' k (Finset.mem_toList.mp hkmem)
  · rintro ⟨hsel, hlab, hord₁, hord₂, hdsuf', hdpre'⟩
    refine ⟨((P.toPoly.selDef c).choose_spec (copiedSlice mS n) ī).mpr hsel,
      ((P.toPoly.labelDef c U).choose_spec (copiedSlice mS n) ī).mpr hlab, ?_, ?_, ?_⟩
    · rintro ⟨c', xb⟩ hbsel hbD (⟨rs, t, hrsv, hz, hbcell, hbcfg⟩ | ⟨rs, t, hrsv, hz, hbcell, hbcfg⟩)
      · rw [MSOMarkN.sat_andList] at hord₁
        have hclause := hord₁ (CopiedTieGate.cellClauseF P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
            (fun r hr => (hS₁ c' rs r hr).1) rs)
          (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
            List.mem_map_of_mem (Finset.mem_toList.mpr
              ((CopiedRank.mem_regionTuplesF rs).mpr hrsv))⟩)
        rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
          (fun r hr => (hS₁ c' rs r hr).1) rs mS n ī hm hn hBn hM2
          (fun r hr => (hS₁ c' rs r hr).2) (hF₁ c' rs) (hK₁ c' rs) hrsv hval] at hclause
        exact hclause t xb hz hbsel.1 hbcell hbsel.2 hbD hbcfg
      · rw [MSOMarkN.sat_andList] at hord₂
        have hclause := hord₂ (CopiedTieGate.cellClauseF P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
            (fun r hr => (hS₂ c' rs r hr).1) rs)
          (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
            List.mem_map_of_mem (Finset.mem_toList.mpr
              ((CopiedRank.mem_regionTuplesF rs).mpr hrsv))⟩)
        rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
          (fun r hr => (hS₂ c' rs r hr).1) rs mS n ī hm hn hBhn hM2
          (fun r hr => (hS₂ c' rs r hr).2) (hF₂ c' rs) (hK₂ c' rs) hrsv hval] at hclause
        exact hclause t xb hz hbsel.1 hbcell hbsel.2 hbD hbcfg
    · intro c' k hk
      rw [MSOMarkN.sat_andList] at hdsuf'
      have hclause := hdsuf' (deepSufOrdClauseAt P c c' k)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hk)⟩)
      rw [deepSufOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval] at hclause
      exact hclause
    · intro c' k hk
      rw [MSOMarkN.sat_andList] at hdpre'
      have hclause := hdpre' (deepPreOrdClauseAt P c c' k)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hk)⟩)
      rw [deepPreOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval] at hclause
      exact hclause

/-- **Total per-residue suffix run clause** (clamps `r ↦ r % Q`, so the clause takes only `r : ℕ`
with NO `r < Q` proof in the formula — letting it be `map`ped over a plain `Finset ℕ` without the
dependent-proof issue that breaks `markedDFAN_exists`). -/
noncomputable def sufOrdClauseAtTot (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hQ : 0 < Q) : MSO.Formula Step (P.toPoly.arity c) 0 :=
  sufOrdClauseAt P c c' Q (r % Q) (Nat.mod_lt r hQ)

theorem sufOrdClauseAtTot_sat (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) (Q r : ℕ)
    (hQ : 0 < Q) (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ) (hi : ∀ i, i_marks i < w.length) :
    (sufOrdClauseAtTot P c c' Q r hQ).Sat w i_marks Fin.elim0 ↔
      ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < w.length) →
        ((∀ i, (w[xb i]? = some D ∧ ∀ q, q < w.length → xb i < q → w[q]? = some D)
            ∧ xb i % Q = r % Q)
          ∧ P.toPoly.sel c' w xb ∧ P.toPoly.label c' w xb = D) →
        P.toPoly.ord c c' w i_marks xb :=
  sufOrdClauseAt_sat P c c' Q (r % Q) (Nat.mod_lt r hQ) w i_marks hi

/-- Prefix twin of `sufOrdClauseAtTot`. -/
noncomputable def prefOrdClauseAtTot (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hQ : 0 < Q) : MSO.Formula Step (P.toPoly.arity c) 0 :=
  prefOrdClauseAt P c c' Q (r % Q) (Nat.mod_lt r hQ)

theorem prefOrdClauseAtTot_sat (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) (Q r : ℕ)
    (hQ : 0 < Q) (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ) (hi : ∀ i, i_marks i < w.length) :
    (prefOrdClauseAtTot P c c' Q r hQ).Sat w i_marks Fin.elim0 ↔
      ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < w.length) →
        ((∀ i, (w[xb i]? = some U ∧ ∀ q, q < w.length → q < xb i → w[q]? = some U)
            ∧ xb i % Q = r % Q)
          ∧ P.toPoly.sel c' w xb ∧ P.toPoly.label c' w xb = D) →
        P.toPoly.ord c c' w i_marks xb :=
  prefOrdClauseAt_sat P c c' Q (r % Q) (Nat.mod_lt r hQ) w i_marks hi

/-! ## The FULL conjoined gate: CORE ∧ run clauses ∧ deep clauses -/

/-- **The FULL conjoined gate.**  `fasU_atomOrd_cell_deep_gate_fibred` further extended with the
per-residue-class boundary RUN clauses (`sufOrdClauseAt`/`prefOrdClauseAt` over the tying sets
`Ssuf`/`Spre ⊆ range Q`), as further `andList` sub-formulas of the ONE `markedDFAN`.  Acceptance ⟺
CORE (cfgCellGAFL) ∧ run-suf ∧ run-pre ∧ deep-suf ∧ deep-pre — the full direct-bridge gate condition. -/
theorem fasU_atomOrd_full_gate_fibred (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (B Bh M mthr : ℕ)
    (S₁ F₁ K₁ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (S₂ F₂ K₂ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : (c' : Fin P.toPoly.K) → Finset ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hSsuf : ∀ c' r, r ∈ Ssuf c' → r < Q) (hSpre : ∀ c' r, r ∈ Spre c' → r < Q)
    (mS : ℕ) (hm : 1 ≤ mS) (hBB : B ≤ Bh) (hBh1 : 1 ≤ Bh) (hM2 : M % 2 = 0)
    (hS₁ : ∀ c' rs, ∀ r ∈ S₁ c' rs, r < M ∧ r % 2 = 1)
    (hS₂ : ∀ c' rs, ∀ r ∈ S₂ c' rs, r < M ∧ r % 2 = 1)
    (hF₁ : ∀ c' rs, ∀ f ∈ F₁ c' rs, f % 2 = 1)
    (hF₂ : ∀ c' rs, ∀ f ∈ F₂ c' rs, f % 2 = 1)
    (hK₁ : ∀ c' rs, ∀ k ∈ K₁ c' rs, k % 2 = 0)
    (hK₂ : ∀ c' rs, ∀ k ∈ K₂ c' rs, k % 2 = 0) :
    ∃ Mdfa : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ), Bh ≤ n →
        (∀ i, ī i < (copiedSlice mS n).length) →
        ((P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.label c (copiedSlice mS n) ī = U
          ∧ (∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
              P.toPoly.labelOf (copiedSlice mS n) b = D →
              CopiedTieGate.cfgCellGAFL B Bh M mthr S₁ F₁ K₁ S₂ F₂ K₂ mS n b →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
          ∧ (∀ (c' : Fin P.toPoly.K) (r : ℕ), r ∈ Ssuf c' →
              ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < (copiedSlice mS n).length) →
                ((∀ i, ((copiedSlice mS n)[xb i]? = some D
                      ∧ ∀ q, q < (copiedSlice mS n).length → xb i < q → (copiedSlice mS n)[q]? = some D)
                    ∧ xb i % Q = r)
                  ∧ P.toPoly.sel c' (copiedSlice mS n) xb ∧ P.toPoly.label c' (copiedSlice mS n) xb = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī xb)
          ∧ (∀ (c' : Fin P.toPoly.K) (r : ℕ), r ∈ Spre c' →
              ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < (copiedSlice mS n).length) →
                ((∀ i, ((copiedSlice mS n)[xb i]? = some U
                      ∧ ∀ q, q < (copiedSlice mS n).length → q < xb i → (copiedSlice mS n)[q]? = some U)
                    ∧ xb i % Q = r)
                  ∧ P.toPoly.sel c' (copiedSlice mS n) xb ∧ P.toPoly.label c' (copiedSlice mS n) xb = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī xb)
          ∧ (∀ (c' : Fin P.toPoly.K) (k : ℕ), k ∈ Dsuf c' →
              ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < (copiedSlice mS n).length) →
                ((∀ i, (((copiedSlice mS n)[xb i]? = some D
                      ∧ ∀ q, q < (copiedSlice mS n).length → xb i < q → (copiedSlice mS n)[q]? = some D)
                    ∧ xb i + 1 + k = (copiedSlice mS n).length))
                  ∧ P.toPoly.sel c' (copiedSlice mS n) xb ∧ P.toPoly.label c' (copiedSlice mS n) xb = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī xb)
          ∧ (∀ (c' : Fin P.toPoly.K) (k : ℕ), k ∈ Dpre c' →
              ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < (copiedSlice mS n).length) →
                ((∀ i, ((copiedSlice mS n)[xb i]? = some U
                      ∧ ∀ q, q < (copiedSlice mS n).length → q < xb i → (copiedSlice mS n)[q]? = some U)
                    ∧ ((copiedSlice mS n)[xb i + k]? = some D
                      ∧ ∀ q, q < xb i + k → (copiedSlice mS n)[q]? ≠ some D))
                  ∧ P.toPoly.sel c' (copiedSlice mS n) xb ∧ P.toPoly.label c' (copiedSlice mS n) xb = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī xb))
         ↔ Mdfa.accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)) := by
  obtain ⟨Mdfa, hM⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c)
    (MSO.Formula.and (P.toPoly.selDef c).choose
      (MSO.Formula.and (P.toPoly.labelDef c U).choose
        (MSO.Formula.and
          (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
            ((CopiedRank.regionTuplesF B (P.toPoly.arity c') mS).toList).map
              (fun rs => CopiedTieGate.cellClauseF P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
                (fun r hr => (hS₁ c' rs r hr).1) rs))))
          (MSO.Formula.and
            (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
              ((CopiedRank.regionTuplesF Bh (P.toPoly.arity c') mS).toList).map
                (fun rs => CopiedTieGate.cellClauseF P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
                  (fun r hr => (hS₂ c' rs r hr).1) rs))))
            (MSO.Formula.and
              (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                ((Ssuf c').toList).map (fun r => sufOrdClauseAtTot P c c' Q r hQ))))
              (MSO.Formula.and
                (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                  ((Spre c').toList).map (fun r => prefOrdClauseAtTot P c c' Q r hQ))))
                (MSO.Formula.and
                  (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                    ((Dsuf c').toList).map (fun k => deepSufOrdClauseAt P c c' k))))
                  (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                    ((Dpre c').toList).map (fun k => deepPreOrdClauseAt P c c' k)))))))))))
  refine ⟨Mdfa, fun n ī hBhn hval => ?_⟩
  have hBn : B ≤ n := le_trans hBB hBhn
  have hn : 1 ≤ n := le_trans hBh1 hBhn
  rw [hM (copiedSlice mS n) ī hval, MSO.Formula.sat_and, MSO.Formula.sat_and,
    MSO.Formula.sat_and, MSO.Formula.sat_and, MSO.Formula.sat_and, MSO.Formula.sat_and,
    MSO.Formula.sat_and]
  constructor
  · rintro ⟨hsel, hlab, hord, hrsuf, hrpre, hdsuf, hdpre⟩
    refine ⟨((P.toPoly.selDef c).choose_spec (copiedSlice mS n) ī).mp hsel,
      ((P.toPoly.labelDef c U).choose_spec (copiedSlice mS n) ī).mp hlab, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨rs, hrsmem, rfl⟩ := hψ
      have hrsv : ∀ i, (rs i).valid mS :=
        (CopiedRank.mem_regionTuplesF rs).mp (Finset.mem_toList.mp hrsmem)
      rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
        (fun r hr => (hS₁ c' rs r hr).1) rs mS n ī hm hn hBn hM2
        (fun r hr => (hS₁ c' rs r hr).2) (hF₁ c' rs) (hK₁ c' rs) hrsv hval]
      intro t xb hz hxv hcell hsel' hlab' hcfg
      exact hord ⟨c', xb⟩ ⟨hxv, hsel'⟩ hlab' (Or.inl ⟨rs, t, hrsv, hz, hcell, hcfg⟩)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨rs, hrsmem, rfl⟩ := hψ
      have hrsv : ∀ i, (rs i).valid mS :=
        (CopiedRank.mem_regionTuplesF rs).mp (Finset.mem_toList.mp hrsmem)
      rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
        (fun r hr => (hS₂ c' rs r hr).1) rs mS n ī hm hn hBhn hM2
        (fun r hr => (hS₂ c' rs r hr).2) (hF₂ c' rs) (hK₂ c' rs) hrsv hval]
      intro t xb hz hxv hcell hsel' hlab' hcfg
      exact hord ⟨c', xb⟩ ⟨hxv, hsel'⟩ hlab' (Or.inr ⟨rs, t, hrsv, hz, hcell, hcfg⟩)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨r, hrmem, rfl⟩ := hψ
      have hrin : r ∈ Ssuf c' := Finset.mem_toList.mp hrmem
      rw [sufOrdClauseAtTot_sat P c c' Q r hQ (copiedSlice mS n) ī hval,
        Nat.mod_eq_of_lt (hSsuf c' r hrin)]
      exact hrsuf c' r hrin
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨r, hrmem, rfl⟩ := hψ
      have hrin : r ∈ Spre c' := Finset.mem_toList.mp hrmem
      rw [prefOrdClauseAtTot_sat P c c' Q r hQ (copiedSlice mS n) ī hval,
        Nat.mod_eq_of_lt (hSpre c' r hrin)]
      exact hrpre c' r hrin
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨k, hkmem, rfl⟩ := hψ
      rw [deepSufOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval]
      exact hdsuf c' k (Finset.mem_toList.mp hkmem)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨k, hkmem, rfl⟩ := hψ
      rw [deepPreOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval]
      exact hdpre c' k (Finset.mem_toList.mp hkmem)
  · rintro ⟨hsel, hlab, hord₁, hord₂, hrsuf', hrpre', hdsuf', hdpre'⟩
    refine ⟨((P.toPoly.selDef c).choose_spec (copiedSlice mS n) ī).mpr hsel,
      ((P.toPoly.labelDef c U).choose_spec (copiedSlice mS n) ī).mpr hlab, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨c', xb⟩ hbsel hbD (⟨rs, t, hrsv, hz, hbcell, hbcfg⟩ | ⟨rs, t, hrsv, hz, hbcell, hbcfg⟩)
      · rw [MSOMarkN.sat_andList] at hord₁
        have hclause := hord₁ (CopiedTieGate.cellClauseF P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
            (fun r hr => (hS₁ c' rs r hr).1) rs)
          (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
            List.mem_map_of_mem (Finset.mem_toList.mpr
              ((CopiedRank.mem_regionTuplesF rs).mpr hrsv))⟩)
        rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
          (fun r hr => (hS₁ c' rs r hr).1) rs mS n ī hm hn hBn hM2
          (fun r hr => (hS₁ c' rs r hr).2) (hF₁ c' rs) (hK₁ c' rs) hrsv hval] at hclause
        exact hclause t xb hz hbsel.1 hbcell hbsel.2 hbD hbcfg
      · rw [MSOMarkN.sat_andList] at hord₂
        have hclause := hord₂ (CopiedTieGate.cellClauseF P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
            (fun r hr => (hS₂ c' rs r hr).1) rs)
          (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
            List.mem_map_of_mem (Finset.mem_toList.mpr
              ((CopiedRank.mem_regionTuplesF rs).mpr hrsv))⟩)
        rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
          (fun r hr => (hS₂ c' rs r hr).1) rs mS n ī hm hn hBhn hM2
          (fun r hr => (hS₂ c' rs r hr).2) (hF₂ c' rs) (hK₂ c' rs) hrsv hval] at hclause
        exact hclause t xb hz hbsel.1 hbcell hbsel.2 hbD hbcfg
    · intro c' r hr
      rw [MSOMarkN.sat_andList] at hrsuf'
      have hclause := hrsuf' (sufOrdClauseAtTot P c c' Q r hQ)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hr)⟩)
      rw [sufOrdClauseAtTot_sat P c c' Q r hQ (copiedSlice mS n) ī hval,
        Nat.mod_eq_of_lt (hSsuf c' r hr)] at hclause
      exact hclause
    · intro c' r hr
      rw [MSOMarkN.sat_andList] at hrpre'
      have hclause := hrpre' (prefOrdClauseAtTot P c c' Q r hQ)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hr)⟩)
      rw [prefOrdClauseAtTot_sat P c c' Q r hQ (copiedSlice mS n) ī hval,
        Nat.mod_eq_of_lt (hSpre c' r hr)] at hclause
      exact hclause
    · intro c' k hk
      rw [MSOMarkN.sat_andList] at hdsuf'
      have hclause := hdsuf' (deepSufOrdClauseAt P c c' k)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hk)⟩)
      rw [deepSufOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval] at hclause
      exact hclause
    · intro c' k hk
      rw [MSOMarkN.sat_andList] at hdpre'
      have hclause := hdpre' (deepPreOrdClauseAt P c c' k)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hk)⟩)
      rw [deepPreOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval] at hclause
      exact hclause

end CopiedFullGate
