/-
# The deep-suffix (from-end) atomOrd gate (§9 single-gate selector-mS, the FROM-END component)

The decoupled mS-direction selector `eqRankD_cell_selector_fibred_mS` realises CORE only for
SHALLOW achievers (`¬DeepSuf`, depth `l < q_D`).  But a nonzero-slope final-`D`-run whose DEEP
endpoint is the global `d*`-min is a genuine selected-`D` achiever at depth `l ∈ [Nc, mS-2]`
(`selB` minimises over the `.inr (.inl i_off)` from-end cells, `i_off ∈ [1, q_D]`, via
`dstarRankGA_m_eq_selB`).  Such a from-end achiever is `¬cfgCellGAFL` (it is `DeepSuf`) and lies in
no slope-0 tying class, so NEITHER the CORE gate NOR the per-residue-class run-clauses force
`atomOrd`-precedence to it — a genuine coverage gap (`FORMALISATION_WORKLOG.md` UPDATE 62).

This file builds the missing FROM-END component: one clause per from-end offset `k`
(`= i_off - 1`), pinning the single position `|w| - 1 - k` via `SliceFasGates.mso_position_fromEnd`
in place of the residue-class guard.  It is the from-end twin of `CopiedSufRunGate.sufOrdClauseAt`
(which guards on `position ≡ r [Q]`); the boundary shapes are folded into the EP-in-mS family
(`CopiedTie2b.gate_accepts_EP_mS_mixed`) downstream.

* `deepSufOrdClauseAt` — the universal-over-competitor-coord atomOrd clause with the from-end pin.
* `deepSufOrdClauseAt_gate` — its DFA realisation, spec ∀-word.

Mirrors `CopiedSufRunGate.sufOrdClauseAt` / `sufOrdClauseAt_gate` verbatim, swapping the
`mso_position_mod Q r hr` guard for `mso_position_fromEnd k`.
-/
import RequestProject.CopiedSufRunGate

namespace CopiedDeepRunGate

open WRP Step MSO MSOMarkN SliceMarkN CopiedSufRunGate

/-- **Per-from-end-offset suffix-run atomOrd clause.**  The from-end twin of
`CopiedSufRunGate.sufOrdClauseAt`: the residue guard `position ≡ r [Q]` is replaced by the
from-end pin `position + 1 + k = |w|` (`SliceFasGates.mso_position_fromEnd k`), which selects the
single position `|w|-1-k` (the `(k+1)`-th position from the end). -/
noncomputable def deepSufOrdClauseAt (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (k : ℕ) :
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
            (SliceFasGates.mso_position_fromEnd k).choose))))
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

/-- **Per-from-end-offset suffix-run atomOrd gate** (DFA realisation of `deepSufOrdClauseAt`),
spec ∀-word.  `A.accepts(markAtN a) ↔ ∀ xb (in-slice), (all coords of xb in the final D-run, each
the `(k+1)`-th from the end, ∧ xb a selected `D`-atom) → ord c c' a xb`. -/
theorem deepSufOrdClauseAt_gate (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) (k : ℕ) :
    ∃ A : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ),
        (∀ i, i_marks i < w.length) →
        (A.accepts (markAtN _ w i_marks) ↔
          ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < w.length) →
            ((∀ i, (w[xb i]? = some D ∧ ∀ q, q < w.length → xb i < q → w[q]? = some D)
                ∧ xb i + 1 + k = w.length)
              ∧ P.toPoly.sel c' w xb ∧ P.toPoly.label c' w xb = D) →
            P.toPoly.ord c c' w i_marks xb) := by
  obtain ⟨A, hA⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c) (deepSufOrdClauseAt P c c' k)
  refine ⟨A, fun w i_marks hi => ?_⟩
  rw [hA w i_marks hi, deepSufOrdClauseAt, SliceFasGatesGA.sat_faFOs]
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

/-! ## The PREFIX deep twin (the initial `U^mS`-run, anchored at the first `D`)

The deep-prefix cell `.inr (.inr i_off)` sits at position `mS-1-i_off`, near the END of the initial
U-run — which for `n ≥ 1` is exactly `firstD - (i_off+2)` (the first `D` is at position `mS+1`).  So,
unlike the suffix (anchored at the word end via `mso_position_fromEnd`), the deep-prefix is anchored
at the FIRST `D`.  `mso_position_beforeFirstD k` pins "`p+k` is the first `D`"; the deep-prefix
competitor at offset `i_off` is captured at `k = i_off + 2`. -/

/-- **Position-`k`-before-the-first-`D` MSO predicate.**  For a fixed `k`, an MSO formula deciding
"`p + k` is the first `D`" (`w[p+k] = D ∧ no earlier position is a `D`) at every valid position `p`.
Successor-based induction like `SliceFasGates.mso_position_fromEnd`; base `k = 0` = "`p` is the first
`D`". -/
theorem mso_position_beforeFirstD (k : ℕ) :
    ∃ φ : MSO.Formula Step 1 0, ∀ (w : List Step) (p : ℕ), p < w.length →
      (φ.Sat w (fun _ => p) Fin.elim0 ↔
        (w[p + k]? = some D ∧ ∀ q, q < p + k → w[q]? ≠ some D)) := by
  induction k with
  | zero =>
      refine ⟨MSO.Formula.and (MSO.Formula.labelEq (0 : Fin 1) D)
        (MSO.Formula.faFO (MSO.Formula.imp (MSO.Formula.lt (0 : Fin 2) (1 : Fin 2))
          (MSO.Formula.neg (MSO.Formula.labelEq (0 : Fin 2) D)))),
        fun w p hp => ?_⟩
      rw [MSO.Formula.sat_and, MSO.Formula.sat_labelEq, SliceFasGates.sat_faFO]
      simp only [Nat.add_zero]
      constructor
      · rintro ⟨hD, hf⟩
        refine ⟨hD, fun q hq => ?_⟩
        have hql : q < w.length := by omega
        have h := hf q hql
        rw [SliceFasGates.sat_imp, MSO.Formula.sat_lt, MSO.Formula.sat_neg,
          MSO.Formula.sat_labelEq] at h
        exact h hq
      · rintro ⟨hD, hf⟩
        refine ⟨hD, fun q _ => ?_⟩
        rw [SliceFasGates.sat_imp, MSO.Formula.sat_lt, MSO.Formula.sat_neg,
          MSO.Formula.sat_labelEq]
        intro hqp
        exact hf q hqp
  | succ k ih =>
      obtain ⟨φk, hφk⟩ := ih
      refine ⟨MSO.Formula.exFO (MSO.Formula.and (MSO.Formula.lt (1 : Fin 2) (0 : Fin 2))
        (MSO.Formula.and (SliceFasGates.relabelFO (fun _ => (0 : Fin 2)) φk)
          (MSO.Formula.faFO (MSO.Formula.neg (MSO.Formula.and (MSO.Formula.lt (2 : Fin 3) (0 : Fin 3))
            (MSO.Formula.lt (0 : Fin 3) (1 : Fin 3))))))),
        fun w p hp => ?_⟩
      rw [MSO.Formula.sat_exFO]
      have hidx : p + 1 + k = p + (k + 1) := by omega
      constructor
      · rintro ⟨s, hs, hsat⟩
        rw [MSO.Formula.sat_and, MSO.Formula.sat_and] at hsat
        obtain ⟨hlt, hk, hbet⟩ := hsat
        have hps : p < s := hlt
        rw [SliceFasGates.sat_relabelFO] at hk
        have hval : (Fin.cons s (fun _ => p) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
            = fun _ => s := by funext x; simp
        rw [hval] at hk
        have hkspec := (hφk w s hs).mp hk
        rw [SliceFasGates.sat_faFO] at hbet
        have hsp1 : s = p + 1 := by
          by_contra hne
          have hcon := hbet (p + 1) (by omega)
          rw [MSO.Formula.sat_neg, MSO.Formula.sat_and, MSO.Formula.sat_lt,
            MSO.Formula.sat_lt] at hcon
          exact hcon ⟨by show p < p + 1; omega, by show p + 1 < s; omega⟩
        subst hsp1
        rw [hidx] at hkspec
        exact hkspec
      · rintro ⟨hD, hf⟩
        rw [← hidx] at hD hf
        obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.mp hD
        refine ⟨p + 1, by omega, ?_⟩
        rw [MSO.Formula.sat_and, MSO.Formula.sat_and]
        refine ⟨?_, ?_, ?_⟩
        · rw [MSO.Formula.sat_lt]; show p < p + 1; omega
        · rw [SliceFasGates.sat_relabelFO]
          have hval : (Fin.cons (p + 1) (fun _ => p) : Fin 2 → ℕ)
              ∘ (fun _ : Fin 1 => (0 : Fin 2)) = fun _ => p + 1 := by funext x; simp
          rw [hval]
          exact (hφk w (p + 1) (by omega)).mpr ⟨hD, hf⟩
        · rw [SliceFasGates.sat_faFO]
          intro r _
          rw [MSO.Formula.sat_neg, MSO.Formula.sat_and, MSO.Formula.sat_lt, MSO.Formula.sat_lt]
          rintro ⟨h1, h2⟩
          have hh1 : p < r := h1
          have hh2 : r < p + 1 := h2
          omega

/-- **Per-from-first-D-offset prefix-run atomOrd clause.**  The deep-prefix twin of
`deepSufOrdClauseAt`: `inInitialURun` (in place of `inFinalDRun`) and the first-`D` anchor
`mso_position_beforeFirstD k` (in place of `mso_position_fromEnd k`). -/
noncomputable def deepPreOrdClauseAt (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (k : ℕ) :
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
            (mso_position_beforeFirstD k).choose))))
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

/-- **Per-from-first-D-offset prefix-run atomOrd gate** (DFA realisation of `deepPreOrdClauseAt`). -/
theorem deepPreOrdClauseAt_gate (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) (k : ℕ) :
    ∃ A : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ),
        (∀ i, i_marks i < w.length) →
        (A.accepts (markAtN _ w i_marks) ↔
          ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < w.length) →
            ((∀ i, (w[xb i]? = some U ∧ ∀ q, q < w.length → q < xb i → w[q]? = some U)
                ∧ (w[xb i + k]? = some D ∧ ∀ q, q < xb i + k → w[q]? ≠ some D))
              ∧ P.toPoly.sel c' w xb ∧ P.toPoly.label c' w xb = D) →
            P.toPoly.ord c c' w i_marks xb) := by
  obtain ⟨A, hA⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c) (deepPreOrdClauseAt P c c' k)
  refine ⟨A, fun w i_marks hi => ?_⟩
  rw [hA w i_marks hi, deepPreOrdClauseAt, SliceFasGatesGA.sat_faFOs]
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

/-! ## Pulling the deep band out of CORE (the logical skeleton of the 5-arm split) -/

end CopiedDeepRunGate
