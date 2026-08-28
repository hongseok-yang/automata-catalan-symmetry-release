/-
# The bounded-cell gate variant (§9 mS-direction, the fibred-fold ONE-DFA piece)

`fasU_atomOrd_full_gate_fibred` builds its DFA from a formula whose cellClause `andList`s range over
`regionTuplesF B/Bh (arity c') mS`, which GROWS with `mS` — so the DFA differs per `mS` and cannot be a
single folded `GdfaF` object.  This file builds the variant whose cellClause `andList`s range over a
FIXED, mS-FREE cell set `boundedTuplesF` (the only cells with non-empty selector emitters: `core` plus
shallow `prefIdx q < q_U` / `sufIdx l < q_D`).  Because the formula is mS-free, the resulting `Mdfa` is
ONE object usable for EVERY `mS` in the class — folding becomes `rfl`.

The deep cells (in `regionTuplesF mS \ boundedTuplesF`) are dropped: their selector emitters are empty
(`hS₁b`/`hF₁b`/… hypotheses, supplied by the selector's emptiness conclusions), so in the BACKWARD
direction a `cfgCellGAFL` witness cell — whose `cfgPosL` premise forces some emitter non-empty — is
necessarily a bounded cell.  In the FORWARD direction the bounded cells are valid at every `mS > max q_U q_D`.
-/
import RequestProject.CopiedFullGate

namespace CopiedBoundedGate

open WRP Step SliceMSO MSOMarkN SliceMarkN CopiedCells CopiedSufRunGate CopiedDeepRunGate CopiedFullGate

/-- The bounded (mS-free) descriptor set: all `core` cells plus shallow `prefIdx q < q_U` / `sufIdx l < q_D`. -/
def boundedSpecFs (B q_U q_D : ℕ) : Finset (RegionSpecF B) :=
  (Finset.univ.image RegionSpecF.core)
    ∪ ((Finset.range q_U).image RegionSpecF.prefIdx)
    ∪ ((Finset.range q_D).image RegionSpecF.sufIdx)

theorem mem_boundedSpecFs {B : ℕ} (q_U q_D : ℕ) (r : RegionSpecF B) :
    r ∈ boundedSpecFs B q_U q_D ↔
      (match r with
        | .core _ => True
        | .prefIdx q => q < q_U
        | .sufIdx l => l < q_D) := by
  unfold boundedSpecFs
  rcases r with r | q | l <;>
    simp [Finset.mem_union, Finset.mem_image]

/-- The bounded tuple enumeration (mS-free; NOT a `Fintype` instance). -/
def boundedTuplesF (B k q_U q_D : ℕ) : Finset (Fin k → RegionSpecF B) :=
  Fintype.piFinset (fun _ => boundedSpecFs B q_U q_D)

theorem mem_boundedTuplesF {B k : ℕ} (q_U q_D : ℕ) (r : Fin k → RegionSpecF B) :
    r ∈ boundedTuplesF B k q_U q_D ↔
      ∀ i, (match r i with
        | .core _ => True
        | .prefIdx q => q < q_U
        | .sufIdx l => l < q_D) := by
  unfold boundedTuplesF
  rw [Fintype.mem_piFinset]
  exact forall_congr' (fun i => mem_boundedSpecFs q_U q_D (r i))

/-- Every bounded cell is `valid` at any `mS > max q_U q_D`. -/
theorem boundedTuplesF_valid {B k : ℕ} (q_U q_D mS : ℕ) (hqU : q_U < mS) (hqD : q_D < mS)
    (rs : Fin k → RegionSpecF B) (hrs : rs ∈ boundedTuplesF B k q_U q_D) :
    ∀ i, (rs i).valid mS := by
  intro i
  have hi := (mem_boundedTuplesF q_U q_D rs).mp hrs i
  rcases hrsi : rs i with r | q | l
  · simp only [RegionSpecF.valid]
  · simp only [hrsi] at hi; simp only [RegionSpecF.valid]; omega
  · simp only [hrsi] at hi; simp only [RegionSpecF.valid]; omega

variable (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)

/-- **The bounded-cell full gate** — the mS-FREE twin of `fasU_atomOrd_full_gate_fibred`.  Its DFA is a
single object (the cellClause `andList`s range over the fixed `boundedTuplesF`, not `regionTuplesF mS`),
so `Mdfa` is hoisted before `∀ mS` and works for EVERY `mS > max q_U q_D` in the class.  Acceptance is the
SAME gate condition (sel ∧ label=U ∧ ∀b cfgCellGAFL→atomOrd ∧ run ∧ deep).  Needs the emitter-emptiness
hypotheses `hS₁b/…/hK₂b` (deep cells have empty emitters) to route the backward `cfgCellGAFL` witness to a
bounded cell. -/
theorem fasU_atomOrd_full_gate_bounded (B Bh M mthr q_U q_D : ℕ)
    (S₁ F₁ K₁ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpecF B) → Finset ℕ)
    (S₂ F₂ K₂ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpecF Bh) → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : (c' : Fin P.toPoly.K) → Finset ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hSsuf : ∀ c' r, r ∈ Ssuf c' → r < Q) (hSpre : ∀ c' r, r ∈ Spre c' → r < Q)
    (hBB : B ≤ Bh) (hBh1 : 1 ≤ Bh) (hM2 : M % 2 = 0)
    (hS₁ : ∀ c' rs, ∀ r ∈ S₁ c' rs, r < M ∧ r % 2 = 1)
    (hS₂ : ∀ c' rs, ∀ r ∈ S₂ c' rs, r < M ∧ r % 2 = 1)
    (hF₁ : ∀ c' rs, ∀ f ∈ F₁ c' rs, f % 2 = 1)
    (hF₂ : ∀ c' rs, ∀ f ∈ F₂ c' rs, f % 2 = 1)
    (hK₁ : ∀ c' rs, ∀ k ∈ K₁ c' rs, k % 2 = 0)
    (hK₂ : ∀ c' rs, ∀ k ∈ K₂ c' rs, k % 2 = 0)
    (hS₁b : ∀ c' rs, rs ∉ boundedTuplesF B (P.toPoly.arity c') q_U q_D → S₁ c' rs = ∅)
    (hF₁b : ∀ c' rs, rs ∉ boundedTuplesF B (P.toPoly.arity c') q_U q_D → F₁ c' rs = ∅)
    (hK₁b : ∀ c' rs, rs ∉ boundedTuplesF B (P.toPoly.arity c') q_U q_D → K₁ c' rs = ∅)
    (hS₂b : ∀ c' rs, rs ∉ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D → S₂ c' rs = ∅)
    (hF₂b : ∀ c' rs, rs ∉ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D → F₂ c' rs = ∅)
    (hK₂b : ∀ c' rs, rs ∉ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D → K₂ c' rs = ∅) :
    ∃ Mdfa : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (mS n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ), q_U < mS → q_D < mS → Bh ≤ n →
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
            ((boundedTuplesF B (P.toPoly.arity c') q_U q_D).toList).map
              (fun rs => CopiedTieGate.cellClauseF P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
                (fun r hr => (hS₁ c' rs r hr).1) rs))))
          (MSO.Formula.and
            (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
              ((boundedTuplesF Bh (P.toPoly.arity c') q_U q_D).toList).map
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
  refine ⟨Mdfa, fun mS n ī hqU hqD hBhn hval => ?_⟩
  have hm : 1 ≤ mS := by omega
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
        boundedTuplesF_valid q_U q_D mS hqU hqD rs (Finset.mem_toList.mp hrsmem)
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
        boundedTuplesF_valid q_U q_D mS hqU hqD rs (Finset.mem_toList.mp hrsmem)
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
      · have hrsbound : rs ∈ boundedTuplesF B (P.toPoly.arity c') q_U q_D := by
          by_contra hns
          rcases hbcfg.2 with ⟨_, _, r, hr, _⟩ | ⟨f, hf, _⟩ | ⟨k, hk, _⟩
          · rw [hS₁b c' rs hns] at hr; exact absurd hr (Finset.notMem_empty r)
          · rw [hF₁b c' rs hns] at hf; exact absurd hf (Finset.notMem_empty f)
          · rw [hK₁b c' rs hns] at hk; exact absurd hk (Finset.notMem_empty k)
        rw [MSOMarkN.sat_andList] at hord₁
        have hclause := hord₁ (CopiedTieGate.cellClauseF P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
            (fun r hr => (hS₁ c' rs r hr).1) rs)
          (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
            List.mem_map_of_mem (Finset.mem_toList.mpr hrsbound)⟩)
        rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
          (fun r hr => (hS₁ c' rs r hr).1) rs mS n ī hm hn hBn hM2
          (fun r hr => (hS₁ c' rs r hr).2) (hF₁ c' rs) (hK₁ c' rs) hrsv hval] at hclause
        exact hclause t xb hz hbsel.1 hbcell hbsel.2 hbD hbcfg
      · have hrsbound : rs ∈ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D := by
          by_contra hns
          rcases hbcfg.2 with ⟨_, _, r, hr, _⟩ | ⟨f, hf, _⟩ | ⟨k, hk, _⟩
          · rw [hS₂b c' rs hns] at hr; exact absurd hr (Finset.notMem_empty r)
          · rw [hF₂b c' rs hns] at hf; exact absurd hf (Finset.notMem_empty f)
          · rw [hK₂b c' rs hns] at hk; exact absurd hk (Finset.notMem_empty k)
        rw [MSOMarkN.sat_andList] at hord₂
        have hclause := hord₂ (CopiedTieGate.cellClauseF P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
            (fun r hr => (hS₂ c' rs r hr).1) rs)
          (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
            List.mem_map_of_mem (Finset.mem_toList.mpr hrsbound)⟩)
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

end CopiedBoundedGate
