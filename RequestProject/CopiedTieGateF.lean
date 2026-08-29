/-
# The FULL-cell sigma-marked clause (§9 tower, F3.9 — the FG4 fix)

The core sigma-marked clause decodes the `D`-atom via `regionDecodeL (rsB i)`, which places the atom
at `mS-1 + (rsB i).posAt t n` — the MIDDLE region only.  The tie gate must cover the FULL
`RegionSpecF` cells, including the SUFFIX `D^{mS-1}` `sufIdx` cells (the FG4 undercount).
`clauseFormulaMkF` is the verbatim twin with the `D`-atom decode arm
`regionDecodeL (rsB i) → regionDecodeLF (rs i)` over `rs : RegionSpecF Bh`; ALL position reasoning is
delegated to `CopiedLandmarkF.regionDecodeLF_sat`, so the rest of the proof is unchanged (the
validity hypothesis `hv` is threaded for the `sufIdx` in-slice bound).  The `D`-atom coordinate
becomes the full `(rs i).posAt mS t n = cellTupleF rs mS t n i`.

On top of it, Option A builds the single-arity full-cell TIE clause `cellClauseF` (with
`cellClauseF_sat`) and the fibred cell configurations `cfgCellArmFL` / `cfgCellGAFL`.
-/import RequestProject.CopiedTieGate
import RequestProject.CopiedLandmarkF

namespace CopiedTieGate

open WRP Step MSOMarkN SliceFasGatesGA CopiedLandmark CopiedCells
open scoped Classical

variable (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)

section ClauseMkF
variable {Bh : ℕ}

/-- **The FULL-cell sigma-marked clause formula** (FG4): the sigma-marked bulk clause with the
`D`-atom decode arm `regionDecodeL (rsB i) → regionDecodeLF (rs i)` over a full
`RegionSpecF Bh` descriptor. -/
noncomputable def clauseFormulaMkF (M mthr : ℕ) (Sv Fv Bv : Finset ℕ)
    (hS : ∀ r ∈ Sv, r < M)
    (rs : Fin (P.toPoly.arity c') → RegionSpecF Bh)
    (sigma : Finset (Fin (P.toPoly.arity c'))) :
    MSO.Formula Step (P.toPoly.arity c + P.toPoly.arity c') 0 :=
  faFOs (P.toPoly.arity c' + 3) (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        if i ∈ sigma then MSO.Formula.tru
        else SliceFasGates.relabelFO (decAddrMk P c c' i)
          (CopiedLandmark.regionDecodeLF (rs i)))))
      (MSO.Formula.and
        (MSOMarkN.andList (sigma.toList.map (fun i =>
          SliceFasGates.relabelFO (eqAddrMk P c c' i)
            (SliceFasGates.mso_offset_eq (Alpha := Step) 0).choose)))
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun _ : Fin 1 => (⟨P.toPoly.arity c' + 1, by omega⟩ :
            Fin (P.toPoly.arity c + P.toPoly.arity c' + (P.toPoly.arity c' + 3))))
          CopiedLandmark.mso_firstD.choose)
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun _ : Fin 1 => (⟨P.toPoly.arity c' + 2, by omega⟩ :
            Fin (P.toPoly.arity c + P.toPoly.arity c' + (P.toPoly.arity c' + 3))))
          CopiedLandmark.mso_lastU.choose)
      (MSO.Formula.and
        (SliceFasGates.relabelFO (embAddrMk P c c') (P.toPoly.selDef c').choose)
      (MSO.Formula.and
        (SliceFasGates.relabelFO (embAddrMk P c c') (P.toPoly.labelDef c' D).choose)
        (SliceFasGates.relabelFO (cfgAddrMk P c c')
          (cfgPosFormulaL M mthr Sv Fv Bv hS))))))))
    (SliceFasGates.relabelFO (gordLMk P c c') (P.toPoly.ordDef c c').choose))

/-! ## Option A: the single-arity full-cell TIE clause (the gate building block) -/

/-- The ord-addressing for the single-arity clause: the `U`-atom (first `arity c` of
`ordDef`) reads the FREE marks (HIGH block, offset `arity c' + 3`); the `D`-atom (next
`arity c'`) reads the bound `D`-coords (LOW block, `0..arity c'-1`). -/
def gordCellF (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) :
    Fin (P.toPoly.arity c + P.toPoly.arity c') →
      Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)) :=
  fun a => if h : a.1 < P.toPoly.arity c
    then ⟨P.toPoly.arity c' + 3 + a.1, by have := a.2; omega⟩
    else ⟨a.1 - P.toPoly.arity c, by have := a.2; omega⟩

section CellClauseF
variable (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
variable {Bh : ℕ}

/-- **The single-arity full-cell TIE clause** (option A): the `D`-atom is QUANTIFIED
(faFOs block `arity c' + 3` = `D`-coords + base + firstD + lastU); the position is decoded
via `regionDecodeLF` (full cell, incl. suffix).  A `Formula Step (arity c) 0`, suitable for
the single `markedDFAN` gate. -/
noncomputable def cellClauseF (M mthr : ℕ) (Sv Fv Bv : Finset ℕ)
    (hS : ∀ r ∈ Sv, r < M)
    (rs : Fin (P.toPoly.arity c') → RegionSpecF Bh) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  faFOs (P.toPoly.arity c' + 3) (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        SliceFasGates.relabelFO
          (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
            ⟨P.toPoly.arity c', by omega⟩
            (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
              ⟨i.1, by have := i.2; omega⟩
              (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
                ⟨P.toPoly.arity c' + 1, by omega⟩
                (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
                  ⟨P.toPoly.arity c' + 2, by omega⟩ Fin.elim0))))
          (CopiedLandmark.regionDecodeLF (rs i)))))
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun _ : Fin 1 => (⟨P.toPoly.arity c' + 1, by omega⟩ :
            Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3))))
          CopiedLandmark.mso_firstD.choose)
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun _ : Fin 1 => (⟨P.toPoly.arity c' + 2, by omega⟩ :
            Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3))))
          CopiedLandmark.mso_lastU.choose)
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ :
              Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3))))
          (P.toPoly.selDef c').choose)
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ :
              Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3))))
          (P.toPoly.labelDef c' D).choose)
        (SliceFasGates.relabelFO
          (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
            ⟨P.toPoly.arity c', by omega⟩
            (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
              ⟨P.toPoly.arity c' + 1, by omega⟩
              (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
                ⟨P.toPoly.arity c' + 2, by omega⟩ Fin.elim0)))
          (cfgPosFormulaL M mthr Sv Fv Bv hS)))))))
    (SliceFasGates.relabelFO (gordCellF P c c') (P.toPoly.ordDef c c').choose))

/-- **The single-arity full-cell clause characterization**: holds of the `U`-marks `ī`
exactly when every selected `D`-atom in full cell form (over `rs`) whose base passes the
position clause is `ord`-above `ī`. -/
theorem cellClauseF_sat (M mthr : ℕ) (Sv Fv Bv : Finset ℕ)
    (hS : ∀ r ∈ Sv, r < M)
    (rs : Fin (P.toPoly.arity c') → RegionSpecF Bh)
    (mS n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hBn : Bh ≤ n) (hM2 : M % 2 = 0)
    (hSodd : ∀ r ∈ Sv, r % 2 = 1) (hFodd : ∀ f ∈ Fv, f % 2 = 1)
    (hBeven : ∀ k ∈ Bv, k % 2 = 0)
    (hv : ∀ i, (rs i).valid mS)
    (_hīv : ∀ i, ī i < (copiedSlice mS n).length) :
    ((cellClauseF P c c' M mthr Sv Fv Bv hS rs).Sat (copiedSlice mS n) ī Fin.elim0 ↔
      ∀ (t : ℕ) (xb : Fin (P.toPoly.arity c') → ℕ),
        t < n →
        (∀ i, xb i < (copiedSlice mS n).length) →
        xb = (fun i => (rs i).posAt mS t n) →
        P.toPoly.sel c' (copiedSlice mS n) xb →
        P.toPoly.label c' (copiedSlice mS n) xb = D →
        cfgPosL M mthr Sv Fv Bv (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
        P.toPoly.ord c c' (copiedSlice mS n) ī xb) := by
  have hlen : (copiedSlice mS n).length = 2 * (mS + n) := length_copiedSlice mS n
  -- the addressing composition facts (single-arity: pb LOW block, ī HIGH marks)
  have hDec : ∀ (pb : Fin (P.toPoly.arity c' + 3) → ℕ) (i : Fin (P.toPoly.arity c')),
      (appFO pb ī) ∘ (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
        ⟨P.toPoly.arity c', by omega⟩
        (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
          ⟨i.1, by have := i.2; omega⟩
          (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
            ⟨P.toPoly.arity c' + 1, by omega⟩
            (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
              ⟨P.toPoly.arity c' + 2, by omega⟩ Fin.elim0))))
      = Fin.cons (pb ⟨P.toPoly.arity c', by omega⟩)
          (Fin.cons (pb ⟨i.1, by have := i.2; omega⟩)
            (Fin.cons (pb ⟨P.toPoly.arity c' + 1, by omega⟩)
              (Fin.cons (pb ⟨P.toPoly.arity c' + 2, by omega⟩) Fin.elim0))) := by
    intro pb i
    funext s
    refine Fin.cases ?_ (fun s1 => ?_) s
    · exact appFO_low pb ī _ (by omega) (by omega)
    refine Fin.cases ?_ (fun s2 => ?_) s1
    · exact appFO_low pb ī _ (by have := i.2; omega) (by have := i.2; omega)
    refine Fin.cases ?_ (fun s3 => ?_) s2
    · exact appFO_low pb ī _ (by omega) (by omega)
    refine Fin.cases ?_ (fun s4 => s4.elim0) s3
    · exact appFO_low pb ī _ (by omega) (by omega)
  have hCfg : ∀ (pb : Fin (P.toPoly.arity c' + 3) → ℕ),
      (appFO pb ī) ∘ (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
        ⟨P.toPoly.arity c', by omega⟩
        (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
          ⟨P.toPoly.arity c' + 1, by omega⟩
          (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)))
            ⟨P.toPoly.arity c' + 2, by omega⟩ Fin.elim0)))
      = Fin.cons (pb ⟨P.toPoly.arity c', by omega⟩)
          (Fin.cons (pb ⟨P.toPoly.arity c' + 1, by omega⟩)
            (Fin.cons (pb ⟨P.toPoly.arity c' + 2, by omega⟩) Fin.elim0)) := by
    intro pb
    funext s
    refine Fin.cases ?_ (fun s1 => ?_) s
    · exact appFO_low pb ī _ (by omega) (by omega)
    refine Fin.cases ?_ (fun s2 => ?_) s1
    · exact appFO_low pb ī _ (by omega) (by omega)
    refine Fin.cases ?_ (fun s3 => s3.elim0) s2
    · exact appFO_low pb ī _ (by omega) (by omega)
  have hCst : ∀ (pb : Fin (P.toPoly.arity c' + 3) → ℕ) (k : ℕ) (hk : k < P.toPoly.arity c' + 3),
      (appFO pb ī) ∘ (fun _ : Fin 1 =>
        (⟨k, by omega⟩ : Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3))))
      = fun _ => pb ⟨k, hk⟩ := by
    intro pb k hk; funext s; exact appFO_low pb ī k hk (by omega)
  have hEmb : ∀ (pb : Fin (P.toPoly.arity c' + 3) → ℕ),
      (appFO pb ī) ∘ (fun t : Fin (P.toPoly.arity c') =>
        (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3))))
      = fun t => pb ⟨t.1, by have := t.2; omega⟩ := by
    intro pb; funext t; exact appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)
  have hGordU : ∀ (pb : Fin (P.toPoly.arity c' + 3) → ℕ),
      (fun t => ((appFO pb ī) ∘ gordCellF P c c') (Fin.castAdd (P.toPoly.arity c') t)) = ī := by
    intro pb; funext t
    show appFO pb ī (gordCellF P c c' (Fin.castAdd _ t)) = ī t
    have hg : gordCellF P c c' (Fin.castAdd (P.toPoly.arity c') t)
        = ⟨P.toPoly.arity c' + 3 + t.1, by have := t.2; omega⟩ := by
      unfold gordCellF
      rw [dif_pos (show ((Fin.castAdd (P.toPoly.arity c') t) : ℕ) < P.toPoly.arity c from t.2)]
      rfl
    rw [hg]
    exact appFO_high pb ī t.1 t.2 (by have := t.2; omega)
  have hGordD : ∀ (pb : Fin (P.toPoly.arity c' + 3) → ℕ),
      (fun t => ((appFO pb ī) ∘ gordCellF P c c') (Fin.natAdd (P.toPoly.arity c) t))
        = fun t => pb ⟨t.1, by have := t.2; omega⟩ := by
    intro pb; funext t
    show appFO pb ī (gordCellF P c c' (Fin.natAdd _ t)) = pb ⟨t.1, by have := t.2; omega⟩
    have hnv : ((Fin.natAdd (P.toPoly.arity c) t) : ℕ) = P.toPoly.arity c + t.1 := rfl
    have hg : gordCellF P c c' (Fin.natAdd (P.toPoly.arity c) t)
        = ⟨t.1, by have := t.2; omega⟩ := by
      unfold gordCellF
      rw [dif_neg (show ¬(((Fin.natAdd (P.toPoly.arity c) t) : ℕ) < P.toPoly.arity c) from by
        rw [hnv]; omega)]
      congr 1
      show ((Fin.natAdd (P.toPoly.arity c) t) : ℕ) - P.toPoly.arity c = t.1
      rw [hnv]; omega
    rw [hg]
    exact appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)
  rw [cellClauseF, sat_faFOs]
  constructor
  · -- raw → semantic
    intro h t xb hz hxbv hcell hsel hlab hcfg
    set pb : Fin (P.toPoly.arity c' + 3) → ℕ := fun j =>
      if h0 : j.1 < P.toPoly.arity c' then xb ⟨j.1, h0⟩
      else if j.1 < P.toPoly.arity c' + 1 then mS + 2 * t
      else if j.1 < P.toPoly.arity c' + 2 then mS + 1
      else mS + 2 * (n - 1) with hpbdef
    have hpbz : pb ⟨P.toPoly.arity c', by omega⟩ = mS + 2 * t := by
      rw [hpbdef]
      show (if h0 : P.toPoly.arity c' < P.toPoly.arity c' then
          xb ⟨P.toPoly.arity c', h0⟩
        else if P.toPoly.arity c' < P.toPoly.arity c' + 1 then mS + 2 * t
        else if P.toPoly.arity c' < P.toPoly.arity c' + 2 then mS + 1
        else mS + 2 * (n - 1)) = mS + 2 * t
      rw [dif_neg (by omega), if_pos (by omega)]
    have hpbyF : pb ⟨P.toPoly.arity c' + 1, by omega⟩ = mS + 1 := by
      rw [hpbdef]
      show (if h0 : P.toPoly.arity c' + 1 < P.toPoly.arity c' then
          xb ⟨P.toPoly.arity c' + 1, h0⟩
        else if P.toPoly.arity c' + 1 < P.toPoly.arity c' + 1 then mS + 2 * t
        else if P.toPoly.arity c' + 1 < P.toPoly.arity c' + 2 then mS + 1
        else mS + 2 * (n - 1)) = mS + 1
      rw [dif_neg (by omega), if_neg (by omega), if_pos (by omega)]
    have hpbyL : pb ⟨P.toPoly.arity c' + 2, by omega⟩ = mS + 2 * (n - 1) := by
      rw [hpbdef]
      show (if h0 : P.toPoly.arity c' + 2 < P.toPoly.arity c' then
          xb ⟨P.toPoly.arity c' + 2, h0⟩
        else if P.toPoly.arity c' + 2 < P.toPoly.arity c' + 1 then mS + 2 * t
        else if P.toPoly.arity c' + 2 < P.toPoly.arity c' + 2 then mS + 1
        else mS + 2 * (n - 1)) = mS + 2 * (n - 1)
      rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hpbx : ∀ i : Fin (P.toPoly.arity c'), pb ⟨i.1, by have := i.2; omega⟩ = xb i := by
      intro i
      rw [hpbdef]
      show (if h0 : i.1 < P.toPoly.arity c' then xb ⟨i.1, h0⟩
        else if i.1 < P.toPoly.arity c' + 1 then mS + 2 * t
        else if i.1 < P.toPoly.arity c' + 2 then mS + 1
        else mS + 2 * (n - 1)) = xb i
      rw [dif_pos i.2]
    have hval : ∀ j, pb j < (copiedSlice mS n).length := by
      intro j
      rw [hpbdef]; simp only []
      by_cases h0 : j.1 < P.toPoly.arity c'
      · rw [dif_pos h0]; exact hxbv _
      · rw [dif_neg h0]
        by_cases h1 : j.1 < P.toPoly.arity c' + 1
        · rw [if_pos h1, hlen]; omega
        · rw [if_neg h1]
          by_cases h2 : j.1 < P.toPoly.arity c' + 2
          · rw [if_pos h2, hlen]; omega
          · rw [if_neg h2, hlen]; omega
    have hsat := h pb hval
    rw [SliceFasGates.sat_imp] at hsat
    have hord := hsat (by
      simp only [MSO.Formula.sat_and]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [MSOMarkN.sat_andList]
        intro ψ hψ
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hψ
        rw [SliceFasGates.sat_relabelFO, hDec pb i, hpbz, hpbyF, hpbyL, hpbx i]
        refine (regionDecodeLF_sat (rs i) mS t n (xb i) hm hn hBn hz
          (by rw [← hlen]; exact hxbv i) (hv i)).mpr ?_
        rw [hcell]
      · rw [SliceFasGates.sat_relabelFO, hCst pb (P.toPoly.arity c' + 1) (by omega), hpbyF]
        exact (CopiedLandmark.mso_firstD.choose_spec (copiedSlice mS n) (mS + 1)
            (by rw [hlen]; omega)).mpr
          ((firstD_copiedSlice mS n hm hn (mS + 1) (by omega)).mpr rfl)
      · rw [SliceFasGates.sat_relabelFO, hCst pb (P.toPoly.arity c' + 2) (by omega), hpbyL]
        refine (CopiedLandmark.mso_lastU.choose_spec (copiedSlice mS n)
            (mS + 2 * (n - 1)) (by rw [hlen]; omega)).mpr ?_
        rw [hlen]
        exact (lastU_copiedSlice mS n hm hn (mS + 2 * (n - 1)) (by omega)).mpr rfl
      · rw [SliceFasGates.sat_relabelFO, hEmb pb]
        have : (fun t : Fin (P.toPoly.arity c') => pb ⟨t.1, by have := t.2; omega⟩) = xb := by
          funext i; exact hpbx i
        rw [this]
        exact ((P.toPoly.selDef c').choose_spec (copiedSlice mS n) xb).mp hsel
      · rw [SliceFasGates.sat_relabelFO, hEmb pb]
        have : (fun t : Fin (P.toPoly.arity c') => pb ⟨t.1, by have := t.2; omega⟩) = xb := by
          funext i; exact hpbx i
        rw [this]
        exact ((P.toPoly.labelDef c' D).choose_spec (copiedSlice mS n) xb).mp hlab
      · rw [SliceFasGates.sat_relabelFO, hCfg pb, hpbz, hpbyF, hpbyL]
        exact (sat_cfgPosFormulaL M mthr Sv Fv Bv hS mS n (mS + 2 * t) hm hn
          (by omega)).mpr hcfg)
    rw [SliceFasGates.sat_relabelFO] at hord
    have hrel := ((P.toPoly.ordDef c c').choose_spec (copiedSlice mS n)
      ((appFO pb ī) ∘ gordCellF P c c')).mpr hord
    simp only [] at hrel
    rw [hGordU pb, hGordD pb] at hrel
    have hxbeq : (fun t : Fin (P.toPoly.arity c') => pb ⟨t.1, by have := t.2; omega⟩) = xb := by
      funext i; exact hpbx i
    rwa [hxbeq] at hrel
  · -- semantic → raw
    intro h pb hpb
    rw [SliceFasGates.sat_imp]
    intro hant
    simp only [MSO.Formula.sat_and] at hant
    obtain ⟨hdec, hfirstD, hlastU, hselD, hlabD, hcfgF⟩ := hant
    rw [SliceFasGates.sat_relabelFO, hCst pb (P.toPoly.arity c' + 1) (by omega)] at hfirstD
    have hyFval : pb ⟨P.toPoly.arity c' + 1, by omega⟩ = mS + 1 :=
      (firstD_copiedSlice mS n hm hn (pb ⟨P.toPoly.arity c' + 1, by omega⟩)
          (by rw [← hlen]; exact hpb _)).mp
        ((CopiedLandmark.mso_firstD.choose_spec (copiedSlice mS n)
            (pb ⟨P.toPoly.arity c' + 1, by omega⟩) (hpb _)).mp hfirstD)
    rw [SliceFasGates.sat_relabelFO, hCst pb (P.toPoly.arity c' + 2) (by omega)] at hlastU
    have hyLval : pb ⟨P.toPoly.arity c' + 2, by omega⟩ = mS + 2 * (n - 1) := by
      refine (lastU_copiedSlice mS n hm hn (pb ⟨P.toPoly.arity c' + 2, by omega⟩)
          (by rw [← hlen]; exact hpb _)).mp ?_
      have hh := (CopiedLandmark.mso_lastU.choose_spec (copiedSlice mS n)
        (pb ⟨P.toPoly.arity c' + 2, by omega⟩) (hpb _)).mp hlastU
      rw [hlen] at hh
      exact hh
    rw [SliceFasGates.sat_relabelFO, hCfg pb, hyFval, hyLval] at hcfgF
    have hcfgz := (sat_cfgPosFormulaL M mthr Sv Fv Bv hS mS n
      (pb ⟨P.toPoly.arity c', by omega⟩) hm hn
      (by rw [← hlen]; exact hpb _)).mp hcfgF
    obtain ⟨t, htz, htn⟩ := cfgPosL_base M mthr Sv Fv Bv mS n
      (pb ⟨P.toPoly.arity c', by omega⟩) hm hn hM2 hS hSodd hFodd hBeven hcfgz
    have hcell : (fun i : Fin (P.toPoly.arity c') => pb ⟨i.1, by have := i.2; omega⟩)
        = fun i => (rs i).posAt mS t n := by
      funext i
      have hd := (MSOMarkN.sat_andList _ _ _ _).mp hdec _
        (List.mem_map_of_mem (List.mem_finRange i))
      rw [SliceFasGates.sat_relabelFO, hDec pb i, hyFval, hyLval, htz] at hd
      exact (regionDecodeLF_sat (rs i) mS t n (pb ⟨i.1, by have := i.2; omega⟩)
        hm hn hBn htn (by rw [← hlen]; exact hpb _) (hv i)).mp hd
    have hrel := h t (fun i => pb ⟨i.1, by have := i.2; omega⟩) htn (fun i => hpb _) hcell
      (((P.toPoly.selDef c').choose_spec (copiedSlice mS n) _).mpr (by
        rw [SliceFasGates.sat_relabelFO, hEmb pb] at hselD; exact hselD))
      (((P.toPoly.labelDef c' D).choose_spec (copiedSlice mS n) _).mpr (by
        rw [SliceFasGates.sat_relabelFO, hEmb pb] at hlabD; exact hlabD))
      (by rw [← htz]; exact hcfgz)
    rw [SliceFasGates.sat_relabelFO]
    refine ((P.toPoly.ordDef c c').choose_spec (copiedSlice mS n)
      ((appFO pb ī) ∘ gordCellF P c c')).mp ?_
    simp only []
    rw [hGordU pb, hGordD pb]
    exact hrel

end CellClauseF

/-! ## Option A: the fibred TIE gate (single `markedDFAN` over the full cells) -/

/-- One arm of the fibred `cfgPosL` cell premise (the `cfgPosL`/`t<n` twin of
`CopiedSelector.cfgCellArmF`): the atom `b` is a full `RegionSpecF Dd` cell at some valid
base `t < n` whose landmark-relative position config holds. -/
def cfgCellArmFL {P : WRP.Presentation Step Step} (Dd M mthr : ℕ)
    (S Front Back : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Dd) → Finset ℕ)
    (mS n : ℕ) (b : P.toPoly.Atom) : Prop :=
  ∃ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF Dd) (t : ℕ),
    (∀ i, (rs i).valid mS) ∧ t < n ∧
    b.2 = CopiedDstar.cellTupleF rs mS t n ∧
    cfgPosL M mthr (S b.1 rs) (Front b.1 rs) (Back b.1 rs)
      (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t)

/-- The fibred `cfgPosL` cell premise (the two-layer disjunction, `cfgPosL` twin of
`CopiedSelector.cfgCellGAF` carrying the full bulk/frozen finsets). -/
def cfgCellGAFL {P : WRP.Presentation Step Step} (B Bh M mthr : ℕ)
    (S₁ F₁ K₁ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (S₂ F₂ K₂ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (mS n : ℕ) (b : P.toPoly.Atom) : Prop :=
  cfgCellArmFL B M mthr S₁ F₁ K₁ mS n b ∨ cfgCellArmFL Bh M mthr S₂ F₂ K₂ mS n b

end ClauseMkF

end CopiedTieGate
