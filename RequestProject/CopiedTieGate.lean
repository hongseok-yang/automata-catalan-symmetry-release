/-
# The fibred TIE gate (§9 tower, Stage F3.6)

The hybrid gate of decision D2: frozen / boundary / mixed equal-rank
`D`-cells are handled by MARK-BASED pair components (no decode, no binders —
the whole `D`-atom is supplied as marks, so the constant-free formula's spec
is `∀`-word and holds AT the copied slice directly); bulk equal-rank
`D`-cells are handled by landmark-relative clauses (`clauseFormula`, built on
the F3.5 landmark decoder).

This file lands the index structure and the pair-component layer first.
`boundary_pair_component` is the A2 fix: ONE `markedDFAN_exists` per copy
pair `(c, c')` on the formula
`(selDef c' ∧ labelDef c' D) → ordDef c c'`, with the `c`-atom marked in the
low block and the `D`-atom in the high block (`Fin.append`).  Because the
`D`-atom is fully marked, `ordDef`'s `castAdd`/`natAdd` convention applies
with no relabelling.
-/
import RequestProject.CopiedLandmark
import RequestProject.SliceFasGatesGA
import RequestProject.CopiedGateEP

namespace CopiedTieGate

open WRP Step SliceFamilyCell SliceDstarGA MSOMarkN SliceMarkN SliceMSO
  CopiedLandmark
open scoped Classical

/-- **The bulk-clause index** (decision D11): a copy `c'`, the marked boundary
slots `sigma` of its `D`-atom, the total descriptor tuple `rsB` over the
enlarged bound `Bh` (sigma-slots carry junk, ignored by the formula), and the
bulk residue set `arm ⊆ Fin M`.  Parameterised by explicit `(B Bh M)` so it
appears in `tie_point_bridge_fibred`'s existential; `Fintype`/`DecidableEq`
derive from `RegionSpec`'s. -/
structure ClauseIdx (P : WRP.Presentation Step Step) (B Bh M : ℕ) where
  c' : Fin P.toPoly.K
  sigma : Finset (Fin (P.toPoly.arity c'))
  rsB : Fin (P.toPoly.arity c') → RegionSpec Bh
  arm : Finset (Fin M)
  deriving DecidableEq, Fintype

/-! ## The mark-based pair component (the A2 fix) -/

/-- The address map placing copy `c'`'s `arity c'` free variables into the
HIGH block (`arity c + ·`) of the combined `arity c + arity c'` valuation. -/
def hiAddr (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) :
    Fin (P.toPoly.arity c') → Fin (P.toPoly.arity c + P.toPoly.arity c') :=
  fun t => Fin.natAdd (P.toPoly.arity c) t

/-- **The boundary pair component**: a marked DFA over the combined arity that
decides, for the `c`-atom `i_marks` and a fully-marked `D`-atom `xb`,
"`xb` is a selected `D`-atom ⇒ the `c`-atom `≺`-precedes it".  Its spec is
`∀`-word, so it transfers to the copied slice for free. -/
theorem boundary_pair_component (P : WRP.Presentation Step Step)
    (c c' : Fin P.toPoly.K) :
    ∃ A : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c + P.toPoly.arity c')),
      ∀ (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ)
        (xb : Fin (P.toPoly.arity c') → ℕ),
        (∀ i, i_marks i < w.length) → (∀ i, xb i < w.length) →
        (A.accepts (markAtN _ w (Fin.append i_marks xb)) ↔
          ((P.toPoly.sel c' w xb ∧ P.toPoly.label c' w xb = D) →
            P.toPoly.ord c c' w i_marks xb)) := by
  obtain ⟨φs, hφs⟩ := P.toPoly.selDef c'
  obtain ⟨φl, hφl⟩ := P.toPoly.labelDef c' D
  obtain ⟨φo, hφo⟩ := P.toPoly.ordDef c c'
  set ψ : MSO.Formula Step (P.toPoly.arity c + P.toPoly.arity c') 0 :=
    MSO.Formula.imp
      (MSO.Formula.and
        (SliceFasGates.relabelFO (hiAddr P c c') φs)
        (SliceFasGates.relabelFO (hiAddr P c c') φl))
      φo with hψdef
  obtain ⟨A, hA⟩ := MSOMarkN.markedDFAN_exists _ ψ
  refine ⟨A, fun w i_marks xb hi hx => ?_⟩
  have hval : ∀ i, (Fin.append i_marks xb) i < w.length := by
    refine Fin.addCases (fun t => ?_) (fun t => ?_)
    · rw [Fin.append_left]; exact hi t
    · rw [Fin.append_right]; exact hx t
  rw [hA w (Fin.append i_marks xb) hval]
  -- decode the three sub-formulas at the combined valuation
  have hcomp : (Fin.append i_marks xb) ∘ (hiAddr P c c') = xb := by
    funext t
    show (Fin.append i_marks xb) (Fin.natAdd (P.toPoly.arity c) t) = xb t
    rw [Fin.append_right]
  have hsel : (SliceFasGates.relabelFO (hiAddr P c c') φs).Sat w
      (Fin.append i_marks xb) Fin.elim0 ↔ P.toPoly.sel c' w xb := by
    rw [SliceFasGates.sat_relabelFO, hcomp, ← hφs]
  have hlab : (SliceFasGates.relabelFO (hiAddr P c c') φl).Sat w
      (Fin.append i_marks xb) Fin.elim0 ↔ P.toPoly.label c' w xb = D := by
    rw [SliceFasGates.sat_relabelFO, hcomp, ← hφl]
  have h1 : (fun t => (Fin.append i_marks xb) (Fin.castAdd (P.toPoly.arity c') t))
      = i_marks := funext fun t => Fin.append_left i_marks xb t
  have h2 : (fun t => (Fin.append i_marks xb) (Fin.natAdd (P.toPoly.arity c) t))
      = xb := funext fun t => Fin.append_right i_marks xb t
  have hord : φo.Sat w (Fin.append i_marks xb) Fin.elim0
      ↔ P.toPoly.ord c c' w i_marks xb := by
    rw [← hφo]
    show P.toPoly.ord c c' w
        (fun t => (Fin.append i_marks xb) (Fin.castAdd (P.toPoly.arity c') t))
        (fun t => (Fin.append i_marks xb) (Fin.natAdd (P.toPoly.arity c) t)) ↔ _
    rw [h1, h2]
  rw [hψdef]
  rw [SliceFasGates.sat_imp, MSO.Formula.sat_and, hsel, hlab, hord]

/-! ## The bulk landmark clause — supporting layer

`offsetForm3` is the 3-slot fixed-difference gadget (slots `0=z, 1=yF, 2=yL`)
used by the landmark position-cell clause; `gordL`/`xOfL`/`comp_decodeL`/
`comp_gordL` are the address maps for the clause's `(Kc' + 3)`-binder block
(the `D`-tuple, base `z`, and the two landmarks `yF`/`yL`). -/

open SliceFasGatesGA

/-- 3-slot twin of `CopiedLandmark.offsetForm`: asserts `ρ hi = ρ lo + k` over
slots `0=z, 1=yF, 2=yL`. -/
noncomputable def offsetForm3 (lo hi : Fin 3) (k : ℕ) : MSO.Formula Step 3 0 :=
  SliceFasGates.relabelFO (fun i : Fin 2 => if i = 0 then lo else hi)
    (SliceFasGates.mso_offset_eq (Alpha := Step) k).choose

theorem offsetForm3_sat (lo hi : Fin 3) (k : ℕ) (w : List Step)
    (ρ : Fin 3 → ℕ) (hlo : ρ lo < w.length) (hhi : ρ hi < w.length) :
    (offsetForm3 lo hi k).Sat w ρ Fin.elim0 ↔ ρ hi = ρ lo + k := by
  unfold offsetForm3
  rw [SliceFasGates.sat_relabelFO]
  have hval : (ρ ∘ (fun i : Fin 2 => if i = 0 then lo else hi))
      = Fin.cons (ρ lo) (Fin.cons (ρ hi) Fin.elim0) := by
    funext i
    fin_cases i <;> simp [Function.comp]
  rw [hval]
  exact (SliceFasGates.mso_offset_eq (Alpha := Step) k).choose_spec w
    (ρ lo) (ρ hi) hlo hhi

variable (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)

/-- The clause's decode address map (4 slots `z, x_i, yF, yL` into the bound
block): all four targets live in the low `(Kc' + 3)`-block. -/
def decAddr (i : Fin (P.toPoly.arity c')) :
    Fin 4 → Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)) :=
  Fin.cons ⟨P.toPoly.arity c', by omega⟩
    (Fin.cons ⟨i.1, by have := i.2; omega⟩
      (Fin.cons ⟨P.toPoly.arity c' + 1, by omega⟩
        (Fin.cons ⟨P.toPoly.arity c' + 2, by omega⟩ Fin.elim0)))

/-- The `gord` analogue for the `(Kc' + 3)`-binder block: the `c`-atom (HIGH
marks) maps to `Kc' + 3 + idx`, the `c'`-atom (LOW bound `D`-tuple) to `idx`. -/
def gordL :
    Fin (P.toPoly.arity c + P.toPoly.arity c') →
    Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)) :=
  fun idx => if h : idx.1 < P.toPoly.arity c
    then ⟨P.toPoly.arity c' + 3 + idx.1, by omega⟩
    else ⟨idx.1 - P.toPoly.arity c, by have := idx.2; omega⟩

/-- The bound `D`-tuple read out of the binder block. -/
def xOfL {kb : ℕ} (pb : Fin (kb + 3) → ℕ) : Fin kb → ℕ :=
  fun i => pb ⟨i.1, by have := i.2; omega⟩

/-- The decode relabel reads `(z, x_i, yF, yL)` out of `appFO pb ī`. -/
theorem comp_decodeL (pb : Fin (P.toPoly.arity c' + 3) → ℕ)
    (ī : Fin (P.toPoly.arity c) → ℕ) (i : Fin (P.toPoly.arity c')) :
    (appFO pb ī) ∘ (decAddr P c c' i)
      = Fin.cons (pb ⟨P.toPoly.arity c', by omega⟩)
          (Fin.cons (xOfL pb i)
            (Fin.cons (pb ⟨P.toPoly.arity c' + 1, by omega⟩)
              (Fin.cons (pb ⟨P.toPoly.arity c' + 2, by omega⟩) Fin.elim0))) := by
  funext s
  refine Fin.cases ?_ (fun s1 => Fin.cases ?_
    (fun s2 => Fin.cases ?_ (fun s3 => Fin.cases ?_ (fun s4 => s4.elim0) s3) s2)
    s1) s
  · show appFO pb ī ⟨P.toPoly.arity c', _⟩ = pb ⟨P.toPoly.arity c', _⟩
    exact appFO_low pb ī (P.toPoly.arity c') (by omega) (by omega)
  · show appFO pb ī ⟨i.1, _⟩ = xOfL pb i
    exact appFO_low pb ī i.1 (by have := i.2; omega) (by have := i.2; omega)
  · show appFO pb ī ⟨P.toPoly.arity c' + 1, _⟩ = pb ⟨P.toPoly.arity c' + 1, _⟩
    exact appFO_low pb ī (P.toPoly.arity c' + 1) (by omega) (by omega)
  · show appFO pb ī ⟨P.toPoly.arity c' + 2, _⟩ = pb ⟨P.toPoly.arity c' + 2, _⟩
    exact appFO_low pb ī (P.toPoly.arity c' + 2) (by omega) (by omega)

/-- The `gordL` relabel reads `(ī, xOfL pb)` in `ordDef`'s block convention. -/
theorem comp_gordL (pb : Fin (P.toPoly.arity c' + 3) → ℕ)
    (ī : Fin (P.toPoly.arity c) → ℕ) :
    ((fun t => ((appFO pb ī) ∘ gordL P c c') (Fin.castAdd (P.toPoly.arity c') t))
        = ī)
    ∧ ((fun t => ((appFO pb ī) ∘ gordL P c c')
        (Fin.natAdd (P.toPoly.arity c) t)) = xOfL pb) := by
  constructor
  · funext t
    show appFO pb ī (gordL P c c' (Fin.castAdd _ t)) = ī t
    have hg : gordL P c c' (Fin.castAdd (P.toPoly.arity c') t)
        = ⟨P.toPoly.arity c' + 3 + t.1, by have := t.2; omega⟩ := by
      unfold gordL
      rw [dif_pos (show ((Fin.castAdd (P.toPoly.arity c') t) : ℕ)
        < P.toPoly.arity c from t.2)]
      rfl
    rw [hg, appFO_high pb ī t.1 t.2 (by have := t.2; omega)]
  · funext t
    show appFO pb ī (gordL P c c' (Fin.natAdd _ t)) = xOfL pb t
    have hv : ((Fin.natAdd (P.toPoly.arity c) t) : ℕ)
        = P.toPoly.arity c + t.1 := rfl
    have hg : gordL P c c' (Fin.natAdd (P.toPoly.arity c) t)
        = ⟨t.1, by have := t.2; omega⟩ := by
      unfold gordL
      rw [dif_neg (show ¬(((Fin.natAdd (P.toPoly.arity c) t) : ℕ)
        < P.toPoly.arity c) from by omega)]
      congr 1
      omega
    rw [hg]
    exact appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)

/-! ## The landmark position-cell clause -/

/-- The `Prop` the landmark position-cell clause decodes to.  A top-level
middle-window guard `yF ≤ z + 1 ∧ z ≤ yL` (i.e. `mS ≤ z ≤ lastU`, via the
`lt` constructor between bound slots — `mS`-free) EXCLUDES the prefix/suffix
stretch bases, so the backward direction can pin `z = mS + 2t` with `t < n`.
The inner disjunction is the residue arm (`firstD`-relative, with the `mthr`
margins for the cell window), a `firstD`-relative front offset, or a
`lastU`-relative back offset. -/
def cfgPosL (M mthr : ℕ) (S Front Back : Finset ℕ) (yF yL z : ℕ) : Prop :=
  (yF ≤ z + 1 ∧ z ≤ yL) ∧
  ((yF + mthr ≤ z ∧ z + mthr ≤ yL ∧ ∃ r ∈ S, (yF + (M - r)) % M = z % M)
  ∨ (∃ f ∈ Front, (f = 0 ∧ yF = z + 1) ∨ (f ≠ 0 ∧ z = yF + f))
  ∨ (∃ k ∈ Back, yL = z + k))

/-- The landmark-relative position-cell clause (slots `0=z, 1=yF, 2=yL`): a
middle-window guard (`mS ≤ z ≤ yL`, via `lt`/`offsetForm3`) conjoined with the
wrapped `cfgPosFormula` structure, each position primitive replaced by an
`offsetForm3`/`mso_offset_mod` reading a landmark slot — NO formula constant
depends on `mS` (D16). -/
noncomputable def cfgPosFormulaL (M mthr : ℕ) (S Front Back : Finset ℕ)
    (hS : ∀ r ∈ S, r < M) : MSO.Formula Step 3 0 :=
  MSO.Formula.and
    (MSO.Formula.and
      (MSO.Formula.or (MSO.Formula.neg (MSO.Formula.lt 0 1)) (offsetForm3 0 1 1))
      (MSO.Formula.neg (MSO.Formula.lt 2 0)))
    (MSO.Formula.or
      (MSO.Formula.and
        (MSO.Formula.neg (MSO.Formula.lt 0 1))
        (MSO.Formula.and
          (MSO.Formula.neg (SliceFasGates.bigOr ((List.range mthr).map
            (fun e => offsetForm3 1 0 e))))
          (MSO.Formula.and
            (MSO.Formula.neg (MSO.Formula.lt 2 0))
            (MSO.Formula.and
              (MSO.Formula.neg (SliceFasGates.bigOr ((List.range mthr).map
                (fun e => offsetForm3 0 2 e))))
              (SliceFasGates.bigOr (S.toList.attach.map (fun rr =>
                SliceFasGates.relabelFO
                  (fun i : Fin 2 => if i = 0 then (1 : Fin 3) else (0 : Fin 3))
                  (CopiedLandmark.mso_offset_mod M rr.1
                    (by have := hS rr.1 (Finset.mem_toList.mp rr.2); omega)
                    (hS rr.1 (Finset.mem_toList.mp rr.2))).choose)))))))
      (MSO.Formula.or
        (SliceFasGates.bigOr (Front.toList.map (fun f =>
          if f = 0 then offsetForm3 0 1 1 else offsetForm3 1 0 f)))
        (SliceFasGates.bigOr (Back.toList.map (fun k => offsetForm3 0 2 k)))))

/-- The landmark clause decodes to `cfgPosL` at the landmark valuation. -/
theorem sat_cfgPosFormulaL (M mthr : ℕ) (S Front Back : Finset ℕ)
    (hS : ∀ r ∈ S, r < M) (mS n z : ℕ) (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hz : z < 2 * (mS + n)) :
    (cfgPosFormulaL M mthr S Front Back hS).Sat (copiedSlice mS n)
        (Fin.cons z (Fin.cons (mS + 1) (Fin.cons (mS + 2 * (n - 1)) Fin.elim0)))
        Fin.elim0
      ↔ cfgPosL M mthr S Front Back (mS + 1) (mS + 2 * (n - 1)) z := by
  set ρ : Fin 3 → ℕ :=
    Fin.cons z (Fin.cons (mS + 1) (Fin.cons (mS + 2 * (n - 1)) Fin.elim0))
    with hρ
  have hlen : (copiedSlice mS n).length = 2 * (mS + n) := length_copiedSlice mS n
  have e0 : ρ 0 = z := rfl
  have e1 : ρ 1 = mS + 1 := rfl
  have e2 : ρ 2 = mS + 2 * (n - 1) := rfl
  have hz' : ρ 0 < (copiedSlice mS n).length := by rw [e0, hlen]; exact hz
  have hyF : ρ 1 < (copiedSlice mS n).length := by rw [e1, hlen]; omega
  have hyL : ρ 2 < (copiedSlice mS n).length := by rw [e2, hlen]; omega
  rw [cfgPosFormulaL]
  -- T1 : ∃ e < mthr, z = (mS+1) + e
  have h1 : (SliceFasGates.bigOr ((List.range mthr).map
        (fun e => offsetForm3 1 0 e))).Sat (copiedSlice mS n) ρ Fin.elim0
      ↔ ((mS + 1) ≤ z ∧ z < (mS + 1) + mthr) := by
    rw [SliceFasGates.sat_bigOr]
    constructor
    · rintro ⟨φ', hφ', hsat⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hφ'
      rw [List.mem_range] at he
      rw [offsetForm3_sat 1 0 e _ ρ hyF hz', e0, e1] at hsat
      omega
    · rintro ⟨hle, hlt⟩
      refine ⟨_, List.mem_map_of_mem (List.mem_range.mpr
        (show z - (mS + 1) < mthr by omega)), ?_⟩
      rw [offsetForm3_sat 1 0 (z - (mS + 1)) _ ρ hyF hz', e0, e1]
      omega
  -- T2 : ∃ e < mthr, (mS+2(n-1)) = z + e
  have h2 : (SliceFasGates.bigOr ((List.range mthr).map
        (fun e => offsetForm3 0 2 e))).Sat (copiedSlice mS n) ρ Fin.elim0
      ↔ (z ≤ mS + 2 * (n - 1) ∧ mS + 2 * (n - 1) < z + mthr) := by
    rw [SliceFasGates.sat_bigOr]
    constructor
    · rintro ⟨φ', hφ', hsat⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hφ'
      rw [List.mem_range] at he
      rw [offsetForm3_sat 0 2 e _ ρ hz' hyL, e0, e2] at hsat
      omega
    · rintro ⟨hle, hlt⟩
      refine ⟨_, List.mem_map_of_mem (List.mem_range.mpr
        (show mS + 2 * (n - 1) - z < mthr by omega)), ?_⟩
      rw [offsetForm3_sat 0 2 (mS + 2 * (n - 1) - z) _ ρ hz' hyL, e0, e2]
      omega
  -- residue : ∃ r ∈ S, ((mS+1)+(M-r))%M = z%M
  have h3 : (SliceFasGates.bigOr (S.toList.attach.map (fun rr =>
        SliceFasGates.relabelFO
          (fun i : Fin 2 => if i = 0 then (1 : Fin 3) else (0 : Fin 3))
          (CopiedLandmark.mso_offset_mod M rr.1
              (by have := hS rr.1 (Finset.mem_toList.mp rr.2); omega)
              (hS rr.1 (Finset.mem_toList.mp rr.2))).choose))).Sat
        (copiedSlice mS n) ρ Fin.elim0
      ↔ ∃ r ∈ S, ((mS + 1) + (M - r)) % M = z % M := by
    rw [SliceFasGates.sat_bigOr]
    have hcomp : (ρ ∘ (fun i : Fin 2 => if i = 0 then (1 : Fin 3) else (0 : Fin 3)))
        = Fin.cons (mS + 1) (Fin.cons z Fin.elim0) := by
      funext i
      fin_cases i <;> simp [Function.comp, e0, e1]
    constructor
    · rintro ⟨φ', hφ', hsat⟩
      obtain ⟨rr, _, rfl⟩ := List.mem_map.mp hφ'
      rw [SliceFasGates.sat_relabelFO, hcomp] at hsat
      have := ((CopiedLandmark.mso_offset_mod M rr.1
        (by have := hS rr.1 (Finset.mem_toList.mp rr.2); omega)
        (hS rr.1 (Finset.mem_toList.mp rr.2))).choose_spec (copiedSlice mS n)
        (mS + 1) z (by rw [hlen]; omega) (by rw [hlen]; exact hz)).mp hsat
      exact ⟨rr.1, Finset.mem_toList.mp rr.2, this⟩
    · rintro ⟨r, hrS, hres⟩
      refine ⟨_, List.mem_map.mpr ⟨⟨r, Finset.mem_toList.mpr hrS⟩,
        List.mem_attach _ _, rfl⟩, ?_⟩
      rw [SliceFasGates.sat_relabelFO, hcomp]
      exact ((CopiedLandmark.mso_offset_mod M r (by have := hS r hrS; omega) (hS r hrS)).choose_spec
        (copiedSlice mS n) (mS + 1) z (by rw [hlen]; omega)
        (by rw [hlen]; exact hz)).mpr hres
  -- front : ∃ f ∈ Front, (f=0 ∧ mS+1 = z+1) ∨ (f≠0 ∧ z = (mS+1)+f)
  have h4 : (SliceFasGates.bigOr (Front.toList.map (fun f =>
        if f = 0 then offsetForm3 0 1 1 else offsetForm3 1 0 f))).Sat
        (copiedSlice mS n) ρ Fin.elim0
      ↔ ∃ f ∈ Front, (f = 0 ∧ mS + 1 = z + 1) ∨ (f ≠ 0 ∧ z = (mS + 1) + f) := by
    rw [SliceFasGates.sat_bigOr]
    constructor
    · rintro ⟨φ', hφ', hsat⟩
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hφ'
      refine ⟨f, Finset.mem_toList.mp hf, ?_⟩
      by_cases hf0 : f = 0
      · rw [if_pos hf0] at hsat
        rw [offsetForm3_sat 0 1 1 _ ρ hz' hyF, e0, e1] at hsat
        exact Or.inl ⟨hf0, by omega⟩
      · rw [if_neg hf0] at hsat
        rw [offsetForm3_sat 1 0 f _ ρ hyF hz', e0, e1] at hsat
        exact Or.inr ⟨hf0, by omega⟩
    · rintro ⟨f, hf, hcase⟩
      refine ⟨_, List.mem_map_of_mem (Finset.mem_toList.mpr hf), ?_⟩
      rcases hcase with ⟨hf0, heq⟩ | ⟨hf0, heq⟩
      · rw [if_pos hf0, offsetForm3_sat 0 1 1 _ ρ hz' hyF, e0, e1]; omega
      · rw [if_neg hf0, offsetForm3_sat 1 0 f _ ρ hyF hz', e0, e1]; omega
  -- back : ∃ k ∈ Back, mS+2(n-1) = z+k
  have h5 : (SliceFasGates.bigOr (Back.toList.map
        (fun k => offsetForm3 0 2 k))).Sat (copiedSlice mS n) ρ Fin.elim0
      ↔ ∃ k ∈ Back, mS + 2 * (n - 1) = z + k := by
    rw [SliceFasGates.sat_bigOr]
    constructor
    · rintro ⟨φ', hφ', hsat⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ'
      rw [offsetForm3_sat 0 2 k _ ρ hz' hyL, e0, e2] at hsat
      exact ⟨k, Finset.mem_toList.mp hk, hsat⟩
    · rintro ⟨k, hk, heq⟩
      refine ⟨_, List.mem_map_of_mem (Finset.mem_toList.mpr hk), ?_⟩
      rw [offsetForm3_sat 0 2 k _ ρ hz' hyL, e0, e2]
      exact heq
  simp only [MSO.Formula.sat_or, MSO.Formula.sat_and, MSO.Formula.sat_neg]
  rw [show ((MSO.Formula.lt (0 : Fin 3) 1).Sat (copiedSlice mS n) ρ Fin.elim0
      ↔ z < mS + 1) from by rw [MSO.Formula.sat_lt, e0, e1],
    show ((offsetForm3 0 1 1).Sat (copiedSlice mS n) ρ Fin.elim0
      ↔ mS + 1 = z + 1) from by rw [offsetForm3_sat 0 1 1 _ ρ hz' hyF, e0, e1],
    show ((MSO.Formula.lt (2 : Fin 3) 0).Sat (copiedSlice mS n) ρ Fin.elim0
      ↔ mS + 2 * (n - 1) < z) from by rw [MSO.Formula.sat_lt, e0, e2],
    h1, h2, h3, h4, h5, cfgPosL]
  constructor
  · rintro ⟨⟨hgA, hgB⟩, harms⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rcases harms with ⟨hnlt1, hnt1, hnlt2, hnt2, hr⟩ | h
    · exact Or.inl ⟨by omega, by omega, hr⟩
    · exact Or.inr h
  · rintro ⟨⟨hgA, hgB⟩, harms⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rcases harms with ⟨hge, hle, hr⟩ | h
    · exact Or.inl ⟨by omega, by omega, by omega, by omega, hr⟩
    · exact Or.inr h

/-- **The parity+window pinning** (the new mathematics): under the hygiene,
`cfgPosL` at the landmark values forces the base to a middle U-block base
`mS + 2t` with `t < n`.  Every arm gives `z ≡ mS (mod 2)` (residue: `2 ∣ M`
and `r` odd; front/back: odd/even offsets); the guard gives `mS ≤ z ≤ lastU`. -/
theorem cfgPosL_base (M mthr : ℕ) (S Front Back : Finset ℕ) (mS n z : ℕ)
    (_hm : 1 ≤ mS) (hn : 1 ≤ n) (hM2 : M % 2 = 0) (hSlt : ∀ r ∈ S, r < M)
    (hSodd : ∀ r ∈ S, r % 2 = 1) (hFodd : ∀ f ∈ Front, f % 2 = 1)
    (hBeven : ∀ k ∈ Back, k % 2 = 0)
    (h : cfgPosL M mthr S Front Back (mS + 1) (mS + 2 * (n - 1)) z) :
    ∃ t, z = mS + 2 * t ∧ t < n := by
  obtain ⟨⟨hgA, hgB⟩, harms⟩ := h
  have hpar : z % 2 = mS % 2 := by
    rcases harms with ⟨_, _, r, hrS, hres⟩ | ⟨f, hfF, hcase⟩ | ⟨k, hkB, hbk⟩
    · have hrlt := hSlt r hrS
      have hrodd := hSodd r hrS
      have hmod2 : (mS + 1 + (M - r)) % 2 = z % 2 :=
        Nat.ModEq.of_dvd (⟨M / 2, by omega⟩ : (2 : ℕ) ∣ M) hres
      have hMr : (M - r) % 2 = 1 := by omega
      omega
    · rcases hcase with ⟨hf0, _⟩ | ⟨hf0, heq⟩
      · exact absurd (hFodd f hfF) (by rw [hf0]; omega)
      · have := hFodd f hfF; omega
    · have := hBeven k hkB; omega
  refine ⟨(z - mS) / 2, ?_, ?_⟩
  · omega
  · omega

/-! ## The bulk landmark clause -/

section Clause
variable {Bh : ℕ}

/-- The selection/label embedding: the `D`-tuple `x`-block (low indices). -/
def embAddr : Fin (P.toPoly.arity c')
    → Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)) :=
  fun t => ⟨t.1, by have := t.2; omega⟩

/-- The `cfgPosFormulaL` address: slots `z, yF, yL` to `Kc', Kc'+1, Kc'+2`. -/
def cfgAddr : Fin 3 → Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3)) :=
  Fin.cons ⟨P.toPoly.arity c', by omega⟩
    (Fin.cons ⟨P.toPoly.arity c' + 1, by omega⟩
      (Fin.cons ⟨P.toPoly.arity c' + 2, by omega⟩ Fin.elim0))

/-- **The fibred bulk TIE-clause** (landmark route).  Free vars = the `arity c`
marks `ī`.  Binds (LOW) the `D`-coords, base `z`, and the landmarks `yF`/`yL`;
antecedent = per-coord `regionDecodeL` ∧ `firstD`/`lastU` pins ∧ `selDef` ∧
`labelDef D` ∧ `cfgPosFormulaL`; consequent = `ordDef` via `gordL`.  NO
constant depends on `mS` (D16). -/
noncomputable def clauseFormula (M mthr : ℕ)
    (S Front Back : (c'' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c'') → RegionSpec Bh) → Finset ℕ)
    (hS : ∀ c'' rs, ∀ r ∈ S c'' rs, r < M)
    (rs : Fin (P.toPoly.arity c') → RegionSpec Bh) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  faFOs (P.toPoly.arity c' + 3) (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        SliceFasGates.relabelFO (decAddr P c c' i) (regionDecodeL (rs i)))))
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
        (SliceFasGates.relabelFO (embAddr P c c') (P.toPoly.selDef c').choose)
      (MSO.Formula.and
        (SliceFasGates.relabelFO (embAddr P c c')
          (P.toPoly.labelDef c' D).choose)
        (SliceFasGates.relabelFO (cfgAddr P c c')
          (cfgPosFormulaL M mthr (S c' rs) (Front c' rs) (Back c' rs)
            (hS c' rs))))))))
    (SliceFasGates.relabelFO (gordL P c c') (P.toPoly.ordDef c c').choose))

/-- The selection embedding reads the `D`-tuple `xOfL pb`. -/
theorem comp_emb_cl (pb : Fin (P.toPoly.arity c' + 3) → ℕ)
    (ī : Fin (P.toPoly.arity c) → ℕ) :
    (appFO pb ī) ∘ (embAddr P c c') = xOfL pb := by
  funext t
  exact appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)

/-- The `cfgAddr` relabel reads `(z, yF, yL)`. -/
theorem comp_cfg (pb : Fin (P.toPoly.arity c' + 3) → ℕ)
    (ī : Fin (P.toPoly.arity c) → ℕ) :
    (appFO pb ī) ∘ (cfgAddr P c c')
      = Fin.cons (pb ⟨P.toPoly.arity c', by omega⟩)
          (Fin.cons (pb ⟨P.toPoly.arity c' + 1, by omega⟩)
            (Fin.cons (pb ⟨P.toPoly.arity c' + 2, by omega⟩) Fin.elim0)) := by
  funext s
  refine Fin.cases ?_ (fun s1 => Fin.cases ?_
    (fun s2 => Fin.cases ?_ (fun s3 => s3.elim0) s2) s1) s
  · show appFO pb ī ⟨P.toPoly.arity c', _⟩ = pb ⟨P.toPoly.arity c', _⟩
    exact appFO_low pb ī (P.toPoly.arity c') (by omega) (by omega)
  · show appFO pb ī ⟨P.toPoly.arity c' + 1, _⟩ = pb ⟨P.toPoly.arity c' + 1, _⟩
    exact appFO_low pb ī (P.toPoly.arity c' + 1) (by omega) (by omega)
  · show appFO pb ī ⟨P.toPoly.arity c' + 2, _⟩ = pb ⟨P.toPoly.arity c' + 2, _⟩
    exact appFO_low pb ī (P.toPoly.arity c' + 2) (by omega) (by omega)

/-- A landmark-pin relabel reads its single landmark slot. -/
theorem comp_const (q : ℕ) (hq : q < P.toPoly.arity c + (P.toPoly.arity c' + 3))
    (pb : Fin (P.toPoly.arity c' + 3) → ℕ) (ī : Fin (P.toPoly.arity c) → ℕ)
    (hlow : q < P.toPoly.arity c' + 3) :
    (appFO pb ī) ∘ (fun _ : Fin 1 =>
      (⟨q, hq⟩ : Fin (P.toPoly.arity c + (P.toPoly.arity c' + 3))))
      = (fun _ => pb ⟨q, hlow⟩) := by
  funext s
  exact appFO_low pb ī q hlow hq

/-- **The fibred bulk-clause characterization** (the F3.6 capstone).  The
landmark clause holds of the marked tuple `ī` exactly when every selected
`D`-atom in cell form (over `rs`) whose base passes the landmark position
clause is `ord`-above `ī`.  Forward instantiates the bound block at
`(xb, mS+2t, mS+1, mS+2(n−1))`; backward decodes the landmark pins
(`yF = mS+1`, `yL = mS+2(n−1)`) FIRST via `mso_firstD`/`mso_lastU`, then
`cfgPosL_base` pins the base to a middle U-block base, then `regionDecodeL_sat`
pins the cell tuple. -/
theorem clauseF_sat {Bh : ℕ} (M mthr : ℕ)
    (S Front Back : (c'' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c'') → RegionSpec Bh) → Finset ℕ)
    (hS : ∀ c'' rs, ∀ r ∈ S c'' rs, r < M)
    (rs : Fin (P.toPoly.arity c') → RegionSpec Bh)
    (mS n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hBn : Bh ≤ n) (hM2 : M % 2 = 0)
    (hSodd : ∀ r ∈ S c' rs, r % 2 = 1)
    (hFodd : ∀ f ∈ Front c' rs, f % 2 = 1)
    (hBeven : ∀ k ∈ Back c' rs, k % 2 = 0) :
    ((clauseFormula P c c' M mthr S Front Back hS rs).Sat (copiedSlice mS n) ī
        Fin.elim0 ↔
      ∀ (t : ℕ) (xb : Fin (P.toPoly.arity c') → ℕ),
        t < n →
        (∀ i, xb i < (copiedSlice mS n).length) →
        xb = (fun i => mS - 1 + (rs i).posAt t n) →
        P.toPoly.sel c' (copiedSlice mS n) xb →
        P.toPoly.label c' (copiedSlice mS n) xb = D →
        cfgPosL M mthr (S c' rs) (Front c' rs) (Back c' rs)
          (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
        P.toPoly.ord c c' (copiedSlice mS n) ī xb) := by
  have hlen : (copiedSlice mS n).length = 2 * (mS + n) := length_copiedSlice mS n
  rw [clauseFormula, sat_faFOs]
  constructor
  · -- raw → semantic: instantiate the bound block at (xb, mS+2t, mS+1, mS+2(n−1))
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
    have hpbx : xOfL pb = xb := by
      funext i
      show pb ⟨i.1, by have := i.2; omega⟩ = xb i
      rw [hpbdef]
      show (if h0 : i.1 < P.toPoly.arity c' then xb ⟨i.1, h0⟩
        else if i.1 < P.toPoly.arity c' + 1 then mS + 2 * t
        else if i.1 < P.toPoly.arity c' + 2 then mS + 1
        else mS + 2 * (n - 1)) = xb i
      rw [dif_pos i.2]
    have hval : ∀ j, pb j < (copiedSlice mS n).length := by
      intro j
      rw [hpbdef]
      simp only []
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
      · -- per-coord decode
        rw [MSOMarkN.sat_andList]
        intro ψ hψ
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hψ
        rw [SliceFasGates.sat_relabelFO, comp_decodeL, hpbz, hpbyF, hpbyL,
          show xOfL pb i = xb i from by rw [hpbx]]
        exact (regionDecodeL_sat (rs i) mS t n (xb i) hm hn hBn hz
          (by rw [← hlen]; exact hxbv i)).mpr (by rw [hcell])
      · -- firstD pin
        rw [SliceFasGates.sat_relabelFO,
          comp_const P c c' (P.toPoly.arity c' + 1) (by omega) pb ī (by omega),
          hpbyF]
        exact (CopiedLandmark.mso_firstD.choose_spec (copiedSlice mS n) (mS + 1)
            (by rw [hlen]; omega)).mpr
          ((firstD_copiedSlice mS n hm hn (mS + 1) (by omega)).mpr rfl)
      · -- lastU pin
        rw [SliceFasGates.sat_relabelFO,
          comp_const P c c' (P.toPoly.arity c' + 2) (by omega) pb ī (by omega),
          hpbyL]
        refine (CopiedLandmark.mso_lastU.choose_spec (copiedSlice mS n)
            (mS + 2 * (n - 1)) (by rw [hlen]; omega)).mpr ?_
        rw [hlen]
        exact (lastU_copiedSlice mS n hm hn (mS + 2 * (n - 1)) (by omega)).mpr rfl
      · -- selDef
        rw [SliceFasGates.sat_relabelFO, comp_emb_cl, hpbx]
        exact ((P.toPoly.selDef c').choose_spec (copiedSlice mS n) xb).mp hsel
      · -- labelDef
        rw [SliceFasGates.sat_relabelFO, comp_emb_cl, hpbx]
        exact ((P.toPoly.labelDef c' D).choose_spec (copiedSlice mS n) xb).mp hlab
      · -- the position-cell clause at the base
        rw [SliceFasGates.sat_relabelFO, comp_cfg, hpbz, hpbyF, hpbyL]
        exact (sat_cfgPosFormulaL M mthr (S c' rs) (Front c' rs) (Back c' rs)
          (hS c' rs) mS n (mS + 2 * t) hm hn (by omega)).mpr hcfg)
    rw [SliceFasGates.sat_relabelFO] at hord
    have hrel := ((P.toPoly.ordDef c c').choose_spec (copiedSlice mS n)
      ((appFO pb ī) ∘ gordL P c c')).mpr hord
    simp only [] at hrel
    rwa [(comp_gordL P c c' pb ī).1, (comp_gordL P c c' pb ī).2, hpbx] at hrel
  · -- semantic → raw: decode landmarks, pin parity+window, then the cell tuple
    intro h pb hpb
    rw [SliceFasGates.sat_imp]
    intro hant
    simp only [MSO.Formula.sat_and] at hant
    obtain ⟨hdec, hfirstD, hlastU, hselD, hlabD, hcfgF⟩ := hant
    -- the landmark pins
    rw [SliceFasGates.sat_relabelFO,
      comp_const P c c' (P.toPoly.arity c' + 1) (by omega) pb ī (by omega)]
      at hfirstD
    have hyFval : pb ⟨P.toPoly.arity c' + 1, by omega⟩ = mS + 1 :=
      (firstD_copiedSlice mS n hm hn (pb ⟨P.toPoly.arity c' + 1, by omega⟩)
          (by rw [← hlen]; exact hpb _)).mp
        ((CopiedLandmark.mso_firstD.choose_spec (copiedSlice mS n)
            (pb ⟨P.toPoly.arity c' + 1, by omega⟩) (hpb _)).mp hfirstD)
    rw [SliceFasGates.sat_relabelFO,
      comp_const P c c' (P.toPoly.arity c' + 2) (by omega) pb ī (by omega)]
      at hlastU
    have hyLval : pb ⟨P.toPoly.arity c' + 2, by omega⟩ = mS + 2 * (n - 1) := by
      refine (lastU_copiedSlice mS n hm hn (pb ⟨P.toPoly.arity c' + 2, by omega⟩)
          (by rw [← hlen]; exact hpb _)).mp ?_
      have hh := (CopiedLandmark.mso_lastU.choose_spec (copiedSlice mS n)
        (pb ⟨P.toPoly.arity c' + 2, by omega⟩) (hpb _)).mp hlastU
      rw [hlen] at hh
      exact hh
    -- the position clause at the base
    rw [SliceFasGates.sat_relabelFO, comp_cfg, hyFval, hyLval] at hcfgF
    have hcfgz := (sat_cfgPosFormulaL M mthr (S c' rs) (Front c' rs) (Back c' rs)
      (hS c' rs) mS n (pb ⟨P.toPoly.arity c', by omega⟩) hm hn
      (by rw [← hlen]; exact hpb _)).mp hcfgF
    -- the parity+window pinning
    obtain ⟨t, htz, htn⟩ := cfgPosL_base M mthr (S c' rs) (Front c' rs)
      (Back c' rs) mS n (pb ⟨P.toPoly.arity c', by omega⟩) hm hn hM2 (hS c' rs)
      hSodd hFodd hBeven hcfgz
    -- decode the cell tuple
    have hcell : xOfL pb = fun i => mS - 1 + (rs i).posAt t n := by
      funext i
      have hd := (MSOMarkN.sat_andList _ _ _ _).mp hdec _
        (List.mem_map_of_mem (List.mem_finRange i))
      rw [SliceFasGates.sat_relabelFO, comp_decodeL, hyFval, hyLval, htz] at hd
      exact (regionDecodeL_sat (rs i) mS t n (xOfL pb i) hm hn hBn htn
        (by rw [← hlen]; exact hpb _)).mp hd
    -- fire the semantic hypothesis
    have hrel := h t (xOfL pb) htn (fun i => hpb _) hcell
      (((P.toPoly.selDef c').choose_spec (copiedSlice mS n) (xOfL pb)).mpr (by
        rw [SliceFasGates.sat_relabelFO, comp_emb_cl] at hselD; exact hselD))
      (((P.toPoly.labelDef c' D).choose_spec (copiedSlice mS n) (xOfL pb)).mpr (by
        rw [SliceFasGates.sat_relabelFO, comp_emb_cl] at hlabD; exact hlabD))
      (by rw [← htz]; exact hcfgz)
    -- repackage via gordL
    rw [SliceFasGates.sat_relabelFO]
    refine ((P.toPoly.ordDef c c').choose_spec (copiedSlice mS n)
      ((appFO pb ī) ∘ gordL P c c')).mp ?_
    simp only []
    rw [(comp_gordL P c c' pb ī).1, (comp_gordL P c c' pb ī).2]
    exact hrel

/-- **The bulk landmark clause DFA** (one Büchi call per `(c, c', rs)`): the
marked DFA over the `arity c` `U`-marks realising `clauseFormula`.  A `def`
(not an `∃`) so its `bFN` is a definite function for the eventual-periodicity
of `clause_bFN_EP`. -/
noncomputable def clauseDFA (M mthr : ℕ)
    (S Front Back : (c'' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c'') → RegionSpec Bh) → Finset ℕ)
    (hS : ∀ c'' rs, ∀ r ∈ S c'' rs, r < M)
    (rs : Fin (P.toPoly.arity c') → RegionSpec Bh) :
    SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)) :=
  (MSOMarkN.markedDFAN_exists (P.toPoly.arity c)
    (clauseFormula P c c' M mthr S Front Back hS rs)).choose

end Clause

/-! ## The uniform clause/pair `bFN` eventual-periodicity -/

/-- **The uniform clause-machine periodicity** (`pG`, before `mS`): there is a
single threshold/period `(mG, pG)` at which the block map `bFN` of EVERY bulk
clause DFA (over all `c, c', rs`) AND every boundary pair component (over all
`c, c'`) is eventually periodic.  `pG` is the product of the finitely many
per-machine periods (each divides `pG`), `mG` the sup of the thresholds —
both machine-level, before any `mS`.  This is what lets the §9 count be EP in
`n` at a single period. -/
theorem clause_bFN_EP {Bh : ℕ} (P : WRP.Presentation Step Step) (M mthr : ℕ)
    (S Front Back : (c'' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c'') → RegionSpec Bh) → Finset ℕ)
    (hS : ∀ c'' rs, ∀ r ∈ S c'' rs, r < M) :
    ∃ mG pG : ℕ, 1 ≤ pG ∧
      (∀ (c c' : Fin P.toPoly.K)
          (rs : Fin (P.toPoly.arity c') → RegionSpec Bh) (g : ℕ), mG ≤ g →
        (bFN (clauseDFA P c c' M mthr S Front Back hS rs))^[g + pG]
          = (bFN (clauseDFA P c c' M mthr S Front Back hS rs))^[g]) ∧
      (∀ (c c' : Fin P.toPoly.K) (g : ℕ), mG ≤ g →
        (bFN (boundary_pair_component P c c').choose)^[g + pG]
          = (bFN (boundary_pair_component P c c').choose)^[g]) := by
  classical
  -- per-machine EP for the clause family (indexed by c, c', rs — a Fintype)
  choose mv1 pv1 hpv1 hEP1 using
    fun x : (c : Fin P.toPoly.K) × (c' : Fin P.toPoly.K) ×
        (Fin (P.toPoly.arity c') → RegionSpec Bh) =>
      SliceMarkN.bFN_func_iterate_eventuallyPeriodic
        (clauseDFA P x.1 x.2.1 M mthr S Front Back hS x.2.2)
  -- per-machine EP for the pair family (indexed by c, c')
  choose mv2 pv2 hpv2 hEP2 using
    fun x : Fin P.toPoly.K × Fin P.toPoly.K =>
      SliceMarkN.bFN_func_iterate_eventuallyPeriodic
        (boundary_pair_component P x.1 x.2).choose
  set pG : ℕ := (∏ x, pv1 x) * (∏ x, pv2 x) with hpGdef
  have hpos1 : 0 < ∏ x, pv1 x := Finset.prod_pos (fun x _ => hpv1 x)
  have hpos2 : 0 < ∏ x, pv2 x := Finset.prod_pos (fun x _ => hpv2 x)
  set mG : ℕ := Finset.univ.sup mv1 ⊔ Finset.univ.sup mv2 with hmGdef
  refine ⟨mG, pG, Nat.mul_pos hpos1 hpos2, ?_, ?_⟩
  · -- clause family at (mG, pG)
    intro c c' rs g hg
    set x : (c : Fin P.toPoly.K) × (c' : Fin P.toPoly.K) ×
        (Fin (P.toPoly.arity c') → RegionSpec Bh) := ⟨c, c', rs⟩ with hx
    obtain ⟨q, hq⟩ : pv1 x ∣ pG := by
      rw [hpGdef]
      exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ x)) _
    rw [hq, Nat.mul_comm]
    refine SliceGrowthCollapse.bFN_iterate_period_mul
      (clauseDFA P c c' M mthr S Front Back hS rs)
      (mv1 x) (pv1 x) (hEP1 x) q g ?_
    exact le_trans (le_trans (Finset.le_sup (Finset.mem_univ x))
      (le_max_left _ _)) hg
  · -- pair family at (mG, pG)
    intro c c' g hg
    obtain ⟨q, hq⟩ : pv2 (c, c') ∣ pG := by
      rw [hpGdef]
      exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) _
    rw [hq, Nat.mul_comm]
    refine SliceGrowthCollapse.bFN_iterate_period_mul
      (boundary_pair_component P c c').choose
      (mv2 (c, c')) (pv2 (c, c')) (hEP2 (c, c')) q g ?_
    exact le_trans (le_trans (Finset.le_sup (Finset.mem_univ ((c, c'))))
      (le_max_right _ _)) hg

/-! ## The sigma-marked bulk clause (Design B — mixed cells)

The core-only `clauseFormula` cannot express `atomOrd` against MIXED cells
(some coordinates on a middle cluster, others in the far prefix/suffix
stretches): the stretch coordinates carry unbounded positions that no
`RegionSpec Bh` descriptor (finite, needed for the `ClauseIdx` `Fintype`) can
hold.  The sigma-marked clause `clauseFormulaMk` MARKS the stretch coordinates
(the `sigma` slots, supplied at FIXED `t`-independent positions) and DECODES
only the non-`sigma` core coordinates via `regionDecodeL`.  The machine now
marks the combined `arity c + arity c'` tuple: the first `arity c` are the
`U`-atom marks, the next `arity c'` are the `D`-atom marks (only the `sigma`
ones matter; the rest are pinned to the decode and the marks ignored). -/

section ClauseMk
variable {Bh : ℕ}

/-- The `U`-atom part (first `arity c`) of the combined free marks. -/
def uOfMk (ī : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) :
    Fin (P.toPoly.arity c) → ℕ :=
  fun t => ī ⟨t.1, by have := t.2; omega⟩

/-- The `D`-atom mark part (next `arity c'`) of the combined free marks. -/
def dMarkMk (ī : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) :
    Fin (P.toPoly.arity c') → ℕ :=
  fun t => ī ⟨P.toPoly.arity c + t.1, by have := t.2; omega⟩

/-- Decode address (4 slots `z, x_i, yF, yL`) into the LOW bound block. -/
def decAddrMk (i : Fin (P.toPoly.arity c')) :
    Fin 4 → Fin (P.toPoly.arity c + P.toPoly.arity c' + (P.toPoly.arity c' + 3)) :=
  Fin.cons ⟨P.toPoly.arity c', by omega⟩
    (Fin.cons ⟨i.1, by have := i.2; omega⟩
      (Fin.cons ⟨P.toPoly.arity c' + 1, by omega⟩
        (Fin.cons ⟨P.toPoly.arity c' + 2, by omega⟩ Fin.elim0)))

/-- The sigma-equality address (2 slots): the bound `D`-coordinate `i` (LOW)
and its supplied `D`-mark (HIGH free, offset `arity c + i`). -/
def eqAddrMk (i : Fin (P.toPoly.arity c')) :
    Fin 2 → Fin (P.toPoly.arity c + P.toPoly.arity c' + (P.toPoly.arity c' + 3)) :=
  Fin.cons ⟨i.1, by have := i.2; omega⟩
    (Fin.cons ⟨P.toPoly.arity c' + 3 + (P.toPoly.arity c + i.1), by have := i.2; omega⟩
      Fin.elim0)

/-- The `ord` address: the `c`-atom to the HIGH `U`-marks, the `c'`-atom to the
LOW bound `D`-coordinates. -/
def gordLMk :
    Fin (P.toPoly.arity c + P.toPoly.arity c') →
    Fin (P.toPoly.arity c + P.toPoly.arity c' + (P.toPoly.arity c' + 3)) :=
  fun idx => if h : idx.1 < P.toPoly.arity c
    then ⟨P.toPoly.arity c' + 3 + idx.1, by omega⟩
    else ⟨idx.1 - P.toPoly.arity c, by have := idx.2; omega⟩

/-- The selection/label embedding: the LOW bound `D`-coordinate block. -/
def embAddrMk : Fin (P.toPoly.arity c')
    → Fin (P.toPoly.arity c + P.toPoly.arity c' + (P.toPoly.arity c' + 3)) :=
  fun t => ⟨t.1, by have := t.2; omega⟩

/-- The `cfgPosFormulaL` address: slots `z, yF, yL` to the LOW bound block. -/
def cfgAddrMk : Fin 3
    → Fin (P.toPoly.arity c + P.toPoly.arity c' + (P.toPoly.arity c' + 3)) :=
  Fin.cons ⟨P.toPoly.arity c', by omega⟩
    (Fin.cons ⟨P.toPoly.arity c' + 1, by omega⟩
      (Fin.cons ⟨P.toPoly.arity c' + 2, by omega⟩ Fin.elim0))

/-- The decode relabel reads `(z, x_i, yF, yL)`. -/
theorem comp_decodeLMk (pb : Fin (P.toPoly.arity c' + 3) → ℕ)
    (ī : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ)
    (i : Fin (P.toPoly.arity c')) :
    (appFO pb ī) ∘ (decAddrMk P c c' i)
      = Fin.cons (pb ⟨P.toPoly.arity c', by omega⟩)
          (Fin.cons (xOfL pb i)
            (Fin.cons (pb ⟨P.toPoly.arity c' + 1, by omega⟩)
              (Fin.cons (pb ⟨P.toPoly.arity c' + 2, by omega⟩) Fin.elim0))) := by
  funext s
  refine Fin.cases ?_ (fun s1 => Fin.cases ?_
    (fun s2 => Fin.cases ?_ (fun s3 => Fin.cases ?_ (fun s4 => s4.elim0) s3) s2)
    s1) s
  · show appFO pb ī ⟨P.toPoly.arity c', _⟩ = pb ⟨P.toPoly.arity c', _⟩
    exact appFO_low pb ī (P.toPoly.arity c') (by omega) (by omega)
  · show appFO pb ī ⟨i.1, _⟩ = xOfL pb i
    exact appFO_low pb ī i.1 (by have := i.2; omega) (by have := i.2; omega)
  · show appFO pb ī ⟨P.toPoly.arity c' + 1, _⟩ = pb ⟨P.toPoly.arity c' + 1, _⟩
    exact appFO_low pb ī (P.toPoly.arity c' + 1) (by omega) (by omega)
  · show appFO pb ī ⟨P.toPoly.arity c' + 2, _⟩ = pb ⟨P.toPoly.arity c' + 2, _⟩
    exact appFO_low pb ī (P.toPoly.arity c' + 2) (by omega) (by omega)

/-- The sigma-equality relabel reads `(bound-coord_i, D-mark_i)`. -/
theorem comp_eqMk (pb : Fin (P.toPoly.arity c' + 3) → ℕ)
    (ī : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ)
    (i : Fin (P.toPoly.arity c')) :
    (appFO pb ī) ∘ (eqAddrMk P c c' i)
      = Fin.cons (pb ⟨i.1, by have := i.2; omega⟩)
          (Fin.cons (dMarkMk P c c' ī i) Fin.elim0) := by
  funext s
  refine Fin.cases ?_ (fun s1 => Fin.cases ?_ (fun s2 => s2.elim0) s1) s
  · show appFO pb ī ⟨i.1, _⟩ = pb ⟨i.1, _⟩
    exact appFO_low pb ī i.1 (by have := i.2; omega) (by have := i.2; omega)
  · show appFO pb ī ⟨P.toPoly.arity c' + 3 + (P.toPoly.arity c + i.1), _⟩
      = dMarkMk P c c' ī i
    exact appFO_high pb ī (P.toPoly.arity c + i.1) (by have := i.2; omega)
      (by have := i.2; omega)

/-- The `gordLMk` relabel reads `(uOfMk ī, xOfL pb)`. -/
theorem comp_gordLMk (pb : Fin (P.toPoly.arity c' + 3) → ℕ)
    (ī : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) :
    ((fun t => ((appFO pb ī) ∘ gordLMk P c c')
        (Fin.castAdd (P.toPoly.arity c') t)) = uOfMk P c c' ī)
    ∧ ((fun t => ((appFO pb ī) ∘ gordLMk P c c')
        (Fin.natAdd (P.toPoly.arity c) t)) = xOfL pb) := by
  constructor
  · funext t
    show appFO pb ī (gordLMk P c c' (Fin.castAdd _ t)) = uOfMk P c c' ī t
    have hg : gordLMk P c c' (Fin.castAdd (P.toPoly.arity c') t)
        = ⟨P.toPoly.arity c' + 3 + t.1, by have := t.2; omega⟩ := by
      unfold gordLMk
      rw [dif_pos (show ((Fin.castAdd (P.toPoly.arity c') t) : ℕ)
        < P.toPoly.arity c from t.2)]
      rfl
    rw [hg]
    exact appFO_high pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)
  · funext t
    show appFO pb ī (gordLMk P c c' (Fin.natAdd _ t)) = xOfL pb t
    have hv : ((Fin.natAdd (P.toPoly.arity c) t) : ℕ)
        = P.toPoly.arity c + t.1 := rfl
    have hg : gordLMk P c c' (Fin.natAdd (P.toPoly.arity c) t)
        = ⟨t.1, by have := t.2; omega⟩ := by
      unfold gordLMk
      rw [dif_neg (show ¬(((Fin.natAdd (P.toPoly.arity c) t) : ℕ)
        < P.toPoly.arity c) from by omega)]
      congr 1
      omega
    rw [hg]
    exact appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)

/-- The selection embedding reads the bound `D`-tuple `xOfL pb`. -/
theorem comp_emb_clMk (pb : Fin (P.toPoly.arity c' + 3) → ℕ)
    (ī : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) :
    (appFO pb ī) ∘ (embAddrMk P c c') = xOfL pb := by
  funext t
  exact appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)

/-- The `cfgAddrMk` relabel reads `(z, yF, yL)`. -/
theorem comp_cfgMk (pb : Fin (P.toPoly.arity c' + 3) → ℕ)
    (ī : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) :
    (appFO pb ī) ∘ (cfgAddrMk P c c')
      = Fin.cons (pb ⟨P.toPoly.arity c', by omega⟩)
          (Fin.cons (pb ⟨P.toPoly.arity c' + 1, by omega⟩)
            (Fin.cons (pb ⟨P.toPoly.arity c' + 2, by omega⟩) Fin.elim0)) := by
  funext s
  refine Fin.cases ?_ (fun s1 => Fin.cases ?_
    (fun s2 => Fin.cases ?_ (fun s3 => s3.elim0) s2) s1) s
  · show appFO pb ī ⟨P.toPoly.arity c', _⟩ = pb ⟨P.toPoly.arity c', _⟩
    exact appFO_low pb ī (P.toPoly.arity c') (by omega) (by omega)
  · show appFO pb ī ⟨P.toPoly.arity c' + 1, _⟩ = pb ⟨P.toPoly.arity c' + 1, _⟩
    exact appFO_low pb ī (P.toPoly.arity c' + 1) (by omega) (by omega)
  · show appFO pb ī ⟨P.toPoly.arity c' + 2, _⟩ = pb ⟨P.toPoly.arity c' + 2, _⟩
    exact appFO_low pb ī (P.toPoly.arity c' + 2) (by omega) (by omega)

/-- A landmark-pin relabel reads its single LOW landmark slot. -/
theorem comp_constMk (q : ℕ)
    (hq : q < P.toPoly.arity c + P.toPoly.arity c' + (P.toPoly.arity c' + 3))
    (pb : Fin (P.toPoly.arity c' + 3) → ℕ)
    (ī : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ)
    (hlow : q < P.toPoly.arity c' + 3) :
    (appFO pb ī) ∘ (fun _ : Fin 1 =>
      (⟨q, hq⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c' + (P.toPoly.arity c' + 3))))
      = (fun _ => pb ⟨q, hlow⟩) := by
  funext s
  exact appFO_low pb ī q hlow hq

/-- **The fibred sigma-marked bulk TIE clause**.  Free vars = `arity c`
`U`-marks ++ `arity c'` `D`-marks.  Binds (LOW) the `D`-coordinates, base `z`,
landmarks `yF`/`yL`; antecedent = (for `i ∉ sigma`: `regionDecodeL` pins the
core coord; for `i ∈ sigma`: the bound coord EQUALS the supplied `D`-mark) ∧
`firstD`/`lastU` pins ∧ `selDef` ∧ `labelDef D` ∧ `cfgPosFormulaL`; consequent
= `ordDef` via `gordLMk`.  No constant depends on `mS` (D16): the stretch
positions enter only as runtime marks. -/
noncomputable def clauseFormulaMk (M mthr : ℕ) (Sv Fv Bv : Finset ℕ)
    (hS : ∀ r ∈ Sv, r < M)
    (rsB : Fin (P.toPoly.arity c') → RegionSpec Bh)
    (sigma : Finset (Fin (P.toPoly.arity c'))) :
    MSO.Formula Step (P.toPoly.arity c + P.toPoly.arity c') 0 :=
  faFOs (P.toPoly.arity c' + 3) (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        if i ∈ sigma then MSO.Formula.tru
        else SliceFasGates.relabelFO (decAddrMk P c c' i) (regionDecodeL (rsB i)))))
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

/-- **The fibred sigma-marked bulk-clause characterization** (the Design-B F3.6
capstone, mixed cells).  Mirrors `clauseF_sat`: the sigma-marked clause holds of
the combined `U`-marks ++ `D`-marks `ī` exactly when, for every base `t < n`, the
REASSEMBLED `D`-atom `xb` (sigma coords from the supplied `D`-marks `dMarkMk ī`,
core coords from the `rsB`-cell) that is selected/`D`-labelled and whose base
passes the landmark position clause is `ord`-above the `U`-atom `uOfMk ī`.
Forward instantiates the bound block at the reassembled `(xb, mS+2t, mS+1,
mS+2(n−1))`, discharging the sigma decode-`tru`s, the sigma-equalities (`pb_i =
dMarkMk ī i`), and the landmark/position conjuncts; backward decodes the landmark
pins, `cfgPosL_base` pins the middle base, then reassembles per-coord. -/
theorem clauseFMk_sat {Bh : ℕ} (M mthr : ℕ) (Sv Fv Bv : Finset ℕ)
    (hS : ∀ r ∈ Sv, r < M)
    (rsB : Fin (P.toPoly.arity c') → RegionSpec Bh)
    (sigma : Finset (Fin (P.toPoly.arity c')))
    (mS n : ℕ) (ī : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hBn : Bh ≤ n) (hM2 : M % 2 = 0)
    (hSodd : ∀ r ∈ Sv, r % 2 = 1)
    (hFodd : ∀ f ∈ Fv, f % 2 = 1)
    (hBeven : ∀ k ∈ Bv, k % 2 = 0)
    (hīv : ∀ i, ī i < (copiedSlice mS n).length) :
    ((clauseFormulaMk P c c' M mthr Sv Fv Bv hS rsB sigma).Sat (copiedSlice mS n) ī
        Fin.elim0 ↔
      ∀ (t : ℕ) (xb : Fin (P.toPoly.arity c') → ℕ),
        t < n →
        (∀ i, xb i < (copiedSlice mS n).length) →
        xb = (fun i => if i ∈ sigma then dMarkMk P c c' ī i
                       else mS - 1 + (rsB i).posAt t n) →
        P.toPoly.sel c' (copiedSlice mS n) xb →
        P.toPoly.label c' (copiedSlice mS n) xb = D →
        cfgPosL M mthr Sv Fv Bv (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
        P.toPoly.ord c c' (copiedSlice mS n) (uOfMk P c c' ī) xb) := by
  have hlen : (copiedSlice mS n).length = 2 * (mS + n) := length_copiedSlice mS n
  rw [clauseFormulaMk, sat_faFOs]
  constructor
  · -- raw → semantic: instantiate the bound block at the reassembled tuple
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
    have hpbx : xOfL pb = xb := by
      funext i
      show pb ⟨i.1, by have := i.2; omega⟩ = xb i
      rw [hpbdef]
      show (if h0 : i.1 < P.toPoly.arity c' then xb ⟨i.1, h0⟩
        else if i.1 < P.toPoly.arity c' + 1 then mS + 2 * t
        else if i.1 < P.toPoly.arity c' + 2 then mS + 1
        else mS + 2 * (n - 1)) = xb i
      rw [dif_pos i.2]
    have hval : ∀ j, pb j < (copiedSlice mS n).length := by
      intro j
      rw [hpbdef]
      simp only []
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
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- per-coord decode (`tru` for sigma coords)
        rw [MSOMarkN.sat_andList]
        intro ψ hψ
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hψ
        by_cases hi : i ∈ sigma
        · simp only [if_pos hi]
          exact (MSO.Formula.sat_tru _ _ _).mpr ⟨⟩
        · simp only [if_neg hi]
          rw [SliceFasGates.sat_relabelFO, comp_decodeLMk, hpbz, hpbyF, hpbyL,
            show xOfL pb i = xb i from by rw [hpbx]]
          refine (regionDecodeL_sat (rsB i) mS t n (xb i) hm hn hBn hz
            (by rw [← hlen]; exact hxbv i)).mpr ?_
          simp only [hcell, if_neg hi]
      · -- the sigma-equalities (bound coord = supplied D-mark)
        rw [MSOMarkN.sat_andList]
        intro ψ hψ
        obtain ⟨i, hi_mem, rfl⟩ := List.mem_map.mp hψ
        have hi : i ∈ sigma := Finset.mem_toList.mp hi_mem
        rw [SliceFasGates.sat_relabelFO, comp_eqMk]
        refine ((SliceFasGates.mso_offset_eq (Alpha := Step) 0).choose_spec
          (copiedSlice mS n) (pb ⟨i.1, by have := i.2; omega⟩) (dMarkMk P c c' ī i)
          (hval _) (hīv _)).mpr ?_
        have h1 : pb ⟨i.1, by have := i.2; omega⟩ = xb i := by
          show xOfL pb i = xb i; rw [hpbx]
        have hxbeq : xb i = dMarkMk P c c' ī i := by simp only [hcell, if_pos hi]
        rw [Nat.add_zero, h1, hxbeq]
      · -- firstD pin
        rw [SliceFasGates.sat_relabelFO,
          comp_constMk P c c' (P.toPoly.arity c' + 1) (by omega) pb ī (by omega),
          hpbyF]
        exact (CopiedLandmark.mso_firstD.choose_spec (copiedSlice mS n) (mS + 1)
            (by rw [hlen]; omega)).mpr
          ((firstD_copiedSlice mS n hm hn (mS + 1) (by omega)).mpr rfl)
      · -- lastU pin
        rw [SliceFasGates.sat_relabelFO,
          comp_constMk P c c' (P.toPoly.arity c' + 2) (by omega) pb ī (by omega),
          hpbyL]
        refine (CopiedLandmark.mso_lastU.choose_spec (copiedSlice mS n)
            (mS + 2 * (n - 1)) (by rw [hlen]; omega)).mpr ?_
        rw [hlen]
        exact (lastU_copiedSlice mS n hm hn (mS + 2 * (n - 1)) (by omega)).mpr rfl
      · -- selDef
        rw [SliceFasGates.sat_relabelFO, comp_emb_clMk, hpbx]
        exact ((P.toPoly.selDef c').choose_spec (copiedSlice mS n) xb).mp hsel
      · -- labelDef
        rw [SliceFasGates.sat_relabelFO, comp_emb_clMk, hpbx]
        exact ((P.toPoly.labelDef c' D).choose_spec (copiedSlice mS n) xb).mp hlab
      · -- the position-cell clause at the base
        rw [SliceFasGates.sat_relabelFO, comp_cfgMk, hpbz, hpbyF, hpbyL]
        exact (sat_cfgPosFormulaL M mthr Sv Fv Bv hS mS n (mS + 2 * t) hm hn
          (by omega)).mpr hcfg)
    rw [SliceFasGates.sat_relabelFO] at hord
    have hrel := ((P.toPoly.ordDef c c').choose_spec (copiedSlice mS n)
      ((appFO pb ī) ∘ gordLMk P c c')).mpr hord
    simp only [] at hrel
    rwa [(comp_gordLMk P c c' pb ī).1, (comp_gordLMk P c c' pb ī).2, hpbx] at hrel
  · -- semantic → raw: decode landmarks, pin parity+window, reassemble cell tuple
    intro h pb hpb
    rw [SliceFasGates.sat_imp]
    intro hant
    simp only [MSO.Formula.sat_and] at hant
    obtain ⟨hdec, hsigeq, hfirstD, hlastU, hselD, hlabD, hcfgF⟩ := hant
    -- the landmark pins
    rw [SliceFasGates.sat_relabelFO,
      comp_constMk P c c' (P.toPoly.arity c' + 1) (by omega) pb ī (by omega)]
      at hfirstD
    have hyFval : pb ⟨P.toPoly.arity c' + 1, by omega⟩ = mS + 1 :=
      (firstD_copiedSlice mS n hm hn (pb ⟨P.toPoly.arity c' + 1, by omega⟩)
          (by rw [← hlen]; exact hpb _)).mp
        ((CopiedLandmark.mso_firstD.choose_spec (copiedSlice mS n)
            (pb ⟨P.toPoly.arity c' + 1, by omega⟩) (hpb _)).mp hfirstD)
    rw [SliceFasGates.sat_relabelFO,
      comp_constMk P c c' (P.toPoly.arity c' + 2) (by omega) pb ī (by omega)]
      at hlastU
    have hyLval : pb ⟨P.toPoly.arity c' + 2, by omega⟩ = mS + 2 * (n - 1) := by
      refine (lastU_copiedSlice mS n hm hn (pb ⟨P.toPoly.arity c' + 2, by omega⟩)
          (by rw [← hlen]; exact hpb _)).mp ?_
      have hh := (CopiedLandmark.mso_lastU.choose_spec (copiedSlice mS n)
        (pb ⟨P.toPoly.arity c' + 2, by omega⟩) (hpb _)).mp hlastU
      rw [hlen] at hh
      exact hh
    -- the position clause at the base
    rw [SliceFasGates.sat_relabelFO, comp_cfgMk, hyFval, hyLval] at hcfgF
    have hcfgz := (sat_cfgPosFormulaL M mthr Sv Fv Bv hS mS n
      (pb ⟨P.toPoly.arity c', by omega⟩) hm hn
      (by rw [← hlen]; exact hpb _)).mp hcfgF
    -- the parity+window pinning
    obtain ⟨t, htz, htn⟩ := cfgPosL_base M mthr Sv Fv Bv mS n
      (pb ⟨P.toPoly.arity c', by omega⟩) hm hn hM2 hS hSodd hFodd hBeven hcfgz
    -- reassemble the cell tuple
    have hcell : xOfL pb = fun i => if i ∈ sigma then dMarkMk P c c' ī i
        else mS - 1 + (rsB i).posAt t n := by
      funext i
      by_cases hi : i ∈ sigma
      · simp only [if_pos hi]
        have hq := (MSOMarkN.sat_andList _ _ _ _).mp hsigeq _
          (List.mem_map_of_mem (Finset.mem_toList.mpr hi))
        rw [SliceFasGates.sat_relabelFO, comp_eqMk] at hq
        have hpieq := ((SliceFasGates.mso_offset_eq (Alpha := Step) 0).choose_spec
          (copiedSlice mS n) (pb ⟨i.1, by have := i.2; omega⟩) (dMarkMk P c c' ī i)
          (hpb _) (hīv _)).mp hq
        show pb ⟨i.1, by have := i.2; omega⟩ = dMarkMk P c c' ī i
        omega
      · simp only [if_neg hi]
        have hd := (MSOMarkN.sat_andList _ _ _ _).mp hdec _
          (List.mem_map_of_mem (List.mem_finRange i))
        rw [if_neg hi, SliceFasGates.sat_relabelFO, comp_decodeLMk, hyFval, hyLval,
          htz] at hd
        exact (regionDecodeL_sat (rsB i) mS t n (xOfL pb i) hm hn hBn htn
          (by rw [← hlen]; exact hpb _)).mp hd
    -- fire the semantic hypothesis
    have hrel := h t (xOfL pb) htn (fun i => hpb _) hcell
      (((P.toPoly.selDef c').choose_spec (copiedSlice mS n) (xOfL pb)).mpr (by
        rw [SliceFasGates.sat_relabelFO, comp_emb_clMk] at hselD; exact hselD))
      (((P.toPoly.labelDef c' D).choose_spec (copiedSlice mS n) (xOfL pb)).mpr (by
        rw [SliceFasGates.sat_relabelFO, comp_emb_clMk] at hlabD; exact hlabD))
      (by rw [← htz]; exact hcfgz)
    -- repackage via gordLMk (rewrite the hypothesis — searching for the atoms
    -- `uOfMk ī`/`xOfL pb` is cheap, unlike an expensive lambda-pattern goal rewrite)
    rw [SliceFasGates.sat_relabelFO]
    rw [← (comp_gordLMk P c c' pb ī).1, ← (comp_gordLMk P c c' pb ī).2] at hrel
    exact ((P.toPoly.ordDef c c').choose_spec (copiedSlice mS n)
      ((appFO pb ī) ∘ gordLMk P c c')).mp hrel

/-- **The sigma-marked clause DFA** (one `markedDFAN_exists` per data tuple):
the marked DFA over the combined `arity c + arity c'` marks realising
`clauseFormulaMk`.  A `def` so its `bFN` is a definite function. -/
noncomputable def clauseDFAMk (M mthr : ℕ) (Sv Fv Bv : Finset ℕ)
    (hS : ∀ r ∈ Sv, r < M)
    (rsB : Fin (P.toPoly.arity c') → RegionSpec Bh)
    (sigma : Finset (Fin (P.toPoly.arity c'))) :
    SliceMSO.DetAuto (MarkedN (P.toPoly.arity c + P.toPoly.arity c')) :=
  (MSOMarkN.markedDFAN_exists (P.toPoly.arity c + P.toPoly.arity c')
    (clauseFormulaMk P c c' M mthr Sv Fv Bv hS rsB sigma)).choose

/-- The Mk clause DFA accepts exactly when `clauseFormulaMk` is satisfied. -/
theorem clauseDFAMk_spec (M mthr : ℕ) (Sv Fv Bv : Finset ℕ)
    (hS : ∀ r ∈ Sv, r < M)
    (rsB : Fin (P.toPoly.arity c') → RegionSpec Bh)
    (sigma : Finset (Fin (P.toPoly.arity c')))
    (w : List Step) (ī : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ)
    (hī : ∀ i, ī i < w.length) :
    (clauseDFAMk P c c' M mthr Sv Fv Bv hS rsB sigma).accepts (markAtN _ w ī)
      ↔ (clauseFormulaMk P c c' M mthr Sv Fv Bv hS rsB sigma).Sat w ī Fin.elim0 :=
  (MSOMarkN.markedDFAN_exists (P.toPoly.arity c + P.toPoly.arity c')
    (clauseFormulaMk P c c' M mthr Sv Fv Bv hS rsB sigma)).choose_spec w ī hī

/-- **The Mk clause-DFA characterization AT the copied word** (`clauseDFAMk_spec ∘
clauseFMk_sat`): acceptance of the Mk clause DFA on the marked copied slice is
the sigma-marked equal-rank TIE semantics. -/
theorem clauseFMk_accepts (M mthr : ℕ) (Sv Fv Bv : Finset ℕ)
    (hS : ∀ r ∈ Sv, r < M)
    (rsB : Fin (P.toPoly.arity c') → RegionSpec Bh)
    (sigma : Finset (Fin (P.toPoly.arity c')))
    (mS n : ℕ) (ī : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hBn : Bh ≤ n) (hM2 : M % 2 = 0)
    (hSodd : ∀ r ∈ Sv, r % 2 = 1) (hFodd : ∀ f ∈ Fv, f % 2 = 1)
    (hBeven : ∀ k ∈ Bv, k % 2 = 0)
    (hīv : ∀ i, ī i < (copiedSlice mS n).length) :
    (clauseDFAMk P c c' M mthr Sv Fv Bv hS rsB sigma).accepts
        (markAtN _ (copiedSlice mS n) ī) ↔
      ∀ (t : ℕ) (xb : Fin (P.toPoly.arity c') → ℕ),
        t < n →
        (∀ i, xb i < (copiedSlice mS n).length) →
        xb = (fun i => if i ∈ sigma then dMarkMk P c c' ī i
                       else mS - 1 + (rsB i).posAt t n) →
        P.toPoly.sel c' (copiedSlice mS n) xb →
        P.toPoly.label c' (copiedSlice mS n) xb = D →
        cfgPosL M mthr Sv Fv Bv (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) →
        P.toPoly.ord c c' (copiedSlice mS n) (uOfMk P c c' ī) xb := by
  rw [clauseDFAMk_spec P c c' M mthr Sv Fv Bv hS rsB sigma (copiedSlice mS n) ī hīv,
    clauseFMk_sat P c c' M mthr Sv Fv Bv hS rsB sigma mS n ī hm hn hBn hM2
      hSodd hFodd hBeven hīv]

end ClauseMk

end CopiedTieGate
