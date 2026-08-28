/-
# The general-arity TIE gate, layer 1 (GA-6.2a/b/e/f)

The GA-6 build (design: `GA6_DESIGN.json`) mirrors the arity-1
`fasU_atomOrd_cfg_gate` with cells replacing positions.  This file lands the
foundation:

* `faFOs` / `appFO` / `sat_faFOs` — THE new generic MSO primitive: the iterated
  universal first-order binder over the LOW de Bruijn block, keeping the `ka` mark
  variables free at the HIGH indices (arity 1 needed a single `faFO` and never built
  this).  `appFO pb ī` is the composite valuation: index `i < kb` reads the bound
  block (`0` = innermost binder), index `kb + t` reads the marks.
* `appFO_low` / `appFO_high` — the two index-evaluation lemmas every relabelling
  composition in the clause Sat-proofs rewrites through.
* `clusterFreeTuple` / `cfgCellGA` — the semantic premise: the quantified `b`-atom in
  cell form, with the landed arity-1 `cfgPos` REUSED VERBATIM at the base position
  `1 + 2t`.
* `selectedU_gate_GA` — the `U`-twin of `exists_selDDFA` (GA-7's STRICT count needs it).
* `gord` — the address map sending `ordDef`'s two variable blocks to the marks (HIGH)
  and the bound tuple (LOW).

Axiom-clean except the DFA layer (+`SliceMSO.buchi`).
-/
import RequestProject.SliceDstarGateGA

namespace SliceFasGatesGA

open WRP Step SliceFamilyCell SliceDstarGA SliceDstarGateGA MSOMarkN
open scoped Classical

/-! ## GA-6.2a: the iterated low-block binder -/

/-- Iterated universal first-order quantification over the LOW `kb` de Bruijn
indices, keeping the `ka` mark variables free at the HIGH indices. -/
def faFOs {Alpha : Type*} {ka ns : ℕ} : (kb : ℕ) →
    MSO.Formula Alpha (ka + kb) ns → MSO.Formula Alpha ka ns
  | 0, φ => φ
  | (kb + 1), φ => faFOs kb (MSO.Formula.faFO φ)

/-- The composite valuation: the bound block at the low indices (`0` = innermost
binder), the marks at the high indices. -/
def appFO {ka kb : ℕ} (pb : Fin kb → ℕ) (ī : Fin ka → ℕ) : Fin (ka + kb) → ℕ :=
  fun idx => if h : idx.1 < kb then pb ⟨idx.1, h⟩
    else ī ⟨idx.1 - kb, by have := idx.2; omega⟩

theorem appFO_low {ka kb : ℕ} (pb : Fin kb → ℕ) (ī : Fin ka → ℕ)
    (i : ℕ) (h : i < kb) (h' : i < ka + kb) :
    appFO pb ī ⟨i, h'⟩ = pb ⟨i, h⟩ := by
  unfold appFO
  exact dif_pos h

theorem appFO_high {ka kb : ℕ} (pb : Fin kb → ℕ) (ī : Fin ka → ℕ)
    (t : ℕ) (h : t < ka) (h' : kb + t < ka + kb) :
    appFO pb ī ⟨kb + t, h'⟩ = ī ⟨t, h⟩ := by
  unfold appFO
  rw [dif_neg (show ¬(kb + t < kb) by omega)]
  congr 1
  exact Fin.ext (show kb + t - kb = t by omega)

/-- The cons-equation: peeling the innermost bound variable. -/
theorem appFO_succ {ka kb : ℕ} (pb : Fin (kb + 1) → ℕ) (ī : Fin ka → ℕ) :
    appFO pb ī = Fin.cons (α := fun _ => ℕ) (pb 0) (appFO (pb ∘ Fin.succ) ī) := by
  funext idx
  refine Fin.cases ?_ (fun j => ?_) idx
  · rw [Fin.cons_zero]
    unfold appFO
    rw [dif_pos (show ((0 : Fin (ka + (kb + 1))) : ℕ) < kb + 1 from by
      rw [Fin.val_zero]; omega)]
    congr 1
  · rw [Fin.cons_succ]
    unfold appFO
    by_cases hj : (j : ℕ) < kb
    · rw [dif_pos (show ((Fin.succ j : Fin (ka + (kb + 1))) : ℕ) < kb + 1 from by
        rw [Fin.val_succ]; omega), dif_pos hj]
      show pb _ = pb (Fin.succ ⟨(j : ℕ), hj⟩)
      congr 1
    · rw [dif_neg (show ¬((Fin.succ j : Fin (ka + (kb + 1))) : ℕ) < kb + 1 from by
        rw [Fin.val_succ]; omega), dif_neg hj]
      congr 1
      refine Fin.ext ?_
      show ((Fin.succ j : Fin (ka + (kb + 1))) : ℕ) - (kb + 1) = (j : ℕ) - kb
      have hv := Fin.val_succ j
      omega

/-- **Satisfaction of the iterated binder**: the bound block ranges over all valid
tuples, evaluated through the composite valuation. -/
theorem sat_faFOs {Alpha : Type*} (w : List Alpha) {ka ns : ℕ} (ī : Fin ka → ℕ)
    (σ : Fin ns → Finset ℕ) : ∀ (kb : ℕ) (φ : MSO.Formula Alpha (ka + kb) ns),
    (faFOs kb φ).Sat w ī σ ↔
      ∀ pb : Fin kb → ℕ, (∀ t, pb t < w.length) → φ.Sat w (appFO pb ī) σ := by
  intro kb
  induction kb with
  | zero =>
      intro φ
      have hid : ∀ pb : Fin 0 → ℕ, appFO pb ī = ī := by
        intro pb
        funext idx
        unfold appFO
        rw [dif_neg (by omega)]
        congr 1
      constructor
      · intro h pb _
        rw [hid pb]
        exact h
      · intro h
        have := h Fin.elim0 (fun t => t.elim0)
        rwa [hid Fin.elim0] at this
  | succ kb ih =>
      intro φ
      show (faFOs kb (MSO.Formula.faFO φ)).Sat w ī σ ↔ _
      rw [ih (MSO.Formula.faFO φ)]
      constructor
      · intro h pb hpb
        have hstep := h (pb ∘ Fin.succ) (fun t => hpb t.succ)
        rw [SliceFasGates.sat_faFO] at hstep
        have := hstep (pb 0) (hpb 0)
        rwa [← appFO_succ] at this
      · intro h pb hpb
        rw [SliceFasGates.sat_faFO]
        intro q hq
        have hq' := h (Fin.cons q pb) (fun t => by
          refine Fin.cases ?_ ?_ t
          · simpa using hq
          · intro j
            simpa using hpb j)
        rwa [appFO_succ, Fin.cons_zero,
          show (Fin.cons q pb : Fin (kb + 1) → ℕ) ∘ Fin.succ = pb from
            funext (fun j => Fin.cons_succ _ _ j)] at hq'

/-! ## GA-6.2b: the semantic premise -/

/-- A descriptor tuple is cluster-free when no coordinate rides the window. -/
def clusterFreeTuple {B k : ℕ} (rs : Fin k → RegionSpec B) : Prop :=
  ∀ i, clusterFree (rs i)

/-- **One arm of the GA cell premise**: the atom `b` is in cell form over descriptors
at bound `D`, with the landed arity-1 `cfgPos` evaluated at the base position `1+2t`. -/
def cfgCellArm {P : WRP.Presentation Step Step} (D M mthr : ℕ)
    (S Front Back : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpec D) → Finset ℕ)
    (n : ℕ) (b : P.toPoly.Atom) : Prop :=
  ∃ (rs : Fin (P.toPoly.arity b.1) → RegionSpec D) (t : ℕ),
    1 + 2 * t < (wrappedFlat n).length ∧
    b.2 = cellTuple rs t n ∧
    SliceFasGates.cfgPos M mthr (S b.1 rs) (Front b.1 rs) (Back b.1 rs)
      (wrappedFlat n).length (1 + 2 * t)

/-- **The GA cell premise** (the frozen interface, GA-6.0): the two-layer disjunction —
the bulk arm over descriptors at bound `B`, the frozen arm at the enlarged `Bh`. -/
def cfgCellGA {P : WRP.Presentation Step Step} (B Bh M mthr : ℕ)
    (S₁ F₁ K₁ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpec B) → Finset ℕ)
    (S₂ F₂ K₂ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpec Bh) → Finset ℕ)
    (n : ℕ) (b : P.toPoly.Atom) : Prop :=
  cfgCellArm B M mthr S₁ F₁ K₁ n b ∨ cfgCellArm Bh M mthr S₂ F₂ K₂ n b

/-! ## GA-6.2e: the selected-`U` recogniser -/

/-- The `U`-twin of `exists_selDDFA` (consumed by GA-7's STRICT count). -/
theorem selectedU_gate_GA (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    ∃ M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = U)) := by
  obtain ⟨φs, hφs⟩ := P.toPoly.selDef c
  obtain ⟨φl, hφl⟩ := P.toPoly.labelDef c U
  obtain ⟨M, hM⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c) (MSO.Formula.and φs φl)
  refine ⟨M, fun w ī hval => ?_⟩
  rw [hM w ī hval, MSO.Formula.sat_and, ← hφs w ī, ← hφl w ī]

/-! ## GA-6.2f: the `ordDef` address map -/

/-- The address map for the binary order formula inside the clause: `ordDef`'s
first block (the `a`-atom) goes to the marks at the HIGH indices, its second block
(the `b`-atom) to the bound tuple at the LOW indices. -/
def gord (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) :
    Fin (P.toPoly.arity c + P.toPoly.arity c') →
    Fin (P.toPoly.arity c + (P.toPoly.arity c' + 1)) :=
  fun idx => if h : idx.1 < P.toPoly.arity c
    then ⟨P.toPoly.arity c' + 1 + idx.1, by omega⟩
    else ⟨idx.1 - P.toPoly.arity c, by have := idx.2; omega⟩

/-! ## GA-6.2c: the per-coordinate decode against the bound base -/

/-- The per-coordinate decode with free variable `0` the base position `z = 1 + 2t`
and free variable `1` the coordinate `x`: pinned regions ignore `z` (constant or
from-end positions), cluster regions read `x = z + 2δ + e` via the offset primitive. -/
noncomputable def regionDecodeOff {B : ℕ} : RegionSpec B → MSO.Formula Step 2 0
  | .pre => SliceFasGates.relabelFO (fun _ : Fin 1 => 1)
      (SliceFasGates.mso_position_eq (Alpha := Step) 0).choose
  | .suf => SliceFasGates.relabelFO (fun _ : Fin 1 => 1)
      (SliceFasGates.mso_position_fromEnd (Alpha := Step) 0).choose
  | .front f e => SliceFasGates.relabelFO (fun _ : Fin 1 => 1)
      (SliceFasGates.mso_position_eq (Alpha := Step) (1 + 2 * f.1 + e.toNat)).choose
  | .back l e => SliceFasGates.relabelFO (fun _ : Fin 1 => 1)
      (SliceFasGates.mso_position_fromEnd (Alpha := Step) (2 * l.1 + 2 - e.toNat)).choose
  | .cluster δ e => (SliceFasGates.mso_offset_eq (Alpha := Step) (2 * δ.1 + e.toNat)).choose

/-- **The decode pins the coordinate**: at base `z = 1 + 2t`, the decode of region `r`
holds of `x` exactly when `x` is the position `r` describes at base `t`. -/
theorem regionDecodeOff_sat {B : ℕ} (r : RegionSpec B) (n t x : ℕ)
    (hz : 1 + 2 * t < (wrappedFlat n).length) (hx : x < (wrappedFlat n).length)
    (hBn : B ≤ n) :
    ((regionDecodeOff r).Sat (wrappedFlat n)
        (Fin.cons (1 + 2 * t) (Fin.cons x Fin.elim0)) Fin.elim0 ↔ x = r.posAt t n) := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
  · show (SliceFasGates.relabelFO _ _).Sat _ _ _ ↔ _
    rw [SliceFasGates.sat_relabelFO]
    exact ((SliceFasGates.mso_position_eq (Alpha := Step) 0).choose_spec
      (wrappedFlat n) x hx).trans (by simp only [RegionSpec.posAt])
  · show (SliceFasGates.relabelFO _ _).Sat _ _ _ ↔ _
    rw [SliceFasGates.sat_relabelFO]
    refine ((SliceFasGates.mso_position_fromEnd (Alpha := Step) 0).choose_spec
      (wrappedFlat n) x hx).trans ?_
    rw [length_wrappedFlat]
    simp only [RegionSpec.posAt]
    omega
  · show (SliceFasGates.relabelFO _ _).Sat _ _ _ ↔ _
    rw [SliceFasGates.sat_relabelFO]
    exact ((SliceFasGates.mso_position_eq (Alpha := Step)
      (1 + 2 * f.1 + e.toNat)).choose_spec (wrappedFlat n) x hx).trans
      (by simp only [RegionSpec.posAt])
  · show (SliceFasGates.relabelFO _ _).Sat _ _ _ ↔ _
    rw [SliceFasGates.sat_relabelFO]
    refine ((SliceFasGates.mso_position_fromEnd (Alpha := Step)
      (2 * l.1 + 2 - e.toNat)).choose_spec (wrappedFlat n) x hx).trans ?_
    rw [length_wrappedFlat]
    simp only [RegionSpec.posAt]
    have := l.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · refine ((SliceFasGates.mso_offset_eq (Alpha := Step)
      (2 * δ.1 + e.toNat)).choose_spec (wrappedFlat n) (1 + 2 * t) x hz hx).trans ?_
    simp only [RegionSpec.posAt]
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      constructor <;> intro h <;> omega


/-! ## GA-6.2d: the position-cell clause as a standalone formula -/

/-- The three-way position-cell clause as a single-FO-variable formula: the standalone
extraction of the arity-1 gate's inline `posClause` (`fasU_atomOrd_cfg_gate`). -/
noncomputable def cfgPosFormula (M mthr : ℕ) (S Front Back : Finset ℕ)
    (hS : ∀ r ∈ S, r < M) : MSO.Formula Step 1 0 :=
  MSO.Formula.or
    (MSO.Formula.and
      (MSO.Formula.neg (SliceFasGates.bigOr ((List.range mthr).map (fun k =>
        (SliceFasGates.mso_position_eq (Alpha := Step) k).choose))))
      (MSO.Formula.and
        (MSO.Formula.neg (SliceFasGates.bigOr ((List.range mthr).map (fun k =>
          (SliceFasGates.mso_position_fromEnd (Alpha := Step) k).choose))))
        (SliceFasGates.bigOr (S.toList.attach.map (fun rr =>
          (SliceFasGates.mso_position_mod (Alpha := Step) M rr.1
            (hS rr.1 (Finset.mem_toList.mp rr.2))).choose)))))
    (MSO.Formula.or
      (SliceFasGates.bigOr (Front.toList.map (fun k =>
        (SliceFasGates.mso_position_eq (Alpha := Step) k).choose)))
      (SliceFasGates.bigOr (Back.toList.map (fun k =>
        (SliceFasGates.mso_position_fromEnd (Alpha := Step) k).choose))))

/-- **The clause decodes to `cfgPos`** (transcription of the arity-1 `hposSat`). -/
theorem sat_cfgPosFormula (M mthr : ℕ) (S Front Back : Finset ℕ)
    (hS : ∀ r ∈ S, r < M) (w : List Step) (p : ℕ) (hp : p < w.length) :
    ((cfgPosFormula M mthr S Front Back hS).Sat w (fun _ => p) Fin.elim0 ↔
      SliceFasGates.cfgPos M mthr S Front Back w.length p) := by
  rw [cfgPosFormula]
  have h1 : ((SliceFasGates.bigOr ((List.range mthr).map (fun k =>
        (SliceFasGates.mso_position_eq (Alpha := Step) k).choose))).Sat w
        (fun _ => p) Fin.elim0) ↔ p < mthr := by
    rw [SliceFasGates.sat_bigOr]
    constructor
    · rintro ⟨φ', hφ', hsat⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hφ'
      rw [List.mem_range] at hi
      rw [(SliceFasGates.mso_position_eq (Alpha := Step) i).choose_spec w p hp] at hsat
      omega
    · intro hlt
      exact ⟨_, List.mem_map_of_mem (List.mem_range.mpr hlt),
        ((SliceFasGates.mso_position_eq (Alpha := Step) p).choose_spec w p hp).mpr rfl⟩
  have h2 : ((SliceFasGates.bigOr ((List.range mthr).map (fun k =>
        (SliceFasGates.mso_position_fromEnd (Alpha := Step) k).choose))).Sat w
        (fun _ => p) Fin.elim0) ↔ w.length ≤ p + mthr := by
    rw [SliceFasGates.sat_bigOr]
    constructor
    · rintro ⟨φ', hφ', hsat⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hφ'
      rw [List.mem_range] at hi
      rw [(SliceFasGates.mso_position_fromEnd (Alpha := Step) i).choose_spec w p hp]
        at hsat
      omega
    · intro hle
      refine ⟨_, List.mem_map_of_mem (List.mem_range.mpr
        (show w.length - p - 1 < mthr by omega)), ?_⟩
      exact ((SliceFasGates.mso_position_fromEnd (Alpha := Step)
        (w.length - p - 1)).choose_spec w p hp).mpr (by omega)
  have h3 : ((SliceFasGates.bigOr (S.toList.attach.map (fun rr =>
        (SliceFasGates.mso_position_mod (Alpha := Step) M rr.1
          (hS rr.1 (Finset.mem_toList.mp rr.2))).choose))).Sat w
        (fun _ => p) Fin.elim0) ↔ p % M ∈ S := by
    rw [SliceFasGates.sat_bigOr]
    constructor
    · rintro ⟨φ', hφ', hsat⟩
      obtain ⟨rr, _, rfl⟩ := List.mem_map.mp hφ'
      have := ((SliceFasGates.mso_position_mod (Alpha := Step) M rr.1
        (hS rr.1 (Finset.mem_toList.mp rr.2))).choose_spec w p hp).mp hsat
      rw [this]
      exact Finset.mem_toList.mp rr.2
    · intro hmem
      refine ⟨_, List.mem_map.mpr ⟨⟨p % M, Finset.mem_toList.mpr hmem⟩,
        List.mem_attach _ _, rfl⟩, ?_⟩
      exact ((SliceFasGates.mso_position_mod (Alpha := Step) M (p % M)
        (hS (p % M) hmem)).choose_spec w p hp).mpr rfl
  have h4 : ((SliceFasGates.bigOr (Front.toList.map (fun k =>
        (SliceFasGates.mso_position_eq (Alpha := Step) k).choose))).Sat w
        (fun _ => p) Fin.elim0) ↔ p ∈ Front := by
    rw [SliceFasGates.sat_bigOr]
    constructor
    · rintro ⟨φ', hφ', hsat⟩
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hφ'
      rw [((SliceFasGates.mso_position_eq (Alpha := Step) f).choose_spec w p hp).mp hsat]
      exact Finset.mem_toList.mp hf
    · intro hmem
      exact ⟨_, List.mem_map_of_mem (Finset.mem_toList.mpr hmem),
        ((SliceFasGates.mso_position_eq (Alpha := Step) p).choose_spec w p hp).mpr rfl⟩
  have h5 : ((SliceFasGates.bigOr (Back.toList.map (fun k =>
        (SliceFasGates.mso_position_fromEnd (Alpha := Step) k).choose))).Sat w
        (fun _ => p) Fin.elim0) ↔ ∃ k ∈ Back, p + 1 + k = w.length := by
    rw [SliceFasGates.sat_bigOr]
    constructor
    · rintro ⟨φ', hφ', hsat⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ'
      exact ⟨k, Finset.mem_toList.mp hk,
        ((SliceFasGates.mso_position_fromEnd (Alpha := Step) k).choose_spec
          w p hp).mp hsat⟩
    · rintro ⟨k, hk, heq⟩
      exact ⟨_, List.mem_map_of_mem (Finset.mem_toList.mpr hk),
        ((SliceFasGates.mso_position_fromEnd (Alpha := Step) k).choose_spec
          w p hp).mpr heq⟩
  simp only [MSO.Formula.sat_or, MSO.Formula.sat_and, MSO.Formula.sat_neg]
  rw [h1, h2, h3, h4, h5, SliceFasGates.cfgPos]
  constructor
  · rintro (⟨ha, hb, hc⟩ | h)
    · exact Or.inl ⟨by omega, by omega, hc⟩
    · exact Or.inr h
  · rintro (⟨ha, hb, hc⟩ | h)
    · exact Or.inl ⟨by omega, by omega, hc⟩
    · exact Or.inr h


/-! ## GA-6.2g: the per-(copy, descriptor) clause -/

/-- **The cell clause**: for every bound `b`-tuple `xb` and base `z` (the `arity c' + 1`
bound variables; `z` at index `arity c'`, `x_i` at index `i`), if the decodes pin
`xb` to the cell at `z = 1+2t`, the atom is selected with label `D`, and the base
passes the position-cell clause, then the marked `a`-atom `ordDef`-precedes it. -/
noncomputable def cellClause (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    {B : ℕ} (M mthr : ℕ)
    (S Front Back : (c'' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c'') → RegionSpec B) → Finset ℕ)
    (hS : ∀ c'' rs, ∀ r ∈ S c'' rs, r < M)
    (rs : Fin (P.toPoly.arity c') → RegionSpec B) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  faFOs (P.toPoly.arity c' + 1) (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        SliceFasGates.relabelFO
          (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 1)))
            ⟨P.toPoly.arity c', by omega⟩
            (Fin.cons (α := fun _ => Fin (P.toPoly.arity c + (P.toPoly.arity c' + 1)))
              ⟨i.1, by have := i.2; omega⟩ Fin.elim0))
          (regionDecodeOff (rs i)))))
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + (P.toPoly.arity c' + 1))))
          (P.toPoly.selDef c').choose)
        (MSO.Formula.and
          (SliceFasGates.relabelFO
            (fun t : Fin (P.toPoly.arity c') =>
              (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + (P.toPoly.arity c' + 1))))
            (P.toPoly.labelDef c' D).choose)
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 =>
              (⟨P.toPoly.arity c', by omega⟩ : Fin (P.toPoly.arity c + (P.toPoly.arity c' + 1))))
            (cfgPosFormula M mthr (S c' rs) (Front c' rs) (Back c' rs) (hS c' rs))))))
    (SliceFasGates.relabelFO (gord P c c') (P.toPoly.ordDef c c').choose))

section CellClauseSat

variable (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)

/-- The low-block restriction: the bound `xb` read out of `pb`. -/
def xOf {kb : ℕ} (pb : Fin (kb + 1) → ℕ) : Fin kb → ℕ :=
  fun i => pb ⟨i.1, by have := i.2; omega⟩

/-- Composition: the decode relabel reads `(z, x_i)`. -/
theorem comp_decode {ka kb : ℕ} (pb : Fin (kb + 1) → ℕ) (ī : Fin ka → ℕ) (i : Fin kb) :
    (appFO pb ī) ∘ (Fin.cons (α := fun _ => Fin (ka + (kb + 1)))
        (⟨kb, by omega⟩ : Fin (ka + (kb + 1)))
        (Fin.cons (α := fun _ => Fin (ka + (kb + 1)))
          (⟨i.1, by have := i.2; omega⟩ : Fin (ka + (kb + 1))) Fin.elim0))
      = Fin.cons (α := fun _ => ℕ) (pb ⟨kb, by omega⟩)
          (Fin.cons (α := fun _ => ℕ) (xOf pb i) Fin.elim0) := by
  funext j
  refine Fin.cases ?_ (fun j' => ?_) j
  · show appFO pb ī ⟨kb, by omega⟩ = pb ⟨kb, by omega⟩
    exact appFO_low pb ī kb (by omega) (by omega)
  · refine Fin.cases ?_ (fun j'' => j''.elim0) j'
    show appFO pb ī ⟨i.1, _⟩ = xOf pb i
    exact appFO_low pb ī i.1 (by have := i.2; omega) (by have := i.2; omega)

/-- Composition: the low-block embedding reads `xb`. -/
theorem comp_emb {ka kb : ℕ} (pb : Fin (kb + 1) → ℕ) (ī : Fin ka → ℕ) :
    (appFO pb ī) ∘ (fun t : Fin kb =>
        (⟨t.1, by have := t.2; omega⟩ : Fin (ka + (kb + 1))))
      = xOf pb := by
  funext t
  exact appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)

/-- Composition: the `gord` relabel reads `(ī, xb)` in `ordDef`'s block convention. -/
theorem comp_gord (pb : Fin (P.toPoly.arity c' + 1) → ℕ)
    (ī : Fin (P.toPoly.arity c) → ℕ) :
    ((fun t => ((appFO pb ī) ∘ gord P c c') (Fin.castAdd (P.toPoly.arity c') t)) = ī)
    ∧ ((fun t => ((appFO pb ī) ∘ gord P c c') (Fin.natAdd (P.toPoly.arity c) t))
        = xOf pb) := by
  constructor
  · funext t
    show appFO pb ī (gord P c c' (Fin.castAdd _ t)) = ī t
    have hg : gord P c c' (Fin.castAdd (P.toPoly.arity c') t)
        = ⟨P.toPoly.arity c' + 1 + t.1, by have := t.2; omega⟩ := by
      unfold gord
      rw [dif_pos (show ((Fin.castAdd (P.toPoly.arity c') t) : ℕ) < P.toPoly.arity c
        from t.2)]
      rfl
    rw [hg, appFO_high pb ī t.1 t.2 (by have := t.2; omega)]
  · funext t
    show appFO pb ī (gord P c c' (Fin.natAdd _ t)) = xOf pb t
    have hg : gord P c c' (Fin.natAdd (P.toPoly.arity c) t)
        = ⟨t.1, by have := t.2; omega⟩ := by
      unfold gord
      rw [dif_neg (show ¬(((Fin.natAdd (P.toPoly.arity c) t) : ℕ) < P.toPoly.arity c)
        from by
          have hv : ((Fin.natAdd (P.toPoly.arity c) t) : ℕ) = P.toPoly.arity c + t.1 :=
            rfl
          omega)]
      congr 1
      show ((Fin.natAdd (P.toPoly.arity c) t) : ℕ) - P.toPoly.arity c = (t : ℕ)
      have hv : ((Fin.natAdd (P.toPoly.arity c) t) : ℕ) = P.toPoly.arity c + t.1 := rfl
      omega
    rw [hg]
    exact appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)

/-- **The clause characterization**: the cell clause holds of the marked tuple exactly
when every selected `D`-atom in cell form (over `rs`) whose base passes the position
clause is `ord`-above it.  The bound base ranges over ALL valid positions in the raw
satisfaction; the hygiene hypotheses (even `M`, odd residues, odd fronts, even
end-offsets) force every passing base to be odd, which is what pins `z = 1 + 2t`. -/
theorem cellClause_sat {B : ℕ} (M mthr : ℕ)
    (S Front Back : (c'' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c'') → RegionSpec B) → Finset ℕ)
    (hS : ∀ c'' rs, ∀ r ∈ S c'' rs, r < M)
    (rs : Fin (P.toPoly.arity c') → RegionSpec B)
    (n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ) (hBn : B ≤ n)
    (hM2 : M % 2 = 0)
    (hSodd : ∀ r ∈ S c' rs, r % 2 = 1)
    (hFodd : ∀ f ∈ Front c' rs, f % 2 = 1)
    (hBeven : ∀ k ∈ Back c' rs, k % 2 = 0) :
    ((cellClause P c c' M mthr S Front Back hS rs).Sat (wrappedFlat n) ī Fin.elim0 ↔
      ∀ (t : ℕ) (xb : Fin (P.toPoly.arity c') → ℕ),
        1 + 2 * t < (wrappedFlat n).length →
        (∀ i, xb i < (wrappedFlat n).length) →
        xb = cellTuple rs t n →
        P.toPoly.sel c' (wrappedFlat n) xb →
        P.toPoly.label c' (wrappedFlat n) xb = D →
        SliceFasGates.cfgPos M mthr (S c' rs) (Front c' rs) (Back c' rs)
          (wrappedFlat n).length (1 + 2 * t) →
        P.toPoly.ord c c' (wrappedFlat n) ī xb) := by
  rw [cellClause, sat_faFOs]
  constructor
  · -- raw satisfaction → semantic form: instantiate the bound tuple at (xb, 1+2t)
    intro h t xb hz hxbv hcell hsel hlab hcfg
    set pb : Fin (P.toPoly.arity c' + 1) → ℕ := fun j =>
      if hj : j.1 < P.toPoly.arity c' then xb ⟨j.1, hj⟩ else 1 + 2 * t with hpbdef
    have hpbz : pb ⟨P.toPoly.arity c', by omega⟩ = 1 + 2 * t := by
      rw [hpbdef]
      exact dif_neg (show ¬(P.toPoly.arity c' < P.toPoly.arity c') by omega)
    have hpbx : xOf pb = xb := by
      funext i
      show pb ⟨i.1, by have := i.2; omega⟩ = xb i
      rw [hpbdef]
      show (if hj : i.1 < P.toPoly.arity c' then xb ⟨i.1, hj⟩ else 1 + 2 * t) = xb i
      rw [dif_pos i.2]
    have hval : ∀ j, pb j < (wrappedFlat n).length := by
      intro j
      rw [hpbdef]
      simp only []
      by_cases hj : j.1 < P.toPoly.arity c'
      · rw [dif_pos hj]
        exact hxbv _
      · rw [dif_neg hj]
        exact hz
    have hsat := h pb hval
    rw [SliceFasGates.sat_imp] at hsat
    have hord := hsat (by
      rw [MSO.Formula.sat_and]
      constructor
      · -- the decodes
        rw [MSOMarkN.sat_andList]
        intro ψ hψ
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hψ
        rw [SliceFasGates.sat_relabelFO, comp_decode, hpbz, hpbx]
        exact (regionDecodeOff_sat (rs i) n t (xb i) hz (hxbv i) hBn).mpr
          (by rw [hcell]; rfl)
      rw [MSO.Formula.sat_and]
      constructor
      · -- selection
        rw [SliceFasGates.sat_relabelFO, comp_emb, hpbx]
        exact ((P.toPoly.selDef c').choose_spec (wrappedFlat n) xb).mp hsel
      rw [MSO.Formula.sat_and]
      constructor
      · -- the D label
        rw [SliceFasGates.sat_relabelFO, comp_emb, hpbx]
        exact ((P.toPoly.labelDef c' D).choose_spec (wrappedFlat n) xb).mp hlab
      · -- the position-cell clause at the base
        rw [SliceFasGates.sat_relabelFO,
          show (appFO pb ī) ∘ (fun _ : Fin 1 =>
              (⟨P.toPoly.arity c', by omega⟩ :
                Fin (P.toPoly.arity c + (P.toPoly.arity c' + 1))))
            = fun _ => pb ⟨P.toPoly.arity c', by omega⟩ from
            funext (fun _ => appFO_low pb ī (P.toPoly.arity c') (by omega) (by omega)),
          hpbz]
        exact (sat_cfgPosFormula M mthr (S c' rs) (Front c' rs) (Back c' rs) (hS c' rs)
          (wrappedFlat n) (1 + 2 * t) hz).mpr hcfg)
    rw [SliceFasGates.sat_relabelFO] at hord
    have hrel := ((P.toPoly.ordDef c c').choose_spec (wrappedFlat n)
      ((appFO pb ī) ∘ gord P c c')).mpr hord
    simp only [] at hrel
    rwa [(comp_gord P c c' pb ī).1, (comp_gord P c c' pb ī).2, hpbx] at hrel
  · -- semantic form → raw satisfaction: hygiene forces the bound base odd
    intro h pb hpb
    rw [SliceFasGates.sat_imp]
    intro hprem
    rw [MSO.Formula.sat_and] at hprem
    obtain ⟨hdec, hprem⟩ := hprem
    rw [MSO.Formula.sat_and] at hprem
    obtain ⟨hselD, hprem⟩ := hprem
    rw [MSO.Formula.sat_and] at hprem
    obtain ⟨hlabD, hcfgF⟩ := hprem
    set z : ℕ := pb ⟨P.toPoly.arity c', by omega⟩ with hzdef
    have hzlen : z < (wrappedFlat n).length := hpb _
    -- decode the position clause at the base
    rw [SliceFasGates.sat_relabelFO,
      show (appFO pb ī) ∘ (fun _ : Fin 1 =>
          (⟨P.toPoly.arity c', by omega⟩ :
            Fin (P.toPoly.arity c + (P.toPoly.arity c' + 1))))
        = fun _ => pb ⟨P.toPoly.arity c', by omega⟩ from
        funext (fun _ => appFO_low pb ī (P.toPoly.arity c') (by omega) (by omega))]
      at hcfgF
    have hcfgz := (sat_cfgPosFormula M mthr (S c' rs) (Front c' rs) (Back c' rs)
      (hS c' rs) (wrappedFlat n) z hzlen).mp hcfgF
    -- hygiene: the base is odd
    have hzodd : z % 2 = 1 := by
      rcases hcfgz with ⟨_, _, hmod⟩ | hf | ⟨k, hk, hke⟩
      · have hr := hSodd _ hmod
        have hM0 : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) (hS c' rs _ hmod)
        have hdm := Nat.div_add_mod z M
        obtain ⟨M2, hM2'⟩ : ∃ M2, M = 2 * M2 := ⟨M / 2, by omega⟩
        have h2 : M * (z / M) = 2 * (M2 * (z / M)) := by
          rw [hM2']
          ring
        omega
      · exact hFodd _ hf
      · have hk2 := hBeven _ hk
        rw [length_wrappedFlat] at hke
        omega
    obtain ⟨t, ht⟩ : ∃ t, z = 1 + 2 * t :=
      ⟨z / 2, by have := Nat.div_add_mod z 2; omega⟩
    -- the decodes pin the bound tuple to the cell
    have hcell : xOf pb = cellTuple rs t n := by
      funext i
      have hd := (MSOMarkN.sat_andList _ _ _ _).mp hdec _
        (List.mem_map_of_mem (List.mem_finRange i))
      rw [SliceFasGates.sat_relabelFO, comp_decode] at hd
      have := (regionDecodeOff_sat (rs i) n t (xOf pb i) (by rw [← ht]; exact hzlen)
        (hpb _) hBn).mp (by rwa [← hzdef, ht] at hd)
      exact this
    -- fire the semantic hypothesis
    have hrel := h t (xOf pb) (by rw [← ht]; exact hzlen) (fun i => hpb _) hcell
      (((P.toPoly.selDef c').choose_spec (wrappedFlat n) (xOf pb)).mpr (by
        rw [SliceFasGates.sat_relabelFO, comp_emb] at hselD
        exact hselD))
      (((P.toPoly.labelDef c' D).choose_spec (wrappedFlat n) (xOf pb)).mpr (by
        rw [SliceFasGates.sat_relabelFO, comp_emb] at hlabD
        exact hlabD))
      (by rwa [← ht])
    -- repackage as the relabelled order formula
    rw [SliceFasGates.sat_relabelFO]
    refine ((P.toPoly.ordDef c c').choose_spec (wrappedFlat n)
      ((appFO pb ī) ∘ gord P c c')).mp ?_
    simp only []
    rw [(comp_gord P c c' pb ī).1, (comp_gord P c c' pb ī).2]
    exact hrel

end CellClauseSat



/-! ## GA-6.2h: the gate -/

/-- **The general-arity TIE gate** (the cell mirror of `fasU_atomOrd_cfg_gate`),
POSITION-UNIFORM in the marked tuple: the atom of copy `c` at ANY valid tuple `ī` is
selected, labelled `U`, and `atomOrd`-precedes every selected `D`-atom in cell form
whose base passes the position-cell clause — the two-layer premise covers the bulk
(bound `B`) and frozen (bound `Bh`) descriptor layers.  The hygiene hypotheses (even
`M`, odd residues, odd fronts, even end-offsets) are what make the bound bases
decodable.  A faithful MSO-gate→DFA; that the selector's data captures exactly the
equal-rank `D`-atoms is the GA-6.3/6.4 assembly's job, not asserted here. -/
theorem fasU_atomOrd_cellCfg_gate (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (B Bh M mthr : ℕ)
    (S₁ F₁ K₁ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpec B) → Finset ℕ)
    (S₂ F₂ K₂ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpec Bh) → Finset ℕ)
    (hBB : B ≤ Bh) (hM2 : M % 2 = 0)
    (hS₁ : ∀ c' rs, ∀ r ∈ S₁ c' rs, r < M ∧ r % 2 = 1)
    (hS₂ : ∀ c' rs, ∀ r ∈ S₂ c' rs, r < M ∧ r % 2 = 1)
    (hF₁ : ∀ c' rs, ∀ f ∈ F₁ c' rs, f % 2 = 1)
    (hF₂ : ∀ c' rs, ∀ f ∈ F₂ c' rs, f % 2 = 1)
    (hK₁ : ∀ c' rs, ∀ k ∈ K₁ c' rs, k % 2 = 0)
    (hK₂ : ∀ c' rs, ∀ k ∈ K₂ c' rs, k % 2 = 0) :
    ∃ Mdfa : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ), Bh ≤ n →
        (∀ i, ī i < (wrappedFlat n).length) →
        ((P.toPoly.sel c (wrappedFlat n) ī
          ∧ P.toPoly.label c (wrappedFlat n) ī = U
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
              P.toPoly.labelOf (wrappedFlat n) b = D →
              cfgCellGA B Bh M mthr S₁ F₁ K₁ S₂ F₂ K₂ n b →
              P.toPoly.atomOrd (wrappedFlat n) ⟨c, ī⟩ b)
         ↔ Mdfa.accepts (markAtN (P.toPoly.arity c) (wrappedFlat n) ī)) := by
  obtain ⟨Mdfa, hM⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c)
    (MSO.Formula.and (P.toPoly.selDef c).choose
      (MSO.Formula.and (P.toPoly.labelDef c U).choose
        (MSO.Formula.and
          (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
            (regionTuples B (P.toPoly.arity c')).map
              (cellClause P c c' M mthr S₁ F₁ K₁ (fun c'' rs r hr =>
                (hS₁ c'' rs r hr).1)))))
          (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
            (regionTuples Bh (P.toPoly.arity c')).map
              (cellClause P c c' M mthr S₂ F₂ K₂ (fun c'' rs r hr =>
                (hS₂ c'' rs r hr).1))))))))
  refine ⟨Mdfa, fun n ī hBhn hval => ?_⟩
  have hBn : B ≤ n := le_trans hBB hBhn
  rw [hM (wrappedFlat n) ī hval, MSO.Formula.sat_and, MSO.Formula.sat_and,
    MSO.Formula.sat_and]
  constructor
  · rintro ⟨hsel, hlab, hord⟩
    refine ⟨((P.toPoly.selDef c).choose_spec (wrappedFlat n) ī).mp hsel,
      ((P.toPoly.labelDef c U).choose_spec (wrappedFlat n) ī).mp hlab, ?_, ?_⟩
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨rs, _, rfl⟩ := hψ
      rw [cellClause_sat P c c' M mthr S₁ F₁ K₁ _ rs n ī hBn hM2
        (fun r hr => (hS₁ c' rs r hr).2) (hF₁ c' rs) (hK₁ c' rs)]
      intro t xb hz hxv hcell hsel' hlab' hcfg
      exact hord ⟨c', xb⟩ ⟨hxv, hsel'⟩ hlab' (Or.inl ⟨rs, t, hz, hcell, hcfg⟩)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨rs, _, rfl⟩ := hψ
      rw [cellClause_sat P c c' M mthr S₂ F₂ K₂ _ rs n ī hBhn hM2
        (fun r hr => (hS₂ c' rs r hr).2) (hF₂ c' rs) (hK₂ c' rs)]
      intro t xb hz hxv hcell hsel' hlab' hcfg
      exact hord ⟨c', xb⟩ ⟨hxv, hsel'⟩ hlab' (Or.inr ⟨rs, t, hz, hcell, hcfg⟩)
  · rintro ⟨hsel, hlab, hord₁, hord₂⟩
    refine ⟨((P.toPoly.selDef c).choose_spec (wrappedFlat n) ī).mpr hsel,
      ((P.toPoly.labelDef c U).choose_spec (wrappedFlat n) ī).mpr hlab, ?_⟩
    rintro ⟨c', xb⟩ hbsel hbD (⟨rs, t, hz, hbcell, hbcfg⟩ | ⟨rs, t, hz, hbcell, hbcfg⟩)
    · rw [MSOMarkN.sat_andList] at hord₁
      have hclause := hord₁ (cellClause P c c' M mthr S₁ F₁ K₁
          (fun c'' rs' r hr => (hS₁ c'' rs' r hr).1) rs)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (mem_regionTuples B _ rs)⟩)
      rw [cellClause_sat P c c' M mthr S₁ F₁ K₁ _ rs n ī hBn hM2
        (fun r hr => (hS₁ c' rs r hr).2) (hF₁ c' rs) (hK₁ c' rs)] at hclause
      exact hclause t xb hz hbsel.1 hbcell hbsel.2 hbD hbcfg
    · rw [MSOMarkN.sat_andList] at hord₂
      have hclause := hord₂ (cellClause P c c' M mthr S₂ F₂ K₂
          (fun c'' rs' r hr => (hS₂ c'' rs' r hr).1) rs)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (mem_regionTuples Bh _ rs)⟩)
      rw [cellClause_sat P c c' M mthr S₂ F₂ K₂ _ rs n ī hBhn hM2
        (fun r hr => (hS₂ c' rs r hr).2) (hF₂ c' rs) (hK₂ c' rs)] at hclause
      exact hclause t xb hz hbsel.1 hbcell hbsel.2 hbD hbcfg

end SliceFasGatesGA
