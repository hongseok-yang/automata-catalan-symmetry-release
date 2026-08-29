/-
# The landmark layer (§9 tower, Stage F3.5)

The bulk TIE-gate clauses of F3.6 must mention positions like the window
start `mS − 1` — but no formula constant may depend on `mS` (D16: an
`mS`-dependent constant means a per-`mS` δ means an `mS`-dependent `bFN`
period).  The fix: LANDMARKS.  On the copied slice the first `D` sits at
`mS + 1` and the last `U` at `mS + 2(n−1)`, both MSO-definable with
machine-level formulas; every decoded position is then a FIXED offset from a
landmark or the bound base, so the `mS`-shift is carried entirely by the
landmark VALUATIONS (semantic), never by the formula syntax.

The dictionary (spike S2):
  `firstD = mS + 1`, `lastU = mS + 2(n−1)`, window start `mS − 1 = firstD − 2`;
  `pre ↦ x + 2 = yF`; `front f e ↦ x = yF + (2f+e−1)` (or `yF = x + 1` at
  `f = 0, e = false`); `suf ↦ x = yL + 2`; `back l e ↦ x + 2l = yL + e`
  (cased on the sign); `cluster δ e ↦ x = z + 2δ + e` (base-relative,
  landmark-free).
-/
import RequestProject.CopiedGates
import RequestProject.SliceFasGates

namespace CopiedLandmark

open Step MSO CopiedRank SliceFasGates SliceFamilyCell

/-! ## Letter facts for the landmark evaluations -/

/-- Prefix-stretch letters (positions `< mS`) are `U`. -/
theorem copiedSlice_getElem?_pref (mS n q : ℕ) (hm : 1 ≤ mS) (hq : q < mS) :
    (copiedSlice mS n)[q]? = some U := by
  have htake := CopiedRank.copiedSlice_take_U mS (q + 1) n hm (by omega)
  have h1 : (copiedSlice mS n)[q]? = ((copiedSlice mS n).take (q + 1))[q]? :=
    (List.getElem?_take_of_lt (by omega)).symm
  rw [h1, htake,
    List.getElem?_eq_getElem (by rw [List.length_replicate]; omega),
    List.getElem_replicate]

/-- Every position strictly after the last `U` is `D`. -/
theorem copiedSlice_getElem?_after_lastU (mS n y : ℕ) (hm : 1 ≤ mS)
    (hn : 1 ≤ n) (hy1 : mS + 2 * (n - 1) < y) (hy2 : y < 2 * (mS + n)) :
    (copiedSlice mS n)[y]? = some D := by
  rcases Nat.lt_trichotomy y (mS + 2 * n) with hlt | heq | hgt
  · -- y = mS + 2(n−1) + 1 = block (n−1)'s D
    have hy : y = mS + 2 * (n - 1) + 1 := by omega
    have h := CopiedRank.copiedSlice_getElem?_blockD mS (n - 1) n hm (by omega)
    rw [show mS + 2 * (n - 1) + 1 = y from hy.symm] at h
    exact h
  · rw [heq]
    exact CopiedRank.copiedSlice_getElem?_sufD mS n hm
  · -- the suffix stretch
    have h := CopiedRank.copiedSlice_getElem?_tail mS (y - (mS + 2 * n + 1)) n
      hm (by omega)
    rw [show mS + 2 * n + 1 + (y - (mS + 2 * n + 1)) = y from by omega] at h
    exact h

/-! ## The landmark formulas -/

/-- **The first-`D` landmark formula**: `y` carries `D` and everything before
it carries `U`. -/
theorem mso_firstD : ∃ φ : MSO.Formula Step 1 0,
    ∀ (w : List Step) (y : ℕ), y < w.length →
      (φ.Sat w (fun _ => y) Fin.elim0 ↔
        (w[y]? = some D ∧ ∀ q, q < y → w[q]? = some U)) := by
  refine ⟨.and (.labelEq 0 D)
    (Formula.faFO (.or (.neg (.lt 0 1)) (.labelEq 0 U))), fun w y hy => ?_⟩
  rw [Formula.sat_and, Formula.sat_labelEq, Formula.faFO, Formula.sat_neg,
    Formula.sat_exFO]
  refine and_congr Iff.rfl ?_
  constructor
  · intro hno q hq
    by_contra hcon
    refine hno ⟨q, by omega, ?_⟩
    rw [Formula.sat_neg, Formula.sat_or, Formula.sat_neg, Formula.sat_lt,
      Formula.sat_labelEq]
    push Not
    refine ⟨?_, ?_⟩
    · simp only [Fin.cons_zero, Fin.cons_one]
      exact hq
    · simp only [Fin.cons_zero]
      exact hcon
  · rintro hall ⟨q, hqw, hq⟩
    rw [Formula.sat_neg, Formula.sat_or, Formula.sat_neg, Formula.sat_lt,
      Formula.sat_labelEq] at hq
    push Not at hq
    obtain ⟨hq1, hq2⟩ := hq
    simp only [Fin.cons_zero, Fin.cons_one] at hq1 hq2
    exact hq2 (hall q hq1)

/-- **The last-`U` landmark formula**: `y` carries `U` and everything after
it carries `D`. -/
theorem mso_lastU : ∃ φ : MSO.Formula Step 1 0,
    ∀ (w : List Step) (y : ℕ), y < w.length →
      (φ.Sat w (fun _ => y) Fin.elim0 ↔
        (w[y]? = some U ∧ ∀ q, y < q → q < w.length → w[q]? = some D)) := by
  refine ⟨.and (.labelEq 0 U)
    (Formula.faFO (.or (.neg (.lt 1 0)) (.labelEq 0 D))), fun w y hy => ?_⟩
  rw [Formula.sat_and, Formula.sat_labelEq, Formula.faFO, Formula.sat_neg,
    Formula.sat_exFO]
  refine and_congr Iff.rfl ?_
  constructor
  · intro hno q hq hqw
    by_contra hcon
    refine hno ⟨q, hqw, ?_⟩
    rw [Formula.sat_neg, Formula.sat_or, Formula.sat_neg, Formula.sat_lt,
      Formula.sat_labelEq]
    push Not
    refine ⟨?_, ?_⟩
    · simp only [Fin.cons_zero, Fin.cons_one]
      exact hq
    · simp only [Fin.cons_zero]
      exact hcon
  · rintro hall ⟨q, hqw, hq⟩
    rw [Formula.sat_neg, Formula.sat_or, Formula.sat_neg, Formula.sat_lt,
      Formula.sat_labelEq] at hq
    push Not at hq
    obtain ⟨hq1, hq2⟩ := hq
    simp only [Fin.cons_zero, Fin.cons_one] at hq1 hq2
    exact hq2 (hall q hq1 hqw)

/-! ## The landmark evaluations on the copied slice -/

/-- `firstD(copiedSlice mS n) = mS + 1` (uniquely). -/
theorem firstD_copiedSlice (mS n : ℕ) (hm : 1 ≤ mS) (hn : 1 ≤ n) (y : ℕ)
    (hy : y < 2 * (mS + n)) :
    ((copiedSlice mS n)[y]? = some D ∧
      ∀ q, q < y → (copiedSlice mS n)[q]? = some U) ↔ y = mS + 1 := by
  constructor
  · rintro ⟨hD, hall⟩
    rcases Nat.lt_trichotomy y (mS + 1) with hlt | heq | hgt
    · -- positions ≤ mS are U
      exfalso
      rcases Nat.lt_or_ge y mS with hy' | hy'
      · rw [copiedSlice_getElem?_pref mS n y hm hy'] at hD
        exact absurd hD (by simp)
      · have hyy : y = mS := by omega
        have h := CopiedRank.copiedSlice_getElem?_blockU mS 0 n hm (by omega)
        rw [show mS + 2 * 0 = mS from by omega] at h
        rw [hyy, h] at hD
        exact absurd hD (by simp)
    · exact heq
    · -- the D at mS + 1 precedes y
      exfalso
      have h := CopiedRank.copiedSlice_getElem?_blockD mS 0 n hm (by omega)
      rw [show mS + 2 * 0 + 1 = mS + 1 from by omega] at h
      have hU := hall (mS + 1) hgt
      rw [h] at hU
      exact absurd hU (by simp)
  · rintro rfl
    have hD := CopiedRank.copiedSlice_getElem?_blockD mS 0 n hm (by omega)
    rw [show mS + 2 * 0 + 1 = mS + 1 from by omega] at hD
    refine ⟨hD, fun q hq => ?_⟩
    rcases Nat.lt_or_ge q mS with hq' | hq'
    · exact copiedSlice_getElem?_pref mS n q hm hq'
    · have hqq : q = mS := by omega
      have h := CopiedRank.copiedSlice_getElem?_blockU mS 0 n hm (by omega)
      rw [show mS + 2 * 0 = mS from by omega] at h
      rw [hqq]
      exact h

/-- `lastU(copiedSlice mS n) = mS + 2(n−1)` (uniquely). -/
theorem lastU_copiedSlice (mS n : ℕ) (hm : 1 ≤ mS) (hn : 1 ≤ n) (y : ℕ)
    (hy : y < 2 * (mS + n)) :
    ((copiedSlice mS n)[y]? = some U ∧
      ∀ q, y < q → q < 2 * (mS + n) → (copiedSlice mS n)[q]? = some D)
      ↔ y = mS + 2 * (n - 1) := by
  constructor
  · rintro ⟨hU, hall⟩
    rcases Nat.lt_trichotomy y (mS + 2 * (n - 1)) with hlt | heq | hgt
    · -- the U at mS + 2(n−1) follows y
      exfalso
      have h := CopiedRank.copiedSlice_getElem?_blockU mS (n - 1) n hm
        (by omega)
      have hD := hall (mS + 2 * (n - 1)) hlt (by omega)
      rw [h] at hD
      exact absurd hD (by simp)
    · exact heq
    · -- everything after mS + 2(n−1) is D
      exfalso
      rw [copiedSlice_getElem?_after_lastU mS n y hm hn hgt hy] at hU
      exact absurd hU (by simp)
  · rintro rfl
    refine ⟨CopiedRank.copiedSlice_getElem?_blockU mS (n - 1) n hm (by omega),
      fun q hq hqw => copiedSlice_getElem?_after_lastU mS n q hm hn hq hqw⟩

/-! ## The offset gadget (a fixed difference between two of the four FO slots) -/

/-- A 4-FO-variable formula asserting `ρ hi = ρ lo + k` (slot `0` = base `z`,
`1` = coordinate `x`, `2` = `firstD` landmark, `3` = `lastU` landmark). -/
noncomputable def offsetForm (lo hi : Fin 4) (k : ℕ) : MSO.Formula Step 4 0 :=
  SliceFasGates.relabelFO (fun i : Fin 2 => if i = 0 then lo else hi)
    (SliceFasGates.mso_offset_eq (Alpha := Step) k).choose

theorem offsetForm_sat (lo hi : Fin 4) (k : ℕ) (w : List Step)
    (ρ : Fin 4 → ℕ) (hlo : ρ lo < w.length) (hhi : ρ hi < w.length) :
    (offsetForm lo hi k).Sat w ρ Fin.elim0 ↔ ρ hi = ρ lo + k := by
  unfold offsetForm
  rw [SliceFasGates.sat_relabelFO]
  have hval : (ρ ∘ (fun i : Fin 2 => if i = 0 then lo else hi))
      = Fin.cons (ρ lo) (Fin.cons (ρ hi) Fin.elim0) := by
    funext i
    fin_cases i <;> simp [Function.comp]
  rw [hval]
  exact (SliceFasGates.mso_offset_eq (Alpha := Step) k).choose_spec
    w (ρ lo) (ρ hi) hlo hhi

/-! ## The landmark-relative position decoder -/

/-- **The landmark decoder**: every region's copied-slice position as a FIXED
offset from a landmark (slot `2` = `firstD`, slot `3` = `lastU`) or the bound
base (slot `0`).  NO constant depends on `mS` (D16): the shift is carried by
the landmark valuations, not the formula syntax. -/
noncomputable def regionDecodeL {B : ℕ} : RegionSpec B → MSO.Formula Step 4 0
  | .pre => offsetForm 1 2 2
  | .suf => offsetForm 3 1 2
  | .front f e =>
      if 2 * f.val + e.toNat = 0 then offsetForm 1 2 1
      else offsetForm 2 1 (2 * f.val + e.toNat - 1)
  | .back l e =>
      if l.val = 0 then offsetForm 3 1 e.toNat
      else offsetForm 1 3 (2 * l.val - e.toNat)
  | .cluster δ e => offsetForm 0 1 (2 * δ.val + e.toNat)

/-- **The decode pins the coordinate** (the F3.5 capstone): at the landmark
valuation `(z, x, firstD, lastU) = (mS+2t, x, mS+1, mS+2(n−1))`, the decode of
region `r` holds of `x` exactly when `x` is the copied-slice position `r`
describes at base `t` (the wrapped position shifted by `mS−1`). -/
theorem regionDecodeL_sat {B : ℕ} (r : RegionSpec B) (mS t n x : ℕ)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hBn : B ≤ n) (hz : t < n)
    (hx : x < 2 * (mS + n)) :
    ((regionDecodeL r).Sat (copiedSlice mS n)
        (Fin.cons (mS + 2 * t) (Fin.cons x (Fin.cons (mS + 1)
          (Fin.cons (mS + 2 * (n - 1)) Fin.elim0)))) Fin.elim0
      ↔ x = mS - 1 + r.posAt t n) := by
  set ρ : Fin 4 → ℕ := Fin.cons (mS + 2 * t) (Fin.cons x (Fin.cons (mS + 1)
    (Fin.cons (mS + 2 * (n - 1)) Fin.elim0))) with hρ
  have hlen : (copiedSlice mS n).length = 2 * (mS + n) := length_copiedSlice mS n
  -- the four slot valuations are in-slice
  have hρ0 : ρ 0 < (copiedSlice mS n).length := by rw [hlen]; show mS + 2 * t < _; omega
  have hρ1 : ρ 1 < (copiedSlice mS n).length := by rw [hlen]; show x < _; exact hx
  have hρ2 : ρ 2 < (copiedSlice mS n).length := by rw [hlen]; show mS + 1 < _; omega
  have hρ3 : ρ 3 < (copiedSlice mS n).length := by rw [hlen]; show mS + 2 * (n - 1) < _; omega
  have e0 : ρ 0 = mS + 2 * t := rfl
  have e1 : ρ 1 = x := rfl
  have e2 : ρ 2 = mS + 1 := rfl
  have e3 : ρ 3 = mS + 2 * (n - 1) := rfl
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
  · -- pre
    rw [show regionDecodeL (RegionSpec.pre (B := B)) = offsetForm 1 2 2 from rfl,
      offsetForm_sat 1 2 2 _ ρ hρ1 hρ2, e1, e2]
    simp only [RegionSpec.posAt]
    omega
  · -- suf
    rw [show regionDecodeL (RegionSpec.suf (B := B)) = offsetForm 3 1 2 from rfl,
      offsetForm_sat 3 1 2 _ ρ hρ3 hρ1, e1, e3]
    simp only [RegionSpec.posAt]
    omega
  · -- front
    have hf := f.isLt
    have he : e.toNat ≤ 1 := by cases e <;> decide
    by_cases hfe : 2 * f.val + e.toNat = 0
    · rw [show regionDecodeL (RegionSpec.front f e) = offsetForm 1 2 1 from by
        simp only [regionDecodeL, hfe, if_pos],
        offsetForm_sat 1 2 1 _ ρ hρ1 hρ2, e1, e2]
      simp only [RegionSpec.posAt]
      omega
    · rw [show regionDecodeL (RegionSpec.front f e)
          = offsetForm 2 1 (2 * f.val + e.toNat - 1) from by
        simp only [regionDecodeL, hfe, if_false],
        offsetForm_sat 2 1 (2 * f.val + e.toNat - 1) _ ρ hρ2 hρ1, e1, e2]
      simp only [RegionSpec.posAt]
      omega
  · -- back
    have hl := l.isLt
    have he : e.toNat ≤ 1 := by cases e <;> decide
    by_cases hl0 : l.val = 0
    · rw [show regionDecodeL (RegionSpec.back l e) = offsetForm 3 1 e.toNat from by
        simp only [regionDecodeL, hl0, if_pos],
        offsetForm_sat 3 1 e.toNat _ ρ hρ3 hρ1, e1, e3]
      simp only [RegionSpec.posAt, hl0]
      omega
    · rw [show regionDecodeL (RegionSpec.back l e)
          = offsetForm 1 3 (2 * l.val - e.toNat) from by
        simp only [regionDecodeL, hl0, if_false],
        offsetForm_sat 1 3 (2 * l.val - e.toNat) _ ρ hρ1 hρ3, e1, e3]
      simp only [RegionSpec.posAt]
      omega
  · -- cluster
    have hδ := δ.isLt
    rw [show regionDecodeL (RegionSpec.cluster δ e)
        = offsetForm 0 1 (2 * δ.val + e.toNat) from rfl,
      offsetForm_sat 0 1 (2 * δ.val + e.toNat) _ ρ hρ0 hρ1, e0, e1]
    simp only [RegionSpec.posAt]
    omega

/-! ## The residue-offset gadget (for the bulk landmark clause) -/

/-- **The residue-offset formula**: `(x + (M − r)) % M = y % M`, i.e. the
period-`M` residue of `y` lies `r` ahead of `x`'s.  All constants
machine-level. -/
theorem mso_offset_mod (M r : ℕ) (hM : 1 ≤ M) (_hr : r < M) :
    ∃ φ : MSO.Formula Step 2 0, ∀ (w : List Step) (x y : ℕ),
      x < w.length → y < w.length →
      (φ.Sat w (Fin.cons x (Fin.cons y Fin.elim0)) Fin.elim0
        ↔ (x + (M - r)) % M = y % M) := by
  classical
  refine ⟨SliceFasGates.bigOr ((List.finRange M).map (fun a =>
    MSO.Formula.and
      (SliceFasGates.relabelFO (fun _ : Fin 1 => (0 : Fin 2))
        (mso_position_mod (Alpha := Step) M a.val a.isLt).choose)
      (SliceFasGates.relabelFO (fun _ : Fin 1 => (1 : Fin 2))
        (mso_position_mod (Alpha := Step) M ((a.val + (M - r)) % M)
          (Nat.mod_lt _ hM)).choose))), fun w x y hx hy => ?_⟩
  rw [SliceFasGates.sat_bigOr]
  have hmodeq : (x + (M - r)) % M = (x % M + (M - r)) % M :=
    ((Nat.mod_modEq x M).add_right (M - r)).symm
  constructor
  · rintro ⟨φ, hφmem, hφsat⟩
    rw [List.mem_map] at hφmem
    obtain ⟨a, _, rfl⟩ := hφmem
    rw [MSO.Formula.sat_and, SliceFasGates.sat_relabelFO,
      SliceFasGates.sat_relabelFO] at hφsat
    obtain ⟨hsx, hsy⟩ := hφsat
    have hxa : x % M = a.val := by
      have := (mso_position_mod (Alpha := Step) M a.val a.isLt).choose_spec w x hx
      rw [show (Fin.cons x (Fin.cons y Fin.elim0)) ∘ (fun _ : Fin 1 => (0 : Fin 2))
          = (fun _ => x) from by funext i; fin_cases i; rfl] at hsx
      exact this.mp hsx
    have hya : y % M = (a.val + (M - r)) % M := by
      have := (mso_position_mod (Alpha := Step) M ((a.val + (M - r)) % M)
        (Nat.mod_lt _ hM)).choose_spec w y hy
      rw [show (Fin.cons x (Fin.cons y Fin.elim0)) ∘ (fun _ : Fin 1 => (1 : Fin 2))
          = (fun _ => y) from by funext i; fin_cases i; rfl] at hsy
      exact this.mp hsy
    rw [hya, ← hxa]
    exact hmodeq
  · intro hmod
    refine ⟨_, List.mem_map_of_mem (List.mem_finRange ⟨x % M, Nat.mod_lt _ hM⟩), ?_⟩
    rw [MSO.Formula.sat_and, SliceFasGates.sat_relabelFO,
      SliceFasGates.sat_relabelFO]
    constructor
    · rw [show (Fin.cons x (Fin.cons y Fin.elim0)) ∘ (fun _ : Fin 1 => (0 : Fin 2))
          = (fun _ => x) from by funext i; fin_cases i; rfl]
      exact ((mso_position_mod (Alpha := Step) M (x % M)
        (Nat.mod_lt _ hM)).choose_spec w x hx).mpr rfl
    · rw [show (Fin.cons x (Fin.cons y Fin.elim0)) ∘ (fun _ : Fin 1 => (1 : Fin 2))
          = (fun _ => y) from by funext i; fin_cases i; rfl]
      refine ((mso_position_mod (Alpha := Step) M
        (((⟨x % M, Nat.mod_lt _ hM⟩ : Fin M).val + (M - r)) % M)
        (Nat.mod_lt _ hM)).choose_spec w y hy).mpr ?_
      show y % M = (x % M + (M - r)) % M
      rw [← hmod]
      exact hmodeq

end CopiedLandmark
