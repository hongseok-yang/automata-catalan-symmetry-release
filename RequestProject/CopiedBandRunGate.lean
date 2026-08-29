/-
# The DEPTH-BANDED run-clause variant (§9 mS-direction)

An unbanded per-residue-class run clause fires on EVERY sel-`D` atom in the final
`D`-run at `position % Q = r`, with no depth filter.  That is UNSOUND for the bridge's forward
direction (`TIE ⇒ accepts`): `atomOrd` (the raw MSO tie-order `χ`) is unconstrained between atoms of
DIFFERENT rank, and a valid presentation can have a sub-`Ts` (gate-cycle pre-period) sel-`D`
NON-achiever at a band-tying residue with `¬ atomOrd ī xb` — `TIE` (which orders only achievers) is
silent, so the whole-run clause fails while `TIE` holds.

The fix is to BAND the run clause to depth `≥ q_D` (suffix) / `≥ q_U` (prefix), the affine régime where
a two-rep-tying class is uniformly `d*` (so every band atom of an active residue IS an achiever and
`TIE` discharges it).  The band is `mS`-free: "position `p` is at least `q_D` deep into the final
`D`-run" `⟺ ∃ y, y + (q_D+2) = p ∧ inFinalDRun y` (the cell at `y = p-(q_D+2)` is still in the final
`D`-run, which for the copied slice pins `p ≥ mS+2n+1+q_D`, i.e. suffix depth `≥ q_D`).  The prefix
twin pins `p ≥ q_U` via `∃ y, y + q_U = p ∧ inInitialURun y`.

* `bandLoSuf k` / `bandLoPre k` — the MSO band-lower-bound guards + their `sat` lemmas.
-/
import RequestProject.CopiedDeepRunGate

namespace CopiedBandRunGate

open WRP Step MSO MSOMarkN CopiedSufRunGate

/-- **Suffix band-lower guard.**  One free FO variable `x_0 = p`: there is an earlier position
`y = p - k` that lies in the final maximal `D`-run.  Used with `k = q_D + 2` to pin suffix depth
`≥ q_D` on the copied slice. -/
noncomputable def bandLoSuf (k : ℕ) : MSO.Formula Step 1 0 :=
  MSO.Formula.exFO (MSO.Formula.and
    (SliceFasGates.mso_offset_eq (Alpha := Step) k).choose
    (SliceFasGates.relabelFO (fun _ : Fin 1 => (0 : Fin 2)) inFinalDRun))

theorem sat_bandLoSuf (k : ℕ) (w : List Step) (p : ℕ) (hp : p < w.length) :
    (bandLoSuf k).Sat w (fun _ => p) Fin.elim0 ↔
      ∃ y, y < w.length ∧ p = y + k ∧
        (w[y]? = some D ∧ ∀ q, q < w.length → y < q → w[q]? = some D) := by
  rw [bandLoSuf, MSO.Formula.sat_exFO]
  constructor
  · rintro ⟨y, hy, hsat⟩
    rw [MSO.Formula.sat_and] at hsat
    obtain ⟨hoff, hrun⟩ := hsat
    have hvaloff : (Fin.cons y (fun _ => p) : Fin 2 → ℕ) = Fin.cons y (Fin.cons p Fin.elim0) := by
      funext i; fin_cases i <;> rfl
    rw [hvaloff, (SliceFasGates.mso_offset_eq (Alpha := Step) k).choose_spec w y p hy hp] at hoff
    rw [SliceFasGates.sat_relabelFO] at hrun
    have hvalrun : (Fin.cons y (fun _ => p) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
        = fun _ => y := by funext i; simp
    rw [hvalrun, sat_inFinalDRun] at hrun
    exact ⟨y, hy, hoff, hrun⟩
  · rintro ⟨y, hy, hpk, hrun⟩
    refine ⟨y, hy, ?_⟩
    rw [MSO.Formula.sat_and]
    refine ⟨?_, ?_⟩
    · have hvaloff : (Fin.cons y (fun _ => p) : Fin 2 → ℕ) = Fin.cons y (Fin.cons p Fin.elim0) := by
        funext i; fin_cases i <;> rfl
      rw [hvaloff, (SliceFasGates.mso_offset_eq (Alpha := Step) k).choose_spec w y p hy hp]
      exact hpk
    · rw [SliceFasGates.sat_relabelFO]
      have hvalrun : (Fin.cons y (fun _ => p) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
          = fun _ => y := by funext i; simp
      rw [hvalrun, sat_inFinalDRun]
      exact hrun

/-- On `copiedSlice mS n`, the suffix band guard really is a lower bound on
the stretched suffix depth.  Since the final maximal `D`-run starts one step
after the last `U` (`mS + 2*(n-1)`), a witness `p = y + k` with `2 ≤ k`
places `p` in the suffix tail as `mS + 2*n + 1 + l`, with `k-2 ≤ l`. -/
theorem bandLoSuf_copiedSlice_depth (mS n p k : ℕ) (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hk : 2 ≤ k) (hp : p < (copiedSlice mS n).length)
    (hband : ∃ y, y < (copiedSlice mS n).length ∧ p = y + k ∧
      ((copiedSlice mS n)[y]? = some D ∧
        ∀ q, q < (copiedSlice mS n).length → y < q → (copiedSlice mS n)[q]? = some D)) :
    ∃ l, k - 2 ≤ l ∧ l < mS - 1 ∧ p = mS + 2 * n + 1 + l := by
  rcases hband with ⟨y, hy, rfl, hD, htail⟩
  set yL := mS + 2 * (n - 1) with hyLdef
  have hUlast : (copiedSlice mS n)[yL]? = some U := by
    rw [hyLdef]
    exact CopiedRank.copiedSlice_getElem?_blockU mS (n - 1) n hm (by omega)
  have hyLlt : yL < y := by
    by_contra hnot
    have hyle : y ≤ yL := by omega
    rcases Nat.lt_or_eq_of_le hyle with hylt | hyeq
    · have hDlast := htail yL (by rw [length_copiedSlice]; omega) hylt
      rw [hUlast] at hDlast
      exact absurd hDlast (by simp)
    · subst y
      rw [hUlast] at hD
      exact absurd hD (by simp)
  refine ⟨y + k - (mS + 2 * n + 1), ?_, ?_, ?_⟩
  · omega
  · rw [length_copiedSlice] at hp
    omega
  · omega

/-- **Prefix band-lower guard.**  One free FO variable `x_0 = p`: there is an earlier position
`y = p - k` that lies in the initial maximal `U`-run.  Used with `k = q_U` to pin prefix depth
`≥ q_U` on the copied slice (prefix cell `prefIdx q` sits at position `q`). -/
noncomputable def bandLoPre (k : ℕ) : MSO.Formula Step 1 0 :=
  MSO.Formula.exFO (MSO.Formula.and
    (SliceFasGates.mso_offset_eq (Alpha := Step) k).choose
    (SliceFasGates.relabelFO (fun _ : Fin 1 => (0 : Fin 2)) inInitialURun))

theorem sat_bandLoPre (k : ℕ) (w : List Step) (p : ℕ) (hp : p < w.length) :
    (bandLoPre k).Sat w (fun _ => p) Fin.elim0 ↔
      ∃ y, y < w.length ∧ p = y + k ∧
        (w[y]? = some U ∧ ∀ q, q < w.length → q < y → w[q]? = some U) := by
  rw [bandLoPre, MSO.Formula.sat_exFO]
  constructor
  · rintro ⟨y, hy, hsat⟩
    rw [MSO.Formula.sat_and] at hsat
    obtain ⟨hoff, hrun⟩ := hsat
    have hvaloff : (Fin.cons y (fun _ => p) : Fin 2 → ℕ) = Fin.cons y (Fin.cons p Fin.elim0) := by
      funext i; fin_cases i <;> rfl
    rw [hvaloff, (SliceFasGates.mso_offset_eq (Alpha := Step) k).choose_spec w y p hy hp] at hoff
    rw [SliceFasGates.sat_relabelFO] at hrun
    have hvalrun : (Fin.cons y (fun _ => p) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
        = fun _ => y := by funext i; simp
    rw [hvalrun, sat_inInitialURun] at hrun
    exact ⟨y, hy, hoff, hrun⟩
  · rintro ⟨y, hy, hpk, hrun⟩
    refine ⟨y, hy, ?_⟩
    rw [MSO.Formula.sat_and]
    refine ⟨?_, ?_⟩
    · have hvaloff : (Fin.cons y (fun _ => p) : Fin 2 → ℕ) = Fin.cons y (Fin.cons p Fin.elim0) := by
        funext i; fin_cases i <;> rfl
      rw [hvaloff, (SliceFasGates.mso_offset_eq (Alpha := Step) k).choose_spec w y p hy hp]
      exact hpk
    · rw [SliceFasGates.sat_relabelFO]
      have hvalrun : (Fin.cons y (fun _ => p) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
          = fun _ => y := by funext i; simp
      rw [hvalrun, sat_inInitialURun]
      exact hrun

/-- On `copiedSlice mS n`, the initial-`U` run guard places a position no
later than the last initial `U` (`mS`).  The first following `D` is at
`mS+1`. -/
theorem inInitialURun_copiedSlice_le_midU (mS n p : ℕ) (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hrun : (copiedSlice mS n)[p]? = some U ∧
      ∀ q, q < (copiedSlice mS n).length → q < p → (copiedSlice mS n)[q]? = some U) :
    p ≤ mS := by
  have hDfirst : (copiedSlice mS n)[mS + 1]? = some D := by
    have h := CopiedRank.copiedSlice_getElem?_blockD mS 0 n hm (by omega)
    simpa using h
  by_contra hpnot
  have hgt : mS < p := by omega
  rcases Nat.lt_or_eq_of_le (by omega : mS + 1 ≤ p) with hlt | heq
  · have hUfirst := hrun.2 (mS + 1) (by rw [length_copiedSlice]; omega) hlt
    rw [hDfirst] at hUfirst
    exact absurd hUfirst (by simp)
  · subst p
    rw [hDfirst] at hrun
    exact absurd hrun.1 (by simp)

/-- Prefix band geometry on the copied slice.  A banded initial-`U` position is
either in the genuine prefix stretch (`p < mS-1`, where it can be read as the
local depth `l = p`) or it is one of the two boundary `U` positions `mS-1`/`mS`
that must be handled by the core/deep clauses rather than the prefix-stretch
rank-affine wrapper. -/
theorem bandLoPre_copiedSlice_cases (mS n p k : ℕ) (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hrun : (copiedSlice mS n)[p]? = some U ∧
      ∀ q, q < (copiedSlice mS n).length → q < p → (copiedSlice mS n)[q]? = some U)
    (hband : ∃ y, y < (copiedSlice mS n).length ∧ p = y + k ∧
      ((copiedSlice mS n)[y]? = some U ∧
        ∀ q, q < (copiedSlice mS n).length → q < y → (copiedSlice mS n)[q]? = some U)) :
    (∃ l, k ≤ l ∧ l < mS - 1 ∧ p = l) ∨ p = mS - 1 ∨ p = mS := by
  rcases hband with ⟨y, _hy, hp_eq, _hyrun⟩
  by_cases hpref : p < mS - 1
  · exact Or.inl ⟨p, by omega, hpref, rfl⟩
  · have hle := inInitialURun_copiedSlice_le_midU mS n p hm hn hrun
    exact Or.inr (by omega)

/-- A prefix-run position is strictly inside the prefix stretch: there is a
later position two steps before the first `D`.  On `copiedSlice mS n`, this
is exactly the semantic side condition needed to exclude the two boundary
`U` positions `mS - 1` and `mS`. -/
noncomputable def strictInitialStretch : MSO.Formula Step 1 0 :=
  MSO.Formula.exFO (MSO.Formula.and
    (MSO.Formula.lt (1 : Fin 2) (0 : Fin 2))
    (SliceFasGates.relabelFO (fun _ : Fin 1 => (0 : Fin 2))
      (CopiedDeepRunGate.mso_position_beforeFirstD 2).choose))

theorem sat_strictInitialStretch (w : List Step) (p : ℕ) :
    strictInitialStretch.Sat w (fun _ => p) Fin.elim0 ↔
      ∃ z, z < w.length ∧ p < z ∧
        (w[z + 2]? = some D ∧ ∀ q, q < z + 2 → w[q]? ≠ some D) := by
  rw [strictInitialStretch, MSO.Formula.sat_exFO]
  constructor
  · rintro ⟨z, hz, hsat⟩
    rw [MSO.Formula.sat_and, MSO.Formula.sat_lt, SliceFasGates.sat_relabelFO] at hsat
    obtain ⟨hpz, hfirst⟩ := hsat
    have hval : (Fin.cons z (fun _ => p) : Fin 2 → ℕ) ∘
        (fun _ : Fin 1 => (0 : Fin 2)) = fun _ => z := by
      funext i
      fin_cases i
      rfl
    rw [hval] at hfirst
    exact ⟨z, hz, hpz, ((CopiedDeepRunGate.mso_position_beforeFirstD 2).choose_spec w z hz).mp hfirst⟩
  · rintro ⟨z, hz, hpz, hfirst⟩
    refine ⟨z, hz, ?_⟩
    rw [MSO.Formula.sat_and, MSO.Formula.sat_lt, SliceFasGates.sat_relabelFO]
    refine ⟨hpz, ?_⟩
    have hval : (Fin.cons z (fun _ => p) : Fin 2 → ℕ) ∘
        (fun _ : Fin 1 => (0 : Fin 2)) = fun _ => z := by
      funext i
      fin_cases i
      rfl
    rw [hval]
    exact ((CopiedDeepRunGate.mso_position_beforeFirstD 2).choose_spec w z hz).mpr hfirst

/-- Semantic guard for the strict banded prefix-run clause. -/
def preBandStrictGuard (w : List Step) (Q r k p : ℕ) : Prop :=
  ((w[p]? = some U ∧ ∀ q, q < w.length → q < p → w[q]? = some U) ∧ p % Q = r) ∧
    (∃ y, y < w.length ∧ p = y + k ∧
      (w[y]? = some U ∧ ∀ q, q < w.length → q < y → w[q]? = some U)) ∧
    (∃ z, z < w.length ∧ p < z ∧
      (w[z + 2]? = some D ∧ ∀ q, q < z + 2 → w[q]? ≠ some D))

theorem suffixBandGuard_copiedSlice (mS n q_D l : ℕ) (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hl : l < mS - 1) (hql : q_D ≤ l) :
    (((copiedSlice mS n)[mS + 2 * n + 1 + l]? = some D
      ∧ ∀ q, q < (copiedSlice mS n).length → mS + 2 * n + 1 + l < q →
          (copiedSlice mS n)[q]? = some D)
    ∧ (∃ y, y < (copiedSlice mS n).length
        ∧ mS + 2 * n + 1 + l = y + (q_D + 2)
        ∧ ((copiedSlice mS n)[y]? = some D
          ∧ ∀ q, q < (copiedSlice mS n).length → y < q →
              (copiedSlice mS n)[q]? = some D))) := by
  constructor
  · constructor
    · exact CopiedRank.copiedSlice_getElem?_tail mS l n hm hl
    · intro q hq hpq
      exact CopiedLandmark.copiedSlice_getElem?_after_lastU mS n q hm hn (by omega)
        (by simpa [length_copiedSlice] using hq)
  · let y := mS + 2 * n + 1 + l - (q_D + 2)
    refine ⟨y, ?_, ?_, ?_⟩
    · rw [length_copiedSlice]
      omega
    · omega
    · constructor
      · exact CopiedLandmark.copiedSlice_getElem?_after_lastU mS n y hm hn (by omega) (by
          omega)
      · intro q hq hyq
        exact CopiedLandmark.copiedSlice_getElem?_after_lastU mS n q hm hn (by omega)
          (by simpa [length_copiedSlice] using hq)

theorem preBandStrictGuard_copiedSlice (mS n Q q_U l : ℕ) (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hl : l < mS - 1) (hql : q_U ≤ l) :
    preBandStrictGuard (copiedSlice mS n) Q (l % Q) q_U l := by
  have hinit : ∀ p, p < mS →
      (copiedSlice mS n)[p]? = some U ∧
        ∀ q, q < (copiedSlice mS n).length → q < p → (copiedSlice mS n)[q]? = some U := by
    intro p hp
    constructor
    · exact CopiedLandmark.copiedSlice_getElem?_pref mS n p hm hp
    · intro q _hq hqp
      exact CopiedLandmark.copiedSlice_getElem?_pref mS n q hm (by omega)
  refine ⟨⟨hinit l (by omega), rfl⟩, ?_, ?_⟩
  · refine ⟨l - q_U, ?_, ?_, hinit (l - q_U) (by omega)⟩
    · rw [length_copiedSlice]
      omega
    · omega
  · refine ⟨mS - 1, ?_, ?_, ?_⟩
    · rw [length_copiedSlice]
      omega
    · omega
    · constructor
      · rw [show mS - 1 + 2 = mS + 1 by omega]
        simpa using CopiedRank.copiedSlice_getElem?_blockD mS 0 n hm (by omega)
      · intro q hq
        by_cases hqpre : q < mS
        · rw [CopiedLandmark.copiedSlice_getElem?_pref mS n q hm hqpre]
          simp
        · have hqeq : q = mS := by omega
          subst q
          have hU : (copiedSlice mS n)[mS]? = some U := by
            simpa using CopiedRank.copiedSlice_getElem?_blockU mS 0 n hm (by omega)
          rw [hU]
          simp

theorem firstDGuard_copiedSlice (mS n : ℕ) (hm : 1 ≤ mS) (hn : 1 ≤ n) :
    (copiedSlice mS n)[mS + 1]? = some D ∧
      ∀ q, q < mS + 1 → (copiedSlice mS n)[q]? ≠ some D := by
  constructor
  · simpa using CopiedRank.copiedSlice_getElem?_blockD mS 0 n hm (by omega)
  · intro q hq
    by_cases hqpre : q < mS
    · rw [CopiedLandmark.copiedSlice_getElem?_pref mS n q hm hqpre]
      simp
    · have hqeq : q = mS := by omega
      subst q
      have hU : (copiedSlice mS n)[mS]? = some U := by
        simpa using CopiedRank.copiedSlice_getElem?_blockU mS 0 n hm (by omega)
      rw [hU]
      simp

/-! ## The banded suffix run clause -/

/-- **Banded per-residue-class suffix-run atomOrd clause.**  The per-residue-class clause with
one extra per-coord antecedent conjunct `bandLoSuf k` (the competitor must be at least `k` deep into the
final `D`-run).  At `k = q_D + 2` on the copied slice this restricts to suffix depth `≥ q_D`, the affine
régime where a two-rep-tying class is uniformly `d*`. -/
noncomputable def sufOrdClauseAtBand (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) (k : ℕ) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  SliceFasGatesGA.faFOs (P.toPoly.arity c') (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        MSO.Formula.and
          (MSO.Formula.and
            (SliceFasGates.relabelFO
              (fun _ : Fin 1 =>
                (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
              inFinalDRun)
            (SliceFasGates.relabelFO
              (fun _ : Fin 1 =>
                (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
              (SliceFasGates.mso_position_mod Q r hr).choose))
          (SliceFasGates.relabelFO
            (fun _ : Fin 1 =>
              (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
            (bandLoSuf k)))))
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

/-! ## Update-shaped banded suffix run clause -/

/-- Relabel a one-variable formula to competitor coordinate `i` inside the
usual `arity c'` block of quantified target coordinates. -/
def targetCoordFO (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (i : Fin (P.toPoly.arity c')) :
    Fin 1 → Fin (P.toPoly.arity c + P.toPoly.arity c') :=
  fun _ => (⟨i.1, by have := i.2; omega⟩ :
    Fin (P.toPoly.arity c + P.toPoly.arity c'))

/-- Semantic suffix band/residue guard for one moving update coordinate. -/
def updateSufBandGuard (w : List Step) (Q r k p : ℕ) : Prop :=
  ((w[p]? = some D ∧ ∀ q, q < w.length → p < q → w[q]? = some D) ∧ p % Q = r) ∧
    (∃ y, y < w.length ∧ p = y + k ∧
      (w[y]? = some D ∧ ∀ q, q < w.length → y < q → w[q]? = some D))

/-- Coordinate formula for the moving coordinate of an update-shaped suffix
run clause. -/
noncomputable def updateSufBandCoordFormula
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) (k : ℕ) (i : Fin (P.toPoly.arity c')) :
    MSO.Formula Step (P.toPoly.arity c + P.toPoly.arity c') 0 :=
  MSO.Formula.and
    (MSO.Formula.and
      (SliceFasGates.relabelFO (targetCoordFO P c c' i) inFinalDRun)
      (SliceFasGates.relabelFO (targetCoordFO P c c' i)
        (SliceFasGates.mso_position_mod Q r hr).choose))
    (SliceFasGates.relabelFO (targetCoordFO P c c' i) (bandLoSuf k))

theorem updateSufBandCoordFormula_sat
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) (k : ℕ) (i : Fin (P.toPoly.arity c'))
    (w : List Step) (xb : Fin (P.toPoly.arity c') → ℕ)
    (i_marks : Fin (P.toPoly.arity c) → ℕ) (hxb : xb i < w.length) :
    (updateSufBandCoordFormula P c c' Q r hr k i).Sat w
        (SliceFasGatesGA.appFO xb i_marks) Fin.elim0 ↔
      updateSufBandGuard w Q r k (xb i) := by
  have hv0 :
      (SliceFasGatesGA.appFO xb i_marks) ∘ targetCoordFO P c c' i =
        fun _ => xb i := by
    funext _
    exact SliceFasGatesGA.appFO_low xb i_marks i.1 (by have := i.2; omega)
      (by have := i.2; omega)
  rw [updateSufBandCoordFormula, updateSufBandGuard, MSO.Formula.sat_and,
    MSO.Formula.sat_and, SliceFasGates.sat_relabelFO,
    SliceFasGates.sat_relabelFO, SliceFasGates.sat_relabelFO, sat_inFinalDRun,
    hv0, (SliceFasGates.mso_position_mod Q r hr).choose_spec w (xb i) hxb,
    sat_bandLoSuf k w (xb i) hxb]

/-- Pin a quantified competitor coordinate to a fixed base value. -/
noncomputable def updatePinCoordFormula
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (ī0 : Fin (P.toPoly.arity c') → ℕ) (i : Fin (P.toPoly.arity c')) :
    MSO.Formula Step (P.toPoly.arity c + P.toPoly.arity c') 0 :=
  SliceFasGates.relabelFO (targetCoordFO P c c' i)
    (SliceFasGates.mso_position_eq (Alpha := Step) (ī0 i)).choose

theorem updatePinCoordFormula_sat
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (ī0 : Fin (P.toPoly.arity c') → ℕ) (i : Fin (P.toPoly.arity c'))
    (w : List Step) (xb : Fin (P.toPoly.arity c') → ℕ)
    (i_marks : Fin (P.toPoly.arity c) → ℕ) (hxb : xb i < w.length) :
    (updatePinCoordFormula P c c' ī0 i).Sat w
        (SliceFasGatesGA.appFO xb i_marks) Fin.elim0 ↔
      xb i = ī0 i := by
  have hv0 :
      (SliceFasGatesGA.appFO xb i_marks) ∘ targetCoordFO P c c' i =
        fun _ => xb i := by
    funext _
    exact SliceFasGatesGA.appFO_low xb i_marks i.1 (by have := i.2; omega)
      (by have := i.2; omega)
  rw [updatePinCoordFormula, SliceFasGates.sat_relabelFO, hv0,
    (SliceFasGates.mso_position_eq (Alpha := Step) (ī0 i)).choose_spec w (xb i) hxb]

/-- Distinguished-coordinate deep-suffix guard for update-shaped deep clauses. -/
noncomputable def updateDeepSufCoordFormula
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (k : ℕ) (i : Fin (P.toPoly.arity c')) :
    MSO.Formula Step (P.toPoly.arity c + P.toPoly.arity c') 0 :=
  MSO.Formula.and
    (SliceFasGates.relabelFO (targetCoordFO P c c' i) inFinalDRun)
    (SliceFasGates.relabelFO (targetCoordFO P c c' i)
      (SliceFasGates.mso_position_fromEnd k).choose)

theorem updateDeepSufCoordFormula_sat
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (k : ℕ) (i : Fin (P.toPoly.arity c'))
    (w : List Step) (xb : Fin (P.toPoly.arity c') → ℕ)
    (i_marks : Fin (P.toPoly.arity c) → ℕ) (hxb : xb i < w.length) :
    (updateDeepSufCoordFormula P c c' k i).Sat w
        (SliceFasGatesGA.appFO xb i_marks) Fin.elim0 ↔
      ((w[xb i]? = some D ∧ ∀ q, q < w.length → xb i < q → w[q]? = some D)
        ∧ xb i + 1 + k = w.length) := by
  have hv0 :
      (SliceFasGatesGA.appFO xb i_marks) ∘ targetCoordFO P c c' i =
        fun _ => xb i := by
    funext _
    exact SliceFasGatesGA.appFO_low xb i_marks i.1 (by have := i.2; omega)
      (by have := i.2; omega)
  rw [updateDeepSufCoordFormula, MSO.Formula.sat_and, SliceFasGates.sat_relabelFO,
    SliceFasGates.sat_relabelFO, sat_inFinalDRun, hv0,
    (SliceFasGates.mso_position_fromEnd k).choose_spec w (xb i) hxb]

/-- Distinguished-coordinate deep-prefix guard for update-shaped deep clauses. -/
noncomputable def updateDeepPreCoordFormula
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (k : ℕ) (i : Fin (P.toPoly.arity c')) :
    MSO.Formula Step (P.toPoly.arity c + P.toPoly.arity c') 0 :=
  MSO.Formula.and
    (SliceFasGates.relabelFO (targetCoordFO P c c' i) inInitialURun)
    (SliceFasGates.relabelFO (targetCoordFO P c c' i)
      (CopiedDeepRunGate.mso_position_beforeFirstD k).choose)

theorem updateDeepPreCoordFormula_sat
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (k : ℕ) (i : Fin (P.toPoly.arity c'))
    (w : List Step) (xb : Fin (P.toPoly.arity c') → ℕ)
    (i_marks : Fin (P.toPoly.arity c) → ℕ) (hxb : xb i < w.length) :
    (updateDeepPreCoordFormula P c c' k i).Sat w
        (SliceFasGatesGA.appFO xb i_marks) Fin.elim0 ↔
      ((w[xb i]? = some U ∧ ∀ q, q < w.length → q < xb i → w[q]? = some U)
        ∧ (w[xb i + k]? = some D ∧ ∀ q, q < xb i + k → w[q]? ≠ some D)) := by
  have hv0 :
      (SliceFasGatesGA.appFO xb i_marks) ∘ targetCoordFO P c c' i =
        fun _ => xb i := by
    funext _
    exact SliceFasGatesGA.appFO_low xb i_marks i.1 (by have := i.2; omega)
      (by have := i.2; omega)
  rw [updateDeepPreCoordFormula, MSO.Formula.sat_and, SliceFasGates.sat_relabelFO,
    SliceFasGates.sat_relabelFO, sat_inInitialURun, hv0,
    (CopiedDeepRunGate.mso_position_beforeFirstD k).choose_spec w (xb i) hxb]

/-- Update-shaped deep suffix clause: nonmoving competitor coordinates are
pinned to `ī0`, and only `j0` ranges over the deep suffix guard. -/
noncomputable def updateDeepSufOrdClauseAt
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (k : ℕ) (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  SliceFasGatesGA.faFOs (P.toPoly.arity c') (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        if i = j0 then updateDeepSufCoordFormula P c c' k i
        else updatePinCoordFormula P c c' ī0 i)))
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

theorem updateDeepSufOrdClauseAt_sat
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (k : ℕ) (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ)
    (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ)
    (_hi : ∀ i, i_marks i < w.length) (hbase : ∀ i, ī0 i < w.length) :
    (updateDeepSufOrdClauseAt P c c' k j0 ī0).Sat w i_marks Fin.elim0 ↔
      ∀ p, p < w.length →
        (((w[p]? = some D ∧ ∀ q, q < w.length → p < q → w[q]? = some D)
            ∧ p + 1 + k = w.length)
          ∧ P.toPoly.sel c' w (Function.update ī0 j0 p)
          ∧ P.toPoly.label c' w (Function.update ī0 j0 p) = D) →
        P.toPoly.ord c c' w i_marks (Function.update ī0 j0 p) := by
  rw [updateDeepSufOrdClauseAt, SliceFasGatesGA.sat_faFOs]
  constructor
  · intro h p hp hcond
    obtain ⟨hguard, hsel, hlab⟩ := hcond
    let xb : Fin (P.toPoly.arity c') → ℕ := Function.update ī0 j0 p
    have hxbv : ∀ i, xb i < w.length := by
      intro i
      by_cases hij : i = j0
      · subst i
        simp [xb, hp]
      · simp [xb, hij, hbase i]
    have hsat := h xb hxbv
    rw [SliceFasGates.sat_imp] at hsat
    have hord := hsat (by
      rw [MSO.Formula.sat_and]
      refine ⟨?_, ?_⟩
      · rw [MSOMarkN.sat_andList]
        intro ψ hψ
        obtain ⟨i, _himem, rfl⟩ := List.mem_map.mp hψ
        by_cases hij : i = j0
        · simp only [if_pos hij]
          subst i
          exact (updateDeepSufCoordFormula_sat P c c' k j0 w xb i_marks
            (hxbv j0)).mpr (by simpa [xb] using hguard)
        · simp only [if_neg hij]
          exact (updatePinCoordFormula_sat P c c' ī0 i w xb i_marks (hxbv i)).mpr
            (by simp [xb, hij])
      · rw [MSO.Formula.sat_and]
        refine ⟨?_, ?_⟩
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.selDef c').choose_spec w xb).mp (by simpa [xb] using hsel)
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.labelDef c' D).choose_spec w xb).mp (by simpa [xb] using hlab))
    rw [SliceFasGates.sat_relabelFO] at hord
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' xb i_marks
    have hfinal := ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO xb i_marks) ∘ gordNB P c c')).mpr hord
    simp only [hg1, hg2] at hfinal
    simpa [xb] using hfinal
  · intro h pb hpbv
    rw [SliceFasGates.sat_imp]
    intro hprem
    rw [MSO.Formula.sat_and] at hprem
    obtain ⟨hdec, hsl⟩ := hprem
    rw [MSO.Formula.sat_and] at hsl
    obtain ⟨hsel1, hlab1⟩ := hsl
    have hguard :
        (w[pb j0]? = some D ∧ ∀ q, q < w.length → pb j0 < q → w[q]? = some D)
          ∧ pb j0 + 1 + k = w.length := by
      rw [MSOMarkN.sat_andList] at hdec
      have hpiece := hdec (updateDeepSufCoordFormula P c c' k j0)
        (List.mem_map.mpr ⟨j0, List.mem_finRange j0, by simp⟩)
      simpa using
        (updateDeepSufCoordFormula_sat P c c' k j0 w pb i_marks
          (hpbv j0)).mp hpiece
    have hpin : ∀ i, i ≠ j0 → pb i = ī0 i := by
      intro i hij
      rw [MSOMarkN.sat_andList] at hdec
      have hpiece := hdec (updatePinCoordFormula P c c' ī0 i)
        (List.mem_map.mpr ⟨i, List.mem_finRange i, by simp [hij]⟩)
      exact (updatePinCoordFormula_sat P c c' ī0 i w pb i_marks (hpbv i)).mp hpiece
    have hpb_eq : pb = Function.update ī0 j0 (pb j0) := by
      funext i
      by_cases hij : i = j0
      · subst i
        simp [Function.update]
      · simp [Function.update, hij, hpin i hij]
    have hsel : P.toPoly.sel c' w (Function.update ī0 j0 (pb j0)) := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hsel1
      have hs := ((P.toPoly.selDef c').choose_spec w pb).mpr hsel1
      rw [← hpb_eq]
      exact hs
    have hlab : P.toPoly.label c' w (Function.update ī0 j0 (pb j0)) = D := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hlab1
      have hl := ((P.toPoly.labelDef c' D).choose_spec w pb).mpr hlab1
      rw [← hpb_eq]
      exact hl
    have hord := h (pb j0) (hpbv j0) ⟨hguard, hsel, hlab⟩
    rw [SliceFasGates.sat_relabelFO]
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' pb i_marks
    refine ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO pb i_marks) ∘ gordNB P c c')).mp ?_
    simp only [hg1, hg2]
    rw [hpb_eq]
    exact hord

/-- Update-shaped deep prefix clause: nonmoving competitor coordinates are
pinned to `ī0`, and only `j0` ranges over the deep prefix guard. -/
noncomputable def updateDeepPreOrdClauseAt
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (k : ℕ) (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  SliceFasGatesGA.faFOs (P.toPoly.arity c') (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        if i = j0 then updateDeepPreCoordFormula P c c' k i
        else updatePinCoordFormula P c c' ī0 i)))
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

theorem updateDeepPreOrdClauseAt_sat
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (k : ℕ) (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ)
    (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ)
    (_hi : ∀ i, i_marks i < w.length) (hbase : ∀ i, ī0 i < w.length) :
    (updateDeepPreOrdClauseAt P c c' k j0 ī0).Sat w i_marks Fin.elim0 ↔
      ∀ p, p < w.length →
        (((w[p]? = some U ∧ ∀ q, q < w.length → q < p → w[q]? = some U)
            ∧ (w[p + k]? = some D ∧ ∀ q, q < p + k → w[q]? ≠ some D))
          ∧ P.toPoly.sel c' w (Function.update ī0 j0 p)
          ∧ P.toPoly.label c' w (Function.update ī0 j0 p) = D) →
        P.toPoly.ord c c' w i_marks (Function.update ī0 j0 p) := by
  rw [updateDeepPreOrdClauseAt, SliceFasGatesGA.sat_faFOs]
  constructor
  · intro h p hp hcond
    obtain ⟨hguard, hsel, hlab⟩ := hcond
    let xb : Fin (P.toPoly.arity c') → ℕ := Function.update ī0 j0 p
    have hxbv : ∀ i, xb i < w.length := by
      intro i
      by_cases hij : i = j0
      · subst i
        simp [xb, hp]
      · simp [xb, hij, hbase i]
    have hsat := h xb hxbv
    rw [SliceFasGates.sat_imp] at hsat
    have hord := hsat (by
      rw [MSO.Formula.sat_and]
      refine ⟨?_, ?_⟩
      · rw [MSOMarkN.sat_andList]
        intro ψ hψ
        obtain ⟨i, _himem, rfl⟩ := List.mem_map.mp hψ
        by_cases hij : i = j0
        · simp only [if_pos hij]
          subst i
          exact (updateDeepPreCoordFormula_sat P c c' k j0 w xb i_marks
            (hxbv j0)).mpr (by simpa [xb] using hguard)
        · simp only [if_neg hij]
          exact (updatePinCoordFormula_sat P c c' ī0 i w xb i_marks (hxbv i)).mpr
            (by simp [xb, hij])
      · rw [MSO.Formula.sat_and]
        refine ⟨?_, ?_⟩
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.selDef c').choose_spec w xb).mp (by simpa [xb] using hsel)
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.labelDef c' D).choose_spec w xb).mp (by simpa [xb] using hlab))
    rw [SliceFasGates.sat_relabelFO] at hord
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' xb i_marks
    have hfinal := ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO xb i_marks) ∘ gordNB P c c')).mpr hord
    simp only [hg1, hg2] at hfinal
    simpa [xb] using hfinal
  · intro h pb hpbv
    rw [SliceFasGates.sat_imp]
    intro hprem
    rw [MSO.Formula.sat_and] at hprem
    obtain ⟨hdec, hsl⟩ := hprem
    rw [MSO.Formula.sat_and] at hsl
    obtain ⟨hsel1, hlab1⟩ := hsl
    have hguard :
        (w[pb j0]? = some U ∧ ∀ q, q < w.length → q < pb j0 → w[q]? = some U)
          ∧ (w[pb j0 + k]? = some D ∧ ∀ q, q < pb j0 + k → w[q]? ≠ some D) := by
      rw [MSOMarkN.sat_andList] at hdec
      have hpiece := hdec (updateDeepPreCoordFormula P c c' k j0)
        (List.mem_map.mpr ⟨j0, List.mem_finRange j0, by simp⟩)
      simpa using
        (updateDeepPreCoordFormula_sat P c c' k j0 w pb i_marks
          (hpbv j0)).mp hpiece
    have hpin : ∀ i, i ≠ j0 → pb i = ī0 i := by
      intro i hij
      rw [MSOMarkN.sat_andList] at hdec
      have hpiece := hdec (updatePinCoordFormula P c c' ī0 i)
        (List.mem_map.mpr ⟨i, List.mem_finRange i, by simp [hij]⟩)
      exact (updatePinCoordFormula_sat P c c' ī0 i w pb i_marks (hpbv i)).mp hpiece
    have hpb_eq : pb = Function.update ī0 j0 (pb j0) := by
      funext i
      by_cases hij : i = j0
      · subst i
        simp [Function.update]
      · simp [Function.update, hij, hpin i hij]
    have hsel : P.toPoly.sel c' w (Function.update ī0 j0 (pb j0)) := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hsel1
      have hs := ((P.toPoly.selDef c').choose_spec w pb).mpr hsel1
      rw [← hpb_eq]
      exact hs
    have hlab : P.toPoly.label c' w (Function.update ī0 j0 (pb j0)) = D := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hlab1
      have hl := ((P.toPoly.labelDef c' D).choose_spec w pb).mpr hlab1
      rw [← hpb_eq]
      exact hl
    have hord := h (pb j0) (hpbv j0) ⟨hguard, hsel, hlab⟩
    rw [SliceFasGates.sat_relabelFO]
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' pb i_marks
    refine ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO pb i_marks) ∘ gordNB P c c')).mp ?_
    simp only [hg1, hg2]
    rw [hpb_eq]
    exact hord

/-- Update-shaped suffix run clause: all nonmoving competitor coordinates are
pinned to the fixed base tuple `ī0`; only `j0` ranges over the suffix
band/residue class. -/
noncomputable def updateSufOrdClauseAtBand
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) (k : ℕ)
    (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  SliceFasGatesGA.faFOs (P.toPoly.arity c') (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        if i = j0 then updateSufBandCoordFormula P c c' Q r hr k i
        else updatePinCoordFormula P c c' ī0 i)))
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

theorem updateSufOrdClauseAtBand_sat
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) (k : ℕ)
    (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ)
    (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ)
    (_hi : ∀ i, i_marks i < w.length) (hbase : ∀ i, ī0 i < w.length) :
    (updateSufOrdClauseAtBand P c c' Q r hr k j0 ī0).Sat w i_marks Fin.elim0 ↔
      ∀ p, p < w.length →
        (updateSufBandGuard w Q r k p
          ∧ P.toPoly.sel c' w (Function.update ī0 j0 p)
          ∧ P.toPoly.label c' w (Function.update ī0 j0 p) = D) →
        P.toPoly.ord c c' w i_marks (Function.update ī0 j0 p) := by
  rw [updateSufOrdClauseAtBand, SliceFasGatesGA.sat_faFOs]
  constructor
  · intro h p hp hcond
    obtain ⟨hguard, hsel, hlab⟩ := hcond
    let xb : Fin (P.toPoly.arity c') → ℕ := Function.update ī0 j0 p
    have hxbv : ∀ i, xb i < w.length := by
      intro i
      by_cases hij : i = j0
      · subst i
        simp [xb, hp]
      · simp [xb, hij, hbase i]
    have hsat := h xb hxbv
    rw [SliceFasGates.sat_imp] at hsat
    have hord := hsat (by
      rw [MSO.Formula.sat_and]
      refine ⟨?_, ?_⟩
      · rw [MSOMarkN.sat_andList]
        intro ψ hψ
        obtain ⟨i, _himem, rfl⟩ := List.mem_map.mp hψ
        by_cases hij : i = j0
        · simp only [if_pos hij]
          subst i
          exact (updateSufBandCoordFormula_sat P c c' Q r hr k j0 w xb
            i_marks (hxbv j0)).mpr (by simpa [xb] using hguard)
        · simp only [if_neg hij]
          exact (updatePinCoordFormula_sat P c c' ī0 i w xb i_marks (hxbv i)).mpr
            (by simp [xb, hij])
      · rw [MSO.Formula.sat_and]
        refine ⟨?_, ?_⟩
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.selDef c').choose_spec w xb).mp (by simpa [xb] using hsel)
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.labelDef c' D).choose_spec w xb).mp (by simpa [xb] using hlab))
    rw [SliceFasGates.sat_relabelFO] at hord
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' xb i_marks
    have hfinal := ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO xb i_marks) ∘ gordNB P c c')).mpr hord
    simp only [hg1, hg2] at hfinal
    simpa [xb] using hfinal
  · intro h pb hpbv
    rw [SliceFasGates.sat_imp]
    intro hprem
    rw [MSO.Formula.sat_and] at hprem
    obtain ⟨hdec, hsl⟩ := hprem
    rw [MSO.Formula.sat_and] at hsl
    obtain ⟨hsel1, hlab1⟩ := hsl
    have hguard : updateSufBandGuard w Q r k (pb j0) := by
      rw [MSOMarkN.sat_andList] at hdec
      have hpiece := hdec (updateSufBandCoordFormula P c c' Q r hr k j0)
        (List.mem_map.mpr ⟨j0, List.mem_finRange j0, by simp⟩)
      simpa using
        (updateSufBandCoordFormula_sat P c c' Q r hr k j0 w pb i_marks
          (hpbv j0)).mp hpiece
    have hpin : ∀ i, i ≠ j0 → pb i = ī0 i := by
      intro i hij
      rw [MSOMarkN.sat_andList] at hdec
      have hpiece := hdec (updatePinCoordFormula P c c' ī0 i)
        (List.mem_map.mpr ⟨i, List.mem_finRange i, by simp [hij]⟩)
      exact (updatePinCoordFormula_sat P c c' ī0 i w pb i_marks (hpbv i)).mp hpiece
    have hpb_eq : pb = Function.update ī0 j0 (pb j0) := by
      funext i
      by_cases hij : i = j0
      · subst i
        simp [Function.update]
      · simp [Function.update, hij, hpin i hij]
    have hsel : P.toPoly.sel c' w (Function.update ī0 j0 (pb j0)) := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hsel1
      have hs := ((P.toPoly.selDef c').choose_spec w pb).mpr hsel1
      rw [← hpb_eq]
      exact hs
    have hlab : P.toPoly.label c' w (Function.update ī0 j0 (pb j0)) = D := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hlab1
      have hl := ((P.toPoly.labelDef c' D).choose_spec w pb).mpr hlab1
      rw [← hpb_eq]
      exact hl
    have hord := h (pb j0) (hpbv j0) ⟨hguard, hsel, hlab⟩
    rw [SliceFasGates.sat_relabelFO]
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' pb i_marks
    refine ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO pb i_marks) ∘ gordNB P c c')).mp ?_
    simp only [hg1, hg2]
    rw [hpb_eq]
    exact hord

/-- Total (clamped `r ↦ r % Q`) update-shaped suffix band clause. -/
noncomputable def updateSufOrdClauseAtBandTot
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hQ : 0 < Q) (k : ℕ)
    (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  updateSufOrdClauseAtBand P c c' Q (r % Q) (Nat.mod_lt r hQ) k j0 ī0

theorem updateSufOrdClauseAtBandTot_sat
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hQ : 0 < Q) (k : ℕ)
    (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ)
    (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ)
    (hi : ∀ i, i_marks i < w.length) (hbase : ∀ i, ī0 i < w.length) :
    (updateSufOrdClauseAtBandTot P c c' Q r hQ k j0 ī0).Sat w i_marks Fin.elim0 ↔
      ∀ p, p < w.length →
        (updateSufBandGuard w Q (r % Q) k p
          ∧ P.toPoly.sel c' w (Function.update ī0 j0 p)
          ∧ P.toPoly.label c' w (Function.update ī0 j0 p) = D) →
        P.toPoly.ord c c' w i_marks (Function.update ī0 j0 p) :=
  updateSufOrdClauseAtBand_sat P c c' Q (r % Q) (Nat.mod_lt r hQ) k j0 ī0
    w i_marks hi hbase

/-! ## Update-shaped banded prefix run clause -/

/-- Coordinate formula for the moving coordinate of an update-shaped prefix
run clause. -/
noncomputable def updatePreBandCoordFormula
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) (k : ℕ) (i : Fin (P.toPoly.arity c')) :
    MSO.Formula Step (P.toPoly.arity c + P.toPoly.arity c') 0 :=
  MSO.Formula.and
    (MSO.Formula.and
      (SliceFasGates.relabelFO (targetCoordFO P c c' i) inInitialURun)
      (SliceFasGates.relabelFO (targetCoordFO P c c' i)
        (SliceFasGates.mso_position_mod Q r hr).choose))
    (MSO.Formula.and
      (SliceFasGates.relabelFO (targetCoordFO P c c' i) (bandLoPre k))
      (SliceFasGates.relabelFO (targetCoordFO P c c' i) strictInitialStretch))

theorem updatePreBandCoordFormula_sat
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) (k : ℕ) (i : Fin (P.toPoly.arity c'))
    (w : List Step) (xb : Fin (P.toPoly.arity c') → ℕ)
    (i_marks : Fin (P.toPoly.arity c) → ℕ) (hxb : xb i < w.length) :
    (updatePreBandCoordFormula P c c' Q r hr k i).Sat w
        (SliceFasGatesGA.appFO xb i_marks) Fin.elim0 ↔
      preBandStrictGuard w Q r k (xb i) := by
  have hv0 :
      (SliceFasGatesGA.appFO xb i_marks) ∘ targetCoordFO P c c' i =
        fun _ => xb i := by
    funext _
    exact SliceFasGatesGA.appFO_low xb i_marks i.1 (by have := i.2; omega)
      (by have := i.2; omega)
  rw [updatePreBandCoordFormula, preBandStrictGuard, MSO.Formula.sat_and,
    MSO.Formula.sat_and, MSO.Formula.sat_and, SliceFasGates.sat_relabelFO,
    SliceFasGates.sat_relabelFO, SliceFasGates.sat_relabelFO,
    SliceFasGates.sat_relabelFO, sat_inInitialURun, hv0,
    (SliceFasGates.mso_position_mod Q r hr).choose_spec w (xb i) hxb,
    sat_bandLoPre k w (xb i) hxb, sat_strictInitialStretch w (xb i)]

/-- Update-shaped prefix run clause: all nonmoving competitor coordinates are
pinned to the fixed base tuple `ī0`; only `j0` ranges over the prefix
band/residue class. -/
noncomputable def updatePreOrdClauseAtBand
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) (k : ℕ)
    (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  SliceFasGatesGA.faFOs (P.toPoly.arity c') (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        if i = j0 then updatePreBandCoordFormula P c c' Q r hr k i
        else updatePinCoordFormula P c c' ī0 i)))
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

theorem updatePreOrdClauseAtBand_sat
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hr : r < Q) (k : ℕ)
    (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ)
    (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ)
    (_hi : ∀ i, i_marks i < w.length) (hbase : ∀ i, ī0 i < w.length) :
    (updatePreOrdClauseAtBand P c c' Q r hr k j0 ī0).Sat w i_marks Fin.elim0 ↔
      ∀ p, p < w.length →
        (preBandStrictGuard w Q r k p
          ∧ P.toPoly.sel c' w (Function.update ī0 j0 p)
          ∧ P.toPoly.label c' w (Function.update ī0 j0 p) = D) →
        P.toPoly.ord c c' w i_marks (Function.update ī0 j0 p) := by
  rw [updatePreOrdClauseAtBand, SliceFasGatesGA.sat_faFOs]
  constructor
  · intro h p hp hcond
    obtain ⟨hguard, hsel, hlab⟩ := hcond
    let xb : Fin (P.toPoly.arity c') → ℕ := Function.update ī0 j0 p
    have hxbv : ∀ i, xb i < w.length := by
      intro i
      by_cases hij : i = j0
      · subst i
        simp [xb, hp]
      · simp [xb, hij, hbase i]
    have hsat := h xb hxbv
    rw [SliceFasGates.sat_imp] at hsat
    have hord := hsat (by
      rw [MSO.Formula.sat_and]
      refine ⟨?_, ?_⟩
      · rw [MSOMarkN.sat_andList]
        intro ψ hψ
        obtain ⟨i, _himem, rfl⟩ := List.mem_map.mp hψ
        by_cases hij : i = j0
        · simp only [if_pos hij]
          subst i
          exact (updatePreBandCoordFormula_sat P c c' Q r hr k j0 w xb
            i_marks (hxbv j0)).mpr (by simpa [xb] using hguard)
        · simp only [if_neg hij]
          exact (updatePinCoordFormula_sat P c c' ī0 i w xb i_marks (hxbv i)).mpr
            (by simp [xb, hij])
      · rw [MSO.Formula.sat_and]
        refine ⟨?_, ?_⟩
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.selDef c').choose_spec w xb).mp (by simpa [xb] using hsel)
        · rw [SliceFasGates.sat_relabelFO, comp_embNB]
          exact ((P.toPoly.labelDef c' D).choose_spec w xb).mp (by simpa [xb] using hlab))
    rw [SliceFasGates.sat_relabelFO] at hord
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' xb i_marks
    have hfinal := ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO xb i_marks) ∘ gordNB P c c')).mpr hord
    simp only [hg1, hg2] at hfinal
    simpa [xb] using hfinal
  · intro h pb hpbv
    rw [SliceFasGates.sat_imp]
    intro hprem
    rw [MSO.Formula.sat_and] at hprem
    obtain ⟨hdec, hsl⟩ := hprem
    rw [MSO.Formula.sat_and] at hsl
    obtain ⟨hsel1, hlab1⟩ := hsl
    have hguard : preBandStrictGuard w Q r k (pb j0) := by
      rw [MSOMarkN.sat_andList] at hdec
      have hpiece := hdec (updatePreBandCoordFormula P c c' Q r hr k j0)
        (List.mem_map.mpr ⟨j0, List.mem_finRange j0, by simp⟩)
      simpa using
        (updatePreBandCoordFormula_sat P c c' Q r hr k j0 w pb i_marks
          (hpbv j0)).mp hpiece
    have hpin : ∀ i, i ≠ j0 → pb i = ī0 i := by
      intro i hij
      rw [MSOMarkN.sat_andList] at hdec
      have hpiece := hdec (updatePinCoordFormula P c c' ī0 i)
        (List.mem_map.mpr ⟨i, List.mem_finRange i, by simp [hij]⟩)
      exact (updatePinCoordFormula_sat P c c' ī0 i w pb i_marks (hpbv i)).mp hpiece
    have hpb_eq : pb = Function.update ī0 j0 (pb j0) := by
      funext i
      by_cases hij : i = j0
      · subst i
        simp [Function.update]
      · simp [Function.update, hij, hpin i hij]
    have hsel : P.toPoly.sel c' w (Function.update ī0 j0 (pb j0)) := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hsel1
      have hs := ((P.toPoly.selDef c').choose_spec w pb).mpr hsel1
      rw [← hpb_eq]
      exact hs
    have hlab : P.toPoly.label c' w (Function.update ī0 j0 (pb j0)) = D := by
      rw [SliceFasGates.sat_relabelFO, comp_embNB] at hlab1
      have hl := ((P.toPoly.labelDef c' D).choose_spec w pb).mpr hlab1
      rw [← hpb_eq]
      exact hl
    have hord := h (pb j0) (hpbv j0) ⟨hguard, hsel, hlab⟩
    rw [SliceFasGates.sat_relabelFO]
    obtain ⟨hg1, hg2⟩ := comp_gordNB P c c' pb i_marks
    refine ((P.toPoly.ordDef c c').choose_spec w
      ((SliceFasGatesGA.appFO pb i_marks) ∘ gordNB P c c')).mp ?_
    simp only [hg1, hg2]
    rw [hpb_eq]
    exact hord

/-- Total (clamped `r ↦ r % Q`) update-shaped prefix band clause. -/
noncomputable def updatePreOrdClauseAtBandTot
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hQ : 0 < Q) (k : ℕ)
    (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  updatePreOrdClauseAtBand P c c' Q (r % Q) (Nat.mod_lt r hQ) k j0 ī0

theorem updatePreOrdClauseAtBandTot_sat
    (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (Q r : ℕ) (hQ : 0 < Q) (k : ℕ)
    (j0 : Fin (P.toPoly.arity c')) (ī0 : Fin (P.toPoly.arity c') → ℕ)
    (w : List Step) (i_marks : Fin (P.toPoly.arity c) → ℕ)
    (hi : ∀ i, i_marks i < w.length) (hbase : ∀ i, ī0 i < w.length) :
    (updatePreOrdClauseAtBandTot P c c' Q r hQ k j0 ī0).Sat w i_marks Fin.elim0 ↔
      ∀ p, p < w.length →
        (preBandStrictGuard w Q (r % Q) k p
          ∧ P.toPoly.sel c' w (Function.update ī0 j0 p)
          ∧ P.toPoly.label c' w (Function.update ī0 j0 p) = D) →
        P.toPoly.ord c c' w i_marks (Function.update ī0 j0 p) :=
  updatePreOrdClauseAtBand_sat P c c' Q (r % Q) (Nat.mod_lt r hQ) k j0 ī0
    w i_marks hi hbase

end CopiedBandRunGate
