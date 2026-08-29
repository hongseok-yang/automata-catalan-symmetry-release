/-
# The deep (from-end) atomOrd gate (§9 single-gate selector-mS, the FROM-END component)

The decoupled mS-direction selector realises the CORE gate only for SHALLOW achievers (depth
`l < q_D`).  A nonzero-slope final-`D`-run whose DEEP endpoint is the global `d*`-min is a genuine
selected-`D` achiever at depth `l ∈ [Nc, mS-2]`, lying in no slope-0 tying class, so neither the CORE
gate nor the per-residue-class run clauses force `atomOrd`-precedence to it.  The missing FROM-END
component is one clause per from-end offset `k`, pinning the single position `|w| - 1 - k` (via
`SliceFasGates.mso_position_fromEnd`) in place of the residue-class guard used by the run clauses of
`CopiedSufRunGate`.

What survives here is the *prefix* half of that construction: `mso_position_beforeFirstD`, the
MSO predicate pinning "`p + k` is the first `D`".  The deep-prefix cell `.inr (.inr i_off)` sits near
the end of the initial `U`-run, at `firstD - (i_off + 2)`, so it is anchored at the first `D` rather
than at the word end.
-/import RequestProject.CopiedSufRunGate

namespace CopiedDeepRunGate

open Step MSO

/-! ## The PREFIX deep twin (the initial `U^mS`-run, anchored at the first `D`)

The deep-prefix cell `.inr (.inr i_off)` sits at position `mS-1-i_off`, near the END of the initial
U-run — which for `n ≥ 1` is exactly `firstD - (i_off+2)` (the first `D` is at position `mS+1`).  So,
unlike the suffix (anchored at the word end via `SliceFasGates.mso_position_fromEnd`), the deep-prefix
is anchored at the FIRST `D`.  `mso_position_beforeFirstD k` pins "`p+k` is the first `D`"; the
deep-prefix competitor at offset `i_off` is captured at `k = i_off + 2`. -/

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

end CopiedDeepRunGate
