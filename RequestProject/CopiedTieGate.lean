/-
# The fibred TIE gate (§9 tower, Stage F3.6) — the landmark clause layer

The hybrid gate of decision D2 handles bulk equal-rank `D`-cells by *landmark-relative* clauses,
built on the F3.5 landmark decoder (`CopiedLandmark`).  This file supplies that layer:

* `offsetForm3` — the 3-slot fixed-difference gadget (slots `0 = z`, `1 = yF`, `2 = yL`) the
  landmark position-cell clause is assembled from;
* `cfgPosL` / `cfgPosFormulaL` / `sat_cfgPosFormulaL` / `cfgPosL_base` — the landmark position-cell
  predicate, its MSO formula, the satisfaction characterisation, and its value at the cell base;
* the `ClauseMk` address maps (`decAddrMk`, `eqAddrMk`, `gordLMk`, `embAddrMk`, `cfgAddrMk`) for the
  sigma-marked variant of the clause.
-/
import RequestProject.CopiedLandmark
import RequestProject.CopiedGateEP

namespace CopiedTieGate

open WRP SliceFamilyCell CopiedLandmark
open scoped Classical

/-! ## The bulk landmark clause — supporting layer

`offsetForm3` is the 3-slot fixed-difference gadget (slots `0 = z`, `1 = yF`, `2 = yL`)
used by the landmark position-cell clause, over the clause's `(Kc' + 3)`-binder block
(the `D`-tuple, base `z`, and the two landmarks `yF`/`yL`). -/

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

/-! ## The sigma-marked bulk clause (Design B — mixed cells)

A core-only clause cannot express `atomOrd` against MIXED cells (some coordinates on a middle
cluster, others in the far prefix/suffix stretches): the stretch coordinates carry unbounded
positions that no finite `RegionSpec Bh` descriptor can hold.  The sigma-marked variant MARKS the
stretch coordinates (the `sigma` slots, supplied at FIXED `t`-independent positions) and DECODES only
the non-`sigma` core coordinates via `regionDecodeL`.  The machine marks the combined
`arity c + arity c'` tuple: the first `arity c` are the `U`-atom marks, the next `arity c'` the
`D`-atom marks (only the `sigma` ones matter; the rest are pinned to the decode and their marks
ignored).  The address maps below lay out that binder block. -/

section ClauseMk

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

end ClauseMk

end CopiedTieGate
