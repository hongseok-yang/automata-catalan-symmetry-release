/-
# Tight Targets and the Forced Triangular Profile

Formalization of Lemmas 7.3–7.5 of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.
-/
import RequestProject.TriangularDecomp
import RequestProject.WrappedFlat

open Step

/-! ## Tight paths -/

/-- **`lem:deficit-zero-targets` (paper.tex).**
A Dyck path is *tight* if `dinv(Q) = coarea(Q)`, the extreme case of
the general inequality `dinv ≤ coarea`. -/
noncomputable def IsTight (Q : List Step) : Prop :=
  (dinv Q : ℤ) = coarea Q

/-! ## Tight ⟺ every column attains its `dinv ≤ coarea` bound with equality

`dinv = ∑_j #partners(j)` and `#partners(j) ≤ j - a_j` for every column `j`
(`dinv_column_bound`), with `∑_j (j - a_j) = coarea`.  So `dinv = coarea` holds
iff every per-column bound is attained with equality. -/

open Finset in
/-- The number of dinv partners of column `j`: earlier columns `i < j` whose area
entry exceeds `a_j` by `0` or `1`. -/
noncomputable def numPartners (P : List Step) (j : Fin (areaSeq P).length) : ℕ :=
  #{i : Fin (areaSeq P).length | (i : ℕ) < (j : ℕ) ∧
      ((areaSeq P)[(i : ℕ)] - (areaSeq P)[(j : ℕ)] = 0 ∨
       (areaSeq P)[(i : ℕ)] - (areaSeq P)[(j : ℕ)] = 1)}

/-- `dinv` is the sum of per-column partner counts (integer form). -/
theorem dinv_eq_sum_numPartners (P : List Step) :
    (dinv P : ℤ) = ∑ j : Fin (areaSeq P).length, (numPartners P j : ℤ) := by
  rw [dinv_eq_sum_card]; push_cast; rfl

/-- The per-column bound `#partners(j) ≤ j - a_j` (restated via `numPartners`). -/
theorem numPartners_le (P : List Step) (hP : IsDyckPath P)
    (j : Fin (areaSeq P).length) :
    (numPartners P j : ℤ) ≤ (j : ℕ) - (areaSeq P)[(j : ℕ)] :=
  dinv_column_bound P hP j

/-- The column-bound totals `∑_j (j - a_j) = coarea`. -/
theorem sum_sub_areaSeq_eq_coarea (P : List Step) (hP : IsDyckPath P) :
    ∑ j : Fin (areaSeq P).length, (((j : ℕ) : ℤ) - (areaSeq P)[(j : ℕ)]) = coarea P := by
  have hlen : (areaSeq P).length = semilength P := length_areaSeq_eq_semilength P hP
  rw [Finset.sum_sub_distrib, sum_fin_areaSeq P, sum_fin_cast_int, hlen]
  rfl

open Finset in
/-- **Tightness criterion.**  A Dyck path is tight iff every column attains its
`dinv ≤ coarea` bound with equality. -/
theorem isTight_iff_columns (Q : List Step) (hQ : IsDyckPath Q) :
    IsTight Q ↔ ∀ j : Fin (areaSeq Q).length,
      (numPartners Q j : ℤ) = ((j : ℕ) : ℤ) - (areaSeq Q)[(j : ℕ)] := by
  rw [IsTight, dinv_eq_sum_numPartners Q, ← sum_sub_areaSeq_eq_coarea Q hQ,
    Finset.sum_eq_sum_iff_of_le (fun j _ => numPartners_le Q hQ j)]
  simp

/-! ## Structure of the canonical area sequence `canonAreaSeq` -/

/-- The value of `canonAreaSeq a b d` at index `i`: the staircase value `i`,
then the plateau value `a-1`, then the tail value `a-2`. -/
def canonVal (a b d i : ℕ) : ℤ :=
  if i < a then (i : ℤ) else if i < a + (b - d) then (a : ℤ) - 1 else (a : ℤ) - 2

/-- Length of the canonical area sequence. -/
theorem length_canonAreaSeq (a b d : ℕ) (hd : d ≤ b) :
    (canonAreaSeq a b d).length = a + b := by
  unfold canonAreaSeq
  simp only [List.length_append, List.length_map, List.length_replicate, List.length_range]
  omega

/-- The `getElem?` form of the entry description (no dependent proof terms). -/
theorem getElem?_canonAreaSeq (a b d : ℕ) (i : ℕ) (hi : i < a + b) :
    (canonAreaSeq a b d)[i]? = some (canonVal a b d i) := by
  unfold canonAreaSeq canonVal
  have hsl : ((List.range a).map (fun (i : ℕ) => (i : ℤ))).length = a := by simp
  have hpl : (List.replicate (b - d) ((a : ℤ) - 1)).length = b - d := by simp
  by_cases h1 : i < a
  · rw [if_pos h1,
      List.getElem?_append_left (by rw [List.length_append, hsl, hpl]; omega),
      List.getElem?_append_left (by rw [hsl]; exact h1)]
    rw [List.getElem?_map, List.getElem?_range h1]; rfl
  · rw [if_neg h1]
    by_cases h2 : i < a + (b - d)
    · rw [if_pos h2,
        List.getElem?_append_left (by rw [List.length_append, hsl, hpl]; omega),
        List.getElem?_append_right (by rw [hsl]; omega), hsl,
        List.getElem?_replicate, if_pos (by omega)]
    · rw [if_neg h2,
        List.getElem?_append_right (by rw [List.length_append, hsl, hpl]; omega),
        List.length_append, hsl, hpl, List.getElem?_replicate, if_pos (by omega)]

/-- **Entry-by-entry description of the canonical area sequence.** -/
theorem getElem_canonAreaSeq (a b d : ℕ) (hd : d ≤ b) (i : ℕ) (hi : i < a + b) :
    (canonAreaSeq a b d)[i]'(by rw [length_canonAreaSeq a b d hd]; exact hi)
      = canonVal a b d i := by
  have hi' : i < (canonAreaSeq a b d).length := by rw [length_canonAreaSeq a b d hd]; exact hi
  have h := getElem?_canonAreaSeq a b d i hi
  rw [List.getElem?_eq_getElem hi'] at h
  exact Option.some_inj.mp h

/-- `canonAreaSeq` entries are nonnegative (given `a ≥ 1` and the edge condition). -/
theorem canonVal_nonneg (a b d i : ℕ) (ha : 1 ≤ a) (hedge : 2 ≤ a ∨ d = 0)
    (hi : i < a + b) : 0 ≤ canonVal a b d i := by
  unfold canonVal; split_ifs <;> omega

/-- The `toNat` of a `canonAreaSeq` value is at most its index. -/
theorem canonVal_toNat_le (a b d i : ℕ) (_hi : i < a + b) :
    (canonVal a b d i).toNat ≤ i := by
  unfold canonVal; split_ifs <;> omega

/-- **Partner characterisation.**  In the canonical area sequence, an earlier
column `i < j` is a dinv partner of `j` (its value exceeds `a_j` by `0` or `1`)
exactly when `i ≥ a_j` as a natural number. -/
theorem canon_partner_iff (a b d : ℕ) (ha : 1 ≤ a) (_hd : d ≤ b) (_hedge : 2 ≤ a ∨ d = 0)
    (i j : ℕ) (hij : i < j) (_hj : j < a + b) :
    (canonVal a b d i - canonVal a b d j = 0 ∨ canonVal a b d i - canonVal a b d j = 1)
      ↔ (canonVal a b d j).toNat ≤ i := by
  unfold canonVal; split_ifs <;> omega

/-- The number of `Fin n` indices in the half-open interval `[lo, hi)` is `hi - lo`
(when `hi ≤ n`). -/
theorem card_filter_Fin_Ico (n lo hi : ℕ) (hhi : hi ≤ n) :
    (Finset.filter (fun i : Fin n => lo ≤ (i : ℕ) ∧ (i : ℕ) < hi) Finset.univ).card
      = hi - lo := by
  rw [← Finset.card_image_of_injective _ Fin.val_injective, ← Nat.card_Ico lo hi]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
  constructor
  · rintro ⟨i, ⟨hlo, hhi'⟩, rfl⟩; exact ⟨hlo, hhi'⟩
  · rintro ⟨hlo, hx⟩; exact ⟨⟨x, by omega⟩, ⟨hlo, hx⟩, rfl⟩

/-! ## Existence: the canonical path is tight -/

open Finset in
/-- **Column equality (COL-EQ).**  For a Dyck path whose area sequence is the
canonical one, every column attains its `dinv ≤ coarea` bound with equality:
`#partners(j) = j - a_j`.  The partners of `j` are exactly the indices in
`[a_j, j)`. -/
theorem numPartners_canon (P : List Step) (a b d : ℕ)
    (ha : 1 ≤ a) (hd : d ≤ b) (hedge : 2 ≤ a ∨ d = 0)
    (heq : areaSeq P = canonAreaSeq a b d)
    (j : Fin (areaSeq P).length) :
    (numPartners P j : ℤ) = ((j : ℕ) : ℤ) - (areaSeq P)[(j : ℕ)] := by
  have hlen : (areaSeq P).length = a + b := by rw [heq, length_canonAreaSeq a b d hd]
  have hval : ∀ k (hk : k < (areaSeq P).length), (areaSeq P)[k]'hk = canonVal a b d k := by
    intro k hk
    have hk' : k < a + b := hlen ▸ hk
    have e1 : (areaSeq P)[k]? = (canonAreaSeq a b d)[k]? := by rw [heq]
    rw [List.getElem?_eq_getElem hk, getElem?_canonAreaSeq a b d k hk'] at e1
    exact Option.some_inj.mp e1
  have hjlt : (j : ℕ) < a + b := hlen ▸ j.isLt
  have haj : (areaSeq P)[(j : ℕ)] = canonVal a b d (j : ℕ) := hval _ _
  -- The partner filter set is the index interval `[a_j, j)`.
  have hset : (Finset.filter (fun i : Fin (areaSeq P).length =>
        (i : ℕ) < (j : ℕ) ∧ ((areaSeq P)[(i : ℕ)] - (areaSeq P)[(j : ℕ)] = 0 ∨
          (areaSeq P)[(i : ℕ)] - (areaSeq P)[(j : ℕ)] = 1)) Finset.univ)
      = Finset.filter (fun i : Fin (areaSeq P).length =>
          (canonVal a b d (j : ℕ)).toNat ≤ (i : ℕ) ∧ (i : ℕ) < (j : ℕ)) Finset.univ := by
    apply Finset.filter_congr
    intro i _
    rw [hval (i : ℕ) i.isLt, haj]
    constructor
    · rintro ⟨hij, hp⟩
      exact ⟨(canon_partner_iff a b d ha hd hedge (i : ℕ) (j : ℕ) hij hjlt).mp hp, hij⟩
    · rintro ⟨hle, hij⟩
      exact ⟨hij, (canon_partner_iff a b d ha hd hedge (i : ℕ) (j : ℕ) hij hjlt).mpr hle⟩
  have hnp : numPartners P j = (j : ℕ) - (canonVal a b d (j : ℕ)).toNat := by
    rw [numPartners, hset,
      card_filter_Fin_Ico (areaSeq P).length (canonVal a b d (j : ℕ)).toNat (j : ℕ)
        (le_of_lt j.isLt)]
  rw [haj, hnp,
    Nat.cast_sub (canonVal_toNat_le a b d (j : ℕ) hjlt),
    Int.toNat_of_nonneg (canonVal_nonneg a b d (j : ℕ) ha hedge hjlt)]

/-- The canonical path is **tight**. -/
theorem isTight_of_areaSeq_canon (P : List Step) (a b d : ℕ)
    (hP : IsDyckPath P) (ha : 1 ≤ a) (hd : d ≤ b) (hedge : 2 ≤ a ∨ d = 0)
    (heq : areaSeq P = canonAreaSeq a b d) :
    IsTight P :=
  (isTight_iff_columns P hP).mpr (fun j => numPartners_canon P a b d ha hd hedge heq j)

/-! ## The dinv/coarea value of the canonical path is `c` -/

/-- Gauss over `Finset.range`, doubled (cast to `ℤ`). -/
theorem two_mul_sum_range_id (a : ℕ) :
    2 * ∑ i ∈ Finset.range a, (i : ℤ) = (a : ℤ) * ((a : ℤ) - 1) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => (i : ℤ)) a]
  exact two_mul_sum_fin_int a

/-- **Twice the area of a canonical path**, as a division-free polynomial.  Computed
by splitting `area = ∑ canonVal` over the three regions `[0,a)`, `[a,a+(b-d))`,
`[a+(b-d),a+b)`. -/
theorem two_mul_area_canon (P : List Step) (a b d : ℕ)
    (hd : d ≤ b) (heq : areaSeq P = canonAreaSeq a b d) :
    2 * area P = (a : ℤ) * ((a : ℤ) - 1)
      + 2 * ((b - d : ℕ) : ℤ) * ((a : ℤ) - 1) + 2 * (d : ℤ) * ((a : ℤ) - 2) := by
  have hlen : (areaSeq P).length = a + b := by rw [heq, length_canonAreaSeq a b d hd]
  have hval : ∀ k (hk : k < (areaSeq P).length), (areaSeq P)[k]'hk = canonVal a b d k := by
    intro k hk
    have hk' : k < a + b := hlen ▸ hk
    have e1 : (areaSeq P)[k]? = (canonAreaSeq a b d)[k]? := by rw [heq]
    rw [List.getElem?_eq_getElem hk, getElem?_canonAreaSeq a b d k hk'] at e1
    exact Option.some_inj.mp e1
  have harea : area P = ∑ i ∈ Finset.range (a + b), canonVal a b d i := by
    rw [← sum_fin_areaSeq P,
      Finset.sum_congr rfl (fun (j : Fin (areaSeq P).length) _ => hval (j : ℕ) j.isLt),
      Fin.sum_univ_eq_sum_range (fun i => canonVal a b d i) (areaSeq P).length, hlen]
  have hP1 : ∑ i ∈ Finset.Ico 0 a, canonVal a b d i = ∑ i ∈ Finset.range a, (i : ℤ) := by
    rw [← Finset.range_eq_Ico]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi; unfold canonVal; rw [if_pos hi]
  have hP2 : ∑ i ∈ Finset.Ico a (a + (b - d)), canonVal a b d i
      = ((b - d : ℕ) : ℤ) * ((a : ℤ) - 1) := by
    have hc : ∀ i ∈ Finset.Ico a (a + (b - d)), canonVal a b d i = (a : ℤ) - 1 := by
      intro i hi; rw [Finset.mem_Ico] at hi; unfold canonVal
      rw [if_neg (by omega), if_pos (by omega)]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
      nsmul_eq_mul]
  have hP3 : ∑ i ∈ Finset.Ico (a + (b - d)) (a + b), canonVal a b d i
      = (d : ℤ) * ((a : ℤ) - 2) := by
    have hc : ∀ i ∈ Finset.Ico (a + (b - d)) (a + b), canonVal a b d i = (a : ℤ) - 2 := by
      intro i hi; rw [Finset.mem_Ico] at hi; unfold canonVal
      rw [if_neg (by omega), if_neg (by omega)]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico,
      show a + b - (a + (b - d)) = d by omega, nsmul_eq_mul]
  rw [harea, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (fun i => canonVal a b d i) (Nat.zero_le a)
      (by omega : a ≤ a + b),
    ← Finset.sum_Ico_consecutive (fun i => canonVal a b d i) (by omega : a ≤ a + (b - d))
      (by omega : a + (b - d) ≤ a + b),
    hP1, hP2, hP3, mul_add, mul_add, two_mul_sum_range_id]
  ring

/-- **`2·coarea = b(b+1) + 2d`** for a canonical path (division-free form). -/
theorem two_mul_coarea_canon (P : List Step) (a b d : ℕ)
    (hP : IsDyckPath P) (hd : d ≤ b)
    (heq : areaSeq P = canonAreaSeq a b d) :
    2 * coarea P = (b : ℤ) * ((b : ℤ) + 1) + 2 * (d : ℤ) := by
  have hsl : semilength P = a + b := by
    rw [← length_areaSeq_eq_semilength P hP, heq, length_canonAreaSeq a b d hd]
  have harea : (2 : ℤ) * area P
      = (a : ℤ) * ((a : ℤ) - 1)
        + 2 * ((b - d : ℕ) : ℤ) * ((a : ℤ) - 1) + 2 * (d : ℤ) * ((a : ℤ) - 2) :=
    two_mul_area_canon P a b d hd heq
  set m : ℤ := ((a + b : ℕ) : ℤ) with hm
  have hXeven : (2 : ℤ) ∣ m * (m - 1) := by
    have h := (Int.even_mul_succ_self (m - 1)).two_dvd
    have he : (m - 1) * (m - 1 + 1) = m * (m - 1) := by ring
    rwa [he] at h
  have hco : coarea P = m * (m - 1) / 2 - area P := by
    show (↑(semilength P) : ℤ) * ((↑(semilength P) : ℤ) - 1) / 2 - area P = _
    rw [hsl, ← hm]
  rw [hco, mul_sub, mul_comm (2 : ℤ) (m * (m - 1) / 2), Int.ediv_mul_cancel hXeven,
    harea, hm, Nat.cast_sub hd]
  push_cast
  ring

/-! ## Uniqueness: the rigidity argument -/

/-- Each area-sequence entry is at most its index (`a_j ≤ j`). -/
theorem areaSeq_getElem_le_index (Q : List Step) (j : ℕ) (hj : j < (areaSeq Q).length) :
    (areaSeq Q)[j] ≤ (j : ℤ) := by
  rw [areaSeq_getElem_eq Q j hj]
  have hjU : j < (uPositions Q).length := by rwa [← length_areaSeq_eq_length_uPositions]
  have hj_le : j ≤ (uPositions Q)[j] := by
    have h1 := count_U_take_uPos Q j hjU
    have h2 : (Q.take ((uPositions Q)[j])).count U ≤ (Q.take ((uPositions Q)[j])).length :=
      List.count_le_length
    have h3 : (Q.take ((uPositions Q)[j])).length ≤ (uPositions Q)[j] := by
      rw [List.length_take]; omega
    omega
  omega

open Finset in
/-- **The equality conditions behind tightness.**  At a column `j` attaining
`#partners(j) = j - a_j`, every earlier entry is at most `a_j + 1` (no "high"
entries), and each level below `a_j` occurs at most once before `j`. -/
theorem tight_column (Q : List Step) (hQ : IsDyckPath Q)
    (j : Fin (areaSeq Q).length)
    (heq : (numPartners Q j : ℤ) = ((j : ℕ) : ℤ) - (areaSeq Q)[(j : ℕ)]) :
    (∀ i : Fin (areaSeq Q).length, (i : ℕ) < (j : ℕ) →
        (areaSeq Q)[(i : ℕ)] ≤ (areaSeq Q)[(j : ℕ)] + 1)
      ∧ (∀ i1 i2 : Fin (areaSeq Q).length, (i1 : ℕ) < (j : ℕ) → (i2 : ℕ) < (j : ℕ) →
          (areaSeq Q)[(i1 : ℕ)] < (areaSeq Q)[(j : ℕ)] →
          (areaSeq Q)[(i1 : ℕ)] = (areaSeq Q)[(i2 : ℕ)] → i1 = i2) := by
  have haj_nonneg : 0 ≤ (areaSeq Q)[(j : ℕ)] := by
    have := areaSeq_get_nonneg Q hQ ⟨(j : ℕ), j.isLt⟩
    rwa [List.get_eq_getElem] at this
  have haj_le : (areaSeq Q)[(j : ℕ)] ≤ ((j : ℕ) : ℤ) := areaSeq_getElem_le_index Q (j : ℕ) j.isLt
  set Counted := Finset.univ.filter (fun i : Fin (areaSeq Q).length =>
      (i : ℕ) < (j : ℕ) ∧ ((areaSeq Q)[(i : ℕ)] - (areaSeq Q)[(j : ℕ)] = 0 ∨
        (areaSeq Q)[(i : ℕ)] - (areaSeq Q)[(j : ℕ)] = 1)) with hCounted
  set Low := Finset.univ.filter (fun i : Fin (areaSeq Q).length =>
      (i : ℕ) < (j : ℕ) ∧ (areaSeq Q)[(i : ℕ)] < (areaSeq Q)[(j : ℕ)]) with hLow
  set Before := Finset.univ.filter (fun i : Fin (areaSeq Q).length => (i : ℕ) < (j : ℕ))
    with hBefore
  set f : Fin (areaSeq Q).length → ℕ := fun i => ((areaSeq Q)[(i : ℕ)]).toNat with hf
  have hdisj : Disjoint Low Counted := by
    rw [Finset.disjoint_left]; intro i hiL hiC
    rw [hLow, Finset.mem_filter] at hiL; rw [hCounted, Finset.mem_filter] at hiC
    obtain ⟨_, _, hL⟩ := hiL; obtain ⟨_, _, hC⟩ := hiC
    rcases hC with h | h <;> omega
  have hsubLC : Low ∪ Counted ⊆ Before := by
    apply Finset.union_subset
    · intro i hi; rw [hLow, Finset.mem_filter] at hi; rw [hBefore, Finset.mem_filter]
      exact ⟨hi.1, hi.2.1⟩
    · intro i hi; rw [hCounted, Finset.mem_filter] at hi; rw [hBefore, Finset.mem_filter]
      exact ⟨hi.1, hi.2.1⟩
  have hBefore_card : Before.card = (j : ℕ) := by
    rw [hBefore, Fin.card_filter_val_lt]; exact min_eq_right (le_of_lt j.isLt)
  have hclimb : Finset.range ((areaSeq Q)[(j : ℕ)]).toNat ⊆ Low.image f := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkz : (k : ℤ) < (areaSeq Q)[(j : ℕ)] := by
      have : (k : ℤ) < (((areaSeq Q)[(j : ℕ)]).toNat : ℤ) := by exact_mod_cast hk
      omega
    obtain ⟨i, hij, hi, hival⟩ := areaSeq_exists_lt_index Q (j : ℕ) j.isLt (k : ℤ) (by positivity) hkz
    refine Finset.mem_image.mpr ⟨⟨i, hi⟩, ?_, ?_⟩
    · rw [hLow, Finset.mem_filter]; refine ⟨Finset.mem_univ _, hij, ?_⟩
      show (areaSeq Q)[i] < (areaSeq Q)[(j : ℕ)]; rw [hival]; exact hkz
    · show ((areaSeq Q)[i]).toNat = k; rw [hival]; exact Int.toNat_natCast k
  have hLow_ge : ((areaSeq Q)[(j : ℕ)]).toNat ≤ Low.card :=
    le_trans (le_of_eq (Finset.card_range _).symm)
      (le_trans (Finset.card_le_card hclimb) Finset.card_image_le)
  have hajTN : ((areaSeq Q)[(j : ℕ)]).toNat ≤ (j : ℕ) := by
    have : (((areaSeq Q)[(j : ℕ)]).toNat : ℤ) ≤ ((j : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg haj_nonneg]; exact haj_le
    exact_mod_cast this
  have hCounted_nat : Counted.card = (j : ℕ) - ((areaSeq Q)[(j : ℕ)]).toNat := by
    have hc : (Counted.card : ℤ) = (((j : ℕ) - ((areaSeq Q)[(j : ℕ)]).toNat : ℕ) : ℤ) := by
      rw [Nat.cast_sub hajTN, Int.toNat_of_nonneg haj_nonneg]
      exact heq
    exact_mod_cast hc
  have hsum_le : Low.card + Counted.card ≤ (j : ℕ) := by
    rw [← hBefore_card, ← Finset.card_union_of_disjoint hdisj]; exact Finset.card_le_card hsubLC
  have hLow_card : Low.card = ((areaSeq Q)[(j : ℕ)]).toNat := by omega
  have hunion : Low ∪ Counted = Before := by
    apply Finset.eq_of_subset_of_card_le hsubLC
    rw [Finset.card_union_of_disjoint hdisj, hBefore_card]; omega
  refine ⟨?_, ?_⟩
  · intro i hij
    have hiB : i ∈ Before := by rw [hBefore, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hij⟩
    rw [← hunion, Finset.mem_union] at hiB
    rcases hiB with hiL | hiC
    · rw [hLow, Finset.mem_filter] at hiL; linarith [hiL.2.2]
    · rw [hCounted, Finset.mem_filter] at hiC; rcases hiC.2.2 with h | h <;> omega
  · intro i1 i2 hi1 hi2 hlt heqval
    have hi1L : i1 ∈ Low := by rw [hLow, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi1, hlt⟩
    have hi2L : i2 ∈ Low := by
      rw [hLow, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi2, heqval ▸ hlt⟩
    have hcard_eq : (Low.image f).card = Low.card := by
      have h1 : ((areaSeq Q)[(j : ℕ)]).toNat ≤ (Low.image f).card :=
        le_trans (le_of_eq (Finset.card_range _).symm) (Finset.card_le_card hclimb)
      have h2 : (Low.image f).card ≤ Low.card := Finset.card_image_le
      omega
    have hinj : Set.InjOn f Low := Finset.injOn_of_card_image_eq hcard_eq
    refine hinj hi1L hi2L ?_
    show ((areaSeq Q)[(i1 : ℕ)]).toNat = ((areaSeq Q)[(i2 : ℕ)]).toNat
    rw [heqval]

/-- A list whose entries lie in `{x, y}` and in which `y` is "absorbing"
(once an entry is `y`, every later entry is `y`) is a block of `x`'s followed by a
block of `y`'s. -/
theorem mono_two_value_eq {α : Type*} (l : List α) (x y : α)
    (hmem : ∀ a ∈ l, a = x ∨ a = y)
    (hmono : ∀ i j (hj : j < l.length) (_ : i < j), l[i]'(by omega) = y → l[j] = y) :
    ∃ p, l = List.replicate p x ++ List.replicate (l.length - p) y := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a t ih =>
    have hmem' : ∀ b ∈ t, b = x ∨ b = y := fun b hb => hmem b (List.mem_cons_of_mem a hb)
    have hmono' : ∀ i j (hj : j < t.length) (_ : i < j), t[i]'(by omega) = y → t[j] = y := by
      intro i j hj hij hiy
      have h := hmono (i + 1) (j + 1) (by simpa using hj) (by omega) ?_
      · simpa using h
      · simpa using hiy
    rcases hmem a (by simp) with hax | hay
    · obtain ⟨p, hp⟩ := ih hmem' hmono'
      refine ⟨p + 1, ?_⟩
      conv_lhs => rw [hax, hp]
      rw [List.length_cons, List.replicate_succ, List.cons_append,
        show t.length + 1 - (p + 1) = t.length - p from by omega]
    · -- `a = y`, hence every entry of `t` is `y`
      have htall : t = List.replicate t.length y := by
        apply List.eq_replicate_of_mem
        intro b hb
        obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hb
        have h := hmono 0 (m + 1) (by simpa using hm) (by omega) ?_
        · simpa using h
        · simp [hay]
      refine ⟨0, ?_⟩
      conv_lhs => rw [hay, htall]
      rw [List.replicate_zero, List.nil_append, List.length_cons, Nat.sub_zero,
        List.replicate_succ]

/-- Consecutive area-sequence entries climb by at most one. -/
theorem areaSeq_getElem_succ_le (Q : List Step) (i : ℕ) (hi : i + 1 < (areaSeq Q).length) :
    (areaSeq Q)[i + 1] ≤ (areaSeq Q)[i]'(by omega) + 1 := by
  have hi0 : i < (areaSeq Q).length := by omega
  rw [areaSeq_getElem_eq Q i hi0, areaSeq_getElem_eq Q (i + 1) hi]
  have hiU : i < (uPositions Q).length := by rwa [← length_areaSeq_eq_length_uPositions]
  have hi1U : i + 1 < (uPositions Q).length := by rwa [← length_areaSeq_eq_length_uPositions]
  have hmono : (uPositions Q)[i] < (uPositions Q)[i + 1] := by
    have h := uPositions_strictMono Q (a := ⟨i, hiU⟩) (b := ⟨i + 1, hi1U⟩) (by simp [Fin.lt_def])
    simpa [List.get_eq_getElem] using h
  push_cast
  omega

open Finset in
/-- **Shape of a tight area sequence (the rigidity core).**  A tight Dyck path's
area sequence is an initial staircase `0,1,…,r-1` followed by a block of `r-1`'s
and a block of `r-2`'s; i.e. it equals `canonAreaSeq r (p+q) q`. -/
theorem tight_shape (Q : List Step) (hQ : IsDyckPath Q)
    (hn : 1 ≤ (areaSeq Q).length)
    (htight : ∀ j : Fin (areaSeq Q).length,
      (numPartners Q j : ℤ) = ((j : ℕ) : ℤ) - (areaSeq Q)[(j : ℕ)]) :
    ∃ r p q : ℕ, 1 ≤ r ∧ r + p + q = (areaSeq Q).length ∧ (q = 0 ∨ 2 ≤ r) ∧
      areaSeq Q = canonAreaSeq r (p + q) q := by
  set n := (areaSeq Q).length with hn_def
  -- A total area-sequence function (no proof obligations on indexing).
  set g : ℕ → ℤ := fun i => ((areaSeq Q)[i]?).getD 0 with hg_def
  have hg : ∀ i (hi : i < n), g i = (areaSeq Q)[i]'hi := by
    intro i hi; simp only [hg_def, List.getElem?_eq_getElem hi, Option.getD_some]
  -- The two equality conditions of tightness, in `g`-form.
  have hNH : ∀ j, j < n → ∀ i, i < j → g i ≤ g j + 1 := by
    intro j hj i hij
    rw [hg i (by omega), hg j hj]
    exact (tight_column Q hQ ⟨j, hj⟩ (htight ⟨j, hj⟩)).1 ⟨i, by omega⟩ hij
  have hLO : ∀ j, j < n → ∀ i1 i2, i1 < j → i2 < j → g i1 < g j → g i1 = g i2 → i1 = i2 := by
    intro j hj i1 i2 hi1 hi2 hlt heqv
    refine congrArg Fin.val
      ((tight_column Q hQ ⟨j, hj⟩ (htight ⟨j, hj⟩)).2 ⟨i1, by omega⟩ ⟨i2, by omega⟩ hi1 hi2 ?_ ?_)
    · rw [← hg i1 (by omega), ← hg j hj]; exact hlt
    · rw [← hg i1 (by omega), ← hg i2 (by omega)]; exact heqv
  have hnn : ∀ i, i < n → 0 ≤ g i := by
    intro i hi; rw [hg i hi]
    have := areaSeq_get_nonneg Q hQ ⟨i, hi⟩; rwa [List.get_eq_getElem] at this
  have hsucc : ∀ i, i + 1 < n → g (i + 1) ≤ g i + 1 := by
    intro i hi; rw [hg (i + 1) hi, hg i (by omega)]; exact areaSeq_getElem_succ_le Q i hi
  have hQpos : 0 < Q.length := by
    have h1 : Q.count U ≤ Q.length := List.count_le_length
    have h2 : (areaSeq Q).length = Q.count U := length_areaSeq Q
    omega
  have hs0 : g 0 = 0 := by
    rw [hg 0 (by omega)]
    have h := areaSeq_head?_eq_zero_of_isDyckPath Q hQ hQpos
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some_inj.mp h
  -- The staircase length `r`: least `m` with `g m ≠ m` (or `m ≥ n`).
  have hPwit : n ≤ n ∨ g n ≠ (n : ℤ) := Or.inl (le_refl n)
  set r := Nat.find (⟨n, hPwit⟩ : ∃ m : ℕ, n ≤ m ∨ g m ≠ (m : ℤ)) with hr_def
  have hr_le : r ≤ n := Nat.find_le hPwit
  have hr_stair : ∀ m, m < r → g m = (m : ℤ) := by
    intro m hm
    have h := Nat.find_min (⟨n, hPwit⟩ : ∃ m : ℕ, n ≤ m ∨ g m ≠ (m : ℤ))
      (by rw [← hr_def]; exact hm)
    push Not at h; exact h.2
  have hr_pos : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h
    · exfalso
      have h := Nat.find_spec (⟨n, hPwit⟩ : ∃ m : ℕ, n ≤ m ∨ g m ≠ (m : ℤ))
      rw [← hr_def, h0] at h
      rcases h with h | h
      · omega
      · exact h (by rw [hs0]; norm_num)
    · exact h
  by_cases hrn : r = n
  · -- Full staircase: `areaSeq Q = canonAreaSeq n 0 0`.
    refine ⟨n, 0, 0, hn, by omega, Or.inl rfl, ?_⟩
    apply List.ext_getElem?
    intro i
    by_cases hi : i < n
    · rw [List.getElem?_eq_getElem hi, getElem?_canonAreaSeq n 0 0 i (by omega)]
      refine congrArg some ?_
      rw [← hg i hi, hr_stair i (by omega)]; unfold canonVal; rw [if_pos (by omega)]
    · rw [List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (by rw [length_canonAreaSeq n 0 0 (le_refl 0)]; omega)]
  · -- `r < n`: there is a two-level tail.
    have hrn' : r < n := lt_of_le_of_ne hr_le hrn
    have hr_break : g r ≠ (r : ℤ) := by
      have h := Nat.find_spec (⟨n, hPwit⟩ : ∃ m : ℕ, n ≤ m ∨ g m ≠ (m : ℤ))
      rw [← hr_def] at h
      rcases h with h | h
      · omega
      · exact h
    have hsr_le : g r ≤ (r : ℤ) - 1 := by
      have hprev : g (r - 1) = ((r - 1 : ℕ) : ℤ) := hr_stair (r - 1) (by omega)
      have hval : g ((r - 1) + 1) ≤ g (r - 1) + 1 := hsucc (r - 1) (by omega)
      rw [show (r - 1) + 1 = r by omega] at hval
      have hc : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by push_cast [Nat.cast_sub hr_pos]; ring
      rw [hprev, hc] at hval
      have := hr_break; omega
    -- Tail bound: every entry from `r` on is `r-1` or `r-2`.
    have htail : ∀ k, r ≤ k → k < n → g k = (r : ℤ) - 1 ∨ g k = (r : ℤ) - 2 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hrk hk
        have hlow : (r : ℤ) - 2 ≤ g k := by
          have hA : g (r - 1) = ((r - 1 : ℕ) : ℤ) := hr_stair (r - 1) (by omega)
          have hAk : g (r - 1) ≤ g k + 1 := hNH k hk (r - 1) (by omega)
          have hc : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by push_cast [Nat.cast_sub hr_pos]; ring
          rw [hA, hc] at hAk; omega
        have hup : g k ≤ (r : ℤ) - 1 := by
          rcases eq_or_lt_of_le hrk with hkr | hkr
          · rw [← hkr]; exact hsr_le
          · have hprev := ih (k - 1) (by omega) (by omega) (by omega)
            by_contra hcon
            push Not at hcon
            have hvlt : g (k - 1) < g k := by rcases hprev with h | h <;> rw [h] <;> omega
            have hvn : (g (k - 1)).toNat < r := by rcases hprev with h | h <;> rw [h] <;> omega
            have hstv : g (g (k - 1)).toNat = g (k - 1) := by
              rw [hr_stair (g (k - 1)).toNat hvn, Int.toNat_of_nonneg (hnn _ (by omega))]
            have hidx : k - 1 = (g (k - 1)).toNat :=
              hLO k hk (k - 1) (g (k - 1)).toNat (by omega) (by omega) hvlt hstv.symm
            omega
        omega
    -- Absorbing monotonicity: once `r-2`, stays `r-2`.
    have hmono_tail : ∀ k1 k2, r ≤ k1 → k1 < k2 → k2 < n →
        g k1 = (r : ℤ) - 2 → g k2 = (r : ℤ) - 2 := by
      intro k1 k2 hrk1 hk12 hk2 hk1val
      rcases htail k2 (by omega) hk2 with h2 | h2
      · exfalso
        have hr2 : (2 : ℤ) ≤ r := by
          by_contra hlt; push Not at hlt
          have := hnn k1 (by omega); rw [hk1val] at this; omega
        have hvlt : g k1 < g k2 := by rw [hk1val, h2]; omega
        have hstv : g (r - 2) = (r : ℤ) - 2 := by
          rw [hr_stair (r - 2) (by omega)]; push_cast [Nat.cast_sub (by omega : 2 ≤ r)]; ring
        have hidx : k1 = r - 2 :=
          hLO k2 hk2 k1 (r - 2) (by omega) (by omega) hvlt (by rw [hk1val, hstv])
        omega
      · exact h2
    -- Structure of the tail list `g r, g (r+1), …`.
    have hmem : ∀ a ∈ (List.range (n - r)).map (fun k => g (r + k)),
        a = (r : ℤ) - 1 ∨ a = (r : ℤ) - 2 := by
      intro a ha
      rw [List.mem_map] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      rw [List.mem_range] at hk
      exact htail (r + k) (by omega) (by omega)
    have hmono : ∀ i j (hj : j < ((List.range (n - r)).map (fun k => g (r + k))).length)
        (_ : i < j),
        ((List.range (n - r)).map (fun k => g (r + k)))[i]'(by omega) = (r : ℤ) - 2 →
        ((List.range (n - r)).map (fun k => g (r + k)))[j] = (r : ℤ) - 2 := by
      intro i j hj hij hiy
      rw [List.getElem_map, List.getElem_range] at hiy ⊢
      rw [List.length_map, List.length_range] at hj
      exact hmono_tail (r + i) (r + j) (by omega) (by omega) (by omega) hiy
    obtain ⟨p, hp⟩ := mono_two_value_eq ((List.range (n - r)).map (fun k => g (r + k)))
      ((r : ℤ) - 1) ((r : ℤ) - 2) hmem hmono
    rw [List.length_map, List.length_range] at hp
    have hpq : p ≤ n - r := by
      by_contra hcon; push Not at hcon
      rw [show n - r - p = 0 by omega, List.replicate_zero, List.append_nil] at hp
      have := congrArg List.length hp
      rw [List.length_map, List.length_range, List.length_replicate] at this; omega
    set q := n - r - p with hq
    have hrsum : r + (p + q) = n := by omega
    have hqle : q ≤ p + q := by omega
    -- Per-index value of the tail.
    have hgtail : ∀ k, k < n - r → g (r + k) = if k < p then (r : ℤ) - 1 else (r : ℤ) - 2 := by
      intro k hk
      have e : ((List.range (n - r)).map (fun k => g (r + k)))[k]? = some (g (r + k)) := by
        rw [List.getElem?_eq_getElem (by rw [List.length_map, List.length_range]; omega),
          List.getElem_map, List.getElem_range]
      rw [hp] at e
      by_cases hkp : k < p
      · rw [List.getElem?_append_left (by rw [List.length_replicate]; omega),
          List.getElem?_replicate, if_pos hkp] at e
        rw [if_pos hkp]; exact (Option.some_inj.mp e).symm
      · rw [List.getElem?_append_right (by rw [List.length_replicate]; omega),
          List.length_replicate, List.getElem?_replicate, if_pos (by omega)] at e
        rw [if_neg hkp]; exact (Option.some_inj.mp e).symm
    refine ⟨r, p, q, hr_pos, by omega, ?_, ?_⟩
    · -- edge condition `q = 0 ∨ 2 ≤ r`
      rcases Nat.lt_or_ge r 2 with hr1 | hr2
      · left
        by_contra hqne
        have hqpos : 0 < q := Nat.pos_of_ne_zero hqne
        have hval := hgtail p (by omega)
        rw [if_neg (by omega)] at hval
        have := hnn (r + p) (by omega); rw [hval] at this; omega
      · right; exact hr2
    · -- the list equality `areaSeq Q = canonAreaSeq r (p+q) q`
      apply List.ext_getElem?
      intro i
      by_cases hi : i < n
      · rw [List.getElem?_eq_getElem hi, getElem?_canonAreaSeq r (p + q) q i (by omega)]
        refine congrArg some ?_
        rw [← hg i hi]
        rcases lt_or_ge i r with hir | hir
        · rw [hr_stair i hir]; unfold canonVal; rw [if_pos hir]
        · have hgi : g i = g (r + (i - r)) := by rw [show r + (i - r) = i by omega]
          rw [hgi, hgtail (i - r) (by omega)]
          unfold canonVal
          rw [if_neg (show ¬ i < r by omega)]
          by_cases hip : i - r < p
          · rw [if_pos hip, if_pos (show i < r + (p + q - q) by omega)]
          · rw [if_neg hip, if_neg (show ¬ i < r + (p + q - q) by omega)]
      · rw [List.getElem?_eq_none (by omega),
          List.getElem?_eq_none (by rw [length_canonAreaSeq r (p + q) q hqle]; omega)]

/-- **Uniqueness of the triangular decomposition.**  If `C(B+1,2) + D = c` with
`D ≤ B`, then `(B, D)` is the triangular decomposition of `c`. -/
theorem triB_unique (B D c : ℕ) (hDB : D ≤ B) (hc : B * (B + 1) / 2 + D = c) :
    B = triB c ∧ D = triD c := by
  have tri_eq : ∀ X : ℕ, X * (X + 1) / 2 = (X + 1).choose 2 := by
    intro X; rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]
  have htri_succ : (B + 1) * (B + 2) / 2 = B * (B + 1) / 2 + (B + 1) := by
    have h : (B + 1 + 1) * (B + 1) / 2 = B * (B + 1) / 2 + (B + 1) := by
      have := Nat.triangle_succ (B + 1)
      simpa [Nat.mul_comm] using this
    rw [show (B + 1) * (B + 2) = (B + 1 + 1) * (B + 1) by ring]
    exact h
  have hlow : B * (B + 1) / 2 ≤ c := by omega
  have hhigh : c < (B + 1) * (B + 2) / 2 := by omega
  have hB : B = triB c := by
    rcases lt_trichotomy B (triB c) with h | h | h
    · exfalso
      have hmono : (B + 2).choose 2 ≤ (triB c + 1).choose 2 := Nat.choose_le_choose 2 (by omega)
      have e1 : (B + 1) * (B + 2) / 2 = (B + 2).choose 2 := tri_eq (B + 1)
      have e2 : triB c * (triB c + 1) / 2 = (triB c + 1).choose 2 := tri_eq (triB c)
      have := triB_choose_le c
      omega
    · exact h
    · exfalso
      have hmono : (triB c + 2).choose 2 ≤ (B + 1).choose 2 := Nat.choose_le_choose 2 (by omega)
      have e1 : (triB c + 1) * (triB c + 2) / 2 = (triB c + 2).choose 2 := tri_eq (triB c + 1)
      have e2 : B * (B + 1) / 2 = (B + 1).choose 2 := tri_eq B
      have := lt_triB_succ_choose c
      omega
  refine ⟨hB, ?_⟩
  have := tri_recompose c
  rw [← hB] at this; omega

/-- **Rigidity (standalone).**  Any tight Dyck path of semilength `N` with
`dinv = c` has the canonical area sequence `canonAreaSeq (N - triB c) (triB c) (triD c)`. -/
theorem areaSeq_of_tight (N : ℕ) (hN : N ≥ 1) (c : ℕ)
    (Q : List Step) (hQmem : Q ∈ DyckPath N) (hQtight : IsTight Q) (hQdinv : dinv Q = c) :
    areaSeq Q = canonAreaSeq (N - triB c) (triB c) (triD c) := by
  obtain ⟨hQdyck, hQlen2⟩ := hQmem
  have hQslen : semilength Q = N := by unfold semilength; rw [hQlen2]; omega
  have hQareaLen : (areaSeq Q).length = N := by
    rw [length_areaSeq_eq_semilength Q hQdyck, hQslen]
  have hcol : ∀ j : Fin (areaSeq Q).length,
      (numPartners Q j : ℤ) = ((j : ℕ) : ℤ) - (areaSeq Q)[(j : ℕ)] :=
    (isTight_iff_columns Q hQdyck).mp hQtight
  obtain ⟨r, pp, qq, hr1, hsum, hedge', hcanon⟩ :=
    tight_shape Q hQdyck (by rw [hQareaLen]; exact hN) hcol
  rw [hQareaLen] at hsum
  have hqqle : qq ≤ pp + qq := by omega
  have hco2 : 2 * coarea Q = ((pp + qq : ℕ) : ℤ) * (((pp + qq : ℕ) : ℤ) + 1) + 2 * (qq : ℤ) :=
    two_mul_coarea_canon Q r (pp + qq) qq hQdyck hqqle hcanon
  have hcd : coarea Q = (c : ℤ) := by rw [← hQtight]; exact_mod_cast hQdinv
  have h2c : ((pp + qq : ℕ) : ℤ) * (((pp + qq : ℕ) : ℤ) + 1) + 2 * (qq : ℤ) = 2 * (c : ℤ) := by
    rw [← hco2, hcd]
  have hnat : (pp + qq) * ((pp + qq) + 1) + 2 * qq = 2 * c := by exact_mod_cast h2c
  have heven : 2 ∣ (pp + qq) * ((pp + qq) + 1) := (Nat.even_mul_succ_self (pp + qq)).two_dvd
  have hdinveq : (pp + qq) * ((pp + qq) + 1) / 2 + qq = c := by omega
  obtain ⟨hbeq, hdeq⟩ := triB_unique (pp + qq) qq c hqqle hdinveq
  rw [hcanon, ← hbeq, ← hdeq]
  congr 1
  omega

/-! ## `lem:deficit-zero-targets`: Tight targets are rigid -/

/-- **`lem:deficit-zero-targets` (paper.tex).**
Fix `N ≥ 1` and `c ∈ {0, …, C(N,2)}`. There is a unique Dyck path
`Γ_{N,c} ∈ D_N` satisfying `dinv(Γ_{N,c}) = coarea(Γ_{N,c}) = c`.
Its area sequence is the staircase-plus-tail form described above. -/
theorem tight_targets_rigid (N : ℕ) (hN : N ≥ 1)
    (c : ℕ) (hc : c ≤ N * (N - 1) / 2) :
    ∃! Q : List Step, Q ∈ DyckPath N ∧ IsTight Q ∧
      dinv Q = c := by
  -- The triangular decomposition `c = C(b+1,2) + d` and `a = N - b`.
  set b := triB c with hb
  set d := triD c with hd_def
  set a := N - b with ha_def
  have hbN : b ≤ N - 1 := triB_le_of_le_choose N c hN hc
  have hdb : d ≤ b := triD_le_triB c
  have ha1 : 1 ≤ a := by omega
  have hab : a + b = N := by omega
  have htri : b * (b + 1) / 2 + d = c := by rw [hb, hd_def]; exact tri_recompose c
  -- The edge condition `2 ≤ a ∨ d = 0` (forced by `c ≤ C(N,2)` when `a = 1`).
  have hedge : 2 ≤ a ∨ d = 0 := by
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · right
      have hba : b = N - 1 := by omega
      have hKeq : b * (b + 1) / 2 = N * (N - 1) / 2 := by
        rw [hba]; congr 1
        have hN1 : (N - 1) + 1 = N := by omega
        rw [hN1, Nat.mul_comm]
      omega
    · left; exact ha2
  have hvalid : IsValidAreaSeq (canonAreaSeq a b d) := isValidAreaSeq_canon a b d ha1 hdb hedge
  -- The canonical witness.
  set Q0 := pathOfAreaSeq (canonAreaSeq a b d) with hQ0def
  have hareaSeq : areaSeq Q0 = canonAreaSeq a b d := areaSeq_pathOfAreaSeq _ hvalid
  have hdyck : IsDyckPath Q0 := isDyckPath_pathOfAreaSeq _ hvalid
  have hlen : Q0.length = 2 * N := by
    rw [hQ0def, length_pathOfAreaSeq _ hvalid, length_canonAreaSeq a b d hdb]; omega
  have hmem : Q0 ∈ DyckPath N := ⟨hdyck, hlen⟩
  have htight : IsTight Q0 := isTight_of_areaSeq_canon Q0 a b d hdyck ha1 hdb hedge hareaSeq
  -- `dinv Q0 = c` via `2·dinv = 2·coarea = b(b+1) + 2d = 2c`.
  have htc : (b : ℤ) * ((b : ℤ) + 1) + 2 * (d : ℤ) = 2 * (c : ℤ) := by
    have heven : 2 ∣ b * (b + 1) := (Nat.even_mul_succ_self b).two_dvd
    have hnat : 2 * c = b * (b + 1) + 2 * d := by omega
    have hcast : ((2 * c : ℕ) : ℤ) = ((b * (b + 1) + 2 * d : ℕ) : ℤ) := by exact_mod_cast hnat
    push_cast at hcast; linarith
  have hdinv : dinv Q0 = c := by
    have hco2 : 2 * coarea Q0 = (b : ℤ) * ((b : ℤ) + 1) + 2 * (d : ℤ) :=
      two_mul_coarea_canon Q0 a b d hdyck hdb hareaSeq
    have hz : (dinv Q0 : ℤ) = (c : ℤ) := by
      have h2 : 2 * (dinv Q0 : ℤ) = 2 * (c : ℤ) := by rw [htight, hco2, htc]
      linarith
    exact_mod_cast hz
  refine ⟨Q0, ⟨hmem, htight, hdinv⟩, ?_⟩
  -- Uniqueness (rigidity): any tight target has the same area sequence as `Q0`.
  rintro Q ⟨hQmem, hQtight, hQdinv⟩
  have hAQ : areaSeq Q = canonAreaSeq (N - triB c) (triB c) (triD c) :=
    areaSeq_of_tight N hN c Q hQmem hQtight hQdinv
  have hfinal : areaSeq Q = areaSeq Q0 := by
    rw [hAQ, hareaSeq, ← hb, ← hd_def, ← ha_def]
  exact dyck_eq_of_areaSeq_eq Q Q0 hQmem.1 hdyck hfinal

/-! ## `cor:forced-triangular-pairs`: forced triangular profile -/

/-! ### First-ascent and tail of the canonical path -/

/-- `pathOfAreaSeqAux` on a consecutive run `prev, prev+1, …` emits a leading
block of `U`'s of that length. -/
theorem pathOfAreaSeqAux_consec (stair rest : List ℤ) (prev : ℤ)
    (hcon : ∀ i (hi : i < stair.length), stair[i] = prev + (i : ℤ)) :
    pathOfAreaSeqAux prev (stair ++ rest)
      = List.replicate stair.length U ++ pathOfAreaSeqAux (prev + (stair.length : ℤ)) rest := by
  induction stair generalizing prev with
  | nil => simp
  | cons x t ih =>
      have hx : x = prev := by have := hcon 0 (by simp); simpa using this
      have hcon' : ∀ i (hi : i < t.length), t[i] = (prev + 1) + (i : ℤ) := by
        intro i hi
        have h := hcon (i + 1) (by rw [List.length_cons]; omega)
        rw [List.getElem_cons_succ] at h
        rw [h]; push_cast; ring
      rw [List.cons_append, pathOfAreaSeqAux, hx, sub_self, Int.toNat_zero,
        List.replicate_zero, List.nil_append, ih (prev + 1) hcon', List.length_cons,
        List.replicate_succ, List.cons_append,
        show (prev + 1) + (t.length : ℤ) = prev + ((t.length + 1 : ℕ) : ℤ) by push_cast; ring]

/-- `takeWhile (· = U)` passes through a leading block of `U`'s. -/
theorem takeWhile_replicate_U_append (a : ℕ) (R : List Step) :
    (List.replicate a U ++ R).takeWhile (· = U) = List.replicate a U ++ R.takeWhile (· = U) := by
  induction a with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, List.takeWhile_cons_of_pos (by decide), ih,
        List.cons_append]

/-- After the initial staircase, the constructor descends (emits a `D`), so the
leading `U`-run stops there. -/
theorem takeWhile_pathOfAreaSeqAux_nil (prev : ℤ) (L : List ℤ) (hp : 1 ≤ prev)
    (hhead : ∀ v, L.head? = some v → v + 1 ≤ prev) :
    (pathOfAreaSeqAux prev L).takeWhile (· = U) = [] := by
  cases L with
  | nil =>
      rw [pathOfAreaSeqAux]
      obtain ⟨m, hm⟩ : ∃ m, prev.toNat = m + 1 := ⟨prev.toNat - 1, by omega⟩
      rw [hm, List.replicate_succ, List.takeWhile_cons_of_neg (by decide)]
  | cons x t =>
      have hx : x + 1 ≤ prev := hhead x (by simp)
      rw [pathOfAreaSeqAux]
      obtain ⟨m, hm⟩ : ∃ m, (prev - x).toNat = m + 1 := ⟨(prev - x).toNat - 1, by omega⟩
      rw [hm, List.replicate_succ, List.cons_append, List.takeWhile_cons_of_neg (by decide)]

/-- **First-ascent of the canonical path is `a`.** -/
theorem firstAscent_canon (a b d : ℕ) (ha : 1 ≤ a) (hd : d ≤ b) (_hedge : 2 ≤ a ∨ d = 0) :
    firstAscent (pathOfAreaSeq (canonAreaSeq a b d)) = a := by
  have hlenc : (canonAreaSeq a b d).length = a + b := length_canonAreaSeq a b d hd
  have htakelen : ((canonAreaSeq a b d).take a).length = a := by
    rw [List.length_take, hlenc]; omega
  have hpath : pathOfAreaSeq (canonAreaSeq a b d)
      = List.replicate a U ++ pathOfAreaSeqAux (a : ℤ) ((canonAreaSeq a b d).drop a) := by
    conv_lhs => rw [pathOfAreaSeq, ← List.take_append_drop a (canonAreaSeq a b d)]
    rw [pathOfAreaSeqAux_consec ((canonAreaSeq a b d).take a) ((canonAreaSeq a b d).drop a) 0 ?_,
      htakelen]
    · simp
    · intro i hi
      rw [htakelen] at hi
      rw [List.getElem_take, getElem_canonAreaSeq a b d hd i (by omega)]
      unfold canonVal; rw [if_pos hi]; ring
  rw [hpath, firstAscent, takeWhile_replicate_U_append]
  rw [takeWhile_pathOfAreaSeqAux_nil (a : ℤ) ((canonAreaSeq a b d).drop a) (by exact_mod_cast ha) ?_]
  · simp
  · intro v hv
    have hdroplen : ((canonAreaSeq a b d).drop a).length = b := by rw [List.length_drop, hlenc]; omega
    rw [List.head?_eq_getElem?] at hv
    by_cases h0 : 0 < b
    · rw [List.getElem?_drop, Nat.add_zero, getElem?_canonAreaSeq a b d a (by omega)] at hv
      simp only [Option.some.injEq] at hv
      have hle : canonVal a b d a ≤ (a : ℤ) - 1 := by
        unfold canonVal; rw [if_neg (by omega)]; split <;> omega
      rw [← hv]; linarith
    · rw [List.getElem?_eq_none (by rw [hdroplen]; omega)] at hv
      simp at hv

/-- **Tail-U of the canonical path is `b`.** -/
theorem tailU_canon (a b d : ℕ) (ha : 1 ≤ a) (hd : d ≤ b) (hedge : 2 ≤ a ∨ d = 0) :
    tailU (pathOfAreaSeq (canonAreaSeq a b d)) = b := by
  have hcU : (pathOfAreaSeq (canonAreaSeq a b d)).count U = a + b := by
    rw [pathOfAreaSeq, count_U_pathOfAreaSeqAux, length_canonAreaSeq a b d hd]
  rw [tailU, firstAscent_canon a b d ha hd hedge, hcU]; omega

/-- The triangular number `C(k,2)` commutes with the cast `ℕ → ℤ`. -/
theorem cast_triangular (k : ℕ) :
    (k : ℤ) * ((k : ℤ) - 1) / 2 = ((k * (k - 1) / 2 : ℕ) : ℤ) := by
  have hev : (2 : ℤ) ∣ (k : ℤ) * ((k : ℤ) - 1) := by
    have h := (Int.even_mul_succ_self ((k : ℤ) - 1)).two_dvd
    have he : ((k : ℤ) - 1) * (((k : ℤ) - 1) + 1) = (k : ℤ) * ((k : ℤ) - 1) := by ring
    rwa [he] at h
  have hnd : 2 ∣ k * (k - 1) := by
    rcases k with _ | m
    · simp
    · rw [Nat.succ_sub_one, Nat.mul_comm]; exact (Nat.even_mul_succ_self m).two_dvd
  have e1 : 2 * ((k : ℤ) * ((k : ℤ) - 1) / 2) = (k : ℤ) * ((k : ℤ) - 1) := by
    rw [mul_comm]; exact Int.ediv_mul_cancel hev
  have e2 : 2 * (((k * (k - 1) / 2 : ℕ)) : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
    have hc : 2 * (k * (k - 1) / 2) = k * (k - 1) := Nat.mul_div_cancel' hnd
    rcases k with _ | m
    · simp
    · rw [Nat.succ_sub_one] at hc
      have hcZ : ((2 * ((m + 1) * m / 2) : ℕ) : ℤ) = (((m + 1) * m : ℕ) : ℤ) := by exact_mod_cast hc
      push_cast at hcZ ⊢
      linear_combination hcZ
  omega

/-- **First-ascent and tail of any tight target.**  Packages the rigidity result
with the first-ascent computation of the canonical path. -/
theorem fas_tailU_of_tight (N c : ℕ) (hN : N ≥ 1) (hc : c ≤ N * (N - 1) / 2)
    (Q : List Step) (hmem : Q ∈ DyckPath N) (htight : IsTight Q) (hQdinv : dinv Q = c) :
    firstAscent Q = N - triB c ∧ tailU Q = triB c := by
  set b := triB c with hb
  set d := triD c with hd_def
  set a := N - b with ha_def
  have hbN : b ≤ N - 1 := triB_le_of_le_choose N c hN hc
  have hdb : d ≤ b := triD_le_triB c
  have ha1 : 1 ≤ a := by omega
  have htri : b * (b + 1) / 2 + d = c := tri_recompose c
  have hedge : 2 ≤ a ∨ d = 0 := by
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · right
      have hba : b = N - 1 := by omega
      have hKeq : b * (b + 1) / 2 = N * (N - 1) / 2 := by
        rw [hba]; congr 1
        have hN1 : (N - 1) + 1 = N := by omega
        rw [hN1, Nat.mul_comm]
      omega
    · left; exact ha2
  have hvalid : IsValidAreaSeq (canonAreaSeq a b d) := isValidAreaSeq_canon a b d ha1 hdb hedge
  have hAQ : areaSeq Q = canonAreaSeq a b d := areaSeq_of_tight N hN c Q hmem htight hQdinv
  have hQeq : Q = pathOfAreaSeq (canonAreaSeq a b d) := by
    apply dyck_eq_of_areaSeq_eq Q _ hmem.1 (isDyckPath_pathOfAreaSeq _ hvalid)
    rw [hAQ, areaSeq_pathOfAreaSeq _ hvalid]
  rw [hQeq]
  exact ⟨firstAscent_canon a b d ha1 hdb hedge, tailU_canon a b d ha1 hdb hedge⟩

/-- **`cor:forced-triangular-pairs` (paper.tex).**
If `F : D → D` is length-preserving and satisfies
`area(F(P)) = dinv(P)` and `dinv(F(P)) = area(P)` for every Dyck path,
then the first-ascent profile `{(fas(F(W_n)), tailU(F(W_n))) : n ≥ 1} = S_tri`.

The key steps:
1. `Q_n := F(W_n)` has `area = C(n,2)` and `dinv = n`,
2. Hence `coarea(Q_n) = C(n+1,2) - C(n,2) = n = dinv(Q_n)`, so Q_n is tight,
3. By `lem:deficit-zero-targets`, Q_n is determined uniquely, and its profile lies in S_tri. -/
theorem forced_triangular_profile
    (f : List Step → List Step)
    (hDyck : ∀ P, IsDyckPath P → IsDyckPath (f P))
    (hlen : ∀ P, IsDyckPath P → (f P).length = P.length)
    (harea : ∀ P, IsDyckPath P → area (f P) = ↑(dinv P))
    (hdinv : ∀ P, IsDyckPath P → dinv (f P) = (area P).toNat) :
    {p : ℕ × ℕ | ∃ n : ℕ, n ≥ 1 ∧
      p = (firstAscent (f (wrappedFlat n)), tailU (f (wrappedFlat n)))} = S_tri := by
  -- Profile of `Q_n = f(W_n)`: it is the tight target `Γ_{n+1,n}`.
  have hprofile : ∀ n, 1 ≤ n →
      firstAscent (f (wrappedFlat n)) = (n + 1) - triB n ∧
        tailU (f (wrappedFlat n)) = triB n := by
    intro n hn1
    set Q := f (wrappedFlat n) with hQdef
    have hWdyck : IsDyckPath (wrappedFlat n) := isDyckPath_wrappedFlat n
    have hQdyck : IsDyckPath Q := hDyck _ hWdyck
    have hQlen : Q.length = 2 * (n + 1) := by rw [hQdef, hlen _ hWdyck, length_wrappedFlat]
    have hmem : Q ∈ DyckPath (n + 1) := ⟨hQdyck, hQlen⟩
    have hdinvQ : dinv Q = n := by rw [hQdef, hdinv _ hWdyck, area_wrappedFlat]; simp
    have hareaQ : area Q = ((n * (n - 1) / 2 : ℕ) : ℤ) := by
      rw [hQdef, harea _ hWdyck, dinv_wrappedFlat]
    have hcoareaQ : coarea Q = (n : ℤ) := by
      have hsl : semilength Q = n + 1 := by unfold semilength; rw [hQlen]; omega
      have hco : coarea Q = ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) - 1) / 2 - area Q := by
        show (↑(semilength Q) : ℤ) * (↑(semilength Q) - 1) / 2 - area Q = _; rw [hsl]
      rw [hco, hareaQ, cast_triangular (n + 1), Nat.triangle_succ n]
      push_cast; ring
    have htightQ : IsTight Q := by rw [IsTight, hcoareaQ]; exact_mod_cast hdinvQ
    have hc : n ≤ (n + 1) * ((n + 1) - 1) / 2 := by rw [Nat.triangle_succ n]; omega
    exact fas_tailU_of_tight (n + 1) n (by omega) hc Q hmem htightQ hdinvQ
  -- A pair of triangular successor identities (used in both directions).
  have hTri : ∀ b : ℕ, b * (b + 1) / 2 = b * (b - 1) / 2 + b ∧
      (b + 1) * (b + 2) / 2 = b * (b + 1) / 2 + (b + 1) := by
    intro b
    refine ⟨?_, ?_⟩
    · have h := Nat.triangle_succ b; rw [Nat.add_sub_cancel, Nat.mul_comm] at h; exact h
    · have h := Nat.triangle_succ (b + 1)
      simp only [Nat.add_sub_cancel] at h
      rw [Nat.mul_comm (b + 2) (b + 1), Nat.mul_comm (b + 1) b] at h; exact h
  -- The profile set is exactly `S_tri`.
  ext p
  constructor
  · rintro ⟨n, hn1, rfl⟩
    obtain ⟨hf, ht⟩ := hprofile n hn1
    simp only [Set.mem_ofPred_eq, S_tri, hf, ht]
    obtain ⟨hTb, hTb2⟩ := hTri (triB n)
    have hb1 : 1 ≤ triB n := triB_pos_of_pos n hn1
    have hlow : triB n * (triB n + 1) / 2 ≤ n := triB_choose_le n
    have hhigh : n < (triB n + 1) * (triB n + 2) / 2 := lt_triB_succ_choose n
    refine ⟨hb1, ?_, ?_⟩ <;> omega
  · intro hp
    simp only [Set.mem_ofPred_eq, S_tri] at hp
    obtain ⟨hb1, hlo, hhi⟩ := hp
    obtain ⟨hTb, hTb2⟩ := hTri p.2
    -- `n := p.1 + p.2 - 1`, with `triB n = p.2`.
    refine ⟨p.1 + p.2 - 1, by omega, ?_⟩
    have hDb : (p.1 + p.2 - 1) - p.2 * (p.2 + 1) / 2 ≤ p.2 := by omega
    have hrec : p.2 * (p.2 + 1) / 2 + ((p.1 + p.2 - 1) - p.2 * (p.2 + 1) / 2) = p.1 + p.2 - 1 := by
      omega
    obtain ⟨hbeq, _⟩ :=
      triB_unique p.2 ((p.1 + p.2 - 1) - p.2 * (p.2 + 1) / 2) (p.1 + p.2 - 1) hDb hrec
    obtain ⟨hf, ht⟩ := hprofile (p.1 + p.2 - 1) (by omega)
    rw [hf, ht, ← hbeq]
    have hane : (p.1 + p.2 - 1 + 1) - p.2 = p.1 := by omega
    rw [hane]
