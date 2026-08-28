/-
# Wrapped-Flat Paths and Statistics

Formalization of Section 8 (The wrapped-flat slice and the no-swap theorem)
of "A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.
-/
import RequestProject.DyckPath
import RequestProject.AreaSeq

open Step

/-! ## Lemma 7.1: Statistics of W_n -/

/-
**`lem:wrapped-flat-stats` (paper-full-new.tex).**
`W_n = U(UD)^n D` is a Dyck path, i.e., it lies in `D_{n+1}`.
-/
theorem isDyckPath_wrappedFlat (n : ℕ) : IsDyckPath (wrappedFlat n) := by
  constructor;
  · intro k hk;
    rcases k with ( _ | k ) <;> simp_all +decide [ wrappedFlat ];
    · exact le_rfl;
    · induction' n with n ih generalizing k <;> simp_all +decide [ List.replicate ];
      · decide +revert;
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ height ];
        exact ih k ( by linarith );
  · unfold wrappedFlat height;
    induction n <;> simp_all +decide [ List.replicate ]

/-
**`lem:wrapped-flat-stats` (paper-full-new.tex).**
The area sequence of `W_n` is `(0, 1, 1, …, 1)` with `n` ones.
-/
theorem areaSeq_wrappedFlat (n : ℕ) :
    areaSeq (wrappedFlat n) = 0 :: List.replicate n 1 := by
  have hbody : ∀ m : ℕ,
      areaSeq ((List.replicate m [U, D]).flatten ++ [D]) = List.replicate m 0 := by
    intro m
    induction m with
    | zero =>
        show areaSeq (D :: []) = []
        rw [areaSeq_cons_D]
        rfl
    | succ k ih =>
        show areaSeq (U :: D :: ((List.replicate k [U, D]).flatten ++ [D]))
          = 0 :: List.replicate k 0
        rw [areaSeq_cons_U, areaSeq_cons_D, ih, List.map_map]
        simp
  show areaSeq (U :: ((List.replicate n [U, D]).flatten ++ [D]))
    = 0 :: List.replicate n 1
  rw [areaSeq_cons_U, hbody]
  simp [List.map_replicate]

/-
**`lem:wrapped-flat-stats` (paper-full-new.tex).**
`area(W_n) = n`.
-/
theorem area_wrappedFlat (n : ℕ) : area (wrappedFlat n) = ↑n := by
  unfold area;
  rw [ areaSeq_wrappedFlat ] ; norm_num

/-
**`lem:wrapped-flat-stats` (paper-full-new.tex).**
`dinv(W_n) = n*(n-1)/2 = C(n, 2)`.
The leading entry 0 forms no pair; the only contributing pairs are the
equal pairs among the `n` entries equal to 1, of which there are C(n,2).
-/
theorem dinv_wrappedFlat (n : ℕ) : dinv (wrappedFlat n) = n * (n - 1) / 2 := by
  unfold dinv;
  rcases n with ( _ | n ) <;> simp_all +decide;
  rw [ areaSeq_wrappedFlat ] ; simp +decide [ List.finRange_succ ] ; ring_nf;
  convert Finset.sum_range_id ( n + 1 ) using 1 ; simp +arith +decide [ Finset.sum_range ] ; ring_nf;
  · refine' congr_arg _ ( List.ext_get _ _ ) <;> simp +decide [ Function.comp ];
    intro i hi; rw [ List.filter_map ] ;
    rw [ List.filter_congr ];
    rotate_right;
    use fun x => x.val < i;
    · simp +arith +decide;
      -- The length of the filtered list is equal to the number of elements in the range from 0 to i-1, which is i.
      have h_filter_length : List.length (List.filter (fun x : Fin (n + 1) => x.val < i) (List.finRange (n + 1))) = Finset.card (Finset.filter (fun x : Fin (n + 1) => x.val < i) (Finset.univ : Finset (Fin (n + 1)))) := by
        congr;
      convert h_filter_length using 1;
      · rw [ List.length_replicate ];
      · rw [ Finset.card_eq_of_bijective ];
        use fun x hx => ⟨ x, by linarith ⟩; all_goals aesop;
    · grind;
  · grind +locals

/-!
The wrapped-flat slice has semilength `n + 1`.  This is the bookkeeping
fact used when relating `W_n` to the tight-target slice in Section 8.
-/
theorem length_wrappedFlat (n : ℕ) :
    (wrappedFlat n).length = 2 * (n + 1) := by
  unfold wrappedFlat
  simp [List.length_flatten]
  omega

/-! ## Lemma 7.2: Dinv is bounded by coarea -/

open Finset in
/-- Length of a filtered `finRange` equals the cardinality of the matching
`univ`-filter. -/
theorem length_filter_finRange_eq_card {m : ℕ} (q : Fin m → Prop) [DecidablePred q] :
    ((List.finRange m).filter (fun i => decide (q i))).length = #{i | q i} := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _),
    List.toFinset_filter, List.toFinset_finRange]
  congr 1
  ext i
  simp

open Finset in
/-- `dinv` written as a sum over columns `j` of the number of earlier dinv
partners `i`. -/
theorem dinv_eq_sum_card (P : List Step) :
    dinv P = ∑ j : Fin (areaSeq P).length,
      #{i : Fin (areaSeq P).length | (i : ℕ) < (j : ℕ) ∧
        ((areaSeq P)[(i : ℕ)] - (areaSeq P)[(j : ℕ)] = 0 ∨
         (areaSeq P)[(i : ℕ)] - (areaSeq P)[(j : ℕ)] = 1)} := by
  unfold dinv
  rw [List.length_flatMap, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [length_filter_finRange_eq_card]

open Finset in
/-- **Per-column dinv bound (heart of Lemma 7.2).**
The number of dinv partners `i < j` of column `j` is at most `j - a_j`, because
the `a_j` levels `0,…,a_j-1` each occur before `j` and are never counted. -/
theorem dinv_column_bound (P : List Step) (hP : IsDyckPath P)
    (j : Fin (areaSeq P).length) :
    (#{i : Fin (areaSeq P).length | (i : ℕ) < (j : ℕ) ∧
        ((areaSeq P)[(i : ℕ)] - (areaSeq P)[(j : ℕ)] = 0 ∨
         (areaSeq P)[(i : ℕ)] - (areaSeq P)[(j : ℕ)] = 1)} : ℤ)
      ≤ (j : ℕ) - (areaSeq P)[(j : ℕ)] := by
  have haj_nonneg : 0 ≤ (areaSeq P)[(j : ℕ)] := by
    have := areaSeq_get_nonneg P hP j; rwa [List.get_eq_getElem] at this
  set Counted := Finset.univ.filter (fun i : Fin (areaSeq P).length =>
      (i : ℕ) < (j : ℕ) ∧ ((areaSeq P)[(i : ℕ)] - (areaSeq P)[(j : ℕ)] = 0 ∨
        (areaSeq P)[(i : ℕ)] - (areaSeq P)[(j : ℕ)] = 1)) with hCounted
  set Low := Finset.univ.filter (fun i : Fin (areaSeq P).length =>
      (i : ℕ) < (j : ℕ) ∧ (areaSeq P)[(i : ℕ)] < (areaSeq P)[(j : ℕ)]) with hLow
  set Before := Finset.univ.filter (fun i : Fin (areaSeq P).length => (i : ℕ) < (j : ℕ))
    with hBefore
  -- |Counted| + |Low| ≤ j  (disjoint subsets of the j earlier columns)
  have hdisj : Disjoint Counted Low := by
    rw [Finset.disjoint_left]
    intro i hiC hiL
    rw [hCounted, Finset.mem_filter] at hiC
    rw [hLow, Finset.mem_filter] at hiL
    obtain ⟨_, _, hC⟩ := hiC
    obtain ⟨_, _, hL⟩ := hiL
    rcases hC with h | h <;> omega
  have hsub : Counted ∪ Low ⊆ Before := by
    apply Finset.union_subset
    · intro i hi
      rw [hCounted, Finset.mem_filter] at hi
      rw [hBefore, Finset.mem_filter]; exact ⟨hi.1, hi.2.1⟩
    · intro i hi
      rw [hLow, Finset.mem_filter] at hi
      rw [hBefore, Finset.mem_filter]; exact ⟨hi.1, hi.2.1⟩
  have hBeforeCard : Before.card ≤ (j : ℕ) := by
    rw [hBefore, Fin.card_filter_val_lt]; exact min_le_right _ _
  have hsum : Counted.card + Low.card ≤ (j : ℕ) :=
    le_trans (Finset.card_union_of_disjoint hdisj ▸ Finset.card_le_card hsub) hBeforeCard
  -- |Low| ≥ a_j  (the a_j low levels are realised before j)
  have hLowCard : ((areaSeq P)[(j : ℕ)]).toNat ≤ Low.card := by
    have hsubimg : Finset.range ((areaSeq P)[(j : ℕ)]).toNat ⊆
        Low.image (fun i : Fin (areaSeq P).length => ((areaSeq P)[(i : ℕ)]).toNat) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hkz : (k : ℤ) < (areaSeq P)[(j : ℕ)] := by
        have h1 : (k : ℤ) < (((areaSeq P)[(j : ℕ)]).toNat : ℤ) := by exact_mod_cast hk
        omega
      obtain ⟨i, hij, hi, hival⟩ :=
        areaSeq_exists_lt_index P (j : ℕ) j.isLt (k : ℤ) (by positivity) hkz
      refine Finset.mem_image.mpr ⟨⟨i, hi⟩, ?_, ?_⟩
      · rw [hLow]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hij, ?_⟩
        show (areaSeq P)[i] < (areaSeq P)[(j : ℕ)]
        rw [hival]; exact hkz
      · show ((areaSeq P)[i]).toNat = k
        rw [hival]; exact Int.toNat_natCast k
    calc ((areaSeq P)[(j : ℕ)]).toNat
          = (Finset.range ((areaSeq P)[(j : ℕ)]).toNat).card := (Finset.card_range _).symm
      _ ≤ (Low.image _).card := Finset.card_le_card hsubimg
      _ ≤ Low.card := Finset.card_image_le
  -- combine
  have hkey : Counted.card + ((areaSeq P)[(j : ℕ)]).toNat ≤ (j : ℕ) :=
    le_trans (Nat.add_le_add_left hLowCard _) hsum
  have hcast : (((areaSeq P)[(j : ℕ)]).toNat : ℤ) = (areaSeq P)[(j : ℕ)] :=
    Int.toNat_of_nonneg haj_nonneg
  have hz : (Counted.card : ℤ) + (((areaSeq P)[(j : ℕ)]).toNat : ℤ) ≤ ((j : ℕ) : ℤ) := by
    exact_mod_cast hkey
  rw [hcast] at hz
  show (Counted.card : ℤ) ≤ ((j : ℕ) : ℤ) - (areaSeq P)[(j : ℕ)]
  linarith

/-- Gauss summation over `Fin n`, doubled to avoid division. -/
theorem two_mul_sum_fin_int (n : ℕ) :
    2 * (∑ j : Fin n, (j : ℤ)) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc, mul_add]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]; push_cast; ring

/-- Gauss summation over `Fin n`, valued in `ℤ`. -/
theorem sum_fin_cast_int (n : ℕ) :
    (∑ j : Fin n, (j : ℤ)) = (n : ℤ) * ((n : ℤ) - 1) / 2 := by
  have h := two_mul_sum_fin_int n
  generalize hm : (n : ℤ) * ((n : ℤ) - 1) = m at h
  omega

/-- The area is the sum of area-sequence entries indexed by `Fin`. -/
theorem sum_fin_areaSeq (Q : List Step) :
    (∑ j : Fin (areaSeq Q).length, (areaSeq Q)[(j : ℕ)]) = area Q := by
  unfold area
  rw [Fin.sum_univ_def]
  congr 1
  exact List.map_getElem_finRange (areaSeq Q)

open Finset in
/-- **`lem:wrapped-flat-stats` (paper-full-new.tex).**
For every Dyck path `Q ∈ D_N`, `dinv(Q) ≤ coarea(Q)`.
The proof fixes `j` and bounds the dinv pairs ending at `j` by `(j-1) - a_j`,
then sums. -/
theorem dinv_le_coarea (Q : List Step) (hQ : IsDyckPath Q) :
    (dinv Q : ℤ) ≤ coarea Q := by
  have hlen : (areaSeq Q).length = semilength Q := length_areaSeq_eq_semilength Q hQ
  have hd : (dinv Q : ℤ) = ∑ j : Fin (areaSeq Q).length,
      (#{i : Fin (areaSeq Q).length | (i : ℕ) < (j : ℕ) ∧
        ((areaSeq Q)[(i : ℕ)] - (areaSeq Q)[(j : ℕ)] = 0 ∨
         (areaSeq Q)[(i : ℕ)] - (areaSeq Q)[(j : ℕ)] = 1)} : ℤ) := by
    rw [dinv_eq_sum_card]; push_cast; rfl
  rw [hd]
  refine le_trans (Finset.sum_le_sum (fun j _ => dinv_column_bound Q hQ j)) (le_of_eq ?_)
  rw [Finset.sum_sub_distrib, sum_fin_areaSeq Q, sum_fin_cast_int, hlen]
  rfl

/-! ## Lemma 7.1 specific values for small n -/

/-- Verification: `area(W_0) = 0`. -/
theorem area_wrappedFlat_zero : area (wrappedFlat 0) = 0 := by native_decide

/-- Verification: `area(W_1) = 1`. -/
theorem area_wrappedFlat_one : area (wrappedFlat 1) = 1 := by native_decide

/-- Verification: `dinv(W_0) = 0`. -/
theorem dinv_wrappedFlat_zero : dinv (wrappedFlat 0) = 0 := by native_decide

/-- Verification: `dinv(W_1) = 0`. -/
theorem dinv_wrappedFlat_one : dinv (wrappedFlat 1) = 0 := by native_decide

/-- Verification: `dinv(W_2) = 1`. -/
theorem dinv_wrappedFlat_two : dinv (wrappedFlat 2) = 1 := by native_decide

/-- Verification: `dinv(W_3) = 3`. -/
theorem dinv_wrappedFlat_three : dinv (wrappedFlat 3) = 3 := by native_decide

/-- Verification: `dinv(W_4) = 6`. -/
theorem dinv_wrappedFlat_four : dinv (wrappedFlat 4) = 6 := by native_decide
