/-
# The Narayana Sweep

Formalization of Section 10.2 (A rank sweep that does swap a statistic pair:
the Narayana symmetry) of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.
-/
import RequestProject.DyckPath

open Step

/-! ## The Narayana polynomial (`sec:discussion`, paper-full-new.tex) -/

/-
**Section 10.2 (`sec:narayana-sweep`, paper-full-new.tex).**
Elementary identity: `val(w) = pk(w) - 1` for any Dyck path of semilength ≥ 1.
-/
theorem valleys_eq_peaks_sub_one (w : List Step) (hw : IsDyckPath w)
    (hn : semilength w ≥ 1) :
    valleys w = peaks w - 1 := by
      unfold valleys peaks;
      have h_first_char : w[0]! = U := by
        have := hw.1 1;
        rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ height ]; all_goals cases x <;> trivial
      have h_last_char : w[w.length - 1]! = D := by
        have h_last_char : w[w.length - 1]! = D := by
          have h_count : (w.count U) = (w.count D) := by
            have := hw.2; simp_all +decide [ height_eq_count ] ;
            grind
          have h_last_char : (w.dropLast.count U) ≥ (w.dropLast.count D) := by
            have := hw.1 ( w.length - 1 ) ; simp_all +decide [ List.dropLast_eq_take ] ;
            rw [ height_eq_count ] at this ; linarith;
          cases h : w.getLast? <;> simp_all +decide [ List.count ];
          cases h' : ‹Step› <;> simp_all +decide;
          · have h_last_char : (w.dropLast.count U) + 1 = (w.count U) ∧ (w.dropLast.count D) = (w.count D) := by
              have h_last_char : ∀ {l : List Step}, l ≠ [] → l.getLast? = some U → (l.dropLast.count U) + 1 = (l.count U) ∧ (l.dropLast.count D) = (l.count D) := by
                intros l hl hl'; induction l using List.reverseRecOn <;> aesop;
              exact h_last_char ( by aesop_cat ) h;
            linarith!;
          · grind;
        exact h_last_char;
      have h_count : ∀ (l : List Step), List.countP (fun i => l[i]! = D ∧ l[i + 1]! = U) (List.range (l.length - 1)) + (if l[0]! = U then 1 else 0) = List.countP (fun i => l[i]! = U ∧ l[i + 1]! = D) (List.range (l.length - 1)) + (if l[l.length - 1]! = U then 1 else 0) := by
        intro l;
        induction' l with hd tl ih;
        · rfl;
        · rcases tl <;> simp_all +decide [ List.range_succ_eq_map ];
          cases hd <;> cases ‹Step› <;> simp_all +decide;
          · convert ih using 1 <;> simp [Function.comp_def]
          · convert congr_arg ( · + 1 ) ih using 1 <;>
              simp +arith +decide [ List.countP_eq_length_filter, Function.comp_def ]
          · convert ih using 1 <;> simp [Function.comp_def]
          · convert ih using 1 <;> simp [Function.comp_def]
      grind

/-
**Section 10.2 (`sec:narayana-sweep`, paper-full-new.tex).**
Elementary identity: `dr(w) = n - pk(w)` for a Dyck path of semilength n.
-/
theorem doubleRises_eq_semilength_sub_peaks (w : List Step) (hw : IsDyckPath w) :
    doubleRises w = semilength w - peaks w := by
      obtain ⟨hw₁, hw₂⟩ := hw;
      -- The number of U's in `w` is equal to the semilength of `w`.
      have h_count_U : w.count U = semilength w := by
        have h_count_U : w.count U + w.count D = w.length := by
          rw [ List.length_eq_countP_add_countP ];
          congr;
          exact List.countP_congr fun x hx => by cases x <;> simp +decide ;
        have h_count_U : height w w.length = w.count U - w.count D := by
          convert height_eq_count w w.length using 1;
          rw [ List.take_length ];
        unfold semilength; omega;
      -- The number of U's in `w` is equal to the number of UU pairs plus the number of UD pairs plus 1 if the last letter is U.
      have h_count_U_pairs : w.count U = doubleRises w + peaks w + (if w.getLast? = some U then 1 else 0) := by
        have h_count_U_pairs : ∀ {l : List Step}, l ≠ [] → l.count U = (List.range (l.length - 1)).countP (fun i => l[i]! = U ∧ l[i + 1]! = U) + (List.range (l.length - 1)).countP (fun i => l[i]! = U ∧ l[i + 1]! = D) + (if l.getLast? = some U then 1 else 0) := by
          intros l hl_nonempty
          induction' l with l_head l_tail ih;
          · contradiction;
          · rcases l_tail <;> simp_all +decide [ List.range_succ_eq_map ];
            · cases l_head <;> rfl;
            · cases l_head <;> cases ‹Step› <;> simp_all +decide;
              · ring!;
              · simp +arith +decide;
                congr! 2;
              · congr! 1;
              · congr! 2;
        by_cases hw : w = [] <;> simp_all +decide [ doubleRises, peaks ];
      have h_last_U : ∀ k : ℕ, k < w.length → w[k]! = U → height w (k + 1) = height w k + 1 := by
        intros k hk_lt hk_U
        have h_height_succ : height w (k + 1) = height w k + (match w[k]! with | U => 1 | D => -1) := by
          unfold height;
          rw [ List.take_add_one ];
          grind;
        rw [ h_height_succ, hk_U ];
      grind

/-
**Section 10.2 (`sec:narayana-sweep`, paper-full-new.tex).**
`val(w) + dr(w) = n - 1` for a Dyck path of semilength n ≥ 1.
-/
theorem valleys_add_doubleRises (w : List Step) (hw : IsDyckPath w)
    (hn : semilength w ≥ 1) :
    valleys w + doubleRises w = semilength w - 1 := by
      convert congr_arg₂ ( · + · ) ( valleys_eq_peaks_sub_one w hw hn ) ( doubleRises_eq_semilength_sub_peaks w hw ) using 1;
      rw [ tsub_add_eq_add_tsub ];
      · have h_peaks_le_semilength : ∀ (w : List Step), IsDyckPath w → peaks w ≤ semilength w := by
          intros w hw
          have h_peaks_le_semilength : peaks w ≤ (w.count U) := by
            have h_peaks_le_semilength : ∀ (w : List Step), peaks w ≤ (w.count U) := by
              intros w
              induction' w with w ih;
              · rfl;
              · rcases ih with ( _ | ⟨ x, ih ⟩ ) <;> simp_all +decide [ peaks ];
                simp_all +decide [ List.range_succ_eq_map, List.countP_cons ];
                split_ifs <;> simp_all +decide [ List.count_cons ];
                · convert ‹List.countP ( fun i => decide ( ( D :: ih )[i]?.getD default = U ) && decide ( ih[i]?.getD default = D ) ) ( List.range ih.length ) ≤ List.count U ih› using 1
                  simp [Function.comp_def]
                · refine' le_trans _ ( Nat.le_add_right _ _ );
                  convert ‹List.countP ( fun i => decide ( ( x :: ih )[i]?.getD default = U ) && decide ( ih[i]?.getD default = D ) ) ( List.range ih.length ) ≤ List.count U ih + if x = U then 1 else 0› using 1
                  · rfl
                  · simp [Function.comp_def]
            exact h_peaks_le_semilength w;
          have h_count_U_le_semilength : (w.count U) = (w.count D) := by
            have := hw.2;
            rw [ height_eq_count ] at this;
            simp_all +decide [ sub_eq_zero ];
          have h_count_U_le_semilength : (w.count U) + (w.count D) = w.length := by
            have h_count_U_le_semilength : ∀ (w : List Step), (w.count U) + (w.count D) = w.length := by
              intro w; induction w <;> simp +decide [ * ] ;
              cases ‹Step› <;> simp +decide [ * ] <;> linarith;
            apply h_count_U_le_semilength;
          exact h_peaks_le_semilength.trans ( by rw [ semilength ] ; omega );
        grind;
      · have := hw.1;
        contrapose! this;
        -- If there are no peaks, then the path must be a sequence of U's followed by D's.
        have h_no_peaks : ∀ i < w.length - 1, w[i]! = U → w[i + 1]! = U := by
          intro i hi hi'; have := this; simp_all +decide [ peaks ] ;
          cases h : w[i + 1]?.getD default <;> specialize this i hi hi' <;> aesop;
        -- If there are no peaks, then the path must be a sequence of U's followed by D's. Hence, the first step must be U.
        have h_first_step : w[0]! = U := by
          have h_first_step : ∀ k ≤ w.length, k > 0 → (w.take k).count U ≥ (w.take k).count D := by
            intros k hk hk_pos
            have h_height_nonneg : 0 ≤ height w k := by
              exact hw.1 k hk;
            rw [ height_eq_count ] at h_height_nonneg ; linarith;
          rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide;
          · cases x <;> trivial;
          · specialize h_first_step 1 ; simp_all +decide;
            cases x <;> cases y <;> simp_all +decide;
        -- If there are no peaks, then the path must be a sequence of U's followed by D's. Hence, the entire path must be U's.
        have h_all_U : ∀ i < w.length, w[i]! = U := by
          intro i hi;
          induction' i with i ih;
          · exact h_first_step;
          · exact h_no_peaks i ( Nat.lt_pred_iff.mpr hi ) ( ih ( Nat.lt_of_succ_lt hi ) );
        have := hw.2; simp_all +decide [ height_eq_count ] ;
        rw [ show w = List.replicate w.length U from List.ext_get ( by aesop ) ( by aesop ) ] at this ; simp_all +decide [ List.count_replicate ]

/-! ## `thm:narayana-sweep`: Narayana sweep (`sec:narayana-sweep`, paper-full-new.tex) -/

/-! ### Normal form via a reflexive comparator proxy

`heightSweep` sorts by the strict comparator `cmpHS` (height ascending, position
descending).  That comparator is **not total** (it is irreflexive on the tie),
so `pairwise_mergeSort` does not apply to it directly.  We route through a
reflexive proxy `cmpHS'` (`≥` on the tie-break), which is total and transitive,
and which agrees with `cmpHS` on triples with distinct positions — and the
sweep's triples all have distinct positions. -/

open List in
/-- Two comparators that agree on all **distinct** members of a `Nodup` list produce the
same `mergeSort`.  (The diagonal `a = b` never matters: it is excluded by the `a ≠ b`
hypothesis, and `merge` only ever compares elements of the two disjoint halves.) -/
theorem mergeSort_congr {α} (le₂ : α → α → Bool) :
    ∀ (l : List α) (le₁ : α → α → Bool), l.Nodup →
      (∀ a ∈ l, ∀ b ∈ l, a ≠ b → le₁ a b = le₂ a b) → l.mergeSort le₁ = l.mergeSort le₂ := by
  intro l le₁
  induction l, le₁ using List.mergeSort.induct with
  | case1 le => intro _ _; simp
  | case2 le a => intro _ _; simp
  | case3 a b xs le lr _ _ ih1 ih2 =>
    intro hnd hle
    have happ : (lr.1.1 : List α) ++ lr.2.1 = a :: b :: xs :=
      List.MergeSort.Internal.splitInTwo_fst_append_splitInTwo_snd _
    have hsubT : lr.1.1 <+ a :: b :: xs := by
      have := List.sublist_append_left lr.1.1 lr.2.1; rwa [happ] at this
    have hsubD : lr.2.1 <+ a :: b :: xs := by
      have := List.sublist_append_right lr.1.1 lr.2.1; rwa [happ] at this
    have hdisj : ∀ x ∈ lr.1.1, x ∉ lr.2.1 := by
      have h := hnd; rw [← happ, List.nodup_append] at h
      exact fun x hx hx2 => (h.2.2 x hx x hx2) rfl
    have hL : (a :: b :: xs).mergeSort le
        = (lr.1.1.mergeSort le).merge (lr.2.1.mergeSort le) le := by rw [List.mergeSort]
    have hR : (a :: b :: xs).mergeSort le₂
        = (lr.1.1.mergeSort le₂).merge (lr.2.1.mergeSort le₂) le₂ := by rw [List.mergeSort]
    rw [hL, hR]
    rw [ih1 (hnd.sublist hsubT) (fun x hx y hy h => hle x (hsubT.subset hx) y (hsubT.subset hy) h)]
    rw [ih2 (hnd.sublist hsubD) (fun x hx y hy h => hle x (hsubD.subset hx) y (hsubD.subset hy) h)]
    have hm := List.map_merge (f := id) (r := le) (s := le₂)
      (l := lr.1.1.mergeSort le₂) (l' := lr.2.1.mergeSort le₂)
      (fun x hx y hy => hle x (hsubT.subset (List.mem_mergeSort.mp hx))
        y (hsubD.subset (List.mem_mergeSort.mp hy))
        (fun hxy => hdisj x (List.mem_mergeSort.mp hx) (hxy ▸ List.mem_mergeSort.mp hy)))
    simpa using hm

/-- The indexed triples `(starting height, position, step)` that `heightSweep` sorts. -/
def sweepIdx (P : List Step) : List (ℤ × ℕ × Step) :=
  P.zipIdx.map (fun p => (height P p.2, p.2, p.1))

/-- The strict comparator used by `heightSweep`. -/
def cmpHS (a b : ℤ × ℕ × Step) : Bool :=
  if a.1 < b.1 then true else if a.1 > b.1 then false else a.2.1 > b.2.1

/-- A reflexive proxy comparator (`≥` on the tie-break): total and transitive. -/
def cmpHS' (a b : ℤ × ℕ × Step) : Bool :=
  if a.1 < b.1 then true else if a.1 > b.1 then false else a.2.1 ≥ b.2.1

theorem heightSweep_eq (P : List Step) :
    heightSweep P = ((sweepIdx P).mergeSort cmpHS).map (·.2.2) := by
  unfold heightSweep sweepIdx cmpHS; rfl

theorem cmpHS'_total (a b : ℤ × ℕ × Step) : cmpHS' a b || cmpHS' b a := by
  unfold cmpHS'; split_ifs <;> simp_all; omega

theorem cmpHS'_trans (a b c : ℤ × ℕ × Step) :
    cmpHS' a b → cmpHS' b c → cmpHS' a c := by
  unfold cmpHS'; split_ifs <;> simp_all <;> omega

theorem cmpHS_eq_cmpHS'_of_ne_pos (a b : ℤ × ℕ × Step) (h : a.2.1 ≠ b.2.1) :
    cmpHS a b = cmpHS' a b := by
  unfold cmpHS cmpHS'; split_ifs <;> simp_all; omega

theorem nodup_pos_sweepIdx (P : List Step) :
    ((sweepIdx P).map (·.2.1)).Nodup := by
  unfold sweepIdx
  rw [List.map_map]
  have hcomp : ((·.2.1) ∘ fun p : Step × ℕ => (height P p.2, p.2, p.1)) = Prod.snd := by
    funext p; rfl
  rw [hcomp, List.zipIdx_map_snd]
  exact List.nodup_range'

theorem nodup_sweepIdx (P : List Step) : (sweepIdx P).Nodup :=
  (nodup_pos_sweepIdx P).of_map _

/-- A sweep triple is determined by its position. -/
theorem sweepIdx_eq_of_pos_eq (P : List Step) {a b : ℤ × ℕ × Step}
    (ha : a ∈ sweepIdx P) (hb : b ∈ sweepIdx P) (hpos : a.2.1 = b.2.1) : a = b := by
  unfold sweepIdx at ha hb
  rw [List.mem_map] at ha hb
  obtain ⟨⟨s, i⟩, hi, rfl⟩ := ha
  obtain ⟨⟨t, j⟩, hj, rfl⟩ := hb
  simp only at hpos
  subst hpos
  obtain ⟨_, hs⟩ := List.mem_zipIdx' hi
  obtain ⟨_, ht⟩ := List.mem_zipIdx' hj
  simp only [Prod.mk.injEq, true_and]
  rw [hs, ht]

/-- `heightSweep` written via the total proxy comparator `cmpHS'`. -/
theorem heightSweep_eq' (P : List Step) :
    heightSweep P = ((sweepIdx P).mergeSort cmpHS').map (·.2.2) := by
  rw [heightSweep_eq]
  congr 1
  exact mergeSort_congr cmpHS' (sweepIdx P) cmpHS (nodup_sweepIdx P)
    (fun a ha b hb hab => cmpHS_eq_cmpHS'_of_ne_pos a b
      (fun hpos => hab (sweepIdx_eq_of_pos_eq P ha hb hpos)))

/-! ### Cumulative crossing identity -/

/-- `U`-steps at starting height `< t` among the first `n` positions. -/
def belowUpre (P : List Step) (n : ℕ) (t : ℤ) : ℕ :=
  (List.range n).countP (fun i => decide (height P i < t ∧ P[i]? = some U))

/-- `D`-steps at starting height `≤ t` among the first `n` positions. -/
def atMostDpre (P : List Step) (n : ℕ) (t : ℤ) : ℕ :=
  (List.range n).countP (fun i => decide (height P i ≤ t ∧ P[i]? = some D))

theorem belowUpre_succ (P : List Step) (n : ℕ) (t : ℤ) :
    belowUpre P (n + 1) t
      = belowUpre P n t + (if height P n < t ∧ P[n]? = some U then 1 else 0) := by
  unfold belowUpre
  rw [List.range_succ, List.countP_append, List.countP_singleton]
  congr 1
  by_cases hc : height P n < t ∧ P[n]? = some U
  · rw [if_pos hc, if_pos (by simpa using hc)]
  · rw [if_neg hc, if_neg (by simpa using hc)]

theorem atMostDpre_succ (P : List Step) (n : ℕ) (t : ℤ) :
    atMostDpre P (n + 1) t
      = atMostDpre P n t + (if height P n ≤ t ∧ P[n]? = some D then 1 else 0) := by
  unfold atMostDpre
  rw [List.range_succ, List.countP_append, List.countP_singleton]
  congr 1
  by_cases hc : height P n ≤ t ∧ P[n]? = some D
  · rw [if_pos hc, if_pos (by simpa using hc)]
  · rw [if_neg hc, if_neg (by simpa using hc)]

/-- Cumulative invariant: among the first `n` steps, the up-crossings of all levels
below `t` minus the down-crossings equals `min (height P n) t`. -/
theorem cumulative_invariant (P : List Step) (hP : IsDyckPath P) (t : ℤ) (ht : 0 ≤ t) (n : ℕ) :
    (belowUpre P n t : ℤ) - (atMostDpre P n t : ℤ) = min (height P n) t := by
  induction n with
  | zero =>
      simp only [belowUpre, atMostDpre, List.range_zero, List.countP_nil, Nat.cast_zero, sub_zero,
        height_zero]
      omega
  | succ n ih =>
      rw [belowUpre_succ, atMostDpre_succ]
      by_cases hn : n < P.length
      · have hstep := height_succ P n hn
        have hge : 0 ≤ height P n := hP.1 n (by omega)
        cases hPn : P[n] with
        | U =>
            have hUsome : P[n]? = some U := by rw [List.getElem?_eq_getElem hn, hPn]
            have hheight : height P (n + 1) = height P n + 1 := by rw [hstep, hPn]
            have hb : (if height P n < t ∧ P[n]? = some U then (1 : ℕ) else 0)
                = (if height P n < t then 1 else 0) := by
              by_cases hc : height P n < t
              · rw [if_pos ⟨hc, hUsome⟩, if_pos hc]
              · rw [if_neg (fun hx => hc hx.1), if_neg hc]
            have hd : (if height P n ≤ t ∧ P[n]? = some D then (1 : ℕ) else 0) = 0 := by
              rw [if_neg]; rintro ⟨_, hD⟩; rw [hUsome] at hD; exact absurd hD (by decide)
            rw [hb, hd, hheight]; push_cast
            split_ifs at ih ⊢ <;> omega
        | D =>
            have hDsome : P[n]? = some D := by rw [List.getElem?_eq_getElem hn, hPn]
            have hheight : height P (n + 1) = height P n - 1 := by rw [hstep, hPn]; ring
            have hg1 : 1 ≤ height P n := by
              have := hP.1 (n + 1) (by omega); rw [hheight] at this; omega
            have hb : (if height P n < t ∧ P[n]? = some U then (1 : ℕ) else 0) = 0 := by
              rw [if_neg]; rintro ⟨_, hU⟩; rw [hDsome] at hU; exact absurd hU (by decide)
            have hd : (if height P n ≤ t ∧ P[n]? = some D then (1 : ℕ) else 0)
                = (if height P n ≤ t then 1 else 0) := by
              by_cases hc : height P n ≤ t
              · rw [if_pos ⟨hc, hDsome⟩, if_pos hc]
              · rw [if_neg (fun hx => hc hx.1), if_neg hc]
            rw [hb, hd, hheight]; push_cast
            split_ifs at ih ⊢ <;> omega
      · have hnone : P[n]? = none := by rw [List.getElem?_eq_none]; omega
        have hheight : height P (n + 1) = height P n := by
          rw [height_of_length_le P (n + 1) (by omega), height_of_length_le P n (by omega)]
        rw [hheight, hnone]
        simp only [reduceCtorEq, and_false, if_false, Nat.add_zero]
        exact ih

/-- **Cumulative crossing identity.**  For a Dyck path and any level `t ≥ 0`, the
total number of `U`-steps below height `t` equals the number of `D`-steps at height
`≤ t`. -/
theorem belowU_eq_atMostD (P : List Step) (hP : IsDyckPath P) (t : ℤ) (ht : 0 ≤ t) :
    belowUpre P P.length t = atMostDpre P P.length t := by
  have hinv := cumulative_invariant P hP t ht P.length
  rw [hP.2] at hinv
  simp only [min_eq_left ht] at hinv
  omega

/-! ### Assembly: from the sorted normal form to the Dyck property -/

/-- Position-count `belowUpre` as a count over the sweep triples. -/
theorem belowUpre_eq_count (P : List Step) (t : ℤ) :
    belowUpre P P.length t = (sweepIdx P).countP (fun tr => decide (tr.1 < t ∧ tr.2.2 = U)) := by
  unfold belowUpre sweepIdx
  rw [List.range_eq_range', ← List.zipIdx_map_snd (l := P) (i := 0),
    List.countP_map, List.countP_map]
  apply List.countP_congr
  intro x hx
  obtain ⟨hi, hs⟩ := List.mem_zipIdx' hx
  simp only [Function.comp_apply, decide_eq_true_eq, List.getElem?_eq_getElem hi, ← hs,
    Option.some.injEq]

/-- Position-count `atMostDpre` as a count over the sweep triples. -/
theorem atMostDpre_eq_count (P : List Step) (t : ℤ) :
    atMostDpre P P.length t = (sweepIdx P).countP (fun tr => decide (tr.1 ≤ t ∧ tr.2.2 = D)) := by
  unfold atMostDpre sweepIdx
  rw [List.range_eq_range', ← List.zipIdx_map_snd (l := P) (i := 0),
    List.countP_map, List.countP_map]
  apply List.countP_congr
  intro x hx
  obtain ⟨hi, hs⟩ := List.mem_zipIdx' hx
  simp only [Function.comp_apply, decide_eq_true_eq, List.getElem?_eq_getElem hi, ← hs,
    Option.some.injEq]

/-- The central inequality: every prefix of the sorted sweep has at least as many
`U`-triples as `D`-triples. -/
theorem take_D_le_U (P : List Step) (hP : IsDyckPath P) (k : ℕ)
    (hk : k ≤ ((sweepIdx P).mergeSort cmpHS').length) :
    (((sweepIdx P).mergeSort cmpHS').take k).countP (fun tr => tr.2.2 == D)
      ≤ (((sweepIdx P).mergeSort cmpHS').take k).countP (fun tr => tr.2.2 == U) := by
  set T := (sweepIdx P).mergeSort cmpHS' with hT
  have hperm : T.Perm (sweepIdx P) := List.mergeSort_perm _ _
  have hpair : T.Pairwise (fun a b => cmpHS' a b = true) :=
    List.pairwise_mergeSort cmpHS'_trans cmpHS'_total _
  have hsorted : ∀ i j (hi : i < T.length) (hj : j < T.length), i < j → T[i].1 ≤ T[j].1 := by
    intro i j hi hj hij
    have hcmp := (List.pairwise_iff_getElem.mp hpair) i j hi hj hij
    unfold cmpHS' at hcmp; split_ifs at hcmp with h1 h2 <;> simp_all; omega
  have hsorted_le : ∀ i j (hi : i < T.length) (hj : j < T.length), i ≤ j → T[i].1 ≤ T[j].1 := by
    intro i j hi hj hij
    rcases Nat.lt_or_eq_of_le hij with hlt | rfl
    · exact hsorted i j hi hj hlt
    · exact le_refl _
  have htri_nn : ∀ tr ∈ T, 0 ≤ tr.1 := by
    intro tr htr
    have h2 : tr ∈ sweepIdx P := hperm.subset htr
    unfold sweepIdx at h2
    obtain ⟨⟨s, i⟩, hi, rfl⟩ := List.mem_map.mp h2
    obtain ⟨hi', _⟩ := List.mem_zipIdx' hi
    exact hP.1 i hi'.le
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0; simp
  have hk1 : k - 1 < T.length := by omega
  set t := T[k - 1].1 with ht
  have ht_nn : 0 ≤ t := htri_nn _ (List.getElem_mem _)
  have hle_take : ∀ tr ∈ T.take k, tr.1 ≤ t := by
    intro tr htr
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp htr
    rw [List.length_take] at hj
    have hjT : j < T.length := by omega
    have hval : tr.1 = T[j].1 := by rw [← hjeq]; congr 1; exact List.getElem_take
    have hbound : T[j].1 ≤ T[k - 1].1 := hsorted_le j (k - 1) hjT hk1 (by omega)
    omega
  have hge_drop : ∀ tr ∈ T.drop k, ¬ (tr.1 < t) := by
    intro tr htr
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp htr
    rw [List.length_drop] at hj
    have hval : tr.1 = T[k + j].1 := by rw [← hjeq]; congr 1; exact List.getElem_drop
    have hcmp := hsorted (k - 1) (k + j) hk1 (by omega) (by omega)
    omega
  have hcD : (T.take k).countP (fun tr => tr.2.2 == D) ≤ atMostDpre P P.length t := by
    rw [atMostDpre_eq_count, ← hperm.countP_eq]
    calc (T.take k).countP (fun tr => tr.2.2 == D)
        = (T.take k).countP (fun tr => decide (tr.1 ≤ t ∧ tr.2.2 = D)) := by
          apply List.countP_congr; intro tr htr
          have hle := hle_take tr htr
          simp only [beq_iff_eq, decide_eq_true_eq]
          exact ⟨fun hd => ⟨hle, hd⟩, fun hd => hd.2⟩
      _ ≤ T.countP (fun tr => decide (tr.1 ≤ t ∧ tr.2.2 = D)) :=
          List.Sublist.countP_le (List.take_sublist _ _)
  have hcU : belowUpre P P.length t ≤ (T.take k).countP (fun tr => tr.2.2 == U) := by
    rw [belowUpre_eq_count, ← hperm.countP_eq]
    have hsplit : T.countP (fun tr => decide (tr.1 < t ∧ tr.2.2 = U))
        = (T.take k).countP (fun tr => decide (tr.1 < t ∧ tr.2.2 = U)) := by
      conv_lhs => rw [← List.take_append_drop k T]
      rw [List.countP_append]
      have hdrop0 : (T.drop k).countP (fun tr => decide (tr.1 < t ∧ tr.2.2 = U)) = 0 := by
        rw [List.countP_eq_zero]; intro tr htr hh
        simp only [decide_eq_true_eq] at hh; exact hge_drop tr htr hh.1
      rw [hdrop0, Nat.add_zero]
    rw [hsplit]
    apply List.countP_mono_left
    intro tr _ hh
    simp only [decide_eq_true_eq] at hh; simp only [beq_iff_eq]; exact hh.2
  calc (T.take k).countP (fun tr => tr.2.2 == D)
      ≤ atMostDpre P P.length t := hcD
    _ = belowUpre P P.length t := (belowU_eq_atMostD P hP t ht_nn).symm
    _ ≤ (T.take k).countP (fun tr => tr.2.2 == U) := hcU

/-- **`thm:narayana-sweep` (`sec:narayana-sweep`, paper-full-new.tex).**
The height sweep H (with right-to-left tie-breaking) preserves Dyck paths:
if `P ∈ D_n` then `H(P) ∈ D_n`. -/
theorem isDyckPath_heightSweep (P : List Step) (hP : IsDyckPath P) :
    IsDyckPath (heightSweep P) := by
  refine ⟨fun k hk => ?_, by rw [height_heightSweep_length]; exact hP.2⟩
  rw [height_eq_count, heightSweep_eq', ← List.map_take, List.count_eq_countP,
    List.count_eq_countP, List.countP_map, List.countP_map]
  have hkle : k ≤ ((sweepIdx P).mergeSort cmpHS').length := by
    have hlen : (heightSweep P).length = ((sweepIdx P).mergeSort cmpHS').length := by
      rw [heightSweep_eq', List.length_map]
    rw [hlen] at hk; exact hk
  have hkey := take_D_le_U P hP k hkle
  simp only [Function.comp_def]
  omega

/-
**`thm:narayana-sweep` (`sec:narayana-sweep`, paper-full-new.tex).**
The height sweep preserves length.
-/
theorem length_heightSweep (P : List Step) :
    (heightSweep P).length = P.length := by
      -- The length of the height sweep is equal to the length of the input list because it processes each element exactly once.
      simp [heightSweep]

/-- The height sweep preserves semilength. -/
theorem semilength_heightSweep (P : List Step) :
    semilength (heightSweep P) = semilength P := by
  unfold semilength
  rw [length_heightSweep]

/-! ### Phase 1: Dyck-path matching (parenthesis nesting)

`matchD P i` is the down-step that closes the up-step at position `i` — the first
return of the height to its value just before `i`.  This is the standard
parenthesis matching, the backbone of the contour-forest argument. -/

/-- Positions after `i` at which the height has returned to (at most) its value
before `i`. -/
def returnSet (P : List Step) (i : ℕ) : Set ℕ := {j | i < j ∧ height P (j + 1) ≤ height P i}

/-- The matching down-step of the up-step at position `i`. -/
noncomputable def matchD (P : List Step) (i : ℕ) : ℕ := sInf (returnSet P i)

/-- The return set is nonempty (the path eventually returns to height `0`). -/
theorem returnSet_nonempty (P : List Step) (hP : IsDyckPath P) (i : ℕ) (hi : i < P.length) :
    (returnSet P i).Nonempty := by
  refine ⟨P.length, hi, ?_⟩
  rw [height_of_length_le P (P.length + 1) (by omega), hP.2]
  exact hP.1 i hi.le

theorem matchD_mem (P : List Step) (hP : IsDyckPath P) (i : ℕ) (hi : i < P.length) :
    i < matchD P i ∧ height P (matchD P i + 1) ≤ height P i :=
  Nat.sInf_mem (returnSet_nonempty P hP i hi)

/-- The height stays strictly above its pre-`i` value throughout `(i, matchD P i]`. -/
theorem matchD_height_above (P : List Step) (_hP : IsDyckPath P) (i : ℕ) (hi : i < P.length)
    (hU : P[i] = U) :
    ∀ k, i < k → k ≤ matchD P i → height P i < height P k := by
  have hup : height P (i + 1) = height P i + 1 := height_succ_of_get_U P i hi hU
  have hbelow : ∀ j, i < j → j < matchD P i → height P i < height P (j + 1) := by
    intro j hij hjm
    by_contra hle; push Not at hle
    have : matchD P i ≤ j := Nat.sInf_le (show j ∈ returnSet P i from ⟨hij, hle⟩)
    omega
  intro k hik hkm
  rcases Nat.lt_or_ge i (k - 1) with h1 | h1
  · have := hbelow (k - 1) h1 (by omega); rwa [show k - 1 + 1 = k by omega] at this
  · have hk : k = i + 1 := by omega
    rw [hk, hup]; omega

theorem matchD_lt_length (P : List Step) (hP : IsDyckPath P) (i : ℕ) (hi : i < P.length)
    (hU : P[i] = U) : matchD P i < P.length := by
  by_contra hge; push Not at hge
  have hab := matchD_height_above P hP i hi hU P.length hi hge
  rw [hP.2] at hab
  have := hP.1 i hi.le; omega

/-- **Matching specification.**  The closing down-step: `P[m] = D`, its height is
one above the pre-`i` height, and the height returns there after it. -/
theorem matchD_props (P : List Step) (hP : IsDyckPath P) (i : ℕ) (hi : i < P.length)
    (hU : P[i] = U) :
    P[matchD P i]'(matchD_lt_length P hP i hi hU) = D ∧
    height P (matchD P i) = height P i + 1 ∧
    height P (matchD P i + 1) = height P i := by
  have hmlt : matchD P i < P.length := matchD_lt_length P hP i hi hU
  have habove : height P i < height P (matchD P i) :=
    matchD_height_above P hP i hi hU (matchD P i) (matchD_mem P hP i hi).1 le_rfl
  have hbelow : height P (matchD P i + 1) ≤ height P i := (matchD_mem P hP i hi).2
  have hD : P[matchD P i]'hmlt = D := by
    cases hPm : P[matchD P i]'hmlt with
    | D => rfl
    | U =>
        have hstep := height_succ_of_get_U P (matchD P i) hmlt hPm
        omega
  have hstep := height_succ_of_get_D P (matchD P i) hmlt hD
  exact ⟨hD, by omega, by omega⟩

/-- Positions before `d` at which the height has (at most) returned to its value
after `d`.  Used to define the inverse matching (opening up-step of a down-step). -/
def openSet (P : List Step) (d : ℕ) : Set ℕ := {i | i < d ∧ height P i ≤ height P (d + 1)}

/-- The matching up-step opened by the down-step at `d`. -/
noncomputable def matchU (P : List Step) (d : ℕ) : ℕ := sSup (openSet P d)

theorem openSet_bddAbove (P : List Step) (d : ℕ) : BddAbove (openSet P d) :=
  ⟨d, fun _i hi => le_of_lt hi.1⟩

/-- The opening set is nonempty for a genuine down-step (the path climbed to its
current level earlier). -/
theorem openSet_nonempty (P : List Step) (hP : IsDyckPath P) (d : ℕ) (hd : d < P.length)
    (hD : P[d] = D) : (openSet P d).Nonempty := by
  have hdpos : 0 < d := by
    by_contra h; push Not at h
    have hd0 : d = 0 := by omega
    subst hd0
    have hstep := height_succ_of_get_D P 0 hd hD
    simp only [Nat.zero_add, height_zero] at hstep
    have := hP.1 1 (by omega)
    omega
  refine ⟨0, hdpos, ?_⟩
  rw [height_zero]
  exact hP.1 (d + 1) (by omega)

theorem matchU_mem (P : List Step) (hP : IsDyckPath P) (d : ℕ) (hd : d < P.length)
    (hD : P[d] = D) : matchU P d < d ∧ height P (matchU P d) ≤ height P (d + 1) :=
  Nat.sSup_mem (openSet_nonempty P hP d hd hD) (openSet_bddAbove P d)

/-- The height stays strictly above the return level throughout `(matchU P d, d]`. -/
theorem matchU_height_above (P : List Step) (_hP : IsDyckPath P) (d : ℕ) (hd : d < P.length)
    (hD : P[d] = D) :
    ∀ k, matchU P d < k → k ≤ d → height P (d + 1) < height P k := by
  have hstep := height_succ_of_get_D P d hd hD
  have habove : ∀ j, matchU P d < j → j < d → height P (d + 1) < height P j := by
    intro j hmj hjd
    by_contra hle; push Not at hle
    have : j ≤ matchU P d := le_csSup (openSet_bddAbove P d) ⟨hjd, hle⟩
    omega
  intro k hmk hkd
  rcases Nat.lt_or_eq_of_le hkd with hlt | rfl
  · exact habove k hmk hlt
  · omega

/-- **Inverse matching specification.**  The opening up-step: `P[matchU P d] = U`,
its height is one below the post-`d` height, and `matchD` sends it back to `d`. -/
theorem matchU_props (P : List Step) (hP : IsDyckPath P) (d : ℕ) (hd : d < P.length)
    (hD : P[d] = D) :
    P[matchU P d]'(by have := (matchU_mem P hP d hd hD).1; omega) = U ∧
    height P (matchU P d) = height P (d + 1) ∧
    matchD P (matchU P d) = d := by
  have hmlt : matchU P d < d := (matchU_mem P hP d hd hD).1
  have hUi : matchU P d < P.length := by omega
  have hle : height P (matchU P d) ≤ height P (d + 1) := (matchU_mem P hP d hd hD).2
  have habove1 : height P (d + 1) < height P (matchU P d + 1) :=
    matchU_height_above P hP d hd hD (matchU P d + 1) (by omega) (by omega)
  have hU : P[matchU P d]'hUi = U := by
    cases hPm : P[matchU P d]'hUi with
    | U => rfl
    | D => have hstep := height_succ_of_get_D P (matchU P d) hUi hPm; omega
  have hstepU := height_succ_of_get_U P (matchU P d) hUi hU
  have heq : height P (matchU P d) = height P (d + 1) := by omega
  refine ⟨hU, heq, ?_⟩
  have hd_in : d ∈ returnSet P (matchU P d) := ⟨hmlt, by rw [heq]⟩
  have hle_d : matchD P (matchU P d) ≤ d := Nat.sInf_le hd_in
  have hge_d : d ≤ matchD P (matchU P d) := by
    by_contra hlt; push Not at hlt
    have hmm := matchD_mem P hP (matchU P d) hUi
    have hb := matchU_height_above P hP d hd hD (matchD P (matchU P d) + 1) (by omega) (by omega)
    rw [heq] at hmm
    omega
  omega

/-- The two matchings are mutually inverse: `matchU` undoes `matchD`. -/
theorem matchU_matchD (P : List Step) (hP : IsDyckPath P) (i : ℕ) (hi : i < P.length)
    (hU : P[i] = U) : matchU P (matchD P i) = i := by
  have hmh : height P (matchD P i + 1) = height P i := (matchD_props P hP i hi hU).2.2
  have hi_mem : i ∈ openSet P (matchD P i) :=
    ⟨(matchD_mem P hP i hi).1, le_of_eq hmh.symm⟩
  have hub : ∀ j ∈ openSet P (matchD P i), j ≤ i := by
    intro j hj
    by_contra hlt; push Not at hlt
    obtain ⟨hjm, hjh⟩ := hj
    have hab := matchD_height_above P hP i hi hU j hlt (by omega)
    rw [hmh] at hjh
    omega
  exact le_antisymm (csSup_le ⟨i, hi_mem⟩ hub) (le_csSup (openSet_bddAbove P (matchD P i)) hi_mem)

/-! ### Phase 2a: the combinatorial core (count = `dr(P)`) -/

/-- `doubleRises` as the cardinality of a `getElem?`-based filter over all indices. -/
theorem doubleRises_eq_card (P : List Step) :
    doubleRises P = ((Finset.range P.length).filter
      (fun i => P[i]? = some U ∧ P[i + 1]? = some U)).card := by
  rw [doubleRises,
    show (List.range (P.length - 1)).countP (fun i => decide (P[i]! = U ∧ P[i + 1]! = U))
      = Nat.count (fun i => P[i]! = U ∧ P[i + 1]! = U) (P.length - 1) from rfl,
    Nat.count_eq_card_filter_range]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hp⟩
    have hil : i < P.length := by omega
    have hi1l : i + 1 < P.length := by omega
    rw [getElem!_pos P i hil, getElem!_pos P (i + 1) hi1l] at hp
    exact ⟨hil, by rw [List.getElem?_eq_getElem hil, hp.1], by rw [List.getElem?_eq_getElem hi1l, hp.2]⟩
  · rintro ⟨hil, hU, hU1⟩
    have hi1l : i + 1 < P.length := by
      by_contra h; push Not at h
      rw [List.getElem?_eq_none (by omega)] at hU1; exact absurd hU1 (by simp)
    refine ⟨by omega, ?_⟩
    rw [getElem!_pos P i hil, getElem!_pos P (i + 1) hi1l]
    rw [List.getElem?_eq_getElem hil] at hU
    rw [List.getElem?_eq_getElem hi1l] at hU1
    exact ⟨Option.some.inj hU, Option.some.inj hU1⟩

open Finset in
/-- **Combinatorial core.**  The matching identifies "the closing `D` of an
internal vertex" with "the first-child `UU`", so the two counts agree: the number
of down-steps `q` whose opened vertex is internal (`P[matchU q + 1] = U`) is
exactly `doubleRises P`.  Bijection: `q ↦ matchU P q`, inverse `i ↦ matchD P i`. -/
theorem matchU_count_eq_doubleRises (P : List Step) (hP : IsDyckPath P) :
    ((Finset.range P.length).filter
      (fun q => P[q]? = some D ∧ P[matchU P q + 1]? = some U)).card = doubleRises P := by
  rw [doubleRises_eq_card]
  apply Finset.card_nbij' (matchU P) (matchD P)
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    obtain ⟨hql, hqD, hqU⟩ := hq
    have hqDget : P[q]'hql = D := by
      rw [List.getElem?_eq_getElem hql] at hqD; exact Option.some.inj hqD
    have hmU := matchU_props P hP q hql hqDget
    have hmlt : matchU P q < q := (matchU_mem P hP q hql hqDget).1
    exact ⟨by omega, by rw [List.getElem?_eq_getElem (by omega : matchU P q < P.length), hmU.1], hqU⟩
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    obtain ⟨hil, hiU, hiU1⟩ := hi
    have hiUget : P[i]'hil = U := by
      rw [List.getElem?_eq_getElem hil] at hiU; exact Option.some.inj hiU
    have hmD := matchD_props P hP i hil hiUget
    have hmlt := matchD_lt_length P hP i hil hiUget
    refine ⟨hmlt, by rw [List.getElem?_eq_getElem hmlt, hmD.1], ?_⟩
    rw [matchU_matchD P hP i hil hiUget]; exact hiU1
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hql, hqD, _⟩ := hq
    have hqDget : P[q]'hql = D := by
      rw [List.getElem?_eq_getElem hql] at hqD; exact Option.some.inj hqD
    exact (matchU_props P hP q hql hqDget).2.2
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hil, hiU, _⟩ := hi
    have hiUget : P[i]'hil = U := by
      rw [List.getElem?_eq_getElem hil] at hiU; exact Option.some.inj hiU
    exact matchU_matchD P hP i hil hiUget

/-! ### Toward the normal form: ordering within a height level

The sweep lists steps by increasing height and, within a height level, by
*decreasing* input position.  `sweep_pos_desc` records the second half: any two
sorted triples at the same height appear in strictly decreasing position order.
This is the first structural step toward the contour-forest normal form
`H(P) = U^r ∏_v D U^{c(v)}` that closes `thm:narayana-sweep` (the `dr`/`val` swap). -/

/-- On equal-height triples, the proxy comparator reduces to `≥` on position. -/
theorem cmpHS'_pos_of_eq_height (a b : ℤ × ℕ × Step) (h : cmpHS' a b = true) (hh : a.1 = b.1) :
    b.2.1 ≤ a.2.1 := by
  unfold cmpHS' at h; rw [hh] at h; simp only [lt_self_iff_false, if_false, decide_eq_true_eq] at h; exact h

/-- Within a height level the sorted sweep is in strictly decreasing position
order. -/
theorem sweep_pos_desc (P : List Step) (i j : ℕ)
    (hi : i < ((sweepIdx P).mergeSort cmpHS').length)
    (hj : j < ((sweepIdx P).mergeSort cmpHS').length) (hij : i < j)
    (hheight : ((sweepIdx P).mergeSort cmpHS')[i].1 = ((sweepIdx P).mergeSort cmpHS')[j].1) :
    ((sweepIdx P).mergeSort cmpHS')[j].2.1 < ((sweepIdx P).mergeSort cmpHS')[i].2.1 := by
  set T := (sweepIdx P).mergeSort cmpHS' with hT
  have hperm : T.Perm (sweepIdx P) := List.mergeSort_perm _ _
  have hpair : T.Pairwise (fun a b => cmpHS' a b = true) :=
    List.pairwise_mergeSort cmpHS'_trans cmpHS'_total _
  have hcmp := (List.pairwise_iff_getElem.mp hpair) i j hi hj hij
  have hnd : T.Nodup := List.nodup_mergeSort.mpr (nodup_sweepIdx P)
  have hposne : T[i].2.1 ≠ T[j].2.1 := by
    intro he
    have hmem_i : T[i] ∈ sweepIdx P := hperm.subset (List.getElem_mem hi)
    have hmem_j : T[j] ∈ sweepIdx P := hperm.subset (List.getElem_mem hj)
    have heq : T[i] = T[j] := sweepIdx_eq_of_pos_eq P hmem_i hmem_j he
    rw [hnd.getElem_inj_iff] at heq
    omega
  exact lt_of_le_of_ne (cmpHS'_pos_of_eq_height T[i] T[j] hcmp hheight) (Ne.symm hposne)

/-! ### A strict order on sweep triples, and the sorted-adjacency lemma

To pin down *consecutive* elements of the sorted sweep we use the strict order
`klt` (height ascending, then position descending), which `cmpHS'` refines on
triples with distinct positions.  The key abstract fact `adjacent_of_between`
says: in a list whose `getElem` is `klt`-monotone, two members with nothing
strictly between them are at consecutive indices. -/

/-- Strict order on sweep triples: height ascending, then position descending. -/
def klt (a b : ℤ × ℕ × Step) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ b.2.1 < a.2.1)

theorem klt_irrefl (a : ℤ × ℕ × Step) : ¬ klt a a := by unfold klt; omega

theorem klt_trans (a b c : ℤ × ℕ × Step) : klt a b → klt b c → klt a c := by
  intro h1 h2; unfold klt at h1 h2 ⊢; omega

/-- On triples with distinct positions, `cmpHS'` implies the strict order `klt`. -/
theorem klt_of_cmpHS' (a b : ℤ × ℕ × Step) (h : cmpHS' a b = true) (hpos : a.2.1 ≠ b.2.1) :
    klt a b := by
  rcases lt_trichotomy a.1 b.1 with h1 | h1 | h1
  · exact Or.inl h1
  · have := cmpHS'_pos_of_eq_height a b h h1; right; exact ⟨h1, by omega⟩
  · exfalso; unfold cmpHS' at h
    rw [if_neg (by omega), if_pos (by omega)] at h; simp at h

/-- `getElem` of the sorted sweep is `klt`-monotone. -/
theorem klt_getElem (P : List Step) {i j : ℕ}
    (hi : i < ((sweepIdx P).mergeSort cmpHS').length)
    (hj : j < ((sweepIdx P).mergeSort cmpHS').length) (hij : i < j) :
    klt ((sweepIdx P).mergeSort cmpHS')[i] ((sweepIdx P).mergeSort cmpHS')[j] := by
  set T := (sweepIdx P).mergeSort cmpHS' with hT
  have hpair : T.Pairwise (fun a b => cmpHS' a b = true) :=
    List.pairwise_mergeSort cmpHS'_trans cmpHS'_total _
  have hcmp := (List.pairwise_iff_getElem.mp hpair) i j hi hj hij
  have hperm : T.Perm (sweepIdx P) := List.mergeSort_perm _ _
  have hnd : T.Nodup := List.nodup_mergeSort.mpr (nodup_sweepIdx P)
  have hposne : T[i].2.1 ≠ T[j].2.1 := by
    intro he
    have hmem_i : T[i] ∈ sweepIdx P := hperm.subset (List.getElem_mem hi)
    have hmem_j : T[j] ∈ sweepIdx P := hperm.subset (List.getElem_mem hj)
    have heq : T[i] = T[j] := sweepIdx_eq_of_pos_eq P hmem_i hmem_j he
    rw [hnd.getElem_inj_iff] at heq; omega
  exact klt_of_cmpHS' T[i] T[j] hcmp hposne

/-- **Sorted-adjacency.**  In a list whose `getElem` is strictly monotone under an
irreflexive transitive `r`, two members `x r y` with nothing strictly between are
at consecutive indices. -/
theorem adjacent_of_between {α} (r : α → α → Prop) (T : List α)
    (hmono : ∀ i j (hi : i < T.length) (hj : j < T.length), i < j → r T[i] T[j])
    (hirr : ∀ a, ¬ r a a) (htrans : ∀ a b c, r a b → r b c → r a c)
    (x y : α) (hx : x ∈ T) (hy : y ∈ T) (hxy : r x y)
    (hbtw : ∀ z ∈ T, ¬ (r x z ∧ r z y)) :
    ∃ i, T[i]? = some x ∧ T[i + 1]? = some y := by
  obtain ⟨ix, hix, hxeq⟩ := List.getElem_of_mem hx
  obtain ⟨iy, hiy, hyeq⟩ := List.getElem_of_mem hy
  have hasymm : ∀ a b, r a b → r b a → False := fun a b hab hba => hirr a (htrans a b a hab hba)
  have hltij : ix < iy := by
    rcases Nat.lt_trichotomy ix iy with h | h | h
    · exact h
    · exfalso; subst h
      have hxy' : x = y := hxeq ▸ hyeq
      exact hirr x (hxy' ▸ hxy)
    · exfalso
      have hm := hmono iy ix hiy hix h
      rw [hxeq, hyeq] at hm
      exact hasymm x y hxy hm
  have hadj : iy = ix + 1 := by
    by_contra hne
    have hlen : ix + 1 < T.length := by omega
    have h1 := hmono ix (ix + 1) hix hlen (by omega)
    have h2 := hmono (ix + 1) iy hlen hiy (by omega)
    rw [hxeq] at h1; rw [hyeq] at h2
    exact hbtw T[ix + 1] (List.getElem_mem hlen) ⟨h1, h2⟩
  exact ⟨ix, by rw [List.getElem?_eq_getElem hix, hxeq],
    by rw [show ix + 1 = iy from hadj.symm, List.getElem?_eq_getElem hiy, hyeq]⟩

/-- Length of the index list equals the path length. -/
theorem length_sweepIdx (P : List Step) : (sweepIdx P).length = P.length := by
  unfold sweepIdx; rw [List.length_map, List.length_zipIdx]

/-- The sweep triple at position `p`: `(height, position, step)`. -/
def tripleAt (P : List Step) (p : ℕ) (hp : p < P.length) : ℤ × ℕ × Step :=
  (height P p, p, P[p])

theorem tripleAt_mem (P : List Step) (p : ℕ) (hp : p < P.length) :
    tripleAt P p hp ∈ sweepIdx P := by
  unfold sweepIdx tripleAt
  rw [List.mem_map]
  exact ⟨(P[p], p), by rw [List.mem_iff_getElem]; exact
    ⟨p, by rw [List.length_zipIdx]; exact hp, by simp [List.getElem_zipIdx]⟩, rfl⟩

/-- An element of the sweep at position `p` is exactly `tripleAt P p`. -/
theorem eq_tripleAt_of_pos (P : List Step) (p : ℕ) (hp : p < P.length)
    {z : ℤ × ℕ × Step} (hz : z ∈ sweepIdx P) (hzpos : z.2.1 = p) :
    z = tripleAt P p hp :=
  sweepIdx_eq_of_pos_eq P hz (tripleAt_mem P p hp) hzpos

/-- Converse monotonicity: `klt` between two sweep entries forces index order. -/
theorem lt_of_klt_getElem (P : List Step) {a b : ℕ}
    (ha : a < ((sweepIdx P).mergeSort cmpHS').length)
    (hb : b < ((sweepIdx P).mergeSort cmpHS').length)
    (h : klt ((sweepIdx P).mergeSort cmpHS')[a] ((sweepIdx P).mergeSort cmpHS')[b]) : a < b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact hab
  · subst hab; exact absurd h (klt_irrefl _)
  · exact absurd (klt_getElem P hb ha hab) (fun hba => klt_irrefl _ (klt_trans _ _ _ h hba))

/-- No sweep entry lies strictly (in `klt`) between two consecutive entries. -/
theorem not_between_succ (P : List Step) {i : ℕ}
    (hi1 : i + 1 < ((sweepIdx P).mergeSort cmpHS').length)
    {w : ℤ × ℕ × Step} (hw : w ∈ (sweepIdx P).mergeSort cmpHS')
    (h1 : klt ((sweepIdx P).mergeSort cmpHS')[i] w)
    (h2 : klt w ((sweepIdx P).mergeSort cmpHS')[i + 1]) : False := by
  obtain ⟨k, hk, hweq⟩ := List.getElem_of_mem hw
  rw [← hweq] at h1 h2
  have hik := lt_of_klt_getElem P (by omega) hk h1
  have hki := lt_of_klt_getElem P hk hi1 h2
  omega

/-- Positions recorded in the sweep are valid indices into `P`. -/
theorem sweepIdx_pos_lt (P : List Step) {z : ℤ × ℕ × Step} (hz : z ∈ sweepIdx P) :
    z.2.1 < P.length := by
  unfold sweepIdx at hz
  rw [List.mem_map] at hz
  obtain ⟨pr, hpr, rfl⟩ := hz
  exact (List.mem_zipIdx' hpr).1

/-- `getElem?` of the swept word reads the step component of the sorted triples. -/
theorem heightSweep_getElem? (P : List Step) (i : ℕ) :
    (heightSweep P)[i]? = (((sweepIdx P).mergeSort cmpHS')[i]?).map (·.2.2) := by
  rw [heightSweep_eq', List.getElem?_map]

/-- `valleys` as the cardinality of a `getElem?`-based filter over all indices. -/
theorem valleys_eq_card (P : List Step) :
    valleys P = ((Finset.range P.length).filter
      (fun i => P[i]? = some D ∧ P[i + 1]? = some U)).card := by
  rw [valleys,
    show (List.range (P.length - 1)).countP (fun i => decide (P[i]! = D ∧ P[i + 1]! = U))
      = Nat.count (fun i => P[i]! = D ∧ P[i + 1]! = U) (P.length - 1) from rfl,
    Nat.count_eq_card_filter_range]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hp⟩
    have hil : i < P.length := by omega
    have hi1l : i + 1 < P.length := by omega
    rw [getElem!_pos P i hil, getElem!_pos P (i + 1) hi1l] at hp
    exact ⟨hil, by rw [List.getElem?_eq_getElem hil, hp.1], by rw [List.getElem?_eq_getElem hi1l, hp.2]⟩
  · rintro ⟨hil, hD, hU1⟩
    have hi1l : i + 1 < P.length := by
      by_contra h; push Not at h
      rw [List.getElem?_eq_none (by omega)] at hU1; exact absurd hU1 (by simp)
    refine ⟨by omega, ?_⟩
    rw [getElem!_pos P i hil, getElem!_pos P (i + 1) hi1l]
    rw [List.getElem?_eq_getElem hil] at hD
    rw [List.getElem?_eq_getElem hi1l] at hU1
    exact ⟨Option.some.inj hD, Option.some.inj hU1⟩

/-- The step component of a sweep entry at position `k` is `P[k]`. -/
theorem sweep_step_at (P : List Step) (k : ℕ) (hk : k < P.length) {z : ℤ × ℕ × Step}
    (hz : z ∈ sweepIdx P) (hzk : z.2.1 = k) : z.2.2 = P[k]'hk := by
  have : z = tripleAt P k hk := eq_tripleAt_of_pos P k hk hz hzk
  rw [this]; rfl

/-- The height component of a sweep entry at position `k` is `height P k`. -/
theorem sweep_height_at (P : List Step) (k : ℕ) (hk : k < P.length) {z : ℤ × ℕ × Step}
    (hz : z ∈ sweepIdx P) (hzk : z.2.1 = k) : z.1 = height P k := by
  have : z = tripleAt P k hk := eq_tripleAt_of_pos P k hk hz hzk
  rw [this]; rfl

/-- **The sort bridge (U-side).**  Valleys of the swept word are counted by the
up-steps `p` whose level-predecessor `matchD P p + 1` is a down-step.  The sorted
sweep groups by height and orders by decreasing position, so the entry just before
`tripleAt P p` is `tripleAt P (matchD P p + 1)` (the next-higher level-`h`
position); a `DU` valley there means that predecessor is a `D`. -/
theorem valleys_heightSweep_eq_Uside (P : List Step) (hP : IsDyckPath P) :
    valleys (heightSweep P) = ((Finset.range P.length).filter
      (fun p => P[p]? = some U ∧ P[matchD P p + 1]? = some D)).card := by
  set T := (sweepIdx P).mergeSort cmpHS' with hT
  have hperm : T.Perm (sweepIdx P) := List.mergeSort_perm _ _
  have hnd : T.Nodup := List.nodup_mergeSort.mpr (nodup_sweepIdx P)
  have hTlen : T.length = P.length := by rw [hT, List.length_mergeSort, length_sweepIdx]
  have hlenHP : (heightSweep P).length = T.length := by rw [hT, heightSweep_eq', List.length_map]
  have hmem : ∀ {k : ℕ} (hk : k < T.length), T[k] ∈ sweepIdx P :=
    fun hk => hperm.subset (List.getElem_mem hk)
  -- read the swept word's steps off the sorted triples
  have hHPstep : ∀ {i : ℕ} {s : Step}, (heightSweep P)[i]? = some s →
      ∃ t : ℤ × ℕ × Step, T[i]? = some t ∧ t.2.2 = s := by
    intro i s hh
    rw [heightSweep_getElem?, ← hT, Option.map_eq_some_iff] at hh
    obtain ⟨t, ht, hts⟩ := hh; exact ⟨t, ht, hts⟩
  rw [valleys_eq_card]
  apply Finset.card_bij (fun i _ => (T[i + 1]?.getD (0, 0, U)).2.1)
  · -- maps into the U-side set
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨_, hcondD, hcondU⟩ := hi
    obtain ⟨ti, htiE, htiD⟩ := hHPstep hcondD
    obtain ⟨ti1, hti1E, hti1U⟩ := hHPstep hcondU
    obtain ⟨hiT, htiG⟩ := List.getElem?_eq_some_iff.mp htiE
    obtain ⟨hi1T, hti1G⟩ := List.getElem?_eq_some_iff.mp hti1E
    set p := T[i + 1].2.1 with hp_def
    set q := T[i].2.1 with hq_def
    have hp : p < P.length := hTlen ▸ sweepIdx_pos_lt P (hmem hi1T)
    have hq : q < P.length := hTlen ▸ sweepIdx_pos_lt P (hmem hiT)
    have hval : (T[i + 1]?.getD (0, 0, U)).2.1 = p := by
      rw [hti1E, Option.getD_some, hp_def, hti1G]
    simp only [Finset.mem_filter, Finset.mem_range, hval]
    have hPpU : P[p]'hp = U := by
      have := sweep_step_at P p hp (hmem hi1T) rfl; rw [hti1G] at this; rw [← this, hti1U]
    have hPqD : P[q]'hq = D := by
      have := sweep_step_at P q hq (hmem hiT) rfl; rw [htiG] at this; rw [← this, htiD]
    have hheightI : T[i].1 = height P q := sweep_height_at P q hq (hmem hiT) rfl
    have hheightI1 : T[i + 1].1 = height P p := sweep_height_at P p hp (hmem hi1T) rfl
    have hii1 : klt T[i] T[i + 1] := klt_getElem P hiT hi1T (by omega)
    have hpm : p < matchD P p := (matchD_mem P hP p hp).1
    have hmh : height P (matchD P p + 1) = height P p := (matchD_props P hP p hp hPpU).2.2
    refine ⟨hp, by rw [List.getElem?_eq_getElem hp, hPpU], ?_⟩
    -- show `q = matchD P p + 1`, hence `P[matchD P p + 1] = P[q] = D`
    have hqeq : q = matchD P p + 1 := by
      rcases hii1 with hlt | ⟨heq, hposlt⟩
      · -- height strictly increases: impossible (the level predecessor lies between)
        exfalso
        rw [hheightI, hheightI1] at hlt
        have hpos : (0 : ℤ) ≤ height P q := hP.1 q hq.le
        have hm1lt : matchD P p + 1 < P.length := by
          by_contra hge; push Not at hge
          have hmd := matchD_lt_length P hP p hp hPpU
          have he : matchD P p + 1 = P.length := by omega
          rw [he, hP.2] at hmh; omega
        have hwmem : tripleAt P (matchD P p + 1) hm1lt ∈ T :=
          hperm.symm.subset (tripleAt_mem P (matchD P p + 1) hm1lt)
        refine not_between_succ P hi1T hwmem ?_ ?_
        · left
          show T[i].1 < (tripleAt P (matchD P p + 1) hm1lt).1
          rw [hheightI]; show height P q < height P (matchD P p + 1); rw [hmh]; exact hlt
        · right
          refine ⟨?_, ?_⟩
          · show (tripleAt P (matchD P p + 1) hm1lt).1 = T[i + 1].1
            rw [hheightI1]; exact hmh
          · show T[i + 1].2.1 < matchD P p + 1
            rw [← hp_def]; omega
      · -- same height: `p < q`; pin `q = matchD P p + 1`
        have hpq : p < q := hposlt
        have heqh : height P q = height P p := by rw [← hheightI, ← hheightI1]; exact heq
        have hqge : matchD P p + 1 ≤ q := by
          by_contra hlt; push Not at hlt
          have hle : q ≤ matchD P p := by omega
          have := matchD_height_above P hP p hp hPpU q hpq hle
          omega
        have hqle : q ≤ matchD P p + 1 := by
          by_contra hlt; push Not at hlt
          have hm1lt : matchD P p + 1 < P.length := by omega
          have hwmem : tripleAt P (matchD P p + 1) hm1lt ∈ T :=
            hperm.symm.subset (tripleAt_mem P (matchD P p + 1) hm1lt)
          refine not_between_succ P hi1T hwmem ?_ ?_
          · right
            refine ⟨?_, ?_⟩
            · show T[i].1 = (tripleAt P (matchD P p + 1) hm1lt).1
              rw [hheightI]; show height P q = height P (matchD P p + 1); rw [hmh]; exact heqh
            · show matchD P p + 1 < T[i].2.1
              rw [← hq_def]; omega
          · right
            refine ⟨?_, ?_⟩
            · show (tripleAt P (matchD P p + 1) hm1lt).1 = T[i + 1].1
              rw [hheightI1]; exact hmh
            · show T[i + 1].2.1 < matchD P p + 1
              rw [← hp_def]; omega
        omega
    rw [← hqeq, List.getElem?_eq_getElem hq, hPqD]
  · -- injectivity
    intro a ha b hb hab
    rw [Finset.mem_filter, Finset.mem_range] at ha hb
    obtain ⟨_, _, haU⟩ := ha
    obtain ⟨_, _, hbU⟩ := hb
    obtain ⟨ta, htaE, _⟩ := hHPstep haU
    obtain ⟨tb, htbE, _⟩ := hHPstep hbU
    obtain ⟨haT, htaG⟩ := List.getElem?_eq_some_iff.mp htaE
    obtain ⟨hbT, htbG⟩ := List.getElem?_eq_some_iff.mp htbE
    rw [htaE, htbE, Option.getD_some, Option.getD_some] at hab
    have hpos : T[a + 1].2.1 = T[b + 1].2.1 := by rw [htaG, htbG]; exact hab
    have heq : T[a + 1] = T[b + 1] := sweepIdx_eq_of_pos_eq P (hmem haT) (hmem hbT) hpos
    rw [hnd.getElem_inj_iff] at heq; omega
  · -- surjectivity
    intro p hp_mem
    rw [Finset.mem_filter, Finset.mem_range] at hp_mem
    obtain ⟨hp, hPpU?, hPm1D?⟩ := hp_mem
    obtain ⟨hp', hPpU⟩ := List.getElem?_eq_some_iff.mp hPpU?
    obtain ⟨hm1lt, hPm1D⟩ := List.getElem?_eq_some_iff.mp hPm1D?
    set w := tripleAt P (matchD P p + 1) hm1lt with hw_def
    set v := tripleAt P p hp with hv_def
    have hwT : w ∈ T := hperm.symm.subset (tripleAt_mem P (matchD P p + 1) hm1lt)
    have hvT : v ∈ T := hperm.symm.subset (tripleAt_mem P p hp)
    have hwh : w.1 = height P p := (matchD_props P hP p hp hPpU).2.2
    have hvh : v.1 = height P p := rfl
    have hw2 : w.2.1 = matchD P p + 1 := rfl
    have hv2 : v.2.1 = p := rfl
    have hpm : p < matchD P p := (matchD_mem P hP p hp).1
    have hwv : klt w v := by
      right; refine ⟨by rw [hwh, hvh], ?_⟩; rw [hw2, hv2]; omega
    have hbtw : ∀ z ∈ T, ¬ (klt w z ∧ klt z v) := by
      rintro z hzT ⟨hwz, hzv⟩
      have hzs : z ∈ sweepIdx P := hperm.subset hzT
      have hzlt : z.2.1 < P.length := sweepIdx_pos_lt P hzs
      have hzh : z.1 = height P z.2.1 := sweep_height_at P z.2.1 hzlt hzs rfl
      unfold klt at hwz hzv
      rw [hwh, hw2] at hwz
      rw [hvh, hv2] at hzv
      have key : height P p = z.1 ∧ p < z.2.1 ∧ z.2.1 ≤ matchD P p := by
        rcases hwz with h1 | ⟨h1a, h1b⟩ <;> rcases hzv with h2 | ⟨h2a, h2b⟩
        · omega
        · omega
        · omega
        · exact ⟨h1a, h2b, by omega⟩
      obtain ⟨hzeq, hgt, hle⟩ := key
      have := matchD_height_above P hP p hp hPpU z.2.1 hgt hle
      rw [← hzh] at this; omega
    obtain ⟨idx, hidxW, hidxV⟩ := adjacent_of_between klt T
      (fun i j hi hj hij => klt_getElem P hi hj hij) klt_irrefl klt_trans
      w v hwT hvT hwv hbtw
    obtain ⟨hidx1T, hidxVG⟩ := List.getElem?_eq_some_iff.mp hidxV
    refine ⟨idx, ?_, by rw [hidxV, Option.getD_some]; exact hv2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by rw [hlenHP]; omega, ?_, ?_⟩
    · rw [heightSweep_getElem?, ← hT, hidxW]
      show some w.2.2 = some D
      have : w.2.2 = P[matchD P p + 1]'hm1lt :=
        sweep_step_at P (matchD P p + 1) hm1lt (tripleAt_mem P (matchD P p + 1) hm1lt) rfl
      rw [this, hPm1D]
    · rw [heightSweep_getElem?, ← hT, hidxV]
      show some v.2.2 = some U
      have : v.2.2 = P[p]'hp := sweep_step_at P p hp (tripleAt_mem P p hp) rfl
      rw [this, hPpU]

/-- In a Dyck path the last step is a down-step, so every up-step has a successor. -/
theorem U_not_last (P : List Step) (hP : IsDyckPath P) (i : ℕ) (hi : i < P.length)
    (hU : P[i] = U) : i + 1 < P.length := by
  by_contra h; push Not at h
  have hieq : i + 1 = P.length := by omega
  have hstep := height_succ_of_get_U P i hi hU
  rw [hieq, hP.2] at hstep
  have := hP.1 i hi.le
  omega

/-- **Elementary identity `#UU = #DD`.**  For a Dyck path the number of `UU`
factors equals the number of `DD` factors (both equal `#D − #UD`). -/
theorem doubleRises_eq_DD (P : List Step) (hP : IsDyckPath P) :
    doubleRises P = ((Finset.range P.length).filter
      (fun i => P[i]? = some D ∧ P[i + 1]? = some D)).card := by
  classical
  rw [doubleRises_eq_card]
  set A_UU := (Finset.range P.length).filter (fun i => P[i]? = some U ∧ P[i + 1]? = some U)
    with hAUU
  set A_DD := (Finset.range P.length).filter (fun i => P[i]? = some D ∧ P[i + 1]? = some D)
    with hADD
  set A_UD := (Finset.range P.length).filter (fun i => P[i]? = some U ∧ P[i + 1]? = some D)
    with hAUD
  set Uall := (Finset.range P.length).filter (fun i => P[i]? = some U) with hUall
  set Dnext := (Finset.range P.length).filter (fun i => P[i + 1]? = some D) with hDnext
  have hsplitU : A_UU.card + A_UD.card = Uall.card := by
    have hdisj : Disjoint A_UU A_UD := by
      rw [Finset.disjoint_left]; intro i hi1 hi2
      rw [hAUU, Finset.mem_filter] at hi1; rw [hAUD, Finset.mem_filter] at hi2
      have := hi1.2.2.symm.trans hi2.2.2; simp at this
    have huni : A_UU ∪ A_UD = Uall := by
      ext i
      simp only [hAUU, hAUD, hUall, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (⟨hi, hU, _⟩ | ⟨hi, hU, _⟩) <;> exact ⟨hi, hU⟩
      · rintro ⟨hi, hU⟩
        have hU' : P[i]'hi = U := by
          rw [List.getElem?_eq_getElem hi] at hU; exact Option.some.inj hU
        have hi1 := U_not_last P hP i hi hU'
        cases hP1 : P[i + 1]'hi1 with
        | U => exact Or.inl ⟨hi, hU, by rw [List.getElem?_eq_getElem hi1, hP1]⟩
        | D => exact Or.inr ⟨hi, hU, by rw [List.getElem?_eq_getElem hi1, hP1]⟩
    rw [← huni, Finset.card_union_of_disjoint hdisj]
  have hsplitD : A_DD.card + A_UD.card = Dnext.card := by
    have hdisj : Disjoint A_DD A_UD := by
      rw [Finset.disjoint_left]; intro i hi1 hi2
      rw [hADD, Finset.mem_filter] at hi1; rw [hAUD, Finset.mem_filter] at hi2
      have := hi1.2.1.symm.trans hi2.2.1; simp at this
    have huni : A_DD ∪ A_UD = Dnext := by
      ext i
      simp only [hADD, hAUD, hDnext, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (⟨hi, _, h1⟩ | ⟨hi, _, h1⟩) <;> exact ⟨hi, h1⟩
      · rintro ⟨hi, h1⟩
        have hi1l : i + 1 < P.length := by
          by_contra h; push Not at h
          rw [List.getElem?_eq_none (by omega)] at h1; simp at h1
        have hil : i < P.length := by omega
        cases hP0 : P[i]'hil with
        | U => exact Or.inr ⟨hil, by rw [List.getElem?_eq_getElem hil, hP0], h1⟩
        | D => exact Or.inl ⟨hil, by rw [List.getElem?_eq_getElem hil, hP0], h1⟩
    rw [← huni, Finset.card_union_of_disjoint hdisj]
  have hcardUD : Uall.card = Dnext.card := by
    rw [hUall, hDnext]
    apply Finset.card_nbij' (fun i => matchD P i - 1) (fun j => matchU P (j + 1))
    · intro i hi
      dsimp only
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      obtain ⟨hil, hiU⟩ := hi
      have hiU' : P[i]'hil = U := by
        rw [List.getElem?_eq_getElem hil] at hiU; exact Option.some.inj hiU
      have hmd := matchD_props P hP i hil hiU'
      have hmdlt := matchD_lt_length P hP i hil hiU'
      have hmdpos : 1 ≤ matchD P i := by have := (matchD_mem P hP i hil).1; omega
      refine ⟨by omega, ?_⟩
      rw [show matchD P i - 1 + 1 = matchD P i by omega, List.getElem?_eq_getElem hmdlt, hmd.1]
    · intro j hj
      dsimp only
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      obtain ⟨hjl, hjD⟩ := hj
      have hj1l : j + 1 < P.length := by
        by_contra h; push Not at h; rw [List.getElem?_eq_none (by omega)] at hjD; simp at hjD
      have hjD' : P[j + 1]'hj1l = D := by
        rw [List.getElem?_eq_getElem hj1l] at hjD; exact Option.some.inj hjD
      have hmu := matchU_props P hP (j + 1) hj1l hjD'
      have hmult : matchU P (j + 1) < j + 1 := (matchU_mem P hP (j + 1) hj1l hjD').1
      exact ⟨by omega, by rw [List.getElem?_eq_getElem (by omega : matchU P (j + 1) < P.length), hmu.1]⟩
    · intro i hi
      dsimp only
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hil, hiU⟩ := hi
      have hiU' : P[i]'hil = U := by
        rw [List.getElem?_eq_getElem hil] at hiU; exact Option.some.inj hiU
      have hmdpos : 1 ≤ matchD P i := by have := (matchD_mem P hP i hil).1; omega
      rw [show matchD P i - 1 + 1 = matchD P i by omega, matchU_matchD P hP i hil hiU']
    · intro j hj
      dsimp only
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hjl, hjD⟩ := hj
      have hj1l : j + 1 < P.length := by
        by_contra h; push Not at h; rw [List.getElem?_eq_none (by omega)] at hjD; simp at hjD
      have hjD' : P[j + 1]'hj1l = D := by
        rw [List.getElem?_eq_getElem hj1l] at hjD; exact Option.some.inj hjD
      rw [(matchU_props P hP (j + 1) hj1l hjD').2.2]; omega
  omega

/-- **`Uside ≅ #DD`.**  Sending an up-step `p` to its matching down-step `matchD P p`
is a bijection from the U-side valley count onto the `DD`-factor count. -/
theorem Uside_card_eq_DD (P : List Step) (hP : IsDyckPath P) :
    ((Finset.range P.length).filter
      (fun p => P[p]? = some U ∧ P[matchD P p + 1]? = some D)).card =
    ((Finset.range P.length).filter (fun q => P[q]? = some D ∧ P[q + 1]? = some D)).card := by
  apply Finset.card_nbij' (matchD P) (matchU P)
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    obtain ⟨hpl, hpU, hpD⟩ := hp
    have hpU' : P[p]'hpl = U := by
      rw [List.getElem?_eq_getElem hpl] at hpU; exact Option.some.inj hpU
    have hmd := matchD_props P hP p hpl hpU'
    have hmdlt := matchD_lt_length P hP p hpl hpU'
    exact ⟨hmdlt, by rw [List.getElem?_eq_getElem hmdlt, hmd.1], hpD⟩
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    obtain ⟨hql, hqD, hq1D⟩ := hq
    have hqD' : P[q]'hql = D := by
      rw [List.getElem?_eq_getElem hql] at hqD; exact Option.some.inj hqD
    have hmu := matchU_props P hP q hql hqD'
    have hmult : matchU P q < q := (matchU_mem P hP q hql hqD').1
    refine ⟨by omega, by rw [List.getElem?_eq_getElem (by omega : matchU P q < P.length), hmu.1], ?_⟩
    rw [hmu.2.2]; exact hq1D
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpl, hpU, _⟩ := hp
    have hpU' : P[p]'hpl = U := by
      rw [List.getElem?_eq_getElem hpl] at hpU; exact Option.some.inj hpU
    exact matchU_matchD P hP p hpl hpU'
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hql, hqD, _⟩ := hq
    have hqD' : P[q]'hql = D := by
      rw [List.getElem?_eq_getElem hql] at hqD; exact Option.some.inj hqD
    exact (matchU_props P hP q hql hqD').2.2

/-! ### Phase 2b: `thm:narayana-sweep`, the `dr`/`val` swap

The height sweep swaps double rises and valleys: `dr(H(P)) = val(P)`.

The sort bridge is now fully proved.  The chain is:

* `valleys_heightSweep_eq_Uside`: `val(H(P)) = #{p : P[p] = U ∧ P[matchD P p+1] = D}`
  — the *sorted-adjacency* step.  By `klt`-monotonicity of the sweep the entry just
  before `tripleAt P p` is `tripleAt P (matchD P p + 1)` (the next-higher level-`h`
  position, nothing between by `matchD_height_above`), so a `DU` valley there means
  that predecessor is a `D`.
* `Uside_card_eq_DD`: `p ↦ matchD P p` rebrackets this as `#DD(P)`.
* `doubleRises_eq_DD`: `#DD(P) = #UU(P) = dr(P)` (elementary, `#U = #D`).

Finally `val + dr = n − 1` (`valleys_add_doubleRises`) turns `val(H(P)) = dr(P)`
into `dr(H(P)) = val(P)`. -/
theorem doubleRises_heightSweep_eq_valleys (P : List Step) (hP : IsDyckPath P)
    (hn : semilength P ≥ 1) :
    doubleRises (heightSweep P) = valleys P := by
  -- `val(H(P)) = #DD(P) = dr(P)`, then `val + dr = n - 1`.
  have hHP : IsDyckPath (heightSweep P) := isDyckPath_heightSweep P hP
  have hsem : semilength (heightSweep P) = semilength P := semilength_heightSweep P
  have hvalH := valleys_add_doubleRises (heightSweep P) hHP (by rw [hsem]; exact hn)
  rw [hsem] at hvalH
  have hvalP := valleys_add_doubleRises P hP hn
  have hbridge : valleys (heightSweep P) = doubleRises P := by
    rw [valleys_heightSweep_eq_Uside P hP, Uside_card_eq_DD P hP, ← doubleRises_eq_DD P hP]
  omega

/-- **`thm:narayana-sweep` (`sec:narayana-sweep`, paper-full-new.tex).**
The height sweep swaps valleys and double rises:
`val(H(P)) = dr(P)` for any Dyck path P. -/
theorem valleys_heightSweep_eq_doubleRises (P : List Step) (hP : IsDyckPath P)
    (hn : semilength P ≥ 1) :
    valleys (heightSweep P) = doubleRises P := by
  have hHP : IsDyckPath (heightSweep P) := isDyckPath_heightSweep P hP
  have hsem : semilength (heightSweep P) = semilength P := semilength_heightSweep P
  have hnH : semilength (heightSweep P) ≥ 1 := by
    rw [hsem]
    exact hn
  have hsumH := valleys_add_doubleRises (heightSweep P) hHP hnH
  have hsumP := valleys_add_doubleRises P hP hn
  have hdrH := doubleRises_heightSweep_eq_valleys P hP hn
  omega

/-- The paper's rank sweep theorem proves `heightSweep` restricts to a bijection
of `D_n` — now formalised: see `heightSweep_bijOn` in `NarayanaBijection.lean`.
The stronger involutivity claim is false; the checked counterexample below
documents the distinction. -/
theorem heightSweep_not_involutive_counterexample :
    IsDyckPath [U, U, D, U, D, U, D, D] ∧
      heightSweep (heightSweep [U, U, D, U, D, U, D, D]) ≠
        [U, U, D, U, D, U, D, D] := by
  constructor
  · unfold IsDyckPath
    refine ⟨?_, ?_⟩
    · intro k hk
      simp only [List.length] at hk
      interval_cases k <;> simp [height]
    · simp [height]
  · native_decide

/-! ## Small verifications of the Narayana sweep -/

/-- Verification: H sends UUDD to UDUD. -/
theorem heightSweep_UUDD :
    heightSweep [U, U, D, D] = [U, D, U, D] := by native_decide

/-- Verification: H sends UDUD to UUDD. -/
theorem heightSweep_UDUD :
    heightSweep [U, D, U, D] = [U, U, D, D] := by native_decide

/-- Verification: dr(UUDD) = 1, val(UUDD) = 0. -/
theorem dr_UUDD : doubleRises [U, U, D, D] = 1 := by native_decide
theorem val_UUDD : valleys [U, U, D, D] = 0 := by native_decide

/-- Verification: dr(UDUD) = 0, val(UDUD) = 1. -/
theorem dr_UDUD : doubleRises [U, D, U, D] = 0 := by native_decide
theorem val_UDUD : valleys [U, D, U, D] = 1 := by native_decide

/-- Verification: H swaps dr and val on UUDD: dr(H(UUDD)) = val(UUDD). -/
theorem dr_heightSweep_UUDD :
    doubleRises (heightSweep [U, U, D, D]) = valleys [U, U, D, D] := by native_decide

/-- Verification: H swaps val and dr on UUDD: val(H(UUDD)) = dr(UUDD). -/
theorem val_heightSweep_UUDD :
    valleys (heightSweep [U, U, D, D]) = doubleRises [U, U, D, D] := by native_decide
