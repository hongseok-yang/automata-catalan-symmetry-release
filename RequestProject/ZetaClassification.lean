/-
# Classifying the Zeta Map

Formalization of Section 5 (Classifying the zeta map) of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.
-/
import RequestProject.DyckPath
import RequestProject.WrappedFlat
import RequestProject.Transducers

open Step

/-! ## Zeta on two-pyramid paths (Lemma 5.2) -/

/-- **`lem:zeta-two-pyramid` (paper-full-new.tex).**
Two-pyramid paths `P_{m,n} = U^m D^m U^n D^n` are Dyck paths for `m, n ≥ 1`. -/
theorem isDyckPath_twoPyramid (m n : ℕ) (_hm : 0 < m) (hn : 0 < n) :
    IsDyckPath (twoPyramid m n) := by
  constructor
  · intro k hk; rw [height_eq_count]; simp +decide [twoPyramid]
    by_cases hkm : k ≤ m <;> by_cases hkm' : k ≤ m + m <;>
      by_cases hkm'' : k ≤ m + m + n <;> simp_all +decide [List.take_append]
    all_goals simp_all +decide [List.count_replicate]
    · omega
    · omega
  · rw [height_eq_count]
    simp +decide [twoPyramid]
    rw [List.take_of_length_le] <;> simp +arith +decide [List.count_replicate]

/-
**`lem:zeta-two-pyramid` (paper-full-new.tex).**
The area sequence of `P_{m,n}` is `(0, 1, …, m-1, 0, 1, …, n-1)`.
-/
theorem areaSeq_twoPyramid (m n : ℕ) :
    areaSeq (twoPyramid m n) =
      (List.range m).map (↑· : ℕ → ℤ) ++ (List.range n).map (↑· : ℕ → ℤ) := by
        unfold areaSeq;
        unfold uPositions; simp +decide [ twoPyramid ] ;
        have h_filter : List.filter (fun i : Fin (2 * m + 2 * n) => (List.replicate m U ++ (List.replicate m D ++ (List.replicate n U ++ List.replicate n D)))[↑i] = U) (List.finRange (2 * m + 2 * n)) = List.map (fun i : Fin m => ⟨i.val, by linarith [Fin.is_lt i]⟩) (List.finRange m) ++ List.map (fun i : Fin n => ⟨m + m + i.val, by linarith [Fin.is_lt i]⟩) (List.finRange n) := by
          have h_iff : ∀ i : Fin (2 * m + 2 * n), (List.replicate m U ++ (List.replicate m D ++ (List.replicate n U ++ List.replicate n D)))[i] = U ↔ i.val < m ∨ m + m ≤ i.val ∧ i.val < m + m + n := by
            grind;
          have h_nodup : List.Nodup (List.filter (fun i : Fin (2 * m + 2 * n) => i.val < m ∨ m + m ≤ i.val ∧ i.val < m + m + n) (List.finRange (2 * m + 2 * n))) := by
            exact List.Nodup.filter _ ( List.nodup_finRange _ );
          have h_perm : List.Perm (List.filter (fun i : Fin (2 * m + 2 * n) => i.val < m ∨ m + m ≤ i.val ∧ i.val < m + m + n) (List.finRange (2 * m + 2 * n))) (List.map (fun i : Fin m => ⟨i.val, by linarith [Fin.is_lt i]⟩) (List.finRange m) ++ List.map (fun i : Fin n => ⟨m + m + i.val, by linarith [Fin.is_lt i]⟩) (List.finRange n)) := by
            rw [ List.perm_iff_count ];
            intro i; by_cases hi : i.val < m <;> by_cases hi' : m + m ≤ i.val ∧ i.val < m + m + n <;> simp_all +decide [ List.Nodup.count ] ;
            · grind;
            · rw [ List.count_eq_one_of_mem, List.count_eq_zero_of_not_mem ] <;> norm_num;
              · lia;
              · exact List.Nodup.map ( fun x y hxy => by simpa [ Fin.ext_iff ] using hxy ) ( List.nodup_finRange _ );
              · exact ⟨ ⟨ i, by linarith ⟩, rfl ⟩;
            · rw [ List.count_eq_zero_of_not_mem, List.count_eq_one_of_mem ] <;> norm_num;
              · rw [ List.nodup_map_iff_inj_on ];
                · simp +decide [ Fin.ext_iff ];
                · exact List.nodup_finRange _;
              · exact ⟨ ⟨ i - ( m + m ), by omega ⟩, by simp +decide [ add_tsub_cancel_of_le hi'.1 ] ⟩;
              · exact fun x => ne_of_lt ( Nat.lt_of_lt_of_le x.2 hi );
            · rw [ List.count_eq_zero_of_not_mem, List.count_eq_zero_of_not_mem ] <;> simp_all +decide [ Fin.ext_iff ];
              · grind;
              · exact fun x => by linarith [ Fin.is_lt x ] ;
          have hpred : (fun i : Fin (2 * m + 2 * n) => decide ((List.replicate m U ++ (List.replicate m D ++ (List.replicate n U ++ List.replicate n D)))[↑i] = U)) = (fun i : Fin (2 * m + 2 * n) => decide (i.val < m ∨ m + m ≤ i.val ∧ i.val < m + m + n)) := by
            funext i
            exact decide_eq_decide.mpr (h_iff i)
          rw [hpred]
          refine h_perm.eq_of_sortedLE ?_ ?_
          · exact (List.Pairwise.sortedLT (List.Pairwise.sublist List.filter_sublist
              (List.pairwise_lt_finRange _))).sortedLE
          · refine (List.Pairwise.sortedLT ?_).sortedLE
            rw [List.pairwise_append]
            refine ⟨?_, ?_, ?_⟩
            · rw [List.pairwise_map]
              refine (List.pairwise_lt_finRange _).imp ?_
              intro i j hij
              exact hij
            · rw [List.pairwise_map]
              refine (List.pairwise_lt_finRange _).imp ?_
              intro i j hij
              show m + m + (i : ℕ) < m + m + (j : ℕ)
              omega
            · intro a ha b hb
              simp only [List.mem_map, List.mem_finRange, true_and] at ha hb
              obtain ⟨i, rfl⟩ := ha
              obtain ⟨j, rfl⟩ := hb
              show (i : ℕ) < m + m + (j : ℕ)
              have := i.isLt
              omega
        convert congr_arg ( fun l : List ( Fin ( 2 * m + 2 * n ) ) => List.map ( fun i : Fin ( 2 * m + 2 * n ) => height ( List.replicate m U ++ ( List.replicate m D ++ ( List.replicate n U ++ List.replicate n D ) ) ) i ) l ) h_filter using 1;
        · simp +arith +decide;
          convert rfl;
          · simp +arith +decide [ List.length_append, List.length_replicate ];
          · grind +revert;
          · simp +arith +decide [ List.length_append, List.length_replicate ];
          · simp +arith +decide [ List.length_append, List.length_replicate ];
        · simp +decide [ List.map_append, List.map_map ];
          congr! 1;
          · refine' List.ext_get _ _ <;> simp +decide [ height_eq_count ];
            intro i hi; rw [ List.take_append_of_le_length ] <;> norm_num [ hi.le ] ;
            rw [ List.count_replicate ] ; aesop;
          · refine' List.ext_get _ _ <;> simp +decide;
            intro i hi; rw [ height_eq_count ] ; simp +decide [ List.take_append, List.count_append, List.count_replicate ] ; ring_nf;
            grind

/-! ## Lemma 5.3 (`lem:zeta-probe`): A regular output probe -/

/-- **`lem:zeta-probe` (paper-full-new.tex).**
The language `R = {UU(DU)^{2q} DD(UD)^s : q, s ≥ 0}`. -/
def inRegularProbe (w : List Step) : Prop :=
  ∃ q s : ℕ, w = [U, U] ++
    (List.replicate (2 * q) [D, U]).flatten ++
    [D, D] ++
    (List.replicate s [U, D]).flatten

/-! ## Zeta preserves Dyck paths -/

/-! ### Concatenation lemmas for `height` -/

/-- Height of a prefix that reaches into the right summand of a concatenation.
(`height_append_left` is provided by `AreaSeq.lean`.) -/
theorem height_append_ge (X Y : List Step) (k : ℕ) (hk : X.length ≤ k) :
    height (X ++ Y) k = height X X.length + height Y (k - X.length) := by
  have hsplit : (X ++ Y).take k = X ++ Y.take (k - X.length) := by
    conv_lhs => rw [show k = X.length + (k - X.length) from by omega]
    rw [List.take_length_add_append]
  simp only [height_eq_count, hsplit, List.take_length, List.count_append]
  push_cast; ring

/-- Prefix Dyck-nonnegativity is preserved by concatenation:
if every prefix of `X` is nonnegative and every prefix of `Y` is nonnegative once
shifted by the total height of `X`, then every prefix of `X ++ Y` is nonnegative. -/
theorem height_nonneg_append (X Y : List Step)
    (hX : ∀ k, k ≤ X.length → 0 ≤ height X k)
    (hY : ∀ j, j ≤ Y.length → 0 ≤ height X X.length + height Y j) :
    ∀ k, k ≤ (X ++ Y).length → 0 ≤ height (X ++ Y) k := by
  intro k hk
  by_cases h : k ≤ X.length
  · rw [height_append_left X Y k h]; exact hX k h
  · push Not at h
    rw [height_append_ge X Y k (le_of_lt h)]
    apply hY (k - X.length)
    rw [List.length_append] at hk; omega

/-! ### Counting in a `flatMap` -/

/-- Count of a value in a `flatMap`, as a sum of per-element counts. -/
theorem count_flatMap_step {β : Type*} (x : Step) (f : β → List Step) (l : List β) :
    (l.flatMap f).count x = (l.map (fun b => (f b).count x)).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [List.flatMap_cons, List.count_append, ih]

/-- Counting a value as an indicator sum over the list. -/
theorem count_eq_sum_ite (v : ℤ) (a : List ℤ) :
    a.count v = (a.map (fun x => if x = v then 1 else 0)).sum := by
  induction a with
  | nil => simp
  | cons x a ih =>
      rw [List.map_cons, List.sum_cons, List.count_cons, ih]
      by_cases h : x = v <;> simp [h, Nat.add_comm]

/-! ### Foldl-max bounds -/

/-- The running `foldl max` is at least its accumulator. -/
theorem foldl_max_ge_acc (a : List ℤ) : ∀ acc, acc ≤ a.foldl max acc := by
  induction a with
  | nil => intro acc; simp
  | cons x a ih =>
      intro acc
      simp only [List.foldl_cons]
      exact le_trans (le_max_left acc x) (ih (max acc x))

/-- Every element of an `ℤ` list is at most its running `foldl max`. -/
theorem le_foldl_max (a : List ℤ) : ∀ x ∈ a, ∀ acc, x ≤ a.foldl max acc := by
  induction a with
  | nil => simp
  | cons y a ih =>
      intro x hx acc
      rcases List.mem_cons.mp hx with h | h
      · subst h
        simp only [List.foldl_cons]
        exact le_trans (le_max_right acc x) (foldl_max_ge_acc a (max acc x))
      · simp only [List.foldl_cons]
        exact ih x h (max acc y)

/-! ### The rank-block decomposition of `zetaMap` -/

/-- The step(s) emitted at rank `r` for an area value `ai`. -/
def zEmit (r ai : ℤ) : List Step :=
  if ai = r then [U] else if ai = r - 1 then [D] else []

/-- The rank-`r` block of the zeta output: scan the area sequence, emitting `U`
for each entry equal to `r` and `D` for each entry equal to `r - 1`. -/
def zBlock (a : List ℤ) (r : ℕ) : List Step :=
  a.flatMap (zEmit (r : ℤ))

/-- The zeta output restricted to ranks `< r`. -/
def zAcc (a : List ℤ) (r : ℕ) : List Step :=
  (List.range r).flatMap (zBlock a)

/-- `zetaMap` is `zAcc` over all ranks `0, …, maxA + 1`. -/
theorem zetaMap_eq_zAcc (P : List Step) :
    zetaMap P = zAcc (areaSeq P) (((areaSeq P).foldl max 0).toNat + 2) := by
  unfold zetaMap zAcc zBlock zEmit
  simp only [bind_pure_comp, List.map_eq_map, List.flatMap_map]

/-- One more rank appends one more block. -/
theorem zAcc_succ (a : List ℤ) (r : ℕ) :
    zAcc a (r + 1) = zAcc a r ++ zBlock a r := by
  unfold zAcc
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The number of `U`s in a rank block is the number of area entries equal to `r`. -/
theorem countU_zBlock (a : List ℤ) (r : ℕ) :
    (zBlock a r).count U = a.count (r : ℤ) := by
  rw [zBlock, count_flatMap_step, count_eq_sum_ite (r : ℤ) a]
  congr 1
  refine List.map_congr_left (fun ai _ => ?_)
  unfold zEmit; split_ifs with h1 h2 <;> simp_all

/-- The number of `D`s in a rank block is the number of area entries equal to `r - 1`. -/
theorem countD_zBlock (a : List ℤ) (r : ℕ) :
    (zBlock a r).count D = a.count ((r : ℤ) - 1) := by
  rw [zBlock, count_flatMap_step, count_eq_sum_ite ((r : ℤ) - 1) a]
  congr 1
  refine List.map_congr_left (fun ai _ => ?_)
  unfold zEmit; split_ifs with h1 h2 <;> simp_all

/-- **Core invariant.** For a Dyck path's (nonnegative) area sequence `a`, the
word built from ranks `0, …, r-1` is prefix-nonnegative and ends at height
`#{i : aᵢ = r-1}`. The telescoping is hidden in the running height. -/
theorem zAcc_dyck_invariant (a : List ℤ) (hnn : ∀ x ∈ a, 0 ≤ x) :
    ∀ r : ℕ,
      (∀ k, k ≤ (zAcc a r).length → 0 ≤ height (zAcc a r) k) ∧
      height (zAcc a r) (zAcc a r).length = (a.count ((r : ℤ) - 1) : ℤ) := by
  intro r
  induction r with
  | zero =>
      have h0 : zAcc a 0 = [] := by simp [zAcc]
      refine ⟨fun k hk => ?_, ?_⟩
      · rw [h0] at hk ⊢
        simp only [List.length_nil, Nat.le_zero] at hk
        subst hk; simp [height]
      · rw [h0]
        simp only [List.length_nil, Nat.cast_zero, zero_sub, height_zero]
        symm
        rw [Nat.cast_eq_zero, List.count_eq_zero]
        intro hmem; have := hnn _ hmem; omega
  | succ r ih =>
      obtain ⟨ihpref, ihfull⟩ := ih
      have hsucc : zAcc a (r + 1) = zAcc a r ++ zBlock a r := zAcc_succ a r
      have hblockfull : height (zBlock a r) (zBlock a r).length
          = (a.count (r : ℤ) : ℤ) - (a.count ((r : ℤ) - 1) : ℤ) := by
        rw [height_eq_count, List.take_length, countU_zBlock, countD_zBlock]
      refine ⟨?_, ?_⟩
      · rw [hsucc]
        apply height_nonneg_append _ _ ihpref
        intro j hj
        rw [ihfull]
        have hcD : ((zBlock a r).take j).count D ≤ (zBlock a r).count D :=
          List.Sublist.count_le D (List.take_sublist j (zBlock a r))
        rw [countD_zBlock] at hcD
        rw [height_eq_count]
        have hUnn : (0 : ℤ) ≤ (((zBlock a r).take j).count U : ℤ) := by positivity
        have hcDz : (((zBlock a r).take j).count D : ℤ) ≤ (a.count ((r : ℤ) - 1) : ℤ) := by
          exact_mod_cast hcD
        linarith
      · rw [hsucc]
        have hidx : (zAcc a r ++ zBlock a r).length - (zAcc a r).length
            = (zBlock a r).length := by rw [List.length_append]; omega
        rw [height_append_ge (zAcc a r) (zBlock a r) _ (by rw [List.length_append]; omega),
          hidx, ihfull, hblockfull]
        have hr1 : ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) := by push_cast; ring
        rw [hr1]; ring

/-- **Implicit in Definition 2.5 (`def:zeta`, paper-full-new.tex).**
Haglund showed that `ζ(P)` is a Dyck path whenever `P` is. -/
theorem isDyckPath_zetaMap (P : List Step) (hP : IsDyckPath P) :
    IsDyckPath (zetaMap P) := by
  have hnn : ∀ x ∈ areaSeq P, 0 ≤ x := areaSeq_nonneg P hP
  rw [zetaMap_eq_zAcc]
  obtain ⟨hpref, hfull⟩ :=
    zAcc_dyck_invariant (areaSeq P) hnn (((areaSeq P).foldl max 0).toNat + 2)
  refine ⟨hpref, ?_⟩
  rw [hfull]
  have hmaxnn : (0 : ℤ) ≤ (areaSeq P).foldl max 0 := foldl_max_ge_acc (areaSeq P) 0
  have hcast : ((((areaSeq P).foldl max 0).toNat : ℕ) : ℤ) = (areaSeq P).foldl max 0 :=
    Int.toNat_of_nonneg hmaxnn
  have harg : ((((areaSeq P).foldl max 0).toNat + 2 : ℕ) : ℤ) - 1
      = (areaSeq P).foldl max 0 + 1 := by
    push_cast; omega
  rw [harg, Nat.cast_eq_zero, List.count_eq_zero]
  intro hmem
  have hcon := le_foldl_max (areaSeq P) ((areaSeq P).foldl max 0 + 1) hmem 0
  omega

/-! ### Append-native area (`areaR`) -/

/-- An append-friendly form of `area`: sum over **all** positions of the height
just before each `U`-step (and `0` at `D`-steps).  Equal to `area` (see
`areaR_eq_area`) but it splits cleanly under concatenation. -/
def areaR (W : List Step) : ℤ :=
  ((List.range W.length).map (fun k => if W[k]? = some U then height W k else 0)).sum

/-- Summing `g ∘ (·[k]?)` over `range |l|` equals summing `g ∘ some` over `l`
(when `g none = 0`). -/
theorem range_get_map_eq {α} [DecidableEq α] (l : List α) (g : Option α → ℤ)
    (hg : g none = 0) :
    ((List.range l.length).map (fun k => g (l[k]?))).sum
      = (l.map (fun a => g (some a))).sum := by
  induction l using List.reverseRecOn with
  | nil => simp [hg]
  | append_singleton l x ih =>
      rw [List.length_append, List.range_add, List.map_append, List.sum_append,
        List.map_append, List.sum_append]
      congr 1
      · rw [← ih]
        congr 1
        apply List.map_congr_left
        intro k hk
        rw [List.mem_range] at hk
        rw [List.getElem?_append_left hk]
      · simp

/-- `count` as a range-indicator sum.  Needs `Step`'s native `BEq` (hence the
explicit `[BEq α] [LawfulBEq α]` alongside `[DecidableEq α]`). -/
theorem count_eq_range_indicator {α} [DecidableEq α] [BEq α] [LawfulBEq α]
    (l : List α) (v : α) :
    (l.count v : ℤ)
      = ((List.range l.length).map (fun k => if l[k]? = some v then (1:ℤ) else 0)).sum := by
  rw [range_get_map_eq l (fun o => if o = some v then (1:ℤ) else 0) (by simp)]
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.count_cons, List.map_cons, List.sum_cons, ← ih]
      push_cast
      by_cases h : a = v <;> simp [h]; ring

/-- Sum of `f` over a filtered list equals the indicator sum of `f`. -/
theorem sum_map_filter_eq_ite {α} (p : α → Prop) [DecidablePred p] (f : α → ℤ)
    (l : List α) :
    ((l.filter (fun a => decide (p a))).map f).sum
      = (l.map (fun a => if p a then f a else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/-- `areaR` agrees with `area`. -/
theorem areaR_eq_area (W : List Step) : areaR W = area W := by
  have key : area W = ((List.finRange W.length).map
      (fun i => if W.get i = U then height W i.val else 0)).sum := by
    unfold area areaSeq uPositions
    rw [List.map_map]
    simp only [Function.comp_def]
    rw [sum_map_filter_eq_ite (fun i : Fin W.length => W.get i = U) (fun i => height W i.val)]
  rw [key, areaR, ← List.map_coe_finRange_eq_range, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [Function.comp_apply, List.getElem?_eq_getElem i.isLt, List.get_eq_getElem]
  by_cases h : W[i.val] = U <;> simp [h]

/-- **Area is additive over concatenation**, up to the cross term `(#U in Y)·h(X)`. -/
theorem areaR_append (X Y : List Step) :
    areaR (X ++ Y) = areaR X + areaR Y + (Y.count U : ℤ) * height X X.length := by
  unfold areaR
  rw [List.length_append, List.range_add, List.map_append, List.sum_append, List.map_map]
  have hL : (List.range X.length).map
        (fun k => if (X ++ Y)[k]? = some U then height (X ++ Y) k else 0)
      = (List.range X.length).map (fun k => if X[k]? = some U then height X k else 0) := by
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    rw [List.getElem?_append_left hk, height_append_left X Y k (le_of_lt hk)]
  have hR : (List.range Y.length).map
        ((fun k => if (X ++ Y)[k]? = some U then height (X ++ Y) k else 0) ∘ fun x => X.length + x)
      = (List.range Y.length).map (fun k =>
          (if Y[k]? = some U then height Y k else 0)
            + (if Y[k]? = some U then (1:ℤ) else 0) * height X X.length) := by
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    simp only [Function.comp_apply]
    rw [List.getElem?_append_right (by omega), height_append_ge X Y (X.length + k) (by omega),
      show X.length + k - X.length = k from by omega]
    by_cases h : Y[k]? = some U <;> simp [h]; ring
  rw [hL, hR, List.sum_map_add, List.sum_map_mul_right, ← count_eq_range_indicator]
  ring

/-! ### Blockwise area accumulation -/

/-- A single emitted step contributes no area (its only step starts at height 0). -/
theorem areaR_zEmit (r ai : ℤ) : areaR (zEmit r ai) = 0 := by
  unfold areaR zEmit
  split_ifs <;> simp [height]

/-- `U`-count of a single emit. -/
theorem countU_zEmit (r ai : ℤ) : (zEmit r ai).count U = if ai = r then 1 else 0 := by
  unfold zEmit; split_ifs with h1 h2 <;> simp_all

/-- The net height across a whole rank block. -/
theorem height_zBlock_end (a : List ℤ) (r : ℕ) :
    height (zBlock a r) (zBlock a r).length
      = (a.count (r : ℤ) : ℤ) - (a.count ((r : ℤ) - 1) : ℤ) := by
  rw [height_eq_count, List.take_length, countU_zBlock, countD_zBlock]

/-- Closed form for the area of a single rank block: a "within-block" pair sum. -/
def blockAreaForm (a : List ℤ) (r : ℕ) : ℤ :=
  ((List.range a.length).map (fun i =>
    if a[i]? = some (r : ℤ)
    then ((a.take i).count (r : ℤ) : ℤ) - ((a.take i).count ((r : ℤ) - 1) : ℤ)
    else 0)).sum

/-- `blockAreaForm` peels its last entry. -/
theorem blockAreaForm_append_singleton (a : List ℤ) (x : ℤ) (r : ℕ) :
    blockAreaForm (a ++ [x]) r
      = blockAreaForm a r
        + (if x = (r : ℤ) then (a.count (r : ℤ) : ℤ) - (a.count ((r : ℤ) - 1) : ℤ) else 0) := by
  unfold blockAreaForm
  rw [List.length_append, List.length_singleton, List.range_add, List.map_append, List.sum_append]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [List.getElem?_append_left hi, List.take_append_of_le_length (le_of_lt hi)]
  · simp only [List.range_one, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [List.getElem?_append_right (by simp), List.take_append_of_le_length (le_refl _),
      List.take_length]
    simp

/-- The area of a rank block equals its `blockAreaForm`. -/
theorem areaR_zBlock (a : List ℤ) (r : ℕ) : areaR (zBlock a r) = blockAreaForm a r := by
  induction a using List.reverseRecOn with
  | nil => simp [zBlock, blockAreaForm, areaR]
  | append_singleton a x ih =>
      rw [zBlock, List.flatMap_append, List.flatMap_singleton, ← zBlock, areaR_append, ih,
        areaR_zEmit, height_zBlock_end, countU_zEmit, blockAreaForm_append_singleton]
      split_ifs <;> ring

/-- Closed form for the accumulated area over ranks `0, …, r-1`:
each rank contributes a cross term `count(ρ)·count(ρ-1)` plus its `blockAreaForm`. -/
def accForm (a : List ℤ) (r : ℕ) : ℤ :=
  ((List.range r).map (fun ρ : ℕ =>
    (a.count (ρ : ℤ) : ℤ) * (a.count ((ρ : ℤ) - 1) : ℤ) + blockAreaForm a ρ)).sum

/-- The area of `zAcc a r` equals its `accForm`. -/
theorem areaR_zAcc (a : List ℤ) (hnn : ∀ x ∈ a, 0 ≤ x) (r : ℕ) :
    areaR (zAcc a r) = accForm a r := by
  induction r with
  | zero => simp [zAcc, accForm, areaR]
  | succ r ih =>
      rw [accForm, List.range_succ, List.map_append, List.sum_append, ← accForm]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [zAcc_succ, areaR_append, ih, areaR_zBlock, countU_zBlock,
        (zAcc_dyck_invariant a hnn r).2]
      ring

/-! ### Count ↔ indicator-sum bridges -/

/-- A `List.range` map-sum is the corresponding `Finset.range` sum. -/
theorem list_range_map_sum (n : ℕ) (g : ℕ → ℤ) :
    ((List.range n).map g).sum = ∑ k ∈ Finset.range n, g k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
      simp

/-- `count` as an indicator sum over `Finset.range`. -/
theorem count_eq_ind (a : List ℤ) (v : ℤ) :
    (a.count v : ℤ) = ∑ k ∈ Finset.range a.length, (if a[k]? = some v then (1:ℤ) else 0) := by
  rw [count_eq_range_indicator a v, list_range_map_sum]

/-- `count` of a prefix as a bounded indicator sum. -/
theorem count_take_eq_ind (a : List ℤ) (j : ℕ) (hj : j ≤ a.length) (v : ℤ) :
    ((a.take j).count v : ℤ)
      = ∑ k ∈ Finset.range a.length, (if k < j ∧ a[k]? = some v then (1:ℤ) else 0) := by
  rw [count_eq_range_indicator (a.take j) v, list_range_map_sum, List.length_take,
    Nat.min_eq_left hj]
  have hcongr : ∀ k ∈ Finset.range j,
      (if (a.take j)[k]? = some v then (1:ℤ) else 0)
        = (if k < j ∧ a[k]? = some v then (1:ℤ) else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [List.getElem?_take_of_lt hk]
    simp [hk]
  rw [Finset.sum_congr rfl hcongr]
  exact Finset.sum_subset
    (fun k hk => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hj))
    (fun k _ hk => if_neg (fun (h : k < j ∧ a[k]? = some v) =>
      hk (Finset.mem_range.mpr h.1)))

/-- `count` as a `Fin`-indexed indicator sum (matches `dinv_eq_sum_card`'s shape). -/
theorem count_eq_card_fin (a : List ℤ) (v : ℤ) :
    (a.count v : ℤ) = ∑ i : Fin a.length, (if a.get i = v then (1:ℤ) else 0) := by
  rw [count_eq_ind a v,
    ← Fin.sum_univ_eq_sum_range (fun k => if a[k]? = some v then (1:ℤ) else 0)]
  apply Finset.sum_congr rfl
  intro i _
  rw [List.getElem?_eq_getElem i.isLt, List.get_eq_getElem]
  simp

/-- `count` of a prefix as a `Fin`-indexed bounded indicator sum. -/
theorem count_take_eq_card_fin (a : List ℤ) (j : ℕ) (hj : j ≤ a.length) (v : ℤ) :
    ((a.take j).count v : ℤ)
      = ∑ i : Fin a.length, (if (i:ℕ) < j ∧ a.get i = v then (1:ℤ) else 0) := by
  rw [count_take_eq_ind a j hj v,
    ← Fin.sum_univ_eq_sum_range (fun k => if k < j ∧ a[k]? = some v then (1:ℤ) else 0)]
  apply Finset.sum_congr rfl
  intro i _
  rw [List.getElem?_eq_getElem i.isLt, List.get_eq_getElem]
  simp

/-- Per-rank: the cross term plus the block area, written as an index sum. -/
theorem accForm_incr (a : List ℤ) (ρ : ℕ) :
    (a.count (ρ : ℤ) : ℤ) * (a.count ((ρ : ℤ) - 1) : ℤ) + blockAreaForm a ρ
      = ∑ i ∈ Finset.range a.length,
          (if a[i]? = some (ρ : ℤ)
           then (a.count ((ρ : ℤ) - 1) : ℤ)
             + ((a.take i).count (ρ : ℤ) : ℤ) - ((a.take i).count ((ρ : ℤ) - 1) : ℤ)
           else 0) := by
  have h1 : (a.count (ρ : ℤ) : ℤ) * (a.count ((ρ : ℤ) - 1) : ℤ)
      = ∑ i ∈ Finset.range a.length,
          (if a[i]? = some (ρ : ℤ) then (a.count ((ρ : ℤ) - 1) : ℤ) else 0) := by
    rw [count_eq_ind a (ρ : ℤ), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _; split_ifs <;> ring
  have h2 : blockAreaForm a ρ
      = ∑ i ∈ Finset.range a.length,
          (if a[i]? = some (ρ : ℤ)
           then ((a.take i).count (ρ : ℤ) : ℤ) - ((a.take i).count ((ρ : ℤ) - 1) : ℤ) else 0) := by
    rw [blockAreaForm, list_range_map_sum]
  rw [h1, h2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; split_ifs <;> ring

/-! ### The accumulated form is `dinv` -/

/-- Collapse the rank sum: only `ρ = aᵢ` survives at each index `i`. -/
theorem accForm_collapse (a : List ℤ) (m : ℕ)
    (hnn : ∀ i : Fin a.length, 0 ≤ a.get i)
    (hub : ∀ i : Fin a.length, (a.get i).toNat < m) :
    accForm a m = ∑ i : Fin a.length,
      ((a.count (a.get i - 1) : ℤ)
        + ((a.take (i:ℕ)).count (a.get i) : ℤ) - ((a.take (i:ℕ)).count (a.get i - 1) : ℤ)) := by
  rw [accForm, list_range_map_sum, Finset.sum_congr rfl (fun ρ _ => accForm_incr a ρ),
    Finset.sum_comm,
    ← Fin.sum_univ_eq_sum_range (fun i => ∑ ρ ∈ Finset.range m,
      (if a[i]? = some (ρ : ℤ)
       then (a.count ((ρ : ℤ) - 1) : ℤ)
         + ((a.take i).count (ρ : ℤ) : ℤ) - ((a.take i).count ((ρ : ℤ) - 1) : ℤ)
       else 0))]
  apply Finset.sum_congr rfl
  intro i _
  have hget : a[(i:ℕ)]? = some (a.get i) := by
    rw [List.get_eq_getElem, List.getElem?_eq_getElem i.isLt]
  have hcast : ((a.get i).toNat : ℤ) = a.get i := Int.toNat_of_nonneg (hnn i)
  rw [show (fun ρ : ℕ =>
        if a[(i:ℕ)]? = some (ρ : ℤ)
        then (a.count ((ρ : ℤ) - 1) : ℤ)
          + ((a.take (i:ℕ)).count (ρ : ℤ) : ℤ) - ((a.take (i:ℕ)).count ((ρ : ℤ) - 1) : ℤ)
        else 0)
      = (fun ρ : ℕ =>
        if ρ = (a.get i).toNat
        then (a.count (a.get i - 1) : ℤ)
          + ((a.take (i:ℕ)).count (a.get i) : ℤ) - ((a.take (i:ℕ)).count (a.get i - 1) : ℤ)
        else 0) from ?_]
  · rw [Finset.sum_ite_eq' (Finset.range m) ((a.get i).toNat), if_pos (Finset.mem_range.mpr (hub i))]
  · funext ρ
    rw [hget]
    by_cases hρ : ρ = (a.get i).toNat
    · subst hρ
      simp only [hcast]
    · have hLHS : ¬ (some (a.get i) = some (ρ : ℤ)) := by
        intro h
        exact hρ (by have := Option.some.inj h; omega)
      rw [if_neg hLHS, if_neg hρ]

/-- **The combinatorial heart:** the accumulated area form over all ranks equals
`dinv(P)`.  Both sides count the same two pair-classes of the area sequence:
`#{i'<i : a_{i'} = a_i}` (equal pairs) and `#{i'>i : a_{i'} = a_i - 1}`
(`a_i = a_{i'}+1` pairs). -/
theorem accForm_eq_dinv (P : List Step) (hP : IsDyckPath P) :
    accForm (areaSeq P) (((areaSeq P).foldl max 0).toNat + 2) = (dinv P : ℤ) := by
  set a := areaSeq P with ha
  have hnn : ∀ i : Fin a.length, 0 ≤ a.get i := by
    intro i; rw [List.get_eq_getElem]; exact areaSeq_nonneg P hP _ (List.getElem_mem _)
  have hub : ∀ i : Fin a.length, (a.get i).toNat < (a.foldl max 0).toNat + 2 := by
    intro i
    have h0 := hnn i
    have h1 : a.get i ≤ a.foldl max 0 := by
      rw [List.get_eq_getElem]; exact le_foldl_max a _ (List.getElem_mem _) 0
    have h2 : (0 : ℤ) ≤ a.foldl max 0 := foldl_max_ge_acc a 0
    omega
  rw [accForm_collapse a _ hnn hub]
  -- expand each per-index term into a double sum over `i'`
  have hbridge : ∀ i : Fin a.length,
      (a.count (a.get i - 1) : ℤ) + ((a.take (i:ℕ)).count (a.get i) : ℤ)
        - ((a.take (i:ℕ)).count (a.get i - 1) : ℤ)
      = ∑ i' : Fin a.length,
          ((if (i:ℕ) < (i':ℕ) ∧ a.get i' = a.get i - 1 then (1:ℤ) else 0)
           + (if (i':ℕ) < (i:ℕ) ∧ a.get i' = a.get i then (1:ℤ) else 0)) := by
    intro i
    rw [count_eq_card_fin a (a.get i - 1),
      count_take_eq_card_fin a (i:ℕ) (le_of_lt i.isLt) (a.get i),
      count_take_eq_card_fin a (i:ℕ) (le_of_lt i.isLt) (a.get i - 1),
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i' _
    rcases lt_trichotomy (i':ℕ) (i:ℕ) with h | h | h
    · simp only [h, Nat.lt_asymm h, true_and, false_and, if_false]; split_ifs <;> ring
    · have hii : i' = i := Fin.ext h
      subst hii
      simp only [lt_self_iff_false, false_and, if_false, add_zero, sub_zero]
      split_ifs <;> omega
    · simp only [h, Nat.lt_asymm h, true_and, false_and, if_false]; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hbridge i)]
  simp only [Finset.sum_add_distrib]
  -- convert each `dinv` column card to two indicator sums
  have hcard : ∀ j : Fin a.length,
      ((Finset.univ.filter (fun i : Fin a.length =>
          (i:ℕ) < (j:ℕ) ∧ (a[(i:ℕ)] - a[(j:ℕ)] = 0 ∨ a[(i:ℕ)] - a[(j:ℕ)] = 1))).card : ℤ)
      = (∑ i : Fin a.length, (if (i:ℕ) < (j:ℕ) ∧ a.get i = a.get j then (1:ℤ) else 0))
        + (∑ i : Fin a.length, (if (i:ℕ) < (j:ℕ) ∧ a.get i = a.get j + 1 then (1:ℤ) else 0)) := by
    intro j
    rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [List.get_eq_getElem]
    by_cases h1 : (i:ℕ) < (j:ℕ) <;> by_cases h2 : a[(i:ℕ)] = a[(j:ℕ)] <;>
      by_cases h3 : a[(i:ℕ)] = a[(j:ℕ)] + 1 <;> simp_all; omega
  -- dinv = (equal-pair double sum) + (a_i = a_j+1 double sum)
  have hdinv : (dinv P : ℤ)
      = (∑ i : Fin a.length, ∑ i' : Fin a.length,
          (if (i':ℕ) < (i:ℕ) ∧ a.get i' = a.get i then (1:ℤ) else 0))
        + (∑ i : Fin a.length, ∑ i' : Fin a.length,
          (if (i:ℕ) < (i':ℕ) ∧ a.get i' = a.get i - 1 then (1:ℤ) else 0)) := by
    have hpart1 : (∑ j : Fin a.length, ∑ i : Fin a.length,
          (if (i:ℕ) < (j:ℕ) ∧ a.get i = a.get j then (1:ℤ) else 0))
        = ∑ i : Fin a.length, ∑ i' : Fin a.length,
          (if (i':ℕ) < (i:ℕ) ∧ a.get i' = a.get i then (1:ℤ) else 0) := rfl
    have hpart2 : (∑ j : Fin a.length, ∑ i : Fin a.length,
          (if (i:ℕ) < (j:ℕ) ∧ a.get i = a.get j + 1 then (1:ℤ) else 0))
        = ∑ i : Fin a.length, ∑ i' : Fin a.length,
          (if (i:ℕ) < (i':ℕ) ∧ a.get i' = a.get i - 1 then (1:ℤ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      by_cases hxy : (x:ℕ) < (y:ℕ)
      · by_cases he : a.get x = a.get y + 1
        · rw [if_pos ⟨hxy, he⟩, if_pos ⟨hxy, by omega⟩]
        · rw [if_neg (fun h => he h.2), if_neg (fun h => he (by have := h.2; omega))]
      · rw [if_neg (fun h => hxy h.1), if_neg (fun h => hxy h.1)]
    rw [dinv_eq_sum_card, Nat.cast_sum,
      Finset.sum_congr rfl (fun j _ => hcard j), Finset.sum_add_distrib, hpart1, hpart2]
  rw [hdinv]; ring

/-- **Key property of ζ (`def:zeta`, paper-full-new.tex).**
`area(ζ(P)) = dinv(P)` for any Dyck path P. -/
theorem area_zetaMap_eq_dinv (P : List Step) (hP : IsDyckPath P) :
    area (zetaMap P) = ↑(dinv P) := by
  rw [← areaR_eq_area, zetaMap_eq_zAcc, areaR_zAcc (areaSeq P) (areaSeq_nonneg P hP),
    accForm_eq_dinv P hP]

/-
**Key property of ζ (`def:zeta`, paper-full-new.tex).**
`ζ` preserves the semilength: `|ζ(P)| = |P|`.
-/
theorem length_zetaMap_eq (P : List Step) (hP : IsDyckPath P) :
    (zetaMap P).length = P.length := by
      -- Since each entry a_i in the area sequence contributes exactly two letters to the zeta map output, the total length is 2n.
      have h_areaSeq_length : (areaSeq P).length = P.count U := by
        unfold areaSeq uPositions;
        -- The length of the list of positions of U's in P is equal to the count of U's in P.
        have h_count_U : (List.filter (fun i => P.get i = U) (List.finRange P.length)).length = List.count U P := by
          have h_count_U : ∀ (l : List Step), (List.filter (fun i => l.get i = U) (List.finRange l.length)).length = List.count U l := by
            intro l;
            induction l <;> simp +decide [ *, List.finRange_succ ];
            cases ‹Step› <;> simp_all +decide; all_goals rw [ List.filter_map ] ; aesop;
          apply h_count_U;
        aesop;
      -- Since P is a Dyck path, it has an equal number of U's and D's, so the length of P is twice the number of U's.
      have h_count_U : P.count U = P.count D := by
        have := hP.2;
        rw [ height_eq_count ] at this;
        simp_all +decide [ sub_eq_zero ];
      have h_length : (zetaMap P).length = 2 * (areaSeq P).length := by
        unfold zetaMap;
        have h_length : ∀ ai ∈ areaSeq P, List.sum (List.map (fun r => List.length (if ai = (r : ℤ) then [U] else if ai = (r : ℤ) - 1 then [D] else [])) (List.range ((List.foldl max 0 (areaSeq P)).toNat + 2))) = 2 := by
          intro ai hai; simp +decide ;
          have h_count : List.count (ai : ℤ) (List.flatMap (fun a => [↑a]) (List.range ((List.foldl max 0 (areaSeq P)).toNat + 2))) = 1 ∧ List.count (ai + 1 : ℤ) (List.flatMap (fun a => [↑a]) (List.range ((List.foldl max 0 (areaSeq P)).toNat + 2))) = 1 := by
            have h_count : ai ≥ 0 ∧ ai ≤ (List.foldl max 0 (areaSeq P)).toNat := by
              have h_ai_bounds : ∀ ai ∈ areaSeq P, 0 ≤ ai ∧ ai ≤ List.foldl max 0 (areaSeq P) := by
                intros ai hai
                have h_ai_range : 0 ≤ ai := by
                  have h_ai_range : ∀ k ≤ P.length, 0 ≤ height P k := by
                    exact hP.1;
                  unfold areaSeq at hai;
                  unfold uPositions at hai; aesop;
                have h_ai_max : ai ≤ List.foldl max 0 (areaSeq P) := by
                  have h_ai_max : ∀ {l : List ℤ}, ai ∈ l → ai ≤ List.foldl max 0 l := by
                    intros l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
                  exact h_ai_max hai
                exact ⟨h_ai_range, h_ai_max⟩;
              exact ⟨ h_ai_bounds ai hai |>.1, by linarith [ h_ai_bounds ai hai |>.2, Int.self_le_toNat ( List.foldl max 0 ( areaSeq P ) ) ] ⟩;
            constructor <;> rw [ List.count_eq_one_of_mem ];
            · simp +decide [ List.nodup_flatMap ];
              norm_num [ List.pairwise_iff_get ];
              exact fun i j hij => ne_of_gt hij;
            · simp +zetaDelta at *;
              exact ⟨ Int.toNat ai, by omega, by rw [ Int.toNat_of_nonneg h_count.1 ] ⟩;
            · simp +decide [ List.nodup_flatMap ];
              norm_num [ List.pairwise_iff_get ];
              exact fun i j hij => ne_of_gt hij;
            · simp +decide [ List.mem_flatMap, List.mem_range ];
              exact ⟨ Int.toNat ( ai + 1 ), by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ ai + 1 ) ], by rw [ Int.toNat_of_nonneg ( by linarith : 0 ≤ ai + 1 ) ] ⟩;
          convert congr_arg₂ ( · + · ) h_count.1 h_count.2 using 1;
          induction ( List.range ( ( List.foldl max 0 ( areaSeq P ) ).toNat + 2 ) ) <;> simp +decide [ *, List.count ];
          grind +splitImp;
        convert congr_arg ( fun x : List ℕ => List.sum x ) ( List.map_congr_left h_length ) using 1;
        · simp +decide [ List.flatMap ];
          induction ( List.range ( ( List.foldl max 0 ( areaSeq P ) ).toNat + 2 ) ) <;> simp +decide [ * ];
          rfl;
        · norm_num [ mul_comm ];
      have h_count : ∀ (l : List Step), List.count U l + List.count D l = l.length := by
        intro l; induction l <;> simp +decide [ * ] ;
        cases ‹Step› <;> simp +decide [ * ] <;> linarith;
      linarith [ h_count P ]

/-! ## Lemma 5.2 (`lem:zeta-two-pyramid`): the closed form of zeta on two-pyramid paths
(`lem:zeta-two-pyramid`, paper-full-new.tex)

We compute `ζ(P_{m,n})` in closed form for all `m,n ≥ 1`, then use it (together
with the explicit DFA `probeDFA` below) to prove the §5.3 probe characterisation
`ζ(P_{m,n}) ∈ R ⟺ m ≤ n`.  These supersede the earlier `native_decide` spot checks.
The development reuses the rank-block machinery (`zBlock`, `zAcc`,
`zetaMap_eq_zAcc`, `areaSeq_twoPyramid`) established above. -/

-- Step 1: per-rank block of a single pyramid range
theorem zBlock_rangePyr (k r : ℕ) :
    zBlock ((List.range k).map (↑· : ℕ → ℤ)) r
      = if r = 0 then (if 0 < k then [U] else [])
        else if r < k then [D, U] else if r = k then [D] else [] := by
  unfold zBlock
  rw [List.flatMap_map]
  induction k with
  | zero => simp [zEmit]
  | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih]
      -- The tail emit `zEmit r (↑k)`:  [U] if k = r, [D] if k = r-1, [] else.
      have htail : zEmit (↑r) (↑k : ℤ) =
          if k = r then [U] else if k + 1 = r then [D] else [] := by
        unfold zEmit
        have h1 : ((↑k : ℤ) = (↑r : ℤ)) ↔ k = r := by
          constructor <;> intro h <;> [exact_mod_cast h; exact_mod_cast h]
        have h2 : ((↑k : ℤ) = (↑r : ℤ) - 1) ↔ k + 1 = r := by omega
        by_cases hkr : k = r
        · rw [if_pos (h1.mpr hkr), if_pos hkr]
        · rw [if_neg (fun h => hkr (h1.mp h))]
          by_cases hkr2 : k + 1 = r
          · rw [if_pos (h2.mpr hkr2), if_neg hkr, if_pos hkr2]
          · rw [if_neg (fun h => hkr2 (h2.mp h)), if_neg hkr, if_neg hkr2]
      rw [htail]
      -- Now a pure ℕ case-split; the lists are literals.
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · subst hr0
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0; simp
        · simp only [if_pos hk0, if_neg (by omega : ¬ k = 0)]; simp
      · rw [if_neg (by omega : ¬ r = 0), if_neg (by omega : ¬ r = 0)]
        rcases lt_trichotomy r k with hk | hk | hk
        · rw [if_pos hk, if_pos (by omega : r < k + 1),
            if_neg (by omega : ¬ k = r), if_neg (by omega : ¬ k + 1 = r)]; simp
        · subst hk
          rw [if_neg (by omega : ¬ r < r), if_pos rfl, if_pos (by omega : r < r + 1),
            if_pos rfl]; rfl
        · rw [if_neg (by omega : ¬ r < k), if_neg (by omega : ¬ k = r)]
          rcases (by omega : r = k + 1 ∨ k + 1 < r) with hk2 | hk2
          · subst hk2
            rw [if_neg (by omega : ¬ k + 1 = k), if_pos (by omega : k + 1 = k + 1),
              if_neg (by omega : ¬ k + 1 < k + 1)]; simp
          · rw [if_neg (by omega : ¬ k + 1 = r), if_neg (by omega : ¬ r = k),
              if_neg (by omega : ¬ r < k + 1), if_neg (by omega : ¬ r = k + 1)]; rfl

-- helper: foldl max over (range k).map cast, parametrized by accumulator (k ≥ 1)
theorem foldl_max_rangePyr (k : ℕ) (hk : 0 < k) (acc : ℤ) :
    ((List.range k).map (↑· : ℕ → ℤ)).foldl max acc = max acc ((k : ℤ) - 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simp
      · rw [ih hk0]; push_cast; omega

-- Step 0: rank range of twoPyramid
theorem foldl_max_areaSeq_twoPyramid (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ((areaSeq (twoPyramid m n)).foldl max 0).toNat + 2 = max m n + 1 := by
  rw [areaSeq_twoPyramid, List.foldl_append, foldl_max_rangePyr m hm,
    foldl_max_rangePyr n hn (max 0 ((m : ℤ) - 1))]
  have hsplit : max (max (0 : ℤ) ((m : ℤ) - 1)) ((n : ℤ) - 1) = ((max m n : ℕ) : ℤ) - 1 := by
    rw [Nat.cast_max]; omega
  rw [hsplit]
  have hmn : (1 : ℤ) ≤ ((max m n : ℕ) : ℤ) := by
    have : 1 ≤ max m n := by omega
    exact_mod_cast this
  omega

-- Step 1: per-rank block of twoPyramid splits as two pyramid blocks
theorem zBlock_twoPyramid (m n r : ℕ) :
    zBlock (areaSeq (twoPyramid m n)) r
      = zBlock ((List.range m).map (↑· : ℕ → ℤ)) r
        ++ zBlock ((List.range n).map (↑· : ℕ → ℤ)) r := by
  rw [areaSeq_twoPyramid]
  unfold zBlock
  rw [List.flatMap_append]

-- ============ Step 2: range-segment flatMap lemmas ============

/-- flatMap of `f` over `range' a L` is `(replicate L blk).flatten` when `f` is
constantly `blk` on the segment `[a, a+L)`. -/
theorem flatMap_range'_const {β} (f : ℕ → List β) (blk : List β) (a L : ℕ)
    (hconst : ∀ r, a ≤ r → r < a + L → f r = blk) :
    (List.range' a L).flatMap f = (List.replicate L blk).flatten := by
  induction L generalizing a with
  | zero => simp
  | succ L ih =>
      rw [List.range'_succ, List.flatMap_cons, List.replicate_succ, List.flatten_cons,
        hconst a (le_refl _) (by omega)]
      congr 1
      apply ih
      intro r hr hr'
      exact hconst r (by omega) (by omega)

-- The combined per-rank block of twoPyramid, evaluated.
theorem zBlock_twoPyramid_eval (m n r : ℕ) (hm : 0 < m) (hn : 0 < n) :
    zBlock (areaSeq (twoPyramid m n)) r =
      (if r = 0 then [U] else if r < m then [D, U] else if r = m then [D] else [])
      ++ (if r = 0 then [U] else if r < n then [D, U] else if r = n then [D] else []) := by
  rw [zBlock_twoPyramid, zBlock_rangePyr, zBlock_rangePyr]
  congr 1
  · rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp [hm]
    · rw [if_neg (by omega : ¬ r = 0), if_neg (by omega : ¬ r = 0)]
  · rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp [hn]
    · rw [if_neg (by omega : ¬ r = 0), if_neg (by omega : ¬ r = 0)]

-- ============ regrouping identities ============

theorem flatten_replicate_DUDU (p : ℕ) :
    (List.replicate p ([D, U] ++ [D, U])).flatten = (List.replicate (2 * p) [D, U]).flatten := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [List.replicate_succ, List.flatten_cons, ih,
        show 2 * (p + 1) = 2 + 2 * p from by ring,
        show (2 : ℕ) = 1 + 1 from rfl, add_assoc, List.replicate_add, List.flatten_append]
      simp [List.replicate_add]

theorem D_flatten_DU_D (k : ℕ) :
    [D] ++ (List.replicate k [D, U]).flatten ++ [D] = [D, D] ++ (List.replicate k [U, D]).flatten := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hrep : (List.replicate (k + 1) [D, U]).flatten
          = (List.replicate k [D, U]).flatten ++ [D, U] := by
        rw [List.replicate_succ', List.flatten_concat]
      rw [hrep,
        show [D] ++ ((List.replicate k [D, U]).flatten ++ [D, U]) ++ [D]
            = ([D] ++ (List.replicate k [D, U]).flatten ++ [D]) ++ [U, D] from by
          simp [List.append_assoc],
        ih]
      have hrep2 : (List.replicate (k + 1) [U, D]).flatten
          = (List.replicate k [U, D]).flatten ++ [U, D] := by
        rw [List.replicate_succ', List.flatten_concat]
      rw [hrep2]; simp

theorem U_flatten_DU_D (k : ℕ) :
    [U] ++ (List.replicate k [D, U]).flatten ++ [D] = (List.replicate (k + 1) [U, D]).flatten := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hrep : (List.replicate (k + 1) [D, U]).flatten
          = (List.replicate k [D, U]).flatten ++ [D, U] := by
        rw [List.replicate_succ', List.flatten_concat]
      rw [hrep,
        show [U] ++ ((List.replicate k [D, U]).flatten ++ [D, U]) ++ [D]
            = ([U] ++ (List.replicate k [D, U]).flatten ++ [D]) ++ [U, D] from by
          simp [List.append_assoc],
        ih]
      have hrep2 : (List.replicate (k + 1 + 1) [U, D]).flatten
          = (List.replicate (k + 1) [U, D]).flatten ++ [U, D] := by
        rw [List.replicate_succ', List.flatten_concat]
      rw [hrep2]

-- ============ Step 2 assembly ============

-- The "pure second-pyramid" suffix: over ranks [a, n+1) with m < a ≤ n, the first
-- pyramid contributes nothing, so each block is the second pyramid's block.
-- We sum these into (DU)^{n-a} D.
theorem zBlock_suffix_pyr_n (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (a : ℕ)
    (hma : m < a) (han : a ≤ n) :
    (List.range' a (n + 1 - a)).flatMap (zBlock (areaSeq (twoPyramid m n)))
      = (List.replicate (n - a) [D, U]).flatten ++ [D] := by
  -- induct on d = n - a
  obtain ⟨d, hd⟩ : ∃ d, n = a + d := ⟨n - a, by omega⟩
  subst hd
  clear han
  induction d generalizing a with
  | zero =>
      -- single rank a = n: block is [D]
      simp only [Nat.add_zero, Nat.sub_self, List.replicate_zero, List.flatten_nil,
        List.nil_append]
      rw [show a + 1 - a = 1 from by omega, List.range'_one, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, zBlock_twoPyramid_eval m a a hm (by omega)]
      rw [if_neg (by omega : ¬ a = 0), if_neg (by omega : ¬ a < m), if_neg (by omega : ¬ a = m),
        if_neg (by omega : ¬ a = 0), if_neg (by omega : ¬ a < a), if_pos rfl]; rfl
  | succ d ih =>
      -- ranks [a, a+d+2): peel rank a (gives [D,U]), recurse on [a+1, ...)
      rw [show a + (d + 1) + 1 - a = (a + 1 + d + 1 - (a + 1)) + 1 from by omega,
        List.range'_succ, List.flatMap_cons,
        zBlock_twoPyramid_eval m (a + (d + 1)) a hm (by omega)]
      rw [if_neg (by omega : ¬ a = 0), if_neg (by omega : ¬ a < m), if_neg (by omega : ¬ a = m),
        if_neg (by omega : ¬ a = 0), if_pos (by omega : a < a + (d + 1)), List.nil_append]
      rw [show a + (d + 1) = (a + 1) + d from by omega]
      rw [ih (a + 1) (by omega) (by omega)]
      rw [show a + 1 + d - (a + 1) = d from by omega, show a + 1 + d - a = (d + 1) from by omega]
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc]

-- The "interior" head: over ranks [1, k) (both pyramids interior, k ≤ min m n),
-- each block is DUDU. Sums to (DU)^{2(k-1)}.
theorem zBlock_head_interior (m n k : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hkm : k ≤ m) (hkn : k ≤ n) :
    (List.range' 1 (k - 1)).flatMap (zBlock (areaSeq (twoPyramid m n)))
      = (List.replicate (2 * (k - 1)) [D, U]).flatten := by
  rw [flatMap_range'_const (zBlock (areaSeq (twoPyramid m n))) ([D, U] ++ [D, U]) 1 (k - 1)
    (fun r hr hr' => ?_), flatten_replicate_DUDU]
  rw [zBlock_twoPyramid_eval m n r hm hn]
  rw [if_neg (by omega : ¬ r = 0), if_pos (by omega : r < m),
    if_neg (by omega : ¬ r = 0), if_pos (by omega : r < n)]

-- Assembled zAcc for the case m ≤ n.
theorem zAcc_twoPyramid_le (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n) :
    zAcc (areaSeq (twoPyramid m n)) (n + 1)
      = [U, U] ++ (List.replicate (2 * (m - 1)) [D, U]).flatten
        ++ [D, D] ++ (List.replicate (n - m) [U, D]).flatten := by
  -- zAcc = flatMap over range (n+1) = range' 0 (n+1)
  show (List.range (n + 1)).flatMap (zBlock (areaSeq (twoPyramid m n))) = _
  rw [List.range_eq_range']
  -- split [0, n+1) = [0,1) ++ [1, m) ++ [m, n+1)
  rw [show n + 1 = 1 + ((m - 1) + (n + 1 - m)) from by omega,
    ← List.range'_append_1, ← List.range'_append_1, List.flatMap_append, List.flatMap_append]
  -- segment 1: rank 0 → UU
  rw [show (0 : ℕ) + 1 = 1 from rfl, List.range'_one, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, zBlock_twoPyramid_eval m n 0 hm hn]
  simp only [if_true]
  -- segment 2: head interior over [1, m) → (DU)^{2(m-1)}
  rw [zBlock_head_interior m n m hm hn (le_refl m) hmn]
  -- segment 3: tail over [m, n+1).  Split into rank m and suffix [m+1, n+1).
  rw [show (1 : ℕ) + (m - 1) = m from by omega]
  rcases Nat.lt_or_ge m n with hlt | hge
  · -- m < n
    rw [show n + 1 - m = 1 + (n + 1 - (m + 1)) from by omega, ← List.range'_append_1,
      List.flatMap_append, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      zBlock_twoPyramid_eval m n m hm hn]
    rw [if_neg (by omega : ¬ m = 0), if_neg (by omega : ¬ m < m), if_pos rfl,
      if_neg (by omega : ¬ m = 0), if_pos (by omega : m < n)]
    rw [show m + 1 = m + 1 from rfl, zBlock_suffix_pyr_n m n hm hn (m + 1) (by omega) (by omega)]
    -- now: UU ++ (DU)^{2(m-1)} ++ ([D] ++ [D,U]) ++ ((DU)^{n-m-1} ++ [D])
    -- target: UU ++ (DU)^{2(m-1)} ++ [D,D] ++ (UD)^{n-m}
    have hkey : ([D] ++ [D, U]) ++ ((List.replicate (n - (m + 1)) [D, U]).flatten ++ [D])
        = [D, D] ++ (List.replicate (n - m) [U, D]).flatten := by
      rw [show ([D] ++ [D, U]) ++ ((List.replicate (n - (m + 1)) [D, U]).flatten ++ [D])
            = [D, D] ++ ([U] ++ (List.replicate (n - (m + 1)) [D, U]).flatten ++ [D]) from by
          simp,
        U_flatten_DU_D (n - (m + 1)), show n - (m + 1) + 1 = n - m from by omega]
    simp only [List.append_assoc] at hkey ⊢
    rw [hkey]; rfl
  · -- m = n
    have hmn' : m = n := by omega
    subst hmn'
    rw [show m + 1 - m = 1 from by omega, List.range'_one, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, zBlock_twoPyramid_eval m m m hm hm]
    simp only [if_neg (by omega : ¬ m = 0), if_neg (by omega : ¬ m < m),
      show m - m = 0 from by omega, List.replicate_zero, List.flatten_nil, List.append_nil]
    simp

-- The "pure first-pyramid" suffix: over ranks [a, m+1) with n < a ≤ m, the second
-- pyramid contributes nothing, so each block is the first pyramid's block.
theorem zBlock_suffix_pyr_m (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (a : ℕ)
    (hna : n < a) (ham : a ≤ m) :
    (List.range' a (m + 1 - a)).flatMap (zBlock (areaSeq (twoPyramid m n)))
      = (List.replicate (m - a) [D, U]).flatten ++ [D] := by
  obtain ⟨d, hd⟩ : ∃ d, m = a + d := ⟨m - a, by omega⟩
  subst hd
  clear ham
  induction d generalizing a with
  | zero =>
      simp only [Nat.add_zero, Nat.sub_self, List.replicate_zero, List.flatten_nil,
        List.nil_append]
      rw [show a + 1 - a = 1 from by omega, List.range'_one, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, zBlock_twoPyramid_eval a n a (by omega) hn]
      rw [if_neg (by omega : ¬ a = 0), if_neg (by omega : ¬ a < a), if_pos rfl,
        if_neg (by omega : ¬ a = 0), if_neg (by omega : ¬ a < n), if_neg (by omega : ¬ a = n)]; rfl
  | succ d ih =>
      rw [show a + (d + 1) + 1 - a = (a + 1 + d + 1 - (a + 1)) + 1 from by omega,
        List.range'_succ, List.flatMap_cons,
        zBlock_twoPyramid_eval (a + (d + 1)) n a (by omega) hn]
      rw [if_neg (by omega : ¬ a = 0), if_pos (by omega : a < a + (d + 1)),
        if_neg (by omega : ¬ a = 0), if_neg (by omega : ¬ a < n), if_neg (by omega : ¬ a = n),
        List.append_nil]
      rw [show a + (d + 1) = (a + 1) + d from by omega]
      rw [ih (a + 1) (by omega) (by omega)]
      rw [show a + 1 + d - (a + 1) = d from by omega, show a + 1 + d - a = (d + 1) from by omega]
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc]

-- Assembled zAcc for the case m > n.
theorem zAcc_twoPyramid_gt (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : n < m) :
    zAcc (areaSeq (twoPyramid m n)) (m + 1)
      = [U, U] ++ (List.replicate (2 * n - 1) [D, U]).flatten
        ++ [D, D] ++ (List.replicate (m - n - 1) [U, D]).flatten := by
  show (List.range (m + 1)).flatMap (zBlock (areaSeq (twoPyramid m n))) = _
  rw [List.range_eq_range']
  -- split [0, m+1) = [0,1) ++ [1, n) ++ [n, n+1) ++ [n+1, m+1)
  rw [show m + 1 = 1 + ((n - 1) + (1 + (m + 1 - (n + 1)))) from by omega,
    ← List.range'_append_1, ← List.range'_append_1, ← List.range'_append_1,
    List.flatMap_append, List.flatMap_append, List.flatMap_append]
  -- segment 1: rank 0 → UU
  rw [show (0 : ℕ) + 1 = 1 from rfl, List.range'_one, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, zBlock_twoPyramid_eval m n 0 hm hn]
  simp only [if_true]
  -- segment 2: head interior over [1, n) → (DU)^{2(n-1)}
  rw [zBlock_head_interior m n n hm hn (le_of_lt hmn) (le_refl n)]
  -- segment 3: rank n → DUD
  rw [show (1 : ℕ) + (n - 1) = n from by omega, List.range'_one, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, zBlock_twoPyramid_eval m n n hm hn]
  rw [if_neg (by omega : ¬ n = 0), if_pos (by omega : n < m),
    if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ n < n), if_pos rfl]
  -- segment 4: pure pyr-m suffix over [n+1, m+1) → (DU)^{m-1-n} ++ [D]
  rw [show n + 1 = n + 1 from rfl, zBlock_suffix_pyr_m m n hm hn (n + 1) (by omega) (by omega)]
  -- now: UU ++ (DU)^{2(n-1)} ++ ([D,U] ++ [D]) ++ ((DU)^{m-(n+1)} ++ [D])
  -- target: UU ++ (DU)^{2n-1} ++ [D,D] ++ (UD)^{m-n-1}
  -- step A: (DU)^{2(n-1)} ++ [D,U] = (DU)^{2n-1}
  have hstepA : (List.replicate (2 * (n - 1)) [D, U]).flatten ++ [D, U]
      = (List.replicate (2 * n - 1) [D, U]).flatten := by
    rw [show 2 * n - 1 = (2 * (n - 1)) + 1 from by omega, List.replicate_succ',
      List.flatten_concat]
  -- step B: [D] ++ ((DU)^{m-(n+1)} ++ [D]) = [D,D] ++ (UD)^{m-n-1}
  have hstepB : [D] ++ ((List.replicate (m - (n + 1)) [D, U]).flatten ++ [D])
      = [D, D] ++ (List.replicate (m - n - 1) [U, D]).flatten := by
    rw [show m - (n + 1) = m - n - 1 from by omega, ← List.append_assoc,
      D_flatten_DU_D (m - n - 1)]
  -- assemble
  calc [U] ++ [U] ++
        ((List.replicate (2 * (n - 1)) [D, U]).flatten ++
          ([D, U] ++ [D] ++ ((List.replicate (m - (n + 1)) [D, U]).flatten ++ [D])))
      = [U, U] ++ (((List.replicate (2 * (n - 1)) [D, U]).flatten ++ [D, U])
          ++ ([D] ++ ((List.replicate (m - (n + 1)) [D, U]).flatten ++ [D]))) := by
            simp [List.append_assoc]
    _ = [U, U] ++ ((List.replicate (2 * n - 1) [D, U]).flatten
          ++ ([D, D] ++ (List.replicate (m - n - 1) [U, D]).flatten)) := by
            rw [hstepA, hstepB]
    _ = [U, U] ++ (List.replicate (2 * n - 1) [D, U]).flatten ++ [D, D]
          ++ (List.replicate (m - n - 1) [U, D]).flatten := by simp [List.append_assoc]

-- ============ MAIN: closed form of zeta on two-pyramid paths ============

theorem zetaMap_twoPyramid (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    zetaMap (twoPyramid m n) =
      if m ≤ n then
        [U, U] ++ (List.replicate (2 * (m - 1)) [D, U]).flatten
          ++ [D, D] ++ (List.replicate (n - m) [U, D]).flatten
      else
        [U, U] ++ (List.replicate (2 * n - 1) [D, U]).flatten
          ++ [D, D] ++ (List.replicate (m - n - 1) [U, D]).flatten := by
  rw [zetaMap_eq_zAcc, foldl_max_areaSeq_twoPyramid m n hm hn]
  by_cases hmn : m ≤ n
  · rw [if_pos hmn, show max m n + 1 = n + 1 from by omega]
    exact zAcc_twoPyramid_le m n hm hn hmn
  · rw [if_neg hmn, show max m n + 1 = m + 1 from by omega]
    exact zAcc_twoPyramid_gt m n hm hn (by omega)

/-- Sanity checks of the closed form against small explicit values. -/
example : zetaMap (twoPyramid 1 1) = [U, U, D, D] := by
  rw [zetaMap_twoPyramid 1 1 (by norm_num) (by norm_num)]; decide
example : zetaMap (twoPyramid 1 2) = [U, U, D, D, U, D] := by
  rw [zetaMap_twoPyramid 1 2 (by norm_num) (by norm_num)]; decide
example : zetaMap (twoPyramid 2 2) = [U, U, D, U, D, U, D, D] := by
  rw [zetaMap_twoPyramid 2 2 (by norm_num) (by norm_num)]; decide
example : zetaMap (twoPyramid 2 3) = [U, U, D, U, D, U, D, D, U, D] := by
  rw [zetaMap_twoPyramid 2 3 (by norm_num) (by norm_num)]; decide
example : zetaMap (twoPyramid 3 1) = [U, U, D, U, D, D, U, D] := by
  rw [zetaMap_twoPyramid 3 1 (by norm_num) (by norm_num)]; decide

-- ============ Part B: regularity of the probe language ============

/-- States for a DFA recognising `R = UU(DU)^{2q}DD(UD)^s`. -/
inductive ProbeState where
  | start    -- q0: nothing read
  | u1       -- read U
  | pE       -- read UU(DUDU)^j (even # of DU-blocks), at a block boundary, expect D
  | pEd      -- ... ++ D from pE (could begin a DU block or the central DD)
  | pO       -- odd # of DU-blocks completed, expect D
  | pOd      -- ... ++ D from pO
  | tl       -- read UU(DU)^{2q}DD(UD)^s for some s, at a (UD)-boundary  [ACCEPT]
  | tlU      -- ... ++ U from tl
  | dead     -- sink
  deriving DecidableEq

instance : Fintype ProbeState :=
  ⟨⟨{.start, .u1, .pE, .pEd, .pO, .pOd, .tl, .tlU, .dead}, by decide⟩,
    fun x => by cases x <;> decide⟩

open ProbeState

def probeDelta : ProbeState → Step → ProbeState
  | start, U => u1   | start, D => dead
  | u1,    U => pE   | u1,    D => dead
  | pE,    U => dead | pE,    D => pEd
  | pEd,   U => pO   | pEd,   D => tl
  | pO,    U => dead | pO,    D => pOd
  | pOd,   U => pE   | pOd,   D => dead
  | tl,    U => tlU  | tl,    D => dead
  | tlU,   U => dead | tlU,   D => tl
  | dead,  _ => dead

def probeDFA : DFA' Step where
  Q := ProbeState
  delta := probeDelta
  q0 := start
  F := {tl}

-- foldl of probeDelta over the (DU)-blocks: from pE, reading (DU)^{2q} returns to pE.
theorem fold_DU_even (q : ℕ) :
    (((List.replicate (2 * q) [D, U]).flatten).foldl probeDelta pE) = pE := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show 2 * (q + 1) = 2 * q + 1 + 1 from by ring]
      rw [List.replicate_succ', List.flatten_concat, List.replicate_succ', List.flatten_concat]
      rw [List.foldl_append, List.foldl_append, ih]
      rfl

-- foldl over (UD)^s from tl returns to tl.
theorem fold_UD (s : ℕ) :
    (((List.replicate s [U, D]).flatten).foldl probeDelta tl) = tl := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [List.replicate_succ', List.flatten_concat, List.foldl_append, ih]
      rfl

-- Probe words are accepted.
theorem probe_accepts {w : List Step} (hw : inRegularProbe w) : probeDFA.accepts w := by
  obtain ⟨q, s, rfl⟩ := hw
  unfold DFA'.accepts
  show (([U, U] ++ (List.replicate (2 * q) [D, U]).flatten ++ [D, D]
      ++ (List.replicate s [U, D]).flatten).foldl probeDelta start) ∈ ({tl} : Set ProbeState)
  rw [List.foldl_append, List.foldl_append, List.foldl_append]
  rw [show ([U, U]).foldl probeDelta start = pE from rfl, fold_DU_even q,
    show ([D, D]).foldl probeDelta pE = tl from rfl, fold_UD s]
  rfl

-- The per-state characterisation of words reaching that state from `start`.
def ProbeInv : ProbeState → List Step → Prop
  | start, w => w = []
  | u1,    w => w = [U]
  | pE,    w => ∃ q, w = [U, U] ++ (List.replicate (2 * q) [D, U]).flatten
  | pEd,   w => ∃ q, w = [U, U] ++ (List.replicate (2 * q) [D, U]).flatten ++ [D]
  | pO,    w => ∃ q, w = [U, U] ++ (List.replicate (2 * q + 1) [D, U]).flatten
  | pOd,   w => ∃ q, w = [U, U] ++ (List.replicate (2 * q + 1) [D, U]).flatten ++ [D]
  | tl,    w => inRegularProbe w
  | tlU,   w => ∃ q s, w = [U, U] ++ (List.replicate (2 * q) [D, U]).flatten ++ [D, D]
                  ++ (List.replicate s [U, D]).flatten ++ [U]
  | dead,  _ => True

-- The invariant holds for every word's run.
theorem probeInv_foldl (w : List Step) : ProbeInv (w.foldl probeDelta start) w := by
  induction w using List.reverseRecOn with
  | nil => exact rfl
  | append_singleton w x ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      -- case on the state reached by w, then on x
      set st := w.foldl probeDelta start with hst
      cases hcase : st with
      | start =>
          rw [hcase] at ih; simp only [ProbeInv] at ih; subst ih
          cases x <;> simp only [probeDelta, ProbeInv, List.nil_append]
      | u1 =>
          rw [hcase] at ih; simp only [ProbeInv] at ih; subst ih
          cases x with
          | U => exact ⟨0, by simp⟩
          | D => simp only [probeDelta, ProbeInv]
      | pE =>
          rw [hcase] at ih; simp only [ProbeInv] at ih; obtain ⟨q, rfl⟩ := ih
          cases x with
          | U => simp only [probeDelta, ProbeInv]
          | D => exact ⟨q, by simp⟩
      | pEd =>
          rw [hcase] at ih; simp only [ProbeInv] at ih; obtain ⟨q, rfl⟩ := ih
          cases x with
          | U => -- pEd → pO, blocks 2q+1
            refine ⟨q, ?_⟩
            rw [List.replicate_succ', List.flatten_concat]
            simp [List.append_assoc]
          | D => -- pEd → tl, central DD, s = 0
            exact ⟨q, 0, by simp [List.append_assoc]⟩
      | pO =>
          rw [hcase] at ih; simp only [ProbeInv] at ih; obtain ⟨q, rfl⟩ := ih
          cases x with
          | U => simp only [probeDelta, ProbeInv]
          | D => exact ⟨q, by simp⟩
      | pOd =>
          rw [hcase] at ih; simp only [ProbeInv] at ih; obtain ⟨q, rfl⟩ := ih
          cases x with
          | U => -- pOd → pE, blocks 2q+2 = 2(q+1)
            refine ⟨q + 1, ?_⟩
            have hL : (List.replicate (2 * (q + 1)) [D, U]).flatten
                = (List.replicate (2 * q) [D, U]).flatten ++ [D, U] ++ [D, U] := by
              rw [show 2 * (q + 1) = (2 * q + 1) + 1 from by ring, List.replicate_succ',
                List.flatten_concat, List.replicate_succ', List.flatten_concat]
            have hR : (List.replicate (2 * q + 1) [D, U]).flatten
                = (List.replicate (2 * q) [D, U]).flatten ++ [D, U] := by
              rw [List.replicate_succ', List.flatten_concat]
            rw [hL, hR]; simp [List.append_assoc]
          | D => simp only [probeDelta, ProbeInv]
      | tl =>
          rw [hcase] at ih; simp only [ProbeInv] at ih; obtain ⟨q, s, rfl⟩ := ih
          cases x with
          | U => -- tl → tlU
            exact ⟨q, s, by simp [List.append_assoc]⟩
          | D => simp only [probeDelta, ProbeInv]
      | tlU =>
          rw [hcase] at ih; simp only [ProbeInv] at ih; obtain ⟨q, s, rfl⟩ := ih
          cases x with
          | U => simp only [probeDelta, ProbeInv]
          | D => -- tlU → tl, completes one more UD, s+1
            refine ⟨q, s + 1, ?_⟩
            rw [List.replicate_succ', List.flatten_concat]
            simp [List.append_assoc]
      | dead =>
          rw [hcase] at ih
          cases x <;> simp only [probeDelta, ProbeInv]

-- The DFA's language is exactly the probe language.
theorem probeDFA_language : probeDFA.language = {w : List Step | inRegularProbe w} := by
  ext w
  constructor
  · intro hw
    -- hw : probeDFA.accepts w, i.e. foldl ... ∈ {tl}
    have hinv := probeInv_foldl w
    have hst : w.foldl probeDelta start = tl := by
      have : w.foldl probeDFA.delta probeDFA.q0 ∈ probeDFA.F := hw
      exact this
    rw [hst] at hinv
    exact hinv
  · intro hw
    exact probe_accepts hw

-- The probe language is regular.
theorem inRegularProbe_isRegular : IsRegularLang {w : List Step | inRegularProbe w} :=
  ⟨probeDFA, probeDFA_language⟩

-- foldl over (DU)-blocks from pE with ODD count lands in pO.
theorem fold_DU_odd (q : ℕ) :
    (((List.replicate (2 * q + 1) [D, U]).flatten).foldl probeDelta pE) = pO := by
  rw [List.replicate_succ', List.flatten_concat, List.foldl_append, fold_DU_even q]
  rfl

-- foldl over (UD)^t from dead stays dead.
theorem fold_UD_dead (t : ℕ) :
    (((List.replicate t [U, D]).flatten).foldl probeDelta dead) = dead := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [List.replicate_succ', List.flatten_concat, List.foldl_append, ih]
      rfl

-- The m > n closed-form word lands in `dead` (so is NOT accepted).
theorem fold_gt_word_dead (n t : ℕ) (hn : 0 < n) :
    (([U, U] ++ (List.replicate (2 * n - 1) [D, U]).flatten ++ [D, D]
      ++ (List.replicate t [U, D]).flatten).foldl probeDelta start) = dead := by
  rw [List.foldl_append, List.foldl_append, List.foldl_append,
    show ([U, U]).foldl probeDelta start = pE from rfl,
    show 2 * n - 1 = 2 * (n - 1) + 1 from by omega, fold_DU_odd (n - 1),
    show ([D, D]).foldl probeDelta pO = dead from rfl, fold_UD_dead t]

-- ============ MAIN: the probe characterises m ≤ n ============

theorem inRegularProbe_zetaMap_twoPyramid (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    inRegularProbe (zetaMap (twoPyramid m n)) ↔ m ≤ n := by
  rw [zetaMap_twoPyramid m n hm hn]
  constructor
  · intro hmem
    by_contra hgt
    push Not at hgt
    -- m > n: the word lands in `dead`, so it is not in the probe language
    rw [if_neg (by omega : ¬ m ≤ n)] at hmem
    have hacc : probeDFA.accepts
        ([U, U] ++ (List.replicate (2 * n - 1) [D, U]).flatten ++ [D, D]
          ++ (List.replicate (m - n - 1) [U, D]).flatten) := by
      have := probeDFA_language
      rw [Set.ext_iff] at this
      exact (this _).mpr hmem
    have hdead := fold_gt_word_dead n (m - n - 1) hn
    simp only [DFA'.accepts, probeDFA] at hacc
    rw [hdead] at hacc
    exact ProbeState.noConfusion hacc
  · intro hle
    rw [if_pos hle]
    -- exhibit q = m - 1, s = n - m
    exact ⟨m - 1, n - m, rfl⟩


/-! ## Theorem 5.4: Zeta is not regular/MSO (`cor:zeta-not-regular`, paper-full-new.tex) -/
