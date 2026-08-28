/-
# `lem:inverse-zeta-fas`: first ascent of inverse zeta on the
# copied slice — the honest bijectivity-free form

Formalises paper `lem:inverse-zeta-fas` (paper.tex): rather than
`fas(ζ⁻¹(W_{m,n}))` (which presupposes that `ζ` is a bijection, nowhere
formalised), we exhibit the EXPLICIT ζ-preimage — the row of `m + 1` balanced
pyramids — and prove `zetaMap (pyramidRow m n) = copiedSlice m n` together with
`firstAscent (pyramidRow m n) = ⌈(m+n)/(m+1)⌉`.  The component theorems are
UNCONDITIONAL (no `m ≥ 1` needed); the packaging corollary `inverse_zeta_fas`
carries the paper's hypothesis for fidelity.

Trust base of the headline chain:
`[propext, Classical.choice, Quot.sound]` (the `native_decide` examples are
regression anchors only).
-/
import RequestProject.InverseZeta
import RequestProject.ZetaClassification
import RequestProject.AreaSeq
import RequestProject.TightTargets

open Step

/-! ## S1 — the pyramid row -/

/-- A single pyramid `U^l D^l`. -/
def pyramid (l : ℕ) : List Step := List.replicate l U ++ List.replicate l D

/-- The balanced number of blocks: `⌈(m+n)/(m+1)⌉` as a `Nat` division. -/
def pyrB (m n : ℕ) : ℕ := (m + n + m) / (m + 1)

/-- The number of long (length-`b`) blocks. -/
def pyrS (m n : ℕ) : ℕ := (m + n) - (m + 1) * (pyrB m n - 1)

/-- The balanced block lengths: `s` long blocks then `m + 1 - s` short ones. -/
def pyramidLens (m n : ℕ) : List ℕ :=
  List.replicate (pyrS m n) (pyrB m n)
    ++ List.replicate (m + 1 - pyrS m n) (pyrB m n - 1)

/-- **The explicit ζ-preimage of the copied slice**: the balanced pyramid row. -/
def pyramidRow (m n : ℕ) : List Step := (pyramidLens m n).flatMap pyramid

/-- The staircase area sequence `(0, 1, …, l-1)`. -/
def stairSeq (l : ℕ) : List ℤ := (List.range l).map (fun (a : ℕ) => (a : ℤ))

-- Regression anchors (the paper's worked example `W_{2,5}` and corners).
example : pyramidRow 2 5 = [U, U, U, D, D, D, U, U, D, D, U, U, D, D] := by
  native_decide
example : zetaMap (pyramidRow 2 5) = copiedSlice 2 5 := by native_decide
example : firstAscent (pyramidRow 2 5) = (2 + 5 + 2) / (2 + 1) := by native_decide
example : zetaMap (pyramidRow 1 0) = copiedSlice 1 0 := by native_decide
example : zetaMap (pyramidRow 3 1) = copiedSlice 3 1 := by native_decide
example : zetaMap (pyramidRow 0 0) = copiedSlice 0 0 := by native_decide
example : zetaMap (pyramidRow 0 4) = copiedSlice 0 4 := by native_decide
example : zetaMap (pyramidRow 4 9) = copiedSlice 4 9 := by native_decide

/-! ## S2 — the balanced-partition arithmetic -/

theorem pyrArith (m n : ℕ) (hN : 1 ≤ m + n) :
    1 ≤ pyrB m n ∧ 1 ≤ pyrS m n ∧ pyrS m n ≤ m + 1
      ∧ pyrS m n + (m + 1) * (pyrB m n - 1) = m + n := by
  have hb1 : 1 ≤ pyrB m n := by
    rw [pyrB, Nat.le_div_iff_mul_le (by omega)]
    omega
  have hX : (m + 1) * 1 ≤ (m + 1) * pyrB m n := Nat.mul_le_mul_left _ hb1
  have hd := Nat.div_add_mod (m + n + m) (m + 1)
  have hmod : (m + n + m) % (m + 1) < m + 1 := Nat.mod_lt _ (by omega)
  rw [pyrS, Nat.mul_sub_one]
  refine ⟨hb1, ?_, ?_, ?_⟩ <;>
  · rw [pyrB] at *
    generalize hXg : (m + 1) * ((m + n + m) / (m + 1)) = X at *
    omega

theorem pyrB_two_le (m n : ℕ) (hn : 2 ≤ n) : 2 ≤ pyrB m n := by
  rw [pyrB, Nat.le_div_iff_mul_le (by omega)]
  omega

theorem pyrArith_mid (m n : ℕ) (hn : 2 ≤ n) :
    (m + 1) * (pyrB m n - 2) + pyrS m n = n - 1 := by
  obtain ⟨hb1, hs1, hsle, hsum⟩ := pyrArith m n (by omega)
  have hb2 := pyrB_two_le m n hn
  have h1 : (m + 1) * (pyrB m n - 1) = (m + 1) * pyrB m n - (m + 1) * 1 := by
    rw [Nat.mul_sub]
  have h2 : (m + 1) * (pyrB m n - 2) = (m + 1) * pyrB m n - (m + 1) * 2 := by
    rw [Nat.mul_sub]
  have hmul2 : (m + 1) * 2 ≤ (m + 1) * pyrB m n := Nat.mul_le_mul_left _ hb2
  rw [h2]
  rw [h1] at hsum
  generalize hXg : (m + 1) * pyrB m n = X at hsum hmul2 ⊢
  omega

/-! ## S3 — the degenerate route (`n ≤ 1`) -/

theorem pyramidLens_of_le_one (m n : ℕ) (hn : n ≤ 1) :
    pyramidLens m n
      = List.replicate (m + n) 1 ++ List.replicate (m + 1 - (m + n)) 0 := by
  rcases Nat.eq_zero_or_pos (m + n) with h0 | hN
  · have hm : m = 0 := by omega
    have hn0 : n = 0 := by omega
    subst hm hn0
    decide
  · have hb : pyrB m n = 1 := by
      rw [pyrB]
      apply Nat.div_eq_of_lt_le
      · omega
      · omega
    have hs : pyrS m n = m + n := by
      rw [pyrS, hb]
      simp
    rw [pyramidLens, hb, hs]

theorem pyramidRow_of_le_one (m n : ℕ) (hn : n ≤ 1) :
    pyramidRow m n = (List.replicate (m + n) [U, D]).flatten := by
  rw [pyramidRow, pyramidLens_of_le_one m n hn, List.flatMap_append,
    List.flatMap_replicate, List.flatMap_replicate]
  have h1 : pyramid 1 = [U, D] := by decide
  have h0 : pyramid 0 = [] := by decide
  rw [h1, h0]
  simp

theorem areaSeq_flat (N : ℕ) :
    areaSeq ((List.replicate N [U, D]).flatten) = List.replicate N 0 := by
  induction N with
  | zero => simp [areaSeq, uPositions]
  | succ N ih =>
    rw [List.replicate_succ, List.flatten_cons,
      show ([U, D] : List Step) ++ (List.replicate N [U, D]).flatten
        = U :: (D :: (List.replicate N [U, D]).flatten) from rfl,
      areaSeq_cons_U, areaSeq_cons_D, ih]
    simp [List.map_replicate, List.replicate_succ]

/-- ζ of the flat path `(UD)^N` is the two-run path `U^N D^N`. -/
theorem zetaMap_flat (N : ℕ) :
    zetaMap ((List.replicate N [U, D]).flatten)
      = List.replicate N U ++ List.replicate N D := by
  rw [zetaMap_eq_zAcc, areaSeq_flat]
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    simp [zAcc, zBlock]
  · have hle : ∀ k : ℕ, (List.replicate k (0 : ℤ)).foldl max 0 ≤ 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [List.replicate_succ]
        simpa using ih
    have hmax : (List.replicate N (0 : ℤ)).foldl max 0 = 0 := by
      have hge := foldl_max_ge_acc (List.replicate N (0 : ℤ)) 0
      have := hle N
      omega
    rw [hmax]
    show zAcc (List.replicate N (0 : ℤ)) 2 = _
    rw [show (2 : ℕ) = 1 + 1 from rfl, zAcc_succ,
      show (1 : ℕ) = 0 + 1 from rfl, zAcc_succ]
    have hz : zAcc (List.replicate N (0 : ℤ)) 0 = [] := by
      simp [zAcc]
    have hb0 : zBlock (List.replicate N (0 : ℤ)) 0 = List.replicate N U := by
      rw [zBlock, List.flatMap_replicate]
      have : zEmit ((0 : ℕ) : ℤ) 0 = [U] := by decide
      rw [this]
      simp [List.flatten_replicate_singleton]
    have hb1 : zBlock (List.replicate N (0 : ℤ)) 1 = List.replicate N D := by
      rw [zBlock, List.flatMap_replicate]
      have : zEmit ((1 : ℕ) : ℤ) 0 = [D] := by decide
      rw [this]
      simp [List.flatten_replicate_singleton]
    rw [hz, hb0, hb1]
    simp

/-! ## S4 — the staircase scan kit -/

theorem stairSeq_succ (l : ℕ) :
    stairSeq (l + 1) = 0 :: (stairSeq l).map (· + 1) := by
  unfold stairSeq
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, Nat.cast_zero, List.map_map, Function.comp_def,
    Nat.cast_succ]

theorem stairSeq_concat (l : ℕ) : stairSeq (l + 1) = stairSeq l ++ [(l : ℤ)] := by
  unfold stairSeq
  rw [List.range_succ, List.map_append]
  rfl

theorem areaSeq_replicate_U (l : ℕ) :
    areaSeq (List.replicate l U) = stairSeq l := by
  induction l with
  | zero => simp [areaSeq, uPositions, stairSeq]
  | succ l ih =>
    rw [List.replicate_succ, areaSeq_cons_U, ih, stairSeq_succ]

theorem height_pyramid_end (l : ℕ) :
    height (pyramid l) (pyramid l).length = 0 := by
  rw [height_eq_count, List.take_length, pyramid, List.count_append,
    List.count_append]
  simp [List.count_replicate]

theorem areaSeq_pyramid (l : ℕ) : areaSeq (pyramid l) = stairSeq l := by
  rw [pyramid, areaSeq_append, areaSeq_replicate_D, areaSeq_replicate_U]
  simp

theorem areaSeq_flatMap_pyramid (ls : List ℕ) :
    areaSeq (ls.flatMap pyramid) = ls.flatMap stairSeq := by
  induction ls with
  | nil => exact areaSeq_replicate_D 0
  | cons l ls ih =>
    rw [List.flatMap_cons, List.flatMap_cons, areaSeq_append, ih,
      areaSeq_pyramid, height_pyramid_end]
    simp

/-- **The workhorse**: the rank-`r` scan of a staircase block. -/
theorem zBlock_stair (l r : ℕ) :
    zBlock (stairSeq l) r
      = (if 1 ≤ r ∧ r ≤ l then [D] else []) ++ (if r < l then [U] else []) := by
  induction l with
  | zero =>
    simp [stairSeq, zBlock]
    omega
  | succ l ih =>
    rw [stairSeq_concat, zBlock, List.flatMap_append, ← zBlock, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rcases Nat.lt_trichotomy r l with h | h | h
    · have hz : zEmit (r : ℤ) (l : ℤ) = [] := by
        rw [zEmit, if_neg (by omega), if_neg (by omega)]
      rw [hz, List.append_nil]
      have hd1 : r < l := h
      have hd2 : r < l + 1 := by omega
      have hc1 : r ≤ l := by omega
      have hc2 : r ≤ l + 1 := by omega
      by_cases hr0 : 1 ≤ r
      · rw [if_pos ⟨hr0, hc1⟩, if_pos hd1, if_pos ⟨hr0, hc2⟩, if_pos hd2]
      · have hn1 : ¬ (1 ≤ r ∧ r ≤ l) := by omega
        have hn2 : ¬ (1 ≤ r ∧ r ≤ l + 1) := by omega
        rw [if_neg hn1, if_pos hd1, if_neg hn2, if_pos hd2]
    · subst h
      have hz : zEmit (r : ℤ) (r : ℤ) = [U] := by
        rw [zEmit, if_pos rfl]
      rw [hz]
      have hlt : ¬ (r < r) := by omega
      have hlt1 : r < r + 1 := by omega
      by_cases hr0 : 1 ≤ r
      · have hp1 : 1 ≤ r ∧ r ≤ r := by omega
        have hp2 : 1 ≤ r ∧ r ≤ r + 1 := by omega
        rw [if_pos hp1, if_neg hlt, if_pos hp2, if_pos hlt1]
        simp
      · have hn1 : ¬ (1 ≤ r ∧ r ≤ r) := by omega
        have hn2 : ¬ (1 ≤ r ∧ r ≤ r + 1) := by omega
        rw [if_neg hn1, if_neg hlt, if_neg hn2, if_pos hlt1]
        simp
    · rcases Nat.lt_or_ge l (r - 1) with h2 | h2
      · have hz : zEmit (r : ℤ) (l : ℤ) = [] := by
          rw [zEmit, if_neg (by omega), if_neg (by omega)]
        have hn1 : ¬ (1 ≤ r ∧ r ≤ l) := by omega
        have hn2 : ¬ (r < l) := by omega
        have hn3 : ¬ (1 ≤ r ∧ r ≤ l + 1) := by omega
        have hn4 : ¬ (r < l + 1) := by omega
        rw [hz, List.append_nil, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4]
      · have hr1 : r = l + 1 := by omega
        subst hr1
        have hz : zEmit ((l + 1 : ℕ) : ℤ) (l : ℤ) = [D] := by
          rw [zEmit, if_neg (by omega), if_pos (by push_cast; ring)]
        have hn1 : ¬ (1 ≤ l + 1 ∧ l + 1 ≤ l) := by omega
        have hn2 : ¬ (l + 1 < l) := by omega
        have hp3 : 1 ≤ l + 1 ∧ l + 1 ≤ l + 1 := by omega
        have hn4 : ¬ (l + 1 < l + 1) := by omega
        rw [hz, if_neg hn1, if_neg hn2, if_pos hp3, if_neg hn4]
        simp

theorem zBlock_flatten_replicate (k : ℕ) (w : List ℤ) (r : ℕ) :
    zBlock ((List.replicate k w).flatten) r
      = (List.replicate k (zBlock w r)).flatten := by
  induction k with
  | zero => simp [zBlock]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, zBlock, List.flatMap_append,
      ← zBlock, ← zBlock, ih, List.replicate_succ, List.flatten_cons]

/-! ## S5 — per-rank blocks of the pyramid row (`n ≥ 2`) -/

theorem areaSeq_pyramidRow (m n : ℕ) :
    areaSeq (pyramidRow m n)
      = (List.replicate (pyrS m n) (stairSeq (pyrB m n))).flatten
        ++ (List.replicate (m + 1 - pyrS m n) (stairSeq (pyrB m n - 1))).flatten := by
  rw [pyramidRow, areaSeq_flatMap_pyramid, pyramidLens, List.flatMap_append,
    List.flatMap_replicate, List.flatMap_replicate]

theorem zBlock_pyramidRow (m n r : ℕ) :
    zBlock (areaSeq (pyramidRow m n)) r
      = (List.replicate (pyrS m n) (zBlock (stairSeq (pyrB m n)) r)).flatten
        ++ (List.replicate (m + 1 - pyrS m n)
            (zBlock (stairSeq (pyrB m n - 1)) r)).flatten := by
  rw [areaSeq_pyramidRow, zBlock, List.flatMap_append, ← zBlock, ← zBlock,
    zBlock_flatten_replicate, zBlock_flatten_replicate]

theorem zBlock_pyramidRow_zero (m n : ℕ) (hn : 2 ≤ n) :
    zBlock (areaSeq (pyramidRow m n)) 0 = List.replicate (m + 1) U := by
  obtain ⟨hb1, hs1, hsle, hsum⟩ := pyrArith m n (by omega)
  have hb2 := pyrB_two_le m n hn
  rw [zBlock_pyramidRow,
    zBlock_stair, zBlock_stair,
    if_neg (by omega : ¬ (1 ≤ 0 ∧ 0 ≤ pyrB m n)),
    if_pos (by omega : 0 < pyrB m n),
    if_neg (by omega : ¬ (1 ≤ 0 ∧ 0 ≤ pyrB m n - 1)),
    if_pos (by omega : 0 < pyrB m n - 1)]
  simp only [List.nil_append, List.flatten_replicate_singleton]
  rw [← List.replicate_add]
  congr 1
  omega

theorem zBlock_pyramidRow_mid (m n r : ℕ) (hn : 2 ≤ n) (h1 : 1 ≤ r)
    (h2 : r ≤ pyrB m n - 2) :
    zBlock (areaSeq (pyramidRow m n)) r
      = (List.replicate (m + 1) [D, U]).flatten := by
  obtain ⟨hb1, hs1, hsle, hsum⟩ := pyrArith m n (by omega)
  have hb2 := pyrB_two_le m n hn
  rw [zBlock_pyramidRow,
    zBlock_stair, zBlock_stair,
    if_pos (⟨h1, by omega⟩ : 1 ≤ r ∧ r ≤ pyrB m n),
    if_pos (by omega : r < pyrB m n),
    if_pos (⟨h1, by omega⟩ : 1 ≤ r ∧ r ≤ pyrB m n - 1),
    if_pos (by omega : r < pyrB m n - 1)]
  show (List.replicate (pyrS m n) [D, U]).flatten
      ++ (List.replicate (m + 1 - pyrS m n) [D, U]).flatten = _
  rw [← List.flatten_append, ← List.replicate_add]
  congr 2
  omega

theorem zBlock_pyramidRow_top (m n : ℕ) (hn : 2 ≤ n) :
    zBlock (areaSeq (pyramidRow m n)) (pyrB m n - 1)
      = (List.replicate (pyrS m n) [D, U]).flatten
        ++ List.replicate (m + 1 - pyrS m n) D := by
  obtain ⟨hb1, hs1, hsle, hsum⟩ := pyrArith m n (by omega)
  have hb2 := pyrB_two_le m n hn
  rw [zBlock_pyramidRow,
    zBlock_stair, zBlock_stair,
    if_pos (⟨by omega, by omega⟩ : 1 ≤ pyrB m n - 1 ∧ pyrB m n - 1 ≤ pyrB m n),
    if_pos (by omega : pyrB m n - 1 < pyrB m n),
    if_pos (⟨by omega, by omega⟩ : 1 ≤ pyrB m n - 1 ∧ pyrB m n - 1 ≤ pyrB m n - 1),
    if_neg (by omega : ¬ (pyrB m n - 1 < pyrB m n - 1))]
  simp only [List.append_nil]
  congr 1
  rw [List.flatten_replicate_singleton]

theorem zBlock_pyramidRow_end (m n : ℕ) (hn : 2 ≤ n) :
    zBlock (areaSeq (pyramidRow m n)) (pyrB m n)
      = List.replicate (pyrS m n) D := by
  obtain ⟨hb1, hs1, hsle, hsum⟩ := pyrArith m n (by omega)
  have hb2 := pyrB_two_le m n hn
  rw [zBlock_pyramidRow,
    zBlock_stair, zBlock_stair,
    if_pos (⟨by omega, le_refl _⟩ : 1 ≤ pyrB m n ∧ pyrB m n ≤ pyrB m n),
    if_neg (by omega : ¬ (pyrB m n < pyrB m n)),
    if_neg (by omega : ¬ (1 ≤ pyrB m n ∧ pyrB m n ≤ pyrB m n - 1)),
    if_neg (by omega : ¬ (pyrB m n < pyrB m n - 1))]
  simp [List.flatten_replicate_singleton, List.flatten_replicate_nil]

/-! ## S6 — rank accumulation and the scan window -/

theorem zAcc_pyramidRow_prefix (m n : ℕ) (hn : 2 ≤ n) (j : ℕ)
    (hj : j ≤ pyrB m n - 2) :
    zAcc (areaSeq (pyramidRow m n)) (j + 1)
      = List.replicate (m + 1) U ++ (List.replicate ((m + 1) * j) [D, U]).flatten := by
  induction j with
  | zero =>
    rw [zAcc_succ, zBlock_pyramidRow_zero m n hn]
    all_goals simp [zAcc]
  | succ j ih =>
    have hih := ih (by omega)
    have hstep := zBlock_pyramidRow_mid m n (j + 1) hn (by omega) (by omega)
    rw [zAcc_succ, hih]
    rw [hstep]
    rw [List.append_assoc]
    all_goals rw [← List.flatten_append]
    all_goals rw [← List.replicate_add]
    congr 3

/-- Upper bound for a `foldl max`. -/
theorem foldl_max_le (a : List ℤ) (c : ℤ) (hc : 0 ≤ c) (h : ∀ x ∈ a, x ≤ c) :
    a.foldl max 0 ≤ c := by
  suffices hgen : ∀ acc : ℤ, acc ≤ c → a.foldl max acc ≤ c by
    exact hgen 0 hc
  induction a with
  | nil => intro acc hacc; simpa using hacc
  | cons x xs ih =>
    intro acc hacc
    have hx : x ≤ c := h x List.mem_cons_self
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy)) (max acc x)
      (max_le hacc hx)

theorem maxA_pyramidRow (m n : ℕ) (hn : 2 ≤ n) :
    (areaSeq (pyramidRow m n)).foldl max 0 = (pyrB m n : ℤ) - 1 := by
  obtain ⟨hb1, hs1, hsle, hsum⟩ := pyrArith m n (by omega)
  have hb2 := pyrB_two_le m n hn
  apply le_antisymm
  · apply foldl_max_le _ _ (by omega)
    intro x hx
    rw [areaSeq_pyramidRow, List.mem_append] at hx
    rcases hx with hx | hx <;>
    · rw [List.mem_flatten] at hx
      obtain ⟨w, hw, hxw⟩ := hx
      rw [List.mem_replicate] at hw
      rw [hw.2, stairSeq, List.mem_map] at hxw
      obtain ⟨a, ha, rfl⟩ := hxw
      rw [List.mem_range] at ha
      omega
  · apply le_foldl_max
    rw [areaSeq_pyramidRow, List.mem_append]
    left
    rw [List.mem_flatten]
    refine ⟨stairSeq (pyrB m n), ?_, ?_⟩
    · rw [List.mem_replicate]
      exact ⟨by omega, rfl⟩
    · rw [stairSeq, List.mem_map]
      refine ⟨pyrB m n - 1, ?_, ?_⟩
      · rw [List.mem_range]
        omega
      · omega

theorem zetaMap_pyramidRow_of_two_le (m n : ℕ) (hn : 2 ≤ n) :
    zetaMap (pyramidRow m n)
      = List.replicate (m + 1) U ++ (List.replicate (n - 1) [D, U]).flatten
        ++ List.replicate (m + 1) D := by
  obtain ⟨hb1, hs1, hsle, hsum⟩ := pyrArith m n (by omega)
  have hb2 := pyrB_two_le m n hn
  have hmid := pyrArith_mid m n hn
  rw [zetaMap_eq_zAcc, maxA_pyramidRow m n hn]
  have hwin : ((pyrB m n : ℤ) - 1).toNat + 2 = (pyrB m n - 2 + 1) + 1 + 1 := by
    omega
  rw [hwin, zAcc_succ, zAcc_succ,
    zAcc_pyramidRow_prefix m n hn (pyrB m n - 2) (le_refl _),
    show pyrB m n - 2 + 1 = pyrB m n - 1 from by omega,
    zBlock_pyramidRow_top m n hn,
    show pyrB m n - 2 + 2 = pyrB m n from by omega,
    zBlock_pyramidRow_end m n hn]
  simp only [List.append_assoc]
  congr 1
  rw [← List.replicate_add,
    show m + 1 - pyrS m n + pyrS m n = m + 1 from by omega,
    ← List.append_assoc, ← List.flatten_append, ← List.replicate_add, hmid]

/-! ## S7 — word algebra and the headline -/

theorem cons_U_flatten_DU (k : ℕ) :
    U :: (List.replicate k [D, U]).flatten
      = (List.replicate k [U, D]).flatten ++ [U] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons,
      show ([D, U] : List Step) ++ (List.replicate k [D, U]).flatten
        = D :: (U :: (List.replicate k [D, U]).flatten) from rfl,
      ih, List.replicate_succ, List.flatten_cons]
    rfl

/-- **The headline computation** (`lem:inverse-zeta-fas`, the scan): ζ of the
balanced pyramid row is the copied slice — unconditionally. -/
theorem zetaMap_pyramidRow (m n : ℕ) :
    zetaMap (pyramidRow m n) = copiedSlice m n := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · -- n ≥ 2
    rw [zetaMap_pyramidRow_of_two_le m n (by omega), copiedSlice]
    have h4 : (List.replicate (n - 1) [U, D]).flatten ++ [U, D]
        = (List.replicate n [U, D]).flatten := by
      conv_rhs => rw [show n = (n - 1) + 1 from by omega]
      rw [List.replicate_succ', List.flatten_append]
      rfl
    rw [List.replicate_succ' (n := m) (a := U),
      List.replicate_succ (n := m) (a := D), ← h4]
    simp only [List.append_assoc]
    congr 1
    rw [show [U] ++ ((List.replicate (n - 1) [D, U]).flatten
          ++ (D :: List.replicate m D))
        = (U :: (List.replicate (n - 1) [D, U]).flatten)
          ++ (D :: List.replicate m D) from rfl,
      cons_U_flatten_DU (n - 1), List.append_assoc]
    rfl
  · -- n ≤ 1
    rw [pyramidRow_of_le_one m n hn, zetaMap_flat (m + n), copiedSlice]
    interval_cases n
    · simp
    · rw [List.replicate_succ' (n := m) (a := U),
        List.replicate_succ (n := m) (a := D)]
      simp [List.append_assoc]

/-! ## S8 — Dyck-ness and length of the pyramid row -/

theorem isDyckPath_pyramid (l : ℕ) : IsDyckPath (pyramid l) := by
  induction l with
  | zero =>
    constructor
    · intro k hk
      have h0 : (pyramid 0).length = 0 := rfl
      have hk0 : k = 0 := by omega
      rw [hk0, height_zero]
    · decide
  | succ l ih =>
    have h : pyramid (l + 1) = U :: (pyramid l ++ [D]) := by
      rw [pyramid, pyramid, List.replicate_succ (n := l) (a := U),
        List.replicate_succ' (n := l) (a := D)]
      simp [List.append_assoc]
    rw [h]
    exact isDyckPath_raise ih

theorem isDyckPath_flatMap_pyramid (ls : List ℕ) :
    IsDyckPath (ls.flatMap pyramid) := by
  induction ls with
  | nil =>
    constructor
    · intro k hk
      have hk0 : k = 0 := by simpa using hk
      rw [hk0, height_zero]
    · decide
  | cons l ls ih =>
    rw [List.flatMap_cons]
    exact isDyckPath_append (isDyckPath_pyramid l) ih

theorem isDyckPath_pyramidRow (m n : ℕ) : IsDyckPath (pyramidRow m n) :=
  isDyckPath_flatMap_pyramid _

theorem length_flatMap_pyramid (ls : List ℕ) :
    (ls.flatMap pyramid).length = 2 * ls.sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.sum_cons, pyramid,
      List.length_append, List.length_replicate, List.length_replicate]
    ring

theorem sum_pyramidLens (m n : ℕ) : (pyramidLens m n).sum = m + n := by
  rcases Nat.eq_zero_or_pos (m + n) with h0 | hN
  · have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    subst hm hn
    decide
  · obtain ⟨hb1, hs1, hsle, hsum⟩ := pyrArith m n hN
    obtain ⟨c, hc⟩ : ∃ c, pyrB m n = c + 1 := ⟨pyrB m n - 1, by omega⟩
    have hsum' : pyrS m n + (m + 1) * c = m + n := by
      rw [hc, Nat.add_sub_cancel] at hsum
      exact hsum
    have hst : pyrS m n + (m + 1 - pyrS m n) = m + 1 := by omega
    rw [pyramidLens, hc, List.sum_append, List.sum_replicate, List.sum_replicate,
      smul_eq_mul, smul_eq_mul]
    simp only [Nat.add_sub_cancel]
    calc pyrS m n * (c + 1) + (m + 1 - pyrS m n) * c
        = pyrS m n + (pyrS m n + (m + 1 - pyrS m n)) * c := by ring
      _ = pyrS m n + (m + 1) * c := by rw [hst]
      _ = m + n := hsum'

theorem length_pyramidRow (m n : ℕ) :
    (pyramidRow m n).length = 2 * (m + n) := by
  rw [pyramidRow, length_flatMap_pyramid, sum_pyramidLens]

theorem pyramidRow_mem_dyckPath (m n : ℕ) :
    pyramidRow m n ∈ DyckPath (m + n) :=
  ⟨isDyckPath_pyramidRow m n, length_pyramidRow m n⟩

/-! ## S9 — the first ascent -/

theorem firstAscent_flatMap_pyramid_cons (l : ℕ) (hl : 1 ≤ l) (rest : List ℕ) :
    firstAscent ((l :: rest).flatMap pyramid) = l := by
  rw [List.flatMap_cons, firstAscent, pyramid, List.append_assoc,
    takeWhile_replicate_U_append,
    show List.replicate l D ++ rest.flatMap pyramid
      = D :: (List.replicate (l - 1) D ++ rest.flatMap pyramid) from by
        rw [show l = (l - 1) + 1 from by omega, List.replicate_succ]
        simp,
    List.takeWhile_cons_of_neg (by decide)]
  simp

/-- **The first ascent of the pyramid row is the ceiling** — unconditionally. -/
theorem firstAscent_pyramidRow (m n : ℕ) :
    firstAscent (pyramidRow m n) = (m + n + m) / (m + 1) := by
  rcases Nat.eq_zero_or_pos (m + n) with h0 | hN
  · have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    subst hm hn
    decide
  · obtain ⟨hb1, hs1, hsle, hsum⟩ := pyrArith m n hN
    rw [pyramidRow, pyramidLens,
      show List.replicate (pyrS m n) (pyrB m n)
        = pyrB m n :: List.replicate (pyrS m n - 1) (pyrB m n) from by
          conv_lhs => rw [show pyrS m n = (pyrS m n - 1) + 1 from by omega]
          rw [List.replicate_succ],
      List.cons_append, firstAscent_flatMap_pyramid_cons _ hb1]
    rfl

/-- The `Nat.ceilDiv` rendering of the same statement. -/
theorem firstAscent_pyramidRow_ceilDiv (m n : ℕ) :
    firstAscent (pyramidRow m n) = (m + n) ⌈/⌉ (m + 1) := by
  rw [Nat.ceilDiv_eq_add_pred_div, firstAscent_pyramidRow]
  congr 1

/-! ## S10 — the packaging corollary -/

/-- **`lem:inverse-zeta-fas` (paper.tex)** in its
honest bijectivity-free form: rather than `fas(ζ⁻¹(W_{m,n}))` (which
presupposes that `ζ` is a bijection), an explicit ζ-preimage of the copied
slice with first ascent `⌈(m+n)/(m+1)⌉`.  The hypothesis `m ≥ 1` mirrors the
paper; the component theorems hold for all `m`. -/
theorem inverse_zeta_fas (m n : ℕ) (_hm : 1 ≤ m) :
    ∃ Q ∈ DyckPath (m + n),
      zetaMap Q = copiedSlice m n ∧ firstAscent Q = (m + n + m) / (m + 1) :=
  ⟨pyramidRow m n, pyramidRow_mem_dyckPath m n, zetaMap_pyramidRow m n,
    firstAscent_pyramidRow m n⟩

/-! ## `lem:inverse-zeta-not-semilinear`: the first-ascent graph
is not semilinear

The paper's set `G ⊆ ℕ³` reduces, by intersection with `{f = m}` and
projection (the Ginsburg–Spanier closure side, deliberately not formalised),
to the band `H = {(n, m) : m ≥ 1, m² − m ≤ n ≤ m²}` — which the paper then
kills via the envelope lemma.  We formalise the band step genuinely: the band
IS the ceiling graph (`ceil_eq_self_iff_band`), and it is not semilinear
(`invBand_not_semilinear`), by `semilinear_envelope` against the quadratic
lower envelope `m² − m`. -/

/-- The band `{(n, m) : m ≥ 1 ∧ m² − m ≤ n ≤ m²}` — the diagonal section of
the first-ascent graph, in the `(a, b) = (n, m)` orientation of
`semilinear_envelope`. -/
def invBand : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | 1 ≤ p.2 ∧ p.2 * p.2 - p.2 ≤ p.1 ∧ p.1 ≤ p.2 * p.2}

/-- **The band is the ceiling graph**: for `m ≥ 1`,
`⌈(m+n)/(m+1)⌉ = m ↔ m² − m ≤ n ≤ m²`. -/
theorem ceil_eq_self_iff_band (m n : ℕ) (hm : 1 ≤ m) :
    (m + n + m) / (m + 1) = m ↔ (m * m - m ≤ n ∧ n ≤ m * m) := by
  constructor
  · intro h
    have hd := Nat.div_add_mod (m + n + m) (m + 1)
    have hmod : (m + n + m) % (m + 1) < m + 1 := Nat.mod_lt _ (by omega)
    rw [h] at hd
    have hexp : (m + 1) * m = m * m + m := by ring
    generalize hX : m * m = X at *
    omega
  · rintro ⟨h1, h2⟩
    have hexp1 : m * (m + 1) = m * m + m := by ring
    have hexp2 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
    apply Nat.div_eq_of_lt_le
    · rw [hexp1]
      generalize hX : m * m = X at *
      omega
    · rw [show (m + 1) * (m + 1) = (m + 1) * (m + 1) from rfl, hexp2]
      generalize hX : m * m = X at *
      omega

theorem invBand_lower_bound {a b : ℕ} (h : (a, b) ∈ invBand) :
    b * b - b ≤ a := h.2.1

theorem invBand_section_finite (b : ℕ) :
    Set.Finite {a | (a, b) ∈ invBand} := by
  refine (Set.finite_Icc 0 (b * b)).subset ?_
  intro a ha
  exact ⟨Nat.zero_le _, ha.2.2⟩

theorem invBand_section_nonempty (b : ℕ) (hb : b ≥ 1) :
    {a | (a, b) ∈ invBand}.Nonempty := by
  refine ⟨b * b - b, hb, le_refl _, ?_⟩
  generalize hX : b * b = X
  omega

/-- The band's quadratic lower envelope dominates the `S_tri` quadratic for
`b ≥ 2`, so the existing kernel applies. -/
theorem quad_le_band_lower (b : ℕ) (hb : 2 ≤ b) :
    b * (b - 1) / 2 + 1 ≤ b * b - b := by
  have h1 : b * (b - 1) = b * b - b := by
    rw [Nat.mul_sub_one]
  have h2 : 2 ≤ b * (b - 1) := by
    calc 2 = 2 * 1 := by norm_num
      _ ≤ b * (b - 1) := Nat.mul_le_mul hb (by omega)
  rw [← h1]
  generalize hY : b * (b - 1) = Y at *
  omega

/-- **`lem:inverse-zeta-not-semilinear`, the heart**: the band is not semilinear. -/
theorem invBand_not_semilinear : ¬ IsSemilinear2 invBand := by
  intro hband
  rcases semilinear_envelope invBand hband invBand_section_finite with
    ⟨M, hM, henv⟩
  rcases henv 0 (by omega) with ⟨p, q, gamma, hq, hevent⟩
  rw [Filter.eventually_atTop] at hevent
  rcases hevent with ⟨N, hN⟩
  rcases exists_multiple_quadratic_gt_affine M hM p gamma (Nat.max N 2) with
    ⟨b, hbNmax, hbmod, hbquad⟩
  have hbN : N ≤ b := le_trans (Nat.le_max_left N 2) hbNmax
  have hb2 : b ≥ 2 := le_trans (Nat.le_max_right N 2) hbNmax
  have hnonempty : {a | (a, b) ∈ invBand}.Nonempty :=
    invBand_section_nonempty b (by omega)
  rcases hN b hbN hbmod hnonempty with ⟨a, ha_mem, ha_affine⟩
  have hlower_nat : b * b - b ≤ a := invBand_lower_bound ha_mem
  have hchain : ((b * (b - 1) / 2 + 1 : ℕ) : ℤ) ≤ (a : ℤ) := by
    exact_mod_cast le_trans (quad_le_band_lower b hb2) hlower_nat
  -- q·a = p·b + γ < quad ≤ a ≤ q·a : contradiction
  have ha_le : (a : ℤ) ≤ q * (a : ℤ) :=
    le_mul_of_one_le_left (by exact_mod_cast Nat.zero_le a) (by omega)
  linarith [ha_affine, hbquad, hchain, ha_le]

/-- **`lem:inverse-zeta-not-semilinear`, ceiling form**: the
diagonal section of the first-ascent graph — the set of `(n, m)` with `m ≥ 1`
and `⌈(m+n)/(m+1)⌉ = m` — is not semilinear.  (The paper's `ℕ³`-packaging
`G` reduces to this by intersection and projection, the Presburger-closure
side deliberately not formalised.) -/
theorem inverse_zeta_graph_band_not_semilinear :
    ¬ IsSemilinear2 {p : ℕ × ℕ | 1 ≤ p.2 ∧ (p.2 + p.1 + p.2) / (p.2 + 1) = p.2} := by
  have hset : {p : ℕ × ℕ | 1 ≤ p.2 ∧ (p.2 + p.1 + p.2) / (p.2 + 1) = p.2}
      = invBand := by
    ext ⟨n, m⟩
    simp only [Set.mem_ofPred_eq, invBand]
    constructor
    · rintro ⟨hm, h⟩
      exact ⟨hm, (ceil_eq_self_iff_band m n hm).mp h⟩
    · rintro ⟨hm, h1, h2⟩
      exact ⟨hm, (ceil_eq_self_iff_band m n hm).mpr ⟨h1, h2⟩⟩
  rw [hset]
  exact invBand_not_semilinear
