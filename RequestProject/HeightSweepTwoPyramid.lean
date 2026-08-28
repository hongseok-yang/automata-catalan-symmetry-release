/-
# The height sweep on two-pyramid paths

`lem:H-two-pyramid` (paper.tex): the closed form of the height sweep on the
two-pyramid paths `P_{m,n} = U^m D^m U^n D^n`,

* `H(P_{m,n}) = UU (DU)^{2(n-1)} DD (UD)^{m-n}`   if `n ≤ m`,
* `H(P_{m,n}) = UU (DU)^{2m-1}   DD (UD)^{n-m-1}` if `n > m`.

The proof evaluates the sort in `heightSweep` explicitly.  The triples
`(starting height, position, step)` of `P_{m,n}` are listed level by level:
level `0` holds the two `U`-steps opening the pyramids (positions `2m` and
`0`), and each level `h ≥ 1` holds, in decreasing position order, the second
pyramid's `D` at `2m + 2n - h` (for `h ≤ n`), the second pyramid's `U` at
`2m + h` (for `h < n`), the first pyramid's `D` at `2m - h` (for `h ≤ m`),
and the first pyramid's `U` at `h` (for `h < m`).  This level list is sorted
for the sweep comparator and is a permutation of the sweep triples, so it is
the sort; reading off the step labels and regrouping gives the closed form.
-/
import RequestProject.NarayanaSweep
import RequestProject.ZetaClassification

open Step

/-! ### The letters and the height profile of `P_{m,n}` -/

private theorem length_twoPyramid (m n : ℕ) : (twoPyramid m n).length = 2 * m + 2 * n := by
  unfold twoPyramid
  rw [List.length_append, List.length_append, List.length_append, List.length_replicate,
    List.length_replicate, List.length_replicate, List.length_replicate]
  omega

/-- The height profile of `P_{m,n}`: up to `m`, down to `0`, up to `n`, down to `0`. -/
private theorem height_twoPyramid (m n k : ℕ) (hk : k ≤ 2 * m + 2 * n) :
    height (twoPyramid m n) k =
      if k < m then (k : ℤ)
      else if k < 2 * m then 2 * (m : ℤ) - k
      else if k < 2 * m + n then (k : ℤ) - 2 * m
      else 2 * (m : ℤ) + 2 * n - k := by
  rw [height_eq_count]
  simp [twoPyramid, List.take_append, List.take_replicate, List.count_append,
    List.count_replicate]
  split_ifs <;> omega

/-- The letters of `P_{m,n}`. -/
private theorem getElem_twoPyramid (m n i : ℕ) (hi : i < (twoPyramid m n).length) :
    (twoPyramid m n)[i] =
      if i < m then U else if i < 2 * m then D else if i < 2 * m + n then U else D := by
  simp only [twoPyramid, List.length_append, List.length_replicate] at hi
  simp only [twoPyramid, List.append_assoc, List.getElem_append, List.length_replicate,
    List.getElem_replicate]
  split_ifs <;> first | rfl | omega

/-! ### The sweep triples of `P_{m,n}` -/

/-- The sweep triples of a path, characterised by position. -/
private theorem mem_sweepIdx_iff {P : List Step} {x : ℤ × ℕ × Step} :
    x ∈ sweepIdx P ↔ ∃ i : ℕ, ∃ hi : i < P.length, x = (height P i, i, P[i]) := by
  unfold sweepIdx
  constructor
  · intro hx
    obtain ⟨⟨s, i⟩, hmem, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hi, hs⟩ := List.mem_zipIdx' hmem
    exact ⟨i, hi, by rw [hs]⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_map.mpr ⟨(P[i], i),
      by rw [List.mem_zipIdx_iff_getElem?]; simp [List.getElem?_eq_getElem hi], rfl⟩

/-- The sweep triples of `P_{m,n}`: the four ascending/descending runs. -/
private theorem mem_sweepIdx_twoPyramid (m n : ℕ) (x : ℤ × ℕ × Step) :
    x ∈ sweepIdx (twoPyramid m n) ↔
      (∃ i, i < m ∧ x = ((i : ℤ), i, U)) ∨
      (∃ h, 1 ≤ h ∧ h ≤ m ∧ x = ((h : ℤ), 2 * m - h, D)) ∨
      (∃ k, k < n ∧ x = ((k : ℤ), 2 * m + k, U)) ∨
      (∃ h, 1 ≤ h ∧ h ≤ n ∧ x = ((h : ℤ), 2 * m + 2 * n - h, D)) := by
  rw [mem_sweepIdx_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < 2 * m + 2 * n := by rw [length_twoPyramid] at hi; exact hi
    rw [getElem_twoPyramid m n i hi, height_twoPyramid m n i (by omega)]
    split_ifs with h1 h2 h3
    · exact Or.inl ⟨i, h1, rfl⟩
    · refine Or.inr (Or.inl ⟨2 * m - i, by omega, by omega, ?_⟩)
      simp only [Prod.mk.injEq, and_true]
      omega
    · refine Or.inr (Or.inr (Or.inl ⟨i - 2 * m, by omega, ?_⟩))
      simp only [Prod.mk.injEq, and_true]
      omega
    · refine Or.inr (Or.inr (Or.inr ⟨2 * m + 2 * n - i, by omega, by omega, ?_⟩))
      simp only [Prod.mk.injEq, and_true]
      omega
  · have hlen : ∀ i, i < 2 * m + 2 * n → i < (twoPyramid m n).length := by
      intro i hi; rw [length_twoPyramid]; exact hi
    rintro (⟨i, hi, rfl⟩ | ⟨h, hh1, hh2, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨h, hh1, hh2, rfl⟩)
    · refine ⟨i, hlen i (by omega), ?_⟩
      rw [getElem_twoPyramid m n i (hlen i (by omega)),
        height_twoPyramid m n i (by omega), if_pos hi, if_pos hi]
    · refine ⟨2 * m - h, hlen _ (by omega), ?_⟩
      rw [getElem_twoPyramid m n _ (hlen _ (by omega)), height_twoPyramid m n _ (by omega),
        if_neg (by omega : ¬ 2 * m - h < m), if_pos (by omega : 2 * m - h < 2 * m),
        if_neg (by omega : ¬ 2 * m - h < m), if_pos (by omega : 2 * m - h < 2 * m)]
      simp only [Prod.mk.injEq, and_true]
      omega
    · refine ⟨2 * m + k, hlen _ (by omega), ?_⟩
      rw [getElem_twoPyramid m n _ (hlen _ (by omega)), height_twoPyramid m n _ (by omega),
        if_neg (by omega : ¬ 2 * m + k < m), if_neg (by omega : ¬ 2 * m + k < 2 * m),
        if_pos (by omega : 2 * m + k < 2 * m + n),
        if_neg (by omega : ¬ 2 * m + k < m), if_neg (by omega : ¬ 2 * m + k < 2 * m),
        if_pos (by omega : 2 * m + k < 2 * m + n)]
      simp only [Prod.mk.injEq, and_true]
      omega
    · refine ⟨2 * m + 2 * n - h, hlen _ (by omega), ?_⟩
      rw [getElem_twoPyramid m n _ (hlen _ (by omega)), height_twoPyramid m n _ (by omega),
        if_neg (by omega : ¬ 2 * m + 2 * n - h < m),
        if_neg (by omega : ¬ 2 * m + 2 * n - h < 2 * m),
        if_neg (by omega : ¬ 2 * m + 2 * n - h < 2 * m + n),
        if_neg (by omega : ¬ 2 * m + 2 * n - h < m),
        if_neg (by omega : ¬ 2 * m + 2 * n - h < 2 * m),
        if_neg (by omega : ¬ 2 * m + 2 * n - h < 2 * m + n)]
      simp only [Prod.mk.injEq, and_true]
      omega

/-! ### The sorted list of sweep triples, level by level -/

/-- The sweep triples of `P_{m,n}` at level `h ≥ 1`, in decreasing position order. -/
private def levelBlock (m n h : ℕ) : List (ℤ × ℕ × Step) :=
  (if h ≤ n then [((h : ℤ), 2 * m + 2 * n - h, D)] else []) ++
  (if h + 1 ≤ n then [((h : ℤ), 2 * m + h, U)] else []) ++
  (if h ≤ m then [((h : ℤ), 2 * m - h, D)] else []) ++
  (if h + 1 ≤ m then [((h : ℤ), h, U)] else [])

/-- The sorted sweep triples of `P_{m,n}`: level `0`, then levels `1, …, max m n`. -/
private def sortedSweep (m n : ℕ) : List (ℤ × ℕ × Step) :=
  [((0 : ℤ), 2 * m, U), ((0 : ℤ), 0, U)] ++
    (List.range' 1 (max m n)).flatMap (levelBlock m n)

private theorem mem_levelBlock_iff (m n h : ℕ) (x : ℤ × ℕ × Step) :
    x ∈ levelBlock m n h ↔
      (h ≤ n ∧ x = ((h : ℤ), 2 * m + 2 * n - h, D)) ∨
      (h + 1 ≤ n ∧ x = ((h : ℤ), 2 * m + h, U)) ∨
      (h ≤ m ∧ x = ((h : ℤ), 2 * m - h, D)) ∨
      (h + 1 ≤ m ∧ x = ((h : ℤ), h, U)) := by
  unfold levelBlock
  simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc]

/-- `sortedSweep` and `sweepIdx` have the same members. -/
private theorem mem_sortedSweep_iff (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (x : ℤ × ℕ × Step) : x ∈ sortedSweep m n ↔ x ∈ sweepIdx (twoPyramid m n) := by
  rw [mem_sweepIdx_twoPyramid]
  unfold sortedSweep
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_range'_1, mem_levelBlock_iff]
  constructor
  · rintro ((rfl | rfl) | ⟨h, ⟨hh1, _⟩, hblk⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨0, hn, by simp⟩))
    · exact Or.inl ⟨0, hm, by simp⟩
    · rcases hblk with ⟨hg, rfl⟩ | ⟨hg, rfl⟩ | ⟨hg, rfl⟩ | ⟨hg, rfl⟩
      · exact Or.inr (Or.inr (Or.inr ⟨h, hh1, hg, rfl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h, by omega, rfl⟩))
      · exact Or.inr (Or.inl ⟨h, hh1, hg, rfl⟩)
      · exact Or.inl ⟨h, by omega, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨h, hh1, hh2, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨h, hh1, hh2, rfl⟩)
    · rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact Or.inl (Or.inr (by simp))
      · exact Or.inr ⟨i, ⟨hpos, by omega⟩, Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))⟩
    · exact Or.inr ⟨h, ⟨hh1, by omega⟩, Or.inr (Or.inr (Or.inl ⟨hh2, rfl⟩))⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exact Or.inl (Or.inl (by simp))
      · exact Or.inr ⟨k, ⟨hpos, by omega⟩, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩
    · exact Or.inr ⟨h, ⟨hh1, by omega⟩, Or.inl ⟨hh2, rfl⟩⟩

/-! ### `sortedSweep` is sorted for the sweep comparator -/

private theorem cmpHS_of_height_lt {a b : ℤ × ℕ × Step} (h : a.1 < b.1) :
    cmpHS a b = true := by
  unfold cmpHS
  rw [if_pos h]

private theorem cmpHS_of_height_eq {a b : ℤ × ℕ × Step} (h1 : a.1 = b.1)
    (h2 : b.2.1 < a.2.1) : cmpHS a b = true := by
  unfold cmpHS
  rw [if_neg (by omega), if_neg (by omega)]
  exact decide_eq_true h2

private theorem height_of_mem_levelBlock {m n h : ℕ} {x : ℤ × ℕ × Step}
    (hx : x ∈ levelBlock m n h) : x.1 = (h : ℤ) := by
  rw [mem_levelBlock_iff] at hx
  rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- Within a level, the positions strictly decrease, so the block is sorted. -/
private theorem pairwise_levelBlock (m n h : ℕ) (hh : 0 < h) :
    (levelBlock m n h).Pairwise (fun a b => cmpHS a b = true) := by
  unfold levelBlock cmpHS
  split_ifs <;>
    simp_all [List.pairwise_cons] <;>
    omega

/-- The heights strictly increase from level to level, so `sortedSweep` is sorted. -/
private theorem pairwise_sortedSweep (m n : ℕ) (hm : 0 < m) :
    (sortedSweep m n).Pairwise (fun a b => cmpHS a b = true) := by
  unfold sortedSweep
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · refine List.pairwise_cons.mpr ⟨fun b hb => ?_, List.pairwise_singleton _ _⟩
    rw [List.mem_singleton] at hb
    subst hb
    exact cmpHS_of_height_eq rfl (by show (0 : ℕ) < 2 * m; omega)
  · rw [List.flatMap_def, List.pairwise_flatten]
    refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hl
      rw [List.mem_range'_1] at hh
      exact pairwise_levelBlock m n h (by omega)
    · rw [List.pairwise_map]
      refine List.Pairwise.imp ?_ (List.pairwise_lt_range' 1 one_pos)
      intro h h' hlt x hx y hy
      refine cmpHS_of_height_lt ?_
      rw [height_of_mem_levelBlock hx, height_of_mem_levelBlock hy]
      omega
  · intro a ha b hb
    rw [List.mem_flatMap] at hb
    obtain ⟨h, hh, hbh⟩ := hb
    rw [List.mem_range'_1] at hh
    refine cmpHS_of_height_lt ?_
    rw [height_of_mem_levelBlock hbh]
    have ha1 : a.1 = 0 := by
      rcases List.mem_cons.mp ha with rfl | ha'
      · rfl
      · rw [List.mem_singleton] at ha'
        subst ha'
        rfl
    rw [ha1]
    omega

private theorem ne_of_cmpHS {a b : ℤ × ℕ × Step} (h : cmpHS a b = true) : a ≠ b := by
  rintro rfl
  unfold cmpHS at h
  simp at h

private theorem cmpHS'_of_cmpHS {a b : ℤ × ℕ × Step} (h : cmpHS a b = true) :
    cmpHS' a b = true := by
  unfold cmpHS at h
  unfold cmpHS'
  rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
  · rw [if_pos hlt]
  · rw [if_neg (by omega : ¬ a.1 < b.1), if_neg (by omega : ¬ a.1 > b.1)] at h ⊢
    simp only [decide_eq_true_eq] at h ⊢
    omega
  · rw [if_neg (by omega : ¬ a.1 < b.1), if_pos (by omega : a.1 > b.1)] at h
    exact absurd h Bool.false_ne_true

/-- Mutually `cmpHS'`-comparable triples share their position. -/
private theorem pos_eq_of_cmpHS' {a b : ℤ × ℕ × Step}
    (h1 : cmpHS' a b = true) (h2 : cmpHS' b a = true) : a.2.1 = b.2.1 := by
  unfold cmpHS' at h1 h2
  rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
  · rw [if_neg (by omega : ¬ b.1 < a.1), if_pos (by omega : b.1 > a.1)] at h2
    exact absurd h2 Bool.false_ne_true
  · rw [if_neg (by omega : ¬ a.1 < b.1), if_neg (by omega : ¬ a.1 > b.1)] at h1
    rw [if_neg (by omega : ¬ b.1 < a.1), if_neg (by omega : ¬ b.1 > a.1)] at h2
    simp only [decide_eq_true_eq] at h1 h2
    omega
  · rw [if_neg (by omega : ¬ a.1 < b.1), if_pos (by omega : a.1 > b.1)] at h1
    exact absurd h1 Bool.false_ne_true

/-! ### `sortedSweep` is the sort of the sweep triples -/

private theorem perm_sortedSweep (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (sortedSweep m n).Perm (sweepIdx (twoPyramid m n)) := by
  refine List.perm_of_nodup_nodup_toFinset_eq
    ((pairwise_sortedSweep m n hm).imp ne_of_cmpHS) (nodup_sweepIdx _)
    (Finset.ext fun x => ?_)
  rw [List.mem_toFinset, List.mem_toFinset]
  exact mem_sortedSweep_iff m n hm hn x

/-- Two sorted permutations of each other agree, given antisymmetry on members. -/
private theorem eq_of_perm_of_pairwise {α : Type*} {le : α → α → Bool} :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ →
      (∀ a ∈ l₁, ∀ b ∈ l₁, le a b = true → le b a = true → a = b) →
      l₁.Pairwise (fun a b => le a b = true) →
      l₂.Pairwise (fun a b => le a b = true) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ hp _ _ _
      exact hp.nil_eq
  | cons a t₁ ih =>
      intro l₂ hp hanti h₁ h₂
      cases l₂ with
      | nil => exact absurd (List.perm_nil.mp hp) (List.cons_ne_nil a t₁)
      | cons b t₂ =>
          obtain rfl : a = b := by
            by_contra hne
            have ha₂ : a ∈ t₂ := by
              rcases List.mem_cons.mp (hp.subset List.mem_cons_self) with h | h
              · exact absurd h hne
              · exact h
            have hb₁ : b ∈ t₁ := by
              rcases List.mem_cons.mp (hp.symm.subset List.mem_cons_self) with h | h
              · exact absurd h.symm hne
              · exact h
            exact hne (hanti a List.mem_cons_self b (List.mem_cons_of_mem a hb₁)
              ((List.pairwise_cons.mp h₁).1 b hb₁) ((List.pairwise_cons.mp h₂).1 a ha₂))
          rw [ih hp.cons_inv
            (fun x hx y hy => hanti x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))
            (List.pairwise_cons.mp h₁).2 (List.pairwise_cons.mp h₂).2]

/-- The sort in `heightSweep (twoPyramid m n)` evaluates to `sortedSweep m n`. -/
private theorem mergeSort_sweepIdx_twoPyramid (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (sweepIdx (twoPyramid m n)).mergeSort cmpHS' = sortedSweep m n := by
  refine eq_of_perm_of_pairwise
    ((List.mergeSort_perm _ _).trans (perm_sortedSweep m n hm hn).symm)
    (fun a ha b hb h1 h2 => ?_)
    (List.pairwise_mergeSort cmpHS'_trans cmpHS'_total _)
    ((pairwise_sortedSweep m n hm).imp cmpHS'_of_cmpHS)
  exact sweepIdx_eq_of_pos_eq (twoPyramid m n)
    ((List.mergeSort_perm _ _).subset ha) ((List.mergeSort_perm _ _).subset hb)
    (pos_eq_of_cmpHS' h1 h2)

/-! ### Reading off the step labels -/

/-- The step labels of a level block. -/
private def levelWord (m n h : ℕ) : List Step :=
  (if h ≤ n then [D] else []) ++ (if h + 1 ≤ n then [U] else []) ++
  (if h ≤ m then [D] else []) ++ (if h + 1 ≤ m then [U] else [])

private theorem map_levelBlock (m n h : ℕ) :
    (levelBlock m n h).map (·.2.2) = levelWord m n h := by
  unfold levelBlock levelWord
  split_ifs <;> rfl

private theorem map_sortedSweep (m n : ℕ) :
    (sortedSweep m n).map (·.2.2) =
      [U, U] ++ (List.range' 1 (max m n)).flatMap (levelWord m n) := by
  unfold sortedSweep
  rw [List.map_append, List.map_flatMap]
  simp only [map_levelBlock]
  rfl

private theorem range'_split (s a b L : ℕ) (h : a + b = L) :
    List.range' s L = List.range' s a ++ List.range' (s + a) b := by
  rw [List.range'_append_1, h]

/-- Assembling the level words for `n ≤ m`. -/
private theorem flatMap_levelWord_le (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnm : n ≤ m) :
    (List.range' 1 m).flatMap (levelWord m n) =
      (List.replicate (2 * (n - 1)) [D, U]).flatten ++ [D, D]
        ++ (List.replicate (m - n) [U, D]).flatten := by
  rcases Nat.lt_or_ge n m with hlt | hge
  · -- levels `[1, n) ⧺ {n} ⧺ (n, m) ⧺ {m}`
    rw [range'_split 1 (n - 1) (m - n + 1) m (by omega), List.flatMap_append,
      show (1 : ℕ) + (n - 1) = n from by omega,
      range'_split n 1 (m - n) (m - n + 1) (by omega), List.flatMap_append,
      range'_split (n + 1) (m - n - 1) 1 (m - n) (by omega), List.flatMap_append,
      show (n + 1) + (m - n - 1) = m from by omega,
      flatMap_range'_const (levelWord m n) ([D, U] ++ [D, U]) 1 (n - 1)
        (fun r hr hr' => by
          unfold levelWord
          rw [if_pos (by omega : r ≤ n), if_pos (by omega : r + 1 ≤ n),
            if_pos (by omega : r ≤ m), if_pos (by omega : r + 1 ≤ m)]
          rfl),
      flatten_replicate_DUDU,
      List.range'_one, List.flatMap_singleton,
      show levelWord m n n = [D, D, U] from by
        unfold levelWord
        rw [if_pos (le_refl n), if_neg (by omega : ¬ n + 1 ≤ n), if_pos hnm,
          if_pos (by omega : n + 1 ≤ m)]
        rfl,
      flatMap_range'_const (levelWord m n) [D, U] (n + 1) (m - n - 1)
        (fun r hr hr' => by
          unfold levelWord
          rw [if_neg (by omega : ¬ r ≤ n), if_neg (by omega : ¬ r + 1 ≤ n),
            if_pos (by omega : r ≤ m), if_pos (by omega : r + 1 ≤ m)]
          rfl),
      List.range'_one, List.flatMap_singleton,
      show levelWord m n m = [D] from by
        unfold levelWord
        rw [if_neg (by omega : ¬ m ≤ n), if_neg (by omega : ¬ m + 1 ≤ n),
          if_pos (le_refl m), if_neg (by omega : ¬ m + 1 ≤ m)]
        rfl]
    -- regroup `DDU ⧺ (DU)^{m-n-1} ⧺ D` into `DD ⧺ (UD)^{m-n}`
    have hkey : [D, D, U] ++ ((List.replicate (m - n - 1) [D, U]).flatten ++ [D])
        = [D, D] ++ (List.replicate (m - n) [U, D]).flatten := by
      have hcount : m - n - 1 + 1 = m - n := by omega
      calc [D, D, U] ++ ((List.replicate (m - n - 1) [D, U]).flatten ++ [D])
          = [D, D] ++ ([U] ++ (List.replicate (m - n - 1) [D, U]).flatten ++ [D]) := by
            simp
        _ = [D, D] ++ (List.replicate (m - n - 1 + 1) [U, D]).flatten := by
            rw [U_flatten_DU_D]
        _ = [D, D] ++ (List.replicate (m - n) [U, D]).flatten := by rw [hcount]
    rw [hkey, ← List.append_assoc]
  · -- `n = m`: levels `[1, n) ⧺ {n}`
    rw [show m - n = 0 from by omega, List.replicate_zero, List.flatten_nil,
      List.append_nil,
      range'_split 1 (n - 1) 1 m (by omega), List.flatMap_append,
      show (1 : ℕ) + (n - 1) = n from by omega,
      flatMap_range'_const (levelWord m n) ([D, U] ++ [D, U]) 1 (n - 1)
        (fun r hr hr' => by
          unfold levelWord
          rw [if_pos (by omega : r ≤ n), if_pos (by omega : r + 1 ≤ n),
            if_pos (by omega : r ≤ m), if_pos (by omega : r + 1 ≤ m)]
          rfl),
      flatten_replicate_DUDU,
      List.range'_one, List.flatMap_singleton,
      show levelWord m n n = [D, D] from by
        unfold levelWord
        rw [if_pos (le_refl n), if_neg (by omega : ¬ n + 1 ≤ n), if_pos hnm,
          if_neg (by omega : ¬ n + 1 ≤ m)]
        rfl]

/-- Assembling the level words for `m < n`. -/
private theorem flatMap_levelWord_gt (m n : ℕ) (hm : 0 < m) (hmn : m < n) :
    (List.range' 1 n).flatMap (levelWord m n) =
      (List.replicate (2 * m - 1) [D, U]).flatten ++ [D, D]
        ++ (List.replicate (n - m - 1) [U, D]).flatten := by
  -- levels `[1, m) ⧺ {m} ⧺ (m, n) ⧺ {n}`
  rw [range'_split 1 (m - 1) (n - m + 1) n (by omega), List.flatMap_append,
    show (1 : ℕ) + (m - 1) = m from by omega,
    range'_split m 1 (n - m) (n - m + 1) (by omega), List.flatMap_append,
    range'_split (m + 1) (n - m - 1) 1 (n - m) (by omega), List.flatMap_append,
    show (m + 1) + (n - m - 1) = n from by omega,
    flatMap_range'_const (levelWord m n) ([D, U] ++ [D, U]) 1 (m - 1)
      (fun r hr hr' => by
        unfold levelWord
        rw [if_pos (by omega : r ≤ n), if_pos (by omega : r + 1 ≤ n),
          if_pos (by omega : r ≤ m), if_pos (by omega : r + 1 ≤ m)]
        rfl),
    flatten_replicate_DUDU,
    List.range'_one, List.flatMap_singleton,
    show levelWord m n m = [D, U, D] from by
      unfold levelWord
      rw [if_pos (by omega : m ≤ n), if_pos (by omega : m + 1 ≤ n),
        if_pos (le_refl m), if_neg (by omega : ¬ m + 1 ≤ m)]
      rfl,
    flatMap_range'_const (levelWord m n) [D, U] (m + 1) (n - m - 1)
      (fun r hr hr' => by
        unfold levelWord
        rw [if_pos (by omega : r ≤ n), if_pos (by omega : r + 1 ≤ n),
          if_neg (by omega : ¬ r ≤ m), if_neg (by omega : ¬ r + 1 ≤ m)]
        rfl),
    List.range'_one, List.flatMap_singleton,
    show levelWord m n n = [D] from by
      unfold levelWord
      rw [if_pos (le_refl n), if_neg (by omega : ¬ n + 1 ≤ n),
        if_neg (by omega : ¬ n ≤ m), if_neg (by omega : ¬ n + 1 ≤ m)]
      rfl]
  -- regroup `(DU)^{2(m-1)} ⧺ DUD ⧺ (DU)^{n-m-1} ⧺ D` into `(DU)^{2m-1} ⧺ DD ⧺ (UD)^{n-m-1}`
  have hA : (List.replicate (2 * (m - 1)) [D, U]).flatten ++ [D, U]
      = (List.replicate (2 * m - 1) [D, U]).flatten := by
    rw [show 2 * m - 1 = 2 * (m - 1) + 1 from by omega, List.replicate_succ',
      List.flatten_concat]
  have hkey : [D, U, D] ++ ((List.replicate (n - m - 1) [D, U]).flatten ++ [D])
      = [D, U] ++ ([D, D] ++ (List.replicate (n - m - 1) [U, D]).flatten) := by
    rw [← D_flatten_DU_D]
    simp
  rw [hkey, ← List.append_assoc, hA, ← List.append_assoc]

/-- **`lem:H-two-pyramid` (paper.tex).**  The closed form of the height sweep
on two-pyramid paths. -/
theorem heightSweep_twoPyramid (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    heightSweep (twoPyramid m n) =
      if n ≤ m then
        [U, U] ++ (List.replicate (2 * (n - 1)) [D, U]).flatten
          ++ [D, D] ++ (List.replicate (m - n) [U, D]).flatten
      else
        [U, U] ++ (List.replicate (2 * m - 1) [D, U]).flatten
          ++ [D, D] ++ (List.replicate (n - m - 1) [U, D]).flatten := by
  rw [heightSweep_eq', mergeSort_sweepIdx_twoPyramid m n hm hn, map_sortedSweep]
  by_cases hnm : n ≤ m
  · rw [if_pos hnm, show max m n = m from by omega, flatMap_levelWord_le m n hm hn hnm]
    simp only [List.append_assoc]
  · rw [if_neg hnm, show max m n = n from by omega,
      flatMap_levelWord_gt m n hm (by omega)]
    simp only [List.append_assoc]

/-- Sanity checks of the closed form against small explicit values. -/
example : heightSweep (twoPyramid 1 1) = [U, U, D, D] := by
  rw [heightSweep_twoPyramid 1 1 (by norm_num) (by norm_num)]; decide
example : heightSweep (twoPyramid 1 2) = [U, U, D, U, D, D] := by
  rw [heightSweep_twoPyramid 1 2 (by norm_num) (by norm_num)]; decide
example : heightSweep (twoPyramid 2 1) = [U, U, D, D, U, D] := by
  rw [heightSweep_twoPyramid 2 1 (by norm_num) (by norm_num)]; decide
example : heightSweep (twoPyramid 2 2) = [U, U, D, U, D, U, D, D] := by
  rw [heightSweep_twoPyramid 2 2 (by norm_num) (by norm_num)]; decide
example : heightSweep (twoPyramid 3 2) = [U, U, D, U, D, U, D, D, U, D] := by
  rw [heightSweep_twoPyramid 3 2 (by norm_num) (by norm_num)]; decide
