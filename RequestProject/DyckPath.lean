/-
# Dyck Paths, Statistics, and Named Bijections

Formalization of Section 2 of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.
-/
import Mathlib

/-! ## Step alphabet -/

/-- **`rmk:step-word` (paper.tex).**
The two-letter step alphabet `{U, D}` for encoding Dyck paths. -/
inductive Step : Type where
  | U : Step
  | D : Step
  deriving DecidableEq, Repr, Inhabited, BEq

open Step

instance : Fintype Step where
  elems := {U, D}
  complete := by intro x; cases x <;> simp

instance : LawfulBEq Step where
  eq_of_beq := by intro a b; cases a <;> cases b <;> simp [BEq.beq] <;> decide
  rfl := by intro a; cases a <;> rfl

/-! ## Height function -/

/-- **`rmk:step-word` (paper.tex).**
The height `h_w(k)` after the first `k` letters of a step word `w`,
defined as `#{1 ≤ i ≤ k : w_i = U} - #{1 ≤ i ≤ k : w_i = D}`. -/
def height (w : List Step) (k : ℕ) : ℤ :=
  (w.take k).foldl (fun acc s => acc + match s with | U => 1 | D => -1) 0

/-- The height before reading any letters is zero. -/
theorem height_zero (w : List Step) : height w 0 = 0 := by rfl

/-- One-step update formula for the height. -/
theorem height_succ (w : List Step) (k : ℕ) (hk : k < w.length) :
    height w (k + 1) = height w k + match w[k] with | U => 1 | D => -1 := by
  unfold height
  rw [← List.take_concat_get (l := w) (i := k) hk]
  rw [List.concat_eq_append, List.foldl_concat]

/-- Reading a `U` step increases the height by one. -/
theorem height_succ_of_get_U (w : List Step) (k : ℕ) (hk : k < w.length)
    (hU : w[k] = U) :
    height w (k + 1) = height w k + 1 := by
  rw [height_succ w k hk, hU]

/-- Reading a `D` step decreases the height by one. -/
theorem height_succ_of_get_D (w : List Step) (k : ℕ) (hk : k < w.length)
    (hD : w[k] = D) :
    height w (k + 1) = height w k - 1 := by
  rw [height_succ w k hk, hD]
  ring

/-- A single step can increase height by at most one. -/
theorem height_succ_le_height_add_one (w : List Step) (k : ℕ)
    (hk : k < w.length) :
    height w (k + 1) ≤ height w k + 1 := by
  rw [height_succ w k hk]
  cases w[k] <;> norm_num

/-- A single step can decrease height by at most one. -/
theorem height_sub_one_le_height_succ (w : List Step) (k : ℕ)
    (hk : k < w.length) :
    height w k - 1 ≤ height w (k + 1) := by
  rw [height_succ w k hk]
  cases w[k] <;> linarith

/-- The height stabilises once we read past the end of the word. -/
theorem height_of_length_le (w : List Step) (k : ℕ) (hk : w.length ≤ k) :
    height w k = height w w.length := by
  unfold height
  rw [List.take_of_length_le hk, List.take_length]

/-- **Discrete intermediate value theorem for heights.**
If after `t₀` steps the height exceeds a nonnegative level `v`, then some
earlier up-step starts at height exactly `v`: there is a position `t < t₀`
with `P[t] = U` and `height P t = v`.  This is the key climbing fact behind
valid area sequences. -/
theorem exists_uStep_at_height (P : List Step) :
    ∀ t₀ : ℕ, ∀ v : ℤ, 0 ≤ v → v < height P t₀ →
      ∃ t, t < t₀ ∧ P[t]? = some U ∧ height P t = v := by
  intro t₀
  induction t₀ with
  | zero =>
      intro v hv hlt
      rw [height_zero] at hlt
      exfalso; omega
  | succ s ih =>
      intro v hv hlt
      by_cases hcase : v < height P s
      · obtain ⟨t, htlt, hU, hval⟩ := ih v hv hcase
        exact ⟨t, Nat.lt_succ_of_lt htlt, hU, hval⟩
      · push Not at hcase
        by_cases hs : s < P.length
        · cases hPs : P[s]'hs with
          | U =>
              rw [height_succ_of_get_U P s hs hPs] at hlt
              have hveq : v = height P s := by omega
              refine ⟨s, Nat.lt_succ_self s, ?_, hveq.symm⟩
              rw [List.getElem?_eq_getElem hs, hPs]
          | D =>
              rw [height_succ_of_get_D P s hs hPs] at hlt
              exfalso; omega
        · push Not at hs
          rw [height_of_length_le P (s + 1) (by omega),
            ← height_of_length_le P s hs] at hlt
          exfalso; omega

/-! ## Dyck paths -/

/-- **`rmk:step-word` (paper.tex).**
A Dyck path of semilength `n` is a word `P ∈ {U, D}^{2n}` such that every
prefix has at least as many U's as D's and the whole word has exactly `n` U's
and `n` D's. `IsDyckPath P` asserts that `P` is a Dyck path. -/
def IsDyckPath (P : List Step) : Prop :=
  (∀ k : ℕ, k ≤ P.length → 0 ≤ height P k) ∧
  height P P.length = 0

/-- A nonempty Dyck path starts with an up-step. -/
theorem first_step_eq_U_of_isDyckPath (P : List Step) (hP : IsDyckPath P)
    (hpos : 0 < P.length) :
    P[0] = U := by
  have hnonneg : 0 ≤ height P 1 := hP.1 1 (Nat.succ_le_of_lt hpos)
  have hstep := height_succ P 0 hpos
  rw [height_zero] at hstep
  cases h : P[0] <;> simp [h] at hstep
  · rfl
  · linarith

/-- The semilength of a Dyck path is half its length. -/
def semilength (P : List Step) : ℕ := P.length / 2

/-- `DyckPath n` is the set of Dyck paths of semilength `n`. -/
def DyckPath (n : ℕ) : Set (List Step) :=
  {P | IsDyckPath P ∧ P.length = 2 * n}

/-! ## U-positions and area sequence -/

/-- The list of 0-indexed positions of U-steps in a step word. -/
def uPositions (w : List Step) : List ℕ :=
  (List.finRange w.length).filter (fun i => w.get i = U) |>.map (·.val)

/-- Counting occurrences by scanning all valid `Fin` positions agrees with
`List.count`. -/
theorem countP_finRange_get_eq_count (w : List Step) (s : Step) :
    (List.finRange w.length).countP (fun i => w.get i = s) = w.count s := by
  induction w with
  | nil => simp
  | cons t w ih =>
      cases t <;> cases s
      · simp [List.finRange_succ]
        have hcongr :
            List.countP ((fun i => decide ((U :: w).get i = U)) ∘ Fin.succ)
                (List.finRange w.length) =
              List.countP (fun i => w.get i = U) (List.finRange w.length) := by
          apply List.countP_congr
          intro i _hi
          cases i
          simp [Fin.succ]
        exact Eq.trans hcongr ih
      · simp [List.finRange_succ]
        have hcongr :
            List.countP ((fun i => decide ((U :: w).get i = D)) ∘ Fin.succ)
                (List.finRange w.length) =
              List.countP (fun i => w.get i = D) (List.finRange w.length) := by
          apply List.countP_congr
          intro i _hi
          cases i
          simp [Fin.succ]
        exact Eq.trans hcongr ih
      · simp [List.finRange_succ]
        have hcongr :
            List.countP ((fun i => decide ((D :: w).get i = U)) ∘ Fin.succ)
                (List.finRange w.length) =
              List.countP (fun i => w.get i = U) (List.finRange w.length) := by
          apply List.countP_congr
          intro i _hi
          cases i
          simp [Fin.succ]
        exact Eq.trans hcongr ih
      · simp [List.finRange_succ]
        have hcongr :
            List.countP ((fun i => decide ((D :: w).get i = D)) ∘ Fin.succ)
                (List.finRange w.length) =
              List.countP (fun i => w.get i = D) (List.finRange w.length) := by
          apply List.countP_congr
          intro i _hi
          cases i
          simp [Fin.succ]
        exact Eq.trans hcongr ih

/-- The number of recorded `U` positions is the number of `U` steps. -/
theorem length_uPositions (w : List Step) :
    (uPositions w).length = w.count U := by
  unfold uPositions
  rw [List.length_map]
  rw [← List.countP_eq_length_filter]
  exact countP_finRange_get_eq_count w U

/-- If a word begins with `U`, the first recorded `U` position is `0`. -/
theorem head?_uPositions_cons_U (w : List Step) :
    (uPositions (U :: w)).head? = some 0 := by
  unfold uPositions
  simp [List.finRange_succ]

/-- **`rmk:step-word` (paper.tex).**
The area sequence `a(P) = (a_1, …, a_n)` where `a_i = h_P(p_i)` with
0-indexed positions. This equals the height just before the `i`-th U-step. -/
def areaSeq (P : List Step) : List ℤ :=
  (uPositions P).map (fun pos => height P pos)

/-- If a word begins with `U`, the first area-sequence entry is `0`. -/
theorem head?_areaSeq_cons_U (w : List Step) :
    (areaSeq (U :: w)).head? = some 0 := by
  unfold areaSeq
  rw [List.head?_map, head?_uPositions_cons_U]
  rfl

/-- Entries of the area sequence of a Dyck path are nonnegative. -/
theorem areaSeq_nonneg (P : List Step) (hP : IsDyckPath P) :
    ∀ a ∈ areaSeq P, 0 ≤ a := by
  intro a ha
  unfold areaSeq at ha
  simp only [List.mem_map] at ha
  rcases ha with ⟨pos, hpos_mem, rfl⟩
  unfold uPositions at hpos_mem
  simp only [List.mem_map] at hpos_mem
  rcases hpos_mem with ⟨i, _hi_mem, rfl⟩
  exact hP.1 i.val (Nat.le_of_lt i.isLt)

/-- Pointwise form of `areaSeq_nonneg`. -/
theorem areaSeq_get_nonneg (P : List Step) (hP : IsDyckPath P)
    (i : Fin (areaSeq P).length) :
    0 ≤ (areaSeq P).get i := by
  exact areaSeq_nonneg P hP ((areaSeq P).get i) (List.get_mem (areaSeq P) i)

/-- A nonempty Dyck path has first area-sequence entry `0`. -/
theorem areaSeq_head?_eq_zero_of_isDyckPath (P : List Step) (hP : IsDyckPath P)
    (hpos : 0 < P.length) :
    (areaSeq P).head? = some 0 := by
  cases P with
  | nil => simp at hpos
  | cons s tail =>
      have hfirst := first_step_eq_U_of_isDyckPath (s :: tail) hP hpos
      cases s
      · exact head?_areaSeq_cons_U tail
      · simp at hfirst

/-- The length of the area sequence is the number of `U` steps. -/
theorem length_areaSeq (P : List Step) :
    (areaSeq P).length = P.count U := by
  unfold areaSeq
  rw [List.length_map, length_uPositions]

/-- The area sequence and the list of `U`-positions have the same length. -/
theorem length_areaSeq_eq_length_uPositions (P : List Step) :
    (areaSeq P).length = (uPositions P).length := by
  unfold areaSeq; rw [List.length_map]

/-- The `i`-th area-sequence entry is the height just before the `i`-th `U`-step. -/
theorem getElem_areaSeq (P : List Step) (i : ℕ) (hi : i < (areaSeq P).length) :
    (areaSeq P)[i] = height P ((uPositions P)[i]'(length_areaSeq_eq_length_uPositions P ▸ hi)) := by
  simp only [areaSeq, List.getElem_map]

/-- The `U`-positions of a word are exactly the indices carrying a `U`. -/
theorem mem_uPositions {w : List Step} {t : ℕ} :
    t ∈ uPositions w ↔ ∃ h : t < w.length, w[t] = U := by
  unfold uPositions
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, hiU, rfl⟩
    exact ⟨i.isLt, by simpa [List.get_eq_getElem] using hiU⟩
  · rintro ⟨h, hU⟩
    exact ⟨⟨t, h⟩, by simpa [List.get_eq_getElem] using hU, rfl⟩

/-- A position carrying a `U` belongs to `uPositions`. -/
theorem mem_uPositions_of_getElem? {w : List Step} {t : ℕ}
    (ht : w[t]? = some U) : t ∈ uPositions w := by
  have h : t < w.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at ht
    exact absurd ht (by simp)
  rw [mem_uPositions]
  exact ⟨h, Option.some.inj (by rw [← List.getElem?_eq_getElem h]; exact ht)⟩

/-- `uPositions` is strictly increasing. -/
theorem uPositions_pairwise_lt (w : List Step) :
    (uPositions w).Pairwise (· < ·) := by
  unfold uPositions
  rw [List.pairwise_map]
  have hfin : (List.finRange w.length).Pairwise (· < ·) := by
    rw [← List.sortedLT_iff_pairwise]; exact List.sortedLT_finRange w.length
  exact (hfin.sublist List.filter_sublist).imp (fun h => h)

/-- The `U`-positions are sorted strictly increasingly (as a `StrictMono` index map). -/
theorem uPositions_strictMono (w : List Step) :
    StrictMono (uPositions w).get := by
  rw [← List.sortedLT_iff_strictMono_get, List.sortedLT_iff_pairwise]
  exact uPositions_pairwise_lt w

/-- **Climbing witness for area sequences.**
For any index `j` into the area sequence and any level `0 ≤ v < a_j`, there is
an earlier index `i < j` with `a_i = v`.  The area sequence climbs from `0` by
unit steps, so it hits every intermediate level before position `j`. -/
theorem areaSeq_exists_lt_index (P : List Step)
    (j : ℕ) (hj : j < (areaSeq P).length) (v : ℤ)
    (hv : 0 ≤ v) (hlt : v < (areaSeq P)[j]) :
    ∃ i, i < j ∧ ∃ hi : i < (areaSeq P).length, (areaSeq P)[i] = v := by
  have hlen := length_areaSeq_eq_length_uPositions P
  have hjU : j < (uPositions P).length := hlen ▸ hj
  rw [getElem_areaSeq] at hlt
  obtain ⟨t, htlt, htU, htval⟩ := exists_uStep_at_height P _ v hv hlt
  have htmem : t ∈ uPositions P := mem_uPositions_of_getElem? htU
  obtain ⟨i, hi, hival⟩ := List.mem_iff_getElem.mp htmem
  have hij : i < j := by
    have h1 : (uPositions P).get ⟨i, hi⟩ < (uPositions P).get ⟨j, hjU⟩ := by
      simp only [List.get_eq_getElem]; rw [hival]; exact htlt
    exact (uPositions_strictMono P).lt_iff_lt.mp h1
  have hi' : i < (areaSeq P).length := hlen ▸ hi
  refine ⟨i, hij, hi', ?_⟩
  have hmap : (areaSeq P)[i]'hi' = height P ((uPositions P)[i]'hi) := by
    simp only [areaSeq, List.getElem_map]
  rw [hmap, hival]; exact htval

/-! ## Statistics: area, dinv, coarea -/

/-- **Area–dinv–coarea definition (`sec:dyck`, paper.tex).**
`area(P) = Σ_{i=1}^{n} a_i`, the sum of the area sequence. -/
def area (P : List Step) : ℤ :=
  (areaSeq P).sum

/-- The area of a Dyck path is nonnegative. -/
theorem area_nonneg (P : List Step) (hP : IsDyckPath P) : 0 ≤ area P := by
  unfold area
  exact List.sum_nonneg (areaSeq_nonneg P hP)

/-- **Area–dinv–coarea definition (`sec:dyck`, paper.tex).**
`dinv(P) = #{(i,j) : 1 ≤ i < j ≤ n, a_i - a_j ∈ {0, 1}}`,
counting the dinv pairs in the area sequence. -/
def dinv (P : List Step) : ℕ :=
  let a := areaSeq P
  let n := a.length
  ((List.finRange n).flatMap fun ⟨j, hj⟩ =>
    ((List.finRange n).filter fun ⟨i, hi⟩ =>
      i < j ∧ (a[i] - a[j] = 0 ∨ a[i] - a[j] = 1))).length

/-- **Area–dinv–coarea definition (`sec:dyck`, paper.tex).**
`coarea(P) = C(n,2) - area(P)` where `n` is the semilength. -/
noncomputable def coarea (P : List Step) : ℤ :=
  let n : ℤ := semilength P
  n * (n - 1) / 2 - area P

/-! ## Zeta map -/

/-- **`def:zeta` (paper.tex).**
The Haglund zeta map. For each rank `r = 0, 1, …, max_i a_i + 1`, scan
`a_1, …, a_n` left to right and at position `i` append:
- U if `a_i = r`
- D if `a_i = r - 1`
- nothing otherwise. -/
def zetaMap (P : List Step) : List Step :=
  let a := areaSeq P
  let maxA := a.foldl max 0
  (List.range (maxA.toNat + 2)).flatMap fun r =>
    a.flatMap fun ai =>
      if ai = (r : ℤ) then [U]
      else if ai = (r : ℤ) - 1 then [D]
      else []

/-! ## Reverse complement -/

/-- **Table 1 (`tab:named-bijections`, paper.tex).**
`comp` swaps U ↔ D. -/
def Step.comp : Step → Step
  | U => D
  | D => U

/-- **Table 1 (`tab:named-bijections`, paper.tex).**
The reverse-complement `rc(w) = comp(rev(w))`, a Catalan involution. -/
def reverseComplement (w : List Step) : List Step :=
  (w.reverse).map Step.comp

/-! ## Two-pyramid paths -/

/-- **`lem:zeta-two-pyramid` (paper.tex).**
Two-pyramid paths: `P_{m,n} = U^m D^m U^n D^n`. -/
def twoPyramid (m n : ℕ) : List Step :=
  List.replicate m U ++ List.replicate m D ++
  List.replicate n U ++ List.replicate n D

/-! ## Wrapped-flat paths W_n -/

/-- **`lem:wrapped-flat-stats` (paper.tex).**
The wrapped-flat path `W_n = U(UD)^n D`. -/
def wrappedFlat (n : ℕ) : List Step :=
  [U] ++ (List.replicate n [U, D]).flatten ++ [D]

/-! ## First ascent and tailU -/

/-- **`sec:wrapped-flat` (paper.tex).**
The first-ascent length `fas(P)`: the length of the maximal initial run of U's. -/
def firstAscent (P : List Step) : ℕ :=
  P.takeWhile (· = U) |>.length

/-- **`sec:wrapped-flat` (paper.tex).**
`tailU(P)`: the number of U-steps after the first ascent, i.e., the total
number of U-steps minus the first-ascent length. -/
def tailU (P : List Step) : ℕ :=
  P.count U - firstAscent P

/-! ## Height and count relationship -/

/-
The height equals count U minus count D in the first k letters.
-/
theorem height_eq_count (w : List Step) (k : ℕ) :
    height w k = (w.take k).count U - (w.take k).count D := by
      unfold height;
      induction' ( List.take k w ) using List.reverseRecOn with l ih;
      · rfl;
      · cases ih <;> simp +decide [ * ] <;> ring

/-- Every step is either `U` or `D`, so the two counts add to the length. -/
theorem count_U_add_count_D (w : List Step) :
    w.count U + w.count D = w.length := by
  induction w with
  | nil => simp
  | cons s w ih =>
      cases s <;> simp <;> omega

/-- A Dyck path has the same number of `U` and `D` steps. -/
theorem count_U_eq_count_D_of_isDyckPath (P : List Step) (hP : IsDyckPath P) :
    P.count U = P.count D := by
  have h := hP.2
  rw [height_eq_count, List.take_length] at h
  omega

/-- The number of `U` steps in a Dyck path is its semilength. -/
theorem count_U_eq_semilength (P : List Step) (hP : IsDyckPath P) :
    P.count U = semilength P := by
  have hcount := count_U_eq_count_D_of_isDyckPath P hP
  have hlen := count_U_add_count_D P
  unfold semilength
  omega

/-- The number of `D` steps in a Dyck path is its semilength. -/
theorem count_D_eq_semilength (P : List Step) (hP : IsDyckPath P) :
    P.count D = semilength P := by
  rw [← count_U_eq_count_D_of_isDyckPath P hP]
  exact count_U_eq_semilength P hP

/-- The area sequence of a Dyck path has length equal to the semilength. -/
theorem length_areaSeq_eq_semilength (P : List Step) (hP : IsDyckPath P) :
    (areaSeq P).length = semilength P := by
  rw [length_areaSeq, count_U_eq_semilength P hP]

/-! ## Local statistics: valleys, double rises, peaks -/

/-- **`sec:narayana-sweep` (paper.tex).**
The number of valleys `val(w) = #{i : w_i w_{i+1} = DU}`. -/
def valleys (w : List Step) : ℕ :=
  (List.range (w.length - 1)).countP fun i =>
    w[i]! = D ∧ w[i + 1]! = U

/-- **`sec:narayana-sweep` (paper.tex).**
The number of double rises `dr(w) = #{i : w_i w_{i+1} = UU}`. -/
def doubleRises (w : List Step) : ℕ :=
  (List.range (w.length - 1)).countP fun i =>
    w[i]! = U ∧ w[i + 1]! = U

/-- **`sec:narayana-sweep` (paper.tex).**
The number of peaks `pk(w) = #{i : w_i w_{i+1} = UD}`. -/
def peaks (w : List Step) : ℕ :=
  (List.range (w.length - 1)).countP fun i =>
    w[i]! = U ∧ w[i + 1]! = D

/-! ## S_tri -/

/-- **`cor:forced-triangular-pairs` (paper.tex).**
The triangular set `S_tri = {(a, b) ∈ ℕ² : b ≥ 1, b*(b-1)/2 + 1 ≤ a ≤ b*(b+1)/2 + 1}`. -/
def S_tri : Set (ℕ × ℕ) :=
  {p | p.2 ≥ 1 ∧ p.2 * (p.2 - 1) / 2 + 1 ≤ p.1 ∧ p.1 ≤ p.2 * (p.2 + 1) / 2 + 1}

/-! ## Height sweep (Narayana) -/

/-- **`sec:narayana-sweep` (paper.tex).**
The height sweep `H(P)`: list the steps of `P` by increasing starting height
(height just before the step), breaking ties by decreasing input position
(right-to-left). -/
def heightSweep (P : List Step) : List Step :=
  let indexed := P.zipIdx |>.map fun (s, i) => (height P i, i, s)
  -- Sort by (height ascending, position descending for ties)
  let sorted := indexed.mergeSort (fun a b =>
    if a.1 < b.1 then true
    else if a.1 > b.1 then false
    else a.2.1 > b.2.1)
  sorted.map fun (_, _, s) => s

/-
The height sweep is a permutation of the input.
-/
theorem heightSweep_perm (P : List Step) : (heightSweep P).Perm P := by
  unfold heightSweep
  refine ((List.mergeSort_perm _ _).map _).trans ?_
  rw [List.map_map]
  have h2 : (P.zipIdx.map
      ((fun t : ℤ × ℕ × Step => t.2.2) ∘ fun (si : Step × ℕ) => (height P si.2, si.2, si.1)))
      = P.zipIdx.map Prod.fst :=
    List.map_congr_left fun si _ => by rcases si with ⟨s, i⟩; rfl
  rw [h2, List.zipIdx_map_fst]

/-- The height sweep preserves the final height, since it only permutes steps. -/
theorem height_heightSweep_length (P : List Step) :
    height (heightSweep P) (heightSweep P).length = height P P.length := by
  rw [height_eq_count, height_eq_count, List.take_length, List.take_length]
  have hp := heightSweep_perm P
  have hU : (heightSweep P).count U = P.count U := by
    exact hp.count_eq U
  have hD : (heightSweep P).count D = P.count D := by
    exact hp.count_eq D
  rw [hU, hD]
