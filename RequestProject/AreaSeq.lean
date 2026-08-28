/-
# Area sequences and the path-from-area-sequence constructor

Foundational, reusable infrastructure for the Dyck-path and no-swap sections of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry".

The key construction is `pathOfAreaSeq : List ℤ → List Step`, the standard Dyck
path realising a valid area sequence, together with the two round-trip facts:

* `areaSeq_pathOfAreaSeq` : `areaSeq (pathOfAreaSeq a) = a` for valid `a`;
* `dyck_eq_of_areaSeq_eq` : a Dyck path is determined by its area sequence.

These let Lemma 7.3 build the canonical tight path and prove its uniqueness.
-/
import RequestProject.DyckPath

open Step

/-! ## Cons lemmas for `height`, `uPositions`, `areaSeq` -/

/-- Prepending a `U` raises later heights by one. -/
theorem height_cons_U (w : List Step) (k : ℕ) :
    height (U :: w) (k + 1) = height w k + 1 := by
  rw [height_eq_count, height_eq_count, List.take_succ_cons, List.count_cons,
    List.count_cons]
  simp
  ring

/-- Prepending a `D` lowers later heights by one. -/
theorem height_cons_D (w : List Step) (k : ℕ) :
    height (D :: w) (k + 1) = height w k - 1 := by
  rw [height_eq_count, height_eq_count, List.take_succ_cons, List.count_cons,
    List.count_cons]
  simp
  ring

/-- The `U`-positions of `U :: w`: position `0`, then the shifted positions of `w`. -/
theorem uPositions_cons_U (w : List Step) :
    uPositions (U :: w) = 0 :: (uPositions w).map (· + 1) := by
  unfold uPositions
  simp only [List.length_cons, List.finRange_succ, List.filter_cons]
  simp only [List.filter_map, List.map_map]
  rw [List.filter_congr (q := fun j : Fin w.length => decide (w.get j = U))
        (by intro j _; rfl)]
  simp [Function.comp, Fin.val_succ]

/-- The `U`-positions of `D :: w`: just the shifted positions of `w`. -/
theorem uPositions_cons_D (w : List Step) :
    uPositions (D :: w) = (uPositions w).map (· + 1) := by
  unfold uPositions
  simp only [List.length_cons, List.finRange_succ, List.filter_cons]
  simp only [List.filter_map, List.map_map]
  rw [List.filter_congr (q := fun j : Fin w.length => decide (w.get j = U))
        (by intro j _; rfl)]
  simp [Function.comp, Fin.val_succ]

/-- Area sequence of `U :: w`: a leading `0`, then `w`'s entries raised by one. -/
theorem areaSeq_cons_U (w : List Step) :
    areaSeq (U :: w) = 0 :: (areaSeq w).map (· + 1) := by
  unfold areaSeq
  rw [uPositions_cons_U]
  simp only [List.map_cons, List.map_map, height_zero]
  congr 1
  apply List.map_congr_left
  intro pos _hpos
  simp only [Function.comp]
  rw [height_cons_U]

/-- Area sequence of `D :: w`: `w`'s entries lowered by one. -/
theorem areaSeq_cons_D (w : List Step) :
    areaSeq (D :: w) = (areaSeq w).map (· - 1) := by
  unfold areaSeq
  rw [uPositions_cons_D]
  simp only [List.map_map]
  apply List.map_congr_left
  intro pos _hpos
  simp only [Function.comp]
  rw [height_cons_D]

/-! ## Append and `replicate D` lemmas -/

/-- Area sequence of an append: the left area sequence, then the right one
shifted up by the height the left part ends at. -/
theorem areaSeq_append (p q : List Step) :
    areaSeq (p ++ q) = areaSeq p ++ (areaSeq q).map (· + height p p.length) := by
  induction p with
  | nil =>
      have h0 : areaSeq ([] : List Step) = [] := by simp [areaSeq, uPositions]
      simp [h0, height_zero]
  | cons s p' ih =>
      cases s with
      | U =>
          rw [List.cons_append, areaSeq_cons_U, areaSeq_cons_U, ih, List.map_append,
            List.map_map, List.cons_append, List.length_cons, height_cons_U]
          congr 1
          congr 1
          apply List.map_congr_left; intro x _; simp only [Function.comp]; ring
      | D =>
          rw [List.cons_append, areaSeq_cons_D, areaSeq_cons_D, ih, List.map_append,
            List.map_map, List.length_cons, height_cons_D]
          congr 1
          apply List.map_congr_left; intro x _; simp only [Function.comp]; ring

/-- A run of `D`'s contains no `U`, so its area sequence is empty. -/
theorem areaSeq_replicate_D (n : ℕ) : areaSeq (List.replicate n D) = [] := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, areaSeq_cons_D, ih]; rfl

/-- The height after `k ≤ n` `D`'s is `-k`. -/
theorem height_replicate_D_le (n k : ℕ) (hk : k ≤ n) :
    height (List.replicate n D) k = -(k : ℤ) := by
  rw [height_eq_count, List.take_replicate, Nat.min_eq_left hk]
  simp [List.count_replicate]

/-- The height after a full run of `n` `D`'s is `-n`. -/
theorem height_replicate_D (n : ℕ) :
    height (List.replicate n D) n = -(n : ℤ) :=
  height_replicate_D_le n n le_rfl

/-! ## The path-from-area-sequence constructor -/

/-- Validity of an area-sequence suffix whose first up-step starts at height
`prev`: every entry is nonnegative, the head is at most `prev`, and the rest is
valid from `head + 1`.  `IsValidAreaSeq = ValidFrom 0`. -/
def ValidFrom (prev : ℤ) : List ℤ → Prop
  | [] => True
  | x :: rest => 0 ≤ x ∧ x ≤ prev ∧ ValidFrom (x + 1) rest

/-- A list of integers is a valid Dyck area sequence: it climbs from `0` by unit
steps and stays nonnegative. -/
def IsValidAreaSeq (a : List ℤ) : Prop := ValidFrom 0 a

/-- Build the Dyck path realising an area sequence.  Sitting at height `prev`,
emit the `D`'s descending to the next start height `x`, then a `U`, and recurse;
when the list is exhausted, descend the remaining `prev` `D`'s to height `0`. -/
def pathOfAreaSeqAux : ℤ → List ℤ → List Step
  | prev, [] => List.replicate prev.toNat D
  | prev, x :: rest =>
      List.replicate (prev - x).toNat D ++ U :: pathOfAreaSeqAux (x + 1) rest

/-- The Dyck path realising the area sequence `a` (starting from height `0`). -/
def pathOfAreaSeq (a : List ℤ) : List Step := pathOfAreaSeqAux 0 a

/-! ## Round-trip A: the constructor realises the area sequence -/

/-- **Round-trip (general form).**  The area sequence of `pathOfAreaSeqAux prev a`
is `a` shifted down by `prev` (the path descends `prev` below height `0` before
its first up-step). -/
theorem areaSeq_pathOfAreaSeqAux (prev : ℤ) (a : List ℤ) (h : ValidFrom prev a) :
    areaSeq (pathOfAreaSeqAux prev a) = a.map (· - prev) := by
  induction a generalizing prev with
  | nil => simp [pathOfAreaSeqAux, areaSeq_replicate_D]
  | cons x rest ih =>
      obtain ⟨hx0, hxle, hrest⟩ := h
      have hm : ((prev - x).toNat : ℤ) = prev - x := Int.toNat_of_nonneg (by linarith)
      show areaSeq (List.replicate (prev - x).toNat D ++ U :: pathOfAreaSeqAux (x + 1) rest)
        = (x :: rest).map (· - prev)
      rw [areaSeq_append, areaSeq_replicate_D, areaSeq_cons_U, ih (x + 1) hrest,
        List.length_replicate, height_replicate_D]
      simp only [List.nil_append, List.map_cons, List.map_map]
      congr 1
      · simp only [zero_add]; rw [hm]; ring
      · apply List.map_congr_left; intro y _; simp only [Function.comp]; rw [hm]; ring

/-- **Round-trip A.**  The constructor realises a valid area sequence. -/
theorem areaSeq_pathOfAreaSeq (a : List ℤ) (h : IsValidAreaSeq a) :
    areaSeq (pathOfAreaSeq a) = a := by
  rw [pathOfAreaSeq, areaSeq_pathOfAreaSeqAux 0 a h]
  simp

/-! ## Height of appends; Dyck-ness and length of the constructor -/

/-- Height within the left part of an append. -/
theorem height_append_left (p q : List Step) (k : ℕ) (hk : k ≤ p.length) :
    height (p ++ q) k = height p k := by
  rw [height_eq_count, height_eq_count, List.take_append_of_le_length hk]

/-- Height past the left part of an append splits as a sum. -/
theorem height_append_right (p q : List Step) (j : ℕ) :
    height (p ++ q) (p.length + j) = height p p.length + height q j := by
  rw [height_eq_count, List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.count_append, List.count_append, height_eq_count, List.take_length,
    height_eq_count]
  push_cast; ring

/-- The constructor emits exactly one `U` per area entry. -/
theorem count_U_pathOfAreaSeqAux (prev : ℤ) (a : List ℤ) :
    (pathOfAreaSeqAux prev a).count U = a.length := by
  induction a generalizing prev with
  | nil => simp [pathOfAreaSeqAux, List.count_replicate]
  | cons x rest ih =>
      simp [pathOfAreaSeqAux, List.count_append, List.count_replicate, ih]

/-- Length of the constructor output. -/
theorem length_pathOfAreaSeqAux (prev : ℤ) (a : List ℤ) (h : ValidFrom prev a) :
    (pathOfAreaSeqAux prev a).length = prev.toNat + 2 * a.length := by
  induction a generalizing prev with
  | nil => simp [pathOfAreaSeqAux]
  | cons x rest ih =>
      obtain ⟨hx0, hxle, hrest⟩ := h
      rw [pathOfAreaSeqAux]
      rw [List.length_append, List.length_replicate, List.length_cons,
        ih (x + 1) hrest]
      have h1 : ((prev - x).toNat : ℤ) = prev - x := Int.toNat_of_nonneg (by linarith)
      have h2 : ((x + 1).toNat : ℤ) = x + 1 := Int.toNat_of_nonneg (by linarith)
      have h3 : (prev.toNat : ℤ) = prev := Int.toNat_of_nonneg (by linarith)
      simp only [List.length_cons]
      omega

/-- The constructor stays at or above `-prev` everywhere (with `0 ≤ prev`). -/
theorem height_pathOfAreaSeqAux_ge (prev : ℤ) (a : List ℤ) (hprev : 0 ≤ prev)
    (h : ValidFrom prev a) :
    ∀ k, k ≤ (pathOfAreaSeqAux prev a).length →
      -prev ≤ height (pathOfAreaSeqAux prev a) k := by
  induction a generalizing prev with
  | nil =>
      intro k hk
      rw [pathOfAreaSeqAux] at hk ⊢
      rw [List.length_replicate] at hk
      rw [height_replicate_D_le _ _ hk]
      have hpn : (k : ℤ) ≤ (prev.toNat : ℤ) := by exact_mod_cast hk
      rw [Int.toNat_of_nonneg hprev] at hpn
      linarith
  | cons x rest ih =>
      obtain ⟨hx0, hxle, hrest⟩ := h
      intro k hk
      set m := (prev - x).toNat with hm_def
      have hm : (m : ℤ) = prev - x := Int.toNat_of_nonneg (by linarith)
      rw [pathOfAreaSeqAux] at hk ⊢
      have hlentail : k ≤ m + 1 + (pathOfAreaSeqAux (x + 1) rest).length := by
        have h' := hk
        simp only [List.length_append, List.length_replicate, List.length_cons] at h'
        omega
      by_cases hk1 : k ≤ m
      · rw [height_append_left _ _ _ (by rw [List.length_replicate]; exact hk1),
          height_replicate_D_le _ _ hk1]
        have hkm : (k : ℤ) ≤ m := by exact_mod_cast hk1
        rw [hm] at hkm; linarith
      · push Not at hk1
        obtain ⟨j, rfl⟩ : ∃ j, k = (m + 1) + j := ⟨k - (m + 1), by omega⟩
        rw [show List.replicate m D ++ U :: pathOfAreaSeqAux (x + 1) rest
            = (List.replicate m D ++ [U]) ++ pathOfAreaSeqAux (x + 1) rest by simp]
        have hplen : (List.replicate m D ++ [U]).length = m + 1 := by
          simp [List.length_append, List.length_replicate]
        rw [show (m + 1) + j = (List.replicate m D ++ [U]).length + j by rw [hplen],
          height_append_right]
        have hpre : height (List.replicate m D ++ [U])
            (List.replicate m D ++ [U]).length = -(m : ℤ) + 1 := by
          rw [hplen, show m + 1 = (List.replicate m D).length + 1 by
              rw [List.length_replicate],
            height_append_right, List.length_replicate, height_replicate_D]
          norm_num [show height [U] 1 = 1 from by decide]
        rw [hpre]
        have htail := ih (x + 1) (by linarith) hrest j (by omega)
        linarith [hm]

/-- The constructor ends at height `-prev`. -/
theorem height_pathOfAreaSeqAux_end (prev : ℤ) (a : List ℤ) (hprev : 0 ≤ prev)
    (h : ValidFrom prev a) :
    height (pathOfAreaSeqAux prev a) (pathOfAreaSeqAux prev a).length = -prev := by
  rw [height_eq_count, List.take_length]
  have hU := count_U_pathOfAreaSeqAux prev a
  have hlen := length_pathOfAreaSeqAux prev a h
  have hUD := count_U_add_count_D (pathOfAreaSeqAux prev a)
  have hpt : (prev.toNat : ℤ) = prev := Int.toNat_of_nonneg hprev
  have hD : (pathOfAreaSeqAux prev a).count D = prev.toNat + a.length := by omega
  rw [hU, hD]; push_cast; omega

/-- **Dyck-ness.**  The constructor of a valid area sequence is a Dyck path. -/
theorem isDyckPath_pathOfAreaSeq (a : List ℤ) (h : IsValidAreaSeq a) :
    IsDyckPath (pathOfAreaSeq a) := by
  rw [pathOfAreaSeq]
  refine ⟨fun k hk => ?_, ?_⟩
  · have := height_pathOfAreaSeqAux_ge 0 a le_rfl h k hk; simpa using this
  · have := height_pathOfAreaSeqAux_end 0 a le_rfl h; simpa using this

/-- The constructor of an area sequence of length `n` has length `2n`. -/
theorem length_pathOfAreaSeq (a : List ℤ) (h : IsValidAreaSeq a) :
    (pathOfAreaSeq a).length = 2 * a.length := by
  rw [pathOfAreaSeq, length_pathOfAreaSeqAux 0 a h]; simp

/-- The constructor lands in `DyckPath a.length`. -/
theorem pathOfAreaSeq_mem_dyckPath (a : List ℤ) (h : IsValidAreaSeq a) :
    pathOfAreaSeq a ∈ DyckPath a.length :=
  ⟨isDyckPath_pathOfAreaSeq a h, length_pathOfAreaSeq a h⟩

/-! ## A step word is determined by its length and `U`-positions -/

/-- Two step words of the same length with the same `U`-positions are equal. -/
theorem eq_of_length_uPositions_eq (p q : List Step)
    (hlen : p.length = q.length) (hU : uPositions p = uPositions q) :
    p = q := by
  apply List.ext_getElem hlen
  intro i hip hiq
  have hp : p[i] = U ↔ i ∈ uPositions p := by
    rw [mem_uPositions]; constructor
    · intro h; exact ⟨hip, h⟩
    · rintro ⟨_, h⟩; exact h
  have hq : q[i] = U ↔ i ∈ uPositions q := by
    rw [mem_uPositions]; constructor
    · intro h; exact ⟨hiq, h⟩
    · rintro ⟨_, h⟩; exact h
  rw [hU] at hp
  cases hpi : p[i] <;> cases hqi : q[i] <;> first | rfl | (exfalso; simp_all)

/-! ## Injectivity of `areaSeq` on Dyck paths -/

/-- The `U`-positions of a prefix are the `U`-positions below the cut. -/
theorem uPositions_take (w : List Step) (k : ℕ) :
    uPositions (w.take k) = (uPositions w).filter (· < k) := by
  apply List.Pairwise.eq_of_mem_iff (uPositions_pairwise_lt _)
    ((uPositions_pairwise_lt _).filter _)
  intro t
  rw [mem_uPositions, List.mem_filter, mem_uPositions]
  constructor
  · rintro ⟨ht, hU⟩
    have htk : t < k := by
      have := ht; rw [List.length_take] at this; omega
    have htw : t < w.length := by
      have := ht; rw [List.length_take] at this; omega
    refine ⟨⟨htw, ?_⟩, by simpa using htk⟩
    rwa [List.getElem_take] at hU
  · rintro ⟨⟨htw, hU⟩, htk⟩
    have htk' : t < k := by simpa using htk
    have ht : t < (w.take k).length := by rw [List.length_take]; omega
    exact ⟨ht, by rw [List.getElem_take]; exact hU⟩

/-- In a strictly increasing `ℕ`-list, exactly `i` entries lie below the `i`-th. -/
theorem length_filter_lt_getElem {L : List ℕ} (hL : L.Pairwise (· < ·))
    (i : ℕ) (hi : i < L.length) :
    (L.filter (· < L[i])).length = i := by
  have key := List.pairwise_iff_getElem.mp hL
  set t := L[i] with ht
  have hmono : ∀ j (hj : j < L.length), j < i → L[j] < t :=
    fun j hj hji => ht ▸ key j i hj hi hji
  have hmono' : ∀ j (hj : j < L.length), i ≤ j → t ≤ L[j] := by
    intro j hj hij
    rcases Nat.eq_or_lt_of_le hij with h | h
    · subst h; rw [ht]
    · exact le_of_lt (ht ▸ key i j hi hj h)
  rw [show L = L.take i ++ L.drop i from (List.take_append_drop i L).symm,
    List.filter_append]
  have h1 : (L.take i).filter (· < t) = L.take i := by
    apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_take]
    have hjlen : j < L.length := by rw [List.length_take] at hj; omega
    have hji : j < i := by rw [List.length_take] at hj; omega
    simpa using hmono j hjlen hji
  have h2 : (L.drop i).filter (· < t) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_drop]
    have hjlen : i + j < L.length := by rw [List.length_drop] at hj; omega
    have := hmono' (i + j) hjlen (by omega)
    simp; omega
  rw [h1, h2, List.length_append, List.length_take]
  simp; omega

/-- The number of `U`'s strictly before the `i`-th `U`-position is `i`. -/
theorem count_U_take_uPos (w : List Step) (i : ℕ) (hi : i < (uPositions w).length) :
    (w.take ((uPositions w)[i])).count U = i := by
  rw [← length_uPositions, uPositions_take,
    length_filter_lt_getElem (uPositions_pairwise_lt w) i hi]

/-- **Closed form.**  The `i`-th area entry equals `2i` minus the `i`-th
`U`-position. -/
theorem areaSeq_getElem_eq (w : List Step) (i : ℕ) (hi : i < (areaSeq w).length) :
    (areaSeq w)[i] = 2 * (i : ℤ) - ((uPositions w)[i]'(by
      rwa [← length_areaSeq_eq_length_uPositions]) : ℕ) := by
  have hiU : i < (uPositions w).length := by rwa [← length_areaSeq_eq_length_uPositions]
  rw [getElem_areaSeq, height_eq_count]
  set p := (uPositions w)[i]
  have hp_lt : p < w.length := by
    have : p ∈ uPositions w := List.getElem_mem hiU
    rw [mem_uPositions] at this; exact this.1
  have hcU : (w.take p).count U = i := count_U_take_uPos w i hiU
  have hUD := count_U_add_count_D (w.take p)
  have htlen : (w.take p).length = p := by rw [List.length_take]; omega
  rw [hcU] at hUD ⊢
  have hcD : (w.take p).count D = p - i := by omega
  rw [hcD]
  have : i ≤ p := by omega
  push_cast [Nat.cast_sub this]
  ring

/-- **Injectivity.**  A Dyck path is determined by its area sequence. -/
theorem dyck_eq_of_areaSeq_eq (P Q : List Step)
    (hP : IsDyckPath P) (hQ : IsDyckPath Q) (h : areaSeq P = areaSeq Q) :
    P = Q := by
  have hlenU : P.count U = Q.count U := by
    have := congrArg List.length h
    rwa [length_areaSeq, length_areaSeq] at this
  have hlen : P.length = Q.length := by
    have hP2 := count_U_add_count_D P
    have hQ2 := count_U_add_count_D Q
    have hPD := count_U_eq_count_D_of_isDyckPath P hP
    have hQD := count_U_eq_count_D_of_isDyckPath Q hQ
    omega
  apply eq_of_length_uPositions_eq P Q hlen
  have hlenUP : (uPositions P).length = (uPositions Q).length := by
    rw [length_uPositions, length_uPositions, hlenU]
  apply List.ext_getElem hlenUP
  intro i hiP hiQ
  have hiAP : i < (areaSeq P).length := by rwa [length_areaSeq_eq_length_uPositions]
  have hiAQ : i < (areaSeq Q).length := by rwa [length_areaSeq_eq_length_uPositions]
  have e1 : (areaSeq P)[i] = 2 * (i : ℤ) - ((uPositions P)[i] : ℤ) :=
    areaSeq_getElem_eq P i hiAP
  have e2 : (areaSeq Q)[i] = 2 * (i : ℤ) - ((uPositions Q)[i] : ℤ) :=
    areaSeq_getElem_eq Q i hiAQ
  have e3 : (areaSeq P)[i]? = (areaSeq Q)[i]? := by rw [h]
  rw [List.getElem?_eq_getElem hiAP, List.getElem?_eq_getElem hiAQ, Option.some_inj] at e3
  have hu : ((uPositions P)[i] : ℤ) = ((uPositions Q)[i] : ℤ) := by omega
  exact_mod_cast hu
