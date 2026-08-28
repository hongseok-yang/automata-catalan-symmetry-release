/-
# The fibred rank decomposition (§9 tower, Stage E)

The copied slice is `U^mS (UD)^n D^mS`; ranks are prefix-determined, so every
summand family re-runs the wrapped-flat analysis with the prefix `pre := U^mS`
absorbed wholesale by `SliceRank.prefixRank_pre_blocks_affineOnResidues` (which
is stated for an arbitrary `pre`).  Layer by layer:

* word geometry — `copiedSlice_take_mid` (middle positions are the wrapped-flat
  takes shifted by `mS − 1`), `copiedSlice_take_U` (prefix stretch),
  `copiedSlice_take_tail` (suffix stretch `U^mS (UD)^n D^(i+1)`);
* the copied block/suf summand families at `q₁ := δ^*(q0, U^mS)` — mirrors of
  `SliceRankBlock`/`SliceRankRegions` at positions `mS + 2j (+1)`;
* `prefixRank_pre_blocks_tail_rankAffine` — THE one new piece of mathematics
  (CS-4): the `D^l`-tail variant of the pre-blocks engine, by splitting the
  fold and reading the tail correction off the post-loop state iterate;
* `summand_region_decomp_fibred` / `rank_cell_decomp_fibred` — the per-cell
  `R(t) + B(n)` split over `RegionSpecF`, prefix/suffix stretches landing as
  constants and the `D`-stretch families;
* `regionSpecFs` / `regionTuplesF` — the per-`mS` EXPLICIT `Finset`
  enumerations of valid descriptors (deliberately never `Fintype` instances —
  the CS-4 freeze keeps them out of `Finset.univ` period products).
-/
import RequestProject.SliceFamilyRank
import RequestProject.CopiedCells
import RequestProject.CopiedMark

namespace CopiedRank

open WRP Step SliceRankAtom SliceRank SliceFamilyRank SliceFamilyCell
  CopiedCells CopiedMark

variable {d : ℕ}

/-! ## Word geometry of the copied slice -/

/-- Middle-window takes are the wrapped-flat takes shifted by the prefix
stretch. -/
theorem copiedSlice_take_mid (mS x n : ℕ) (hm : 1 ≤ mS) (hx : x ≤ 2 * (n + 1)) :
    (copiedSlice mS n).take (mS - 1 + x)
      = List.replicate (mS - 1) U ++ (wrappedFlat n).take x := by
  rw [copiedSlice_eq_wrap mS n hm, List.append_assoc, List.take_append,
    List.length_replicate, List.take_replicate]
  have h1 : min (mS - 1 + x) (mS - 1) = mS - 1 := by omega
  have h2 : mS - 1 + x - (mS - 1) = x := by omega
  rw [h1, h2, List.take_append_of_le_length (by rw [length_wrappedFlat]; omega)]

/-- Middle-window letters are the wrapped-flat letters shifted by the prefix
stretch. -/
theorem copiedSlice_getElem?_mid (mS x n : ℕ) (hm : 1 ≤ mS)
    (hx : x < 2 * (n + 1)) :
    (copiedSlice mS n)[mS - 1 + x]? = (wrappedFlat n)[x]? := by
  rw [copiedSlice_eq_wrap mS n hm, List.append_assoc,
    List.getElem?_append_right (by rw [List.length_replicate]; omega),
    List.length_replicate]
  have h2 : mS - 1 + x - (mS - 1) = x := by omega
  rw [h2, List.getElem?_append_left (by rw [length_wrappedFlat]; omega)]

/-- Takes inside the (closed) prefix stretch are all-`U`. -/
theorem copiedSlice_take_U (mS q n : ℕ) (hm : 1 ≤ mS) (hq : q ≤ mS) :
    (copiedSlice mS n).take q = List.replicate q U := by
  by_cases h : q ≤ mS - 1
  · rw [copiedSlice_eq_wrap mS n hm, List.append_assoc,
      List.take_append_of_le_length (by rw [List.length_replicate]; omega),
      List.take_replicate]
    congr 1
    omega
  · have hq' : q = mS := by omega
    have key := copiedSlice_take_mid mS 1 n hm (by omega)
    have harg : mS - 1 + 1 = mS := by omega
    rw [harg] at key
    have ht : (wrappedFlat n).take 1 = [U] := by
      have h0 := SliceWords.wrappedFlat_take 0 n (Nat.zero_le n)
      simpa using h0
    rw [hq', key, ht, show ([U] : List Step) = List.replicate 1 U from rfl,
      List.replicate_append_replicate, harg]

/-- The copied block prefix `U^mS (UD)^j` as a take. -/
theorem copiedSlice_take_block (mS j n : ℕ) (hm : 1 ≤ mS) (h : j ≤ n) :
    (copiedSlice mS n).take (mS + 2 * j)
      = List.replicate mS U ++ (List.replicate j [U, D]).flatten := by
  have e : mS + 2 * j = mS - 1 + (1 + 2 * j) := by omega
  rw [e, copiedSlice_take_mid mS (1 + 2 * j) n hm (by omega),
    SliceWords.wrappedFlat_take j n h]
  have hUU : List.replicate (mS - 1) U ++ [U] = List.replicate mS U := by
    rw [show ([U] : List Step) = List.replicate 1 U from rfl,
      List.replicate_append_replicate]
    congr 1
    omega
  rw [← List.append_assoc, hUU]

/-- The suffix-stretch take `U^mS (UD)^n D^(i+1)`. -/
theorem copiedSlice_take_tail (mS i n : ℕ) (hm : 1 ≤ mS) (hi : i ≤ mS - 1) :
    (copiedSlice mS n).take (mS + 2 * n + 1 + i)
      = List.replicate mS U ++ (List.replicate n [U, D]).flatten
          ++ List.replicate (i + 1) D := by
  rw [copiedSlice_eq_wrap mS n hm, List.take_append,
    List.take_of_length_le (by
      rw [List.length_append, List.length_replicate, length_wrappedFlat]
      omega)]
  rw [List.length_append, List.length_replicate, length_wrappedFlat,
    List.take_replicate]
  have h1 : min (mS + 2 * n + 1 + i - (mS - 1 + 2 * (n + 1))) (mS - 1) = i := by
    omega
  rw [h1]
  have hU : List.replicate (mS - 1) U ++ [U] = List.replicate mS U := by
    rw [show ([U] : List Step) = List.replicate 1 U from rfl,
      List.replicate_append_replicate]
    congr 1
    omega
  have hD : ([D] : List Step) ++ List.replicate i D
      = List.replicate (i + 1) D := by
    rw [show ([D] : List Step) = List.replicate 1 D from rfl,
      List.replicate_append_replicate]
    congr 1
    omega
  rw [← hU, ← hD, wrappedFlat]
  simp only [List.append_assoc]

/-- Suffix-stretch letters are `D`. -/
theorem copiedSlice_getElem?_tail (mS l n : ℕ) (hm : 1 ≤ mS)
    (hl : l < mS - 1) :
    (copiedSlice mS n)[mS + 2 * n + 1 + l]? = some D := by
  rw [copiedSlice_eq_wrap mS n hm,
    List.getElem?_append_right (by
      rw [List.length_append, List.length_replicate, length_wrappedFlat]
      omega)]
  rw [List.length_append, List.length_replicate, length_wrappedFlat,
    List.getElem?_eq_getElem (by rw [List.length_replicate]; omega),
    List.getElem_replicate]

/-- Middle block `U`-letters. -/
theorem copiedSlice_getElem?_blockU (mS j n : ℕ) (hm : 1 ≤ mS) (h : j < n) :
    (copiedSlice mS n)[mS + 2 * j]? = some U := by
  have e : mS + 2 * j = mS - 1 + (1 + 2 * j) := by omega
  rw [e, copiedSlice_getElem?_mid mS (1 + 2 * j) n hm (by omega),
    List.getElem?_eq_getElem (by rw [length_wrappedFlat]; omega),
    SliceCount.wrappedFlat_getElem_U n j h (by rw [length_wrappedFlat]; omega)]

/-- Middle block `D`-letters. -/
theorem copiedSlice_getElem?_blockD (mS j n : ℕ) (hm : 1 ≤ mS) (h : j < n) :
    (copiedSlice mS n)[mS + 2 * j + 1]? = some D := by
  have e : mS + 2 * j + 1 = mS - 1 + (1 + 2 * j + 1) := by omega
  rw [e, copiedSlice_getElem?_mid mS (1 + 2 * j + 1) n hm (by omega),
    List.getElem?_eq_getElem (by rw [length_wrappedFlat]; omega),
    SliceCount.wrappedFlat_getElem_D n j h (by rw [length_wrappedFlat]; omega)]

/-- The wrapped trailing `D` (the first letter of the `D`-stretch block). -/
theorem copiedSlice_getElem?_sufD (mS n : ℕ) (hm : 1 ≤ mS) :
    (copiedSlice mS n)[mS + 2 * n]? = some D := by
  have e : mS + 2 * n = mS - 1 + (1 + 2 * n) := by omega
  rw [e, copiedSlice_getElem?_mid mS (1 + 2 * n) n hm (by omega),
    show (1 + 2 * n) = 2 * n + 1 from by ring,
    List.getElem?_eq_getElem (by rw [length_wrappedFlat]; omega),
    SliceCount.wrappedFlat_getElem_last n (by rw [length_wrappedFlat]; omega)]

/-! ## Stability: pinned positions do not see the slice grow -/

/-- A summand at a middle position `mS − 1 + x` is stable across slice sizes
containing the pin (the fibred `summand_eval_slice_stable`). -/
theorem summand_copied_mid_stable {k : ℕ} (s : Summand Step d k)
    (mS x n n' : ℕ) (hm : 1 ≤ mS) (hn : x + 1 ≤ 1 + 2 * n)
    (hn' : x + 1 ≤ 1 + 2 * n') :
    s.eval (copiedSlice mS n) (fun _ => mS - 1 + x)
      = s.eval (copiedSlice mS n') (fun _ => mS - 1 + x) := by
  apply SliceRankAtom.summand_eval_const_prefix_stable
  have e : mS - 1 + x + 1 = mS - 1 + (x + 1) := by omega
  rw [e, copiedSlice_take_mid mS (x + 1) n hm (by omega),
    copiedSlice_take_mid mS (x + 1) n' hm (by omega),
    SliceFamilyRank.wrappedFlat_take_stable (x + 1) n n' hn hn']

/-- A summand at a prefix-stretch position is constant in `n`. -/
theorem summand_copied_pref_stable {k : ℕ} (s : Summand Step d k)
    (mS q n n' : ℕ) (hm : 1 ≤ mS) (hq : q + 1 ≤ mS) :
    s.eval (copiedSlice mS n) (fun _ => q)
      = s.eval (copiedSlice mS n') (fun _ => q) := by
  apply SliceRankAtom.summand_eval_const_prefix_stable
  rw [copiedSlice_take_U mS (q + 1) n hm hq, copiedSlice_take_U mS (q + 1) n' hm hq]

/-! ## The copied block families at `q₁ := δ^*(q0, U^mS)` -/

/-- Copied block prefix-rank reduces to the `pre := U^mS` one-loop family. -/
theorem prefixRank_copied_blockU (A : RankSource Step d) (mS j n : ℕ)
    (hm : 1 ≤ mS) (h : j ≤ n) :
    A.prefixRank (copiedSlice mS n) (mS + 2 * j)
      = A.prefixRank (List.replicate mS U ++ (List.replicate j [U, D]).flatten)
          (List.replicate mS U ++ (List.replicate j [U, D]).flatten).length := by
  have hlen : (List.replicate mS U
      ++ (List.replicate j [U, D]).flatten).length = mS + 2 * j := by
    rw [List.length_append, List.length_replicate,
      SliceWords.length_flatten_replicate]
    simp only [List.length_cons, List.length_nil]
    omega
  have htake : (copiedSlice mS n).take (mS + 2 * j)
      = (List.replicate mS U
          ++ (List.replicate j [U, D]).flatten).take (mS + 2 * j) := by
    rw [copiedSlice_take_block mS j n hm h, List.take_of_length_le hlen.le]
  rw [SliceRankAtom.prefixRank_prefix_stable A _ _ (mS + 2 * j) htake, hlen]

/-- The `pre := U^mS` one-loop prefix-rank family is `RankAffine` — the
pre-blocks engine consumed verbatim at the copied prefix. -/
theorem prefixRank_copied_blockU_rankAffine (A : RankSource Step d) (mS : ℕ) :
    RankAffine (fun j => A.prefixRank
      (List.replicate mS U ++ (List.replicate j [U, D]).flatten)
      (List.replicate mS U ++ (List.replicate j [U, D]).flatten).length) := by
  obtain ⟨m, p, P, hp, haff⟩ :=
    SliceRank.prefixRank_pre_blocks_affineOnResidues A (List.replicate mS U) [U, D]
  exact rankAffine_of_pre_blocks hp haff

/-- Copied `stateBefore` at the block-`j` `U`-position is the `j`-fold one-block
iterate from the post-prefix state. -/
theorem stateBefore_copied_block (A : RankSource Step d) (mS j n : ℕ)
    (hm : 1 ≤ mS) (h : j ≤ n) :
    A.stateBefore (copiedSlice mS n) (mS + 2 * j)
      = (fun q => List.foldl A.δ q [U, D])^[j]
          (List.foldl A.δ A.q0 (List.replicate mS U)) := by
  unfold RankSource.stateBefore
  rw [copiedSlice_take_block mS j n hm h, List.foldl_append,
    SliceMSO.foldl_replicate_flatten]

/-- The copied block-`U` summand, in engine form. -/
theorem summand_copied_block_eq {k : ℕ} (s : Summand Step d k) (mS j : ℕ)
    (hm : 1 ≤ mS) :
    s.eval (copiedSlice mS (j + 1)) (fun _ => mS + 2 * j) =
      s.coeff • (s.A.prefixRank
          (List.replicate mS U ++ (List.replicate j [U, D]).flatten)
          (List.replicate mS U ++ (List.replicate j [U, D]).flatten).length)
        + s.β ((fun q => List.foldl s.A.δ q [U, D])^[j]
            (List.foldl s.A.δ s.A.q0 (List.replicate mS U))) U := by
  have hget : (copiedSlice mS (j + 1))[mS + 2 * j]? = some U :=
    copiedSlice_getElem?_blockU mS j (j + 1) hm (by omega)
  unfold Summand.eval
  rw [prefixRank_copied_blockU s.A mS j (j + 1) hm (by omega),
    stateBefore_copied_block s.A mS j (j + 1) hm (by omega)]
  funext c
  rw [hget]
  simp [smul_eq_mul]

/-- The copied block-`U` summand family is `RankAffine` in `j`. -/
theorem summand_copied_block_rankAffine {k : ℕ} (s : Summand Step d k)
    (mS : ℕ) (hm : 1 ≤ mS) :
    RankAffine (fun j => s.eval (copiedSlice mS (j + 1)) (fun _ => mS + 2 * j)) := by
  have := s.A.fintypeQ
  refine RankAffine.congr (fun j => (summand_copied_block_eq s mS j hm).symm) ?_
  exact (RankAffine.smul s.coeff (prefixRank_copied_blockU_rankAffine s.A mS)).add
    (rankAffine_of_iterate (fun q => List.foldl s.A.δ q [U, D])
      (List.foldl s.A.δ s.A.q0 (List.replicate mS U)) (fun q => s.β q U))

/-- The copied block-`D` summand, in engine form. -/
theorem summand_copied_blockD_eq {k : ℕ} (s : Summand Step d k) (mS j : ℕ)
    (hm : 1 ≤ mS) :
    s.eval (copiedSlice mS (j + 1)) (fun _ => mS + 2 * j + 1) =
      s.coeff • (s.A.prefixRank
            (List.replicate mS U ++ (List.replicate j [U, D]).flatten)
            (List.replicate mS U ++ (List.replicate j [U, D]).flatten).length
          + s.A.ω ((fun q => List.foldl s.A.δ q [U, D])^[j]
              (List.foldl s.A.δ s.A.q0 (List.replicate mS U))) U)
        + s.β (s.A.δ ((fun q => List.foldl s.A.δ q [U, D])^[j]
            (List.foldl s.A.δ s.A.q0 (List.replicate mS U))) U) D := by
  have hlenU : mS + 2 * j < (copiedSlice mS (j + 1)).length := by
    rw [length_copiedSlice]
    omega
  have hgetU? : (copiedSlice mS (j + 1))[mS + 2 * j]? = some U :=
    copiedSlice_getElem?_blockU mS j (j + 1) hm (by omega)
  have hgetU : (copiedSlice mS (j + 1))[mS + 2 * j] = U := by
    rw [List.getElem?_eq_getElem hlenU] at hgetU?
    exact Option.some.inj hgetU?
  have hgetD? : (copiedSlice mS (j + 1))[mS + 2 * j + 1]? = some D :=
    copiedSlice_getElem?_blockD mS j (j + 1) hm (by omega)
  have hpref : s.A.prefixRank (copiedSlice mS (j + 1)) (mS + 2 * j + 1) =
      s.A.prefixRank (List.replicate mS U ++ (List.replicate j [U, D]).flatten)
          (List.replicate mS U ++ (List.replicate j [U, D]).flatten).length
        + s.A.ω ((fun q => List.foldl s.A.δ q [U, D])^[j]
            (List.foldl s.A.δ s.A.q0 (List.replicate mS U))) U := by
    rw [SliceRankAtom.prefixRank_succ s.A _ (mS + 2 * j) hgetU?,
      prefixRank_copied_blockU s.A mS j (j + 1) hm (by omega),
      stateBefore_copied_block s.A mS j (j + 1) hm (by omega)]
  have hstate : s.A.stateBefore (copiedSlice mS (j + 1)) (mS + 2 * j + 1) =
      s.A.δ ((fun q => List.foldl s.A.δ q [U, D])^[j]
        (List.foldl s.A.δ s.A.q0 (List.replicate mS U))) U := by
    rw [SliceRankAtom.stateBefore_succ s.A _ (mS + 2 * j) hlenU, hgetU,
      stateBefore_copied_block s.A mS j (j + 1) hm (by omega)]
  unfold Summand.eval
  funext c
  rw [hgetD?, Option.elim_some, hpref, hstate]
  simp [smul_eq_mul, Pi.add_apply, mul_add]

/-- The copied block-`D` summand family is `RankAffine` in `j`. -/
theorem summand_copied_blockD_rankAffine {k : ℕ} (s : Summand Step d k)
    (mS : ℕ) (hm : 1 ≤ mS) :
    RankAffine (fun j => s.eval (copiedSlice mS (j + 1))
      (fun _ => mS + 2 * j + 1)) := by
  have := s.A.fintypeQ
  refine RankAffine.congr (fun j => (summand_copied_blockD_eq s mS j hm).symm) ?_
  refine (RankAffine.smul s.coeff
    ((prefixRank_copied_blockU_rankAffine s.A mS).add ?_)).add ?_
  · exact rankAffine_of_iterate (fun q => List.foldl s.A.δ q [U, D])
      (List.foldl s.A.δ s.A.q0 (List.replicate mS U)) (fun q => s.A.ω q U)
  · exact rankAffine_of_iterate (fun q => List.foldl s.A.δ q [U, D])
      (List.foldl s.A.δ s.A.q0 (List.replicate mS U))
      (fun q => s.β (s.A.δ q U) D)

/-- The copied suf summand (the wrapped trailing `D` at `mS + 2n`), in engine
form. -/
theorem summand_copied_suf_eq {k : ℕ} (s : Summand Step d k) (mS n : ℕ)
    (hm : 1 ≤ mS) :
    s.eval (copiedSlice mS n) (fun _ => mS + 2 * n) =
      s.coeff • (s.A.prefixRank
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten)
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten).length)
        + s.β ((fun q => List.foldl s.A.δ q [U, D])^[n]
            (List.foldl s.A.δ s.A.q0 (List.replicate mS U))) D := by
  have hget : (copiedSlice mS n)[mS + 2 * n]? = some D :=
    copiedSlice_getElem?_sufD mS n hm
  unfold Summand.eval
  rw [prefixRank_copied_blockU s.A mS n n hm le_rfl,
    stateBefore_copied_block s.A mS n n hm le_rfl]
  funext c
  rw [hget]
  simp [smul_eq_mul]

/-- The copied suf summand family is `RankAffine` in `n`. -/
theorem summand_copied_suf_rankAffine {k : ℕ} (s : Summand Step d k)
    (mS : ℕ) (hm : 1 ≤ mS) :
    RankAffine (fun n => s.eval (copiedSlice mS n) (fun _ => mS + 2 * n)) := by
  have := s.A.fintypeQ
  refine RankAffine.congr (fun n => (summand_copied_suf_eq s mS n hm).symm) ?_
  exact (RankAffine.smul s.coeff (prefixRank_copied_blockU_rankAffine s.A mS)).add
    (rankAffine_of_iterate (fun q => List.foldl s.A.δ q [U, D])
      (List.foldl s.A.δ s.A.q0 (List.replicate mS U)) (fun q => s.β q D))

/-! ## The suffix-stretch family (the one new piece of mathematics) -/

/-- **The tail engine**: the prefix-rank of `pre ++ loop^n ++ tail` over its
whole length is `RankAffine` in `n` — split the fold after the loops; the tail
correction is a bounded function of the post-loop state iterate. -/
theorem prefixRank_pre_blocks_tail_rankAffine (A : RankSource Step d)
    (pre loop tail : List Step) :
    RankAffine (fun n => A.prefixRank
      (pre ++ (List.replicate n loop).flatten ++ tail)
      (pre ++ (List.replicate n loop).flatten ++ tail).length) := by
  have : Fintype A.Q := A.fintypeQ
  have hsnd : ∀ z : A.Q × (Fin d → ℤ),
      (List.foldl (SliceRank.rankStep A) z tail).2
        = z.2 + (List.foldl (SliceRank.rankStep A) (z.1, 0) tail).2 := by
    rintro ⟨q, acc⟩
    exact SliceRank.rankStep_snd_add A q acc tail
  have hval : ∀ n, A.prefixRank
      (pre ++ (List.replicate n loop).flatten ++ tail)
      (pre ++ (List.replicate n loop).flatten ++ tail).length
      = A.prefixRank (pre ++ (List.replicate n loop).flatten)
          (pre ++ (List.replicate n loop).flatten).length
        + (List.foldl (SliceRank.rankStep A)
            ((fun q => List.foldl A.δ q loop)^[n] (List.foldl A.δ A.q0 pre), 0)
            tail).2 := by
    intro n
    have hY1 : (List.foldl (SliceRank.rankStep A) (A.q0, 0)
        (pre ++ (List.replicate n loop).flatten)).1
        = (fun q => List.foldl A.δ q loop)^[n] (List.foldl A.δ A.q0 pre) := by
      rw [SliceRank.rankStep_fst, List.foldl_append,
        SliceMSO.foldl_replicate_flatten]
    rw [SliceRank.prefixRank_eq_foldl, SliceRank.prefixRank_eq_foldl,
      List.foldl_append, hsnd, hY1]
  refine RankAffine.congr (fun n => (hval n).symm) (RankAffine.add ?_ ?_)
  · obtain ⟨m, p, P, hp, haff⟩ :=
      SliceRank.prefixRank_pre_blocks_affineOnResidues A pre loop
    exact rankAffine_of_pre_blocks hp haff
  · exact rankAffine_of_iterate (fun q => List.foldl A.δ q loop)
      (List.foldl A.δ A.q0 pre)
      (fun q => (List.foldl (SliceRank.rankStep A) (q, 0) tail).2)

/-- The suffix-stretch summand at `mS + 2n + 1 + l`, in engine form. -/
theorem summand_copied_sufStretch_eq {k : ℕ} (s : Summand Step d k)
    (mS l : ℕ) (hl : l < mS - 1) (n : ℕ) :
    s.eval (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l) =
      s.coeff • (s.A.prefixRank
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten
            ++ List.replicate (l + 1) D)
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten
            ++ List.replicate (l + 1) D).length)
        + s.β (List.foldl s.A.δ
            ((fun q => List.foldl s.A.δ q [U, D])^[n]
              (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
            (List.replicate (l + 1) D)) D := by
  have hm : 1 ≤ mS := by omega
  have hlenTW : (List.replicate mS U ++ (List.replicate n [U, D]).flatten
      ++ List.replicate (l + 1) D).length = mS + 2 * n + 1 + l := by
    rw [List.length_append, List.length_append, List.length_replicate,
      List.length_replicate, SliceWords.length_flatten_replicate]
    simp only [List.length_cons, List.length_nil]
    omega
  have hget : (copiedSlice mS n)[mS + 2 * n + 1 + l]? = some D :=
    copiedSlice_getElem?_tail mS l n hm hl
  have hpref : s.A.prefixRank (copiedSlice mS n) (mS + 2 * n + 1 + l)
      = s.A.prefixRank (List.replicate mS U ++ (List.replicate n [U, D]).flatten
          ++ List.replicate (l + 1) D)
        (List.replicate mS U ++ (List.replicate n [U, D]).flatten
          ++ List.replicate (l + 1) D).length := by
    have htake : (copiedSlice mS n).take (mS + 2 * n + 1 + l)
        = (List.replicate mS U ++ (List.replicate n [U, D]).flatten
            ++ List.replicate (l + 1) D).take (mS + 2 * n + 1 + l) := by
      rw [copiedSlice_take_tail mS l n hm (by omega),
        List.take_of_length_le hlenTW.le]
    rw [SliceRankAtom.prefixRank_prefix_stable s.A _ _ (mS + 2 * n + 1 + l) htake,
      hlenTW]
  have hstate : s.A.stateBefore (copiedSlice mS n) (mS + 2 * n + 1 + l)
      = List.foldl s.A.δ
          ((fun q => List.foldl s.A.δ q [U, D])^[n]
            (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
          (List.replicate (l + 1) D) := by
    unfold RankSource.stateBefore
    rw [copiedSlice_take_tail mS l n hm (by omega), List.foldl_append,
      List.foldl_append, SliceMSO.foldl_replicate_flatten]
  unfold Summand.eval
  funext c
  rw [hget, Option.elim_some, hpref, hstate]
  simp [smul_eq_mul]

/-- **The suffix-stretch summand family is `RankAffine` in `n`** (CS-4's one
new piece of mathematics, assembled from the tail engine). -/
theorem summand_copied_sufStretch_rankAffine {k : ℕ} (s : Summand Step d k)
    (mS l : ℕ) (hl : l < mS - 1) :
    RankAffine (fun n => s.eval (copiedSlice mS n)
      (fun _ => mS + 2 * n + 1 + l)) := by
  have := s.A.fintypeQ
  refine RankAffine.congr
    (fun n => (summand_copied_sufStretch_eq s mS l hl n).symm) ?_
  exact (RankAffine.smul s.coeff
      (prefixRank_pre_blocks_tail_rankAffine s.A (List.replicate mS U) [U, D]
        (List.replicate (l + 1) D))).add
    (rankAffine_of_iterate (fun q => List.foldl s.A.δ q [U, D])
      (List.foldl s.A.δ s.A.q0 (List.replicate mS U))
      (fun q => s.β (List.foldl s.A.δ q (List.replicate (l + 1) D)) D))

/-- `foldl` over a uniform run is the single-step iterate (local copy; the `CopiedSetupMS` twin imports
this file). -/
theorem foldl_replicate_iterate {Alpha : Type*} {Q : Type*} (δ : Q → Alpha → Q)
    (x : Alpha) (a : Q) (k : ℕ) :
    List.foldl δ a (List.replicate k x) = (fun q => δ q x)^[k] a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.foldl_cons, Function.iterate_succ_apply, ih]

/-- `(replicate k [x]).flatten = replicate k x` (local copy). -/
theorem flatten_replicate_singleton {Alpha : Type*} (x : Alpha) (k : ℕ) :
    (List.replicate k [x]).flatten = List.replicate k x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, ih, List.singleton_append,
      ← List.replicate_succ]

/-- **The l-DIRECTION rank recurrence of a suffix-stretch summand** (d3.3 crux): for FIXED `mS, n`, the
sufIdx-`l` summand FORMULA (`s.coeff • prefixRank(U^mS (UD)^n D^{l+1}) + β(…)`) is `RankAffine` in the
suffix depth `l`.  The l-twin of `summand_copied_sufStretch_rankAffine` (which binds `n`); strictly easier
because the prefix `U^mS (UD)^n` and the pre-state are FROZEN — only the `D^{l+1}` tail grows.  Stated on
the FORMULA (not `s.eval`, which is out of range for `l ≥ mS-1`); `summand_copied_sufStretch_eq` bridges
formula↔`s.eval` on `l < mS-1`.  PART A = growing-D-tail prefixRank; PART B = `β` over the `D`-iterate. -/
theorem sufStretch_formula_rankAffine_l {k : ℕ} (s : Summand Step d k) (mS n : ℕ) :
    RankAffine (fun l =>
      s.coeff • s.A.prefixRank
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten
            ++ List.replicate (l + 1) D).length
        + s.β (List.foldl s.A.δ
            ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
            (List.replicate (l + 1) D)) D) := by
  have := s.A.fintypeQ
  refine RankAffine.add (RankAffine.smul s.coeff ?_) ?_
  · -- PART A: prefixRank over the growing D^{l+1} tail
    have hbase : RankAffine (fun count => s.A.prefixRank
        (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate count D)
        (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate count D).length) := by
      refine RankAffine.congr (fun count => ?_)
        (prefixRank_pre_blocks_tail_rankAffine s.A
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten) [D] [])
      rw [flatten_replicate_singleton, List.append_nil]
    obtain ⟨m, p, P, hp, hbr⟩ := hbase
    refine ⟨m, p, P, hp, fun l hl => ?_⟩
    have h := hbr (l + 1) (by omega)
    rwa [show l + 1 + p = l + p + 1 from by omega] at h
  · -- PART B: the β-correction over the D-iterate
    have hbase : RankAffine (fun l' => s.β (List.foldl s.A.δ
        ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
        (List.replicate l' D)) D) := by
      refine RankAffine.congr (fun l' => ?_)
        (rankAffine_of_iterate (fun q => s.A.δ q D)
          ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
          (fun q => s.β q D))
      rw [foldl_replicate_iterate s.A.δ D]
    obtain ⟨m, p, P, hp, hbr⟩ := hbase
    refine ⟨m, p, P, hp, fun l hl => ?_⟩
    have h := hbr (l + 1) (by omega)
    rwa [show l + 1 + p = l + p + 1 from by omega] at h

/-- **The CELL rank as a function of the suffix depth `l` is `RankAffine`** (d3.3): for a cell whose
coordinate `j0` is the suffix-stretch D-atom at `sufIdx l` (position `mS+2n+1+l`) with the OTHER coords
fixed (`ī0`), there is a `RankAffine` family `F` agreeing with the actual cell rank on the valid range
`l < mS-1`.  `F` is the FORMULA extrapolation (the actual rank saturates at `l ≥ mS-1`).  Built by summing
the per-summand l-recurrences (`sufStretch_formula_rankAffine_l` for the `s.π = j0` summands, constant for
the rest) via `RankAffine.listSum`; agreement on `l < mS-1` via `rankTerm_eval_proj` +
`summand_copied_sufStretch_eq` + `Function.update`.  This `F` feeds `SliceDstarBridge.selBvec_le_member`. -/
theorem rank_cell_sufStretch_rankAffine_l (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (j0 : Fin (P.toPoly.arity c)) (mS n : ℕ) :
    ∃ F : ℕ → Fin P.d → ℤ, RankAffine F ∧
      ∀ l, l < mS - 1 → P.rank c (copiedSlice mS n)
        (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  refine ⟨fun l => κ.c0 + (κ.summands.map (fun s =>
      if s.π = j0 then
        s.coeff • s.A.prefixRank
            (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
            (List.replicate mS U ++ (List.replicate n [U, D]).flatten
              ++ List.replicate (l + 1) D).length
          + s.β (List.foldl s.A.δ
              ((fun q => List.foldl s.A.δ q [U, D])^[n]
                (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
              (List.replicate (l + 1) D)) D
      else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π)))).sum, ?_, ?_⟩
  · refine RankAffine.add (RankAffine.const _)
      (RankAffine.listSum κ.summands _ (fun s _ => ?_))
    by_cases hπ : s.π = j0
    · simp only [if_pos hπ]; exact sufStretch_formula_rankAffine_l s mS n
    · simp only [if_neg hπ]; exact RankAffine.const _
  · intro l hl
    rw [hκ (copiedSlice mS n) _, rankTerm_eval_proj]
    funext c'
    simp only [Pi.add_apply]
    rw [list_sum_pi_apply]
    refine congrArg (κ.c0 c' + ·) (congrArg List.sum (List.map_congr_left (fun s _ => ?_)))
    by_cases hπ : s.π = j0
    · rw [if_pos hπ, hπ, Function.update_self]
      exact congrFun (summand_copied_sufStretch_eq s mS l hl n) c'
    · rw [if_neg hπ, Function.update_of_ne hπ]

/-! ## The fibred per-summand region decomposition -/

/-- **One summand splits by the fibred region of its coordinate**: on the
window, its value is `Rs t + Bs n` with both parts `RankAffine` — stretch and
front/pre regions are constants, cluster regions are shifted copied block
families in `t`, back/suf/suffix-stretch regions are families in `n`. -/
theorem summand_region_decomp_fibred {B k : ℕ} (s : Summand Step d k)
    (mS : ℕ) (hm : 1 ≤ mS) (r : RegionSpecF B) (hv : r.valid mS) :
    ∃ Rs Bs : ℕ → Fin d → ℤ, RankAffine Rs ∧ RankAffine Bs ∧
      ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
        s.eval (copiedSlice mS n) (fun _ => r.posAt mS t n)
          = fun c => Rs t c + Bs n c := by
  rcases r with r | q | l
  case prefIdx =>
    -- prefix stretch: a constant
    have hq : q < mS - 1 := hv
    refine ⟨fun _ => s.eval (copiedSlice mS 0) (fun _ => q), fun _ => 0,
      RankAffine.const _, RankAffine.const _, fun t n _ _ => ?_⟩
    show s.eval (copiedSlice mS n) (fun _ => q) = _
    rw [summand_copied_pref_stable s mS q n 0 hm (by omega)]
    funext c
    simp
  case sufIdx =>
    -- suffix stretch: the D-tail family
    have hlv : l < mS - 1 := hv
    refine ⟨fun _ => 0,
      fun n => s.eval (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l),
      RankAffine.const _, summand_copied_sufStretch_rankAffine s mS l hlv,
      fun t n _ _ => ?_⟩
    show s.eval (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l) = _
    funext c
    simp
  case core =>
    rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
    · -- pre: a constant
      refine ⟨fun _ => s.eval (copiedSlice mS 0) (fun _ => mS - 1 + 0),
        fun _ => 0, RankAffine.const _, RankAffine.const _, fun t n _ _ => ?_⟩
      show s.eval (copiedSlice mS n) (fun _ => mS - 1 + 0) = _
      rw [summand_copied_mid_stable s mS 0 n 0 hm (by omega) (by omega)]
      funext c
      simp
    · -- suf: the trailing-D n-family
      refine ⟨fun _ => 0,
        fun n => s.eval (copiedSlice mS n) (fun _ => mS + 2 * n),
        RankAffine.const _, summand_copied_suf_rankAffine s mS hm,
        fun t n _ _ => ?_⟩
      have hpos : mS - 1 + (1 + 2 * n) = mS + 2 * n := by omega
      show s.eval (copiedSlice mS n) (fun _ => mS - 1 + (1 + 2 * n)) = _
      rw [hpos]
      funext c
      simp
    · -- front-pinned: constant once the slice clears the pin
      rcases e with _ | _
      · refine ⟨fun _ => s.eval (copiedSlice mS (f.val + 1))
            (fun _ => mS - 1 + (1 + 2 * f.val)),
          fun _ => 0, RankAffine.const _, RankAffine.const _,
          fun t n ht htn => ?_⟩
        have hf := f.isLt
        show s.eval (copiedSlice mS n) (fun _ => mS - 1 + (1 + 2 * f.val)) = _
        rw [summand_copied_mid_stable s mS (1 + 2 * f.val) n (f.val + 1) hm
          (by omega) (by omega)]
        funext c
        simp
      · refine ⟨fun _ => s.eval (copiedSlice mS (f.val + 1))
            (fun _ => mS - 1 + (1 + 2 * f.val + 1)),
          fun _ => 0, RankAffine.const _, RankAffine.const _,
          fun t n ht htn => ?_⟩
        have hf := f.isLt
        show s.eval (copiedSlice mS n)
          (fun _ => mS - 1 + (1 + 2 * f.val + 1)) = _
        rw [summand_copied_mid_stable s mS (1 + 2 * f.val + 1) n (f.val + 1) hm
          (by omega) (by omega)]
        funext c
        simp
    · -- back-pinned: the copied block family read at index n − (1 + l)
      rcases e with _ | _
      · refine ⟨fun _ => 0,
          fun n => s.eval (copiedSlice mS (n - (1 + l.val) + 1))
            (fun _ => mS + 2 * (n - (1 + l.val))),
          RankAffine.const _,
          rankAffine_subShift (summand_copied_block_rankAffine s mS hm)
            (1 + l.val), fun t n ht htn => ?_⟩
        have hl := l.isLt
        have harg : n - 1 - l.val = n - (1 + l.val) := by omega
        have hpos : mS - 1 + (1 + 2 * (n - (1 + l.val)))
            = mS + 2 * (n - (1 + l.val)) := by omega
        show s.eval (copiedSlice mS n)
          (fun _ => mS - 1 + (1 + 2 * (n - 1 - l.val))) = _
        rw [harg, summand_copied_mid_stable s mS (1 + 2 * (n - (1 + l.val))) n
          (n - (1 + l.val) + 1) hm (by omega) (by omega), hpos]
        funext c
        simp
      · refine ⟨fun _ => 0,
          fun n => s.eval (copiedSlice mS (n - (1 + l.val) + 1))
            (fun _ => mS + 2 * (n - (1 + l.val)) + 1),
          RankAffine.const _,
          rankAffine_subShift (summand_copied_blockD_rankAffine s mS hm)
            (1 + l.val), fun t n ht htn => ?_⟩
        have hl := l.isLt
        have harg : n - 1 - l.val = n - (1 + l.val) := by omega
        have hpos : mS - 1 + (1 + 2 * (n - (1 + l.val)) + 1)
            = mS + 2 * (n - (1 + l.val)) + 1 := by omega
        show s.eval (copiedSlice mS n)
          (fun _ => mS - 1 + (1 + 2 * (n - 1 - l.val) + 1)) = _
        rw [harg, summand_copied_mid_stable s mS
          (1 + 2 * (n - (1 + l.val)) + 1) n (n - (1 + l.val) + 1) hm
          (by omega) (by omega), hpos]
        funext c
        simp
    · -- cluster: the copied block family shifted to base t
      rcases e with _ | _
      · refine ⟨fun t => s.eval (copiedSlice mS (t + δ.val + 1))
            (fun _ => mS + 2 * (t + δ.val)),
          fun _ => 0,
          rankAffine_shift (summand_copied_block_rankAffine s mS hm) δ.val,
          RankAffine.const _, fun t n ht htn => ?_⟩
        have hδ := δ.isLt
        have hpos : mS - 1 + (1 + 2 * (t + δ.val)) = mS + 2 * (t + δ.val) := by
          omega
        show s.eval (copiedSlice mS n)
          (fun _ => mS - 1 + (1 + 2 * (t + δ.val))) = _
        rw [summand_copied_mid_stable s mS (1 + 2 * (t + δ.val)) n
          (t + δ.val + 1) hm (by omega) (by omega), hpos]
        funext c
        simp
      · refine ⟨fun t => s.eval (copiedSlice mS (t + δ.val + 1))
            (fun _ => mS + 2 * (t + δ.val) + 1),
          fun _ => 0,
          rankAffine_shift (summand_copied_blockD_rankAffine s mS hm) δ.val,
          RankAffine.const _, fun t n ht htn => ?_⟩
        have hδ := δ.isLt
        have hpos : mS - 1 + (1 + 2 * (t + δ.val) + 1)
            = mS + 2 * (t + δ.val) + 1 := by omega
        show s.eval (copiedSlice mS n)
          (fun _ => mS - 1 + (1 + 2 * (t + δ.val) + 1)) = _
        rw [summand_copied_mid_stable s mS (1 + 2 * (t + δ.val) + 1) n
          (t + δ.val + 1) hm (by omega) (by omega), hpos]
        funext c
        simp

/-! ## The fibred per-cell rank decomposition -/

/-- The fibred rank-term split `R(t) + B(n)` on a cell. -/
theorem rankTerm_cell_decomp_fibred {B k : ℕ} (κ : RankTerm Step d k)
    (mS : ℕ) (hm : 1 ≤ mS) (r : Fin k → RegionSpecF B)
    (hv : ∀ i, (r i).valid mS) :
    ∃ R Bn : ℕ → Fin d → ℤ, RankAffine R ∧ RankAffine Bn ∧
      ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
        κ.eval (copiedSlice mS n) (fun i => (r i).posAt mS t n)
          = fun c => R t c + Bn n c := by
  have hdec := fun s : Summand Step d k =>
    summand_region_decomp_fibred s mS hm (r s.π) (hv s.π)
  choose Rs Bs hRA hBA heq using hdec
  refine ⟨fun t => κ.c0 + (κ.summands.map (fun s => Rs s t)).sum,
    fun n => (κ.summands.map (fun s => Bs s n)).sum,
    (RankAffine.const κ.c0).add (RankAffine.listSum _ _ (fun s _ => hRA s)),
    RankAffine.listSum _ _ (fun s _ => hBA s), ?_⟩
  intro t n ht htn
  rw [rankTerm_eval_proj]
  funext c
  have hsummand : ∀ s ∈ κ.summands,
      s.eval (copiedSlice mS n)
        (fun _ => (fun i => (r i).posAt mS t n) s.π) c
        = Rs s t c + Bs s n c := by
    intro s _
    rw [heq s t n ht htn]
  calc κ.c0 c + (κ.summands.map (fun s =>
        s.eval (copiedSlice mS n)
          (fun _ => (fun i => (r i).posAt mS t n) s.π) c)).sum
      = κ.c0 c + (κ.summands.map (fun s => Rs s t c + Bs s n c)).sum := by
        rw [congrArg List.sum (List.map_congr_left hsummand)]
    _ = κ.c0 c + ((κ.summands.map (fun s => Rs s t c)).sum
          + (κ.summands.map (fun s => Bs s n c)).sum) := by
        rw [list_sum_map_add]
    _ = (κ.c0 c + ((κ.summands.map (fun s => Rs s t)).sum) c)
          + ((κ.summands.map (fun s => Bs s n)).sum) c := by
        rw [list_sum_pi_apply, list_sum_pi_apply]
        ring

/-- **The fibred family rank shape** (Stage E capstone): the rank of the atom
a valid fibred cell describes splits as `R(t) + B(n)` on the window, with both
parts `RankAffine` (`mS`-parameterised families). -/
theorem rank_cell_decomp_fibred {B : ℕ} (P : WRP.Presentation Step Step)
    (c : Fin P.toPoly.K) (mS : ℕ) (hm : 1 ≤ mS)
    (r : Fin (P.toPoly.arity c) → RegionSpecF B)
    (hv : ∀ i, (r i).valid mS) :
    ∃ R Bn : ℕ → Fin P.d → ℤ, RankAffine R ∧ RankAffine Bn ∧
      ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
        P.rank c (copiedSlice mS n) (fun i => (r i).posAt mS t n)
          = fun i => R t i + Bn n i := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  obtain ⟨R, Bn, hR, hBn, heq⟩ := rankTerm_cell_decomp_fibred κ mS hm r hv
  exact ⟨R, Bn, hR, hBn, fun t n ht htn => by rw [hκ, heq t n ht htn]⟩

/-! ## The per-`mS` explicit descriptor enumerations (CS-4 freeze) -/

/-- The valid fibred descriptors at boundary width `mS`, as an explicit
`Finset` (deliberately NOT a `Fintype` instance). -/
def regionSpecFs (B mS : ℕ) : Finset (RegionSpecF B) :=
  (Finset.univ.image RegionSpecF.core)
    ∪ ((Finset.range (mS - 1)).image RegionSpecF.prefIdx)
    ∪ ((Finset.range (mS - 1)).image RegionSpecF.sufIdx)

theorem mem_regionSpecFs {B : ℕ} (mS : ℕ) (r : RegionSpecF B) :
    r ∈ regionSpecFs B mS ↔ r.valid mS := by
  unfold regionSpecFs
  rcases r with r | q | l <;>
    simp [RegionSpecF.valid, Finset.mem_union, Finset.mem_image]

/-- The per-`mS` explicit tuple enumeration (never a `Fintype` instance, so it
can never leak into a `Finset.univ` period product). -/
def regionTuplesF (B k mS : ℕ) : Finset (Fin k → RegionSpecF B) :=
  Fintype.piFinset (fun _ => regionSpecFs B mS)

theorem mem_regionTuplesF {B k mS : ℕ} (r : Fin k → RegionSpecF B) :
    r ∈ regionTuplesF B k mS ↔ ∀ i, (r i).valid mS := by
  unfold regionTuplesF
  rw [Fintype.mem_piFinset]
  exact forall_congr' (fun i => mem_regionSpecFs mS (r i))

end CopiedRank
