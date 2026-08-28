/-
# The WRP rank of a slice atom is `RankAffine` in its loop-index — all regions (fas piece (a′))

`SliceRankBlock` did the block-`U` position `1+2j`.  This file adds the analogues for
the other three position types of `W_n = U(UD)^n D`, completing the rank ingredient
of the `fas` discharge:

  * **block-`D`** position `1+2j+1` (the loop-block's down-step), `RankAffine` in `j`;
  * the **pre** atom `p=0` (the leading `U`): its rank is *constant* in `n`
    (`prefixRank` at `0` is `0`, `stateBefore` is `q0`), hence `RankAffine`;
  * the **suf** atom `p=2n+1` (the trailing `D`): its prefix-rank is the block-`U`
    prefix-rank at `j=n` and its `β` reads `D` from `blockState^[n] q₁`, so it is
    `RankAffine` in `n`.

The recipe is the same as block-`U`: reduce the summand to
`coeff·(one-loop prefix-rank) + (bounded β/ω of a finite-state iterate)`, both
`RankAffine`, then assemble `c₀ + Σ summands`.  Works for any arity.  Axiom-clean.
-/
import RequestProject.SliceRankBlock

open WRP Step

namespace SliceRankAtom

variable {d : ℕ}

/-! ### Generic prefix/state successor steps -/

/-- `stateBefore` advances by one letter: `stateBefore w (i+1) = δ (stateBefore w i) (w[i])`. -/
theorem stateBefore_succ {Alpha : Type*} (A : RankSource Alpha d) (w : List Alpha) (i : ℕ)
    (hi : i < w.length) :
    A.stateBefore w (i + 1) = A.δ (A.stateBefore w i) (w[i]) := by
  unfold RankSource.stateBefore
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
  rfl

/-- `prefixRank` advances by one letter: reading `w[i] = a` adds `ω (stateBefore w i) a`. -/
theorem prefixRank_succ {Alpha : Type*} (A : RankSource Alpha d) (w : List Alpha) (i : ℕ)
    {a : Alpha} (hi : w[i]? = some a) :
    A.prefixRank w (i + 1) = A.prefixRank w i + A.ω (A.stateBefore w i) a := by
  funext c
  simp only [RankSource.prefixRank, Pi.add_apply]
  rw [Finset.sum_range_succ, hi, Option.elim_some]

/-! ### Generic `RankTerm` assembly (any per-index word/position) -/

/-- The block-`U` assembly, generalised over an arbitrary per-index word `F j` and
position `q j`: if every summand is `RankAffine` in `j` at `(F j, ·↦q j)`, so is the
whole rank term. -/
theorem rankTerm_eval_rankAffine {k : ℕ} (κ : RankTerm Step d k)
    (F : ℕ → List Step) (q : ℕ → ℕ)
    (h : ∀ s : Summand Step d k, RankAffine (fun j => s.eval (F j) (fun _ => q j))) :
    RankAffine (fun j => κ.eval (F j) (fun _ => q j)) := by
  refine RankAffine.congr (fun j => ?_)
    ((RankAffine.const κ.c0).add (RankAffine.listSum κ.summands
      (fun s j => s.eval (F j) (fun _ => q j)) (fun s _ => h s)))
  unfold RankTerm.eval
  funext c
  have key : (κ.summands.map (fun s => s.eval (F j) (fun _ => q j))).sum c =
      (κ.summands.map (fun s => s.eval (F j) (fun _ => q j) c)).sum := by
    induction κ.summands with
    | nil => rfl
    | cons s t ih => simp only [List.map_cons, List.sum_cons, Pi.add_apply, ih]
  rw [Pi.add_apply, key]

/-! ### block-`D` position `1+2j+1` -/

/-- A summand at the block-`j` `D`-position, reduced to the block-`U` prefix-rank plus
one forward `ω`-step (reading the block's `U`) and the bounded `β` reading the `D`. -/
theorem summand_blockD_eq {k : ℕ} (s : Summand Step d k) (j : ℕ) :
    s.eval (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1) =
      s.coeff • (s.A.prefixRank ([U] ++ (List.replicate j [U, D]).flatten)
            (([U] ++ (List.replicate j [U, D]).flatten).length)
          + s.A.ω ((fun q => List.foldl s.A.δ q [U, D])^[j] (s.A.δ s.A.q0 U)) U)
        + s.β (s.A.δ ((fun q => List.foldl s.A.δ q [U, D])^[j] (s.A.δ s.A.q0 U)) U) D := by
  have hlen : 1 + 2 * j < (wrappedFlat (j + 1)).length := by rw [length_wrappedFlat]; omega
  have hlen1 : 1 + 2 * j + 1 < (wrappedFlat (j + 1)).length := by rw [length_wrappedFlat]; omega
  have hgetU : (wrappedFlat (j + 1))[1 + 2 * j] = U :=
    SliceCount.wrappedFlat_getElem_U (j + 1) j (by omega) hlen
  have hgetU? : (wrappedFlat (j + 1))[1 + 2 * j]? = some U := by
    rw [List.getElem?_eq_getElem hlen, hgetU]
  have hgetD? : (wrappedFlat (j + 1))[1 + 2 * j + 1]? = some D := by
    rw [List.getElem?_eq_getElem hlen1, SliceCount.wrappedFlat_getElem_D (j + 1) j (by omega) hlen1]
  have hpref : s.A.prefixRank (wrappedFlat (j + 1)) (1 + 2 * j + 1) =
      s.A.prefixRank ([U] ++ (List.replicate j [U, D]).flatten)
          (([U] ++ (List.replicate j [U, D]).flatten).length)
        + s.A.ω ((fun q => List.foldl s.A.δ q [U, D])^[j] (s.A.δ s.A.q0 U)) U := by
    rw [prefixRank_succ s.A (wrappedFlat (j + 1)) (1 + 2 * j) hgetU?,
      prefixRank_slice_blockU s.A (j + 1) j (by omega),
      stateBefore_block s.A (j + 1) j (by omega)]
  have hstate : s.A.stateBefore (wrappedFlat (j + 1)) (1 + 2 * j + 1) =
      s.A.δ ((fun q => List.foldl s.A.δ q [U, D])^[j] (s.A.δ s.A.q0 U)) U := by
    rw [stateBefore_succ s.A (wrappedFlat (j + 1)) (1 + 2 * j) hlen, hgetU,
      stateBefore_block s.A (j + 1) j (by omega)]
  unfold Summand.eval
  funext c
  rw [hgetD?, Option.elim_some, hpref, hstate]
  simp [smul_eq_mul, Pi.add_apply, mul_add]

/-- Each block-`D` summand is `RankAffine` in `j`. -/
theorem summand_blockD_rankAffine {k : ℕ} (s : Summand Step d k) :
    RankAffine (fun j => s.eval (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1)) := by
  have := s.A.fintypeQ
  refine RankAffine.congr (fun j => (summand_blockD_eq s j).symm) ?_
  refine (RankAffine.smul s.coeff ((prefixRank_blockU_rankAffine s.A).add ?_)).add ?_
  · exact rankAffine_of_iterate (fun q => List.foldl s.A.δ q [U, D]) (s.A.δ s.A.q0 U)
      (fun q => s.A.ω q U)
  · exact rankAffine_of_iterate (fun q => List.foldl s.A.δ q [U, D]) (s.A.δ s.A.q0 U)
      (fun q => s.β (s.A.δ q U) D)

/-- **The WRP rank of a slice block-`D`-atom is `RankAffine` in its loop-index.** -/
theorem rank_blockD_rankAffine {Gamma : Type*} (P : WRP.Presentation Step Gamma)
    (c : Fin P.toPoly.K) :
    RankAffine (fun j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1)) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  exact RankAffine.congr (fun j => (hκ _ _).symm)
    (rankTerm_eval_rankAffine κ (fun j => wrappedFlat (j + 1)) (fun j => 1 + 2 * j + 1)
      (fun s => summand_blockD_rankAffine s))

/-! ### pre atom `p = 0` (the leading `U`) -/

/-- A summand at position `0` reads nothing (`prefixRank = 0`, `stateBefore = q0`,
letter `U`), so it is the constant `β q0 U`. -/
theorem summand_pre_eq {k : ℕ} (s : Summand Step d k) (n : ℕ) :
    s.eval (wrappedFlat n) (fun _ => 0) = s.β s.A.q0 U := by
  have hb : 0 < (wrappedFlat n).length := by rw [length_wrappedFlat]; omega
  have hget? : (wrappedFlat n)[0]? = some U := by
    rw [List.getElem?_eq_getElem hb, SliceCount.wrappedFlat_getElem_zero n hb]
  unfold Summand.eval
  funext c
  rw [hget?, Option.elim_some]
  simp [RankSource.prefixRank, RankSource.stateBefore]

/-- The pre-atom rank is constant in `n`, hence `RankAffine`. -/
theorem summand_pre_rankAffine {k : ℕ} (s : Summand Step d k) :
    RankAffine (fun n => s.eval (wrappedFlat n) (fun _ => 0)) :=
  RankAffine.congr (fun n => (summand_pre_eq s n).symm) (RankAffine.const (s.β s.A.q0 U))

/-- **The WRP rank of the slice pre-atom (`p=0`) is `RankAffine` in `n` (in fact
constant).** -/
theorem rank_pre_rankAffine {Gamma : Type*} (P : WRP.Presentation Step Gamma)
    (c : Fin P.toPoly.K) :
    RankAffine (fun n => P.rank c (wrappedFlat n) (fun _ => 0)) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  exact RankAffine.congr (fun n => (hκ _ _).symm)
    (rankTerm_eval_rankAffine κ (fun n => wrappedFlat n) (fun _ => 0)
      (fun s => summand_pre_rankAffine s))

/-! ### suf atom `p = 2n+1 = 1+2n` (the trailing `D`) -/

/-- A summand at the trailing-`D` position `1+2n`: same shape as block-`U` at `j=n`,
but reading the letter `D`. -/
theorem summand_suf_eq {k : ℕ} (s : Summand Step d k) (n : ℕ) :
    s.eval (wrappedFlat n) (fun _ => 1 + 2 * n) =
      s.coeff • s.A.prefixRank ([U] ++ (List.replicate n [U, D]).flatten)
          (([U] ++ (List.replicate n [U, D]).flatten).length)
        + s.β ((fun q => List.foldl s.A.δ q [U, D])^[n] (s.A.δ s.A.q0 U)) D := by
  have hgetD? : (wrappedFlat n)[1 + 2 * n]? = some D := by
    rw [show 1 + 2 * n = 2 * n + 1 from by ring,
      List.getElem?_eq_getElem (by rw [length_wrappedFlat]; omega),
      SliceCount.wrappedFlat_getElem_last n (by rw [length_wrappedFlat]; omega)]
  unfold Summand.eval
  rw [prefixRank_slice_blockU s.A n n (le_refl n), stateBefore_block s.A n n (le_refl n)]
  funext c
  rw [hgetD?, Option.elim_some]
  simp [smul_eq_mul]

/-- Each suf summand is `RankAffine` in `n`. -/
theorem summand_suf_rankAffine {k : ℕ} (s : Summand Step d k) :
    RankAffine (fun n => s.eval (wrappedFlat n) (fun _ => 1 + 2 * n)) := by
  have := s.A.fintypeQ
  refine RankAffine.congr (fun n => (summand_suf_eq s n).symm) ?_
  exact (RankAffine.smul s.coeff (prefixRank_blockU_rankAffine s.A)).add
    (rankAffine_of_iterate (fun q => List.foldl s.A.δ q [U, D]) (s.A.δ s.A.q0 U)
      (fun q => s.β q D))

/-- **The WRP rank of the slice suf-atom (`p=2n+1`) is `RankAffine` in `n`.** -/
theorem rank_suf_rankAffine {Gamma : Type*} (P : WRP.Presentation Step Gamma)
    (c : Fin P.toPoly.K) :
    RankAffine (fun n => P.rank c (wrappedFlat n) (fun _ => 1 + 2 * n)) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  exact RankAffine.congr (fun n => (hκ _ _).symm)
    (rankTerm_eval_rankAffine κ (fun n => wrappedFlat n) (fun n => 1 + 2 * n)
      (fun s => summand_suf_rankAffine s))

end SliceRankAtom
