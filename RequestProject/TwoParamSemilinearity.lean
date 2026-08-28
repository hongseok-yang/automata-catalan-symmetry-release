/-
# Semilinearity on the two-parameter family `W_{m,n}` (`thm:two-parameter-semilinearity`)

Formalisation of **Theorem `thm:two-parameter-semilinearity`** of `paper.tex`
(§9 `sec:inverse-zeta`, subsection "The two-parameter family and its Presburger control"):

> Let `T ∈ WRP` be fixed and suppose `|T(W_{m,n})| = O(m+n)`.  Then
> `S_T = {(m, n, fas(T(W_{m,n})), tailU(T(W_{m,n}))) : m ≥ 1, n ≥ 0} ⊆ ℕ⁴`
> is semilinear.

Here `W_{m,n} = Uᵐ(UD)ⁿDᵐ` is the copied slice (`def:two-parameter-family`
— `copiedSlice` in `InverseZeta.lean`), `fas` is `firstAscent`
(`DyckPath.lean`), and `tailU` is `tailU`.

## What is proved, and the one residual hypothesis

The paper's proof has two halves.

* **Definability** (`lem:two-parameter-presburger`, paper.tex): selection,
  labelling, rank comparison and tie-order of a fixed WRP presentation are
  Presburger-definable over the family.  This half is **fully discharged** here, on top of
  the project's existing (project-agnostic) slice-definability axioms: the fas membership
  predicate "selected `U`-atom that `≺`-precedes every selected `D`-atom" and the
  total-`U` predicate are proved `IsSliceFamilySemilinear2`
  (`fasPhi_semilinear`, `selUPhi_semilinear`), via the new two-atom order comparison
  `wrpOrd2_semilinear` (parts (c) and (d) of the paper's lemma, assembled from the rank
  value-graph and MSO axioms already admitted by the repo — no new axiom).

* **Counting** (`lem:presburger-counting` in its tuple form, as applied in the
  paper's §9 proof): a semilinear `(m, n, ī)`-family with linearly bounded finite fibres has a
  **semilinear count graph** `{(m, n, #fibre)}`.  This is the `p = 2` instance of the
  admitted counting axiom `PresburgerCounting.count_graph_semilinear`, and is derived from
  it here as `twoParamCountGraph_proved`.  The main theorem
  `two_param_profile_semilinear` still takes the principle as the explicit hypothesis
  `TwoParamCountGraph`, so that the residual counting boundary is visible in its
  statement; `two_param_profile_semilinear_unconditional` discharges it.  Everything
  else — the semantic bridges `firstAscent/tailU ↔` atom counts, the growth budget, and
  the ℕ⁴ assembly — is proved.

As an **unconditional** corollary of the repo's weaker counting axiom, every row of
`S_T` is semilinear: `two_param_profile_row_semilinear` proves that for each fixed
`m ≥ 1` the set `{(fas(T(W_{m,n})), tailU(T(W_{m,n}))) : n ≥ 1}` is `IsSemilinear2` —
the two-parameter mirror of `wrp_slice_profile_semilinear` (`NoSwapWRP.lean`), which it
generalises from the row `m = 1`.

## Correspondence to the paper statement

* `S_T` is rendered as the set of `v : Fin 4 → ℕ` with
  `∃ m n out, 1 ≤ m ∧ T (copiedSlice m n) = some out ∧ v = (m, n, fas out, tailU out)`.
* The growth hypothesis `|T(W_{m,n})| = O(m+n)` is rendered as
  `∃ C, ∀ m n out, 1 ≤ m → T (copiedSlice m n) = some out → out.length ≤ C * (m+n+1)`.
* The paper computes `T(W_{m,n})` for every `m ≥ 1, n ≥ 0`, i.e. it implicitly assumes
  the family lies in `T`'s domain; this is the explicit hypothesis `hdom` (the same
  quantification-honesty point as the domain hypothesis of `thm:wrp-slice-semilinearity`
  and the `hne` hypothesis of
  `wrp_slice_profile_affine`).

No `sorry`, no new axiom.  The axioms reachable from the declarations here are a subset
of the project's standard admitted axioms.
-/
import RequestProject.CopiedTieSemilinear2
import RequestProject.CopiedDischarge
import RequestProject.SliceCountGlobal

namespace TwoParamSemilinearity

open WRP Step SliceSemilinearN MSO CopiedTieSemilinear2
open scoped Classical

/-! ## A. Small additions to the semilinear toolkit

Linear-equation sets (`w i = w j + w k` etc.) as preimages of the diagonal under
`AddMonoidHom`s, concrete-coordinate cylindrifications, and the graph-sum and
profile-assembly lemmas used to combine the two count graphs into the ℕ⁴ set. -/

/-- The diagonal `{w : Fin 2 → ℕ | w 0 = w 1}` is semilinear: it is the single linear
set `![0,0] + ℕ·{![1,1]}`. -/
theorem diag_semilinear : IsSemilinearSet {w : Fin 2 → ℕ | w 0 = w 1} := by
  have heq : {w : Fin 2 → ℕ | w 0 = w 1} = LinearSet 2 ![0, 0] {![1, 1]} := by
    ext w
    simp only [LinearSet, Set.mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨fun _ => w 0, ?_⟩
      funext i
      fin_cases i
      · simp
      · simp
        omega
    · rintro ⟨coeffs, hw⟩
      have h0 := congrFun hw 0
      have h1 := congrFun hw 1
      simp [Finset.sum_singleton] at h0 h1
      omega
  rw [heq]
  exact (repo_linearSet_isLinearSet 2 ![0, 0] {![1, 1]}).isSemilinearSet

private theorem list_sum_map_zero {d : ℕ} (A : List (Fin d)) :
    (A.map (0 : Fin d → ℕ)).sum = 0 := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [ih]

private theorem list_sum_map_add {d : ℕ} (x y : Fin d → ℕ) (A : List (Fin d)) :
    (A.map (x + y)).sum = (A.map x).sum + (A.map y).sum := by
  induction A with
  | nil => rfl
  | cons a A ih =>
      simp only [List.map_cons, List.sum_cons, ih, Pi.add_apply]
      ring

/-- Hom picking two ℕ-linear forms out of a coordinate vector: `v ↦ ![L₁ v, L₂ v]`,
for `L₁ v = Σ v (A i)`, `L₂ v = Σ v (B j)` over index lists `A`, `B`. -/
def formsHom (d : ℕ) (A B : List (Fin d)) : (Fin d → ℕ) →+ (Fin 2 → ℕ) where
  toFun v := ![(A.map v).sum, (B.map v).sum]
  map_zero' := by
    funext i
    fin_cases i <;> simp [list_sum_map_zero]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [list_sum_map_add]

/-- The linear-equation set `{v | Σ_{i ∈ A} v i = Σ_{j ∈ B} v j}` is semilinear. -/
theorem isSemilinearNd_forms_eq (d : ℕ) (A B : List (Fin d)) :
    IsSemilinearNd d {v : Fin d → ℕ | (A.map v).sum = (B.map v).sum} := by
  have hpre : IsSemilinearSet (formsHom d A B ⁻¹' {w : Fin 2 → ℕ | w 0 = w 1}) :=
    diag_semilinear.preimage (formsHom d A B)
  refine isSemilinearNd_congr ?_ (mathlib_to_isSemilinearNd d _ hpre)
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, formsHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Hom `v ↦ ![0, v i]` (for the coordinate lower bound `1 ≤ v i`). -/
private def ge1Hom (d : ℕ) (i : Fin d) : (Fin d → ℕ) →+ (Fin 2 → ℕ) where
  toFun v := ![0, v i]
  map_zero' := by funext j; fin_cases j <;> simp
  map_add' x y := by funext j; fin_cases j <;> simp

/-- The coordinate-bound set `{v | 1 ≤ v i}` is semilinear (preimage of the strict
order set under `v ↦ ![0, v i]`). -/
theorem isSemilinearNd_coord_ge1 (d : ℕ) (i : Fin d) :
    IsSemilinearNd d {v : Fin d → ℕ | 1 ≤ v i} := by
  have hpre : IsSemilinearSet (ge1Hom d i ⁻¹' {w : Fin 2 → ℕ | w 0 < w 1}) :=
    order_lt_semilinear.preimage (ge1Hom d i)
  refine isSemilinearNd_congr ?_ (mathlib_to_isSemilinearNd d _ hpre)
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, ge1Hom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- `1 ≤ mS` as a two-parameter slice family (cylindrified over the atom tuple). -/
theorem paramGe1_semilinear (k : ℕ) :
    IsSliceFamilySemilinear2 (fun mS _n (_ī : Fin k → ℕ) => 1 ≤ mS) := by
  refine isSemilinearNd_congr ?_ (isSemilinearNd_coord_ge1 (k + 2) 0)
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq]

/-! ### Concrete-index evaluation of `Fin.snoc` (for the ℕ⁵/ℕ⁴ projections) -/

private theorem snoc5_zero (v : Fin 4 → ℕ) (t : ℕ) : (Fin.snoc v t : Fin 5 → ℕ) 0 = v 0 := by
  rw [show (0 : Fin 5) = Fin.castSucc (0 : Fin 4) from rfl, Fin.snoc_castSucc]

private theorem snoc5_one (v : Fin 4 → ℕ) (t : ℕ) : (Fin.snoc v t : Fin 5 → ℕ) 1 = v 1 := by
  rw [show (1 : Fin 5) = Fin.castSucc (1 : Fin 4) from rfl, Fin.snoc_castSucc]

private theorem snoc5_two (v : Fin 4 → ℕ) (t : ℕ) : (Fin.snoc v t : Fin 5 → ℕ) 2 = v 2 := by
  rw [show (2 : Fin 5) = Fin.castSucc (2 : Fin 4) from rfl, Fin.snoc_castSucc]

private theorem snoc5_three (v : Fin 4 → ℕ) (t : ℕ) : (Fin.snoc v t : Fin 5 → ℕ) 3 = v 3 := by
  rw [show (3 : Fin 5) = Fin.castSucc (3 : Fin 4) from rfl, Fin.snoc_castSucc]

private theorem snoc5_four (v : Fin 4 → ℕ) (t : ℕ) : (Fin.snoc v t : Fin 5 → ℕ) 4 = t := by
  rw [show (4 : Fin 5) = Fin.last 4 from rfl, Fin.snoc_last]

private theorem snoc4_zero (v : Fin 3 → ℕ) (t : ℕ) : (Fin.snoc v t : Fin 4 → ℕ) 0 = v 0 := by
  rw [show (0 : Fin 4) = Fin.castSucc (0 : Fin 3) from rfl, Fin.snoc_castSucc]

private theorem snoc4_one (v : Fin 3 → ℕ) (t : ℕ) : (Fin.snoc v t : Fin 4 → ℕ) 1 = v 1 := by
  rw [show (1 : Fin 4) = Fin.castSucc (1 : Fin 3) from rfl, Fin.snoc_castSucc]

private theorem snoc4_two (v : Fin 3 → ℕ) (t : ℕ) : (Fin.snoc v t : Fin 4 → ℕ) 2 = v 2 := by
  rw [show (2 : Fin 4) = Fin.castSucc (2 : Fin 3) from rfl, Fin.snoc_castSucc]

private theorem snoc4_three (v : Fin 3 → ℕ) (t : ℕ) : (Fin.snoc v t : Fin 4 → ℕ) 3 = t := by
  rw [show (3 : Fin 4) = Fin.last 3 from rfl, Fin.snoc_last]

/-! ### Coordinate selections `Fin 3 → Fin 5` used in the assemblies -/

private def sel012 : Fin 3 → Fin 5 := fun i =>
  if i.val = 0 then 0 else if i.val = 1 then 1 else 2

private def sel013 : Fin 3 → Fin 5 := fun i =>
  if i.val = 0 then 0 else if i.val = 1 then 1 else 3

private def sel014 : Fin 3 → Fin 5 := fun i =>
  if i.val = 0 then 0 else if i.val = 1 then 1 else 4

private theorem sel012_inj : Function.Injective sel012 := by decide
private theorem sel013_inj : Function.Injective sel013 := by decide
private theorem sel014_inj : Function.Injective sel014 := by decide

private theorem sel012_eval : sel012 0 = 0 ∧ sel012 1 = 1 ∧ sel012 2 = 2 := ⟨rfl, rfl, rfl⟩
private theorem sel013_eval : sel013 0 = 0 ∧ sel013 1 = 1 ∧ sel013 2 = 3 := ⟨rfl, rfl, rfl⟩
private theorem sel014_eval : sel014 0 = 0 ∧ sel014 1 = 1 ∧ sel014 2 = 4 := ⟨rfl, rfl, rfl⟩

/-- **Sum of count graphs.**  If each `f i` (over a finite index) has a semilinear
graph `{(m, n, f i m n)}` in ℕ³, so does the pointwise sum `Σ i, f i`.  This is the
"tuple form" bookkeeping of the paper's counting step: the per-copy counts add up to
the full count. -/
theorem isSemilinearNd_graph_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℕ → ℕ)
    (hf : ∀ i ∈ s, IsSemilinearNd 3 {v : Fin 3 → ℕ | f i (v 0) (v 1) = v 2}) :
    IsSemilinearNd 3 {v : Fin 3 → ℕ | (∑ i ∈ s, f i (v 0) (v 1)) = v 2} := by
  classical
  induction s using Finset.induction with
  | empty =>
      -- `{v | 0 = v 2}` is the linear-equation set `Σ_∅ = Σ_{[2]}` reversed
      refine isSemilinearNd_congr ?_ (isSemilinearNd_forms_eq 3 [] [2])
      ext v
      simp only [Set.mem_ofPred_eq, List.map_nil, List.sum_nil, List.map_cons,
        List.sum_cons, List.sum_nil, Finset.sum_empty]
      omega
  | insert a s ha ih =>
      have hA := hf a (Finset.mem_insert_self a s)
      have hS := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      -- ℕ⁵ assembly: coordinates (m, n, total, aCount, restCount)
      have hA5 := isSemilinearNd_comap_injective sel013 sel013_inj hA
      have hS5 := isSemilinearNd_comap_injective sel014 sel014_inj hS
      have hL5 := isSemilinearNd_forms_eq 5 [2] [3, 4]
      have hM := isSemilinearNd_inter (isSemilinearNd_inter hA5 hS5) hL5
      have hP1 := isSemilinearNd_proj (d := 4) hM
      have hP2 := isSemilinearNd_proj (d := 3) hP1
      refine isSemilinearNd_congr ?_ hP2
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, sel013_eval.1, sel013_eval.2.1,
        sel013_eval.2.2, sel014_eval.1, sel014_eval.2.1, sel014_eval.2.2,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      constructor
      · rintro ⟨sA, sR, ⟨hfa, hfs⟩, hlin⟩
        rw [snoc5_zero, snoc4_zero, snoc5_one, snoc4_one, snoc5_three, snoc4_three] at hfa
        rw [snoc5_zero, snoc4_zero, snoc5_one, snoc4_one, snoc5_four] at hfs
        rw [snoc5_two, snoc4_two, snoc5_three, snoc4_three, snoc5_four] at hlin
        rw [Finset.sum_insert ha, hfa, hfs]
        omega
      · intro h
        refine ⟨f a (u 0) (u 1), ∑ i ∈ s, f i (u 0) (u 1), ⟨?_, ?_⟩, ?_⟩
        · rw [snoc5_zero, snoc4_zero, snoc5_one, snoc4_one, snoc5_three, snoc4_three]
        · rw [snoc5_zero, snoc4_zero, snoc5_one, snoc4_one, snoc5_four]
        · rw [snoc5_two, snoc4_two, snoc5_three, snoc4_three, snoc5_four]
          rw [Finset.sum_insert ha] at h
          omega

/-- **The ℕ⁴ profile assembly.**  From semilinear ℕ³ graphs of two functions
`F G : ℕ → ℕ → ℕ`, the ℕ⁴ set `{(m, n, F m n, G m n − F m n) : 1 ≤ m}` — written with
the subtraction moved to the sum side, as `G m n = v 2 + v 3` — is semilinear.
Coordinates: `v = (m, n, fas, tailU)`. -/
theorem isSemilinearNd_profile_of_graphs (F G : ℕ → ℕ → ℕ)
    (hF : IsSemilinearNd 3 {v : Fin 3 → ℕ | F (v 0) (v 1) = v 2})
    (hG : IsSemilinearNd 3 {v : Fin 3 → ℕ | G (v 0) (v 1) = v 2}) :
    IsSemilinearNd 4 {v : Fin 4 → ℕ |
      1 ≤ v 0 ∧ F (v 0) (v 1) = v 2 ∧ G (v 0) (v 1) = v 2 + v 3} := by
  -- ℕ⁵ assembly: coordinates (m, n, fas, tail, total)
  have hF5 := isSemilinearNd_comap_injective sel012 sel012_inj hF
  have hG5 := isSemilinearNd_comap_injective sel014 sel014_inj hG
  have hL5 := isSemilinearNd_forms_eq 5 [4] [2, 3]
  have hGe := isSemilinearNd_coord_ge1 5 0
  have hM := isSemilinearNd_inter (isSemilinearNd_inter (isSemilinearNd_inter hF5 hG5) hL5) hGe
  have hP := isSemilinearNd_proj (d := 4) hM
  refine isSemilinearNd_congr ?_ hP
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, sel012_eval.1, sel012_eval.2.1,
    sel012_eval.2.2, sel014_eval.1, sel014_eval.2.1, sel014_eval.2.2,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  constructor
  · rintro ⟨t, ⟨⟨hf, hg⟩, hlin⟩, hge⟩
    rw [snoc5_zero, snoc5_one, snoc5_two] at hf
    rw [snoc5_zero, snoc5_one, snoc5_four] at hg
    rw [snoc5_four, snoc5_two, snoc5_three] at hlin
    rw [snoc5_zero] at hge
    refine ⟨hge, hf, ?_⟩
    rw [hg]
    omega
  · rintro ⟨hge, hf, hg⟩
    refine ⟨G (v 0) (v 1), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [snoc5_zero, snoc5_one, snoc5_two]; exact hf
    · rw [snoc5_zero, snoc5_one, snoc5_four]
    · rw [snoc5_four, snoc5_two, snoc5_three]; omega
    · rw [snoc5_zero]; exact hge

/-! ## B. The two-atom order comparison is semilinear (`lem:two-parameter-presburger` (c), (d))

`wrpOrd` between an atom of copy `c` and an atom of copy `c'` — rank lex-comparison
first, MSO tie-order on rank ties — as a semilinear family in `(mS, n, ī ++ j̄)`.
Assembled from the admitted project-agnostic axioms: the rank value graph
(`regularRankTerm_value2_graph_semilinear`, via `rankOf_value2_c_semilinear`) for the
two rank vectors, `lexLt_decodeZ_sel` for their comparison, and the MSO bridge
(`msoDefinableRel2_semilinear`) for the tie-order `χ`. -/

section OrderComparison

variable (P : WRP.Presentation Step Step)

/-- Selector embedding the `(ī, v)`-space of copy `c`'s rank value graph into the
shared space `(ī ++ j̄) ++ v`: atom block to the `castAdd` half of the pair block,
value block to the trailing value block. -/
private def selE1 (c c' : Fin P.toPoly.K) :
    Fin (P.toPoly.arity c + (P.d + P.d)) →
      Fin ((P.toPoly.arity c + P.toPoly.arity c') + (P.d + P.d)) :=
  Fin.append
    (fun t : Fin (P.toPoly.arity c) =>
      Fin.castAdd (P.d + P.d) (Fin.castAdd (P.toPoly.arity c') t))
    (fun cc : Fin (P.d + P.d) =>
      Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') cc)

/-- Selector embedding the `(j̄, v)`-space of copy `c'`'s rank value graph into the
shared space: atom block to the `natAdd` half of the pair block, value block shared. -/
private def selE2 (c c' : Fin P.toPoly.K) :
    Fin (P.toPoly.arity c' + (P.d + P.d)) →
      Fin ((P.toPoly.arity c + P.toPoly.arity c') + (P.d + P.d)) :=
  Fin.append
    (fun t : Fin (P.toPoly.arity c') =>
      Fin.castAdd (P.d + P.d) (Fin.natAdd (P.toPoly.arity c) t))
    (fun cc : Fin (P.d + P.d) =>
      Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') cc)

private theorem selE1_injective (c c' : Fin P.toPoly.K) :
    Function.Injective (selE1 P c c') := by
  intro a b hab
  have hv : ((selE1 P c c' a : Fin _) : ℕ) = (selE1 P c c' b : ℕ) := Fin.val_eq_of_eq hab
  unfold selE1 at hv
  refine Fin.ext ?_
  induction a using Fin.addCases with
  | left ta =>
    induction b using Fin.addCases with
    | left tb =>
      rw [Fin.append_left, Fin.append_left] at hv
      simp only [Fin.val_castAdd] at hv ⊢
      omega
    | right tb =>
      rw [Fin.append_left, Fin.append_right] at hv
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
      have := ta.isLt
      omega
  | right ta =>
    induction b using Fin.addCases with
    | left tb =>
      rw [Fin.append_right, Fin.append_left] at hv
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
      have := tb.isLt
      omega
    | right tb =>
      rw [Fin.append_right, Fin.append_right] at hv
      simp only [Fin.val_natAdd] at hv ⊢
      omega

private theorem selE2_injective (c c' : Fin P.toPoly.K) :
    Function.Injective (selE2 P c c') := by
  intro a b hab
  have hv : ((selE2 P c c' a : Fin _) : ℕ) = (selE2 P c c' b : ℕ) := Fin.val_eq_of_eq hab
  unfold selE2 at hv
  refine Fin.ext ?_
  induction a using Fin.addCases with
  | left ta =>
    induction b using Fin.addCases with
    | left tb =>
      rw [Fin.append_left, Fin.append_left] at hv
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
      omega
    | right tb =>
      rw [Fin.append_left, Fin.append_right] at hv
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
      have := ta.isLt
      omega
  | right ta =>
    induction b using Fin.addCases with
    | left tb =>
      rw [Fin.append_right, Fin.append_left] at hv
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
      have := tb.isLt
      omega
    | right tb =>
      rw [Fin.append_right, Fin.append_right] at hv
      simp only [Fin.val_natAdd] at hv ⊢
      omega

private theorem selE1_castAdd (c c' : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c)) :
    selE1 P c c' (Fin.castAdd (P.d + P.d) t)
      = Fin.castAdd (P.d + P.d) (Fin.castAdd (P.toPoly.arity c') t) :=
  Fin.append_left _ _ t

private theorem selE1_natAdd (c c' : Fin P.toPoly.K) (cc : Fin (P.d + P.d)) :
    selE1 P c c' (Fin.natAdd (P.toPoly.arity c) cc)
      = Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') cc :=
  Fin.append_right _ _ cc

private theorem selE2_castAdd (c c' : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c')) :
    selE2 P c c' (Fin.castAdd (P.d + P.d) t)
      = Fin.castAdd (P.d + P.d) (Fin.natAdd (P.toPoly.arity c) t) :=
  Fin.append_left _ _ t

private theorem selE2_natAdd (c c' : Fin P.toPoly.K) (cc : Fin (P.d + P.d)) :
    selE2 P c c' (Fin.natAdd (P.toPoly.arity c') cc)
      = Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') cc :=
  Fin.append_right _ _ cc

/-- **Rank equality of two atoms is semilinear** on the two-loop slice: introduce one
shared value block `v`, pin both rank vectors to `decodeZ v` (two instances of the rank
value graph), and existentially project `v`. -/
theorem rankPairEq2_semilinear (c c' : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2
      (fun mS n (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) =>
        P.rankOf (copiedSlice mS n)
            (⟨c, fun t => ij (Fin.castAdd (P.toPoly.arity c') t)⟩ : P.toPoly.Atom)
          = P.rankOf (copiedSlice mS n)
            (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom)) := by
  have h1 := IsSliceFamilySemilinear2.comap_sel (selE1 P c c') (selE1_injective P c c')
    (rankOf_value2_c_semilinear P c)
  have h2 := IsSliceFamilySemilinear2.comap_sel (selE2 P c c') (selE2_injective P c c')
    (rankOf_value2_c_semilinear P c')
  have hex := IsSliceFamilySemilinear2.exists_extra_tuple
    (k := P.toPoly.arity c + P.toPoly.arity c') (m := P.d + P.d) (h1.and h2)
  refine isSemilinearNd_congr ?_ hex
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, selE1_castAdd, selE1_natAdd,
    selE2_castAdd, selE2_natAdd, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨bb, hb1, hb2⟩
    rw [hb1, hb2]
  · intro heq
    obtain ⟨bb, hbb⟩ := decodeZ_surjective
      (P.rankOf (copiedSlice (w 0) (w 1))
        (⟨c, fun t =>
          w (Fin.castAdd (P.toPoly.arity c') t).succ.succ⟩ : P.toPoly.Atom))
    exact ⟨bb, hbb.symm, by rw [← heq]; exact hbb.symm⟩

/-- Selector embedding the `(ī, v)`-space of copy `c`'s rank value graph into the
two-value-block space `(ī ++ j̄) ++ (v ++ v')`: value block to the first half. -/
private def selL1 (c c' : Fin P.toPoly.K) :
    Fin (P.toPoly.arity c + (P.d + P.d)) →
      Fin ((P.toPoly.arity c + P.toPoly.arity c') + ((P.d + P.d) + (P.d + P.d))) :=
  Fin.append
    (fun t : Fin (P.toPoly.arity c) =>
      Fin.castAdd ((P.d + P.d) + (P.d + P.d)) (Fin.castAdd (P.toPoly.arity c') t))
    (fun cc : Fin (P.d + P.d) =>
      Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') (Fin.castAdd (P.d + P.d) cc))

/-- Selector for copy `c'`'s rank value graph: value block to the second half. -/
private def selL2 (c c' : Fin P.toPoly.K) :
    Fin (P.toPoly.arity c' + (P.d + P.d)) →
      Fin ((P.toPoly.arity c + P.toPoly.arity c') + ((P.d + P.d) + (P.d + P.d))) :=
  Fin.append
    (fun t : Fin (P.toPoly.arity c') =>
      Fin.castAdd ((P.d + P.d) + (P.d + P.d)) (Fin.natAdd (P.toPoly.arity c) t))
    (fun cc : Fin (P.d + P.d) =>
      Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') (Fin.natAdd (P.d + P.d) cc))

private theorem selL1_injective (c c' : Fin P.toPoly.K) :
    Function.Injective (selL1 P c c') := by
  intro a b hab
  have hv : ((selL1 P c c' a : Fin _) : ℕ) = (selL1 P c c' b : ℕ) := Fin.val_eq_of_eq hab
  unfold selL1 at hv
  refine Fin.ext ?_
  induction a using Fin.addCases with
  | left ta =>
    induction b using Fin.addCases with
    | left tb =>
      rw [Fin.append_left, Fin.append_left] at hv
      simp only [Fin.val_castAdd] at hv ⊢
      omega
    | right tb =>
      rw [Fin.append_left, Fin.append_right] at hv
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
      have := ta.isLt
      omega
  | right ta =>
    induction b using Fin.addCases with
    | left tb =>
      rw [Fin.append_right, Fin.append_left] at hv
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
      have := tb.isLt
      omega
    | right tb =>
      rw [Fin.append_right, Fin.append_right] at hv
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
      omega

private theorem selL2_injective (c c' : Fin P.toPoly.K) :
    Function.Injective (selL2 P c c') := by
  intro a b hab
  have hv : ((selL2 P c c' a : Fin _) : ℕ) = (selL2 P c c' b : ℕ) := Fin.val_eq_of_eq hab
  unfold selL2 at hv
  refine Fin.ext ?_
  induction a using Fin.addCases with
  | left ta =>
    induction b using Fin.addCases with
    | left tb =>
      rw [Fin.append_left, Fin.append_left] at hv
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
      omega
    | right tb =>
      rw [Fin.append_left, Fin.append_right] at hv
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
      have := ta.isLt
      omega
  | right ta =>
    induction b using Fin.addCases with
    | left tb =>
      rw [Fin.append_right, Fin.append_left] at hv
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
      have := tb.isLt
      omega
    | right tb =>
      rw [Fin.append_right, Fin.append_right] at hv
      simp only [Fin.val_natAdd] at hv ⊢
      omega

private theorem selL1_castAdd (c c' : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c)) :
    selL1 P c c' (Fin.castAdd (P.d + P.d) t)
      = Fin.castAdd ((P.d + P.d) + (P.d + P.d)) (Fin.castAdd (P.toPoly.arity c') t) :=
  Fin.append_left _ _ t

private theorem selL1_natAdd (c c' : Fin P.toPoly.K) (cc : Fin (P.d + P.d)) :
    selL1 P c c' (Fin.natAdd (P.toPoly.arity c) cc)
      = Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') (Fin.castAdd (P.d + P.d) cc) :=
  Fin.append_right _ _ cc

private theorem selL2_castAdd (c c' : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c')) :
    selL2 P c c' (Fin.castAdd (P.d + P.d) t)
      = Fin.castAdd ((P.d + P.d) + (P.d + P.d)) (Fin.natAdd (P.toPoly.arity c) t) :=
  Fin.append_left _ _ t

private theorem selL2_natAdd (c c' : Fin P.toPoly.K) (cc : Fin (P.d + P.d)) :
    selL2 P c c' (Fin.natAdd (P.toPoly.arity c') cc)
      = Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') (Fin.natAdd (P.d + P.d) cc) :=
  Fin.append_right _ _ cc

/-- **Rank lex-comparison of two atoms is semilinear** on the two-loop slice: introduce
two value blocks `v, v'`, pin the two rank vectors to `decodeZ v`, `decodeZ v'`,
compare with `lexLt_decodeZ_sel`, and existentially project both blocks. -/
theorem rankPairLexLt2_semilinear (c c' : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2
      (fun mS n (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) =>
        WRP.lexLt
          (P.rankOf (copiedSlice mS n)
            (⟨c, fun t => ij (Fin.castAdd (P.toPoly.arity c') t)⟩ : P.toPoly.Atom))
          (P.rankOf (copiedSlice mS n)
            (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom))) := by
  have h1 := IsSliceFamilySemilinear2.comap_sel (selL1 P c c') (selL1_injective P c c')
    (rankOf_value2_c_semilinear P c)
  have h2 := IsSliceFamilySemilinear2.comap_sel (selL2 P c c') (selL2_injective P c c')
    (rankOf_value2_c_semilinear P c')
  have h3 := lexLt_decodeZ_sel (d := P.d)
    (K := (P.toPoly.arity c + P.toPoly.arity c') + ((P.d + P.d) + (P.d + P.d)))
    (fun cc => Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') (Fin.castAdd (P.d + P.d) cc))
    (fun cc => Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') (Fin.natAdd (P.d + P.d) cc))
  have hex := IsSliceFamilySemilinear2.exists_extra_tuple
    (k := P.toPoly.arity c + P.toPoly.arity c') (m := (P.d + P.d) + (P.d + P.d))
    (h1.and (h2.and h3))
  refine isSemilinearNd_congr ?_ hex
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, selL1_castAdd, selL1_natAdd,
    selL2_castAdd, selL2_natAdd, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨bb, hb1, hb2, hlex⟩
    rw [hb1, hb2]
    exact hlex
  · intro hlex
    obtain ⟨v1, hv1⟩ := decodeZ_surjective
      (P.rankOf (copiedSlice (w 0) (w 1))
        (⟨c, fun t =>
          w (Fin.castAdd (P.toPoly.arity c') t).succ.succ⟩ : P.toPoly.Atom))
    obtain ⟨v2, hv2⟩ := decodeZ_surjective
      (P.rankOf (copiedSlice (w 0) (w 1))
        (⟨c', fun t =>
          w (Fin.natAdd (P.toPoly.arity c) t).succ.succ⟩ : P.toPoly.Atom))
    have e1 : (fun cc => Fin.append v1 v2 (Fin.castAdd (P.d + P.d) cc)) = v1 :=
      funext fun cc => Fin.append_left _ _ cc
    have e2 : (fun cc => Fin.append v1 v2 (Fin.natAdd (P.d + P.d) cc)) = v2 :=
      funext fun cc => Fin.append_right _ _ cc
    refine ⟨Fin.append v1 v2, ?_, ?_, ?_⟩
    · rw [e1]
      exact hv1.symm
    · rw [e2]
      exact hv2.symm
    · rw [e1, e2, hv1, hv2]
      exact hlex

/-- **The output order `≺` between two atoms is semilinear** on the two-loop slice
(paper `lem:two-parameter-presburger`, parts (c) + (d) combined): rank lex-comparison
or (rank equality and MSO tie-order). -/
theorem wrpOrd2_semilinear (c c' : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2
      (fun mS n (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) =>
        P.wrpOrd (copiedSlice mS n)
          (⟨c, fun t => ij (Fin.castAdd (P.toPoly.arity c') t)⟩ : P.toPoly.Atom)
          (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom)) := by
  have hord := msoDefinableRel2_semilinear (P.toPoly.ordDef c c')
  refine isSemilinearNd_congr ?_
    ((rankPairLexLt2_semilinear P c c').or ((rankPairEq2_semilinear P c c').and hord))
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  exact Iff.rfl

end OrderComparison

/-! ## C. The first-ascent and total-`U` membership families

Following the paper's §9 proof with the `∀`-collapse of `SliceOutput` /
`CopiedDischarge.fasCount'`: the selected `U`-atoms counted by `fas` are exactly those
that `≺`-precede every selected `D`-atom, so no explicit first-`D` parameterisation is
needed — the universal over the opposing atom is erased by the proved
complement/projection closures.  Both families carry the row gate
`1 ≤ mS ∧ domain (copiedSlice mS n)` (so that off-family rows have empty fibres and the
growth budget applies everywhere) and the range gate `validAtom` (finite fibres). -/

section FasPredicates

variable (P : WRP.Presentation Step Step)

/-- Inner comparison of the fas predicate against an atom of copy `c'`, on the combined
tuple: if the `c'`-atom is selected, it is a `U` or the `c`-atom `≺`-precedes it. -/
theorem fasInner2_semilinear (c c' : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2
      (fun mS n (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) =>
        P.toPoly.selectedAtom (copiedSlice mS n)
            (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom) →
          (P.toPoly.labelOf (copiedSlice mS n)
              (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom) = U ∨
            P.wrpOrd (copiedSlice mS n)
              (⟨c, fun t => ij (Fin.castAdd (P.toPoly.arity c') t)⟩ : P.toPoly.Atom)
              (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom))) := by
  have hsel := IsSliceFamilySemilinear2.weaken_natAdd (j := P.toPoly.arity c)
    (selectedAtom2_semilinear P c')
  have hlab := IsSliceFamilySemilinear2.weaken_natAdd (j := P.toPoly.arity c)
    (labelClass2_semilinear P c' U)
  have hord := wrpOrd2_semilinear P c c'
  refine isSemilinearNd_congr ?_ ((hsel.not).or (hlab.or hord))
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  tauto

/-- The per-`c'` universal of the fas comparison, over the opposing atom tuple. -/
theorem fasForallBar2_semilinear (c c' : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin (P.toPoly.arity c) → ℕ) =>
      ∀ bb : Fin (P.toPoly.arity c') → ℕ,
        P.toPoly.selectedAtom (copiedSlice mS n) (⟨c', bb⟩ : P.toPoly.Atom) →
        (P.toPoly.labelOf (copiedSlice mS n) (⟨c', bb⟩ : P.toPoly.Atom) = U ∨
          P.wrpOrd (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom)
            (⟨c', bb⟩ : P.toPoly.Atom))) := by
  have h := IsSliceFamilySemilinear2.forall_extra_tuple
    (k := P.toPoly.arity c) (m := P.toPoly.arity c') (fasInner2_semilinear P c c')
  refine isSemilinearNd_congr ?_ h
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]

/-- The full `∀`-guard of the fas predicate: the `c`-atom `≺`-precedes every selected
`D`-atom (phrased as: every selected atom is a `U` or is `≺`-after it). -/
theorem fasForallB2_semilinear (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin (P.toPoly.arity c) → ℕ) =>
      ∀ b : P.toPoly.Atom,
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        (P.toPoly.labelOf (copiedSlice mS n) b = U ∨
          P.wrpOrd (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) b)) := by
  have h := IsSliceFamilySemilinear2.forall_fintype
    (fun c' => fasForallBar2_semilinear P c c')
  refine isSemilinearNd_congr ?_ h
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  constructor
  · intro h b
    obtain ⟨i, bb⟩ := b
    exact h i bb
  · intro h i bb
    exact h ⟨i, bb⟩

/-- **The fas membership family** for copy `c` (gated): `⟨c, ī⟩` is selected, labelled
`U`, and `≺`-precedes every selected `D`-atom; plus the range gate `validAtom` and the
row gate `1 ≤ mS ∧ domain`.  Its fibre count, summed over copies, is `firstAscent` of
the output (`firstAscent_eq_fasCnt`). -/
def fasPhi (c : Fin P.toPoly.K) : ℕ → ℕ → (Fin (P.toPoly.arity c) → ℕ) → Prop :=
  fun mS n ī =>
    (P.toPoly.sel c (copiedSlice mS n) ī ∧
      P.toPoly.labelOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) = U ∧
      ∀ b : P.toPoly.Atom,
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        (P.toPoly.labelOf (copiedSlice mS n) b = U ∨
          P.wrpOrd (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) b)) ∧
    (P.toPoly.validAtom (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) ∧
      (1 ≤ mS ∧ P.toPoly.domain (copiedSlice mS n)))

/-- **The total-`U` membership family** for copy `c` (gated): `⟨c, ī⟩` is selected and
labelled `U`; same gates.  Its fibre count, summed over copies, is `(out).count U`. -/
def selUPhi (c : Fin P.toPoly.K) : ℕ → ℕ → (Fin (P.toPoly.arity c) → ℕ) → Prop :=
  fun mS n ī =>
    (P.toPoly.sel c (copiedSlice mS n) ī ∧
      P.toPoly.labelOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) = U) ∧
    (P.toPoly.validAtom (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) ∧
      (1 ≤ mS ∧ P.toPoly.domain (copiedSlice mS n)))

/-- The fas family is semilinear (`lem:two-parameter-presburger`, assembled). -/
theorem fasPhi_semilinear (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fasPhi P c) :=
  ((sel2_semilinear P c).and ((labelClass2_semilinear P c U).and
      (fasForallB2_semilinear P c))).and
    ((validAtom2_semilinear P c).and
      ((paramGe1_semilinear (P.toPoly.arity c)).and
        (domain2_semilinear P (P.toPoly.arity c))))

/-- The total-`U` family is semilinear. -/
theorem selUPhi_semilinear (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (selUPhi P c) :=
  ((sel2_semilinear P c).and (labelClass2_semilinear P c U)).and
    ((validAtom2_semilinear P c).and
      ((paramGe1_semilinear (P.toPoly.arity c)).and
        (domain2_semilinear P (P.toPoly.arity c))))

theorem fasPhi_validAtom {c : Fin P.toPoly.K} {mS n : ℕ}
    {ī : Fin (P.toPoly.arity c) → ℕ} (h : fasPhi P c mS n ī) :
    ∀ i, ī i < (copiedSlice mS n).length := h.2.1

theorem selUPhi_validAtom {c : Fin P.toPoly.K} {mS n : ℕ}
    {ī : Fin (P.toPoly.arity c) → ℕ} (h : selUPhi P c mS n ī) :
    ∀ i, ī i < (copiedSlice mS n).length := h.2.1

theorem fasPhi_finite (c : Fin P.toPoly.K) (mS n : ℕ) :
    Set.Finite {ī : Fin (P.toPoly.arity c) → ℕ | fasPhi P c mS n ī} :=
  SliceSemilinearN.finite_setOf_of_support (fun n ī => fasPhi P c mS n ī) n
    (Fintype.piFinset fun _ => Finset.range (copiedSlice mS n).length)
    (fun _ī h => Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_range.mpr (fasPhi_validAtom P h i))

theorem selUPhi_finite (c : Fin P.toPoly.K) (mS n : ℕ) :
    Set.Finite {ī : Fin (P.toPoly.arity c) → ℕ | selUPhi P c mS n ī} :=
  SliceSemilinearN.finite_setOf_of_support (fun n ī => selUPhi P c mS n ī) n
    (Fintype.piFinset fun _ => Finset.range (copiedSlice mS n).length)
    (fun _ī h => Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_range.mpr (selUPhi_validAtom P h i))

/-- Every fas atom is a total-`U` atom. -/
theorem fasPhi_subset_selUPhi (c : Fin P.toPoly.K) (mS n : ℕ) :
    {ī : Fin (P.toPoly.arity c) → ℕ | fasPhi P c mS n ī}
      ⊆ {ī : Fin (P.toPoly.arity c) → ℕ | selUPhi P c mS n ī} :=
  fun _ī h => ⟨⟨h.1.1, h.1.2.1⟩, h.2⟩

end FasPredicates

/-! ## D. The two counts, their growth budget, and the semantic bridges -/

section Counts

variable (P : WRP.Presentation Step Step)

/-- The first-ascent count: fas atoms summed over all copies. -/
noncomputable def fasCnt (mS n : ℕ) : ℕ :=
  ∑ c : Fin P.toPoly.K,
    Nat.card {ī : Fin (P.toPoly.arity c) → ℕ | fasPhi P c mS n ī}

/-- The total-`U` count: selected `U`-atoms summed over all copies. -/
noncomputable def totUCnt (mS n : ℕ) : ℕ :=
  ∑ c : Fin P.toPoly.K,
    Nat.card {ī : Fin (P.toPoly.arity c) → ℕ | selUPhi P c mS n ī}

theorem fasCnt_le_totUCnt (mS n : ℕ) : fasCnt P mS n ≤ totUCnt P mS n :=
  Finset.sum_le_sum fun c _ => by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (fasPhi_subset_selUPhi P c mS n) (selUPhi_finite P c mS n)

/-- **The growth budget** for the fas family: on gated rows the fibre injects into the
selected atoms of an output of `T`, whose length the growth hypothesis bounds; off
gated rows the fibre is empty. -/
theorem fasPhi_card_le (hV : P.Valid) (T : List Step → Option (List Step)) (C : ℕ)
    (hPT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (hgrow : ∀ m n out, 1 ≤ m → T (copiedSlice m n) = some out →
      out.length ≤ C * (m + n + 1))
    (c : Fin P.toPoly.K) (mS n : ℕ) :
    Nat.card {ī : Fin (P.toPoly.arity c) → ℕ | fasPhi P c mS n ī}
      ≤ C * (mS + n + 1) := by
  by_cases hgate : 1 ≤ mS ∧ P.toPoly.domain (copiedSlice mS n)
  · obtain ⟨out, hout⟩ := CopiedDischarge.exists_isOutput' P hV (copiedSlice mS n)
    have hTout : T (copiedSlice mS n) = some out := (hPT _ _).mpr ⟨hgate.2, hout⟩
    have hlen := hgrow mS n out hgate.1 hTout
    have hfin := fasPhi_finite P c mS n
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin,
      ← Finset.length_toList hfin.toFinset]
    refine SliceGrowthCollapse.one_cluster_hcard_of_output P (copiedSlice mS n) out hout
      C (mS + n) hlen c hfin.toFinset.toList hfin.toFinset.nodup_toList
      (fun x hx => ?_)
    rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hx
    exact ⟨hx.2.1, hx.1.1⟩
  · have hempty : {ī : Fin (P.toPoly.arity c) → ℕ | fasPhi P c mS n ī} = ∅ := by
      ext ī
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hgate h.2.2
    rw [hempty]
    simp

/-- The growth budget for the total-`U` family. -/
theorem selUPhi_card_le (hV : P.Valid) (T : List Step → Option (List Step)) (C : ℕ)
    (hPT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (hgrow : ∀ m n out, 1 ≤ m → T (copiedSlice m n) = some out →
      out.length ≤ C * (m + n + 1))
    (c : Fin P.toPoly.K) (mS n : ℕ) :
    Nat.card {ī : Fin (P.toPoly.arity c) → ℕ | selUPhi P c mS n ī}
      ≤ C * (mS + n + 1) := by
  by_cases hgate : 1 ≤ mS ∧ P.toPoly.domain (copiedSlice mS n)
  · obtain ⟨out, hout⟩ := CopiedDischarge.exists_isOutput' P hV (copiedSlice mS n)
    have hTout : T (copiedSlice mS n) = some out := (hPT _ _).mpr ⟨hgate.2, hout⟩
    have hlen := hgrow mS n out hgate.1 hTout
    have hfin := selUPhi_finite P c mS n
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin,
      ← Finset.length_toList hfin.toFinset]
    refine SliceGrowthCollapse.one_cluster_hcard_of_output P (copiedSlice mS n) out hout
      C (mS + n) hlen c hfin.toFinset.toList hfin.toFinset.nodup_toList
      (fun x hx => ?_)
    rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hx
    exact ⟨hx.2.1, hx.1.1⟩
  · have hempty : {ī : Fin (P.toPoly.arity c) → ℕ | selUPhi P c mS n ī} = ∅ := by
      ext ī
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hgate h.2.2
    rw [hempty]
    simp

/-- **Semantic bridge, fas half**: on a gated row, `firstAscent` of any output equals
the fas count.  Via `CopiedDischarge.fas_eq_firstAscent_out'` (whose count this is,
re-expressed through set-fibre cardinalities). -/
theorem firstAscent_eq_fasCnt (hV : P.Valid) {mS n : ℕ} (hm : 1 ≤ mS)
    (hdomW : P.toPoly.domain (copiedSlice mS n)) {out : List Step}
    (hout : P.IsOutput (copiedSlice mS n) out) :
    firstAscent out = fasCnt P mS n := by
  classical
  rw [CopiedDischarge.fas_eq_firstAscent_out' P hV _ out hout]
  unfold CopiedDischarge.fasCount' fasCnt
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [SliceSemilinearN.natCard_setOf_eq_filter_card (fun n ī => fasPhi P c mS n ī) n
      (Fintype.piFinset fun _ => Finset.range (copiedSlice mS n).length)
      (fun ī h => Fintype.mem_piFinset.mpr fun i =>
        Finset.mem_range.mpr (fasPhi_validAtom P h i)),
    Finset.card_filter]
  refine Finset.sum_congr rfl (fun ī hī => ?_)
  have hrange : ∀ i, ī i < (copiedSlice mS n).length := fun i =>
    Finset.mem_range.mp (Fintype.mem_piFinset.mp hī i)
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨hsel, hU, hall⟩
    exact ⟨⟨hsel, hU, hall⟩, hrange, hm, hdomW⟩
  · rintro ⟨⟨hsel, hU, hall⟩, -⟩
    exact ⟨hsel, hU, hall⟩

private theorem count_U_map {α : Type*} (f : α → Step) (l : List α) :
    (l.map f).count U = l.countP fun a => decide (f a = U) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rcases hx : f x with _ | _
      · simp [List.map_cons, ih, hx]
      · simp [List.map_cons, ih, hx]

/-- **Semantic bridge, total-`U` half**: on a gated row, the `U`-count of any output
equals the total-`U` count (the output is the label list of the selected atoms). -/
theorem countU_eq_totUCnt (_hV : P.Valid) {mS n : ℕ} (hm : 1 ≤ mS)
    (hdomW : P.toPoly.domain (copiedSlice mS n)) {out : List Step}
    (hout : P.IsOutput (copiedSlice mS n) out) :
    out.count U = totUCnt P mS n := by
  classical
  obtain ⟨atoms, hnd, hmem, _hpair, hmap⟩ := hout
  rw [hmap, count_U_map (P.toPoly.labelOf (copiedSlice mS n)) atoms]
  have hcp : List.countP
        (fun a => decide (P.toPoly.labelOf (copiedSlice mS n) a = U)) atoms
      = List.countP (fun a =>
          @decide (P.toPoly.labelOf (copiedSlice mS n) a = U)
            (Classical.propDecidable _)) atoms := by
    refine List.countP_congr (fun a _ => ?_)
    simp only [decide_eq_true_eq]
  refine Eq.trans hcp (Eq.trans (CopiedDischarge.atom_countP_eq_sigmaSum' P
    (copiedSlice mS n) atoms hnd hmem
    (fun a => P.toPoly.labelOf (copiedSlice mS n) a = U)) ?_)
  unfold totUCnt
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [SliceSemilinearN.natCard_setOf_eq_filter_card (fun n ī => selUPhi P c mS n ī) n
      (Fintype.piFinset fun _ => Finset.range (copiedSlice mS n).length)
      (fun ī h => Fintype.mem_piFinset.mpr fun i =>
        Finset.mem_range.mpr (selUPhi_validAtom P h i)),
    Finset.card_filter]
  refine Finset.sum_congr rfl (fun ī hī => ?_)
  have hrange : ∀ i, ī i < (copiedSlice mS n).length := fun i =>
    Finset.mem_range.mp (Fintype.mem_piFinset.mp hī i)
  by_cases h : P.toPoly.sel c (copiedSlice mS n) ī ∧
      P.toPoly.labelOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) = U
  · rw [if_pos h, if_pos (show selUPhi P c mS n ī from ⟨⟨h.1, h.2⟩, hrange, hm, hdomW⟩)]
  · rw [if_neg h, if_neg (show ¬ selUPhi P c mS n ī from fun hc => h ⟨hc.1.1, hc.1.2⟩)]

/-- **Semantic bridge, tailU half**: `tailU` of any output is the total-`U` count minus
the fas count. -/
theorem tailU_eq_totUCnt_sub_fasCnt (hV : P.Valid) {mS n : ℕ} (hm : 1 ≤ mS)
    (hdomW : P.toPoly.domain (copiedSlice mS n)) {out : List Step}
    (hout : P.IsOutput (copiedSlice mS n) out) :
    tailU out = totUCnt P mS n - fasCnt P mS n := by
  unfold tailU
  rw [firstAscent_eq_fasCnt P hV hm hdomW hout, countU_eq_totUCnt P hV hm hdomW hout]

end Counts

/-! ## E. The counting principle and the main theorem -/

/-- **The two-parameter bounded-counting principle** — the tuple/graph form of the
paper's `lem:presburger-counting`, exactly as used in the proof of
`thm:two-parameter-semilinearity` (paper.tex): a semilinear
two-parameter atom family with finite fibres of linearly bounded size has a semilinear
count graph `{(m, n, #fibre_{m,n})} ⊆ ℕ³`.

It is proved as `twoParamCountGraph_proved`, by instantiating the admitted
`lem:presburger-counting` (`PresburgerCounting.count_graph_semilinear`) at `p = 2`,
`q = k`.  It is strictly stronger than the row-wise consequence
`SliceSemilinearN.isSliceFamilySemilinear2_count_global`, which yields only affinity of
`n ↦ #fibre` on residues of a row-uniform period, with row-dependent base/slope: joint
`(m,n)`-semilinearity genuinely does not follow from that, since
`count(m,n) = if n < f m then 1 else 0` is row- and column-wise eventually affine for
any monotone `f`, with a non-semilinear graph for non-affine `f`.  The principle is kept
as an explicit hypothesis of `two_param_profile_semilinear`, marking the counting
boundary in that statement; it is the **only** unproved ingredient there. -/
def TwoParamCountGraph : Prop :=
  ∀ (k : ℕ) (Φ : ℕ → ℕ → (Fin k → ℕ) → Prop),
    SliceSemilinearN.IsSliceFamilySemilinear2 Φ →
    (∀ mS n, Set.Finite {ī : Fin k → ℕ | Φ mS n ī}) →
    (∃ C : ℕ, ∀ mS n, Nat.card {ī : Fin k → ℕ | Φ mS n ī} ≤ C * (mS + n + 1)) →
    IsSemilinearNd 3
      {v : Fin 3 → ℕ | Nat.card {ī : Fin k → ℕ | Φ (v 0) (v 1) ī} = v 2}

/-- **The assembly half of `thm:two-parameter-semilinearity`**, factored at the exact
residual boundary (everything in this statement is proved with no counting input):
for a valid presentation realising `T`, total on the family, IF the ℕ³ graphs of the
two counts `fasCnt`/`totUCnt` are semilinear THEN the profile set `S_T` is semilinear.
The bridges identify `S_T` with `{(m, n, fasCnt, totUCnt − fasCnt) : m ≥ 1}` and the
ℕ⁵-projection assembly finishes. -/
theorem two_param_profile_semilinear_of_count_graphs
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (T : List Step → Option (List Step))
    (hPT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (hdom : ∀ m n, 1 ≤ m → ∃ out, T (copiedSlice m n) = some out)
    (hfasG : IsSemilinearNd 3 {v : Fin 3 → ℕ | fasCnt P (v 0) (v 1) = v 2})
    (htotG : IsSemilinearNd 3 {v : Fin 3 → ℕ | totUCnt P (v 0) (v 1) = v 2}) :
    IsSemilinearNd 4 {v : Fin 4 → ℕ |
      ∃ m n out, 1 ≤ m ∧ T (copiedSlice m n) = some out ∧
        v 0 = m ∧ v 1 = n ∧ v 2 = firstAscent out ∧ v 3 = tailU out} := by
  have hprof := isSemilinearNd_profile_of_graphs (fasCnt P) (totUCnt P) hfasG htotG
  refine isSemilinearNd_congr ?_ hprof
  ext v
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hge, hfas, htot⟩
    obtain ⟨out, hTout⟩ := hdom (v 0) (v 1) hge
    obtain ⟨hdomW, hout⟩ := (hPT _ _).mp hTout
    have hb1 := firstAscent_eq_fasCnt P hV hge hdomW hout
    have hb3 := tailU_eq_totUCnt_sub_fasCnt P hV hge hdomW hout
    refine ⟨v 0, v 1, out, hge, hTout, rfl, rfl, ?_, ?_⟩
    · rw [hb1]
      exact hfas.symm
    · rw [hb3]
      omega
  · rintro ⟨m, n, out, hge, hTout, rfl, rfl, hv2, hv3⟩
    obtain ⟨hdomW, hout⟩ := (hPT _ _).mp hTout
    have hb1 := firstAscent_eq_fasCnt P hV hge hdomW hout
    have hb3 := tailU_eq_totUCnt_sub_fasCnt P hV hge hdomW hout
    have hle := fasCnt_le_totUCnt P (v 0) (v 1)
    have e2 : v 2 = fasCnt P (v 0) (v 1) := hv2.trans hb1
    have e3 : v 3 = totUCnt P (v 0) (v 1) - fasCnt P (v 0) (v 1) := hv3.trans hb3
    exact ⟨hge, e2.symm, by omega⟩

/-- **Theorem `thm:two-parameter-semilinearity`** (paper.tex),
formalised relative to the two-parameter counting principle `TwoParamCountGraph`
(see its docstring: it is the paper's `lem:presburger-counting` in graph form, the one
ingredient not available from the repo's admitted axioms).

Let `T` be a WRP transduction defined on the whole two-parameter family
`W_{m,n} = copiedSlice m n` (`hdom`; the paper's implicit domain assumption) with
`|T(W_{m,n})| = O(m+n)` (`hgrow`).  Then
`S_T = {(m, n, fas (T(W_{m,n})), tailU (T(W_{m,n}))) : m ≥ 1, n ≥ 0}` is a semilinear
subset of `ℕ⁴`.

Everything except `hcount` is proved: the definability half
(`lem:two-parameter-presburger`) via `fasPhi_semilinear`/`selUPhi_semilinear`, the
semantic bridges via `firstAscent_eq_fasCnt`/`tailU_eq_totUCnt_sub_fasCnt`, the growth
budget via `fasPhi_card_le`/`selUPhi_card_le`, and the ℕ⁴ assembly via
`isSemilinearNd_graph_sum`/`isSemilinearNd_profile_of_graphs`. -/
theorem two_param_profile_semilinear
    (T : List Step → Option (List Step)) (hT : WRP.IsWRP T)
    (hcount : TwoParamCountGraph)
    (hgrow : ∃ C, ∀ m n out, 1 ≤ m → T (copiedSlice m n) = some out →
      out.length ≤ C * (m + n + 1))
    (hdom : ∀ m n, 1 ≤ m → ∃ out, T (copiedSlice m n) = some out) :
    IsSemilinearNd 4 {v : Fin 4 → ℕ |
      ∃ m n out, 1 ≤ m ∧ T (copiedSlice m n) = some out ∧
        v 0 = m ∧ v 1 = n ∧ v 2 = firstAscent out ∧ v 3 = tailU out} := by
  obtain ⟨P, hV, hPT⟩ := hT
  obtain ⟨C, hC⟩ := hgrow
  refine two_param_profile_semilinear_of_count_graphs P hV T hPT hdom ?_ ?_
  · -- the fas count graph: counting principle per copy, then summed over copies
    exact isSemilinearNd_graph_sum Finset.univ
      (fun c mS n => Nat.card {ī : Fin (P.toPoly.arity c) → ℕ | fasPhi P c mS n ī})
      (fun c _ => hcount _ _ (fasPhi_semilinear P c) (fun mS n => fasPhi_finite P c mS n)
        ⟨C, fun mS n => fasPhi_card_le P hV T C hPT hC c mS n⟩)
  · -- the total-`U` count graph, likewise
    exact isSemilinearNd_graph_sum Finset.univ
      (fun c mS n => Nat.card {ī : Fin (P.toPoly.arity c) → ℕ | selUPhi P c mS n ī})
      (fun c _ => hcount _ _ (selUPhi_semilinear P c) (fun mS n => selUPhi_finite P c mS n)
        ⟨C, fun mS n => selUPhi_card_le P hV T C hPT hC c mS n⟩)

/-! ## F. Unconditional row semilinearity from the row-wise counting consequence

What the row-wise consequence `SliceSemilinearN.isSliceFamilySemilinear2_count_global`
already gives: for every fixed `m ≥ 1`, the row
`{(fas(T(W_{m,n})), tailU(T(W_{m,n}))) : n ≥ 1}` of `S_T` is semilinear — the
two-parameter generalisation of `wrp_slice_profile_semilinear` (`NoSwapWRP.lean`),
which is the row `m = 1` (`W_{1,n} = W_n`).  The period is even uniform across `m`,
but the base/slope data is not, which is exactly why the joint statement needs
`TwoParamCountGraph`. -/

section RowTheorem

/-- Raise the threshold of a residue-wise affine description: affinity beyond `m`
implies affinity beyond any `M ≥ m` (re-aligning the residue offsets). -/
private theorem affine_shift {p : ℕ} (hp : 1 ≤ p) {f : ℕ → ℕ} {m : ℕ} (M : ℕ)
    (hm : m ≤ M) (h : ∀ j, j < p → ∃ b s : ℕ, ∀ k, f (m + j + p * k) = b + k * s) :
    ∀ j, j < p → ∃ b s : ℕ, ∀ k, f (M + j + p * k) = b + k * s := by
  intro j hj
  obtain ⟨b, s, hbs⟩ := h ((M - m + j) % p) (Nat.mod_lt _ hp)
  refine ⟨b + ((M - m + j) / p) * s, s, fun k => ?_⟩
  have harg : M + j + p * k = m + (M - m + j) % p + p * ((M - m + j) / p + k) := by
    have hdm := Nat.div_add_mod (M - m + j) p
    rw [Nat.mul_add p ((M - m + j) / p) k]
    set A := p * ((M - m + j) / p) with hA
    set B := p * k with hB
    omega
  rw [harg, hbs ((M - m + j) / p + k)]
  ring

/-- Combine residue-wise affine descriptions of `F` and of `G ≥ F` (same period, same
threshold) into a joint affine description of `(F, G − F)`: the ℕ-subtraction of two
affine rays with `F ≤ G` is again an affine ray. -/
private theorem affine_pair_sub {p : ℕ} {F G : ℕ → ℕ} {M : ℕ}
    (hFG : ∀ n, F n ≤ G n)
    (hF : ∀ j, j < p → ∃ b s : ℕ, ∀ k, F (M + j + p * k) = b + k * s)
    (hG : ∀ j, j < p → ∃ b s : ℕ, ∀ k, G (M + j + p * k) = b + k * s) :
    ∀ j, j < p → ∃ b₁ s₁ b₂ s₂ : ℕ, ∀ k,
      F (M + j + p * k) = b₁ + k * s₁ ∧
        G (M + j + p * k) - F (M + j + p * k) = b₂ + k * s₂ := by
  intro j hj
  obtain ⟨bf, sf, hf⟩ := hF j hj
  obtain ⟨bg, sg, hg⟩ := hG j hj
  have hle : ∀ k, bf + k * sf ≤ bg + k * sg := fun k => by
    rw [← hf k, ← hg k]
    exact hFG _
  have hbf : bf ≤ bg := by
    have := hle 0
    simpa using this
  have hsf : sf ≤ sg := by
    by_contra hlt
    push Not at hlt
    have hk := hle (bg + 1)
    have hmul : (bg + 1) * sg + (bg + 1) ≤ (bg + 1) * sf := by
      have h1 : sg + 1 ≤ sf := hlt
      calc (bg + 1) * sg + (bg + 1) = (bg + 1) * (sg + 1) := by ring
        _ ≤ (bg + 1) * sf := Nat.mul_le_mul_left _ h1
    have hswap1 : (bg + 1) * sf = sf * (bg + 1) := Nat.mul_comm _ _
    have hswap2 : (bg + 1) * sg = sg * (bg + 1) := Nat.mul_comm _ _
    set A := (bg + 1) * sf with hA
    set B := (bg + 1) * sg with hB
    omega
  refine ⟨bf, sf, bg - bf, sg - sf, fun k => ⟨hf k, ?_⟩⟩
  rw [hf k, hg k]
  have hks : k * sg = k * sf + k * (sg - sf) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  set A := k * sg with hA
  set B := k * sf with hB
  set Cc := k * (sg - sf) with hCc
  omega

/-- **Row semilinearity (unconditional).**  For a WRP transduction `T` with linear
growth on and totality over the two-parameter family, every row `m = mS ≥ 1` of the
first-ascent profile is semilinear:
`{(fas(T(W_{mS,n})), tailU(T(W_{mS,n}))) : n ≥ 1} ∈ IsSemilinear2`.

This is what the row-wise counting consequence
`SliceSemilinearN.isSliceFamilySemilinear2_count_global` yields, the global fibre bound
being supplied by `fasPhi_card_le` / `selUPhi_card_le`; at `mS = 1` it recovers the shape of
`wrp_slice_profile_semilinear` on the wrapped-flat slice `W_n = W_{1,n}`.  (The `n ≥ 1`
restriction matches the one-parameter kernel `isSemilinear2_of_affineInPeriod`.) -/
theorem two_param_profile_row_semilinear
    (T : List Step → Option (List Step)) (hT : WRP.IsWRP T)
    (hgrow : ∃ C, ∀ m n out, 1 ≤ m → T (copiedSlice m n) = some out →
      out.length ≤ C * (m + n + 1))
    (hdom : ∀ m n, 1 ≤ m → ∃ out, T (copiedSlice m n) = some out)
    (mS : ℕ) (hmS : 1 ≤ mS) :
    IsSemilinear2 {q : ℕ × ℕ | ∃ n, 1 ≤ n ∧ ∃ out, T (copiedSlice mS n) = some out ∧
      q = (firstAscent out, tailU out)} := by
  classical
  obtain ⟨P, hV, hPT⟩ := hT
  obtain ⟨C, hC⟩ := hgrow
  -- the counting principle, per copy, for both families
  choose pf hpf1 hpf using fun c : Fin P.toPoly.K =>
    SliceSemilinearN.isSliceFamilySemilinear2_count_global (fasPhi_semilinear P c)
      (fun mS n => fasPhi_finite P c mS n) C
      (fun mS n => fasPhi_card_le P hV T C hPT hC c mS n)
  choose pu hpu1 hpu using fun c : Fin P.toPoly.K =>
    SliceSemilinearN.isSliceFamilySemilinear2_count_global (selUPhi_semilinear P c)
      (fun mS n => selUPhi_finite P c mS n) C
      (fun mS n => selUPhi_card_le P hV T C hPT hC c mS n)
  have hp1 : 1 ≤ ∏ c : Fin P.toPoly.K, pf c := Finset.one_le_prod' fun c _ => hpf1 c
  have hp2 : 1 ≤ ∏ c : Fin P.toPoly.K, pu c := Finset.one_le_prod' fun c _ => hpu1 c
  have hp : 1 ≤ (∏ c : Fin P.toPoly.K, pf c) * ∏ c : Fin P.toPoly.K, pu c := by
    calc (1 : ℕ) = 1 * 1 := rfl
      _ ≤ _ := Nat.mul_le_mul hp1 hp2
  -- both counts are affine on residues at the common period, on this row
  have hFaff : SlicePeriodStar.AffineOnResiduesAt
      ((∏ c : Fin P.toPoly.K, pf c) * ∏ c : Fin P.toPoly.K, pu c)
      (fun n => fasCnt P mS n) := by
    unfold fasCnt
    refine SliceSemilinearN.affineOnResiduesAt_sum Finset.univ hp _ (fun c _ => ?_)
    exact (hpf c mS).of_dvd (hpf1 c)
      ((Finset.dvd_prod_of_mem _ (Finset.mem_univ c)).mul_right _) hp
  have hUaff : SlicePeriodStar.AffineOnResiduesAt
      ((∏ c : Fin P.toPoly.K, pf c) * ∏ c : Fin P.toPoly.K, pu c)
      (fun n => totUCnt P mS n) := by
    unfold totUCnt
    refine SliceSemilinearN.affineOnResiduesAt_sum Finset.univ hp _ (fun c _ => ?_)
    exact (hpu c mS).of_dvd (hpu1 c)
      ((Finset.dvd_prod_of_mem _ (Finset.mem_univ c)).mul_left _) hp
  obtain ⟨mf, hmf⟩ := hFaff
  obtain ⟨mu, hmu⟩ := hUaff
  -- align both to the common threshold `max (max mf mu) 1`
  have hshiftF := affine_shift hp (max (max mf mu) 1)
    (le_trans (le_max_left mf mu) (le_max_left _ 1)) hmf
  have hshiftU := affine_shift hp (max (max mf mu) 1)
    (le_trans (le_max_right mf mu) (le_max_left _ 1)) hmu
  have hjoint := affine_pair_sub (fun n => fasCnt_le_totUCnt P mS n) hshiftF hshiftU
  have haff : ∀ j, j < (∏ c : Fin P.toPoly.K, pf c) * ∏ c : Fin P.toPoly.K, pu c →
      ∃ b₁ s₁ b₂ s₂ : ℕ, ∀ k,
        (fun n => (fasCnt P mS n, totUCnt P mS n - fasCnt P mS n))
            (max (max mf mu) 1 + j +
              ((∏ c : Fin P.toPoly.K, pf c) * ∏ c : Fin P.toPoly.K, pu c) * k)
          = (b₁ + k * s₁, b₂ + k * s₂) := by
    intro j hj
    obtain ⟨b₁, s₁, b₂, s₂, hk⟩ := hjoint j hj
    refine ⟨b₁, s₁, b₂, s₂, fun k => ?_⟩
    rw [Prod.mk.injEq]
    exact ⟨(hk k).1, (hk k).2⟩
  have hker := SliceSemilinear.isSemilinear2_of_affineInPeriod
    (fun n => (fasCnt P mS n, totUCnt P mS n - fasCnt P mS n))
    ((∏ c : Fin P.toPoly.K, pf c) * ∏ c : Fin P.toPoly.K, pu c)
    (max (max mf mu) 1) hp (le_max_right _ 1) haff
  -- identify the row set with the graph of the count pair
  have hset : {q : ℕ × ℕ | ∃ n, 1 ≤ n ∧ ∃ out, T (copiedSlice mS n) = some out ∧
      q = (firstAscent out, tailU out)}
      = {q : ℕ × ℕ | ∃ n, 1 ≤ n ∧
          q = (fasCnt P mS n, totUCnt P mS n - fasCnt P mS n)} := by
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn, out, hTout, rfl⟩
      obtain ⟨hdomW, hout⟩ := (hPT _ _).mp hTout
      exact ⟨n, hn, by
        rw [firstAscent_eq_fasCnt P hV hmS hdomW hout,
          tailU_eq_totUCnt_sub_fasCnt P hV hmS hdomW hout]⟩
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨out, hTout⟩ := hdom mS n hmS
      obtain ⟨hdomW, hout⟩ := (hPT _ _).mp hTout
      exact ⟨n, hn, out, hTout, by
        rw [firstAscent_eq_fasCnt P hV hmS hdomW hout,
          tailU_eq_totUCnt_sub_fasCnt P hV hmS hdomW hout]⟩
  rw [hset]
  exact hker

end RowTheorem

/-! ## The counting principle, derived from `lem:presburger-counting` -/

/-- **The two-parameter counting principle, proved.**  `TwoParamCountGraph` is exactly
`SliceSemilinearN.sliceFamilyCount2_graph_semilinear`, the `p = 2`, `q = k` instance of
`PresburgerCounting.count_graph_semilinear` (the single admitted transcription of
`lem:presburger-counting`), with the bound hypothesis unbundled. -/
theorem twoParamCountGraph_proved : TwoParamCountGraph := by
  intro k Φ hΦ hfin hbd
  obtain ⟨C, hC⟩ := hbd
  exact SliceSemilinearN.sliceFamilyCount2_graph_semilinear hΦ hfin C hC

/-- **Theorem `thm:two-parameter-semilinearity`
(paper.tex), unconditional** — `two_param_profile_semilinear` discharged with the
counting principle `twoParamCountGraph_proved`.  Trust base (verified by
`#print axioms`): the kernel axioms, the two general slice-definability axioms
`msoDefinableRel2_semilinear_general` / `regularRankTerm_value2_graph_semilinear`,
and the counting axiom `PresburgerCounting.count_graph_semilinear`. -/
theorem two_param_profile_semilinear_unconditional
    (T : List Step → Option (List Step)) (hT : WRP.IsWRP T)
    (hgrow : ∃ C, ∀ m n out, 1 ≤ m → T (copiedSlice m n) = some out →
      out.length ≤ C * (m + n + 1))
    (hdom : ∀ m n, 1 ≤ m → ∃ out, T (copiedSlice m n) = some out) :
    IsSemilinearNd 4 {v : Fin 4 → ℕ |
      ∃ m n out, 1 ≤ m ∧ T (copiedSlice m n) = some out ∧
        v 0 = m ∧ v 1 = n ∧ v 2 = firstAscent out ∧ v 3 = tailU out} :=
  two_param_profile_semilinear T hT twoParamCountGraph_proved hgrow hdom

end TwoParamSemilinearity
