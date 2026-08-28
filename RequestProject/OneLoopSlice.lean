/-
# The general one-loop lemmas (§7): `lem:one-loop-finite-state`,
# `lem:one-loop-rank-affine` (graph form), `lem:one-loop-presburger`

The §7 slice analysis of `paper-full-new.tex` is stated for a **general
regular slice** `w_n = u·vⁿ·z`, with the positions of MSO variables and rank
coordinates addressed by *(region, offset, repetition-index)* coordinates
(`τ ∈ {u, v, z}`, offset `s`, index `j`).  The copied-slice development
(`CopiedTieSemilinear2.lean`, `TwoParamSemilinearity.lean`) instantiates that
analysis at the two-parameter word `UᵐˢUDⁿDᵐˢ` — the instance §8 consumes —
with raw input positions as coordinates.  This file closes the gap: it states
the paper's three one-loop lemmas **1:1 over an arbitrary slice `u·vⁿ·z`**
and derives them from the same two project-agnostic admitted facts
(`msoDefinableRel2_semilinear_general`, `regularRankTerm_value2_graph_semilinear`)
— so the trust base is unchanged.

* `one_loop_finite_state` — `lem:one-loop-finite-state`: for an MSO formula
  `φ(x₁,…,x_k)` with fixed regions/offsets, the set of valid parameter tuples
  `(n, j₁, …, j_k)` with `w_n ⊨ φ(i₁,…,i_k)` is semilinear
  (= Presburger-definable).
* `one_loop_rank_graph` — `lem:one-loop-rank-affine` in the **graph form the
  paper consumes** (the discussion after the lemma and
  `lem:one-loop-presburger`(c,d) use only Presburger-definability of rank
  comparisons, which the semilinear value graph provides): the value graph of
  a `d`-dimensional regular rank term at region/offset-encoded positions is
  semilinear over the valid parameter tuples.  The paper's explicit
  `b₀ + b_n·n + Σ b_ℓ j_ℓ` piecewise-affine normal form is not separately
  formalised.
* `one_loop_presburger_sel` / `_label` / `_rankLt` / `_tie` / `_wrpOrd` —
  `lem:one-loop-presburger`(a)–(d): selection, output label, rank
  lex-comparison, tie-order on equal rank (and the combined output order `≺`)
  of region/offset-encoded atoms are semilinear in the valid parameter
  tuples, for **any** WRP presentation over **any** finite alphabet.

The file has three layers: elementary semilinear tools (linear forms with
constants, iterated projection); the atom-level semilinear facts of a WRP
presentation over an **arbitrary** block-linear family `F` (generalising the
`copiedSlice`-specific instances, same derivations); and the region/offset
**encoding engine** that turns a semilinear raw-position family into a
semilinear set of `(n, j⃗)`-parameters by adjoining the affine
position-encoding constraints and projecting the raw data away.
-/
import RequestProject.TwoParamSemilinearity

namespace OneLoopSlice

open WRP SliceSemilinearN MSO TwoParamSemilinearity

/-! ## Elementary semilinear tools: linear forms with constants -/

/-- The single-coordinate evaluation hom `v ↦ (fun _ => v i)`. -/
private def projHom (d : ℕ) (i : Fin d) : (Fin d → ℕ) →+ (Fin 1 → ℕ) where
  toFun v := fun _ => v i
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A coordinate pinned to a constant is semilinear. -/
theorem isSemilinearNd_coord_eq_const (d : ℕ) (i : Fin d) (c : ℕ) :
    IsSemilinearNd d {v : Fin d → ℕ | v i = c} := by
  have hpre : IsSemilinearSet (projHom d i ⁻¹' {fun _ : Fin 1 => c}) :=
    (IsSemilinearSet.singleton _).preimage (projHom d i)
  refine isSemilinearNd_congr ?_ (mathlib_to_isSemilinearNd d _ hpre)
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, projHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Set.mem_singleton_iff]
  constructor
  · intro h
    exact congrFun h 0
  · intro h
    funext j
    exact h

/-- The linear-form inequality `{v | Σ_{i ∈ A} v i ≤ Σ_{j ∈ B} v j}` is semilinear:
introduce a slack coordinate and project the equation. -/
theorem isSemilinearNd_forms_le (d : ℕ) (A B : List (Fin d)) :
    IsSemilinearNd d {v : Fin d → ℕ | (A.map v).sum ≤ (B.map v).sum} := by
  have h := isSemilinearNd_forms_eq (d + 1)
    (A.map Fin.castSucc ++ [Fin.last d]) (B.map Fin.castSucc)
  refine isSemilinearNd_congr ?_ (isSemilinearNd_proj h)
  ext v
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht⟩
    simp only [List.map_append, List.map_map, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def,
      Fin.snoc_castSucc, Fin.snoc_last] at ht
    have hA : (List.map (fun x : Fin d => v x) A).sum = (List.map v A).sum := rfl
    have hB : (List.map (fun x : Fin d => v x) B).sum = (List.map v B).sum := rfl
    omega
  · intro hle
    refine ⟨(B.map v).sum - (A.map v).sum, ?_⟩
    simp only [List.map_append, List.map_map, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def,
      Fin.snoc_castSucc, Fin.snoc_last]
    have hA : (List.map (fun x : Fin d => v x) A).sum = (List.map v A).sum := rfl
    have hB : (List.map (fun x : Fin d => v x) B).sum = (List.map v B).sum := rfl
    omega

/-- The linear-form equation **with constants**
`{v | Σ_A v + c₁ = Σ_B v + c₂}` is semilinear: adjoin one coordinate pinned
to `1`, absorb the constants as its repetition coefficients, project. -/
theorem isSemilinearNd_forms_eq_const (d : ℕ) (A B : List (Fin d)) (c₁ c₂ : ℕ) :
    IsSemilinearNd d {v : Fin d → ℕ | (A.map v).sum + c₁ = (B.map v).sum + c₂} := by
  have hforms := isSemilinearNd_forms_eq (d + 1)
    (A.map Fin.castSucc ++ List.replicate c₁ (Fin.last d))
    (B.map Fin.castSucc ++ List.replicate c₂ (Fin.last d))
  have hpin := isSemilinearNd_coord_eq_const (d + 1) (Fin.last d) 1
  refine isSemilinearNd_congr ?_ (isSemilinearNd_proj (isSemilinearNd_inter hforms hpin))
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, List.map_append, List.map_map,
    List.sum_append, List.map_replicate, List.sum_replicate, smul_eq_mul,
    Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hA : (List.map (fun x : Fin d => v x) A).sum = (List.map v A).sum := rfl
    have hB : (List.map (fun x : Fin d => v x) B).sum = (List.map v B).sum := rfl
    omega
  · intro h
    refine ⟨1, ?_, rfl⟩
    have hA : (List.map (fun x : Fin d => v x) A).sum = (List.map v A).sum := rfl
    have hB : (List.map (fun x : Fin d => v x) B).sum = (List.map v B).sum := rfl
    omega

/-- The linear-form inequality **with constants**
`{v | Σ_A v + c₁ ≤ Σ_B v + c₂}` is semilinear. -/
theorem isSemilinearNd_forms_le_const (d : ℕ) (A B : List (Fin d)) (c₁ c₂ : ℕ) :
    IsSemilinearNd d {v : Fin d → ℕ | (A.map v).sum + c₁ ≤ (B.map v).sum + c₂} := by
  have hforms := isSemilinearNd_forms_le (d + 1)
    (A.map Fin.castSucc ++ List.replicate c₁ (Fin.last d))
    (B.map Fin.castSucc ++ List.replicate c₂ (Fin.last d))
  have hpin := isSemilinearNd_coord_eq_const (d + 1) (Fin.last d) 1
  refine isSemilinearNd_congr ?_ (isSemilinearNd_proj (isSemilinearNd_inter hforms hpin))
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, List.map_append, List.map_map,
    List.sum_append, List.map_replicate, List.sum_replicate, smul_eq_mul,
    Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hA : (List.map (fun x : Fin d => v x) A).sum = (List.map v A).sum := rfl
    have hB : (List.map (fun x : Fin d => v x) B).sum = (List.map v B).sum := rfl
    omega
  · intro h
    refine ⟨1, ?_, rfl⟩
    have hA : (List.map (fun x : Fin d => v x) A).sum = (List.map v A).sum := rfl
    have hB : (List.map (fun x : Fin d => v x) B).sum = (List.map v B).sum := rfl
    omega

/-! ## Iterated tail projection -/

/-- **Iterated tail projection**: erasing a whole trailing block of `m`
coordinates of a semilinear set is semilinear.  (`Fin (d + (m+1))` and
`Fin ((d + m) + 1)` coincide definitionally, so `isSemilinearNd_proj` and
`Fin.append_snoc` iterate without casts.) -/
theorem isSemilinearNd_proj_tail (m : ℕ) :
    ∀ {d : ℕ} {S : Set (Fin (d + m) → ℕ)}, IsSemilinearNd (d + m) S →
      IsSemilinearNd d {v : Fin d → ℕ | ∃ y : Fin m → ℕ, Fin.append v y ∈ S} := by
  induction m with
  | zero =>
      intro d S hS
      have happ : ∀ (v : Fin d → ℕ) (y : Fin 0 → ℕ),
          (Fin.append v y : Fin (d + 0) → ℕ) = v := by
        intro v y
        funext i
        rw [show i = Fin.castAdd 0 ⟨(i : ℕ), i.isLt⟩ from Fin.ext rfl, Fin.append_left]
        rfl
      refine isSemilinearNd_congr ?_ hS
      ext v
      constructor
      · intro hv
        exact ⟨Fin.elim0, by rw [happ]; exact hv⟩
      · rintro ⟨y, hy⟩
        rw [happ] at hy
        exact hy
  | succ m ih =>
      intro d S hS
      have hproj := isSemilinearNd_proj (d := d + m) (S := S) hS
      have hih := ih hproj
      refine isSemilinearNd_congr ?_ hih
      ext v
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨y', t, hty⟩
        exact ⟨Fin.snoc y' t, by rw [Fin.append_snoc]; exact hty⟩
      · rintro ⟨y, hy⟩
        refine ⟨Fin.init y, y (Fin.last m), ?_⟩
        rw [← Fin.append_snoc, Fin.snoc_init_self]
        exact hy

/-! ## The atom layer of a WRP presentation over an arbitrary block-linear family

The `copiedSlice`-specific semilinear instances of `CopiedTieSemilinear2` /
`TwoParamSemilinearity` (selection, label, validity, rank value graph, rank
comparisons, output order) redone over an **arbitrary** `F : BlockLinearWord2
Alpha` — the derivations are the same, from the two general admitted facts. -/

section GeneralFamily

variable {Alpha Gamma : Type} [Fintype Alpha] (F : BlockLinearWord2 Alpha)

/-- The `mS`-coefficient of the length of `F.eval mS n`. -/
def lenMS : ℕ := (F.blocks.map fun b => b.2.1 * b.1.length).sum

/-- The `n`-coefficient of the length of `F.eval mS n`. -/
def lenN : ℕ := (F.blocks.map fun b => b.2.2.1 * b.1.length).sum

/-- The constant part of the length of `F.eval mS n`. -/
def lenC : ℕ := (F.blocks.map fun b => b.2.2.2 * b.1.length).sum

private theorem length_flatten_replicate {α : Type*} (m : ℕ) (b : List α) :
    (List.replicate m b).flatten.length = m * b.length := by
  induction m with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; ring

omit [Fintype Alpha] in
/-- The length of `F.eval mS n` is the affine form
`lenMS·mS + lenN·n + lenC`. -/
theorem eval_length (mS n : ℕ) :
    (F.eval mS n).length = lenMS F * mS + lenN F * n + lenC F := by
  unfold BlockLinearWord2.eval lenMS lenN lenC
  induction F.blocks with
  | nil => simp
  | cons b bs ih =>
      obtain ⟨w, aMS, aN, cst⟩ := b
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons, ih,
        length_flatten_replicate]
      ring

variable (P : WRP.Presentation Alpha Gamma)

omit [Fintype Alpha] in
/-- **Atom validity is semilinear over `F`**: each coordinate is below the
affine slice length. -/
theorem validAtomF_semilinear (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin (P.toPoly.arity c) → ℕ) =>
      P.toPoly.validAtom (F.eval mS n) (⟨c, ī⟩ : P.toPoly.Atom)) := by
  have h := isSemilinearNd_biInter (Finset.univ : Finset (Fin (P.toPoly.arity c)))
    (fun t => {v : Fin (P.toPoly.arity c + 2) → ℕ |
      (([t.succ.succ] : List (Fin (P.toPoly.arity c + 2))).map v).sum + 1
        ≤ (((List.replicate (lenMS F) (0 : Fin (P.toPoly.arity c + 2)))
            ++ List.replicate (lenN F) (1 : Fin (P.toPoly.arity c + 2))).map v).sum
          + lenC F})
    (fun t _ => isSemilinearNd_forms_le_const _ _ _ 1 (lenC F))
  refine isSemilinearNd_congr ?_ h
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq, Set.mem_iInter,
    Finset.mem_univ, forall_const, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul, Polyreg.Presentation.validAtom, eval_length]
  constructor
  · intro hall t
    have := hall t
    omega
  · intro hall t
    have := hall t
    omega

/-- **Selection is semilinear over `F`** (from the general MSO fact at `selDef`). -/
theorem selF_semilinear (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin (P.toPoly.arity c) → ℕ) =>
      P.toPoly.sel c (F.eval mS n) ī) :=
  msoDefinableRel2_semilinear_general F (P.toPoly.selDef c)

/-- **Selectedness is semilinear over `F`**. -/
theorem selectedAtomF_semilinear (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin (P.toPoly.arity c) → ℕ) =>
      P.toPoly.selectedAtom (F.eval mS n) (⟨c, ī⟩ : P.toPoly.Atom)) :=
  (validAtomF_semilinear F P c).and (selF_semilinear F P c)

/-- **Each label class is semilinear over `F`**. -/
theorem labelClassF_semilinear (c : Fin P.toPoly.K) (g : Gamma) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin (P.toPoly.arity c) → ℕ) =>
      P.toPoly.labelOf (F.eval mS n) (⟨c, ī⟩ : P.toPoly.Atom) = g) :=
  msoDefinableRel2_semilinear_general F (P.toPoly.labelDef c g)

/-- **The tie-order `χ` on an atom pair is semilinear over `F`**. -/
theorem atomOrdF_semilinear (c c' : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2
      (fun mS n (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) =>
        P.toPoly.atomOrd (F.eval mS n)
          (⟨c, fun t => ij (Fin.castAdd (P.toPoly.arity c') t)⟩ : P.toPoly.Atom)
          (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom)) :=
  msoDefinableRel2_semilinear_general F (P.toPoly.ordDef c c')

/-- **The rank value graph of one copy is semilinear over `F`** (the general
rank-term fact at `P.rank c`; `ī` first, value block last). -/
theorem rankOfF_value_semilinear (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2
      (fun mS n (iv : Fin (P.toPoly.arity c + (P.d + P.d)) → ℕ) =>
        P.rankOf (F.eval mS n)
            (⟨c, fun t => iv (Fin.castAdd (P.d + P.d) t)⟩ : P.toPoly.Atom)
          = decodeZ (fun cc => iv (Fin.natAdd (P.toPoly.arity c) cc))) := by
  have h := regularRankTerm_value2_graph_semilinear (Alpha := Alpha) F (P.rankReg c)
  refine isSemilinearNd_congr ?_ h
  ext iv
  simp only [familyGraph2, Set.mem_ofPred_eq, WRP.Presentation.rankOf]

/-! ### Rank comparisons of atom pairs over `F`

The `copiedSlice` pair machinery of `TwoParamSemilinearity` redone over `F`:
the derivations are identical — only the two leaf instances change. -/

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

omit [Fintype Alpha] in
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

omit [Fintype Alpha] in
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

omit [Fintype Alpha] in
private theorem selE1_castAdd (c c' : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c)) :
    selE1 P c c' (Fin.castAdd (P.d + P.d) t)
      = Fin.castAdd (P.d + P.d) (Fin.castAdd (P.toPoly.arity c') t) :=
  Fin.append_left _ _ t

omit [Fintype Alpha] in
private theorem selE1_natAdd (c c' : Fin P.toPoly.K) (cc : Fin (P.d + P.d)) :
    selE1 P c c' (Fin.natAdd (P.toPoly.arity c) cc)
      = Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') cc :=
  Fin.append_right _ _ cc

omit [Fintype Alpha] in
private theorem selE2_castAdd (c c' : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c')) :
    selE2 P c c' (Fin.castAdd (P.d + P.d) t)
      = Fin.castAdd (P.d + P.d) (Fin.natAdd (P.toPoly.arity c) t) :=
  Fin.append_left _ _ t

omit [Fintype Alpha] in
private theorem selE2_natAdd (c c' : Fin P.toPoly.K) (cc : Fin (P.d + P.d)) :
    selE2 P c c' (Fin.natAdd (P.toPoly.arity c') cc)
      = Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') cc :=
  Fin.append_right _ _ cc

/-- **Rank equality of two atoms is semilinear over `F`**: introduce one shared
value block `v`, pin both rank vectors to `decodeZ v`, and existentially
project the block. -/
theorem rankPairEqF_semilinear (c c' : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2
      (fun mS n (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) =>
        P.rankOf (F.eval mS n)
            (⟨c, fun t => ij (Fin.castAdd (P.toPoly.arity c') t)⟩ : P.toPoly.Atom)
          = P.rankOf (F.eval mS n)
            (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom)) := by
  have h1 := IsSliceFamilySemilinear2.comap_sel (selE1 P c c') (selE1_injective P c c')
    (rankOfF_value_semilinear F P c)
  have h2 := IsSliceFamilySemilinear2.comap_sel (selE2 P c c') (selE2_injective P c c')
    (rankOfF_value_semilinear F P c')
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
      (P.rankOf (F.eval (w 0) (w 1))
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

omit [Fintype Alpha] in
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

omit [Fintype Alpha] in
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

omit [Fintype Alpha] in
private theorem selL1_castAdd (c c' : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c)) :
    selL1 P c c' (Fin.castAdd (P.d + P.d) t)
      = Fin.castAdd ((P.d + P.d) + (P.d + P.d)) (Fin.castAdd (P.toPoly.arity c') t) :=
  Fin.append_left _ _ t

omit [Fintype Alpha] in
private theorem selL1_natAdd (c c' : Fin P.toPoly.K) (cc : Fin (P.d + P.d)) :
    selL1 P c c' (Fin.natAdd (P.toPoly.arity c) cc)
      = Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') (Fin.castAdd (P.d + P.d) cc) :=
  Fin.append_right _ _ cc

omit [Fintype Alpha] in
private theorem selL2_castAdd (c c' : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c')) :
    selL2 P c c' (Fin.castAdd (P.d + P.d) t)
      = Fin.castAdd ((P.d + P.d) + (P.d + P.d)) (Fin.natAdd (P.toPoly.arity c) t) :=
  Fin.append_left _ _ t

omit [Fintype Alpha] in
private theorem selL2_natAdd (c c' : Fin P.toPoly.K) (cc : Fin (P.d + P.d)) :
    selL2 P c c' (Fin.natAdd (P.toPoly.arity c') cc)
      = Fin.natAdd (P.toPoly.arity c + P.toPoly.arity c') (Fin.natAdd (P.d + P.d) cc) :=
  Fin.append_right _ _ cc

/-- **Rank lex-comparison of two atoms is semilinear over `F`**: introduce two
value blocks `v, v'`, pin the two rank vectors, compare with
`lexLt_decodeZ_sel`, and existentially project both blocks. -/
theorem rankPairLexLtF_semilinear (c c' : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2
      (fun mS n (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) =>
        WRP.lexLt
          (P.rankOf (F.eval mS n)
            (⟨c, fun t => ij (Fin.castAdd (P.toPoly.arity c') t)⟩ : P.toPoly.Atom))
          (P.rankOf (F.eval mS n)
            (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom))) := by
  have h1 := IsSliceFamilySemilinear2.comap_sel (selL1 P c c') (selL1_injective P c c')
    (rankOfF_value_semilinear F P c)
  have h2 := IsSliceFamilySemilinear2.comap_sel (selL2 P c c') (selL2_injective P c c')
    (rankOfF_value_semilinear F P c')
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
      (P.rankOf (F.eval (w 0) (w 1))
        (⟨c, fun t =>
          w (Fin.castAdd (P.toPoly.arity c') t).succ.succ⟩ : P.toPoly.Atom))
    obtain ⟨v2, hv2⟩ := decodeZ_surjective
      (P.rankOf (F.eval (w 0) (w 1))
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

/-- **The output order `≺` between two atoms is semilinear over `F`**: rank
lex-comparison, or rank equality together with the MSO tie-order. -/
theorem wrpOrdF_semilinear (c c' : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2
      (fun mS n (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) =>
        P.wrpOrd (F.eval mS n)
          (⟨c, fun t => ij (Fin.castAdd (P.toPoly.arity c') t)⟩ : P.toPoly.Atom)
          (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom)) := by
  refine isSemilinearNd_congr ?_
    ((rankPairLexLtF_semilinear F P c c').or
      ((rankPairEqF_semilinear F P c c').and (atomOrdF_semilinear F P c c')))
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  exact Iff.rfl

end GeneralFamily

/-! ## The one-loop slice `u·vⁿ·z` and its position encoding -/

/-- The one-loop word `u·vⁿ·z` — the paper's regular slice `w_n`. -/
def oneLoopWord {Alpha : Type} (u v z : List Alpha) (n : ℕ) : List Alpha :=
  u ++ (List.replicate n v).flatten ++ z

/-- `u·vⁿ·z` as a (degenerate, `mS`-independent) block-linear two-parameter
family: blocks `u`, `v`, `z` with multiplicities `1`, `n`, `1`. -/
def oneLoopBLW {Alpha : Type} (u v z : List Alpha) : BlockLinearWord2 Alpha :=
  ⟨[(u, 0, 0, 1), (v, 0, 1, 0), (z, 0, 0, 1)]⟩

private theorem flatten_replicate_one {Alpha : Type} (w : List Alpha) :
    (List.replicate 1 w).flatten = w := by
  rw [List.replicate_one, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem oneLoopBLW_eval {Alpha : Type} (u v z : List Alpha) (mS n : ℕ) :
    (oneLoopBLW u v z).eval mS n = oneLoopWord u v z n := by
  simp only [oneLoopBLW, BlockLinearWord2.eval, oneLoopWord, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.one_mul, flatten_replicate_one, List.append_nil, List.append_assoc]

/-- Propositionally equal two-parameter families are semilinear together. -/
theorem family_congr {k : ℕ} {Φ Φ' : ℕ → ℕ → (Fin k → ℕ) → Prop}
    (h : ∀ mS n ī, Φ mS n ī ↔ Φ' mS n ī) (hΦ : IsSliceFamilySemilinear2 Φ) :
    IsSliceFamilySemilinear2 Φ' := by
  refine isSemilinearNd_congr ?_ hΦ
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  exact h _ _ _

/-- The region of a coordinate on the slice `u·vⁿ·z` — the paper's
`τ ∈ {u, v, z}`, extended by `free` (a coordinate that is not
position-encoded but passed through verbatim; used for the value block of
the rank-graph lemma). -/
inductive Region | u | v | z | free
deriving DecidableEq

/-- The position encoded by *(region, offset, repetition index)* on
`u·vⁿ·z`: offset `s` into the prefix `u`, into the `j`-th copy of `v`
(`j` is `1`-based), or into the suffix `z`; a `free` coordinate is the raw
value `j` itself. -/
def regionPos {Alpha : Type} (u v : List Alpha) (n : ℕ) :
    Region → ℕ → ℕ → ℕ
  | Region.u, s, _ => s
  | Region.v, s, j => u.length + (j - 1) * v.length + s
  | Region.z, s, _ => u.length + n * v.length + s
  | Region.free, _, j => j

/-- Validity of one parameter: a `v`-region index is `1`-based in
`{1, …, n}`, a `free` index is arbitrary, all others are `0`. -/
def ValidIdx (n : ℕ) : Region → ℕ → Prop
  | Region.v, j => 1 ≤ j ∧ j ≤ n
  | Region.free, _ => True
  | _, j => j = 0

/-- Validity of an offset for its region. -/
def ValidOff {Alpha : Type} (u v z : List Alpha) : Region → ℕ → Prop
  | Region.u, s => s < u.length
  | Region.v, s => s < v.length
  | Region.z, s => s < z.length
  | Region.free, _ => True

/-! ## The encoding engine

From a semilinear (`mS`-independent) raw-position family `Ψ n ī`, the set of
`(n, j₁, …, j_k)`-parameters at which `Ψ` holds of the region/offset-encoded
positions is semilinear: adjoin the affine position-encoding constraints in a
doubled coordinate space and project the raw data away. -/

section Engine

/-- The coordinate selection embedding the family's packed `(mS, n, ī)`-space
into the doubled space `[n | j⃗] ++ [mS | ī]`. -/
private def selFam (k : ℕ) : Fin (k + 2) → Fin ((1 + k) + (1 + k)) := fun q =>
  if h0 : (q : ℕ) = 0 then ⟨1 + k, by omega⟩
  else if h1 : (q : ℕ) = 1 then ⟨0, by omega⟩
  else ⟨1 + k + (1 + ((q : ℕ) - 2)), by omega⟩

private theorem selFam_zero (k : ℕ) :
    selFam k ⟨0, by omega⟩ = ⟨1 + k, by omega⟩ := by
  simp [selFam]

private theorem selFam_one (k : ℕ) :
    selFam k ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
  simp [selFam]

private theorem selFam_ss (k : ℕ) (i : Fin k) :
    selFam k i.succ.succ = ⟨1 + k + (1 + (i : ℕ)), by omega⟩ := by
  have h2 : ((i.succ.succ : Fin (k + 2)) : ℕ) = (i : ℕ) + 2 := rfl
  simp only [selFam, h2]
  rw [dif_neg (by omega), dif_neg (by omega)]
  exact Fin.ext (by simp)

private theorem selFam_injective (k : ℕ) : Function.Injective (selFam k) := by
  intro a b hab
  have hv := Fin.val_eq_of_eq hab
  unfold selFam at hv
  refine Fin.ext ?_
  have ha := a.isLt
  have hb := b.isLt
  split_ifs at hv <;> simp only [] at hv <;> omega

/-- The per-coordinate encoding constraint in the doubled space: the raw
position `x[ī_t]` equals the region/offset-encoded position determined by
`x[n]` and `x[j_t]`, and `x[j_t]` is a valid index.  (The `v`-region equation
is stated monus-free as `ī_t + |v| = |v|·j_t + (|u| + s)`.) -/
private def cSet {Alpha : Type} (u v : List Alpha) {k : ℕ} (τ1 : Region) (s1 : ℕ)
    (t : Fin k) : Set (Fin ((1 + k) + (1 + k)) → ℕ) :=
  match τ1 with
  | Region.u => {x | x ⟨1 + k + (1 + (t : ℕ)), by omega⟩ = s1
      ∧ x ⟨1 + (t : ℕ), by omega⟩ = 0}
  | Region.v => {x | x ⟨1 + k + (1 + (t : ℕ)), by omega⟩ + v.length
        = v.length * x ⟨1 + (t : ℕ), by omega⟩ + (u.length + s1)
      ∧ 1 ≤ x ⟨1 + (t : ℕ), by omega⟩
      ∧ x ⟨1 + (t : ℕ), by omega⟩ ≤ x ⟨0, by omega⟩}
  | Region.z => {x | x ⟨1 + k + (1 + (t : ℕ)), by omega⟩
        = v.length * x ⟨0, by omega⟩ + (u.length + s1)
      ∧ x ⟨1 + (t : ℕ), by omega⟩ = 0}
  | Region.free => {x | x ⟨1 + k + (1 + (t : ℕ)), by omega⟩
      = x ⟨1 + (t : ℕ), by omega⟩}

private theorem cSet_semilinear {Alpha : Type} (u v : List Alpha) {k : ℕ}
    (τ1 : Region) (s1 : ℕ) (t : Fin k) :
    IsSemilinearNd ((1 + k) + (1 + k)) (cSet u v τ1 s1 t) := by
  cases τ1 with
  | u =>
      refine isSemilinearNd_congr ?_ (isSemilinearNd_inter
        (isSemilinearNd_coord_eq_const _ ⟨1 + k + (1 + (t : ℕ)), by omega⟩ s1)
        (isSemilinearNd_coord_eq_const _ ⟨1 + (t : ℕ), by omega⟩ 0))
      ext x
      simp only [cSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  | v =>
      refine isSemilinearNd_congr ?_ (isSemilinearNd_inter
        (isSemilinearNd_forms_eq_const _ [⟨1 + k + (1 + (t : ℕ)), by omega⟩]
          (List.replicate v.length ⟨1 + (t : ℕ), by omega⟩) v.length (u.length + s1))
        (isSemilinearNd_inter
          (isSemilinearNd_forms_le_const _ [] [⟨1 + (t : ℕ), by omega⟩] 1 0)
          (isSemilinearNd_forms_le_const _ [⟨1 + (t : ℕ), by omega⟩] [⟨0, by omega⟩] 0 0)))
      ext x
      simp only [cSet, Set.mem_inter_iff, Set.mem_ofPred_eq, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.map_replicate, List.sum_replicate, smul_eq_mul,
        Nat.add_zero, Nat.zero_add]
  | z =>
      refine isSemilinearNd_congr ?_ (isSemilinearNd_inter
        (isSemilinearNd_forms_eq_const _ [⟨1 + k + (1 + (t : ℕ)), by omega⟩]
          (List.replicate v.length (⟨0, by omega⟩ : Fin ((1 + k) + (1 + k)))) 0
          (u.length + s1))
        (isSemilinearNd_coord_eq_const _ ⟨1 + (t : ℕ), by omega⟩ 0))
      ext x
      simp only [cSet, Set.mem_inter_iff, Set.mem_ofPred_eq, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.map_replicate, List.sum_replicate, smul_eq_mul,
        Nat.add_zero]
  | free =>
      refine isSemilinearNd_congr ?_
        (isSemilinearNd_forms_eq_const _ [⟨1 + k + (1 + (t : ℕ)), by omega⟩]
          [⟨1 + (t : ℕ), by omega⟩] 0 0)
      ext x
      simp only [cSet, Set.mem_ofPred_eq, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]

/-- **The encoding engine.**  If the raw-position family `Ψ` is semilinear
(cylindrified over a vacuous `mS`), then so is the set of parameter tuples
`(n, j₁, …, j_k)` — packed as `p : Fin (1+k) → ℕ` with `n = p 0` and
`j_t = p (1+t)` — at which every index is valid and `Ψ` holds of the
region/offset-encoded positions. -/
theorem encode_semilinear {Alpha : Type} {k : ℕ} (u v : List Alpha)
    (τ : Fin k → Region) (s : Fin k → ℕ)
    {Ψ : ℕ → (Fin k → ℕ) → Prop}
    (hΨ : IsSliceFamilySemilinear2 (fun _mS n ī => Ψ n ī)) :
    IsSemilinearNd (1 + k)
      {p : Fin (1 + k) → ℕ |
        (∀ t : Fin k, ValidIdx (p ⟨0, by omega⟩) (τ t) (p ⟨1 + (t : ℕ), by omega⟩)) ∧
        Ψ (p ⟨0, by omega⟩)
          (fun t => regionPos u v (p ⟨0, by omega⟩) (τ t) (s t)
            (p ⟨1 + (t : ℕ), by omega⟩))} := by
  classical
  have hfam : IsSemilinearNd ((1 + k) + (1 + k))
      {x : Fin ((1 + k) + (1 + k)) → ℕ |
        Ψ (x ⟨0, by omega⟩)
          (fun i : Fin k => x ⟨1 + k + (1 + (i : ℕ)), by omega⟩)} := by
    have h := isSemilinearNd_comap_injective (selFam k) (selFam_injective k) hΨ
    refine isSemilinearNd_congr ?_ h
    ext x
    simp only [Set.mem_ofPred_eq, familyGraph2]
    have e1 : x (selFam k ⟨1, by omega⟩) = x ⟨0, by omega⟩ := by rw [selFam_one]
    have e2 : (fun i : Fin k => x (selFam k i.succ.succ))
        = fun i : Fin k => x ⟨1 + k + (1 + (i : ℕ)), by omega⟩ :=
      funext fun i => by rw [selFam_ss]
    show Ψ (x (selFam k ⟨1, by omega⟩)) (fun i => x (selFam k i.succ.succ)) ↔ _
    rw [e1, e2]
  have hbig := isSemilinearNd_inter hfam (isSemilinearNd_biInter Finset.univ
    (fun t : Fin k => cSet u v (τ t) (s t) t)
    (fun t _ => cSet_semilinear u v (τ t) (s t) t))
  have hproj := isSemilinearNd_proj_tail (1 + k) (d := 1 + k) hbig
  refine isSemilinearNd_congr ?_ hproj
  have happL : ∀ (p : Fin (1 + k) → ℕ) (y : Fin (1 + k) → ℕ) (i : ℕ) (h : i < 1 + k),
      Fin.append p y ⟨i, by omega⟩ = p ⟨i, h⟩ := by
    intro p y i h
    rw [show (⟨i, by omega⟩ : Fin ((1 + k) + (1 + k))) = Fin.castAdd (1 + k) ⟨i, h⟩ from
      Fin.ext rfl, Fin.append_left]
  have happR : ∀ (p : Fin (1 + k) → ℕ) (y : Fin (1 + k) → ℕ) (i : ℕ) (h : i < 1 + k),
      Fin.append p y ⟨1 + k + i, by omega⟩ = y ⟨i, h⟩ := by
    intro p y i h
    rw [show (⟨1 + k + i, by omega⟩ : Fin ((1 + k) + (1 + k)))
        = Fin.natAdd (1 + k) ⟨i, h⟩ from Fin.ext rfl, Fin.append_right]
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
    Finset.mem_univ, forall_const]
  constructor
  · rintro ⟨y, hm, hc⟩
    have hboth : ∀ t : Fin k,
        ValidIdx (p ⟨0, by omega⟩) (τ t) (p ⟨1 + (t : ℕ), by omega⟩) ∧
        y ⟨1 + (t : ℕ), by omega⟩
          = regionPos u v (p ⟨0, by omega⟩) (τ t) (s t) (p ⟨1 + (t : ℕ), by omega⟩) := by
      intro t
      have hct := hc t
      rcases hτ : τ t with _ | _ | _ | _
      · rw [hτ] at hct
        simp only [cSet, Set.mem_ofPred_eq] at hct
        rw [happR p y (1 + (t : ℕ)) (by omega),
          happL p y (1 + (t : ℕ)) (by omega)] at hct
        exact ⟨hct.2, by simp only [regionPos]; exact hct.1⟩
      · rw [hτ] at hct
        simp only [cSet, Set.mem_ofPred_eq] at hct
        rw [happR p y (1 + (t : ℕ)) (by omega),
          happL p y (1 + (t : ℕ)) (by omega), happL p y 0 (by omega)] at hct
        obtain ⟨heq, hge, hle⟩ := hct
        refine ⟨⟨hge, hle⟩, ?_⟩
        simp only [regionPos]
        have hb1 : v.length * p ⟨1 + (t : ℕ), by omega⟩
            = v.length * (p ⟨1 + (t : ℕ), by omega⟩ - 1) + v.length := by
          have h1 : p ⟨1 + (t : ℕ), by omega⟩ = (p ⟨1 + (t : ℕ), by omega⟩ - 1) + 1 := by
            omega
          conv_lhs => rw [h1]
          rw [Nat.mul_succ]
        have hb2 : (p ⟨1 + (t : ℕ), by omega⟩ - 1) * v.length
            = v.length * (p ⟨1 + (t : ℕ), by omega⟩ - 1) := Nat.mul_comm _ _
        omega
      · rw [hτ] at hct
        simp only [cSet, Set.mem_ofPred_eq] at hct
        rw [happR p y (1 + (t : ℕ)) (by omega),
          happL p y (1 + (t : ℕ)) (by omega), happL p y 0 (by omega)] at hct
        obtain ⟨heq, hj0⟩ := hct
        refine ⟨hj0, ?_⟩
        simp only [regionPos]
        have hb : (p ⟨0, by omega⟩) * v.length = v.length * (p ⟨0, by omega⟩) :=
          Nat.mul_comm _ _
        omega
      · rw [hτ] at hct
        simp only [cSet, Set.mem_ofPred_eq] at hct
        rw [happR p y (1 + (t : ℕ)) (by omega),
          happL p y (1 + (t : ℕ)) (by omega)] at hct
        exact ⟨trivial, by simp only [regionPos]; exact hct⟩
    refine ⟨fun t => (hboth t).1, ?_⟩
    rw [happL p y 0 (by omega)] at hm
    have harg : (fun i : Fin k => Fin.append p y ⟨1 + k + (1 + (i : ℕ)), by omega⟩)
        = fun t => regionPos u v (p ⟨0, by omega⟩) (τ t) (s t)
            (p ⟨1 + (t : ℕ), by omega⟩) := by
      funext i
      rw [happR p y (1 + (i : ℕ)) (by omega)]
      exact (hboth i).2
    rw [harg] at hm
    exact hm
  · rintro ⟨hval, hΨp⟩
    refine ⟨fun w => if _h0 : (w : ℕ) = 0 then 0
      else regionPos u v (p ⟨0, by omega⟩) (τ ⟨(w : ℕ) - 1, by omega⟩)
        (s ⟨(w : ℕ) - 1, by omega⟩) (p ⟨1 + ((w : ℕ) - 1), by omega⟩), ?_, ?_⟩
    · rw [happL p _ 0 (by omega)]
      have harg : (fun i : Fin k => Fin.append p
            (fun w : Fin (1 + k) => if _h0 : (w : ℕ) = 0 then 0
              else regionPos u v (p ⟨0, by omega⟩) (τ ⟨(w : ℕ) - 1, by omega⟩)
                (s ⟨(w : ℕ) - 1, by omega⟩) (p ⟨1 + ((w : ℕ) - 1), by omega⟩))
            ⟨1 + k + (1 + (i : ℕ)), by omega⟩)
          = fun t => regionPos u v (p ⟨0, by omega⟩) (τ t) (s t)
              (p ⟨1 + (t : ℕ), by omega⟩) := by
        funext i
        rw [happR p _ (1 + (i : ℕ)) (by omega)]
        simp only [dif_neg (show ¬ ((⟨1 + (i : ℕ), by omega⟩ : Fin (1 + k)) : ℕ) = 0 by
          simp)]
        have e1 : (⟨((⟨1 + (i : ℕ), by omega⟩ : Fin (1 + k)) : ℕ) - 1,
              by show 1 + (i : ℕ) - 1 < k; omega⟩ : Fin k)
            = i := Fin.ext (by show 1 + (i : ℕ) - 1 = (i : ℕ); omega)
        have e2 : (⟨1 + (((⟨1 + (i : ℕ), by omega⟩ : Fin (1 + k)) : ℕ) - 1),
              by show 1 + (1 + (i : ℕ) - 1) < 1 + k; omega⟩
            : Fin (1 + k)) = ⟨1 + (i : ℕ), by omega⟩ :=
          Fin.ext (by show 1 + (1 + (i : ℕ) - 1) = 1 + (i : ℕ); omega)
        rw [e1, e2]
      rw [harg]
      exact hΨp
    · intro t
      have hvt := hval t
      have e1 : (⟨((⟨1 + (t : ℕ), by omega⟩ : Fin (1 + k)) : ℕ) - 1,
            by show 1 + (t : ℕ) - 1 < k; omega⟩ : Fin k)
          = t := Fin.ext (by show 1 + (t : ℕ) - 1 = (t : ℕ); omega)
      have e2 : (⟨1 + (((⟨1 + (t : ℕ), by omega⟩ : Fin (1 + k)) : ℕ) - 1),
            by show 1 + (1 + (t : ℕ) - 1) < 1 + k; omega⟩
          : Fin (1 + k)) = ⟨1 + (t : ℕ), by omega⟩ :=
        Fin.ext (by show 1 + (1 + (t : ℕ) - 1) = 1 + (t : ℕ); omega)
      have hne : ¬ ((⟨1 + (t : ℕ), by omega⟩ : Fin (1 + k)) : ℕ) = 0 := by simp
      rcases hτ : τ t with _ | _ | _ | _
      · rw [hτ] at hvt
        simp only [ValidIdx] at hvt
        simp only [cSet, Set.mem_ofPred_eq]
        rw [happR p _ (1 + (t : ℕ)) (by omega),
          happL p _ (1 + (t : ℕ)) (by omega), dif_neg hne, e1, e2, hτ]
        simp only [regionPos]
        exact ⟨trivial, hvt⟩
      · rw [hτ] at hvt
        simp only [ValidIdx] at hvt
        simp only [cSet, Set.mem_ofPred_eq]
        rw [happR p _ (1 + (t : ℕ)) (by omega),
          happL p _ (1 + (t : ℕ)) (by omega), happL p _ 0 (by omega),
          dif_neg hne, e1, e2, hτ]
        simp only [regionPos]
        refine ⟨?_, hvt.1, hvt.2⟩
        have hb1 : v.length * p ⟨1 + (t : ℕ), by omega⟩
            = v.length * (p ⟨1 + (t : ℕ), by omega⟩ - 1) + v.length := by
          have h1 : p ⟨1 + (t : ℕ), by omega⟩ = (p ⟨1 + (t : ℕ), by omega⟩ - 1) + 1 := by
            have := hvt.1
            omega
          conv_lhs => rw [h1]
          rw [Nat.mul_succ]
        have hb2 : (p ⟨1 + (t : ℕ), by omega⟩ - 1) * v.length
            = v.length * (p ⟨1 + (t : ℕ), by omega⟩ - 1) := Nat.mul_comm _ _
        omega
      · rw [hτ] at hvt
        simp only [ValidIdx] at hvt
        simp only [cSet, Set.mem_ofPred_eq]
        rw [happR p _ (1 + (t : ℕ)) (by omega),
          happL p _ (1 + (t : ℕ)) (by omega), happL p _ 0 (by omega),
          dif_neg hne, e1, e2, hτ]
        simp only [regionPos]
        have hb : (p ⟨0, by omega⟩) * v.length = v.length * (p ⟨0, by omega⟩) :=
          Nat.mul_comm _ _
        exact ⟨by omega, hvt⟩
      · simp only [cSet, Set.mem_ofPred_eq]
        rw [happR p _ (1 + (t : ℕ)) (by omega),
          happL p _ (1 + (t : ℕ)) (by omega), dif_neg hne, e1, e2, hτ]
        simp only [regionPos]

end Engine

/-! ## The paper's one-loop lemmas over `u·vⁿ·z`

Parameter tuples are packed as `p : Fin (1 + k) → ℕ` with `n = p 0` and
`j_t = p (1 + t)`; "Presburger-definable in `(n, j₁, …, j_k)`" is
`IsSemilinearNd (1 + k)` of the packed set (Ginsburg–Spanier).  Every
statement quantifies a region `τ t` and offset `s t` per coordinate, exactly
as the paper fixes them, and restricts to the **valid** parameter tuples
(`ValidIdx`: `1 ≤ j_t ≤ n` in region `v`, `j_t = 0` in regions `u`/`z`). -/

section OneLoopLemmas

variable {Alpha Gamma : Type} [Fintype Alpha] (u v z : List Alpha)

/-- **`lem:one-loop-finite-state` (MSO conditions on a regular slice)**: for
an MSO-definable `k`-ary relation `R` and fixed regions/offsets, the set of
valid parameter tuples `(n, j₁, …, j_k)` with
`u·vⁿ·z ⊨ R(i₁, …, i_k)` at the encoded positions is semilinear. -/
theorem one_loop_finite_state {k : ℕ} {R : List Alpha → (Fin k → ℕ) → Prop}
    (hR : MSO.MSODefinableRel k R) (τ : Fin k → Region) (s : Fin k → ℕ) :
    IsSemilinearNd (1 + k)
      {p : Fin (1 + k) → ℕ |
        (∀ t : Fin k, ValidIdx (p ⟨0, by omega⟩) (τ t) (p ⟨1 + (t : ℕ), by omega⟩)) ∧
        R (oneLoopWord u v z (p ⟨0, by omega⟩))
          (fun t => regionPos u v (p ⟨0, by omega⟩) (τ t) (s t)
            (p ⟨1 + (t : ℕ), by omega⟩))} :=
  encode_semilinear u v τ s (family_congr
    (fun mS n ī => by rw [oneLoopBLW_eval])
    (msoDefinableRel2_semilinear_general (oneLoopBLW u v z) hR))

/-- **`lem:one-loop-rank-affine`, in the graph form the paper consumes**: the
value graph of one copy's `d`-dimensional regular rank term at
region/offset-encoded positions is semilinear over the valid parameter
tuples.  The coordinate block `Fin (arity c + (d+d))` carries the atom
positions first and the `(positive, negative)` value split last; taking
`τ = Region.free` on the value block leaves those `d+d` parameters as the raw
value split, so rank comparisons against parameters are Presburger.  (The
paper's explicit `b₀ + b_n·n + Σ b_ℓ j_ℓ` rational normal form is not
separately formalised; parts (c)/(d) of `lem:one-loop-presburger` below are
derived from this graph instead, as in the paper's own application.) -/
theorem one_loop_rank_graph (P : WRP.Presentation Alpha Gamma) (c : Fin P.toPoly.K)
    (τ : Fin (P.toPoly.arity c + (P.d + P.d)) → Region)
    (s : Fin (P.toPoly.arity c + (P.d + P.d)) → ℕ) :
    IsSemilinearNd (1 + (P.toPoly.arity c + (P.d + P.d)))
      {p : Fin (1 + (P.toPoly.arity c + (P.d + P.d))) → ℕ |
        (∀ t, ValidIdx (p ⟨0, by omega⟩) (τ t) (p ⟨1 + (t : ℕ), by omega⟩)) ∧
        P.rankOf (oneLoopWord u v z (p ⟨0, by omega⟩))
            (⟨c, fun t => regionPos u v (p ⟨0, by omega⟩) (τ (Fin.castAdd (P.d + P.d) t))
              (s (Fin.castAdd (P.d + P.d) t))
              (p ⟨1 + ((Fin.castAdd (P.d + P.d) t : Fin _) : ℕ), by omega⟩)⟩ : P.toPoly.Atom)
          = decodeZ (fun cc => regionPos u v (p ⟨0, by omega⟩)
              (τ (Fin.natAdd (P.toPoly.arity c) cc)) (s (Fin.natAdd (P.toPoly.arity c) cc))
              (p ⟨1 + ((Fin.natAdd (P.toPoly.arity c) cc : Fin _) : ℕ), by omega⟩))} :=
  encode_semilinear u v τ s (family_congr
    (fun mS n iv => by rw [oneLoopBLW_eval])
    (rankOfF_value_semilinear (oneLoopBLW u v z) P c))

/-- **`lem:one-loop-presburger`(a)**: selectedness of a region/offset-encoded
atom is semilinear in the valid parameter tuples. -/
theorem one_loop_presburger_sel (P : WRP.Presentation Alpha Gamma)
    (c : Fin P.toPoly.K) (τ : Fin (P.toPoly.arity c) → Region)
    (s : Fin (P.toPoly.arity c) → ℕ) :
    IsSemilinearNd (1 + P.toPoly.arity c)
      {p : Fin (1 + P.toPoly.arity c) → ℕ |
        (∀ t, ValidIdx (p ⟨0, by omega⟩) (τ t) (p ⟨1 + (t : ℕ), by omega⟩)) ∧
        P.toPoly.selectedAtom (oneLoopWord u v z (p ⟨0, by omega⟩))
          (⟨c, fun t => regionPos u v (p ⟨0, by omega⟩) (τ t) (s t)
            (p ⟨1 + (t : ℕ), by omega⟩)⟩ : P.toPoly.Atom)} :=
  encode_semilinear u v τ s (family_congr
    (fun mS n ī => by rw [oneLoopBLW_eval])
    (selectedAtomF_semilinear (oneLoopBLW u v z) P c))

/-- **`lem:one-loop-presburger`(b)**: each output-label class of a
region/offset-encoded atom is semilinear in the valid parameter tuples. -/
theorem one_loop_presburger_label (P : WRP.Presentation Alpha Gamma)
    (c : Fin P.toPoly.K) (g : Gamma) (τ : Fin (P.toPoly.arity c) → Region)
    (s : Fin (P.toPoly.arity c) → ℕ) :
    IsSemilinearNd (1 + P.toPoly.arity c)
      {p : Fin (1 + P.toPoly.arity c) → ℕ |
        (∀ t, ValidIdx (p ⟨0, by omega⟩) (τ t) (p ⟨1 + (t : ℕ), by omega⟩)) ∧
        P.toPoly.labelOf (oneLoopWord u v z (p ⟨0, by omega⟩))
          (⟨c, fun t => regionPos u v (p ⟨0, by omega⟩) (τ t) (s t)
            (p ⟨1 + (t : ℕ), by omega⟩)⟩ : P.toPoly.Atom) = g} :=
  encode_semilinear u v τ s (family_congr
    (fun mS n ī => by rw [oneLoopBLW_eval])
    (labelClassF_semilinear (oneLoopBLW u v z) P c g))

/-- **`lem:one-loop-presburger`(c)**: the strict lexicographic rank comparison
of two region/offset-encoded atoms is semilinear in the valid parameter
tuples (the coordinate block carries the first atom's positions, then the
second's). -/
theorem one_loop_presburger_rankLt (P : WRP.Presentation Alpha Gamma)
    (c c' : Fin P.toPoly.K)
    (τ : Fin (P.toPoly.arity c + P.toPoly.arity c') → Region)
    (s : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) :
    IsSemilinearNd (1 + (P.toPoly.arity c + P.toPoly.arity c'))
      {p : Fin (1 + (P.toPoly.arity c + P.toPoly.arity c')) → ℕ |
        (∀ t, ValidIdx (p ⟨0, by omega⟩) (τ t) (p ⟨1 + (t : ℕ), by omega⟩)) ∧
        WRP.lexLt
          (P.rankOf (oneLoopWord u v z (p ⟨0, by omega⟩))
            (⟨c, fun t => regionPos u v (p ⟨0, by omega⟩)
              (τ (Fin.castAdd (P.toPoly.arity c') t)) (s (Fin.castAdd (P.toPoly.arity c') t))
              (p ⟨1 + ((Fin.castAdd (P.toPoly.arity c') t : Fin _) : ℕ), by omega⟩)⟩
              : P.toPoly.Atom))
          (P.rankOf (oneLoopWord u v z (p ⟨0, by omega⟩))
            (⟨c', fun t => regionPos u v (p ⟨0, by omega⟩)
              (τ (Fin.natAdd (P.toPoly.arity c) t)) (s (Fin.natAdd (P.toPoly.arity c) t))
              (p ⟨1 + ((Fin.natAdd (P.toPoly.arity c) t : Fin _) : ℕ), by omega⟩)⟩
              : P.toPoly.Atom))} :=
  encode_semilinear u v τ s (family_congr
    (fun mS n ij => by rw [oneLoopBLW_eval])
    (rankPairLexLtF_semilinear (oneLoopBLW u v z) P c c'))

/-- Rank **equality** of two region/offset-encoded atoms is semilinear (the
equal-rank guard of `lem:one-loop-presburger`(d)). -/
theorem one_loop_presburger_rankEq (P : WRP.Presentation Alpha Gamma)
    (c c' : Fin P.toPoly.K)
    (τ : Fin (P.toPoly.arity c + P.toPoly.arity c') → Region)
    (s : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) :
    IsSemilinearNd (1 + (P.toPoly.arity c + P.toPoly.arity c'))
      {p : Fin (1 + (P.toPoly.arity c + P.toPoly.arity c')) → ℕ |
        (∀ t, ValidIdx (p ⟨0, by omega⟩) (τ t) (p ⟨1 + (t : ℕ), by omega⟩)) ∧
        P.rankOf (oneLoopWord u v z (p ⟨0, by omega⟩))
            (⟨c, fun t => regionPos u v (p ⟨0, by omega⟩)
              (τ (Fin.castAdd (P.toPoly.arity c') t)) (s (Fin.castAdd (P.toPoly.arity c') t))
              (p ⟨1 + ((Fin.castAdd (P.toPoly.arity c') t : Fin _) : ℕ), by omega⟩)⟩
              : P.toPoly.Atom)
          = P.rankOf (oneLoopWord u v z (p ⟨0, by omega⟩))
            (⟨c', fun t => regionPos u v (p ⟨0, by omega⟩)
              (τ (Fin.natAdd (P.toPoly.arity c) t)) (s (Fin.natAdd (P.toPoly.arity c) t))
              (p ⟨1 + ((Fin.natAdd (P.toPoly.arity c) t : Fin _) : ℕ), by omega⟩)⟩
              : P.toPoly.Atom)} :=
  encode_semilinear u v τ s (family_congr
    (fun mS n ij => by rw [oneLoopBLW_eval])
    (rankPairEqF_semilinear (oneLoopBLW u v z) P c c'))

/-- The MSO tie-order `χ` between two region/offset-encoded atoms is
semilinear (the tie-order component of `lem:one-loop-presburger`(d);
part (d) itself is the conjunction with `one_loop_presburger_rankEq`, and
conjunctions of semilinear sets are semilinear). -/
theorem one_loop_presburger_tie (P : WRP.Presentation Alpha Gamma)
    (c c' : Fin P.toPoly.K)
    (τ : Fin (P.toPoly.arity c + P.toPoly.arity c') → Region)
    (s : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) :
    IsSemilinearNd (1 + (P.toPoly.arity c + P.toPoly.arity c'))
      {p : Fin (1 + (P.toPoly.arity c + P.toPoly.arity c')) → ℕ |
        (∀ t, ValidIdx (p ⟨0, by omega⟩) (τ t) (p ⟨1 + (t : ℕ), by omega⟩)) ∧
        P.toPoly.atomOrd (oneLoopWord u v z (p ⟨0, by omega⟩))
          (⟨c, fun t => regionPos u v (p ⟨0, by omega⟩)
            (τ (Fin.castAdd (P.toPoly.arity c') t)) (s (Fin.castAdd (P.toPoly.arity c') t))
            (p ⟨1 + ((Fin.castAdd (P.toPoly.arity c') t : Fin _) : ℕ), by omega⟩)⟩
            : P.toPoly.Atom)
          (⟨c', fun t => regionPos u v (p ⟨0, by omega⟩)
            (τ (Fin.natAdd (P.toPoly.arity c) t)) (s (Fin.natAdd (P.toPoly.arity c) t))
            (p ⟨1 + ((Fin.natAdd (P.toPoly.arity c) t : Fin _) : ℕ), by omega⟩)⟩
            : P.toPoly.Atom)} :=
  encode_semilinear u v τ s (family_congr
    (fun mS n ij => by rw [oneLoopBLW_eval])
    (atomOrdF_semilinear (oneLoopBLW u v z) P c c'))

/-- **`lem:one-loop-presburger`(c) + (d) combined**: the full output order `≺`
(rank-lexicographic, ties by `χ`) between two region/offset-encoded atoms is
semilinear in the valid parameter tuples. -/
theorem one_loop_presburger_wrpOrd (P : WRP.Presentation Alpha Gamma)
    (c c' : Fin P.toPoly.K)
    (τ : Fin (P.toPoly.arity c + P.toPoly.arity c') → Region)
    (s : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) :
    IsSemilinearNd (1 + (P.toPoly.arity c + P.toPoly.arity c'))
      {p : Fin (1 + (P.toPoly.arity c + P.toPoly.arity c')) → ℕ |
        (∀ t, ValidIdx (p ⟨0, by omega⟩) (τ t) (p ⟨1 + (t : ℕ), by omega⟩)) ∧
        P.wrpOrd (oneLoopWord u v z (p ⟨0, by omega⟩))
          (⟨c, fun t => regionPos u v (p ⟨0, by omega⟩)
            (τ (Fin.castAdd (P.toPoly.arity c') t)) (s (Fin.castAdd (P.toPoly.arity c') t))
            (p ⟨1 + ((Fin.castAdd (P.toPoly.arity c') t : Fin _) : ℕ), by omega⟩)⟩
            : P.toPoly.Atom)
          (⟨c', fun t => regionPos u v (p ⟨0, by omega⟩)
            (τ (Fin.natAdd (P.toPoly.arity c) t)) (s (Fin.natAdd (P.toPoly.arity c) t))
            (p ⟨1 + ((Fin.natAdd (P.toPoly.arity c) t : Fin _) : ℕ), by omega⟩)⟩
            : P.toPoly.Atom)} :=
  encode_semilinear u v τ s (family_congr
    (fun mS n ij => by rw [oneLoopBLW_eval])
    (wrpOrdF_semilinear (oneLoopBLW u v z) P c c'))

end OneLoopLemmas

end OneLoopSlice
