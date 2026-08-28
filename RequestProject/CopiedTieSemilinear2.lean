/-
# Route-B step 4: the two-parameter tie predicate, and discharging the tie count

The two-parameter mirror of `CopiedTieSemilinear`: the per-copy tie predicate is
`IsSliceFamilySemilinear2` (semilinear in `(mS, n, ī)`), so the two-parameter
bounded-counting axiom `isSliceFamilySemilinear2_count` yields a tie count affine on
residues in `n` with a period uniform across `mS` — exactly
`CopiedD4.TieCountAffineBudgeted`.

The two-loop slice-arithmetic facts are factored into project-agnostic general axioms
(`SliceSemilinearN.msoDefinableRel2_semilinear_general` for the MSO part,
`regularRankTerm_value2_graph_semilinear` for the rank value graph; both over a generic
`BlockLinearWord2` family).  The former project-specific residual on the `d*`-rank value
graph, `dstarRankGA_m_const_semilinear`, is now a **theorem** (no longer admitted): it is
assembled from the first-order characterisation `dstarRankGA'_eq_decodeZ_iff` and the
project-agnostic building blocks.  The copied-slice instances `msoDefinableRel2_semilinear`
and `rankOf_eq_dstar2_semilinear` are derived theorems here, obtained by instantiating the
general axioms at `copiedSliceBLW`.  No project-specific axiom remains in the inverse-zeta
tower.
-/
import RequestProject.CopiedTieCounting
import RequestProject.SliceSemilinear2

namespace CopiedTieSemilinear2

open WRP Step SliceSemilinearN MSO

/-! ## Two-loop slice-arithmetic facts

The MSO and rank bridges below are now **theorems**, derived from the project-agnostic
axioms `SliceSemilinearN.msoDefinableRel2_semilinear_general` and
`regularRankTerm_value2_graph_semilinear` by instantiating the generic block-linear word
family at the copied slice (`copiedSliceBLW`).  The former residual
`dstarRankGA_m_const_semilinear` (the `d*`-rank value graph) is now also a theorem, so no
project-specific axiom remains. -/

/-- The copied slice `Uᵐˢ(UD)ⁿDᵐˢ` as a block-linear two-parameter word family. -/
def copiedSliceBLW : BlockLinearWord2 Step :=
  ⟨[([U], 1, 0, 0), ([U, D], 0, 1, 0), ([D], 1, 0, 0)]⟩

/-- Flattening `m` copies of a singleton word `[a]` gives `m` copies of `a`. -/
private theorem flatten_replicate_singleton {α : Type*} (m : ℕ) (a : α) :
    (List.replicate m [a]).flatten = List.replicate m a := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, ih, List.replicate_succ,
        List.singleton_append]

/-- The block-linear family `copiedSliceBLW` evaluates to the copied slice. -/
theorem copiedSliceBLW_eval (mS n : ℕ) :
    copiedSliceBLW.eval mS n = copiedSlice mS n := by
  simp only [copiedSliceBLW, BlockLinearWord2.eval, copiedSlice, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, flatten_replicate_singleton,
    List.append_nil, List.append_assoc, Nat.one_mul, Nat.zero_mul, Nat.add_zero,
    Nat.zero_add]

/-- **MSO-definable ⟹ semilinear on the two-loop slice.**  Covers selection, label
and the tie-order.  Derived from the project-agnostic
`msoDefinableRel2_semilinear_general` at the `copiedSlice` instance, so all downstream
consumers see the identical conclusion. -/
theorem msoDefinableRel2_semilinear {k : ℕ} {R : List Step → (Fin k → ℕ) → Prop}
    (hR : MSODefinableRel k R) :
    IsSliceFamilySemilinear2 (fun mS n ī => R (copiedSlice mS n) ī) := by
  refine isSemilinearNd_congr ?_ (msoDefinableRel2_semilinear_general copiedSliceBLW hR)
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq, copiedSliceBLW_eval]

/-! ## The `d*`-rank value graph, as a first-order characterisation

The fibred `d*`-rank `dstarRankGA_m P hV mS n` is `dstarRankGA'` read on `copiedSlice mS n`,
i.e. the rank of the `≺`-minimal selected-`D` atom (or `0` if none).  Because `≺` compares
rank lexicographically first, the rank of the `≺`-minimal atom is exactly the **lex-minimum**
of the selected-`D` ranks.  So `dstarRankGA' P hV w = z` iff either `D` is present and `z`
is *achieved* by a selected-`D` atom and *no* selected-`D` rank is `lexLt`-below it, or `D`
is absent and `z = 0`.  This avoids any atom-vs-atom comparison and any tie-order: every
rank is compared only against the fixed target `z`. -/

/-- The strict lexicographic order on rank vectors is irreflexive. -/
theorem lexLt_irrefl {d : ℕ} (x : Fin d → ℤ) : ¬ lexLt x x := by
  rintro ⟨i, _, hi⟩; exact absurd hi (lt_irrefl _)

/-- The strict lexicographic order on rank vectors is asymmetric. -/
theorem lexLt_asymm {d : ℕ} (x y : Fin d → ℤ) (h : lexLt y x) : ¬ lexLt x y := by
  rintro ⟨i, hi_lt, hi⟩
  obtain ⟨i', hi'_lt, hi'⟩ := h
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · have := hi'_lt i hlt; omega
  · subst heq; omega
  · have := hi_lt i' hgt; omega

/-- The first-order `↔` characterisation of `dstarRankGA' P hV w = decodeZ v` as the
achieved lex-minimum of the selected-`D` ranks. -/
theorem dstarRankGA'_eq_decodeZ_iff (P : WRP.Presentation Step Step) (hV : P.Valid)
    (w : List Step) (v : Fin (P.d + P.d) → ℕ) :
    CopiedDstar.dstarRankGA' P hV w = decodeZ v ↔
      (((∃ b, P.toPoly.selectedAtom w b ∧ P.toPoly.labelOf w b = D ∧
            P.rankOf w b = decodeZ v) ∧
         (∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = D →
            ¬ lexLt (P.rankOf w b) (decodeZ v)))
       ∨ ((¬ ∃ a, P.toPoly.selectedAtom w a ∧ P.toPoly.labelOf w a = D) ∧
          (fun (_ : Fin P.d) => (0 : ℤ)) = decodeZ v)) := by
  by_cases h : ∃ a, P.toPoly.selectedAtom w a ∧ P.toPoly.labelOf w a = D
  · obtain ⟨dstar, hsel, hD, hmin, hrank⟩ := CopiedDstar.dstarRankGA'_spec P hV w h
    constructor
    · intro heq
      have hrd : P.rankOf w dstar = decodeZ v := by rw [← hrank]; exact heq
      refine Or.inl ⟨⟨dstar, hsel, hD, hrd⟩, ?_⟩
      intro b hsb hDb
      rcases hmin b hsb hDb with hdb | hwdb
      · rw [← hdb, hrd]; exact lexLt_irrefl _
      · unfold WRP.Presentation.wrpOrd at hwdb
        rcases hwdb with hlt | ⟨heqr, _⟩
        · rw [hrd] at hlt; exact lexLt_asymm _ _ hlt
        · rw [← heqr, hrd]; exact lexLt_irrefl _
    · rintro (⟨⟨b0, hsb0, hDb0, hrb0⟩, hminall⟩ | ⟨hno, _⟩)
      · rw [hrank]
        rcases hmin b0 hsb0 hDb0 with hdb0 | hwdb0
        · rw [hdb0]; exact hrb0
        · unfold WRP.Presentation.wrpOrd at hwdb0
          rcases hwdb0 with hlt | ⟨heqr, _⟩
          · rw [hrb0] at hlt; exact absurd hlt (hminall dstar hsel hD)
          · rw [heqr]; exact hrb0
      · exact absurd h hno
  · have h0 : CopiedDstar.dstarRankGA' P hV w = (fun _ => 0) := by
      unfold CopiedDstar.dstarRankGA'; rw [dif_neg h]
    constructor
    · intro heq
      exact Or.inr ⟨h, by rw [← h0]; exact heq⟩
    · rintro (⟨⟨b0, hsb0, hDb0, _⟩, _⟩ | ⟨_, heq0⟩)
      · exact absurd ⟨b0, hsb0, hDb0⟩ h
      · rw [h0]; exact heq0

/-! ## Semilinear building blocks for the `d*`-value-graph assembly -/

/-- **Corollary (b):** on a single copy `c`, the rank value graph
`rankOf ⟨c, ī⟩ = decodeZ v` is semilinear (the `ī` coordinates first, the value coords
last).  A direct instance of `regularRankTerm_value2_graph_semilinear` at `f := P.rank c`. -/
theorem rankOf_value2_c_semilinear (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2
      (fun mS n (iv : Fin (P.toPoly.arity c + (P.d + P.d)) → ℕ) =>
        P.rankOf (copiedSlice mS n)
            (⟨c, fun t => iv (Fin.castAdd (P.d + P.d) t)⟩ : P.toPoly.Atom)
          = decodeZ (fun cc => iv (Fin.natAdd (P.toPoly.arity c) cc))) := by
  have h := regularRankTerm_value2_graph_semilinear (Alpha := Step) copiedSliceBLW (P.rankReg c)
  refine isSemilinearNd_congr ?_ h
  ext iv
  simp only [familyGraph2, Set.mem_ofPred_eq, copiedSliceBLW_eval, WRP.Presentation.rankOf]

/-! ### MSO building blocks (selection, label, validity), per copy -/

/-- **`validAtom` is semilinear on the two-loop slice** — native proof.  `validAtom`
unfolds to `∀ t, ī t < (copiedSlice mS n).length = 2(mS+n)`, a finite conjunction
(`forall_fintype`) of single affine coordinate bounds (`coord_lt_semilinear`). -/
theorem validAtom2_semilinear (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n ī =>
      P.toPoly.validAtom (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom)) := by
  have hpred : (fun mS n (ī : Fin (P.toPoly.arity c) → ℕ) =>
      P.toPoly.validAtom (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom))
      = (fun mS n ī => ∀ t, ī t < 2 * (mS + n)) := by
    funext mS n ī
    simp only [Polyreg.Presentation.validAtom, length_copiedSlice]
  rw [hpred]
  exact SliceSemilinearN.IsSliceFamilySemilinear2.forall_fintype
    (fun t => SliceSemilinearN.coord_lt_semilinear _ t)

theorem sel2_semilinear (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n ī => P.toPoly.sel c (copiedSlice mS n) ī) :=
  msoDefinableRel2_semilinear (P.toPoly.selDef c)

theorem labelClass2_semilinear (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) (g : Step) :
    IsSliceFamilySemilinear2 (fun mS n ī =>
      P.toPoly.labelOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) = g) :=
  msoDefinableRel2_semilinear (P.toPoly.labelDef c g)

theorem selectedAtom2_semilinear (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n ī =>
      P.toPoly.selectedAtom (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom)) :=
  (validAtom2_semilinear P c).and (sel2_semilinear P c)

/-! ### Coordinate relocation: rank value graph in *value-first* layout

The exists/forall closures over an extra atom tuple (`exists_extra_tuple`,
`forall_extra_tuple`) place the *value* block `v : Fin (P.d+P.d) → ℕ` (the family
argument) FIRST and the bound atom tuple `ī : Fin (arity c) → ℕ` LAST, i.e. on
`Fin ((P.d+P.d) + arity c)`.  `rankOf_value2_c_semilinear` uses the opposite layout
(`ī` first, value last, on `Fin (arity c + (P.d+P.d))`).  The injective coordinate
selection `relocVAI c` swaps the two blocks, and `comap_sel` transports the rank value
graph into the value-first layout. -/

/-- The block-swap selector `Fin (arity c + (P.d+P.d)) → Fin ((P.d+P.d) + arity c)`:
the source's `ī`-block (`castAdd`) maps to the target's `ī`-block (`natAdd`), and the
source's value-block (`natAdd`) maps to the target's value-block (`castAdd`). -/
def relocVAI (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    Fin (P.toPoly.arity c + (P.d + P.d)) → Fin ((P.d + P.d) + P.toPoly.arity c) :=
  Fin.append (fun t : Fin (P.toPoly.arity c) => Fin.natAdd (P.d + P.d) t)
    (fun cc : Fin (P.d + P.d) => Fin.castAdd (P.toPoly.arity c) cc)

theorem relocVAI_injective (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    Function.Injective (relocVAI P c) := by
  intro a b hab
  have hval : ((relocVAI P c a : Fin _) : ℕ) = (relocVAI P c b : ℕ) := Fin.val_eq_of_eq hab
  unfold relocVAI at hval
  refine Fin.ext ?_
  induction a using Fin.addCases with
  | left ta =>
    induction b using Fin.addCases with
    | left tb =>
      rw [Fin.append_left, Fin.append_left, Fin.val_natAdd, Fin.val_natAdd] at hval
      simp only [Fin.val_castAdd]; omega
    | right tb =>
      rw [Fin.append_left, Fin.append_right, Fin.val_natAdd, Fin.val_castAdd] at hval
      have := tb.isLt; omega
  | right ta =>
    induction b using Fin.addCases with
    | left tb =>
      rw [Fin.append_right, Fin.append_left, Fin.val_castAdd, Fin.val_natAdd] at hval
      have := ta.isLt; omega
    | right tb =>
      rw [Fin.append_right, Fin.append_right, Fin.val_castAdd, Fin.val_castAdd] at hval
      simp only [Fin.val_natAdd]; omega

/-- **Rank value graph, value-first layout.**  `rankOf ⟨c, ī⟩ = decodeZ v` as a family
on `Fin ((P.d+P.d) + arity c)` with the value block `v` FIRST and the atom tuple `ī`
LAST — the layout produced by the extra-tuple `∃`/`∀` closures. -/
theorem rankOf_value2_c_vfirst_semilinear
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2
      (fun mS n (vi : Fin ((P.d + P.d) + P.toPoly.arity c) → ℕ) =>
        P.rankOf (copiedSlice mS n)
            (⟨c, fun t => vi (Fin.natAdd (P.d + P.d) t)⟩ : P.toPoly.Atom)
          = decodeZ (fun cc => vi (Fin.castAdd (P.toPoly.arity c) cc))) := by
  have h := IsSliceFamilySemilinear2.comap_sel (relocVAI P c) (relocVAI_injective P c)
    (rankOf_value2_c_semilinear P c)
  refine isSemilinearNd_congr ?_ h
  ext vi
  simp only [familyGraph2, Set.mem_ofPred_eq, relocVAI, Fin.append_left, Fin.append_right]

/-! ### The disjuncts of `dstarRankGA'_eq_decodeZ_iff`, as semilinear families

The two disjuncts of the characterisation are now assembled coordinate-by-coordinate from
the building blocks above.  Throughout, the family argument is the value block
`v : Fin (P.d+P.d) → ℕ` encoding `decodeZ v`. -/

/-- **D-present disjunct, achiever part:** `∃ b, sel b ∧ label b = D ∧ rankOf b = decodeZ v`,
as a semilinear family in `(mS, n, v)`.  `∃ c` (over `Fin K`) of `∃ ī` (extra tuple) of the
three conjuncts, with `ī` read past the leading value block. -/
theorem dPresentAchiever2_semilinear (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (v : Fin (P.d + P.d) → ℕ) =>
      ∃ ī : Fin (P.toPoly.arity c) → ℕ,
        P.toPoly.selectedAtom (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) ∧
        P.toPoly.labelOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) = D ∧
        P.rankOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) = decodeZ v) := by
  -- combined family on `Fin ((P.d+P.d) + arity c)`: `v` first, `ī` last
  have hsel := IsSliceFamilySemilinear2.weaken_natAdd (j := P.d + P.d)
    (selectedAtom2_semilinear P c)
  have hlab := IsSliceFamilySemilinear2.weaken_natAdd (j := P.d + P.d)
    (labelClass2_semilinear P c D)
  have hrank := rankOf_value2_c_vfirst_semilinear P c
  have hcomb := IsSliceFamilySemilinear2.exists_extra_tuple
    (k := P.d + P.d) (m := P.toPoly.arity c) (hsel.and (hlab.and hrank))
  refine isSemilinearNd_congr ?_ hcomb
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]

/-- **D-present disjunct, minimality part:** `∀ b, sel b → label b = D → ¬ lexLt (rankOf b)
(decodeZ v)`, as a semilinear family in `(mS, n, v)`.  Per-copy `∀ ī`, with the negated
`lexLt` pushed through the surjective `decodeZ` of the second atom's rank. -/
theorem dPresentMinimal2_semilinear (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (v : Fin (P.d + P.d) → ℕ) =>
      ∀ ī : Fin (P.toPoly.arity c) → ℕ,
        P.toPoly.selectedAtom (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) →
        P.toPoly.labelOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) = D →
        ¬ lexLt (P.rankOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom)) (decodeZ v)) := by
  classical
  set dd := P.d + P.d with hdd
  set ar := P.toPoly.arity c with har
  set K := dd + ar with hK
  -- layout on the body tuple `Fin (K + dd)`:
  --   v  = first  dd coords:  castAdd dd (castAdd ar ·)
  --   ī  = middle ar coords:  castAdd dd (natAdd dd ·)
  --   vb = last   dd coords:  natAdd K ·
  -- selector placing the per-copy atom tuple `ī` into the middle block
  let selI : Fin ar → Fin (K + dd) := fun t => Fin.castAdd dd (Fin.natAdd dd t)
  have hselI : Function.Injective selI := by
    intro a b hab
    have := Fin.val_eq_of_eq hab
    simp only [selI, Fin.val_castAdd, Fin.val_natAdd] at this
    exact Fin.ext (by omega)
  -- selector for the rank value graph: ī to middle, value block to `vb` (last)
  let selR : Fin (ar + dd) → Fin (K + dd) :=
    Fin.append (fun t : Fin ar => Fin.castAdd dd (Fin.natAdd dd t))
      (fun cc : Fin dd => Fin.natAdd K cc)
  have hselR : Function.Injective selR := by
    intro a b hab
    have hv : ((selR a : Fin _) : ℕ) = (selR b : ℕ) := Fin.val_eq_of_eq hab
    simp only [selR] at hv
    refine Fin.ext ?_
    induction a using Fin.addCases with
    | left ta =>
      induction b using Fin.addCases with
      | left tb =>
        rw [Fin.append_left, Fin.append_left] at hv
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢; omega
      | right tb =>
        rw [Fin.append_left, Fin.append_right] at hv
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
        have := ta.isLt; have := tb.isLt; omega
    | right ta =>
      induction b using Fin.addCases with
      | left tb =>
        rw [Fin.append_right, Fin.append_left] at hv
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv ⊢
        have := ta.isLt; have := tb.isLt; omega
      | right tb =>
        rw [Fin.append_right, Fin.append_right] at hv
        simp only [Fin.val_natAdd] at hv ⊢; omega
  -- the three innermost pieces, all over `Fin (K + dd)`
  have hsel : IsSliceFamilySemilinear2 (fun mS n (u : Fin (K + dd) → ℕ) =>
      P.toPoly.selectedAtom (copiedSlice mS n) (⟨c, fun t => u (selI t)⟩ : P.toPoly.Atom)) :=
    IsSliceFamilySemilinear2.comap_sel selI hselI (selectedAtom2_semilinear P c)
  have hlab : IsSliceFamilySemilinear2 (fun mS n (u : Fin (K + dd) → ℕ) =>
      P.toPoly.labelOf (copiedSlice mS n) (⟨c, fun t => u (selI t)⟩ : P.toPoly.Atom) = D) :=
    IsSliceFamilySemilinear2.comap_sel selI hselI (labelClass2_semilinear P c D)
  have hrank : IsSliceFamilySemilinear2 (fun mS n (u : Fin (K + dd) → ℕ) =>
      P.rankOf (copiedSlice mS n) (⟨c, fun t => u (selI t)⟩ : P.toPoly.Atom)
        = decodeZ (fun cc => u (Fin.natAdd K cc))) := by
    have h := IsSliceFamilySemilinear2.comap_sel selR hselR (rankOf_value2_c_semilinear P c)
    refine isSemilinearNd_congr ?_ h
    ext u
    simp only [familyGraph2, Set.mem_ofPred_eq]
    have e1 : (fun t => u (selR (Fin.castAdd (P.d + P.d) t)).succ.succ)
        = (fun t => u (selI t).succ.succ) := by
      funext t
      have : selR (Fin.castAdd (P.d + P.d) t) = selI t := Fin.append_left _ _ t
      rw [this]
    have e2 : (fun cc => u (selR (Fin.natAdd (P.toPoly.arity c) cc)).succ.succ)
        = (fun cc => u (Fin.natAdd K cc).succ.succ) := by
      funext cc
      have : selR (Fin.natAdd (P.toPoly.arity c) cc) = Fin.natAdd K cc := Fin.append_right _ _ cc
      rw [this]
    rw [e1, e2]
  -- `lexLt (decodeZ vb) (decodeZ v)` over `Fin (K + dd)`
  have hlex : IsSliceFamilySemilinear2 (fun mS n (u : Fin (K + dd) → ℕ) =>
      WRP.lexLt (decodeZ (fun cc => u (Fin.natAdd K cc)))
        (decodeZ (fun cc => u (Fin.castAdd dd (Fin.castAdd ar cc))))) := by
    have h := lexLt_decodeZ_sel (d := P.d) (K := K + dd)
      (fun cc => Fin.natAdd K cc) (fun cc => Fin.castAdd dd (Fin.castAdd ar cc))
    -- `lexLt_decodeZ_sel` expects `Fin (P.d + P.d) → Fin (K+dd)` selectors; `dd = P.d+P.d`
    exact h
  -- inner body: `rankOf = decodeZ vb → ¬ lexLt (decodeZ vb) (decodeZ v)`, over `Fin (K+dd)`
  have hbody : IsSliceFamilySemilinear2 (fun mS n (u : Fin (K + dd) → ℕ) =>
      P.rankOf (copiedSlice mS n) (⟨c, fun t => u (selI t)⟩ : P.toPoly.Atom)
          = decodeZ (fun cc => u (Fin.natAdd K cc)) →
      ¬ WRP.lexLt (decodeZ (fun cc => u (Fin.natAdd K cc)))
          (decodeZ (fun cc => u (Fin.castAdd dd (Fin.castAdd ar cc))))) := by
    refine isSemilinearNd_congr ?_ (hrank.not.or hlex.not)
    ext u
    simp only [familyGraph2, Set.mem_ofPred_eq]
    tauto
  -- `∀ vb` over the last `dd`-block: family over `Fin K` (= `Fin (dd + ar)`)
  have hforallVb := IsSliceFamilySemilinear2.forall_extra_tuple
    (k := K) (m := dd) hbody
  -- glue with `sel`, `label = D`: `sel → label=D → ∀ vb, ...`, over `Fin K`
  have hselK : IsSliceFamilySemilinear2 (fun mS n (u : Fin K → ℕ) =>
      P.toPoly.selectedAtom (copiedSlice mS n)
        (⟨c, fun t => u (Fin.natAdd dd t)⟩ : P.toPoly.Atom)) :=
    IsSliceFamilySemilinear2.weaken_natAdd (j := dd) (selectedAtom2_semilinear P c)
  have hlabK : IsSliceFamilySemilinear2 (fun mS n (u : Fin K → ℕ) =>
      P.toPoly.labelOf (copiedSlice mS n)
        (⟨c, fun t => u (Fin.natAdd dd t)⟩ : P.toPoly.Atom) = D) :=
    IsSliceFamilySemilinear2.weaken_natAdd (j := dd) (labelClass2_semilinear P c D)
  have hguarded : IsSliceFamilySemilinear2 (fun mS n (u : Fin K → ℕ) =>
      P.toPoly.selectedAtom (copiedSlice mS n)
          (⟨c, fun t => u (Fin.natAdd dd t)⟩ : P.toPoly.Atom) →
      P.toPoly.labelOf (copiedSlice mS n)
          (⟨c, fun t => u (Fin.natAdd dd t)⟩ : P.toPoly.Atom) = D →
      ∀ vb : Fin dd → ℕ,
        P.rankOf (copiedSlice mS n)
            (⟨c, fun t => (Fin.append u vb) (selI t)⟩ : P.toPoly.Atom)
            = decodeZ (fun cc => (Fin.append u vb) (Fin.natAdd K cc)) →
        ¬ WRP.lexLt (decodeZ (fun cc => (Fin.append u vb) (Fin.natAdd K cc)))
            (decodeZ (fun cc => (Fin.append u vb)
              (Fin.castAdd dd (Fin.castAdd ar cc))))) := by
    refine isSemilinearNd_congr ?_ (hselK.not.or (hlabK.not.or hforallVb))
    ext u
    simp only [familyGraph2, Set.mem_ofPred_eq]
    tauto
  -- `∀ ī` over the middle `ar`-block: family over `Fin dd` (the value block `v`)
  have hfinal := IsSliceFamilySemilinear2.forall_extra_tuple
    (k := dd) (m := ar) hguarded
  refine isSemilinearNd_congr ?_ hfinal
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  set vv : Fin dd → ℕ := fun i => w i.succ.succ with hvv
  -- coordinate-alignment reductions of the nested appends
  have eī : ∀ (ī : Fin ar → ℕ),
      (fun t => Fin.append vv ī (Fin.natAdd dd t)) = ī := fun ī => by
    funext t; rw [Fin.append_right]
  have eImid : ∀ (ī : Fin ar → ℕ) (vb : Fin dd → ℕ),
      (fun t => Fin.append (Fin.append vv ī) vb (selI t)) = ī := fun ī vb => by
    funext t; simp only [selI]; rw [Fin.append_left, Fin.append_right]
  have eVb : ∀ (ī : Fin ar → ℕ) (vb : Fin dd → ℕ),
      (fun cc => Fin.append (Fin.append vv ī) vb (Fin.natAdd K cc)) = vb := fun ī vb => by
    funext cc; rw [Fin.append_right]
  have eV : ∀ (ī : Fin ar → ℕ) (vb : Fin dd → ℕ),
      (fun cc => Fin.append (Fin.append vv ī) vb (Fin.castAdd dd (Fin.castAdd ar cc))) = vv :=
    fun ī vb => by funext cc; rw [Fin.append_left, Fin.append_left]
  constructor
  · -- forward: assembled `∀ ī, sel → label=D → ∀ vb, rankOf=decodeZ vb → ¬lexLt`
    --           ⟹ target `∀ ī, sel → label=D → ¬lexLt (rankOf) (decodeZ v)`
    intro h ī hsi hDi hlexlt
    have hī := h ī
    rw [eī ī] at hī
    obtain ⟨vb0, hvb0⟩ := decodeZ_surjective (P.rankOf (copiedSlice (w 0) (w 1)) (⟨c, ī⟩ : P.toPoly.Atom))
    have hr : P.rankOf (copiedSlice (w 0) (w 1)) (⟨c, ī⟩ : P.toPoly.Atom)
        = decodeZ (fun cc => Fin.append (Fin.append vv ī) vb0 (Fin.natAdd K cc)) := by
      rw [eVb ī vb0, hvb0]
    have hno := hī hsi hDi vb0
    rw [eImid ī vb0] at hno
    have hno' := hno hr
    rw [eVb ī vb0, eV ī vb0, hvb0] at hno'
    exact hno' hlexlt
  · -- backward: target ⟹ assembled
    intro h ī hsi hDi vb hrvb
    rw [eī ī] at hsi hDi
    rw [eImid ī vb, eVb ī vb] at hrvb
    have hnl := h ī hsi hDi
    rw [eVb ī vb, eV ī vb, ← hrvb]
    exact hnl

/-- **D-absent disjunct, no-`D` part:** `¬ ∃ a, sel a ∧ label a = D`, as a semilinear
family in `(mS, n, v)` (the value block `v` is ignored — cylindrified back in). -/
theorem dAbsentNoD2_semilinear (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (_v : Fin (P.d + P.d) → ℕ) =>
      ¬ ∃ ī : Fin (P.toPoly.arity c) → ℕ,
        P.toPoly.selectedAtom (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) ∧
        P.toPoly.labelOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) = D) := by
  -- `∃ ī` over a `(P.d+P.d)`-cylindrified per-copy predicate, then negate.
  have hsel := IsSliceFamilySemilinear2.weaken_natAdd (j := P.d + P.d)
    (selectedAtom2_semilinear P c)
  have hlab := IsSliceFamilySemilinear2.weaken_natAdd (j := P.d + P.d)
    (labelClass2_semilinear P c D)
  have hex := IsSliceFamilySemilinear2.exists_extra_tuple
    (k := P.d + P.d) (m := P.toPoly.arity c) (hsel.and hlab)
  refine isSemilinearNd_congr ?_ hex.not
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, not_exists, Fin.append_right]

/-- **D-absent disjunct, zero-value part:** `(fun _ => 0) = decodeZ v`, as a semilinear
family in `(mS, n, v)`.  Per-coordinate, `decodeZ v i = 0 ⟺ v(castAdd i) = v(natAdd i)`,
a `coord_diff_eq` comparison; the finite `∀ i` closes it. -/
theorem dAbsentZero2_semilinear (P : WRP.Presentation Step Step) :
    IsSliceFamilySemilinear2 (fun _mS _n (v : Fin (P.d + P.d) → ℕ) =>
      (fun (_ : Fin P.d) => (0 : ℤ)) = decodeZ v) := by
  have hcoord : ∀ i : Fin P.d, IsSliceFamilySemilinear2
      (fun _mS _n (v : Fin (P.d + P.d) → ℕ) => decodeZ v i = (0 : ℤ)) := by
    intro i
    refine isSemilinearNd_congr ?_ (coord_diff_eq_semilinear (P.d + P.d)
      (Fin.castAdd P.d i) (Fin.natAdd P.d i) (Fin.castAdd P.d i) (Fin.castAdd P.d i))
    ext v
    simp only [familyGraph2, Set.mem_ofPred_eq, decodeZ]
    constructor
    · intro h; rw [h]; ring
    · intro h; omega
  refine isSemilinearNd_congr ?_ (IsSliceFamilySemilinear2.forall_fintype hcoord)
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq, funext_iff, eq_comm]

/-- **Residual (now a theorem):** the fibred `d*`-rank family `dstarRankGA_m P hV` is
slice-const-semilinear.  Proved from the first-order characterisation
`dstarRankGA'_eq_decodeZ_iff` (the rank of the `≺`-minimal selected-`D` atom is the
achieved lex-minimum of the selected-`D` ranks) together with the per-disjunct semilinear
assemblies above.  No atom-vs-atom tie order, no `atomOrd`: every rank is compared only
against the fixed target `decodeZ v`, so the whole graph is a finite Boolean combination
of `∃`/`∀` over the bounded-counting-friendly building blocks. -/
theorem dstarRankGA_m_const_semilinear (P : WRP.Presentation Step Step) (hV : P.Valid) :
    IsSliceConstSemilinear2 (CopiedDstar.dstarRankGA_m P hV) := by
  unfold IsSliceConstSemilinear2
  -- the value graph as the disjunction of the characterisation
  have hPres := (IsSliceFamilySemilinear2.exists_fintype (ι := Fin P.toPoly.K)
      (fun c => dPresentAchiever2_semilinear P c)).and
    (IsSliceFamilySemilinear2.forall_fintype (ι := Fin P.toPoly.K)
      (fun c => dPresentMinimal2_semilinear P c))
  have hAbs := (IsSliceFamilySemilinear2.forall_fintype (ι := Fin P.toPoly.K)
      (fun c => dAbsentNoD2_semilinear P c)).and (dAbsentZero2_semilinear P)
  refine isSemilinearNd_congr ?_ (hPres.or hAbs)
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  -- bridge through the iff (note: the value graph is `g mS n = decodeZ v`, i.e.
  -- `dstarRankGA' P hV (copiedSlice mS n) = decodeZ v`)
  rw [show CopiedDstar.dstarRankGA_m P hV (w 0) (w 1)
      = CopiedDstar.dstarRankGA' P hV (copiedSlice (w 0) (w 1)) from rfl,
    dstarRankGA'_eq_decodeZ_iff P hV (copiedSlice (w 0) (w 1)) (fun i => w i.succ.succ)]
  constructor
  · rintro (⟨⟨c, ī, hsi, hDi, hri⟩, hmin⟩ | ⟨hno, hz⟩)
    · exact Or.inl ⟨⟨⟨c, ī⟩, hsi, hDi, hri⟩, fun b => hmin b.1 b.2⟩
    · refine Or.inr ⟨?_, hz⟩
      rintro ⟨b, hsb, hDb⟩
      exact hno b.1 ⟨b.2, hsb, hDb⟩
  · rintro (⟨⟨b, hsb, hDb, hrb⟩, hmin⟩ | ⟨hno, hz⟩)
    · exact Or.inl ⟨⟨b.1, b.2, hsb, hDb, hrb⟩, fun c ī => hmin ⟨c, ī⟩⟩
    · refine Or.inr ⟨fun c => ?_, hz⟩
      rintro ⟨ī, hsi, hDi⟩
      exact hno ⟨⟨c, ī⟩, hsi, hDi⟩

/-- **Rank `= d*` is semilinear on the two-loop slice.**  Now a theorem, derived from the
project-agnostic `regularRankTerm_eq_value2_semilinear` with the regular rank term
`P.rank c` (`P.rankReg c`) and the small residual `dstarRankGA_m_const_semilinear`, then
specialised to `copiedSlice` via `copiedSliceBLW_eval`.  Identical conclusion to the
former axiom, so every downstream consumer is untouched. -/
theorem rankOf_eq_dstar2_semilinear (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n ī =>
      P.rankOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom)
        = CopiedDstar.dstarRankGA_m P hV mS n) := by
  have hgen := regularRankTerm_eq_value2_semilinear (Alpha := Step) (F := copiedSliceBLW)
    (f := P.rank c) (hf := P.rankReg c) (g := CopiedDstar.dstarRankGA_m P hV)
    (hg := dstarRankGA_m_const_semilinear P hV)
  refine isSemilinearNd_congr ?_ hgen
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq, copiedSliceBLW_eval, WRP.Presentation.rankOf]

/-! ## The tie predicate (two-parameter) -/

/-- The combined-arity inner tie-order predicate (two-parameter). -/
theorem tieOrderInner2_semilinear (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c c' : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ) =>
      P.toPoly.selectedAtom (copiedSlice mS n)
          (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom) →
      P.toPoly.labelOf (copiedSlice mS n)
          (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom) = D →
      P.rankOf (copiedSlice mS n)
          (⟨c', fun t => ij (Fin.natAdd (P.toPoly.arity c) t)⟩ : P.toPoly.Atom)
          = CopiedDstar.dstarRankGA_m P hV mS n →
      P.toPoly.ord c c' (copiedSlice mS n)
          (fun t => ij (Fin.castAdd (P.toPoly.arity c') t))
          (fun t => ij (Fin.natAdd (P.toPoly.arity c) t))) := by
  have hsel := IsSliceFamilySemilinear2.weaken_natAdd (j := P.toPoly.arity c)
    (selectedAtom2_semilinear P c')
  have hlab := IsSliceFamilySemilinear2.weaken_natAdd (j := P.toPoly.arity c)
    (labelClass2_semilinear P c' D)
  have hrank := IsSliceFamilySemilinear2.weaken_natAdd (j := P.toPoly.arity c)
    (rankOf_eq_dstar2_semilinear P hV c')
  have hord := msoDefinableRel2_semilinear (P.toPoly.ordDef c c')
  refine isSemilinearNd_congr ?_
    ((hsel.not).or ((hlab.not).or ((hrank.not).or hord)))
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  tauto

/-- The per-`c'` `∀b̄` tie-order family (two-parameter). -/
theorem tieOrderForallBar2_semilinear (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c c' : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin (P.toPoly.arity c) → ℕ) =>
      ∀ bb : Fin (P.toPoly.arity c') → ℕ,
        P.toPoly.selectedAtom (copiedSlice mS n) (⟨c', bb⟩ : P.toPoly.Atom) →
        P.toPoly.labelOf (copiedSlice mS n) (⟨c', bb⟩ : P.toPoly.Atom) = D →
        P.rankOf (copiedSlice mS n) (⟨c', bb⟩ : P.toPoly.Atom)
            = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.ord c c' (copiedSlice mS n) ī bb) := by
  have h := IsSliceFamilySemilinear2.forall_extra_tuple
    (k := P.toPoly.arity c) (m := P.toPoly.arity c')
    (tieOrderInner2_semilinear P hV c c')
  refine isSemilinearNd_congr ?_ h
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]

/-- The full `∀b` tie-order guard (two-parameter). -/
theorem tieOrderForallB2_semilinear (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin (P.toPoly.arity c) → ℕ) =>
      ∀ b : P.toPoly.Atom,
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) b) := by
  have h := IsSliceFamilySemilinear2.forall_fintype
    (fun c' => tieOrderForallBar2_semilinear P hV c c')
  refine isSemilinearNd_congr ?_ h
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  constructor
  · intro h b
    obtain ⟨i, bb⟩ := b
    exact h i bb
  · intro h i bb
    exact h ⟨i, bb⟩

/-- **The full per-copy tie predicate is semilinear in `(mS, n, ī)`** — exactly the
`if`-condition of `CopiedD4.TieCountAffineBudgeted`, conjoined with `validAtom` so
the fibre is supported in range. -/
theorem tiePredicate2_semilinear (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin (P.toPoly.arity c) → ℕ) =>
      (P.toPoly.sel c (copiedSlice mS n) ī ∧
        P.toPoly.labelOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) = U ∧
        P.rankOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom)
            = CopiedDstar.dstarRankGA_m P hV mS n ∧
        ∀ b : P.toPoly.Atom,
          P.toPoly.selectedAtom (copiedSlice mS n) b →
          P.toPoly.labelOf (copiedSlice mS n) b = D →
          P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
          P.toPoly.atomOrd (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) b) ∧
      P.toPoly.validAtom (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom)) :=
  ((sel2_semilinear P c).and
    ((labelClass2_semilinear P c U).and
      ((rankOf_eq_dstar2_semilinear P hV c).and (tieOrderForallB2_semilinear P hV c)))).and
    (validAtom2_semilinear P c)

/-- **`domain` is semilinear on the two-loop slice** — native proof.  `domain` is
MSO-definable (`domainDef`, a `Sentence`), so it is `MSODefinableRel 0`; apply
`msoDefinableRel2_semilinear` at arity `0`, then cylindrify the `k` (ignored) atom
coordinates back in with the proved `weaken_natAdd`. -/
theorem domain2_semilinear (P : WRP.Presentation Step Step) (k : ℕ) :
    IsSliceFamilySemilinear2 (fun mS n (_ : Fin k → ℕ) =>
      P.toPoly.domain (copiedSlice mS n)) := by
  have hdom_mso : MSODefinableRel 0 (fun w (_ : Fin 0 → ℕ) => P.toPoly.domain w) := by
    obtain ⟨φ, hφ⟩ := P.toPoly.domainDef
    refine ⟨φ, fun w ρ => ?_⟩
    rw [Subsingleton.elim ρ Fin.elim0]
    exact hφ w
  exact SliceSemilinearN.IsSliceFamilySemilinear2.weaken_natAdd (j := k)
    (msoDefinableRel2_semilinear hdom_mso)

/-! ## Discharging `TieCountAffineBudgeted` -/

/-- The domain-gated tie predicate for copy `c`: the `TieCountAffineBudgeted`
if-condition, plus `validAtom` (range support) and `domain` (so its count is `0` —
hence affine — at non-domain rows). -/
def tieΦ (P : WRP.Presentation Step Step) (hV : P.Valid) (c : Fin P.toPoly.K) :
    ℕ → ℕ → (Fin (P.toPoly.arity c) → ℕ) → Prop :=
  fun mS n ī =>
    ((P.toPoly.sel c (copiedSlice mS n) ī ∧
      P.toPoly.labelOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) = U ∧
      P.rankOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom)
          = CopiedDstar.dstarRankGA_m P hV mS n ∧
      ∀ b : P.toPoly.Atom,
        P.toPoly.selectedAtom (copiedSlice mS n) b →
        P.toPoly.labelOf (copiedSlice mS n) b = D →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom) b) ∧
      P.toPoly.validAtom (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom)) ∧
    P.toPoly.domain (copiedSlice mS n)

theorem tieΦ_semilinear (P : WRP.Presentation Step Step) (hV : P.Valid) (c : Fin P.toPoly.K) :
    IsSliceFamilySemilinear2 (tieΦ P hV c) :=
  (tiePredicate2_semilinear P hV c).and (domain2_semilinear P (P.toPoly.arity c))

/-- `tieΦ` membership implies the atom is in range. -/
theorem tieΦ_validAtom {P : WRP.Presentation Step Step} {hV : P.Valid} {c : Fin P.toPoly.K}
    {mS n : ℕ} {ī : Fin (P.toPoly.arity c) → ℕ} (h : tieΦ P hV c mS n ī) :
    ∀ i, ī i < (copiedSlice mS n).length := h.1.2

theorem tieΦ_finite (P : WRP.Presentation Step Step) (hV : P.Valid) (c : Fin P.toPoly.K)
    (mS n : ℕ) : Set.Finite {ī : Fin (P.toPoly.arity c) → ℕ | tieΦ P hV c mS n ī} :=
  SliceSemilinearN.finite_setOf_of_support (fun n ī => tieΦ P hV c mS n ī) n
    (Fintype.piFinset (fun _ => Finset.range (copiedSlice mS n).length))
    (fun _ī h => Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (tieΦ_validAtom h i)))

/-- **The pin-free route discharges `TieCountAffineBudgeted`.** -/
theorem tieCountAffineBudgeted_route_b
    (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ) :
    CopiedD4.TieCountAffineBudgeted P hV C := by
  classical
  choose pc hpc1 hpc using fun c =>
    SliceSemilinearN.isSliceFamilySemilinear2_count (tieΦ_semilinear P hV c) C
      (fun mS n => tieΦ_finite P hV c mS n)
  refine ⟨∏ c : Fin P.toPoly.K, pc c, 1,
    Finset.one_le_prod' (fun c _ => hpc1 c), le_refl 1, fun mS _hmS hbudget => ?_⟩
  have hpcdvd : ∀ c, pc c ∣ ∏ c : Fin P.toPoly.K, pc c :=
    fun c => Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  have hp0 : 1 ≤ ∏ c : Fin P.toPoly.K, pc c := Finset.one_le_prod' (fun c _ => hpc1 c)
  -- per-copy count bound: domain rows from the budget, non-domain rows are empty
  have hbound : ∀ c n,
      Nat.card {ī : Fin (P.toPoly.arity c) → ℕ | tieΦ P hV c mS n ī} ≤ C * (mS + n + 1) := by
    intro c n
    by_cases hdom : P.toPoly.domain (copiedSlice mS n)
    · have hfin := tieΦ_finite P hV c mS n
      rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin,
        ← Finset.length_toList hfin.toFinset]
      refine hbudget n hdom c hfin.toFinset.toList hfin.toFinset.nodup_toList (fun x hx => ?_)
      rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hx
      exact ⟨tieΦ_validAtom hx, hx.1.1.1⟩
    · have hempty : {ī : Fin (P.toPoly.arity c) → ℕ | tieΦ P hV c mS n ī} = ∅ := by
        ext ī; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hdom h.2
      rw [hempty]; simp
  refine ⟨fun n => ∑ c : Fin P.toPoly.K,
    Nat.card {ī : Fin (P.toPoly.arity c) → ℕ | tieΦ P hV c mS n ī}, 0, ?_, ?_⟩
  · -- affine on residues at the common period
    refine SliceSemilinearN.affineOnResiduesAt_sum Finset.univ hp0 _ (fun c _ => ?_)
    exact (hpc c mS (fun n => hbound c n)).of_dvd (hpc1 c) (hpcdvd c) hp0
  · -- agreement with the TieCountAffineBudgeted sum
    intro n _hn hdom _hDpres
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [SliceSemilinearN.natCard_setOf_eq_filter_card (fun n ī => tieΦ P hV c mS n ī) n
      (Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
        Finset.range (copiedSlice mS n).length))
      (fun ī h => Fintype.mem_piFinset.mpr
        (fun i => Finset.mem_range.mpr (tieΦ_validAtom h i))),
      Finset.card_filter]
    refine Finset.sum_congr rfl (fun ī hī => ?_)
    have hrange : ∀ i, ī i < (copiedSlice mS n).length := by
      intro i; have := Fintype.mem_piFinset.mp hī i; exact Finset.mem_range.mp this
    refine if_congr ?_ rfl rfl
    constructor
    · exact fun h => h.1.1
    · exact fun h => ⟨⟨h, hrange⟩, hdom⟩

/-! ## The general-arity capstone -/

/-- **Inverse zeta is not WRP (general arity).**  No WRP transduction left-inverts the
zeta map on Dyck paths.  Closes the route-B tower: the pin-free tie count
(`tieCountAffineBudgeted_route_b`) discharges `TieCountAffineBudgeted`, which the
existing tower (`fas_count_affine_fibred_budgeted_of_tie`, `inverse_zeta_not_wrp_of_fas`)
turns into the non-WRP statement.  Over the genuine `WRP.IsWRP` semantics; admits only
the standard Presburger / two-loop slice-arithmetic facts plus `SliceMSO.buchi`. -/
theorem inverse_zeta_not_wrp :
    ¬ ∃ T : List Step → Option (List Step),
      WRP.IsWRP T ∧ ∀ P, IsDyckPath P → T (zetaMap P) = some P :=
  CopiedD4.inverse_zeta_not_wrp_of_fas (fun P hV C =>
    CopiedD4.fas_count_affine_fibred_budgeted_of_tie P hV C
      (tieCountAffineBudgeted_route_b P hV C))

end CopiedTieSemilinear2
