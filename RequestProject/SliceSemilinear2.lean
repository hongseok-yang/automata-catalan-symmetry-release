/-
# Two-parameter slice atom-families (route-B step 4)

`SliceSemilinearN.IsSliceFamilySemilinear` packs one parameter `n` at coordinate 0
and the atom coordinates after it.  For the uniform-period tie count we need TWO
parameters `(mS, n)` — the copied slice `Uᵐˢ(UD)ⁿDᵐˢ` loops in both, and the
`n`-period must be uniform across `mS`.  This file is the two-parameter mirror:
`(mS, n)` at coordinates `0, 1`, atom coordinates after.  The generic
`IsSemilinearNd` closures of `SliceSemilinearN` carry over unchanged; only the
family-level packing changes (two leading coordinates instead of one).
-/
import RequestProject.SliceSemilinearN
import RequestProject.CopiedAffineAt
import RequestProject.MSO
import RequestProject.WRP

namespace SliceSemilinearN

/-- Pack `(mS, n, ī)` into `Fin (k+2) → ℕ` with `mS, n` first. -/
def familyGraph2 {k : ℕ} (Φ : ℕ → ℕ → (Fin k → ℕ) → Prop) : Set (Fin (k + 2) → ℕ) :=
  {v | Φ (v 0) (v 1) (fun i => v i.succ.succ)}

/-- A two-parameter slice atom-family `Φ : ℕ → ℕ → (Fin k → ℕ) → Prop` is
semilinear when its packed `(mS, n, ī)`-graph is. -/
def IsSliceFamilySemilinear2 {k : ℕ} (Φ : ℕ → ℕ → (Fin k → ℕ) → Prop) : Prop :=
  IsSemilinearNd (k + 2) (familyGraph2 Φ)

/-- Closed under conjunction. -/
theorem IsSliceFamilySemilinear2.and {k : ℕ} {Φ Ψ : ℕ → ℕ → (Fin k → ℕ) → Prop}
    (hΦ : IsSliceFamilySemilinear2 Φ) (hΨ : IsSliceFamilySemilinear2 Ψ) :
    IsSliceFamilySemilinear2 (fun mS n ī => Φ mS n ī ∧ Ψ mS n ī) := by
  refine isSemilinearNd_congr ?_ (isSemilinearNd_inter hΦ hΨ)
  ext v; simp [familyGraph2, Set.mem_inter_iff]

/-- Closed under disjunction. -/
theorem IsSliceFamilySemilinear2.or {k : ℕ} {Φ Ψ : ℕ → ℕ → (Fin k → ℕ) → Prop}
    (hΦ : IsSliceFamilySemilinear2 Φ) (hΨ : IsSliceFamilySemilinear2 Ψ) :
    IsSliceFamilySemilinear2 (fun mS n ī => Φ mS n ī ∨ Ψ mS n ī) := by
  refine isSemilinearNd_congr ?_ (SliceSemilinear.isSemilinearNd_union hΦ hΨ)
  ext v; simp [familyGraph2, Set.mem_union]

/-- Closed under negation. -/
theorem IsSliceFamilySemilinear2.not {k : ℕ} {Φ : ℕ → ℕ → (Fin k → ℕ) → Prop}
    (hΦ : IsSliceFamilySemilinear2 Φ) :
    IsSliceFamilySemilinear2 (fun mS n ī => ¬ Φ mS n ī) := by
  refine isSemilinearNd_congr ?_ (isSemilinearNd_compl hΦ)
  ext v; simp [familyGraph2, Set.mem_compl_iff]

/-- Coordinate selection for the two-parameter cylindrification: keep `0,1` (the
parameters), shift the atom coordinates up by `j` (skipping the `j` dummies). -/
private def selWeaken (j k : ℕ) : Fin (k + 2) → Fin (j + k + 2) := fun c =>
  if h : (c : ℕ) < 2 then ⟨c, by omega⟩ else ⟨(c : ℕ) + j, by have := c.isLt; omega⟩

private theorem selWeaken_injective (j k : ℕ) : Function.Injective (selWeaken j k) := by
  intro a b hab
  apply Fin.ext
  unfold selWeaken at hab
  split_ifs at hab with ha hb hb <;> simp only [Fin.mk.injEq] at hab <;> omega

private theorem selWeaken_zero (j k : ℕ) : selWeaken j k 0 = 0 := by
  apply Fin.ext; simp [selWeaken]

private theorem selWeaken_one (j k : ℕ) : selWeaken j k 1 = 1 := by
  apply Fin.ext
  unfold selWeaken
  have h1 : ((1 : Fin (k + 2)) : ℕ) = 1 := by simp
  rw [dif_pos (by rw [h1]; omega)]
  simp

private theorem selWeaken_succ (j k : ℕ) (i : Fin k) :
    selWeaken j k i.succ.succ = (Fin.natAdd j i).succ.succ := by
  apply Fin.ext
  unfold selWeaken
  rw [dif_neg (show ¬ ((i.succ.succ : Fin (k + 2)) : ℕ) < 2 by simp [Fin.val_succ])]
  simp only [Fin.val_succ, Fin.val_natAdd]
  omega

/-- **Cylindrification** (adding dummy atom coordinates), two-parameter form.  Native
proof: the weakened family graph is the preimage of `familyGraph2 Φ` under the
injective coordinate selection `selWeaken` (keep the two parameters, shift the atom
coordinates past the `j` dummies), so `isSemilinearNd_comap_injective` applies. -/
theorem IsSliceFamilySemilinear2.weaken_natAdd {j k : ℕ} {Φ : ℕ → ℕ → (Fin k → ℕ) → Prop}
    (hΦ : IsSliceFamilySemilinear2 Φ) :
    IsSliceFamilySemilinear2
      (fun mS n (ij : Fin (j + k) → ℕ) => Φ mS n (fun t => ij (Fin.natAdd j t))) := by
  have hcomap := isSemilinearNd_comap_injective (selWeaken j k) (selWeaken_injective j k) hΦ
  refine isSemilinearNd_congr ?_ hcomap
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq]
  rw [selWeaken_zero, selWeaken_one]
  have htup : (fun i : Fin k => v (selWeaken j k i.succ.succ))
      = (fun t : Fin k => v (Fin.natAdd j t).succ.succ) :=
    funext (fun i => by rw [selWeaken_succ])
  rw [htup]

/-- The atom-coordinate index `c - 2` (for `c ≥ 2`) packaged as a `Fin k`. -/
private def selRelocateIdx {k : ℕ} (c : Fin (k + 2)) (h : ¬ (c : ℕ) < 2) : Fin k :=
  ⟨(c : ℕ) - 2, by have := c.isLt; omega⟩

/-- Lift a coordinate selection `sel : Fin k → Fin K` to `Fin (k+2) → Fin (K+2)`,
fixing the two parameter coordinates `0, 1` and sending atom coordinate `i+2` to
`(sel i)+2`. -/
private def selRelocate {k K : ℕ} (sel : Fin k → Fin K) : Fin (k + 2) → Fin (K + 2) :=
  fun c => if h : (c : ℕ) < 2 then ⟨c, by omega⟩
    else ⟨(sel (selRelocateIdx c h) : Fin K) + 2,
      by have := (sel (selRelocateIdx c h)).isLt; omega⟩

private theorem selRelocate_zero {k K : ℕ} (sel : Fin k → Fin K) :
    selRelocate sel 0 = 0 := by
  apply Fin.ext; simp [selRelocate]

private theorem selRelocate_one {k K : ℕ} (sel : Fin k → Fin K) :
    selRelocate sel 1 = 1 := by
  apply Fin.ext
  unfold selRelocate
  have h1 : ((1 : Fin (k + 2)) : ℕ) = 1 := by simp
  rw [dif_pos (by rw [h1]; omega)]; simp

private theorem selRelocate_succ {k K : ℕ} (sel : Fin k → Fin K) (i : Fin k) :
    selRelocate sel i.succ.succ = (sel i).succ.succ := by
  apply Fin.ext
  unfold selRelocate
  rw [dif_neg (show ¬ ((i.succ.succ : Fin (k + 2)) : ℕ) < 2 by simp [Fin.val_succ])]
  have harg : selRelocateIdx (i.succ.succ) (by simp [Fin.val_succ]) = i := by
    apply Fin.ext; simp [selRelocateIdx, Fin.val_succ]
  have hsv : (sel (selRelocateIdx (i.succ.succ) (by simp [Fin.val_succ]))).val
      = (sel i).val := Fin.val_eq_of_eq (congrArg sel harg)
  show (sel (selRelocateIdx (i.succ.succ) (by simp [Fin.val_succ]))).val + 2
      = (sel i).succ.succ.val
  rw [hsv]; simp [Fin.val_succ]

private theorem selRelocate_injective {k K : ℕ} (sel : Fin k → Fin K)
    (hsel : Function.Injective sel) : Function.Injective (selRelocate sel) := by
  intro a b hab
  apply Fin.ext
  unfold selRelocate at hab
  split_ifs at hab with ha hb hb
  · simpa using hab
  · exfalso; simp only [Fin.mk.injEq] at hab
    have := (sel (selRelocateIdx b hb)).isLt; omega
  · exfalso; simp only [Fin.mk.injEq] at hab
    have := (sel (selRelocateIdx a ha)).isLt; omega
  · simp only [Fin.mk.injEq, add_left_inj] at hab
    have hse : sel (selRelocateIdx a ha) = sel (selRelocateIdx b hb) := by
      apply Fin.ext; rw [hab]
    have := hsel hse
    simp only [selRelocateIdx, Fin.mk.injEq] at this
    omega

/-- **Cylindrification (general coordinate relocation), two-parameter form.**  For any
injective coordinate selection `sel : Fin k → Fin K`, reading a semilinear family `Φ`
through `sel` (keeping the two parameters and relocating the atom coordinates) is again
semilinear.  Generalises `weaken_natAdd` (which is the special case `sel = Fin.natAdd j`). -/
theorem IsSliceFamilySemilinear2.comap_sel {k K : ℕ} (sel : Fin k → Fin K)
    (hsel : Function.Injective sel) {Φ : ℕ → ℕ → (Fin k → ℕ) → Prop}
    (hΦ : IsSliceFamilySemilinear2 Φ) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin K → ℕ) => Φ mS n (fun t => ī (sel t))) := by
  have hcomap := isSemilinearNd_comap_injective (selRelocate sel)
    (selRelocate_injective sel hsel) hΦ
  refine isSemilinearNd_congr ?_ hcomap
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq]
  rw [selRelocate_zero, selRelocate_one]
  have htup : (fun i : Fin k => v (selRelocate sel i.succ.succ))
      = (fun t : Fin k => v (sel t).succ.succ) :=
    funext (fun i => by rw [selRelocate_succ])
  rw [htup]

/-- Finite `∀i` of two-parameter semilinear families is semilinear. -/
theorem IsSliceFamilySemilinear2.forall_fintype {k : ℕ} {ι : Type*} [Fintype ι]
    {Φ : ι → ℕ → ℕ → (Fin k → ℕ) → Prop} (hΦ : ∀ i, IsSliceFamilySemilinear2 (Φ i)) :
    IsSliceFamilySemilinear2 (fun mS n ī => ∀ i, Φ i mS n ī) := by
  classical
  refine isSemilinearNd_congr ?_
    (isSemilinearNd_biInter Finset.univ (fun i => familyGraph2 (Φ i)) (fun i _ => hΦ i))
  ext w
  simp only [familyGraph2, Set.mem_iInter, Set.mem_ofPred_eq, Finset.mem_univ, forall_const]

/-! ## `∀`-elimination (two-parameter) -/

private theorem tail_snoc2 {k : ℕ} (v : Fin (k + 1) → ℕ) (t : ℕ) :
    Fin.tail (@Fin.snoc (k + 1) (fun _ => ℕ) v t) = @Fin.snoc k (fun _ => ℕ) (Fin.tail v) t := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [Fin.tail]
  | cast i' =>
      simp only [Fin.tail]
      rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      simp only [Fin.tail]

/-- Universal over one extra atom coordinate (two-parameter). -/
theorem IsSliceFamilySemilinear2.forall_extra {k : ℕ}
    {Ψ : ℕ → ℕ → (Fin (k + 1) → ℕ) → Prop} (hΨ : IsSliceFamilySemilinear2 Ψ) :
    IsSliceFamilySemilinear2
      (fun mS n (ī : Fin k → ℕ) => ∀ t : ℕ, Ψ mS n (@Fin.snoc k (fun _ => ℕ) ī t)) := by
  have h := isSemilinearNd_forall_last (d := k + 2) hΨ
  refine isSemilinearNd_congr ?_ h
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  have hz : ∀ t, (@Fin.snoc (k + 2) (fun _ => ℕ) w t) 0 = w 0 := fun t => by
    rw [show (0 : Fin (k + 3)) = Fin.castSucc 0 from (Fin.castSucc_zero).symm, Fin.snoc_castSucc]
  have ho : ∀ t, (@Fin.snoc (k + 2) (fun _ => ℕ) w t) 1 = w 1 := fun t => by
    rw [show (1 : Fin (k + 3)) = Fin.castSucc 1 from by rfl, Fin.snoc_castSucc]
  have ht : ∀ t, (fun i : Fin (k + 1) => (@Fin.snoc (k + 2) (fun _ => ℕ) w t) i.succ.succ)
      = @Fin.snoc k (fun _ => ℕ) (fun i : Fin k => w i.succ.succ) t := fun t => by
    have e1 : Fin.tail (@Fin.snoc (k + 2) (fun _ => ℕ) w t)
        = @Fin.snoc (k + 1) (fun _ => ℕ) (Fin.tail w) t := tail_snoc2 w t
    have e2 := tail_snoc2 (Fin.tail w) t
    funext i
    rw [show (@Fin.snoc (k + 2) (fun _ => ℕ) w t) i.succ.succ
        = Fin.tail (Fin.tail (@Fin.snoc (k + 2) (fun _ => ℕ) w t)) i from rfl, e1, e2]
    rfl
  constructor
  · intro hL t; have := hL t; rw [hz, ho, ht] at this; exact this
  · intro hR t; rw [hz, ho, ht]; exact hR t

/-- Universal over a whole extra atom tuple (two-parameter). -/
theorem IsSliceFamilySemilinear2.forall_extra_tuple {k : ℕ} :
    ∀ {m : ℕ} {Ψ : ℕ → ℕ → (Fin (k + m) → ℕ) → Prop},
      IsSliceFamilySemilinear2 Ψ →
      IsSliceFamilySemilinear2 (fun mS n (ii : Fin k → ℕ) =>
        ∀ bb : Fin m → ℕ, Ψ mS n (Fin.append ii bb)) := by
  intro m
  induction m with
  | zero =>
      intro Ψ hΨ
      refine isSemilinearNd_congr ?_ hΨ
      ext w
      simp only [familyGraph2, Set.mem_ofPred_eq]
      have heq : ∀ bb : Fin 0 → ℕ,
          Fin.append (fun i : Fin k => w i.succ.succ) bb = (fun i : Fin k => w i.succ.succ) := by
        intro bb; funext i
        have hlt : (i : ℕ) < k := by omega
        simp only [Fin.append, Fin.addCases, dif_pos hlt]
        congr 1
      constructor
      · intro h bb; rw [heq bb]; exact h
      · intro h; have := h (fun i => i.elim0); rwa [heq] at this
  | succ m ih =>
      intro Ψ hΨ
      have hrec := ih (IsSliceFamilySemilinear2.forall_extra hΨ)
      refine isSemilinearNd_congr ?_ hrec
      ext w
      simp only [familyGraph2, Set.mem_ofPred_eq]
      constructor
      · intro h bb
        have hthis := h (Fin.init bb) (bb (Fin.last m))
        rwa [← Fin.append_snoc, Fin.snoc_init_self] at hthis
      · intro h c x
        have hthis := h (@Fin.snoc m (fun _ => ℕ) c x)
        rwa [Fin.append_snoc] at hthis

/-! ## `∃`-introduction (two-parameter), as `¬∀¬` of the `∀`-closures -/

/-- Finite `∃i` of two-parameter semilinear families is semilinear. -/
theorem IsSliceFamilySemilinear2.exists_fintype {k : ℕ} {ι : Type*} [Fintype ι]
    {Φ : ι → ℕ → ℕ → (Fin k → ℕ) → Prop} (hΦ : ∀ i, IsSliceFamilySemilinear2 (Φ i)) :
    IsSliceFamilySemilinear2 (fun mS n ī => ∃ i, Φ i mS n ī) := by
  refine isSemilinearNd_congr ?_
    (IsSliceFamilySemilinear2.forall_fintype (fun i => (hΦ i).not)).not
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, not_forall, not_not]

/-- Existential over a whole extra atom tuple (two-parameter). -/
theorem IsSliceFamilySemilinear2.exists_extra_tuple {k m : ℕ}
    {Ψ : ℕ → ℕ → (Fin (k + m) → ℕ) → Prop} (hΨ : IsSliceFamilySemilinear2 Ψ) :
    IsSliceFamilySemilinear2 (fun mS n (ii : Fin k → ℕ) =>
      ∃ bb : Fin m → ℕ, Ψ mS n (Fin.append ii bb)) := by
  refine isSemilinearNd_congr ?_
    (IsSliceFamilySemilinear2.forall_extra_tuple hΨ.not).not
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, not_forall, not_not]

/-! ## Two-parameter bounded counting (admitted) and the `Finset` bridge -/

/-- **Bounded Presburger counting, two-parameter form** (Ginsburg–Spanier,
`lem:presburger-counting`).  Admitted as a standard fact.  For a semilinear
`(mS, n, ī)`-family with finite fibres, the `n`-period of the count is fixed by the
(`mS`-independent) semilinear structure, so a single `p0` works **uniformly across
`mS`**; the per-`mS` linear bound `≤ C·(mS+n+1)` ensures the count for that row is
affine (degree ≤ 1) rather than higher-degree.  The per-`mS` bound (rather than a
global one) matches `TieCountAffineBudgeted`, which exposes its budget per row. -/
axiom isSliceFamilySemilinear2_count {k : ℕ}
    {Φ : ℕ → ℕ → (Fin k → ℕ) → Prop} (hΦ : IsSliceFamilySemilinear2 Φ) (C : ℕ)
    (hfin : ∀ mS n, Set.Finite {ī : Fin k → ℕ | Φ mS n ī}) :
    ∃ p0 : ℕ, 1 ≤ p0 ∧ ∀ mS : ℕ,
      (∀ n, Nat.card {ī : Fin k → ℕ | Φ mS n ī} ≤ C * (mS + n + 1)) →
      SlicePeriodStar.AffineOnResiduesAt p0 (fun n => Nat.card {ī : Fin k → ℕ | Φ mS n ī})

/-! ## `AffineOnResiduesAt` helpers for the count assembly -/

/-- The zero function is affine on residues. -/
theorem affineOnResiduesAt_zero (p : ℕ) :
    SlicePeriodStar.AffineOnResiduesAt p (fun _ => 0) :=
  ⟨0, fun _ _ => ⟨0, 0, fun _ => by simp⟩⟩

/-- A finite sum of affine-on-residues functions (same period) is affine on
residues. -/
theorem affineOnResiduesAt_sum {ι : Type*} (s : Finset ι) {p : ℕ} (hp : 1 ≤ p)
    (f : ι → ℕ → ℕ) (hf : ∀ i ∈ s, SlicePeriodStar.AffineOnResiduesAt p (f i)) :
    SlicePeriodStar.AffineOnResiduesAt p (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using affineOnResiduesAt_zero p
  | insert a s ha ih =>
      have hsum : (fun n => ∑ i ∈ insert a s, f i n)
          = (fun n => f a n + ∑ i ∈ s, f i n) := by
        funext n; rw [Finset.sum_insert ha]
      rw [hsum]
      exact SlicePeriodStar.AffineOnResiduesAt.add hp (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-! ## Affine coordinate bounds are semilinear -/

/-- The strict-order set on `Fin 2 → ℕ` is semilinear: it is the single linear set
`![0,1] + ℕ·{![1,1], ![0,1]}`. -/
theorem order_lt_semilinear : IsSemilinearSet {w : Fin 2 → ℕ | w 0 < w 1} := by
  have hne : (![1, 1] : Fin 2 → ℕ) ≠ ![0, 1] := by decide
  have heq : {w : Fin 2 → ℕ | w 0 < w 1} = LinearSet 2 ![0, 1] {![1, 1], ![0, 1]} := by
    ext w
    simp only [LinearSet, Set.mem_ofPred_eq]
    constructor
    · intro hlt
      refine ⟨fun s => if s = ![1, 1] then w 0 else w 1 - w 0 - 1, ?_⟩
      funext i
      fin_cases i <;> simp [Finset.sum_pair hne, Ne.symm hne]
      omega
    · rintro ⟨coeffs, hw⟩
      have h0 := congrFun hw 0
      have h1 := congrFun hw 1
      simp [Finset.sum_pair hne] at h0 h1
      omega
  rw [heq]
  exact (repo_linearSet_isLinearSet 2 ![0, 1] {![1, 1], ![0, 1]}).isSemilinearSet

/-- Coordinate hom: `v ↦ (v at the `t`-th atom coordinate, 2·v₀ + 2·v₁)`. -/
def coordHom (k : ℕ) (t : Fin k) : (Fin (k + 2) → ℕ) →+ (Fin 2 → ℕ) where
  toFun v := ![v t.succ.succ, 2 * v 0 + 2 * v 1]
  map_zero' := by funext i; fin_cases i <;> simp
  map_add' x y := by funext i; fin_cases i <;> simp; ring

/-- A single atom coordinate bounded by `2(mS+n)` is semilinear on the two-loop slice
(the preimage of the strict-order set under `coordHom`). -/
theorem coord_lt_semilinear (k : ℕ) (t : Fin k) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin k → ℕ) => ī t < 2 * (mS + n)) := by
  have hpre : IsSemilinearSet (coordHom k t ⁻¹' {w : Fin 2 → ℕ | w 0 < w 1}) :=
    order_lt_semilinear.preimage (coordHom k t)
  refine isSemilinearNd_congr ?_ (mathlib_to_isSemilinearNd (k + 2) _ hpre)
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq, Set.mem_preimage, coordHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- Pair-difference comparison hom: `v ↦ (v p1 + v p4, v p3 + v p2)`, so the strict
order on the image encodes `(v p1 - v p2) < (v p3 - v p4)` over ℤ. -/
def pairCmpHom (k : ℕ) (p1 p2 p3 p4 : Fin k) : (Fin (k + 2) → ℕ) →+ (Fin 2 → ℕ) where
  toFun v := ![v p1.succ.succ + v p4.succ.succ, v p3.succ.succ + v p2.succ.succ]
  map_zero' := by funext i; fin_cases i <;> simp
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring

/-- A difference of two coordinates is `<` a difference of two others: semilinear (the
ℤ-comparison `ī p1 - ī p2 < ī p3 - ī p4`, the atom of every rank/`decodeZ` comparison). -/
theorem coord_diff_lt_semilinear (k : ℕ) (p1 p2 p3 p4 : Fin k) :
    IsSliceFamilySemilinear2 (fun _mS _n (ī : Fin k → ℕ) =>
      (ī p1 : ℤ) - (ī p2 : ℤ) < (ī p3 : ℤ) - (ī p4 : ℤ)) := by
  have hpre : IsSemilinearSet (pairCmpHom k p1 p2 p3 p4 ⁻¹' {w : Fin 2 → ℕ | w 0 < w 1}) :=
    order_lt_semilinear.preimage (pairCmpHom k p1 p2 p3 p4)
  refine isSemilinearNd_congr ?_ (mathlib_to_isSemilinearNd (k + 2) _ hpre)
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq, Set.mem_preimage, pairCmpHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- A difference of two coordinates equals a difference of two others: semilinear (from
the strict comparison via `¬< ∧ ¬>`). -/
theorem coord_diff_eq_semilinear (k : ℕ) (p1 p2 p3 p4 : Fin k) :
    IsSliceFamilySemilinear2 (fun _mS _n (ī : Fin k → ℕ) =>
      (ī p1 : ℤ) - (ī p2 : ℤ) = (ī p3 : ℤ) - (ī p4 : ℤ)) := by
  refine isSemilinearNd_congr ?_
    ((coord_diff_lt_semilinear k p1 p2 p3 p4).not.and (coord_diff_lt_semilinear k p3 p4 p1 p2).not)
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq]
  omega

/-! ## General block-linear two-parameter word families, and the MSO bridge

The §9 tie-counting argument reads MSO-definable position relations along the copied
slice `Uᵐˢ(UD)ⁿDᵐˢ`.  The only project-specific ingredient in that bridge is the slice
word itself; the hypothesis (`MSO.MSODefinableRel`) and the conclusion
(`IsSliceFamilySemilinear2`) are already general.  We isolate the slice as an instance
of a generic **block-linear two-parameter word family**: a fixed finite list of blocks,
each a base word repeated an `ℕ`-affine-in-`(mS, n)` number of times.  This lets the
admitted bridge be stated with no reference to `WRP`/`copiedSlice`/`Step`. -/

/-- A block-linear two-parameter word family over an alphabet `Alpha`: a finite list of
blocks, each `(baseWord, a_mS, a_n, const)`, where block `i` contributes
`baseWord` repeated `a_mS·mS + a_n·n + const` times.  The canonical instance for the
copied slice `Uᵐˢ(UD)ⁿDᵐˢ` is `[([U],1,0,0), ([U,D],0,1,0), ([D],1,0,0)]`. -/
structure BlockLinearWord2 (Alpha : Type*) where
  /-- The blocks, each `(baseWord, a_mS, a_n, const)`. -/
  blocks : List (List Alpha × ℕ × ℕ × ℕ)

/-- Evaluate a block-linear word family at parameters `(mS, n)`: concatenate, for each
block `(b, a_mS, a_n, c)`, the word `b` repeated `a_mS·mS + a_n·n + c` times. -/
def BlockLinearWord2.eval {Alpha : Type*} (F : BlockLinearWord2 Alpha) (mS n : ℕ) :
    List Alpha :=
  (F.blocks.map fun (b, aMS, aN, c) =>
    (List.replicate (aMS * mS + aN * n + c) b).flatten).flatten

/-- **MSO-definable relations over a block-linear two-parameter word family are
semilinear.**  Admitted as a standard fact: by Büchi–Elgot–Trakhtenbrot the relation `R`
is recognised by a finite automaton on the marked alphabet, and the marked word read
along `F.eval mS n` ranges over a regular two-loop slice language, whose Parikh image is
semilinear (Ginsburg–Spanier).  Both hypotheses are load-bearing: `[Fintype Alpha]` is
needed for the MSO⇒automaton step, and the block-linear shape of `F` is needed for the
slice language to be regular (an arbitrary `slice : ℕ → ℕ → List Alpha` can encode a
non-semilinear position set).  This is the same kind of fact as the kept counting axiom
`isSliceFamilySemilinear2_count`, and is project-agnostic in exactly the same way. -/
axiom msoDefinableRel2_semilinear_general {Alpha : Type*} [Fintype Alpha] {k : ℕ}
    (F : BlockLinearWord2 Alpha)
    {R : List Alpha → (Fin k → ℕ) → Prop} (hR : MSO.MSODefinableRel k R) :
    IsSliceFamilySemilinear2 (fun mS n ī => R (F.eval mS n) ī)

/-! ## General regular-rank-term equality on a block-linear slice

The §9 tie counting also needs the rank-equality fact: the predicate "the rank of an
atom equals the fibred `d*`-rank" is semilinear on the copied slice.  This is the
ℤ-valued sibling of `msoDefinableRel2_semilinear_general`, hung on the general
`IsRegularRankTerm` class rather than on any specific presentation.  The only
non-`MSO` ingredient is comparing a regular rank vector against a `(mS, n)`-indexed
target `g`; we keep that comparison project-agnostic by requiring `g`'s own value graph
to be semilinear, independent of the rank term (so the axiom is genuinely general and
not circular). -/

/-- Decode a `Fin (d + d) → ℕ` vector as a `Fin d → ℤ` vector: coordinate `c` is the
first-block entry minus the second-block entry, the standard `(positive, negative)`
encoding of a signed value by a pair of naturals. -/
def decodeZ {d : ℕ} (v : Fin (d + d) → ℕ) (c : Fin d) : ℤ :=
  (v (Fin.castAdd d c) : ℤ) - (v (Fin.natAdd d c) : ℤ)

/-- `decodeZ` is surjective: every `z : Fin d → ℤ` is `decodeZ` of its
`(positive, negative)` split appended into one `ℕ` pair vector. -/
theorem decodeZ_surjective {d : ℕ} (z : Fin d → ℤ) :
    ∃ v : Fin (d + d) → ℕ, decodeZ v = z := by
  refine ⟨Fin.append (fun c => (z c).toNat) (fun c => (- z c).toNat), ?_⟩
  funext c
  simp only [decodeZ, Fin.append_left, Fin.append_right]
  omega

/-- At coordinate `i`, the `selA`-block `decodeZ` value is `<` the `selB`-block value:
semilinear (the `coord_diff_lt` kernel at the four selected `(pos, neg)` coordinates).
`selA`/`selB` place the two `(d+d)`-sized value blocks anywhere in the `Fin K` tuple. -/
theorem decodeZ_sel_lt_at {d K : ℕ} (selA selB : Fin (d + d) → Fin K) (i : Fin d) :
    IsSliceFamilySemilinear2 (fun _mS _n (ī : Fin K → ℕ) =>
      decodeZ (fun c => ī (selA c)) i < decodeZ (fun c => ī (selB c)) i) := by
  refine isSemilinearNd_congr ?_ (coord_diff_lt_semilinear K
    (selA (Fin.castAdd d i)) (selA (Fin.natAdd d i))
    (selB (Fin.castAdd d i)) (selB (Fin.natAdd d i)))
  ext ī
  simp only [familyGraph2, Set.mem_ofPred_eq, decodeZ]

/-- At coordinate `i`, the two selected `decodeZ` blocks are equal: semilinear. -/
theorem decodeZ_sel_eq_at {d K : ℕ} (selA selB : Fin (d + d) → Fin K) (i : Fin d) :
    IsSliceFamilySemilinear2 (fun _mS _n (ī : Fin K → ℕ) =>
      decodeZ (fun c => ī (selA c)) i = decodeZ (fun c => ī (selB c)) i) := by
  refine isSemilinearNd_congr ?_ (coord_diff_eq_semilinear K
    (selA (Fin.castAdd d i)) (selA (Fin.natAdd d i))
    (selB (Fin.castAdd d i)) (selB (Fin.natAdd d i)))
  ext ī
  simp only [familyGraph2, Set.mem_ofPred_eq, decodeZ]

/-- **`lexLt` of two selected `decodeZ` blocks is semilinear.**  The lexicographic
comparison `∃ i, (∀ j < i, eq) ∧ (<)` assembled from the per-coordinate comparisons via
the finite `∃`/`∀` closures.  The blocks are selected by `selA`/`selB` from anywhere. -/
theorem lexLt_decodeZ_sel {d K : ℕ} (selA selB : Fin (d + d) → Fin K) :
    IsSliceFamilySemilinear2 (fun _mS _n (ī : Fin K → ℕ) =>
      WRP.lexLt (decodeZ (fun c => ī (selA c))) (decodeZ (fun c => ī (selB c)))) := by
  refine isSemilinearNd_congr ?_
    (IsSliceFamilySemilinear2.exists_fintype (ι := Fin d) (fun i =>
      (IsSliceFamilySemilinear2.forall_fintype (ι := {j : Fin d // j < i})
        (fun j' => decodeZ_sel_eq_at selA selB j'.val)).and (decodeZ_sel_lt_at selA selB i)))
  ext ī
  simp only [familyGraph2, Set.mem_ofPred_eq, WRP.lexLt, Subtype.forall]

/-- A two-parameter ℤ^d-valued constant family `g : ℕ → ℕ → (Fin d → ℤ)` (no atom
dependence) is *slice-const-semilinear* when its value graph is semilinear: the set of
`(mS, n, v)` with `v ∈ Fin (d + d) → ℕ` encoding `g mS n` (via `decodeZ`) is
`IsSliceFamilySemilinear2`.  This is a statement about `g` alone — it does not mention
any rank term — which kept the rank-equality development non-circular: it is the target
hypothesis of the corollary `regularRankTerm_eq_value2_semilinear` and the conclusion
shape of the now-theorem `dstarRankGA_m_const_semilinear`.  It holds whenever `g` is a
Presburger function of `(mS, n)`. -/
def IsSliceConstSemilinear2 {d : ℕ} (g : ℕ → ℕ → (Fin d → ℤ)) : Prop :=
  IsSliceFamilySemilinear2 (fun mS n (v : Fin (d + d) → ℕ) => g mS n = decodeZ v)

/-- **A regular rank term has a semilinear VALUE GRAPH on a block-linear slice.**
Admitted as a standard fact (the rank-counting analogue of
`msoDefinableRel2_semilinear_general`): a `IsRegularRankTerm` `f` read along a
block-linear two-parameter word family `F` has a semilinear value graph — the set of
`(mS, n, ī, v)` with the rank value `f (F.eval mS n) ī` decoded by `v : Fin (d+d) → ℕ`
(the `ī` coordinates first, the `v` value coordinates last).  A faithful two-loop / ℤ^d
lift of the already-native one-loop `SliceFamilyRank` rank-affine chain (Ginsburg–Spanier
on the regular two-loop slice language).  Project-agnostic: it mentions only
`IsRegularRankTerm`, `BlockLinearWord2`, `decodeZ`, and `IsSliceFamilySemilinear2`,
no specific presentation or slice.  Both hypotheses are load-bearing: `[Fintype Alpha]`
(automaton step) and the block-linear shape of `F` (regularity of the slice).  This is
strictly stronger than the bundled `= g` form (`regularRankTerm_eq_value2_semilinear`
below), which it derives: exposing the value as free coordinates lets a *second* atom's
rank be a free variable, after which `lexLt`/`=` of two ranks are first-order. -/
axiom regularRankTerm_value2_graph_semilinear {Alpha : Type*} [Fintype Alpha] {d k : ℕ}
    (F : BlockLinearWord2 Alpha)
    {f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)} (hf : IsRegularRankTerm f) :
    IsSliceFamilySemilinear2
      (fun mS n (iv : Fin (k + (d + d)) → ℕ) =>
        f (F.eval mS n) (fun t => iv (Fin.castAdd (d + d) t))
          = decodeZ (fun c => iv (Fin.natAdd k c)))

/-- **A regular rank term equals a slice-semilinear target: semilinear.**  A theorem —
the bundled `= g` corollary of the value-graph axiom: intersect `f`'s value graph with
`g`'s value graph (sharing the value block) and existentially project the value, using
`decodeZ_surjective` to pick the common split. -/
theorem regularRankTerm_eq_value2_semilinear {Alpha : Type*} [Fintype Alpha] {d k : ℕ}
    (F : BlockLinearWord2 Alpha)
    {f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)} (hf : IsRegularRankTerm f)
    {g : ℕ → ℕ → (Fin d → ℤ)} (hg : IsSliceConstSemilinear2 g) :
    IsSliceFamilySemilinear2 (fun mS n ī => f (F.eval mS n) ī = g mS n) := by
  have hf2 := regularRankTerm_value2_graph_semilinear F hf
  have hgw : IsSliceFamilySemilinear2
      (fun mS n (iv : Fin (k + (d + d)) → ℕ) =>
        g mS n = decodeZ (fun c => iv (Fin.natAdd k c))) :=
    IsSliceFamilySemilinear2.weaken_natAdd (j := k) hg
  have hex := IsSliceFamilySemilinear2.exists_extra_tuple (k := k) (m := d + d) (hf2.and hgw)
  refine isSemilinearNd_congr ?_ hex
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨bb, hA, hB⟩
    rw [hA, hB]
  · intro hAB
    obtain ⟨bb, hbb⟩ := decodeZ_surjective (g (w 0) (w 1))
    exact ⟨bb, by rw [hAB, hbb], hbb.symm⟩

end SliceSemilinearN
