/-
# Integer-valued graph arithmetic for two-parameter slice families

`SliceSemilinearN.decodeZ` encodes a signed vector `Fin d → ℤ` by a pair of `ℕ`-blocks
(`positive, negative`).  A two-parameter `ℤ^d`-valued slice function
`f : ℕ → ℕ → (Fin k → ℕ) → (Fin d → ℤ)` has a **semilinear value graph**
(`IsSliceValueSemilinear2`) when the packed relation

    f mS n ī = decodeZ v      over  (mS, n, ī, v) ∈ ℕ × ℕ × ℕ^k × ℕ^(d+d)

is `IsSliceFamilySemilinear2`.  This is exactly the conclusion shape of the rank-term
value-graph statement of `SliceSemilinear2`.

The file supplies the closure operations at that interface:

* `IsSliceFamilySemilinear2.comap` — reindexing of the atom coordinates along an
  **arbitrary** (not necessarily injective) map, the workhorse for placing several value
  blocks inside one tuple;
* `natAffineEq_semilinear2`, `intAffineEq_semilinear2`, `intSelEq_semilinear2` — one
  `ℕ`- resp. `ℤ`-linear equation in (selected) coordinates cuts out a semilinear family;
* `decodeZ_add_rel_semilinear2`, `decodeZ_smul_rel_semilinear2`,
  `decodeZ_natCoeff_rel_semilinear2` — the `decodeZ`-level relations `z = x + y`,
  `z = λ·x`, `z = λ·N` between selected value blocks;
* `isSliceValueSemilinear2_const`, `IsSliceValueSemilinear2.add`,
  `IsSliceValueSemilinear2.smul`, `.neg`, `.sub`, `.listSum`, `.finsetSum` — constants,
  pointwise sums, integer multiples and finite sums of value graphs;
* `isSliceValueSemilinear2_of_coords` — a value graph is semilinear as soon as each of its `d`
  coordinate equations is;
* `isSliceValueSemilinear2_natCoeff`, `isSliceValueSemilinear2_natCoeffSum` — the bridge
  from `ℕ`-valued counts with semilinear count graphs (`IsSliceCountSemilinear2`) to the
  `ℤ^d`-valued functions `c ↦ λ c · count` and `c ↦ ∑ i, λ i c · countᵢ`;
* `isSliceValueSemilinear2_of_cases` — a finite semilinear case split;
* `isSliceValueSemilinear2_blockLinear_iff` — the identification of
  `IsSliceValueSemilinear2` with the value-graph statement of `SliceSemilinear2`.

Every value-block construction goes through the same idiom: existentially quantify the
`decodeZ` blocks of the arguments with `IsSliceFamilySemilinear2.exists_extra_tuple`,
pin them with the (reindexed) hypotheses, and tie them to the output block by one linear
equation per coordinate.  `decodeZ_surjective` supplies the witness blocks in the
converse direction.

No `sorry`, no new axiom.
-/
import RequestProject.SliceSemilinear2
import RequestProject.SemilinearGraphArith

namespace SliceSemilinearN

open scoped BigOperators

/-! ## Arbitrary reindexing of the atom coordinates

`IsSliceFamilySemilinear2.comap_sel` needs an injective selection because it is proved
through `isSemilinearNd_comap_injective`.  Mathlib's Presburger bridge gives the same
closure for an arbitrary reindexing (`SemilinearGraphArith.isSemilinearSet_comap`), which
is what repeated value blocks inside one tuple need. -/

/-- The atom-coordinate index `c - 2` (for `c ≥ 2`) packaged as a `Fin k`. -/
private def liftIdx {k : ℕ} (c : Fin (k + 2)) (h : ¬ (c : ℕ) < 2) : Fin k :=
  ⟨(c : ℕ) - 2, by have := c.isLt; omega⟩

/-- Lift a coordinate selection `sel : Fin k → Fin K` to the two-parameter packing:
the parameter coordinates `0, 1` are fixed and atom coordinate `t + 2` goes to
`sel t + 2`. -/
def selLift {k K : ℕ} (sel : Fin k → Fin K) : Fin (k + 2) → Fin (K + 2) :=
  fun c => if h : (c : ℕ) < 2 then ⟨c, by omega⟩
    else ⟨(sel (liftIdx c h) : Fin K) + 2, by have := (sel (liftIdx c h)).isLt; omega⟩

@[simp] theorem selLift_zero {k K : ℕ} (sel : Fin k → Fin K) : selLift sel 0 = 0 := by
  apply Fin.ext; simp [selLift]

@[simp] theorem selLift_one {k K : ℕ} (sel : Fin k → Fin K) : selLift sel 1 = 1 := by
  apply Fin.ext
  unfold selLift
  have h1 : ((1 : Fin (k + 2)) : ℕ) = 1 := by simp
  rw [dif_pos (by rw [h1]; omega)]
  simp

@[simp] theorem selLift_succ_succ {k K : ℕ} (sel : Fin k → Fin K) (i : Fin k) :
    selLift sel i.succ.succ = (sel i).succ.succ := by
  apply Fin.ext
  unfold selLift
  rw [dif_neg (show ¬ ((i.succ.succ : Fin (k + 2)) : ℕ) < 2 by simp [Fin.val_succ])]
  have harg : liftIdx (i.succ.succ) (by simp [Fin.val_succ]) = i := by
    apply Fin.ext; simp [liftIdx, Fin.val_succ]
  have hsv : (sel (liftIdx (i.succ.succ) (by simp [Fin.val_succ]))).val = (sel i).val :=
    Fin.val_eq_of_eq (congrArg sel harg)
  show (sel (liftIdx (i.succ.succ) (by simp [Fin.val_succ]))).val + 2 = (sel i).succ.succ.val
  rw [hsv]; simp [Fin.val_succ]

/-- **Reindexing of the atom coordinates along an arbitrary map.**  Reading a semilinear
two-parameter family through any `sel : Fin k → Fin K` (the parameters untouched) is again
semilinear; unlike `comap_sel`, `sel` need not be injective, so the same coordinate may be
read twice. -/
theorem IsSliceFamilySemilinear2.comap {k K : ℕ} (sel : Fin k → Fin K)
    {Φ : ℕ → ℕ → (Fin k → ℕ) → Prop} (hΦ : IsSliceFamilySemilinear2 Φ) :
    IsSliceFamilySemilinear2 (fun mS n (ī : Fin K → ℕ) => Φ mS n (fun t => ī (sel t))) := by
  have h := SemilinearGraphArith.isSemilinearSet_comap (selLift sel)
    (isSemilinearNd_to_mathlib (k + 2) _ hΦ)
  refine isSemilinearNd_congr ?_ (mathlib_to_isSemilinearNd (K + 2) _ h)
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq, selLift_zero, selLift_one, selLift_succ_succ]

/-! ## Linear equations as slice families -/

/-- One inhomogeneous `ℕ`-linear equation in the atom coordinates cuts out a semilinear
two-parameter family. -/
theorem natAffineEq_semilinear2 {k : ℕ} (a b : ℕ) (α β : Fin k → ℕ) :
    IsSliceFamilySemilinear2 (fun _mS _n (ī : Fin k → ℕ) =>
      a + ∑ t, α t * ī t = b + ∑ t, β t * ī t) := by
  have hS : IsSemilinearSet {x : Fin k → ℕ | a + ∑ t, α t * x t = b + ∑ t, β t * x t} :=
    SemilinearGraphArith.isSemilinearSet_affine_eq a b α β
  have h := SemilinearGraphArith.isSemilinearSet_comap
    (fun t : Fin k => (t.succ.succ : Fin (k + 2))) hS
  refine isSemilinearNd_congr ?_ (mathlib_to_isSemilinearNd (k + 2) _ h)
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq]

/-- One inhomogeneous `ℤ`-linear equation in the atom coordinates cuts out a semilinear
two-parameter family: split each integer coefficient into `(positive, negative)` parts and
read the equation as an `ℕ`-equation between the two sides. -/
theorem intAffineEq_semilinear2 {k : ℕ} (a : ℤ) (α : Fin k → ℤ) :
    IsSliceFamilySemilinear2 (fun _mS _n (ī : Fin k → ℕ) =>
      a + ∑ t, α t * (ī t : ℤ) = 0) := by
  have key : ∀ x : Fin k → ℕ,
      ((a.toNat : ℤ) + ∑ t, ((α t).toNat : ℤ) * (x t : ℤ))
        - (((-a).toNat : ℤ) + ∑ t, ((-(α t)).toNat : ℤ) * (x t : ℤ))
        = a + ∑ t, α t * (x t : ℤ) := by
    intro x
    have hsum : (∑ t, ((α t).toNat : ℤ) * (x t : ℤ))
        - (∑ t, ((-(α t)).toNat : ℤ) * (x t : ℤ)) = ∑ t, α t * (x t : ℤ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have h1 : ((α t).toNat : ℤ) - ((-(α t)).toNat : ℤ) = α t := by omega
      calc ((α t).toNat : ℤ) * (x t : ℤ) - ((-(α t)).toNat : ℤ) * (x t : ℤ)
          = (((α t).toNat : ℤ) - ((-(α t)).toNat : ℤ)) * (x t : ℤ) := by ring
        _ = α t * (x t : ℤ) := by rw [h1]
    have ha : (a.toNat : ℤ) - ((-a).toNat : ℤ) = a := by omega
    linarith
  refine isSemilinearNd_congr ?_ (natAffineEq_semilinear2 a.toNat (-a).toNat
    (fun t => (α t).toNat) (fun t => (-(α t)).toNat))
  ext v
  simp only [familyGraph2, Set.mem_ofPred_eq]
  have hk := key (fun i => v i.succ.succ)
  constructor
  · intro h
    have hZ : ((a.toNat + ∑ t, (α t).toNat * v t.succ.succ : ℕ) : ℤ)
        = (((-a).toNat + ∑ t, (-(α t)).toNat * v t.succ.succ : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at hZ
    linarith
  · intro h
    have hZ : ((a.toNat + ∑ t, (α t).toNat * v t.succ.succ : ℕ) : ℤ)
        = (((-a).toNat + ∑ t, (-(α t)).toNat * v t.succ.succ : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast hZ

/-- One inhomogeneous `ℤ`-linear equation in **selected** coordinates (repetitions
allowed) cuts out a semilinear two-parameter family. -/
theorem intSelEq_semilinear2 {m K : ℕ} (a : ℤ) (α : Fin m → ℤ) (sel : Fin m → Fin K) :
    IsSliceFamilySemilinear2 (fun _mS _n (ī : Fin K → ℕ) =>
      a + ∑ t, α t * (ī (sel t) : ℤ) = 0) :=
  IsSliceFamilySemilinear2.comap sel (intAffineEq_semilinear2 a α)

/-! ## `decodeZ` basics -/

/-- `![a, b, c, d, e, f] 5 = f`: the Mathlib `Matrix.cons_val_*` chain stops at index
four, and the six-entry equations below need one more step. -/
private theorem cons_val_five {α : Type*} {m : ℕ} (x : α)
    (u : Fin m.succ.succ.succ.succ.succ → α) :
    Matrix.vecCons x u 5
      = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))) :=
  rfl

/-- The `decodeZ` **addition relation** between three selected value blocks is semilinear:
one linear equation per coordinate, on the six selected `(positive, negative)` entries. -/
theorem decodeZ_add_rel_semilinear2 {K d : ℕ} (sz sx sy : Fin (d + d) → Fin K) :
    IsSliceFamilySemilinear2 (fun _mS _n (ī : Fin K → ℕ) =>
      ∀ c : Fin d, decodeZ (fun j => ī (sz j)) c
        = decodeZ (fun j => ī (sx j)) c + decodeZ (fun j => ī (sy j)) c) := by
  refine IsSliceFamilySemilinear2.forall_fintype (fun c => ?_)
  refine isSemilinearNd_congr ?_ (intSelEq_semilinear2 (K := K) 0
    ![1, -1, -1, 1, -1, 1]
    ![sz (Fin.castAdd d c), sz (Fin.natAdd d c), sx (Fin.castAdd d c), sx (Fin.natAdd d c),
      sy (Fin.castAdd d c), sy (Fin.natAdd d c)])
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, decodeZ, Fin.sum_univ_six, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_val_five]
  constructor <;> intro h <;> linarith

/-- The `decodeZ` **integer-multiple relation** `z = λ·x` between two selected value
blocks is semilinear. -/
theorem decodeZ_smul_rel_semilinear2 {K d : ℕ} (lam : ℤ) (sz sx : Fin (d + d) → Fin K) :
    IsSliceFamilySemilinear2 (fun _mS _n (ī : Fin K → ℕ) =>
      ∀ c : Fin d, decodeZ (fun j => ī (sz j)) c = lam * decodeZ (fun j => ī (sx j)) c) := by
  refine IsSliceFamilySemilinear2.forall_fintype (fun c => ?_)
  refine isSemilinearNd_congr ?_ (intSelEq_semilinear2 (K := K) 0
    ![1, -1, -lam, lam]
    ![sz (Fin.castAdd d c), sz (Fin.natAdd d c), sx (Fin.castAdd d c), sx (Fin.natAdd d c)])
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, decodeZ, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three]
  constructor <;> intro h <;> linarith

/-- The `decodeZ` **scaled-count relation** `z c = λ c · N` between a selected value block
and a single selected `ℕ` coordinate is semilinear. -/
theorem decodeZ_natCoeff_rel_semilinear2 {K d : ℕ} (lam : Fin d → ℤ)
    (sz : Fin (d + d) → Fin K) (p : Fin K) :
    IsSliceFamilySemilinear2 (fun _mS _n (ī : Fin K → ℕ) =>
      ∀ c : Fin d, decodeZ (fun j => ī (sz j)) c = lam c * (ī p : ℤ)) := by
  refine IsSliceFamilySemilinear2.forall_fintype (fun c => ?_)
  refine isSemilinearNd_congr ?_ (intSelEq_semilinear2 (K := K) 0
    ![1, -1, -(lam c)] ![sz (Fin.castAdd d c), sz (Fin.natAdd d c), p])
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, decodeZ, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  constructor <;> intro h <;> linarith

/-! ## The value graph of a `ℤ^d`-valued slice function -/

/-- A two-parameter `ℤ^d`-valued slice function has a **semilinear value graph** when the
packed relation `f mS n ī = decodeZ v` — the `k` atom coordinates first, the `d + d`
`decodeZ` value coordinates last — is `IsSliceFamilySemilinear2`. -/
def IsSliceValueSemilinear2 {k d : ℕ} (f : ℕ → ℕ → (Fin k → ℕ) → (Fin d → ℤ)) : Prop :=
  IsSliceFamilySemilinear2 (fun mS n (iv : Fin (k + (d + d)) → ℕ) =>
    f mS n (fun t => iv (Fin.castAdd (d + d) t)) = decodeZ (fun c => iv (Fin.natAdd k c)))

/-- A two-parameter `ℕ`-valued slice function has a **semilinear count graph** when the
packed relation `g mS n ī = N` — the `k` atom coordinates first, the value coordinate
last — is `IsSliceFamilySemilinear2`. -/
def IsSliceCountSemilinear2 {k : ℕ} (g : ℕ → ℕ → (Fin k → ℕ) → ℕ) : Prop :=
  IsSliceFamilySemilinear2 (fun mS n (iu : Fin (k + 1) → ℕ) =>
    g mS n (fun t => iu (Fin.castAdd 1 t)) = iu (Fin.natAdd k 0))

/-- Value graphs only depend on the function. -/
theorem IsSliceValueSemilinear2.congr {k d : ℕ}
    {f g : ℕ → ℕ → (Fin k → ℕ) → (Fin d → ℤ)} (h : ∀ mS n ī, f mS n ī = g mS n ī)
    (hf : IsSliceValueSemilinear2 f) : IsSliceValueSemilinear2 g := by
  have hfg : f = g := funext fun mS => funext fun n => funext fun ī => h mS n ī
  exact hfg ▸ hf

/-- **Coordinatewise criterion**: a value graph is semilinear once each coordinate's
equation is, the `d` equations reading the same value block. -/
theorem isSliceValueSemilinear2_of_coords {k d : ℕ}
    (f : ℕ → ℕ → (Fin k → ℕ) → (Fin d → ℤ))
    (h : ∀ c : Fin d, IsSliceFamilySemilinear2 (fun mS n (iv : Fin (k + (d + d)) → ℕ) =>
      f mS n (fun t => iv (Fin.castAdd (d + d) t)) c
        = decodeZ (fun j => iv (Fin.natAdd k j)) c)) :
    IsSliceValueSemilinear2 f := by
  refine isSemilinearNd_congr ?_ (IsSliceFamilySemilinear2.forall_fintype h)
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  exact ⟨fun hc => funext hc, fun he c => congrFun he c⟩

/-- **Constants.**  A constant `ℤ^d`-valued slice function has a semilinear value graph. -/
theorem isSliceValueSemilinear2_const {k d : ℕ} (z : Fin d → ℤ) :
    IsSliceValueSemilinear2 (fun (_ _ : ℕ) (_ : Fin k → ℕ) => z) := by
  refine isSliceValueSemilinear2_of_coords _ (fun c => ?_)
  refine isSemilinearNd_congr ?_ (intSelEq_semilinear2 (K := k + (d + d)) (-(z c))
    ![1, -1] ![Fin.natAdd k (Fin.castAdd d c), Fin.natAdd k (Fin.natAdd d c)])
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, decodeZ, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  constructor <;> intro h <;> linarith

/-- **Sums.**  The pointwise sum of two `ℤ^d`-valued slice functions with semilinear value
graphs has a semilinear value graph: quantify the two summand blocks, pin them with the
two hypotheses, and tie them to the output block by the `decodeZ` addition relation. -/
theorem IsSliceValueSemilinear2.add {k d : ℕ}
    {f g : ℕ → ℕ → (Fin k → ℕ) → (Fin d → ℤ)}
    (hf : IsSliceValueSemilinear2 f) (hg : IsSliceValueSemilinear2 g) :
    IsSliceValueSemilinear2 (fun mS n ī => f mS n ī + g mS n ī) := by
  have hA : IsSliceFamilySemilinear2
      (fun mS n (u : Fin ((k + (d + d)) + ((d + d) + (d + d))) → ℕ) =>
        f mS n (fun t => u (Fin.castAdd ((d + d) + (d + d)) (Fin.castAdd (d + d) t)))
          = decodeZ (fun c => u (Fin.natAdd (k + (d + d)) (Fin.castAdd (d + d) c)))) := by
    refine isSemilinearNd_congr ?_ (IsSliceFamilySemilinear2.comap
      (Fin.append (fun t : Fin k => Fin.castAdd ((d + d) + (d + d)) (Fin.castAdd (d + d) t))
        (fun c : Fin (d + d) => Fin.natAdd (k + (d + d)) (Fin.castAdd (d + d) c))) hf)
    ext w
    simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]
  have hB : IsSliceFamilySemilinear2
      (fun mS n (u : Fin ((k + (d + d)) + ((d + d) + (d + d))) → ℕ) =>
        g mS n (fun t => u (Fin.castAdd ((d + d) + (d + d)) (Fin.castAdd (d + d) t)))
          = decodeZ (fun c => u (Fin.natAdd (k + (d + d)) (Fin.natAdd (d + d) c)))) := by
    refine isSemilinearNd_congr ?_ (IsSliceFamilySemilinear2.comap
      (Fin.append (fun t : Fin k => Fin.castAdd ((d + d) + (d + d)) (Fin.castAdd (d + d) t))
        (fun c : Fin (d + d) => Fin.natAdd (k + (d + d)) (Fin.natAdd (d + d) c))) hg)
    ext w
    simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]
  have hC := decodeZ_add_rel_semilinear2 (d := d)
    (fun j => Fin.castAdd ((d + d) + (d + d)) (Fin.natAdd k j))
    (fun j => Fin.natAdd (k + (d + d)) (Fin.castAdd (d + d) j))
    (fun j => Fin.natAdd (k + (d + d)) (Fin.natAdd (d + d) j))
  have hex := IsSliceFamilySemilinear2.exists_extra_tuple (k := k + (d + d))
    (m := (d + d) + (d + d)) ((hA.and hB).and hC)
  refine isSemilinearNd_congr ?_ hex
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨bb, ⟨hfa, hgb⟩, hc⟩
    funext c
    have := hc c
    simp only [Pi.add_apply]
    rw [hfa, hgb, ← this]
  · intro h
    obtain ⟨b1, hb1⟩ := decodeZ_surjective (f (w 0) (w 1) (fun t => w (Fin.castAdd (d + d) t).succ.succ))
    obtain ⟨b2, hb2⟩ := decodeZ_surjective (g (w 0) (w 1) (fun t => w (Fin.castAdd (d + d) t).succ.succ))
    refine ⟨Fin.append b1 b2, ⟨?_, ?_⟩, ?_⟩
    · have he : (fun c => Fin.append b1 b2 (Fin.castAdd (d + d) c)) = b1 := by
        funext c; rw [Fin.append_left]
      rw [he, hb1]
    · have he : (fun c => Fin.append b1 b2 (Fin.natAdd (d + d) c)) = b2 := by
        funext c; rw [Fin.append_right]
      rw [he, hb2]
    · intro c
      have he1 : (fun j => Fin.append b1 b2 (Fin.castAdd (d + d) j)) = b1 := by
        funext j; rw [Fin.append_left]
      have he2 : (fun j => Fin.append b1 b2 (Fin.natAdd (d + d) j)) = b2 := by
        funext j; rw [Fin.append_right]
      rw [he1, he2, hb1, hb2, ← h]
      simp

/-- **Integer multiples.**  A fixed integer multiple of a `ℤ^d`-valued slice function with
a semilinear value graph has a semilinear value graph. -/
theorem IsSliceValueSemilinear2.smul {k d : ℕ} (lam : ℤ)
    {f : ℕ → ℕ → (Fin k → ℕ) → (Fin d → ℤ)} (hf : IsSliceValueSemilinear2 f) :
    IsSliceValueSemilinear2 (fun mS n ī => fun c => lam * f mS n ī c) := by
  have hA : IsSliceFamilySemilinear2
      (fun mS n (u : Fin ((k + (d + d)) + (d + d)) → ℕ) =>
        f mS n (fun t => u (Fin.castAdd (d + d) (Fin.castAdd (d + d) t)))
          = decodeZ (fun c => u (Fin.natAdd (k + (d + d)) c))) := by
    refine isSemilinearNd_congr ?_ (IsSliceFamilySemilinear2.comap
      (Fin.append (fun t : Fin k => Fin.castAdd (d + d) (Fin.castAdd (d + d) t))
        (fun c : Fin (d + d) => Fin.natAdd (k + (d + d)) c)) hf)
    ext w
    simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]
  have hC := decodeZ_smul_rel_semilinear2 (d := d) lam
    (fun j => Fin.castAdd (d + d) (Fin.natAdd k j))
    (fun j => Fin.natAdd (k + (d + d)) j)
  have hex := IsSliceFamilySemilinear2.exists_extra_tuple (k := k + (d + d))
    (m := d + d) (hA.and hC)
  refine isSemilinearNd_congr ?_ hex
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨bb, hfa, hc⟩
    funext c
    rw [hfa, ← hc c]
  · intro h
    obtain ⟨b1, hb1⟩ := decodeZ_surjective (f (w 0) (w 1) (fun t => w (Fin.castAdd (d + d) t).succ.succ))
    refine ⟨b1, hb1.symm, fun c => ?_⟩
    rw [hb1, ← congrFun h c]

/-- **Negation.** -/
theorem IsSliceValueSemilinear2.neg {k d : ℕ}
    {f : ℕ → ℕ → (Fin k → ℕ) → (Fin d → ℤ)} (hf : IsSliceValueSemilinear2 f) :
    IsSliceValueSemilinear2 (fun mS n ī => -(f mS n ī)) :=
  IsSliceValueSemilinear2.congr (fun mS n ī => by funext c; simp)
    (IsSliceValueSemilinear2.smul (-1) hf)

/-- **The zero function.** -/
theorem isSliceValueSemilinear2_zero {k d : ℕ} :
    IsSliceValueSemilinear2 (fun (_ _ : ℕ) (_ : Fin k → ℕ) => (0 : Fin d → ℤ)) :=
  isSliceValueSemilinear2_const 0

/-- **Finset sums.**  A finite `Finset`-indexed pointwise sum of value graphs is a value
graph. -/
theorem IsSliceValueSemilinear2.finsetSum {k d : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → ℕ → ℕ → (Fin k → ℕ) → (Fin d → ℤ))
    (hF : ∀ i ∈ s, IsSliceValueSemilinear2 (F i)) :
    IsSliceValueSemilinear2 (fun mS n ī => ∑ i ∈ s, F i mS n ī) := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine IsSliceValueSemilinear2.congr (fun mS n ī => ?_) isSliceValueSemilinear2_zero
      simp
  | insert a s ha ih =>
      have hFa : IsSliceValueSemilinear2 (F a) := hF a (Finset.mem_insert_self a s)
      have hrest := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      refine IsSliceValueSemilinear2.congr (fun mS n ī => ?_) (hFa.add hrest)
      rw [Finset.sum_insert ha]

/-- **From an `ℕ`-valued count.**  If `g` has a semilinear count graph then the
`ℤ^d`-valued function `c ↦ λ c · g` has a semilinear value graph.  This is the bridge the
prefix-rank step needs: the count enters as one existentially quantified `ℕ` coordinate,
pinned by the count graph and tied to the value block by one equation per coordinate. -/
theorem isSliceValueSemilinear2_natCoeff {k d : ℕ} (lam : Fin d → ℤ)
    {g : ℕ → ℕ → (Fin k → ℕ) → ℕ} (hg : IsSliceCountSemilinear2 g) :
    IsSliceValueSemilinear2 (fun mS n ī => fun c => lam c * (g mS n ī : ℤ)) := by
  have hA : IsSliceFamilySemilinear2
      (fun mS n (u : Fin ((k + (d + d)) + 1) → ℕ) =>
        g mS n (fun t => u (Fin.castAdd 1 (Fin.castAdd (d + d) t)))
          = u (Fin.natAdd (k + (d + d)) 0)) := by
    refine isSemilinearNd_congr ?_ (IsSliceFamilySemilinear2.comap
      (Fin.append (fun t : Fin k => Fin.castAdd 1 (Fin.castAdd (d + d) t))
        (fun c : Fin 1 => Fin.natAdd (k + (d + d)) c)) hg)
    ext w
    simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]
  have hC := decodeZ_natCoeff_rel_semilinear2 (d := d) lam
    (fun j => Fin.castAdd 1 (Fin.natAdd k j)) (Fin.natAdd (k + (d + d)) 0)
  have hex := IsSliceFamilySemilinear2.exists_extra_tuple (k := k + (d + d))
    (m := 1) (hA.and hC)
  refine isSemilinearNd_congr ?_ hex
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨bb, hga, hc⟩
    funext c
    rw [hga, ← hc c]
  · intro h
    refine ⟨fun _ => g (w 0) (w 1) (fun t => w (Fin.castAdd (d + d) t).succ.succ), rfl, fun c => ?_⟩
    rw [← congrFun h c]

/-- **A finite signed combination of counts.**  The shape a prefix rank takes: a finite
sum `c ↦ ∑ i, λ i c · gᵢ` of integer multiples of `ℕ`-valued counts with semilinear count
graphs has a semilinear value graph. -/
theorem isSliceValueSemilinear2_natCoeffSum {k d : ℕ} {ι : Type*} (s : Finset ι)
    (lam : ι → Fin d → ℤ) (g : ι → ℕ → ℕ → (Fin k → ℕ) → ℕ)
    (hg : ∀ i ∈ s, IsSliceCountSemilinear2 (g i)) :
    IsSliceValueSemilinear2 (fun mS n ī => fun c => ∑ i ∈ s, lam i c * (g i mS n ī : ℤ)) := by
  refine IsSliceValueSemilinear2.congr (fun mS n ī => ?_)
    (IsSliceValueSemilinear2.finsetSum s
      (fun i mS n ī => fun c => lam i c * (g i mS n ī : ℤ))
      (fun i hi => isSliceValueSemilinear2_natCoeff (lam i) (hg i hi)))
  funext c
  simp

/-- **Finite case split.**  If a `ℤ^d`-valued slice function agrees, on each cell of a
finite semilinear cover, with a function having a semilinear value graph, then it has a
semilinear value graph.  This is what a bounded correction table indexed by a finite set
of states and letters needs. -/
theorem isSliceValueSemilinear2_of_cases {k d : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → ℕ → ℕ → (Fin k → ℕ) → Prop)
    (F : ι → ℕ → ℕ → (Fin k → ℕ) → (Fin d → ℤ))
    (f : ℕ → ℕ → (Fin k → ℕ) → (Fin d → ℤ))
    (hP : ∀ i, IsSliceFamilySemilinear2 (P i))
    (hF : ∀ i, IsSliceValueSemilinear2 (F i))
    (hcover : ∀ mS n ī, ∃ i, P i mS n ī)
    (hagree : ∀ i mS n ī, P i mS n ī → f mS n ī = F i mS n ī) :
    IsSliceValueSemilinear2 f := by
  have hPw : ∀ i, IsSliceFamilySemilinear2
      (fun mS n (iv : Fin (k + (d + d)) → ℕ) =>
        P i mS n (fun t => iv (Fin.castAdd (d + d) t))) :=
    fun i => IsSliceFamilySemilinear2.comap (Fin.castAdd (d + d)) (hP i)
  have hcase := IsSliceFamilySemilinear2.exists_fintype (ι := ι)
    (fun i => (hPw i).and (hF i))
  refine isSemilinearNd_congr ?_ hcase
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hPi, hFi⟩
    rw [hagree i _ _ _ hPi]
    exact hFi
  · intro h
    obtain ⟨i, hPi⟩ := hcover (w 0) (w 1) (fun t => w (Fin.castAdd (d + d) t).succ.succ)
    exact ⟨i, hPi, by rw [← hagree i _ _ _ hPi]; exact h⟩

/-- **The target shape.**  For a word-indexed function read along a block-linear
two-parameter word family, the value-graph statement of `SliceSemilinear2` is exactly the
semilinear value graph of the two-parameter function `(mS, n, ī) ↦ f (F.eval mS n) ī`. -/
theorem isSliceValueSemilinear2_blockLinear_iff {Alpha : Type*} {d k : ℕ}
    (F : BlockLinearWord2 Alpha) (f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)) :
    IsSliceValueSemilinear2 (fun mS n ī => f (F.eval mS n) ī) ↔
      IsSliceFamilySemilinear2 (fun mS n (iv : Fin (k + (d + d)) → ℕ) =>
        f (F.eval mS n) (fun t => iv (Fin.castAdd (d + d) t))
          = decodeZ (fun c => iv (Fin.natAdd k c))) :=
  Iff.rfl

end SliceSemilinearN
