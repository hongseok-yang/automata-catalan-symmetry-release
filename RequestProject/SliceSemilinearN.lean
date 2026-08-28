/-
# Multidimensional semilinear toolkit (route-B step 1)

Lifts the `ℕ²` semilinear lemmas of `SliceSemilinear` to arbitrary dimension `d`
and provides the Ginsburg–Spanier closure operations on `IsSemilinearNd`:
intersection and complement (bridged to Mathlib's Presburger/Semilinear
development), projection (`isSemilinearNd_proj`), and cylindrification under an
injective coordinate selection (`isSemilinearNd_comap_injective`) — all proved,
not admitted — plus the derived `univ`/`biInter`/`forall_last` closures.

This is the toolkit the pin-free tie count (`CopiedTieCounting.lean`) is built
on.  The slice atom-family wrapper used by the live general-arity result is the
two-parameter `IsSliceFamilySemilinear2` in `SliceSemilinear2.lean`; the
set-fibre ↔ `Finset.filter` count bridges (`natCard_setOf_eq_filter_card`,
`finite_setOf_of_support`) live here.
-/
import RequestProject.SliceSemilinear
import RequestProject.SliceOrder
import RequestProject.SlicePeriodStar

namespace SliceSemilinearN

open scoped Classical
open scoped BigOperators

/-! ## Dimension-`d` generalizations of the `ℕ²` basics (all provable) -/

/-- The empty set is semilinear in any dimension. -/
theorem isSemilinearNd_empty (d : ℕ) : IsSemilinearNd d (∅ : Set (Fin d → ℕ)) := by
  refine ⟨∅, fun C hC => absurd hC (Finset.notMem_empty C), ?_⟩
  simp

/-- Rewriting helper. -/
theorem isSemilinearNd_congr {d : ℕ} {S T : Set (Fin d → ℕ)} (h : S = T)
    (hS : IsSemilinearNd d S) : IsSemilinearNd d T := h ▸ hS

/-! ## Ginsburg–Spanier closure operations

Semilinear sets are exactly the Presburger-definable sets (Ginsburg–Spanier 1966),
hence closed under all Boolean operations.  Union is proved directly
(`SliceSemilinear.isSemilinearNd_union`).  Intersection and complement carry the deep
linear-Diophantine content; rather than rebuild it, we **bridge** the repo's
`LinearSet`/`IsSemilinearNd` to Mathlib's `IsLinearSet`/`IsSemilinearSet`
(`Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear`) and invoke
`IsSemilinearSet.inter` / `IsSemilinearSet.compl`.  The two notions coincide: the
repo's `base + Σ cᵢ·sᵢ` (arbitrary `ℕ` coefficients on a finite step set) is exactly
`base +ᵥ AddSubmonoid.closure steps`. -/

section MathlibBridge
open Set Pointwise AddSubmonoid

/-- A repo `LinearSet` is a Mathlib `IsLinearSet`: `base + ℕ`-span of `steps` equals
`base +ᵥ AddSubmonoid.closure steps`. -/
theorem repo_linearSet_isLinearSet (d : ℕ) (base : Fin d → ℕ)
    (steps : Finset (Fin d → ℕ)) : IsLinearSet (LinearSet d base steps) := by
  rw [isLinearSet_iff]
  refine ⟨base, steps, ?_⟩
  ext v
  simp only [LinearSet, Set.mem_ofPred_eq, mem_vadd_set, vadd_eq_add, SetLike.mem_coe]
  constructor
  · rintro ⟨coeffs, rfl⟩
    refine ⟨∑ s ∈ steps, coeffs s • s, ?_, ?_⟩
    · exact sum_mem fun s hs => nsmul_mem (mem_closure_of_mem hs) _
    · funext i; simp [Finset.sum_apply, mul_comm]
  · rintro ⟨w, hw, rfl⟩
    rw [mem_closure_finset] at hw
    rcases hw with ⟨c, -, rfl⟩
    exact ⟨c, by funext i; simp [Finset.sum_apply, mul_comm]⟩

/-- Forward bridge: a repo-semilinear set is Mathlib-semilinear. -/
theorem isSemilinearNd_to_mathlib (d : ℕ) (S : Set (Fin d → ℕ))
    (hS : IsSemilinearNd d S) : IsSemilinearSet S := by
  classical
  obtain ⟨comps, hcomp, rfl⟩ := hS
  rw [show (⋃ C ∈ comps, C) = ⋃ C ∈ (comps : Set (Set (Fin d → ℕ))), C from rfl]
  apply IsSemilinearSet.biUnion comps.finite_toSet
  intro C hC
  obtain ⟨base, steps, rfl⟩ := hcomp C hC
  exact (repo_linearSet_isLinearSet d base steps).isSemilinearSet

/-- A Mathlib `IsLinearSet` over `Fin d → ℕ` is a repo `LinearSet`. -/
theorem mathlib_isLinearSet_to_repo (d : ℕ) (C : Set (Fin d → ℕ))
    (hC : IsLinearSet C) : ∃ base steps, C = LinearSet d base steps := by
  classical
  rw [isLinearSet_iff] at hC
  obtain ⟨a, t, rfl⟩ := hC
  refine ⟨a, t, ?_⟩
  ext v
  simp only [LinearSet, Set.mem_ofPred_eq, mem_vadd_set, vadd_eq_add, SetLike.mem_coe]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_closure_finset] at hw
    rcases hw with ⟨c, -, rfl⟩
    exact ⟨c, by funext i; simp [Finset.sum_apply, mul_comm]⟩
  · rintro ⟨coeffs, rfl⟩
    refine ⟨∑ s ∈ t, coeffs s • s, ?_, ?_⟩
    · exact sum_mem fun s hs => nsmul_mem (mem_closure_of_mem hs) _
    · funext i; simp [Finset.sum_apply, mul_comm]

/-- Reverse bridge: a Mathlib-semilinear set is repo-semilinear. -/
theorem mathlib_to_isSemilinearNd (d : ℕ) (S : Set (Fin d → ℕ))
    (hS : IsSemilinearSet S) : IsSemilinearNd d S := by
  classical
  obtain ⟨comps, hfin, hlin, rfl⟩ := hS
  refine ⟨hfin.toFinset, fun C hC => ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset] at hC
    exact mathlib_isLinearSet_to_repo d C (hlin C hC)
  · rw [Set.sUnion_eq_biUnion]
    ext v; simp [Set.Finite.mem_toFinset]

/-- **Intersection of semilinear sets is semilinear** (Ginsburg–Spanier), via the
Mathlib bridge. -/
theorem isSemilinearNd_inter {d : ℕ} {S T : Set (Fin d → ℕ)}
    (hS : IsSemilinearNd d S) (hT : IsSemilinearNd d T) : IsSemilinearNd d (S ∩ T) :=
  mathlib_to_isSemilinearNd d _
    ((isSemilinearNd_to_mathlib d S hS).inter (isSemilinearNd_to_mathlib d T hT))

/-- **Complement of a semilinear set is semilinear** (Ginsburg–Spanier), via the
Mathlib bridge. -/
theorem isSemilinearNd_compl {d : ℕ} {S : Set (Fin d → ℕ)}
    (hS : IsSemilinearNd d S) : IsSemilinearNd d Sᶜ :=
  mathlib_to_isSemilinearNd d _ (isSemilinearNd_to_mathlib d S hS).compl

end MathlibBridge

/-- Image of a single linear set under `Fin.init` (drop the last coordinate) is a
linear set: `Fin.init` is linear, so it maps `base + Σ cᵢ·sᵢ` to
`Fin.init base + Σ cᵢ·(Fin.init sᵢ)`; the step coefficients are pushed forward along
the (possibly non-injective) projection of the step set. -/
theorem linearSet_image_init {d : ℕ} (base : Fin (d + 1) → ℕ)
    (steps : Finset (Fin (d + 1) → ℕ)) :
    Fin.init '' (LinearSet (d + 1) base steps)
      = LinearSet d (Fin.init base) (steps.image Fin.init) := by
  classical
  ext v
  simp only [LinearSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, ⟨coeffs, rfl⟩, rfl⟩
    refine ⟨fun w' => ∑ s ∈ steps.filter (fun s => Fin.init s = w'), coeffs s, ?_⟩
    funext i
    simp only [Fin.init]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (t := steps.image Fin.init) (g := Fin.init)
        (fun s hs => Finset.mem_image_of_mem _ hs) (f := fun s => coeffs s * s i.castSucc)]
    apply Finset.sum_congr rfl
    intro w' _hw'
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [← hs.2]
    simp only [Fin.init]
  · rintro ⟨c', hv⟩
    set img := steps.image Fin.init with himg
    have hmem : ∀ w' ∈ img, ∃ s ∈ steps, Fin.init s = w' := fun w' h => Finset.mem_image.mp h
    let pre : (Fin d → ℕ) → (Fin (d + 1) → ℕ) :=
      fun w' => if h : w' ∈ img then (hmem w' h).choose else 0
    have hpre_mem : ∀ w' ∈ img, pre w' ∈ steps := by
      intro w' h; simp only [pre, dif_pos h]; exact (hmem w' h).choose_spec.1
    have hpre_eq : ∀ w' ∈ img, Fin.init (pre w') = w' := by
      intro w' h; simp only [pre, dif_pos h]; exact (hmem w' h).choose_spec.2
    refine ⟨fun i => base i + ∑ s ∈ steps,
        (fun s => ∑ w' ∈ img.filter (fun w' => pre w' = s), c' w') s * s i, ⟨_, rfl⟩, ?_⟩
    funext i
    simp only [Fin.init]
    rw [hv]
    congr 1
    symm
    rw [← Finset.sum_fiberwise_of_maps_to (s := img) (t := steps) (g := pre) hpre_mem
        (f := fun w' => c' w' * w' i)]
    apply Finset.sum_congr rfl
    intro s _hs
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w' hw'
    rw [Finset.mem_filter] at hw'
    have hwi : w' i = s i.castSucc := by
      have h2 := hpre_eq w' hw'.1
      rw [hw'.2] at h2
      rw [← h2]
      simp only [Fin.init]
    rw [hwi]

/-- **Projection of a semilinear set is semilinear** (Ginsburg–Spanier): erasing
the last coordinate of a semilinear subset of `ℕ^(d+1)` gives a semilinear subset
of `ℕ^d`.  Native proof — the projected set is `Fin.init '' S`, and `Fin.init`
sends each linear component to a linear set (`linearSet_image_init`). -/
theorem isSemilinearNd_proj {d : ℕ} {S : Set (Fin (d + 1) → ℕ)}
    (hS : IsSemilinearNd (d + 1) S) :
    IsSemilinearNd d {v : Fin d → ℕ | ∃ t : ℕ, (Fin.snoc v t) ∈ S} := by
  classical
  have hset : {v : Fin d → ℕ | ∃ t : ℕ, (Fin.snoc v t) ∈ S} = Fin.init '' S := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨t, h⟩; exact ⟨Fin.snoc v t, h, by simp⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨w (Fin.last d), by rw [Fin.snoc_init_self]; exact hw⟩
  rw [hset]
  obtain ⟨comps, hcomp, hSeq⟩ := hS
  subst hSeq
  refine ⟨comps.image (fun C => Fin.init '' C), ?_, ?_⟩
  · intro C' hC'
    rw [Finset.mem_image] at hC'
    obtain ⟨C, hC, rfl⟩ := hC'
    obtain ⟨base, steps, rfl⟩ := hcomp C hC
    exact ⟨Fin.init base, steps.image Fin.init, linearSet_image_init base steps⟩
  · rw [Set.image_iUnion₂, Finset.set_biUnion_finset_image]

/-! ## Cylindrification (preimage under an injective coordinate selection) -/

/-- Extend `f : Fin e → ℕ` to `Fin d → ℕ` along injective `sel`, `0` off the range. -/
private def extZ {d e : ℕ} (sel : Fin e → Fin d) (f : Fin e → ℕ) : Fin d → ℕ :=
  fun p => ∑ c ∈ Finset.univ.filter (fun c => sel c = p), f c

private theorem extZ_sel {d e : ℕ} {sel : Fin e → Fin d} (hsel : Function.Injective sel)
    (f : Fin e → ℕ) (c : Fin e) : extZ sel f (sel c) = f c := by
  classical
  unfold extZ
  have hfilt : Finset.univ.filter (fun x => sel x = sel c) = {c} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hsel h, fun h => by rw [h]⟩
  rw [hfilt, Finset.sum_singleton]

private theorem extZ_not_range {d e : ℕ} {sel : Fin e → Fin d} (f : Fin e → ℕ)
    {p : Fin d} (hp : ∀ c, sel c ≠ p) : extZ sel f p = 0 := by
  classical
  unfold extZ
  rw [Finset.filter_false_of_mem (fun c _ => hp c), Finset.sum_empty]

private theorem extZ_injective {d e : ℕ} {sel : Fin e → Fin d}
    (hsel : Function.Injective sel) : Function.Injective (extZ sel) := by
  intro f g h
  funext c
  have := congrFun h (sel c)
  rwa [extZ_sel hsel, extZ_sel hsel] at this

/-- The `p`-th unit coordinate vector in `Fin d → ℕ` (explicitly typed to pin the
`Pi.single` family). -/
private def unitVec {d : ℕ} (p : Fin d) : Fin d → ℕ := Pi.single p 1

private theorem unitVec_same {d : ℕ} (p : Fin d) : unitVec p p = 1 := by simp [unitVec]

private theorem unitVec_ne {d : ℕ} {p q : Fin d} (h : p ≠ q) : unitVec q p = 0 := by
  simp [unitVec, Pi.single_eq_of_ne h]

private theorem unitVec_inj {d : ℕ} {p q : Fin d} (h : unitVec p = unitVec q) : p = q := by
  by_contra hpq
  have hc := congrFun h p
  rw [unitVec_same, unitVec_ne hpq] at hc
  exact one_ne_zero hc

/-- **Preimage of a linear set under an injective coordinate selection is a linear
set** — the unselected coordinates become free (cylindrification). -/
theorem linearSet_comap_injective {d e : ℕ} (sel : Fin e → Fin d)
    (hsel : Function.Injective sel) (base : Fin e → ℕ) (steps : Finset (Fin e → ℕ)) :
    {v : Fin d → ℕ | (fun c => v (sel c)) ∈ LinearSet e base steps}
      = LinearSet d (extZ sel base)
          (steps.image (extZ sel) ∪
            (Finset.univ.filter (fun p => ∀ c, sel c ≠ p)).image unitVec) := by
  classical
  set E := steps.image (extZ sel) with hE
  set NR := Finset.univ.filter (fun p : Fin d => ∀ c, sel c ≠ p) with hNR
  set U := NR.image unitVec with hU
  have hdisj : Disjoint E U := by
    rw [Finset.disjoint_left]
    intro x hxE hxU
    rw [hE, Finset.mem_image] at hxE
    rw [hU, Finset.mem_image] at hxU
    obtain ⟨s, _hs, rfl⟩ := hxE
    obtain ⟨p, hp, hpx⟩ := hxU
    rw [hNR, Finset.mem_filter] at hp
    have h1 : extZ sel s p = 1 := by rw [← hpx]; exact unitVec_same p
    rw [extZ_not_range s hp.2] at h1
    exact absurd h1 (by norm_num)
  have hEinj : Set.InjOn (extZ sel) (↑steps : Set (Fin e → ℕ)) :=
    fun a _ b _ hab => extZ_injective hsel hab
  have hUinj : Set.InjOn unitVec (↑NR : Set (Fin d)) :=
    fun a _ b _ hab => unitVec_inj hab
  ext v
  simp only [Set.mem_ofPred_eq, LinearSet]
  constructor
  · rintro ⟨coeffs, hc⟩
    set cf : (Fin d → ℕ) → ℕ := fun s' =>
      (∑ s ∈ steps.filter (fun s => extZ sel s = s'), coeffs s)
        + (∑ p ∈ NR.filter (fun p => unitVec p = s'), v p) with hcf
    have cE : ∀ s ∈ steps, cf (extZ sel s) = coeffs s := by
      intro s hs
      have h1 : steps.filter (fun s2 => extZ sel s2 = extZ sel s) = {s} := by
        ext s2
        simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun h => extZ_injective hsel h.2, fun h => ⟨h ▸ hs, by rw [h]⟩⟩
      have h2 : NR.filter (fun p => unitVec p = extZ sel s) = ∅ := by
        apply Finset.filter_false_of_mem
        intro p hp hpx
        rw [hNR, Finset.mem_filter] at hp
        have hps : extZ sel s p = 1 := by rw [← hpx]; exact unitVec_same p
        rw [extZ_not_range s hp.2] at hps
        exact absurd hps (by norm_num)
      rw [hcf]; simp only [h1, h2, Finset.sum_singleton, Finset.sum_empty, add_zero]
    have cU : ∀ p ∈ NR, cf (unitVec p) = v p := by
      intro p hp
      have h1 : steps.filter (fun s => extZ sel s = unitVec p) = ∅ := by
        apply Finset.filter_false_of_mem
        intro s _hs hsx
        rw [hNR, Finset.mem_filter] at hp
        have hps : extZ sel s p = 1 := by rw [hsx]; exact unitVec_same p
        rw [extZ_not_range s hp.2] at hps
        exact absurd hps (by norm_num)
      have h2 : NR.filter (fun q => unitVec q = unitVec p) = {p} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun h => unitVec_inj h.2, fun h => ⟨h ▸ hp, by rw [h]⟩⟩
      rw [hcf]; simp only [h1, h2, Finset.sum_empty, Finset.sum_singleton, zero_add]
    refine ⟨cf, ?_⟩
    funext i
    rw [Finset.sum_union hdisj, hE, hU]
    simp only [Finset.sum_image hEinj, Finset.sum_image hUinj]
    by_cases hi : ∃ c, sel c = i
    · obtain ⟨c, rfl⟩ := hi
      rw [extZ_sel hsel]
      have hE2 : ∑ x ∈ steps, cf (extZ sel x) * extZ sel x (sel c) = ∑ x ∈ steps, coeffs x * x c :=
        Finset.sum_congr rfl (fun x hx => by rw [cE x hx, extZ_sel hsel])
      have hU2 : ∑ p ∈ NR, cf (unitVec p) * unitVec p (sel c) = 0 :=
        Finset.sum_eq_zero (fun p hp => by
          rw [hNR, Finset.mem_filter] at hp; rw [unitVec_ne (hp.2 c), mul_zero])
      rw [hE2, hU2, add_zero]
      have hcc := congrFun hc c
      simpa using hcc
    · push Not at hi
      rw [extZ_not_range base hi]
      have hE2 : ∑ x ∈ steps, cf (extZ sel x) * extZ sel x i = 0 :=
        Finset.sum_eq_zero (fun x _ => by rw [extZ_not_range x hi, mul_zero])
      have hU2 : ∑ p ∈ NR, cf (unitVec p) * unitVec p i = v i := by
        rw [Finset.sum_eq_single i]
        · rw [cU i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩), unitVec_same, mul_one]
        · intro p _ hpi; rw [unitVec_ne (Ne.symm hpi), mul_zero]
        · intro hni; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) (hNR ▸ hni)
      rw [hE2, hU2, zero_add, zero_add]
  · rintro ⟨coeffs', hv⟩
    refine ⟨fun s => coeffs' (extZ sel s), ?_⟩
    funext c
    have hvsc : v (sel c) = extZ sel base (sel c)
        + ∑ s' ∈ (E ∪ U), coeffs' s' * s' (sel c) := by rw [hv]
    rw [hvsc, extZ_sel hsel, Finset.sum_union hdisj, hE, hU]
    simp only [Finset.sum_image hEinj, Finset.sum_image hUinj]
    have hUz : ∑ p ∈ NR, coeffs' (unitVec p) * unitVec p (sel c) = 0 :=
      Finset.sum_eq_zero (fun p hp => by
        rw [hNR, Finset.mem_filter] at hp; rw [unitVec_ne (hp.2 c), mul_zero])
    rw [hUz, add_zero]
    congr 1
    exact Finset.sum_congr rfl (fun s _ => by rw [extZ_sel hsel])

/-- **Cylindrification (general form):** the preimage of a semilinear set under an
injective coordinate selection `v ↦ v ∘ sel` is semilinear. -/
theorem isSemilinearNd_comap_injective {d e : ℕ} (sel : Fin e → Fin d)
    (hsel : Function.Injective sel) {S : Set (Fin e → ℕ)} (hS : IsSemilinearNd e S) :
    IsSemilinearNd d {v : Fin d → ℕ | (fun c => v (sel c)) ∈ S} := by
  classical
  obtain ⟨comps, hcomp, rfl⟩ := hS
  refine ⟨comps.image (fun C => {v : Fin d → ℕ | (fun c => v (sel c)) ∈ C}), ?_, ?_⟩
  · intro C' hC'
    rw [Finset.mem_image] at hC'
    obtain ⟨C, hC, rfl⟩ := hC'
    obtain ⟨base, steps, rfl⟩ := hcomp C hC
    exact ⟨extZ sel base, _, linearSet_comap_injective sel hsel base steps⟩
  · have hpre : {v : Fin d → ℕ | (fun c => v (sel c)) ∈ ⋃ C ∈ comps, C}
        = ⋃ C ∈ comps, {v : Fin d → ℕ | (fun c => v (sel c)) ∈ C} := by
      ext v; simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    rw [hpre, Finset.set_biUnion_finset_image]

/-! ## Derived closures -/

/-- The full space is semilinear (complement of `∅`). -/
theorem isSemilinearNd_univ (d : ℕ) :
    IsSemilinearNd d (Set.univ : Set (Fin d → ℕ)) :=
  isSemilinearNd_congr (by simp) (isSemilinearNd_compl (isSemilinearNd_empty d))

/-- A finite indexed intersection of semilinear sets is semilinear. -/
theorem isSemilinearNd_biInter {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Set (Fin d → ℕ)) (h : ∀ i ∈ s, IsSemilinearNd d (f i)) :
    IsSemilinearNd d (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isSemilinearNd_univ d
  | insert a s ha ih =>
      rw [Finset.set_biInter_insert]
      exact isSemilinearNd_inter (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **Bounded/guarded universal over the last coordinate is semilinear.**  This is
the `∀b` building block: erasing one quantified atom coordinate by
`∀ = ¬∃¬`, via the complement and projection closures. -/
theorem isSemilinearNd_forall_last {d : ℕ} {S : Set (Fin (d + 1) → ℕ)}
    (hS : IsSemilinearNd (d + 1) S) :
    IsSemilinearNd d {v : Fin d → ℕ | ∀ t : ℕ, (Fin.snoc v t) ∈ S} := by
  have h3 := isSemilinearNd_compl (isSemilinearNd_proj (isSemilinearNd_compl hS))
  refine isSemilinearNd_congr ?_ h3
  ext v
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, Set.mem_compl_iff]
  exact ⟨fun h t => not_not.mp (h t), fun h t => not_not.mpr (h t)⟩


/-! ## Finset-count bridges (set-fibre cardinality ↔ Finset.filter count) -/

/-- **Fibre cardinality as a `Finset` count.**  When the family `Φ` at slice `n` is
supported inside a finite range `F`, its set-fibre cardinality `Nat.card {ī : Φ n ī}`
equals the `Finset.filter` count over `F` — the form the `TieCountAffineBudgeted`
sum is written in.  Bridges the counting axiom to step 4. -/
theorem natCard_setOf_eq_filter_card {k : ℕ} (Φ : ℕ → (Fin k → ℕ) → Prop)
    (n : ℕ) (F : Finset (Fin k → ℕ))
    (hsupp : ∀ ī, Φ n ī → ī ∈ F) :
    Nat.card {ī : Fin k → ℕ | Φ n ī}
      = (F.filter (fun ī => Φ n ī)).card := by
  classical
  have hset : {ī : Fin k → ℕ | Φ n ī} = ↑(F.filter (fun ī => Φ n ī)) := by
    ext ī
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter]
    exact ⟨fun h => ⟨hsupp ī h, h⟩, fun h => h.2⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- The set-fibre of a `Finset`-supported family is finite. -/
theorem finite_setOf_of_support {k : ℕ} (Φ : ℕ → (Fin k → ℕ) → Prop)
    (n : ℕ) (F : Finset (Fin k → ℕ)) (hsupp : ∀ ī, Φ n ī → ī ∈ F) :
    Set.Finite {ī : Fin k → ℕ | Φ n ī} := by
  apply Set.Finite.subset F.finite_toSet
  intro ī hī
  exact hsupp ī hī

end SliceSemilinearN
