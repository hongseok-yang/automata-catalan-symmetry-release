/-
# Prefix-additive rank functions (`def:prefix-additive-rank`)

Formalisation of the rank layer of "A Computational Obstruction to Swapping Area and Dinv" (paper.tex): the *prefix-additive rank function* of
Definition `def:prefix-additive-rank` (paper.tex), the paper's
packaging of the rank-term primitive `RankTerm` of `WRP.lean`.  The prefix-rank notion itself (`def:prefix-rank`,
paper.tex) is
`RankSource.prefixRank`; the underlying source (`def:rank-source`,
paper.tex) has a *total* transition function, exactly
as `RankSource` does.

The two shapes are

* regular rank term (the Lean primitive):
  `κ(x̄) = c₀ + Σ_{t=1}^m (c_t·ρ_{A_t}(x_{π(t)}) + β_t(q_{x_{π(t)}}, a_{x_{π(t)}}))` —
  finitely many sources with integer coefficients, attached to tuple
  coordinates by an assignment `π`;
* prefix-additive rank function (the paper's shape):
  `κ(x₁,…,x_k) = c₀ + Σ_{r=1}^k (ρ_{A_r}(x_r) + β_r(q_{x_r}, a_{x_r}))` —
  exactly one coefficient-free source and correction table per coordinate.

They define the same class of functions.  This is the unlabelled equivalence
remark following `def:prefix-additive-rank`
(paper.tex), whose merge construction we formalise verbatim:

* a prefix-additive function is a regular rank term with one coefficient-`1`
  summand per coordinate (`isRegularRankTerm_of_isPrefixAdditiveRank`);
* conversely, group the summands of a regular rank term by their coordinate
  `π(t) = r` and merge each group into the product source whose transition
  weight is `Σ_{π(t)=r} c_t·ω_t` and whose local correction is the summed
  table (`isPrefixAdditiveRank_of_isRegularRankTerm`, via
  `Summand.mergedSource`/`Summand.mergedβ`).

Consequently the WRP class is unchanged when presentations are required to
carry prefix-additive rank functions (`WRP.isWRP_iff_prefixAdditive`), so
every theorem about `WRP.IsWRP` in this repository reads verbatim as a theorem
about the paper's `def:wrp` (paper.tex).
`WRP.Presentation.ofPrefixAdditive` packages the paper's presentation data
into a `WRP.Presentation`.
-/
import RequestProject.WRP

/-! ## Source combinators: zero, scaling, weight-adding product -/

section PrefixAdditiveTheory

variable {Alpha : Type*}

namespace RankSource

/-- The one-state zero-weight source ("a coordinate that makes no contribution
uses the one-state zero-weight source", `def:prefix-additive-rank`). -/
def zero (Alpha : Type*) (d : ℕ) : RankSource Alpha d where
  Q := PUnit
  fintypeQ := inferInstance
  q0 := PUnit.unit
  δ := fun _ _ => PUnit.unit
  ω := fun _ _ => 0

@[simp] theorem prefixRank_zero {d : ℕ} (w : List Alpha) (i : ℕ) (c : Fin d) :
    (zero Alpha d).prefixRank w i c = 0 := by
  unfold prefixRank
  refine Finset.sum_eq_zero fun j _ => ?_
  cases w[j]? <;> simp [zero]

/-- Scale the transition weights of a source by a fixed integer.  The states,
transitions, and hence the run are unchanged. -/
def scale {d : ℕ} (z : ℤ) (A : RankSource Alpha d) : RankSource Alpha d :=
  { A with ω := fun q a c => z * A.ω q a c }

@[simp] theorem stateBefore_scale {d : ℕ} (z : ℤ) (A : RankSource Alpha d)
    (w : List Alpha) (i : ℕ) :
    (scale z A).stateBefore w i = A.stateBefore w i := rfl

@[simp] theorem scale_ω {d : ℕ} (z : ℤ) (A : RankSource Alpha d)
    (q : A.Q) (a : Alpha) (c : Fin d) :
    (scale z A).ω q a c = z * A.ω q a c := rfl

@[simp] theorem prefixRank_scale {d : ℕ} (z : ℤ) (A : RankSource Alpha d)
    (w : List Alpha) (i : ℕ) (c : Fin d) :
    (scale z A).prefixRank w i c = z * A.prefixRank w i c := by
  unfold prefixRank
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases w[j]? <;> simp

/-- The product of two sources, running both in lockstep and *adding* their
transition weights: the "product automaton" of the merge construction
(paper.tex). -/
def add {d : ℕ} (A B : RankSource Alpha d) : RankSource Alpha d where
  Q := A.Q × B.Q
  fintypeQ := by have := A.fintypeQ; have := B.fintypeQ; exact inferInstance
  q0 := (A.q0, B.q0)
  δ := fun p a => (A.δ p.1 a, B.δ p.2 a)
  ω := fun p a c => A.ω p.1 a c + B.ω p.2 a c

private theorem foldl_prod {γ γ' : Type*} (f : γ → Alpha → γ) (g : γ' → Alpha → γ') :
    ∀ (l : List Alpha) (x : γ) (y : γ'),
      l.foldl (fun p a => (f p.1 a, g p.2 a)) (x, y) = (l.foldl f x, l.foldl g y)
  | [], _, _ => rfl
  | a :: t, x, y => foldl_prod f g t (f x a) (g y a)

@[simp] theorem stateBefore_add {d : ℕ} (A B : RankSource Alpha d)
    (w : List Alpha) (i : ℕ) :
    (add A B).stateBefore w i = (A.stateBefore w i, B.stateBefore w i) :=
  foldl_prod A.δ B.δ (w.take i) A.q0 B.q0

@[simp] theorem prefixRank_add {d : ℕ} (A B : RankSource Alpha d)
    (w : List Alpha) (i : ℕ) (c : Fin d) :
    (add A B).prefixRank w i c = A.prefixRank w i c + B.prefixRank w i c := by
  unfold prefixRank
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [stateBefore_add]
  cases w[j]? <;> simp [add]

end RankSource

/-! ## Merging a coordinate's summands into one source

`Summand.mergedSource l` runs all the sources of the summand list `l` in
lockstep, with each transition weight scaled by its summand's coefficient;
`Summand.mergedβ l` is the summed local-correction table.  When every summand
of `l` targets the tuple coordinate `r`, the merged source and table evaluated
at `x_r` reproduce the total contribution of `l` (`Summand.merged_eval`). -/

namespace Summand

variable {d k : ℕ}

/-- Merge a list of summands into a single product source with transition
weight `Σ_t c_t·ω_t`. -/
def mergedSource : List (Summand Alpha d k) → RankSource Alpha d
  | [] => RankSource.zero Alpha d
  | s :: t => RankSource.add (RankSource.scale s.coeff s.A) (mergedSource t)

/-- The summed local-correction table of a summand list, read on the merged
product state. -/
def mergedβ : (l : List (Summand Alpha d k)) → (mergedSource l).Q → Alpha → (Fin d → ℤ)
  | [] => fun _ _ => 0
  | s :: t => fun q a c => s.β q.1 a c + mergedβ t q.2 a c

theorem prefixRank_mergedSource (l : List (Summand Alpha d k)) (w : List Alpha)
    (i : ℕ) (c : Fin d) :
    (mergedSource l).prefixRank w i c
      = (l.map fun s => s.coeff * s.A.prefixRank w i c).sum := by
  induction l with
  | nil => simp [mergedSource]
  | cons s t ih => simp [mergedSource, ih]

theorem mergedβ_stateBefore (l : List (Summand Alpha d k)) (w : List Alpha)
    (i : ℕ) (a : Alpha) (c : Fin d) :
    mergedβ l ((mergedSource l).stateBefore w i) a c
      = (l.map fun s => s.β (s.A.stateBefore w i) a c).sum := by
  induction l with
  | nil => simp [mergedβ]
  | cons s t ih =>
      simp only [mergedSource, mergedβ, RankSource.stateBefore_add,
        RankSource.stateBefore_scale, List.map_cons, List.sum_cons, ih]

private theorem list_sum_map_add {γ : Type*} (l : List γ) (f g : γ → ℤ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **The merge step of the equivalence remark** (following
`def:prefix-additive-rank`, paper.tex): if every summand of `l` targets coordinate `r`, then the merged
source's prefix rank at `x_r` plus the merged correction there equals the sum
of the summands' contributions. -/
theorem merged_eval (l : List (Summand Alpha d k)) (r : Fin k)
    (hl : ∀ s ∈ l, s.π = r) (w : List Alpha) (ī : Fin k → ℕ) (c : Fin d) :
    (mergedSource l).prefixRank w (ī r) c
        + (w[ī r]?).elim 0
            (fun a => mergedβ l ((mergedSource l).stateBefore w (ī r)) a) c
      = (l.map fun s => s.eval w ī c).sum := by
  have hmap : (l.map fun s => s.eval w ī c)
      = l.map fun s => s.coeff * s.A.prefixRank w (ī r) c
          + (w[ī r]?).elim (0 : Fin d → ℤ)
              (fun a => s.β (s.A.stateBefore w (ī r)) a) c := by
    refine List.map_congr_left fun s hs => ?_
    simp only [Summand.eval, hl s hs]
  rw [hmap, list_sum_map_add, prefixRank_mergedSource]
  congr 1
  cases hw : w[ī r]? with
  | none =>
      simp
  | some a =>
      simp [mergedβ_stateBefore]

end Summand

/-! ## Definition `def:prefix-additive-rank` and the equivalence -/

/-- **Definition (`def:prefix-additive-rank`, paper.tex).**
A `d`-dimensional prefix-additive rank function on `k`-tuples: a constant
`c₀ ∈ ℤ^d` and, for each tuple coordinate `r`, one deterministic additive rank
source `A_r` together with a local-correction table `β_r`.  There are no
integer coefficients and no coordinate assignment `π` — each coordinate reads
exactly its own source. -/
structure PrefixAdditiveRank (Alpha : Type*) (d k : ℕ) where
  c0 : Fin d → ℤ
  A : Fin k → RankSource Alpha d
  β : (r : Fin k) → (A r).Q → Alpha → (Fin d → ℤ)

/-- Value `κ^w(x₁,…,x_k) = c₀ + Σ_r (ρ_{A_r}(x_r) + β_r(q_{x_r}, a_{x_r}))`. -/
def PrefixAdditiveRank.eval {d k : ℕ} (κ : PrefixAdditiveRank Alpha d k)
    (w : List Alpha) (ī : Fin k → ℕ) : Fin d → ℤ :=
  fun c => κ.c0 c + ∑ r : Fin k,
    ((κ.A r).prefixRank w (ī r) c
      + (w[ī r]?).elim 0 (fun a => κ.β r ((κ.A r).stateBefore w (ī r)) a) c)

/-- A function is a *prefix-additive rank function* when it is the evaluation
of some `PrefixAdditiveRank` data. -/
def IsPrefixAdditiveRank {d k : ℕ}
    (f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)) : Prop :=
  ∃ κ : PrefixAdditiveRank Alpha d k, ∀ w ī, f w ī = κ.eval w ī

/-- The easy inclusion: a prefix-additive rank function is a regular rank term
with one coefficient-`1` summand per tuple coordinate ("that definition is
already such an affine combination with one coefficient-1 term per
coordinate", paper.tex). -/
theorem isRegularRankTerm_of_isPrefixAdditiveRank {d k : ℕ}
    {f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)}
    (hf : IsPrefixAdditiveRank f) : IsRegularRankTerm f := by
  obtain ⟨κ, hκ⟩ := hf
  refine ⟨⟨κ.c0, List.ofFn fun r => ⟨κ.A r, 1, r, κ.β r⟩⟩, fun w ī => ?_⟩
  funext c
  rw [hκ]
  simp only [PrefixAdditiveRank.eval, RankTerm.eval]
  congr 1
  rw [List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [Summand.eval]

private theorem sum_map_filter_partition {k : ℕ} {γ : Type*} (l : List γ)
    (proj : γ → Fin k) (f : γ → ℤ) :
    (l.map f).sum = ∑ r : Fin k, ((l.filter fun s => proj s == r).map f).sum := by
  induction l with
  | nil => simp
  | cons s t ih =>
      have hsplit : ∀ r : Fin k,
          ((s :: t).filter fun x => proj x == r)
            = (if proj s = r then [s] else [])
                ++ (t.filter fun x => proj x == r) := by
        intro r
        rw [List.filter_cons]
        by_cases h : proj s = r
        · simp [h]
        · simp [h]
      simp only [List.map_cons, List.sum_cons, ih, hsplit, List.map_append,
        List.sum_append]
      rw [Finset.sum_add_distrib]
      congr 1
      have hpick : ∀ r : Fin k,
          (((if proj s = r then [s] else []) : List γ).map f).sum
            = if proj s = r then f s else 0 := by
        intro r
        by_cases h : proj s = r <;> simp [h]
      simp [hpick]

/-- The merge direction: every regular rank term is a prefix-additive rank
function.  "For each coordinate `r`, group the terms with `π(t) = r`.  Their
product automaton is a single source `A_r` […]" (the remark following
`def:prefix-additive-rank`, paper.tex). -/
theorem isPrefixAdditiveRank_of_isRegularRankTerm {d k : ℕ}
    {f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)}
    (hf : IsRegularRankTerm f) : IsPrefixAdditiveRank f := by
  obtain ⟨κ, hκ⟩ := hf
  refine ⟨⟨κ.c0,
      fun r => Summand.mergedSource (κ.summands.filter fun s => s.π == r),
      fun r => Summand.mergedβ (κ.summands.filter fun s => s.π == r)⟩,
    fun w ī => ?_⟩
  funext c
  rw [hκ]
  simp only [RankTerm.eval, PrefixAdditiveRank.eval]
  congr 1
  rw [sum_map_filter_partition κ.summands (fun s => s.π) (fun s => s.eval w ī c)]
  refine Finset.sum_congr rfl fun r _ => ?_
  refine (Summand.merged_eval _ r (fun s hs => ?_) w ī c).symm
  simpa using (List.mem_filter.mp hs).2

/-- **The equivalence remark after `def:prefix-additive-rank`**
(paper.tex): the "apparently more general" regular rank terms
(`RankTerm`) define exactly the prefix-additive rank functions. -/
theorem isRegularRankTerm_iff_isPrefixAdditiveRank {d k : ℕ}
    (f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)) :
    IsRegularRankTerm f ↔ IsPrefixAdditiveRank f :=
  ⟨isPrefixAdditiveRank_of_isRegularRankTerm, isRegularRankTerm_of_isPrefixAdditiveRank⟩

end PrefixAdditiveTheory

/-! ## The paper's `def:wrp` presents the same class -/

namespace WRP

variable {Alpha Gamma : Type*}

/-- **Definition (`def:wrp`, paper.tex) — presentation
constructor.**  The paper's WRP presentation data: a polyregular
presentation, a rank dimension `d`, and for each copy a `d`-dimensional
*prefix-additive* rank function.  It packages into a `WRP.Presentation` (whose
stored certificate is the equivalent regular-rank-term property), leaving
`Valid`, `IsOutput`, and `IsWRP` untouched. -/
def Presentation.ofPrefixAdditive (toPoly : Polyreg.Presentation Alpha Gamma) (d : ℕ)
    (rank : (c : Fin toPoly.K) → List Alpha → (Fin (toPoly.arity c) → ℕ) → (Fin d → ℤ))
    (h : ∀ c, IsPrefixAdditiveRank (rank c)) : Presentation Alpha Gamma :=
  ⟨toPoly, d, rank, fun c => isRegularRankTerm_of_isPrefixAdditiveRank (h c)⟩

@[simp] theorem Presentation.ofPrefixAdditive_rank (toPoly : Polyreg.Presentation Alpha Gamma)
    (d : ℕ) (rank : (c : Fin toPoly.K) → List Alpha → (Fin (toPoly.arity c) → ℕ) → (Fin d → ℤ))
    (h : ∀ c, IsPrefixAdditiveRank (rank c)) :
    (Presentation.ofPrefixAdditive toPoly d rank h).rank = rank := rfl

/-- **The paper's `def:wrp` defines the same class.**  `T` is WRP (in the
`RankTerm` formulation stored by `Presentation`) iff it admits a presentation
all of whose rank functions are prefix-additive, i.e. iff it is a
weighted-rank polyregular map in the sense of paper.tex
(`def:wrp`). -/
theorem isWRP_iff_prefixAdditive (T : List Alpha → Option (List Gamma)) :
    IsWRP T ↔ ∃ P : Presentation Alpha Gamma,
      (∀ c, IsPrefixAdditiveRank (P.rank c)) ∧ P.Valid ∧
      ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out) := by
  constructor
  · rintro ⟨P, hV, hT⟩
    exact ⟨P, fun c => isPrefixAdditiveRank_of_isRegularRankTerm (P.rankReg c), hV, hT⟩
  · rintro ⟨P, _, hV, hT⟩
    exact ⟨P, hV, hT⟩

end WRP
