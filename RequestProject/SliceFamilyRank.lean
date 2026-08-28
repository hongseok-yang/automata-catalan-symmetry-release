/-
# Family rank structure: the per-summand toolkit (route GA-4, foundation)

The GA-4 families evaluate the rank of a GENERAL atom `(c, ī)` whose coordinates sit
in the five cells of `SliceGrowthCollapse.one_cluster_cells` (pre / suf / front-pinned
/ back-pinned / one bulk cluster at base `t`).  Ranks are separable: each summand of a
regular rank term reads ONE coordinate `ī (s.π)` (`Summand.eval`), so the rank of
the general atom decomposes through per-summand CONSTANT-tuple evaluations
(`summand_eval_proj`, definitionally), where the entire existing arity-1 region
machinery (`SliceRankRegions`, `SliceRankAtom`) applies:

* a summand whose coordinate is **pre**/`suf` is the existing `summand_pre_eq` /
  `summand_suf_*` family;
* one at a **front-pinned** position `x` is constant in both `t` and `n` once
  `x ≤ 2n` (`summand_eval_slice_stable` — prefix-determinedness plus the slice
  take-stability `wrappedFlat_take_stable`);
* one in the **cluster** at block `t+δ` equals its value on the smaller slice
  `W_{t+δ+1}` — the `RankAffine`-in-block-index families;
* one at a **back-pinned** block `n−e` equals its value on `W_{n−e+1}` — the same
  families read at index `n−e`, `RankAffine` in `n`.

This file provides the three bridges; the per-cell decomposition theorem
`rank(t, n) = R(t) + B(n)` (`rank_cell_decomp` below) assembles them.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import RequestProject.SliceRankAtom
import RequestProject.SliceRankRegions
import RequestProject.SliceWords
import RequestProject.SliceFamilyCell
import RequestProject.SliceRankBlock

namespace SliceFamilyRank

open WRP Step

variable {d : ℕ}

/-- **Separability**: a summand reads only its own coordinate, so its value at a
general tuple is its value at the constant tuple of that coordinate. -/
theorem summand_eval_proj {Alpha : Type*} {k : ℕ} (s : Summand Alpha d k)
    (w : List Alpha) (ī : Fin k → ℕ) :
    s.eval w ī = s.eval w (fun _ => ī s.π) := rfl

/-- **Separability at the term level**: the rank term at a general tuple is the
constant-plus-sum of its summands' constant-tuple values. -/
theorem rankTerm_eval_proj {Alpha : Type*} {k : ℕ} (κ : RankTerm Alpha d k)
    (w : List Alpha) (ī : Fin k → ℕ) :
    κ.eval w ī = fun c => κ.c0 c
      + (κ.summands.map (fun s => s.eval w (fun _ => ī s.π) c)).sum := by
  funext c
  unfold RankTerm.eval
  refine congrArg (κ.c0 c + ·) ?_
  refine congrArg List.sum (List.map_congr_left (fun s _ => ?_))
  rw [← summand_eval_proj]

/-- **Slice take-stability**: two slices agree up to any position `≤ 1 + 2·min`. -/
theorem wrappedFlat_take_stable (q n n' : ℕ) (hn : q ≤ 1 + 2 * n) (hn' : q ≤ 1 + 2 * n') :
    (wrappedFlat n).take q = (wrappedFlat n').take q := by
  set i := min n n' with hi
  have hq : q ≤ 1 + 2 * i := by omega
  have key : ∀ nn : ℕ, i ≤ nn → (wrappedFlat nn).take q
      = ([U] ++ (List.replicate i [U, D]).flatten).take q := by
    intro nn hnn
    rw [show (wrappedFlat nn).take q = ((wrappedFlat nn).take (1 + 2 * i)).take q from by
        rw [List.take_take, Nat.min_eq_left hq],
      SliceWords.wrappedFlat_take i nn hnn]
  rw [key n (by omega), key n' (by omega)]

/-- **A pinned summand does not see the slice grow**: at a position `x ≤ 2·min`,
the summand's value is the same on `W_n` and `W_{n'}`.  Instances: front-pinned
positions (constant for `n` beyond the pin), cluster positions (reduce to
`W_{t+δ+1}`), back-pinned positions (reduce to `W_{n−e+1}`). -/
theorem summand_eval_slice_stable {k : ℕ} (s : Summand Step d k) (x n n' : ℕ)
    (hn : x + 1 ≤ 1 + 2 * n) (hn' : x + 1 ≤ 1 + 2 * n') :
    s.eval (wrappedFlat n) (fun _ => x) = s.eval (wrappedFlat n') (fun _ => x) :=
  SliceRankAtom.summand_eval_const_prefix_stable s _ _ x
    (wrappedFlat_take_stable (x + 1) n n' hn hn')

/-! ## Shift combinators for `RankAffine` -/

open SliceRankAtom SliceFamilyCell

/-- A forward shift of a `RankAffine` sequence is `RankAffine`. -/
theorem rankAffine_shift {F : ℕ → Fin d → ℤ} (hF : RankAffine F) (δ : ℕ) :
    RankAffine (fun t => F (t + δ)) := by
  obtain ⟨m, p, P, hp, hrec⟩ := hF
  refine ⟨m, p, P, hp, fun t ht => ?_⟩
  have harg : t + p + δ = (t + δ) + p := by omega
  show F (t + p + δ) = F (t + δ) + P
  rw [harg]
  exact hrec (t + δ) (by omega)

/-- A backward (truncated-subtraction) shift of a `RankAffine` sequence is
`RankAffine`. -/
theorem rankAffine_subShift {F : ℕ → Fin d → ℤ} (hF : RankAffine F) (l : ℕ) :
    RankAffine (fun n => F (n - l)) := by
  obtain ⟨m, p, P, hp, hrec⟩ := hF
  refine ⟨m + l, p, P, hp, fun n hn => ?_⟩
  have harg : n + p - l = (n - l) + p := by omega
  show F (n + p - l) = F (n - l) + P
  rw [harg]
  exact hrec (n - l) (by omega)

/-! ## Sum-manipulation helpers -/

theorem list_sum_pi_apply {ι : Type*} (l : List ι) (g : ι → Fin d → ℤ) (c : Fin d) :
    ((l.map g).sum) c = (l.map (fun x => g x c)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.sum_cons, Pi.add_apply, ih]

theorem list_sum_map_add {ι : Type*} (l : List ι) (f g : ι → ℤ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-! ## The per-summand region decomposition -/

/-- **One summand splits by the region of its coordinate** (route GA-4): on the
window, its value is `Rs t + Bs n` with both parts `RankAffine` — front/pre regions
are constants (parked in `Rs`), cluster regions are shifted block families in `t`,
back/suf regions are (sub-shifted) families in `n`. -/
theorem summand_region_decomp {B k : ℕ} (s : Summand Step d k) (r : RegionSpec B) :
    ∃ Rs Bs : ℕ → Fin d → ℤ, RankAffine Rs ∧ RankAffine Bs ∧
      ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
        s.eval (wrappedFlat n) (fun _ => r.posAt t n) = fun c => Rs t c + Bs n c := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
  · -- pre: the constant β q0 U
    refine ⟨fun _ => s.β s.A.q0 U, fun _ => 0, RankAffine.const _, RankAffine.const _, ?_⟩
    intro t n _ _
    show s.eval (wrappedFlat n) (fun _ => 0) = _
    rw [summand_pre_eq s n]
    funext c
    simp
  · -- suf: the n-family
    refine ⟨fun _ => 0, fun n => s.eval (wrappedFlat n) (fun _ => 1 + 2 * n),
      RankAffine.const _, summand_suf_rankAffine s, ?_⟩
    intro t n _ _
    show s.eval (wrappedFlat n) (fun _ => 1 + 2 * n) = _
    funext c
    simp
  · -- front-pinned: constant once the slice clears the pin
    rcases e with _ | _
    · refine ⟨fun _ => s.eval (wrappedFlat (f.val + 1)) (fun _ => 1 + 2 * f.val),
        fun _ => 0, RankAffine.const _, RankAffine.const _, ?_⟩
      intro t n ht htn
      have hf := f.isLt
      show s.eval (wrappedFlat n) (fun _ => 1 + 2 * f.val) = _
      rw [summand_eval_slice_stable s (1 + 2 * f.val) n (f.val + 1) (by omega) (by omega)]
      funext c
      simp
    · refine ⟨fun _ => s.eval (wrappedFlat (f.val + 1)) (fun _ => 1 + 2 * f.val + 1),
        fun _ => 0, RankAffine.const _, RankAffine.const _, ?_⟩
      intro t n ht htn
      have hf := f.isLt
      show s.eval (wrappedFlat n) (fun _ => 1 + 2 * f.val + 1) = _
      rw [summand_eval_slice_stable s (1 + 2 * f.val + 1) n (f.val + 1) (by omega) (by omega)]
      funext c
      simp
  · -- back-pinned: the block family read at index n − (1 + l)
    rcases e with _ | _
    · refine ⟨fun _ => 0,
        fun n => s.eval (wrappedFlat (n - (1 + l.val) + 1))
          (fun _ => 1 + 2 * (n - (1 + l.val))),
        RankAffine.const _, rankAffine_subShift (summand_block_rankAffine s) (1 + l.val), ?_⟩
      intro t n ht htn
      have hl := l.isLt
      have harg : n - 1 - l.val = n - (1 + l.val) := by omega
      show s.eval (wrappedFlat n) (fun _ => 1 + 2 * (n - 1 - l.val)) = _
      rw [harg, summand_eval_slice_stable s (1 + 2 * (n - (1 + l.val))) n
        (n - (1 + l.val) + 1) (by omega) (by omega)]
      funext c
      simp
    · refine ⟨fun _ => 0,
        fun n => s.eval (wrappedFlat (n - (1 + l.val) + 1))
          (fun _ => 1 + 2 * (n - (1 + l.val)) + 1),
        RankAffine.const _, rankAffine_subShift (summand_blockD_rankAffine s) (1 + l.val), ?_⟩
      intro t n ht htn
      have hl := l.isLt
      have harg : n - 1 - l.val = n - (1 + l.val) := by omega
      show s.eval (wrappedFlat n) (fun _ => 1 + 2 * (n - 1 - l.val) + 1) = _
      rw [harg, summand_eval_slice_stable s (1 + 2 * (n - (1 + l.val)) + 1) n
        (n - (1 + l.val) + 1) (by omega) (by omega)]
      funext c
      simp
  · -- cluster: the block family shifted to base t
    rcases e with _ | _
    · refine ⟨fun t => s.eval (wrappedFlat (t + δ.val + 1)) (fun _ => 1 + 2 * (t + δ.val)),
        fun _ => 0, rankAffine_shift (summand_block_rankAffine s) δ.val,
        RankAffine.const _, ?_⟩
      intro t n ht htn
      have hδ := δ.isLt
      show s.eval (wrappedFlat n) (fun _ => 1 + 2 * (t + δ.val)) = _
      rw [summand_eval_slice_stable s (1 + 2 * (t + δ.val)) n (t + δ.val + 1)
        (by omega) (by omega)]
      funext c
      simp
    · refine ⟨fun t => s.eval (wrappedFlat (t + δ.val + 1))
          (fun _ => 1 + 2 * (t + δ.val) + 1),
        fun _ => 0, rankAffine_shift (summand_blockD_rankAffine s) δ.val,
        RankAffine.const _, ?_⟩
      intro t n ht htn
      have hδ := δ.isLt
      show s.eval (wrappedFlat n) (fun _ => 1 + 2 * (t + δ.val) + 1) = _
      rw [summand_eval_slice_stable s (1 + 2 * (t + δ.val) + 1) n (t + δ.val + 1)
        (by omega) (by omega)]
      funext c
      simp

/-! ## The per-cell rank decomposition -/

/-- **The family rank shape** (route GA-4): on a cell, the rank term splits as
`R(t) + B(n)` with both parts `RankAffine` — the kernels read `R` as the running-index
family and absorb `B` into thresholds. -/
theorem rankTerm_cell_decomp {B k : ℕ} (κ : RankTerm Step d k)
    (r : Fin k → RegionSpec B) :
    ∃ R Bn : ℕ → Fin d → ℤ, RankAffine R ∧ RankAffine Bn ∧
      ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
        κ.eval (wrappedFlat n) (fun i => (r i).posAt t n) = fun c => R t c + Bn n c := by
  have hdec := fun s : Summand Step d k => summand_region_decomp s (r s.π)
  choose Rs Bs hRA hBA heq using hdec
  refine ⟨fun t => κ.c0 + (κ.summands.map (fun s => Rs s t)).sum,
    fun n => (κ.summands.map (fun s => Bs s n)).sum,
    (RankAffine.const κ.c0).add (RankAffine.listSum _ _ (fun s _ => hRA s)),
    RankAffine.listSum _ _ (fun s _ => hBA s), ?_⟩
  intro t n ht htn
  rw [rankTerm_eval_proj]
  funext c
  have hsummand : ∀ s ∈ κ.summands,
      s.eval (wrappedFlat n) (fun _ => (fun i => (r i).posAt t n) s.π) c
        = Rs s t c + Bs s n c := by
    intro s _
    rw [heq s t n ht htn]
  calc κ.c0 c + (κ.summands.map (fun s =>
        s.eval (wrappedFlat n) (fun _ => (fun i => (r i).posAt t n) s.π) c)).sum
      = κ.c0 c + (κ.summands.map (fun s => Rs s t c + Bs s n c)).sum := by
        rw [congrArg List.sum (List.map_congr_left hsummand)]
    _ = κ.c0 c + ((κ.summands.map (fun s => Rs s t c)).sum
          + (κ.summands.map (fun s => Bs s n c)).sum) := by
        rw [list_sum_map_add]
    _ = (κ.c0 c + ((κ.summands.map (fun s => Rs s t)).sum) c)
          + ((κ.summands.map (fun s => Bs s n)).sum) c := by
        rw [list_sum_pi_apply, list_sum_pi_apply]
        ring


/-- **The family rank shape at the presentation level** (route GA-4, capstone): the
rank of the atom a cell describes splits as `R(t) + B(n)` on the window, with both
parts `RankAffine`. -/
theorem rank_cell_decomp {B : ℕ} (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (r : Fin (P.toPoly.arity c) → RegionSpec B) :
    ∃ R Bn : ℕ → Fin P.d → ℤ, RankAffine R ∧ RankAffine Bn ∧
      ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
        P.rank c (wrappedFlat n) (fun i => (r i).posAt t n)
          = fun i => R t i + Bn n i := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  obtain ⟨R, Bn, hR, hBn, heq⟩ := rankTerm_cell_decomp κ r
  exact ⟨R, Bn, hR, hBn, fun t n ht htn => by rw [hκ, heq t n ht htn]⟩


end SliceFamilyRank
