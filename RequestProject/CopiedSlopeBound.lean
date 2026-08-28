/-
# The bounded block-iterate slope (§9 tower, F3.9 prep)

The rank slope of a fibred cell is, at bottom, a BLOCK-CYCLE weight sum
`P(q₀) = ∑_{i ∈ Ico m (m+p)} w (blockStep^[i] q₀)` (the slope from
`SlicePeriodStar.affineOnResidues_of_blockIterate_func`).  Because `q₀` ranges
over the FINITE state set and `w` is bounded, this slope is bounded by an
`mS`-FREE constant `p · sup_q |w q|`.  This is the atomic ingredient that lets the
strict/tie counts pin at the `mS`-free period `RowAffine` demands (the lex/eq
kernels need the slope-product to divide an `mS`-free `Q`; a bound gives that via
`slope-product ∣ K!`).
-/
import RequestProject.SlicePeriodStar

namespace SlicePeriodStar

open scoped Classical

/-- **The bounded block-iterate slope** (the rank twin's bound): the eventual
per-period increment `P` of `∑_{i<n} w (blockStep^[i] q₀)` is bounded, in EACH
coordinate, by the `mS`-free constant `SP c = p · sup_q |w q c|` — uniformly in
the start state `q₀`.  Same `(m, p)` and recurrence as
`affineOnResidues_of_blockIterate_func`. -/
theorem affineOnResidues_of_blockIterate_func_bounded {Q : Type*} [Finite Q] {d : ℕ}
    (blockStep : Q → Q) (w : Q → Fin d → ℤ) :
    ∃ (m p : ℕ) (SP : Fin d → ℕ), 1 ≤ p ∧ ∀ q₀ : Q, ∃ P : Fin d → ℤ,
      (∀ k r : ℕ, (∑ i ∈ Finset.range (m + p * k + r), w (blockStep^[i] q₀)) =
        (∑ i ∈ Finset.range (m + r), w (blockStep^[i] q₀)) + k • P)
      ∧ (∀ c, (P c).natAbs ≤ SP c) := by
  have : Fintype Q := Fintype.ofFinite Q
  obtain ⟨m, p, hp, hper⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic
      (fun g : Q → Q => blockStep ∘ g) id
  have key : ∀ k, (fun g : Q → Q => blockStep ∘ g)^[k] id = blockStep^[k] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, ← Function.iterate_succ']
  -- the coordinatewise sup bound on `w`
  set SUP : Fin d → ℕ := fun c => Finset.univ.sup (fun q : Q => (w q c).natAbs)
    with hSUPdef
  have hwbound : ∀ q c, (w q c).natAbs ≤ SUP c := by
    intro q c
    rw [hSUPdef]
    exact Finset.le_sup (f := fun q : Q => (w q c).natAbs) (Finset.mem_univ q)
  refine ⟨m, p, fun c => p * SUP c, hp, fun q₀ => ?_⟩
  set g : ℕ → Fin d → ℤ := fun i => w (blockStep^[i] q₀) with hg
  have hgper : ∀ i, m ≤ i → g (i + p) = g i := by
    intro i hi
    show w (blockStep^[i + p] q₀) = w (blockStep^[i] q₀)
    have hfun : blockStep^[i + p] = blockStep^[i] := by
      rw [← key, ← key]; exact hper i hi
    rw [hfun]
  refine ⟨∑ i ∈ Finset.Ico m (m + p), g i,
    SliceAutomata.recurrence_affineOnResidues
      (fun n => ∑ i ∈ Finset.range n, g i) m p _
      (SliceAutomata.partialSum_recurrence' g m p hgper), fun c => ?_⟩
  -- the bound: |∑_{Ico m (m+p)} g i c| ≤ p · SUP c
  rw [Finset.sum_apply]
  show (∑ i ∈ Finset.Ico m (m + p), g i c).natAbs ≤ p * SUP c
  have hcard : (Finset.Ico m (m + p)).card = p := by rw [Nat.card_Ico]; omega
  have hperi : ∀ i, -((SUP c : ℕ) : ℤ) ≤ g i c ∧ g i c ≤ ((SUP c : ℕ) : ℤ) := by
    intro i
    have hb : (g i c).natAbs ≤ SUP c := by rw [hg]; exact hwbound _ c
    have hb' : |g i c| ≤ ((SUP c : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hb
    exact abs_le.mp hb'
  have hb : |∑ i ∈ Finset.Ico m (m + p), g i c| ≤ ((p * SUP c : ℕ) : ℤ) := by
    rw [abs_le]
    constructor
    · calc -(((p * SUP c : ℕ)) : ℤ)
          = ∑ _i ∈ Finset.Ico m (m + p), (-((SUP c : ℕ) : ℤ)) := by
            rw [Finset.sum_const, hcard]; push_cast; ring
        _ ≤ ∑ i ∈ Finset.Ico m (m + p), g i c :=
            Finset.sum_le_sum (fun i _ => (hperi i).1)
    · calc (∑ i ∈ Finset.Ico m (m + p), g i c)
          ≤ ∑ _i ∈ Finset.Ico m (m + p), ((SUP c : ℕ) : ℤ) :=
            Finset.sum_le_sum (fun i _ => (hperi i).2)
        _ = ((p * SUP c : ℕ)) := by rw [Finset.sum_const, hcard]; push_cast; ring
  rw [Int.abs_eq_natAbs] at hb
  exact_mod_cast hb

/-- **The slope-product divides a factorial of its `mS`-free bound.**  The
gated lex/eq convolution kernels require `slope-product ∣ Q`; here the slope
`PR` is bounded per-coordinate by an `mS`-free `SP`, so the kernel's
`∏_i max ((a·PR i).natAbs) 1` divides `(∏_i max (a·SP i) 1)!` — an `mS`-free
`Q`-factor (since any positive `n ≤ K` divides `K!`).  This is the bridge from
the bounded-slope tower to the count-level divisibility hypothesis. -/
theorem prod_max_natAbs_dvd_factorial {d : ℕ} (a : ℕ) (PR : Fin d → ℤ)
    (SP : Fin d → ℕ) (h : ∀ i, (PR i).natAbs ≤ SP i) :
    (∏ i : Fin d, max (((a : ℤ) * PR i).natAbs) 1) ∣
      Nat.factorial (∏ i : Fin d, max (a * SP i) 1) := by
  refine Nat.dvd_factorial
    (Finset.prod_pos (fun i _ => lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)))
    (Finset.prod_le_prod' (fun i _ => ?_))
  have hi : (((a : ℤ) * PR i).natAbs) ≤ a * SP i := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul le_rfl (h i)
  exact max_le_max hi le_rfl

end SlicePeriodStar
