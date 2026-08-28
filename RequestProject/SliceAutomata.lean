/-
# Automata core for the slice analysis (paper §7)

The mathematical heart of the regular-slice reduction is finite-automaton
*eventual periodicity*: reading a fixed block `loop` repeatedly, the state of a
finite automaton is eventually periodic in the number of repetitions, and any
ℤ-weight accumulated along the run therefore grows *affinely on residue classes*
of the repetition count.  This file proves those two facts abstractly:

* `iterate_eventuallyPeriodic` — a finite-state iteration is eventually periodic;
* `recurrence_affineOnResidues` — a sequence with `S(n+p) = S(n) + P` for `n ≥ m`
  is affine on residue classes;
* `partialSum_recurrence` — partial sums of an eventually-periodic sequence
  satisfy that recurrence.

These are reusable and are what the paper's one-loop slice lemmas rest on.
-/
import Mathlib

namespace SliceAutomata

/-- **Finite-state eventual periodicity.**  For `f : Q → Q` with `Q` finite and any
start `q₀`, the iterates `f^[j] q₀` are eventually periodic: there are a threshold
`m` and a period `p ≥ 1` with `f^[j+p] q₀ = f^[j] q₀` for all `j ≥ m`. -/
theorem iterate_eventuallyPeriodic {Q : Type*} [Finite Q] (f : Q → Q) (q₀ : Q) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ j, m ≤ j → f^[j + p] q₀ = f^[j] q₀ := by
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite (fun j : ℕ => f^[j] q₀)
  -- Reduce to the case `a < b`.
  suffices h : ∀ a b : ℕ, a < b → f^[a] q₀ = f^[b] q₀ →
      ∃ m p : ℕ, 1 ≤ p ∧ ∀ j, m ≤ j → f^[j + p] q₀ = f^[j] q₀ by
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact h a b hlt hfab
    · exact h b a hgt hfab.symm
  intro a b hlt hfab
  refine ⟨a, b - a, by omega, fun j hj => ?_⟩
  have hidx : j + (b - a) = (j - a) + b := by omega
  have hidx2 : (j - a) + a = j := by omega
  rw [hidx, Function.iterate_add_apply, ← hfab, ← Function.iterate_add_apply, hidx2]

/-- **Recurrence ⇒ affine on residues.**  If `S(n+p) = S(n) + P` for every `n ≥ m`,
then on the residue class of `m + r` (mod `p`) the sequence `S` is affine in the
repetition count `k`: `S(m + p·k + r) = S(m + r) + k • P`. -/
theorem recurrence_affineOnResidues {M : Type*} [AddCommMonoid M] (S : ℕ → M) (m p : ℕ)
    (P : M) (h : ∀ n, m ≤ n → S (n + p) = S n + P) :
    ∀ k r : ℕ, S (m + p * k + r) = S (m + r) + k • P := by
  intro k r
  induction k with
  | zero => simp
  | succ k ih =>
      have hidx : m + p * (k + 1) + r = (m + p * k + r) + p := by ring
      rw [hidx, h _ (by omega), ih, succ_nsmul, add_assoc]

/-- Partial sums `S n = Σ_{i<n} g i` of an *eventually periodic* sequence (period
`p` from threshold `m`) satisfy the recurrence `S(N+p) = S(N) + P` for `N ≥ m`,
with `P` the sum over one period.  Proved by induction on `N` from `m`, using
`sum_range_succ` and `g(i+p) = g(i)` — no window rotation needed. -/
theorem partialSum_recurrence {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m p : ℕ)
    (hper : ∀ i, m ≤ i → g (i + p) = g i) :
    ∀ n, (∑ i ∈ Finset.range (m + n + p), g i) =
      (∑ i ∈ Finset.range (m + n), g i) + (∑ i ∈ Finset.Ico m (m + p), g i) := by
  intro n
  induction n with
  | zero =>
      simp only [add_zero, Finset.range_eq_Ico]
      exact (Finset.sum_Ico_consecutive g (Nat.zero_le m) (Nat.le_add_right m p)).symm
  | succ n ih =>
      have e1 : m + (n + 1) + p = (m + n + p) + 1 := by ring
      have e2 : m + (n + 1) = (m + n) + 1 := by ring
      rw [e1, e2, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        hper (m + n) (Nat.le_add_right m n)]
      abel

/-- Repackaged for `recurrence_affineOnResidues`: the partial-sum recurrence in
`∀ N ≥ m, S(N+p) = S(N) + P` form. -/
theorem partialSum_recurrence' {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m p : ℕ)
    (hper : ∀ i, m ≤ i → g (i + p) = g i) :
    ∀ N, m ≤ N → (∑ i ∈ Finset.range (N + p), g i) =
      (∑ i ∈ Finset.range N, g i) + (∑ i ∈ Finset.Ico m (m + p), g i) := by
  intro N hN
  have := partialSum_recurrence g m p hper (N - m)
  rwa [show m + (N - m) = N from by omega] at this

/-- **Rank accumulation over `n` blocks is affine on residue classes (paper
Lemma 6.3).**  For a finite-state block transition `blockStep`, start `q₀`, and a
weight `w : Q → M`, the total weight accumulated over the first `n` blocks,
`Σ_{i<n} w(blockStep^[i] q₀)`, is — beyond a threshold `m` and on the residue
class of `m + r` mod a period `p` — affine in the block count: it equals
`(value at m+r) + k • P` for a fixed `P`.  This is the proved automata heart of
the regular-slice rank analysis. -/
theorem affineOnResidues_of_blockIterate {Q : Type*} [Finite Q] {M : Type*} [AddCommMonoid M]
    (blockStep : Q → Q) (q₀ : Q) (w : Q → M) :
    ∃ (m p : ℕ) (P : M), 1 ≤ p ∧
      ∀ k r : ℕ, (∑ i ∈ Finset.range (m + p * k + r), w (blockStep^[i] q₀)) =
        (∑ i ∈ Finset.range (m + r), w (blockStep^[i] q₀)) + k • P := by
  obtain ⟨m, p, hp, hper⟩ := iterate_eventuallyPeriodic blockStep q₀
  set g : ℕ → M := fun i => w (blockStep^[i] q₀) with hg
  have hgper : ∀ i, m ≤ i → g (i + p) = g i := fun i hi => congrArg w (hper i hi)
  exact ⟨m, p, ∑ i ∈ Finset.Ico m (m + p), g i, hp,
    recurrence_affineOnResidues (fun n => ∑ i ∈ Finset.range n, g i) m p _
      (partialSum_recurrence' g m p hgper)⟩

end SliceAutomata
