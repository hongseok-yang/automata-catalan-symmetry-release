/-
# An "affine on residue classes" algebra for ℕ-valued slice statistics

The selection-counting assembly needs to add up several `ℕ → ℕ` contributions —
eventually-periodic boundary terms and a convolution core — and conclude the total
is affine on residue classes of `n`.  This file fixes a single predicate
`AffineOnResidues` capturing exactly that shape and proves it is closed under the
operations the assembly uses:

* eventually-periodic ⇒ `AffineOnResidues` (slope `0`);
* closed under pointwise addition (align thresholds and periods) and finite sums;
* closed under shifting the argument by a constant;
* closed under eventual agreement (`AffineOnResidues.congr_eventually`).

The convolution kernels that produce the assembly's core terms live in `SliceGatedConv`.

`#print axioms` of everything here stays at `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib

namespace SliceAffine

/-- `f : ℕ → ℕ` is **affine on residue classes**: beyond a threshold `m`, on the
arithmetic progression `m + r, m + r + p, m + r + 2p, …` it is affine in the step
count, with a residue-dependent slope `s r`. -/
def AffineOnResidues (f : ℕ → ℕ) : Prop :=
  ∃ (m p : ℕ) (s : ℕ → ℕ), 1 ≤ p ∧ ∀ r k : ℕ, f (m + r + p * k) = f (m + r) + k * s r

/-- An eventually-periodic function is affine on residues with slope `0`. -/
theorem affineOnResidues_of_eventuallyPeriodic {f : ℕ → ℕ} {m p : ℕ} (hp : 1 ≤ p)
    (h : ∀ n, m ≤ n → f (n + p) = f n) : AffineOnResidues f := by
  refine ⟨m, p, fun _ => 0, hp, fun r k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show m + r + p * (k + 1) = (m + r + p * k) + p from by ring, h _ (by omega), ih]
      simp

/-- Affine-on-residues is closed under pointwise addition. -/
theorem AffineOnResidues.add {f g : ℕ → ℕ} (hf : AffineOnResidues f)
    (hg : AffineOnResidues g) : AffineOnResidues (fun n => f n + g n) := by
  obtain ⟨mf, pf, sf, hpf, hf⟩ := hf
  obtain ⟨mg, pg, sg, hpg, hg⟩ := hg
  refine ⟨max mf mg, pf * pg, fun r => pg * sf (max mf mg + r - mf) + pf * sg (max mf mg + r - mg),
    Nat.one_le_iff_ne_zero.mpr (by positivity), fun r k => ?_⟩
  set m := max mf mg with hm
  -- evaluate `f` along its own period `pf`
  have ef : f (m + r + pf * pg * k) = f (m + r) + k * (pg * sf (m + r - mf)) := by
    have hb : m + r = mf + (m + r - mf) := by omega
    rw [show m + r + pf * pg * k = mf + (m + r - mf) + pf * (pg * k) from by rw [← hb]; ring,
      hf (m + r - mf) (pg * k), ← hb]
    ring
  have eg : g (m + r + pf * pg * k) = g (m + r) + k * (pf * sg (m + r - mg)) := by
    have hb : m + r = mg + (m + r - mg) := by omega
    rw [show m + r + pf * pg * k = mg + (m + r - mg) + pg * (pf * k) from by rw [← hb]; ring,
      hg (m + r - mg) (pf * k), ← hb]
    ring
  simp only []
  rw [ef, eg]
  ring

/-- Affine-on-residues is preserved by shifting the argument down by a constant. -/
theorem AffineOnResidues.shift {f : ℕ → ℕ} (hf : AffineOnResidues f) (d : ℕ) :
    AffineOnResidues (fun n => f (n - d)) := by
  obtain ⟨m, p, s, hp, hf⟩ := hf
  refine ⟨m + d, p, s, hp, fun r k => ?_⟩
  simp only [show m + d + r + p * k - d = m + r + p * k from by omega,
    show m + d + r - d = m + r from by omega]
  exact hf r k

/-- Affine-on-residues transfers along eventual pointwise equality. -/
theorem AffineOnResidues.congr_eventually {f g : ℕ → ℕ} {N : ℕ} (h : ∀ n, N ≤ n → f n = g n)
    (hg : AffineOnResidues g) : AffineOnResidues f := by
  obtain ⟨mg, pg, sg, hpg, hg⟩ := hg
  refine ⟨max N mg, pg, fun r => sg (max N mg + r - mg), hpg, fun r k => ?_⟩
  set m := max N mg with hm
  rw [h _ (show N ≤ m + r + pg * k from by omega), h _ (show N ≤ m + r from by omega)]
  have hb : m + r = mg + (m + r - mg) := by omega
  rw [show m + r + pg * k = mg + (m + r - mg) + pg * k from by rw [← hb], hg (m + r - mg) k, ← hb]

/-- The zero function is affine on residues. -/
theorem AffineOnResidues.zero : AffineOnResidues (fun _ => 0) :=
  ⟨0, 1, fun _ => 0, le_refl 1, fun r k => by simp⟩

/-- Affine-on-residues is closed under finite sums. -/
theorem AffineOnResidues.finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℕ) :
    (∀ i ∈ s, AffineOnResidues (fun n => f i n)) →
      AffineOnResidues (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction with
  | empty => intro _; simpa using AffineOnResidues.zero
  | insert a s ha ih =>
      intro h
      exact AffineOnResidues.congr_eventually (N := 0) (fun n _ => Finset.sum_insert ha)
        ((h a (Finset.mem_insert_self a s)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))

end SliceAffine
