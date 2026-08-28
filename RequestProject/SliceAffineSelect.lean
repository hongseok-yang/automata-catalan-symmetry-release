/-
# `AffineOnResidues` of an eventually-periodically-selected family

The singly-tagged slice count assembles several `AffineOnResidues` pieces under a
*case split that depends on `n` eventually-periodically*: e.g. the pre-segment of the
tagged convolution uses, on each residue class of `n`, a fixed "tail-acceptance"
kernel `β_n` (which ranges over a finite set and is eventually periodic in `n`); and
the D-present / D-absent split of `fas` is gated by an eventually-periodic predicate.

This file packages that pattern once:

  **`AffineOnResidues.select`** — if `sel : ℕ → ι` lands in a finite set `s`, each
  `f i` is `AffineOnResidues`, and each fibre `{n | sel n = i}` is eventually periodic,
  then `n ↦ f (sel n) n` is `AffineOnResidues`.

Proof: `f (sel n) n = ∑_{i ∈ s} f i n · [sel n = i]`, a finite sum of an
`AffineOnResidues` times an eventually-periodic `{0,1}` indicator — each summand is
`AffineOnResidues` by `affineOnResidues_mul_bddOne`, the sum by `finsetSum`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import RequestProject.SliceFasCount

namespace SliceAffine

open SliceThreshold SliceOrder SliceFasCount
open scoped Classical

/-- **`AffineOnResidues` of an eventually-periodically-selected family.**  If the
selector `sel` always lands in the finite set `s`, every selected family `f i` is
`AffineOnResidues`, and every fibre `{n | sel n = i}` is eventually periodic with a
common period `p`, then `n ↦ f (sel n) n` is `AffineOnResidues`. -/
theorem AffineOnResidues.select {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℕ) (sel : ℕ → ι)
    (p : ℕ) (hp : 1 ≤ p) (hf : ∀ i ∈ s, AffineOnResidues (f i)) (hmem : ∀ n, sel n ∈ s)
    (hEP : ∀ i ∈ s, EventuallyPeriodic (fun n => sel n = i) p) :
    AffineOnResidues (fun n => f (sel n) n) := by
  have hpt : (fun n => f (sel n) n)
      = (fun n => ∑ i ∈ s, f i n * (if sel n = i then 1 else 0)) := by
    funext n
    have hcong : ∀ i ∈ s,
        f i n * (if sel n = i then (1 : ℕ) else 0) = if sel n = i then f i n else 0 :=
      fun i _ => by by_cases h : sel n = i <;> simp [h]
    rw [Finset.sum_congr rfl hcong, Finset.sum_ite_eq s (sel n) (fun i => f i n), if_pos (hmem n)]
  rw [hpt]
  refine AffineOnResidues.finsetSum s _ (fun i hi => ?_)
  exact affineOnResidues_mul_bddOne (hf i hi)
    (affineOnResidues_indicator_of_EP hp (hEP i hi)) (fun n => by by_cases h : sel n = i <;> simp [h])

end SliceAffine
