/-
# Bounded gated convolution kernels (§9 tower, F3.9)

The lex/eq convolution kernels (`CopiedKernels.gated{Lex,Eq}Convolution_at`)
require the slope-product `∏_c max ((pu·pv)·PR c).natAbs 1` to divide the output
period `Q`.  In the fibred tower the rank slope `PR` is bounded per-coordinate by
an `mS`-FREE `SP` (the bounded-slope tower, ending at
`CopiedSetup.dstar_setup_fibred_bounded`), so the slope-product divides the
`mS`-free factorial `(∏_c max ((pu·pv)·SP c) 1)!`
(`SlicePeriodStar.prod_max_natAbs_dvd_factorial`).  These wrappers pre-discharge
`hdvdQ` from the bound, exposing the explicit `mS`-free output period.  Both the
strict and the tie fibred counts call these.
-/
import RequestProject.CopiedKernels
import RequestProject.CopiedSlopeBound

namespace CopiedKernels

open SlicePeriodStar CopiedAffineAt
open scoped Classical

/-- **The bounded lex convolution kernel**: same as `gatedLexConvolution_at` but
with `hdvdQ` discharged from an `mS`-free per-coordinate slope bound `SP`, so the
output period is the explicit `mS`-free
`P · (pu·pv·pR) · (∏_c max ((pu·pv)·SP c) 1)!`. -/
theorem gatedLexConvolution_bounded {α β : Type*} {d : ℕ}
    (u : ℕ → α) (v : ℕ → β) (b : α → β → Prop)
    {mu pu : ℕ} (hpu : 1 ≤ pu) (hu : ∀ i, mu ≤ i → u (i + pu) = u i)
    {mv pv : ℕ} (hpv : 1 ≤ pv) (hv : ∀ j, mv ≤ j → v (j + pv) = v j)
    (R : ℕ → Fin d → ℤ) {mR pR : ℕ} (PR : Fin d → ℤ) (hpR : 1 ≤ pR)
    (hR : ∀ j, mR ≤ j → R (j + pR) = R j + PR)
    (T : ℕ → Fin d → ℤ) {P : ℕ} (hP : 1 ≤ P)
    (hT : ∀ i, AffineOnResiduesAtZ P (fun n => T n i))
    (SP : Fin d → ℕ) (hPRb : ∀ i, (PR i).natAbs ≤ SP i) :
    SlicePeriodStar.AffineOnResiduesAt
      (P * (pu * pv * pR) * Nat.factorial (∏ c : Fin d, max (pu * pv * SP c) 1))
      (fun n => ((Finset.range n).filter
        (fun j : ℕ => WRP.lexLt (R j) (T n) ∧ b (u j) (v (n - 1 - j)))).card) := by
  have hQ : 1 ≤ P * (pu * pv * pR)
      * Nat.factorial (∏ c : Fin d, max (pu * pv * SP c) 1) :=
    Nat.mul_pos (Nat.mul_pos hP (Nat.mul_pos (Nat.mul_pos hpu hpv) hpR))
      (Nat.factorial_pos _)
  refine gatedLexConvolution_at u v b hpu hu hpv hv R PR hpR hR T hP hT hQ ?_
  exact mul_dvd_mul_left (P * (pu * pv * pR))
    (SlicePeriodStar.prod_max_natAbs_dvd_factorial (pu * pv) PR SP hPRb)

/-- **The bounded eq convolution kernel**: same as `gatedEqConvolution_at` with
`hdvdQ` discharged from the `mS`-free slope bound `SP`. -/
theorem gatedEqConvolution_bounded {α β : Type*} {d : ℕ}
    (u : ℕ → α) (v : ℕ → β) (b : α → β → Prop)
    {mu pu : ℕ} (hpu : 1 ≤ pu) (hu : ∀ i, mu ≤ i → u (i + pu) = u i)
    {mv pv : ℕ} (hpv : 1 ≤ pv) (hv : ∀ j, mv ≤ j → v (j + pv) = v j)
    (R : ℕ → Fin d → ℤ) {mR pR : ℕ} (PR : Fin d → ℤ) (hpR : 1 ≤ pR)
    (hR : ∀ j, mR ≤ j → R (j + pR) = R j + PR)
    (T : ℕ → Fin d → ℤ) {P : ℕ} (hP : 1 ≤ P)
    (hT : ∀ i, AffineOnResiduesAtZ P (fun n => T n i))
    (SP : Fin d → ℕ) (hPRb : ∀ i, (PR i).natAbs ≤ SP i) :
    SlicePeriodStar.AffineOnResiduesAt
      (P * (pu * pv * pR) * Nat.factorial (∏ c : Fin d, max (pu * pv * SP c) 1))
      (fun n => ((Finset.range n).filter
        (fun j : ℕ => R j = T n ∧ b (u j) (v (n - 1 - j)))).card) := by
  have hQ : 1 ≤ P * (pu * pv * pR)
      * Nat.factorial (∏ c : Fin d, max (pu * pv * SP c) 1) :=
    Nat.mul_pos (Nat.mul_pos hP (Nat.mul_pos (Nat.mul_pos hpu hpv) hpR))
      (Nat.factorial_pos _)
  refine gatedEqConvolution_at u v b hpu hu hpv hv R PR hpR hR T hP hT hQ ?_
  exact mul_dvd_mul_left (P * (pu * pv * pR))
    (SlicePeriodStar.prod_max_natAbs_dvd_factorial (pu * pv) PR SP hPRb)

end CopiedKernels
