/-
# `cor:inverse-zeta-not-wrp`: the conditional endgame

Stage A of the §9 tower.  This file
fixes the FROZEN interface `RowAffine` — the row-uniform, fas-only fragment of
`thm:two-parameter-semilinearity` that the corollary consumes — and proves everything downstream of
it unconditionally:

* `pyramid_section_not_affine` — the arithmetic finisher: the ceiling
  `(m+n+m)/(m+1)` violates row-affineness at `m := p` (two evaluations;
  `(p+1)·s = p` is impossible);
* `inverse_zeta_not_wrp_of_rowAffine` — the honest, ζ-bijectivity-free
  `cor:inverse-zeta-not-wrp`, conditional on the row theorem: no WRP transduction is a
  left inverse of `zetaMap` on Dyck paths;
* `wrp_not_closed_under_inverse_of_rowAffine` — the closure form: WRP contains
  a realiser of ζ (`zetaSweep_isWRP`) but no realiser of ζ⁻¹.

THE QUANTIFIER ORDER IN `RowAffine` IS LOAD-BEARING: the period `p` is fixed
BEFORE `m`.  The per-`m` form (period allowed to depend on `m`) is vacuous
here, because for each fixed `m` the ceiling IS eventually affine in `n` on
residue classes mod `m + 1`.  Stages B–F discharge `RowAffine` for every
linear-growth slice-total WRP transduction via the fibred re-rooting route;
`RowAffine` is an ordinary hypothesis, NOT an axiom.
-/
import RequestProject.InverseZetaFas
import RequestProject.ZetaWRP

open Step

/-- **The frozen interface** (the row-uniform fas-only fragment of
`thm:two-parameter-semilinearity`): ONE period `p ≥ 1` such that for EVERY `m ≥ 1` the section
`n ↦ firstAscent (T (W_{m,n}))` is eventually affine on each residue class of
`n` mod `p`. -/
def RowAffine (T : List Step → Option (List Step)) : Prop :=
  ∃ p, 1 ≤ p ∧ ∀ m, 1 ≤ m → ∃ N, ∀ j, j < p → ∃ b s : ℕ,
    ∀ k out, T (copiedSlice m (N + j + p * k)) = some out →
      firstAscent out = b + k * s

/-- **The arithmetic finisher**: the ceiling section at `m := p` is not
affine with period `p` — the slope would satisfy `(p+1)·s = p`. -/
theorem pyramid_section_not_affine (p N b s : ℕ) (hp : 1 ≤ p)
    (h : ∀ k, (p + (N + p * k) + p) / (p + 1) = b + k * s) : False := by
  have h0 := h 0
  have h1 := h (p + 1)
  rw [Nat.mul_zero] at h0
  have hdiv : (p + (N + p * (p + 1)) + p) / (p + 1)
      = (p + (N + 0) + p) / (p + 1) + p := by
    rw [show p + (N + p * (p + 1)) + p = (p + (N + 0) + p) + (p + 1) * p from by
      ring, Nat.add_mul_div_left _ _ (by omega : 0 < p + 1)]
  have e1 : b + 0 * s + p = b + (p + 1) * s := by
    rw [← h0, ← hdiv]
    exact h1
  have hps : p = (p + 1) * s := by
    have h2 : b + p = b + (p + 1) * s := by simpa using e1
    exact Nat.add_left_cancel h2
  rcases Nat.eq_zero_or_pos s with hs | hs
  · rw [hs, Nat.mul_zero] at hps
    omega
  · have hge : p + 1 ≤ (p + 1) * s := Nat.le_mul_of_pos_right _ hs
    rw [← hps] at hge
    omega

/-- **`cor:inverse-zeta-not-wrp`, conditional form**: given
the row theorem (Stages B–F), no WRP transduction acts as a left inverse of
the zeta map on Dyck paths.  Honest ζ-bijectivity-free statement, with FEWER
hypotheses than the paper's (no growth or totality assumed — both are derived
from the left-inverse property and `zetaMap_pyramidRow`). -/
theorem inverse_zeta_not_wrp_of_rowAffine
    (hrow : ∀ T : List Step → Option (List Step), WRP.IsWRP T →
      (∀ m n, 1 ≤ m → ∃ out, T (copiedSlice m n) = some out) →
      (∃ C, ∀ m n out, T (copiedSlice m n) = some out →
        out.length ≤ C * (m + n + 1)) →
      RowAffine T) :
    ¬ ∃ T : List Step → Option (List Step),
      WRP.IsWRP T ∧ ∀ P, IsDyckPath P → T (zetaMap P) = some P := by
  rintro ⟨T, hT, hinv⟩
  -- the left inverse pins T on every copied slice
  have hTW : ∀ m n, T (copiedSlice m n) = some (pyramidRow m n) := by
    intro m n
    rw [← zetaMap_pyramidRow m n]
    exact hinv (pyramidRow m n) (isDyckPath_pyramidRow m n)
  have htot : ∀ m n, 1 ≤ m → ∃ out, T (copiedSlice m n) = some out :=
    fun m n _ => ⟨pyramidRow m n, hTW m n⟩
  have hgrow : ∃ C, ∀ m n out, T (copiedSlice m n) = some out →
      out.length ≤ C * (m + n + 1) := by
    refine ⟨2, fun m n out hout => ?_⟩
    rw [hTW m n] at hout
    obtain rfl := Option.some.inj hout.symm
    rw [length_pyramidRow]
    omega
  obtain ⟨p, hp, hrowp⟩ := hrow T hT htot hgrow
  obtain ⟨N, hN⟩ := hrowp p hp
  obtain ⟨b, s, hbs⟩ := hN 0 (by omega)
  refine pyramid_section_not_affine p (N + 0) b s hp (fun k => ?_)
  have := hbs k (pyramidRow p (N + 0 + p * k)) (hTW p (N + 0 + p * k))
  rw [firstAscent_pyramidRow] at this
  exact this

/-- **The closure form**: WRP contains a realiser of ζ but — given the row
theorem — no realiser of ζ⁻¹: it is not closed under inversion on the Dyck
domain. -/
theorem wrp_not_closed_under_inverse_of_rowAffine
    (hrow : ∀ T : List Step → Option (List Step), WRP.IsWRP T →
      (∀ m n, 1 ≤ m → ∃ out, T (copiedSlice m n) = some out) →
      (∃ C, ∀ m n out, T (copiedSlice m n) = some out →
        out.length ≤ C * (m + n + 1)) →
      RowAffine T) :
    (∃ T : List Step → Option (List Step),
      WRP.IsWRP T ∧ ∀ P, IsDyckPath P → T P = some (zetaMap P))
    ∧ ¬ ∃ T : List Step → Option (List Step),
      WRP.IsWRP T ∧ ∀ P, IsDyckPath P → T (zetaMap P) = some P :=
  ⟨⟨fun w => some (zetaSweep w), zetaSweep_isWRP,
    fun P hP => congrArg some (zetaSweep_eq_zetaMap_of_isDyckPath P hP)⟩,
   inverse_zeta_not_wrp_of_rowAffine hrow⟩
