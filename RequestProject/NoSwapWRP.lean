/-
# The no-swap theorem: no WRP transduction swaps area and dinv  (the real statement)

Formalisation of the headline theorem (`thm:wrp-no-swap`, paper-full-new.tex) of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.

Paper references below cite the STABLE LaTeX labels with the numbering of the
current revision (the paper has been renumbered: the slice analysis is §7, the
wrapped-flat/no-swap section is §8).

Unlike the `: True := trivial` milestone marker in `Semilinearity.lean`, this is
a *genuine* theorem about the concrete class `WRP.IsWRP` defined in `WRP.lean`:
it concludes `False` from the hypotheses that a WRP transduction realises an
area↔dinv swap.

Every ingredient is now **proved**: the former axiom `wrp_slice_profile_affine`
(the `W_n`-instance of the paper's §7 slice analysis, Lemmas 7.2–7.4) is a
THEOREM, discharged for GENERAL arity by
`SliceFasAssemblyGA.wrp_slice_profile_affine_general`.  The route is
deliberately NOT the paper's Presburger/Woods outline: it is an elementary,
Woods-free route — the m-mark recogniser, the one-cluster growth collapse, the
per-cell rank decomposition, the constructive `d*`-rank, the cell TIE
gate/selector/bridge, and the canonical-cell counting layer — proving exactly
the `W_n`-instance that the no-swap theorem needs (multi-parameter Presburger
definability is never formalised).  The counting step
(`thm:wrp-slice-semilinearity`, Theorem 7.6) is `wrp_slice_profile_semilinear`,
and the combinatorial results `forced_triangular_profile`
(`cor:forced-triangular-profile`, Cor 8.5) and `S_tri_not_semilinear` (Lem 8.7)
are proved as before.  Run `#print axioms wrp_no_area_dinv_swap` for the full trust
base: `[propext, Classical.choice, Quot.sound, SliceMSO.buchi]` — the textbook
Büchi–Elgot–Trakhtenbrot equivalence is the only remaining axiom.
-/
import RequestProject.WRP
import RequestProject.TightTargets
import RequestProject.Semilinearity
import RequestProject.Transducers
import RequestProject.SliceSemilinear
import RequestProject.SliceProfile
import RequestProject.SliceFasAssemblyGA

open WRP

/-- **Paper §7 slice analysis (Lemmas 7.2–7.4, `lem:one-loop-*`), now a
THEOREM** (in its `W_n`-instance, which is all the no-swap theorem uses).  On the wrapped-flat slice, the WRP machinery becomes arithmetic: the
first-ascent profile `n ↦ (fas, tailU)` of `T(W_n)` is, beyond a threshold,
*jointly affine on each residue class of `n` mod some period `p`* — equivalently,
`sliceProfile T` is the graph of such an affine-on-residues function.  This
is fully discharged for general
arity by `SliceFasAssemblyGA.wrp_slice_profile_affine_general` — the
growth-collapse route through the m-mark recogniser, the one-cluster property,
the per-cell rank decomposition, the constructive `d*`-rank, the cell TIE
gate/selector/bridge, and the canonical-cell counting layer.  The *counting* step
that turns it into semilinearity is `wrp_slice_profile_semilinear`, below, via
`SliceSemilinear.isSemilinear2_of_affineInPeriod`.

⚠ **Soundness correction (2026-06-10, found by adversarial design review).**  The
hypothesis `hne` (some slice is in `T`'s domain) is REQUIRED: without it the
statement is refutable — for the `K = 0` presentation with `domain := fun _ =>
False` the transduction `T := fun _ => none` is `IsWRP` with `sliceProfile T = ∅`,
while the conclusion's set `{q | ∃ n ≥ 1, q = g n}` is never empty.  The paper
only ever applies the lemma to a `T` realising a total map on the Dyck slice, so
`hne` is implicit there (and is supplied for free at this file's use site, the
no-swap theorem below); the paper's Remark 7.7 (`rem:slice-domain`) records the
same point.

The conclusion also carries the **pointwise identification** (deviation A4 of
`PAPER_DEVIATIONS.md`, closed 2026-08-28): on every in-domain slice the profile
of `T(W_n)` *is* `g n`, matching the paper's pointwise reading; the set-level
equality is its consequence.  The paper-literal corollaries (totality-hypothesis
form, pointwise form) are exported in `WRPPaperTheorems.lean`. -/
theorem wrp_slice_profile_affine (T : List Step → Option (List Step)) (hT : IsWRP T)
    (hgrow : ∃ C, ∀ n out, T (wrappedFlat n) = some out → out.length ≤ C * (n + 1))
    (hne : ∃ n : ℕ, 1 ≤ n ∧ ∃ out, T (wrappedFlat n) = some out) :
    ∃ (g : ℕ → ℕ × ℕ) (p m : ℕ), 1 ≤ p ∧ 1 ≤ m ∧
      (∀ j, j < p → ∃ b₁ s₁ b₂ s₂ : ℕ,
        ∀ k, g (m + j + p * k) = (b₁ + k * s₁, b₂ + k * s₂)) ∧
      (∀ n, 1 ≤ n → ∀ out, T (wrappedFlat n) = some out →
        (firstAscent out, tailU out) = g n) ∧
      sliceProfile T = {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧ q = g n} := by
  obtain ⟨P, hV, hPT⟩ := hT
  exact SliceFasAssemblyGA.wrp_slice_profile_affine_general T P hV hPT hgrow hne

/-- **`thm:wrp-slice-semilinearity` (paper-full-new.tex).**
For a WRP transduction `T` with linear output growth on the wrapped-flat slice,
the first-ascent profile set is semilinear.  Proved from the (now likewise
proved) slice-analysis theorem `wrp_slice_profile_affine` together with the
counting kernel `isSemilinear2_of_affineInPeriod`. -/
theorem wrp_slice_profile_semilinear (T : List Step → Option (List Step)) (hT : IsWRP T)
    (hgrow : ∃ C, ∀ n out, T (wrappedFlat n) = some out → out.length ≤ C * (n + 1))
    (hne : ∃ n : ℕ, 1 ≤ n ∧ ∃ out, T (wrappedFlat n) = some out) :
    IsSemilinear2 (sliceProfile T) := by
  obtain ⟨g, p, m, hp, hm, haff, -, heq⟩ := wrp_slice_profile_affine T hT hgrow hne
  rw [heq]
  exact SliceSemilinear.isSemilinear2_of_affineInPeriod g p m hp hm haff

/-- **`thm:wrp-no-swap` (paper-full-new.tex).**  There is no
WRP transduction `T` realising a length-preserving Dyck-path map `F` that swaps
`area` and `dinv`.

This is the genuine statement (it concludes `False` from the hypotheses), over
the concrete class `WRP.IsWRP`.  Two intentional strengthenings against the
paper: `F` is NOT assumed bijective (the paper's proof never uses it), and
`Presentation.Valid` asks totality only of the combined order `≺`, so `IsWRP`
quantifies over a superset of the paper's class.  Proof: by `Realises`, `T`
agrees with `F` on the Dyck slice `W_n`, so its profile set equals `F`'s, which
`forced_triangular_profile` (`cor:forced-triangular-profile`, Cor 8.5)
identifies with `S_tri`; length preservation gives the `O(n)` growth, so the
slice analysis makes that set semilinear — contradicting `S_tri_not_semilinear`
(Lem 8.7). -/
theorem wrp_no_area_dinv_swap
    (T : List Step → Option (List Step)) (hWRP : IsWRP T)
    (F : List Step → List Step)
    (hreal : Realises T {P | IsDyckPath P} F)
    (hDyck : ∀ P, IsDyckPath P → IsDyckPath (F P))
    (hlen : ∀ P, IsDyckPath P → (F P).length = P.length)
    (harea : ∀ P, IsDyckPath P → area (F P) = ↑(dinv P))
    (hdinv : ∀ P, IsDyckPath P → dinv (F P) = (area P).toNat) :
    False := by
  -- On the Dyck slice, `T` agrees with `F`.
  have hTW : ∀ n, T (wrappedFlat n) = some (F (wrappedFlat n)) := fun n =>
    hreal (wrappedFlat n) (isDyckPath_wrappedFlat n)
  -- The profile of `T` is the profile of `F`.
  have hprof : sliceProfile T =
      {p : ℕ × ℕ | ∃ n : ℕ, n ≥ 1 ∧
        p = (firstAscent (F (wrappedFlat n)), tailU (F (wrappedFlat n)))} := by
    ext p
    simp only [sliceProfile, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn, out, hout, hp⟩
      rw [hTW n] at hout
      obtain rfl := (Option.some.inj hout).symm
      exact ⟨n, hn, hp⟩
    · rintro ⟨n, hn, hp⟩
      exact ⟨n, hn, F (wrappedFlat n), hTW n, hp⟩
  -- … which Cor 7.5 identifies with `S_tri`.
  have hStri : sliceProfile T = S_tri := by
    rw [hprof]; exact forced_triangular_profile F hDyck hlen harea hdinv
  -- Length preservation gives the `O(n)` output bound.
  have hgrow : ∃ C, ∀ n out, T (wrappedFlat n) = some out → out.length ≤ C * (n + 1) := by
    refine ⟨2, fun n out hout => ?_⟩
    rw [hTW n] at hout
    obtain rfl := (Option.some.inj hout).symm
    have hl := length_wrappedFlat n
    rw [hlen (wrappedFlat n) (isDyckPath_wrappedFlat n)]
    omega
  -- `T` outputs on every slice, so slice-realizedness is immediate.
  have hne : ∃ n : ℕ, 1 ≤ n ∧ ∃ out, T (wrappedFlat n) = some out :=
    ⟨1, le_refl 1, F (wrappedFlat 1), hTW 1⟩
  -- Theorem 7.6 makes the profile semilinear, but `S_tri` is not. Contradiction.
  have hsemi := wrp_slice_profile_semilinear T hWRP hgrow hne
  rw [hStri] at hsemi
  exact S_tri_not_semilinear hsemi
