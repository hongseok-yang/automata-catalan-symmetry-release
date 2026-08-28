/-
# The height sweep is not polyregular

`lem:H-probe` and `thm:H-not-polyregular` (paper.tex): the height sweep `H`
is not realised by any polyregular transduction on the Dyck domain, hence not
by any deterministic MSO string transduction (2DFT) either.

The route is the two-pyramid criterion (`two_pyramid_criterion`,
`prop:two-pyramid-criterion`), shared with the zeta lower bound: by the
closed form `heightSweep_twoPyramid` (`lem:H-two-pyramid`), the regular probe
`R = UU(DU)^{2q}DD(UD)^s` of `lem:zeta-probe` cuts the family
`H(P_{m,n})` along `{n ≤ m}` (`lem:H-probe`), which no regular language
realises on the index family (`not_regular_ge_family`).  The only admitted
fact is `polyreg_regular_preimage`, inside the criterion.
-/
import RequestProject.HeightSweepTwoPyramid
import RequestProject.ZetaNotPolyreg

open Step

namespace HeightSweepNotPolyreg

open ZetaNotPolyreg

/-! ## The probe characterisation (`lem:H-probe`) -/

/-- **`lem:H-probe` (paper.tex).**  On two-pyramid paths, membership of the
height-sweep image in the probe language `R` of `lem:zeta-probe`
characterises `n ≤ m`: the exponent of `DU` before the central `DD` is the
even number `2(n-1)` when `n ≤ m` and the odd number `2m-1` when `n > m`. -/
theorem inRegularProbe_heightSweep_twoPyramid (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    inRegularProbe (heightSweep (twoPyramid m n)) ↔ n ≤ m := by
  rw [heightSweep_twoPyramid m n hm hn]
  constructor
  · intro hmem
    by_contra hgt
    push Not at hgt
    -- n > m: the word lands in `dead`, so it is not in the probe language
    rw [if_neg (by omega : ¬ n ≤ m)] at hmem
    have hacc : probeDFA.accepts
        ([U, U] ++ (List.replicate (2 * m - 1) [D, U]).flatten ++ [D, D]
          ++ (List.replicate (n - m - 1) [U, D]).flatten) := by
      have := probeDFA_language
      rw [Set.ext_iff] at this
      exact (this _).mpr hmem
    have hdead := fold_gt_word_dead m (n - m - 1) hm
    simp only [DFA'.accepts, probeDFA] at hacc
    rw [hdead] at hacc
    exact ProbeState.noConfusion hacc
  · intro hle
    rw [if_pos hle]
    -- exhibit q = n - 1, s = m - n
    exact ⟨n - 1, m - n, rfl⟩

/-! ## The separation (`thm:H-not-polyregular`) -/

/-- **`thm:H-not-polyregular` (paper.tex), genuine.**  No ordinary polyregular
transduction realises the height sweep on the Dyck domain, over the real
`Polyreg.IsPolyregular`.  Together with `heightSweep_isSRR1`
(`prop:alw-sweep-swr`), this places `H` in `sRR₁ \ PolyReg`.  Admits only
`polyreg_regular_preimage`. -/
theorem heightSweep_not_polyregular :
    ¬ ∃ T : List Step → Option (List Step),
      Polyreg.IsPolyregular T ∧ Realises T {P | IsDyckPath P} heightSweep :=
  -- the probe cuts `H(P_{m,n})` along `{n ≤ m}`, which no regular language realises
  two_pyramid_criterion heightSweep {w | inRegularProbe w} inRegularProbe_isRegular
    (fun Bad hBad hchar => not_regular_ge_family Bad hBad
      (fun m n hm hn =>
        (hchar m n hm hn).trans (inRegularProbe_heightSweep_twoPyramid m n hm hn)))

/-- **`thm:H-not-polyregular` (paper.tex), the 2DFT clause.**  The height sweep
is not realisable, on the Dyck domain, by any deterministic MSO string
transduction — equivalently (Engelfriet–Hoogeboom, the equivalence the paper
invokes) by any deterministic two-way finite-state transducer.  Every regular
string transduction is polyregular (`Polyreg.IsRegular.isPolyregular`), so the
theorem applies directly.  Same trust base (`polyreg_regular_preimage`). -/
theorem heightSweep_not_regular :
    ¬ ∃ T : List Step → Option (List Step),
      Polyreg.IsRegular T ∧ Realises T {P | IsDyckPath P} heightSweep := by
  rintro ⟨T, hreg, hreal⟩
  exact heightSweep_not_polyregular ⟨T, hreg.isPolyregular, hreal⟩

end HeightSweepNotPolyreg
