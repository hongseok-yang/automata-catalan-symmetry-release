/-
# The §7 capstone, general arity (GA-8.1)

`wrp_slice_profile_affine_general` — the FULL general-arity slice-analysis statement,
with the byte-identical conclusion of the axiom `wrp_slice_profile_affine`: for a
`Valid` WRP presentation realising `T` with linear output growth and some realized
slice, the slice profile of `T` is the graph of a function affine on residue classes.
No arity hypothesis.  `g` is the gated `fasCountGA`/`tailUCountGA` pair on in-domain
slices and a fixed realized profile point elsewhere; affineness from the GA-7
deliverables + the eventually periodic domain bit; the set equality from
`exists_isOutput_slice_GA` + `fas_eq_firstAscent_out_GA`.  Base `+ SliceMSO.buchi`.
-/
import RequestProject.SliceFasCountGA
import RequestProject.SliceProfile

namespace SliceFasAssemblyGA

open WRP SliceFasCountGA
open scoped Classical

/-- **The general-arity capstone**: the slice profile is affine-in-period. -/
theorem wrp_slice_profile_affine_general
    (T : List Step → Option (List Step))
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hPT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (hgrow : ∃ C, ∀ n out, T (wrappedFlat n) = some out → out.length ≤ C * (n + 1))
    (hne : ∃ n : ℕ, 1 ≤ n ∧ ∃ out, T (wrappedFlat n) = some out) :
    ∃ (g : ℕ → ℕ × ℕ) (p m : ℕ), 1 ≤ p ∧ 1 ≤ m ∧
      (∀ j, j < p → ∃ b₁ s₁ b₂ s₂ : ℕ,
        ∀ k, g (m + j + p * k) = (b₁ + k * s₁, b₂ + k * s₂)) ∧
      (∀ n, 1 ≤ n → ∀ out, T (wrappedFlat n) = some out →
        (firstAscent out, tailU out) = g n) ∧
      sliceProfile T = {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧ q = g n} := by
  classical
  obtain ⟨n₀, hn₀1, out₀, hTout₀⟩ := hne
  obtain ⟨C, hgrowC⟩ := hgrow
  have hbud := SliceProfileDischargeGA.hbud_of_hgrow P hV T C hPT hgrowC
  obtain ⟨fas', Nf, hfasAff, hfasAgr⟩ := fas_count_affineOnResidues_GA P hV C hbud
  have htailAff := tailU_count_affineOnResidues_GA P hV C hbud
  obtain ⟨mf, pf, sf, hpf, hfrec⟩ := hfasAff
  obtain ⟨mt, pt, st, hpt, htrec⟩ := htailAff
  obtain ⟨mD, pD, hpD, hDper⟩ := SliceFasAssembly.domain_slice_EP P.toPoly
  set fb : ℕ × ℕ := (firstAscent out₀, tailU out₀) with hfbdef
  set g : ℕ → ℕ × ℕ := fun n =>
    if P.toPoly.domain (wrappedFlat n)
    then (SliceProfileDischargeGA.fasCountGA P n,
      SliceProfileDischargeGA.tailUCountGA P n)
    else fb with hgdef
  set p : ℕ := pf * pt * pD with hpdef
  have hp : 1 ≤ p := by
    rw [hpdef]
    exact Nat.mul_pos (Nat.mul_pos hpf hpt) hpD
  set m : ℕ := mf + mt + mD + Nf + 1 with hmdef
  have hmge : mf ≤ m ∧ mt ≤ m ∧ mD ≤ m ∧ Nf ≤ m ∧ 1 ≤ m := by
    rw [hmdef]
    omega
  have hpfd : pf ∣ p := by
    rw [hpdef]
    exact (dvd_mul_right pf pt).mul_right pD
  have hptd : pt ∣ p := by
    rw [hpdef]
    exact (dvd_mul_left pt pf).mul_right pD
  have hpDd : pD ∣ p := by
    rw [hpdef]
    exact dvd_mul_left pD (pf * pt)
  refine ⟨g, p, m, hp, hmge.2.2.2.2, ?_, ?_, ?_⟩
  · -- per-class affineness
    intro j hj
    have hdomconst : ∀ k, (P.toPoly.domain (wrappedFlat (m + j + p * k))
        ↔ P.toPoly.domain (wrappedFlat (m + j))) := by
      intro k
      refine SliceFasSelector.iff_on_class
        (Pr := fun x => P.toPoly.domain (wrappedFlat x)) hpD hDper
        (by omega) (by omega) ?_
      obtain ⟨t, ht⟩ := hpDd
      rw [ht, show m + j + pD * t * k = m + j + pD * (t * k) from by ring,
        Nat.add_mul_mod_self_left]
    by_cases hcl : P.toPoly.domain (wrappedFlat (m + j))
    · -- in-domain class: ride the fas/gated-tail affine witnesses
      obtain ⟨tf, htf⟩ := hpfd
      obtain ⟨tt, htt⟩ := hptd
      refine ⟨fas' (m + j), tf * sf (m + j - mf),
        SliceProfileDischargeGA.gatedTailUCountGA P (m + j), tt * st (m + j - mt),
        fun k => ?_⟩
      have hdomk := (hdomconst k).mpr hcl
      have hfas_affine : fas' (m + j + p * k)
          = fas' (m + j) + k * (tf * sf (m + j - mf)) := by
        have h := hfrec (m + j - mf) (tf * k)
        rw [show mf + (m + j - mf) = m + j from by omega] at h
        rw [show m + j + p * k = m + j + pf * (tf * k) from by rw [htf]; ring, h]
        ring
      have htail_affine : SliceProfileDischargeGA.gatedTailUCountGA P (m + j + p * k)
          = SliceProfileDischargeGA.gatedTailUCountGA P (m + j)
            + k * (tt * st (m + j - mt)) := by
        have h := htrec (m + j - mt) (tt * k)
        simp only [] at h
        rw [show mt + (m + j - mt) = m + j from by omega] at h
        rw [show m + j + p * k = m + j + pt * (tt * k) from by rw [htt]; ring, h]
        ring
      have hfask : SliceProfileDischargeGA.fasCountGA P (m + j + p * k)
          = fas' (m + j + p * k) := by
        have := hfasAgr (m + j + p * k) (by omega)
        rw [SliceProfileDischargeGA.gatedFasCountGA, if_pos hdomk] at this
        exact this.symm
      have htailk : SliceProfileDischargeGA.tailUCountGA P (m + j + p * k)
          = SliceProfileDischargeGA.gatedTailUCountGA P (m + j + p * k) := by
        rw [SliceProfileDischargeGA.gatedTailUCountGA, if_pos hdomk]
      rw [hgdef]
      simp only []
      rw [if_pos hdomk, hfask, htailk, hfas_affine, htail_affine]
    · -- out-of-domain class: the constant fallback
      refine ⟨fb.1, 0, fb.2, 0, fun k => ?_⟩
      rw [hgdef]
      simp only []
      rw [if_neg (fun hcon => hcl ((hdomconst k).mp hcon))]
      simp
  · -- the pointwise identification on in-domain slices
    intro n _ out hTout
    obtain ⟨hdom, hIsOut⟩ := (hPT _ _).mp hTout
    obtain ⟨hfa, hta⟩ :=
      SliceProfileDischargeGA.fas_eq_firstAscent_out_GA P hV n out hIsOut
    rw [hgdef]
    simp only []
    rw [if_pos hdom, ← hfa, ← hta]
  · -- the slice-profile set equality
    ext q
    simp only [sliceProfile, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn1, out, hTout, hq⟩
      obtain ⟨hdom, hIsOut⟩ := (hPT _ _).mp hTout
      obtain ⟨hfa, hta⟩ :=
        SliceProfileDischargeGA.fas_eq_firstAscent_out_GA P hV n out hIsOut
      refine ⟨n, hn1, ?_⟩
      rw [hq, hgdef]
      simp only []
      rw [if_pos hdom, ← hfa, ← hta]
    · rintro ⟨n, hn1, hq⟩
      by_cases hdom : P.toPoly.domain (wrappedFlat n)
      · obtain ⟨out, hIsOut⟩ := SliceProfileDischargeGA.exists_isOutput_slice_GA P hV n
        obtain ⟨hfa, hta⟩ :=
          SliceProfileDischargeGA.fas_eq_firstAscent_out_GA P hV n out hIsOut
        refine ⟨n, hn1, out, (hPT _ _).mpr ⟨hdom, hIsOut⟩, ?_⟩
        rw [hq, hgdef]
        simp only []
        rw [if_pos hdom, ← hfa, ← hta]
      · refine ⟨n₀, hn₀1, out₀, hTout₀, ?_⟩
        rw [hq, hgdef]
        simp only []
        rw [if_neg hdom, hfbdef]

end SliceFasAssemblyGA
