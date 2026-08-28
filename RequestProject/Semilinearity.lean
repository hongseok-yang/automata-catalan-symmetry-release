/-
# Semilinearity and the No-Swap Theorem

Formalization of §7 (semilinear sets) and §8 (the no-swap chain) of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.
-/
import Mathlib
import RequestProject.DyckPath
import RequestProject.Transducers

open Step

/-! ## Semilinear sets (`sec:slice-semilinearity`, paper.tex) -/

/-- **§7 semilinear sets (`sec:slice-semilinearity`, paper.tex).**
A *linear set* in ℕ^d is a set of the form `{β + Σ c_j s_j : c_j ∈ ℕ}`
for a base point β and finitely many step vectors s_j. -/
def LinearSet (d : ℕ) (base : Fin d → ℕ) (steps : Finset (Fin d → ℕ)) :
    Set (Fin d → ℕ) :=
  {v | ∃ coeffs : (Fin d → ℕ) → ℕ,
    v = fun i => base i + steps.sum (fun s => coeffs s * s i)}

/-- **§7 semilinear sets (`sec:slice-semilinearity`, paper.tex).**
A *semilinear set* is a finite union of linear sets.
This is the Ginsburg–Spanier characterization of sets definable in
Presburger arithmetic. -/
def IsSemilinearNd (d : ℕ) (S : Set (Fin d → ℕ)) : Prop :=
  ∃ (components : Finset (Set (Fin d → ℕ))),
    (∀ C ∈ components, ∃ base steps, C = LinearSet d base steps) ∧
    S = ⋃ C ∈ components, C

/-- Semilinearity for subsets of ℕ². -/
def IsSemilinear2 (S : Set (ℕ × ℕ)) : Prop :=
  IsSemilinearNd 2 {v | (v 0, v 1) ∈ S}

/-! ## Theorem 7.6 (`thm:wrp-slice-semilinearity`): semilinearity for
linear-growth WRP — see `wrp_slice_profile_semilinear` in `NoSwapWRP.lean` -/
/-! ## Lemma 8.6 (`lem:semilinear-envelope`): semilinear finite-section envelopes
(`lem:semilinear-envelope`, paper.tex) -/

/-- **`lem:semilinear-envelope` (paper.tex), in a
deliberately WEAKENED sufficient form.**  If `S ⊆ ℕ²` is semilinear and every
vertical section `S_b` is finite, then on each residue class some section
element eventually lies on a fixed **rational** line — written in
integer-cleared form `q·a = p·b + γ` (i.e. `a = (p·b + γ)/q`).  This is weaker
than the paper's conclusion (the eventually-affine *minimum*), but any
affine-growth witness already beats `S_tri`'s quadratic lower bound, which is
all `S_tri_not_semilinear` needs.

An integer-slope version (`a = alpha·b + gamma`, `alpha : ℤ`) is **false**:
take `S = {(m, 2m)} ∪ {(m, 2m+1)}` — semilinear, every section the nonempty
singleton `{⌊b/2⌋}`, so every residue class mod every period qualifies; even
periods force slope `1/2 ∉ ℤ` on the even class, and odd periods mix parities,
where `⌊b/2⌋` is not affine at all.  Hence the paper's "constants α, γ" must
be read as rationals (see `PAPER_DEVIATIONS.md` § A5). -/
theorem semilinear_envelope (S : Set (ℕ × ℕ)) (hS : IsSemilinear2 S)
    -- `_hfinite` is kept for fidelity to the paper's hypotheses, but the
    -- "some affine element" construction below does not need it.
    (_hfinite : ∀ b : ℕ, Set.Finite {a | (a, b) ∈ S}) :
    ∃ M : ℕ, M ≥ 1 ∧ ∀ r : ℕ, r < M →
      ∃ p q gamma : ℤ, 0 < q ∧ ∀ᶠ b in Filter.atTop,
        b % M = r → {a | (a, b) ∈ S}.Nonempty →
        ∃ a ∈ {a | (a, b) ∈ S}, q * (a : ℤ) = p * (b : ℤ) + gamma := by
  classical
  obtain ⟨components, hcomp, hunion⟩ := hS
  choose baseF stepsF hbsF using hcomp
  -- step vectors of each component, packaged non-dependently
  set stepsOf : Set (Fin 2 → ℕ) → Finset (Fin 2 → ℕ) :=
    fun C => if hC : C ∈ components then stepsF C hC else ∅ with hstepsOf
  set allSteps : Finset (Fin 2 → ℕ) := components.biUnion stepsOf with hallSteps
  -- M is divisible by every positive step-height, and ≥ 1
  set M : ℕ := (allSteps.filter (fun s => s 1 ≠ 0)).prod (fun s => s 1) with hM_def
  have hM1 : 1 ≤ M := by
    rw [hM_def]; apply Finset.one_le_prod'; intro s hs
    rw [Finset.mem_filter] at hs; omega
  refine ⟨M, hM1, ?_⟩
  intro r hr
  by_cases hfreq : ∃ᶠ b in Filter.atTop, (b % M = r ∧ {a | (a, b) ∈ S}.Nonempty)
  · -- pick a base point `b0` so large that any element there uses a positive step
    set baseHt : Set (Fin 2 → ℕ) → ℕ :=
      fun C => if hC : C ∈ components then baseF C hC 1 else 0 with hbaseHt
    obtain ⟨b0, hb0_ge, hb0_mod, hb0_ne⟩ :=
      (Filter.frequently_atTop.mp hfreq) (components.sup baseHt + 1)
    obtain ⟨a0, ha0⟩ := hb0_ne
    -- locate the component `C` and a representation of `(a0, b0)`
    have hv0 : (![a0, b0] : Fin 2 → ℕ) ∈ {v | (v 0, v 1) ∈ S} := by simpa using ha0
    rw [hunion, Set.mem_iUnion₂] at hv0
    obtain ⟨C, hC, hvC⟩ := hv0
    rw [hbsF C hC] at hvC
    obtain ⟨coeffs, hcoeffs⟩ := hvC
    have hbase1 : baseF C hC 1 < b0 := by
      have hle : baseHt C ≤ components.sup baseHt := Finset.le_sup hC
      have : baseHt C = baseF C hC 1 := by rw [hbaseHt]; simp [hC]
      omega
    have hb0eq : b0 = baseF C hC 1 + (stepsF C hC).sum (fun s => coeffs s * s 1) := by
      have h := congrFun hcoeffs 1; simp only [Matrix.cons_val_one] at h; exact h
    -- some positive step `sstar` is used
    have hsum_ne : (stepsF C hC).sum (fun s => coeffs s * s 1) ≠ 0 := by
      intro hc; rw [hc] at hb0eq; omega
    obtain ⟨sstar, hsstar_mem, hsstar_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
    have hs1pos : 0 < sstar 1 := by
      rcases Nat.eq_zero_or_pos (sstar 1) with h | h
      · simp [h] at hsstar_ne
      · exact h
    have hdvd : sstar 1 ∣ M := by
      rw [hM_def]
      apply Finset.dvd_prod_of_mem
      rw [Finset.mem_filter]
      refine ⟨?_, by omega⟩
      rw [hallSteps, Finset.mem_biUnion]
      exact ⟨C, hC, by rw [hstepsOf]; simp [hC, hsstar_mem]⟩
    refine ⟨(sstar 0 : ℤ), (sstar 1 : ℤ), (sstar 1 : ℤ) * a0 - (sstar 0 : ℤ) * b0,
      by exact_mod_cast hs1pos, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop b0] with b hb_ge hbr _hbne
    -- on this class, `b = b0 + M·k`
    obtain ⟨k, hk⟩ : ∃ k, b = b0 + M * k := by
      have hmod : b0 ≡ b [MOD M] := by rw [Nat.ModEq, hb0_mod, hbr]
      obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hb_ge).mp hmod
      exact ⟨k, by omega⟩
    set δ : ℕ := k * (M / sstar 1) with hδ
    have hδmul : δ * sstar 1 = M * k := by
      rw [hδ, Nat.mul_assoc, Nat.div_mul_cancel hdvd, Nat.mul_comm]
    set coeffs' : (Fin 2 → ℕ) → ℕ :=
      Function.update coeffs sstar (coeffs sstar + δ) with hcoeffs'
    set a : ℕ := a0 + δ * sstar 0 with ha
    have hsum_i : ∀ i, (stepsF C hC).sum (fun s => coeffs' s * s i)
        = (stepsF C hC).sum (fun s => coeffs s * s i) + δ * sstar i := by
      intro i
      have hpt : ∀ s ∈ stepsF C hC,
          coeffs' s * s i = coeffs s * s i + (if s = sstar then δ * sstar i else 0) := by
        intro s _
        simp only [hcoeffs', Function.update_apply]
        split_ifs with h
        · subst h; ring
        · ring
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib,
        Finset.sum_ite_eq' (stepsF C hC) sstar, if_pos hsstar_mem]
    -- the extended element of `C`, and its coordinates
    set v' : Fin 2 → ℕ := fun i => baseF C hC i + (stepsF C hC).sum (fun s => coeffs' s * s i)
      with hv'
    have hv'mem : v' ∈ C := by rw [hbsF C hC]; exact ⟨coeffs', hv'⟩
    have hv'0 : v' 0 = a := by
      have h0 := congrFun hcoeffs 0; simp only [Matrix.cons_val_zero] at h0
      simp only [hv', hsum_i]; omega
    have hv'1 : v' 1 = b := by
      have h1 := congrFun hcoeffs 1; simp only [Matrix.cons_val_one] at h1
      simp only [hv', hsum_i]; omega
    have hSmem : (a, b) ∈ S := by
      have hmem : v' ∈ {v : Fin 2 → ℕ | (v 0, v 1) ∈ S} := by
        rw [hunion]; exact Set.mem_iUnion₂.mpr ⟨C, hC, hv'mem⟩
      rw [Set.mem_ofPred_eq] at hmem
      rwa [hv'0, hv'1] at hmem
    refine ⟨a, hSmem, ?_⟩
    have hδmulZ : (δ : ℤ) * sstar 1 = M * k := by exact_mod_cast hδmul
    rw [ha, hk]; push_cast
    linear_combination (sstar 0 : ℤ) * hδmulZ
  · -- eventually empty on this residue class: the conclusion is vacuous
    refine ⟨0, 1, 0, by norm_num, ?_⟩
    rw [Filter.not_frequently] at hfreq
    filter_upwards [hfreq] with b hb hbr hbne
    exact absurd ⟨hbr, hbne⟩ hb

/-! ## Lemma 8.7: The triangular profile is not semilinear
(`lem:triangular-not-semilinear`, paper.tex) -/

/-- The lower bound defining membership in `S_tri`. -/
theorem S_tri_lower_bound {a b : ℕ} (h : (a, b) ∈ S_tri) :
    b * (b - 1) / 2 + 1 ≤ a := by
  simpa [S_tri] using h.2.1

/-- The upper bound defining membership in `S_tri`. -/
theorem S_tri_upper_bound {a b : ℕ} (h : (a, b) ∈ S_tri) :
    a ≤ b * (b + 1) / 2 + 1 := by
  simpa [S_tri] using h.2.2

/-- Every vertical section of `S_tri` is finite. -/
theorem S_tri_vertical_section_finite (b : ℕ) :
    Set.Finite {a | (a, b) ∈ S_tri} := by
  refine (Set.finite_Icc 0 (b * (b + 1) / 2 + 1)).subset ?_
  intro a ha
  simp [S_tri] at ha ⊢
  exact ha.2.2

/-- Every vertical section of `S_tri` with `b >= 1` is nonempty. -/
theorem S_tri_vertical_section_nonempty (b : ℕ) (hb : b ≥ 1) :
    {a | (a, b) ∈ S_tri}.Nonempty := by
  refine ⟨b * (b - 1) / 2 + 1, ?_⟩
  have hdiv : b * (b - 1) / 2 ≤ b * (b + 1) / 2 := by
    apply Nat.div_le_div_right
    gcongr
    omega
  simp [S_tri, hb, hdiv]

/-- A quadratic lower bound eventually beats every affine function along
nonzero arithmetic progressions. -/
theorem exists_multiple_quadratic_gt_affine (M : ℕ) (hM : M ≥ 1)
    (alpha gamma : ℤ) (N : ℕ) :
    ∃ b : ℕ, N ≤ b ∧ b % M = 0 ∧
      alpha * (b : ℤ) + gamma < ((b * (b - 1) / 2 + 1 : ℕ) : ℤ) := by
  let A : ℕ := alpha.natAbs
  let G : ℕ := gamma.natAbs
  let K : ℕ := A + G + N + M + 10
  let T : ℕ := M * K
  let b : ℕ := 2 * T
  refine ⟨b, ?_, ?_, ?_⟩
  · have hK : N ≤ K := by omega
    have hT : K ≤ T := by
      simpa [T] using Nat.mul_le_mul_right K hM
    omega
  · have hdiv : M ∣ b := by
      refine ⟨2 * K, ?_⟩
      simp [b, T]
      ring
    exact Nat.mod_eq_zero_of_dvd hdiv
  · have h_alpha : alpha ≤ (A : ℤ) := by
      simpa [A] using (Int.le_natAbs (a := alpha))
    have h_gamma : gamma ≤ (G : ℤ) := by
      simpa [G] using (Int.le_natAbs (a := gamma))
    have hb_nonneg : 0 ≤ (b : ℤ) := by exact_mod_cast Nat.zero_le b
    have h_alpha_mul : alpha * (b : ℤ) ≤ (A : ℤ) * (b : ℤ) := by
      exact mul_le_mul_of_nonneg_right h_alpha hb_nonneg
    have h_lhs_le :
        alpha * (b : ℤ) + gamma ≤ (A : ℤ) * (b : ℤ) + (G : ℤ) := by
      linarith
    have hTpos : 0 < T := by
      have hMpos : 0 < M := by omega
      have hKpos : 0 < K := by positivity
      exact Nat.mul_pos hMpos hKpos
    have hb_form : b = 2 * T := by rfl
    have hquad_nat :
        b * (b - 1) / 2 + 1 = T * (2 * T - 1) + 1 := by
      subst b
      have hpos2 : 0 < 2 := by norm_num
      have hrewrite :
          (2 * T) * (2 * T - 1) = 2 * (T * (2 * T - 1)) := by
        ring
      rw [hrewrite]
      exact congr_arg (fun x => x + 1)
        (Nat.mul_div_right (T * (2 * T - 1)) hpos2)
    have h_nat : A * b + G < b * (b - 1) / 2 + 1 := by
      rw [hquad_nat, hb_form]
      have hKbig : A + G + 2 ≤ T := by
        have hKleT : K ≤ T := by
          simpa [T] using Nat.mul_le_mul_right K hM
        omega
      have hKbigZ : (A : ℤ) + (G : ℤ) + 2 ≤ (T : ℤ) := by
        exact_mod_cast hKbig
      have hTposZ : (0 : ℤ) < (T : ℤ) := by exact_mod_cast hTpos
      have hZ : (A : ℤ) * ((2 * T : ℕ) : ℤ) + (G : ℤ) <
          (T : ℤ) * (((2 * T - 1 : ℕ) : ℤ)) + 1 := by
        have hsubZ : (((2 * T - 1 : ℕ) : ℤ)) = 2 * (T : ℤ) - 1 := by
          omega
        rw [hsubZ]
        nlinarith
      exact_mod_cast hZ
    have h_int :
        (A : ℤ) * (b : ℤ) + (G : ℤ) <
          ((b * (b - 1) / 2 + 1 : ℕ) : ℤ) := by
      exact_mod_cast h_nat
    exact lt_of_le_of_lt h_lhs_le h_int

/-- **`lem:triangular-not-semilinear` (paper.tex).**
The triangular set `S_tri` is not semilinear.
Its lower envelope `m(b) = b*(b-1)/2 + 1` is quadratic in `b`,
which contradicts eventual affinity. -/
theorem S_tri_not_semilinear : ¬ IsSemilinear2 S_tri := by
  intro htri
  rcases semilinear_envelope S_tri htri S_tri_vertical_section_finite with
    ⟨M, hM, henv⟩
  rcases henv 0 (by omega) with ⟨p, q, gamma, hq, hevent⟩
  rw [Filter.eventually_atTop] at hevent
  rcases hevent with ⟨N, hN⟩
  rcases exists_multiple_quadratic_gt_affine M hM p gamma (Nat.max N 1) with
    ⟨b, hbNmax, hbmod, hbquad⟩
  have hbN : N ≤ b := le_trans (Nat.le_max_left N 1) hbNmax
  have hb1 : b ≥ 1 := le_trans (Nat.le_max_right N 1) hbNmax
  have hnonempty : {a | (a, b) ∈ S_tri}.Nonempty :=
    S_tri_vertical_section_nonempty b hb1
  rcases hN b hbN hbmod hnonempty with ⟨a, ha_mem, ha_affine⟩
  have hlower_nat := S_tri_lower_bound ha_mem
  have hlower_int : ((b * (b - 1) / 2 + 1 : ℕ) : ℤ) ≤ (a : ℤ) := by
    exact_mod_cast hlower_nat
  -- ha_affine : q·a = p·b + γ ; hbquad : p·b+γ < quad ; hlower_int : quad ≤ a ; hq : 0 < q
  have hq_quad : q * ((b * (b - 1) / 2 + 1 : ℕ) : ℤ) ≤ q * (a : ℤ) :=
    mul_le_mul_of_nonneg_left hlower_int hq.le
  have hquad_pos : (0 : ℤ) ≤ ((b * (b - 1) / 2 + 1 : ℕ) : ℤ) := by positivity
  nlinarith [ha_affine, hbquad, hq_quad,
    mul_nonneg (show (0 : ℤ) ≤ q - 1 from by omega) hquad_pos]

/-! ## The revision's dichotomy form of `lem:semilinear-envelope`
(paper.tex)

paper.tex strengthens `lem:semilinear-envelope` to a per-residue-
class **dichotomy**: for a period `M` determined by `S`, on every residue
class modulo `M` either the sections `S_b` are empty for all sufficiently
large `b` in the class, or they are nonempty for all sufficiently large `b`
in the class (and the envelope is eventually affine).

`semilinear_envelope_dichotomy` below proves the dichotomy, with the affine
clause in the same weakened "some section element on a fixed rational line"
form as `semilinear_envelope` (see that lemma's docstring and
`PAPER_DEVIATIONS.md` § A5 for why the rational form is forced; the genuine
eventually-affine *minimum* remains a documented deviation).

The dichotomy needs no lattice-point counting: choose `M` divisible by every
nonzero second coordinate of every step vector.  If a class contains section
elements at arbitrarily large `b`, one of the finitely many components
witnesses infinitely many of them, hence has a step with nonzero second
coordinate (else it meets only the single height `base 1`), and adding that
step `M / s₀ 1` times shifts any witness up by exactly `M` — so nonemptiness
propagates up the whole class. -/

section EnvelopeDichotomy

/-- On a component all of whose steps have zero second coordinate, every
member has second coordinate `base 1`. -/
private theorem linearSet_all_zero_snd {β : Fin 2 → ℕ} {st : Finset (Fin 2 → ℕ)}
    {v : Fin 2 → ℕ} (hv : v ∈ LinearSet 2 β st) (hz : ∀ s ∈ st, s 1 = 0) :
    v 1 = β 1 := by
  obtain ⟨coeffs, hveq⟩ := hv
  have hzero : st.sum (fun s => coeffs s * s 1) = 0 :=
    Finset.sum_eq_zero (fun s hs => by rw [hz s hs, Nat.mul_zero])
  rw [hveq]
  show β 1 + st.sum (fun s => coeffs s * s 1) = β 1
  rw [hzero, Nat.add_zero]

/-- Shifting a member of a linear set up by any multiple of an available
nonzero step's second coordinate: add `N / s₀ 1` copies of `s₀`. -/
private theorem linearSet_shift {β : Fin 2 → ℕ} {st : Finset (Fin 2 → ℕ)}
    {v : Fin 2 → ℕ} (hv : v ∈ LinearSet 2 β st) {s₀ : Fin 2 → ℕ} (hs₀ : s₀ ∈ st)
    {N : ℕ} (hdvd : s₀ 1 ∣ N) :
    ∃ v' ∈ LinearSet 2 β st, v' 1 = v 1 + N := by
  classical
  obtain ⟨coeffs, hveq⟩ := hv
  by_cases hz : s₀ 1 = 0
  · obtain rfl : N = 0 := zero_dvd_iff.mp (hz ▸ hdvd)
    exact ⟨v, ⟨coeffs, hveq⟩, by omega⟩
  refine ⟨fun i => β i +
      st.sum (fun s => Function.update coeffs s₀ (coeffs s₀ + N / s₀ 1) s * s i),
    ⟨_, rfl⟩, ?_⟩
  show β 1 + st.sum (fun s => Function.update coeffs s₀ (coeffs s₀ + N / s₀ 1) s * s 1)
      = v 1 + N
  have hsum : st.sum (fun s => Function.update coeffs s₀ (coeffs s₀ + N / s₀ 1) s * s 1)
      = st.sum (fun s => coeffs s * s 1) + (N / s₀ 1) * s₀ 1 := by
    rw [← Finset.insert_erase hs₀,
      Finset.sum_insert (Finset.notMem_erase s₀ st),
      Finset.sum_insert (Finset.notMem_erase s₀ st),
      Function.update_self]
    have herase : (st.erase s₀).sum
        (fun s => Function.update coeffs s₀ (coeffs s₀ + N / s₀ 1) s * s 1)
        = (st.erase s₀).sum (fun s => coeffs s * s 1) :=
      Finset.sum_congr rfl (fun s hs => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)])
    rw [herase]
    ring
  rw [hsum, Nat.div_mul_cancel hdvd]
  have hv1 : v 1 = β 1 + st.sum (fun s => coeffs s * s 1) := by
    rw [hveq]
  omega

/-- **The revision's `lem:semilinear-envelope` dichotomy
(paper.tex).**  For semilinear `S ⊆ ℕ²` with finite
sections there is a period `M ≥ 1` such that on every residue class modulo
`M`, exactly one of: (i) the sections are eventually empty along the class;
(ii) they are eventually nonempty along the class, and some section element
eventually lies on a fixed rational line (the weakened affine clause of
`semilinear_envelope`). -/
theorem semilinear_envelope_dichotomy (S : Set (ℕ × ℕ)) (hS : IsSemilinear2 S)
    (hfinite : ∀ b : ℕ, Set.Finite {a | (a, b) ∈ S}) :
    ∃ M : ℕ, M ≥ 1 ∧ ∀ r : ℕ, r < M →
      (∀ᶠ b in Filter.atTop, b % M = r → {a | (a, b) ∈ S} = ∅) ∨
      ((∀ᶠ b in Filter.atTop, b % M = r → {a | (a, b) ∈ S}.Nonempty) ∧
        ∃ p q gamma : ℤ, 0 < q ∧ ∀ᶠ b in Filter.atTop, b % M = r →
          ∃ a ∈ {a | (a, b) ∈ S}, q * (a : ℤ) = p * (b : ℤ) + gamma) := by
  classical
  obtain ⟨M₁, hM₁, hEnv⟩ := semilinear_envelope S hS hfinite
  obtain ⟨comps, hcomp, hunion⟩ := hS
  choose baseF stepsF hbsF using hcomp
  set baseOf : Set (Fin 2 → ℕ) → (Fin 2 → ℕ) :=
    fun C => if h : C ∈ comps then baseF C h else 0 with hbaseOf
  set stepsOf : Set (Fin 2 → ℕ) → Finset (Fin 2 → ℕ) :=
    fun C => if h : C ∈ comps then stepsF C h else ∅ with hstepsOf
  have hC_eq : ∀ C ∈ comps, C = LinearSet 2 (baseOf C) (stepsOf C) := by
    intro C hC
    rw [hbaseOf, hstepsOf]
    simp only [dif_pos hC]
    exact hbsF C hC
  set M₂ : ℕ :=
    comps.prod (fun C => (stepsOf C).prod (fun s => if s 1 = 0 then 1 else s 1))
    with hM₂
  have hM₂pos : 0 < M₂ := by
    rw [hM₂]
    refine Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun C _ => ?_)
    refine Finset.prod_ne_zero_iff.mpr fun s _ => ?_
    by_cases h : s 1 = 0
    · rw [if_pos h]; omega
    · rw [if_neg h]; exact h
  have hdvdM₂ : ∀ C ∈ comps, ∀ s ∈ stepsOf C, s 1 ≠ 0 → s 1 ∣ M₂ := by
    intro C hC s hs hne
    have h1 : (if s 1 = 0 then 1 else s 1)
        ∣ (stepsOf C).prod (fun s => if s 1 = 0 then 1 else s 1) :=
      Finset.dvd_prod_of_mem _ hs
    rw [if_neg hne] at h1
    exact h1.trans (Finset.dvd_prod_of_mem _ hC)
  set M : ℕ := M₁ * M₂ with hMdef
  have hMpos : 1 ≤ M := by
    have := Nat.mul_pos (show 0 < M₁ by omega) hM₂pos
    omega
  refine ⟨M, hMpos, fun r hr => ?_⟩
  have hmemS : ∀ a b : ℕ, (a, b) ∈ S ↔ ∃ C ∈ comps, (![a, b] : Fin 2 → ℕ) ∈ C := by
    intro a b
    have hv : (![a, b] : Fin 2 → ℕ) ∈ {v : Fin 2 → ℕ | (v 0, v 1) ∈ S}
        ↔ (a, b) ∈ S := by
      simp
    rw [← hv, hunion]
    simp
  by_cases hbdd : ∃ N, ∀ b, N ≤ b → b % M = r → {a | (a, b) ∈ S} = ∅
  · obtain ⟨N, hN⟩ := hbdd
    exact Or.inl (Filter.eventually_atTop.mpr ⟨N, hN⟩)
  · push Not at hbdd
    -- a hit beyond every pure-base height
    obtain ⟨b₀, hb₀ge, hb₀r, hb₀ne⟩ := hbdd (comps.sup (fun C => baseOf C 1) + 1)
    obtain ⟨a₀, ha₀⟩ := hb₀ne
    obtain ⟨C, hC, hvC⟩ := (hmemS a₀ b₀).mp ha₀
    have hvC' : (![a₀, b₀] : Fin 2 → ℕ) ∈ LinearSet 2 (baseOf C) (stepsOf C) :=
      hC_eq C hC ▸ hvC
    -- the component has a step with nonzero second coordinate
    obtain ⟨s₀, hs₀, hs₀ne⟩ : ∃ s ∈ stepsOf C, s 1 ≠ 0 := by
      by_contra hall
      push Not at hall
      have hb₀eq : (![a₀, b₀] : Fin 2 → ℕ) 1 = baseOf C 1 :=
        linearSet_all_zero_snd hvC' hall
      have hb₀eq' : b₀ = baseOf C 1 := by simpa using hb₀eq
      have hle : baseOf C 1 ≤ comps.sup (fun C => baseOf C 1) :=
        Finset.le_sup (f := fun C => baseOf C 1) hC
      omega
    -- forward closure: every later `b` in the class has a nonempty section
    have hclosed : ∀ b, b₀ ≤ b → b % M = r → {a | (a, b) ∈ S}.Nonempty := by
      intro b hge hbr
      have hmod : b₀ ≡ b [MOD M] := by
        show b₀ % M = b % M
        rw [hbr, hb₀r]
      obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hge).mp hmod
      have hs₀dvd : s₀ 1 ∣ b - b₀ := hk ▸ ((hdvdM₂ C hC s₀ hs₀ hs₀ne).mul_left M₁).mul_right k
      obtain ⟨v', hv'C, hv'1⟩ := linearSet_shift hvC' hs₀ hs₀dvd
      have hv'S : (v' 0, v' 1) ∈ S := by
        have hv'mem : v' ∈ {v : Fin 2 → ℕ | (v 0, v 1) ∈ S} := by
          rw [hunion]
          exact Set.mem_biUnion hC (hC_eq C hC ▸ hv'C)
        exact hv'mem
      refine ⟨v' 0, ?_⟩
      have hb1 : v' 1 = b := by
        rw [hv'1]
        have : (![a₀, b₀] : Fin 2 → ℕ) 1 = b₀ := by simp
        omega
      show (v' 0, b) ∈ S
      rw [← hb1]
      exact hv'S
    have hNE : ∀ᶠ b in Filter.atTop, b % M = r → {a | (a, b) ∈ S}.Nonempty :=
      Filter.eventually_atTop.mpr ⟨b₀, hclosed⟩
    obtain ⟨p, q, gamma, hq, hAff⟩ := hEnv (r % M₁) (Nat.mod_lt _ (by omega))
    refine Or.inr ⟨hNE, p, q, gamma, hq, ?_⟩
    have hrefine : ∀ b : ℕ, b % M = r → b % M₁ = r % M₁ := by
      intro b hb
      rw [← hb, hMdef]
      exact (Nat.mod_mod_of_dvd b ⟨M₂, rfl⟩).symm
    filter_upwards [hAff, hNE] with b h1 h2 hb
    exact h1 (hrefine b hb) (h2 hb)

end EnvelopeDichotomy
