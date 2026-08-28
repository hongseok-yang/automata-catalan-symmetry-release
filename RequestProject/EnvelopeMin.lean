/-
# The eventually-affine minimum (`lem:semilinear-envelope`, full form)

The revision's `lem:semilinear-envelope` (paper.tex)
asserts, on each residue class of a period `M` determined by the semilinear
set `S`: either the sections `S_b` are eventually empty along the class, or
they are eventually nonempty and their **minimum** `m(b) = min S_b` is
eventually affine, `m(b) = αb + γ` with constants depending on the class.

`Semilinearity.lean` proves the dichotomy (`semilinear_envelope_dichotomy`)
with a weakened affine clause ("*some* section element on a fixed rational
line").  This file proves the full statement, `semilinear_envelope_min`: the
minimum itself is eventually affine (integer-cleared rational form
`M·min S_b = p·b + γ`, cf. `PAPER_DEVIATIONS.md` § A5 for why the slope must
be rational).

The proof is elementary lattice-point reasoning, no Ehrhart theory:

* **Component value function.**  For one linear set with base `β` and steps
  `st`, the fibre over `b` is `fibSet β st b`, with minimum `sInf`.  Among
  the steps with positive second coordinate pick `s*` of minimal ratio
  `s 0 / s 1` (`exists_ratio_min`).  With `M` divisible by every positive
  second coordinate, adding `M / s* 1` copies of `s*` shifts any fibre
  element up by `M` at cost `Δ = (M / s* 1) · s* 0` (`fib_shift_up`); and
  beyond an explicit threshold, any element of the `b + M` fibre uses some
  step `≥ M` times (pigeonhole), so removing `M / s 1` copies of it lands in
  the `b` fibre at cost `≥ Δ` less (`fib_shift_down`, using the minimality
  of `s*`'s ratio).  Hence `min(b + M) = min(b) + Δ` beyond the threshold
  (`sInf_fib_step`), and by iteration the minimum is affine along each
  residue class where the component keeps a nonempty fibre
  (`component_class_dichotomy`).
* **Assembly.**  The section `S_b` is the finite union of component fibres.
  On a residue class, split the components into the eventually-empty ones and
  the eventually-affine ones; among the latter pick the lexicographically
  least line `(p, γ)` — eventually it is below every other component line, so
  the union's minimum is that component's minimum, hence affine.

Everything is axiom-clean (kernel axioms only).
-/
import RequestProject.Semilinearity

open Filter

namespace EnvelopeMin

/-! ## Fibres of a linear set -/

/-- The `b`-fibre of the linear set with base `β` and steps `st`, described by
achieving coefficients. -/
def fibSet (β : Fin 2 → ℕ) (st : Finset (Fin 2 → ℕ)) (b : ℕ) : Set ℕ :=
  {a | ∃ c : (Fin 2 → ℕ) → ℕ,
    a = β 0 + st.sum (fun s => c s * s 0) ∧
    b = β 1 + st.sum (fun s => c s * s 1)}

theorem mem_linearSet_iff_fib (β : Fin 2 → ℕ) (st : Finset (Fin 2 → ℕ))
    (a b : ℕ) :
    (![a, b] : Fin 2 → ℕ) ∈ LinearSet 2 β st ↔ a ∈ fibSet β st b := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, ?_⟩
    · have h := congrFun hc 0
      simpa using h
    · have h := congrFun hc 1
      simpa using h
  · rintro ⟨c, h0, h1⟩
    refine ⟨c, funext fun i => ?_⟩
    fin_cases i
    · simpa using h0
    · simpa using h1

/-! ## Coefficient-update sums -/

private theorem sum_update_add (st : Finset (Fin 2 → ℕ)) {s₀ : Fin 2 → ℕ}
    (hs₀ : s₀ ∈ st) (c : (Fin 2 → ℕ) → ℕ) (k : ℕ) (i : Fin 2) :
    st.sum (fun s => Function.update c s₀ (c s₀ + k) s * s i)
      = st.sum (fun s => c s * s i) + k * s₀ i := by
  classical
  rw [← Finset.insert_erase hs₀,
    Finset.sum_insert (Finset.notMem_erase s₀ st),
    Finset.sum_insert (Finset.notMem_erase s₀ st),
    Function.update_self]
  have herase : (st.erase s₀).sum (fun s => Function.update c s₀ (c s₀ + k) s * s i)
      = (st.erase s₀).sum (fun s => c s * s i) :=
    Finset.sum_congr rfl (fun s hs => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)])
  rw [herase]
  ring

private theorem sum_update_sub (st : Finset (Fin 2 → ℕ)) {s₀ : Fin 2 → ℕ}
    (hs₀ : s₀ ∈ st) (c : (Fin 2 → ℕ) → ℕ) (k : ℕ) (hk : k ≤ c s₀) (i : Fin 2) :
    st.sum (fun s => Function.update c s₀ (c s₀ - k) s * s i) + k * s₀ i
      = st.sum (fun s => c s * s i) := by
  classical
  rw [← Finset.insert_erase hs₀,
    Finset.sum_insert (Finset.notMem_erase s₀ st),
    Finset.sum_insert (Finset.notMem_erase s₀ st),
    Function.update_self]
  have herase : (st.erase s₀).sum (fun s => Function.update c s₀ (c s₀ - k) s * s i)
      = (st.erase s₀).sum (fun s => c s * s i) :=
    Finset.sum_congr rfl (fun s hs => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)])
  rw [herase]
  have hmul : (c s₀ - k) * s₀ i + k * s₀ i = c s₀ * s₀ i := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hk]
  omega

/-! ## The minimal-ratio step -/

/-- Among the steps with positive second coordinate there is one of minimal
ratio `s 0 / s 1` (stated cross-multiplied). -/
theorem exists_ratio_min (st : Finset (Fin 2 → ℕ))
    (hpos : ∃ s ∈ st, 0 < s 1) :
    ∃ sm ∈ st, 0 < sm 1 ∧ ∀ s ∈ st, 0 < s 1 → sm 0 * s 1 ≤ s 0 * sm 1 := by
  classical
  obtain ⟨s₀, hs₀, hs₀pos⟩ := hpos
  have hne : (st.filter (fun s => 0 < s 1)).Nonempty :=
    ⟨s₀, Finset.mem_filter.mpr ⟨hs₀, hs₀pos⟩⟩
  obtain ⟨sm, hsm, hmin⟩ := (st.filter (fun s => 0 < s 1)).exists_min_image
    (fun s => (s 0 : ℚ) / (s 1 : ℚ)) hne
  obtain ⟨hsmst, hsmpos⟩ := Finset.mem_filter.mp hsm
  refine ⟨sm, hsmst, hsmpos, fun s hs hspos => ?_⟩
  have h := hmin s (Finset.mem_filter.mpr ⟨hs, hspos⟩)
  rw [div_le_div_iff₀ (by exact_mod_cast hsmpos) (by exact_mod_cast hspos)] at h
  exact_mod_cast h

/-! ## Component periodicity -/

/-- The affine increment of a component: the cost of shifting `b` up by `M`
along the minimal-ratio step. -/
def Δc (M : ℕ) (sm : Fin 2 → ℕ) : ℕ := (M / sm 1) * sm 0

/-- The threshold beyond which the pigeonhole removal works. -/
def thr (β : Fin 2 → ℕ) (st : Finset (Fin 2 → ℕ)) (M : ℕ) : ℕ :=
  β 1 + M * st.sum (fun s => s 1) + M

/-- Shifting a fibre element up by `M` along the minimal-ratio step. -/
theorem fib_shift_up {β : Fin 2 → ℕ} {st : Finset (Fin 2 → ℕ)} {M : ℕ}
    {sm : Fin 2 → ℕ} (hsm : sm ∈ st) (hdvdsm : sm 1 ∣ M)
    {b a : ℕ} (ha : a ∈ fibSet β st b) :
    a + Δc M sm ∈ fibSet β st (b + M) := by
  classical
  obtain ⟨c, h0, h1⟩ := ha
  refine ⟨Function.update c sm (c sm + M / sm 1), ?_, ?_⟩
  · rw [sum_update_add st hsm c (M / sm 1) 0, Δc]
    omega
  · rw [sum_update_add st hsm c (M / sm 1) 1, Nat.div_mul_cancel hdvdsm]
    omega

/-- Beyond the threshold, any element of the `b + M` fibre can be shifted down
by `M`, saving at least `Δ` (pigeonhole + minimality of `s*`'s ratio). -/
theorem fib_shift_down {β : Fin 2 → ℕ} {st : Finset (Fin 2 → ℕ)} {M : ℕ}
    {sm : Fin 2 → ℕ} (hMpos : 0 < M)
    (hdvd : ∀ s ∈ st, 0 < s 1 → s 1 ∣ M) (hdvdsm : sm 1 ∣ M)
    (hsmpos : 0 < sm 1)
    (hratio : ∀ s ∈ st, 0 < s 1 → sm 0 * s 1 ≤ s 0 * sm 1)
    {b a' : ℕ} (hb : thr β st M ≤ b) (ha' : a' ∈ fibSet β st (b + M)) :
    ∃ a ∈ fibSet β st b, a + Δc M sm ≤ a' := by
  classical
  obtain ⟨c, h0, h1⟩ := ha'
  simp only [thr] at hb
  -- pigeonhole: some positive-second-coordinate step is used at least M times
  have hpig : ∃ s ∈ st, 0 < s 1 ∧ M ≤ c s := by
    by_contra hall
    push Not at hall
    have hbound : st.sum (fun s => c s * s 1) ≤ M * st.sum (fun s => s 1) := by
      calc st.sum (fun s => c s * s 1) ≤ st.sum (fun s => M * s 1) := by
            refine Finset.sum_le_sum (fun s hs => ?_)
            rcases Nat.eq_zero_or_pos (s 1) with h1' | h1'
            · rw [h1']
              simp
            · exact Nat.mul_le_mul_right _ (le_of_lt (hall s hs h1'))
        _ = M * st.sum (fun s => s 1) := by rw [Finset.mul_sum]
    omega
  obtain ⟨sj, hsj, hsjpos, hsjc⟩ := hpig
  have hkle : M / sj 1 ≤ c sj := le_trans (Nat.div_le_self M (sj 1)) hsjc
  have hsub0 := sum_update_sub st hsj c (M / sj 1) hkle 0
  have hsub1 := sum_update_sub st hsj c (M / sj 1) hkle 1
  rw [Nat.div_mul_cancel (hdvd sj hsj hsjpos)] at hsub1
  refine ⟨β 0 + st.sum (fun s => Function.update c sj (c sj - M / sj 1) s * s 0),
    ⟨Function.update c sj (c sj - M / sj 1), rfl, by omega⟩, ?_⟩
  -- the saving dominates Δ by the minimality of `s*`'s ratio
  have hΔ : Δc M sm ≤ M / sj 1 * sj 0 := by
    have hpos : 0 < sm 1 * sj 1 := Nat.mul_pos hsmpos hsjpos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    have e1 : Δc M sm * (sm 1 * sj 1) = M * (sm 0 * sj 1) := by
      rw [Δc]
      calc M / sm 1 * sm 0 * (sm 1 * sj 1)
          = (M / sm 1 * sm 1) * (sm 0 * sj 1) := by ring
        _ = M * (sm 0 * sj 1) := by rw [Nat.div_mul_cancel hdvdsm]
    have e2 : (M / sj 1 * sj 0) * (sm 1 * sj 1) = M * (sj 0 * sm 1) := by
      calc (M / sj 1 * sj 0) * (sm 1 * sj 1)
          = (M / sj 1 * sj 1) * (sj 0 * sm 1) := by ring
        _ = M * (sj 0 * sm 1) := by rw [Nat.div_mul_cancel (hdvd sj hsj hsjpos)]
    rw [e1, e2]
    exact Nat.mul_le_mul_left M (hratio sj hsj hsjpos)
  omega

/-- **The periodic recurrence of the component minimum**: beyond the
threshold, `min(b + M) = min(b) + Δ`. -/
theorem sInf_fib_step {β : Fin 2 → ℕ} {st : Finset (Fin 2 → ℕ)} {M : ℕ}
    {sm : Fin 2 → ℕ} (hMpos : 0 < M) (hsm : sm ∈ st)
    (hdvd : ∀ s ∈ st, 0 < s 1 → s 1 ∣ M) (hsmpos : 0 < sm 1)
    (hratio : ∀ s ∈ st, 0 < s 1 → sm 0 * s 1 ≤ s 0 * sm 1)
    {b : ℕ} (hb : thr β st M ≤ b) (hne : (fibSet β st b).Nonempty) :
    (fibSet β st (b + M)).Nonempty ∧
      sInf (fibSet β st (b + M)) = sInf (fibSet β st b) + Δc M sm := by
  have hdvdsm : sm 1 ∣ M := hdvd sm hsm hsmpos
  have hmem := Nat.sInf_mem hne
  have hup := fib_shift_up hsm hdvdsm hmem
  have hne' : (fibSet β st (b + M)).Nonempty := ⟨_, hup⟩
  refine ⟨hne', le_antisymm (Nat.sInf_le hup) ?_⟩
  have hmem' := Nat.sInf_mem hne'
  obtain ⟨a, hafib, haΔ⟩ :=
    fib_shift_down hMpos hdvd hdvdsm hsmpos hratio hb hmem'
  have hle := Nat.sInf_le hafib
  omega

/-- Iterating the recurrence: the minimum is affine along `b, b+M, b+2M, …`. -/
theorem sInf_fib_iterate {β : Fin 2 → ℕ} {st : Finset (Fin 2 → ℕ)} {M : ℕ}
    {sm : Fin 2 → ℕ} (hMpos : 0 < M) (hsm : sm ∈ st)
    (hdvd : ∀ s ∈ st, 0 < s 1 → s 1 ∣ M) (hsmpos : 0 < sm 1)
    (hratio : ∀ s ∈ st, 0 < s 1 → sm 0 * s 1 ≤ s 0 * sm 1)
    {b : ℕ} (hb : thr β st M ≤ b) (hne : (fibSet β st b).Nonempty) :
    ∀ k, (fibSet β st (b + k * M)).Nonempty ∧
      sInf (fibSet β st (b + k * M)) = sInf (fibSet β st b) + k * Δc M sm := by
  intro k
  induction k with
  | zero => simpa using hne
  | succ k ih =>
      obtain ⟨ihne, iheq⟩ := ih
      have hb' : thr β st M ≤ b + k * M := by omega
      obtain ⟨hne', heq'⟩ := sInf_fib_step hMpos hsm hdvd hsmpos hratio hb' ihne
      constructor
      · rw [show b + (k + 1) * M = (b + k * M) + M by ring]
        exact hne'
      · rw [show b + (k + 1) * M = (b + k * M) + M by ring, heq', iheq]
        ring

/-! ## The per-class component dichotomy with an affine minimum -/

/-- On each residue class modulo `M`, a component's fibres are eventually
empty, or eventually nonempty with an eventually-affine minimum
(integer-cleared: `M · min = p·b + γ`). -/
theorem component_class_dichotomy (β : Fin 2 → ℕ) (st : Finset (Fin 2 → ℕ))
    (M : ℕ) (hMpos : 0 < M) (hdvd : ∀ s ∈ st, 0 < s 1 → s 1 ∣ M) (r : ℕ) :
    (∀ᶠ b in atTop, b % M = r → fibSet β st b = ∅) ∨
    (∃ p γ : ℤ, ∀ᶠ b in atTop, b % M = r →
      ((fibSet β st b).Nonempty ∧
        (M : ℤ) * ((sInf (fibSet β st b) : ℕ) : ℤ) = p * (b : ℤ) + γ)) := by
  classical
  by_cases hbdd : ∃ N, ∀ b, N ≤ b → b % M = r → fibSet β st b = ∅
  · left
    obtain ⟨N, hN⟩ := hbdd
    exact eventually_atTop.mpr ⟨N, hN⟩
  · right
    push Not at hbdd
    -- unbounded hits force a step with positive second coordinate
    have hpos : ∃ s ∈ st, 0 < s 1 := by
      by_contra hnop
      push Not at hnop
      obtain ⟨b, hbge, hbr, hbne⟩ := hbdd (β 1 + 1)
      obtain ⟨a, c, -, h1⟩ := hbne
      have hzero : st.sum (fun s => c s * s 1) = 0 :=
        Finset.sum_eq_zero (fun s hs => by
          have h0 : s 1 = 0 := by
            have := hnop s hs
            omega
          rw [h0, Nat.mul_zero])
      omega
    obtain ⟨sm, hsm, hsmpos, hratio⟩ := exists_ratio_min st hpos
    -- a hit beyond the threshold, in the class
    obtain ⟨b₀, hb₀ge, hb₀r, hb₀ne⟩ := hbdd (thr β st M)
    refine ⟨(Δc M sm : ℤ),
      (M : ℤ) * ((sInf (fibSet β st b₀) : ℕ) : ℤ) - (Δc M sm : ℤ) * (b₀ : ℤ), ?_⟩
    rw [eventually_atTop]
    refine ⟨b₀, fun b hbge hbr => ?_⟩
    have hmod : b₀ ≡ b [MOD M] := by
      show b₀ % M = b % M
      rw [hbr, hb₀r]
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hbge).mp hmod
    rw [Nat.mul_comm M k] at hk
    obtain rfl : b = b₀ + k * M := by omega
    obtain ⟨hne', heq'⟩ :=
      sInf_fib_iterate hMpos hsm hdvd hsmpos hratio hb₀ge hb₀ne k
    refine ⟨hne', ?_⟩
    rw [heq']
    push_cast
    ring

/-! ## Assembly: the union of components -/

/-- **`lem:semilinear-envelope`, full form (paper.tex).**
For semilinear `S ⊆ ℕ²` (with finite sections, as in the paper; the proof
does not need this) there is a period `M ≥ 1` such that on every residue
class modulo `M`: either the sections are eventually empty along the class,
or they are eventually nonempty and the **minimum** `min S_b = sInf S_b` is
eventually affine, in the integer-cleared rational form
`q · min S_b = p · b + γ` with `q = M > 0`. -/
theorem semilinear_envelope_min (S : Set (ℕ × ℕ)) (hS : IsSemilinear2 S)
    (_hfinite : ∀ b : ℕ, Set.Finite {a | (a, b) ∈ S}) :
    ∃ M : ℕ, M ≥ 1 ∧ ∀ r : ℕ, r < M →
      (∀ᶠ b in atTop, b % M = r → {a | (a, b) ∈ S} = ∅) ∨
      ((∀ᶠ b in atTop, b % M = r → {a | (a, b) ∈ S}.Nonempty) ∧
        ∃ p q γ : ℤ, 0 < q ∧ ∀ᶠ b in atTop, b % M = r →
          q * ((sInf {a | (a, b) ∈ S} : ℕ) : ℤ) = p * (b : ℤ) + γ) := by
  classical
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
  set M : ℕ :=
    comps.prod (fun C => (stepsOf C).prod (fun s => if s 1 = 0 then 1 else s 1))
    with hM
  have hMpos : 0 < M := by
    rw [hM]
    refine Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun C _ => ?_)
    refine Finset.prod_ne_zero_iff.mpr fun s _ => ?_
    by_cases h : s 1 = 0
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      exact h
  have hdvdM : ∀ C ∈ comps, ∀ s ∈ stepsOf C, 0 < s 1 → s 1 ∣ M := by
    intro C hC s hs hpos
    have h1 : (if s 1 = 0 then 1 else s 1)
        ∣ (stepsOf C).prod (fun s => if s 1 = 0 then 1 else s 1) :=
      Finset.dvd_prod_of_mem _ hs
    rw [if_neg (by omega)] at h1
    exact h1.trans (Finset.dvd_prod_of_mem _ hC)
  -- the section of `S` is the union of the component fibres
  have hSfib : ∀ b : ℕ, {a | (a, b) ∈ S}
      = ⋃ C ∈ comps, fibSet (baseOf C) (stepsOf C) b := by
    intro b
    ext a
    constructor
    · intro ha
      have hv : (![a, b] : Fin 2 → ℕ) ∈ {v : Fin 2 → ℕ | (v 0, v 1) ∈ S} := by
        simpa using ha
      rw [hunion] at hv
      have : ∃ C, C ∈ comps ∧ (![a, b] : Fin 2 → ℕ) ∈ C := by
        simpa using hv
      obtain ⟨C, hC, hvC⟩ := this
      refine Set.mem_biUnion hC ?_
      rw [← mem_linearSet_iff_fib, ← hC_eq C hC]
      exact hvC
    · intro ha
      have : ∃ C, C ∈ comps ∧ a ∈ fibSet (baseOf C) (stepsOf C) b := by
        simpa using ha
      obtain ⟨C, hC, haC⟩ := this
      have hvC : (![a, b] : Fin 2 → ℕ) ∈ C := by
        rw [hC_eq C hC, mem_linearSet_iff_fib]
        exact haC
      have hv : (![a, b] : Fin 2 → ℕ) ∈ {v : Fin 2 → ℕ | (v 0, v 1) ∈ S} := by
        rw [hunion]
        exact Set.mem_biUnion hC hvC
      simpa using hv
  refine ⟨M, hMpos, fun r hr => ?_⟩
  -- the eventually-empty and eventually-affine components
  set NE : Finset (Set (Fin 2 → ℕ)) :=
    comps.filter (fun C =>
      ¬ (∀ᶠ b in atTop, b % M = r → fibSet (baseOf C) (stepsOf C) b = ∅))
    with hNE
  have hE : ∀ C ∈ comps, C ∉ NE →
      (∀ᶠ b in atTop, b % M = r → fibSet (baseOf C) (stepsOf C) b = ∅) := by
    intro C hC hCnot
    by_contra hne
    exact hCnot (Finset.mem_filter.mpr ⟨hC, hne⟩)
  have hNEaff : ∀ C ∈ NE, ∃ p γ : ℤ, ∀ᶠ b in atTop, b % M = r →
      ((fibSet (baseOf C) (stepsOf C) b).Nonempty ∧
        (M : ℤ) * ((sInf (fibSet (baseOf C) (stepsOf C) b) : ℕ) : ℤ)
          = p * (b : ℤ) + γ) := by
    intro C hCNE
    obtain ⟨hC, hCne⟩ := Finset.mem_filter.mp hCNE
    rcases component_class_dichotomy (baseOf C) (stepsOf C) M hMpos
      (hdvdM C hC) r with h | h
    · exact absurd h hCne
    · exact h
  rcases NE.eq_empty_or_nonempty with hNEe | hNEne
  · -- every component is eventually empty on the class
    left
    have hall : ∀ᶠ b in atTop, ∀ C ∈ comps,
        b % M = r → fibSet (baseOf C) (stepsOf C) b = ∅ := by
      rw [eventually_all_finset]
      intro C hC
      have := hE C hC (by rw [hNEe]; exact Finset.notMem_empty C)
      filter_upwards [this] with b hb hbr
      exact hb hbr
    filter_upwards [hall] with b hb hbr
    rw [hSfib b]
    ext a
    simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
    rintro ⟨C, hC, haC⟩
    rw [hb C hC hbr] at haC
    exact haC
  · -- pick the lexicographically least component line
    right
    choose pF γF hF using hNEaff
    set pB : Set (Fin 2 → ℕ) → ℤ := fun C => if h : C ∈ NE then pF C h else 0 with hpB
    set γB : Set (Fin 2 → ℕ) → ℤ := fun C => if h : C ∈ NE then γF C h else 0 with hγB
    have hB : ∀ C ∈ NE, ∀ᶠ b in atTop, b % M = r →
        ((fibSet (baseOf C) (stepsOf C) b).Nonempty ∧
          (M : ℤ) * ((sInf (fibSet (baseOf C) (stepsOf C) b) : ℕ) : ℤ)
            = pB C * (b : ℤ) + γB C) := by
      intro C hC
      have hp : pB C = pF C hC := by rw [hpB]; exact dif_pos hC
      have hγ : γB C = γF C hC := by rw [hγB]; exact dif_pos hC
      rw [hp, hγ]
      exact hF C hC
    obtain ⟨Cm, hCm, hlex⟩ :=
      NE.exists_min_image (fun C => toLex (pB C, γB C)) hNEne
    have hNEall : ∀ᶠ b in atTop, ∀ C ∈ NE, (b % M = r →
        ((fibSet (baseOf C) (stepsOf C) b).Nonempty ∧
          (M : ℤ) * ((sInf (fibSet (baseOf C) (stepsOf C) b) : ℕ) : ℤ)
            = pB C * (b : ℤ) + γB C)) := by
      rw [eventually_all_finset]
      exact hB
    have hEall : ∀ᶠ b in atTop, ∀ C ∈ comps, (C ∉ NE →
        (b % M = r → fibSet (baseOf C) (stepsOf C) b = ∅)) := by
      rw [eventually_all_finset]
      intro C hC
      by_cases hCNE : C ∈ NE
      · exact Eventually.of_forall (fun b h => absurd hCNE h)
      · have h := hE C hC hCNE
        filter_upwards [h] with b hb _hnot hbr
        exact hb hbr
    have hlines : ∀ᶠ (b : ℕ) in atTop, ∀ C ∈ NE,
        pB Cm * (b : ℤ) + γB Cm ≤ pB C * (b : ℤ) + γB C := by
      rw [eventually_all_finset]
      intro C hC
      have h := hlex C hC
      have h' : pB Cm < pB C ∨ (pB Cm = pB C ∧ γB Cm ≤ γB C) := by
        rw [Prod.Lex.le_iff] at h
        exact h
      rcases h' with hslope | ⟨h1, h2⟩
      · by_cases hγ : γB Cm - γB C ≤ 0
        · refine Eventually.of_forall (fun b => ?_)
          have hnn : (0 : ℤ) ≤ (pB C - pB Cm) * (b : ℤ) :=
            mul_nonneg (by omega) (Int.natCast_nonneg b)
          rw [sub_mul] at hnn
          linarith
        · rw [eventually_atTop]
          refine ⟨(γB Cm - γB C).toNat, fun b hb => ?_⟩
          have e1 : ((γB Cm - γB C).toNat : ℤ) = γB Cm - γB C :=
            Int.toNat_of_nonneg (by omega)
          have e2 : ((γB Cm - γB C).toNat : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
          have e3 : γB Cm - γB C ≤ (b : ℤ) := by omega
          have e4 : (b : ℤ) * 1 ≤ (b : ℤ) * (pB C - pB Cm) :=
            mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg b)
          have e5 : (b : ℤ) * (pB C - pB Cm) = pB C * (b : ℤ) - pB Cm * (b : ℤ) := by
            ring
          linarith
      · refine Eventually.of_forall (fun b => ?_)
        rw [h1]
        linarith
    have hCmcomps : Cm ∈ comps := (Finset.mem_filter.mp hCm).1
    refine ⟨?_, pB Cm, (M : ℤ), γB Cm, by exact_mod_cast hMpos, ?_⟩
    · filter_upwards [hNEall] with b hb hbr
      obtain ⟨hne, -⟩ := hb Cm hCm hbr
      obtain ⟨a, ha⟩ := hne
      rw [hSfib b]
      exact ⟨a, Set.mem_biUnion hCmcomps ha⟩
    · filter_upwards [hNEall, hEall, hlines] with b hNEb hEb hlinesb hbr
      obtain ⟨hCmne, hCmline⟩ := hNEb Cm hCm hbr
      have hSne : {a | (a, b) ∈ S}.Nonempty := by
        obtain ⟨a, ha⟩ := hCmne
        rw [hSfib b]
        exact ⟨a, Set.mem_biUnion hCmcomps ha⟩
      have hle : sInf {a | (a, b) ∈ S}
          ≤ sInf (fibSet (baseOf Cm) (stepsOf Cm) b) := by
        refine Nat.sInf_le ?_
        rw [hSfib b]
        exact Set.mem_biUnion hCmcomps (Nat.sInf_mem hCmne)
      have hmem : sInf {a | (a, b) ∈ S}
          ∈ ⋃ C ∈ comps, fibSet (baseOf C) (stepsOf C) b := by
        rw [← hSfib b]
        exact Nat.sInf_mem hSne
      have hmem' : ∃ C, C ∈ comps ∧ sInf {a | (a, b) ∈ S}
          ∈ fibSet (baseOf C) (stepsOf C) b := by
        simpa using hmem
      obtain ⟨C, hC, haC⟩ := hmem'
      have hCNE : C ∈ NE := by
        by_contra hCnot
        rw [hEb C hC hCnot hbr] at haC
        exact haC
      obtain ⟨-, hCline⟩ := hNEb C hCNE hbr
      have hge : sInf (fibSet (baseOf C) (stepsOf C) b)
          ≤ sInf {a | (a, b) ∈ S} := Nat.sInf_le haC
      have hlineC := hlinesb C hCNE
      have hM' : (0 : ℤ) ≤ (M : ℤ) := by positivity
      have h1 : (M : ℤ) * ((sInf {a | (a, b) ∈ S} : ℕ) : ℤ)
          ≤ (M : ℤ) * ((sInf (fibSet (baseOf Cm) (stepsOf Cm) b) : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hM'
      have h2 : (M : ℤ) * ((sInf (fibSet (baseOf C) (stepsOf C) b) : ℕ) : ℤ)
          ≤ (M : ℤ) * ((sInf {a | (a, b) ∈ S} : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hge) hM'
      rw [hCmline] at h1
      rw [hCline] at h2
      linarith

end EnvelopeMin
