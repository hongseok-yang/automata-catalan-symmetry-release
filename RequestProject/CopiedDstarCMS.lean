import RequestProject.CopiedSetupMS
import RequestProject.CopiedDstarC

/-!
# d3.4 bridge — PERIOD UNIFORMITY (the §9 Stage F-mS linchpin)

The mS-direction tie-count route hoists a SINGLE mS-period `pstar_mS` BEFORE the `∀ n` binder, so that
`fun mS => dstarRankGA_m P hV mS n` is `AffineOnResiduesAtZ pstar_mS` uniformly in `n`.  This file
exposes that period — the one place with no n-direction analog (there `dstar_setup_fibred` hands back the
machine product `p·p₂` directly at the binder; here `mS` couples both growing runs through the automaton,
so the period is hidden inside the opaque `∃p` of `gateF_deepShape_EP_mS` / `rank_cell_mixedDeep_vec`).

Two halves, both proved `(t,n)`-free:
* **GATE** (`accepts_two_sided_EP_deepSuf_mp` → `gateF_deepShape_EP_mS_uniform`): a MACHINE-ONLY gate
  period `qC` (the prefix cycle switched to the start-free `endofunction_EP_mul`), the same for every
  `ds,t,n`.
* **RANK** (`prefixRank_run_affine_mS_uniform` … `rank_cell_mixedDeep_vec_uniform`): the per-`(c,ds)`
  rank period, uniform over `(t,n)` — each leaf period is built from `iterate_eventuallyPeriodic` /
  `endofunction_EP_mul` of FIXED automaton maps from FIXED starts, with `t,n` entering only affine
  offsets, so the uniform variants are binder reorderings of the existing proofs.

`coordCands_period_uniform` takes the n-FREE product over the `mixedTuplesF` shape set of
(machine gate period × presentation rank period); `selB_period_uniform` re-derives `selB`'s affineness
directly at that `pstar_mS` via `gated_lexMin_affine_at` with per-candidate `EP_of_dvd` / `of_dvd` lifts
(NOT through `selB_affine`'s opaque `cands_common_period`, whose `n`-indexed product divides no fixed
period).  This is what `dstarC_exists_fibred_mS` will hoist.
-/

namespace CopiedDstarCMS

open WRP Step CopiedRank CopiedAffineAt CopiedLandmark CopiedCells SliceFamilyCell CopiedDstar
  SliceMarkN CopiedMark SliceMSO MSOMarkN CopiedGateEP SliceDstarGA SliceReRoot
  SliceDstarCore SliceDstar SliceLexOrder CopiedSetupMS CopiedRegionF CopiedDstarC

/-- **Machine-only gate period (deep-suffix two-sided pumping).** -/
theorem accepts_two_sided_EP_deepSuf_mp {α : Type*} (M : DetAuto α) (xP xS : α) :
    ∃ qM, 1 ≤ qM ∧ ∀ (pre suf : ℕ → List α) (mid preBase sufBaseEnd : List α) (cP cS : ℕ),
      (∀ mS, cP ≤ mS → pre mS = preBase ++ List.replicate (mS - cP) xP) →
      (∀ mS, cS ≤ mS → suf mS = List.replicate (mS - cS) xS ++ sufBaseEnd) →
      SliceOrder.EventuallyPeriodic (fun mS => M.accepts (pre mS ++ mid ++ suf mS)) qM := by
  have := M.fintypeQ
  obtain ⟨mP, pP, hpP, hperP⟩ := endofunction_EP_mul (fun s => M.δ s xP)
  obtain ⟨mS0, pS, hpS, hperS⟩ := endofunction_EP_mul (fun s => M.δ s xS)
  refine ⟨pP * pS, Nat.mul_pos hpP hpS,
    fun pre suf mid preBase sufBaseEnd cP cS hpre hsuf => ?_⟩
  have hform : ∀ mS, max cP cS ≤ mS →
      M.accepts (pre mS ++ mid ++ suf mS)
        = M.accept (List.foldl M.δ ((fun s => M.δ s xS)^[mS - cS]
            (List.foldl M.δ ((fun s => M.δ s xP)^[mS - cP] (List.foldl M.δ M.q0 preBase)) mid))
            sufBaseEnd) := by
    intro mS hmS
    have hP := hpre mS (le_trans (le_max_left _ _) hmS)
    have hS := hsuf mS (le_trans (le_max_right _ _) hmS)
    show M.accept (List.foldl M.δ M.q0 (pre mS ++ mid ++ suf mS)) = _
    rw [hP, hS, List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_append,
      foldl_replicate_eq_iterate, foldl_replicate_eq_iterate]
  refine ⟨max (max cP cS) (max (mP + cP) (mS0 + cS)), fun mS hmS => ?_⟩
  have h1 : max cP cS ≤ mS := le_trans (le_max_left _ _) hmS
  have h2 : mP + cP ≤ mS := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hmS
  have h3 : mS0 + cS ≤ mS := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hmS
  have hcP : cP ≤ mS := le_trans (le_max_left _ _) h1
  have hcS : cS ≤ mS := le_trans (le_max_right _ _) h1
  show M.accepts (pre (mS + pP * pS) ++ mid ++ suf (mS + pP * pS))
      ↔ M.accepts (pre mS ++ mid ++ suf mS)
  rw [hform (mS + pP * pS) (le_trans h1 (by omega)), hform mS h1]
  have eP : (fun s => M.δ s xP)^[(mS + pP * pS) - cP] (List.foldl M.δ M.q0 preBase)
      = (fun s => M.δ s xP)^[mS - cP] (List.foldl M.δ M.q0 preBase) := by
    rw [show (mS + pP * pS) - cP = (mS - cP) + pP * pS by omega]
    exact congrFun (hperP pS (mS - cP) (by omega)) (List.foldl M.δ M.q0 preBase)
  have eS : (fun s => M.δ s xS)^[(mS + pP * pS) - cS]
      = (fun s => M.δ s xS)^[mS - cS] := by
    rw [show (mS + pP * pS) - cS = (mS - cS) + pS * pP by rw [Nat.mul_comm pP pS]; omega]
    exact hperS pP (mS - cS) (by omega)
  rw [eP, eS]

/-- **Uniform deep-shape gate period.**  A SINGLE machine period `qC` for ALL shapes `ds`, bases `t0`,
slice lengths `n`. -/
theorem gateF_deepShape_EP_mS_uniform {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k)) :
    ∃ qC, 1 ≤ qC ∧ ∀ (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (t0 n : ℕ), t0 + B ≤ n →
      (∀ i e, ds i = .inr e → 1 ≤ e.elim id id) →
      SliceOrder.EventuallyPeriodic (fun mS => gateF M (deepShapeF ds mS) mS t0 n) qC := by
  obtain ⟨qC, hqC, hMP⟩ := accepts_two_sided_EP_deepSuf_mp M
    (mkLetter k U (fun _ => false)) (mkLetter k D (fun _ => false))
  refine ⟨qC, hqC, fun ds t0 n hwin hdeep => ?_⟩
  obtain ⟨cP, preBaseFront, preBaseEnd, _hcP, hpreU⟩ := cellSegU_deepForm ds t0 (t0 + B) hdeep
  obtain ⟨cS, sufBaseFront, sufBaseEnd, _hcS, hsufD⟩ := cellSegD_deepForm ds t0 hdeep
  obtain ⟨vth, hvth⟩ := deepShape_valid_ge ds hdeep
  have hQEP := hMP
    (fun mS => preBaseFront ++ List.replicate (mS - cP) (mkLetter k U (fun _ => false)))
    (fun mS => List.replicate (mS - cS) (mkLetter k D (fun _ => false)) ++ sufBaseEnd)
    (preBaseEnd ++ (markAtN (coreSet (coreOnly ds)).card (wrappedFlat n)
        (cellTuple (coreSpec (coreOnly ds)) t0 n)).map (mapBits (coreEmb (coreOnly ds)))
      ++ sufBaseFront)
    preBaseFront sufBaseEnd cP cS
    (fun _ _ => rfl) (fun _ _ => rfl)
  refine eventuallyPeriodic_congr_eventually
    (max 1 (max vth (max cP cS))) (fun mS hmS => ?_) hQEP
  have hm1 : 1 ≤ mS := le_trans (le_max_left _ _) hmS
  have hvmS : ∀ i, (deepShapeF ds mS i).valid mS :=
    hvth mS (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hmS)
  have hcSmS : cS ≤ mS :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hmS))
  have hcPmS : cP ≤ mS :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hmS))
  show gateF M (deepShapeF ds mS) mS t0 n ↔ _
  rw [gateF_reduced M mS hm1 (deepShapeF ds mS) hvmS t0 n hwin]
  unfold redM
  rw [accepts_pullback, accepts_reRoot, cellTupleF_deepShapeF ds mS t0 (t0 + B),
    midWord_deepShapeF_eq ds t0 n mS, hsufD mS hcSmS, hpreU mS hcPmS]
  simp only [List.append_assoc]

/-- **`prefixRank_run_affine_mS` with the period/slope hoisted before `suf`.**  The `(m,p,P)` returned
by `prefixRank_run_affine_mS` are built from `iterate_eventuallyPeriodic (blockStep A [x]) A.q0` and a
fixed-start block-weight sum — both `suf`-FREE.  So a SINGLE `(m,p,P)` serves every `suf`. -/
theorem prefixRank_run_affine_mS_uniform {Alpha : Type*} {d : ℕ} (A : RankSource Alpha d) (x : Alpha) :
    ∃ (m p : ℕ) (P : Fin d → ℤ), 1 ≤ p ∧ ∀ (suf : List Alpha) (k r : ℕ),
      A.prefixRank (List.replicate (m + p * k + r) x ++ suf)
          (List.replicate (m + p * k + r) x ++ suf).length
        = A.prefixRank (List.replicate (m + r) x ++ suf)
            (List.replicate (m + r) x ++ suf).length + k • P := by
  have := A.fintypeQ
  obtain ⟨m, p, hp, hper⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic (SliceRank.blockStep A [x]) A.q0
  have hgper : ∀ i, m ≤ i →
      SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i + p] A.q0)
        = SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i] A.q0) := by
    intro i hi; rw [hper i hi]
  refine ⟨m, p, ∑ i ∈ Finset.Ico m (m + p),
    SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i] A.q0), hp, fun suf k r => ?_⟩
  have hdecomp : ∀ mS, A.prefixRank (List.replicate mS x ++ suf)
      (List.replicate mS x ++ suf).length
      = (∑ i ∈ Finset.range mS, SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i] A.q0))
        + (List.foldl (SliceRank.rankStep A) ((SliceRank.blockStep A [x])^[mS] A.q0, 0) suf).2 := by
    intro mS
    rw [SliceRank.prefixRank_eq_foldl, List.foldl_append]
    obtain ⟨st, rk, hpr⟩ :
        ∃ st rk, List.foldl (SliceRank.rankStep A) (A.q0, 0) (List.replicate mS x) = (st, rk) :=
      ⟨_, _, rfl⟩
    have hrk : rk = ∑ i ∈ Finset.range mS,
        SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i] A.q0) := by
      have h := SliceRank.foldl_rankStep_replicate_snd A [x] A.q0 0 mS
      rw [CopiedSetupMS.flatten_replicate_singleton, hpr] at h
      simpa using h
    have hst : st = (SliceRank.blockStep A [x])^[mS] A.q0 := by
      have hbs : SliceRank.blockStep A [x] = fun q => A.δ q x := by funext q; rfl
      have h : st = List.foldl A.δ A.q0 (List.replicate mS x) := by
        rw [← SliceRank.rankStep_fst A A.q0 0 (List.replicate mS x), hpr]
      rw [h, foldl_replicate_eq_iterate, hbs]
    rw [hpr, SliceRank.rankStep_snd_add, hrk, hst]
  rw [hdecomp, hdecomp]
  have hsum := SliceAutomata.recurrence_affineOnResidues
    (fun N => ∑ i ∈ Finset.range N,
      SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i] A.q0)) m p _
    (SliceAutomata.partialSum_recurrence' _ m p hgper) k r
  have hstate : (SliceRank.blockStep A [x])^[m + p * k + r] A.q0
      = (SliceRank.blockStep A [x])^[m + r] A.q0 := by
    rw [show m + p * k + r = (m + r) + p * k by ring]
    exact iterate_period_mul (SliceRank.blockStep A [x]) A.q0 m p hper k (m + r) (by omega)
  rw [hstate, hsum]
  abel

/-- Coordinate form of `prefixRank_run_affine_mS_uniform` (one `suf`-free period for all `suf`). -/
theorem prefixRank_run_coord_affine_mS_uniform {Alpha : Type*} {d : ℕ} (A : RankSource Alpha d)
    (x : Alpha) (i : Fin d) :
    ∃ p, 1 ≤ p ∧ ∀ (suf : List Alpha), AffineOnResiduesAtZ p
      (fun mS => A.prefixRank (List.replicate mS x ++ suf)
        (List.replicate mS x ++ suf).length i) := by
  obtain ⟨m, p, P, hp, hb⟩ := prefixRank_run_affine_mS_uniform A x
  refine ⟨p, hp, fun suf => AffineOnResiduesAtZ.of_recurrence hp (m := m) (S := P i) (fun mS hmS => ?_)⟩
  have hthis := hb suf 1 (mS - m)
  rw [show m + p * 1 + (mS - m) = mS + p by omega, show m + (mS - m) = mS by omega] at hthis
  have hc := congrFun hthis i
  rw [Pi.add_apply, Pi.smul_apply, one_nsmul] at hc
  exact hc

/-- **`iterate_EPstate_EP_mS` over a FAMILY of EP-starts** sharing one period `pσ`.  Returns ONE period
`pσ*pf` (the `pf` from the start-FREE `endofunction_EP_mul f`) good for EVERY family member `a`. -/
theorem iterate_EPstate_EP_mS_unif {Q ι : Type*} [Finite Q] (f : Q → Q) (σ : ι → ℕ → Q)
    (pσ : ℕ) (hpσ : 1 ≤ pσ) (mσ : ℕ) (hσper : ∀ a mS, mσ ≤ mS → σ a (mS + pσ) = σ a mS) (c : ℕ) :
    ∃ q, 1 ≤ q ∧ ∀ a, ∃ M, ∀ mS, M ≤ mS → f^[mS + q - c] (σ a (mS + q)) = f^[mS - c] (σ a mS) := by
  obtain ⟨mf, pf, hpf, hf⟩ := endofunction_EP_mul f
  refine ⟨pσ * pf, Nat.mul_pos hpσ hpf, fun a => ?_⟩
  have hσmul : ∀ k mS, mσ ≤ mS → σ a (mS + pσ * k) = σ a mS := by
    intro k
    induction k with
    | zero => intro mS _; simp
    | succ j ih =>
      intro mS h
      rw [show mS + pσ * (j + 1) = (mS + pσ * j) + pσ by ring, hσper a _ (by omega), ih mS h]
  refine ⟨max mσ (mf + c), fun mS hmS => ?_⟩
  have hmσle : mσ ≤ mS := le_trans (le_max_left _ _) hmS
  have hmfc : mf + c ≤ mS := le_trans (le_max_right _ _) hmS
  have hσe : σ a (mS + pσ * pf) = σ a mS := hσmul pf mS hmσle
  have hfe : f^[mS + pσ * pf - c] = f^[mS - c] := by
    rw [show mS + pσ * pf - c = (mS - c) + pf * pσ by rw [Nat.mul_comm pσ pf]; omega]
    exact hf pσ (mS - c) (by omega)
  rw [hσe, hfe]

/-- **`partialSum_blockWeight_EPstate_affine_mS` over a FAMILY of EP-starts** sharing one period `pσ`.
Returns ONE period `pσ*pb` (the `pb` from the start-FREE `endofunction_EP_mul (blockStep A [y])`) good
for EVERY family member `a`. -/
theorem partialSum_blockWeight_EPstate_affine_mS_unif {Alpha : Type*} {d : ℕ} {ι : Type*}
    (A : RankSource Alpha d) (y : Alpha) (σ : ι → ℕ → A.Q)
    (pσ : ℕ) (hpσ : 1 ≤ pσ) (mσ : ℕ) (hσper : ∀ a mS, mσ ≤ mS → σ a (mS + pσ) = σ a mS)
    (c : ℕ) (i : Fin d) :
    ∃ p, 1 ≤ p ∧ ∀ a, AffineOnResiduesAtZ p
      (fun mS => (∑ j ∈ Finset.range (mS - c),
        SliceRank.blockWeight A [y] ((SliceRank.blockStep A [y])^[j] (σ a mS))) i) := by
  have := A.fintypeQ
  obtain ⟨mb, pb, hpb, hb⟩ := endofunction_EP_mul (SliceRank.blockStep A [y])
  set g : A.Q → ℕ → ℤ := fun q j =>
    SliceRank.blockWeight A [y] ((SliceRank.blockStep A [y])^[j] q) i with hgdef
  have hgper : ∀ q : A.Q, ∀ j, mb ≤ j → g q (j + pσ * pb) = g q j := by
    intro q j hj
    have hstep : (SliceRank.blockStep A [y])^[j + pσ * pb] = (SliceRank.blockStep A [y])^[j] := by
      rw [show j + pσ * pb = j + pb * pσ by ring]; exact hb pσ j hj
    show SliceRank.blockWeight A [y] ((SliceRank.blockStep A [y])^[j + pσ * pb] q) i
        = SliceRank.blockWeight A [y] ((SliceRank.blockStep A [y])^[j] q) i
    rw [congrFun hstep q]
  refine ⟨pσ * pb, Nat.mul_pos hpσ hpb, fun a => ?_⟩
  have hσmul : ∀ k mS, mσ ≤ mS → σ a (mS + pσ * k) = σ a mS := by
    intro k
    induction k with
    | zero => intro mS _; simp
    | succ b ih =>
      intro mS h
      rw [show mS + pσ * (b + 1) = (mS + pσ * b) + pσ by ring, hσper a _ (by omega), ih mS h]
  have hcoord : (fun mS => (∑ j ∈ Finset.range (mS - c),
        SliceRank.blockWeight A [y] ((SliceRank.blockStep A [y])^[j] (σ a mS))) i)
      = fun mS => ∑ j ∈ Finset.range (mS - c), g (σ a mS) j := by
    funext mS; rw [Finset.sum_apply]
  rw [hcoord]
  refine ⟨max mσ (mb + c), fun jr _ => ?_⟩
  set q0 : A.Q := σ a (max mσ (mb + c) + jr) with hq0def
  have hmσle : mσ ≤ max mσ (mb + c) + jr := by
    have := le_max_left mσ (mb + c); omega
  have hmbc : mb + c ≤ max mσ (mb + c) + jr := by
    have := le_max_right mσ (mb + c); omega
  have hrec : ∀ N, mb ≤ N → (∑ j ∈ Finset.range (N + pσ * pb), g q0 j)
      = (∑ j ∈ Finset.range N, g q0 j)
        + (∑ j ∈ Finset.Ico mb (mb + pσ * pb), g q0 j) :=
    SliceAutomata.partialSum_recurrence' (g q0) mb (pσ * pb)
      (fun j hj => hgper q0 j hj)
  refine ⟨∑ j ∈ Finset.range (max mσ (mb + c) + jr - c), g q0 j,
    ∑ j ∈ Finset.Ico mb (mb + pσ * pb), g q0 j, fun k => ?_⟩
  show (∑ j ∈ Finset.range (max mσ (mb + c) + jr + pσ * pb * k - c),
      g (σ a (max mσ (mb + c) + jr + pσ * pb * k)) j) = _
  have hσfix : σ a (max mσ (mb + c) + jr + pσ * pb * k) = q0 := by
    rw [show max mσ (mb + c) + jr + pσ * pb * k = (max mσ (mb + c) + jr) + pσ * (pb * k) by ring,
      hσmul (pb * k) _ hmσle]
  rw [hσfix]
  rw [show max mσ (mb + c) + jr + pσ * pb * k - c
      = (max mσ (mb + c) + jr - c) + pσ * pb * k by omega]
  have haff := SliceAutomata.recurrence_affineOnResidues
    (fun N => ∑ j ∈ Finset.range N, g q0 j) mb (pσ * pb)
    (∑ j ∈ Finset.Ico mb (mb + pσ * pb), g q0 j) hrec k
    (max mσ (mb + c) + jr - c - mb)
  rw [show mb + pσ * pb * k + (max mσ (mb + c) + jr - c - mb)
      = (max mσ (mb + c) + jr - c) + pσ * pb * k by omega,
    show mb + (max mσ (mb + c) + jr - c - mb) = max mσ (mb + c) + jr - c by omega] at haff
  rw [haff, nsmul_eq_mul]

/-- **`prefixRank_deepSuf_affine_mS` with the period hoisted before `suf`.**  Both the prefix-run
period (via `prefixRank_run_coord_affine_mS_uniform`) and the `D`-tail period (via
`partialSum_blockWeight_EPstate_affine_mS_unif`, σ-family over `suf`) are `suf`-free, so one period
`pH*pT` serves all `suf`. -/
theorem prefixRank_deepSuf_affine_mS_uniform {d : ℕ} (A : RankSource Step d) (i_off : ℕ) (i : Fin d) :
    ∃ p, 1 ≤ p ∧ ∀ (suf : List Step), AffineOnResiduesAtZ p
      (fun mS => A.prefixRank (List.replicate mS U ++ suf ++ List.replicate (mS - i_off) D)
        (List.replicate mS U ++ suf ++ List.replicate (mS - i_off) D).length i) := by
  have := A.fintypeQ
  obtain ⟨pH, hpH, hHaff⟩ := prefixRank_run_coord_affine_mS_uniform A U i
  obtain ⟨m2, p2, hp2, hper2⟩ := SliceAutomata.iterate_eventuallyPeriodic (fun q => A.δ q U) A.q0
  have hσ2per : ∀ (suf : List Step) mS, m2 ≤ mS →
      (fun mS => List.foldl A.δ A.q0 (List.replicate mS U ++ suf)) (mS + p2)
        = (fun mS => List.foldl A.δ A.q0 (List.replicate mS U ++ suf)) mS := by
    intro suf mS hmS
    simp only []
    rw [List.foldl_append, List.foldl_append, foldl_replicate_eq_iterate,
      foldl_replicate_eq_iterate, hper2 mS hmS]
  obtain ⟨pT, hpT, hTaff⟩ := partialSum_blockWeight_EPstate_affine_mS_unif A D
    (fun (suf : List Step) mS => List.foldl A.δ A.q0 (List.replicate mS U ++ suf)) p2 hp2 m2 hσ2per
    i_off i
  refine ⟨pH * pT, Nat.mul_pos hpH hpT, fun suf => ?_⟩
  have hG := ((hHaff suf).of_dvd hpH (dvd_mul_right pH pT) (Nat.mul_pos hpH hpT)).add
    (Nat.mul_pos hpH hpT) ((hTaff suf).of_dvd hpT (dvd_mul_left pT pH) (Nat.mul_pos hpH hpT))
  refine AffineOnResiduesAtZ.congr' (fun mS => ?_) hG
  have hsplit := congrFun (prefixRank_headTail_split A (List.replicate mS U ++ suf) D (mS - i_off)) i
  rw [Pi.add_apply] at hsplit
  exact hsplit.symm

/-- **`summand_copied_deepSuf_affine_mS` with the period hoisted before `n0`.**  The deep-suffix
summand's period `pA*qF` (from `prefixRank_deepSuf_affine_mS_uniform` + `iterate_EPstate_EP_mS_unif`)
is `n0`-free, so one period serves all `n0`. -/
theorem summand_copied_deepSuf_affine_mS_uniform {k : ℕ} (s : Summand Step d k)
    (i_off : ℕ) (hi : 1 ≤ i_off) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ (n0 : ℕ), AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n0) (fun _ => mS + 2 * n0 + 1 + (mS - 1 - i_off)) i) := by
  have := s.A.fintypeQ
  obtain ⟨pA, hpA, hAaff⟩ := prefixRank_deepSuf_affine_mS_uniform s.A i_off i
  obtain ⟨m2, p2, hp2, hper2⟩ := SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
  have hσBper : ∀ (n0 : ℕ) mS, m2 ≤ mS →
      (fun mS => (fun q => List.foldl s.A.δ q [U, D])^[n0] (List.foldl s.A.δ s.A.q0
        (List.replicate mS U))) (mS + p2)
        = (fun mS => (fun q => List.foldl s.A.δ q [U, D])^[n0] (List.foldl s.A.δ s.A.q0
            (List.replicate mS U))) mS := by
    intro n0 mS hmS
    simp only []
    rw [foldl_replicate_eq_iterate, foldl_replicate_eq_iterate, hper2 mS hmS]
  obtain ⟨qF, hqF, hFunif⟩ := iterate_EPstate_EP_mS_unif (fun q => s.A.δ q D)
    (fun (n0 : ℕ) mS => (fun q => List.foldl s.A.δ q [U, D])^[n0] (List.foldl s.A.δ s.A.q0
      (List.replicate mS U))) p2 hp2 m2 hσBper i_off
  refine ⟨pA * qF, Nat.mul_pos hpA hqF, fun n0 => ?_⟩
  obtain ⟨MF, hFper⟩ := hFunif n0
  have hβaff : AffineOnResiduesAtZ qF (fun mS => (s.β ((fun q => s.A.δ q D)^[mS - i_off]
      ((fun q => List.foldl s.A.δ q [U, D])^[n0] (List.foldl s.A.δ s.A.q0
        (List.replicate mS U)))) D) i) := by
    refine affineOnResiduesAtZ_of_EP MF (fun mS hmS => ?_)
    show (s.β ((fun q => s.A.δ q D)^[mS + qF - i_off]
        ((fun q => List.foldl s.A.δ q [U, D])^[n0] (List.foldl s.A.δ s.A.q0
          (List.replicate (mS + qF) U)))) D) i = _
    rw [hFper mS hmS]
  have hG := (((hAaff ((List.replicate n0 [U, D]).flatten)).of_dvd hpA (dvd_mul_right pA qF)
      (Nat.mul_pos hpA hqF)).smul s.coeff).add (Nat.mul_pos hpA hqF)
    (hβaff.of_dvd hqF (dvd_mul_left qF pA) (Nat.mul_pos hpA hqF))
  refine affineOnResiduesAtZ_congr_eventually (m0 := i_off + 2) (Nat.mul_pos hpA hqF)
    (fun mS hmS => ?_) hG
  rw [congrFun (summand_copied_sufStretch_eq s mS (mS - 1 - i_off) (by omega) n0) i,
    show mS - 1 - i_off + 1 = mS - i_off by omega, foldl_replicate_eq_iterate]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **`summand_copied_deepPref_affine_mS` with the period hoisted before `n0`.**  The deep-prefix
period (from `prefStretch_formula_rankAffine_q s`) takes only `s`, so it is trivially `n0`-uniform. -/
theorem summand_copied_deepPref_affine_mS_uniform {k : ℕ} (s : Summand Step d k)
    (i_off : ℕ) (hi : 1 ≤ i_off) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ (n0 : ℕ), AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n0) (fun _ => mS - 1 - i_off) i) := by
  obtain ⟨m, p, P, hp, hrec⟩ := prefStretch_formula_rankAffine_q s
  refine ⟨p, hp, fun n0 => AffineOnResiduesAtZ.of_recurrence hp (m := m + 1 + i_off) (S := P i)
    (fun w hw => ?_)⟩
  rw [congrFun (summand_copied_prefStretch_eq s (w + p) (w + p - 1 - i_off) (by omega) n0) i,
      congrFun (summand_copied_prefStretch_eq s w (w - 1 - i_off) (by omega) n0) i,
      show w + p - 1 - i_off = (w - 1 - i_off) + p by omega]
  exact congrFun (hrec (w - 1 - i_off) (by omega)) i

/-- Block-`U` cell value uniform over the block index `j`. -/
theorem summand_copied_block_affine_mS_uniform {k : ℕ} (s : Summand Step d k) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ j, AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS (j + 1)) (fun _ => mS + 2 * j) i) := by
  have := s.A.fintypeQ
  obtain ⟨m1, p1, P1, hp1, hb⟩ := prefixRank_run_affine_mS_uniform s.A U
  obtain ⟨m2, p2, hp2, hper2⟩ := SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
  refine ⟨p1 * p2, Nat.mul_pos hp1 hp2, fun j => ?_⟩
  refine AffineOnResiduesAtZ.of_recurrence (Nat.mul_pos hp1 hp2)
    (m := max m1 m2 + 1) (S := s.coeff * ((p2 : ℤ) * P1 i)) (fun n hn => ?_)
  have hnpos : 1 ≤ n := by omega
  have hpre := hb ((List.replicate j [U, D]).flatten) p2 (n - m1)
  rw [show m1 + p1 * p2 + (n - m1) = n + p1 * p2 by omega,
    show m1 + (n - m1) = n by omega] at hpre
  have hstate : List.foldl s.A.δ s.A.q0 (List.replicate (n + p1 * p2) U)
      = List.foldl s.A.δ s.A.q0 (List.replicate n U) := by
    rw [foldl_replicate_eq_iterate, foldl_replicate_eq_iterate,
      show n + p1 * p2 = n + p2 * p1 by ring]
    exact iterate_period_mul (fun q => s.A.δ q U) s.A.q0 m2 p2 hper2 p1 n (by omega)
  rw [congrFun (summand_copied_block_eq s (n + p1 * p2) j (by omega)) i,
    congrFun (summand_copied_block_eq s n j hnpos) i, hpre, hstate]
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  ring

/-- Block-`D` cell value uniform over the block index `j`. -/
theorem summand_copied_blockD_affine_mS_uniform {k : ℕ} (s : Summand Step d k) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ j, AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS (j + 1)) (fun _ => mS + 2 * j + 1) i) := by
  have := s.A.fintypeQ
  obtain ⟨m1, p1, P1, hp1, hb⟩ := prefixRank_run_affine_mS_uniform s.A U
  obtain ⟨m2, p2, hp2, hper2⟩ := SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
  refine ⟨p1 * p2, Nat.mul_pos hp1 hp2, fun j => ?_⟩
  refine AffineOnResiduesAtZ.of_recurrence (Nat.mul_pos hp1 hp2)
    (m := max m1 m2 + 1) (S := s.coeff * ((p2 : ℤ) * P1 i)) (fun n hn => ?_)
  have hnpos : 1 ≤ n := by omega
  have hpre := hb ((List.replicate j [U, D]).flatten) p2 (n - m1)
  rw [show m1 + p1 * p2 + (n - m1) = n + p1 * p2 by omega,
    show m1 + (n - m1) = n by omega] at hpre
  have hstate : List.foldl s.A.δ s.A.q0 (List.replicate (n + p1 * p2) U)
      = List.foldl s.A.δ s.A.q0 (List.replicate n U) := by
    rw [foldl_replicate_eq_iterate, foldl_replicate_eq_iterate,
      show n + p1 * p2 = n + p2 * p1 by ring]
    exact iterate_period_mul (fun q => s.A.δ q U) s.A.q0 m2 p2 hper2 p1 n (by omega)
  rw [congrFun (summand_copied_blockD_eq s (n + p1 * p2) j (by omega)) i,
    congrFun (summand_copied_blockD_eq s n j hnpos) i, hpre, hstate]
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  ring

/-- Unified middle cell value uniform over the block index `j` (`j < n`). -/
theorem summand_copied_mid_affine_mS_uniform {k : ℕ} (s : Summand Step d k) (e : Bool) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ j n, j < n → AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n) (fun _ => mS - 1 + (1 + 2 * j + e.toNat)) i) := by
  cases e with
  | false =>
    obtain ⟨p, hp, hG⟩ := summand_copied_block_affine_mS_uniform s i
    refine ⟨p, hp, fun j n hjn => affineOnResiduesAtZ_congr_eventually hp (m0 := 1)
      (fun w hw => ?_) (hG j)⟩
    rw [show w - 1 + (1 + 2 * j + (false : Bool).toNat) = w - 1 + (2 * j + 1) from by
        simp only [Bool.toNat_false]; omega,
      congrFun (summand_copied_mid_stable s w (2 * j + 1) n (j + 1) hw (by omega) (by omega)) i,
      show w - 1 + (2 * j + 1) = w + 2 * j from by omega]
  | true =>
    obtain ⟨p, hp, hG⟩ := summand_copied_blockD_affine_mS_uniform s i
    refine ⟨p, hp, fun j n hjn => affineOnResiduesAtZ_congr_eventually hp (m0 := 1)
      (fun w hw => ?_) (hG j)⟩
    rw [show w - 1 + (1 + 2 * j + (true : Bool).toNat) = w - 1 + (2 * j + 2) from by
        simp only [Bool.toNat_true]; omega,
      congrFun (summand_copied_mid_stable s w (2 * j + 2) n (j + 1) hw (by omega) (by omega)) i,
      show w - 1 + (2 * j + 2) = w + 2 * j + 1 from by omega]

/-- Prefix-letter cell value uniform over `n` (the value reads only the `U`-prefix, n-free). -/
theorem summand_copied_pre_affine_mS_uniform {k : ℕ} (s : Summand Step d k) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ n, AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n) (fun _ => mS - 1) i) := by
  have := s.A.fintypeQ
  obtain ⟨m1, p1, P1, hp1, hb⟩ := prefixRank_run_affine_mS_uniform s.A U
  obtain ⟨m2, p2, hp2, hper2⟩ := SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
  refine ⟨p1 * p2, Nat.mul_pos hp1 hp2, fun n => ?_⟩
  have hEq : ∀ w, 1 ≤ w → s.eval (copiedSlice w n) (fun _ => w - 1) i
      = s.coeff * s.A.prefixRank (List.replicate (w - 1) U) (List.replicate (w - 1) U).length i
        + s.β (List.foldl s.A.δ s.A.q0 (List.replicate (w - 1) U)) U i := by
    intro w hw
    have hget : (copiedSlice w n)[w - 1]? = some U :=
      copiedSlice_getElem?_pref w n (w - 1) hw (by omega)
    have htake : (copiedSlice w n).take (w - 1) = List.replicate (w - 1) U :=
      copiedSlice_take_U w (w - 1) n hw (by omega)
    have hps : s.A.prefixRank (copiedSlice w n) (w - 1)
        = s.A.prefixRank (List.replicate (w - 1) U) (List.replicate (w - 1) U).length := by
      rw [List.length_replicate]
      exact SliceRankAtom.prefixRank_prefix_stable s.A _ _ (w - 1)
        (by rw [htake, List.take_replicate, Nat.min_self])
    have hsb : s.A.stateBefore (copiedSlice w n) (w - 1)
        = List.foldl s.A.δ s.A.q0 (List.replicate (w - 1) U) := by
      unfold RankSource.stateBefore; rw [htake]
    simp only [Summand.eval, hget, hps, hsb, Option.elim_some]
  refine AffineOnResiduesAtZ.of_recurrence (Nat.mul_pos hp1 hp2)
    (m := max m1 m2 + 2) (S := s.coeff * ((p2 : ℤ) * P1 i)) (fun w hw => ?_)
  rw [hEq (w + p1 * p2) (by omega), hEq w (by omega)]
  have hpre := hb [] p2 ((w - 1) - m1)
  simp only [List.append_nil] at hpre
  rw [show m1 + p1 * p2 + ((w - 1) - m1) = (w + p1 * p2) - 1 by omega,
    show m1 + ((w - 1) - m1) = w - 1 by omega] at hpre
  have hstate : List.foldl s.A.δ s.A.q0 (List.replicate ((w + p1 * p2) - 1) U)
      = List.foldl s.A.δ s.A.q0 (List.replicate (w - 1) U) := by
    rw [foldl_replicate_eq_iterate, foldl_replicate_eq_iterate,
      show (w + p1 * p2) - 1 = (w - 1) + p2 * p1 by rw [Nat.mul_comm p2 p1]; omega]
    exact iterate_period_mul (fun q => s.A.δ q U) s.A.q0 m2 p2 hper2 p1 (w - 1) (by omega)
  rw [hpre, hstate]
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  ring

/-- Suffix-letter cell value uniform over the base `n0`. -/
theorem summand_copied_suf_affine_mS_uniform {k : ℕ} (s : Summand Step d k) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ n0, AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n0) (fun _ => mS + 2 * n0) i) := by
  have := s.A.fintypeQ
  obtain ⟨m1, p1, P1, hp1, hb⟩ := prefixRank_run_affine_mS_uniform s.A U
  obtain ⟨m2, p2, hp2, hper2⟩ := SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
  refine ⟨p1 * p2, Nat.mul_pos hp1 hp2, fun n0 => ?_⟩
  refine AffineOnResiduesAtZ.of_recurrence (Nat.mul_pos hp1 hp2)
    (m := max m1 m2 + 1) (S := s.coeff * ((p2 : ℤ) * P1 i)) (fun n hn => ?_)
  have hnpos : 1 ≤ n := by omega
  have hpre := hb ((List.replicate n0 [U, D]).flatten) p2 (n - m1)
  rw [show m1 + p1 * p2 + (n - m1) = n + p1 * p2 by omega,
    show m1 + (n - m1) = n by omega] at hpre
  have hstate : List.foldl s.A.δ s.A.q0 (List.replicate (n + p1 * p2) U)
      = List.foldl s.A.δ s.A.q0 (List.replicate n U) := by
    rw [foldl_replicate_eq_iterate, foldl_replicate_eq_iterate,
      show n + p1 * p2 = n + p2 * p1 by ring]
    exact iterate_period_mul (fun q => s.A.δ q U) s.A.q0 m2 p2 hper2 p1 n (by omega)
  rw [congrFun (summand_copied_suf_eq s (n + p1 * p2) n0 (by omega)) i,
    congrFun (summand_copied_suf_eq s n n0 hnpos) i, hpre, hstate]
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

/-- Suffix-stretch (`sufIdx l`) cell value uniform over the base `n0`. -/
theorem summand_copied_sufStretch_affine_mS_uniform {k : ℕ} (s : Summand Step d k) (l : ℕ) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ n0, AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n0) (fun _ => mS + 2 * n0 + 1 + l) i) := by
  have := s.A.fintypeQ
  obtain ⟨m1, p1, P1, hp1, hb⟩ := prefixRank_run_affine_mS_uniform s.A U
  obtain ⟨m2, p2, hp2, hper2⟩ := SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
  refine ⟨p1 * p2, Nat.mul_pos hp1 hp2, fun n0 => ?_⟩
  refine AffineOnResiduesAtZ.of_recurrence (Nat.mul_pos hp1 hp2)
    (m := max (max m1 m2) (l + 1) + 1) (S := s.coeff * ((p2 : ℤ) * P1 i)) (fun n hn => ?_)
  have hpre := hb ((List.replicate n0 [U, D]).flatten ++ List.replicate (l + 1) D) p2 (n - m1)
  rw [show m1 + p1 * p2 + (n - m1) = n + p1 * p2 by omega,
    show m1 + (n - m1) = n by omega] at hpre
  simp only [← List.append_assoc] at hpre
  have hstate : List.foldl s.A.δ s.A.q0 (List.replicate (n + p1 * p2) U)
      = List.foldl s.A.δ s.A.q0 (List.replicate n U) := by
    rw [foldl_replicate_eq_iterate, foldl_replicate_eq_iterate,
      show n + p1 * p2 = n + p2 * p1 by ring]
    exact iterate_period_mul (fun q => s.A.δ q U) s.A.q0 m2 p2 hper2 p1 n (by omega)
  rw [congrFun (summand_copied_sufStretch_eq s (n + p1 * p2) l (by omega) n0) i,
    congrFun (summand_copied_sufStretch_eq s n l (by omega) n0) i, hpre, hstate]
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

/-- Prefix-stretch (`prefIdx q`) cell value uniform over `n` (constant in `mS`, period 1). -/
theorem summand_copied_prefIdx_affine_mS_uniform {k : ℕ} (s : Summand Step d k) (q : ℕ) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ n, AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n) (fun _ => q) i) := by
  refine ⟨1, le_refl 1, fun n => affineOnResiduesAtZ_congr_eventually (le_refl 1)
    (G := fun _ => s.eval (copiedSlice (q + 1) n) (fun _ => q) i) (m0 := q + 1) (fun w hw => ?_)
    (AffineOnResiduesAtZ.const 1 _)⟩
  exact congrFun (SliceRankAtom.summand_eval_const_prefix_stable s (copiedSlice w n)
    (copiedSlice (q + 1) n) q (by
      rw [copiedSlice_take_U w (q + 1) n (by omega) (by omega),
        copiedSlice_take_U (q + 1) (q + 1) n (by omega) (le_refl _)])) i

/-- **Uniform core/shallow summand** (the `(t,n)`-free-period variant of `summand_cell_affine_mS`):
each region descriptor's per-summand cell value is affine-on-residues at a `(t,n)`-FREE period,
uniformly for all bulk bases `t` and slice lengths `n` (`t+B≤n`).  Dispatches each region constructor
to its uniform piece-(c) lemma; the period from each leaf is built from `prefixRank_run_affine_mS_uniform`
/ the constant-prefix bound, so it is `(t,n)`-free. -/
theorem summand_cell_affine_mS_uniform {k B : ℕ} (s : Summand Step d k) (r : RegionSpecF B)
    (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ (t n : ℕ), t + B ≤ n → AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n) (fun _ => r.posAt mS t n) i) := by
  rcases r with rr | q | l
  · rcases rr with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
    · obtain ⟨p, hp, hG⟩ := summand_copied_pre_affine_mS_uniform s i
      refine ⟨p, hp, fun t n _ => affineOnResiduesAtZ_congr_eventually hp (m0 := 1)
        (fun w hw => ?_) (hG n)⟩
      simp only [RegionSpecF.posAt, RegionSpec.posAt, Nat.add_zero]
    · obtain ⟨p, hp, hG⟩ := summand_copied_suf_affine_mS_uniform s i
      refine ⟨p, hp, fun t n _ => affineOnResiduesAtZ_congr_eventually hp (m0 := 1)
        (fun w hw => ?_) (hG n)⟩
      simp only [RegionSpecF.posAt, RegionSpec.posAt]
      rw [show (fun _ : Fin k => w - 1 + (1 + 2 * n)) = (fun _ : Fin k => w + 2 * n) from
        funext fun _ => by omega]
    · obtain ⟨p, hp, hG⟩ := summand_copied_mid_affine_mS_uniform s e i
      refine ⟨p, hp, fun t n htBn => ?_⟩
      simp only [RegionSpecF.posAt, RegionSpec.posAt]
      exact hG f.val n (by have := f.isLt; omega)
    · obtain ⟨p, hp, hG⟩ := summand_copied_mid_affine_mS_uniform s e i
      refine ⟨p, hp, fun t n htBn => ?_⟩
      simp only [RegionSpecF.posAt, RegionSpec.posAt]
      exact hG (n - 1 - l.val) n (by omega)
    · obtain ⟨p, hp, hG⟩ := summand_copied_mid_affine_mS_uniform s e i
      refine ⟨p, hp, fun t n htBn => ?_⟩
      simp only [RegionSpecF.posAt, RegionSpec.posAt]
      exact hG (t + δ.val) n (by have := δ.isLt; omega)
  · obtain ⟨p, hp, hG⟩ := summand_copied_prefIdx_affine_mS_uniform s q i
    refine ⟨p, hp, fun t n _ => ?_⟩
    simp only [RegionSpecF.posAt]
    exact hG n
  · obtain ⟨p, hp, hG⟩ := summand_copied_sufStretch_affine_mS_uniform s l i
    refine ⟨p, hp, fun t n _ => ?_⟩
    simp only [RegionSpecF.posAt]
    exact hG n

/-- **List-sum closure for `AffineOnResiduesAtZ`, t,n-UNIFORM**: a finite sum of per-term
affine-on-residues functions (each at its own t,n-FREE period, uniformly affine over all `t,n` with
`t+B≤n`) is affine-on-residues at the period PRODUCT, uniformly over all such `t,n`. -/
theorem affineOnResiduesAtZ_listSum_tnUnif {α : Type*} {B : ℕ} (L : List α)
    (F : α → ℕ → ℕ → ℕ → ℤ)
    (hF : ∀ a ∈ L, ∃ p, 1 ≤ p ∧ ∀ t n, t + B ≤ n → AffineOnResiduesAtZ p (fun mS => F a t n mS)) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ t n, t + B ≤ n →
      AffineOnResiduesAtZ p (fun mS => (L.map (fun a => F a t n mS)).sum) := by
  induction L with
  | nil => exact ⟨1, le_refl 1, fun t n _ => by simpa using AffineOnResiduesAtZ.const 1 0⟩
  | cons a L' ih =>
    obtain ⟨pa, hpa, hAa⟩ := hF a (by simp)
    obtain ⟨pL, hpL, hAL⟩ := ih (fun b hb => hF b (by simp [hb]))
    have hpos : 1 ≤ pa * pL := Nat.mul_pos hpa hpL
    refine ⟨pa * pL, hpos, fun t n htBn => ?_⟩
    have heq : (fun mS => ((a :: L').map (fun b => F b t n mS)).sum)
        = (fun mS => F a t n mS + (L'.map (fun b => F b t n mS)).sum) := by
      funext mS; simp [List.map_cons, List.sum_cons]
    rw [heq]
    exact AffineOnResiduesAtZ.add hpos
      ((hAa t n htBn).of_dvd hpa ⟨pL, rfl⟩ hpos)
      ((hAL t n htBn).of_dvd hpL ⟨pa, Nat.mul_comm pa pL⟩ hpos)

/-- **`rank_cell_mixedDeep_affine_mS` with the period hoisted before `t,n`** (per coordinate `i`).
Each summand's value is affine at a `t,n`-FREE period (core/shallow via `summand_cell_affine_mS_uniform`,
deep-suffix via `summand_copied_deepSuf_affine_mS_uniform`, deep-prefix via
`summand_copied_deepPref_affine_mS_uniform`); the cell rank is their `t,n`-uniform list-sum. -/
theorem rank_cell_mixedDeep_affine_mS_uniform {B : ℕ} (P : WRP.Presentation Step Step)
    (c : Fin P.toPoly.K) (ds : Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ))
    (_hB : 1 ≤ B) (hdeep : ∀ j e, ds j = .inr e → 1 ≤ e.elim id id) (i : Fin P.d) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ (t n : ℕ), t + B ≤ n → AffineOnResiduesAtZ p
      (fun mS => P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n) i) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  obtain ⟨p, hp, hAsum⟩ := affineOnResiduesAtZ_listSum_tnUnif (B := B) κ.summands
    (fun s t n mS => s.eval (copiedSlice mS n) (mixedTupleF ds mS t n) i)
    (fun s _ => by
      show ∃ p : ℕ, 1 ≤ p ∧ ∀ t n, t + B ≤ n → AffineOnResiduesAtZ p
        (fun mS => s.eval (copiedSlice mS n) (fun _ => mixedPosAt (ds s.π) mS t n) i)
      rcases hd : ds s.π with r | (i_off | i_off)
      · exact summand_cell_affine_mS_uniform s r i
      · obtain ⟨ps, hps, haff⟩ :=
          summand_copied_deepSuf_affine_mS_uniform s i_off (hdeep s.π (.inl i_off) hd) i
        exact ⟨ps, hps, fun t n _ => haff n⟩
      · obtain ⟨ps, hps, haff⟩ :=
          summand_copied_deepPref_affine_mS_uniform s i_off (hdeep s.π (.inr i_off) hd) i
        exact ⟨ps, hps, fun t n _ => haff n⟩)
  refine ⟨p, hp, fun t n htBn => ?_⟩
  have key : (fun mS => P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n) i)
      = (fun mS => κ.c0 i
          + (κ.summands.map (fun s => s.eval (copiedSlice mS n) (mixedTupleF ds mS t n) i)).sum) := by
    funext mS
    rw [hκ (copiedSlice mS n) (mixedTupleF ds mS t n)]
    rfl
  rw [key]
  exact AffineOnResiduesAtZ.add hp (AffineOnResiduesAtZ.const p _) (hAsum t n htBn)

/-- **The `t,n`-uniform vector form of the mixed-deep cell rank**: ALL `Fin P.d` coordinates are
affine-on-residues in `mS` at a COMMON `(t,n)`-FREE period (the product of the per-coordinate periods
from `rank_cell_mixedDeep_affine_mS_uniform`).  This is the rank half of the d3.4 bridge's
`coordCands_period_uniform` (paired with `gateF_deepShape_EP_mS_uniform`). -/
theorem rank_cell_mixedDeep_vec_uniform {B : ℕ} (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (ds : Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ))
    (hB : 1 ≤ B) (hdeep : ∀ j e, ds j = .inr e → 1 ≤ e.elim id id) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ (t n : ℕ), t + B ≤ n → ∀ i, AffineOnResiduesAtZ p
      (fun mS => P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n) i) := by
  classical
  choose pf hpf haf using fun i => rank_cell_mixedDeep_affine_mS_uniform P c ds hB hdeep i
  have hppos : 0 < Finset.univ.prod pf := Finset.prod_pos (fun i _ => hpf i)
  exact ⟨Finset.univ.prod pf, hppos, fun t n htBn i =>
    (haf i t n htBn).of_dvd (hpf i) (Finset.dvd_prod_of_mem pf (Finset.mem_univ i)) hppos⟩

/-! ### The period hoist: `coordCands_period_uniform` -/

open scoped Classical in
/-- Total per-`(c,ds)` rank period: the `(c,ds)`-only period of `rank_cell_mixedDeep_vec_uniform` when
`ds` is a genuine deep tuple, else `1`.  Used to take a finite product over the n-FREE shape set. -/
noncomputable def rankPeriodTot {B : ℕ} (P : WRP.Presentation Step Step) (hB : 1 ≤ B)
    (cds : Σ c : Fin P.toPoly.K, Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) : ℕ :=
  if h : (∀ j e, cds.2 j = .inr e → 1 ≤ e.elim id id)
    then (rank_cell_mixedDeep_vec_uniform P cds.1 cds.2 hB h).choose else 1

/-- **The hoisted machine/presentation period `pstar_mS`** for the bounded `selB` candidate list,
together with the per-candidate divisibility + EP/affine certificate.  `pstar_mS` is the product over
the n-FREE `mixedTuplesF` shape set of (machine gate period × presentation rank period), so it is
independent of `n` and of the base `t`.  This is the d3.4 linchpin (no n-direction analog): the gate
period (`gateF_deepShape_EP_mS_uniform`, machine-only per `c`) and the rank period
(`rank_cell_mixedDeep_vec_uniform`, presentation-only per `(c,ds)`) are both `(t,n)`-free. -/
theorem coordCands_period_uniform {B : ℕ} (P : WRP.Presentation Step Step) (hB : 1 ≤ B)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (q_U q_D : ℕ) :
    ∃ pstar_mS : ℕ, 1 ≤ pstar_mS ∧
      ∀ (c : Fin P.toPoly.K) (ds : Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
        ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) →
        ∀ (t n : ℕ), t + B ≤ n →
        ∃ p, 1 ≤ p ∧ p ∣ pstar_mS
          ∧ SliceOrder.EventuallyPeriodic
              (fun mS => gateF (Mc c) (deepShapeF ds mS) mS t n) p
          ∧ ∀ i, AffineOnResiduesAtZ p
              (fun mS => P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n) i) := by
  classical
  choose qC hqC1 hqCep using fun c => gateF_deepShape_EP_mS_uniform (B := B) (Mc c)
  have hrP1 : ∀ cds, 1 ≤ rankPeriodTot P hB cds := by
    intro cds; unfold rankPeriodTot
    split_ifs with h
    · exact (rank_cell_mixedDeep_vec_uniform P cds.1 cds.2 hB h).choose_spec.1
    · exact le_refl 1
  set sigmaSet : Finset (Σ c : Fin P.toPoly.K, Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) :=
    Finset.univ.sigma (fun c => mixedTuplesF B q_U q_D (P.toPoly.arity c)) with hsigdef
  refine ⟨(∏ c, qC c) * (∏ cds ∈ sigmaSet, rankPeriodTot P hB cds), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun c _ => Nat.one_le_iff_ne_zero.mp (hqC1 c)))
      (Finset.prod_ne_zero_iff.mpr (fun cds _ => Nat.one_le_iff_ne_zero.mp (hrP1 cds))))
  · intro c ds hds t n htBn
    have hdeep : ∀ j e, ds j = .inr e → 1 ≤ e.elim id id :=
      coordCands_hdeep ((mem_mixedTuplesF ds).mp hds)
    have hmemS : (⟨c, ds⟩ : Σ c, Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) ∈ sigmaSet := by
      rw [hsigdef, Finset.mem_sigma]; exact ⟨Finset.mem_univ c, hds⟩
    have hrPeq : rankPeriodTot P hB ⟨c, ds⟩
        = (rank_cell_mixedDeep_vec_uniform P c ds hB hdeep).choose := by
      unfold rankPeriodTot; exact dif_pos hdeep
    refine ⟨qC c * rankPeriodTot P hB ⟨c, ds⟩, Nat.mul_pos (hqC1 c) (hrP1 _), ?_, ?_, ?_⟩
    · exact mul_dvd_mul
        (Finset.dvd_prod_of_mem qC (Finset.mem_univ c))
        (Finset.dvd_prod_of_mem (rankPeriodTot P hB) hmemS)
    · exact SliceDstar.EP_of_dvd (hqCep c ds t n htBn hdeep)
        (dvd_mul_right (qC c) (rankPeriodTot P hB ⟨c, ds⟩))
    · intro i
      have haff := (rank_cell_mixedDeep_vec_uniform P c ds hB hdeep).choose_spec.2 t n htBn i
      rw [← hrPeq] at haff
      exact haff.of_dvd (hrP1 _) (dvd_mul_left (rankPeriodTot P hB ⟨c, ds⟩) (qC c))
        (Nat.mul_pos (hqC1 c) (hrP1 _))

/-- **The bounded `selB` is affine-on-residues at a SINGLE machine/presentation period `pstar_mS`,
hoisted before the `∀ n` binder** (the d3.4 linchpin).  Unlike `selB_affine` — whose period
`cands_common_period` over the n-INDEXED `selCands` list grows with `n` and divides no fixed period —
this re-derives `selB`'s affineness directly at the n-FREE `pstar_mS` from `coordCands_period_uniform`,
lifting each candidate's `(t,n)`-free gate-EP / value-affine period to `pstar_mS` per-candidate via
`EP_of_dvd` / `of_dvd`, then `gated_lexMin_affine_at`.  This is what `dstarC_exists_fibred_mS` hoists. -/
theorem selB_period_uniform {B : ℕ} (P : WRP.Presentation Step Step) (hB : 1 ≤ B)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (q_U q_D : ℕ) (hd : 0 < P.d) :
    ∃ pstar_mS : ℕ, 1 ≤ pstar_mS ∧
      ∀ n i, AffineOnResiduesAtZ pstar_mS (fun mS => selB B q_U q_D P Mc n hd mS i) := by
  classical
  obtain ⟨pstar, hpstar1, hcert⟩ := coordCands_period_uniform P hB Mc q_U q_D
  refine ⟨pstar, hpstar1, fun n i => ?_⟩
  have hgate : ∀ gf ∈ selCands B q_U q_D P Mc n, SliceOrder.EventuallyPeriodic gf.1 pstar := by
    intro gf hgf
    simp only [selCands, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hgf
    obtain ⟨c, _, t, htmem, ds, hdsmem, rfl⟩ := hgf
    have hwin : t + B ≤ n := by rw [Finset.mem_Icc] at htmem; omega
    obtain ⟨p, _, hpdvd, hEP, _⟩ := hcert c ds hdsmem t n hwin
    exact SliceDstar.EP_of_dvd hEP hpdvd
  have haff : ∀ gf ∈ selCands B q_U q_D P Mc n, ∀ j,
      AffineOnResiduesAtZ pstar (fun mS => gf.2 mS j) := by
    intro gf hgf j
    simp only [selCands, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hgf
    obtain ⟨c, _, t, htmem, ds, hdsmem, rfl⟩ := hgf
    have hwin : t + B ≤ n := by rw [Finset.mem_Icc] at htmem; omega
    obtain ⟨p, hp1, hpdvd, _, hAff⟩ := hcert c ds hdsmem t n hwin
    exact (hAff j).of_dvd hp1 hpdvd hpstar1
  have hBIGaff : ∀ j, AffineOnResiduesAtZ pstar (fun mS => bigDom B q_U q_D P Mc n hd mS j) := by
    intro j
    by_cases hj : j = ⟨0, hd⟩
    · have heq : (fun mS => bigDom B q_U q_D P Mc n hd mS j)
          = (fun mS => (((selCands B q_U q_D P Mc n).map (fun gf => fun mS => gf.2 mS ⟨0, hd⟩)).map
              (fun f => f mS)).foldr max 0 + 1) := by
        funext mS
        simp only [bigDom, hj, ↓reduceIte, List.map_map, Function.comp_def]
      rw [heq]
      exact (affineOnResiduesAtZ_listMax hpstar1
        ((selCands B q_U q_D P Mc n).map (fun gf => fun mS => gf.2 mS ⟨0, hd⟩))
        (fun f hf => by
          rw [List.mem_map] at hf
          obtain ⟨gf, hgf, rfl⟩ := hf
          exact haff gf hgf ⟨0, hd⟩)).add hpstar1 (AffineOnResiduesAtZ.const pstar 1)
    · have heq : (fun mS => bigDom B q_U q_D P Mc n hd mS j) = (fun _ => (0 : ℤ)) := by
        funext mS; simp only [bigDom, if_neg hj]
      rw [heq]; exact AffineOnResiduesAtZ.const pstar 0
  show AffineOnResiduesAtZ pstar (fun mS => lexMinList (bigDom B q_U q_D P Mc n hd ::
    (selCands B q_U q_D P Mc n).map
      (fun gf => fun mS => if gf.1 mS then gf.2 mS else bigDom B q_U q_D P Mc n hd mS)) mS i)
  exact gated_lexMin_affine_at hpstar1 (selCands B q_U q_D P Mc n) hgate haff
    (bigDom B q_U q_D P Mc n hd) hBIGaff i

/-! ## d3.4 content core — step 1: the uniform `l`-direction (depth) rank recurrence

The boundary collapse (`sufStretch_boundary_eq_coordCand`) runs `selBvec_le_member` in the DEPTH
direction at a period `lcm(depth-recurrence, gate-cycle)`.  For that `lcm` to be `mS`-FREE (so the
shallow/deep `coordCands` band width `q_D` is `mS`-free), the depth-recurrence period must itself be
`mS,n`-free.  `sufStretch_formula_rankAffine_l` (`CopiedRank`) hides its period inside `RankAffine`, and
that period is `mS,n`-DEPENDENT (it comes from `iterate_eventuallyPeriodic` on the start
`U^mS (UD)^n`).  Here we re-expose it with the start-FREE `endofunction_EP_mul` on the `D`-step, so one
`p_D` (depending only on `s.A`) serves every `mS, n` — the slope may move with `mS,n`, the period may
not.  (The prefix `p_U` is already `mS,n`-free via `prefStretch_formula_rankAffine_q`.) -/

/-- **Tail-run decomposition**: the prefix-rank of `pre ++ x^N` over its whole length is the rank read
over `pre` plus the partial sum of block-weights of the `x`-block iterate started at the post-`pre`
state.  The tail-side mirror of the `hdecomp` step inside `prefixRank_run_affine_mS_uniform`. -/
theorem prefixRank_tail_decomp {Alpha : Type*} {d : ℕ} (A : RankSource Alpha d) (x : Alpha)
    (pre : List Alpha) (N : ℕ) :
    A.prefixRank (pre ++ List.replicate N x) (pre ++ List.replicate N x).length
      = (List.foldl (SliceRank.rankStep A) (A.q0, 0) pre).2
        + ∑ i ∈ Finset.range N,
            SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i] (List.foldl A.δ A.q0 pre)) := by
  rw [SliceRank.prefixRank_eq_foldl, List.foldl_append]
  obtain ⟨st, rk, hpr⟩ :
      ∃ st rk, List.foldl (SliceRank.rankStep A) (A.q0, 0) pre = (st, rk) := ⟨_, _, rfl⟩
  have hst : st = List.foldl A.δ A.q0 pre := by
    rw [← SliceRank.rankStep_fst A A.q0 0 pre, hpr]
  rw [hpr, SliceRank.rankStep_snd_add]
  have hflat : List.replicate N x = (List.replicate N [x]).flatten :=
    (CopiedRank.flatten_replicate_singleton x N).symm
  rw [hflat, SliceRank.foldl_rankStep_replicate_snd A [x] st 0 N, zero_add, hst]

/-- **Uniform `l`-direction recurrence of a suffix-stretch summand FORMULA** (d3.4 content core, step 1):
one period `p_D`, depending ONLY on the summand's automaton `s.A` (`mS,n`-FREE), serves the depth
recurrence at EVERY `mS, n`.  The slope `P` may depend on `mS, n` (it is the per-cycle rank increment),
but the period does not.  Built with the start-FREE `endofunction_EP_mul` on the `D`-step (in place of
the start-specific `iterate_eventuallyPeriodic` used by `sufStretch_formula_rankAffine_l`), so the
boundary collapse can take an `lcm` with the (machine-only) gate cycle to one `mS`-free `q_D`. -/
theorem sufStretch_formula_rankAffine_l_uniform {k : ℕ} (s : Summand Step d k) :
    ∃ p_D, 1 ≤ p_D ∧ ∀ mS n, ∃ (m : ℕ) (P : Fin d → ℤ), ∀ l, m ≤ l →
      ( s.coeff • s.A.prefixRank
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1 + p_D) D)
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten
            ++ List.replicate (l + 1 + p_D) D).length
        + s.β (List.foldl s.A.δ
            ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
            (List.replicate (l + 1 + p_D) D)) D )
      = ( s.coeff • s.A.prefixRank
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten
            ++ List.replicate (l + 1) D).length
        + s.β (List.foldl s.A.δ
            ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
            (List.replicate (l + 1) D)) D )
      + P := by
  have := s.A.fintypeQ
  obtain ⟨mD, pD, hpD, hcyc⟩ := endofunction_EP_mul (fun q => s.A.δ q D)
  refine ⟨pD, hpD, fun mS n => ?_⟩
  set pre : List Step := List.replicate mS U ++ (List.replicate n [U, D]).flatten with hpre
  have hstpre : (fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U))
      = List.foldl s.A.δ s.A.q0 pre := by
    rw [hpre, List.foldl_append, SliceMSO.foldl_replicate_flatten]
  set stpre : s.A.Q := List.foldl s.A.δ s.A.q0 pre with hstdef
  have hbsD : SliceRank.blockStep s.A [D] = fun q => s.A.δ q D := by funext q; rfl
  have hgper : ∀ i, mD ≤ i →
      SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[i + pD] stpre)
        = SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[i] stpre) := by
    intro i hi
    rw [hbsD]
    have := hcyc 1 i hi
    rw [show i + pD * 1 = i + pD by ring] at this
    rw [this]
  set Δ : Fin d → ℤ := ∑ j ∈ Finset.Ico mD (mD + pD),
    SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[j] stpre) with hΔ
  refine ⟨mD, s.coeff • Δ, fun l hl => ?_⟩
  have hPA : s.A.prefixRank
      (pre ++ List.replicate (l + 1 + pD) D) (pre ++ List.replicate (l + 1 + pD) D).length
      = s.A.prefixRank (pre ++ List.replicate (l + 1) D) (pre ++ List.replicate (l + 1) D).length
        + Δ := by
    rw [prefixRank_tail_decomp s.A D pre (l + 1 + pD), prefixRank_tail_decomp s.A D pre (l + 1),
      SliceAutomata.partialSum_recurrence'
        (fun i => SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[i] stpre)) mD pD hgper
        (l + 1) (by omega), ← hΔ]
    abel
  have hPB : s.β (List.foldl s.A.δ stpre (List.replicate (l + 1 + pD) D)) D
      = s.β (List.foldl s.A.δ stpre (List.replicate (l + 1) D)) D := by
    rw [CopiedRank.foldl_replicate_iterate s.A.δ D stpre (l + 1 + pD),
      CopiedRank.foldl_replicate_iterate s.A.δ D stpre (l + 1)]
    have hc := hcyc 1 (l + 1) (by omega)
    rw [Nat.mul_one] at hc
    rw [hc]
  rw [hstpre, hPB, hPA, smul_add]
  abel

/-! ## d3.4 content core — step 1b: the cell-level uniform depth recurrence

`selBvec_le_member` (step 4) consumes a `ℤ^d`-vector depth recurrence `F(m+r+p·k) = F(m+r) + k·P` at a
single period `p`.  For that `p` to be `mS`-free we expose the period.  `SliceRankAtom.RankAffine` hides
its period in `∃p` (and that period is `mS,n`-dependent), so we introduce `RankAffineAt Q` (period `Q` a
parameter) with the few combinators a list-sum at a COMMON period needs, then sum the per-summand
uniform recurrences (`sufStretch_formula_rankAffine_l_uniform`) at the product period. -/

/-- A `ℤ^d`-valued sequence is **affine-on-residues at the EXPOSED period `Q`**.  Unlike
`SliceRankAtom.RankAffine` (period hidden in `∃p`), `Q` is a parameter, so list-sums can be taken at a
COMMON period (the product of per-term periods). -/
def RankAffineAt (Q : ℕ) (F : ℕ → Fin d → ℤ) : Prop :=
  ∃ (m : ℕ) (P : Fin d → ℤ), ∀ l, m ≤ l → F (l + Q) = F l + P

theorem RankAffineAt.const (Q : ℕ) (v : Fin d → ℤ) : RankAffineAt Q (fun _ => v) :=
  ⟨0, 0, fun _ _ => by simp⟩

theorem RankAffineAt.add {Q : ℕ} {F G : ℕ → Fin d → ℤ}
    (hF : RankAffineAt Q F) (hG : RankAffineAt Q G) :
    RankAffineAt Q (fun l => F l + G l) := by
  obtain ⟨mF, PF, hF⟩ := hF
  obtain ⟨mG, PG, hG⟩ := hG
  refine ⟨max mF mG, PF + PG, fun l hl => ?_⟩
  show F (l + Q) + G (l + Q) = (F l + G l) + (PF + PG)
  rw [hF l (le_of_max_le_left hl), hG l (le_of_max_le_right hl)]; abel

/-- Lift the period of a `RankAffineAt` to any multiple (via `RankAffine.iterate`). -/
theorem RankAffineAt.of_dvd {Q : ℕ} {F : ℕ → Fin d → ℤ} {p : ℕ}
    (h : RankAffineAt p F) (hpQ : p ∣ Q) : RankAffineAt Q F := by
  obtain ⟨m, P, hrec⟩ := h
  obtain ⟨k, rfl⟩ := hpQ
  exact ⟨m, k • P, fun l hl => SliceRankAtom.RankAffine.iterate hrec l k hl⟩

theorem RankAffineAt.listSum {ι : Type*} (L : List ι) (Q : ℕ) (g : ι → ℕ → Fin d → ℤ)
    (h : ∀ i ∈ L, RankAffineAt Q (g i)) :
    RankAffineAt Q (fun l => (L.map (fun i => g i l)).sum) := by
  induction L with
  | nil => simpa using RankAffineAt.const Q (0 : Fin d → ℤ)
  | cons a L' ih =>
      have ha := h a (List.mem_cons.mpr (Or.inl rfl))
      have ih' := ih (fun i hi => h i (List.mem_cons.mpr (Or.inr hi)))
      obtain ⟨m, P, hrec⟩ := RankAffineAt.add ha ih'
      exact ⟨m, P, fun l hl => by simpa [List.map_cons, List.sum_cons] using hrec l hl⟩

/-- **The CELL rank as a function of the suffix depth `l` is `RankAffineAt` a UNIFORM period `Q`**
(d3.4 content core, step 1b): one period `Q` — depending only on `P, c, j0` (`mS,n,ī0`-FREE) — serves
the cell-rank depth recurrence (coord `j0` moving, others fixed `ī0`) at EVERY `ī0, mS, n`.  `Q` is the
product over `κ.summands` of the per-summand `mS,n`-free periods from
`sufStretch_formula_rankAffine_l_uniform`.  The agreement leg (formula `= rank` on `l < mS-1`) is the
verbatim `rank_cell_sufStretch_rankAffine_l` argument.  This `F` feeds `selBvec_le_member` in step 4. -/
theorem rank_cell_sufStretch_rankAffine_l_uniform (P : WRP.Presentation Step Step)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) :
    ∃ Q, 1 ≤ Q ∧ ∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n : ℕ),
      ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAt Q F ∧
        (∀ l, l < mS - 1 → P.rank c (copiedSlice mS n)
          (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  choose pf hpf using fun s : Summand Step P.d (P.toPoly.arity c) =>
    sufStretch_formula_rankAffine_l_uniform s
  refine ⟨(κ.summands.map pf).prod, ?_, fun ī0 mS n => ?_⟩
  · exact List.one_le_prod_of_one_le (by
      intro x hx; obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx; exact (hpf s).1)
  · refine ⟨fun l => κ.c0 + (κ.summands.map (fun s =>
        if s.π = j0 then
          s.coeff • s.A.prefixRank
              (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
              (List.replicate mS U ++ (List.replicate n [U, D]).flatten
                ++ List.replicate (l + 1) D).length
            + s.β (List.foldl s.A.δ
                ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
                (List.replicate (l + 1) D)) D
        else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π)))).sum, ?_, ?_⟩
    · -- period leg: sum the per-summand uniform recurrences at the product period
      refine RankAffineAt.add (RankAffineAt.const _ _)
        (RankAffineAt.listSum κ.summands _ _ (fun s _ => ?_))
      by_cases hπ : s.π = j0
      · have hpQ : pf s ∣ (κ.summands.map pf).prod := List.dvd_prod (by
          exact List.mem_map.mpr ⟨s, by assumption, rfl⟩)
        obtain ⟨m, Pv, hrec⟩ := (hpf s).2 mS n
        have hform : RankAffineAt (pf s)
            (fun l => if s.π = j0 then
              s.coeff • s.A.prefixRank
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten
                    ++ List.replicate (l + 1) D).length
                + s.β (List.foldl s.A.δ
                    ((fun q => List.foldl s.A.δ q [U, D])^[n]
                      (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
                    (List.replicate (l + 1) D)) D
              else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π))) := by
          refine ⟨m, Pv, fun l hl => ?_⟩
          simp only [if_pos hπ]
          rw [show l + pf s + 1 = l + 1 + pf s from by omega]
          exact hrec l hl
        exact hform.of_dvd hpQ
      · have : (fun l => if s.π = j0 then
              s.coeff • s.A.prefixRank
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten
                    ++ List.replicate (l + 1) D).length
                + s.β (List.foldl s.A.δ
                    ((fun q => List.foldl s.A.δ q [U, D])^[n]
                      (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
                    (List.replicate (l + 1) D)) D
              else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π)))
            = (fun _ => s.eval (copiedSlice mS n) (fun _ => ī0 (s.π))) := by
          funext l; simp only [if_neg hπ]
        rw [this]; exact RankAffineAt.const _ _
    · -- agreement leg (verbatim rank_cell_sufStretch_rankAffine_l)
      intro l hl
      rw [hκ (copiedSlice mS n) _, SliceFamilyRank.rankTerm_eval_proj]
      funext c'
      simp only [Pi.add_apply]
      rw [SliceFamilyRank.list_sum_pi_apply]
      refine congrArg (κ.c0 c' + ·) (congrArg List.sum (List.map_congr_left (fun s _ => ?_)))
      by_cases hπ : s.π = j0
      · rw [if_pos hπ, hπ, Function.update_self]
        exact congrFun (summand_copied_sufStretch_eq s mS l hl n) c'
      · rw [if_neg hπ, Function.update_of_ne hπ]

/-! ## d3.4 step 2 — the LINCHPIN: gate invariance under a depth slide of one boundary coord

The mS-direction collapse must move a cell's MIDDLE-band suffix (resp. prefix) coordinates onto a
bounded representative without changing the gate.  Unlike the n-direction (a uniform whole-base group
shift), the depth collapse is per-coordinate, so a naive move could slide one coord's mark across
another's and change the foldl.  The resolution: each move stays inside a CLEAR sub-window `[s,e)` of
the growing run holding only the moving coord, and shifts its depth by a multiple of the unmarked
machine cycle `p` while every in-window gap stays `≥ m`.  Then the gate is preserved.

The whole argument collapses to a 4-line abstract identity, `iterate_mark_slide`: a marked step `g`
between two unmarked-`f` runs whose gaps differ by `p*κ` (both `≥ m`) is invariant
(`f^[R] (g (f^[A] q)) = f^[R'] (g (f^[A'] q))`).  `foldl_window_slide` lifts it to one clear `markSeg`
window; the two capstones (`accepts_copiedSlice_suf_shift` / `_pref_shift`) wrap it with
`markAtN_copiedSlice` + `markSeg_congr_outside` (the untouched U-prefix / middle / D-suffix segments are
identical between the source and target tuples). -/

/-- **Abstract single-mark slide.**  A marked transition `g` sandwiched between two unmarked-`f` runs
whose left/right gaps differ by a common multiple `p*κ` of the period (and stay `≥ m`) leaves the
composite state unchanged. -/
theorem iterate_mark_slide {Q : Type*} (f g : Q → Q) (m p : ℕ)
    (hper : ∀ κ b, m ≤ b → f^[b + p * κ] = f^[b])
    {A R A' R' κ : ℕ}
    (hA' : A' = A + p * κ) (hR : R = R' + p * κ) (hA : m ≤ A) (hR' : m ≤ R')
    (q : Q) :
    f^[R] (g (f^[A] q)) = f^[R'] (g (f^[A'] q)) := by
  have e1 : f^[A'] q = f^[A] q := by rw [hA', hper κ A hA]
  have e2 : f^[R] = f^[R'] := by rw [hR, hper κ R' hR']
  rw [e1, e2]

/-- **Single-mark clear-window decomposition of `markSeg`.**  Over a `len`-letter run of `x`s at offset
`off` in which the ONLY in-window mark is coord `j0` (at relative depth `a`), the marked segment factors
as an unmarked left run, the single marked letter (bit `j0` only), and an unmarked right run. -/
theorem markSeg_single_window {k : ℕ} (x : Step) (ī : Fin k → ℕ) (j0 : Fin k)
    (off a len : ℕ) (ha : a < len) (hj0 : ī j0 = off + a)
    (hclear : ∀ i, i ≠ j0 → ī i < off ∨ off + len ≤ ī i) :
    markSeg k (List.replicate len x) ī off
      = unmark k (List.replicate a x)
        ++ (mkLetter k x (fun i => decide (i = j0))
              :: unmark k (List.replicate (len - a - 1) x)) := by
  have hsplit : List.replicate len x
      = List.replicate a x ++ (x :: List.replicate (len - a - 1) x) := by
    rw [← List.replicate_succ, ← List.replicate_add]
    congr 1; omega
  rw [hsplit, markSeg_append, List.length_replicate]
  congr 1
  · -- left part is unmarked
    apply markSeg_unmarked
    intro i
    rw [List.length_replicate]
    by_cases hi : i = j0
    · subst hi; right; omega
    · rcases hclear i hi with h | h
      · left; exact h
      · right; omega
  · -- marked letter :: right part
    rw [markSeg_cons]
    congr 1
    · -- the marked letter's bit vector is exactly `{j0}`
      congr 1
      funext i
      simp only [bitsAt]
      by_cases hi : i = j0
      · subst hi; rw [hj0]; simp
      · rw [decide_eq_false (by
          rcases hclear i hi with h | h
          · omega
          · omega), decide_eq_false hi]
    · -- right part is unmarked
      apply markSeg_unmarked
      intro i
      rw [List.length_replicate]
      by_cases hi : i = j0
      · subst hi; left; omega
      · rcases hclear i hi with h | h
        · left; omega
        · right; omega

/-- The foldl over a single-mark clear window, in the `f^[R] (g (f^[A] q))` slide shape. -/
theorem foldl_markSeg_single_window {k : ℕ} (M : DetAuto (MarkedN k)) (x : Step) (ī : Fin k → ℕ)
    (j0 : Fin k) (off a len : ℕ) (ha : a < len) (hj0 : ī j0 = off + a)
    (hclear : ∀ i, i ≠ j0 → ī i < off ∨ off + len ≤ ī i) (q : M.Q) :
    List.foldl M.δ q (markSeg k (List.replicate len x) ī off)
      = (fun s => M.δ s (mkLetter k x (fun _ => false)))^[len - a - 1]
          (M.δ ((fun s => M.δ s (mkLetter k x (fun _ => false)))^[a] q)
               (mkLetter k x (fun i => decide (i = j0)))) := by
  rw [markSeg_single_window x ī j0 off a len ha hj0 hclear, List.foldl_append, List.foldl_cons]
  have hunmark : ∀ (b : ℕ), unmark k (List.replicate b x)
      = List.replicate b (mkLetter k x (fun _ => false)) := by
    intro b; rw [unmark, List.map_replicate]
  rw [hunmark, hunmark, foldl_replicate_eq_iterate, foldl_replicate_eq_iterate]

/-- **The window slide workhorse.**  Within a clear window `x^winLen` at offset `winStart` holding only
coord `j0`, sliding `j0` from relative depth `a` to `a'` (differing by `p*κ`, all in-window gaps `≥ m`)
leaves the foldl from any start state unchanged. -/
theorem foldl_window_slide {k : ℕ} (M : DetAuto (MarkedN k)) (x : Step)
    (ī ī' : Fin k → ℕ) (j0 : Fin k) (winStart winLen a a' κ m p : ℕ)
    (hper : ∀ κ b, m ≤ b → (fun s => M.δ s (mkLetter k x (fun _ => false)))^[b + p * κ]
                          = (fun s => M.δ s (mkLetter k x (fun _ => false)))^[b])
    (hsame : ∀ i, i ≠ j0 → ī i = ī' i)
    (hj0 : ī j0 = winStart + a) (hj0' : ī' j0 = winStart + a')
    (ha : a < winLen) (ha' : a' < winLen)
    (hclear : ∀ i, i ≠ j0 → ī i < winStart ∨ winStart + winLen ≤ ī i)
    (hgapA : m ≤ a) (hgapA' : m ≤ a') (hgapR : m ≤ winLen - 1 - a) (hgapR' : m ≤ winLen - 1 - a')
    (hshift : a' = a + p * κ ∨ a = a' + p * κ) (qstart : M.Q) :
    List.foldl M.δ qstart (markSeg k (List.replicate winLen x) ī winStart)
      = List.foldl M.δ qstart (markSeg k (List.replicate winLen x) ī' winStart) := by
  have hclear' : ∀ i, i ≠ j0 → ī' i < winStart ∨ winStart + winLen ≤ ī' i := by
    intro i hi; rw [← hsame i hi]; exact hclear i hi
  rw [foldl_markSeg_single_window M x ī j0 winStart a winLen ha hj0 hclear,
      foldl_markSeg_single_window M x ī' j0 winStart a' winLen ha' hj0' hclear']
  rcases hshift with h | h
  · exact iterate_mark_slide (fun s => M.δ s (mkLetter k x (fun _ => false)))
      (fun s => M.δ s (mkLetter k x (fun i => decide (i = j0)))) m p hper
      (A := a) (R := winLen - a - 1) (A' := a') (R' := winLen - a' - 1) (κ := κ)
      h (by omega) hgapA (by omega) qstart
  · exact (iterate_mark_slide (fun s => M.δ s (mkLetter k x (fun _ => false)))
      (fun s => M.δ s (mkLetter k x (fun i => decide (i = j0)))) m p hper
      (A := a') (R := winLen - a' - 1) (A' := a) (R' := winLen - a - 1) (κ := κ)
      h (by omega) hgapA' (by omega) qstart).symm

/-- **Gate invariance under a suffix-coord depth slide (the linchpin, suffix side).**  Moving coord
`j0` (a D-suffix coord at depth `a`) to depth `a'` inside a clear sub-window `[s,e)` of the D-suffix,
with the depths differing by `p*κ` (`p` = the unmarked-D machine cycle) and all in-window gaps `≥ m`,
preserves cell acceptance on the copied slice. -/
theorem accepts_copiedSlice_suf_shift {k : ℕ} (M : DetAuto (MarkedN k)) (mS n : ℕ) (hm : 1 ≤ mS)
    (ī ī' : Fin k → ℕ) (j0 : Fin k) (s e a a' κ m p : ℕ)
    (hper : ∀ κ b, m ≤ b → (fun st => M.δ st (mkLetter k D (fun _ => false)))^[b + p * κ]
                          = (fun st => M.δ st (mkLetter k D (fun _ => false)))^[b])
    (hsame : ∀ i, i ≠ j0 → ī i = ī' i)
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hj0 : ī j0 = mS + 2 * n + 1 + a) (hj0' : ī' j0 = mS + 2 * n + 1 + a')
    (hclear : ∀ i, i ≠ j0 → ī i < mS + 2 * n + 1 + s ∨ mS + 2 * n + 1 + e ≤ ī i)
    (hgapA : m ≤ a - s) (hgapA' : m ≤ a' - s) (hgapR : m ≤ e - 1 - a) (hgapR' : m ≤ e - 1 - a')
    (hshift : a' = a + p * κ ∨ a = a' + p * κ) :
    M.accepts (markAtN k (copiedSlice mS n) ī) ↔ M.accepts (markAtN k (copiedSlice mS n) ī') := by
  -- boundary segments (U-prefix, middle) are identical: j0 lives in the D-suffix
  have hUpre : markSeg k (List.replicate (mS - 1) U) ī 0
      = markSeg k (List.replicate (mS - 1) U) ī' 0 := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; rw [List.length_replicate]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    · exact Or.inl (hsame i hi)
  have hMid : markSeg k (wrappedFlat n) ī (mS - 1) = markSeg k (wrappedFlat n) ī' (mS - 1) := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; rw [length_wrappedFlat]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    · exact Or.inl (hsame i hi)
  -- D-suffix split: Dleft (clear) ++ Dwin (the slide window) ++ Dright (clear)
  have hDsplit : ∀ (j : Fin k → ℕ),
      markSeg k (List.replicate (mS - 1) D) j (mS + 2 * n + 1)
      = markSeg k (List.replicate s D) j (mS + 2 * n + 1)
        ++ markSeg k (List.replicate (e - s) D) j (mS + 2 * n + 1 + s)
        ++ markSeg k (List.replicate (mS - 1 - e) D) j (mS + 2 * n + 1 + e) := by
    intro j
    have hrep : List.replicate (mS - 1) D
        = (List.replicate s D ++ List.replicate (e - s) D) ++ List.replicate (mS - 1 - e) D := by
      rw [List.append_assoc, ← List.replicate_add, ← List.replicate_add]; congr 1; omega
    rw [hrep, markSeg_append, markSeg_append, List.length_replicate, List.length_append,
      List.length_replicate, List.length_replicate]
    congr 2
    omega
  have hDleft : markSeg k (List.replicate s D) ī (mS + 2 * n + 1)
      = markSeg k (List.replicate s D) ī' (mS + 2 * n + 1) := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; rw [List.length_replicate]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    · exact Or.inl (hsame i hi)
  have hDright : markSeg k (List.replicate (mS - 1 - e) D) ī (mS + 2 * n + 1 + e)
      = markSeg k (List.replicate (mS - 1 - e) D) ī' (mS + 2 * n + 1 + e) := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · exact Or.inl (hsame i hi)
  -- the window slide
  have hwin : List.foldl M.δ
        (List.foldl M.δ M.q0
          (markSeg k (List.replicate (mS - 1) U) ī' 0 ++ markSeg k (wrappedFlat n) ī' (mS - 1)
            ++ markSeg k (List.replicate s D) ī' (mS + 2 * n + 1)))
        (markSeg k (List.replicate (e - s) D) ī (mS + 2 * n + 1 + s))
      = List.foldl M.δ
        (List.foldl M.δ M.q0
          (markSeg k (List.replicate (mS - 1) U) ī' 0 ++ markSeg k (wrappedFlat n) ī' (mS - 1)
            ++ markSeg k (List.replicate s D) ī' (mS + 2 * n + 1)))
        (markSeg k (List.replicate (e - s) D) ī' (mS + 2 * n + 1 + s)) := by
    apply foldl_window_slide M D ī ī' j0 (mS + 2 * n + 1 + s) (e - s) (a - s) (a' - s) κ m p hper hsame
    · rw [hj0]; omega
    · rw [hj0']; omega
    · omega
    · omega
    · intro i hi; rcases hclear i hi with h | h
      · left; omega
      · right; omega
    · exact hgapA
    · exact hgapA'
    · omega
    · omega
    · rcases hshift with h | h
      · left; omega
      · right; omega
  -- assemble
  have key : List.foldl M.δ M.q0 (markAtN k (copiedSlice mS n) ī)
      = List.foldl M.δ M.q0 (markAtN k (copiedSlice mS n) ī') := by
    rw [markAtN_copiedSlice k mS n hm, markAtN_copiedSlice k mS n hm, hUpre, hMid,
      hDsplit ī, hDsplit ī', hDleft, hDright]
    have hL : ∀ (W : List (MarkedN k)),
        List.foldl M.δ M.q0 (markSeg k (List.replicate (mS - 1) U) ī' 0
            ++ markSeg k (wrappedFlat n) ī' (mS - 1)
            ++ (markSeg k (List.replicate s D) ī' (mS + 2 * n + 1) ++ W
                ++ markSeg k (List.replicate (mS - 1 - e) D) ī' (mS + 2 * n + 1 + e)))
          = List.foldl M.δ (List.foldl M.δ
              (List.foldl M.δ M.q0 (markSeg k (List.replicate (mS - 1) U) ī' 0
                ++ markSeg k (wrappedFlat n) ī' (mS - 1)
                ++ markSeg k (List.replicate s D) ī' (mS + 2 * n + 1))) W)
              (markSeg k (List.replicate (mS - 1 - e) D) ī' (mS + 2 * n + 1 + e)) := by
      intro W
      rw [← List.append_assoc, ← List.append_assoc, List.foldl_append, List.foldl_append]
    rw [hL, hL]
    exact congrArg
      (fun st => List.foldl M.δ st (markSeg k (List.replicate (mS - 1 - e) D) ī' (mS + 2 * n + 1 + e)))
      hwin
  have hacc : M.accepts (markAtN k (copiedSlice mS n) ī)
      = M.accepts (markAtN k (copiedSlice mS n) ī') := by
    unfold DetAuto.accepts; rw [key]
  rw [hacc]

/-- Cell-gate wrapper for `accepts_copiedSlice_suf_shift`: if the two cell
tuples differ only by sliding coordinate `j0` inside a clear D-suffix window,
then `gateF` transfers to the target descriptor. -/
theorem gateF_suf_shift {B k : ℕ} (M : DetAuto (MarkedN k)) (mS n t : ℕ) (hm : 1 ≤ mS)
    (rs rs' : Fin k → RegionSpecF B) (j0 : Fin k) (s e a a' κ m p : ℕ)
    (hper : ∀ κ b, m ≤ b → (fun st => M.δ st (mkLetter k D (fun _ => false)))^[b + p * κ]
                          = (fun st => M.δ st (mkLetter k D (fun _ => false)))^[b])
    (hsame : ∀ i, i ≠ j0 → cellTupleF rs mS t n i = cellTupleF rs' mS t n i)
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hj0 : cellTupleF rs mS t n j0 = mS + 2 * n + 1 + a)
    (hj0' : cellTupleF rs' mS t n j0 = mS + 2 * n + 1 + a')
    (hclear : ∀ i, i ≠ j0 →
      cellTupleF rs mS t n i < mS + 2 * n + 1 + s ∨
        mS + 2 * n + 1 + e ≤ cellTupleF rs mS t n i)
    (hgapA : m ≤ a - s) (hgapA' : m ≤ a' - s)
    (hgapR : m ≤ e - 1 - a) (hgapR' : m ≤ e - 1 - a')
    (hshift : a' = a + p * κ ∨ a = a' + p * κ)
    (hgate : gateF M rs mS t n) :
    gateF M rs' mS t n := by
  unfold gateF at hgate ⊢
  exact (accepts_copiedSlice_suf_shift M mS n hm (cellTupleF rs mS t n)
    (cellTupleF rs' mS t n) j0 s e a a' κ m p hper hsame hse heL hsa hae
    hsa' hae' hj0 hj0' hclear hgapA hgapA' hgapR hgapR' hshift).mp hgate

/-- Specialised suffix move for the descriptor update used by the general
collapse induction: replace coordinate `j0 = sufIdx a` by `sufIdx a'`.
All non-moving coordinates are fixed by `Function.update`; the caller supplies
the clear-window and gap facts. -/
theorem gateF_sufIdx_update_shift {B k : ℕ} (M : DetAuto (MarkedN k)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (rs : Fin k → RegionSpecF B) (j0 : Fin k)
    (s e a a' κ m p : ℕ)
    (hsrc : rs j0 = RegionSpecF.sufIdx a)
    (hper : ∀ κ b, m ≤ b → (fun st => M.δ st (mkLetter k D (fun _ => false)))^[b + p * κ]
                          = (fun st => M.δ st (mkLetter k D (fun _ => false)))^[b])
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hclear : ∀ i, i ≠ j0 →
      cellTupleF rs mS t n i < mS + 2 * n + 1 + s ∨
        mS + 2 * n + 1 + e ≤ cellTupleF rs mS t n i)
    (hgapA : m ≤ a - s) (hgapA' : m ≤ a' - s)
    (hgapR : m ≤ e - 1 - a) (hgapR' : m ≤ e - 1 - a')
    (hshift : a' = a + p * κ ∨ a = a' + p * κ)
    (hgate : gateF M rs mS t n) :
    gateF M (Function.update rs j0 (RegionSpecF.sufIdx a')) mS t n := by
  refine gateF_suf_shift M mS n t hm rs (Function.update rs j0 (RegionSpecF.sufIdx a'))
    j0 s e a a' κ m p hper ?_ hse heL hsa hae hsa' hae' ?_ ?_ hclear
    hgapA hgapA' hgapR hgapR' hshift hgate
  · intro i hi
    simp only [cellTupleF, Function.update_of_ne hi]
  · simp only [cellTupleF, hsrc, RegionSpecF.posAt]
  · simp only [cellTupleF, Function.update_self, RegionSpecF.posAt]

/-- Updating a descriptor coordinate to `sufIdx l` updates the corresponding
cell-tuple position to the copied-slice suffix position. -/
theorem cellTupleF_update_sufIdx {B k : ℕ} (rs : Fin k → RegionSpecF B)
    (j0 : Fin k) (mS t n l : ℕ) :
    cellTupleF (Function.update rs j0 (RegionSpecF.sufIdx l)) mS t n =
      Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l) := by
  funext i
  by_cases hi : i = j0
  · subst hi
    simp only [cellTupleF, Function.update_self, RegionSpecF.posAt]
  · simp only [cellTupleF, Function.update_of_ne hi]

/-- **Gate invariance under a prefix-coord depth slide (the linchpin, prefix side).**  Moving coord
`j0` (a U-prefix coord at depth `a`) to depth `a'` inside a clear sub-window `[s,e)` of the U-prefix,
with the depths differing by `p*κ` (`p` = the unmarked-U machine cycle) and all in-window gaps `≥ m`,
preserves cell acceptance on the copied slice. -/
theorem accepts_copiedSlice_pref_shift {k : ℕ} (M : DetAuto (MarkedN k)) (mS n : ℕ) (hm : 1 ≤ mS)
    (ī ī' : Fin k → ℕ) (j0 : Fin k) (s e a a' κ m p : ℕ)
    (hper : ∀ κ b, m ≤ b → (fun st => M.δ st (mkLetter k U (fun _ => false)))^[b + p * κ]
                          = (fun st => M.δ st (mkLetter k U (fun _ => false)))^[b])
    (hsame : ∀ i, i ≠ j0 → ī i = ī' i)
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hj0 : ī j0 = a) (hj0' : ī' j0 = a')
    (hclear : ∀ i, i ≠ j0 → ī i < s ∨ e ≤ ī i)
    (hgapA : m ≤ a - s) (hgapA' : m ≤ a' - s) (hgapR : m ≤ e - 1 - a) (hgapR' : m ≤ e - 1 - a')
    (hshift : a' = a + p * κ ∨ a = a' + p * κ) :
    M.accepts (markAtN k (copiedSlice mS n) ī) ↔ M.accepts (markAtN k (copiedSlice mS n) ī') := by
  -- middle and D-suffix segments are identical: j0 lives in the U-prefix
  have hMid : markSeg k (wrappedFlat n) ī (mS - 1) = markSeg k (wrappedFlat n) ī' (mS - 1) := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · exact Or.inl (hsame i hi)
  have hDsuf : markSeg k (List.replicate (mS - 1) D) ī (mS + 2 * n + 1)
      = markSeg k (List.replicate (mS - 1) D) ī' (mS + 2 * n + 1) := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · exact Or.inl (hsame i hi)
  -- U-prefix split: Uleft (clear) ++ Uwin (the slide window) ++ Uright (clear)
  have hUsplit : ∀ (j : Fin k → ℕ),
      markSeg k (List.replicate (mS - 1) U) j 0
      = markSeg k (List.replicate s U) j 0
        ++ markSeg k (List.replicate (e - s) U) j s
        ++ markSeg k (List.replicate (mS - 1 - e) U) j e := by
    intro j
    have hrep : List.replicate (mS - 1) U
        = (List.replicate s U ++ List.replicate (e - s) U) ++ List.replicate (mS - 1 - e) U := by
      rw [List.append_assoc, ← List.replicate_add, ← List.replicate_add]; congr 1; omega
    rw [hrep, markSeg_append, markSeg_append]
    simp only [List.length_append, List.length_replicate, Nat.zero_add]
    congr 2
    omega
  have hUleft : markSeg k (List.replicate s U) ī 0 = markSeg k (List.replicate s U) ī' 0 := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; rw [List.length_replicate]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    · exact Or.inl (hsame i hi)
  have hUright : markSeg k (List.replicate (mS - 1 - e) U) ī e
      = markSeg k (List.replicate (mS - 1 - e) U) ī' e := by
    apply markSeg_congr_outside
    intro i
    by_cases hi : i = j0
    · subst hi; right; exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · exact Or.inl (hsame i hi)
  -- the window slide
  have hwin : List.foldl M.δ (List.foldl M.δ M.q0 (markSeg k (List.replicate s U) ī' 0))
        (markSeg k (List.replicate (e - s) U) ī s)
      = List.foldl M.δ (List.foldl M.δ M.q0 (markSeg k (List.replicate s U) ī' 0))
        (markSeg k (List.replicate (e - s) U) ī' s) := by
    apply foldl_window_slide M U ī ī' j0 s (e - s) (a - s) (a' - s) κ m p hper hsame
    · rw [hj0]; omega
    · rw [hj0']; omega
    · omega
    · omega
    · intro i hi; rcases hclear i hi with h | h
      · left; omega
      · right; omega
    · exact hgapA
    · exact hgapA'
    · omega
    · omega
    · rcases hshift with h | h
      · left; omega
      · right; omega
  -- assemble
  have key : List.foldl M.δ M.q0 (markAtN k (copiedSlice mS n) ī)
      = List.foldl M.δ M.q0 (markAtN k (copiedSlice mS n) ī') := by
    rw [markAtN_copiedSlice k mS n hm, markAtN_copiedSlice k mS n hm, hMid, hDsuf,
      hUsplit ī, hUsplit ī', hUleft, hUright]
    simp only [List.foldl_append]
    rw [hwin]
  have hacc : M.accepts (markAtN k (copiedSlice mS n) ī)
      = M.accepts (markAtN k (copiedSlice mS n) ī') := by
    unfold DetAuto.accepts; rw [key]
  rw [hacc]

/-- Cell-gate wrapper for `accepts_copiedSlice_pref_shift`: if the two cell
tuples differ only by sliding coordinate `j0` inside a clear U-prefix window,
then `gateF` transfers to the target descriptor. -/
theorem gateF_pref_shift {B k : ℕ} (M : DetAuto (MarkedN k)) (mS n t : ℕ) (hm : 1 ≤ mS)
    (rs rs' : Fin k → RegionSpecF B) (j0 : Fin k) (s e a a' κ m p : ℕ)
    (hper : ∀ κ b, m ≤ b → (fun st => M.δ st (mkLetter k U (fun _ => false)))^[b + p * κ]
                          = (fun st => M.δ st (mkLetter k U (fun _ => false)))^[b])
    (hsame : ∀ i, i ≠ j0 → cellTupleF rs mS t n i = cellTupleF rs' mS t n i)
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hj0 : cellTupleF rs mS t n j0 = a)
    (hj0' : cellTupleF rs' mS t n j0 = a')
    (hclear : ∀ i, i ≠ j0 → cellTupleF rs mS t n i < s ∨ e ≤ cellTupleF rs mS t n i)
    (hgapA : m ≤ a - s) (hgapA' : m ≤ a' - s)
    (hgapR : m ≤ e - 1 - a) (hgapR' : m ≤ e - 1 - a')
    (hshift : a' = a + p * κ ∨ a = a' + p * κ)
    (hgate : gateF M rs mS t n) :
    gateF M rs' mS t n := by
  unfold gateF at hgate ⊢
  exact (accepts_copiedSlice_pref_shift M mS n hm (cellTupleF rs mS t n)
    (cellTupleF rs' mS t n) j0 s e a a' κ m p hper hsame hse heL hsa hae
    hsa' hae' hj0 hj0' hclear hgapA hgapA' hgapR hgapR' hshift).mp hgate

/-- Specialised prefix move for the descriptor update used by the general
collapse induction: replace coordinate `j0 = prefIdx a` by `prefIdx a'`.
All non-moving coordinates are fixed by `Function.update`; the caller supplies
the clear-window and gap facts. -/
theorem gateF_prefIdx_update_shift {B k : ℕ} (M : DetAuto (MarkedN k)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (rs : Fin k → RegionSpecF B) (j0 : Fin k)
    (s e a a' κ m p : ℕ)
    (hsrc : rs j0 = RegionSpecF.prefIdx a)
    (hper : ∀ κ b, m ≤ b → (fun st => M.δ st (mkLetter k U (fun _ => false)))^[b + p * κ]
                          = (fun st => M.δ st (mkLetter k U (fun _ => false)))^[b])
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hclear : ∀ i, i ≠ j0 → cellTupleF rs mS t n i < s ∨ e ≤ cellTupleF rs mS t n i)
    (hgapA : m ≤ a - s) (hgapA' : m ≤ a' - s)
    (hgapR : m ≤ e - 1 - a) (hgapR' : m ≤ e - 1 - a')
    (hshift : a' = a + p * κ ∨ a = a' + p * κ)
    (hgate : gateF M rs mS t n) :
    gateF M (Function.update rs j0 (RegionSpecF.prefIdx a')) mS t n := by
  refine gateF_pref_shift M mS n t hm rs (Function.update rs j0 (RegionSpecF.prefIdx a'))
    j0 s e a a' κ m p hper ?_ hse heL hsa hae hsa' hae' ?_ ?_ hclear
    hgapA hgapA' hgapR hgapR' hshift hgate
  · intro i hi
    simp only [cellTupleF, Function.update_of_ne hi]
  · simp only [cellTupleF, hsrc, RegionSpecF.posAt]
  · simp only [cellTupleF, Function.update_self, RegionSpecF.posAt]

/-- Updating a descriptor coordinate to `prefIdx q` updates the corresponding
cell-tuple position to the copied-slice prefix position. -/
theorem cellTupleF_update_prefIdx {B k : ℕ} (rs : Fin k → RegionSpecF B)
    (j0 : Fin k) (mS t n q : ℕ) :
    cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q)) mS t n =
      Function.update (cellTupleF rs mS t n) j0 q := by
  funext i
  by_cases hi : i = j0
  · subst hi
    simp only [cellTupleF, Function.update_self, RegionSpecF.posAt]
  · simp only [cellTupleF, Function.update_of_ne hi]


-- Threshold-EXPOSING per-summand variant: hoist `∃ mD` outside `∀ mS n` (binder reorder of
-- `sufStretch_formula_rankAffine_l_uniform`).  Both period p_D and threshold mD are mS,n-free.
theorem sufStretch_formula_rankAffine_l_uniform' {k : ℕ} (s : Summand Step d k) :
    ∃ p_D mD, 1 ≤ p_D ∧ ∀ mS n, ∃ (P : Fin d → ℤ), ∀ l, mD ≤ l →
      ( s.coeff • s.A.prefixRank
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1 + p_D) D)
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten
            ++ List.replicate (l + 1 + p_D) D).length
        + s.β (List.foldl s.A.δ
            ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
            (List.replicate (l + 1 + p_D) D)) D )
      = ( s.coeff • s.A.prefixRank
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
          (List.replicate mS U ++ (List.replicate n [U, D]).flatten
            ++ List.replicate (l + 1) D).length
        + s.β (List.foldl s.A.δ
            ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
            (List.replicate (l + 1) D)) D )
      + P := by
  have := s.A.fintypeQ
  obtain ⟨mD, pD, hpD, hcyc⟩ := endofunction_EP_mul (fun q => s.A.δ q D)
  refine ⟨pD, mD, hpD, fun mS n => ?_⟩
  set pre : List Step := List.replicate mS U ++ (List.replicate n [U, D]).flatten with hpre
  have hstpre : (fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U))
      = List.foldl s.A.δ s.A.q0 pre := by
    rw [hpre, List.foldl_append, SliceMSO.foldl_replicate_flatten]
  set stpre : s.A.Q := List.foldl s.A.δ s.A.q0 pre with hstdef
  have hbsD : SliceRank.blockStep s.A [D] = fun q => s.A.δ q D := by funext q; rfl
  have hgper : ∀ i, mD ≤ i →
      SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[i + pD] stpre)
        = SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[i] stpre) := by
    intro i hi
    rw [hbsD]
    have := hcyc 1 i hi
    rw [show i + pD * 1 = i + pD by ring] at this
    rw [this]
  set Δ : Fin d → ℤ := ∑ j ∈ Finset.Ico mD (mD + pD),
    SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[j] stpre) with hΔ
  refine ⟨s.coeff • Δ, fun l hl => ?_⟩
  have hPA : s.A.prefixRank
      (pre ++ List.replicate (l + 1 + pD) D) (pre ++ List.replicate (l + 1 + pD) D).length
      = s.A.prefixRank (pre ++ List.replicate (l + 1) D) (pre ++ List.replicate (l + 1) D).length
        + Δ := by
    rw [prefixRank_tail_decomp s.A D pre (l + 1 + pD), prefixRank_tail_decomp s.A D pre (l + 1),
      SliceAutomata.partialSum_recurrence'
        (fun i => SliceRank.blockWeight s.A [D] ((SliceRank.blockStep s.A [D])^[i] stpre)) mD pD hgper
        (l + 1) (by omega), ← hΔ]
    abel
  have hPB : s.β (List.foldl s.A.δ stpre (List.replicate (l + 1 + pD) D)) D
      = s.β (List.foldl s.A.δ stpre (List.replicate (l + 1) D)) D := by
    rw [CopiedRank.foldl_replicate_iterate s.A.δ D stpre (l + 1 + pD),
      CopiedRank.foldl_replicate_iterate s.A.δ D stpre (l + 1)]
    have hc := hcyc 1 (l + 1) (by omega)
    rw [Nat.mul_one] at hc
    rw [hc]
  rw [hstpre, hPB, hPA, smul_add]
  abel

/-! ### RankAffineAtFrom: threshold-EXPOSED affine-on-residues (period AND threshold parameters). -/

/-- `F` is affine-on-residues at period `Q` with the recurrence valid from the EXPOSED threshold `M`.
Unlike `RankAffineAt` (threshold hidden in `∃ m`), `M` is a parameter, so the d3.4 boundary collapse
can bound the shallow endpoint depth `M + r` against the mS-free band width `q_D`. -/
def RankAffineAtFrom (M Q : ℕ) (F : ℕ → Fin d → ℤ) : Prop :=
  ∃ P : Fin d → ℤ, ∀ l, M ≤ l → F (l + Q) = F l + P

theorem RankAffineAtFrom.const (M Q : ℕ) (v : Fin d → ℤ) : RankAffineAtFrom M Q (fun _ => v) :=
  ⟨0, fun _ _ => by simp⟩

theorem RankAffineAtFrom.mono {M M' Q : ℕ} {F : ℕ → Fin d → ℤ}
    (h : RankAffineAtFrom M Q F) (hMM' : M ≤ M') : RankAffineAtFrom M' Q F := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun l hl => hP l (le_trans hMM' hl)⟩

theorem RankAffineAtFrom.add {M Q : ℕ} {F G : ℕ → Fin d → ℤ}
    (hF : RankAffineAtFrom M Q F) (hG : RankAffineAtFrom M Q G) :
    RankAffineAtFrom M Q (fun l => F l + G l) := by
  obtain ⟨PF, hF⟩ := hF
  obtain ⟨PG, hG⟩ := hG
  refine ⟨PF + PG, fun l hl => ?_⟩
  show F (l + Q) + G (l + Q) = (F l + G l) + (PF + PG)
  rw [hF l hl, hG l hl]; abel

/-- Lift the period of a `RankAffineAtFrom` to any multiple (threshold unchanged). -/
theorem RankAffineAtFrom.of_dvd {M Q : ℕ} {F : ℕ → Fin d → ℤ} {p : ℕ}
    (h : RankAffineAtFrom M p F) (hpQ : p ∣ Q) : RankAffineAtFrom M Q F := by
  obtain ⟨P, hrec⟩ := h
  obtain ⟨k, rfl⟩ := hpQ
  exact ⟨k • P, fun l hl => SliceRankAtom.RankAffine.iterate hrec l k hl⟩

/-- A list-sum at a COMMON exposed threshold `M` and period `Q`. -/
theorem RankAffineAtFrom.listSum {ι : Type*} (L : List ι) (M Q : ℕ) (g : ι → ℕ → Fin d → ℤ)
    (h : ∀ i ∈ L, RankAffineAtFrom M Q (g i)) :
    RankAffineAtFrom M Q (fun l => (L.map (fun i => g i l)).sum) := by
  induction L with
  | nil => simpa using RankAffineAtFrom.const M Q (0 : Fin d → ℤ)
  | cons a L' ih =>
      have ha := h a (List.mem_cons.mpr (Or.inl rfl))
      have ih' := ih (fun i hi => h i (List.mem_cons.mpr (Or.inr hi)))
      obtain ⟨P, hrec⟩ := ha.add ih'
      exact ⟨P, fun l hl => by simpa [List.map_cons, List.sum_cons] using hrec l hl⟩

/-! ### Cell-level threshold-exposed recurrences (suffix + prefix). -/

/-- **Suffix cell rank, threshold EXPOSED** (Option-B of d3.4 step 3): the cell rank as a function of
suffix depth `l` is `RankAffineAtFrom M Q` at one `mS,n,ī0`-FREE period `Q` AND threshold `M` (both =
products / maxes over `κ.summands` of the `endofunction_EP_mul`-derived per-summand period / threshold). -/
theorem rank_cell_sufStretch_threshold_uniform (P : WRP.Presentation Step Step)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) :
    ∃ Q M, 1 ≤ Q ∧ ∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n : ℕ),
      ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom M Q F ∧
        (∀ l, l < mS - 1 → P.rank c (copiedSlice mS n)
          (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  choose pf mDf hpf using fun s : Summand Step P.d (P.toPoly.arity c) =>
    sufStretch_formula_rankAffine_l_uniform' s
  refine ⟨(κ.summands.map pf).prod, (κ.summands.map mDf).sum, ?_, fun ī0 mS n => ?_⟩
  · exact List.one_le_prod_of_one_le (by
      intro x hx; obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx; exact (hpf s).1)
  · set M := (κ.summands.map mDf).sum with hMdef
    refine ⟨fun l => κ.c0 + (κ.summands.map (fun s =>
        if s.π = j0 then
          s.coeff • s.A.prefixRank
              (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
              (List.replicate mS U ++ (List.replicate n [U, D]).flatten
                ++ List.replicate (l + 1) D).length
            + s.β (List.foldl s.A.δ
                ((fun q => List.foldl s.A.δ q [U, D])^[n] (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
                (List.replicate (l + 1) D)) D
        else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π)))).sum, ?_, ?_⟩
    · -- period+threshold leg
      refine (RankAffineAtFrom.const M _ κ.c0).add
        (RankAffineAtFrom.listSum κ.summands M _ _ (fun s hs => ?_))
      by_cases hπ : s.π = j0
      · have hpQ : pf s ∣ (κ.summands.map pf).prod := List.dvd_prod (by
          exact List.mem_map.mpr ⟨s, hs, rfl⟩)
        obtain ⟨Pv, hrec⟩ := (hpf s).2 mS n
        have hform : RankAffineAtFrom (mDf s) (pf s)
            (fun l => if s.π = j0 then
              s.coeff • s.A.prefixRank
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten
                    ++ List.replicate (l + 1) D).length
                + s.β (List.foldl s.A.δ
                    ((fun q => List.foldl s.A.δ q [U, D])^[n]
                      (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
                    (List.replicate (l + 1) D)) D
              else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π))) := by
          refine ⟨Pv, fun l hl => ?_⟩
          simp only [if_pos hπ]
          rw [show l + pf s + 1 = l + 1 + pf s from by omega]
          exact hrec l hl
        exact ((hform.of_dvd hpQ).mono
          (by rw [hMdef]; exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem (f := mDf) hs)))
      · have heq : (fun l => if s.π = j0 then
              s.coeff • s.A.prefixRank
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten ++ List.replicate (l + 1) D)
                  (List.replicate mS U ++ (List.replicate n [U, D]).flatten
                    ++ List.replicate (l + 1) D).length
                + s.β (List.foldl s.A.δ
                    ((fun q => List.foldl s.A.δ q [U, D])^[n]
                      (List.foldl s.A.δ s.A.q0 (List.replicate mS U)))
                    (List.replicate (l + 1) D)) D
              else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π)))
            = (fun _ => s.eval (copiedSlice mS n) (fun _ => ī0 (s.π))) := by
          funext l; simp only [if_neg hπ]
        rw [heq]; exact RankAffineAtFrom.const _ _ _
    · -- agreement leg (verbatim rank_cell_sufStretch_rankAffine_l_uniform)
      intro l hl
      rw [hκ (copiedSlice mS n) _, SliceFamilyRank.rankTerm_eval_proj]
      funext c'
      simp only [Pi.add_apply]
      rw [SliceFamilyRank.list_sum_pi_apply]
      refine congrArg (κ.c0 c' + ·) (congrArg List.sum (List.map_congr_left (fun s _ => ?_)))
      by_cases hπ : s.π = j0
      · rw [if_pos hπ, hπ, Function.update_self]
        exact congrFun (summand_copied_sufStretch_eq s mS l hl n) c'
      · rw [if_neg hπ, Function.update_of_ne hπ]

/-- **Prefix cell rank, threshold EXPOSED** (Option-B of d3.4 step 3): mirror of the suffix, but the
underlying `prefStretch_formula_rankAffine_q` is already `mS,n`-free so its threshold `mf s` is exposed
directly — no primed per-summand lemma needed. -/
theorem rank_cell_prefStretch_threshold_uniform (P : WRP.Presentation Step Step)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) :
    ∃ Q M, 1 ≤ Q ∧ ∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n : ℕ),
      ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom M Q F ∧
        (∀ q, q < mS - 1 → P.rank c (copiedSlice mS n) (Function.update ī0 j0 q) = F q) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  choose mf pf Pf hf using fun s : Summand Step P.d (P.toPoly.arity c) =>
    prefStretch_formula_rankAffine_q s
  refine ⟨(κ.summands.map pf).prod, (κ.summands.map mf).sum, ?_, fun ī0 mS n => ?_⟩
  · exact List.one_le_prod_of_one_le (by
      intro x hx; obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx; exact (hf s).1)
  · set M := (κ.summands.map mf).sum with hMdef
    refine ⟨fun q => κ.c0 + (κ.summands.map (fun s =>
        if s.π = j0 then
          s.coeff • s.A.prefixRank (List.replicate q U) (List.replicate q U).length
            + s.β (List.foldl s.A.δ s.A.q0 (List.replicate q U)) U
        else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π)))).sum, ?_, ?_⟩
    · refine (RankAffineAtFrom.const M _ κ.c0).add
        (RankAffineAtFrom.listSum κ.summands M _ _ (fun s hs => ?_))
      by_cases hπ : s.π = j0
      · have hpQ : pf s ∣ (κ.summands.map pf).prod := List.dvd_prod (by
          exact List.mem_map.mpr ⟨s, hs, rfl⟩)
        have hform : RankAffineAtFrom (mf s) (pf s)
            (fun q => if s.π = j0 then
              s.coeff • s.A.prefixRank (List.replicate q U) (List.replicate q U).length
                + s.β (List.foldl s.A.δ s.A.q0 (List.replicate q U)) U
              else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π))) := by
          refine ⟨Pf s, fun q hq => ?_⟩
          simp only [if_pos hπ]
          exact (hf s).2 q hq
        exact ((hform.of_dvd hpQ).mono
          (by rw [hMdef]; exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem (f := mf) hs)))
      · have heq : (fun q => if s.π = j0 then
              s.coeff • s.A.prefixRank (List.replicate q U) (List.replicate q U).length
                + s.β (List.foldl s.A.δ s.A.q0 (List.replicate q U)) U
              else s.eval (copiedSlice mS n) (fun _ => ī0 (s.π)))
            = (fun _ => s.eval (copiedSlice mS n) (fun _ => ī0 (s.π))) := by
          funext q; simp only [if_neg hπ]
        rw [heq]; exact RankAffineAtFrom.const _ _ _
    · intro q hq
      rw [hκ (copiedSlice mS n) _, SliceFamilyRank.rankTerm_eval_proj]
      funext c'
      simp only [Pi.add_apply]
      rw [SliceFamilyRank.list_sum_pi_apply]
      refine congrArg (κ.c0 c' + ·) (congrArg List.sum (List.map_congr_left (fun s _ => ?_)))
      by_cases hπ : s.π = j0
      · rw [if_pos hπ, hπ, Function.update_self]
        exact congrFun (summand_copied_prefStretch_eq s mS q hq n) c'
      · rw [if_neg hπ, Function.update_of_ne hπ]

/-! ### d3.4 step 3 (Option B'', single threshold) + step 4 boundary collapse.
Step 3 exposes, per coordinate `(c,j0)`, a combined period `pc = pg·Q` and a SINGLE threshold
`T = max(rank threshold, gate threshold)` with `T + pc < q_D`: the bundled `T` is what step 5 needs so
the SHALLOW collapse endpoint `T + r ≥ T ≥ mg` clears the gate before-gap.  Step 4 takes a band bound `N`
(step-5 passes `mS-1-T`) so the DEEP endpoint stays `≥ T` from the suffix end (after-gap), outputs
`M ≤ l_bd` / `l_bd < N` (before/after gaps for step 5), the gate shift (a multiple of `pc`), and the
value domination.  (Arity-1 has one coordinate per cell, so step 5 = step 4 with vacuous clear-window;
the general-arity collapse is blocked by coordinate crossing.) -/

/-- **Revised step 3 (Option B'', single threshold).**  For each suffix/prefix coordinate `(c, j0)`,
exposes a SINGLE collapse period `pc` (= gate cycle × rank period) AND a SINGLE threshold
`T = max(rank threshold, gate threshold)` with `T + pc < q_D`, the gate cyclicity from `T`, and the rank
recurrence `RankAffineAtFrom T pc`.  Bundling the gate threshold `mg` into `T` is what step 5 needs: the
SHALLOW collapse endpoint `T + r ≥ T ≥ mg` clears the gate before-gap, and `T + pc < q_D` keeps it inside
the band.  `q_D`/`q_U` is the additive budget. -/
theorem coordCands_cycle_lengths (P : WRP.Presentation Step Step)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (lo : ℕ) :
    ∃ q_U q_D : ℕ, lo < q_U ∧ lo < q_D ∧
      (∀ c (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
        (∀ κ b, T ≤ b →
          (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
            = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
        (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
          RankAffineAtFrom T pc F ∧
          (∀ l, l < mS - 1 → P.rank c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l))) ∧
      (∀ c (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
        (∀ κ b, T ≤ b →
          (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
            = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
        (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
          RankAffineAtFrom T pc F ∧
          (∀ q, q < mS - 1 → P.rank c (copiedSlice mS n) (Function.update ī0 j0 q) = F q))) := by
  classical
  choose mgD gateDcyc hgD using fun c => by
    have := (Mc c).fintypeQ
    exact endofunction_EP_mul (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))
  choose mgU gateUcyc hgU using fun c => by
    have := (Mc c).fintypeQ
    exact endofunction_EP_mul (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))
  choose Qsuf Msuf hsuf using fun c j0 => rank_cell_sufStretch_threshold_uniform P c j0
  choose Qpref Mpref hpref using fun c j0 => rank_cell_prefStretch_threshold_uniform P c j0
  refine ⟨lo + 1 + (∑ c, mgU c) + (∑ c, ∑ j0, (Mpref c j0 + gateUcyc c * Qpref c j0)),
          lo + 1 + (∑ c, mgD c) + (∑ c, ∑ j0, (Msuf c j0 + gateDcyc c * Qsuf c j0)),
          by omega, by omega, ?_, ?_⟩
  · intro c j0
    refine ⟨gateDcyc c * Qsuf c j0, max (Msuf c j0) (mgD c),
      Nat.mul_pos (hgD c).1 (hsuf c j0).1, ?_, ?_, ?_⟩
    · have hin : Msuf c j0 + gateDcyc c * Qsuf c j0
          ≤ ∑ j0, (Msuf c j0 + gateDcyc c * Qsuf c j0) :=
        Finset.single_le_sum (f := fun j0 => Msuf c j0 + gateDcyc c * Qsuf c j0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j0)
      have hout : (∑ j0, (Msuf c j0 + gateDcyc c * Qsuf c j0))
          ≤ ∑ c, ∑ j0, (Msuf c j0 + gateDcyc c * Qsuf c j0) :=
        Finset.single_le_sum (f := fun c => ∑ j0, (Msuf c j0 + gateDcyc c * Qsuf c j0))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      have h1 : mgD c ≤ ∑ c, mgD c :=
        Finset.single_le_sum (f := fun c => mgD c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
    · intro κ b hb
      rw [show b + gateDcyc c * Qsuf c j0 * κ = b + gateDcyc c * (Qsuf c j0 * κ) by ring]
      exact (hgD c).2 (Qsuf c j0 * κ) b (le_trans (le_max_right _ _) hb)
    · intro ī0 mS n
      obtain ⟨F, hRA, hag⟩ := (hsuf c j0).2 ī0 mS n
      exact ⟨F, (hRA.of_dvd (dvd_mul_left (Qsuf c j0) (gateDcyc c))).mono (le_max_left _ _), hag⟩
  · intro c j0
    refine ⟨gateUcyc c * Qpref c j0, max (Mpref c j0) (mgU c),
      Nat.mul_pos (hgU c).1 (hpref c j0).1, ?_, ?_, ?_⟩
    · have hin : Mpref c j0 + gateUcyc c * Qpref c j0
          ≤ ∑ j0, (Mpref c j0 + gateUcyc c * Qpref c j0) :=
        Finset.single_le_sum (f := fun j0 => Mpref c j0 + gateUcyc c * Qpref c j0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j0)
      have hout : (∑ j0, (Mpref c j0 + gateUcyc c * Qpref c j0))
          ≤ ∑ c, ∑ j0, (Mpref c j0 + gateUcyc c * Qpref c j0) :=
        Finset.single_le_sum (f := fun c => ∑ j0, (Mpref c j0 + gateUcyc c * Qpref c j0))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      have h1 : mgU c ≤ ∑ c, mgU c :=
        Finset.single_le_sum (f := fun c => mgU c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
    · intro κ b hb
      rw [show b + gateUcyc c * Qpref c j0 * κ = b + gateUcyc c * (Qpref c j0 * κ) by ring]
      exact (hgU c).2 (Qpref c j0 * κ) b (le_trans (le_max_right _ _) hb)
    · intro ī0 mS n
      obtain ⟨F, hRA, hag⟩ := (hpref c j0).2 ī0 mS n
      exact ⟨F, (hRA.of_dvd (dvd_mul_left (Qpref c j0) (gateUcyc c))).mono (le_max_left _ _), hag⟩

/-- A finite coordinate candidate `x` realises the row-dependent descriptor `r`
when it is in `coordCands` and its `deepShapeF` interpretation at row `mS` is
exactly `r`. -/
def CoordCandRealizes {B : ℕ} (q_U q_D mS : ℕ)
    (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (r : RegionSpecF B) : Prop :=
  x ∈ coordCands B q_U q_D ∧
    (match x with
      | Sum.inl r' => r'
      | Sum.inr (Sum.inl i_off) => RegionSpecF.sufIdx (mS - 1 - i_off)
      | Sum.inr (Sum.inr i_off) => RegionSpecF.prefIdx (mS - 1 - i_off)) = r

open SliceBoundaryMinCore

/-- **d3.4 step 4 (suffix): the selBvec boundary endpoint is a `coordCands` member, and lex-dominates
the cell value.**  A suffix coordinate `j0` at depth `l` (`M ≤ l < N`) collapses, at the combined period
`pc`, to a boundary depth `l_bd` whose descriptor `x` lies in `coordCands B q_U q_D`: SHALLOW
`Sum.inl (sufIdx l_bd)` with `l_bd < q_D` (slope ≥ 0), or DEEP `Sum.inr (Sum.inl (mS-1-l_bd))` with offset
in `[1,q_D]` (slope < 0).  The band bound `N` (caller passes `mS-1-T`) keeps the deep endpoint `T` away
from the suffix end (step-5 after-gap), and the outputs `M ≤ l_bd` / `l_bd < N` give step-5's before/after
gaps.  Shift `l - l_bd` (or `l_bd - l`) is a multiple of `pc` (gate); rank at `l_bd` lex-dominates rank at
`l` (value). -/
theorem sufStretch_boundary_eq_coordCand
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    {B : ℕ} (q_U q_D : ℕ) (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n t l N : ℕ)
    (pc M : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pc) (hMpc : M + pc < q_D) (hF : RankAffineAtFrom M pc F)
    (hag : ∀ l', l' < mS - 1 → P.rank c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : M ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1) (hNM : mS - 1 ≤ N + M) (hMpcN : M + pc ≤ N) :
    ∃ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      x ∈ coordCands B q_U q_D ∧
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx l_bd) ∧
      mixedPosAt x mS t n = mS + 2 * n + 1 + l_bd ∧
      M ≤ l_bd ∧ l_bd < N ∧
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) ∧
      ¬ WRP.lexLt (P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l)))
                  (P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l_bd))) := by
  obtain ⟨PR, hPR⟩ := hF
  have hrec : ∀ (i : Fin P.d) (r' k : ℕ), F (M + r' + pc * k) i = F (M + r') i + k * PR i := by
    intro i r' k
    have hit := congrFun (SliceRankAtom.RankAffine.iterate hPR (M + r') k (by omega)) i
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
    exact hit
  obtain ⟨r, hrdef⟩ : ∃ rr : ℕ, rr = (l - M) % pc := ⟨_, rfl⟩
  obtain ⟨kd, hkddef⟩ : ∃ kk : ℕ, kk = (l - M) / pc := ⟨_, rfl⟩
  have hrlt : r < pc := by rw [hrdef]; exact Nat.mod_lt _ hpc
  have hjeq : M + r + pc * kd = l := by
    rw [hrdef, hkddef]; have := Nat.mod_add_div (l - M) pc; omega
  have hkd : kd < numReps M pc r N :=
    (mem_iff_lt_numReps M pc r N kd hpc).mp (by rw [hjeq]; exact hlN)
  by_cases hslope : WRP.lexLt PR (fun _ => 0)
  · -- DEEP: slope < 0, F decreasing; collapse UP to the deep endpoint
    have hdom := SliceDstarBridge.selBvec_le_member F PR true hrec
      (iff_of_true rfl hslope) r N kd hkd
    set l_bd := M + r + pc * (numReps M pc r N - 1) with hlbd
    have hnr1 : 1 ≤ numReps M pc r N := by omega
    have hlbdN : l_bd < N := by
      rw [hlbd]
      exact (mem_iff_lt_numReps M pc r N (numReps M pc r N - 1) hpc).mpr (by omega)
    have hlbd_mS : l_bd < mS - 1 := by omega
    have hMlbd : M ≤ l_bd := by rw [hlbd]; omega
    have hge : N ≤ M + r + pc * numReps M pc r N := by
      by_contra h; push Not at h
      exact absurd ((mem_iff_lt_numReps M pc r N (numReps M pc r N) hpc).mp h) (lt_irrefl _)
    have hmuleq : pc * (numReps M pc r N - 1) + pc = pc * numReps M pc r N := by
      rw [← Nat.mul_succ]; congr 1; omega
    have hge' : N ≤ l_bd + pc := by rw [hlbd]; omega
    have hbnd : selBvecVal F M r PR true 0 (numReps M pc r N - 1) = F l_bd := by
      funext i
      rw [hlbd, hrec i r (numReps M pc r N - 1)]
      simp only [selBvecVal, if_true]
    have hxmem : Sum.inr (Sum.inl (mS - 1 - l_bd)) ∈ coordCands B q_U q_D := by
      rw [mem_coordCands]
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨mS - 1 - l_bd, by omega, ?_, rfl⟩)))
      -- i_off = mS-1-l_bd ≤ M+pc < q_D (deep band reaches within M+pc of the end)
      omega
    refine ⟨l_bd, Sum.inr (Sum.inl (mS - 1 - l_bd)), hxmem, ?_, ?_, hMlbd, hlbdN, ?_, ?_⟩
    · refine ⟨hxmem, ?_⟩
      exact congrArg RegionSpecF.sufIdx (by omega)
    · show mixedPosAt (Sum.inr (Sum.inl (mS - 1 - l_bd))) mS t n = mS + 2 * n + 1 + l_bd
      simp only [mixedPosAt]; omega
    · refine Or.inr ⟨numReps M pc r N - 1 - kd, ?_⟩
      have hkdle : kd ≤ numReps M pc r N - 1 := by omega
      have hsplit : pc * (numReps M pc r N - 1)
          = pc * kd + pc * (numReps M pc r N - 1 - kd) := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' hkdle]
      rw [hlbd]; omega
    · rw [hjeq] at hdom; rw [hbnd] at hdom
      rw [hag l (by omega), hag l_bd hlbd_mS]; exact hdom
  · -- SHALLOW: slope ≥ 0, F nondecreasing; collapse DOWN to the shallow endpoint M+r
    have hdom := SliceDstarBridge.selBvec_le_member F PR false hrec
      (iff_of_false Bool.false_ne_true hslope) r N kd hkd
    have hlbdN : M + r < N := by omega
    have hlbd_mS : M + r < mS - 1 := by omega
    have hbnd : selBvecVal F M r PR false 0 (numReps M pc r N - 1) = F (M + r) := by
      funext i; simp only [selBvecVal, Bool.false_eq_true, if_false, Nat.cast_zero, zero_mul, add_zero]
    have hxmem : Sum.inl (RegionSpecF.sufIdx (B := B) (M + r)) ∈ coordCands B q_U q_D := by
      rw [mem_coordCands]; exact Or.inr (Or.inr (Or.inl ⟨M + r, by omega, rfl⟩))
    refine ⟨M + r, Sum.inl (RegionSpecF.sufIdx (M + r)), hxmem, ?_, ?_,
      Nat.le_add_right _ _, hlbdN, ?_, ?_⟩
    · exact ⟨hxmem, rfl⟩
    · show mixedPosAt (Sum.inl (RegionSpecF.sufIdx (M + r))) mS t n = mS + 2 * n + 1 + (M + r)
      simp only [mixedPosAt, RegionSpecF.posAt]
    · exact Or.inl ⟨kd, hjeq.symm⟩
    · rw [hjeq] at hdom; rw [hbnd] at hdom
      rw [hag l (by omega), hag (M + r) hlbd_mS]; exact hdom

/-- **d3.4 step 4 (prefix): the selBvec boundary endpoint is a `coordCands` member, and lex-dominates
the cell value.**  Mirror of the suffix lemma for a prefix-stretch coordinate `j0` at depth `q` (the
position IS the depth, `posAt (prefIdx q) = q`): SHALLOW `Sum.inl (prefIdx q_bd)` with `q_bd < q_U`, or
DEEP `Sum.inr (Sum.inr (mS-1-q_bd))` with offset in `[1,q_U]`. -/
theorem prefStretch_boundary_eq_coordCand
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    {B : ℕ} (q_U q_D : ℕ) (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n t q N : ℕ)
    (pc M : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pc) (hMpc : M + pc < q_U) (hF : RankAffineAtFrom M pc F)
    (hag : ∀ q', q' < mS - 1 → P.rank c (copiedSlice mS n) (Function.update ī0 j0 q') = F q')
    (hMq : M ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1) (hNM : mS - 1 ≤ N + M) (hMpcN : M + pc ≤ N) :
    ∃ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      x ∈ coordCands B q_U q_D ∧
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx q_bd) ∧
      mixedPosAt x mS t n = q_bd ∧
      M ≤ q_bd ∧ q_bd < N ∧
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) ∧
      ¬ WRP.lexLt (P.rank c (copiedSlice mS n) (Function.update ī0 j0 q))
                  (P.rank c (copiedSlice mS n) (Function.update ī0 j0 q_bd)) := by
  obtain ⟨PR, hPR⟩ := hF
  have hrec : ∀ (i : Fin P.d) (r' k : ℕ), F (M + r' + pc * k) i = F (M + r') i + k * PR i := by
    intro i r' k
    have hit := congrFun (SliceRankAtom.RankAffine.iterate hPR (M + r') k (by omega)) i
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
    exact hit
  obtain ⟨r, hrdef⟩ : ∃ rr : ℕ, rr = (q - M) % pc := ⟨_, rfl⟩
  obtain ⟨kd, hkddef⟩ : ∃ kk : ℕ, kk = (q - M) / pc := ⟨_, rfl⟩
  have hrlt : r < pc := by rw [hrdef]; exact Nat.mod_lt _ hpc
  have hjeq : M + r + pc * kd = q := by
    rw [hrdef, hkddef]; have := Nat.mod_add_div (q - M) pc; omega
  have hkd : kd < numReps M pc r N :=
    (mem_iff_lt_numReps M pc r N kd hpc).mp (by rw [hjeq]; exact hqN)
  by_cases hslope : WRP.lexLt PR (fun _ => 0)
  · -- DEEP
    have hdom := SliceDstarBridge.selBvec_le_member F PR true hrec
      (iff_of_true rfl hslope) r N kd hkd
    set q_bd := M + r + pc * (numReps M pc r N - 1) with hqbd
    have hnr1 : 1 ≤ numReps M pc r N := by omega
    have hqbdN : q_bd < N := by
      rw [hqbd]
      exact (mem_iff_lt_numReps M pc r N (numReps M pc r N - 1) hpc).mpr (by omega)
    have hqbd_mS : q_bd < mS - 1 := by omega
    have hMqbd : M ≤ q_bd := by rw [hqbd]; omega
    have hge : N ≤ M + r + pc * numReps M pc r N := by
      by_contra h; push Not at h
      exact absurd ((mem_iff_lt_numReps M pc r N (numReps M pc r N) hpc).mp h) (lt_irrefl _)
    have hmuleq : pc * (numReps M pc r N - 1) + pc = pc * numReps M pc r N := by
      rw [← Nat.mul_succ]; congr 1; omega
    have hge' : N ≤ q_bd + pc := by rw [hqbd]; omega
    have hbnd : selBvecVal F M r PR true 0 (numReps M pc r N - 1) = F q_bd := by
      funext i
      rw [hqbd, hrec i r (numReps M pc r N - 1)]
      simp only [selBvecVal, if_true]
    have hxmem : Sum.inr (Sum.inr (mS - 1 - q_bd)) ∈ coordCands B q_U q_D := by
      rw [mem_coordCands]
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨mS - 1 - q_bd, by omega, ?_, rfl⟩)))
      omega
    refine ⟨q_bd, Sum.inr (Sum.inr (mS - 1 - q_bd)), hxmem, ?_, ?_, hMqbd, hqbdN, ?_, ?_⟩
    · refine ⟨hxmem, ?_⟩
      exact congrArg RegionSpecF.prefIdx (by omega)
    · show mixedPosAt (Sum.inr (Sum.inr (mS - 1 - q_bd))) mS t n = q_bd
      simp only [mixedPosAt]; omega
    · refine Or.inr ⟨numReps M pc r N - 1 - kd, ?_⟩
      have hkdle : kd ≤ numReps M pc r N - 1 := by omega
      have hsplit : pc * (numReps M pc r N - 1)
          = pc * kd + pc * (numReps M pc r N - 1 - kd) := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' hkdle]
      rw [hqbd]; omega
    · rw [hjeq] at hdom; rw [hbnd] at hdom
      rw [hag q (by omega), hag q_bd hqbd_mS]; exact hdom
  · -- SHALLOW
    have hdom := SliceDstarBridge.selBvec_le_member F PR false hrec
      (iff_of_false Bool.false_ne_true hslope) r N kd hkd
    have hqbdN : M + r < N := by omega
    have hqbd_mS : M + r < mS - 1 := by omega
    have hbnd : selBvecVal F M r PR false 0 (numReps M pc r N - 1) = F (M + r) := by
      funext i; simp only [selBvecVal, Bool.false_eq_true, if_false, Nat.cast_zero, zero_mul, add_zero]
    have hxmem : Sum.inl (RegionSpecF.prefIdx (B := B) (M + r)) ∈ coordCands B q_U q_D := by
      rw [mem_coordCands]; exact Or.inr (Or.inl ⟨M + r, by omega, rfl⟩)
    refine ⟨M + r, Sum.inl (RegionSpecF.prefIdx (M + r)), hxmem, ?_, ?_,
      Nat.le_add_right _ _, hqbdN, ?_, ?_⟩
    · exact ⟨hxmem, rfl⟩
    · show mixedPosAt (Sum.inl (RegionSpecF.prefIdx (M + r))) mS t n = M + r
      simp only [mixedPosAt, RegionSpecF.posAt]
    · exact Or.inl ⟨kd, hjeq.symm⟩
    · rw [hjeq] at hdom; rw [hbnd] at hdom
      rw [hag q (by omega), hag (M + r) hqbd_mS]; exact hdom

/-- **Arity-free no-move collapse.**  If a finite mixed descriptor already has
`rs` as its `deepShapeF` at the current row, then the cell is already in the
bounded `mixedTuplesF` candidate pool: the gate is unchanged and the rank value
is definitionally the same via `cellTupleF_deepShapeF`.

This is the reusable part of `cell_collapse_to_coordCand_one`; arbitrary-arity
collapse still has to supply such a descriptor, or move the non-finite stretch
coordinates to one. -/
theorem cell_collapse_to_coordCand_of_deepShape
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (ds : Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ))
    (mS n t : ℕ)
    (hds : ∀ i, ds i ∈ coordCands B q_U q_D)
    (hdeq : deepShapeF ds mS = rs)
    (hgate : gateF Mc rs mS t n) :
    ∃ ds', ds' ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF Mc (deepShapeF ds' mS) mS t n ∧
      ¬ WRP.lexLt (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
                  (P.rank c (copiedSlice mS n) (mixedTupleF ds' mS t n)) := by
  refine ⟨ds, (mem_mixedTuplesF ds).mpr hds, ?_, ?_⟩
  · rw [hdeq]; exact hgate
  · rw [← cellTupleF_deepShapeF ds mS t n, hdeq]
    exact lexLt_irrefl _

theorem coordCandRealizes_core {B q_U q_D mS : ℕ} (r : RegionSpec B) :
    CoordCandRealizes q_U q_D mS (Sum.inl (RegionSpecF.core r)) (RegionSpecF.core r) := by
  refine ⟨?_, rfl⟩
  rw [mem_coordCands]
  exact Or.inl ⟨r, rfl⟩

theorem coordCandRealizes_pref_shallow {B q_U q_D mS q : ℕ} (hq : q < q_U) :
    CoordCandRealizes q_U q_D mS (Sum.inl (RegionSpecF.prefIdx (B := B) q))
      (RegionSpecF.prefIdx q) := by
  refine ⟨?_, rfl⟩
  rw [mem_coordCands]
  exact Or.inr (Or.inl ⟨q, hq, rfl⟩)

theorem coordCandRealizes_suf_shallow {B q_U q_D mS l : ℕ} (hl : l < q_D) :
    CoordCandRealizes q_U q_D mS (Sum.inl (RegionSpecF.sufIdx (B := B) l))
      (RegionSpecF.sufIdx l) := by
  refine ⟨?_, rfl⟩
  rw [mem_coordCands]
  exact Or.inr (Or.inr (Or.inl ⟨l, hl, rfl⟩))

theorem coordCandRealizes_suf_deep {B q_U q_D mS i_off : ℕ}
    (hi1 : 1 ≤ i_off) (hiq : i_off ≤ q_D) :
    CoordCandRealizes q_U q_D mS (Sum.inr (Sum.inl i_off))
      (RegionSpecF.sufIdx (B := B) (mS - 1 - i_off)) := by
  refine ⟨?_, rfl⟩
  rw [mem_coordCands]
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i_off, hi1, hiq, rfl⟩)))

theorem coordCandRealizes_pref_deep {B q_U q_D mS i_off : ℕ}
    (hi1 : 1 ≤ i_off) (hiq : i_off ≤ q_U) :
    CoordCandRealizes q_U q_D mS (Sum.inr (Sum.inr i_off))
      (RegionSpecF.prefIdx (B := B) (mS - 1 - i_off)) := by
  refine ⟨?_, rfl⟩
  rw [mem_coordCands]
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i_off, hi1, hiq, rfl⟩)))

theorem coordCandRealizes_pref_shallow_or_deep {B q_U q_D mS q : ℕ}
    (hv : q < mS - 1) (hside : q < q_U ∨ mS - 1 - q_U < q) :
    ∃ x, CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q) := by
  rcases hside with hqsh | hqdeep
  · exact ⟨Sum.inl (RegionSpecF.prefIdx q), coordCandRealizes_pref_shallow hqsh⟩
  · refine ⟨Sum.inr (Sum.inr (mS - 1 - q)), ?_⟩
    simpa [show mS - 1 - (mS - 1 - q) = q by omega] using
      (coordCandRealizes_pref_deep (B := B) (q_U := q_U) (q_D := q_D)
        (mS := mS) (i_off := mS - 1 - q) (by omega) (by omega))

theorem coordCandRealizes_suf_shallow_or_deep {B q_U q_D mS l : ℕ}
    (hv : l < mS - 1) (hside : l < q_D ∨ mS - 1 - q_D < l) :
    ∃ x, CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l) := by
  rcases hside with hlsh | hldeep
  · exact ⟨Sum.inl (RegionSpecF.sufIdx l), coordCandRealizes_suf_shallow hlsh⟩
  · refine ⟨Sum.inr (Sum.inl (mS - 1 - l)), ?_⟩
    simpa [show mS - 1 - (mS - 1 - l) = l by omega] using
      (coordCandRealizes_suf_deep (B := B) (q_U := q_U) (q_D := q_D)
        (mS := mS) (i_off := mS - 1 - l) (by omega) (by omega))

/-- A descriptor is a genuine prefix middle-band coordinate when it is a
`prefIdx` whose index is not already in either finite boundary band. -/
def PrefMiddleDescriptor {B : ℕ} (q_U mS : ℕ) (r : RegionSpecF B) : Prop :=
  ∃ q, r = RegionSpecF.prefIdx q ∧ q_U ≤ q ∧ q ≤ mS - 1 - q_U

/-- A descriptor is a genuine suffix middle-band coordinate when it is a
`sufIdx` whose depth is not already in either finite boundary band. -/
def SufMiddleDescriptor {B : ℕ} (q_D mS : ℕ) (r : RegionSpecF B) : Prop :=
  ∃ l, r = RegionSpecF.sufIdx l ∧ q_D ≤ l ∧ l ≤ mS - 1 - q_D

/-- Bounds used when collapsing a prefix middle descriptor to a boundary
representative with `N = mS - 1 - T`. -/
theorem prefMiddle_collapse_bounds {q_U mS q pc T : ℕ}
    (hqL : q_U ≤ q) (hqR : q ≤ mS - 1 - q_U)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hmSu : 2 * q_U + 2 ≤ mS) :
    T ≤ q ∧ q < mS - 1 - T ∧ mS - 1 - T ≤ mS - 1 ∧
      mS - 1 ≤ (mS - 1 - T) + T ∧ (mS - 1 - T) + T ≤ mS - 1 ∧
      T + pc ≤ mS - 1 - T := by
  omega

/-- Bounds used when collapsing a suffix middle descriptor to a boundary
representative with `N = mS - 1 - T`. -/
theorem sufMiddle_collapse_bounds {q_D mS l pc T : ℕ}
    (hlL : q_D ≤ l) (hlR : l ≤ mS - 1 - q_D)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hmSq : 2 * q_D + 2 ≤ mS) :
    T ≤ l ∧ l < mS - 1 - T ∧ mS - 1 - T ≤ mS - 1 ∧
      mS - 1 ≤ (mS - 1 - T) + T ∧ (mS - 1 - T) + T ≤ mS - 1 ∧
      T + pc ≤ mS - 1 - T := by
  omega

theorem PrefMiddleDescriptor.collapse_bounds {B q_U mS pc T : ℕ}
    {r : RegionSpecF B}
    (hmid : PrefMiddleDescriptor q_U mS r)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hmSu : 2 * q_U + 2 ≤ mS) :
    ∃ q, r = RegionSpecF.prefIdx q ∧
      T ≤ q ∧ q < mS - 1 - T ∧ mS - 1 - T ≤ mS - 1 ∧
        mS - 1 ≤ (mS - 1 - T) + T ∧ (mS - 1 - T) + T ≤ mS - 1 ∧
        T + pc ≤ mS - 1 - T := by
  rcases hmid with ⟨q, hsrc, hqL, hqR⟩
  exact ⟨q, hsrc, prefMiddle_collapse_bounds hqL hqR hpc hMpc hmSu⟩

theorem SufMiddleDescriptor.collapse_bounds {B q_D mS pc T : ℕ}
    {r : RegionSpecF B}
    (hmid : SufMiddleDescriptor q_D mS r)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hmSq : 2 * q_D + 2 ≤ mS) :
    ∃ l, r = RegionSpecF.sufIdx l ∧
      T ≤ l ∧ l < mS - 1 - T ∧ mS - 1 - T ≤ mS - 1 ∧
        mS - 1 ≤ (mS - 1 - T) + T ∧ (mS - 1 - T) + T ≤ mS - 1 ∧
        T + pc ≤ mS - 1 - T := by
  rcases hmid with ⟨l, hsrc, hlL, hlR⟩
  exact ⟨l, hsrc, sufMiddle_collapse_bounds hlL hlR hpc hMpc hmSq⟩

/-- The set of coordinates already represented by finite candidates: neither a
prefix-middle nor a suffix-middle descriptor. -/
noncomputable def finiteDescriptorSet {B k : ℕ} (q_U q_D mS : ℕ)
    (rs : Fin k → RegionSpecF B) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun i =>
    ¬ PrefMiddleDescriptor q_U mS (rs i) ∧
    ¬ SufMiddleDescriptor q_D mS (rs i))

/-- The complementary scheduler target: coordinates that still need a
middle-band prefix/suffix move. -/
noncomputable def middleDescriptorSet {B k : ℕ} (q_U q_D mS : ℕ)
    (rs : Fin k → RegionSpecF B) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun i =>
    PrefMiddleDescriptor q_U mS (rs i) ∨
    SufMiddleDescriptor q_D mS (rs i))

theorem mem_finiteDescriptorSet {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {i : Fin k} :
    i ∈ finiteDescriptorSet q_U q_D mS rs ↔
      ¬ PrefMiddleDescriptor q_U mS (rs i) ∧
      ¬ SufMiddleDescriptor q_D mS (rs i) := by
  classical
  simp [finiteDescriptorSet]

theorem mem_middleDescriptorSet {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {i : Fin k} :
    i ∈ middleDescriptorSet q_U q_D mS rs ↔
      PrefMiddleDescriptor q_U mS (rs i) ∨
      SufMiddleDescriptor q_D mS (rs i) := by
  classical
  simp [middleDescriptorSet]

theorem mem_middleDescriptorSet_update_iff_of_ne {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {i j : Fin k} {r : RegionSpecF B}
    (hij : i ≠ j) :
    i ∈ middleDescriptorSet q_U q_D mS (Function.update rs j r) ↔
      i ∈ middleDescriptorSet q_U q_D mS rs := by
  rw [mem_middleDescriptorSet, mem_middleDescriptorSet]
  simp [Function.update_of_ne hij]

theorem mem_middleDescriptorSet_update_of_ne {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {i j : Fin k} {r : RegionSpecF B}
    (hij : i ≠ j)
    (hi : i ∈ middleDescriptorSet q_U q_D mS rs) :
    i ∈ middleDescriptorSet q_U q_D mS (Function.update rs j r) :=
  (mem_middleDescriptorSet_update_iff_of_ne (r := r) hij).mpr hi

theorem mem_finiteDescriptorSet_or_middleDescriptorSet {B k q_U q_D mS : ℕ}
    (rs : Fin k → RegionSpecF B) (i : Fin k) :
    i ∈ finiteDescriptorSet q_U q_D mS rs ∨
      i ∈ middleDescriptorSet q_U q_D mS rs := by
  classical
  by_cases hP : PrefMiddleDescriptor q_U mS (rs i)
  · exact Or.inr (mem_middleDescriptorSet.mpr (Or.inl hP))
  · by_cases hS : SufMiddleDescriptor q_D mS (rs i)
    · exact Or.inr (mem_middleDescriptorSet.mpr (Or.inr hS))
    · exact Or.inl (mem_finiteDescriptorSet.mpr ⟨hP, hS⟩)

theorem finiteDescriptorSet_union_eq_univ_of_middle_subset {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done : Finset (Fin k)}
    (hsub : middleDescriptorSet q_U q_D mS rs ⊆ done) :
    finiteDescriptorSet q_U q_D mS rs ∪ done = Finset.univ := by
  classical
  ext i
  constructor
  · intro _
    exact Finset.mem_univ i
  · intro _
    rcases mem_finiteDescriptorSet_or_middleDescriptorSet rs i with hfin | hmid
    · exact Finset.mem_union.mpr (Or.inl hfin)
    · exact Finset.mem_union.mpr (Or.inr (hsub hmid))

theorem finiteDescriptorSet_union_mem_of_middle_subset {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done : Finset (Fin k)}
    (hsub : middleDescriptorSet q_U q_D mS rs ⊆ done) :
    ∀ i, i ∈ finiteDescriptorSet q_U q_D mS rs ∪ done := by
  intro i
  have hmem : i ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ i
  rwa [← finiteDescriptorSet_union_eq_univ_of_middle_subset (rs := rs) hsub] at hmem

theorem done_eq_univ_of_descriptor_subsets {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done : Finset (Fin k)}
    (hfin : finiteDescriptorSet q_U q_D mS rs ⊆ done)
    (hmiddle : middleDescriptorSet q_U q_D mS rs ⊆ done) :
    done = Finset.univ := by
  classical
  ext i
  constructor
  · intro _
    exact Finset.mem_univ i
  · intro _
    rcases mem_finiteDescriptorSet_or_middleDescriptorSet rs i with hi | hi
    · exact hfin hi
    · exact hmiddle hi

theorem done_mem_of_descriptor_subsets {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done : Finset (Fin k)}
    (hfin : finiteDescriptorSet q_U q_D mS rs ⊆ done)
    (hmiddle : middleDescriptorSet q_U q_D mS rs ⊆ done) :
    ∀ i, i ∈ done := by
  intro i
  have hmem : i ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ i
  rwa [← done_eq_univ_of_descriptor_subsets (rs := rs) hfin hmiddle] at hmem

theorem finiteDescriptorSet_subset_insert_of_subset {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done : Finset (Fin k)} {j : Fin k}
    (hfin : finiteDescriptorSet q_U q_D mS rs ⊆ done) :
    finiteDescriptorSet q_U q_D mS rs ⊆ insert j done := by
  intro i hi
  exact Finset.mem_insert.mpr (Or.inr (hfin hi))

theorem middleDescriptorSet_subset_insert_of_erase_subset {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done : Finset (Fin k)} {j : Fin k}
    (hmiddle : (middleDescriptorSet q_U q_D mS rs).erase j ⊆ done) :
    middleDescriptorSet q_U q_D mS rs ⊆ insert j done := by
  intro i hi
  by_cases hij : i = j
  · subst i
    exact Finset.mem_insert_self j done
  · exact Finset.mem_insert.mpr (Or.inr (hmiddle (Finset.mem_erase.mpr ⟨hij, hi⟩)))

/-- A valid row descriptor is either already represented by a finite coordinate
candidate, or it is a genuine middle prefix/suffix coordinate.  This is the
case split needed before invoking the stretch-collapse steps. -/
theorem coordCandRealizes_or_middle {B q_U q_D mS : ℕ} (r : RegionSpecF B)
    (hv : r.valid mS) :
    (∃ x, CoordCandRealizes q_U q_D mS x r) ∨
      (∃ q, r = RegionSpecF.prefIdx q ∧ q_U ≤ q ∧ q ≤ mS - 1 - q_U) ∨
      (∃ l, r = RegionSpecF.sufIdx l ∧ q_D ≤ l ∧ l ≤ mS - 1 - q_D) := by
  rcases r with r | q | l
  · exact Or.inl ⟨Sum.inl (RegionSpecF.core r), coordCandRealizes_core r⟩
  · by_cases hqsh : q < q_U
    · exact Or.inl ⟨Sum.inl (RegionSpecF.prefIdx q), coordCandRealizes_pref_shallow hqsh⟩
    · by_cases hqdeep : mS - 1 - q_U < q
      · exact Or.inl (coordCandRealizes_pref_shallow_or_deep hv (Or.inr hqdeep))
      · push Not at hqsh hqdeep
        exact Or.inr (Or.inl ⟨q, rfl, hqsh, hqdeep⟩)
  · by_cases hlsh : l < q_D
    · exact Or.inl ⟨Sum.inl (RegionSpecF.sufIdx l), coordCandRealizes_suf_shallow hlsh⟩
    · by_cases hldeep : mS - 1 - q_D < l
      · exact Or.inl (coordCandRealizes_suf_shallow_or_deep hv (Or.inr hldeep))
      · push Not at hlsh hldeep
        exact Or.inr (Or.inr ⟨l, rfl, hlsh, hldeep⟩)

theorem coordCandRealizes_of_valid_not_middleDescriptor {B q_U q_D mS : ℕ}
    {r : RegionSpecF B}
    (hv : r.valid mS)
    (hnotPref : ¬ PrefMiddleDescriptor q_U mS r)
    (hnotSuf : ¬ SufMiddleDescriptor q_D mS r) :
    ∃ x, CoordCandRealizes q_U q_D mS x r := by
  rcases coordCandRealizes_or_middle r hv with hreal | hmiddle
  · exact hreal
  · rcases hmiddle with hpref | hsuf
    · exact False.elim (hnotPref hpref)
    · exact False.elim (hnotSuf hsuf)

/-- Every coordinate of a row-dependent descriptor tuple is already realised by
a finite `coordCands` representative at row `mS`.  This is the invariant the
general collapse induction should eventually maintain while moving one
prefix/suffix coordinate at a time. -/
def CoordwiseRealizable {B k : ℕ} (q_U q_D mS : ℕ)
    (rs : Fin k → RegionSpecF B) : Prop :=
  ∀ i, ∃ x, CoordCandRealizes q_U q_D mS x (rs i)

theorem CoordwiseRealizable.of_valid_not_middle {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B}
    (hv : ∀ i, (rs i).valid mS)
    (hpref : ∀ i q, rs i = RegionSpecF.prefIdx q → q < q_U ∨ mS - 1 - q_U < q)
    (hsuf : ∀ i l, rs i = RegionSpecF.sufIdx l → l < q_D ∨ mS - 1 - q_D < l) :
    CoordwiseRealizable q_U q_D mS rs := by
  intro i
  rcases hri : rs i with r | q | l
  · exact ⟨Sum.inl (RegionSpecF.core r), coordCandRealizes_core r⟩
  · exact coordCandRealizes_pref_shallow_or_deep (by have h := hv i; rw [hri] at h; exact h)
      (hpref i q hri)
  · exact coordCandRealizes_suf_shallow_or_deep (by have h := hv i; rw [hri] at h; exact h)
      (hsuf i l hri)

theorem CoordwiseRealizable.update {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {j0 : Fin k} {r : RegionSpecF B}
    (hrs : ∀ i, i ≠ j0 → ∃ x, CoordCandRealizes q_U q_D mS x (rs i))
    (hr : ∃ x, CoordCandRealizes q_U q_D mS x r) :
    CoordwiseRealizable q_U q_D mS (Function.update rs j0 r) := by
  intro i
  by_cases hi : i = j0
  · subst hi
    simpa using hr
  · simpa [Function.update_of_ne hi] using hrs i hi

theorem CoordwiseRealizable.update_of_realizable {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {j0 : Fin k} {r : RegionSpecF B}
    (hrs : CoordwiseRealizable q_U q_D mS rs)
    (hr : ∃ x, CoordCandRealizes q_U q_D mS x r) :
    CoordwiseRealizable q_U q_D mS (Function.update rs j0 r) :=
  CoordwiseRealizable.update (fun i _ => hrs i) hr

/-- Coordinatewise realizability after two descriptor updates, assuming all
coordinates outside the two updated indices were already finite-realizable. -/
theorem CoordwiseRealizable.update_two {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {j1 j2 : Fin k} {r1 r2 : RegionSpecF B}
    (hrest : ∀ i, i ≠ j1 → i ≠ j2 → ∃ x, CoordCandRealizes q_U q_D mS x (rs i))
    (hr1 : ∃ x, CoordCandRealizes q_U q_D mS x r1)
    (hr2 : ∃ x, CoordCandRealizes q_U q_D mS x r2) :
    CoordwiseRealizable q_U q_D mS (Function.update (Function.update rs j1 r1) j2 r2) := by
  intro i
  by_cases hi2 : i = j2
  · subst hi2
    simpa using hr2
  · by_cases hi1 : i = j1
    · subst hi1
      simpa [Function.update_of_ne hi2] using hr1
    · simpa [Function.update_of_ne hi2, Function.update_of_ne hi1] using hrest i hi1 hi2

/-- Partial coordinate-realizability invariant: only coordinates in `done`
have already been moved to finite `coordCands` representatives. -/
def CoordwiseRealizableOn {B k : ℕ} (q_U q_D mS : ℕ) (done : Finset (Fin k))
    (rs : Fin k → RegionSpecF B) : Prop :=
  ∀ i, i ∈ done → ∃ x, CoordCandRealizes q_U q_D mS x (rs i)

theorem CoordwiseRealizableOn.empty {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} :
    CoordwiseRealizableOn q_U q_D mS (∅ : Finset (Fin k)) rs := by
  intro i hi
  simp at hi

/-- Partial version of `CoordwiseRealizable.of_valid_not_middle`: every
coordinate already placed in `done` is finite-realizable when it is valid and
outside the middle prefix/suffix bands. -/
theorem CoordwiseRealizableOn.of_valid_not_middle_on {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done : Finset (Fin k)}
    (hv : ∀ i, i ∈ done → (rs i).valid mS)
    (hpref : ∀ i, i ∈ done → ∀ q, rs i = RegionSpecF.prefIdx q →
      q < q_U ∨ mS - 1 - q_U < q)
    (hsuf : ∀ i, i ∈ done → ∀ l, rs i = RegionSpecF.sufIdx l →
      l < q_D ∨ mS - 1 - q_D < l) :
    CoordwiseRealizableOn q_U q_D mS done rs := by
  intro i hi
  rcases hri : rs i with r | q | l
  · exact ⟨Sum.inl (RegionSpecF.core r), coordCandRealizes_core r⟩
  · exact coordCandRealizes_pref_shallow_or_deep (by have h := hv i hi; rw [hri] at h; exact h)
      (hpref i hi q hri)
  · exact coordCandRealizes_suf_shallow_or_deep (by have h := hv i hi; rw [hri] at h; exact h)
      (hsuf i hi l hri)

/-- Initial partial-realizability invariant for a scheduler: all coordinates
outside the middle prefix/suffix bands are already finite candidates. -/
theorem CoordwiseRealizableOn.of_finiteDescriptorSet {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B}
    (hv : ∀ i, (rs i).valid mS) :
    CoordwiseRealizableOn q_U q_D mS (finiteDescriptorSet q_U q_D mS rs) rs := by
  intro i hi
  exact coordCandRealizes_of_valid_not_middleDescriptor (hv i)
    (mem_finiteDescriptorSet.mp hi).1 (mem_finiteDescriptorSet.mp hi).2

theorem CoordwiseRealizableOn.union {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done₁ done₂ : Finset (Fin k)}
    (h₁ : CoordwiseRealizableOn q_U q_D mS done₁ rs)
    (h₂ : CoordwiseRealizableOn q_U q_D mS done₂ rs) :
    CoordwiseRealizableOn q_U q_D mS (done₁ ∪ done₂) rs := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi₁ | hi₂
  · exact h₁ i hi₁
  · exact h₂ i hi₂

theorem CoordwiseRealizableOn.mono {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done₁ done₂ : Finset (Fin k)}
    (hsub : done₁ ⊆ done₂)
    (h₂ : CoordwiseRealizableOn q_U q_D mS done₂ rs) :
    CoordwiseRealizableOn q_U q_D mS done₁ rs := by
  intro i hi
  exact h₂ i (hsub hi)

theorem CoordwiseRealizableOn.finite_union {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done : Finset (Fin k)}
    (hv : ∀ i, (rs i).valid mS)
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs) :
    CoordwiseRealizableOn q_U q_D mS
      (finiteDescriptorSet q_U q_D mS rs ∪ done) rs :=
  CoordwiseRealizableOn.union (CoordwiseRealizableOn.of_finiteDescriptorSet hv) hdone

theorem CoordwiseRealizableOn.to_coordwise_of_middle_subset {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done : Finset (Fin k)}
    (hdone : CoordwiseRealizableOn q_U q_D mS
      (finiteDescriptorSet q_U q_D mS rs ∪ done) rs)
    (hsub : middleDescriptorSet q_U q_D mS rs ⊆ done) :
    CoordwiseRealizable q_U q_D mS rs :=
  by
    intro i
    exact hdone i (finiteDescriptorSet_union_mem_of_middle_subset (rs := rs) hsub i)

theorem CoordwiseRealizableOn.update_insert {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done : Finset (Fin k)}
    {j0 : Fin k} {r : RegionSpecF B}
    (hrs : CoordwiseRealizableOn q_U q_D mS done rs)
    (hr : ∃ x, CoordCandRealizes q_U q_D mS x r) :
    CoordwiseRealizableOn q_U q_D mS (insert j0 done) (Function.update rs j0 r) := by
  intro i hi
  by_cases hij : i = j0
  · subst hij
    simpa using hr
  · have hidone : i ∈ done := by
      simpa [hij] using hi
    simpa [Function.update_of_ne hij] using hrs i hidone

theorem CoordwiseRealizableOn.to_coordwise {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B}
    (hrs : CoordwiseRealizableOn q_U q_D mS (Finset.univ : Finset (Fin k)) rs) :
    CoordwiseRealizable q_U q_D mS rs := by
  intro i
  exact hrs i (Finset.mem_univ i)

theorem CoordwiseRealizableOn.to_coordwise_of_forall_mem {B k q_U q_D mS : ℕ}
    {rs : Fin k → RegionSpecF B} {done : Finset (Fin k)}
    (hrs : CoordwiseRealizableOn q_U q_D mS done rs)
    (hall : ∀ i, i ∈ done) :
    CoordwiseRealizable q_U q_D mS rs := by
  intro i
  exact hrs i (hall i)

/-- Any non-prefix descriptor lies at or to the right of the copied-slice
prefix boundary. -/
theorem cellTupleF_ge_prefix_boundary_of_not_prefIdx {B k : ℕ}
    (rs : Fin k → RegionSpecF B) (i : Fin k) (mS t n : ℕ)
    (hnot : ∀ q, rs i ≠ RegionSpecF.prefIdx q) :
    mS - 1 ≤ cellTupleF rs mS t n i := by
  show mS - 1 ≤ (rs i).posAt mS t n
  rcases hri : rs i with r | q | l
  · simp only [RegionSpecF.posAt]
    omega
  · exact False.elim (hnot q hri)
  · simp only [RegionSpecF.posAt]
    omega

/-- A core descriptor sits strictly before the suffix-stretch boundary on a
valid wrapped window. -/
theorem core_posAt_lt_suffix_boundary {B : ℕ} (r : RegionSpec B)
    (mS t n : ℕ) (hm : 1 ≤ mS) (hwin : t + B ≤ n) :
    (RegionSpecF.core r).posAt mS t n < mS + 2 * n + 1 := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [RegionSpecF.posAt, RegionSpec.posAt]
  · omega
  · omega
  · have := f.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · have := l.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · have := δ.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Any valid non-suffix descriptor lies strictly before the copied-slice suffix
stretch boundary. -/
theorem cellTupleF_lt_suffix_boundary_of_not_sufIdx {B k : ℕ}
    (rs : Fin k → RegionSpecF B) (i : Fin k) (mS t n : ℕ)
    (hm : 1 ≤ mS) (hv : (rs i).valid mS) (hwin : t + B ≤ n)
    (hnot : ∀ l, rs i ≠ RegionSpecF.sufIdx l) :
    cellTupleF rs mS t n i < mS + 2 * n + 1 := by
  show (rs i).posAt mS t n < mS + 2 * n + 1
  rcases hri : rs i with r | q | l
  · simpa [hri] using core_posAt_lt_suffix_boundary r mS t n hm hwin
  · have hq : q < mS - 1 := by
      simpa [hri, RegionSpecF.valid] using hv
    simp only [RegionSpecF.posAt]
    omega
  · exact False.elim (hnot l hri)

/-- Descriptor-shape form of the suffix no-crossing hypothesis for all
coordinates except `j0`. -/
theorem no_other_suf_of_forall_not_sufIdx {B k : ℕ}
    (rs : Fin k → RegionSpecF B) (j0 : Fin k) (mS t n : ℕ)
    (hm : 1 ≤ mS) (hv : ∀ i, (rs i).valid mS) (hwin : t + B ≤ n)
    (hnot : ∀ i, i ≠ j0 → ∀ l, rs i ≠ RegionSpecF.sufIdx l) :
    ∀ i, i ≠ j0 → cellTupleF rs mS t n i < mS + 2 * n + 1 := by
  intro i hi
  exact cellTupleF_lt_suffix_boundary_of_not_sufIdx rs i mS t n hm (hv i) hwin (hnot i hi)

/-- Updating one coordinate to a valid prefix descriptor preserves the
descriptor-shape suffix no-crossing condition for any other active suffix
coordinate. -/
theorem no_other_suf_after_pref_update_of_forall_not_sufIdx {B k : ℕ}
    (rs : Fin k → RegionSpecF B) (jP jS : Fin k) (mS t n q_bd : ℕ)
    (hm : 1 ≤ mS) (hv : ∀ i, (rs i).valid mS) (hwin : t + B ≤ n)
    (hqbd : q_bd < mS - 1)
    (hnotSuf : ∀ i, i ≠ jS → ∀ l, rs i ≠ RegionSpecF.sufIdx l) :
    ∀ i, i ≠ jS →
      cellTupleF (Function.update rs jP (RegionSpecF.prefIdx q_bd)) mS t n i <
        mS + 2 * n + 1 := by
  refine no_other_suf_of_forall_not_sufIdx
    (Function.update rs jP (RegionSpecF.prefIdx q_bd)) jS mS t n hm ?_ hwin ?_
  · intro i
    by_cases hiP : i = jP
    · subst hiP
      simp only [Function.update_self, RegionSpecF.valid]
      exact hqbd
    · simpa [Function.update_of_ne hiP] using hv i
  · intro i hiS l h
    by_cases hiP : i = jP
    · subst hiP
      simp only [Function.update_self] at h
      cases h
    · have horig : rs i = RegionSpecF.sufIdx l := by
        simpa [Function.update_of_ne hiP] using h
      exact hnotSuf i hiS l horig

/-- Clear-window hypothesis for a prefix middle-band move: every other mark is
outside the open prefix interval used to slide `j0` to `q_bd`, with enough
unmarked padding for the automaton cycle on both sides. -/
def PrefClearWindow {B k : ℕ} (rs : Fin k → RegionSpecF B) (j0 : Fin k)
    (mS n t q N pc T : ℕ) : Prop :=
  ∀ q_bd,
    T ≤ q_bd → q_bd < N →
    ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
    ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ q ∧ q < e ∧ s ≤ q_bd ∧ q_bd < e ∧
      (∀ i, i ≠ j0 → cellTupleF rs mS t n i < s ∨ e ≤ cellTupleF rs mS t n i) ∧
      T ≤ q - s ∧ T ≤ q_bd - s ∧ T ≤ e - 1 - q ∧ T ≤ e - 1 - q_bd

/-- Clear-window hypothesis for a suffix middle-band move. -/
def SufClearWindow {B k : ℕ} (rs : Fin k → RegionSpecF B) (j0 : Fin k)
    (mS n t l N pc T : ℕ) : Prop :=
  ∀ l_bd,
    T ≤ l_bd → l_bd < N →
    ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
    ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ l ∧ l < e ∧ s ≤ l_bd ∧ l_bd < e ∧
      (∀ i, i ≠ j0 →
        cellTupleF rs mS t n i < mS + 2 * n + 1 + s ∨
          mS + 2 * n + 1 + e ≤ cellTupleF rs mS t n i) ∧
      T ≤ l - s ∧ T ≤ l_bd - s ∧ T ≤ e - 1 - l ∧ T ≤ e - 1 - l_bd

theorem PrefClearWindow.of_no_other_pref {B k : ℕ}
    (rs : Fin k → RegionSpecF B) (j0 : Fin k)
    (mS n t q N pc T : ℕ)
    (hMq : T ≤ q) (hqN : q < N) (hNright : N + T ≤ mS - 1)
    (hnoPref : ∀ i, i ≠ j0 → mS - 1 ≤ cellTupleF rs mS t n i) :
    PrefClearWindow rs j0 mS n t q N pc T := by
  intro q_bd hTqbd hqbdN hshift
  clear hshift
  refine ⟨0, mS - 1, Nat.zero_le _, le_rfl, Nat.zero_le _, ?_,
    Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro i hi
    exact Or.inr (hnoPref i hi)
  · omega
  · omega
  · omega
  · omega

theorem SufClearWindow.of_no_other_suf {B k : ℕ}
    (rs : Fin k → RegionSpecF B) (j0 : Fin k)
    (mS n t l N pc T : ℕ)
    (hMl : T ≤ l) (hlN : l < N) (hNright : N + T ≤ mS - 1)
    (hnoSuf : ∀ i, i ≠ j0 → cellTupleF rs mS t n i < mS + 2 * n + 1) :
    SufClearWindow rs j0 mS n t l N pc T := by
  intro l_bd hTlbd hlbdN hshift
  clear hshift
  refine ⟨0, mS - 1, Nat.zero_le _, le_rfl, Nat.zero_le _, ?_,
    Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro i hi
    exact Or.inl (hnoSuf i hi)
  · omega
  · omega
  · omega
  · omega

theorem PrefClearWindow.of_fixed_window {B k : ℕ}
    (rs : Fin k → RegionSpecF B) (j0 : Fin k)
    (mS n t q N pc T s e : ℕ)
    (hse : s ≤ e) (hem : e ≤ mS - 1)
    (hclear : ∀ i, i ≠ j0 → cellTupleF rs mS t n i < s ∨ e ≤ cellTupleF rs mS t n i)
    (hspan : ∀ q_bd,
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      s ≤ q ∧ q < e ∧ s ≤ q_bd ∧ q_bd < e ∧
        T ≤ q - s ∧ T ≤ q_bd - s ∧ T ≤ e - 1 - q ∧ T ≤ e - 1 - q_bd) :
    PrefClearWindow rs j0 mS n t q N pc T := by
  intro q_bd hTqbd hqbdN hshift
  obtain ⟨hsq, hqe, hsqbd, hqbde, hTqs, hTqbds, hTeq, hTeqbd⟩ :=
    hspan q_bd hTqbd hqbdN hshift
  exact ⟨s, e, hse, hem, hsq, hqe, hsqbd, hqbde, hclear, hTqs, hTqbds, hTeq, hTeqbd⟩

theorem SufClearWindow.of_fixed_window {B k : ℕ}
    (rs : Fin k → RegionSpecF B) (j0 : Fin k)
    (mS n t l N pc T s e : ℕ)
    (hse : s ≤ e) (hem : e ≤ mS - 1)
    (hclear : ∀ i, i ≠ j0 →
      cellTupleF rs mS t n i < mS + 2 * n + 1 + s ∨
        mS + 2 * n + 1 + e ≤ cellTupleF rs mS t n i)
    (hspan : ∀ l_bd,
      T ≤ l_bd → l_bd < N →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      s ≤ l ∧ l < e ∧ s ≤ l_bd ∧ l_bd < e ∧
        T ≤ l - s ∧ T ≤ l_bd - s ∧ T ≤ e - 1 - l ∧ T ≤ e - 1 - l_bd) :
    SufClearWindow rs j0 mS n t l N pc T := by
  intro l_bd hTlbd hlbdN hshift
  obtain ⟨hsl, hle, hslbd, hlbde, hTls, hTlbds, hTel, hTelbd⟩ :=
    hspan l_bd hTlbd hlbdN hshift
  exact ⟨s, e, hse, hem, hsl, hle, hslbd, hlbde, hclear, hTls, hTlbds, hTel, hTelbd⟩

/-- Raw one-coordinate prefix middle-band collapse.  Unlike
`prefStretch_middle_update_step`, this does not assume the other coordinates
are already finite-realized; it only performs the safe slide of `j0`, returning
the moved coordinate's finite representative together with gate preservation
and rank non-increase. -/
theorem prefStretch_middle_update_step_raw
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hwindow : ∀ q_bd,
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ q ∧ q < e ∧ s ≤ q_bd ∧ q_bd < e ∧
        (∀ i, i ≠ j0 → cellTupleF rs mS t n i < s ∨ e ≤ cellTupleF rs mS t n i) ∧
        T ≤ q - s ∧ T ≤ q_bd - s ∧ T ≤ e - 1 - q ∧ T ≤ e - 1 - q_bd)
    (hgate : gateF Mc rs mS t n) :
    ∃ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx q_bd) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n)) := by
  obtain ⟨q_bd, x, _hxcoord, hxreal, _hxpos, hTqbd, hqbdN, hshift, hval⟩ :=
    prefStretch_boundary_eq_coordCand P c j0 q_U q_D (cellTupleF rs mS t n) mS n t q
      N pc T F hpc hMpc hF hag hMq hqN hNmS hNM hMpcN
  obtain ⟨s, e, hse, heL, hsq, hqe, hsbd, hbde, hclear, hg1, hg2, hg3, hg4⟩ :=
    hwindow q_bd hTqbd hqbdN hshift
  have hgate' : gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n := by
    rcases hshift with ⟨κ, hκ⟩ | ⟨κ, hκ⟩
    · exact gateF_prefIdx_update_shift Mc mS n t hm rs j0 s e q q_bd κ T pc hsrc
        hgateCyc hse heL hsq hqe hsbd hbde hclear hg1 hg2 hg3 hg4 (Or.inr hκ) hgate
    · exact gateF_prefIdx_update_shift Mc mS n t hm rs j0 s e q q_bd κ T pc hsrc
        hgateCyc hse heL hsq hqe hsbd hbde hclear hg1 hg2 hg3 hg4 (Or.inl hκ) hgate
  have hcj0 : cellTupleF rs mS t n j0 = q := by
    simp only [cellTupleF, hsrc, RegionSpecF.posAt]
  have hu1 : Function.update (cellTupleF rs mS t n) j0 q = cellTupleF rs mS t n := by
    funext i
    by_cases hi : i = j0
    · subst hi
      rw [Function.update_self]
      exact hcj0.symm
    · rw [Function.update_of_ne hi]
  have hu2 : Function.update (cellTupleF rs mS t n) j0 q_bd =
      cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n := by
    rw [cellTupleF_update_prefIdx]
  refine ⟨q_bd, x, hxreal, hgate', ?_⟩
  rw [← hu1, ← hu2]
  exact hval

/-- Bounded prefix raw step: the chosen finite representative is returned
together with the stretch-window bounds and residue relation used to move it. -/
theorem prefStretch_middle_update_step_raw_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hwindow : ∀ q_bd,
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ q ∧ q < e ∧ s ≤ q_bd ∧ q_bd < e ∧
        (∀ i, i ≠ j0 → cellTupleF rs mS t n i < s ∨ e ≤ cellTupleF rs mS t n i) ∧
        T ≤ q - s ∧ T ≤ q_bd - s ∧ T ≤ e - 1 - q ∧ T ≤ e - 1 - q_bd)
    (hgate : gateF Mc rs mS t n) :
    ∃ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx q_bd) ∧
      T ≤ q_bd ∧ q_bd < N ∧
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n)) := by
  obtain ⟨q_bd, x, _hxcoord, hxreal, _hxpos, hTqbd, hqbdN, hshift, hval⟩ :=
    prefStretch_boundary_eq_coordCand P c j0 q_U q_D (cellTupleF rs mS t n) mS n t q
      N pc T F hpc hMpc hF hag hMq hqN hNmS hNM hMpcN
  obtain ⟨s, e, hse, heL, hsq, hqe, hsbd, hbde, hclear, hg1, hg2, hg3, hg4⟩ :=
    hwindow q_bd hTqbd hqbdN hshift
  have hgate' : gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n := by
    rcases hshift with ⟨κ, hκ⟩ | ⟨κ, hκ⟩
    · exact gateF_prefIdx_update_shift Mc mS n t hm rs j0 s e q q_bd κ T pc hsrc
        hgateCyc hse heL hsq hqe hsbd hbde hclear hg1 hg2 hg3 hg4 (Or.inr hκ) hgate
    · exact gateF_prefIdx_update_shift Mc mS n t hm rs j0 s e q q_bd κ T pc hsrc
        hgateCyc hse heL hsq hqe hsbd hbde hclear hg1 hg2 hg3 hg4 (Or.inl hκ) hgate
  have hcj0 : cellTupleF rs mS t n j0 = q := by
    simp only [cellTupleF, hsrc, RegionSpecF.posAt]
  have hu1 : Function.update (cellTupleF rs mS t n) j0 q = cellTupleF rs mS t n := by
    funext i
    by_cases hi : i = j0
    · subst hi
      rw [Function.update_self]
      exact hcj0.symm
    · rw [Function.update_of_ne hi]
  have hu2 : Function.update (cellTupleF rs mS t n) j0 q_bd =
      cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n := by
    rw [cellTupleF_update_prefIdx]
  refine ⟨q_bd, x, hxreal, hTqbd, hqbdN, hshift, hgate', ?_⟩
  rw [← hu1, ← hu2]
  exact hval

/-- Prefix raw step plus partial-invariant update: after sliding `j0`, the
finite-realized set grows by `j0`. -/
theorem prefStretch_middle_update_step_on
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hwindow : ∀ q_bd,
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ q ∧ q < e ∧ s ≤ q_bd ∧ q_bd < e ∧
        (∀ i, i ≠ j0 → cellTupleF rs mS t n i < s ∨ e ≤ cellTupleF rs mS t n i) ∧
        T ≤ q - s ∧ T ≤ q_bd - s ∧ T ≤ e - 1 - q ∧ T ≤ e - 1 - q_bd)
    (hgate : gateF Mc rs mS t n) :
    ∃ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx q_bd) ∧
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n)) := by
  obtain ⟨q_bd, x, hxreal, hgate', hval⟩ :=
    prefStretch_middle_update_step_raw P c Mc q_U q_D rs j0 mS n t q N pc T F
      hm hsrc hpc hMpc hF hag hMq hqN hNmS hNM hMpcN hgateCyc hwindow hgate
  refine ⟨q_bd, x, hxreal, ?_, hgate', hval⟩
  exact CoordwiseRealizableOn.update_insert hdone ⟨x, hxreal⟩

/-- Bounded prefix scheduled step with an arbitrary clear-window proof.  This
is the generic one-coordinate move needed by the multi-coordinate scheduler:
it preserves the partial `done` invariant and exposes the selected boundary
index plus residue relation for later no-crossing bookkeeping. -/
theorem prefStretch_middle_update_step_on_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hwindow : ∀ q_bd,
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ q ∧ q < e ∧ s ≤ q_bd ∧ q_bd < e ∧
        (∀ i, i ≠ j0 → cellTupleF rs mS t n i < s ∨ e ≤ cellTupleF rs mS t n i) ∧
        T ≤ q - s ∧ T ≤ q_bd - s ∧ T ≤ e - 1 - q ∧ T ≤ e - 1 - q_bd)
    (hgate : gateF Mc rs mS t n) :
    ∃ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx q_bd) ∧
      T ≤ q_bd ∧ q_bd < N ∧
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) ∧
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n)) := by
  obtain ⟨q_bd, x, hxreal, hTqbd, hqbdN, hshift, hgate', hval⟩ :=
    prefStretch_middle_update_step_raw_bounded P c Mc q_U q_D rs j0 mS n t q N pc T F
      hm hsrc hpc hMpc hF hag hMq hqN hNmS hNM hMpcN hgateCyc hwindow hgate
  refine ⟨q_bd, x, hxreal, hTqbd, hqbdN, hshift, ?_, hgate', hval⟩
  exact CoordwiseRealizableOn.update_insert hdone ⟨x, hxreal⟩

/-- Prefix scheduled step with the clear window discharged by a strong
no-crossing hypothesis: every other coordinate lies outside the whole U-prefix
run.  This is the arbitrary-arity analogue of the arity-1 vacuous window for a
single active prefix coordinate. -/
theorem prefStretch_middle_update_step_on_no_other_pref
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hNright : N + T ≤ mS - 1) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hnoPref : ∀ i, i ≠ j0 → mS - 1 ≤ cellTupleF rs mS t n i)
    (hgate : gateF Mc rs mS t n) :
    ∃ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx q_bd) ∧
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n)) := by
  refine prefStretch_middle_update_step_on P c Mc q_U q_D rs done j0 mS n t q N pc T F
    hm hsrc hpc hMpc hF hag hMq hqN hNmS hNM hMpcN hgateCyc hdone ?_ hgate
  intro q_bd hTqbd hqbdN hshift
  clear hshift hNM
  refine ⟨0, mS - 1, Nat.zero_le _, le_rfl, Nat.zero_le _, ?_,
    Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro i hi
    exact Or.inr (hnoPref i hi)
  · omega
  · omega
  · omega
  · omega

/-- Bounded prefix no-crossing step with partial-invariant update. -/
theorem prefStretch_middle_update_step_on_no_other_pref_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hNright : N + T ≤ mS - 1) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hnoPref : ∀ i, i ≠ j0 → mS - 1 ≤ cellTupleF rs mS t n i)
    (hgate : gateF Mc rs mS t n) :
    ∃ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx q_bd) ∧
      T ≤ q_bd ∧ q_bd < N ∧
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) ∧
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n)) := by
  have hwindow : ∀ q_bd,
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ q ∧ q < e ∧ s ≤ q_bd ∧ q_bd < e ∧
        (∀ i, i ≠ j0 → cellTupleF rs mS t n i < s ∨ e ≤ cellTupleF rs mS t n i) ∧
        T ≤ q - s ∧ T ≤ q_bd - s ∧ T ≤ e - 1 - q ∧ T ≤ e - 1 - q_bd := by
    intro q_bd hTqbd hqbdN hshift
    clear hshift hNM
    refine ⟨0, mS - 1, Nat.zero_le _, le_rfl, Nat.zero_le _, ?_,
      Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro i hi
      exact Or.inr (hnoPref i hi)
    · omega
    · omega
    · omega
    · omega
  obtain ⟨q_bd, x, hxreal, hTqbd, hqbdN, hshift, hgate', hstep⟩ :=
    prefStretch_middle_update_step_raw_bounded P c Mc q_U q_D rs j0 mS n t q
      N pc T F hm hsrc hpc hMpc hF hag hMq hqN hNmS hNM hMpcN
      hgateCyc hwindow hgate
  refine ⟨q_bd, x, hxreal, hTqbd, hqbdN, hshift, ?_, hgate', hstep⟩
  exact CoordwiseRealizableOn.update_insert hdone ⟨x, hxreal⟩

/-- Prefix no-crossing step with a full coordinatewise invariant.  This is the
`hrest` variant of `prefStretch_middle_update_step_on_no_other_pref`: after the
single safe slide, every coordinate is finite-realizable. -/
theorem prefStretch_middle_update_step_no_other_pref
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hNright : N + T ≤ mS - 1) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hrest : ∀ i, i ≠ j0 → ∃ x, CoordCandRealizes q_U q_D mS x (rs i))
    (hnoPref : ∀ i, i ≠ j0 → mS - 1 ≤ cellTupleF rs mS t n i)
    (hgate : gateF Mc rs mS t n) :
    ∃ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx q_bd) ∧
      CoordwiseRealizable q_U q_D mS
        (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n)) := by
  obtain ⟨q_bd, x, hxreal, _hdone, hgate', hstep⟩ :=
    prefStretch_middle_update_step_on_no_other_pref P c Mc q_U q_D rs ∅ j0 mS n t q
      N pc T F hm hsrc hpc hMpc hF hag hMq hqN hNmS hNM hNright hMpcN
      hgateCyc CoordwiseRealizableOn.empty hnoPref hgate
  refine ⟨q_bd, x, hxreal, ?_, hgate', hstep⟩
  exact CoordwiseRealizable.update hrest ⟨x, hxreal⟩

/-- One prefix-coordinate middle-band collapse step.  The boundary lemma chooses
the finite representative depth `q_bd`; the caller supplies a clear window for
sliding the mark there.  The result packages the three induction facts needed
for arbitrary arity: the moved coordinate is realised by a finite candidate,
the coordinatewise-realizable invariant is updated, and both gate preservation
and rank non-increase hold for the updated descriptor tuple. -/
theorem prefStretch_middle_update_step
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hrest : ∀ i, i ≠ j0 → ∃ x, CoordCandRealizes q_U q_D mS x (rs i))
    (hwindow : ∀ q_bd,
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ q ∧ q < e ∧ s ≤ q_bd ∧ q_bd < e ∧
        (∀ i, i ≠ j0 → cellTupleF rs mS t n i < s ∨ e ≤ cellTupleF rs mS t n i) ∧
        T ≤ q - s ∧ T ≤ q_bd - s ∧ T ≤ e - 1 - q ∧ T ≤ e - 1 - q_bd)
    (hgate : gateF Mc rs mS t n) :
    ∃ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx q_bd) ∧
      CoordwiseRealizable q_U q_D mS (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS t n)) := by
  obtain ⟨q_bd, x, hxreal, hgate', hval⟩ :=
    prefStretch_middle_update_step_raw P c Mc q_U q_D rs j0 mS n t q N pc T F
      hm hsrc hpc hMpc hF hag hMq hqN hNmS hNM hMpcN hgateCyc hwindow hgate
  refine ⟨q_bd, x, hxreal, ?_, hgate', hval⟩
  exact CoordwiseRealizable.update hrest ⟨x, hxreal⟩

/-- Raw one-coordinate suffix middle-band collapse.  This is the D-suffix
counterpart of `prefStretch_middle_update_step_raw`: it slides only `j0`, with
no finite-realization assumption on the other coordinates. -/
theorem sufStretch_middle_update_step_raw
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (j0 : Fin (P.toPoly.arity c)) (mS n t l N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.sufIdx l)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : T ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hwindow : ∀ l_bd,
      T ≤ l_bd → l_bd < N →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ l ∧ l < e ∧ s ≤ l_bd ∧ l_bd < e ∧
        (∀ i, i ≠ j0 →
          cellTupleF rs mS t n i < mS + 2 * n + 1 + s ∨
            mS + 2 * n + 1 + e ≤ cellTupleF rs mS t n i) ∧
        T ≤ l - s ∧ T ≤ l_bd - s ∧ T ≤ e - 1 - l ∧ T ≤ e - 1 - l_bd)
    (hgate : gateF Mc rs mS t n) :
    ∃ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx l_bd) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n)) := by
  obtain ⟨l_bd, x, _hxcoord, hxreal, _hxpos, hTlbd, hlbdN, hshift, hval⟩ :=
    sufStretch_boundary_eq_coordCand P c j0 q_U q_D (cellTupleF rs mS t n) mS n t l
      N pc T F hpc hMpc hF hag hMl hlN hNmS hNM hMpcN
  obtain ⟨s, e, hse, heL, hsl, hle, hsbd, hbde, hclear, hg1, hg2, hg3, hg4⟩ :=
    hwindow l_bd hTlbd hlbdN hshift
  have hgate' : gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n := by
    rcases hshift with ⟨κ, hκ⟩ | ⟨κ, hκ⟩
    · exact gateF_sufIdx_update_shift Mc mS n t hm rs j0 s e l l_bd κ T pc hsrc
        hgateCyc hse heL hsl hle hsbd hbde hclear hg1 hg2 hg3 hg4 (Or.inr hκ) hgate
    · exact gateF_sufIdx_update_shift Mc mS n t hm rs j0 s e l l_bd κ T pc hsrc
        hgateCyc hse heL hsl hle hsbd hbde hclear hg1 hg2 hg3 hg4 (Or.inl hκ) hgate
  have hcj0 : cellTupleF rs mS t n j0 = mS + 2 * n + 1 + l := by
    simp only [cellTupleF, hsrc, RegionSpecF.posAt]
  have hu1 : Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l)
      = cellTupleF rs mS t n := by
    funext i
    by_cases hi : i = j0
    · subst hi
      rw [Function.update_self]
      exact hcj0.symm
    · rw [Function.update_of_ne hi]
  have hu2 : Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l_bd) =
      cellTupleF (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n := by
    rw [cellTupleF_update_sufIdx]
  refine ⟨l_bd, x, hxreal, hgate', ?_⟩
  rw [← hu1, ← hu2]
  exact hval

/-- Bounded suffix raw step: the chosen finite representative is returned
together with the stretch-window bounds and residue relation used to move it. -/
theorem sufStretch_middle_update_step_raw_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (j0 : Fin (P.toPoly.arity c)) (mS n t l N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.sufIdx l)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : T ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hwindow : ∀ l_bd,
      T ≤ l_bd → l_bd < N →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ l ∧ l < e ∧ s ≤ l_bd ∧ l_bd < e ∧
        (∀ i, i ≠ j0 →
          cellTupleF rs mS t n i < mS + 2 * n + 1 + s ∨
            mS + 2 * n + 1 + e ≤ cellTupleF rs mS t n i) ∧
        T ≤ l - s ∧ T ≤ l_bd - s ∧ T ≤ e - 1 - l ∧ T ≤ e - 1 - l_bd)
    (hgate : gateF Mc rs mS t n) :
    ∃ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx l_bd) ∧
      T ≤ l_bd ∧ l_bd < N ∧
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n)) := by
  obtain ⟨l_bd, x, _hxcoord, hxreal, _hxpos, hTlbd, hlbdN, hshift, hval⟩ :=
    sufStretch_boundary_eq_coordCand P c j0 q_U q_D (cellTupleF rs mS t n) mS n t l
      N pc T F hpc hMpc hF hag hMl hlN hNmS hNM hMpcN
  obtain ⟨s, e, hse, heL, hsl, hle, hsbd, hbde, hclear, hg1, hg2, hg3, hg4⟩ :=
    hwindow l_bd hTlbd hlbdN hshift
  have hgate' : gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n := by
    rcases hshift with ⟨κ, hκ⟩ | ⟨κ, hκ⟩
    · exact gateF_sufIdx_update_shift Mc mS n t hm rs j0 s e l l_bd κ T pc hsrc
        hgateCyc hse heL hsl hle hsbd hbde hclear hg1 hg2 hg3 hg4 (Or.inr hκ) hgate
    · exact gateF_sufIdx_update_shift Mc mS n t hm rs j0 s e l l_bd κ T pc hsrc
        hgateCyc hse heL hsl hle hsbd hbde hclear hg1 hg2 hg3 hg4 (Or.inl hκ) hgate
  have hcj0 : cellTupleF rs mS t n j0 = mS + 2 * n + 1 + l := by
    simp only [cellTupleF, hsrc, RegionSpecF.posAt]
  have hu1 : Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l)
      = cellTupleF rs mS t n := by
    funext i
    by_cases hi : i = j0
    · subst hi
      rw [Function.update_self]
      exact hcj0.symm
    · rw [Function.update_of_ne hi]
  have hu2 : Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l_bd) =
      cellTupleF (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n := by
    rw [cellTupleF_update_sufIdx]
  refine ⟨l_bd, x, hxreal, hTlbd, hlbdN, hshift, hgate', ?_⟩
  rw [← hu1, ← hu2]
  exact hval

/-- Suffix raw step plus partial-invariant update: after sliding `j0`, the
finite-realized set grows by `j0`. -/
theorem sufStretch_middle_update_step_on
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t l N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.sufIdx l)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : T ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hwindow : ∀ l_bd,
      T ≤ l_bd → l_bd < N →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ l ∧ l < e ∧ s ≤ l_bd ∧ l_bd < e ∧
        (∀ i, i ≠ j0 →
          cellTupleF rs mS t n i < mS + 2 * n + 1 + s ∨
            mS + 2 * n + 1 + e ≤ cellTupleF rs mS t n i) ∧
        T ≤ l - s ∧ T ≤ l_bd - s ∧ T ≤ e - 1 - l ∧ T ≤ e - 1 - l_bd)
    (hgate : gateF Mc rs mS t n) :
    ∃ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx l_bd) ∧
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n)) := by
  obtain ⟨l_bd, x, hxreal, hgate', hval⟩ :=
    sufStretch_middle_update_step_raw P c Mc q_U q_D rs j0 mS n t l N pc T F
      hm hsrc hpc hMpc hF hag hMl hlN hNmS hNM hMpcN hgateCyc hwindow hgate
  refine ⟨l_bd, x, hxreal, ?_, hgate', hval⟩
  exact CoordwiseRealizableOn.update_insert hdone ⟨x, hxreal⟩

/-- Bounded suffix scheduled step with an arbitrary clear-window proof. -/
theorem sufStretch_middle_update_step_on_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t l N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.sufIdx l)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : T ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hwindow : ∀ l_bd,
      T ≤ l_bd → l_bd < N →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ l ∧ l < e ∧ s ≤ l_bd ∧ l_bd < e ∧
        (∀ i, i ≠ j0 →
          cellTupleF rs mS t n i < mS + 2 * n + 1 + s ∨
            mS + 2 * n + 1 + e ≤ cellTupleF rs mS t n i) ∧
        T ≤ l - s ∧ T ≤ l_bd - s ∧ T ≤ e - 1 - l ∧ T ≤ e - 1 - l_bd)
    (hgate : gateF Mc rs mS t n) :
    ∃ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx l_bd) ∧
      T ≤ l_bd ∧ l_bd < N ∧
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) ∧
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n)) := by
  obtain ⟨l_bd, x, hxreal, hTlbd, hlbdN, hshift, hgate', hval⟩ :=
    sufStretch_middle_update_step_raw_bounded P c Mc q_U q_D rs j0 mS n t l N pc T F
      hm hsrc hpc hMpc hF hag hMl hlN hNmS hNM hMpcN hgateCyc hwindow hgate
  refine ⟨l_bd, x, hxreal, hTlbd, hlbdN, hshift, ?_, hgate', hval⟩
  exact CoordwiseRealizableOn.update_insert hdone ⟨x, hxreal⟩

/-- Suffix scheduled step with the clear window discharged by a strong
no-crossing hypothesis: every other coordinate lies before the whole D-suffix
run.  This is the suffix analogue of
`prefStretch_middle_update_step_on_no_other_pref`. -/
theorem sufStretch_middle_update_step_on_no_other_suf
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t l N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.sufIdx l)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : T ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hNright : N + T ≤ mS - 1) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hnoSuf : ∀ i, i ≠ j0 → cellTupleF rs mS t n i < mS + 2 * n + 1)
    (hgate : gateF Mc rs mS t n) :
    ∃ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx l_bd) ∧
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n)) := by
  refine sufStretch_middle_update_step_on P c Mc q_U q_D rs done j0 mS n t l N pc T F
    hm hsrc hpc hMpc hF hag hMl hlN hNmS hNM hMpcN hgateCyc hdone ?_ hgate
  intro l_bd hTlbd hlbdN hshift
  clear hshift hNM
  refine ⟨0, mS - 1, Nat.zero_le _, le_rfl, Nat.zero_le _, ?_,
    Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro i hi
    exact Or.inl (hnoSuf i hi)
  · omega
  · omega
  · omega
  · omega

/-- Bounded suffix no-crossing step with partial-invariant update. -/
theorem sufStretch_middle_update_step_on_no_other_suf_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t l N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.sufIdx l)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : T ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hNright : N + T ≤ mS - 1) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hnoSuf : ∀ i, i ≠ j0 → cellTupleF rs mS t n i < mS + 2 * n + 1)
    (hgate : gateF Mc rs mS t n) :
    ∃ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx l_bd) ∧
      T ≤ l_bd ∧ l_bd < N ∧
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) ∧
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) ∧
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n)
          (cellTupleF (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS t n)) := by
  have hwindow : ∀ l_bd,
      T ≤ l_bd → l_bd < N →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      ∃ s e, s ≤ e ∧ e ≤ mS - 1 ∧ s ≤ l ∧ l < e ∧ s ≤ l_bd ∧ l_bd < e ∧
        (∀ i, i ≠ j0 →
          cellTupleF rs mS t n i < mS + 2 * n + 1 + s ∨
            mS + 2 * n + 1 + e ≤ cellTupleF rs mS t n i) ∧
        T ≤ l - s ∧ T ≤ l_bd - s ∧ T ≤ e - 1 - l ∧ T ≤ e - 1 - l_bd := by
    intro l_bd hTlbd hlbdN hshift
    clear hshift hNM
    refine ⟨0, mS - 1, Nat.zero_le _, le_rfl, Nat.zero_le _, ?_,
      Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro i hi
      exact Or.inl (hnoSuf i hi)
    · omega
    · omega
    · omega
    · omega
  obtain ⟨l_bd, x, hxreal, hTlbd, hlbdN, hshift, hgate', hstep⟩ :=
    sufStretch_middle_update_step_raw_bounded P c Mc q_U q_D rs j0 mS n t l
      N pc T F hm hsrc hpc hMpc hF hag hMl hlN hNmS hNM hMpcN
      hgateCyc hwindow hgate
  refine ⟨l_bd, x, hxreal, hTlbd, hlbdN, hshift, ?_, hgate', hstep⟩
  exact CoordwiseRealizableOn.update_insert hdone ⟨x, hxreal⟩

/-- Coordinatewise version of `cell_collapse_to_coordCand_of_deepShape`: if each
coordinate of `rs` is realised, at the current row, by some finite
`coordCands` descriptor, then these descriptors assemble into a mixed tuple and
the cell collapses without moving any marks. -/
theorem cell_collapse_to_coordCand_of_coordwise_deepShape
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (mS n t : ℕ)
    (hcoord : CoordwiseRealizable q_U q_D mS rs)
    (hgate : gateF Mc rs mS t n) :
    ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF Mc (deepShapeF ds mS) mS t n ∧
      ¬ WRP.lexLt (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
                  (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
  classical
  choose ds hds using hcoord
  refine cell_collapse_to_coordCand_of_deepShape P c Mc q_U q_D rs ds mS n t
    (fun i => (hds i).1) ?_ hgate
  funext i
  exact (hds i).2

/-- Chain one non-increasing descriptor update into a later finite-candidate
collapse.  This is the lexicographic glue for iterating raw coordinate moves:
if `rs` does not rank below `rs'`, and `rs'` collapses to a finite mixed tuple,
then `rs` collapses to the same mixed tuple. -/
theorem cell_collapse_to_coordCand_of_nonincreasing_update
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs rs' : Fin (P.toPoly.arity c) → RegionSpecF B)
    (mS n t : ℕ)
    (hstep : ¬ WRP.lexLt
      (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
      (P.rank c (copiedSlice mS n) (cellTupleF rs' mS t n)))
    (hcollapse : ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF Mc (deepShapeF ds mS) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs' mS t n))
        (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n))) :
    ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF Mc (deepShapeF ds mS) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
  obtain ⟨ds, hds, hgate, htail⟩ := hcollapse
  exact ⟨ds, hds, hgate, lexLt_negtrans _ _ _ hstep htail⟩

/-- If a non-increasing update reaches a coordinatewise-realizable descriptor,
then the original descriptor already has a finite-candidate collapse. -/
theorem cell_collapse_to_coordCand_of_coordwise_update
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs rs' : Fin (P.toPoly.arity c) → RegionSpecF B)
    (mS n t : ℕ)
    (hstep : ¬ WRP.lexLt
      (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
      (P.rank c (copiedSlice mS n) (cellTupleF rs' mS t n)))
    (hcoord' : CoordwiseRealizable q_U q_D mS rs')
    (hgate' : gateF Mc rs' mS t n) :
    ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF Mc (deepShapeF ds mS) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) :=
  cell_collapse_to_coordCand_of_nonincreasing_update P c Mc q_U q_D rs rs' mS n t hstep
    (cell_collapse_to_coordCand_of_coordwise_deepShape P c Mc q_U q_D rs' mS n t hcoord'
      hgate')

/-- Finite-chain form of the update glue.  A scheduler may build any finite
sequence of descriptor tuples, provided each adjacent step is rank
non-increasing and the final tuple is coordinatewise-realizable with the gate
ON.  This isolates the lexicographic chaining needed by the multi-coordinate
middle-band collapse. -/
theorem cell_collapse_to_coordCand_of_nonincreasing_update_chain
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (mS n t : ℕ)
    (N : ℕ)
    (rsAt : ℕ → Fin (P.toPoly.arity c) → RegionSpecF B)
    (hsteps : ∀ s, s < N →
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF (rsAt s) mS t n))
        (P.rank c (copiedSlice mS n) (cellTupleF (rsAt (s + 1)) mS t n)))
    (hcoordN : CoordwiseRealizable q_U q_D mS (rsAt N))
    (hgateN : gateF Mc (rsAt N) mS t n) :
    ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF Mc (deepShapeF ds mS) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF (rsAt 0) mS t n))
        (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
  induction N generalizing rsAt with
  | zero =>
      simpa using
        cell_collapse_to_coordCand_of_coordwise_deepShape P c Mc q_U q_D
          (rsAt 0) mS n t hcoordN hgateN
  | succ N ih =>
      have htail :
          ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
            gateF Mc (deepShapeF ds mS) mS t n ∧
            ¬ WRP.lexLt
              (P.rank c (copiedSlice mS n) (cellTupleF (rsAt 1) mS t n))
              (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
        refine ih (fun s => rsAt (s + 1)) ?_ ?_ ?_
        · intro s hs
          simpa [Nat.add_assoc] using hsteps (s + 1) (Nat.succ_lt_succ hs)
        · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcoordN
        · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hgateN
      exact cell_collapse_to_coordCand_of_nonincreasing_update P c Mc q_U q_D
        (rsAt 0) (rsAt 1) mS n t (hsteps 0 (Nat.zero_lt_succ N)) htail

/-- Bounded continuation form for a prefix move whose clear window is the whole
prefix run.  The tail receives the boundary depth bounds and residue relation
needed for subsequent scheduled moves. -/
theorem cell_collapse_to_coordCand_bind_pref_step_on_no_other_pref_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hNright : N + T ≤ mS - 1) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hnoPref : ∀ i, i ≠ j0 → mS - 1 ≤ cellTupleF rs mS t n i)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q_bd) →
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n →
      ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
        gateF Mc (deepShapeF ds mS) mS t n ∧
        ¬ WRP.lexLt
          (P.rank c (copiedSlice mS n)
            (cellTupleF (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n))
          (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n))) :
    ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF Mc (deepShapeF ds mS) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
  obtain ⟨q_bd, x, hxreal, hTqbd, hqbdN, hshift, hdone', hgate', hstep⟩ :=
    prefStretch_middle_update_step_on_no_other_pref_bounded P c Mc q_U q_D rs done j0
      mS n t q N pc T F hm hsrc hpc hMpc hF hag hMq hqN hNmS hNM hNright
      hMpcN hgateCyc hdone hnoPref hgate
  exact cell_collapse_to_coordCand_of_nonincreasing_update P c Mc q_U q_D rs
    (Function.update rs j0 (RegionSpecF.prefIdx q_bd)) mS n t hstep
    (htail q_bd x hxreal hTqbd hqbdN hshift hdone' hgate')

/-- Bounded continuation form for a suffix move whose clear window is the whole
suffix run.  The tail receives the boundary depth bounds and residue relation
needed for subsequent scheduled moves. -/
theorem cell_collapse_to_coordCand_bind_suf_step_on_no_other_suf_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t l N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.sufIdx l)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : T ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hNright : N + T ≤ mS - 1) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hnoSuf : ∀ i, i ≠ j0 → cellTupleF rs mS t n i < mS + 2 * n + 1)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l_bd) →
      T ≤ l_bd → l_bd < N →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n →
      ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
        gateF Mc (deepShapeF ds mS) mS t n ∧
        ¬ WRP.lexLt
          (P.rank c (copiedSlice mS n)
            (cellTupleF (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n))
          (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n))) :
    ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF Mc (deepShapeF ds mS) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
  obtain ⟨l_bd, x, hxreal, hTlbd, hlbdN, hshift, hdone', hgate', hstep⟩ :=
    sufStretch_middle_update_step_on_no_other_suf_bounded P c Mc q_U q_D rs done j0
      mS n t l N pc T F hm hsrc hpc hMpc hF hag hMl hlN hNmS hNM hNright
      hMpcN hgateCyc hdone hnoSuf hgate
  exact cell_collapse_to_coordCand_of_nonincreasing_update P c Mc q_U q_D rs
    (Function.update rs j0 (RegionSpecF.sufIdx l_bd)) mS n t hstep
    (htail l_bd x hxreal hTlbd hlbdN hshift hdone' hgate')

/-- **d3.4 arity-1 step 5: collapse dstar's (single-coordinate) cell onto a `coordCands` candidate.**
For an arity-1 copy `c`, a valid gated-ON cell `rs` collapses to a tuple `ds ∈ mixedTuplesF` that is
still gated-ON and whose rank lex-dominates the original cell rank.  Because the cell has ONE coordinate
the gate move (`accepts_copiedSlice_suf_shift` / `_pref_shift`) has a VACUOUS clear-window, and the value
domination is a single application of step 4 (no crossing, no chaining). -/
theorem cell_collapse_to_coordCand_one
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (harity1 : P.toPoly.arity c = 1)
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 → P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (mS n t : ℕ) (hm : 1 ≤ mS)
    (hvalid : ∀ i, (rs i).valid mS)
    (hgate : gateF Mc rs mS t n)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS) :
    ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF Mc (deepShapeF ds mS) mS t n ∧
      ¬ WRP.lexLt (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
                  (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
  have hsub : Subsingleton (Fin (P.toPoly.arity c)) := by rw [harity1]; infer_instance
  have j0 : Fin (P.toPoly.arity c) := ⟨0, by rw [harity1]; omega⟩
  -- NO-MOVE helper: a descriptor `x ∈ coordCands` whose deep-shape is `rs` discharges the goal.
  have hno : ∀ x : RegionSpecF B ⊕ (ℕ ⊕ ℕ), x ∈ coordCands B q_U q_D →
      deepShapeF (fun _ => x) mS = rs →
      ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
        gateF Mc (deepShapeF ds mS) mS t n ∧
        ¬ WRP.lexLt (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
                    (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
    intro x hx hdeq
    exact cell_collapse_to_coordCand_of_deepShape P c Mc q_U q_D rs (fun _ => x) mS n t
      (fun _ => hx) hdeq hgate
  rcases hrs : rs j0 with r | q | l
  · -- CORE: no move
    refine hno (Sum.inl (RegionSpecF.core r)) ?_ ?_
    · rw [mem_coordCands]; exact Or.inl ⟨r, rfl⟩
    · funext i; have hi : i = j0 := Subsingleton.elim i j0
      subst hi; simp only [deepShapeF]; exact hrs.symm
  · -- PREFIX
    by_cases hqsh : q < q_U
    · -- shallow: no move
      refine hno (Sum.inl (RegionSpecF.prefIdx q)) ?_ ?_
      · rw [mem_coordCands]; exact Or.inr (Or.inl ⟨q, hqsh, rfl⟩)
      · funext i; have hi : i = j0 := Subsingleton.elim i j0
        subst hi; simp only [deepShapeF]; exact hrs.symm
    · by_cases hqdeep : mS - 1 - q_U < q
      · -- deep: no move via inr (inr (mS-1-q))
        have hqv : q < mS - 1 := by have := hvalid j0; rw [hrs] at this; exact this
        refine hno (Sum.inr (Sum.inr (mS - 1 - q))) ?_ ?_
        · rw [mem_coordCands]
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨mS - 1 - q, by omega, by omega, rfl⟩)))
        · funext i; have hi : i = j0 := Subsingleton.elim i j0
          subst hi; simp only [deepShapeF]; rw [hrs]
          exact congrArg RegionSpecF.prefIdx (Nat.sub_sub_self (le_of_lt hqv))
      · -- MIDDLE prefix: q_U ≤ q < mS-1-q_U; collapse via prefix step 4
        push Not at hqsh hqdeep
        have hqv : q < mS - 1 := by have := hvalid j0; rw [hrs] at this; exact this
        obtain ⟨pc, T, hpc, hTq, hgateCyc, hrankD⟩ := hprefData j0
        obtain ⟨F, hF, hag⟩ := hrankD (cellTupleF rs mS t n) mS n
        obtain ⟨q_bd, x, hxcoord, _hxreal, hxpos, hMqbd, hqbdN, hshift, hval⟩ :=
          prefStretch_boundary_eq_coordCand P c j0 q_U q_D (cellTupleF rs mS t n) mS n t q
            (mS - 1 - T) pc T F hpc hTq hF hag (by omega) (by omega) (by omega) (by omega) (by omega)
        have hcj0 : cellTupleF rs mS t n j0 = q := by
          simp only [cellTupleF, hrs, RegionSpecF.posAt]
        refine ⟨fun _ => x, (mem_mixedTuplesF _).mpr (fun _ => hxcoord), ?_, ?_⟩
        · -- GATE move (prefix)
          have hae1 : q < mS - 1 := by clear hshift; omega
          have hae2 : q_bd < mS - 1 := by clear hshift; omega
          have hg1 : T ≤ q - 0 := by clear hshift; omega
          have hg2 : T ≤ q_bd - 0 := by clear hshift; omega
          have hg3 : T ≤ mS - 1 - 1 - q := by clear hshift; omega
          have hg4 : T ≤ mS - 1 - 1 - q_bd := by clear hshift; omega
          have hj0' : mixedTupleF (fun _ => x) mS t n j0 = q_bd := by
            simp only [mixedTupleF]; exact hxpos
          have hmove : ∀ (κ' : ℕ), (q_bd = q + pc * κ' ∨ q = q_bd + pc * κ') →
              (Mc.accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) (cellTupleF rs mS t n))
                ↔ Mc.accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n)
                    (mixedTupleF (fun _ => x) mS t n))) :=
            fun κ' hsh => accepts_copiedSlice_pref_shift Mc mS n hm (cellTupleF rs mS t n)
              (mixedTupleF (fun _ => x) mS t n) j0 0 (mS - 1) q q_bd κ' T pc hgateCyc
              (fun i hi => absurd (Subsingleton.elim i j0) hi)
              (Nat.zero_le _) (le_refl _) (Nat.zero_le _) hae1 (Nat.zero_le _) hae2
              hcj0 hj0' (fun i hi => absurd (Subsingleton.elim i j0) hi)
              hg1 hg2 hg3 hg4 hsh
          unfold gateF
          rw [cellTupleF_deepShapeF (fun _ => x) mS t n]
          rcases hshift with ⟨κ', hκ'⟩ | ⟨κ', hκ'⟩
          · exact (hmove κ' (Or.inr hκ')).mp hgate
          · exact (hmove κ' (Or.inl hκ')).mp hgate
        · -- VALUE
          have hu1 : Function.update (cellTupleF rs mS t n) j0 q = cellTupleF rs mS t n := by
            funext i; have hi : i = j0 := Subsingleton.elim i j0
            subst hi; rw [Function.update_self]; exact hcj0.symm
          have hu2 : Function.update (cellTupleF rs mS t n) j0 q_bd
              = mixedTupleF (fun _ => x) mS t n := by
            funext i; have hi : i = j0 := Subsingleton.elim i j0
            subst hi; rw [Function.update_self]; simp only [mixedTupleF]; exact hxpos.symm
          rw [← hu1, ← hu2]; exact hval
  · -- SUFFIX
    by_cases hlsh : l < q_D
    · -- shallow: no move
      refine hno (Sum.inl (RegionSpecF.sufIdx l)) ?_ ?_
      · rw [mem_coordCands]; exact Or.inr (Or.inr (Or.inl ⟨l, hlsh, rfl⟩))
      · funext i; have hi : i = j0 := Subsingleton.elim i j0
        subst hi; simp only [deepShapeF]; exact hrs.symm
    · by_cases hldeep : mS - 1 - q_D < l
      · -- deep: no move via inr (inl (mS-1-l))
        have hlv : l < mS - 1 := by have := hvalid j0; rw [hrs] at this; exact this
        refine hno (Sum.inr (Sum.inl (mS - 1 - l))) ?_ ?_
        · rw [mem_coordCands]
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨mS - 1 - l, by omega, by omega, rfl⟩)))
        · funext i; have hi : i = j0 := Subsingleton.elim i j0
          subst hi; simp only [deepShapeF]; rw [hrs]
          exact congrArg RegionSpecF.sufIdx (Nat.sub_sub_self (le_of_lt hlv))
      · -- MIDDLE suffix: q_D ≤ l < mS-1-q_D; collapse via suffix step 4
        push Not at hlsh hldeep
        have hlv : l < mS - 1 := by have := hvalid j0; rw [hrs] at this; exact this
        obtain ⟨pc, T, hpc, hTq, hgateCyc, hrankD⟩ := hsufData j0
        obtain ⟨F, hF, hag⟩ := hrankD (cellTupleF rs mS t n) mS n
        obtain ⟨l_bd, x, hxcoord, _hxreal, hxpos, hMlbd, hlbdN, hshift, hval⟩ :=
          sufStretch_boundary_eq_coordCand P c j0 q_U q_D (cellTupleF rs mS t n) mS n t l
            (mS - 1 - T) pc T F hpc hTq hF hag (by omega) (by omega) (by omega) (by omega) (by omega)
        have hcj0 : cellTupleF rs mS t n j0 = mS + 2 * n + 1 + l := by
          simp only [cellTupleF, hrs, RegionSpecF.posAt]
        refine ⟨fun _ => x, (mem_mixedTuplesF _).mpr (fun _ => hxcoord), ?_, ?_⟩
        · -- GATE move (suffix)
          have hae1 : l < mS - 1 := by clear hshift; omega
          have hae2 : l_bd < mS - 1 := by clear hshift; omega
          have hg1 : T ≤ l - 0 := by clear hshift; omega
          have hg2 : T ≤ l_bd - 0 := by clear hshift; omega
          have hg3 : T ≤ mS - 1 - 1 - l := by clear hshift; omega
          have hg4 : T ≤ mS - 1 - 1 - l_bd := by clear hshift; omega
          have hj0' : mixedTupleF (fun _ => x) mS t n j0 = mS + 2 * n + 1 + l_bd := by
            simp only [mixedTupleF]; exact hxpos
          have hmove : ∀ (κ' : ℕ), (l_bd = l + pc * κ' ∨ l = l_bd + pc * κ') →
              (Mc.accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) (cellTupleF rs mS t n))
                ↔ Mc.accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n)
                    (mixedTupleF (fun _ => x) mS t n))) :=
            fun κ' hsh => accepts_copiedSlice_suf_shift Mc mS n hm (cellTupleF rs mS t n)
              (mixedTupleF (fun _ => x) mS t n) j0 0 (mS - 1) l l_bd κ' T pc hgateCyc
              (fun i hi => absurd (Subsingleton.elim i j0) hi)
              (Nat.zero_le _) (le_refl _) (Nat.zero_le _) hae1 (Nat.zero_le _) hae2
              hcj0 hj0' (fun i hi => absurd (Subsingleton.elim i j0) hi)
              hg1 hg2 hg3 hg4 hsh
          unfold gateF
          rw [cellTupleF_deepShapeF (fun _ => x) mS t n]
          rcases hshift with ⟨κ', hκ'⟩ | ⟨κ', hκ'⟩
          · exact (hmove κ' (Or.inr hκ')).mp hgate
          · exact (hmove κ' (Or.inl hκ')).mp hgate
        · -- VALUE
          have hu1 : Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l)
              = cellTupleF rs mS t n := by
            funext i; have hi : i = j0 := Subsingleton.elim i j0
            subst hi; rw [Function.update_self]; exact hcj0.symm
          have hu2 : Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l_bd)
              = mixedTupleF (fun _ => x) mS t n := by
            funext i; have hi : i = j0 := Subsingleton.elim i j0
            subst hi; rw [Function.update_self]; simp only [mixedTupleF]; exact hxpos.symm
          rw [← hu1, ← hu2]; exact hval

/-- **Arity-1 single-position cover (mS-route).**  At fixed `n ≥ 2B` and any `mS ≥ 1`, the single
coordinate of an in-range arity-1 tuple is described by a valid `RegionSpecF B` descriptor at a base
`t ∈ [B, n-B]`.  Pure position arithmetic: prefix-stretch `< mS-1` → `prefIdx`; suffix-stretch
`≥ mS+2n+1` → `sufIdx`; the core `[mS-1, mS+2n]` decomposes the underlying `W_n` position into a
`RegionSpec` (pre / suf / front / back / cluster) — no clustering threshold (one coordinate). -/
theorem cells_cover_one_mS (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (harity1 : P.toPoly.arity c = 1) (B : ℕ) (hB1 : 1 ≤ B)
    (mS n : ℕ) (hm : 1 ≤ mS) (hn : 2 * B ≤ n)
    (ī : Fin (P.toPoly.arity c) → ℕ) (hī : ∀ i, ī i < (copiedSlice mS n).length) :
    ∃ (t : ℕ) (rs : Fin (P.toPoly.arity c) → RegionSpecF B),
      B ≤ t ∧ t + B ≤ n ∧ (∀ i, (rs i).valid mS) ∧ ī = cellTupleF rs mS t n := by
  have hsub : Subsingleton (Fin (P.toPoly.arity c)) := by rw [harity1]; infer_instance
  have j0 : Fin (P.toPoly.arity c) := ⟨0, by rw [harity1]; omega⟩
  set p : ℕ := ī j0 with hpdef
  have hplt : p < 2 * (mS + n) := by
    have := hī j0; rwa [length_copiedSlice] at this
  -- assemble: a valid descriptor with posAt = p discharges the goal (subsingleton ⟹ constant tuple)
  have mk : ∀ (t : ℕ) (desc : RegionSpecF B), B ≤ t → t + B ≤ n →
      desc.valid mS → desc.posAt mS t n = p →
      ∃ (t : ℕ) (rs : Fin (P.toPoly.arity c) → RegionSpecF B),
        B ≤ t ∧ t + B ≤ n ∧ (∀ i, (rs i).valid mS) ∧ ī = cellTupleF rs mS t n := by
    intro t desc htB htn hv hpos
    refine ⟨t, fun _ => desc, htB, htn, fun _ => hv, ?_⟩
    funext i
    show ī i = desc.posAt mS t n
    rw [Subsingleton.elim i j0, ← hpdef]
    exact hpos.symm
  rcases position_cases_copied mS p n hm hplt with
    hpre | hbL | ⟨hjn, hmid⟩ | hbR | hsuf
  · -- prefix stretch
    exact mk B (RegionSpecF.prefIdx p) (le_refl B) (by omega)
      (by simp [RegionSpecF.valid]; omega) (by simp [RegionSpecF.posAt])
  · -- boundary-left p = mS-1 → core pre
    refine mk B (RegionSpecF.core RegionSpec.pre) (le_refl B) (by omega) trivial ?_
    simp [RegionSpecF.posAt, RegionSpec.posAt]; omega
  · -- core / middle block
    set j : ℕ := (p - mS) / 2 with hjdef
    by_cases hjB : j < B
    · -- front block
      rcases hmid with hp0 | hp1
      · exact mk B (RegionSpecF.core (RegionSpec.front ⟨j, hjB⟩ false)) (le_refl B) (by omega) trivial
          (by simp [RegionSpecF.posAt, RegionSpec.posAt]; omega)
      · exact mk B (RegionSpecF.core (RegionSpec.front ⟨j, hjB⟩ true)) (le_refl B) (by omega) trivial
          (by simp [RegionSpecF.posAt, RegionSpec.posAt]; omega)
    · by_cases hjnB : n - B ≤ j
      · -- back block: l = n-1-j < B
        have hlB : n - 1 - j < B := by omega
        rcases hmid with hp0 | hp1
        · exact mk B (RegionSpecF.core (RegionSpec.back ⟨n - 1 - j, hlB⟩ false)) (le_refl B) (by omega)
            trivial (by simp [RegionSpecF.posAt, RegionSpec.posAt]; omega)
        · exact mk B (RegionSpecF.core (RegionSpec.back ⟨n - 1 - j, hlB⟩ true)) (le_refl B) (by omega)
            trivial (by simp [RegionSpecF.posAt, RegionSpec.posAt]; omega)
      · -- cluster block at base t = j (δ = 0)
        push Not at hjB hjnB
        rcases hmid with hp0 | hp1
        · exact mk j (RegionSpecF.core (RegionSpec.cluster ⟨0, hB1⟩ false)) hjB (by omega) trivial
            (by simp [RegionSpecF.posAt, RegionSpec.posAt]; omega)
        · exact mk j (RegionSpecF.core (RegionSpec.cluster ⟨0, hB1⟩ true)) hjB (by omega) trivial
            (by simp [RegionSpecF.posAt, RegionSpec.posAt]; omega)
  · -- boundary-right p = mS+2n → core suf
    refine mk B (RegionSpecF.core RegionSpec.suf) (le_refl B) (by omega) trivial ?_
    simp [RegionSpecF.posAt, RegionSpec.posAt]; omega
  · -- suffix stretch: l = p - (mS+2n+1)
    refine mk B (RegionSpecF.sufIdx (p - (mS + 2 * n + 1))) (le_refl B) (by omega) ?_ ?_
    · simp [RegionSpecF.valid]; omega
    · simp [RegionSpecF.posAt]; omega

/-- A `mixedTuplesF` descriptor has a valid `deepShapeF` once the prefix/suffix boundary bands
fit inside the slice. -/
theorem mixedTuplesF_deepShape_valid {B q_U q_D k mS : ℕ}
    {ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)}
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hds : ds ∈ mixedTuplesF B q_U q_D k) :
    ∀ i, (deepShapeF ds mS i).valid mS := by
  intro i
  have hcoords : ∀ j, ds j ∈ coordCands B q_U q_D := (mem_mixedTuplesF ds).mp hds
  rcases (mem_coordCands (ds i)).mp (hcoords i) with
    ⟨r, hr⟩ | ⟨q, hq, hr⟩ | ⟨l, hl, hr⟩ | ⟨io, hio1, hio2, hr⟩ | ⟨io, hio1, hio2, hr⟩
  · simp only [deepShapeF, hr, RegionSpecF.valid]
  · simp only [deepShapeF, hr, RegionSpecF.valid]; omega
  · simp only [deepShapeF, hr, RegionSpecF.valid]; omega
  · simp only [deepShapeF, hr, RegionSpecF.valid]; omega
  · simp only [deepShapeF, hr, RegionSpecF.valid]; omega

/-- If the selector automaton gate is ON for a mixed tuple, that tuple is a selected `D` atom. -/
theorem mixedTupleF_gate_selectedD
    (P : WRP.Presentation Step Step)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMc : ∀ (c : Fin P.toPoly.K) (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
      (∀ i, ī i < w.length) →
      ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
        (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    {B q_U q_D n mS : ℕ} {c : Fin P.toPoly.K} {t : ℕ}
    {ds : Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ)}
    (hm : 1 ≤ mS) (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (htn : t + B ≤ n) (hdsmem : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c))
    (hgate : gateF (Mc c) (deepShapeF ds mS) mS t n) :
    P.toPoly.selectedAtom (copiedSlice mS n)
        (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom) ∧
      P.toPoly.labelOf (copiedSlice mS n)
        (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom) = D := by
  classical
  have hshapeValid : ∀ i, (deepShapeF ds mS i).valid mS :=
    mixedTuplesF_deepShape_valid hmSq hmSu hdsmem
  have hposCell : ∀ i, cellTupleF (deepShapeF ds mS) mS t n i < (copiedSlice mS n).length :=
    cellTupleF_valid (deepShapeF ds mS) mS t n hm hshapeValid htn
  have hpos : ∀ i, mixedTupleF ds mS t n i < (copiedSlice mS n).length := by
    intro i
    simpa [cellTupleF_deepShapeF ds mS t n] using hposCell i
  have hacc : (Mc c).accepts (markAtN (P.toPoly.arity c)
      (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
    simpa [gateF, cellTupleF_deepShapeF ds mS t n] using hgate
  obtain ⟨hsel, hlabel⟩ :=
    (hMc c (copiedSlice mS n) (mixedTupleF ds mS t n) hpos).mp hacc
  exact ⟨⟨hpos, hsel⟩, hlabel⟩

/-- Fixed-row selected-`D` representative theorem factored through two local
interfaces: a cover of the selected atom by a fibred cell, and a collapse of
that cell to a finite mixed tuple.  The arity-1 theorem below instantiates these
interfaces with `cells_cover_one_mS` and `cell_collapse_to_coordCand_one`; the
arbitrary-arity route should instantiate them with the fibred growth cover and
the scheduled collapse. -/
theorem selectedD_achiever_mixedTuple_rank_representative_of_cover_collapse
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    {B : ℕ}
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMc : ∀ (c : Fin P.toPoly.K) (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
      (∀ i, ī i < w.length) →
      ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
        (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (q_U q_D n mS : ℕ) (hm : 1 ≤ mS)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hcover : ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
      P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ →
      ∃ (t : ℕ) (rs : Fin (P.toPoly.arity c) → RegionSpecF B),
        B ≤ t ∧ t + B ≤ n ∧ (∀ i, (rs i).valid mS) ∧ ī = cellTupleF rs mS t n)
    (hcollapse : ∀ (c : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t : ℕ),
      (∀ i, (rs i).valid mS) →
      gateF (Mc c) rs mS t n →
      ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
        gateF (Mc c) (deepShapeF ds mS) mS t n ∧
        ¬ WRP.lexLt
          (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
          (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)))
    (b : P.toPoly.Atom)
    (hbsel : P.toPoly.selectedAtom (copiedSlice mS n) b)
    (hbD : P.toPoly.labelOf (copiedSlice mS n) b = D)
    (hbrank : P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n) :
    ∃ (c : Fin P.toPoly.K) (t : ℕ)
      (ds : Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      B ≤ t ∧ t + B ≤ n ∧
      ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF (Mc c) (deepShapeF ds mS) mS t n ∧
      P.toPoly.selectedAtom (copiedSlice mS n)
        (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom) ∧
      P.toPoly.labelOf (copiedSlice mS n)
        (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom) = D ∧
      P.rankOf (copiedSlice mS n) (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom)
        = CopiedDstar.dstarRankGA_m P hV mS n := by
  classical
  obtain ⟨c, ī⟩ := b
  obtain ⟨t, rs, htB, htn, hrsvalid, hīeq⟩ := hcover c ī hbsel
  have hpos_rs : ∀ i, cellTupleF rs mS t n i < (copiedSlice mS n).length :=
    cellTupleF_valid rs mS t n hm hrsvalid htn
  have hsel_rs : P.toPoly.sel c (copiedSlice mS n) (cellTupleF rs mS t n) := by
    have := hbsel.2
    rwa [hīeq] at this
  have hlabel_rs : P.toPoly.label c (copiedSlice mS n) (cellTupleF rs mS t n) = D := by
    show P.toPoly.label c (copiedSlice mS n) (cellTupleF rs mS t n) = D
    rwa [← hīeq]
  have hgate : gateF (Mc c) rs mS t n := by
    show (Mc c).accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) (cellTupleF rs mS t n))
    exact (hMc c (copiedSlice mS n) (cellTupleF rs mS t n) hpos_rs).mpr
      ⟨hsel_rs, hlabel_rs⟩
  obtain ⟨ds, hdsmem, hdsgate, hdsval⟩ := hcollapse c rs t hrsvalid hgate
  obtain ⟨hselD, hlabelD⟩ :=
    mixedTupleF_gate_selectedD P Mc hMc hm hmSq hmSu htn hdsmem hdsgate
  have hcell_rank : P.rank c (copiedSlice mS n) (cellTupleF rs mS t n)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
    show P.rank c (copiedSlice mS n) (cellTupleF rs mS t n) = _
    rwa [← hīeq]
  have hge_dstar : ¬ WRP.lexLt
      (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n))
      (CopiedDstar.dstarRankGA_m P hV mS n) := by
    have hmin := CopiedDstarC.dstarRankGA'_lex_min P hV (copiedSlice mS n)
      ⟨(⟨c, ī⟩ : P.toPoly.Atom), hbsel, hbD⟩
      (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom) hselD hlabelD
    simpa [CopiedDstar.dstarRankGA_m, WRP.Presentation.rankOf] using hmin
  have hle_dstar : ¬ WRP.lexLt (CopiedDstar.dstarRankGA_m P hV mS n)
      (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
    rw [← hcell_rank]
    exact hdsval
  have hrank_eq : P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
    rcases lexLt_trichot
        (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n))
        (CopiedDstar.dstarRankGA_m P hV mS n) with h | h | h
    · exact absurd h hge_dstar
    · exact h
    · exact absurd h hle_dstar
  refine ⟨c, t, ds, htB, htn, hdsmem, hdsgate, hselD, hlabelD, ?_⟩
  simpa [WRP.Presentation.rankOf] using hrank_eq

/-- Variant of
`selectedD_achiever_mixedTuple_rank_representative_of_cover_collapse` whose
cover hypothesis matches the coordinatewise output of `cells_cover_fibred`. -/
theorem selectedD_achiever_mixedTuple_rank_representative_of_coordinate_cover_collapse
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    {B : ℕ}
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMc : ∀ (c : Fin P.toPoly.K) (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
      (∀ i, ī i < w.length) →
      ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
        (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (q_U q_D n mS : ℕ) (hm : 1 ≤ mS)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hcoordCover : ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
      P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ →
      ∃ t : ℕ, B ≤ t ∧ t + B ≤ n ∧
        ∀ i, ∃ r : RegionSpecF B, r.valid mS ∧ ī i = r.posAt mS t n)
    (hcollapse : ∀ (c : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t : ℕ),
      (∀ i, (rs i).valid mS) →
      gateF (Mc c) rs mS t n →
      ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
        gateF (Mc c) (deepShapeF ds mS) mS t n ∧
        ¬ WRP.lexLt
          (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
          (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)))
    (b : P.toPoly.Atom)
    (hbsel : P.toPoly.selectedAtom (copiedSlice mS n) b)
    (hbD : P.toPoly.labelOf (copiedSlice mS n) b = D)
    (hbrank : P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n) :
    ∃ (c : Fin P.toPoly.K) (t : ℕ)
      (ds : Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      B ≤ t ∧ t + B ≤ n ∧
      ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF (Mc c) (deepShapeF ds mS) mS t n ∧
      P.toPoly.selectedAtom (copiedSlice mS n)
        (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom) ∧
      P.toPoly.labelOf (copiedSlice mS n)
        (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom) = D ∧
      P.rankOf (copiedSlice mS n) (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom)
        = CopiedDstar.dstarRankGA_m P hV mS n := by
  classical
  refine selectedD_achiever_mixedTuple_rank_representative_of_cover_collapse
    P hV Mc hMc q_U q_D n mS hm hmSq hmSu ?_ hcollapse b hbsel hbD hbrank
  intro c ī hsel
  obtain ⟨t, htB, htn, hcoord⟩ := hcoordCover c ī hsel
  choose rs hrs using hcoord
  refine ⟨t, rs, htB, htn, fun i => (hrs i).1, ?_⟩
  funext i
  exact (hrs i).2

/-- Window-aware coordinate-cover variant of
`selectedD_achiever_mixedTuple_rank_representative_of_coordinate_cover_collapse`.
The collapse interface receives the cover bounds `B ≤ t` and `t + B ≤ n`,
which are needed by the general-arity no-crossing collapse wrappers. -/
theorem selectedD_achiever_mixedTuple_rank_representative_of_coordinate_cover_collapse_window
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    {B : ℕ}
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMc : ∀ (c : Fin P.toPoly.K) (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
      (∀ i, ī i < w.length) →
      ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
        (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (q_U q_D n mS : ℕ) (hm : 1 ≤ mS)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hcoordCover : ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
      P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ →
      ∃ t : ℕ, B ≤ t ∧ t + B ≤ n ∧
        ∀ i, ∃ r : RegionSpecF B, r.valid mS ∧ ī i = r.posAt mS t n)
    (hcollapse : ∀ (c : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t : ℕ),
      B ≤ t → t + B ≤ n →
      (∀ i, (rs i).valid mS) →
      gateF (Mc c) rs mS t n →
      ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
        gateF (Mc c) (deepShapeF ds mS) mS t n ∧
        ¬ WRP.lexLt
          (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
          (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)))
    (b : P.toPoly.Atom)
    (hbsel : P.toPoly.selectedAtom (copiedSlice mS n) b)
    (hbD : P.toPoly.labelOf (copiedSlice mS n) b = D)
    (hbrank : P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n) :
    ∃ (c : Fin P.toPoly.K) (t : ℕ)
      (ds : Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      B ≤ t ∧ t + B ≤ n ∧
      ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF (Mc c) (deepShapeF ds mS) mS t n ∧
      P.toPoly.selectedAtom (copiedSlice mS n)
        (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom) ∧
      P.toPoly.labelOf (copiedSlice mS n)
        (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom) = D ∧
      P.rankOf (copiedSlice mS n) (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom)
        = CopiedDstar.dstarRankGA_m P hV mS n := by
  classical
  obtain ⟨c, ī⟩ := b
  obtain ⟨t, htB, htn, hcoord⟩ := hcoordCover c ī hbsel
  choose rs hrs using hcoord
  have hrsvalid : ∀ i, (rs i).valid mS := fun i => (hrs i).1
  have hīeq : ī = cellTupleF rs mS t n := by
    funext i
    exact (hrs i).2
  have hpos_rs : ∀ i, cellTupleF rs mS t n i < (copiedSlice mS n).length :=
    cellTupleF_valid rs mS t n hm hrsvalid htn
  have hsel_rs : P.toPoly.sel c (copiedSlice mS n) (cellTupleF rs mS t n) := by
    have := hbsel.2
    rwa [hīeq] at this
  have hlabel_rs : P.toPoly.label c (copiedSlice mS n) (cellTupleF rs mS t n) = D := by
    show P.toPoly.label c (copiedSlice mS n) (cellTupleF rs mS t n) = D
    rwa [← hīeq]
  have hgate : gateF (Mc c) rs mS t n := by
    show (Mc c).accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) (cellTupleF rs mS t n))
    exact (hMc c (copiedSlice mS n) (cellTupleF rs mS t n) hpos_rs).mpr
      ⟨hsel_rs, hlabel_rs⟩
  obtain ⟨ds, hdsmem, hdsgate, hdsval⟩ := hcollapse c rs t htB htn hrsvalid hgate
  obtain ⟨hselD, hlabelD⟩ :=
    mixedTupleF_gate_selectedD P Mc hMc hm hmSq hmSu htn hdsmem hdsgate
  have hcell_rank : P.rank c (copiedSlice mS n) (cellTupleF rs mS t n)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
    show P.rank c (copiedSlice mS n) (cellTupleF rs mS t n) = _
    rwa [← hīeq]
  have hge_dstar : ¬ WRP.lexLt
      (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n))
      (CopiedDstar.dstarRankGA_m P hV mS n) := by
    have hmin := CopiedDstarC.dstarRankGA'_lex_min P hV (copiedSlice mS n)
      ⟨(⟨c, ī⟩ : P.toPoly.Atom), hbsel, hbD⟩
      (⟨c, mixedTupleF ds mS t n⟩ : P.toPoly.Atom) hselD hlabelD
    simpa [CopiedDstar.dstarRankGA_m, WRP.Presentation.rankOf] using hmin
  have hle_dstar : ¬ WRP.lexLt (CopiedDstar.dstarRankGA_m P hV mS n)
      (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
    rw [← hcell_rank]
    exact hdsval
  have hrank_eq : P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
    rcases lexLt_trichot
        (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n))
        (CopiedDstar.dstarRankGA_m P hV mS n) with h | h | h
    · exact absurd h hge_dstar
    · exact h
    · exact absurd h hle_dstar
  refine ⟨c, t, ds, htB, htn, hdsmem, hdsgate, hselD, hlabelD, ?_⟩
  simpa [WRP.Presentation.rankOf] using hrank_eq

/-- Final selector endgame from a single ON `selCands` witness whose value is
the semantic `dstar` rank.  This separates the lexicographic `selB` argument
from the various ways of producing the finite mixed-tuple witness. -/
theorem dstarRankGA_m_eq_selB_of_selCands_witness
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    {B : ℕ}
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMc : ∀ (c : Fin P.toPoly.K) (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
      (∀ i, ī i < w.length) →
      ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
        (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (q_U q_D : ℕ) (hd : 0 < P.d) (n mS : ℕ) (hm : 1 ≤ mS)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hDpres : ∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
      P.toPoly.labelOf (copiedSlice mS n) a = D)
    (hwit : ∃ gf : (ℕ → Prop) × (ℕ → Fin P.d → ℤ),
      gf ∈ selCands B q_U q_D P Mc n ∧ gf.1 mS ∧
        gf.2 mS = CopiedDstar.dstarRankGA_m P hV mS n) :
    CopiedDstar.dstarRankGA_m P hV mS n = selB B q_U q_D P Mc n hd mS := by
  classical
  have hdsv : ∀ {k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      (∀ j, ds j ∈ coordCands B q_U q_D) → ∀ i, (deepShapeF ds mS i).valid mS := by
    intro k ds hds i
    rcases (mem_coordCands (ds i)).mp (hds i) with
      ⟨r, hr⟩ | ⟨q, hq, hr⟩ | ⟨l, hl, hr⟩ | ⟨io, hio1, hio2, hr⟩ | ⟨io, hio1, hio2, hr⟩
    · simp only [deepShapeF, hr, RegionSpecF.valid]
    · simp only [deepShapeF, hr, RegionSpecF.valid]; omega
    · simp only [deepShapeF, hr, RegionSpecF.valid]; omega
    · simp only [deepShapeF, hr, RegionSpecF.valid]; omega
    · simp only [deepShapeF, hr, RegionSpecF.valid]; omega
  have hge_dstar : ∀ gf ∈ selCands B q_U q_D P Mc n, gf.1 mS →
      ¬ WRP.lexLt (gf.2 mS) (CopiedDstar.dstarRankGA_m P hV mS n) := by
    intro gf hgf hon
    simp only [selCands, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hgf
    obtain ⟨c', _, t', ht'mem, ds', hds'mem, rfl⟩ := hgf
    have hcoords : ∀ j, ds' j ∈ coordCands B q_U q_D := (mem_mixedTuplesF ds').mp hds'mem
    have ht'win : t' + B ≤ n := by rw [Finset.mem_Icc] at ht'mem; omega
    have hpos' : ∀ i, cellTupleF (deepShapeF ds' mS) mS t' n i < (copiedSlice mS n).length :=
      cellTupleF_valid (deepShapeF ds' mS) mS t' n hm (hdsv ds' hcoords) ht'win
    have hacc : (Mc c').accepts (markAtN (P.toPoly.arity c')
        (copiedSlice mS n) (cellTupleF (deepShapeF ds' mS) mS t' n)) := hon
    obtain ⟨hsel', hlab'⟩ := (hMc c' (copiedSlice mS n)
      (cellTupleF (deepShapeF ds' mS) mS t' n) hpos').mp hacc
    have hatom : ¬ WRP.lexLt
        (P.rankOf (copiedSlice mS n) ⟨c', cellTupleF (deepShapeF ds' mS) mS t' n⟩)
        (CopiedDstar.dstarRankGA' P hV (copiedSlice mS n)) :=
      CopiedDstarC.dstarRankGA'_lex_min P hV (copiedSlice mS n) hDpres
        ⟨c', cellTupleF (deepShapeF ds' mS) mS t' n⟩ ⟨hpos', hsel'⟩ hlab'
    show ¬ WRP.lexLt (fun i => P.rank c' (copiedSlice mS n) (mixedTupleF ds' mS t' n) i)
      (CopiedDstar.dstarRankGA_m P hV mS n)
    have hval_eq : (fun i => P.rank c' (copiedSlice mS n) (mixedTupleF ds' mS t' n) i)
        = P.rankOf (copiedSlice mS n) ⟨c', cellTupleF (deepShapeF ds' mS) mS t' n⟩ := by
      show _ = P.rank c' (copiedSlice mS n) (cellTupleF (deepShapeF ds' mS) mS t' n)
      rw [cellTupleF_deepShapeF ds' mS t' n]
    rw [hval_eq]; exact hatom
  obtain ⟨gfd, hgfdmem, hgfd_on, hgfd_eq⟩ := hwit
  have hds_eq : CopiedDstar.dstarRankGA_m P hV mS n = gfd.2 mS := hgfd_eq.symm
  have hle_ds : ¬ WRP.lexLt (CopiedDstar.dstarRankGA_m P hV mS n) (gfd.2 mS) := by
    simpa [hds_eq] using lexLt_irrefl (gfd.2 mS)
  have hbigDom_gt : WRP.lexLt (CopiedDstar.dstarRankGA_m P hV mS n)
      (bigDom B q_U q_D P Mc n hd mS) := by
    rw [hds_eq]; exact selCands_lt_bigDom B q_U q_D P Mc n hd gfd hgfdmem mS
  have hdir1 : ¬ WRP.lexLt (CopiedDstar.dstarRankGA_m P hV mS n)
      (selB B q_U q_D P Mc n hd mS) := by
    have hle := selB_le_selCands_on B q_U q_D P Mc n hd mS gfd hgfdmem hgfd_on
    exact lexLt_negtrans _ _ _ hle_ds hle
  have hdir2 : ¬ WRP.lexLt (selB B q_U q_D P Mc n hd mS)
      (CopiedDstar.dstarRankGA_m P hV mS n) := by
    set L : List (ℕ → Fin P.d → ℤ) := bigDom B q_U q_D P Mc n hd ::
      (selCands B q_U q_D P Mc n).map
        (fun gf => fun mS' => if gf.1 mS' then gf.2 mS' else bigDom B q_U q_D P Mc n hd mS') with hLdef
    have hsel_eq : selB B q_U q_D P Mc n hd mS = lexMinList L mS := rfl
    obtain ⟨F, hFmem, hFeq⟩ := (lexMinList_le L (List.cons_ne_nil _ _) mS).2
    rw [hsel_eq, hFeq]
    rcases List.mem_cons.mp hFmem with rfl | hFmem'
    · exact lexLt_asymm _ _ hbigDom_gt
    · rw [List.mem_map] at hFmem'
      obtain ⟨gf', hgf'mem, rfl⟩ := hFmem'
      by_cases hon' : gf'.1 mS
      · simp only [if_pos hon']; exact hge_dstar gf' hgf'mem hon'
      · simp only [if_neg hon']; exact lexLt_asymm _ _ hbigDom_gt
  rcases lexLt_trichot (CopiedDstar.dstarRankGA_m P hV mS n) (selB B q_U q_D P Mc n hd mS) with h | h | h
  · exact absurd h hdir1
  · exact h
  · exact absurd h hdir2

/-- Window-aware coordinate-cover selector equality.  This is the version whose
collapse interface is suitable for the general-arity cell collapse theorem,
because the collapse receives the cover window bounds. -/
theorem dstarRankGA_m_eq_selB_of_coordinate_cover_collapse_window
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    {B : ℕ}
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMc : ∀ (c : Fin P.toPoly.K) (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
      (∀ i, ī i < w.length) →
      ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
        (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (q_U q_D : ℕ) (hd : 0 < P.d) (n mS : ℕ) (hm : 1 ≤ mS)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hcoordCover : ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
      P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ →
      ∃ t : ℕ, B ≤ t ∧ t + B ≤ n ∧
        ∀ i, ∃ r : RegionSpecF B, r.valid mS ∧ ī i = r.posAt mS t n)
    (hcollapse : ∀ (c : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t : ℕ),
      B ≤ t → t + B ≤ n →
      (∀ i, (rs i).valid mS) →
      gateF (Mc c) rs mS t n →
      ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
        gateF (Mc c) (deepShapeF ds mS) mS t n ∧
        ¬ WRP.lexLt
          (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
          (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)))
    (hDpres : ∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
      P.toPoly.labelOf (copiedSlice mS n) a = D) :
    CopiedDstar.dstarRankGA_m P hV mS n = selB B q_U q_D P Mc n hd mS := by
  classical
  obtain ⟨dstaratom, hdsel, hdD, _hdmin, hdrank⟩ :=
    CopiedDstar.dstarRankGA'_spec P hV (copiedSlice mS n) hDpres
  have hbrank : P.rankOf (copiedSlice mS n) dstaratom =
      CopiedDstar.dstarRankGA_m P hV mS n := by
    rw [CopiedDstar.dstarRankGA_m, hdrank]
  obtain ⟨c_d, t, ds, htB, htn, hdsmem, hdsgate, _hselD, _hlabelD, hrank⟩ :=
    selectedD_achiever_mixedTuple_rank_representative_of_coordinate_cover_collapse_window
      P hV Mc hMc q_U q_D n mS hm hmSq hmSu hcoordCover hcollapse
      dstaratom hdsel hdD hbrank
  set gfd : (ℕ → Prop) × (ℕ → Fin P.d → ℤ) :=
    (fun mS' => gateF (Mc c_d) (deepShapeF ds mS') mS' t n,
     fun mS' => fun i => P.rank c_d (copiedSlice mS' n) (mixedTupleF ds mS' t n) i) with hgfddef
  have hgfdmem : gfd ∈ selCands B q_U q_D P Mc n := by
    simp only [selCands, List.mem_flatMap, List.mem_map, Finset.mem_toList]
    exact ⟨c_d, List.mem_finRange c_d, t, Finset.mem_Icc.mpr ⟨htB, by omega⟩, ds, hdsmem, rfl⟩
  have hgfd_on : gfd.1 mS := hdsgate
  have hgfd_eq : gfd.2 mS = CopiedDstar.dstarRankGA_m P hV mS n := by
    dsimp [gfd]
    simpa [WRP.Presentation.rankOf] using hrank
  exact dstarRankGA_m_eq_selB_of_selCands_witness P hV Mc hMc q_U q_D hd n mS hm
    hmSq hmSu hDpres ⟨gfd, hgfdmem, hgfd_on, hgfd_eq⟩

/-- Selector equality factored through the two arity-free local interfaces:
a cover of the selected `D` atom by a fibred cell, and a collapse of that cell
to a finite `mixedTuplesF` candidate.  This is the reusable endgame for the
general-arity route; the remaining mathematical work is to supply
`hcollapse` without the arity-1 scheduler. -/
theorem dstarRankGA_m_eq_selB_of_cover_collapse
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    {B : ℕ}
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMc : ∀ (c : Fin P.toPoly.K) (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
      (∀ i, ī i < w.length) →
      ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
        (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (q_U q_D : ℕ) (hd : 0 < P.d) (n mS : ℕ) (hm : 1 ≤ mS)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hcover : ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
      P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ →
      ∃ (t : ℕ) (rs : Fin (P.toPoly.arity c) → RegionSpecF B),
        B ≤ t ∧ t + B ≤ n ∧ (∀ i, (rs i).valid mS) ∧ ī = cellTupleF rs mS t n)
    (hcollapse : ∀ (c : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t : ℕ),
      (∀ i, (rs i).valid mS) →
      gateF (Mc c) rs mS t n →
      ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
        gateF (Mc c) (deepShapeF ds mS) mS t n ∧
        ¬ WRP.lexLt
          (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
          (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)))
    (hDpres : ∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
      P.toPoly.labelOf (copiedSlice mS n) a = D) :
    CopiedDstar.dstarRankGA_m P hV mS n = selB B q_U q_D P Mc n hd mS := by
  classical
  have hdsv : ∀ {k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      (∀ j, ds j ∈ coordCands B q_U q_D) → ∀ i, (deepShapeF ds mS i).valid mS := by
    intro k ds hds i
    rcases (mem_coordCands (ds i)).mp (hds i) with
      ⟨r, hr⟩ | ⟨q, hq, hr⟩ | ⟨l, hl, hr⟩ | ⟨io, hio1, hio2, hr⟩ | ⟨io, hio1, hio2, hr⟩
    · simp only [deepShapeF, hr, RegionSpecF.valid]
    · simp only [deepShapeF, hr, RegionSpecF.valid]; omega
    · simp only [deepShapeF, hr, RegionSpecF.valid]; omega
    · simp only [deepShapeF, hr, RegionSpecF.valid]; omega
    · simp only [deepShapeF, hr, RegionSpecF.valid]; omega
  have hge_dstar : ∀ gf ∈ selCands B q_U q_D P Mc n, gf.1 mS →
      ¬ WRP.lexLt (gf.2 mS) (CopiedDstar.dstarRankGA_m P hV mS n) := by
    intro gf hgf hon
    simp only [selCands, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hgf
    obtain ⟨c', _, t', ht'mem, ds', hds'mem, rfl⟩ := hgf
    have hcoords : ∀ j, ds' j ∈ coordCands B q_U q_D := (mem_mixedTuplesF ds').mp hds'mem
    have ht'win : t' + B ≤ n := by rw [Finset.mem_Icc] at ht'mem; omega
    have hpos' : ∀ i, cellTupleF (deepShapeF ds' mS) mS t' n i < (copiedSlice mS n).length :=
      cellTupleF_valid (deepShapeF ds' mS) mS t' n hm (hdsv ds' hcoords) ht'win
    have hacc : (Mc c').accepts (markAtN (P.toPoly.arity c')
        (copiedSlice mS n) (cellTupleF (deepShapeF ds' mS) mS t' n)) := hon
    obtain ⟨hsel', hlab'⟩ := (hMc c' (copiedSlice mS n)
      (cellTupleF (deepShapeF ds' mS) mS t' n) hpos').mp hacc
    have hatom : ¬ WRP.lexLt
        (P.rankOf (copiedSlice mS n) ⟨c', cellTupleF (deepShapeF ds' mS) mS t' n⟩)
        (CopiedDstar.dstarRankGA' P hV (copiedSlice mS n)) :=
      CopiedDstarC.dstarRankGA'_lex_min P hV (copiedSlice mS n) hDpres
        ⟨c', cellTupleF (deepShapeF ds' mS) mS t' n⟩ ⟨hpos', hsel'⟩ hlab'
    show ¬ WRP.lexLt (fun i => P.rank c' (copiedSlice mS n) (mixedTupleF ds' mS t' n) i)
      (CopiedDstar.dstarRankGA_m P hV mS n)
    have hval_eq : (fun i => P.rank c' (copiedSlice mS n) (mixedTupleF ds' mS t' n) i)
        = P.rankOf (copiedSlice mS n) ⟨c', cellTupleF (deepShapeF ds' mS) mS t' n⟩ := by
      show _ = P.rank c' (copiedSlice mS n) (cellTupleF (deepShapeF ds' mS) mS t' n)
      rw [cellTupleF_deepShapeF ds' mS t' n]
    rw [hval_eq]; exact hatom
  obtain ⟨dstaratom, hdsel, hdD, _hdmin, hdrank⟩ :=
    CopiedDstar.dstarRankGA'_spec P hV (copiedSlice mS n) hDpres
  have hbrank : P.rankOf (copiedSlice mS n) dstaratom =
      CopiedDstar.dstarRankGA_m P hV mS n := by
    rw [CopiedDstar.dstarRankGA_m, hdrank]
  obtain ⟨c_d, t, ds, htB, htn, hdsmem, hdsgate, _hselD, _hlabelD, hrank⟩ :=
    selectedD_achiever_mixedTuple_rank_representative_of_cover_collapse
      P hV Mc hMc q_U q_D n mS hm hmSq hmSu hcover hcollapse
      dstaratom hdsel hdD hbrank
  set gfd : (ℕ → Prop) × (ℕ → Fin P.d → ℤ) :=
    (fun mS' => gateF (Mc c_d) (deepShapeF ds mS') mS' t n,
     fun mS' => fun i => P.rank c_d (copiedSlice mS' n) (mixedTupleF ds mS' t n) i) with hgfddef
  have hgfdmem : gfd ∈ selCands B q_U q_D P Mc n := by
    simp only [selCands, List.mem_flatMap, List.mem_map, Finset.mem_toList]
    exact ⟨c_d, List.mem_finRange c_d, t, Finset.mem_Icc.mpr ⟨htB, by omega⟩, ds, hdsmem, rfl⟩
  have hgfd_on : gfd.1 mS := hdsgate
  have hgfd_eq : gfd.2 mS = CopiedDstar.dstarRankGA_m P hV mS n := by
    dsimp [gfd]
    simpa [WRP.Presentation.rankOf] using hrank
  have hds_eq : CopiedDstar.dstarRankGA_m P hV mS n = gfd.2 mS := hgfd_eq.symm
  have hle_ds : ¬ WRP.lexLt (CopiedDstar.dstarRankGA_m P hV mS n) (gfd.2 mS) := by
    simpa [hds_eq] using lexLt_irrefl (gfd.2 mS)
  have hge_ds : ¬ WRP.lexLt (gfd.2 mS) (CopiedDstar.dstarRankGA_m P hV mS n) :=
    hge_dstar gfd hgfdmem hgfd_on
  have hbigDom_gt : WRP.lexLt (CopiedDstar.dstarRankGA_m P hV mS n)
      (bigDom B q_U q_D P Mc n hd mS) := by
    rw [hds_eq]; exact selCands_lt_bigDom B q_U q_D P Mc n hd gfd hgfdmem mS
  have hdir1 : ¬ WRP.lexLt (CopiedDstar.dstarRankGA_m P hV mS n)
      (selB B q_U q_D P Mc n hd mS) := by
    have hle := selB_le_selCands_on B q_U q_D P Mc n hd mS gfd hgfdmem hgfd_on
    exact lexLt_negtrans _ _ _ hle_ds hle
  have hdir2 : ¬ WRP.lexLt (selB B q_U q_D P Mc n hd mS)
      (CopiedDstar.dstarRankGA_m P hV mS n) := by
    set L : List (ℕ → Fin P.d → ℤ) := bigDom B q_U q_D P Mc n hd ::
      (selCands B q_U q_D P Mc n).map
        (fun gf => fun mS' => if gf.1 mS' then gf.2 mS' else bigDom B q_U q_D P Mc n hd mS') with hLdef
    have hsel_eq : selB B q_U q_D P Mc n hd mS = lexMinList L mS := rfl
    obtain ⟨F, hFmem, hFeq⟩ := (lexMinList_le L (List.cons_ne_nil _ _) mS).2
    rw [hsel_eq, hFeq]
    rcases List.mem_cons.mp hFmem with rfl | hFmem'
    · exact lexLt_asymm _ _ hbigDom_gt
    · rw [List.mem_map] at hFmem'
      obtain ⟨gf', hgf'mem, rfl⟩ := hFmem'
      by_cases hon' : gf'.1 mS
      · simp only [if_pos hon']; exact hge_dstar gf' hgf'mem hon'
      · simp only [if_neg hon']; exact lexLt_asymm _ _ hbigDom_gt
  rcases lexLt_trichot (CopiedDstar.dstarRankGA_m P hV mS n) (selB B q_U q_D P Mc n hd mS) with h | h | h
  · exact absurd h hdir1
  · exact h
  · exact absurd h hdir2

theorem dstarRankGA_m_eq_selB
    (P : WRP.Presentation Step Step) (hV : P.Valid) (harity1 : ∀ c, P.toPoly.arity c = 1)
    {B : ℕ} (hB1 : 1 ≤ B)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMc : ∀ (c : Fin P.toPoly.K) (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
      (∀ i, ī i < w.length) →
      ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
        (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (q_U q_D : ℕ)
    (hsufData : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (hprefData : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 → P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (hd : 0 < P.d) (n mS : ℕ) (hm : 1 ≤ mS) (hn2B : 2 * B ≤ n)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hDpres : ∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
      P.toPoly.labelOf (copiedSlice mS n) a = D) :
    CopiedDstar.dstarRankGA_m P hV mS n = selB B q_U q_D P Mc n hd mS := by
  refine dstarRankGA_m_eq_selB_of_cover_collapse P hV Mc hMc q_U q_D hd n mS hm
    hmSq hmSu ?_ ?_ hDpres
  · intro c ī hsel
    exact cells_cover_one_mS P c (harity1 c) B hB1 mS n hm hn2B ī hsel.1
  · intro c rs t hrsvalid hgate
    exact cell_collapse_to_coordCand_one P c (Mc c) (harity1 c) q_U q_D
      (hsufData c) (hprefData c) rs mS n t hm hrsvalid hgate hmSq hmSu

/-- Window-aware cell-collapse interface: every valid gated fibred cell in the
cover window collapses to a finite `mixedTuplesF` descriptor that preserves the
gate and lex-dominates the original cell rank.  The general-arity proof project
still has to supply this interface without the arity-1 scheduler. -/
def WindowedCellCollapse (P : WRP.Presentation Step Step) {B : ℕ}
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (q_U q_D n mS : ℕ) : Prop :=
  ∀ (c : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t : ℕ),
    B ≤ t → t + B ≤ n →
    (∀ i, (rs i).valid mS) →
    gateF (Mc c) rs mS t n →
    ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF (Mc c) (deepShapeF ds mS) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n))

/-- Scheduler-shaped window-collapse interface.  Instead of directly returning
the final mixed tuple, it returns a finite sequence of descriptor updates whose
rank is non-increasing at every adjacent step and whose final descriptor tuple
is coordinatewise-realizable. -/
def WindowedCellCollapseChain (P : WRP.Presentation Step Step) {B : ℕ}
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (q_U q_D n mS : ℕ) : Prop :=
  ∀ (c : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t : ℕ),
    B ≤ t → t + B ≤ n →
    (∀ i, (rs i).valid mS) →
    gateF (Mc c) rs mS t n →
    ∃ (N : ℕ) (rsAt : ℕ → Fin (P.toPoly.arity c) → RegionSpecF B),
      rsAt 0 = rs ∧
      (∀ s, s < N →
        ¬ WRP.lexLt
          (P.rank c (copiedSlice mS n) (cellTupleF (rsAt s) mS t n))
          (P.rank c (copiedSlice mS n) (cellTupleF (rsAt (s + 1)) mS t n))) ∧
      CoordwiseRealizable q_U q_D mS (rsAt N) ∧
      gateF (Mc c) (rsAt N) mS t n

/-- Cell-local version of `WindowedCellCollapseChain`, useful while constructing
the scheduler one selected cell at a time. -/
def CellCollapseChain (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B) : Prop :=
  ∃ (N : ℕ) (rsAt : ℕ → Fin (P.toPoly.arity c) → RegionSpecF B),
    rsAt 0 = rs ∧
    (∀ s, s < N →
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF (rsAt s) mS t n))
        (P.rank c (copiedSlice mS n) (cellTupleF (rsAt (s + 1)) mS t n))) ∧
    CoordwiseRealizable q_U q_D mS (rsAt N) ∧
    gateF Mc (rsAt N) mS t n

/-- Assemble the global windowed chain interface from cell-local chains. -/
theorem windowedCellCollapseChain_of_cell_chains
    (P : WRP.Presentation Step Step)
    {B : ℕ}
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (q_U q_D n mS : ℕ)
    (hcell : ∀ (c : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t : ℕ),
      B ≤ t → t + B ≤ n →
      (∀ i, (rs i).valid mS) →
      gateF (Mc c) rs mS t n →
      CellCollapseChain P c (Mc c) q_U q_D mS n t rs) :
    WindowedCellCollapseChain P (B := B) Mc q_U q_D n mS := by
  intro c rs t htB htn hv hgate
  exact hcell c rs t htB htn hv hgate

/-- A coordinatewise-realizable cell has a zero-step collapse chain. -/
theorem cellCollapseChain_of_coordwise
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (hcoord : CoordwiseRealizable q_U q_D mS rs)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseChain P c Mc q_U q_D mS n t rs := by
  refine ⟨0, fun _ => rs, rfl, ?_, hcoord, hgate⟩
  intro s hs
  omega

/-- If the partial scheduler has marked every coordinate done, a gated cell
closes as a zero-step collapse chain. -/
theorem cellCollapseChain_of_coordwiseOn_univ
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (hdone : CoordwiseRealizableOn q_U q_D mS
      (Finset.univ : Finset (Fin (P.toPoly.arity c))) rs)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseChain P c Mc q_U q_D mS n t rs :=
  cellCollapseChain_of_coordwise P c Mc q_U q_D mS n t rs
    (CoordwiseRealizableOn.to_coordwise hdone) hgate

/-- Flexible version of `cellCollapseChain_of_coordwiseOn_univ`: it is enough
that the current `done` set contains every coordinate. -/
theorem cellCollapseChain_of_coordwiseOn_all
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    {done : Finset (Fin (P.toPoly.arity c))}
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hall : ∀ i, i ∈ done)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseChain P c Mc q_U q_D mS n t rs :=
  cellCollapseChain_of_coordwise P c Mc q_U q_D mS n t rs
    (CoordwiseRealizableOn.to_coordwise_of_forall_mem hdone hall) hgate

/-- Prepend one non-increasing update to an existing collapse chain.  This is
the induction step for the eventual multi-coordinate scheduler. -/
theorem cellCollapseChain_cons_update
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ)
    (rs rs' : Fin (P.toPoly.arity c) → RegionSpecF B)
    (hstep : ¬ WRP.lexLt
      (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
      (P.rank c (copiedSlice mS n) (cellTupleF rs' mS t n)))
    (htail : CellCollapseChain P c Mc q_U q_D mS n t rs') :
    CellCollapseChain P c Mc q_U q_D mS n t rs := by
  obtain ⟨N, rsAt, h0, hsteps, hcoordN, hgateN⟩ := htail
  let rsAt' : ℕ → Fin (P.toPoly.arity c) → RegionSpecF B :=
    fun s => if s = 0 then rs else rsAt (s - 1)
  refine ⟨N + 1, rsAt', by simp [rsAt'], ?_, ?_, ?_⟩
  · intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa [rsAt', h0] using hstep
    · have hs1 : s + 1 ≠ 0 := by omega
      have hlt : s - 1 < N := by omega
      have hsucc : (s + 1) - 1 = (s - 1) + 1 := by omega
      simpa [rsAt', hs0, hs1, hsucc] using hsteps (s - 1) hlt
  · have hN : N + 1 ≠ 0 := by omega
    have hsub : (N + 1) - 1 = N := by omega
    simpa [rsAt', hN, hsub] using hcoordN
  · have hN : N + 1 ≠ 0 := by omega
    have hsub : (N + 1) - 1 = N := by omega
    simpa [rsAt', hN, hsub] using hgateN

/-- A finite scheduler trace with a partial `done` invariant at every node.  The
list records the remaining scheduled coordinates; the constructors below will
later refine each cons step with the prefix/suffix clear-window data. -/
def CellCollapseSchedule (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ) :
    List (Fin (P.toPoly.arity c)) →
      Finset (Fin (P.toPoly.arity c)) →
      (Fin (P.toPoly.arity c) → RegionSpecF B) → Prop
  | [], done, rs =>
      CoordwiseRealizableOn q_U q_D mS done rs ∧
      gateF Mc rs mS t n ∧
      ∀ i, i ∈ done
  | _ :: todo, done, rs =>
      CoordwiseRealizableOn q_U q_D mS done rs ∧
      gateF Mc rs mS t n ∧
      ∃ (done' : Finset (Fin (P.toPoly.arity c)))
        (rs' : Fin (P.toPoly.arity c) → RegionSpecF B),
        ¬ WRP.lexLt
          (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
          (P.rank c (copiedSlice mS n) (cellTupleF rs' mS t n)) ∧
        CellCollapseSchedule P c Mc q_U q_D mS n t todo done' rs'

/-- The empty scheduler is closed by the finite-descriptor plus processed-middle
cover. -/
theorem CellCollapseSchedule.nil_of_middle_subset
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    {done : Finset (Fin (P.toPoly.arity c))}
    (hdone : CoordwiseRealizableOn q_U q_D mS
      (finiteDescriptorSet q_U q_D mS rs ∪ done) rs)
    (hsub : middleDescriptorSet q_U q_D mS rs ⊆ done)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseSchedule P c Mc q_U q_D mS n t []
      (finiteDescriptorSet q_U q_D mS rs ∪ done) rs :=
  ⟨hdone, hgate, finiteDescriptorSet_union_mem_of_middle_subset (rs := rs) hsub⟩

/-- Empty scheduler base when the accumulated `done` set contains both the
finite descriptors and all original middle descriptors. -/
theorem CellCollapseSchedule.nil_of_descriptor_subsets
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ)
    (rs₀ rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    {done : Finset (Fin (P.toPoly.arity c))}
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hfin : finiteDescriptorSet q_U q_D mS rs₀ ⊆ done)
    (hmiddle : middleDescriptorSet q_U q_D mS rs₀ ⊆ done)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseSchedule P c Mc q_U q_D mS n t [] done rs :=
  ⟨hdone, hgate, done_mem_of_descriptor_subsets (rs := rs₀) hfin hmiddle⟩

/-- Empty scheduler base after the final original middle coordinate has just
been inserted into `done`.  This is the nil case used by an induction over the
original `middleDescriptorSet`, where the recursive tail proves the erased
middle set is already covered. -/
theorem CellCollapseSchedule.nil_of_descriptor_erase_subset
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ)
    (rs₀ rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    {done : Finset (Fin (P.toPoly.arity c))} {j : Fin (P.toPoly.arity c)}
    (hdone : CoordwiseRealizableOn q_U q_D mS (insert j done) rs)
    (hfin : finiteDescriptorSet q_U q_D mS rs₀ ⊆ done)
    (hmiddle : (middleDescriptorSet q_U q_D mS rs₀).erase j ⊆ done)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseSchedule P c Mc q_U q_D mS n t [] (insert j done) rs :=
  CellCollapseSchedule.nil_of_descriptor_subsets P c Mc q_U q_D mS n t rs₀ rs hdone
    (finiteDescriptorSet_subset_insert_of_subset (j := j) hfin)
    (middleDescriptorSet_subset_insert_of_erase_subset (j := j) hmiddle) hgate

/-- Schedule-level zero-middle base: if there are no middle descriptors, the
canonical finite descriptor set already covers every coordinate. -/
theorem CellCollapseSchedule.nil_of_no_middleDescriptorSet
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (hv : ∀ i, (rs i).valid mS)
    (hnoMiddle : middleDescriptorSet q_U q_D mS rs = ∅)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseSchedule P c Mc q_U q_D mS n t []
      (finiteDescriptorSet q_U q_D mS rs) rs := by
  refine CellCollapseSchedule.nil_of_descriptor_subsets P c Mc q_U q_D mS n t
    rs rs (CoordwiseRealizableOn.of_finiteDescriptorSet hv) ?_ ?_ hgate
  · intro i hi
    exact hi
  · intro i hi
    rw [hnoMiddle] at hi
    simp at hi

/-- Existential schedule interface for the zero-middle case, matching the
`hschedules` argument of
`dstarC_exists_fibred_mS_row_budgeted_of_cell_schedules_data`. -/
theorem CellCollapseSchedule.exists_of_no_middleDescriptorSet
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (hv : ∀ i, (rs i).valid mS)
    (hnoMiddle : middleDescriptorSet q_U q_D mS rs = ∅)
    (hgate : gateF Mc rs mS t n) :
    ∃ todo : List (Fin (P.toPoly.arity c)),
      CellCollapseSchedule P c Mc q_U q_D mS n t todo
        (finiteDescriptorSet q_U q_D mS rs) rs :=
  ⟨[], CellCollapseSchedule.nil_of_no_middleDescriptorSet P c Mc q_U q_D mS n t
    rs hv hnoMiddle hgate⟩

/-- Any finite scheduler trace gives the cell-local collapse chain consumed by
the row-budgeted selector capstone. -/
theorem cellCollapseChain_of_schedule
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ) :
    ∀ {todo : List (Fin (P.toPoly.arity c))}
      {done : Finset (Fin (P.toPoly.arity c))}
      {rs : Fin (P.toPoly.arity c) → RegionSpecF B},
      CellCollapseSchedule P c Mc q_U q_D mS n t todo done rs →
      CellCollapseChain P c Mc q_U q_D mS n t rs := by
  intro todo
  induction todo with
  | nil =>
      intro done rs hsched
      rcases hsched with ⟨hdone, hgate, hall⟩
      exact cellCollapseChain_of_coordwiseOn_all P c Mc q_U q_D mS n t rs hdone hall hgate
  | cons _ todo ih =>
      intro done rs hsched
      rcases hsched with ⟨_hdone, _hgate, done', rs', hstep, hsched'⟩
      exact cellCollapseChain_cons_update P c Mc q_U q_D mS n t rs rs' hstep
        (ih hsched')

/-- The two clear-window obligations needed to schedule a middle descriptor at
one coordinate in the current cell state. -/
def CellMiddleWindows {B k : ℕ} (Mc : SliceMSO.DetAuto (MarkedN k))
    (q_U q_D mS n t : ℕ)
    (rs : Fin k → RegionSpecF B) (j0 : Fin k) : Prop :=
  (∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_U →
    (∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter k U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter k U (fun _ => false)))^[b]) →
    ∀ q, rs j0 = RegionSpecF.prefIdx q →
      PrefClearWindow rs j0 mS n t q (mS - 1 - T) pc T) ∧
  (∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_D →
    (∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter k D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter k D (fun _ => false)))^[b]) →
    ∀ l, rs j0 = RegionSpecF.sufIdx l →
      SufClearWindow rs j0 mS n t l (mS - 1 - T) pc T)

/-- A **side-aware** geometric sufficient condition for the two clear windows of
one middle descriptor `j0`.  A genuine middle descriptor is *either* a prefix
descriptor *or* a suffix descriptor, and only the matching clear-window half is
non-vacuous: a `prefIdx` descriptor never needs the suffix window and vice
versa.  Accordingly we only constrain the coordinates that can actually block
`j0`'s own side — every other coordinate must lie after the whole prefix run
*when `j0` is a prefix descriptor*, and before the whole suffix run *when `j0`
is a suffix descriptor*.

This is strictly weaker than `of_no_other_middle`: when `j0` is a prefix middle
descriptor the suffix hypothesis is discharged with no constraint at all, so
genuinely mixed cells — for instance a prefix middle descriptor whose remaining
coordinates sit in the *suffix* stretch (`cellTupleF rs … i ≥ mS + 2*n + 1`) —
are now covered even though `of_no_other_middle` rejects them. -/
theorem CellMiddleWindows.of_no_other_same_side {B k : ℕ}
    {Mc : SliceMSO.DetAuto (MarkedN k)}
    {q_U q_D mS n t : ℕ}
    {rs : Fin k → RegionSpecF B} {j0 : Fin k}
    (hmSu : 2 * q_U + 2 ≤ mS) (hmSq : 2 * q_D + 2 ≤ mS)
    (hmid : j0 ∈ middleDescriptorSet q_U q_D mS rs)
    (hnoPref : PrefMiddleDescriptor q_U mS (rs j0) →
      ∀ i, i ≠ j0 → mS - 1 ≤ cellTupleF rs mS t n i)
    (hnoSuf : SufMiddleDescriptor q_D mS (rs j0) →
      ∀ i, i ≠ j0 → cellTupleF rs mS t n i < mS + 2 * n + 1) :
    CellMiddleWindows (B := B) Mc q_U q_D mS n t rs j0 := by
  constructor
  · intro pc T hpc hMpc _hgateCyc q hsrc
    have hpref : PrefMiddleDescriptor q_U mS (rs j0) := by
      rcases mem_middleDescriptorSet.mp hmid with hpref | hsuf
      · exact hpref
      · rcases hsuf with ⟨l, hsufsrc, _hlL, _hlR⟩
        rw [hsrc] at hsufsrc
        cases hsufsrc
    rcases PrefMiddleDescriptor.collapse_bounds hpref hpc hMpc hmSu with
      ⟨q0, hsrc0, hTq, hqN, _hNmS, _hNM, hNright, _hMpcN⟩
    rw [hsrc] at hsrc0
    cases hsrc0
    exact PrefClearWindow.of_no_other_pref rs j0 mS n t q
      (mS - 1 - T) pc T hTq hqN hNright (hnoPref hpref)
  · intro pc T hpc hMpc _hgateCyc l hsrc
    have hsuf : SufMiddleDescriptor q_D mS (rs j0) := by
      rcases mem_middleDescriptorSet.mp hmid with hpref | hsuf
      · rcases hpref with ⟨q, hprefsrc, _hqL, _hqR⟩
        rw [hsrc] at hprefsrc
        cases hprefsrc
      · exact hsuf
    rcases SufMiddleDescriptor.collapse_bounds hsuf hpc hMpc hmSq with
      ⟨l0, hsrc0, hTl, hlN, _hNmS, _hNM, hNright, _hMpcN⟩
    rw [hsrc] at hsrc0
    cases hsrc0
    exact SufClearWindow.of_no_other_suf rs j0 mS n t l
      (mS - 1 - T) pc T hTl hlN hNright (hnoSuf hsuf)

/-- A strong geometric isolation condition supplies both clear windows for one
middle descriptor: all other coordinates lie after the whole prefix run and
before the whole suffix run.  This is the unconditional both-sides corollary of
the sharper `of_no_other_same_side`. -/
theorem CellMiddleWindows.of_no_other_middle {B k : ℕ}
    {Mc : SliceMSO.DetAuto (MarkedN k)}
    {q_U q_D mS n t : ℕ}
    {rs : Fin k → RegionSpecF B} {j0 : Fin k}
    (hmSu : 2 * q_U + 2 ≤ mS) (hmSq : 2 * q_D + 2 ≤ mS)
    (hmid : j0 ∈ middleDescriptorSet q_U q_D mS rs)
    (hnoPref : ∀ i, i ≠ j0 → mS - 1 ≤ cellTupleF rs mS t n i)
    (hnoSuf : ∀ i, i ≠ j0 → cellTupleF rs mS t n i < mS + 2 * n + 1) :
    CellMiddleWindows (B := B) Mc q_U q_D mS n t rs j0 :=
  CellMiddleWindows.of_no_other_same_side hmSu hmSq hmid
    (fun _ => hnoPref) (fun _ => hnoSuf)

/-- Prefix clear-window step as a constructor for finite scheduler traces. -/
theorem CellCollapseSchedule.cons_pref_clearWindow_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hwindow : PrefClearWindow rs j0 mS n t q N pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q_bd) →
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo (insert j0 done)
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo) done rs := by
  obtain ⟨q_bd, x, hxreal, hTqbd, hqbdN, hshift, hdone', hgate', hstep⟩ :=
    prefStretch_middle_update_step_on_bounded P c Mc q_U q_D rs done j0 mS n t q
      N pc T F hm hsrc hpc hMpc hF hag hMq hqN hNmS hNM hMpcN
      hgateCyc hdone hwindow hgate
  exact ⟨hdone, hgate, insert j0 done,
    Function.update rs j0 (RegionSpecF.prefIdx q_bd), hstep,
    htail q_bd x hxreal hTqbd hqbdN hshift hdone' hgate'⟩

/-- Suffix clear-window step as a constructor for finite scheduler traces. -/
theorem CellCollapseSchedule.cons_suf_clearWindow_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t l N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.sufIdx l)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : T ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hwindow : SufClearWindow rs j0 mS n t l N pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l_bd) →
      T ≤ l_bd → l_bd < N →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo (insert j0 done)
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo) done rs := by
  obtain ⟨l_bd, x, hxreal, hTlbd, hlbdN, hshift, hdone', hgate', hstep⟩ :=
    sufStretch_middle_update_step_on_bounded P c Mc q_U q_D rs done j0 mS n t l
      N pc T F hm hsrc hpc hMpc hF hag hMl hlN hNmS hNM hMpcN
      hgateCyc hdone hwindow hgate
  exact ⟨hdone, hgate, insert j0 done,
    Function.update rs j0 (RegionSpecF.sufIdx l_bd), hstep,
    htail l_bd x hxreal hTlbd hlbdN hshift hdone' hgate'⟩

/-- Prefix-middle scheduler step with the canonical boundary `N = mS - 1 - T`. -/
theorem CellCollapseSchedule.cons_pref_middle_clearWindow_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hmid : PrefMiddleDescriptor q_U mS (rs j0))
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hmSu : 2 * q_U + 2 ≤ mS)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hwindow : ∀ q, rs j0 = RegionSpecF.prefIdx q →
      PrefClearWindow rs j0 mS n t q (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (q q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      rs j0 = RegionSpecF.prefIdx q →
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q_bd) →
      T ≤ q_bd → q_bd < mS - 1 - T →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo (insert j0 done)
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo) done rs := by
  rcases PrefMiddleDescriptor.collapse_bounds hmid hpc hMpc hmSu with
    ⟨q, hsrc, hTq, hqN, hNmS, hNM, _hNright, hMpcN⟩
  exact CellCollapseSchedule.cons_pref_clearWindow_bounded P c Mc q_U q_D rs done todo j0
    mS n t q (mS - 1 - T) pc T F hm hsrc hpc hMpc hF hag hTq hqN hNmS hNM
    hMpcN hgateCyc hdone (hwindow q hsrc) hgate
    (fun q_bd x hx hTqbd hqbdN hshift hdone' hgate' =>
      htail q q_bd x hsrc hx hTqbd hqbdN hshift hdone' hgate')

/-- Suffix-middle scheduler step with the canonical boundary `N = mS - 1 - T`. -/
theorem CellCollapseSchedule.cons_suf_middle_clearWindow_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hmid : SufMiddleDescriptor q_D mS (rs j0))
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hmSq : 2 * q_D + 2 ≤ mS)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hwindow : ∀ l, rs j0 = RegionSpecF.sufIdx l →
      SufClearWindow rs j0 mS n t l (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (l l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      rs j0 = RegionSpecF.sufIdx l →
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l_bd) →
      T ≤ l_bd → l_bd < mS - 1 - T →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo (insert j0 done)
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo) done rs := by
  rcases SufMiddleDescriptor.collapse_bounds hmid hpc hMpc hmSq with
    ⟨l, hsrc, hTl, hlN, hNmS, hNM, _hNright, hMpcN⟩
  exact CellCollapseSchedule.cons_suf_clearWindow_bounded P c Mc q_U q_D rs done todo j0
    mS n t l (mS - 1 - T) pc T F hm hsrc hpc hMpc hF hag hTl hlN hNmS hNM
    hMpcN hgateCyc hdone (hwindow l hsrc) hgate
    (fun l_bd x hx hTlbd hlbdN hshift hdone' hgate' =>
      htail l l_bd x hsrc hx hTlbd hlbdN hshift hdone' hgate')

/-- First prefix-middle scheduler step from the finite descriptor set, with the
canonical boundary `N = mS - 1 - T`. -/
theorem CellCollapseSchedule.cons_pref_middle_clearWindow_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hmid : PrefMiddleDescriptor q_U mS (rs j0))
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hmSu : 2 * q_U + 2 ≤ mS)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hv : ∀ i, (rs i).valid mS)
    (hwindow : ∀ q, rs j0 = RegionSpecF.prefIdx q →
      PrefClearWindow rs j0 mS n t q (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (q q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      rs j0 = RegionSpecF.prefIdx q →
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q_bd) →
      T ≤ q_bd → q_bd < mS - 1 - T →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo)
      (finiteDescriptorSet q_U q_D mS rs) rs :=
  CellCollapseSchedule.cons_pref_middle_clearWindow_bounded P c Mc q_U q_D rs
    (finiteDescriptorSet q_U q_D mS rs) todo j0 mS n t pc T F hm hmid hpc hMpc hF hag
    hmSu hgateCyc (CoordwiseRealizableOn.of_finiteDescriptorSet hv) hwindow hgate htail

/-- First suffix-middle scheduler step from the finite descriptor set, with the
canonical boundary `N = mS - 1 - T`. -/
theorem CellCollapseSchedule.cons_suf_middle_clearWindow_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hmid : SufMiddleDescriptor q_D mS (rs j0))
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hmSq : 2 * q_D + 2 ≤ mS)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hv : ∀ i, (rs i).valid mS)
    (hwindow : ∀ l, rs j0 = RegionSpecF.sufIdx l →
      SufClearWindow rs j0 mS n t l (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (l l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      rs j0 = RegionSpecF.sufIdx l →
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l_bd) →
      T ≤ l_bd → l_bd < mS - 1 - T →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo)
      (finiteDescriptorSet q_U q_D mS rs) rs :=
  CellCollapseSchedule.cons_suf_middle_clearWindow_bounded P c Mc q_U q_D rs
    (finiteDescriptorSet q_U q_D mS rs) todo j0 mS n t pc T F hm hmid hpc hMpc hF hag
    hmSq hgateCyc (CoordwiseRealizableOn.of_finiteDescriptorSet hv) hwindow hgate htail

/-- Prefix-middle scheduler step with the uniform prefix data unpacked locally.
This is the constructor shape expected by the eventual middle-coordinate
induction: the caller supplies clear-window/tail continuations, and this lemma
extracts the period, threshold, gate cycle, and rank recurrence for `j0`. -/
theorem CellCollapseSchedule.cons_pref_middle_clearWindow_data_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 →
          P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (hmid : PrefMiddleDescriptor q_U mS (rs j0))
    (hmSu : 2 * q_U + 2 ≤ mS)
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hwindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_U →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) →
      ∀ q, rs j0 = RegionSpecF.prefIdx q →
        PrefClearWindow rs j0 mS n t q (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (pc T : ℕ) (F : ℕ → Fin P.d → ℤ),
      1 ≤ pc → T + pc < q_U → RankAffineAtFrom T pc F →
      (∀ q', q' < mS - 1 →
        P.rank c (copiedSlice mS n)
          (Function.update (cellTupleF rs mS t n) j0 q') = F q') →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) →
      ∀ (q q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
        rs j0 = RegionSpecF.prefIdx q →
        CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q_bd) →
        T ≤ q_bd → q_bd < mS - 1 - T →
        ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
        CoordwiseRealizableOn q_U q_D mS (insert j0 done)
          (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) →
        gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n →
        CellCollapseSchedule P c Mc q_U q_D mS n t todo (insert j0 done)
          (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo) done rs := by
  obtain ⟨pc, T, hpc, hMpc, hgateCyc, hrank⟩ := hprefData j0
  obtain ⟨F, hF, hag⟩ := hrank (cellTupleF rs mS t n) mS n
  exact CellCollapseSchedule.cons_pref_middle_clearWindow_bounded P c Mc q_U q_D rs
    done todo j0 mS n t pc T F hm hmid hpc hMpc hF hag hmSu hgateCyc hdone
    (hwindow pc T hpc hMpc hgateCyc) hgate
    (fun q q_bd x hsrc hx hTqbd hqbdN hshift hdone' hgate' =>
      htail pc T F hpc hMpc hF hag hgateCyc q q_bd x hsrc hx hTqbd hqbdN
        hshift hdone' hgate')

/-- Suffix-middle scheduler step with the uniform suffix data unpacked locally. -/
theorem CellCollapseSchedule.cons_suf_middle_clearWindow_data_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (hmid : SufMiddleDescriptor q_D mS (rs j0))
    (hmSq : 2 * q_D + 2 ≤ mS)
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hwindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_D →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) →
      ∀ l, rs j0 = RegionSpecF.sufIdx l →
        SufClearWindow rs j0 mS n t l (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (pc T : ℕ) (F : ℕ → Fin P.d → ℤ),
      1 ≤ pc → T + pc < q_D → RankAffineAtFrom T pc F →
      (∀ l', l' < mS - 1 →
        P.rank c (copiedSlice mS n)
          (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l') →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) →
      ∀ (l l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
        rs j0 = RegionSpecF.sufIdx l →
        CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l_bd) →
        T ≤ l_bd → l_bd < mS - 1 - T →
        ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
        CoordwiseRealizableOn q_U q_D mS (insert j0 done)
          (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) →
        gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n →
        CellCollapseSchedule P c Mc q_U q_D mS n t todo (insert j0 done)
          (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo) done rs := by
  obtain ⟨pc, T, hpc, hMpc, hgateCyc, hrank⟩ := hsufData j0
  obtain ⟨F, hF, hag⟩ := hrank (cellTupleF rs mS t n) mS n
  exact CellCollapseSchedule.cons_suf_middle_clearWindow_bounded P c Mc q_U q_D rs
    done todo j0 mS n t pc T F hm hmid hpc hMpc hF hag hmSq hgateCyc hdone
    (hwindow pc T hpc hMpc hgateCyc) hgate
    (fun l l_bd x hsrc hx hTlbd hlbdN hshift hdone' hgate' =>
      htail pc T F hpc hMpc hF hag hgateCyc l l_bd x hsrc hx hTlbd hlbdN
        hshift hdone' hgate')

/-- First prefix-middle scheduler step from the finite descriptor set, with
uniform prefix data unpacked locally. -/
theorem CellCollapseSchedule.cons_pref_middle_clearWindow_data_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 →
          P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (hmid : PrefMiddleDescriptor q_U mS (rs j0))
    (hmSu : 2 * q_U + 2 ≤ mS)
    (hv : ∀ i, (rs i).valid mS)
    (hwindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_U →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) →
      ∀ q, rs j0 = RegionSpecF.prefIdx q →
        PrefClearWindow rs j0 mS n t q (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (pc T : ℕ) (F : ℕ → Fin P.d → ℤ),
      1 ≤ pc → T + pc < q_U → RankAffineAtFrom T pc F →
      (∀ q', q' < mS - 1 →
        P.rank c (copiedSlice mS n)
          (Function.update (cellTupleF rs mS t n) j0 q') = F q') →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) →
      ∀ (q q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
        rs j0 = RegionSpecF.prefIdx q →
        CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q_bd) →
        T ≤ q_bd → q_bd < mS - 1 - T →
        ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
        CoordwiseRealizableOn q_U q_D mS
          (insert j0 (finiteDescriptorSet q_U q_D mS rs))
          (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) →
        gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n →
        CellCollapseSchedule P c Mc q_U q_D mS n t todo
          (insert j0 (finiteDescriptorSet q_U q_D mS rs))
          (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo)
      (finiteDescriptorSet q_U q_D mS rs) rs :=
  CellCollapseSchedule.cons_pref_middle_clearWindow_data_bounded P c Mc q_U q_D
    hprefData rs (finiteDescriptorSet q_U q_D mS rs) todo j0 mS n t hm hmid hmSu
    (CoordwiseRealizableOn.of_finiteDescriptorSet hv) hwindow hgate htail

/-- First suffix-middle scheduler step from the finite descriptor set, with
uniform suffix data unpacked locally. -/
theorem CellCollapseSchedule.cons_suf_middle_clearWindow_data_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (hmid : SufMiddleDescriptor q_D mS (rs j0))
    (hmSq : 2 * q_D + 2 ≤ mS)
    (hv : ∀ i, (rs i).valid mS)
    (hwindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_D →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) →
      ∀ l, rs j0 = RegionSpecF.sufIdx l →
        SufClearWindow rs j0 mS n t l (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (pc T : ℕ) (F : ℕ → Fin P.d → ℤ),
      1 ≤ pc → T + pc < q_D → RankAffineAtFrom T pc F →
      (∀ l', l' < mS - 1 →
        P.rank c (copiedSlice mS n)
          (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l') →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) →
      ∀ (l l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
        rs j0 = RegionSpecF.sufIdx l →
        CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l_bd) →
        T ≤ l_bd → l_bd < mS - 1 - T →
        ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
        CoordwiseRealizableOn q_U q_D mS
          (insert j0 (finiteDescriptorSet q_U q_D mS rs))
          (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) →
        gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n →
        CellCollapseSchedule P c Mc q_U q_D mS n t todo
          (insert j0 (finiteDescriptorSet q_U q_D mS rs))
          (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo)
      (finiteDescriptorSet q_U q_D mS rs) rs :=
  CellCollapseSchedule.cons_suf_middle_clearWindow_data_bounded P c Mc q_U q_D
    hsufData rs (finiteDescriptorSet q_U q_D mS rs) todo j0 mS n t hm hmid hmSq
    (CoordwiseRealizableOn.of_finiteDescriptorSet hv) hwindow hgate htail

/-- Middle scheduler step from a `middleDescriptorSet` membership.  The theorem
dispatches to the prefix or suffix data-unpacking constructor according to the
descriptor at `j0`. -/
theorem CellCollapseSchedule.cons_middle_clearWindow_data_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 →
          P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (hmid : j0 ∈ middleDescriptorSet q_U q_D mS rs)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hprefWindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_U →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) →
      ∀ q, rs j0 = RegionSpecF.prefIdx q →
        PrefClearWindow rs j0 mS n t q (mS - 1 - T) pc T)
    (hsufWindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_D →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) →
      ∀ l, rs j0 = RegionSpecF.sufIdx l →
        SufClearWindow rs j0 mS n t l (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n)
    (hprefTail : ∀ (pc T : ℕ) (F : ℕ → Fin P.d → ℤ),
      1 ≤ pc → T + pc < q_U → RankAffineAtFrom T pc F →
      (∀ q', q' < mS - 1 →
        P.rank c (copiedSlice mS n)
          (Function.update (cellTupleF rs mS t n) j0 q') = F q') →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) →
      ∀ (q q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
        rs j0 = RegionSpecF.prefIdx q →
        CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q_bd) →
        T ≤ q_bd → q_bd < mS - 1 - T →
        ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
        CoordwiseRealizableOn q_U q_D mS (insert j0 done)
          (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) →
        gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n →
        CellCollapseSchedule P c Mc q_U q_D mS n t todo (insert j0 done)
          (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)))
    (hsufTail : ∀ (pc T : ℕ) (F : ℕ → Fin P.d → ℤ),
      1 ≤ pc → T + pc < q_D → RankAffineAtFrom T pc F →
      (∀ l', l' < mS - 1 →
        P.rank c (copiedSlice mS n)
          (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l') →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) →
      ∀ (l l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
        rs j0 = RegionSpecF.sufIdx l →
        CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l_bd) →
        T ≤ l_bd → l_bd < mS - 1 - T →
        ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
        CoordwiseRealizableOn q_U q_D mS (insert j0 done)
          (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) →
        gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n →
        CellCollapseSchedule P c Mc q_U q_D mS n t todo (insert j0 done)
          (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo) done rs := by
  rcases mem_middleDescriptorSet.mp hmid with hpref | hsuf
  · exact CellCollapseSchedule.cons_pref_middle_clearWindow_data_bounded P c Mc q_U q_D
      hprefData rs done todo j0 mS n t hm hpref hmSu hdone hprefWindow hgate hprefTail
  · exact CellCollapseSchedule.cons_suf_middle_clearWindow_data_bounded P c Mc q_U q_D
      hsufData rs done todo j0 mS n t hm hsuf hmSq hdone hsufWindow hgate hsufTail

/-- First middle scheduler step from the finite descriptor set, dispatching from
`middleDescriptorSet` membership and unpacking the uniform prefix/suffix data
locally. -/
theorem CellCollapseSchedule.cons_middle_clearWindow_data_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 →
          P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (hmid : j0 ∈ middleDescriptorSet q_U q_D mS rs)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hv : ∀ i, (rs i).valid mS)
    (hprefWindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_U →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) →
      ∀ q, rs j0 = RegionSpecF.prefIdx q →
        PrefClearWindow rs j0 mS n t q (mS - 1 - T) pc T)
    (hsufWindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_D →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) →
      ∀ l, rs j0 = RegionSpecF.sufIdx l →
        SufClearWindow rs j0 mS n t l (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n)
    (hprefTail : ∀ (pc T : ℕ) (F : ℕ → Fin P.d → ℤ),
      1 ≤ pc → T + pc < q_U → RankAffineAtFrom T pc F →
      (∀ q', q' < mS - 1 →
        P.rank c (copiedSlice mS n)
          (Function.update (cellTupleF rs mS t n) j0 q') = F q') →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) →
      ∀ (q q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
        rs j0 = RegionSpecF.prefIdx q →
        CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q_bd) →
        T ≤ q_bd → q_bd < mS - 1 - T →
        ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
        CoordwiseRealizableOn q_U q_D mS
          (insert j0 (finiteDescriptorSet q_U q_D mS rs))
          (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) →
        gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n →
        CellCollapseSchedule P c Mc q_U q_D mS n t todo
          (insert j0 (finiteDescriptorSet q_U q_D mS rs))
          (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)))
    (hsufTail : ∀ (pc T : ℕ) (F : ℕ → Fin P.d → ℤ),
      1 ≤ pc → T + pc < q_D → RankAffineAtFrom T pc F →
      (∀ l', l' < mS - 1 →
        P.rank c (copiedSlice mS n)
          (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l') →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) →
      ∀ (l l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
        rs j0 = RegionSpecF.sufIdx l →
        CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l_bd) →
        T ≤ l_bd → l_bd < mS - 1 - T →
        ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
        CoordwiseRealizableOn q_U q_D mS
          (insert j0 (finiteDescriptorSet q_U q_D mS rs))
          (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) →
        gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n →
        CellCollapseSchedule P c Mc q_U q_D mS n t todo
          (insert j0 (finiteDescriptorSet q_U q_D mS rs))
          (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo)
      (finiteDescriptorSet q_U q_D mS rs) rs :=
  CellCollapseSchedule.cons_middle_clearWindow_data_bounded P c Mc q_U q_D
    hsufData hprefData rs (finiteDescriptorSet q_U q_D mS rs) todo j0 mS n t hm hmid
    hmSq hmSu (CoordwiseRealizableOn.of_finiteDescriptorSet hv) hprefWindow hsufWindow
    hgate hprefTail hsufTail

/-- Last middle-coordinate scheduler step.  The clear-window move inserts `j0`
into `done`; if the original finite descriptors and the erased original middle
set were already covered by the old `done`, the tail scheduler closes
immediately. -/
theorem CellCollapseSchedule.cons_middle_clearWindow_data_last_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 →
          P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs₀ rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (hmid : j0 ∈ middleDescriptorSet q_U q_D mS rs)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hfin : finiteDescriptorSet q_U q_D mS rs₀ ⊆ done)
    (hmiddleTail : (middleDescriptorSet q_U q_D mS rs₀).erase j0 ⊆ done)
    (hprefWindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_U →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) →
      ∀ q, rs j0 = RegionSpecF.prefIdx q →
        PrefClearWindow rs j0 mS n t q (mS - 1 - T) pc T)
    (hsufWindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_D →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) →
      ∀ l, rs j0 = RegionSpecF.sufIdx l →
        SufClearWindow rs j0 mS n t l (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseSchedule P c Mc q_U q_D mS n t [j0] done rs := by
  refine CellCollapseSchedule.cons_middle_clearWindow_data_bounded P c Mc q_U q_D
    hsufData hprefData rs done [] j0 mS n t hm hmid hmSq hmSu hdone hprefWindow
    hsufWindow hgate ?_ ?_
  · intro pc T F hpc hMpc hF hag hgateCyc q q_bd x hsrc hx hTqbd hqbdN hshift hdone' hgate'
    exact CellCollapseSchedule.nil_of_descriptor_erase_subset P c Mc q_U q_D mS n t rs₀
      (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) hdone' hfin
      hmiddleTail hgate'
  · intro pc T F hpc hMpc hF hag hgateCyc l l_bd x hsrc hx hTlbd hlbdN hshift hdone' hgate'
    exact CellCollapseSchedule.nil_of_descriptor_erase_subset P c Mc q_U q_D mS n t rs₀
      (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) hdone' hfin
      hmiddleTail hgate'

/-- Last middle-coordinate scheduler step from the canonical finite descriptor
set.  The only remaining coverage obligation is that every original middle
coordinate except `j0` was already absent from the tail. -/
theorem CellCollapseSchedule.cons_middle_clearWindow_data_last_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 →
          P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (j0 : Fin (P.toPoly.arity c)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (hmid : j0 ∈ middleDescriptorSet q_U q_D mS rs)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hv : ∀ i, (rs i).valid mS)
    (hmiddleTail :
      (middleDescriptorSet q_U q_D mS rs).erase j0 ⊆
        finiteDescriptorSet q_U q_D mS rs)
    (hprefWindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_U →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) →
      ∀ q, rs j0 = RegionSpecF.prefIdx q →
        PrefClearWindow rs j0 mS n t q (mS - 1 - T) pc T)
    (hsufWindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_D →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) →
      ∀ l, rs j0 = RegionSpecF.sufIdx l →
        SufClearWindow rs j0 mS n t l (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseSchedule P c Mc q_U q_D mS n t [j0]
      (finiteDescriptorSet q_U q_D mS rs) rs :=
  CellCollapseSchedule.cons_middle_clearWindow_data_last_bounded P c Mc q_U q_D
    hsufData hprefData rs rs (finiteDescriptorSet q_U q_D mS rs) j0 mS n t hm hmid
    hmSq hmSu (CoordwiseRealizableOn.of_finiteDescriptorSet hv) (fun _ hi => hi)
    hmiddleTail hprefWindow hsufWindow hgate

/-- Singleton-middle scheduler from the canonical finite descriptor set.  This
is the one-coordinate base case for the eventual induction over the original
middle descriptor set. -/
theorem CellCollapseSchedule.cons_middle_clearWindow_data_singleton_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 →
          P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (j0 : Fin (P.toPoly.arity c)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (hmid : j0 ∈ middleDescriptorSet q_U q_D mS rs)
    (hmiddleOnly : ∀ i, i ∈ middleDescriptorSet q_U q_D mS rs → i = j0)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hv : ∀ i, (rs i).valid mS)
    (hprefWindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_U →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) →
      ∀ q, rs j0 = RegionSpecF.prefIdx q →
        PrefClearWindow rs j0 mS n t q (mS - 1 - T) pc T)
    (hsufWindow : ∀ (pc T : ℕ), 1 ≤ pc → T + pc < q_D →
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) →
      ∀ l, rs j0 = RegionSpecF.sufIdx l →
        SufClearWindow rs j0 mS n t l (mS - 1 - T) pc T)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseSchedule P c Mc q_U q_D mS n t [j0]
      (finiteDescriptorSet q_U q_D mS rs) rs := by
  refine CellCollapseSchedule.cons_middle_clearWindow_data_last_finite_start_bounded
    P c Mc q_U q_D hsufData hprefData rs j0 mS n t hm hmid hmSq hmSu hv ?_
    hprefWindow hsufWindow hgate
  intro i hi
  rcases Finset.mem_erase.mp hi with ⟨hij, himid⟩
  exact False.elim (hij (hmiddleOnly i himid))

/-- Two-middle-coordinate scheduler from the canonical finite descriptor set.
After the first middle update, the second coordinate remains a middle descriptor
because it is a different coordinate; the tail then closes with the original
descriptor coverage invariant. -/
theorem CellCollapseSchedule.cons_middle_clearWindow_data_two_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 →
          P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (j0 j1 : Fin (P.toPoly.arity c)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (hij : j1 ≠ j0)
    (hmid0 : j0 ∈ middleDescriptorSet q_U q_D mS rs)
    (hmid1 : j1 ∈ middleDescriptorSet q_U q_D mS rs)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hv : ∀ i, (rs i).valid mS)
    (hmiddleTail :
      (middleDescriptorSet q_U q_D mS rs).erase j1 ⊆
        insert j0 (finiteDescriptorSet q_U q_D mS rs))
    (hwindows0 : CellMiddleWindows (B := B) Mc q_U q_D mS n t rs j0)
    (hprefWindows1 : ∀ q_bd,
      CellMiddleWindows (B := B) Mc q_U q_D mS n t
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) j1)
    (hsufWindows1 : ∀ l_bd,
      CellMiddleWindows (B := B) Mc q_U q_D mS n t
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) j1)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseSchedule P c Mc q_U q_D mS n t [j0, j1]
      (finiteDescriptorSet q_U q_D mS rs) rs := by
  refine CellCollapseSchedule.cons_middle_clearWindow_data_finite_start_bounded
    P c Mc q_U q_D hsufData hprefData rs [j1] j0 mS n t hm hmid0 hmSq hmSu
    hv hwindows0.1 hwindows0.2 hgate ?_ ?_
  · intro pc T F hpc hMpc hF hag hgateCyc q q_bd x hsrc hx hTqbd hqbdN
      hshift hdone' hgate'
    have hmid1' : j1 ∈ middleDescriptorSet q_U q_D mS
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) :=
      mem_middleDescriptorSet_update_of_ne (rs := rs) (i := j1) (j := j0)
        (r := RegionSpecF.prefIdx (B := B) q_bd) hij hmid1
    exact CellCollapseSchedule.cons_middle_clearWindow_data_last_bounded
      P c Mc q_U q_D hsufData hprefData rs
      (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd))
      (insert j0 (finiteDescriptorSet q_U q_D mS rs)) j1 mS n t hm hmid1'
      hmSq hmSu hdone'
      (finiteDescriptorSet_subset_insert_of_subset (j := j0) (fun _ hi => hi))
      hmiddleTail (hprefWindows1 q_bd).1 (hprefWindows1 q_bd).2 hgate'
  · intro pc T F hpc hMpc hF hag hgateCyc l l_bd x hsrc hx hTlbd hlbdN
      hshift hdone' hgate'
    have hmid1' : j1 ∈ middleDescriptorSet q_U q_D mS
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) :=
      mem_middleDescriptorSet_update_of_ne (rs := rs) (i := j1) (j := j0)
        (r := RegionSpecF.sufIdx (B := B) l_bd) hij hmid1
    exact CellCollapseSchedule.cons_middle_clearWindow_data_last_bounded
      P c Mc q_U q_D hsufData hprefData rs
      (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd))
      (insert j0 (finiteDescriptorSet q_U q_D mS rs)) j1 mS n t hm hmid1'
      hmSq hmSu hdone'
      (finiteDescriptorSet_subset_insert_of_subset (j := j0) (fun _ hi => hi))
      hmiddleTail (hsufWindows1 l_bd).1 (hsufWindows1 l_bd).2 hgate'

/-- Exact two-middle-coordinate scheduler: every original middle descriptor is
one of the two scheduled coordinates. -/
theorem CellCollapseSchedule.cons_middle_clearWindow_data_pair_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 →
          P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (j0 j1 : Fin (P.toPoly.arity c)) (mS n t : ℕ)
    (hm : 1 ≤ mS) (hij : j1 ≠ j0)
    (hmid0 : j0 ∈ middleDescriptorSet q_U q_D mS rs)
    (hmid1 : j1 ∈ middleDescriptorSet q_U q_D mS rs)
    (hmiddleOnly : ∀ i, i ∈ middleDescriptorSet q_U q_D mS rs → i = j0 ∨ i = j1)
    (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hv : ∀ i, (rs i).valid mS)
    (hwindows0 : CellMiddleWindows (B := B) Mc q_U q_D mS n t rs j0)
    (hprefWindows1 : ∀ q_bd,
      CellMiddleWindows (B := B) Mc q_U q_D mS n t
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) j1)
    (hsufWindows1 : ∀ l_bd,
      CellMiddleWindows (B := B) Mc q_U q_D mS n t
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) j1)
    (hgate : gateF Mc rs mS t n) :
    CellCollapseSchedule P c Mc q_U q_D mS n t [j0, j1]
      (finiteDescriptorSet q_U q_D mS rs) rs := by
  refine CellCollapseSchedule.cons_middle_clearWindow_data_two_finite_start_bounded
    P c Mc q_U q_D hsufData hprefData rs j0 j1 mS n t hm hij hmid0 hmid1
    hmSq hmSu hv ?_ hwindows0 hprefWindows1 hsufWindows1 hgate
  intro i hi
  rcases Finset.mem_erase.mp hi with ⟨hij1, himid⟩
  rcases hmiddleOnly i himid with hi0 | hi1
  · subst i
    exact Finset.mem_insert_self j0 (finiteDescriptorSet q_U q_D mS rs)
  · exact False.elim (hij1 hi1)

/-- Finset-order middle scheduler.  The existential `todo` is chosen before the
current cell state is supplied, so recursive tails use one fixed schedule order
for every boundary representative selected by the first update. -/
theorem CellCollapseSchedule.exists_middle_clearWindow_data_remaining_order_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 →
          P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs₀ : Fin (P.toPoly.arity c) → RegionSpecF B)
    (remaining : Finset (Fin (P.toPoly.arity c)))
    (mS n t : ℕ)
    (hm : 1 ≤ mS) (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hwindow : ∀ (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
      (j : Fin (P.toPoly.arity c)),
      gateF Mc rs mS t n →
      j ∈ middleDescriptorSet q_U q_D mS rs →
      CellMiddleWindows (B := B) Mc q_U q_D mS n t rs j) :
    ∃ todo : List (Fin (P.toPoly.arity c)),
      ∀ (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
        (done : Finset (Fin (P.toPoly.arity c))),
        CoordwiseRealizableOn q_U q_D mS done rs →
        finiteDescriptorSet q_U q_D mS rs₀ ⊆ done →
        (∀ i, i ∈ middleDescriptorSet q_U q_D mS rs₀ → i ∉ remaining → i ∈ done) →
        (∀ i, i ∈ remaining → i ∈ middleDescriptorSet q_U q_D mS rs) →
        gateF Mc rs mS t n →
        CellCollapseSchedule P c Mc q_U q_D mS n t todo done rs := by
  classical
  induction remaining using Finset.induction_on with
  | empty =>
      refine ⟨[], ?_⟩
      intro rs done hdone hfin hmiddleDone _hcurrentMid hgate
      refine CellCollapseSchedule.nil_of_descriptor_subsets P c Mc q_U q_D mS n t
        rs₀ rs hdone hfin ?_ hgate
      intro i hi
      exact hmiddleDone i hi (by simp)
  | @insert j remaining hnot ih =>
      rcases ih with ⟨tailTodo, htail⟩
      refine ⟨j :: tailTodo, ?_⟩
      intro rs done hdone hfin hmiddleDone hcurrentMid hgate
      have hmidj : j ∈ middleDescriptorSet q_U q_D mS rs :=
        hcurrentMid j (Finset.mem_insert_self j remaining)
      have hwj : CellMiddleWindows (B := B) Mc q_U q_D mS n t rs j :=
        hwindow rs j hgate hmidj
      have hfinTail : finiteDescriptorSet q_U q_D mS rs₀ ⊆ insert j done := by
        intro i hi
        exact Finset.mem_insert.mpr (Or.inr (hfin hi))
      have hmiddleDoneTail :
          ∀ i, i ∈ middleDescriptorSet q_U q_D mS rs₀ → i ∉ remaining →
            i ∈ insert j done := by
        intro i himid hinot
        by_cases hij : i = j
        · subst i
          exact Finset.mem_insert_self j done
        · exact Finset.mem_insert.mpr (Or.inr (hmiddleDone i himid (by
            intro hiInsert
            rcases Finset.mem_insert.mp hiInsert with hiEq | hiMem
            · exact hij hiEq
            · exact hinot hiMem)))
      refine CellCollapseSchedule.cons_middle_clearWindow_data_bounded
        P c Mc q_U q_D hsufData hprefData rs done tailTodo j mS n t hm hmidj
        hmSq hmSu hdone hwj.1 hwj.2 hgate ?_ ?_
      · intro pc T F hpc hMpc hF hag hgateCyc q q_bd x hsrc hx hTqbd hqbdN
          hshift hdone' hgate'
        exact htail (Function.update rs j (RegionSpecF.prefIdx (B := B) q_bd))
          (insert j done) hdone' hfinTail hmiddleDoneTail (by
            intro i hi
            have hij : i ≠ j := by
              intro hEq
              subst i
              exact hnot hi
            exact mem_middleDescriptorSet_update_of_ne (rs := rs) (i := i) (j := j)
              (r := RegionSpecF.prefIdx (B := B) q_bd) hij
              (hcurrentMid i (Finset.mem_insert_of_mem hi))) hgate'
      · intro pc T F hpc hMpc hF hag hgateCyc l l_bd x hsrc hx hTlbd hlbdN
          hshift hdone' hgate'
        exact htail (Function.update rs j (RegionSpecF.sufIdx (B := B) l_bd))
          (insert j done) hdone' hfinTail hmiddleDoneTail (by
            intro i hi
            have hij : i ≠ j := by
              intro hEq
              subst i
              exact hnot hi
            exact mem_middleDescriptorSet_update_of_ne (rs := rs) (i := i) (j := j)
              (r := RegionSpecF.sufIdx (B := B) l_bd) hij
              (hcurrentMid i (Finset.mem_insert_of_mem hi))) hgate'

/-- Finite-start arbitrary middle scheduler, parameterized by a clear-window
oracle for every gated current state and middle coordinate. -/
theorem CellCollapseSchedule.exists_middle_clearWindow_data_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (hsufData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
          (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
    (hprefData : ∀ (j0 : Fin (P.toPoly.arity c)), ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
      (∀ κ b, T ≤ b →
        (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
          = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
        RankAffineAtFrom T pc F ∧
        (∀ q, q < mS' - 1 →
          P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (mS n t : ℕ)
    (hm : 1 ≤ mS) (hmSq : 2 * q_D + 2 ≤ mS) (hmSu : 2 * q_U + 2 ≤ mS)
    (hv : ∀ i, (rs i).valid mS)
    (hwindow : ∀ (rs' : Fin (P.toPoly.arity c) → RegionSpecF B)
      (j : Fin (P.toPoly.arity c)),
      gateF Mc rs' mS t n →
      j ∈ middleDescriptorSet q_U q_D mS rs' →
      CellMiddleWindows (B := B) Mc q_U q_D mS n t rs' j)
    (hgate : gateF Mc rs mS t n) :
    ∃ todo : List (Fin (P.toPoly.arity c)),
      CellCollapseSchedule P c Mc q_U q_D mS n t todo
        (finiteDescriptorSet q_U q_D mS rs) rs := by
  obtain ⟨todo, hsched⟩ :=
    CellCollapseSchedule.exists_middle_clearWindow_data_remaining_order_bounded
      P c Mc q_U q_D hsufData hprefData rs (middleDescriptorSet q_U q_D mS rs)
      mS n t hm hmSq hmSu hwindow
  refine ⟨todo, hsched rs (finiteDescriptorSet q_U q_D mS rs)
    (CoordwiseRealizableOn.of_finiteDescriptorSet hv) (fun _ hi => hi) ?_ ?_ hgate⟩
  · intro i hi hinot
    exact False.elim (hinot hi)
  · intro i hi
    exact hi

/-- First prefix clear-window scheduler step from the finite descriptor set. -/
theorem CellCollapseSchedule.cons_pref_clearWindow_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hv : ∀ i, (rs i).valid mS)
    (hwindow : PrefClearWindow rs j0 mS n t q N pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q_bd) →
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo)
      (finiteDescriptorSet q_U q_D mS rs) rs :=
  CellCollapseSchedule.cons_pref_clearWindow_bounded P c Mc q_U q_D rs
    (finiteDescriptorSet q_U q_D mS rs) todo j0 mS n t q N pc T F
    hm hsrc hpc hMpc hF hag hMq hqN hNmS hNM hMpcN hgateCyc
    (CoordwiseRealizableOn.of_finiteDescriptorSet hv) hwindow hgate htail

/-- First suffix clear-window scheduler step from the finite descriptor set. -/
theorem CellCollapseSchedule.cons_suf_clearWindow_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t l N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.sufIdx l)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : T ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hv : ∀ i, (rs i).valid mS)
    (hwindow : SufClearWindow rs j0 mS n t l N pc T)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l_bd) →
      T ≤ l_bd → l_bd < N →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo)
      (finiteDescriptorSet q_U q_D mS rs) rs :=
  CellCollapseSchedule.cons_suf_clearWindow_bounded P c Mc q_U q_D rs
    (finiteDescriptorSet q_U q_D mS rs) todo j0 mS n t l N pc T F
    hm hsrc hpc hMpc hF hag hMl hlN hNmS hNM hMpcN hgateCyc
    (CoordwiseRealizableOn.of_finiteDescriptorSet hv) hwindow hgate htail

/-- Prefix no-crossing step as a scheduler constructor. -/
theorem CellCollapseSchedule.cons_pref_no_other_pref_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hNright : N + T ≤ mS - 1) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hnoPref : ∀ i, i ≠ j0 → mS - 1 ≤ cellTupleF rs mS t n i)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q_bd) →
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo (insert j0 done)
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo) done rs :=
  CellCollapseSchedule.cons_pref_clearWindow_bounded P c Mc q_U q_D rs done todo j0
    mS n t q N pc T F hm hsrc hpc hMpc hF hag hMq hqN hNmS hNM hMpcN
    hgateCyc hdone
    (PrefClearWindow.of_no_other_pref rs j0 mS n t q N pc T hMq hqN hNright hnoPref)
    hgate htail

/-- Suffix no-crossing step as a scheduler constructor. -/
theorem CellCollapseSchedule.cons_suf_no_other_suf_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (done : Finset (Fin (P.toPoly.arity c)))
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t l N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.sufIdx l)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : T ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hNright : N + T ≤ mS - 1) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hdone : CoordwiseRealizableOn q_U q_D mS done rs)
    (hnoSuf : ∀ i, i ≠ j0 → cellTupleF rs mS t n i < mS + 2 * n + 1)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l_bd) →
      T ≤ l_bd → l_bd < N →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS (insert j0 done)
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo (insert j0 done)
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo) done rs :=
  CellCollapseSchedule.cons_suf_clearWindow_bounded P c Mc q_U q_D rs done todo j0
    mS n t l N pc T F hm hsrc hpc hMpc hF hag hMl hlN hNmS hNM hMpcN
    hgateCyc hdone
    (SufClearWindow.of_no_other_suf rs j0 mS n t l N pc T hMl hlN hNright hnoSuf)
    hgate htail

/-- First prefix no-crossing scheduler step from the finite descriptor set. -/
theorem CellCollapseSchedule.cons_pref_no_other_pref_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t q N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.prefIdx q)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_U) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ q', q' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (cellTupleF rs mS t n) j0 q') = F q')
    (hMq : T ≤ q) (hqN : q < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hNright : N + T ≤ mS - 1) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hv : ∀ i, (rs i).valid mS)
    (hnoPref : ∀ i, i ≠ j0 → mS - 1 ≤ cellTupleF rs mS t n i)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (q_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.prefIdx (B := B) q_bd) →
      T ≤ q_bd → q_bd < N →
      ((∃ κ, q = q_bd + pc * κ) ∨ (∃ κ, q_bd = q + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.prefIdx (B := B) q_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo)
      (finiteDescriptorSet q_U q_D mS rs) rs :=
  CellCollapseSchedule.cons_pref_clearWindow_finite_start_bounded P c Mc q_U q_D rs todo
    j0 mS n t q N pc T F hm hsrc hpc hMpc hF hag hMq hqN hNmS hNM hMpcN
    hgateCyc hv
    (PrefClearWindow.of_no_other_pref rs j0 mS n t q N pc T hMq hqN hNright hnoPref)
    hgate htail

/-- First suffix no-crossing scheduler step from the finite descriptor set. -/
theorem CellCollapseSchedule.cons_suf_no_other_suf_finite_start_bounded
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (todo : List (Fin (P.toPoly.arity c)))
    (j0 : Fin (P.toPoly.arity c)) (mS n t l N pc T : ℕ)
    (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hsrc : rs j0 = RegionSpecF.sufIdx l)
    (hpc : 1 ≤ pc) (hMpc : T + pc < q_D) (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (cellTupleF rs mS t n) j0 (mS + 2 * n + 1 + l')) = F l')
    (hMl : T ≤ l) (hlN : l < N) (hNmS : N ≤ mS - 1)
    (hNM : mS - 1 ≤ N + T) (hNright : N + T ≤ mS - 1) (hMpcN : T + pc ≤ N)
    (hgateCyc : ∀ κ b, T ≤ b →
      (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun st => Mc.δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hv : ∀ i, (rs i).valid mS)
    (hnoSuf : ∀ i, i ≠ j0 → cellTupleF rs mS t n i < mS + 2 * n + 1)
    (hgate : gateF Mc rs mS t n)
    (htail : ∀ (l_bd : ℕ) (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      CoordCandRealizes q_U q_D mS x (RegionSpecF.sufIdx (B := B) l_bd) →
      T ≤ l_bd → l_bd < N →
      ((∃ κ, l = l_bd + pc * κ) ∨ (∃ κ, l_bd = l + pc * κ)) →
      CoordwiseRealizableOn q_U q_D mS
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) →
      gateF Mc (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd)) mS t n →
      CellCollapseSchedule P c Mc q_U q_D mS n t todo
        (insert j0 (finiteDescriptorSet q_U q_D mS rs))
        (Function.update rs j0 (RegionSpecF.sufIdx (B := B) l_bd))) :
    CellCollapseSchedule P c Mc q_U q_D mS n t (j0 :: todo)
      (finiteDescriptorSet q_U q_D mS rs) rs :=
  CellCollapseSchedule.cons_suf_clearWindow_finite_start_bounded P c Mc q_U q_D rs todo
    j0 mS n t l N pc T F hm hsrc hpc hMpc hF hag hMl hlN hNmS hNM hMpcN
    hgateCyc hv
    (SufClearWindow.of_no_other_suf rs j0 mS n t l N pc T hMl hlN hNright hnoSuf)
    hgate htail

/-- A cell-local finite non-increasing update chain gives the direct
cell-collapse conclusion. -/
theorem cell_collapse_to_coordCand_of_cellCollapseChain
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Mc : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    {B : ℕ} (q_U q_D mS n t : ℕ)
    (rs : Fin (P.toPoly.arity c) → RegionSpecF B)
    (hchain : CellCollapseChain P c Mc q_U q_D mS n t rs) :
    ∃ ds, ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c) ∧
      gateF Mc (deepShapeF ds mS) mS t n ∧
      ¬ WRP.lexLt
        (P.rank c (copiedSlice mS n) (cellTupleF rs mS t n))
        (P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)) := by
  obtain ⟨N, rsAt, h0, hsteps, hcoordN, hgateN⟩ := hchain
  have hcollapse :=
    cell_collapse_to_coordCand_of_nonincreasing_update_chain P c Mc q_U q_D
      mS n t N rsAt hsteps hcoordN hgateN
  simpa [h0] using hcollapse

/-- Any finite non-increasing update chain gives the direct window-aware cell
collapse interface. -/
theorem windowedCellCollapse_of_nonincreasing_update_chains
    (P : WRP.Presentation Step Step)
    {B : ℕ}
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (q_U q_D n mS : ℕ)
    (hchains : WindowedCellCollapseChain P (B := B) Mc q_U q_D n mS) :
    WindowedCellCollapse P (B := B) Mc q_U q_D n mS := by
  intro c rs t htB htn hv hgate
  exact cell_collapse_to_coordCand_of_cellCollapseChain P c (Mc c) q_U q_D mS n t rs
    (hchains c rs t htB htn hv hgate)

set_option maxHeartbeats 1600000 in
/-- **d3.4 arity-1 capstone**: `fun mS => dstarRankGA_m P hV mS n` is `AffineOnResiduesAtZ pstar_mS`
in `mS` (at fixed `n ≥ Nn`), equal to the bounded `selB`.  The period `pstar_mS` is hoisted BEFORE `n`
(machine + presentation only, via `selB_period_uniform`); the per-mS equality is step 6
`dstarRankGA_m_eq_selB`.  This is the §9 Stage F-mS analogue of `dstarC_exists_fibred`, for arity 1. -/
theorem dstarC_exists_fibred_mS (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity1 : ∀ c, P.toPoly.arity c = 1) :
    ∃ (pstar_mS : ℕ), 1 ≤ pstar_mS ∧ ∃ (Nn : ℕ), ∀ n, Nn ≤ n →
      ∃ (dstarC_mS : ℕ → Fin P.d → ℤ) (N0_mS : ℕ),
        (∀ i, AffineOnResiduesAtZ pstar_mS (fun mS => dstarC_mS mS i)) ∧
        (∀ mS, N0_mS ≤ mS → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          CopiedDstar.dstarRankGA_m P hV mS n = dstarC_mS mS) := by
  classical
  rcases Nat.eq_zero_or_pos P.d with hd0 | hd
  · -- degenerate: P.d = 0
    exact ⟨1, le_rfl, 0, fun n _ => ⟨fun _ _ => 0, 0, fun i => (hd0 ▸ i).elim0,
      fun mS _ _ _ => funext (fun i => (hd0 ▸ i).elim0)⟩⟩
  obtain ⟨B, hB1, _hcov⟩ := CopiedCells.cells_cover_fibred P
  obtain ⟨m, p, Mc, _hp, _hmB, hMc, _hbwd, _hsetup⟩ := CopiedSetup.dstar_setup_fibred P B
  obtain ⟨q_U, q_D, _hloU, _hloD, hsufC, hprefC⟩ := coordCands_cycle_lengths P Mc (3 * B + m)
  obtain ⟨pstar_mS, hpstar1, haff⟩ := selB_period_uniform P hB1 Mc q_U q_D hd
  refine ⟨pstar_mS, hpstar1, 2 * B, fun n hn2B => ?_⟩
  refine ⟨selB B q_U q_D P Mc n hd, max (2 * q_D + 2) (2 * q_U + 2), fun i => haff n i, ?_⟩
  intro mS hN0 hdom hDpres
  exact dstarRankGA_m_eq_selB P hV harity1 hB1 Mc hMc q_U q_D hsufC hprefC hd n mS
    (by omega) hn2B (by omega) (by omega) hDpres

/-- Abstract row-budgeted mS-row affine `dstarC` package.  For each fixed row
`mS` and selected-atom growth budget `C`, the cover threshold in `n` may depend
on both; the period and row floor are presentation data. -/
def DstarCAffineMSRowBudgeted (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
  ∃ (pstar_mS : ℕ), 1 ≤ pstar_mS ∧ ∃ (N0_mS : ℕ),
    ∀ C mS, N0_mS ≤ mS →
      ∃ Nn : ℕ, ∀ n, Nn ≤ n →
        ∃ dstarC_mS : ℕ → Fin P.d → ℤ,
          (∀ i, AffineOnResiduesAtZ pstar_mS (fun mS => dstarC_mS mS i)) ∧
          ((∀ c : Fin P.toPoly.K, ∀ l : List (Fin (P.toPoly.arity c) → ℕ),
              l.Nodup →
              (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
              l.length ≤ C * (mS + n + 1)) →
            P.toPoly.domain (copiedSlice mS n) →
            (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
              P.toPoly.labelOf (copiedSlice mS n) a = D) →
            CopiedDstar.dstarRankGA_m P hV mS n = dstarC_mS mS)

/-- General-arity, row-budgeted `dstarC` producer from a window-aware cell
collapse interface.  Unlike the arity-1 capstone, the cover threshold is
allowed to depend on the fixed row `mS` and selected-atom budget `C`, matching
`cells_cover_fibred`.  The period and row floor remain machine/presentation
data, and no `harity1` hypothesis is used. -/
theorem dstarC_exists_fibred_mS_row_budgeted_of_windowed_collapse
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hcollapse : ∀ {B : ℕ}
      (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (q_U q_D n mS : ℕ),
        1 ≤ mS → 2 * q_D + 2 ≤ mS → 2 * q_U + 2 ≤ mS →
        WindowedCellCollapse P (B := B) Mc q_U q_D n mS) :
    DstarCAffineMSRowBudgeted P hV := by
  classical
  rcases Nat.eq_zero_or_pos P.d with hd0 | hd
  · exact ⟨1, le_rfl, 0, fun C mS _ => ⟨0, fun n _ =>
      ⟨fun _ i => (hd0 ▸ i).elim0, fun i => (hd0 ▸ i).elim0,
        fun _ _ _ => funext (fun i => (hd0 ▸ i).elim0)⟩⟩⟩
  obtain ⟨B, hB1, hcov⟩ := CopiedCells.cells_cover_fibred P
  obtain ⟨m, p, Mc, _hp, _hmB, hMc, _hbwd, _hsetup⟩ := CopiedSetup.dstar_setup_fibred P B
  obtain ⟨q_U, q_D, _hloU, _hloD, _hsufC, _hprefC⟩ :=
    coordCands_cycle_lengths P Mc (3 * B + m)
  obtain ⟨pstar_mS, hpstar1, haff⟩ := selB_period_uniform P hB1 Mc q_U q_D hd
  refine ⟨pstar_mS, hpstar1, max (2 * q_D + 2) (2 * q_U + 2), ?_⟩
  intro C mS hN0
  have hm : 1 ≤ mS := by omega
  have hmSq : 2 * q_D + 2 ≤ mS := by omega
  have hmSu : 2 * q_U + 2 ≤ mS := by omega
  obtain ⟨Ncov, hcoverN⟩ := hcov C mS hm
  refine ⟨Ncov, fun n hn => ?_⟩
  refine ⟨selB B q_U q_D P Mc n hd, fun i => haff n i, ?_⟩
  intro hbudget _hdom hDpres
  exact dstarRankGA_m_eq_selB_of_coordinate_cover_collapse_window P hV Mc hMc
    q_U q_D hd n mS hm hmSq hmSu
    (fun c ī hsel => hcoverN n hn c ī hsel (hbudget c))
    (hcollapse Mc q_U q_D n mS hm hmSq hmSu) hDpres

set_option maxHeartbeats 1600000 in
/-- Data-aware version of
`dstarC_exists_fibred_mS_row_budgeted_of_windowed_collapse`.  The cell-collapse
oracle receives the prefix/suffix stretch cycle data produced by
`coordCands_cycle_lengths`, which is the natural interface for the descriptor
collapse lemmas above. -/
theorem dstarC_exists_fibred_mS_row_budgeted_of_windowed_collapse_data
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hcollapse : ∀ {B : ℕ}
      (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (q_U q_D : ℕ)
      (_hsufData : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)),
        ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
          (∀ κ b, T ≤ b →
            (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
              = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
          (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
            RankAffineAtFrom T pc F ∧
            (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
              (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
      (_hprefData : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)),
        ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
          (∀ κ b, T ≤ b →
            (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
              = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
          (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
            RankAffineAtFrom T pc F ∧
            (∀ q, q < mS' - 1 →
              P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
      (n mS : ℕ),
        1 ≤ mS → 2 * q_D + 2 ≤ mS → 2 * q_U + 2 ≤ mS →
        WindowedCellCollapse P (B := B) Mc q_U q_D n mS) :
    DstarCAffineMSRowBudgeted P hV := by
  classical
  rcases Nat.eq_zero_or_pos P.d with hd0 | hd
  · exact ⟨1, le_rfl, 0, fun C mS _ => ⟨0, fun n _ =>
      ⟨fun _ i => (hd0 ▸ i).elim0, fun i => (hd0 ▸ i).elim0,
        fun _ _ _ => funext (fun i => (hd0 ▸ i).elim0)⟩⟩⟩
  obtain ⟨B, hB1, hcov⟩ := CopiedCells.cells_cover_fibred P
  obtain ⟨m, p, Mc, _hp, _hmB, hMc, _hbwd, _hsetup⟩ := CopiedSetup.dstar_setup_fibred P B
  obtain ⟨q_U, q_D, _hloU, _hloD, hsufC, hprefC⟩ :=
    coordCands_cycle_lengths P Mc (3 * B + m)
  obtain ⟨pstar_mS, hpstar1, haff⟩ := selB_period_uniform P hB1 Mc q_U q_D hd
  refine ⟨pstar_mS, hpstar1, max (2 * q_D + 2) (2 * q_U + 2), ?_⟩
  intro C mS hN0
  have hm : 1 ≤ mS := by omega
  have hmSq : 2 * q_D + 2 ≤ mS := by omega
  have hmSu : 2 * q_U + 2 ≤ mS := by omega
  obtain ⟨Ncov, hcoverN⟩ := hcov C mS hm
  refine ⟨Ncov, fun n hn => ?_⟩
  refine ⟨selB B q_U q_D P Mc n hd, fun i => haff n i, ?_⟩
  intro hbudget _hdom hDpres
  exact dstarRankGA_m_eq_selB_of_coordinate_cover_collapse_window P hV Mc hMc
    q_U q_D hd n mS hm hmSq hmSu
    (fun c ī hsel => hcoverN n hn c ī hsel (hbudget c))
    (hcollapse (B := B) Mc q_U q_D hsufC hprefC n mS hm hmSq hmSu) hDpres

set_option maxHeartbeats 1600000 in
/-- Row-budgeted `dstarC` from data-aware finite update chains.  This is the
preferred target for the arbitrary-arity middle-band scheduler: construct
`WindowedCellCollapseChain` for every covered cell, then this theorem supplies
the selector equality and affine `dstarC` package. -/
theorem dstarC_exists_fibred_mS_row_budgeted_of_update_chains_data
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hchains : ∀ {B : ℕ}
      (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (q_U q_D : ℕ)
      (_hsufData : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)),
        ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
          (∀ κ b, T ≤ b →
            (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
              = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
          (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
            RankAffineAtFrom T pc F ∧
            (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
              (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
      (_hprefData : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)),
        ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
          (∀ κ b, T ≤ b →
            (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
              = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
          (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
            RankAffineAtFrom T pc F ∧
            (∀ q, q < mS' - 1 →
              P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
      (n mS : ℕ),
        1 ≤ mS → 2 * q_D + 2 ≤ mS → 2 * q_U + 2 ≤ mS →
        WindowedCellCollapseChain P (B := B) Mc q_U q_D n mS) :
    DstarCAffineMSRowBudgeted P hV := by
  refine dstarC_exists_fibred_mS_row_budgeted_of_windowed_collapse_data P hV ?_
  intro B Mc q_U q_D hsufData hprefData n mS hm hmSq hmSu
  exact windowedCellCollapse_of_nonincreasing_update_chains P Mc q_U q_D n mS
    (hchains (B := B) Mc q_U q_D hsufData hprefData n mS hm hmSq hmSu)

set_option maxHeartbeats 1600000 in
/-- Row-budgeted `dstarC` from cell-local finite update chains.  This is the
most convenient target for an arbitrary middle-band scheduler: prove a
`CellCollapseChain` for each covered gated cell, and this theorem packages it
into the global windowed-chain interface consumed by the selector capstone. -/
theorem dstarC_exists_fibred_mS_row_budgeted_of_cell_chains_data
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hcell : ∀ {B : ℕ}
      (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (q_U q_D : ℕ)
      (_hsufData : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)),
        ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
          (∀ κ b, T ≤ b →
            (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
              = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
          (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
            RankAffineAtFrom T pc F ∧
            (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
              (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
      (_hprefData : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)),
        ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
          (∀ κ b, T ≤ b →
            (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
              = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
          (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
            RankAffineAtFrom T pc F ∧
            (∀ q, q < mS' - 1 →
              P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
      (n mS : ℕ),
        1 ≤ mS → 2 * q_D + 2 ≤ mS → 2 * q_U + 2 ≤ mS →
        ∀ (c : Fin P.toPoly.K)
          (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t : ℕ),
          B ≤ t → t + B ≤ n →
          (∀ i, (rs i).valid mS) →
          gateF (Mc c) rs mS t n →
          CellCollapseChain P c (Mc c) q_U q_D mS n t rs) :
    DstarCAffineMSRowBudgeted P hV := by
  refine dstarC_exists_fibred_mS_row_budgeted_of_update_chains_data P hV ?_
  intro B Mc q_U q_D hsufData hprefData n mS hm hmSq hmSu
  exact windowedCellCollapseChain_of_cell_chains P Mc q_U q_D n mS
    (fun c rs t htB htn hv hgate =>
      hcell (B := B) Mc q_U q_D hsufData hprefData n mS hm hmSq hmSu
        c rs t htB htn hv hgate)

set_option maxHeartbeats 1600000 in
/-- Row-budgeted `dstarC` from finite scheduler traces.  This is the schedule-level
interface for the arbitrary middle-band induction: each covered gated cell starts
from its finite descriptor set, runs a finite `CellCollapseSchedule`, and the
generic schedule converter supplies the cell-local chain. -/
theorem dstarC_exists_fibred_mS_row_budgeted_of_cell_schedules_data
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hschedules : ∀ {B : ℕ}
      (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (q_U q_D : ℕ)
      (_hsufData : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)),
        ∃ pc T, 1 ≤ pc ∧ T + pc < q_D ∧
          (∀ κ b, T ≤ b →
            (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
              = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
          (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
            RankAffineAtFrom T pc F ∧
            (∀ l, l < mS' - 1 → P.rank c (copiedSlice mS' n')
              (Function.update ī0 j0 (mS' + 2 * n' + 1 + l)) = F l)))
      (_hprefData : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)),
        ∃ pc T, 1 ≤ pc ∧ T + pc < q_U ∧
          (∀ κ b, T ≤ b →
            (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
              = (fun st => (Mc c).δ st (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
          (∀ (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS' n' : ℕ), ∃ F : ℕ → Fin P.d → ℤ,
            RankAffineAtFrom T pc F ∧
            (∀ q, q < mS' - 1 →
              P.rank c (copiedSlice mS' n') (Function.update ī0 j0 q) = F q)))
      (n mS : ℕ),
        1 ≤ mS → 2 * q_D + 2 ≤ mS → 2 * q_U + 2 ≤ mS →
        ∀ (c : Fin P.toPoly.K)
          (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t : ℕ),
          B ≤ t → t + B ≤ n →
          (∀ i, (rs i).valid mS) →
          gateF (Mc c) rs mS t n →
          ∃ todo : List (Fin (P.toPoly.arity c)),
            CellCollapseSchedule P c (Mc c) q_U q_D mS n t todo
              (finiteDescriptorSet q_U q_D mS rs) rs) :
    DstarCAffineMSRowBudgeted P hV := by
  refine dstarC_exists_fibred_mS_row_budgeted_of_cell_chains_data P hV ?_
  intro B Mc q_U q_D hsufData hprefData n mS hm hmSq hmSu c rs t htB htn hv hgate
  obtain ⟨todo, hsched⟩ :=
    hschedules (B := B) Mc q_U q_D hsufData hprefData n mS hm hmSq hmSu
      c rs t htB htn hv hgate
  exact cellCollapseChain_of_schedule P c (Mc c) q_U q_D mS n t hsched

end CopiedDstarCMS
