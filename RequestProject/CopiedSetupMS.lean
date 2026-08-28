/-
# mS-direction eventual periodicity (§9 tower, Stage F-mS — foundation)

The fibred tie count needs the equal-rank cell finsets to be *eventually periodic in the
boundary width* `mS` (not mS-invariant — that is FALSE, see FORMALISATION_WORKLOG update 8 — but
periodic with an mS-free period `q_U`).  The whole mS-dependence flows through the post-prefix
automaton state `δ*(q₀, U^mS)` and the rank accumulated over the `U^mS` prefix and `D^mS` suffix.

This file lays the **cornerstone**: reading a uniform letter run `x^{mS}` through any finite-state
`RankSource` automaton, the post-run STATE is eventually periodic in `mS`.  This is the mS-direction
twin of `SliceAutomata.iterate_eventuallyPeriodic` (used everywhere for the `n` direction), specialised
to the `foldl … (List.replicate mS x)` form in which the rank engine reads the `U^mS` prefix
(`CopiedRank.summand_copied_block_eq`) and the `D^mS` suffix.  The period/threshold are hoisted BEFORE
`mS`, matching the discipline the §9 tower requires.
-/
import RequestProject.CopiedRank
import RequestProject.CopiedAffineAt
import RequestProject.CopiedLandmark
import RequestProject.CopiedDstar
import RequestProject.CopiedGateEP

namespace CopiedSetupMS

open WRP Step CopiedRank CopiedAffineAt CopiedLandmark CopiedCells SliceFamilyCell CopiedDstar
  SliceMarkN CopiedMark SliceMSO MSOMarkN CopiedGateEP SliceDstarGA SliceReRoot
  SliceDstarCore SliceDstar SliceLexOrder

/-- **`foldl` over a uniform run is the single-step iterate.**  Reading `x^k` through the
transition `δ` from any start state is the `k`-fold iterate of the one-letter step. -/
theorem foldl_replicate_eq_iterate {Alpha : Type*} {Q : Type*} (δ : Q → Alpha → Q)
    (x : Alpha) (a : Q) (k : ℕ) :
    List.foldl δ a (List.replicate k x) = (fun q => δ q x)^[k] a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, Function.iterate_succ_apply, ih]

/-- **Iterate period-multiple**: from one-step eventual periodicity `f^[j+p] = f^[j]`
(for `j ≥ m`), any multiple `f^[j + p*k] q₀ = f^[j] q₀`. -/
theorem iterate_period_mul {Q : Type*} (f : Q → Q) (q₀ : Q) (m p : ℕ)
    (hper : ∀ j, m ≤ j → f^[j + p] q₀ = f^[j] q₀) (k j : ℕ) (hj : m ≤ j) :
    f^[j + p * k] q₀ = f^[j] q₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show j + p * (k + 1) = (j + p * k) + p by ring, hper (j + p * k) (by omega)]
    exact ih

/-- **Endofunction-level eventual periodicity (period-multiple form)**: for a finite-state `h`,
the iterate sequence `h^[·]` is eventually periodic *as a function* — `h^[a + p*k] = h^[a]` for all
start states at once, past a threshold `m`.  This uniform-over-start-states form is needed for the
suffix run of `gateF` EP-in-mS, whose base state itself moves with `mS`. -/
theorem endofunction_EP_mul {Q : Type*} [Finite Q] (h : Q → Q) :
    ∃ m p, 1 ≤ p ∧ ∀ k a, m ≤ a → h^[a + p * k] = h^[a] := by
  have key : ∀ a, (fun g : Q → Q => h ∘ g)^[a] id = h^[a] := by
    intro a; induction a with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih]
      exact (Function.iterate_succ' h n).symm
  obtain ⟨m, p, hp, hper⟩ := SliceAutomata.iterate_eventuallyPeriodic (fun g : Q → Q => h ∘ g) id
  refine ⟨m, p, hp, fun k a ha => ?_⟩
  have := iterate_period_mul (fun g : Q → Q => h ∘ g) id m p hper k a ha
  rw [key, key] at this
  exact this

/-- **Coupled-iterate eventual periodicity**: a growing exponent `h^[a]` applied to an
eventually-periodic state `X a` (period `pX`) yields an eventually-periodic predicate stream.  This
is exactly the suffix-run shape of `gateF` EP-in-mS: `M.accept (Dstep^[mS-c] (X mS))` with `X` the
(EP) state reached just before the growing block of unmarked `D`s. -/
theorem accept_iterate_coupled_EP {Q : Type*} [Finite Q] (h : Q → Q) (X : ℕ → Q)
    (pX : ℕ) (hpX : 1 ≤ pX) (mX : ℕ) (hXper : ∀ a, mX ≤ a → X (a + pX) = X a) (P : Q → Prop) :
    ∃ q, 1 ≤ q ∧ SliceOrder.EventuallyPeriodic (fun a => P (h^[a] (X a))) q := by
  obtain ⟨m, p, hp, hper⟩ := endofunction_EP_mul h
  have hXmul : ∀ k a, mX ≤ a → X (a + pX * k) = X a := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ j ih =>
      intro a ha
      rw [show a + pX * (j + 1) = (a + pX * j) + pX by ring, hXper _ (by omega), ih a ha]
  refine ⟨pX * p, Nat.mul_pos hpX hp, max mX m, fun a ha => ?_⟩
  show P (h^[a + pX * p] (X (a + pX * p))) ↔ P (h^[a] (X a))
  have ham : m ≤ a := le_of_max_le_right ha
  have haX : mX ≤ a := le_of_max_le_left ha
  have e1 : h^[a + pX * p] = h^[a] := by
    rw [show a + pX * p = a + p * pX by ring]; exact hper pX a ham
  have e2 : X (a + pX * p) = X a := hXmul p a haX
  rw [e1, e2]

/-- **A growing-length iterate from an eventually-periodic start is eventually periodic.**  If `σ` is
EP-in-mS (period `pσ`) and `f` is finite-state, then `fun mS => f^[mS - c] (σ mS)` is EP-in-mS.  This
is the d3 deep-suffix building block: the automaton state after reading the `D^{mS-i}` suffix run
(`f = D-block-step`, `σ mS = ` the EP post-`(UD)^n` state, `c = i`) is itself EP-in-mS — so the
suffix atom's `β`-state correction is EP-in-mS, and the same `f^[mS-c] (σ mS)` shape feeds the
deep-suffix rank accumulation. -/
theorem iterate_EPstate_EP_mS {Q : Type*} [Finite Q] (f : Q → Q) (σ : ℕ → Q)
    (pσ : ℕ) (hpσ : 1 ≤ pσ) (mσ : ℕ) (hσper : ∀ mS, mσ ≤ mS → σ (mS + pσ) = σ mS) (c : ℕ) :
    ∃ q, 1 ≤ q ∧ ∃ M, ∀ mS, M ≤ mS → f^[mS + q - c] (σ (mS + q)) = f^[mS - c] (σ mS) := by
  obtain ⟨mf, pf, hpf, hf⟩ := endofunction_EP_mul f
  have hσmul : ∀ k mS, mσ ≤ mS → σ (mS + pσ * k) = σ mS := by
    intro k
    induction k with
    | zero => intro mS _; simp
    | succ j ih =>
      intro mS h
      rw [show mS + pσ * (j + 1) = (mS + pσ * j) + pσ by ring, hσper _ (by omega), ih mS h]
  refine ⟨pσ * pf, Nat.mul_pos hpσ hpf, max mσ (mf + c), fun mS hmS => ?_⟩
  have hmσle : mσ ≤ mS := le_trans (le_max_left _ _) hmS
  have hmfc : mf + c ≤ mS := le_trans (le_max_right _ _) hmS
  have hσe : σ (mS + pσ * pf) = σ mS := hσmul pf mS hmσle
  have hfe : f^[mS + pσ * pf - c] = f^[mS - c] := by
    rw [show mS + pσ * pf - c = (mS - c) + pf * pσ by rw [Nat.mul_comm pσ pf]; omega]
    exact hf pσ (mS - c) (by omega)
  rw [hσe, hfe]

/-- **Fixed-marked-prefix / unmarked-tail split of a replicated marked run.**  If every mark of `ī`
lies outside the tail window `[off+c, off+L)` (either before `off+c` or at/after `off+L`), then the
marked run over `x^L` factors as the marked run over `x^c` followed by an UNMARKED `x^(L-c)`.  This is
the markSeg-side bridge: the `gateF` boundary segments (`U`-prefix, `D`-suffix) carry only finitely
many marks (the prefIdx/sufIdx coords, at mS-free positions), so the growing part of each boundary is
a pure unmarked stretch — exactly the `x^growing` the iterate engines consume. -/
theorem markSeg_replicate_decomp {k : ℕ} (x : Step) (ī : Fin k → ℕ) (off c L : ℕ)
    (hcL : c ≤ L) (hout : ∀ i, ī i < off + c ∨ off + L ≤ ī i) :
    markSeg k (List.replicate L x) ī off
      = markSeg k (List.replicate c x) ī off ++ unmark k (List.replicate (L - c) x) := by
  have hrep : List.replicate L x = List.replicate c x ++ List.replicate (L - c) x := by
    rw [← List.replicate_add]; congr 1; omega
  rw [hrep, markSeg_append k (List.replicate c x) (List.replicate (L - c) x) ī off,
    List.length_replicate]
  congr 1
  apply markSeg_unmarked k (List.replicate (L - c) x) ī (off + c)
  intro i
  rw [List.length_replicate]
  rcases hout i with h | h
  · left; omega
  · right; omega

/-- **END-anchored unmarked-prefix / fixed-marked-tail split of a replicated marked run.**  The mirror
of `markSeg_replicate_decomp`: if every mark of `ī` lies outside the leading window `[off, off+(L-c))`
(either before `off` or at/after `off+(L-c)`), then the marked run over `x^L` factors as an UNMARKED
`x^(L-c)` followed by the marked run over `x^c` at offset `off+(L-c)`.  This is the markSeg-side bridge
for DEEP-suffix gates, whose marks ride at a FIXED distance from the suffix END — the growing part is the
UNMARKED PREFIX of the boundary (the `x^growing` that `accepts_two_sided_EP_deepSuf` consumes). -/
theorem markSeg_replicate_decomp_end {k : ℕ} (x : Step) (ī : Fin k → ℕ) (off c L : ℕ)
    (hcL : c ≤ L) (hout : ∀ i, ī i < off ∨ off + (L - c) ≤ ī i) :
    markSeg k (List.replicate L x) ī off
      = unmark k (List.replicate (L - c) x) ++ markSeg k (List.replicate c x) ī (off + (L - c)) := by
  have hrep : List.replicate L x = List.replicate (L - c) x ++ List.replicate c x := by
    rw [← List.replicate_add]; congr 1; omega
  rw [hrep, markSeg_append k (List.replicate (L - c) x) (List.replicate c x) ī off,
    List.length_replicate]
  congr 1
  apply markSeg_unmarked k (List.replicate (L - c) x) ī off
  intro i
  rw [List.length_replicate]
  exact hout i

/-- **Two-sided pumping eventual periodicity.**  If both the prefix word `pre mS` and the suffix word
`suf mS` are a FIXED base followed by a growing uniform stretch `x^(mS - c)` (the prefix appending
unmarked `U`s, the suffix appending unmarked `D`s — see `markSeg_replicate_decomp`), with a FIXED
middle `mid`, then acceptance of `pre mS ++ mid ++ suf mS` is eventually periodic in `mS`.  This
abstracts the entire `gateF` EP-in-mS argument: the prefix run becomes a single-step iterate (EP via
`iterate_eventuallyPeriodic`), the middle composes a fixed map, and the suffix is a growing exponent
over an EP-varying base state (`accept_iterate_coupled_EP`-style, handled inline with
`endofunction_EP_mul`).  Period `q = pP*pS` (prefix-cycle × suffix-cycle). -/
theorem accepts_two_sided_EP {α : Type*} (M : DetAuto α) (pre suf : ℕ → List α)
    (mid preBase sufBase : List α) (xP xS : α) (cP cS : ℕ)
    (hpre : ∀ mS, cP ≤ mS → pre mS = preBase ++ List.replicate (mS - cP) xP)
    (hsuf : ∀ mS, cS ≤ mS → suf mS = sufBase ++ List.replicate (mS - cS) xS) :
    ∃ q, 1 ≤ q ∧ SliceOrder.EventuallyPeriodic
      (fun mS => M.accepts (pre mS ++ mid ++ suf mS)) q := by
  have := M.fintypeQ
  have hform : ∀ mS, max cP cS ≤ mS →
      M.accepts (pre mS ++ mid ++ suf mS)
        = M.accept ((fun s => M.δ s xS)^[mS - cS]
            (List.foldl M.δ (List.foldl M.δ
              ((fun s => M.δ s xP)^[mS - cP] (List.foldl M.δ M.q0 preBase)) mid) sufBase)) := by
    intro mS hmS
    have hP := hpre mS (le_trans (le_max_left _ _) hmS)
    have hS := hsuf mS (le_trans (le_max_right _ _) hmS)
    show M.accept (List.foldl M.δ M.q0 (pre mS ++ mid ++ suf mS)) = _
    rw [hP, hS, List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_append,
      foldl_replicate_eq_iterate, foldl_replicate_eq_iterate]
  obtain ⟨mP, pP, hpP, hperP⟩ := SliceAutomata.iterate_eventuallyPeriodic
    (fun s => M.δ s xP) (List.foldl M.δ M.q0 preBase)
  obtain ⟨mS0, pS, hpS, hperS⟩ := endofunction_EP_mul (fun s => M.δ s xS)
  refine ⟨pP * pS, Nat.mul_pos hpP hpS,
    max (max cP cS) (max (mP + cP) (mS0 + cS)), fun mS hmS => ?_⟩
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
    exact iterate_period_mul (fun s => M.δ s xP) (List.foldl M.δ M.q0 preBase)
      mP pP hperP pS (mS - cP) (by omega)
  have eS : (fun s => M.δ s xS)^[(mS + pP * pS) - cS]
      = (fun s => M.δ s xS)^[mS - cS] := by
    rw [show (mS + pP * pS) - cS = (mS - cS) + pS * pP by rw [Nat.mul_comm pP pS]; omega]
    exact hperS pP (mS - cS) (by omega)
  rw [eP, eS]

/-- **Two-sided pumping, DEEP-suffix variant.**  Like `accepts_two_sided_EP` but the suffix has its
fixed-marked part at the END: `suf mS = replicate (mS-cS) xS ++ sufBaseEnd` (growing-unmarked run FIRST,
fixed tail LAST).  The growing `xS`-run feeds an EP-in-mS state into the fixed tail `sufBaseEnd`, so
`M.accepts (pre mS ++ mid ++ suf mS)` is EP in mS.  This is the form the DEEP-suffix gate needs (deep
marks ride at a FIXED distance from the suffix END, which `accepts_two_sided_EP`'s fixed-marked-prefix
suffix cannot express).  The proof is the `accepts_two_sided_EP` argument with the only change being the
`hform` normal form: `(xS-step)^[mS-cS]` is applied to the post-`mid` state and then `foldl sufBaseEnd`
wraps it (rather than `(xS-step)^[mS-cS]` outermost).  The `eP`/`eS` periodicity rewrites are identical. -/
theorem accepts_two_sided_EP_deepSuf {α : Type*} (M : DetAuto α) (pre suf : ℕ → List α)
    (mid preBase sufBaseEnd : List α) (xP xS : α) (cP cS : ℕ)
    (hpre : ∀ mS, cP ≤ mS → pre mS = preBase ++ List.replicate (mS - cP) xP)
    (hsuf : ∀ mS, cS ≤ mS → suf mS = List.replicate (mS - cS) xS ++ sufBaseEnd) :
    ∃ q, 1 ≤ q ∧ SliceOrder.EventuallyPeriodic
      (fun mS => M.accepts (pre mS ++ mid ++ suf mS)) q := by
  have := M.fintypeQ
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
  obtain ⟨mP, pP, hpP, hperP⟩ := SliceAutomata.iterate_eventuallyPeriodic
    (fun s => M.δ s xP) (List.foldl M.δ M.q0 preBase)
  obtain ⟨mS0, pS, hpS, hperS⟩ := endofunction_EP_mul (fun s => M.δ s xS)
  refine ⟨pP * pS, Nat.mul_pos hpP hpS,
    max (max cP cS) (max (mP + cP) (mS0 + cS)), fun mS hmS => ?_⟩
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
    exact iterate_period_mul (fun s => M.δ s xP) (List.foldl M.δ M.q0 preBase)
      mP pP hperP pS (mS - cP) (by omega)
  have eS : (fun s => M.δ s xS)^[(mS + pP * pS) - cS]
      = (fun s => M.δ s xS)^[mS - cS] := by
    rw [show (mS + pP * pS) - cS = (mS - cS) + pS * pP by rw [Nat.mul_comm pP pS]; omega]
    exact hperS pP (mS - cS) (by omega)
  rw [eP, eS]

/-- **Eventual-equivalence congruence for `EventuallyPeriodic`** (an eventual variant of
`SliceOrder.EventuallyPeriodic.congr`): if `Pr ↔ Qr` past a threshold and `Qr` is EP, so is `Pr`.
Used to transfer `gateF` EP-in-mS from the `redM`-reduced predicate (the iff `gateF_reduced` holds
only for `mS ≥ 1`). -/
theorem eventuallyPeriodic_congr_eventually {Pr Qr : ℕ → Prop} {p : ℕ} (m0 : ℕ)
    (h : ∀ n, m0 ≤ n → (Pr n ↔ Qr n)) (hQ : SliceOrder.EventuallyPeriodic Qr p) :
    SliceOrder.EventuallyPeriodic Pr p := by
  obtain ⟨m, hm⟩ := hQ
  refine ⟨max m m0, fun n hn => ?_⟩
  have hnm : m ≤ n := le_trans (le_max_left _ _) hn
  have hnm0 : m0 ≤ n := le_trans (le_max_right _ _) hn
  rw [h (n + p) (by omega), h n hnm0]
  exact hm n hnm

/-- **`unmark` of a replicated run** is a replicated unmarked letter — bridges the `unmark` produced
by `markSeg_replicate_decomp` to the `replicate (mS - c) xP` shape `accepts_two_sided_EP` consumes. -/
theorem unmark_replicate (k : ℕ) (x : Step) (m : ℕ) :
    unmark k (List.replicate m x) = List.replicate m (mkLetter k x (fun _ => false)) := by
  rw [unmark, List.map_replicate]

/-- The mS-free upper bound contributed by a single descriptor's `prefIdx` value (0 for non-prefIdx);
its `Finset.univ.sup` bounds every prefIdx coordinate of a fixed cell tuple. -/
def prefBoundF {B : ℕ} : RegionSpecF B → ℕ
  | .prefIdx q => q + 1
  | _ => 0

/-- **The `U`-prefix boundary segment has the base ++ growing-unmarked form.**  The marked `U`-prefix
of the copied slice carries only the cell's `prefIdx` coordinates (at mS-free positions `< c0`); the
`core`/`sufIdx` coordinates sit at `≥ mS-1`, outside the segment's growing tail.  Hence the segment is
a FIXED marked base (mS-free by `markSeg_congr_outside`) followed by `(mS - cP)` unmarked `U`s — the
`hpre` hypothesis of `accepts_two_sided_EP`. -/
theorem cellSegU_form {B k : ℕ} (rs : Fin k → RegionSpecF B) (t0 N0 : ℕ) :
    ∃ (cP : ℕ) (preBase : List (MarkedN k)), 1 ≤ cP ∧ ∀ mS, cP ≤ mS →
      markSeg k (List.replicate (mS - 1) U) (cellTupleF rs mS t0 N0) 0
        = preBase ++ List.replicate (mS - cP) (mkLetter k U (fun _ => false)) := by
  classical
  set c0 := Finset.univ.sup (fun i => prefBoundF (rs i)) with hc0
  refine ⟨c0 + 1, markSeg k (List.replicate c0 U) (cellTupleF rs (c0 + 1) t0 N0) 0,
    Nat.le_add_left 1 c0, fun mS hmS => ?_⟩
  have hpref : ∀ i q, rs i = .prefIdx q → q < c0 := by
    intro i q hq
    have hle : prefBoundF (rs i) ≤ c0 := by
      rw [hc0]; exact Finset.le_sup (f := fun i => prefBoundF (rs i)) (Finset.mem_univ i)
    rw [hq] at hle; simp only [prefBoundF] at hle; omega
  have hpos : ∀ i, cellTupleF rs mS t0 N0 i < c0 ∨ (mS - 1) ≤ cellTupleF rs mS t0 N0 i := by
    intro i
    simp only [cellTupleF]
    cases hr : rs i with
    | core r => right; simp only [RegionSpecF.posAt]; omega
    | prefIdx q => left; simp only [RegionSpecF.posAt]; exact hpref i q hr
    | sufIdx l => right; simp only [RegionSpecF.posAt]; omega
  rw [markSeg_replicate_decomp U (cellTupleF rs mS t0 N0) 0 c0 (mS - 1) (by omega)
        (by intro i; rcases hpos i with h | h; exacts [Or.inl (by omega), Or.inr (by omega)]),
      unmark_replicate]
  congr 1
  · apply markSeg_congr_outside
    intro i
    simp only [cellTupleF, List.length_replicate]
    cases hr : rs i with
    | core r => right; simp only [RegionSpecF.posAt]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    | prefIdx q => left; simp only [RegionSpecF.posAt]
    | sufIdx l => right; simp only [RegionSpecF.posAt]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
  · congr 1; omega

/-- The mS-free bound contributed by a single descriptor towards BOTH stretch validity and the
`D`-suffix decomposition (`prefIdx`/`sufIdx` slack `+2`, `core` contributes 0). -/
def valBoundF {B : ℕ} : RegionSpecF B → ℕ
  | .prefIdx q => q + 2
  | .sufIdx l => l + 2
  | _ => 0

/-- **The `D`-suffix boundary segment has the base ++ growing-unmarked form.**  After the offset
normalization `markSegD_eq_rel` (which rewrites the suffix to the mS-free relative form
`markSeg(replicate (mS-1) D)(relDAtF mS ∘ rs) 0`), only the `sufIdx` coordinates land (at mS-free
relative positions `l`); `core`/`prefIdx` map to `mS-1`, outside the growing tail.  The chosen
threshold `cS = bd+1` also forces stretch validity, so `markSegD_eq_rel` applies — giving the `hsuf`
hypothesis of `accepts_two_sided_EP` with no separate validity side-condition. -/
theorem cellSegD_form {B k : ℕ} (rs : Fin k → RegionSpecF B) (t0 : ℕ) :
    ∃ (cS : ℕ) (sufBase : List (MarkedN k)), 1 ≤ cS ∧ ∀ mS, cS ≤ mS →
      markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t0 (t0 + B)) (mS + 2 * (t0 + B) + 1)
        = sufBase ++ List.replicate (mS - cS) (mkLetter k D (fun _ => false)) := by
  classical
  set bd := Finset.univ.sup (fun i => valBoundF (rs i)) with hbd
  refine ⟨bd + 1, markSeg k (List.replicate bd D) (fun i => relDAtF (bd + 1) (rs i)) 0,
    Nat.le_add_left 1 bd, fun mS hmS => ?_⟩
  have hb : ∀ i, valBoundF (rs i) ≤ bd := by
    intro i; rw [hbd]; exact Finset.le_sup (f := fun i => valBoundF (rs i)) (Finset.mem_univ i)
  have hv : ∀ i, (rs i).valid mS := by
    intro i
    cases hr : rs i with
    | core r => simp only [RegionSpecF.valid]
    | prefIdx q =>
        have hbi : valBoundF (rs i) ≤ bd := hb i
        rw [hr] at hbi; simp only [valBoundF] at hbi; simp only [RegionSpecF.valid]; omega
    | sufIdx l =>
        have hbi : valBoundF (rs i) ≤ bd := hb i
        rw [hr] at hbi; simp only [valBoundF] at hbi; simp only [RegionSpecF.valid]; omega
  rw [markSegD_eq_rel rs mS t0 (t0 + B) (by omega) hv le_rfl]
  have hpos : ∀ i, relDAtF mS (rs i) < bd ∨ (mS - 1) ≤ relDAtF mS (rs i) := by
    intro i
    cases hr : rs i with
    | core r => exact Or.inr le_rfl
    | prefIdx q => exact Or.inr le_rfl
    | sufIdx l =>
        left
        have hbi : valBoundF (rs i) ≤ bd := hb i
        rw [hr] at hbi; simp only [valBoundF] at hbi; simp only [relDAtF]; omega
  rw [markSeg_replicate_decomp D (fun i => relDAtF mS (rs i)) 0 bd (mS - 1) (by omega)
        (by intro i; rcases hpos i with h | h;
            exacts [Or.inl (by omega), Or.inr (by omega)]),
      unmark_replicate]
  congr 1
  · apply markSeg_congr_outside
    intro i
    simp only [List.length_replicate]
    cases hr : rs i with
    | core r => right; simp only [relDAtF]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    | prefIdx q => right; simp only [relDAtF]; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    | sufIdx l => left; simp only [relDAtF]
  · congr 1; omega

/-- **Stretch validity holds for all large `mS`** (the `prefIdx`/`sufIdx` indices are below `mS-1`
once `mS` exceeds the descriptors' `valBoundF` sup) — supplies `gateF_reduced`'s validity premise. -/
theorem cell_valid_ge {B k : ℕ} (rs : Fin k → RegionSpecF B) :
    ∃ vth, ∀ mS, vth ≤ mS → ∀ i, (rs i).valid mS := by
  classical
  set bd := Finset.univ.sup (fun i => valBoundF (rs i)) with hbd
  refine ⟨bd + 1, fun mS hmS i => ?_⟩
  have hb : ∀ j, valBoundF (rs j) ≤ bd :=
    fun j => hbd ▸ Finset.le_sup (f := fun i => valBoundF (rs i)) (Finset.mem_univ j)
  cases hr : rs i with
  | core r => simp only [RegionSpecF.valid]
  | prefIdx q =>
      have hbi := hb i; rw [hr] at hbi; simp only [valBoundF] at hbi
      simp only [RegionSpecF.valid]; omega
  | sufIdx l =>
      have hbi := hb i; rw [hr] at hbi; simp only [valBoundF] at hbi
      simp only [RegionSpecF.valid]; omega

/-- **The fibred cell gate is eventually periodic in the boundary width `mS`.**  This is the §9
Stage F-mS cornerstone: combining the two boundary-segment forms (`cellSegU_form`, `cellSegD_form`)
with the mS-free reduced middle (`gateF_reduced`) through the two-sided pumping engine
(`accepts_two_sided_EP`), the gate `fun mS => gateF M rs mS t0 n` is `EventuallyPeriodic`.  The
period is `cP-cycle × cS-cycle` of the underlying machine `M`.  No Büchi axiom. -/
theorem gateF_EP_mS {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k))
    (rs : Fin k → RegionSpecF B) (t0 n : ℕ) (hwin : t0 + B ≤ n) :
    ∃ q, 1 ≤ q ∧ SliceOrder.EventuallyPeriodic (fun mS => gateF M rs mS t0 n) q := by
  obtain ⟨cP, preBase, _hcP, hpreU⟩ := cellSegU_form rs t0 (t0 + B)
  obtain ⟨cS, sufBase, _hcS, hsufD⟩ := cellSegD_form rs t0
  obtain ⟨vth, hvth⟩ := cell_valid_ge rs
  obtain ⟨q, hq, hQEP⟩ := accepts_two_sided_EP M
    (fun mS => markSeg k (List.replicate (mS - 1) U) (cellTupleF rs mS t0 (t0 + B)) 0)
    (fun mS => markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t0 (t0 + B))
      (mS + 2 * (t0 + B) + 1))
    ((markAtN (coreSet rs).card (wrappedFlat n) (cellTuple (coreSpec rs) t0 n)).map
      (mapBits (coreEmb rs)))
    preBase sufBase (mkLetter k U (fun _ => false)) (mkLetter k D (fun _ => false)) cP cS
    hpreU hsufD
  refine ⟨q, hq, eventuallyPeriodic_congr_eventually
    (max 1 (max vth (max cP cS))) (fun mS hmS => ?_) hQEP⟩
  have hm1 : 1 ≤ mS := le_trans (le_max_left _ _) hmS
  have hvmS : ∀ i, (rs i).valid mS :=
    hvth mS (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hmS)
  show gateF M rs mS t0 n ↔ _
  rw [gateF_reduced M mS hm1 rs hvmS t0 n hwin]
  unfold redM
  rw [accepts_pullback, accepts_reRoot]

open scoped Classical in
/-- **Growing-carrier gated lexMin is affine-on-residues.**  The mS-direction replacement for
`gated_lexMin_affine_at`: the candidate LIST `Cands mS` may GROW with `mS` (as the `sufIdx` descriptor
pool does), so `lexMinList_coord_affineOnResiduesAtZ` (hard-wired to a fixed list) does not apply.
But if a SINGLE external family `sel` is provably the gated lexMin at every `mS` — it is on
(`hsel_on`), no on-candidate beats it (`hsel_le`), and it sits strictly below the dominator
(`hsel_lt_BIG`) — then the gated lexMin EQUALS `sel` pointwise, so its affineness transports onto
`sel` (`hsel_aff`).  This sidesteps the growing-list induction entirely.  The per-`mS` collapse is the
`dstarC_exists_fibred` S12 endgame (lexMinList_le + lex-trichotomy). -/
theorem gated_lexMin_affine_at_growing {d : ℕ} {p : ℕ} (_hp : 1 ≤ p)
    (Cands : ℕ → List ((ℕ → Prop) × (ℕ → Fin d → ℤ)))
    (BIG : ℕ → Fin d → ℤ)
    (sel : ℕ → Fin d → ℤ)
    (hsel_aff : ∀ i, AffineOnResiduesAtZ p (fun mS => sel mS i))
    (hsel_on : ∀ mS, ∃ gf ∈ Cands mS, gf.1 mS ∧ gf.2 mS = sel mS)
    (hsel_le : ∀ mS, ∀ gf ∈ Cands mS, gf.1 mS → ¬ WRP.lexLt (gf.2 mS) (sel mS))
    (hsel_lt_BIG : ∀ mS, WRP.lexLt (sel mS) (BIG mS)) (i : Fin d) :
    AffineOnResiduesAtZ p (fun mS => lexMinList
      (BIG :: (Cands mS).map (fun gf => fun n => if gf.1 n then gf.2 n else BIG n)) mS i) := by
  classical
  have hkey : ∀ mS, lexMinList
      (BIG :: (Cands mS).map (fun gf => fun n => if gf.1 n then gf.2 n else BIG n)) mS = sel mS := by
    intro mS
    set Lm : List (ℕ → Fin d → ℤ) :=
      BIG :: (Cands mS).map (fun gf => fun n => if gf.1 n then gf.2 n else BIG n) with hLmdef
    have hLne : Lm ≠ [] := by rw [hLmdef]; exact List.cons_ne_nil _ _
    obtain ⟨hmin, hattn⟩ := lexMinList_le Lm hLne mS
    obtain ⟨gfd, hgfd, hond, hseleq⟩ := hsel_on mS
    set gatedd : ℕ → Fin d → ℤ := fun n => if gfd.1 n then gfd.2 n else BIG n with hgddef
    have hgddmem : gatedd ∈ Lm := by
      rw [hLmdef]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨gfd, hgfd, rfl⟩)
    have hgddval : gatedd mS = sel mS := by rw [hgddef]; simp only [if_pos hond]; exact hseleq
    have hDCle : ¬ WRP.lexLt (gatedd mS) (lexMinList Lm mS) := hmin gatedd hgddmem
    have hI : ¬ WRP.lexLt (sel mS) (lexMinList Lm mS) := by rw [← hgddval]; exact hDCle
    have hDClt : WRP.lexLt (lexMinList Lm mS) (BIG mS) := by
      have hgdlt : WRP.lexLt (gatedd mS) (BIG mS) := by rw [hgddval]; exact hsel_lt_BIG mS
      rcases lexLt_trichot (lexMinList Lm mS) (gatedd mS) with h | h | h
      · exact lexLt_trans _ _ _ h hgdlt
      · rw [h]; exact hgdlt
      · exact absurd h hDCle
    obtain ⟨F, hFmem, hFeq⟩ := hattn
    have hII : ¬ WRP.lexLt (lexMinList Lm mS) (sel mS) := by
      rw [hLmdef, List.mem_cons] at hFmem
      rcases hFmem with rfl | hFmem
      · rw [hFeq] at hDClt; exact absurd hDClt (lexLt_irrefl _)
      · rw [List.mem_map] at hFmem
        obtain ⟨gf, hgf, rfl⟩ := hFmem
        by_cases hon : gf.1 mS
        · have hval : lexMinList Lm mS = gf.2 mS := by rw [hFeq]; simp only [if_pos hon]
          rw [hval]; exact hsel_le mS gf hgf hon
        · have hval : lexMinList Lm mS = BIG mS := by rw [hFeq]; simp only [if_neg hon]
          rw [hval] at hDClt; exact absurd hDClt (lexLt_irrefl _)
    rcases lexLt_trichot (sel mS) (lexMinList Lm mS) with h | h | h
    · exact absurd h hI
    · exact h.symm
    · exact absurd h hII
  exact AffineOnResiduesAtZ.congr' (fun mS => (congrFun (hkey mS) i).symm) (hsel_aff i)

/-- **Flatten of a replicated singleton**: `[x]^k` flattened is `x^k`. -/
theorem flatten_replicate_singleton {Alpha : Type*} (x : Alpha) (k : ℕ) :
    (List.replicate k [x]).flatten = List.replicate k x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, ih, List.singleton_append,
      ← List.replicate_succ]

/-- **The mS-direction prefix-rank engine**: for a fixed suffix `suf`, the prefix-rank of
`A` reading `x^{mS} ++ suf` is, beyond a threshold `m` and on each residue class of `mS` mod a
period `p`, AFFINE in the run length `mS`.  The mS-twin of `SliceRank.prefixRank_pre_blocks_
affineOnResidues` (which is affine in the loop count with the variable run at the END); here the
variable run `x^{mS}` is at the START, the suffix is fixed.  The suffix's contribution depends only
on the post-run state, which is eventually periodic in `mS` at the SAME period `p` — so it cancels,
leaving the pure affine `k • P` from the run accumulation.  Period/threshold are hoisted BEFORE `mS`. -/
theorem prefixRank_run_affine_mS {Alpha : Type*} {d : ℕ} (A : RankSource Alpha d)
    (x : Alpha) (suf : List Alpha) :
    ∃ (m p : ℕ) (P : Fin d → ℤ), 1 ≤ p ∧ ∀ k r : ℕ,
      A.prefixRank (List.replicate (m + p * k + r) x ++ suf)
          (List.replicate (m + p * k + r) x ++ suf).length
        = A.prefixRank (List.replicate (m + r) x ++ suf)
            (List.replicate (m + r) x ++ suf).length + k • P := by
  have := A.fintypeQ
  -- decomposition: prefixRank (x^mS ++ suf) = (run sum) + (suffix contribution from post-run state)
  have hdecomp : ∀ mS, A.prefixRank (List.replicate mS x ++ suf)
      (List.replicate mS x ++ suf).length
      = (∑ i ∈ Finset.range mS,
          SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i] A.q0))
        + (List.foldl (SliceRank.rankStep A)
            ((SliceRank.blockStep A [x])^[mS] A.q0, 0) suf).2 := by
    intro mS
    rw [SliceRank.prefixRank_eq_foldl, List.foldl_append]
    obtain ⟨st, rk, hpr⟩ :
        ∃ st rk, List.foldl (SliceRank.rankStep A) (A.q0, 0) (List.replicate mS x) = (st, rk) :=
      ⟨_, _, rfl⟩
    have hrk : rk = ∑ i ∈ Finset.range mS,
        SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i] A.q0) := by
      have h := SliceRank.foldl_rankStep_replicate_snd A [x] A.q0 0 mS
      rw [flatten_replicate_singleton, hpr] at h
      simpa using h
    have hst : st = (SliceRank.blockStep A [x])^[mS] A.q0 := by
      have hbs : SliceRank.blockStep A [x] = fun q => A.δ q x := by funext q; rfl
      have h : st = List.foldl A.δ A.q0 (List.replicate mS x) := by
        rw [← SliceRank.rankStep_fst A A.q0 0 (List.replicate mS x), hpr]
      rw [h, foldl_replicate_eq_iterate, hbs]
    rw [hpr, SliceRank.rankStep_snd_add, hrk, hst]
  obtain ⟨m, p, hp, hper⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic (SliceRank.blockStep A [x]) A.q0
  have hgper : ∀ i, m ≤ i →
      SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i + p] A.q0)
        = SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i] A.q0) := by
    intro i hi; rw [hper i hi]
  refine ⟨m, p, ∑ i ∈ Finset.Ico m (m + p),
    SliceRank.blockWeight A [x] ((SliceRank.blockStep A [x])^[i] A.q0), hp, fun k r => ?_⟩
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

/-- **Deep-suffix rank engine: a block-weight partial sum from an EP-in-mS start state is
affine-on-residues in `mS`.**  When the start state `σ mS` is eventually periodic in `mS` (period
`pσ`), the accumulated block-weight over a GROWING run `y^{mS-c}` read from `σ mS` is affine-on-residues
in `mS`.  The slopes are PER-RESIDUE (one `y`-cycle sum from the residue's frozen start state `σ*`) —
this is exactly why a single-slope `of_recurrence` does not apply and the full `AffineOnResiduesAtZ`
construction is needed.  This is the genuine new content for d3's deep-suffix atoms (`l ≈ mS`), whose
rank reads `D^{mS-i}` from the EP post-`(UD)^n` state; combined with `prefixRank_run_affine_mS` (the
`U^mS` prefix) and `iterate_EPstate_EP_mS` (the post-run state) it yields the deep-suffix rank. -/
theorem partialSum_blockWeight_EPstate_affine_mS {Alpha : Type*} {d : ℕ}
    (A : RankSource Alpha d) (y : Alpha) (σ : ℕ → A.Q)
    (pσ : ℕ) (hpσ : 1 ≤ pσ) (mσ : ℕ) (hσper : ∀ mS, mσ ≤ mS → σ (mS + pσ) = σ mS)
    (c : ℕ) (i : Fin d) :
    ∃ p, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => (∑ j ∈ Finset.range (mS - c),
        SliceRank.blockWeight A [y] ((SliceRank.blockStep A [y])^[j] (σ mS))) i) := by
  have := A.fintypeQ
  obtain ⟨mb, pb, hpb, hb⟩ := endofunction_EP_mul (SliceRank.blockStep A [y])
  -- the ℤ-valued per-state weight sequence and its uniform period-(pσ*pb) EP in the run index
  set g : A.Q → ℕ → ℤ := fun q j =>
    SliceRank.blockWeight A [y] ((SliceRank.blockStep A [y])^[j] q) i with hgdef
  have hgper : ∀ q : A.Q, ∀ j, mb ≤ j → g q (j + pσ * pb) = g q j := by
    intro q j hj
    have hstep : (SliceRank.blockStep A [y])^[j + pσ * pb] = (SliceRank.blockStep A [y])^[j] := by
      rw [show j + pσ * pb = j + pb * pσ by ring]; exact hb pσ j hj
    show SliceRank.blockWeight A [y] ((SliceRank.blockStep A [y])^[j + pσ * pb] q) i
        = SliceRank.blockWeight A [y] ((SliceRank.blockStep A [y])^[j] q) i
    rw [congrFun hstep q]
  -- σ period-multiple
  have hσmul : ∀ k mS, mσ ≤ mS → σ (mS + pσ * k) = σ mS := by
    intro k
    induction k with
    | zero => intro mS _; simp
    | succ a ih =>
      intro mS h
      rw [show mS + pσ * (a + 1) = (mS + pσ * a) + pσ by ring, hσper _ (by omega), ih mS h]
  -- reduce the goal's coordinate-applied vector sum to the scalar sum of g
  have hcoord : (fun mS => (∑ j ∈ Finset.range (mS - c),
        SliceRank.blockWeight A [y] ((SliceRank.blockStep A [y])^[j] (σ mS))) i)
      = fun mS => ∑ j ∈ Finset.range (mS - c), g (σ mS) j := by
    funext mS; rw [Finset.sum_apply]
  rw [hcoord]
  refine ⟨pσ * pb, Nat.mul_pos hpσ hpb, max mσ (mb + c), fun jr _ => ?_⟩
  set q0 : A.Q := σ (max mσ (mb + c) + jr) with hq0def
  have hmσle : mσ ≤ max mσ (mb + c) + jr := by
    have := le_max_left mσ (mb + c); omega
  have hmbc : mb + c ≤ max mσ (mb + c) + jr := by
    have := le_max_right mσ (mb + c); omega
  -- the per-residue recurrence for the partial sum from the frozen start q0
  have hrec : ∀ N, mb ≤ N → (∑ j ∈ Finset.range (N + pσ * pb), g q0 j)
      = (∑ j ∈ Finset.range N, g q0 j)
        + (∑ j ∈ Finset.Ico mb (mb + pσ * pb), g q0 j) :=
    SliceAutomata.partialSum_recurrence' (g q0) mb (pσ * pb)
      (fun j hj => hgper q0 j hj)
  refine ⟨∑ j ∈ Finset.range (max mσ (mb + c) + jr - c), g q0 j,
    ∑ j ∈ Finset.Ico mb (mb + pσ * pb), g q0 j, fun k => ?_⟩
  show (∑ j ∈ Finset.range (max mσ (mb + c) + jr + pσ * pb * k - c),
      g (σ (max mσ (mb + c) + jr + pσ * pb * k)) j) = _
  -- freeze σ on the residue class
  have hσfix : σ (max mσ (mb + c) + jr + pσ * pb * k) = q0 := by
    rw [show max mσ (mb + c) + jr + pσ * pb * k = (max mσ (mb + c) + jr) + pσ * (pb * k) by ring,
      hσmul (pb * k) _ hmσle]
  rw [hσfix]
  -- absorb the c-subtraction into the range index
  rw [show max mσ (mb + c) + jr + pσ * pb * k - c
      = (max mσ (mb + c) + jr - c) + pσ * pb * k by omega]
  -- partial-sum-as-affine recurrence at period pσ*pb
  have haff := SliceAutomata.recurrence_affineOnResidues
    (fun N => ∑ j ∈ Finset.range N, g q0 j) mb (pσ * pb)
    (∑ j ∈ Finset.Ico mb (mb + pσ * pb), g q0 j) hrec k
    (max mσ (mb + c) + jr - c - mb)
  rw [show mb + pσ * pb * k + (max mσ (mb + c) + jr - c - mb)
      = (max mσ (mb + c) + jr - c) + pσ * pb * k by omega,
    show mb + (max mσ (mb + c) + jr - c - mb) = max mσ (mb + c) + jr - c by omega] at haff
  rw [haff, nsmul_eq_mul]

/-- **An eventually-periodic `ℤ`-stream is affine-on-residues (slope 0).**  The deep-suffix `β`-state
correction `s.β (state mS) D coord` is EP-in-mS (the post-`D^{mS-i}` state is EP via
`iterate_EPstate_EP_mS`), hence affine-on-residues with zero slope — the form the rank assembly
consumes alongside the genuinely-sloped prefix/suffix-run pieces. -/
theorem affineOnResiduesAtZ_of_EP {F : ℕ → ℤ} {q : ℕ} (m : ℕ)
    (hper : ∀ mS, m ≤ mS → F (mS + q) = F mS) : AffineOnResiduesAtZ q F := by
  refine ⟨m, fun jr _ => ⟨F (m + jr), 0, fun k => ?_⟩⟩
  simp only [mul_zero, add_zero]
  induction k with
  | zero => simp
  | succ a ih =>
    rw [show m + jr + q * (a + 1) = (m + jr + q * a) + q by ring, hper _ (by omega), ih]

/-- **Coordinate form of the prefix-run engine.**  The `i`-th coordinate of `prefixRank(x^{mS} ++ suf)`
is affine-on-residues in `mS` — the per-coordinate `of_recurrence` repackaging of
`prefixRank_run_affine_mS` (which is a vector equation with a `k • P` slope). -/
theorem prefixRank_run_coord_affine_mS {Alpha : Type*} {d : ℕ} (A : RankSource Alpha d)
    (x : Alpha) (suf : List Alpha) (i : Fin d) :
    ∃ p, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => A.prefixRank (List.replicate mS x ++ suf)
        (List.replicate mS x ++ suf).length i) := by
  obtain ⟨m, p, P, hp, hb⟩ := prefixRank_run_affine_mS A x suf
  refine ⟨p, hp, AffineOnResiduesAtZ.of_recurrence hp (m := m) (S := P i) (fun mS hmS => ?_)⟩
  have hthis := hb 1 (mS - m)
  rw [show m + p * 1 + (mS - m) = mS + p by omega, show m + (mS - m) = mS by omega] at hthis
  have hc := congrFun hthis i
  rw [Pi.add_apply, Pi.smul_apply, one_nsmul] at hc
  exact hc

/-- **Head/tail split of a prefix rank.**  `prefixRank(headW ++ x^N)` (full length) splits as the
head rank `prefixRank(headW)` plus the block-weight sum of the `x^N` tail read from the post-head state
`foldl δ q₀ headW`.  The arithmetic core of the deep-suffix rank: with `headW = U^mS ++ (UD)^n` and
`x^N = D^{mS-i}`, the head is affine via `prefixRank_run_coord_affine_mS` and the tail via
`partialSum_blockWeight_EPstate_affine_mS` (the post-head state is EP-in-mS). -/
theorem prefixRank_headTail_split {Alpha : Type*} {d : ℕ} (A : RankSource Alpha d)
    (headW : List Alpha) (x : Alpha) (N : ℕ) :
    A.prefixRank (headW ++ List.replicate N x) (headW ++ List.replicate N x).length
      = A.prefixRank headW headW.length
        + ∑ j ∈ Finset.range N, SliceRank.blockWeight A [x]
            ((SliceRank.blockStep A [x])^[j] (List.foldl A.δ A.q0 headW)) := by
  rw [SliceRank.prefixRank_eq_foldl, SliceRank.prefixRank_eq_foldl,
    ← flatten_replicate_singleton x N, List.foldl_append]
  obtain ⟨sth, rkh, hpr⟩ :
      ∃ sth rkh, List.foldl (SliceRank.rankStep A) (A.q0, 0) headW = (sth, rkh) := ⟨_, _, rfl⟩
  have hsth : sth = List.foldl A.δ A.q0 headW := by
    rw [← SliceRank.rankStep_fst A A.q0 0 headW, hpr]
  rw [hpr, SliceRank.rankStep_snd_add, SliceRank.foldl_rankStep_replicate_snd, hsth, zero_add]

/-- **The two-growing-run prefix rank is affine-on-residues in `mS`** (the deep-suffix math core).
For the deep-suffix atom, `prefixRank(U^mS ++ suf ++ D^{mS-i})` reads TWO growing runs.  Via
`prefixRank_headTail_split` it is `prefixRank(U^mS ++ suf)` (affine by `prefixRank_run_coord_affine_mS`)
plus the `D^{mS-i}` tail block-sum from the EP-in-mS post-head state `foldl δ q₀ (U^mS ++ suf)`
(affine by `partialSum_blockWeight_EPstate_affine_mS`).  This is what the existing
`summand_copied_sufStretch_affine_mS` (shallow `l`, fixed run) cannot reach. -/
theorem prefixRank_deepSuf_affine_mS {d : ℕ} (A : RankSource Step d) (suf : List Step)
    (i_off : ℕ) (i : Fin d) :
    ∃ p, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => A.prefixRank (List.replicate mS U ++ suf ++ List.replicate (mS - i_off) D)
        (List.replicate mS U ++ suf ++ List.replicate (mS - i_off) D).length i) := by
  have := A.fintypeQ
  obtain ⟨pH, hpH, hHaff⟩ := prefixRank_run_coord_affine_mS A U suf i
  obtain ⟨m2, p2, hp2, hper2⟩ := SliceAutomata.iterate_eventuallyPeriodic (fun q => A.δ q U) A.q0
  have hσ2per : ∀ mS, m2 ≤ mS →
      (fun mS => List.foldl A.δ A.q0 (List.replicate mS U ++ suf)) (mS + p2)
        = (fun mS => List.foldl A.δ A.q0 (List.replicate mS U ++ suf)) mS := by
    intro mS hmS
    simp only []
    rw [List.foldl_append, List.foldl_append, foldl_replicate_eq_iterate,
      foldl_replicate_eq_iterate, hper2 mS hmS]
  obtain ⟨pT, hpT, hTaff⟩ := partialSum_blockWeight_EPstate_affine_mS A D
    (fun mS => List.foldl A.δ A.q0 (List.replicate mS U ++ suf)) p2 hp2 m2 hσ2per i_off i
  have hG := (hHaff.of_dvd hpH (dvd_mul_right pH pT) (Nat.mul_pos hpH hpT)).add
    (Nat.mul_pos hpH hpT) (hTaff.of_dvd hpT (dvd_mul_left pT pH) (Nat.mul_pos hpH hpT))
  refine ⟨pH * pT, Nat.mul_pos hpH hpT, AffineOnResiduesAtZ.congr' (fun mS => ?_) hG⟩
  have hsplit := congrFun (prefixRank_headTail_split A (List.replicate mS U ++ suf) D (mS - i_off)) i
  rw [Pi.add_apply] at hsplit
  exact hsplit.symm

/-- **Piece (c): a summand's block-`U` cell value is affine-on-residues in `mS`.**  For a fixed
middle block index `j`, the `i`-th component of `s.eval (copiedSlice mS (j+1)) (atom at base j)` is
affine-on-residues in the boundary width `mS` (at period `p₁·p₂`).  This combines the mS-direction
prefix-rank engine (b) for `s.coeff • prefixRank(U^mS ++ (UD)^j)` with the post-prefix-state EP
(cornerstone) for `s.β(state) U`, through `CopiedRank.summand_copied_block_eq`. -/
theorem summand_copied_block_affine_mS {k : ℕ} (s : Summand Step d k) (j : ℕ) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS (j + 1)) (fun _ => mS + 2 * j) i) := by
  have := s.A.fintypeQ
  obtain ⟨m1, p1, P1, hp1, hb⟩ :=
    prefixRank_run_affine_mS s.A U ((List.replicate j [U, D]).flatten)
  obtain ⟨m2, p2, hp2, hper2⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
  refine ⟨p1 * p2, Nat.mul_pos hp1 hp2,
    AffineOnResiduesAtZ.of_recurrence (Nat.mul_pos hp1 hp2)
      (m := max m1 m2 + 1) (S := s.coeff * ((p2 : ℤ) * P1 i)) (fun n hn => ?_)⟩
  have hnpos : 1 ≤ n := by omega
  -- the prefix-rank step (piece b at k = p2): prefixRank(n+p1*p2) = prefixRank(n) + p2 • P1
  have hpre := hb p2 (n - m1)
  rw [show m1 + p1 * p2 + (n - m1) = n + p1 * p2 by omega,
    show m1 + (n - m1) = n by omega] at hpre
  -- the post-prefix state step: state at n+p1*p2 equals state at n
  have hstate : List.foldl s.A.δ s.A.q0 (List.replicate (n + p1 * p2) U)
      = List.foldl s.A.δ s.A.q0 (List.replicate n U) := by
    rw [foldl_replicate_eq_iterate, foldl_replicate_eq_iterate,
      show n + p1 * p2 = n + p2 * p1 by ring]
    exact iterate_period_mul (fun q => s.A.δ q U) s.A.q0 m2 p2 hper2 p1 n (by omega)
  -- decompose both sides via summand_copied_block_eq, then rewrite the two steps
  rw [congrFun (summand_copied_block_eq s (n + p1 * p2) j (by omega)) i,
    congrFun (summand_copied_block_eq s n j hnpos) i, hpre, hstate]
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

/-- **Piece (c), block-`D` case.**  Same template as the block case: the extra `ω(state) U`
(inside `coeff •`) and `β(δ(state) U) D` terms are functions of the post-prefix state, which is
EP in `mS`, so they cancel under the state step — leaving the same affine slope. -/
theorem summand_copied_blockD_affine_mS {k : ℕ} (s : Summand Step d k) (j : ℕ) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS (j + 1)) (fun _ => mS + 2 * j + 1) i) := by
  have := s.A.fintypeQ
  obtain ⟨m1, p1, P1, hp1, hb⟩ :=
    prefixRank_run_affine_mS s.A U ((List.replicate j [U, D]).flatten)
  obtain ⟨m2, p2, hp2, hper2⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
  refine ⟨p1 * p2, Nat.mul_pos hp1 hp2,
    AffineOnResiduesAtZ.of_recurrence (Nat.mul_pos hp1 hp2)
      (m := max m1 m2 + 1) (S := s.coeff * ((p2 : ℤ) * P1 i)) (fun n hn => ?_)⟩
  have hnpos : 1 ≤ n := by omega
  have hpre := hb p2 (n - m1)
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
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

/-- **Piece (c), suffix-letter case** (the leading `D` after the middle, base `n0`). -/
theorem summand_copied_suf_affine_mS {k : ℕ} (s : Summand Step d k) (n0 : ℕ) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n0) (fun _ => mS + 2 * n0) i) := by
  have := s.A.fintypeQ
  obtain ⟨m1, p1, P1, hp1, hb⟩ :=
    prefixRank_run_affine_mS s.A U ((List.replicate n0 [U, D]).flatten)
  obtain ⟨m2, p2, hp2, hper2⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
  refine ⟨p1 * p2, Nat.mul_pos hp1 hp2,
    AffineOnResiduesAtZ.of_recurrence (Nat.mul_pos hp1 hp2)
      (m := max m1 m2 + 1) (S := s.coeff * ((p2 : ℤ) * P1 i)) (fun n hn => ?_)⟩
  have hnpos : 1 ≤ n := by omega
  have hpre := hb p2 (n - m1)
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

/-- **Piece (c), suffix-stretch case** (the `l`-th trailing `D`, `l < mS-1`).  The fixed run
suffix is `(UD)^{n0} ++ D^{l+1}`; the threshold absorbs the `l < mS-1` existence constraint.
An associativity bridge aligns the engine's `U^mS ++ (suf₁ ++ suf₂)` with the eq lemma's
`(U^mS ++ suf₁) ++ suf₂`. -/
theorem summand_copied_sufStretch_affine_mS {k : ℕ} (s : Summand Step d k) (n0 l : ℕ) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n0) (fun _ => mS + 2 * n0 + 1 + l) i) := by
  have := s.A.fintypeQ
  obtain ⟨m1, p1, P1, hp1, hb⟩ :=
    prefixRank_run_affine_mS s.A U ((List.replicate n0 [U, D]).flatten ++ List.replicate (l + 1) D)
  obtain ⟨m2, p2, hp2, hper2⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
  refine ⟨p1 * p2, Nat.mul_pos hp1 hp2,
    AffineOnResiduesAtZ.of_recurrence (Nat.mul_pos hp1 hp2)
      (m := max (max m1 m2) (l + 1) + 1) (S := s.coeff * ((p2 : ℤ) * P1 i)) (fun n hn => ?_)⟩
  have hpre := hb p2 (n - m1)
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

/-- **Eventual-equality congruence for `AffineOnResiduesAtZ`** (a (d)-lift helper): if `F` agrees
with an affine-on-residues `G` past a threshold `m0`, then `F` is affine-on-residues too. -/
theorem affineOnResiduesAtZ_congr_eventually {p : ℕ} (hp : 1 ≤ p) {F G : ℕ → ℤ} {m0 : ℕ}
    (hFG : ∀ w, m0 ≤ w → F w = G w) (hG : AffineOnResiduesAtZ p G) : AffineOnResiduesAtZ p F := by
  obtain ⟨m, hm⟩ := AffineOnResiduesAtZ.exists_rebase hp hG
  refine ⟨max m m0, fun j hj => ?_⟩
  obtain ⟨b, ss, hbs⟩ := hm (max m m0) (le_max_left _ _) j hj
  exact ⟨b, ss, fun k => by
    rw [hFG (max m m0 + j + p * k) (by have := le_max_right m m0; omega)]; exact hbs k⟩

/-- **The PREFIX-stretch summand formula↔eval bridge** (d3.4 prefix-engine, the mirror of
`summand_copied_sufStretch_eq`).  For a coordinate at a prefix position `q < mS-1` (where
`posAt (.prefIdx q) = q` is mS-FREE), `s.eval` reads the first `q` letters `U^q` (a pure `δ_U` run).
STRICTLY SIMPLER than the suffix twin: no `U^mS ++ (UD)^n` pre-blocks and no growing tail — just `U^q`,
and the formula is mS-FREE and n-FREE.  This is what makes the prefix engine cheap (no `reverseComplement`
needed) — the deep-PREFIX analog of the d3.3 suffix collapse. -/
theorem summand_copied_prefStretch_eq {k : ℕ} (s : Summand Step d k)
    (mS q : ℕ) (hq : q < mS - 1) (n : ℕ) :
    s.eval (copiedSlice mS n) (fun _ => q) =
      s.coeff • s.A.prefixRank (List.replicate q U) (List.replicate q U).length
        + s.β (List.foldl s.A.δ s.A.q0 (List.replicate q U)) U := by
  have hm : 1 ≤ mS := by omega
  have hget : (copiedSlice mS n)[q]? = some U :=
    copiedSlice_getElem?_pref mS n q hm (by omega)
  have hpref : s.A.prefixRank (copiedSlice mS n) q
      = s.A.prefixRank (List.replicate q U) (List.replicate q U).length := by
    rw [List.length_replicate]
    exact SliceRankAtom.prefixRank_prefix_stable s.A _ _ q
      (by rw [copiedSlice_take_U mS q n hm (by omega), List.take_replicate, Nat.min_self])
  have hstate : s.A.stateBefore (copiedSlice mS n) q
      = List.foldl s.A.δ s.A.q0 (List.replicate q U) := by
    unfold RankSource.stateBefore
    rw [copiedSlice_take_U mS q n hm (by omega)]
  unfold Summand.eval
  funext c
  rw [hget, Option.elim_some, hpref, hstate]
  simp

open SliceRankAtom in
/-- **The PREFIX-stretch summand formula is `RankAffine` in the prefix depth `q`** (d3.4 prefix-engine,
the mirror of `sufStretch_formula_rankAffine_l`).  EVEN SIMPLER than the suffix: empty pre-blocks and NO
`+1` shift (the run is exactly `U^q`).  PART A `prefixRank(U^q)` via `prefixRank_pre_blocks_tail_rankAffine`
with empty pre/suf; PART B `s.β(δ_U^q q0) U` via `rankAffine_of_iterate` from the bare start `q0`. -/
theorem prefStretch_formula_rankAffine_q {k : ℕ} (s : Summand Step d k) :
    RankAffine (fun q =>
      s.coeff • s.A.prefixRank (List.replicate q U) (List.replicate q U).length
        + s.β (List.foldl s.A.δ s.A.q0 (List.replicate q U)) U) := by
  have := s.A.fintypeQ
  refine RankAffine.add (RankAffine.smul s.coeff ?_) ?_
  · refine RankAffine.congr (fun q => ?_)
      (prefixRank_pre_blocks_tail_rankAffine s.A [] [U] [])
    simp only [List.nil_append, List.append_nil, flatten_replicate_singleton]
  · refine RankAffine.congr (fun q => ?_)
      (rankAffine_of_iterate (fun st => s.A.δ st U) s.A.q0 (fun st => s.β st U))
    rw [foldl_replicate_iterate s.A.δ U]

/-- **Piece (d1): the DEEP-PREFIX coord's rank is affine-on-residues in `mS`** (d3.4 prefix-engine,
the mirror of `summand_copied_deepSuf_affine_mS`).  A deep-prefix coord at `prefIdx (mS-1-i_off)` sits at
position `mS-1-i_off` (GROWING with mS, near the end of the U-prefix); `s.eval` there reads `U^{mS-1-i_off}`,
affine in mS.  Proof: reindex `prefStretch_formula_rankAffine_q`'s `RankAffine` recurrence (period `p`,
`(mS+p)-1-i_off = (mS-1-i_off)+p`) through `AffineOnResiduesAtZ.of_recurrence`, bridging `s.eval` to the
formula via `summand_copied_prefStretch_eq` at `q = mS-1-i_off`.  SIMPLER than the deep-suffix twin (the
U-run is the whole word; no `(UD)^n0` middle or grown D-tail). -/
theorem summand_copied_deepPref_affine_mS {k : ℕ} (s : Summand Step d k)
    (n0 i_off : ℕ) (hi : 1 ≤ i_off) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n0) (fun _ => mS - 1 - i_off) i) := by
  obtain ⟨m, p, P, hp, hrec⟩ := prefStretch_formula_rankAffine_q s
  refine ⟨p, hp, AffineOnResiduesAtZ.of_recurrence hp (m := m + 1 + i_off) (S := P i)
    (fun w hw => ?_)⟩
  rw [congrFun (summand_copied_prefStretch_eq s (w + p) (w + p - 1 - i_off) (by omega) n0) i,
      congrFun (summand_copied_prefStretch_eq s w (w - 1 - i_off) (by omega) n0) i,
      show w + p - 1 - i_off = (w - 1 - i_off) + p by omega]
  exact congrFun (hrec (w - 1 - i_off) (by omega)) i

/-- **Piece (d1), prefIdx case** (prefix stretch coord, FIXED `q`): `s.eval` at a fixed prefix
position is CONSTANT in `mS` (the first `q+1` letters are `U^{q+1}` for every `mS > q`), hence
affine-on-residues with slope 0. -/
theorem summand_copied_prefIdx_affine_mS {k : ℕ} (s : Summand Step d k) (q n : ℕ) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n) (fun _ => q) i) := by
  refine ⟨1, le_refl 1, affineOnResiduesAtZ_congr_eventually (le_refl 1)
    (G := fun _ => s.eval (copiedSlice (q + 1) n) (fun _ => q) i) (m0 := q + 1) (fun w hw => ?_)
    (AffineOnResiduesAtZ.const 1 _)⟩
  exact congrFun (SliceRankAtom.summand_eval_const_prefix_stable s (copiedSlice w n)
    (copiedSlice (q + 1) n) q (by
      rw [copiedSlice_take_U w (q + 1) n (by omega) (by omega),
        copiedSlice_take_U (q + 1) (q + 1) n (by omega) (le_refl _)])) i

/-- **Piece (d1), pre-letter case** (the last prefix `U`, position `mS-1`): `s.eval` there reads
`U^{mS-1}` then the `U` at `mS-1`, so it is affine-on-residues in `mS` (run length `mS-1`). -/
theorem summand_copied_pre_affine_mS {k : ℕ} (s : Summand Step d k) (n : ℕ) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n) (fun _ => mS - 1) i) := by
  have := s.A.fintypeQ
  obtain ⟨m1, p1, P1, hp1, hb⟩ := prefixRank_run_affine_mS s.A U []
  obtain ⟨m2, p2, hp2, hper2⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
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
  refine ⟨p1 * p2, Nat.mul_pos hp1 hp2,
    AffineOnResiduesAtZ.of_recurrence (Nat.mul_pos hp1 hp2)
      (m := max m1 m2 + 2) (S := s.coeff * ((p2 : ℤ) * P1 i)) (fun w hw => ?_)⟩
  rw [hEq (w + p1 * p2) (by omega), hEq w (by omega)]
  have hpre := hb p2 ((w - 1) - m1)
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

/-- **Piece (d1), unified middle case** (front / cluster / back all land here): for an mS-free
block index `j < n`, `s.eval` at the middle position `mS-1+(1+2j+e)` is affine-on-residues in `mS`
— reduce `copiedSlice mS n` → `copiedSlice mS (j+1)` via `summand_copied_mid_stable` and apply the
block (`e=false`) / blockD (`e=true`) piece-(c) lemma through `congr_eventually`. -/
theorem summand_copied_mid_affine_mS {k : ℕ} (s : Summand Step d k) (j n : ℕ) (e : Bool)
    (i : Fin d) (hjn : j < n) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n) (fun _ => mS - 1 + (1 + 2 * j + e.toNat)) i) := by
  cases e with
  | false =>
    obtain ⟨p, hp, hG⟩ := summand_copied_block_affine_mS s j i
    refine ⟨p, hp, affineOnResiduesAtZ_congr_eventually hp (m0 := 1) (fun w hw => ?_) hG⟩
    rw [show w - 1 + (1 + 2 * j + (false : Bool).toNat) = w - 1 + (2 * j + 1) from by
        simp only [Bool.toNat_false]; omega,
      congrFun (summand_copied_mid_stable s w (2 * j + 1) n (j + 1) hw (by omega) (by omega)) i,
      show w - 1 + (2 * j + 1) = w + 2 * j from by omega]
  | true =>
    obtain ⟨p, hp, hG⟩ := summand_copied_blockD_affine_mS s j i
    refine ⟨p, hp, affineOnResiduesAtZ_congr_eventually hp (m0 := 1) (fun w hw => ?_) hG⟩
    rw [show w - 1 + (1 + 2 * j + (true : Bool).toNat) = w - 1 + (2 * j + 2) from by
        simp only [Bool.toNat_true]; omega,
      congrFun (summand_copied_mid_stable s w (2 * j + 2) n (j + 1) hw (by omega) (by omega)) i,
      show w - 1 + (2 * j + 2) = w + 2 * j + 1 from by omega]

/-- **Piece (d1): a summand's cell value at ANY region descriptor is affine-on-residues in `mS`.**
The mS-mirror of `CopiedRank.summand_region_decomp_fibred`'s case analysis: for a descriptor
`r : RegionSpecF B` and a bulk base (`t + B ≤ n`), `s.eval (copiedSlice mS n) (cell at r) i` is
affine-on-residues in `mS`.  Dispatches each region to its piece-(c) lemma (front/cluster/back via
the unified middle helper, suf/sufIdx directly, pre/prefIdx via their cases). -/
theorem summand_cell_affine_mS {k B : ℕ} (s : Summand Step d k) (r : RegionSpecF B)
    (t n : ℕ) (i : Fin d) (_hB : 1 ≤ B) (htBn : t + B ≤ n) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n) (fun _ => r.posAt mS t n) i) := by
  rcases r with rr | q | l
  · rcases rr with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
    · -- core pre
      obtain ⟨p, hp, hG⟩ := summand_copied_pre_affine_mS s n i
      refine ⟨p, hp, affineOnResiduesAtZ_congr_eventually hp (m0 := 1) (fun w hw => ?_) hG⟩
      simp only [RegionSpecF.posAt, RegionSpec.posAt, Nat.add_zero]
    · -- core suf
      obtain ⟨p, hp, hG⟩ := summand_copied_suf_affine_mS s n i
      refine ⟨p, hp, affineOnResiduesAtZ_congr_eventually hp (m0 := 1) (fun w hw => ?_) hG⟩
      simp only [RegionSpecF.posAt, RegionSpec.posAt]
      rw [show (fun _ : Fin k => w - 1 + (1 + 2 * n)) = (fun _ : Fin k => w + 2 * n) from
        funext fun _ => by omega]
    · -- core front f e
      simp only [RegionSpecF.posAt, RegionSpec.posAt]
      exact summand_copied_mid_affine_mS s f.val n e i (by have := f.isLt; omega)
    · -- core back l e
      simp only [RegionSpecF.posAt, RegionSpec.posAt]
      exact summand_copied_mid_affine_mS s (n - 1 - l.val) n e i (by omega)
    · -- core cluster δ e
      simp only [RegionSpecF.posAt, RegionSpec.posAt]
      exact summand_copied_mid_affine_mS s (t + δ.val) n e i (by have := δ.isLt; omega)
  · -- prefIdx q
    simp only [RegionSpecF.posAt]
    exact summand_copied_prefIdx_affine_mS s q n i
  · -- sufIdx l
    simp only [RegionSpecF.posAt]
    exact summand_copied_sufStretch_affine_mS s n l i

/-- **List-sum closure for `AffineOnResiduesAtZ`**: a finite sum of per-term affine-on-residues
functions (each at its own period) is affine-on-residues at the period PRODUCT. -/
theorem affineOnResiduesAtZ_listSum {α : Type*} (L : List α) (F : α → ℕ → ℤ)
    (hF : ∀ a ∈ L, ∃ p, 1 ≤ p ∧ AffineOnResiduesAtZ p (F a)) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p (fun mS => (L.map (fun a => F a mS)).sum) := by
  induction L with
  | nil => exact ⟨1, le_refl 1, by simpa using AffineOnResiduesAtZ.const 1 0⟩
  | cons a L' ih =>
    obtain ⟨pa, hpa, hAa⟩ := hF a (by simp)
    obtain ⟨pL, hpL, hAL⟩ := ih (fun b hb => hF b (by simp [hb]))
    have hpos : 1 ≤ pa * pL := Nat.mul_pos hpa hpL
    have h1 := AffineOnResiduesAtZ.of_dvd hpa ⟨pL, rfl⟩ hpos hAa
    have h2 := AffineOnResiduesAtZ.of_dvd hpL ⟨pa, Nat.mul_comm pa pL⟩ hpos hAL
    refine ⟨pa * pL, hpos, ?_⟩
    have heq : (fun mS => ((a :: L').map (fun b => F b mS)).sum)
        = (fun mS => F a mS + (L'.map (fun b => F b mS)).sum) := by
      funext mS; simp [List.map_cons, List.sum_cons]
    rw [heq]
    exact AffineOnResiduesAtZ.add hpos h1 h2

/-- **Piece (d2): the cell RANK is affine-on-residues in `mS`.**  Summing piece (d1) over the
rank term's summands (each reads its `π`-th coord), plus the constant `c0`, through
`IsRegularRankTerm` and `RankTerm.eval`. -/
theorem rank_cell_affine_mS {B : ℕ} (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c) → CopiedCells.RegionSpecF B) (t n : ℕ) (i : Fin P.d)
    (hB : 1 ≤ B) (htBn : t + B ≤ n) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => P.rank c (copiedSlice mS n) (cellTupleF rs mS t n) i) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  obtain ⟨p, hp, hAsum⟩ := affineOnResiduesAtZ_listSum κ.summands
    (fun s mS => s.eval (copiedSlice mS n) (cellTupleF rs mS t n) i)
    (fun s _ => summand_cell_affine_mS s (rs s.π) t n i hB htBn)
  refine ⟨p, hp, ?_⟩
  have key : (fun mS => P.rank c (copiedSlice mS n) (cellTupleF rs mS t n) i)
      = (fun mS => κ.c0 i
          + (κ.summands.map (fun s => s.eval (copiedSlice mS n) (cellTupleF rs mS t n) i)).sum) := by
    funext mS
    rw [hκ (copiedSlice mS n) (cellTupleF rs mS t n)]
    rfl
  rw [key]
  exact AffineOnResiduesAtZ.add hp (AffineOnResiduesAtZ.const p _) hAsum

/-- **Piece (c), DEEP-suffix case** (`l = mS-1-i_off`, the trailing `D` near the end of `D^mS`).
The summand value of a deep-suffix atom is affine-on-residues in `mS`.  Unlike the shallow case, the
`D`-run `D^{mS-i_off}` GROWS, so it cannot be folded into a fixed `suf`: the `s.coeff • prefixRank`
part is handled by `prefixRank_deepSuf_affine_mS` (two growing runs), and the `β`-state correction is
EP-in-mS (`iterate_EPstate_EP_mS` on the post-`(UD)^{n0}` state `σB`) hence affine by
`affineOnResiduesAtZ_of_EP`.  Glued through `summand_copied_sufStretch_eq` at `l = mS-1-i_off`. -/
theorem summand_copied_deepSuf_affine_mS {k : ℕ} (s : Summand Step d k)
    (n0 i_off : ℕ) (hi : 1 ≤ i_off) (i : Fin d) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => s.eval (copiedSlice mS n0) (fun _ => mS + 2 * n0 + 1 + (mS - 1 - i_off)) i) := by
  have := s.A.fintypeQ
  -- PART A: s.coeff • prefixRank(U^mS ++ (UD)^n0 ++ D^{mS-i_off}) is affine
  obtain ⟨pA, hpA, hAaff⟩ :=
    prefixRank_deepSuf_affine_mS s.A ((List.replicate n0 [U, D]).flatten) i_off i
  -- PART B: the β-state correction, EP-in-mS hence affine
  obtain ⟨m2, p2, hp2, hper2⟩ := SliceAutomata.iterate_eventuallyPeriodic (fun q => s.A.δ q U) s.A.q0
  have hσBper : ∀ mS, m2 ≤ mS →
      (fun mS => (fun q => List.foldl s.A.δ q [U, D])^[n0] (List.foldl s.A.δ s.A.q0
        (List.replicate mS U))) (mS + p2)
        = (fun mS => (fun q => List.foldl s.A.δ q [U, D])^[n0] (List.foldl s.A.δ s.A.q0
            (List.replicate mS U))) mS := by
    intro mS hmS
    simp only []
    rw [foldl_replicate_eq_iterate, foldl_replicate_eq_iterate, hper2 mS hmS]
  obtain ⟨qF, hqF, MF, hFper⟩ := iterate_EPstate_EP_mS (fun q => s.A.δ q D)
    (fun mS => (fun q => List.foldl s.A.δ q [U, D])^[n0] (List.foldl s.A.δ s.A.q0
      (List.replicate mS U))) p2 hp2 m2 hσBper i_off
  have hβaff : AffineOnResiduesAtZ qF (fun mS => (s.β ((fun q => s.A.δ q D)^[mS - i_off]
      ((fun q => List.foldl s.A.δ q [U, D])^[n0] (List.foldl s.A.δ s.A.q0
        (List.replicate mS U)))) D) i) := by
    refine affineOnResiduesAtZ_of_EP MF (fun mS hmS => ?_)
    show (s.β ((fun q => s.A.δ q D)^[mS + qF - i_off]
        ((fun q => List.foldl s.A.δ q [U, D])^[n0] (List.foldl s.A.δ s.A.q0
          (List.replicate (mS + qF) U)))) D) i = _
    rw [hFper mS hmS]
  -- combine and bridge through the eq lemma
  have hG := ((hAaff.of_dvd hpA (dvd_mul_right pA qF) (Nat.mul_pos hpA hqF)).smul s.coeff).add
    (Nat.mul_pos hpA hqF) (hβaff.of_dvd hqF (dvd_mul_left qF pA) (Nat.mul_pos hpA hqF))
  refine ⟨pA * qF, Nat.mul_pos hpA hqF,
    affineOnResiduesAtZ_congr_eventually (m0 := i_off + 2) (Nat.mul_pos hpA hqF) (fun mS hmS => ?_) hG⟩
  rw [congrFun (summand_copied_sufStretch_eq s mS (mS - 1 - i_off) (by omega) n0) i,
    show mS - 1 - i_off + 1 = mS - i_off by omega, foldl_replicate_eq_iterate]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **Mixed cell descriptor (deep-suffix candidate set).**  Each coordinate is either a fixed
wrapped-flat / stretch descriptor (`inl r : RegionSpecF B`) or a DEEP-suffix offset
(`inr i_off`, `i_off ≥ 1`) standing for the moving descriptor `sufIdx (mS-1-i_off)` whose `D`-run
`D^{mS-i_off}` grows with `mS`.  A fixed `RegionSpecF B` cannot reach the deep-suffix region (its
`sufIdx l` carries a fixed `l`), so the deep case needs this separate `inr` marker. -/
def mixedPosAt {B : ℕ} (ds : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (mS t n : ℕ) : ℕ :=
  match ds with
  | .inl r => r.posAt mS t n
  | .inr (.inl i_off) => mS + 2 * n + 1 + (mS - 1 - i_off)
  | .inr (.inr i_off) => mS - 1 - i_off

/-- The cell tuple of a mixed descriptor: coordinatewise `mixedPosAt`. -/
def mixedTupleF {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (mS t n : ℕ) : Fin k → ℕ :=
  fun j => mixedPosAt (ds j) mS t n

/-- **Piece (d3.1): the cell RANK of a MIXED-descriptor tuple is affine-on-residues in `mS`.**
Generalises `rank_cell_affine_mS` to tuples whose suffix coordinates may be DEEP (`l = mS-1-i_off`,
a growing `D`-run).  Each summand reads only its own coordinate `s.π` (`Summand.eval` queries
`ī s.π`), so the per-summand value dispatches on `ds s.π`: a fixed descriptor goes through
`summand_cell_affine_mS`, a deep offset through `summand_copied_deepSuf_affine_mS`; the cell rank is
then the `affineOnResiduesAtZ_listSum` of the summands plus the constant `κ.c0`.  This is the
candidate-value engine for the bounded deep-suffix effective set feeding
`gated_lexMin_affine_at_growing`. -/
theorem rank_cell_mixedDeep_affine_mS {B : ℕ} (P : WRP.Presentation Step Step)
    (c : Fin P.toPoly.K) (ds : Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ))
    (t n : ℕ) (i : Fin P.d) (hB : 1 ≤ B) (htBn : t + B ≤ n)
    (hdeep : ∀ j e, ds j = .inr e → 1 ≤ e.elim id id) :
    ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
      (fun mS => P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n) i) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  obtain ⟨p, hp, hAsum⟩ := affineOnResiduesAtZ_listSum κ.summands
    (fun s mS => s.eval (copiedSlice mS n) (mixedTupleF ds mS t n) i)
    (fun s _ => by
      show ∃ p : ℕ, 1 ≤ p ∧ AffineOnResiduesAtZ p
        (fun mS => s.eval (copiedSlice mS n) (fun _ => mixedPosAt (ds s.π) mS t n) i)
      rcases hd : ds s.π with r | (i_off | i_off)
      · exact summand_cell_affine_mS s r t n i hB htBn
      · exact summand_copied_deepSuf_affine_mS s n i_off (hdeep s.π (.inl i_off) hd) i
      · exact summand_copied_deepPref_affine_mS s n i_off (hdeep s.π (.inr i_off) hd) i)
  refine ⟨p, hp, ?_⟩
  have key : (fun mS => P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n) i)
      = (fun mS => κ.c0 i
          + (κ.summands.map (fun s => s.eval (copiedSlice mS n) (mixedTupleF ds mS t n) i)).sum) := by
    funext mS
    rw [hκ (copiedSlice mS n) (mixedTupleF ds mS t n)]
    rfl
  rw [key]
  exact AffineOnResiduesAtZ.add hp (AffineOnResiduesAtZ.const p _) hAsum

/-- The mS-dependent `RegionSpecF`-tuple of a mixed descriptor: deep coordinates `inr i_off` become
the MOVING descriptor `sufIdx (mS-1-i_off)` (whose suffix offset rides at fixed distance from the end). -/
def deepShapeF {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (mS : ℕ) : Fin k → RegionSpecF B :=
  fun i => match ds i with
    | .inl r => r
    | .inr (.inl i_off) => .sufIdx (mS - 1 - i_off)
    | .inr (.inr i_off) => .prefIdx (mS - 1 - i_off)

/-- The cell tuple of the moving deep shape coincides with the mixed-descriptor positions
`mixedTupleF` (so the deep gate can be stated on `mixedTupleF` and `markSegD_eq_rel` applied via this
bridge). -/
theorem cellTupleF_deepShapeF {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (mS t n : ℕ) :
    cellTupleF (deepShapeF ds mS) mS t n = mixedTupleF ds mS t n := by
  funext i
  simp only [cellTupleF, mixedTupleF, deepShapeF, mixedPosAt]
  rcases ds i with r | (i_off | i_off)
  · rfl
  · simp only [RegionSpecF.posAt]
  · simp only [RegionSpecF.posAt]

/-- mS-free bound for a mixed-descriptor coordinate: shallow `sufIdx l ↦ l+2`, `prefIdx q ↦ q+2`,
deep `inr i_off ↦ i_off+2`, `core ↦ 0`.  Its `Finset.univ.sup` `bd` bounds the front (shallow) block,
the end (deep) block, and the stretch-validity threshold simultaneously. -/
def mixBoundF {B : ℕ} : RegionSpecF B ⊕ (ℕ ⊕ ℕ) → ℕ
  | .inl (.sufIdx l) => l + 2
  | .inl (.prefIdx q) => q + 2
  | .inl (.core _) => 0
  | .inr (.inl i_off) => i_off + 2
  | .inr (.inr i_off) => i_off + 2

/-- The mS-free FRONT-block mark pattern of a mixed descriptor: shallow `sufIdx l ↦ l`, everything else
↦ `bd` (outside the front window `[0, bd)`). -/
def deepFrontPat {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (bd : ℕ) : Fin k → ℕ :=
  fun i => match ds i with | .inl (.sufIdx l) => l | _ => bd

/-- The mS-free END-block mark pattern of a mixed descriptor: deep-SUFFIX `inr (.inl i_off) ↦ bd - i_off`
(its position relative to the `D`-suffix end block), everything else (incl. deep-PREFIX) ↦ `bd` (outside
the `D`-suffix end window). -/
def deepEndPat {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (bd : ℕ) : Fin k → ℕ :=
  fun i => match ds i with | .inr (.inl i_off) => bd - i_off | _ => bd

/-- The mS-free FRONT-block mark pattern of the `U`-prefix: shallow `prefIdx q ↦ q`, everything else ↦
`bd` (outside the front window `[0, bd)`). -/
def preFrontPat {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (bd : ℕ) : Fin k → ℕ :=
  fun i => match ds i with | .inl (.prefIdx q) => q | _ => bd

/-- The mS-free END-block mark pattern of the `U`-prefix: deep-PREFIX `inr (.inr i_off) ↦ bd - i_off`
(its position relative to the `U`-prefix end block), everything else ↦ `bd` (outside the `U`-prefix end
window). -/
def deepUEndPat {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (bd : ℕ) : Fin k → ℕ :=
  fun i => match ds i with | .inr (.inr i_off) => bd - i_off | _ => bd

/-- **The DEEP `D`-suffix boundary segment has the THREE-part form** `sufBaseFront ++ growing ++
sufBaseEnd`.  For a mixed descriptor `ds` (shallow `sufIdx l` ↦ front-anchored mark `l`, deep `inr
i_off` ↦ END-anchored mark `mS-1-i_off`, core/prefIdx ↦ outside the suffix), the marked `D`-suffix
factors as a FIXED shallow-front block, a growing UNMARKED `D` stretch, and a FIXED deep-end block
(both bases mS-free).  This is the deep analogue of `cellSegD_form`; in `gateF_deepShape_EP_mS` the
front block is absorbed into the (mS-free) middle and `growing ++ sufBaseEnd` is the `hsuf` form of
`accepts_two_sided_EP_deepSuf`.  Single bound `bd` for both blocks, `cS = 2*bd+1`. -/
theorem cellSegD_deepForm {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (t0 : ℕ)
    (hdeep : ∀ i e, ds i = .inr e → 1 ≤ e.elim id id) :
    ∃ (cS : ℕ) (sufBaseFront sufBaseEnd : List (MarkedN k)), 1 ≤ cS ∧ ∀ mS, cS ≤ mS →
      markSeg k (List.replicate (mS - 1) D) (mixedTupleF ds mS t0 (t0 + B)) (mS + 2 * (t0 + B) + 1)
        = sufBaseFront
          ++ List.replicate (mS - cS) (mkLetter k D (fun _ => false))
          ++ sufBaseEnd := by
  classical
  set bd := Finset.univ.sup (fun i => mixBoundF (ds i)) with hbd
  have hb : ∀ i, mixBoundF (ds i) ≤ bd :=
    fun i => hbd ▸ Finset.le_sup (f := fun i => mixBoundF (ds i)) (Finset.mem_univ i)
  refine ⟨2 * bd + 1, markSeg k (List.replicate bd D) (deepFrontPat ds bd) 0,
    markSeg k (List.replicate bd D) (deepEndPat ds bd) 0, Nat.le_add_left 1 _, fun mS hmS => ?_⟩
  -- validity of the moving deep shape at this mS
  have hv : ∀ i, (deepShapeF ds mS i).valid mS := by
    intro i
    simp only [deepShapeF]
    cases hd : ds i with
    | inl r =>
        cases r with
        | core c => simp only [RegionSpecF.valid]
        | prefIdx q =>
            have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
            simp only [RegionSpecF.valid]; omega
        | sufIdx l =>
            have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
            simp only [RegionSpecF.valid]; omega
    | inr e =>
        cases e with
        | inl i_off =>
            have h1 : 1 ≤ i_off := hdeep i (.inl i_off) hd
            have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
            simp only [RegionSpecF.valid]; omega
        | inr i_off =>
            have h1 : 1 ≤ i_off := hdeep i (.inr i_off) hd
            have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
            simp only [RegionSpecF.valid]; omega
  rw [← cellTupleF_deepShapeF ds mS t0 (t0 + B),
      markSegD_eq_rel (deepShapeF ds mS) mS t0 (t0 + B) (by omega) hv le_rfl,
      show mS - 1 = bd + (mS - 1 - bd) by omega, List.replicate_add,
      markSeg_append, List.length_replicate, Nat.zero_add,
      markSeg_replicate_decomp_end D (fun i => relDAtF mS (deepShapeF ds mS i)) bd bd (mS - 1 - bd)
        (by omega)
        (by intro i
            cases hd : ds i with
            | inl r =>
                cases r with
                | core c => right; simp only [deepShapeF, hd, relDAtF]; omega
                | prefIdx q => right; simp only [deepShapeF, hd, relDAtF]; omega
                | sufIdx l =>
                    left
                    have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
                    simp only [deepShapeF, hd, relDAtF]; omega
            | inr e =>
                cases e with
                | inl i_off =>
                    right
                    have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
                    simp only [deepShapeF, hd, relDAtF]; omega
                | inr i_off => right; simp only [deepShapeF, hd, relDAtF]; omega),
      unmark_replicate, ← List.append_assoc]
  congr 1
  · congr 1
    · -- FRONT block: markSeg(relPos) 0 = markSeg(deepFrontPat) 0
      apply markSeg_congr_outside
      intro i
      cases hd : ds i with
      | inl r =>
          cases r with
          | core c =>
              right; simp only [deepShapeF, deepFrontPat, hd, relDAtF, List.length_replicate]
              exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
          | prefIdx q =>
              right; simp only [deepShapeF, deepFrontPat, hd, relDAtF, List.length_replicate]
              exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
          | sufIdx l =>
              left; simp only [deepShapeF, deepFrontPat, hd, relDAtF]
      | inr e =>
          cases e with
          | inl i_off =>
              right
              have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
              simp only [deepShapeF, deepFrontPat, hd, relDAtF, List.length_replicate]
              exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
          | inr i_off =>
              right; simp only [deepShapeF, deepFrontPat, hd, relDAtF, List.length_replicate]
              exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    · congr 1; omega
  · -- END block: markSeg(relPos)(off) = markSeg(deepEndPat) 0  via shift
    rw [show bd + (mS - 1 - bd - bd) = mS - 1 - bd by omega,
        ← markSeg_shift k (List.replicate bd D) (deepEndPat ds bd) (mS - 1 - bd) 0, Nat.zero_add]
    apply markSeg_congr_outside
    intro i
    cases hd : ds i with
    | inl r =>
        cases r with
        | core c =>
            right; simp only [deepShapeF, deepEndPat, hd, relDAtF, List.length_replicate]
            exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
        | prefIdx q =>
            right; simp only [deepShapeF, deepEndPat, hd, relDAtF, List.length_replicate]
            exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
        | sufIdx l =>
            right
            have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
            simp only [deepShapeF, deepEndPat, hd, relDAtF, List.length_replicate]
            exact ⟨Or.inl (by omega), Or.inr (by omega)⟩
    | inr e =>
        cases e with
        | inl i_off =>
            left
            have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
            simp only [deepShapeF, deepEndPat, hd, relDAtF]; omega
        | inr i_off =>
            right; simp only [deepShapeF, deepEndPat, hd, relDAtF, List.length_replicate]
            exact ⟨Or.inr (by omega), Or.inr (by omega)⟩

/-- **The `U`-prefix boundary segment has the THREE-part form** `preBaseFront ++ growing ++ preBaseEnd`
(deep analogue handling BOTH growing runs).  Shallow `prefIdx q` mark the FRONT block `[0, bd)`,
deep-PREFIX `inr (.inr i_off)` mark the END block `[mS-1-bd, mS-1)` (position `mS-1-i_off`), and
core/sufIdx/deep-suffix sit `≥ mS-1` (outside the `U`-prefix).  Mirrors `cellSegD_deepForm` but at
offset 0 (the `U`-prefix needs NO `markSegD_eq_rel` normalization — `mixedTupleF` already IS the relative
position).  In `gateF_deepShape_EP_mS` the mS-free `preBaseEnd` is absorbed into the middle word. -/
theorem cellSegU_deepForm {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (t0 N0 : ℕ)
    (hdeep : ∀ i e, ds i = .inr e → 1 ≤ e.elim id id) :
    ∃ (cP : ℕ) (preBaseFront preBaseEnd : List (MarkedN k)), 1 ≤ cP ∧ ∀ mS, cP ≤ mS →
      markSeg k (List.replicate (mS - 1) U) (mixedTupleF ds mS t0 N0) 0
        = preBaseFront
          ++ List.replicate (mS - cP) (mkLetter k U (fun _ => false))
          ++ preBaseEnd := by
  classical
  set bd := Finset.univ.sup (fun i => mixBoundF (ds i)) with hbd
  have hb : ∀ i, mixBoundF (ds i) ≤ bd :=
    fun i => hbd ▸ Finset.le_sup (f := fun i => mixBoundF (ds i)) (Finset.mem_univ i)
  refine ⟨2 * bd + 1, markSeg k (List.replicate bd U) (preFrontPat ds bd) 0,
    markSeg k (List.replicate bd U) (deepUEndPat ds bd) 0, Nat.le_add_left 1 _, fun mS hmS => ?_⟩
  rw [show mS - 1 = bd + (mS - 1 - bd) by omega, List.replicate_add,
      markSeg_append, List.length_replicate, Nat.zero_add,
      markSeg_replicate_decomp_end U (mixedTupleF ds mS t0 N0) bd bd (mS - 1 - bd)
        (by omega)
        (by intro i
            cases hd : ds i with
            | inl r =>
                cases r with
                | core c => right; simp only [mixedTupleF, mixedPosAt, RegionSpecF.posAt, hd]; omega
                | prefIdx q =>
                    left
                    have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
                    simp only [mixedTupleF, mixedPosAt, RegionSpecF.posAt, hd]; omega
                | sufIdx l => right; simp only [mixedTupleF, mixedPosAt, RegionSpecF.posAt, hd]; omega
            | inr e =>
                cases e with
                | inl i_off => right; simp only [mixedTupleF, mixedPosAt, hd]; omega
                | inr i_off =>
                    right
                    have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
                    have h1 : 1 ≤ i_off := hdeep i (.inr i_off) hd
                    simp only [mixedTupleF, mixedPosAt, hd]; omega),
      unmark_replicate, ← List.append_assoc]
  congr 1
  · congr 1
    · apply markSeg_congr_outside
      intro i
      cases hd : ds i with
      | inl r =>
          cases r with
          | core c =>
              right; simp only [mixedTupleF, mixedPosAt, preFrontPat, RegionSpecF.posAt, hd,
                List.length_replicate]
              exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
          | prefIdx q => left; simp only [mixedTupleF, mixedPosAt, preFrontPat, RegionSpecF.posAt, hd]
          | sufIdx l =>
              right; simp only [mixedTupleF, mixedPosAt, preFrontPat, RegionSpecF.posAt, hd,
                List.length_replicate]
              exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
      | inr e =>
          cases e with
          | inl i_off =>
              right; simp only [mixedTupleF, mixedPosAt, preFrontPat, hd, List.length_replicate]
              exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
          | inr i_off =>
              right
              have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
              have h1 : 1 ≤ i_off := hdeep i (.inr i_off) hd
              simp only [mixedTupleF, mixedPosAt, preFrontPat, hd, List.length_replicate]
              exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    · congr 1; omega
  · rw [show bd + (mS - 1 - bd - bd) = mS - 1 - bd by omega,
        ← markSeg_shift k (List.replicate bd U) (deepUEndPat ds bd) (mS - 1 - bd) 0, Nat.zero_add]
    apply markSeg_congr_outside
    intro i
    cases hd : ds i with
    | inl r =>
        cases r with
        | core c =>
            right; simp only [mixedTupleF, mixedPosAt, deepUEndPat, RegionSpecF.posAt, hd,
              List.length_replicate]
            exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
        | prefIdx q =>
            right
            have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
            simp only [mixedTupleF, mixedPosAt, deepUEndPat, RegionSpecF.posAt, hd,
              List.length_replicate]
            exact ⟨Or.inl (by omega), Or.inr (by omega)⟩
        | sufIdx l =>
            right; simp only [mixedTupleF, mixedPosAt, deepUEndPat, RegionSpecF.posAt, hd,
              List.length_replicate]
            exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    | inr e =>
        cases e with
        | inl i_off =>
            right; simp only [mixedTupleF, mixedPosAt, deepUEndPat, hd, List.length_replicate]
            exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
        | inr i_off =>
            left
            have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
            have h1 : 1 ≤ i_off := hdeep i (.inr i_off) hd
            simp only [mixedTupleF, mixedPosAt, deepUEndPat, hd]; omega

/-- The mS-FREE core skeleton of a mixed descriptor: deep coordinates `inr` are sent to a junk
non-core descriptor (`sufIdx 0`), the `inl` ones pass through.  Used as the mS-free reference for the
deep gate's middle word (which reads only core coordinates). -/
def coreOnly {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) : Fin k → RegionSpecF B :=
  fun i => match ds i with | .inl r => r | .inr _ => .sufIdx 0

/-- The core SET of the moving deep shape is mS-INVARIANT — it equals the core set of `coreOnly ds`
(deep coords are non-core for both).  Note this is NOT defeq (the `DecidablePred` instances differ),
so it is a genuine `Finset.filter_congr`. -/
theorem coreSet_deepShapeF_eq {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (mS : ℕ) :
    coreSet (deepShapeF ds mS) = coreSet (coreOnly ds) := by
  unfold coreSet; apply Finset.filter_congr; intro i _
  simp only [deepShapeF, coreOnly, RegionSpecF.isCore]; rcases ds i with r | (i_off | i_off) <;> rfl

/-- On a CORE coordinate the moving deep shape coincides with its mS-free skeleton `coreOnly ds`
(both are the `inl` descriptor; `inr` coords are excluded since they are non-core).  Supplies the
descriptor agreement needed to transport the deep gate's middle word onto `coreOnly ds`. -/
theorem deepShapeF_funeq {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (mS : ℕ) (i : Fin k)
    (h : RegionSpecF.isCore (deepShapeF ds mS i) = true) : deepShapeF ds mS i = coreOnly ds i := by
  simp only [deepShapeF, coreOnly] at h ⊢
  cases hd : ds i with
  | inl r => rfl
  | inr e => rw [hd] at h; cases e <;> simp [RegionSpecF.isCore] at h

/-- `coreEmb` lands inside the core set. -/
theorem coreEmb_mem {B k : ℕ} (rs : Fin k → RegionSpecF B) (i' : Fin (coreSet rs).card) :
    coreEmb rs i' ∈ coreSet rs := ((coreSet rs).orderIsoOfFin rfl i').2

/-- A coordinate missed by every `coreEmb` index is not in the core set (`coreEmb` is onto it). -/
theorem not_mem_coreSet_of_not_range {B k : ℕ} (rs : Fin k → RegionSpecF B) (i : Fin k)
    (h : ∀ i', coreEmb rs i' ≠ i) : i ∉ coreSet rs := by
  intro hi
  obtain ⟨i', hi'⟩ := ((coreSet rs).orderIsoOfFin rfl).surjective ⟨i, hi⟩
  exact h i' (by show ((coreSet rs).orderIsoOfFin rfl i').val = i; rw [hi'])

/-- **The deep gate's MIDDLE word is mS-free** — it equals the `coreOnly ds` version.  Proved WITHOUT
the dependent `Fin.cast` transport: `map_mapBits_markSeg` rewrites BOTH `(markAtN … (coreSpec rs)).map
(mapBits (coreEmb rs))` to `markSeg k (wrappedFlat n) ī 0` for the SAME `k`-vector `ī` (core coords get
their wrapped position, non-core coords are parked at `|wrappedFlat n|`, outside the window).  The two
descriptors agree on core coords (`deepShapeF_funeq`) and have equal core sets (`coreSet_deepShapeF_eq`),
so the common `ī` serves both. -/
theorem midWord_deepShapeF_eq {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (t0 n mS : ℕ) :
    (markAtN (coreSet (deepShapeF ds mS)).card (wrappedFlat n)
        (cellTuple (coreSpec (deepShapeF ds mS)) t0 n)).map (mapBits (coreEmb (deepShapeF ds mS)))
      = (markAtN (coreSet (coreOnly ds)).card (wrappedFlat n)
        (cellTuple (coreSpec (coreOnly ds)) t0 n)).map (mapBits (coreEmb (coreOnly ds))) := by
  have hcs := coreSet_deepShapeF_eq ds mS
  set ī : Fin k → ℕ := fun i => if RegionSpecF.isCore (deepShapeF ds mS i) = true
    then (RegionSpecF.coreOf (deepShapeF ds mS i)).posAt t0 n else (wrappedFlat n).length with hīdef
  have hrA : ∀ i', ī (coreEmb (deepShapeF ds mS) i')
      = cellTuple (coreSpec (deepShapeF ds mS)) t0 n i' := by
    intro i'
    have hic : RegionSpecF.isCore (deepShapeF ds mS (coreEmb (deepShapeF ds mS) i')) = true :=
      (Finset.mem_filter.mp (coreEmb_mem (deepShapeF ds mS) i')).2
    show (if RegionSpecF.isCore (deepShapeF ds mS (coreEmb (deepShapeF ds mS) i')) = true
        then _ else _) = _
    rw [if_pos hic]; rfl
  have houtA : ∀ i, (∀ i', coreEmb (deepShapeF ds mS) i' ≠ i) →
      (ī i < 0 ∨ 0 + (wrappedFlat n).length ≤ ī i) := by
    intro i hi
    refine Or.inr ?_
    show 0 + (wrappedFlat n).length ≤ ī i
    have hnc : RegionSpecF.isCore (deepShapeF ds mS i) ≠ true := fun hc =>
      not_mem_coreSet_of_not_range (deepShapeF ds mS) i hi
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)
    show 0 + (wrappedFlat n).length ≤
      (if RegionSpecF.isCore (deepShapeF ds mS i) = true then _ else (wrappedFlat n).length)
    rw [if_neg hnc]; omega
  have hrB : ∀ i', ī (coreEmb (coreOnly ds) i')
      = cellTuple (coreSpec (coreOnly ds)) t0 n i' := by
    intro i'
    have hmemA : coreEmb (coreOnly ds) i' ∈ coreSet (deepShapeF ds mS) :=
      (Finset.ext_iff.mp hcs (coreEmb (coreOnly ds) i')).mpr (coreEmb_mem (coreOnly ds) i')
    have hic : RegionSpecF.isCore (deepShapeF ds mS (coreEmb (coreOnly ds) i')) = true :=
      (Finset.mem_filter.mp hmemA).2
    show (if RegionSpecF.isCore (deepShapeF ds mS (coreEmb (coreOnly ds) i')) = true
        then _ else _) = _
    rw [if_pos hic, deepShapeF_funeq ds mS (coreEmb (coreOnly ds) i') hic]; rfl
  have houtB : ∀ i, (∀ i', coreEmb (coreOnly ds) i' ≠ i) →
      (ī i < 0 ∨ 0 + (wrappedFlat n).length ≤ ī i) := by
    intro i hi
    refine Or.inr ?_
    show 0 + (wrappedFlat n).length ≤ ī i
    have hnotA : i ∉ coreSet (deepShapeF ds mS) := fun hh =>
      not_mem_coreSet_of_not_range (coreOnly ds) i hi ((Finset.ext_iff.mp hcs i).mp hh)
    have hnc : RegionSpecF.isCore (deepShapeF ds mS i) ≠ true := fun hc =>
      hnotA (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)
    show 0 + (wrappedFlat n).length ≤
      (if RegionSpecF.isCore (deepShapeF ds mS i) = true then _ else (wrappedFlat n).length)
    rw [if_neg hnc]; omega
  rw [markAtN_eq_markSeg, markAtN_eq_markSeg,
    map_mapBits_markSeg (coreEmb (deepShapeF ds mS)) (wrappedFlat n)
      (cellTuple (coreSpec (deepShapeF ds mS)) t0 n) ī hrA 0 houtA,
    map_mapBits_markSeg (coreEmb (coreOnly ds)) (wrappedFlat n)
      (cellTuple (coreSpec (coreOnly ds)) t0 n) ī hrB 0 houtB]

/-- Stretch validity of the moving deep shape holds for all large `mS` (the `cell_valid_ge` analogue
for `deepShapeF`: deep `inr i_off` gives `sufIdx (mS-1-i_off)`, valid once `i_off ≥ 1` and `mS ≥ 2`). -/
theorem deepShape_valid_ge {B k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ))
    (hdeep : ∀ i e, ds i = .inr e → 1 ≤ e.elim id id) :
    ∃ vth, ∀ mS, vth ≤ mS → ∀ i, (deepShapeF ds mS i).valid mS := by
  classical
  set bd := Finset.univ.sup (fun i => mixBoundF (ds i)) with hbd
  have hb : ∀ i, mixBoundF (ds i) ≤ bd :=
    fun i => hbd ▸ Finset.le_sup (f := fun i => mixBoundF (ds i)) (Finset.mem_univ i)
  refine ⟨bd + 2, fun mS hmS i => ?_⟩
  simp only [deepShapeF]
  cases hd : ds i with
  | inl r =>
      cases r with
      | core c => simp only [RegionSpecF.valid]
      | prefIdx q =>
          have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
          simp only [RegionSpecF.valid]; omega
      | sufIdx l =>
          have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
          simp only [RegionSpecF.valid]; omega
  | inr e =>
      cases e with
      | inl i_off =>
          have h1 : 1 ≤ i_off := hdeep i (.inl i_off) hd
          have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
          simp only [RegionSpecF.valid]; omega
      | inr i_off =>
          have h1 : 1 ≤ i_off := hdeep i (.inr i_off) hd
          have hbi := hb i; rw [hd] at hbi; simp only [mixBoundF] at hbi
          simp only [RegionSpecF.valid]; omega

/-- **The DEEP-shape gate is eventually periodic in `mS`** — the d3.2a CAPSTONE.  Mirrors
`gateF_EP_mS` but for the MOVING descriptor `deepShapeF ds mS` (deep coords `inr i_off ↦ sufIdx
(mS-1-i_off)`, end-anchored).  Uses `accepts_two_sided_EP_deepSuf` (the suffix's fixed marks are at the
END): the U-prefix via `cellSegU_deepForm`, the D-suffix three-part split via `cellSegD_deepForm` (its
shallow-front block absorbed into the mS-free middle, the deep-end block as `sufBaseEnd`), the middle
word made mS-free by `midWord_deepShapeF_eq`, and `gateF_reduced` applied POINTWISE at `deepShapeF ds
mS` (whose `coreSet`/`coreSpec`/`coreEmb` are mS-free since deep coords are non-core). -/
theorem gateF_deepShape_EP_mS {B k : ℕ} (M : SliceMSO.DetAuto (MarkedN k))
    (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (t0 n : ℕ) (hwin : t0 + B ≤ n)
    (hdeep : ∀ i e, ds i = .inr e → 1 ≤ e.elim id id) :
    ∃ q, 1 ≤ q ∧ SliceOrder.EventuallyPeriodic
      (fun mS => gateF M (deepShapeF ds mS) mS t0 n) q := by
  obtain ⟨cP, preBaseFront, preBaseEnd, _hcP, hpreU⟩ := cellSegU_deepForm ds t0 (t0 + B) hdeep
  obtain ⟨cS, sufBaseFront, sufBaseEnd, _hcS, hsufD⟩ := cellSegD_deepForm ds t0 hdeep
  obtain ⟨vth, hvth⟩ := deepShape_valid_ge ds hdeep
  obtain ⟨q, hq, hQEP⟩ := accepts_two_sided_EP_deepSuf M
    (fun mS => preBaseFront ++ List.replicate (mS - cP) (mkLetter k U (fun _ => false)))
    (fun mS => List.replicate (mS - cS) (mkLetter k D (fun _ => false)) ++ sufBaseEnd)
    (preBaseEnd ++ (markAtN (coreSet (coreOnly ds)).card (wrappedFlat n)
        (cellTuple (coreSpec (coreOnly ds)) t0 n)).map (mapBits (coreEmb (coreOnly ds)))
      ++ sufBaseFront)
    preBaseFront sufBaseEnd (mkLetter k U (fun _ => false)) (mkLetter k D (fun _ => false)) cP cS
    (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨q, hq, eventuallyPeriodic_congr_eventually
    (max 1 (max vth (max cP cS))) (fun mS hmS => ?_) hQEP⟩
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

/-- **Vector form of the mixed-deep cell rank**: ALL `Fin P.d` coordinates are affine-on-residues in
`mS` at a COMMON period (the product of the per-coordinate periods from `rank_cell_mixedDeep_affine_mS`).
This is the candidate-value form `gated_lexMin_affine_at` consumes (`haff : ∀ i, AffineOnResiduesAtZ p …`
at a single `p`).  d3.2b building block. -/
theorem rank_cell_mixedDeep_vec {B : ℕ} (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (ds : Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (t n : ℕ)
    (hB : 1 ≤ B) (htBn : t + B ≤ n) (hdeep : ∀ j e, ds j = .inr e → 1 ≤ e.elim id id) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ i, AffineOnResiduesAtZ p
      (fun mS => P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n) i) := by
  classical
  choose pf hpf haf using fun i => rank_cell_mixedDeep_affine_mS P c ds t n i hB htBn hdeep
  have hppos : 0 < Finset.univ.prod pf := Finset.prod_pos (fun i _ => hpf i)
  exact ⟨Finset.univ.prod pf, hppos, fun i =>
    (haf i).of_dvd (hpf i) (Finset.dvd_prod_of_mem pf (Finset.mem_univ i)) hppos⟩

/-- **A bounded deep-shape candidate is gate-EP and value-affine at a COMMON period** in `mS`.  Packages
the deep gate `gateF_deepShape_EP_mS` (handles ANY mixed shape — fixed `inl` coords plus end-anchored
deep `inr` coords) with the cell-rank vector `rank_cell_mixedDeep_vec`, aligned to the product period.
This is the per-candidate input `gated_lexMin_affine_at` requires (`hgate` + `haff` at one `p`); the
`selB` candidate list (d3.2b) is finitely many of these. -/
theorem deepShape_candidate_EP_affine {B : ℕ} (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (ds : Fin (P.toPoly.arity c) → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (t n : ℕ)
    (hB : 1 ≤ B) (hwin : t + B ≤ n) (hdeep : ∀ j e, ds j = .inr e → 1 ≤ e.elim id id) :
    ∃ p : ℕ, 1 ≤ p
      ∧ SliceOrder.EventuallyPeriodic (fun mS => gateF M (deepShapeF ds mS) mS t n) p
      ∧ ∀ i, AffineOnResiduesAtZ p
          (fun mS => P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n) i) := by
  obtain ⟨q, hq, hgate⟩ := gateF_deepShape_EP_mS M ds t n hwin hdeep
  obtain ⟨p, hp, haff⟩ := rank_cell_mixedDeep_vec P c ds t n hB hwin hdeep
  exact ⟨q * p, Nat.mul_pos hq hp, SliceDstar.EP_of_dvd hgate (dvd_mul_right q p),
    fun i => (haff i).of_dvd hp (dvd_mul_left p q) (Nat.mul_pos hq hp)⟩

/-- **Common period for a finite candidate list.**  If every candidate is gate-EP and value-affine at
its OWN period, then they are all gate-EP and value-affine at a SINGLE common period (the product over
the list).  List induction aligning periods via `EP_of_dvd` / `AffineOnResiduesAtZ.of_dvd`. -/
theorem cands_common_period {d : ℕ} (cands : List ((ℕ → Prop) × (ℕ → Fin d → ℤ)))
    (hcand : ∀ gf ∈ cands, ∃ p, 1 ≤ p ∧ SliceOrder.EventuallyPeriodic gf.1 p
      ∧ ∀ i, AffineOnResiduesAtZ p (fun mS => gf.2 mS i)) :
    ∃ P, 1 ≤ P ∧ ∀ gf ∈ cands, SliceOrder.EventuallyPeriodic gf.1 P
      ∧ ∀ i, AffineOnResiduesAtZ P (fun mS => gf.2 mS i) := by
  induction cands with
  | nil => exact ⟨1, le_refl 1, fun gf h => by simp at h⟩
  | cons gf rest ih =>
    obtain ⟨p, hp, hep, haf⟩ := hcand gf (List.mem_cons_self)
    obtain ⟨P, hP, hrest⟩ := ih (fun g hg => hcand g (List.mem_cons_of_mem gf hg))
    refine ⟨p * P, Nat.mul_pos hp hP, fun g hg => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨SliceDstar.EP_of_dvd hep (dvd_mul_right p P),
        fun i => (haf i).of_dvd hp (dvd_mul_right p P) (Nat.mul_pos hp hP)⟩
    · obtain ⟨hep', haf'⟩ := hrest g hg
      exact ⟨SliceDstar.EP_of_dvd hep' (dvd_mul_left P p),
        fun i => (haf' i).of_dvd hP (dvd_mul_left P p) (Nat.mul_pos hp hP)⟩

open scoped Classical in
/-- **Per-candidate-period gated lexMin is affine-on-residues.**  The version of `gated_lexMin_affine_at`
that does NOT require a common period upfront: it unifies the per-candidate periods (`cands_common_period`)
and `BIG`'s period to one product period, then applies `gated_lexMin_affine_at`.  This is the d3.2b
consumer for the bounded `selB` candidate list (each candidate via `deepShape_candidate_EP_affine`). -/
theorem gated_lexMin_affine_perCand {d : ℕ} (cands : List ((ℕ → Prop) × (ℕ → Fin d → ℤ)))
    (hcand : ∀ gf ∈ cands, ∃ p, 1 ≤ p ∧ SliceOrder.EventuallyPeriodic gf.1 p
      ∧ ∀ i, AffineOnResiduesAtZ p (fun mS => gf.2 mS i))
    (BIG : ℕ → Fin d → ℤ) (pB : ℕ) (hpB : 1 ≤ pB)
    (hBIG : ∀ i, AffineOnResiduesAtZ pB (fun mS => BIG mS i)) :
    ∃ p, 1 ≤ p ∧ ∀ i, AffineOnResiduesAtZ p
      (fun mS => lexMinList
        (BIG :: cands.map (fun gf => fun n => if gf.1 n then gf.2 n else BIG n)) mS i) := by
  obtain ⟨P, hP, hPcand⟩ := cands_common_period cands hcand
  refine ⟨P * pB, Nat.mul_pos hP hpB, fun i => gated_lexMin_affine_at (Nat.mul_pos hP hpB) cands
    (fun gf hg => SliceDstar.EP_of_dvd (hPcand gf hg).1 (dvd_mul_right P pB))
    (fun gf hg j => ((hPcand gf hg).2 j).of_dvd hP (dvd_mul_right P pB) (Nat.mul_pos hP hpB))
    BIG (fun j => (hBIG j).of_dvd hpB (dvd_mul_left pB P) (Nat.mul_pos hP hpB)) i⟩

/-! ## d3.2b-enum: the bounded mS-free shape enumeration -/

/-- **The bounded mS-free shape enumeration** for one coordinate (d3.2b-enum): the finite set of
candidate `RegionSpecF B ⊕ (ℕ ⊕ ℕ)` descriptors — `inl (core r)` for any wrapped-flat region, `inl (prefIdx q)`
for `q < q_U`, `inl (sufIdx l)` for the SHALLOW suffix depths `l < q_D`, and `inr i_off` for the DEEP
suffix depths `1 ≤ i_off ≤ q_D` (encoding `sufIdx (mS-1-i_off)`).  The l-monotonicity (d3.3) collapses all
other suffix depths to these boundaries; `q_U`/`q_D` are the U-prefix / D-suffix automaton cycle lengths. -/
def coordCands (B q_U q_D : ℕ) : Finset (RegionSpecF B ⊕ (ℕ ⊕ ℕ)) :=
  (Finset.univ.image (fun r : RegionSpec B => Sum.inl (RegionSpecF.core r)))
  ∪ ((Finset.range q_U).image (fun q => Sum.inl (RegionSpecF.prefIdx q)))
  ∪ ((Finset.range q_D).image (fun l => Sum.inl (RegionSpecF.sufIdx l)))
  ∪ ((Finset.Icc 1 q_D).image (fun i_off => Sum.inr (Sum.inl i_off)))
  ∪ ((Finset.Icc 1 q_U).image (fun i_off => Sum.inr (Sum.inr i_off)))

/-- Membership characterization of `coordCands`. -/
theorem mem_coordCands {B q_U q_D : ℕ} (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) :
    x ∈ coordCands B q_U q_D ↔
      (∃ r : RegionSpec B, x = Sum.inl (RegionSpecF.core r))
      ∨ (∃ q, q < q_U ∧ x = Sum.inl (RegionSpecF.prefIdx q))
      ∨ (∃ l, l < q_D ∧ x = Sum.inl (RegionSpecF.sufIdx l))
      ∨ (∃ i_off, 1 ≤ i_off ∧ i_off ≤ q_D ∧ x = Sum.inr (Sum.inl i_off))
      ∨ (∃ i_off, 1 ≤ i_off ∧ i_off ≤ q_U ∧ x = Sum.inr (Sum.inr i_off)) := by
  simp only [coordCands, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ((((⟨r, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨l, hl, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
    · exact Or.inl ⟨r, rfl⟩
    · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨l, hl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi.1, hi.2, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi.1, hi.2, rfl⟩)))
  · rintro (⟨r, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨l, hl, rfl⟩ | ⟨i, hi1, hi2, rfl⟩ | ⟨i, hi1, hi2, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨r, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨l, hl, rfl⟩))
    · exact Or.inl (Or.inr ⟨i, ⟨hi1, hi2⟩, rfl⟩)
    · exact Or.inr ⟨i, ⟨hi1, hi2⟩, rfl⟩

/-- For a tuple whose every coordinate lies in `coordCands`, the deep (`inr`) coordinates carry a
positive offset — exactly the `hdeep` hypothesis of `deepShape_candidate_EP_affine`. -/
theorem coordCands_hdeep {B q_U q_D k : ℕ} {ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)}
    (hds : ∀ j, ds j ∈ coordCands B q_U q_D) :
    ∀ j e, ds j = Sum.inr e → 1 ≤ e.elim id id := by
  intro j e hj
  rcases (mem_coordCands (ds j)).mp (hds j) with
    ⟨r, hr⟩ | ⟨q, _, hq⟩ | ⟨l, _, hl⟩ | ⟨i, hi1, _, hi⟩ | ⟨i, hi1, _, hi⟩
  · rw [hj] at hr; simp at hr
  · rw [hj] at hq; simp at hq
  · rw [hj] at hl; simp at hl
  · rw [hj] at hi; simp only [Sum.inr.injEq] at hi; subst hi; simpa using hi1
  · rw [hj] at hi; simp only [Sum.inr.injEq] at hi; subst hi; simpa using hi1

/-- The mS-FREE bounded shape-TUPLE enumeration (d3.2b-enum): all coordinate-tuples whose every
coordinate lies in `coordCands`.  Mirrors `regionTuplesF` but is INDEPENDENT of mS (the deep coords
are `inr i_off`; the moving descriptor `sufIdx (mS-1-i_off)` is recovered inside `deepShapeF`). -/
def mixedTuplesF (B q_U q_D k : ℕ) : Finset (Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) :=
  Fintype.piFinset (fun _ => coordCands B q_U q_D)

/-- Membership of `mixedTuplesF`: a tuple lies in it exactly when every coordinate is in `coordCands`. -/
theorem mem_mixedTuplesF {B q_U q_D k : ℕ} (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ)) :
    ds ∈ mixedTuplesF B q_U q_D k ↔ ∀ j, ds j ∈ coordCands B q_U q_D := by
  simp [mixedTuplesF, Fintype.mem_piFinset]

/-- **The bounded `selB` candidate list** (d3.2b-enum): one candidate per `(c, base t ∈ [B, n-B], shape
`ds ∈ mixedTuplesF`)`, with gate `gateF (Mc c) (deepShapeF ds)` and value the mixed-deep cell rank.  The
input to `gated_lexMin_affine_perCand` (each candidate gate-EP + value-affine via `selCands_hcand`); the
gated lexMin of this list is `selB`, the bounded effective-set minimiser the d3.4 bridge collapses onto. -/
noncomputable def selCands (B q_U q_D : ℕ) (P : WRP.Presentation Step Step)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (n : ℕ) :
    List ((ℕ → Prop) × (ℕ → Fin P.d → ℤ)) :=
  (List.finRange P.toPoly.K).flatMap (fun c =>
    (Finset.Icc B (n - B)).toList.flatMap (fun t =>
      (mixedTuplesF B q_U q_D (P.toPoly.arity c)).toList.map (fun ds =>
        (fun mS => gateF (Mc c) (deepShapeF ds mS) mS t n,
         fun mS => fun i => P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n) i))))

/-- **Every `selCands` candidate is gate-EP and value-affine** at its own period (d3.2b-enum): unfolds the
`(c, t, ds)` enumeration and discharges each via `deepShape_candidate_EP_affine` (the bulk window `t+B ≤ n`
from `t ∈ [B, n-B]`, the `hdeep` from `coordCands_hdeep`).  This is the `hcand` hypothesis of
`gated_lexMin_affine_perCand`, so `selB := lexMinList (BIG :: selCands.map gating)` is affine-on-residues. -/
theorem selCands_hcand {B : ℕ} (P : WRP.Presentation Step Step) (hB : 1 ≤ B)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (q_U q_D n : ℕ) :
    ∀ gf ∈ selCands B q_U q_D P Mc n, ∃ p, 1 ≤ p
      ∧ SliceOrder.EventuallyPeriodic gf.1 p
      ∧ ∀ i, AffineOnResiduesAtZ p (fun mS => gf.2 mS i) := by
  intro gf hgf
  simp only [selCands, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hgf
  obtain ⟨c, _, t, htmem, ds, hdsmem, rfl⟩ := hgf
  have hmem : ∀ j, ds j ∈ coordCands B q_U q_D := (mem_mixedTuplesF ds).mp hdsmem
  have hwin : t + B ≤ n := by rw [Finset.mem_Icc] at htmem; omega
  exact deepShape_candidate_EP_affine P c (Mc c) ds t n hB hwin (coordCands_hdeep hmem)

/-- **The explicit `selCands` dominator**: the list-max of the candidate values at coordinate `0`, plus
one, on coordinate `0`; zero elsewhere.  Lex-dominates every `selCands` value (`selCands_lt_bigDom`). -/
noncomputable def bigDom (B q_U q_D : ℕ) (P : WRP.Presentation Step Step)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (n : ℕ)
    (hd : 0 < P.d) : ℕ → Fin P.d → ℤ :=
  fun mS coord => if coord = ⟨0, hd⟩
    then ((selCands B q_U q_D P Mc n).map (fun gf => gf.2 mS ⟨0, hd⟩)).foldr max 0 + 1 else 0

open scoped Classical in
/-- **The bounded effective-set minimiser `selB`** = the gated lexMin over `selCands` (with `bigDom`
dominator).  The d3.4 bridge collapses the full growing pool `Cands` onto this `selB`, and `selB` equals
`dstarRankGA_m`.  Affine-on-residues by `selB_affine`. -/
noncomputable def selB (B q_U q_D : ℕ) (P : WRP.Presentation Step Step)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (n : ℕ)
    (hd : 0 < P.d) : ℕ → Fin P.d → ℤ :=
  fun mS => lexMinList (bigDom B q_U q_D P Mc n hd :: (selCands B q_U q_D P Mc n).map
    (fun gf => fun mS => if gf.1 mS then gf.2 mS else bigDom B q_U q_D P Mc n hd mS)) mS

open scoped Classical in
/-- **The bounded `selB` is affine-on-residues in `mS`** (d3.2b-enum — the bridge's `hsel_aff` leg).
`bigDom`'s affineness is the `affineOnResiduesAtZ_listMax` of the candidate values at the common period
from `cands_common_period`; fed with `selCands` + `selCands_hcand` to `gated_lexMin_affine_perCand`. -/
theorem selB_affine {B : ℕ} (P : WRP.Presentation Step Step) (hB : 1 ≤ B)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (q_U q_D n : ℕ) (hd : 0 < P.d) :
    ∃ p, 1 ≤ p ∧ ∀ i, AffineOnResiduesAtZ p (fun mS => selB B q_U q_D P Mc n hd mS i) := by
  obtain ⟨Pp, hPp, hPcand⟩ := cands_common_period (selCands B q_U q_D P Mc n)
    (selCands_hcand P hB Mc q_U q_D n)
  have hBIGaff : ∀ i, AffineOnResiduesAtZ Pp (fun mS => bigDom B q_U q_D P Mc n hd mS i) := by
    intro i
    by_cases hi : i = ⟨0, hd⟩
    · have heq : (fun mS => bigDom B q_U q_D P Mc n hd mS i)
          = (fun mS => (((selCands B q_U q_D P Mc n).map (fun gf => fun mS => gf.2 mS ⟨0, hd⟩)).map
              (fun f => f mS)).foldr max 0 + 1) := by
        funext mS
        simp only [bigDom, hi, ↓reduceIte, List.map_map, Function.comp_def]
      rw [heq]
      exact (affineOnResiduesAtZ_listMax hPp
        ((selCands B q_U q_D P Mc n).map (fun gf => fun mS => gf.2 mS ⟨0, hd⟩))
        (fun f hf => by
          rw [List.mem_map] at hf
          obtain ⟨gf, hgf, rfl⟩ := hf
          exact (hPcand gf hgf).2 ⟨0, hd⟩)).add hPp (AffineOnResiduesAtZ.const Pp 1)
    · have heq : (fun mS => bigDom B q_U q_D P Mc n hd mS i) = (fun _ => (0 : ℤ)) := by
        funext mS; simp only [bigDom, if_neg hi]
      rw [heq]; exact AffineOnResiduesAtZ.const Pp 0
  exact gated_lexMin_affine_perCand (selCands B q_U q_D P Mc n)
    (selCands_hcand P hB Mc q_U q_D n) (bigDom B q_U q_D P Mc n hd) Pp hPp hBIGaff

/-- **`bigDom` lex-dominates every `selCands` value** (the dominator leg, mirroring the n-direction
`hdom`): at coordinate `0`, every candidate value is `≤` the list-max `< bigDom`. -/
theorem selCands_lt_bigDom (B q_U q_D : ℕ) (P : WRP.Presentation Step Step)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (n : ℕ)
    (hd : 0 < P.d) :
    ∀ gf ∈ selCands B q_U q_D P Mc n, ∀ mS,
      WRP.lexLt (gf.2 mS) (bigDom B q_U q_D P Mc n hd mS) := by
  intro gf hgf mS
  refine ⟨⟨0, hd⟩, fun j hj => absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _), ?_⟩
  simp only [bigDom, ↓reduceIte]
  have hmem : gf.2 mS ⟨0, hd⟩ ∈ (selCands B q_U q_D P Mc n).map (fun gf' => gf'.2 mS ⟨0, hd⟩) :=
    List.mem_map.mpr ⟨gf, hgf, rfl⟩
  have := SliceDstarBridge.le_foldr_max hmem
  omega

open scoped Classical in
/-- **`selB` is below every gated-ON `selCands` value** (a collapse ingredient for `hsel_le`/`hsel_on`):
since `selB mS` is the lexMin of `bigDom :: selCands.map gating`, it is `≤` each list member; at a gated-ON
candidate the gating value reduces to the candidate's own value `gf.2 mS`. -/
theorem selB_le_selCands_on (B q_U q_D : ℕ) (P : WRP.Presentation Step Step)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (n : ℕ)
    (hd : 0 < P.d) (mS : ℕ) :
    ∀ gf ∈ selCands B q_U q_D P Mc n, gf.1 mS →
      ¬ WRP.lexLt (gf.2 mS) (selB B q_U q_D P Mc n hd mS) := by
  intro gf hgf hon
  obtain ⟨hmin, _⟩ := lexMinList_le (bigDom B q_U q_D P Mc n hd :: (selCands B q_U q_D P Mc n).map
    (fun gf => fun mS => if gf.1 mS then gf.2 mS else bigDom B q_U q_D P Mc n hd mS))
    (List.cons_ne_nil _ _) mS
  have hmem : (fun mS => if gf.1 mS then gf.2 mS else bigDom B q_U q_D P Mc n hd mS)
      ∈ (bigDom B q_U q_D P Mc n hd :: (selCands B q_U q_D P Mc n).map
        (fun gf => fun mS => if gf.1 mS then gf.2 mS else bigDom B q_U q_D P Mc n hd mS)) :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨gf, hgf, rfl⟩)
  have hle := hmin _ hmem
  simp only [if_pos hon] at hle
  exact hle

/-- **The FULL growing candidate pool** `Cands mS` (the d3.4 bridge): one candidate per `(c, base
t ∈ [0, n], valid RegionSpecF-tuple rs)` — gate `gateF (Mc c) rs`, value the cell rank.  Unlike the
bounded `selCands`, the descriptor pool GROWS with `mS` (`regionTuplesF B _ mS` admits `prefIdx q`/
`sufIdx l` for any `q,l < mS-1`).  `gated_lexMin_affine_at_growing` collapses `lexMinList (bigDom ::
Cands mS …)` onto `selB`; `Cands_member_decomp` recovers the generating `(c, t, rs)`. -/
noncomputable def Cands (B : ℕ) (P : WRP.Presentation Step Step)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (n : ℕ) :
    ℕ → List ((ℕ → Prop) × (ℕ → Fin P.d → ℤ)) :=
  fun mS => (List.finRange P.toPoly.K).flatMap (fun c =>
    (List.range (n + 1)).flatMap (fun t =>
      ((regionTuplesF B (P.toPoly.arity c) mS).toList).map (fun rs =>
        (fun mS => gateF (Mc c) rs mS t n,
         fun mS => fun i => P.rank c (copiedSlice mS n) (cellTupleF rs mS t n) i))))

/-- **Membership destructuring for the full pool** `Cands mS` (d3.4 bridge, build-order step 3): unfolds
the `flatMap/flatMap/map` to recover the generating copy `c`, base `t ≤ n`, and valid descriptor tuple
`rs` (`mem_regionTuplesF`). -/
theorem Cands_member_decomp (B : ℕ) (P : WRP.Presentation Step Step)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (n mS : ℕ)
    (gf : (ℕ → Prop) × (ℕ → Fin P.d → ℤ)) (hgf : gf ∈ Cands B P Mc n mS) :
    ∃ (c : Fin P.toPoly.K) (t : ℕ) (rs : Fin (P.toPoly.arity c) → RegionSpecF B),
      t ≤ n ∧ (∀ i, (rs i).valid mS) ∧
      gf = (fun mS => gateF (Mc c) rs mS t n,
            fun mS => fun i => P.rank c (copiedSlice mS n) (cellTupleF rs mS t n) i) := by
  simp only [Cands, List.mem_flatMap, List.mem_map, Finset.mem_toList, List.mem_range] at hgf
  obtain ⟨c, _, t, ht, rs, hrsmem, rfl⟩ := hgf
  exact ⟨c, t, rs, by omega, (mem_regionTuplesF rs).mp hrsmem, rfl⟩

end CopiedSetupMS
