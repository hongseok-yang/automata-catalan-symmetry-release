/-
# Paper-exact statements of the negative theorems and the slice analysis

The Lean classes deliberately quantify over supersets of the paper's `def:wrp`
class (deviation A2 of `PAPER_DEVIATIONS.md`: `Valid` asks totality only of the
combined order `≺`; the Lean model also admits arity-`0` copies), and the slice
theorems use the weaker some-realised-slice hypothesis with a set-valued
conclusion (deviations A3/A4).  The negative theorems are therefore *stronger*
than the paper's — this file exports the paper's literal statements as
corollaries, so that every headline sentence of `paper.tex` has a
Lean declaration of the same shape:

* `wrp_no_area_dinv_swap_paper` (`thm:wrp-no-swap`) — no map in the revision's
  `def:wrp` class realises an area↔dinv swap (also the `χ`-total form
  `wrp_no_area_dinv_swap_tieTotal` for the previous draft's class);
* `inverse_zeta_not_wrp_paper` (`cor:inverse-zeta-not-wrp`) — general arity —
  and `inverse_zeta_not_wrp_arity1_paper` (the Büchi-only arity-1 route),
  over paper-valid presentations;
* `wrp_paper_isLogspaceMH` / `wrp_paper_logspace_polytime` /
  `wrp_strict_below_logspace_paper` (`thm:wrp-logspace`,
  `thm:wrp-strict-below-logspace`) — the logspace trio over the revision's
  class;
* `wrp_slice_profile_semilinear_total` and its paper-class form
  `wrp_slice_profile_semilinear_paper` (`thm:wrp-slice-semilinearity`) — the
  revision's literal statement: `T` **total on the family** with
  `|T(W_n)| = O(n)`, and the literal set
  `S_T = {(fas(T(W_n)), tailU(T(W_n))) : n ≥ 1}` semilinear (deviation A3);
* `wrp_slice_profile_pointwise_affine` — the pointwise reading of the slice
  analysis: on every in-domain slice the profile of `T(W_n)` *is* `g n`
  (deviation A4).

Trust bases are unchanged by these corollaries: the slice/no-swap statements
admit `SliceMSO.buchi` only; the general-arity inverse-zeta statement adds the
three route-B counting/definability axioms; the logspace statements admit
`SliceMSO.buchi` (the machine cores are axiom-clean).  The not-closed theorem
with paper-exact witnesses is in `WRPPaperNotClosed.lean`.
-/
import RequestProject.WRPTieTotal
import RequestProject.NoSwapWRP
import RequestProject.CopiedTieSemilinear2
import RequestProject.WRPLogspace

open WRP

/-! ## The slice analysis in the paper's literal form (`thm:wrp-slice-semilinearity`) -/

/-- **`thm:wrp-slice-semilinearity` with the paper's totality reading**
(paper.tex, deviation A3 closed): if `T ∈ WRP` is defined on
**every** slice `W_n` (`n ≥ 1`), with output `f n` and linear growth, then the
paper's literal set `S_T = {(fas(T(W_n)), tailU(T(W_n))) : n ≥ 1}` is
semilinear.  (The growth hypothesis keeps the Lean form over all realised
slices — interconvertible with the paper's `|T(W_n)| = O(n)`, deviation A6; at
`n = 0` it is inert by the totalisation convention C3.) -/
theorem wrp_slice_profile_semilinear_total (T : List Step → Option (List Step))
    (hT : IsWRP T) (f : ℕ → List Step)
    (hf : ∀ n, 1 ≤ n → T (wrappedFlat n) = some (f n))
    (hgrow : ∃ C, ∀ n out, T (wrappedFlat n) = some out → out.length ≤ C * (n + 1)) :
    IsSemilinear2 {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧
      q = (firstAscent (f n), tailU (f n))} := by
  have hne : ∃ n : ℕ, 1 ≤ n ∧ ∃ out, T (wrappedFlat n) = some out :=
    ⟨1, le_refl 1, f 1, hf 1 (le_refl 1)⟩
  have hsemi := wrp_slice_profile_semilinear T hT hgrow hne
  have hset : sliceProfile T = {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧
      q = (firstAscent (f n), tailU (f n))} := by
    ext q
    simp only [sliceProfile, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn, out, hout, hq⟩
      have hfo : f n = out := Option.some.inj ((hf n hn).symm.trans hout)
      exact ⟨n, hn, by rw [hq, ← hfo]⟩
    · rintro ⟨n, hn, hq⟩
      exact ⟨n, hn, f n, hf n hn, hq⟩
  rw [← hset]
  exact hsemi

/-- **`thm:wrp-slice-semilinearity` over the revision's `def:wrp` class**: the
same literal statement for `T` in the paper-exact class `IsWRPPaper`. -/
theorem wrp_slice_profile_semilinear_paper (T : List Step → Option (List Step))
    (hT : IsWRPPaper T) (f : ℕ → List Step)
    (hf : ∀ n, 1 ≤ n → T (wrappedFlat n) = some (f n))
    (hgrow : ∃ C, ∀ n out, T (wrappedFlat n) = some out → out.length ≤ C * (n + 1)) :
    IsSemilinear2 {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧
      q = (firstAscent (f n), tailU (f n))} :=
  wrp_slice_profile_semilinear_total T hT.isWRP f hf hgrow

/-- **The pointwise slice analysis** (deviation A4 closed): the profile of
`T(W_n)` on every in-domain slice `n ≥ 1` *is* `g n`, for a single function
`g` affine on residue classes beyond a threshold — the paper's pointwise
reading of Lemmas 7.2–7.4 / `thm:wrp-slice-semilinearity`. -/
theorem wrp_slice_profile_pointwise_affine (T : List Step → Option (List Step))
    (hT : IsWRP T)
    (hgrow : ∃ C, ∀ n out, T (wrappedFlat n) = some out → out.length ≤ C * (n + 1))
    (hne : ∃ n : ℕ, 1 ≤ n ∧ ∃ out, T (wrappedFlat n) = some out) :
    ∃ (g : ℕ → ℕ × ℕ) (p m : ℕ), 1 ≤ p ∧ 1 ≤ m ∧
      (∀ j, j < p → ∃ b₁ s₁ b₂ s₂ : ℕ,
        ∀ k, g (m + j + p * k) = (b₁ + k * s₁, b₂ + k * s₂)) ∧
      ∀ n, 1 ≤ n → ∀ out, T (wrappedFlat n) = some out →
        (firstAscent out, tailU out) = g n := by
  obtain ⟨g, p, m, hp, hm, haff, hpt, -⟩ := wrp_slice_profile_affine T hT hgrow hne
  exact ⟨g, p, m, hp, hm, haff, hpt⟩

/-! ## The no-swap theorem over the paper's classes (`thm:wrp-no-swap`) -/

/-- **`thm:wrp-no-swap` over the previous draft's `def:wrp` class** (tie-order
`χ` a strict total order): no `χ`-total WRP transduction realises a
semilength-preserving area↔dinv swap on Dyck paths. -/
theorem wrp_no_area_dinv_swap_tieTotal
    (T : List Step → Option (List Step)) (hWRP : IsWRPTieTotal T)
    (F : List Step → List Step)
    (hreal : Realises T {P | IsDyckPath P} F)
    (hDyck : ∀ P, IsDyckPath P → IsDyckPath (F P))
    (hlen : ∀ P, IsDyckPath P → (F P).length = P.length)
    (harea : ∀ P, IsDyckPath P → area (F P) = ↑(dinv P))
    (hdinv : ∀ P, IsDyckPath P → dinv (F P) = (area P).toNat) :
    False :=
  wrp_no_area_dinv_swap T hWRP.isWRP F hreal hDyck hlen harea hdinv

/-- **`thm:wrp-no-swap` over the revision's `def:wrp` class verbatim**
(paper.tex): no map in the paper's WRP class — tie-order a strict
total order, every arity `≥ 1` — realises a semilength-preserving area↔dinv
swap on Dyck paths.  A fortiori from the stronger `wrp_no_area_dinv_swap`
(deviation A2 closed). -/
theorem wrp_no_area_dinv_swap_paper
    (T : List Step → Option (List Step)) (hWRP : IsWRPPaper T)
    (F : List Step → List Step)
    (hreal : Realises T {P | IsDyckPath P} F)
    (hDyck : ∀ P, IsDyckPath P → IsDyckPath (F P))
    (hlen : ∀ P, IsDyckPath P → (F P).length = P.length)
    (harea : ∀ P, IsDyckPath P → area (F P) = ↑(dinv P))
    (hdinv : ∀ P, IsDyckPath P → dinv (F P) = (area P).toNat) :
    False :=
  wrp_no_area_dinv_swap T hWRP.isWRP F hreal hDyck hlen harea hdinv

/-! ## The inverse-zeta separation over the paper's classes (`cor:inverse-zeta-not-wrp`) -/

/-- **`cor:inverse-zeta-not-wrp` over the revision's `def:wrp` class**: no map
in the paper's WRP class inverts `ζ` on Dyck paths (general arity; route B). -/
theorem inverse_zeta_not_wrp_paper :
    ¬ ∃ T : List Step → Option (List Step),
      IsWRPPaper T ∧ ∀ P, IsDyckPath P → T (zetaMap P) = some P := by
  rintro ⟨T, hT, hinv⟩
  exact CopiedTieSemilinear2.inverse_zeta_not_wrp ⟨T, hT.isWRP, hinv⟩

/-- **The arity-1 inverse-zeta capstone over paper-valid presentations**
(Büchi-only route): no arity-1 presentation whose tie-order is a strict total
order realises an inverse of `ζ` on Dyck paths.  A fortiori from
`CopiedD4.inverse_zeta_not_wrp_arity1` via `valid_of_polyValid`. -/
theorem inverse_zeta_not_wrp_arity1_paper :
    ¬ ∃ (P : WRP.Presentation Step Step) (T : List Step → Option (List Step)),
      P.toPoly.Valid ∧ (∀ c, P.toPoly.arity c = 1) ∧
      (∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)) ∧
      (∀ Q, IsDyckPath Q → T (zetaMap Q) = some Q) := by
  rintro ⟨P, T, hV, h1, hPT, hinv⟩
  exact CopiedD4.inverse_zeta_not_wrp_arity1
    ⟨P, T, P.valid_of_polyValid hV, h1, hPT, hinv⟩

/-! ## The logspace trio over the paper's class (`thm:wrp-logspace`,
`thm:wrp-strict-below-logspace`) -/

/-- **`thm:wrp-logspace` over the revision's `def:wrp` class**: every
paper-exact WRP map is computable by a deterministic multihead bounded-counter
logspace machine. -/
theorem wrp_paper_isLogspaceMH {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma]
    (T : List Step → Option (List Gamma)) (hT : IsWRPPaper T) :
    Multihead.IsLogspaceMH T :=
  wrp_isLogspaceMH T hT.isWRP

/-- **The polynomial-time clause of `thm:wrp-logspace` over the revision's
class**: the witnessing machine halts within the explicit polynomial bound. -/
theorem wrp_paper_logspace_polytime {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma]
    (T : List Step → Option (List Gamma)) (hT : IsWRPPaper T) :
    ∃ (h c C : ℕ) (M : Multihead.MHC Step Gamma h c),
      Multihead.SpaceBound M C ∧ (∀ w out, T w = some out ↔ M.Computes w out) ∧
      ∀ w out e N, M.StepsN w M.initConfig out e N → M.Halted w e →
        N < M.cardQ * (w.length + 2) ^ h * (C * (w.length + 1) + 1) ^ c :=
  wrp_logspace_polytime T hT.isWRP

/-- **`thm:wrp-strict-below-logspace` over the revision's `def:wrp` class**:
the paper-exact WRP class is contained in deterministic (multihead) logspace,
and some logspace map lies outside it.  Both halves a fortiori: containment
through `IsWRPPaper ⊆ IsWRP`, separation because the witness `F_{≥0}` is not
even in the larger class. -/
theorem wrp_strict_below_logspace_paper :
    (∀ T : List Step → Option (List WRPComp.GBD), IsWRPPaper T →
      Multihead.IsLogspaceMH T) ∧
    ∃ f : List Step → Option (List WRPComp.GBD),
      Multihead.IsLogspaceMH f ∧ ¬ IsWRPPaper f :=
  ⟨fun T hT => wrp_isLogspaceMH T hT.isWRP,
   ⟨WRPComp.Fge0, Multihead.Fge0_isLogspaceMH,
    fun h => WRPComp.Fge0_not_isWRP h.isWRP⟩⟩
