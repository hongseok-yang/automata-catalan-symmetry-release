/-
# COVERAGE: the locus of a suffix-run d*-achiever (§9 mS-direction, the direct-bridge ⟸ crux)

The direct `hbr` bridge `TIE ⟺ accepts(GdfaF)` needs (its `⟸` direction) that EVERY selected-`D`
`d*`-achiever is covered by SOME gate.  This file proves the suffix case: a selected-`D` achiever at
final-`D`-run depth `l` is SHALLOW (`l < q_D` ⇒ cfgCellGAFL/CORE), or in a SLOPE-0 residue class
(⇒ the whole class ties d* ⇒ run-clause `sufOrdClauseAt`), or a FROM-END cell (`mS-1-l < mx+pc`,
`mx = max q_U q_D` ⇒ deep gate `deepSufOrdClauseAt`).

The three cases are clean once `selconst_suf` makes the run's `[Ts, Nc)`-segment of each pc-class
uniformly selected: an interior achiever (`Ts+pc ≤ l ∧ l+pc < Nc`) forces its whole class to tie d*
— this is EXACTLY `CopiedSelUniform.run_class_uniform_core` (the slope-sign / endpoint-domination
collapse), whose conclusion is our slope-0 disjunct.  The shallow and deep ends are pure arithmetic.
The deep band must reach offsets `[1, mx+pc)` (not just `[1,q_D]`) because a slope<0 class's deepest
SELECTED member can sit at `l ∈ [Nc-pc, Nc)` (selconst-unreachable, so deeper same-class members may
be unselected — no rank<d* contradiction); its from-end offset `mS-1-l ∈ [mx, mx+pc)`.
-/
import RequestProject.CopiedSelUniform

namespace CopiedAchieverLocus

open WRP Step SliceMSO MSOMarkN SliceMarkN CopiedDstar CopiedDstarCMS SliceBoundaryMinCore
  CopiedSelConst CopiedSelUniform

/-- **COVERAGE (suffix).**  A selected-`D` achiever at final-`D`-run depth `l` (`rank = d*`) is
SHALLOW (`l < q_D`), or in a SLOPE-0 pc-class (the whole class `≥ Ts` ties d*), or a FROM-END cell
(`mS-1-l < mx+pc`).  `pc/Ts/Nc/FFs/q_D/mx` are the per-`c0` coordCands data (`hselconst` from
`selconst_suf`; `Nc ≤ mS-1`, `mS ≤ Nc+mx` with `mx = max q_U q_D`, `Ts+pc < q_D`). -/
theorem suffix_dstar_achiever_locus_of_runClass
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hRunClass : RunClassAffineUniformCoverage P hV)
    (c0 : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c0)) (ī0 : Fin (P.toPoly.arity c0) → ℕ)
    (mS n : ℕ)
    (pc Ts Nc q_D mx : ℕ) (FFs : ℕ → Fin P.d → ℤ) (hpc : 1 ≤ pc)
    (hTq : Ts + pc < q_D)
    (hF : RankAffineAtFrom Ts pc FFs)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c0 (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l')) = FFs l')
    (hselconst : ∀ l₁ l₂, Ts ≤ l₁ → l₁ < Nc → Ts ≤ l₂ → l₂ < Nc →
        (l₁ - Ts) % pc = (l₂ - Ts) % pc →
        ((P.toPoly.sel c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₁)
            ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₁) = D)
          ↔ (P.toPoly.sel c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₂)
            ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₂) = D)))
    (hNcmS : Nc ≤ mS - 1) (hNcmx : mS ≤ Nc + mx)
    (l : ℕ) (hl : l < mS - 1)
    (hsel : P.toPoly.sel c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l)
        ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l) = D)
    (hachF : FFs l = CopiedDstar.dstarRankGA_m P hV mS n) :
    l < q_D
    ∨ (∀ l', Ts ≤ l' → l' < mS - 1 → (l' - Ts) % pc = (l - Ts) % pc →
        FFs l' = CopiedDstar.dstarRankGA_m P hV mS n)
    ∨ (1 ≤ mS - 1 - l ∧ mS - 1 - l < mx + pc) := by
  by_cases hlq : l < q_D
  · exact Or.inl hlq
  · push Not at hlq
    by_cases hint : l + pc < Nc
    · refine Or.inr (Or.inl ?_)
      exact hRunClass c0 j0 ī0 mS n pc Ts Nc FFs hpc hF
        (fun l' => mS + 2 * n + 1 + l')
        (fun l' hl' => by
          show mS + 2 * n + 1 + l' < (copiedSlice mS n).length
          rw [length_copiedSlice]; omega)
        hag hselconst hNcmS l (by omega) hint hsel hachF
    · push Not at hint
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)

/-- Arity-free suffix achiever trichotomy for an updated-coordinate tuple.
This is the descriptor-facing variant of `suffix_dstar_achiever_locus_of_runClass`:
the selected-D constancy and witness use `Function.update ī0 j0`, so no
tuple-fibre scalarization is needed. -/
theorem suffix_dstar_achiever_update_locus_of_valid
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c0 : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c0)) (ī0 : Fin (P.toPoly.arity c0) → ℕ)
    (mS n : ℕ)
    (pc Ts Nc q_D mx : ℕ) (FFs : ℕ → Fin P.d → ℤ) (hpc : 1 ≤ pc)
    (hTq : Ts + pc < q_D)
    (hF : RankAffineAtFrom Ts pc FFs)
    (hupdval : ∀ l', l' < mS - 1 →
      ∀ i, Function.update ī0 j0 (mS + 2 * n + 1 + l') i < (copiedSlice mS n).length)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c0 (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l')) = FFs l')
    (hselconst : ∀ l₁ l₂, Ts ≤ l₁ → l₁ < Nc → Ts ≤ l₂ → l₂ < Nc →
        (l₁ - Ts) % pc = (l₂ - Ts) % pc →
        ((P.toPoly.sel c0 (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l₁))
            ∧ P.toPoly.label c0 (copiedSlice mS n)
                (Function.update ī0 j0 (mS + 2 * n + 1 + l₁)) = D)
          ↔ (P.toPoly.sel c0 (copiedSlice mS n)
                (Function.update ī0 j0 (mS + 2 * n + 1 + l₂))
            ∧ P.toPoly.label c0 (copiedSlice mS n)
                (Function.update ī0 j0 (mS + 2 * n + 1 + l₂)) = D)))
    (hNcmS : Nc ≤ mS - 1) (hNcmx : mS ≤ Nc + mx)
    (l : ℕ) (hl : l < mS - 1)
    (hsel : P.toPoly.sel c0 (copiedSlice mS n)
          (Function.update ī0 j0 (mS + 2 * n + 1 + l))
        ∧ P.toPoly.label c0 (copiedSlice mS n)
          (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = D)
    (hachF : FFs l = CopiedDstar.dstarRankGA_m P hV mS n) :
    l < q_D
    ∨ (∀ l', Ts ≤ l' → l' < mS - 1 → (l' - Ts) % pc = (l - Ts) % pc →
        FFs l' = CopiedDstar.dstarRankGA_m P hV mS n)
    ∨ (1 ≤ mS - 1 - l ∧ mS - 1 - l < mx + pc) := by
  by_cases hlq : l < q_D
  · exact Or.inl hlq
  · push Not at hlq
    by_cases hint : l + pc < Nc
    · refine Or.inr (Or.inl ?_)
      exact CopiedSelUniform.run_class_uniform_update_core_of_valid P hV c0 j0 ī0 mS n
        pc Ts Nc FFs hpc hF (fun l' => mS + 2 * n + 1 + l') hupdval hag hselconst
        hNcmS l (by omega) hint hsel hachF
    · push Not at hint
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)

/-- Arity-free prefix achiever trichotomy for an updated-coordinate tuple. -/
theorem prefix_dstar_achiever_update_locus_of_valid
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c0 : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c0)) (ī0 : Fin (P.toPoly.arity c0) → ℕ)
    (mS n : ℕ)
    (pc Tp Nc q_U mx : ℕ) (FFp : ℕ → Fin P.d → ℤ) (hpc : 1 ≤ pc)
    (hTq : Tp + pc < q_U)
    (hF : RankAffineAtFrom Tp pc FFp)
    (hupdval : ∀ l', l' < mS - 1 →
      ∀ i, Function.update ī0 j0 l' i < (copiedSlice mS n).length)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c0 (copiedSlice mS n) (Function.update ī0 j0 l') = FFp l')
    (hselconst : ∀ l₁ l₂, Tp ≤ l₁ → l₁ < Nc → Tp ≤ l₂ → l₂ < Nc →
        (l₁ - Tp) % pc = (l₂ - Tp) % pc →
        ((P.toPoly.sel c0 (copiedSlice mS n) (Function.update ī0 j0 l₁)
            ∧ P.toPoly.label c0 (copiedSlice mS n) (Function.update ī0 j0 l₁) = D)
          ↔ (P.toPoly.sel c0 (copiedSlice mS n) (Function.update ī0 j0 l₂)
            ∧ P.toPoly.label c0 (copiedSlice mS n) (Function.update ī0 j0 l₂) = D)))
    (hNcmS : Nc ≤ mS - 1) (hNcmx : mS ≤ Nc + mx)
    (l : ℕ) (hl : l < mS - 1)
    (hsel : P.toPoly.sel c0 (copiedSlice mS n) (Function.update ī0 j0 l)
        ∧ P.toPoly.label c0 (copiedSlice mS n) (Function.update ī0 j0 l) = D)
    (hachF : FFp l = CopiedDstar.dstarRankGA_m P hV mS n) :
    l < q_U
    ∨ (∀ l', Tp ≤ l' → l' < mS - 1 → (l' - Tp) % pc = (l - Tp) % pc →
        FFp l' = CopiedDstar.dstarRankGA_m P hV mS n)
    ∨ (1 ≤ mS - 1 - l ∧ mS - 1 - l < mx + pc) := by
  by_cases hlq : l < q_U
  · exact Or.inl hlq
  · push Not at hlq
    by_cases hint : l + pc < Nc
    · refine Or.inr (Or.inl ?_)
      exact CopiedSelUniform.run_class_uniform_update_core_of_valid P hV c0 j0 ī0 mS n
        pc Tp Nc FFp hpc hF (fun l' => l') hupdval hag hselconst
        hNcmS l (by omega) hint hsel hachF
    · push Not at hint
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)

/-- Descriptor-facing suffix/prefix d*-achiever coverage package.  Unlike the
legacy bridge-facing `DstarAchieverLocus`, selected-D constancy and the witness
are stated directly for the distinguished-coordinate update tuple. -/
def DstarAchieverUpdateLocus (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    (∀ (c0 : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c0))
      (ī0 : Fin (P.toPoly.arity c0) → ℕ)
      (mS n : ℕ)
      (pc Ts Nc q_D mx : ℕ) (FFs : ℕ → Fin P.d → ℤ) (_hpc : 1 ≤ pc)
      (_hTq : Ts + pc < q_D)
      (_hF : RankAffineAtFrom Ts pc FFs)
      (_hupdval : ∀ l', l' < mS - 1 →
        ∀ i, Function.update ī0 j0 (mS + 2 * n + 1 + l') i < (copiedSlice mS n).length)
      (_hag : ∀ l', l' < mS - 1 →
        P.rank c0 (copiedSlice mS n)
          (Function.update ī0 j0 (mS + 2 * n + 1 + l')) = FFs l')
      (_hselconst : ∀ l₁ l₂, Ts ≤ l₁ → l₁ < Nc → Ts ≤ l₂ → l₂ < Nc →
          (l₁ - Ts) % pc = (l₂ - Ts) % pc →
          ((P.toPoly.sel c0 (copiedSlice mS n)
                (Function.update ī0 j0 (mS + 2 * n + 1 + l₁))
              ∧ P.toPoly.label c0 (copiedSlice mS n)
                (Function.update ī0 j0 (mS + 2 * n + 1 + l₁)) = D)
            ↔ (P.toPoly.sel c0 (copiedSlice mS n)
                (Function.update ī0 j0 (mS + 2 * n + 1 + l₂))
              ∧ P.toPoly.label c0 (copiedSlice mS n)
                (Function.update ī0 j0 (mS + 2 * n + 1 + l₂)) = D)))
      (_hNcmS : Nc ≤ mS - 1) (_hNcmx : mS ≤ Nc + mx)
      (l : ℕ) (_hl : l < mS - 1)
      (_hsel : P.toPoly.sel c0 (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + l))
          ∧ P.toPoly.label c0 (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = D)
      (_hachF : FFs l = CopiedDstar.dstarRankGA_m P hV mS n),
      l < q_D
      ∨ (∀ l', Ts ≤ l' → l' < mS - 1 → (l' - Ts) % pc = (l - Ts) % pc →
          FFs l' = CopiedDstar.dstarRankGA_m P hV mS n)
      ∨ (1 ≤ mS - 1 - l ∧ mS - 1 - l < mx + pc)) ∧
    (∀ (c0 : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c0))
      (ī0 : Fin (P.toPoly.arity c0) → ℕ)
      (mS n : ℕ)
      (pc Tp Nc q_U mx : ℕ) (FFp : ℕ → Fin P.d → ℤ) (_hpc : 1 ≤ pc)
      (_hTq : Tp + pc < q_U)
      (_hF : RankAffineAtFrom Tp pc FFp)
      (_hupdval : ∀ l', l' < mS - 1 →
        ∀ i, Function.update ī0 j0 l' i < (copiedSlice mS n).length)
      (_hag : ∀ l', l' < mS - 1 →
        P.rank c0 (copiedSlice mS n) (Function.update ī0 j0 l') = FFp l')
      (_hselconst : ∀ l₁ l₂, Tp ≤ l₁ → l₁ < Nc → Tp ≤ l₂ → l₂ < Nc →
          (l₁ - Tp) % pc = (l₂ - Tp) % pc →
          ((P.toPoly.sel c0 (copiedSlice mS n) (Function.update ī0 j0 l₁)
              ∧ P.toPoly.label c0 (copiedSlice mS n) (Function.update ī0 j0 l₁) = D)
            ↔ (P.toPoly.sel c0 (copiedSlice mS n) (Function.update ī0 j0 l₂)
              ∧ P.toPoly.label c0 (copiedSlice mS n) (Function.update ī0 j0 l₂) = D)))
      (_hNcmS : Nc ≤ mS - 1) (_hNcmx : mS ≤ Nc + mx)
      (l : ℕ) (_hl : l < mS - 1)
      (_hsel : P.toPoly.sel c0 (copiedSlice mS n) (Function.update ī0 j0 l)
          ∧ P.toPoly.label c0 (copiedSlice mS n) (Function.update ī0 j0 l) = D)
      (_hachF : FFp l = CopiedDstar.dstarRankGA_m P hV mS n),
      l < q_U
      ∨ (∀ l', Tp ≤ l' → l' < mS - 1 → (l' - Tp) % pc = (l - Tp) % pc →
          FFp l' = CopiedDstar.dstarRankGA_m P hV mS n)
      ∨ (1 ≤ mS - 1 - l ∧ mS - 1 - l < mx + pc))

/-- Public arity-free supplier for descriptor-facing d*-achiever coverage. -/
theorem dstarAchieverUpdateLocus
    (P : WRP.Presentation Step Step) (hV : P.Valid) :
    DstarAchieverUpdateLocus P hV := by
  constructor
  · intro c0 j0 ī0 mS n pc Ts Nc q_D mx FFs hpc hTq hF hupdval hag hselconst
      hNcmS hNcmx l hl hsel hachF
    exact suffix_dstar_achiever_update_locus_of_valid P hV c0 j0 ī0 mS n pc Ts Nc q_D mx FFs
      hpc hTq hF hupdval hag hselconst hNcmS hNcmx l hl hsel hachF
  · intro c0 j0 ī0 mS n pc Tp Nc q_U mx FFp hpc hTq hF hupdval hag hselconst
      hNcmS hNcmx l hl hsel hachF
    exact prefix_dstar_achiever_update_locus_of_valid P hV c0 j0 ī0 mS n pc Tp Nc q_U mx FFp
      hpc hTq hF hupdval hag hselconst hNcmS hNcmx l hl hsel hachF

/-- Affine-table suffix/prefix d*-achiever coverage package.  This is the run-residue coverage
shape that no longer mentions arity-one scalarization: the slope branch is stated directly for the
affine tables `FFs`/`FFp`. -/
def DstarAchieverAffineLocus (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    (∀ (c0 : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c0))
      (ī0 : Fin (P.toPoly.arity c0) → ℕ)
      (mS n : ℕ)
      (pc Ts Nc q_D mx : ℕ) (FFs : ℕ → Fin P.d → ℤ) (_hpc : 1 ≤ pc)
      (_hTq : Ts + pc < q_D)
      (_hF : RankAffineAtFrom Ts pc FFs)
      (_hag : ∀ l', l' < mS - 1 →
        P.rank c0 (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l')) = FFs l')
      (_hselconst : ∀ l₁ l₂, Ts ≤ l₁ → l₁ < Nc → Ts ≤ l₂ → l₂ < Nc →
          (l₁ - Ts) % pc = (l₂ - Ts) % pc →
          ((P.toPoly.sel c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₁)
              ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₁) = D)
            ↔ (P.toPoly.sel c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₂)
              ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₂) = D)))
      (_hNcmS : Nc ≤ mS - 1) (_hNcmx : mS ≤ Nc + mx)
      (l : ℕ) (_hl : l < mS - 1)
      (_hsel : P.toPoly.sel c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l)
          ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l) = D)
      (_hachF : FFs l = CopiedDstar.dstarRankGA_m P hV mS n),
      l < q_D
      ∨ (∀ l', Ts ≤ l' → l' < mS - 1 → (l' - Ts) % pc = (l - Ts) % pc →
          FFs l' = CopiedDstar.dstarRankGA_m P hV mS n)
      ∨ (1 ≤ mS - 1 - l ∧ mS - 1 - l < mx + pc)) ∧
    (∀ (c0 : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c0))
      (ī0 : Fin (P.toPoly.arity c0) → ℕ)
      (mS n : ℕ)
      (pc Tp Nc q_U mx : ℕ) (FFp : ℕ → Fin P.d → ℤ) (_hpc : 1 ≤ pc)
      (_hTq : Tp + pc < q_U)
      (_hF : RankAffineAtFrom Tp pc FFp)
      (_hag : ∀ l', l' < mS - 1 →
        P.rank c0 (copiedSlice mS n) (Function.update ī0 j0 l') = FFp l')
      (_hselconst : ∀ l₁ l₂, Tp ≤ l₁ → l₁ < Nc → Tp ≤ l₂ → l₂ < Nc →
          (l₁ - Tp) % pc = (l₂ - Tp) % pc →
          ((P.toPoly.sel c0 (copiedSlice mS n) (fun _ => l₁)
              ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => l₁) = D)
            ↔ (P.toPoly.sel c0 (copiedSlice mS n) (fun _ => l₂)
              ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => l₂) = D)))
      (_hNcmS : Nc ≤ mS - 1) (_hNcmx : mS ≤ Nc + mx)
      (l : ℕ) (_hl : l < mS - 1)
      (_hsel : P.toPoly.sel c0 (copiedSlice mS n) (fun _ => l)
          ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => l) = D)
      (_hachF : FFp l = CopiedDstar.dstarRankGA_m P hV mS n),
      l < q_U
      ∨ (∀ l', Tp ≤ l' → l' < mS - 1 → (l' - Tp) % pc = (l - Tp) % pc →
          FFp l' = CopiedDstar.dstarRankGA_m P hV mS n)
      ∨ (1 ≤ mS - 1 - l ∧ mS - 1 - l < mx + pc))

/-- Abstract suffix/prefix d*-achiever coverage package used by the row-indexed
tie bridge.  The current supplier is arity-1; an arbitrary-arity proof should
provide this package directly. -/
def DstarAchieverLocus (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    (∀ (c0 : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c0))
      (ī0 : Fin (P.toPoly.arity c0) → ℕ)
      (mS n : ℕ)
      (pc Ts Nc q_D mx : ℕ) (FFs : ℕ → Fin P.d → ℤ) (_hpc : 1 ≤ pc)
      (_hTq : Ts + pc < q_D)
      (_hF : RankAffineAtFrom Ts pc FFs)
      (_hag : ∀ l', l' < mS - 1 →
        P.rank c0 (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l')) = FFs l')
      (_hselconst : ∀ l₁ l₂, Ts ≤ l₁ → l₁ < Nc → Ts ≤ l₂ → l₂ < Nc →
          (l₁ - Ts) % pc = (l₂ - Ts) % pc →
          ((P.toPoly.sel c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₁)
              ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₁) = D)
            ↔ (P.toPoly.sel c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₂)
              ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₂) = D)))
      (_hNcmS : Nc ≤ mS - 1) (_hNcmx : mS ≤ Nc + mx)
      (l : ℕ) (_hl : l < mS - 1)
      (_hsel : P.toPoly.sel c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l)
          ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l) = D)
      (_hach : P.rank c0 (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l)
          = CopiedDstar.dstarRankGA_m P hV mS n),
      l < q_D
      ∨ (∀ l', Ts ≤ l' → l' < mS - 1 → (l' - Ts) % pc = (l - Ts) % pc →
          FFs l' = CopiedDstar.dstarRankGA_m P hV mS n)
      ∨ (1 ≤ mS - 1 - l ∧ mS - 1 - l < mx + pc)) ∧
    (∀ (c0 : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c0))
      (ī0 : Fin (P.toPoly.arity c0) → ℕ)
      (mS n : ℕ)
      (pc Tp Nc q_U mx : ℕ) (FFp : ℕ → Fin P.d → ℤ) (_hpc : 1 ≤ pc)
      (_hTq : Tp + pc < q_U)
      (_hF : RankAffineAtFrom Tp pc FFp)
      (_hag : ∀ l', l' < mS - 1 →
        P.rank c0 (copiedSlice mS n) (Function.update ī0 j0 l') = FFp l')
      (_hselconst : ∀ l₁ l₂, Tp ≤ l₁ → l₁ < Nc → Tp ≤ l₂ → l₂ < Nc →
          (l₁ - Tp) % pc = (l₂ - Tp) % pc →
          ((P.toPoly.sel c0 (copiedSlice mS n) (fun _ => l₁)
              ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => l₁) = D)
            ↔ (P.toPoly.sel c0 (copiedSlice mS n) (fun _ => l₂)
              ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => l₂) = D)))
      (_hNcmS : Nc ≤ mS - 1) (_hNcmx : mS ≤ Nc + mx)
      (l : ℕ) (_hl : l < mS - 1)
      (_hsel : P.toPoly.sel c0 (copiedSlice mS n) (fun _ => l)
          ∧ P.toPoly.label c0 (copiedSlice mS n) (fun _ => l) = D)
      (_hach : P.rank c0 (copiedSlice mS n) (fun _ => l)
          = CopiedDstar.dstarRankGA_m P hV mS n),
      l < q_U
      ∨ (∀ l', Tp ≤ l' → l' < mS - 1 → (l' - Tp) % pc = (l - Tp) % pc →
          FFp l' = CopiedDstar.dstarRankGA_m P hV mS n)
      ∨ (1 ≤ mS - 1 - l ∧ mS - 1 - l < mx + pc))

end CopiedAchieverLocus
