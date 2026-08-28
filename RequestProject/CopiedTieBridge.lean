/-
# The coordinate bridge `cfgPos → cfgPosL` (§9 tower, Stage F3.7)

The selector (`CopiedSelector.cfgCellArmF`) emits its position clause `cfgPos` in
REDUCED wrapped coordinates (length `2(n+1)`, base `1 + 2t`), while the fibred
clause DFA (`CopiedTieGate.clauseFMk_accepts`) CONSUMES `cfgPosL` in COPIED
landmark coordinates (`yF = mS+1`, `yL = mS+2(n-1)`, `z = mS+2t`).  Because the
first `D` landmark `yF` sits at wrapped position `2`, the two coordinate systems
differ by a constant `-2`:

* the residue set must be REFLECTED `s ↦ (M + 2 - s) % M` (the Lean nat-safe form
  of `(2 - s) % M`),
* the front/back offsets shift by `-2`,
* the window threshold shifts `mthr ↦ mthr - 2`.

`cfgPos_imp_cfgPosL` is the (UNCONDITIONAL) forward direction.  Numerically
verified to hold with zero counterexamples over 400k random instances; the
converse fails only at the boundary bases (`t = 0`, `t ≈ n`) where `cfgPosL`'s
prefix/suffix stretch disjuncts over-fire — those bases are covered by the
selector's frozen arm, so the forward direction is the load-bearing one.
-/
import RequestProject.CopiedTieGate
import RequestProject.CopiedDstarCMS

namespace CopiedTieBridge

open WRP Step MSOMarkN SliceMarkN CopiedCells CopiedDstar CopiedSetupMS CopiedGateEP
open scoped Classical

/-- **The forward coordinate bridge** (FG1/FG2 resolved): the reduced-coordinate
`cfgPos` at base `1+2t` implies the landmark-coordinate `cfgPosL` at `z = mS+2t`,
once the residue set is reflected (`s ↦ (M+2-s)%M`), the front/back offsets are
shifted by `-2`, and the window threshold is `mthr-2`.  Unconditional in `t`. -/
theorem cfgPos_imp_cfgPosL (M mthr : ℕ) (S Front Back : Finset ℕ) (mS n t : ℕ)
    (hM : 1 ≤ M) (hm : 1 ≤ mS) (ht : t < n) (hmthr : 2 ≤ mthr)
    (h : SliceFasGates.cfgPos M mthr S Front Back (2 * (n + 1)) (1 + 2 * t)) :
    CopiedTieGate.cfgPosL M (mthr - 2)
      (S.image (fun s => (M + 2 - s) % M))
      (Front.image (fun f => f - 2))
      (Back.image (fun k => k - 2))
      (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) := by
  rw [CopiedTieGate.cfgPosL]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rcases h with ⟨hw1, hw2, hres⟩ | hfront | ⟨k, hkB, hkeq⟩
  · -- bulk residue arm
    refine Or.inl ⟨by omega, by omega, ?_⟩
    refine ⟨(M + 2 - (1 + 2 * t) % M) % M, Finset.mem_image_of_mem _ hres, ?_⟩
    set s := (1 + 2 * t) % M with hs_def
    set r := (M + 2 - s) % M with hr_def
    have hslt : s < M := by rw [hs_def]; exact Nat.mod_lt _ hM
    have hrlt : r < M := by rw [hr_def]; exact Nat.mod_lt _ hM
    -- s + r ≡ 2 [MOD M]
    have hsr : (s + r) % M = 2 % M := by
      have h1 : r ≡ M + 2 - s [MOD M] := by rw [hr_def]; exact Nat.mod_modEq _ _
      have h2 : (s + r) % M = (s + (M + 2 - s)) % M := Nat.ModEq.add_left s h1
      have h3 : s + (M + 2 - s) = M + 2 := by omega
      rw [h2, h3, Nat.add_mod_left]
    -- s ≡ 1 + 2t [MOD M]
    have hs : s ≡ 1 + 2 * t [MOD M] := by rw [hs_def]; exact Nat.mod_modEq _ _
    -- (1 + 2t) + r ≡ 2 [MOD M]
    have hkey : (1 + 2 * t) + r ≡ 2 [MOD M] := (hs.symm.add_right r).trans hsr
    -- the modular identity: (mS+1+(M-r)) ≡ mS+2t [MOD M]
    show (mS + 1 + (M - r)) % M = (mS + 2 * t) % M
    refine Nat.ModEq.add_right_cancel' r ?_
    have e1 : mS + 1 + (M - r) + r = mS + 1 + M := by omega
    have e2 : mS + 2 * t + r = (mS - 1) + ((1 + 2 * t) + r) := by omega
    rw [e1, e2]
    calc mS + 1 + M ≡ mS + 1 [MOD M] :=
          Nat.ModEq.add_left (mS + 1) (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
      _ = (mS - 1) + 2 := by omega
      _ ≡ (mS - 1) + ((1 + 2 * t) + r) [MOD M] := Nat.ModEq.add_left (mS - 1) hkey.symm
  · -- front arm
    refine Or.inr (Or.inl ⟨(1 + 2 * t) - 2, Finset.mem_image_of_mem _ hfront, ?_⟩)
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · left; subst ht0; exact ⟨by omega, by omega⟩
    · right; exact ⟨by omega, by omega⟩
  · -- back arm
    exact Or.inr (Or.inr ⟨k - 2, Finset.mem_image_of_mem _ hkB, by omega⟩)

/-- **Residue-reflection hygiene**: for `M` even, the reflection `s ↦ (M+2-s)%M`
sends an all-odd, `<M` residue set to an all-odd, `<M` set.  This feeds the
clause's `hSodd`/`hM2` hypotheses when the bridge hands the reflected selector
residues `S₁` to `clauseFMk_accepts`.  (Odd `mod` even is odd; `M+2-s` is odd as
`M+2` is even and `s` odd with `s < M`.) -/
theorem remapS_hygiene (M : ℕ) (S : Finset ℕ) (hM2 : M % 2 = 0)
    (hSlt : ∀ s ∈ S, s < M) (hSodd : ∀ s ∈ S, s % 2 = 1) :
    ∀ r ∈ S.image (fun s => (M + 2 - s) % M), r % 2 = 1 ∧ r < M := by
  intro r hr
  obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.mp hr
  have hslt := hSlt s hsS
  have hsodd := hSodd s hsS
  refine ⟨?_, Nat.mod_lt _ (by omega)⟩
  rw [Nat.mod_mod_of_dvd _ (show (2 : ℕ) ∣ M from ⟨M / 2, by omega⟩)]
  omega

/-- **The d*-reduction** (the key that sidesteps the fibred stretch obstruction): for the
`wrpOrd`-MINIMAL equal-rank selected `D`-atom `dstar`, the TIE condition "`a` atom-precedes every
equal-rank selected `D`-atom" collapses to the SINGLE comparison `atomOrd a dstar`.  Forward:
instantiate `b := dstar`.  Backward: `dstar` is the min, so for any equal-rank `b` we get
`wrpOrd dstar b`; on equal rank `wrpOrd` is exactly `atomOrd` (the lex part is irreflexive); then
`wrpOrd a dstar` and `wrpOrd dstar b` compose by `Valid.trans` and drop back to `atomOrd a b`.
Generic in `w` — composes with `SliceFasTie.fas_member_eqRank` to turn `fas a` into
`atomOrd a dstar`, which a `boundary_pair_component` gate (the whole `dstar` as MARKS, no decode)
checks directly.  This is what makes a single fixed `dstar`-atom gate suffice, with NO `∀b`
conjunction and NO `mS`-free decode of `dstar`'s prefix/suffix stretch coordinates. -/
theorem tie_eq_atomOrd_dstar {Alpha : Type*} (P : WRP.Presentation Alpha Step) (hV : P.Valid)
    (w : List Alpha) (dstar : P.toPoly.Atom)
    (hdsel : P.toPoly.selectedAtom w dstar) (hdD : P.toPoly.labelOf w dstar = D)
    (hdmin : ∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = D →
      dstar = b ∨ P.wrpOrd w dstar b)
    (a : P.toPoly.Atom) (hasel : P.toPoly.selectedAtom w a)
    (hrankeq : P.rankOf w a = P.rankOf w dstar) :
    (∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = D →
        P.rankOf w b = P.rankOf w dstar → P.toPoly.atomOrd w a b)
      ↔ P.toPoly.atomOrd w a dstar := by
  constructor
  · intro h; exact h dstar hdsel hdD rfl
  · intro hao b hbsel hbD hbrank
    by_cases hbd : dstar = b
    · subst hbd; exact hao
    · have hmin := (hdmin b hbsel hbD).resolve_left hbd
      have hatdb : P.toPoly.atomOrd w dstar b := by
        rcases hmin with hlex | ⟨_, hat⟩
        · exact absurd hlex (by rw [hbrank]; exact SliceLexOrder.lexLt_irrefl _)
        · exact hat
      have hwad : P.wrpOrd w a dstar := Or.inr ⟨hrankeq, hao⟩
      have hwdb : P.wrpOrd w dstar b := Or.inr ⟨hbrank.symm, hatdb⟩
      have hwab := hV.trans w a dstar b hasel hdsel hbsel hwad hwdb
      rcases hwab with hlex | ⟨_, hat⟩
      · exact absurd hlex (by rw [hrankeq, hbrank]; exact SliceLexOrder.lexLt_irrefl _)
      · exact hat

/-- **The gate characterization** (the heart of the d*-route bridge): the `selectedU` gate and the
`boundary_pair_component` gate (fed `Fin.append i_tup xb`) together decide
`sel c i_tup ∧ label c i_tup = U ∧ atomOrd ⟨c,i_tup⟩ ⟨c',xb⟩`, for any selected `D`-atom
`⟨c',xb⟩`.  Generic in `w`.  NO decode, NO `∀b`: `xb`'s coordinates (including prefix/suffix stretch
positions) are just the `boundary_pair_component`'s HIGH marks, fed verbatim — which is exactly why
the d*-route sidesteps the stretch obstruction.  Composed with `tie_eq_atomOrd_dstar` (`xb :=` the
minimal `dstar`) and `SliceFasTie.fas_member_eqRank`, the RHS gate-conjunction characterizes `fas`. -/
theorem tie_gate_char (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (w : List Step) (i_tup : Fin (P.toPoly.arity c) → ℕ) (xb : Fin (P.toPoly.arity c') → ℕ)
    (hiv : ∀ i, i_tup i < w.length) (hxv : ∀ i, xb i < w.length)
    (hsel : P.toPoly.sel c' w xb) (hlab : P.toPoly.label c' w xb = D) :
    (P.toPoly.sel c w i_tup ∧ P.toPoly.label c w i_tup = U ∧
        P.toPoly.atomOrd w (⟨c, i_tup⟩ : P.toPoly.Atom) (⟨c', xb⟩ : P.toPoly.Atom))
      ↔ ((SliceFasGatesGA.selectedU_gate_GA P c).choose.accepts
            (markAtN (P.toPoly.arity c) w i_tup) ∧
          (CopiedTieGate.boundary_pair_component P c c').choose.accepts
            (markAtN _ w (Fin.append i_tup xb))) := by
  rw [(SliceFasGatesGA.selectedU_gate_GA P c).choose_spec w i_tup hiv,
    (CopiedTieGate.boundary_pair_component P c c').choose_spec w i_tup xb hiv hxv]
  constructor
  · rintro ⟨hs, hl, hord⟩
    exact ⟨⟨hs, hl⟩, fun _ => hord⟩
  · rintro ⟨⟨hs, hl⟩, hpair⟩
    exact ⟨hs, hl, hpair ⟨hsel, hlab⟩⟩

/-- Pointwise whole-tuple d\*-gate characterization under the exact semantic
minimality hypothesis.  This is the reusable core of the d\*-route: once a
finite `D` tuple is known to be the `wrpOrd`-minimal selected `D` atom at its
rank, the selected-`U` gate and the boundary pair component characterize the
full `∀ b` tie condition, not just `atomOrd` against that one tuple. -/
theorem tie_gate_char_of_minimal_dstar
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c cD : Fin P.toPoly.K) (w : List Step)
    (i_tup : Fin (P.toPoly.arity c) → ℕ)
    (xb : Fin (P.toPoly.arity cD) → ℕ)
    (hiv : ∀ i, i_tup i < w.length)
    (hDsel : P.toPoly.selectedAtom w (⟨cD, xb⟩ : P.toPoly.Atom))
    (hDlabel : P.toPoly.labelOf w (⟨cD, xb⟩ : P.toPoly.Atom) = D)
    (hDmin : ∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = D →
      (⟨cD, xb⟩ : P.toPoly.Atom) = b ∨ P.wrpOrd w (⟨cD, xb⟩ : P.toPoly.Atom) b) :
    ((P.toPoly.sel c w i_tup ∧
        P.toPoly.labelOf w (⟨c, i_tup⟩ : P.toPoly.Atom) = U ∧
        P.rankOf w (⟨c, i_tup⟩ : P.toPoly.Atom)
          = P.rankOf w (⟨cD, xb⟩ : P.toPoly.Atom) ∧
        ∀ b, P.toPoly.selectedAtom w b →
          P.toPoly.labelOf w b = D →
          P.rankOf w b = P.rankOf w (⟨cD, xb⟩ : P.toPoly.Atom) →
          P.toPoly.atomOrd w (⟨c, i_tup⟩ : P.toPoly.Atom) b)
     ↔ ((SliceFasGatesGA.selectedU_gate_GA P c).choose.accepts
            (markAtN (P.toPoly.arity c) w i_tup) ∧
          (CopiedTieGate.boundary_pair_component P c cD).choose.accepts
            (markAtN _ w (Fin.append i_tup xb)) ∧
          P.rankOf w (⟨c, i_tup⟩ : P.toPoly.Atom)
            = P.rankOf w (⟨cD, xb⟩ : P.toPoly.Atom))) := by
  classical
  have hgc := tie_gate_char P c cD w i_tup xb hiv hDsel.1 hDsel.2 hDlabel
  constructor
  · rintro ⟨hs, hl, hrank, hall⟩
    have hred := (tie_eq_atomOrd_dstar P hV w (⟨cD, xb⟩ : P.toPoly.Atom)
      hDsel hDlabel hDmin (⟨c, i_tup⟩ : P.toPoly.Atom) ⟨hiv, hs⟩ hrank).mp hall
    have hgates := hgc.mp ⟨hs, hl, hred⟩
    exact ⟨hgates.1, hgates.2, hrank⟩
  · rintro ⟨hgU, hgP, hrank⟩
    obtain ⟨hs, hl, haod⟩ := hgc.mpr ⟨hgU, hgP⟩
    refine ⟨hs, hl, hrank, fun b hbsel hbD hbrank => ?_⟩
    exact (tie_eq_atomOrd_dstar P hV w (⟨cD, xb⟩ : P.toPoly.Atom)
      hDsel hDlabel hDmin (⟨c, i_tup⟩ : P.toPoly.Atom) ⟨hiv, hs⟩ hrank).mpr
      haod b hbsel hbD hbrank

/-- **The fibred TIE-point bridge** (F3.7 capstone, d*-route).  For every WRP-valid `P`: a uniform
period `(mG, pG)` and two `bFN`-eventually-periodic machine families — `GmU c` (the `selectedU`
gate) and `GmP c c'` (the boundary pair component) — such that on every `D`-present in-domain
copied slice the `fas`/TIE membership of a `U`-atom `i_tup` is decided by `GmU c` (`sel ∧ U`)
together with `GmP c dstar.1` fed `i_tup ++ dstar.2` (`atomOrd` against the single `wrpOrd`-minimal
equal-rank `D`-atom `dstar`).  NO `∀b` conjunction, NO clause activations, NO `mS`-free decode of
`dstar`'s prefix/suffix stretch coordinates — they are the pair component's HIGH marks.  The `∀b`
TIE form (which F3.9 consumes via `SliceFasTie.fas_member_eqRank`) is collapsed to `atomOrd … dstar`
by `tie_eq_atomOrd_dstar` and decided by `tie_gate_char`. -/
theorem tie_point_bridge_fibred (P : WRP.Presentation Step Step) (hV : P.Valid) :
    ∃ (mG pG : ℕ)
      (GmU : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (GmP : (c c' : Fin P.toPoly.K) →
        SliceMSO.DetAuto (MarkedN (P.toPoly.arity c + P.toPoly.arity c'))),
      1 ≤ pG ∧
      (∀ (c : Fin P.toPoly.K) (g : ℕ), mG ≤ g →
        (bFN (GmU c))^[g + pG] = (bFN (GmU c))^[g]) ∧
      (∀ (c c' : Fin P.toPoly.K) (g : ℕ), mG ≤ g →
        (bFN (GmP c c'))^[g + pG] = (bFN (GmP c c'))^[g]) ∧
      ∀ (mS : ℕ), 1 ≤ mS → ∀ n,
        P.toPoly.domain (copiedSlice mS n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
          P.toPoly.labelOf (copiedSlice mS n) a = D) →
        ∃ dstar : P.toPoly.Atom,
          P.toPoly.selectedAtom (copiedSlice mS n) dstar ∧
          P.toPoly.labelOf (copiedSlice mS n) dstar = D ∧
          P.rankOf (copiedSlice mS n) dstar = dstarRankGA_m P hV mS n ∧
          ∀ (c : Fin P.toPoly.K) (i_tup : Fin (P.toPoly.arity c) → ℕ),
            (∀ i, i_tup i < (copiedSlice mS n).length) →
            ((P.toPoly.sel c (copiedSlice mS n) i_tup ∧
                P.toPoly.labelOf (copiedSlice mS n) (⟨c, i_tup⟩ : P.toPoly.Atom) = U ∧
                P.rankOf (copiedSlice mS n) (⟨c, i_tup⟩ : P.toPoly.Atom) = dstarRankGA_m P hV mS n ∧
                ∀ b, P.toPoly.selectedAtom (copiedSlice mS n) b →
                  P.toPoly.labelOf (copiedSlice mS n) b = D →
                  P.rankOf (copiedSlice mS n) b = dstarRankGA_m P hV mS n →
                  P.toPoly.atomOrd (copiedSlice mS n) (⟨c, i_tup⟩ : P.toPoly.Atom) b)
             ↔ ((GmU c).accepts (markAtN _ (copiedSlice mS n) i_tup) ∧
                (GmP c dstar.1).accepts
                  (markAtN _ (copiedSlice mS n) (Fin.append i_tup dstar.2)) ∧
                P.rankOf (copiedSlice mS n) (⟨c, i_tup⟩ : P.toPoly.Atom)
                  = dstarRankGA_m P hV mS n)) := by
  classical
  choose mvU pvU hpvU hEPU using fun c : Fin P.toPoly.K =>
    SliceMarkN.bFN_func_iterate_eventuallyPeriodic (SliceFasGatesGA.selectedU_gate_GA P c).choose
  choose mvP pvP hpvP hEPP using fun x : Fin P.toPoly.K × Fin P.toPoly.K =>
    SliceMarkN.bFN_func_iterate_eventuallyPeriodic
      (CopiedTieGate.boundary_pair_component P x.1 x.2).choose
  set pG : ℕ := (∏ c, pvU c) * (∏ x, pvP x) with hpGdef
  set mG : ℕ := Finset.univ.sup mvU ⊔ Finset.univ.sup mvP with hmGdef
  have hposU : 0 < ∏ c, pvU c := Finset.prod_pos (fun c _ => hpvU c)
  have hposP : 0 < ∏ x, pvP x := Finset.prod_pos (fun x _ => hpvP x)
  refine ⟨mG, pG, fun c => (SliceFasGatesGA.selectedU_gate_GA P c).choose,
    fun c c' => (CopiedTieGate.boundary_pair_component P c c').choose,
    Nat.mul_pos hposU hposP, ?_, ?_, ?_⟩
  · -- GmU eventual periodicity
    intro c g hg
    obtain ⟨q, hq⟩ : pvU c ∣ pG := by
      rw [hpGdef]; exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ c)) _
    rw [hq, Nat.mul_comm]
    exact SliceGrowthCollapse.bFN_iterate_period_mul
      (SliceFasGatesGA.selectedU_gate_GA P c).choose (mvU c) (pvU c) (hEPU c) q g
      (le_trans (le_trans (Finset.le_sup (Finset.mem_univ c)) (le_max_left _ _)) hg)
  · -- GmP eventual periodicity
    intro c c' g hg
    obtain ⟨q, hq⟩ : pvP (c, c') ∣ pG := by
      rw [hpGdef]; exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) _
    rw [hq, Nat.mul_comm]
    exact SliceGrowthCollapse.bFN_iterate_period_mul
      (CopiedTieGate.boundary_pair_component P c c').choose (mvP (c, c')) (pvP (c, c'))
      (hEPP (c, c')) q g
      (le_trans (le_trans (Finset.le_sup (Finset.mem_univ (c, c'))) (le_max_right _ _)) hg)
  · -- the per-slice TIE characterization
    intro mS _hm n _hdom hDpres
    obtain ⟨dstar, hdsel, hdD, hdmin, hdrank⟩ :=
      dstarRankGA'_spec P hV (copiedSlice mS n) hDpres
    have hdrank' : P.rankOf (copiedSlice mS n) dstar = dstarRankGA_m P hV mS n := by
      rw [dstarRankGA_m]; exact hdrank.symm
    refine ⟨dstar, hdsel, hdD, hdrank', fun c i_tup hiv => ?_⟩
    simpa [hdrank'] using
      (tie_gate_char_of_minimal_dstar P hV c dstar.1 (copiedSlice mS n)
        i_tup dstar.2 hiv hdsel hdD hdmin)

end CopiedTieBridge
