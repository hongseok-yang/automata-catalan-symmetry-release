/-
# §9 d4c capstone — the arity-1 `cor:inverse-zeta-not-wrp` tower

Consumes the budgeted row-indexed bridge
`CopiedTieSlice.tie_point_bridge_fibred_clause_budgeted_indexed`.  Threaded with
the `Mbr` mS-floor: the counts and the row producer carry `Mbr`, and the
`cor:inverse-zeta-not-wrp` capstone applies the row at the section `m = p` with the period
`p ≥ Mbr` (so the section-vs-period arithmetic in
`pyramid_section_not_affine` is unchanged).
-/
import RequestProject.CopiedDischarge
import RequestProject.CopiedAffineAt
import RequestProject.CopiedCounts
import RequestProject.CopiedCountStrict
import RequestProject.CopiedCountTie
import RequestProject.CopiedGates
import RequestProject.InverseZetaNotWRP
import RequestProject.CopiedTieSlice

namespace CopiedD4

open WRP Step SlicePeriodStar SliceMSO MSOMarkN
open scoped Classical

/-- Pointwise, when `D` is present, the fas predicate = strict predicate + tie predicate.
(Verbatim from `fas_pred_split_GA`; no mS-floor.) -/
theorem fas_pred_split_fibred (P : WRP.Presentation Step Step) (hV : P.Valid)
    (mS n : ℕ)
    (hDp : ∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
      P.toPoly.labelOf (copiedSlice mS n) a = D)
    (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ)
    (hval : ∀ i, ī i < (copiedSlice mS n).length) :
    ((if (P.toPoly.sel c (copiedSlice mS n) ī
        ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
        ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
            (P.toPoly.labelOf (copiedSlice mS n) b = U
              ∨ P.wrpOrd (copiedSlice mS n) ⟨c, ī⟩ b)) then 1 else 0) : ℕ)
      = (if (P.toPoly.sel c (copiedSlice mS n) ī
            ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
            ∧ WRP.lexLt (P.rankOf (copiedSlice mS n) ⟨c, ī⟩)
                (CopiedDstar.dstarRankGA_m P hV mS n)) then 1 else 0)
        + (if (P.toPoly.sel c (copiedSlice mS n) ī
            ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
            ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ = CopiedDstar.dstarRankGA_m P hV mS n
            ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
                P.toPoly.labelOf (copiedSlice mS n) b = D →
                P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
                P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b) then 1 else 0) := by
  classical
  by_cases hsU : P.toPoly.sel c (copiedSlice mS n) ī
      ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
  · obtain ⟨dstar, hdsel, hdD, hdmin, hdrank⟩ :=
      CopiedDstar.dstarRankGA'_spec P hV (copiedSlice mS n) hDp
    have hdrank : CopiedDstar.dstarRankGA_m P hV mS n
        = P.rankOf (copiedSlice mS n) dstar := hdrank
    have hasel : P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ := ⟨hval, hsU.1⟩
    have hcoll := SliceOutput.fas_inner_collapse P hV (copiedSlice mS n) dstar hdsel hdD
      hdmin ⟨c, ī⟩ hasel
    rcases SliceLexOrder.lexLt_trichot (P.rankOf (copiedSlice mS n) ⟨c, ī⟩)
        (CopiedDstar.dstarRankGA_m P hV mS n) with hlt | heq | hgt
    · rw [if_pos ⟨hsU.1, hsU.2, hcoll.mpr (Or.inl (by rw [← hdrank]; exact hlt))⟩,
        if_pos ⟨hsU.1, hsU.2, hlt⟩,
        if_neg (fun hc => SliceFasCount.lexLt_ne hlt hc.2.2.1)]
    · have hrankeq : P.rankOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom)
          = P.rankOf (copiedSlice mS n) dstar := by rw [heq, hdrank]
      have hkey := SliceFasTie.fas_member_eqRank P hV (copiedSlice mS n) dstar hdsel hdD
        hdmin ⟨c, ī⟩ hasel hrankeq
      have hnB : ¬ (P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
          ∧ WRP.lexLt (P.rankOf (copiedSlice mS n) ⟨c, ī⟩)
              (CopiedDstar.dstarRankGA_m P hV mS n)) := by
        rintro ⟨-, -, hl⟩; rw [heq] at hl; exact SliceLexOrder.lexLt_irrefl _ hl
      by_cases hall : ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
          (P.toPoly.labelOf (copiedSlice mS n) b = U
            ∨ P.wrpOrd (copiedSlice mS n) ⟨c, ī⟩ b)
      · rw [if_pos ⟨hsU.1, hsU.2, hall⟩, if_neg hnB,
          if_pos ⟨hsU.1, hsU.2, heq, fun b hb hbD hbr =>
            (hkey.mp hall) b hb hbD (by rw [← hdrank]; exact hbr)⟩]
      · have hnA : ¬ (P.toPoly.sel c (copiedSlice mS n) ī
            ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
            ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
                (P.toPoly.labelOf (copiedSlice mS n) b = U
                  ∨ P.wrpOrd (copiedSlice mS n) ⟨c, ī⟩ b)) :=
          fun hc => hall hc.2.2
        have hnC : ¬ (P.toPoly.sel c (copiedSlice mS n) ī
            ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
            ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ = CopiedDstar.dstarRankGA_m P hV mS n
            ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
                P.toPoly.labelOf (copiedSlice mS n) b = D →
                P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
                P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b) :=
          fun hc => hall (hkey.mpr (fun b hb hbD hbr =>
            hc.2.2.2 b hb hbD (by rw [← hdrank] at hbr; exact hbr)))
        rw [if_neg hnA, if_neg hnB, if_neg hnC]
    · have hnA : ¬ (P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
              (P.toPoly.labelOf (copiedSlice mS n) b = U
                ∨ P.wrpOrd (copiedSlice mS n) ⟨c, ī⟩ b)) := by
        rintro ⟨-, -, hall⟩
        rcases hcoll.mp hall with hl | ⟨he, -⟩
        · refine SliceDstar.lexLt_asymm _ _ hgt ?_; rw [hdrank]; exact hl
        · refine SliceLexOrder.lexLt_irrefl (CopiedDstar.dstarRankGA_m P hV mS n) ?_
          have he' : P.rankOf (copiedSlice mS n) (⟨c, ī⟩ : P.toPoly.Atom)
              = CopiedDstar.dstarRankGA_m P hV mS n := by rw [he, ← hdrank]
          rw [he'] at hgt; exact hgt
      have hnB' : ¬ (P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
          ∧ WRP.lexLt (P.rankOf (copiedSlice mS n) ⟨c, ī⟩)
              (CopiedDstar.dstarRankGA_m P hV mS n)) := by
        rintro ⟨-, -, hl⟩; exact SliceDstar.lexLt_asymm _ _ hgt hl
      have hnC : ¬ (P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
          ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ = CopiedDstar.dstarRankGA_m P hV mS n
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
              P.toPoly.labelOf (copiedSlice mS n) b = D →
              P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b) := by
        rintro ⟨-, -, he, -⟩; rw [he] at hgt; exact SliceLexOrder.lexLt_irrefl _ hgt
      rw [if_neg hnA, if_neg hnB', if_neg hnC]
  · rw [if_neg (fun hc => hsU ⟨hc.1, hc.2.1⟩), if_neg (fun hc => hsU ⟨hc.1, hc.2.1⟩),
      if_neg (fun hc => hsU ⟨hc.1, hc.2.1⟩)]

/-- **The global selected-atom budget** at constant `C`: on every in-domain copied
slice, any `Nodup` list of selected atoms of one copy has length `≤ C · (mS + n + 1)`.

This is exactly what `CopiedDischarge.hbud_of_hgrow_m` produces from linear output
growth, and it is global in both `mS` and `n`. -/
def GlobalSelectedBudget (P : WRP.Presentation Step Step) (C : ℕ) : Prop :=
    ∀ mS n, P.toPoly.domain (copiedSlice mS n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
        l.length ≤ C * (mS + n + 1)

/-- The tie-count package needed by the copied-slice FAS assembly.  The existing
arity-1 bridge supplies this package; the general inverse-zeta route needs the
same package without an arity restriction.

The budget is consumed **globally**, before the period `p0` and the row threshold `Mbr`
are chosen: the general-arity supplier reads its period off the joint `(mS, n)` count
graph, so the period may not depend on the row.  The arity-1 route is unaffected — it
chooses its period from the bridge data and only ever uses the budget one row at a
time. -/
def TieCountAffineBudgeted (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ) : Prop :=
    GlobalSelectedBudget P C →
    ∃ (p0 Mbr : ℕ), 1 ≤ p0 ∧ 1 ≤ Mbr ∧ ∀ (mS : ℕ), Mbr ≤ mS →
      ∃ (tie' : ℕ → ℕ) (N : ℕ), AffineOnResiduesAt p0 tie' ∧
        ∀ n, N ≤ n → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          tie' n = ∑ c : Fin P.toPoly.K,
            ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
              Finset.range (copiedSlice mS n).length),
            if (P.toPoly.sel c (copiedSlice mS n) ī
                ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
                ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩
                    = CopiedDstar.dstarRankGA_m P hV mS n
                ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
                    P.toPoly.labelOf (copiedSlice mS n) b = D →
                    P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
                    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b) then 1 else 0

/-- Tie count from an abstract budgeted row-indexed tie bridge.  This is the
arity-free plug-in point for the future general bridge supplier. -/
theorem tie_count_affine_budgeted_of_bridge (P : WRP.Presentation Step Step) (hV : P.Valid)
    (C : ℕ) (hbridge : CopiedTieSlice.TiePointBridgeBudgetedIndexed P hV C) :
    TieCountAffineBudgeted P hV C := by
  intro hbud
  obtain ⟨B, Bh, M, _mthr, pG, q_U, q_D, Q, Ndeep, Mbr, hpG, hMbr1, Gidx, hbrIdx⟩ :=
    hbridge
  let ι := CopiedTieSlice.BridgeRowIndex P B Bh M pG q_U q_D Q Ndeep
  obtain ⟨p0, hp0, hcount⟩ :=
    CopiedCounts.tie_count_fibred_of_gate_budgeted_indexed P hV C ι pG hpG Gidx Mbr hMbr1 hbrIdx
  exact ⟨p0, Mbr, hp0, hMbr1, fun mS hm => hcount mS hm (fun n => hbud mS n)⟩

/-- **Whole-tuple d\*-route supplier interface** (the live arity-free target).

This is the d\*-route analogue of the supplier bundles: it isolates EXACTLY what is
left to close the general inverse-zeta bridge, phrased SEMANTICALLY so the hard `∀ b`
tie quantifier is already discharged on the consumer side.

A supplier provides a finite-index gate family `GdfaF` (marking only the `U`-tuple `ī`)
and, for each row `mS ≥ Mbr` under the selected-atom budget, a row index `idx` and a
threshold `Nbr` such that for every large `n` there is a `wrpOrd`-MINIMAL selected `D`
atom `dstar` of rank `dstarRankGA_m` whose `atomOrd` relation against any `U`-tuple `ī`
is decided by `GdfaF idx (n % pG) c`.  The minimal `dstar` is residue-determined: `idx`
is fixed before `n`, and the gate only depends on `n % pG`.

Compared with `CopiedTieSlice.TiePointBridgeBudgetedIndexedFinite`, the gate here only
decides `sel ∧ U ∧ atomOrd ī dstar` against ONE explicit residue-determined `dstar` — a
single `boundary_pair_component`-style pairwise order check with the whole `dstar` tuple
landmark-decoded — instead of the universally quantified `∀ b` tie condition.  The two
genuine arity-free sub-problems this bundles (both open here)
are: (1) residue-determinacy of the minimal `dstar` cell descriptor (so `idx`/`n % pG`
pin it down for all large `n`); and (2) a whole-tuple landmark-decode `atomOrd` gate for
that fixed cell.  Sub-problem (2) becomes tractable precisely because (1) fixes the cell
base, dissolving the mixed-cell decode obstruction (cluster coordinates no
longer move with the counting base). -/
def WholeTupleDstarAtomOrdGate (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ) :
    Prop :=
  ∃ (pG Mbr : ℕ), 1 ≤ pG ∧ 1 ≤ Mbr ∧
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (GdfaF : ι → ℕ →
        (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))),
      ∀ (mS : ℕ), Mbr ≤ mS →
        (∀ n, P.toPoly.domain (copiedSlice mS n) →
          ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
            (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
            l.length ≤ C * (mS + n + 1)) →
        ∃ (idx : ι) (Nbr : ℕ), ∀ n, Nbr ≤ n → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          ∃ dstar : P.toPoly.Atom,
            P.toPoly.selectedAtom (copiedSlice mS n) dstar ∧
            P.toPoly.labelOf (copiedSlice mS n) dstar = D ∧
            P.rankOf (copiedSlice mS n) dstar = CopiedDstar.dstarRankGA_m P hV mS n ∧
            (∀ b, P.toPoly.selectedAtom (copiedSlice mS n) b →
              P.toPoly.labelOf (copiedSlice mS n) b = D →
              dstar = b ∨ P.wrpOrd (copiedSlice mS n) dstar b) ∧
            ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
              (∀ i, ī i < (copiedSlice mS n).length) →
              ((GdfaF idx (n % pG) c).accepts
                  (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)
               ↔ (P.toPoly.sel c (copiedSlice mS n) ī
                  ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
                  ∧ P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ dstar))

/-- Tie count from the canonical zero-base update supplier bundle, using the
direct arbitrary-arity bridge path. -/
theorem tie_count_affine_budgeted_of_update_zero_bundle
    (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ)
    (hUpdate : CopiedTieSlice.BridgeUpdateZeroSupplierBundle P hV) :
    TieCountAffineBudgeted P hV C :=
  tie_count_affine_budgeted_of_bridge P hV C
    (CopiedTieSlice.tie_point_bridge_budgeted_indexed_of_update_zero_bundle P hV C hUpdate)

/-- The FAS-count package produced once total, strict, and tie counts are assembled.
The budget is consumed globally, matching `TieCountAffineBudgeted`. -/
def FasCountAffineBudgeted (P : WRP.Presentation Step Step) (_hV : P.Valid) (C : ℕ) : Prop :=
    GlobalSelectedBudget P C →
    ∃ (p0 Mbr : ℕ), 1 ≤ p0 ∧ 1 ≤ Mbr ∧ ∀ (mS : ℕ), Mbr ≤ mS →
      ∃ (fas' : ℕ → ℕ) (N : ℕ), AffineOnResiduesAt p0 fas' ∧
        ∀ n, N ≤ n → fas' n = CopiedDischarge.gatedFasCountGA_m P mS n

/-- **The strict+tie assembly**, factored through the tie-count package.  This
part is arity-free: total and strict counts are already general arity, and all
arity dependence is isolated in the supplier of `TieCountAffineBudgeted`. -/
theorem fas_count_affine_fibred_budgeted_of_tie (P : WRP.Presentation Step Step)
    (hV : P.Valid) (C : ℕ) (htieBudgeted : TieCountAffineBudgeted P hV C) :
    FasCountAffineBudgeted P hV C := by
  classical
  intro hbud
  obtain ⟨pt, hpt, htot⟩ := CopiedCounts.totalSelectedU_count_fibred P
  obtain ⟨ps, hps, hstrict⟩ := CopiedCounts.strict_count_fibred P hV
  obtain ⟨pti, Mbr, hpti, hMbr1, htie⟩ := htieBudgeted hbud
  obtain ⟨mdom, pdom, hpdom, hdomEP⟩ := CopiedGates.domain_EP_fibred P
  obtain ⟨mDp, pDp, hpDp, hDpEP⟩ := CopiedGates.Dpresent_EP_fibred P
  set p0 : ℕ := pt * ps * pti * pdom * pDp with hp0def
  have hp0 : 1 ≤ p0 := by
    rw [hp0def]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hpt hps) hpti) hpdom) hpDp
  have hpt0 : pt ∣ p0 := by
    rw [hp0def]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_right pt ps) pti) pdom) pDp
  have hps0 : ps ∣ p0 := by
    rw [hp0def]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_left ps pt) pti) pdom) pDp
  have hpti0 : pti ∣ p0 := by
    rw [hp0def]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_left pti (pt * ps)) pdom) pDp
  have hpdom0 : pdom ∣ p0 := by
    rw [hp0def]
    exact dvd_mul_of_dvd_left (dvd_mul_left pdom (pt * ps * pti)) pDp
  have hpDp0 : pDp ∣ p0 := by
    rw [hp0def]; exact dvd_mul_left pDp (pt * ps * pti * pdom)
  refine ⟨p0, Mbr, hp0, hMbr1, fun mS hm => ?_⟩
  have h1mS : 1 ≤ mS := le_trans hMbr1 hm
  obtain ⟨tot', Nt, htotA, htotE⟩ := htot C mS h1mS (fun n => hbud mS n)
  obtain ⟨strict', Ns, hstA, hstE⟩ := hstrict C mS h1mS (fun n => hbud mS n)
  obtain ⟨tie', Nti, htiA, htiE⟩ := htie mS hm
  -- lift the three affine pieces to the merged period p0
  have htotA' : AffineOnResiduesAt p0 tot' := htotA.of_dvd hpt hpt0 hp0
  have hstA' : AffineOnResiduesAt p0 strict' := hstA.of_dvd hps hps0 hp0
  have htiA' : AffineOnResiduesAt p0 tie' := htiA.of_dvd hpti hpti0 hp0
  -- domain / D-present eventual periodicity at p0 (for this mS)
  have hdomEP0 : SliceOrder.EventuallyPeriodic
      (fun n => P.toPoly.domain (copiedSlice mS n)) p0 :=
    SliceDstar.EP_of_dvd ⟨mdom, fun n hn => hdomEP mS h1mS n hn⟩ hpdom0
  have hDpEP0 : SliceOrder.EventuallyPeriodic
      (fun n => ∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
        ∧ P.toPoly.labelOf (copiedSlice mS n) a = D) p0 :=
    SliceDstar.EP_of_dvd ⟨mDp, fun n hn => hDpEP mS h1mS n hn⟩ hpDp0
  set sel3 : ℕ → Bool × Bool := fun n =>
    (decide (P.toPoly.domain (copiedSlice mS n)),
     decide (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
       ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)) with hsel3def
  set f3 : Bool × Bool → ℕ → ℕ := fun bb n =>
    if bb.1 then (if bb.2 then strict' n + tie' n else tot' n) else 0 with hf3def
  refine ⟨fun n => f3 (sel3 n) n, Nt + Ns + Nti, ?_, ?_⟩
  · -- affine via select
    refine AffineOnResiduesAt.select Finset.univ f3 sel3 p0 hp0 (fun bb _ => ?_)
      (fun n => Finset.mem_univ _) (fun bb _ => ?_)
    · rw [hf3def]
      rcases bb with ⟨b1, b2⟩
      rcases b1 with _ | _
      · exact ⟨0, fun j _ => ⟨0, 0, fun k => by simp⟩⟩
      · rcases b2 with _ | _
        · exact htotA'
        · exact AffineOnResiduesAt.add hp0 hstA' htiA'
    · -- the fibre sel3 n = bb is EP at p0
      rcases bb with ⟨b1, b2⟩
      have h1 : SliceOrder.EventuallyPeriodic (fun n =>
          decide (P.toPoly.domain (copiedSlice mS n)) = b1) p0 := by
        rcases b1 with _ | _
        · refine (SliceDstarCore.EP_not hdomEP0).congr (fun n => ?_)
          rw [decide_eq_false_iff_not]
        · refine hdomEP0.congr (fun n => ?_)
          rw [decide_eq_true_eq]
      have h2 : SliceOrder.EventuallyPeriodic (fun n =>
          decide (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
            ∧ P.toPoly.labelOf (copiedSlice mS n) a = D) = b2) p0 := by
        rcases b2 with _ | _
        · refine (SliceDstarCore.EP_not hDpEP0).congr (fun n => ?_)
          rw [decide_eq_false_iff_not]
        · refine hDpEP0.congr (fun n => ?_)
          rw [decide_eq_true_eq]
      refine (h1.and h2).congr (fun n => ?_)
      rw [hsel3def]
      constructor
      · rintro ⟨ha, hb⟩; exact Prod.ext ha hb
      · intro h; exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · -- agreement
    intro n hn
    by_cases hdom : P.toPoly.domain (copiedSlice mS n)
    · by_cases hDp : ∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D
      · have hsel3n : sel3 n = (true, true) := by
          rw [hsel3def]; simp only []; rw [decide_eq_true hdom, decide_eq_true hDp]
        simp only []
        rw [hsel3n, hf3def]
        simp only [if_true]
        rw [CopiedDischarge.gatedFasCountGA_m, if_pos hdom,
          CopiedDischarge.fasCountGA_m, CopiedDischarge.fasCount',
          hstE n (by omega) hdom hDp, htiE n (by omega) hdom hDp,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun ī hī => ?_)
        have hval : ∀ i, ī i < (copiedSlice mS n).length := by
          rw [Fintype.mem_piFinset] at hī
          intro i; have := hī i; rwa [Finset.mem_range] at this
        exact (fas_pred_split_fibred P hV mS n hDp c ī hval).symm
      · have hsel3n : sel3 n = (true, false) := by
          rw [hsel3def]; simp only []; rw [decide_eq_true hdom, decide_eq_false hDp]
        simp only []
        rw [hsel3n, hf3def]
        simp only [if_true]
        rw [if_neg (Bool.false_ne_true),
          CopiedDischarge.gatedFasCountGA_m, if_pos hdom,
          CopiedDischarge.fasCountGA_m, CopiedDischarge.fasCount', htotE n (by omega) hdom]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        refine Finset.sum_congr rfl (fun ī hī => ?_)
        by_cases hsU : P.toPoly.sel c (copiedSlice mS n) ī
            ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
        · have hall : ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
              (P.toPoly.labelOf (copiedSlice mS n) b = U
                ∨ P.wrpOrd (copiedSlice mS n) ⟨c, ī⟩ b) := by
            intro b hb
            rcases hlb : P.toPoly.labelOf (copiedSlice mS n) b with _ | _
            · exact Or.inl rfl
            · exact absurd ⟨b, hb, hlb⟩ hDp
          rw [if_pos hsU, if_pos ⟨hsU.1, hsU.2, hall⟩]
        · rw [if_neg hsU, if_neg (fun hc => hsU ⟨hc.1, hc.2.1⟩)]
    · have hsel3n : (sel3 n).1 = false := by
        rw [hsel3def]; simp only []; rw [decide_eq_false hdom]
      simp only []
      rw [hf3def]
      simp only []
      rw [hsel3n, if_neg (Bool.false_ne_true),
        CopiedDischarge.gatedFasCountGA_m, if_neg hdom]

/-- **Row-affine from a threshold** (the `Mbr`-floored variant of `RowAffine`): the
first-ascent of `T (copiedSlice m ·)` is eventually periodic-affine in the column, for
every section `m ≥ Mbr`, with a fixed period `p ≥ Mbr`. -/
def RowAffineFrom (Mbr : ℕ) (T : List Step → Option (List Step)) : Prop :=
  ∃ p, Mbr ≤ p ∧ 1 ≤ p ∧ ∀ m, Mbr ≤ m → ∃ N, ∀ j, j < p → ∃ b s : ℕ,
    ∀ k out, T (copiedSlice m (N + j + p * k)) = some out →
      firstAscent out = b + k * s

/-- The finite-row complement needed to turn a large-row `RowAffineFrom` theorem
into the public `RowAffine` interface: below `Mbr`, the same period `p` works for
every row. -/
def RowAffineBelow (Mbr p : ℕ) (T : List Step → Option (List Step)) : Prop :=
  ∀ m, 1 ≤ m → m < Mbr → ∃ N, ∀ j, j < p → ∃ b s : ℕ,
    ∀ k out, T (copiedSlice m (N + j + p * k)) = some out →
      firstAscent out = b + k * s

/-- Row-affineness for one fixed row at one fixed period. -/
def RowAffineAtPeriod (p m : ℕ) (T : List Step → Option (List Step)) : Prop :=
  ∃ N, ∀ j, j < p → ∃ b s : ℕ,
    ∀ k out, T (copiedSlice m (N + j + p * k)) = some out →
      firstAscent out = b + k * s

/-- A finite-row complement in its natural form: each row below `Mbr` may come
with its own period.  `rowAffine_of_rowAffineFrom_of_rowsBelow` enlarges the
large-row period by the finite product of these row periods. -/
def RowAffineRowsBelow (Mbr : ℕ) (T : List Step → Option (List Step)) : Prop :=
  ∀ m, 1 ≤ m → m < Mbr → ∃ p, 1 ≤ p ∧ RowAffineAtPeriod p m T

/-- Lift a fixed-row affine description from a period to any positive multiple. -/
theorem rowAffineAtPeriod_of_dvd {p p' m : ℕ} {T : List Step → Option (List Step)}
    (hp : 1 ≤ p) (hdvd : p ∣ p') (hp' : 1 ≤ p')
    (hrow : RowAffineAtPeriod p m T) :
    RowAffineAtPeriod p' m T := by
  obtain ⟨r, rfl⟩ := hdvd
  obtain ⟨N, hN⟩ := hrow
  refine ⟨N, fun j hj => ?_⟩
  set j0 : ℕ := j % p with hj0_def
  set k0 : ℕ := j / p with hk0_def
  have hj0 : j0 < p := by
    rw [hj0_def]
    exact Nat.mod_lt _ (by omega)
  obtain ⟨b, s, hbs⟩ := hN j0 hj0
  refine ⟨b + k0 * s, r * s, fun k out hout => ?_⟩
  have hdm : p * k0 + j0 = j := by
    rw [hk0_def, hj0_def]
    exact Nat.div_add_mod j p
  have harg : N + j + p * r * k = N + j0 + p * (k0 + r * k) := by
    rw [← hdm]
    ring
  have hfirst := hbs (k0 + r * k) out (by rwa [harg] at hout)
  rw [hfirst]
  ring

/-- Combine a large-row theorem with row-wise affine descriptions for the
finite set of rows below the large-row floor.  Unlike `RowAffineBelow`, the
finite complement may choose a different period for each small row; the final
period is the large-row period times their finite product. -/
theorem rowAffine_of_rowAffineFrom_of_rowsBelow {Mbr : ℕ}
    {T : List Step → Option (List Step)}
    (hfrom : RowAffineFrom Mbr T)
    (hbelow : RowAffineRowsBelow Mbr T) :
    RowAffine T := by
  classical
  obtain ⟨pLarge, _hMbrp, hpLarge, hlarge⟩ := hfrom
  let pBelow : Fin Mbr → ℕ := fun r =>
    if hr : 1 ≤ r.1 then Classical.choose (hbelow r.1 hr r.2) else 1
  have hpBelow : ∀ r : Fin Mbr, 1 ≤ pBelow r := by
    intro r
    dsimp [pBelow]
    by_cases hr : 1 ≤ r.1
    · rw [dif_pos hr]
      exact (Classical.choose_spec (hbelow r.1 hr r.2)).1
    · rw [dif_neg hr]
  set pFin : ℕ := ∏ r : Fin Mbr, pBelow r with hpFin_def
  have hpFin : 1 ≤ pFin := by
    rw [hpFin_def]
    exact Finset.prod_pos (fun r _ => Nat.lt_of_lt_of_le Nat.zero_lt_one (hpBelow r))
  set pFinal : ℕ := pLarge * pFin with hpFinal_def
  have hpFinal : 1 ≤ pFinal := by
    rw [hpFinal_def]
    exact Nat.mul_pos hpLarge hpFin
  refine ⟨pFinal, hpFinal, fun m hm => ?_⟩
  by_cases hM : Mbr ≤ m
  · have hdvd : pLarge ∣ pFinal := by
      rw [hpFinal_def]
      exact dvd_mul_right pLarge pFin
    exact rowAffineAtPeriod_of_dvd hpLarge hdvd hpFinal (hlarge m hM)
  · have hlt : m < Mbr := Nat.lt_of_not_ge hM
    let r : Fin Mbr := ⟨m, hlt⟩
    have hrowBase : RowAffineAtPeriod (pBelow r) m T := by
      dsimp [pBelow, r]
      rw [dif_pos hm]
      exact (Classical.choose_spec (hbelow m hm hlt)).2
    have hdvdFin : pBelow r ∣ pFin := by
      rw [hpFin_def]
      exact Finset.dvd_prod_of_mem pBelow (Finset.mem_univ r)
    have hdvd : pBelow r ∣ pFinal := by
      rw [hpFinal_def]
      exact dvd_trans hdvdFin (dvd_mul_left pFin pLarge)
    exact rowAffineAtPeriod_of_dvd (hpBelow r) hdvd hpFinal hrowBase

/-- **The `RowAffineFrom` producer**, factored through the FAS-count package.
Period chosen as `p0 * Mbr ≥ Mbr` (a multiple of the assembly period `p0`). -/
theorem copied_slice_row_affine_of_fas (P : WRP.Presentation Step Step) (hV : P.Valid)
    (T : List Step → Option (List Step))
    (hPT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (hgrow : ∃ C, ∀ mS n out, T (copiedSlice mS n) = some out →
      out.length ≤ C * (mS + n + 1))
    (hfasBudgeted : ∀ C, FasCountAffineBudgeted P hV C) :
    ∃ Mbr, 1 ≤ Mbr ∧ RowAffineFrom Mbr T := by
  obtain ⟨C, hC⟩ := hgrow
  have hbud : GlobalSelectedBudget P C := CopiedDischarge.hbud_of_hgrow_m P hV T C hPT hC
  obtain ⟨p0, Mbr, hp0, hMbr1, hfas⟩ := hfasBudgeted C hbud
  have hpMbr : 1 ≤ p0 * Mbr := Nat.mul_pos hp0 hMbr1
  refine ⟨Mbr, hMbr1, p0 * Mbr, Nat.le_mul_of_pos_left Mbr hp0, hpMbr, fun m hm => ?_⟩
  obtain ⟨fas', N, hAff, hAgree⟩ := hfas m hm
  have hAff' : AffineOnResiduesAt (p0 * Mbr) fas' :=
    hAff.of_dvd hp0 (dvd_mul_right p0 Mbr) hpMbr
  obtain ⟨N', hNN', hrebase⟩ := SlicePeriodStar.AffineOnResiduesAt.rebase hpMbr hAff' N
  refine ⟨N', fun j hj => ?_⟩
  obtain ⟨b, s, hbs⟩ := hrebase j hj
  refine ⟨b, s, fun k out hout => ?_⟩
  have hdom : P.toPoly.domain (copiedSlice m (N' + j + (p0 * Mbr) * k)) := ((hPT _ _).mp hout).1
  have hisout : P.IsOutput (copiedSlice m (N' + j + (p0 * Mbr) * k)) out := ((hPT _ _).mp hout).2
  rw [CopiedDischarge.fas_eq_firstAscent_out' P hV _ out hisout]
  show CopiedDischarge.fasCountGA_m P m (N' + j + (p0 * Mbr) * k) = b + k * s
  rw [show CopiedDischarge.fasCountGA_m P m (N' + j + (p0 * Mbr) * k)
        = CopiedDischarge.gatedFasCountGA_m P m (N' + j + (p0 * Mbr) * k) from by
      rw [CopiedDischarge.gatedFasCountGA_m, if_pos hdom]]
  rw [← hAgree (N' + j + (p0 * Mbr) * k) (by omega)]
  exact hbs k

/-- `RowAffineFrom` from the abstract tie-count bridge package. -/
theorem copied_slice_row_affine_of_tie (P : WRP.Presentation Step Step) (hV : P.Valid)
    (T : List Step → Option (List Step))
    (hPT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (hgrow : ∃ C, ∀ mS n out, T (copiedSlice mS n) = some out →
      out.length ≤ C * (mS + n + 1))
    (htieBudgeted : ∀ C, TieCountAffineBudgeted P hV C) :
    ∃ Mbr, 1 ≤ Mbr ∧ RowAffineFrom Mbr T :=
  copied_slice_row_affine_of_fas P hV T hPT hgrow
    (fun C => fas_count_affine_fibred_budgeted_of_tie P hV C (htieBudgeted C))

/-- `RowAffineFrom` from the canonical zero-base update supplier bundle, using
the direct bridge package. -/
theorem copied_slice_row_affine_of_update_zero_bundle
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (T : List Step → Option (List Step))
    (hPT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (hgrow : ∃ C, ∀ mS n out, T (copiedSlice mS n) = some out →
      out.length ≤ C * (mS + n + 1))
    (hUpdate : CopiedTieSlice.BridgeUpdateZeroSupplierBundle P hV) :
    ∃ Mbr, 1 ≤ Mbr ∧ RowAffineFrom Mbr T :=
  copied_slice_row_affine_of_tie P hV T hPT hgrow
    (fun C => tie_count_affine_budgeted_of_update_zero_bundle P hV C hUpdate)

/-- **The `RowAffineFrom` producer** (arity-1), from the assembly. -/
theorem copied_slice_row_affine (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity1 : ∀ c, P.toPoly.arity c = 1)
    (T : List Step → Option (List Step))
    (hPT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (hgrow : ∃ C, ∀ mS n out, T (copiedSlice mS n) = some out →
      out.length ≤ C * (mS + n + 1)) :
    ∃ Mbr, 1 ≤ Mbr ∧ RowAffineFrom Mbr T :=
  copied_slice_row_affine_of_update_zero_bundle P hV T hPT hgrow
    (CopiedTieSlice.bridgeUpdateZeroSupplierBundle_of_arity_one P hV harity1)

/-- Large-row row-affinity at the public `WRP.IsWRP` boundary, conditional on
an arbitrary-arity FAS-count package. -/
theorem rowAffineFrom_of_isWRP_of_fas
    (hFas : ∀ (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ),
      FasCountAffineBudgeted P hV C)
    (T : List Step → Option (List Step)) (hT : WRP.IsWRP T)
    (hgrow : ∃ C, ∀ mS n out, T (copiedSlice mS n) = some out →
      out.length ≤ C * (mS + n + 1)) :
    ∃ Mbr, 1 ≤ Mbr ∧ RowAffineFrom Mbr T := by
  obtain ⟨P, hV, hPT⟩ := hT
  exact copied_slice_row_affine_of_fas P hV T hPT hgrow (fun C => hFas P hV C)

/-- The inverse-zeta arithmetic only needs the large-row fragment: after
`RowAffineFrom` chooses a period `p ≥ Mbr`, the contradiction is taken on row
`m = p`, so no finite-row complement is needed for the non-WRP corollary. -/
theorem inverse_zeta_not_wrp_of_rowAffineFrom
    (hrow : ∀ T : List Step → Option (List Step), WRP.IsWRP T →
      (∀ m n, 1 ≤ m → ∃ out, T (copiedSlice m n) = some out) →
      (∃ C, ∀ m n out, T (copiedSlice m n) = some out →
        out.length ≤ C * (m + n + 1)) →
      ∃ Mbr, 1 ≤ Mbr ∧ RowAffineFrom Mbr T) :
    ¬ ∃ T : List Step → Option (List Step),
      WRP.IsWRP T ∧ ∀ P, IsDyckPath P → T (zetaMap P) = some P := by
  rintro ⟨T, hT, hinv⟩
  have hTW : ∀ m n, T (copiedSlice m n) = some (pyramidRow m n) := by
    intro m n
    rw [← zetaMap_pyramidRow m n]
    exact hinv (pyramidRow m n) (isDyckPath_pyramidRow m n)
  have htot : ∀ m n, 1 ≤ m → ∃ out, T (copiedSlice m n) = some out :=
    fun m n _ => ⟨pyramidRow m n, hTW m n⟩
  have hgrow : ∃ C, ∀ m n out, T (copiedSlice m n) = some out →
      out.length ≤ C * (m + n + 1) := by
    refine ⟨2, fun m n out hout => ?_⟩
    rw [hTW m n] at hout
    obtain rfl := Option.some.inj hout.symm
    rw [length_pyramidRow]
    omega
  obtain ⟨Mbr, _hMbr1, p, hMbrp, hp, hrowp⟩ := hrow T hT htot hgrow
  obtain ⟨N, hN⟩ := hrowp p hMbrp
  obtain ⟨b, s, hbs⟩ := hN 0 (by omega)
  refine pyramid_section_not_affine p (N + 0) b s hp (fun k => ?_)
  have := hbs k (pyramidRow p (N + 0 + p * k)) (hTW p (N + 0 + p * k))
  rw [firstAscent_pyramidRow] at this
  exact this

/-- Conditional inverse-zeta non-WRP from the arbitrary-arity FAS-count package,
using only the large-row `RowAffineFrom` producer. -/
theorem inverse_zeta_not_wrp_of_fas
    (hFas : ∀ (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ),
      FasCountAffineBudgeted P hV C) :
    ¬ ∃ T : List Step → Option (List Step),
      WRP.IsWRP T ∧ ∀ P, IsDyckPath P → T (zetaMap P) = some P :=
  inverse_zeta_not_wrp_of_rowAffineFrom
    (fun T hT _htot hgrow => rowAffineFrom_of_isWRP_of_fas hFas T hT hgrow)

/-- **`cor:inverse-zeta-not-wrp`, arity-1 form**: no WRP transduction realised by an ARITY-1
presentation is a left inverse of the zeta map on Dyck paths. -/
theorem inverse_zeta_not_wrp_arity1 :
    ¬ ∃ (P : WRP.Presentation Step Step) (T : List Step → Option (List Step)),
      P.Valid ∧ (∀ c, P.toPoly.arity c = 1) ∧
      (∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)) ∧
      (∀ Q, IsDyckPath Q → T (zetaMap Q) = some Q) := by
  rintro ⟨P, T, hV, harity1, hPT, hinv⟩
  have hTW : ∀ m n, T (copiedSlice m n) = some (pyramidRow m n) := by
    intro m n
    rw [← zetaMap_pyramidRow m n]
    exact hinv (pyramidRow m n) (isDyckPath_pyramidRow m n)
  have hgrow : ∃ C, ∀ m n out, T (copiedSlice m n) = some out →
      out.length ≤ C * (m + n + 1) := by
    refine ⟨2, fun m n out hout => ?_⟩
    rw [hTW m n] at hout
    obtain rfl := Option.some.inj hout.symm
    rw [length_pyramidRow]; omega
  obtain ⟨Mbr, hMbr1, p, hMbrp, hp, hrowp⟩ := copied_slice_row_affine P hV harity1 T hPT hgrow
  obtain ⟨N, hN⟩ := hrowp p hMbrp
  obtain ⟨b, s, hbs⟩ := hN 0 (by omega)
  refine pyramid_section_not_affine p (N + 0) b s hp (fun k => ?_)
  have := hbs k (pyramidRow p (N + 0 + p * k)) (hTW p (N + 0 + p * k))
  rw [firstAscent_pyramidRow] at this
  exact this

end CopiedD4
