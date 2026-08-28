/-
# The paper-exact WRP classes: total tie-orders (and the revision's `def:wrp`)

`paper-full-new.tex` requires the tie-order `χ` of a polyregular presentation to
be a strict total order on the selected atoms **by itself** (`def:polyregular`
(v), line 961: `χ` "linearly orders the selected atoms"), and `def:wrp` (line
1217) inherits the requirement, remarking "Since `χ` is a strict total order on
selected atoms, `≺` is also a strict total order."  The Lean class `WRP.IsWRP`
deliberately weakens this (deviation A2 of `PAPER_DEVIATIONS.md`): its
`WRP.Presentation.Valid` asks totality only of the *combined* order `≺`
(`wrpOrd`), so `IsWRP` quantifies over a superset of the paper's class and the
negative theorems are stronger.

This file removes the statement-level deviation by naming the paper's exact
classes and proving the bridges:

* `WRP.lexLt_irrefl` / `lexLt_trans` / `lexLt_trichot` — the lexicographic
  order on `Fin d → ℤ` is a strict total order (general order theory);
* `WRP.Presentation.valid_of_polyValid` — **the paper's remark in `def:wrp`**:
  if `χ` is a strict total order on selected atoms then so is `≺`;
* `WRP.IsWRPTieTotal` — the previous draft's `def:wrp` class (`χ` total,
  arities unconstrained), with `IsWRPTieTotal ⊆ IsWRP`;
* `WRP.IsWRPPaper` — **the revision's `def:wrp` class verbatim**: `χ` a strict
  total order *and* every copy of arity `k_c ≥ 1`
  (`Polyreg.Presentation.ArityPos`), with
  `IsWRPPaper ⊆ IsWRPTieTotal ∩ IsWRPPos ⊆ IsWRP`.  Every negative theorem
  over `IsWRP` therefore yields the paper's statement a fortiori
  (`WRPPaperTheorems.lean`), and the memberships below put the positive
  results in the paper's own class;
* `Polyreg.Presentation.IsScanOrder.valid` — a scan tie-order is a strict
  total order on **all** atoms, so `sRR₁ = SWR` presentations are paper-exact:
  `IsSRR1.isWRPTieTotal`, `IsSRR1.isWRPPaper`;
* conservativity (`prop:conservative`) into the paper classes:
  `isWRPTieTotal_of_isPolyregular`, `isWRPPaper_of_isPolyregularPos`;
* the paper-exact positive memberships `zetaSweep_isWRPPaper`,
  `heightSweep_isWRPPaper`, `additiveSweep_isWRPPaper`.

Everything here is axiom-clean.
-/
import RequestProject.WRPArityPos

open MSO Step

namespace WRP

variable {Alpha Gamma : Type*}

/-! ## The lexicographic order on `Fin d → ℤ` is a strict total order -/

theorem lexLt_irrefl {d : ℕ} (x : Fin d → ℤ) : ¬ lexLt x x := by
  rintro ⟨i, -, hlt⟩
  exact lt_irrefl _ hlt

theorem lexLt_trans {d : ℕ} {x y z : Fin d → ℤ}
    (hxy : lexLt x y) (hyz : lexLt y z) : lexLt x z := by
  obtain ⟨i, hpi, hli⟩ := hxy
  obtain ⟨j, hpj, hlj⟩ := hyz
  rcases lt_trichotomy i j with h | rfl | h
  · exact ⟨i, fun k hk => (hpi k hk).trans (hpj k (hk.trans h)),
      by rw [← hpj i h]; exact hli⟩
  · exact ⟨i, fun k hk => (hpi k hk).trans (hpj k hk), hli.trans hlj⟩
  · exact ⟨j, fun k hk => (hpi k (hk.trans h)).trans (hpj k hk),
      by rw [hpi j h]; exact hlj⟩

theorem lexLt_trichot {d : ℕ} (x y : Fin d → ℤ) :
    lexLt x y ∨ x = y ∨ lexLt y x := by
  by_cases hxy : x = y
  · exact Or.inr (Or.inl hxy)
  · have hS : (Finset.univ.filter (fun i : Fin d => x i ≠ y i)).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
      exact hxy (funext fun i => not_not.mp (h (Finset.mem_univ i)))
    set i₀ := (Finset.univ.filter (fun i : Fin d => x i ≠ y i)).min' hS with hi₀
    have hne : x i₀ ≠ y i₀ :=
      (Finset.mem_filter.mp ((Finset.univ.filter _).min'_mem hS)).2
    have hpre : ∀ j, j < i₀ → x j = y j := by
      intro j hj
      by_contra hne'
      have hle := (Finset.univ.filter (fun i : Fin d => x i ≠ y i)).min'_le j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne'⟩)
      rw [← hi₀] at hle
      exact absurd hj (not_lt.mpr hle)
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨i₀, hpre, h⟩
    · exact Or.inr (Or.inr ⟨i₀, fun j hj => (hpre j hj).symm, h⟩)

/-! ## The paper's remark in `def:wrp`: `χ` total ⟹ `≺` total -/

/-- **`def:wrp` (paper-full-new.tex): "Since `χ` is a strict total
order on selected atoms, `≺` is also a strict total order."**  If the
underlying polyregular presentation is valid in the paper's sense (the
tie-order `χ` is a strict total order on selected atoms), then the WRP
presentation is valid in the Lean sense (the combined order `≺` is a strict
total order on selected atoms). -/
theorem Presentation.valid_of_polyValid (P : Presentation Alpha Gamma)
    (h : P.toPoly.Valid) : P.Valid where
  irrefl := fun w a ha => by
    rintro (hlex | ⟨-, hord⟩)
    · exact lexLt_irrefl _ hlex
    · exact h.irrefl w a ha hord
  trans := fun w a b c ha hb hc hab hbc => by
    rcases hab with hlex | ⟨heq, hord⟩ <;> rcases hbc with hlex' | ⟨heq', hord'⟩
    · exact Or.inl (lexLt_trans hlex hlex')
    · exact Or.inl (heq' ▸ hlex)
    · exact Or.inl (heq ▸ hlex')
    · exact Or.inr ⟨heq.trans heq', h.trans w a b c ha hb hc hord hord'⟩
  trichot := fun w a b ha hb => by
    rcases lexLt_trichot (P.rankOf w a) (P.rankOf w b) with hlex | heq | hlex
    · exact Or.inl (Or.inl hlex)
    · rcases h.trichot w a b ha hb with hord | rfl | hord
      · exact Or.inl (Or.inr ⟨heq, hord⟩)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨heq.symm, hord⟩))
    · exact Or.inr (Or.inr (Or.inl hlex))

/-! ## The paper-exact classes -/

/-- **The previous draft's `def:wrp` class**: realised by a WRP presentation
whose tie-order `χ` is itself a strict total order on selected atoms
(`Polyreg.Presentation.Valid`), with arities unconstrained.  This is the class
`PAPER_DEVIATIONS.md` A2 contrasts with the deliberately larger `IsWRP`. -/
def IsWRPTieTotal (T : List Alpha → Option (List Gamma)) : Prop :=
  ∃ P : Presentation Alpha Gamma, P.toPoly.Valid ∧
    ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)

/-- **The revision's `def:wrp` class verbatim** (paper-full-new.tex):
realised by a WRP presentation over a paper-valid polyregular presentation —
the tie-order `χ` is a strict total order on selected atoms (`def:polyregular`
(v)) and every copy has arity `k_c ≥ 1` (`def:polyregular` (i)). -/
def IsWRPPaper (T : List Alpha → Option (List Gamma)) : Prop :=
  ∃ P : Presentation Alpha Gamma, P.toPoly.Valid ∧ P.toPoly.ArityPos ∧
    ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)

/-- `χ`-total membership is Lean membership: the paper's class is contained in
the Lean class, so every negative theorem over `IsWRP` yields the paper's
statement a fortiori. -/
theorem IsWRPTieTotal.isWRP {T : List Alpha → Option (List Gamma)}
    (h : IsWRPTieTotal T) : IsWRP T := by
  obtain ⟨P, hV, hT⟩ := h
  exact ⟨P, P.valid_of_polyValid hV, hT⟩

/-- The revision's class is contained in the previous draft's class. -/
theorem IsWRPPaper.isWRPTieTotal {T : List Alpha → Option (List Gamma)}
    (h : IsWRPPaper T) : IsWRPTieTotal T := by
  obtain ⟨P, hV, -, hT⟩ := h
  exact ⟨P, hV, hT⟩

/-- The revision's class is contained in the arity-positive class of
`WRPArityPos.lean`. -/
theorem IsWRPPaper.isWRPPos {T : List Alpha → Option (List Gamma)}
    (h : IsWRPPaper T) : IsWRPPos T := by
  obtain ⟨P, hV, hpos, hT⟩ := h
  exact ⟨P, P.valid_of_polyValid hV, hpos, hT⟩

/-- `IsWRPPaper ⊆ IsWRP`: the full inclusion into the Lean class. -/
theorem IsWRPPaper.isWRP {T : List Alpha → Option (List Gamma)}
    (h : IsWRPPaper T) : IsWRP T :=
  h.isWRPTieTotal.isWRP

end WRP

/-! ## Scan tie-orders are strict total orders (the `sRR₁ = SWR` bridge) -/

namespace Polyreg.Presentation

variable {Alpha Gamma : Type*}

/-- **A scan tie-order is a strict total order on all atoms** — hence on the
selected ones: a scan-order presentation is paper-valid.  (This is what
`def:wrp` means by a "scan order": position order in the fixed direction,
copy order breaking position ties; two atoms agreeing in both are equal, the
arity being `1`.) -/
theorem IsScanOrder.valid {P : Presentation Alpha Gamma}
    (h : P.IsScanOrder) : P.Valid := by
  obtain ⟨h1, dir, cord, hirr, htrans, htri, hiff⟩ := h
  have hposirr : ∀ p : ℕ, ¬ (if dir then p < p else p < p) := by
    intro p
    cases dir <;> simp
  refine ⟨?_, ?_, ?_⟩
  · -- irreflexivity
    rintro w a - hbad
    rcases (hiff w a a).mp hbad with hlt | ⟨-, hcord⟩
    · exact hposirr _ hlt
    · exact hirr _ hcord
  · -- transitivity
    rintro w a b c - - - hab hbc
    rw [hiff] at hab hbc ⊢
    rcases hab with hlt | ⟨heq, hcord⟩ <;> rcases hbc with hlt' | ⟨heq', hcord'⟩
    · refine Or.inl ?_
      cases dir <;> simp at hlt hlt' ⊢ <;> omega
    · exact Or.inl (heq' ▸ hlt)
    · exact Or.inl (heq ▸ hlt')
    · exact Or.inr ⟨heq.trans heq', htrans _ _ _ hcord hcord'⟩
  · -- trichotomy
    rintro w a b - -
    rcases lt_trichotomy (P.pos1 h1 a) (P.pos1 h1 b) with hp | hp | hp
    · cases dir
      · exact Or.inr (Or.inr ((hiff w b a).mpr (Or.inl (by simpa using hp))))
      · exact Or.inl ((hiff w a b).mpr (Or.inl (by simpa using hp)))
    · rcases htri a.1 b.1 with hc | hc | hc
      · exact Or.inl ((hiff w a b).mpr (Or.inr ⟨hp, hc⟩))
      · -- equal position and equal copy: the atoms coincide (arity 1)
        refine Or.inr (Or.inl ?_)
        obtain ⟨ca, ia⟩ := a
        obtain ⟨cb, ib⟩ := b
        obtain rfl : ca = cb := hc
        refine congrArg (Sigma.mk ca) (funext fun t => ?_)
        have ht : t = ⟨0, by rw [h1 ca]; exact Nat.one_pos⟩ := by
          apply Fin.ext
          show t.val = 0
          have hlt := t.isLt
          have harity := h1 ca
          omega
        rw [ht]
        exact hp
      · exact Or.inr (Or.inr ((hiff w b a).mpr (Or.inr ⟨hp.symm, hc⟩)))
    · cases dir
      · exact Or.inl ((hiff w a b).mpr (Or.inl (by simpa using hp)))
      · exact Or.inr (Or.inr ((hiff w b a).mpr (Or.inl (by simpa using hp))))

/-- A scan-order presentation is arity-positive (every arity is `1`). -/
theorem IsScanOrder.arityPos {P : Presentation Alpha Gamma}
    (h : P.IsScanOrder) : P.ArityPos := by
  obtain ⟨h1, -, -, -, -, -, -⟩ := h
  intro c
  rw [h1 c]
  exact Nat.one_pos

end Polyreg.Presentation

namespace WRP

variable {Alpha Gamma : Type*}

/-- `sRR₁ = SWR` membership is `χ`-total membership: the scan tie-order is a
genuine strict total order. -/
theorem IsSRR1.isWRPTieTotal {T : List Alpha → Option (List Gamma)}
    (h : IsSRR1 T) : IsWRPTieTotal T := by
  obtain ⟨P, -, -, hscan, hT⟩ := h
  exact ⟨P, hscan.valid, hT⟩

/-- **`sRR₁ = SWR` membership is paper-exact membership**: a scan-order
presentation has a strict-total tie-order and arity `1`, so it realises its
map inside the revision's `def:wrp` class. -/
theorem IsSRR1.isWRPPaper {T : List Alpha → Option (List Gamma)}
    (h : IsSRR1 T) : IsWRPPaper T := by
  obtain ⟨P, -, -, hscan, hT⟩ := h
  exact ⟨P, hscan.valid, hscan.arityPos, hT⟩

/-! ## Conservativity (`prop:conservative`) into the paper classes -/

/-- The rank-dimension-`0` extension of a polyregular presentation, as used by
`isWRP_of_isPolyregular`; at `d = 0` the combined order `≺` is definitionally
the tie-order `χ`. -/
private theorem isOutput_zeroRank_iff (P : Polyreg.Presentation Alpha Gamma)
    (w : List Alpha) (out : List Gamma) :
    (⟨P, 0, fun _ _ _ => Fin.elim0, fun _ => isRegularRankTerm_zero _⟩ :
      Presentation Alpha Gamma).IsOutput w out ↔ P.IsOutput w out := by
  have hwrp : ∀ (a b : P.Atom),
      (⟨P, 0, fun _ _ _ => Fin.elim0, fun _ => isRegularRankTerm_zero _⟩ :
        Presentation Alpha Gamma).wrpOrd w a b ↔ P.atomOrd w a b := by
    intro a b
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact (lexLt_zero _ _ h).elim
      · exact h
    · intro h
      exact Or.inr ⟨funext (fun c => c.elim0), h⟩
  constructor
  · rintro ⟨atoms, hnd, hmem, hpair, hout⟩
    exact ⟨atoms, hnd, hmem, hpair.imp (fun hh => (hwrp _ _).mp hh), hout⟩
  · rintro ⟨atoms, hnd, hmem, hpair, hout⟩
    exact ⟨atoms, hnd, hmem, hpair.imp (fun hh => (hwrp _ _).mpr hh), hout⟩

/-- **`prop:conservative` into the `χ`-total class**: an ordinary polyregular
function (whose validity is already `χ`-totality) is `χ`-total WRP with rank
dimension `0`. -/
theorem isWRPTieTotal_of_isPolyregular {T : List Alpha → Option (List Gamma)}
    (h : Polyreg.IsPolyregular T) : IsWRPTieTotal T := by
  obtain ⟨P, hValid, hT⟩ := h
  refine ⟨⟨P, 0, fun _ _ _ => Fin.elim0, fun _ => isRegularRankTerm_zero _⟩,
    hValid, fun w out => ?_⟩
  rw [hT w out]
  exact and_congr_right fun _ => (isOutput_zeroRank_iff P w out).symm

/-- **`prop:conservative` within the revision's classes** (paper-full-new.tex
`def:wrp`): a polyregular map of the revision's convention (`χ` total, arities
positive — `IsPolyregularPos` with its `Valid`) is a paper-exact WRP map with
rank dimension `0`. -/
theorem isWRPPaper_of_isPolyregularPos {T : List Alpha → Option (List Gamma)}
    (h : Polyreg.IsPolyregularPos T) : IsWRPPaper T := by
  obtain ⟨P, hValid, hpos, hT⟩ := h
  refine ⟨⟨P, 0, fun _ _ _ => Fin.elim0, fun _ => isRegularRankTerm_zero _⟩,
    hValid, hpos, fun w out => ?_⟩
  rw [hT w out]
  exact and_congr_right fun _ => (isOutput_zeroRank_iff P w out).symm

/-- A regular string transduction (deterministic MSO string transduction /
2DFT model) is a paper-exact WRP map. -/
theorem isWRPPaper_of_isRegular {T : List Alpha → Option (List Gamma)}
    (h : Polyreg.IsRegular T) : IsWRPPaper T :=
  isWRPPaper_of_isPolyregularPos h.isPolyregularPos

end WRP

/-! ## The paper-exact positive memberships

The zeta sweep (`thm:zeta-wrp`), the Narayana height sweep
(`thm:narayana-sweep`), and every additive level sort (`prop:alw-sweep-swr`)
are `sRR₁`, hence lie in the revision's `def:wrp` class verbatim. -/

/-- **`thm:zeta-wrp` in the paper-exact class**: the zeta sweep is a WRP map
in the revision's `def:wrp` sense (`χ` a strict total order, arities `≥ 1`). -/
theorem zetaSweep_isWRPPaper :
    WRP.IsWRPPaper (fun w : List Step => some (zetaSweep w)) :=
  zetaSweep_isSRR1.isWRPPaper

/-- **The Narayana height sweep in the paper-exact class**
(`thm:narayana-sweep`, the `H ∈ SWR` clause). -/
theorem heightSweep_isWRPPaper :
    WRP.IsWRPPaper (fun w : List Step => some (heightSweep w)) :=
  heightSweep_isSRR1.isWRPPaper

/-- **`prop:alw-sweep-swr` in the paper-exact class**: every additive level
sort `Φ_ν` is a WRP map in the revision's `def:wrp` sense. -/
theorem additiveSweep_isWRPPaper (nu : Step → ℤ) (dir : Bool) :
    WRP.IsWRPPaper (fun w : List Step => some (additiveSweep nu dir w)) :=
  (additiveSweep_isSRR1 nu dir).isWRPPaper

/-- The zeta map is realised by a paper-exact WRP transduction on the Dyck
domain (`thm:zeta-wrp`). -/
theorem zetaMap_realisedByWRPPaper :
    ∃ T : List Step → Option (List Step),
      WRP.IsWRPPaper T ∧ Realises T {P | IsDyckPath P} zetaMap :=
  ⟨fun w => some (zetaSweep w), zetaSweep_isWRPPaper,
   fun P hP => congrArg some (zetaSweep_eq_zetaMap_of_isDyckPath P hP)⟩
