/-
# The stable one-dimensional ranked-regular fragment `sRR₁ = SWR` (genuine)

This file gives `sRR₁` a genuine semantic definition refining
`WRP.IsWRP`, following `def:wrp` (paper.tex):

* `RR` (ranked-regular) is the **arity-1** fragment: each output atom is a pair
  `(c, i)` indexed by a single input position.
* `sRR₁ = SWR` is the **stable one-dimensional** restriction: arity 1, rank
  dimension `d = 1`, and the tie-order `χ` is a **scan order** — a fixed
  direction on positions together with a linear order on the finite copy set,
  which is exactly what makes `χ` a genuine total order.

We prove the paper's inclusions `sRR₁ ⊆ RR ⊆ WRP`, and the two genuine
memberships the paper asserts: the Narayana height sweep `H` is `sRR₁`
(`thm:narayana-sweep`, the `H ∈ SWR` clause) and the zeta sweep is `sRR₁`
(`thm:zeta-wrp`).  Both are over the real declarative `WRP.IsWRP`, not the
placeholder.
-/
import RequestProject.NarayanaWRP

open MSO Step

namespace Polyreg.Presentation

variable {Alpha Gamma : Type*}

/-- The single input position of an atom in an **arity-1** presentation
(`h1 : every copy has arity 1`); for such a presentation an atom `(c, ī)` is a
pair `(c, ī 0)`. -/
def pos1 {P : Presentation Alpha Gamma} (h1 : ∀ c, P.arity c = 1) (a : P.Atom) : ℕ :=
  a.2 ⟨0, by rw [h1 a.1]; exact Nat.one_pos⟩

/-- **Scan tie-order** (the `sRR₁` condition on `χ`, `def:wrp`).  On arity-1
atoms the underlying order `χ` is a fixed direction `dir` on positions, with a
strict-linear copy order `cord` breaking position ties.  The copy tiebreak is
what keeps `χ` a genuine *total* order: two selected atoms at the same position
lie in different copies and are still strictly ordered. -/
def IsScanOrder (P : Presentation Alpha Gamma) : Prop :=
  ∃ (h1 : ∀ c, P.arity c = 1) (dir : Bool) (cord : Fin P.K → Fin P.K → Prop),
    (∀ c, ¬ cord c c) ∧
    (∀ x y z, cord x y → cord y z → cord x z) ∧
    (∀ x y, cord x y ∨ x = y ∨ cord y x) ∧
    ∀ (w : List Alpha) (a b : P.Atom),
      P.atomOrd w a b ↔
        ((if dir then P.pos1 h1 a < P.pos1 h1 b else P.pos1 h1 b < P.pos1 h1 a)
          ∨ (P.pos1 h1 a = P.pos1 h1 b ∧ cord a.1 b.1))

end Polyreg.Presentation

namespace WRP

variable {Alpha Gamma : Type*}

/-- **Ranked-regular `RR`** (`def:wrp`): a `WRP` transduction admitting an
**arity-1** valid presentation. -/
def IsRR (T : List Alpha → Option (List Gamma)) : Prop :=
  ∃ P : Presentation Alpha Gamma, P.Valid ∧ (∀ c, P.toPoly.arity c = 1) ∧
    ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)

/-- **Stable one-dimensional ranked-regular `sRR₁ = SWR`** (`def:wrp`): a valid
`WRP` presentation with rank dimension `d = 1` and a scan tie-order (hence
arity 1). -/
def IsSRR1 (T : List Alpha → Option (List Gamma)) : Prop :=
  ∃ P : Presentation Alpha Gamma, P.Valid ∧ P.d = 1 ∧ P.toPoly.IsScanOrder ∧
    ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)

/-- `sRR₁ ⊆ RR`: a scan tie-order is in particular arity 1. -/
theorem IsSRR1.isRR {T : List Alpha → Option (List Gamma)} (h : IsSRR1 T) : IsRR T := by
  obtain ⟨P, hv, _, hscan, hreal⟩ := h
  obtain ⟨h1, _, _, _, _, _, _⟩ := hscan
  exact ⟨P, hv, h1, hreal⟩

/-- `RR ⊆ WRP`: forget the arity bound. -/
theorem IsRR.isWRP {T : List Alpha → Option (List Gamma)} (h : IsRR T) : IsWRP T := by
  obtain ⟨P, hv, _, hreal⟩ := h
  exact ⟨P, hv, hreal⟩

/-- **`sRR₁ ⊆ WRP`** (`def:wrp`), the full inclusion chain `sRR₁ ⊆ RR ⊆ WRP`. -/
theorem IsSRR1.isWRP {T : List Alpha → Option (List Gamma)} (h : IsSRR1 T) : IsWRP T :=
  h.isRR.isWRP

end WRP

/-- Realisation boilerplate shared by the membership theorems: a presentation
with total domain that outputs `f w` on every input realises `fun w => some (f w)`. -/
private theorem realisesTotally {Alpha Gamma : Type*} {P : WRP.Presentation Alpha Gamma}
    (hV : P.Valid) {f : List Alpha → List Gamma} (hf : ∀ w, P.IsOutput w (f w))
    (hd : ∀ w, P.toPoly.domain w) (w : List Alpha) (out : List Gamma) :
    (some (f w) = some out) ↔ (P.toPoly.domain w ∧ P.IsOutput w out) :=
  ⟨fun h => ⟨hd w, (Option.some.inj h) ▸ hf w⟩,
   fun ⟨_, hout⟩ => congrArg some (isOutput_unique P hV (hf w) hout)⟩

/-! ## The Narayana height sweep is `sRR₁` (`thm:narayana-sweep`, the `H ∈ SWR` clause) -/

/-- The height-sweep presentation has a genuine scan tie-order: arity 1, the
right-to-left position order (`dir = false`), and the (vacuous, `K = 1`) copy
order. -/
theorem hsPoly_isScanOrder : hsPoly.IsScanOrder := by
  refine ⟨fun _ => rfl, false, fun _ _ => False, ?_, ?_, ?_, ?_⟩
  · intro c h; exact h
  · intro x y z h _; exact h.elim
  · intro x y
    refine Or.inr (Or.inl (Fin.ext ?_))
    have hx : (x : ℕ) < 1 := x.2
    have hy : (y : ℕ) < 1 := y.2
    omega
  · intro w a b
    simp only [Polyreg.Presentation.atomOrd, Polyreg.Presentation.pos1, hsPoly,
      and_false, or_false]
    rw [if_neg (by decide)]
    exact Iff.rfl

/-- **`thm:narayana-sweep` (the `H ∈ SWR` clause), genuine.**  The Narayana
height sweep is a stable one-dimensional rank sweep (`sRR₁`). -/
theorem heightSweep_isSRR1 : WRP.IsSRR1 (fun w : List Step => some (heightSweep w)) :=
  ⟨hsPres, hsPres_valid, rfl, hsPoly_isScanOrder,
   realisesTotally hsPres_valid heightSweep_isOutput (fun _ => trivial)⟩

/-! ## The zeta sweep is `sRR₁` (`thm:zeta-wrp`) -/

/-- `zetaPoly` with a genuine **scan** tie-order: left-to-right by position,
broken by copy index, so `χ` is a total order (as `sRR₁` requires).  Same `sel`,
`label`, `domain` as `zetaPoly`; only `ord` adds the copy tiebreak.  The rank
separates the two same-position atoms by one level, so this never changes the
output order (`zetaPresS_wrpOrd_eq`). -/
@[reducible] def zetaPolyS : Polyreg.Presentation Step Step where
  K := 2
  arity := fun _ => 1
  domain := fun _ => True
  domainDef := ⟨Formula.tru, fun _ => Iff.rfl⟩
  sel := fun _ w ī => w[ī 0]? = some U
  selDef := fun _ => ⟨.labelEq 0 U, fun _ _ => Iff.rfl⟩
  label := fun c _ _ => if c = (0 : Fin 2) then U else D
  labelDef := fun c g => by
    by_cases h : (if c = (0 : Fin 2) then U else D) = g
    · exact ⟨.tru, fun w ρ => iff_of_true h trivial⟩
    · exact ⟨.neg .tru, fun w ρ => iff_of_false h (by simp)⟩
  ord := fun c c' _ ī ī' => ī 0 < ī' 0 ∨ (ī 0 = ī' 0 ∧ c.val < c'.val)
  ordDef := fun c c' => by
    by_cases h : c.val < c'.val
    · refine ⟨.neg (.lt (Fin.natAdd 1 0) (Fin.castAdd 1 0)), fun w ij => ?_⟩
      simp only [Formula.sat_neg, Formula.sat_lt, h, and_true]; omega
    · refine ⟨.lt (Fin.castAdd 1 0) (Fin.natAdd 1 0), fun w ij => ?_⟩
      simp only [Formula.sat_lt, h, and_false, or_false]

/-- The scan-order zeta `WRP` presentation: same rank as `zetaPres`, scan `χ`. -/
@[reducible] def zetaPresS : WRP.Presentation Step Step :=
  { zetaPres with toPoly := zetaPolyS }

/-- The copy tiebreak never matters: at equal rank two distinct atoms have
distinct positions (equal position ⇒ equal height ⇒ the ranks `height + copy`
differ by the copy index), so `zetaPresS` and `zetaPres` induce the same
output order. -/
theorem zetaPresS_wrpOrd_eq (w : List Step) (a b : zetaPolyS.Atom) :
    zetaPresS.wrpOrd w a b ↔ zetaPres.wrpOrd w a b := by
  constructor
  · rintro (hlex | ⟨hReq, hatomS⟩)
    · exact Or.inl hlex
    · rcases (show atomPos a < atomPos b ∨ (atomPos a = atomPos b ∧ a.1.val < b.1.val)
          from hatomS) with hlt | ⟨hpos, hcopy⟩
      · exact Or.inr ⟨hReq, hlt⟩
      · exfalso
        have hr := congrFun hReq ⟨0, Nat.one_pos⟩
        simp only [WRP.Presentation.rankOf, zetaPresS, zetaPres] at hr
        have hpos' : a.2 ⟨0, Nat.one_pos⟩ = b.2 ⟨0, Nat.one_pos⟩ := hpos
        rw [hpos'] at hr
        omega
  · rintro (hlex | ⟨hReq, hatom⟩)
    · exact Or.inl hlex
    · exact Or.inr ⟨hReq, Or.inl hatom⟩

/-- `zetaPresS` is valid, inherited from `zetaPres` through `wrpOrd` equality. -/
theorem zetaPresS_valid : zetaPresS.Valid where
  irrefl := fun w a ha => by
    rw [zetaPresS_wrpOrd_eq]; exact zetaPres_valid.irrefl w a ha
  trans := fun w a b c ha hb hc => by
    rw [zetaPresS_wrpOrd_eq, zetaPresS_wrpOrd_eq, zetaPresS_wrpOrd_eq]
    exact zetaPres_valid.trans w a b c ha hb hc
  trichot := fun w a b ha hb => by
    rw [zetaPresS_wrpOrd_eq, zetaPresS_wrpOrd_eq]
    exact zetaPres_valid.trichot w a b ha hb

/-- The scan presentation produces the same outputs as `zetaPres`. -/
theorem zetaPresS_isOutput_iff (w out : List Step) :
    zetaPresS.IsOutput w out ↔ zetaPres.IsOutput w out := by
  constructor
  · rintro ⟨atoms, hnd, hmem, hpw, hout⟩
    exact ⟨atoms, hnd, hmem, hpw.imp (fun {a b} h => (zetaPresS_wrpOrd_eq w a b).mp h), hout⟩
  · rintro ⟨atoms, hnd, hmem, hpw, hout⟩
    exact ⟨atoms, hnd, hmem, hpw.imp (fun {a b} h => (zetaPresS_wrpOrd_eq w a b).mpr h), hout⟩

/-- `zetaPolyS` has a genuine scan tie-order: arity 1, the left-to-right
position order (`dir = true`), copies ordered by index. -/
theorem zetaPolyS_isScanOrder : zetaPolyS.IsScanOrder := by
  refine ⟨fun _ => rfl, true, fun x y => x.val < y.val, ?_, ?_, ?_, ?_⟩
  · intro c; exact Nat.lt_irrefl c.val
  · intro x y z hxy hyz; exact Nat.lt_trans hxy hyz
  · intro x y
    rcases Nat.lt_trichotomy x.val y.val with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr h)
  · intro w a b
    rw [if_pos (by decide)]
    exact Iff.rfl

/-- **`thm:zeta-wrp` (the `ζ ∈ SWR` clause), genuine.**  The totalised zeta
sweep is a stable one-dimensional rank sweep (`sRR₁`). -/
theorem zetaSweep_isSRR1 : WRP.IsSRR1 (fun w : List Step => some (zetaSweep w)) :=
  ⟨zetaPresS, zetaPresS_valid, rfl, zetaPolyS_isScanOrder,
   realisesTotally zetaPresS_valid
     (fun w => (zetaPresS_isOutput_iff w (zetaSweep w)).mpr (zetaSweep_isOutput w))
     (fun _ => trivial)⟩

/-- **The zeta map is realised by an `sRR₁` transduction on the Dyck domain**
(`thm:zeta-wrp`), genuinely. -/
theorem zetaMap_realisedBySRR1 :
    ∃ T : List Step → Option (List Step),
      WRP.IsSRR1 T ∧ Realises T {P | IsDyckPath P} zetaMap :=
  ⟨fun w => some (zetaSweep w), zetaSweep_isSRR1,
   fun P hP => congrArg some (zetaSweep_eq_zetaMap_of_isDyckPath P hP)⟩
