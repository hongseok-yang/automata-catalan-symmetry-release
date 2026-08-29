/-
# WRP does not have regular preimages of regular languages (`thm:wrp-not-closed`)

Formalises the core of the paper's `thm:wrp-not-closed` (paper.tex): the class of weighted-rank polyregular transductions is **not** closed
under preimages of regular languages.  Concretely we exhibit

* a genuine WRP transduction `wncD : List Step → Option (List GB)`,
* a regular output language `wncK ⊆ List GB`,

such that the preimage `{w | ∃ out, wncD w = some out ∧ out ∈ wncK}` is the
language `Lnn = {w : ∀ i < |w|, height w i ≥ 0}` of "weakly-positive" words,
which is **not** regular (a direct `DFA'` pigeonhole, the same combinatorial
core as `ZetaNotPolyreg.not_regular_le_family`).

## The witness transduction

`wncD` is a two-copy WRP presentation (`wncPres`):

* **Copy 0 — the sentinel `G`:** arity `0`.  Its only atom is the empty tuple
  `Fin 0 → ℕ`; it is always valid, always selected (`Formula.tru`), carries the
  label `g`, and has the constant rank `0` (an arity-0, height-free rank).
* **Copy 1 — the `B`-atoms:** arity `1`.  Copy `1` selects every in-range
  position (`ī 0 < |w|`), carries the label `b`, and has rank `height w (ī 0)`,
  the one-dimensional regular rank term of `ZetaWRP.heightSource` (exactly as in
  `zetaPres`/`hsPres`).

The tie-order `χ` puts the sentinel before every `B`-atom (so at equal rank the
sentinel wins), and orders `B`-atoms by ascending position.  Hence the output
order `≺` is rank-lex (height) then this `χ`.  The first output letter is `g`
precisely when the sentinel — rank `0` — is `≺`-minimal, i.e. precisely when
every selected `B`-atom has rank `≥ 0`, i.e. precisely when `w ∈ Lnn`.

Taking `wncK = {y | y.head? = some g}` (regular, via an explicit `DFA'`) gives
`wncD⁻¹(wncK) = Lnn`, which is not regular.  (Only the regular-preimage half of
the paper theorem is formalised; the paper's blocks 1, 2 yield a *composition*
corollary that needs a sequential-transducer model the repository lacks.)

Trust base: `[propext, Classical.choice, Quot.sound]` — axiom-clean.  The witness
`wncD` is a concrete presentation and the non-regularity is a direct `DFA'`
pigeonhole; no Büchi axiom and no project axioms are used.
-/
import RequestProject.ZetaWRP
import RequestProject.AreaSeq
import RequestProject.Transducers

open MSO Step

namespace WRPNotClosed

/-! ## The output alphabet -/

/-- The output alphabet of the witness transduction: `g` (the sentinel `G`) and
`b` (the `B`-atoms).  (`u`, `d` are spare letters, kept so the type is a small
concrete `Fintype` with `DecidableEq`.) -/
inductive GB | g | b | u | d
  deriving DecidableEq

instance : Fintype GB :=
  ⟨⟨{.g, .b, .u, .d}, by decide⟩, fun x => by cases x <;> decide⟩

open GB

/-! ## The two-copy presentation

The arity of copy `c` is `0` for the sentinel (`c = 0`) and `1` for the
`B`-copy.  We extract "the position of an atom" uniformly with `idxPos`,
returning `0` for the (coordinate-free) sentinel. -/

/-- Arity of copy `c`: `0` for the sentinel, `1` for the `B`-copy. -/
@[reducible] def wncArity (c : Fin 2) : ℕ := if c = 0 then 0 else 1

/-- A coordinate-1 access proof for the `B`-copy. -/
theorem one_lt_wncArity_of_ne {c : Fin 2} (h : c ≠ 0) : 0 < wncArity c := by
  rw [wncArity, if_neg h]; exact Nat.one_pos

/-- A coordinate-1 access proof for the `B`-copy, phrased on `c.val`. -/
theorem zero_lt_wncArity_of_val_ne {c : Fin 2} (h : c.val ≠ 0) : 0 < wncArity c :=
  one_lt_wncArity_of_ne (fun hc => h (congrArg Fin.val hc))

/-- The single position of an atom of copy `c`: `0` for the sentinel (it has no
coordinate), the lone coordinate for the `B`-copy. -/
def idxPos (c : Fin 2) (ī : Fin (wncArity c) → ℕ) : ℕ :=
  if h : c = 0 then 0 else ī ⟨0, one_lt_wncArity_of_ne h⟩

/-- The polyregular part: two copies.  Copy `0` (the sentinel `G`) is always
selected and labelled `g`; copy `1` selects every in-range position and is
labelled `b`.  The tie order `χ` is copy-block primary (`0 ≺ 1`, sentinel first)
and, within a copy, position ascending. -/
@[reducible] def wncPoly : Polyreg.Presentation Step GB where
  K := 2
  arity := wncArity
  domain := fun _ => True
  domainDef := ⟨Formula.tru, fun _ => Iff.rfl⟩
  sel := fun c w ī =>
    if h : c.val = 0 then True else ī ⟨0, zero_lt_wncArity_of_val_ne h⟩ < w.length
  selDef := fun c => by
    by_cases h : c.val = 0
    · refine ⟨Formula.tru, fun w ī => ?_⟩
      simp only [Formula.sat_tru, dif_pos h]
    · refine ⟨.or (.labelEq ⟨0, zero_lt_wncArity_of_val_ne h⟩ U)
        (.labelEq ⟨0, zero_lt_wncArity_of_val_ne h⟩ D), fun w ī => ?_⟩
      simp only [dif_neg h, Formula.sat_or, Formula.sat_labelEq]
      constructor
      · intro hlt
        rcases hU : w[ī ⟨0, zero_lt_wncArity_of_val_ne h⟩] with _ | _
        · exact Or.inl (by rw [List.getElem?_eq_getElem hlt, hU])
        · exact Or.inr (by rw [List.getElem?_eq_getElem hlt, hU])
      · rintro (hh | hh) <;> exact (List.getElem?_eq_some_iff.mp hh).1
  label := fun c _ _ => if c.val = 0 then g else b
  labelDef := fun c gg => by
    by_cases h : (if c.val = 0 then g else b) = gg
    · exact ⟨.tru, fun w ī => iff_of_true h trivial⟩
    · exact ⟨.neg .tru, fun w ī => iff_of_false h (by simp)⟩
  ord := fun c c' _ ī ī' => c.val < c'.val ∨ (c.val = c'.val ∧ idxPos c ī < idxPos c' ī')
  ordDef := fun c c' => by
    -- The free-variable tuple has `arity c + arity c'` coordinates.
    fin_cases c <;> fin_cases c'
    · -- sentinel vs sentinel: 0 + 0 free vars; relation is `False`.
      refine ⟨.neg .tru, fun w ij => ?_⟩
      simp only [Formula.sat_neg, Formula.sat_tru, not_true, iff_false]
      rintro (hh | ⟨_, hh⟩)
      · exact absurd hh (by decide)
      · simp only [idxPos] at hh; exact absurd hh (lt_irrefl 0)
    · -- sentinel vs B: 0 + 1 free vars; relation is `True` (0 < 1).
      refine ⟨.tru, fun w ij => ?_⟩
      simp only [Formula.sat_tru, iff_true]
      exact Or.inl (by decide)
    · -- B vs sentinel: 1 + 0 free vars; relation is `False`.
      refine ⟨.neg .tru, fun w ij => ?_⟩
      simp only [Formula.sat_neg, Formula.sat_tru, not_true, iff_false]
      rintro (hh | ⟨hh, _⟩) <;> exact absurd hh (by decide)
    · -- B vs B: 1 + 1 free vars; relation is `ī 0 < ī' 0`.
      refine ⟨.lt (Fin.castAdd 1 ⟨0, Nat.one_pos⟩) (Fin.natAdd 1 ⟨0, Nat.one_pos⟩),
        fun w ij => ?_⟩
      simp only [Formula.sat_lt]
      constructor
      · rintro (hh | ⟨_, hh⟩)
        · exact absurd hh (by decide)
        · exact hh
      · intro hh
        refine Or.inr ⟨trivial, ?_⟩
        exact hh

/-- The WRP presentation: rank dimension `1`; the sentinel (copy `0`) has the
constant rank `0`, and each `B`-atom (copy `1`) has rank `height w (ī 0)`, via
the one-state height source `ZetaWRP.heightSource`. -/
@[reducible] def wncPres : WRP.Presentation Step GB where
  toPoly := wncPoly
  d := 1
  rank := fun c w ī => fun _ =>
    if h : c.val = 0 then 0 else height w (ī ⟨0, zero_lt_wncArity_of_val_ne h⟩)
  rankReg := fun c => by
    by_cases h : c.val = 0
    · -- constant-0 rank: the empty rank term
      refine ⟨⟨fun _ => 0, []⟩, fun w ī => ?_⟩
      funext x
      simp only [RankTerm.eval, List.map_nil, List.sum_nil, add_zero, dif_pos h]
    · -- height rank: the one-state height source, exactly as in `hsPres`
      refine ⟨⟨fun _ => 0, [⟨heightSource, 1, ⟨0, zero_lt_wncArity_of_val_ne h⟩,
        fun _ _ _ => 0⟩]⟩, fun w ī => ?_⟩
      funext x
      simp only [RankTerm.eval, Summand.eval, heightSource_prefixRank,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dif_neg h]
      cases w[ī ⟨0, zero_lt_wncArity_of_val_ne h⟩]? <;> simp

/-! ## Atoms -/

/-- The copy index `0` (the sentinel), as an element of `Fin wncPoly.K`. -/
@[reducible] def c0 : Fin wncPoly.K := ⟨0, by decide⟩
/-- The copy index `1` (the `B`-copy), as an element of `Fin wncPoly.K`. -/
@[reducible] def c1 : Fin wncPoly.K := ⟨1, by decide⟩

@[simp] theorem c0_val : c0.val = 0 := rfl
@[simp] theorem c1_val : c1.val = 1 := rfl

/-- The sentinel atom (copy `0`, empty coordinate tuple). -/
@[reducible] def sentinel : wncPoly.Atom := ⟨c0, Fin.elim0⟩

/-- The `B`-atom at input position `p` (copy `1`). -/
def bAtom (p : ℕ) : wncPoly.Atom := ⟨c1, fun _ => p⟩

@[simp] theorem sentinel_fst : sentinel.1 = c0 := rfl
@[simp] theorem bAtom_fst (p : ℕ) : (bAtom p).1 = c1 := rfl

/-- The position of an atom: `0` for the sentinel, the lone coordinate for a
`B`-atom.  (The atom-level companion of `idxPos`.) -/
@[reducible] def atomPos (a : wncPoly.Atom) : ℕ :=
  if h : a.1.val = 0 then 0 else a.2 ⟨0, zero_lt_wncArity_of_val_ne h⟩

@[simp] theorem atomPos_sentinel : atomPos sentinel = 0 := by
  simp only [atomPos, sentinel_fst, dif_pos]

@[simp] theorem atomPos_bAtom (p : ℕ) : atomPos (bAtom p) = p := by
  simp only [atomPos, bAtom_fst, c1_val]; rfl

/-- A `B`-atom is determined by its position. -/
theorem bAtom_injective : Function.Injective bAtom := fun p q h => by
  have := congrArg atomPos h
  simpa using this

theorem sentinel_ne_bAtom (p : ℕ) : sentinel ≠ bAtom p := by
  intro h
  have : c0 = c1 := congrArg Sigma.fst h
  exact absurd (congrArg Fin.val this) (by decide)

/-- The two copy indices, by value. -/
theorem copy_val_lt_two (c : Fin wncPoly.K) : c.val = 0 ∨ c.val = 1 := by
  have hlt : c.val < 2 := c.isLt
  omega

theorem eq_c0_of_val_zero {c : Fin wncPoly.K} (h : c.val = 0) : c = c0 := Fin.ext h

theorem eq_c1_of_val_one {c : Fin wncPoly.K} (h : c.val = 1) : c = c1 := Fin.ext h

/-- An atom whose copy is `0` is the sentinel. -/
theorem eq_sentinel_of_val_zero (a : wncPoly.Atom) (h : a.1.val = 0) : a = sentinel := by
  obtain ⟨c, f⟩ := a
  have hc : c = c0 := eq_c0_of_val_zero h
  subst hc
  -- `f : Fin (wncPoly.arity c0) → ℕ`, and `arity c0` reduces to `0`
  show (⟨c0, f⟩ : wncPoly.Atom) = ⟨c0, Fin.elim0⟩
  congr 1
  funext t
  have h1 : t.val < wncPoly.arity c0 := t.isLt
  have h2 : wncPoly.arity c0 = 0 := rfl
  omega

/-- An atom whose copy is `1` is the `B`-atom at its position. -/
theorem eq_bAtom_of_val_one (a : wncPoly.Atom) (h : a.1.val = 1) :
    a = bAtom (atomPos a) := by
  obtain ⟨c, f⟩ := a
  have hc : c = c1 := eq_c1_of_val_one h
  subst hc
  -- now `f : Fin (wncPoly.arity c1) → ℕ`, with `arity c1` reducing to `1`
  have hpos : atomPos (⟨c1, f⟩ : wncPoly.Atom) = f ⟨0, Nat.one_pos⟩ := by
    simp only [atomPos, c1, dif_neg (by decide : (1 : ℕ) ≠ 0)]
  rw [hpos]
  show (⟨c1, f⟩ : wncPoly.Atom) = ⟨c1, fun _ => f ⟨0, Nat.one_pos⟩⟩
  congr 1
  funext t
  have ht : t = ⟨0, Nat.one_pos⟩ := by
    apply Fin.ext
    have h1 : t.val < wncPoly.arity c1 := t.isLt
    have h2 : wncPoly.arity c1 = 1 := rfl
    omega
  rw [ht]

/-- Every atom is either the sentinel or a `B`-atom. -/
theorem atom_cases (a : wncPoly.Atom) : a = sentinel ∨ ∃ p, a = bAtom p := by
  rcases copy_val_lt_two a.1 with hc | hc
  · exact Or.inl (eq_sentinel_of_val_zero a hc)
  · exact Or.inr ⟨atomPos a, eq_bAtom_of_val_one a hc⟩

/-! ## Selection, labels, ranks on the two atom shapes -/

/-- The sentinel's `sel` reduces to `True` (its `dite` condition `c0.val = 0` is
decidably true). -/
theorem sel_sentinel (w : List Step) : wncPoly.sel sentinel.1 w sentinel.2 = True := rfl

/-- The sentinel is always selected. -/
@[simp] theorem selectedAtom_sentinel (w : List Step) : wncPoly.selectedAtom w sentinel := by
  refine ⟨fun t => ?_, ?_⟩
  · have h1 : t.val < wncPoly.arity sentinel.1 := t.isLt
    have h2 : wncPoly.arity sentinel.1 = 0 := rfl
    omega
  · show wncPoly.sel sentinel.1 w sentinel.2
    rw [sel_sentinel]; trivial

/-- `sel` of a `B`-atom reduces to the in-range test (the `dite` condition
`c1.val = 0` is decidably false). -/
theorem sel_bAtom (w : List Step) (p : ℕ) :
    wncPoly.sel (bAtom p).1 w (bAtom p).2 = (p < w.length) := rfl

@[simp] theorem selectedAtom_bAtom (w : List Step) (p : ℕ) :
    wncPoly.selectedAtom w (bAtom p) ↔ p < w.length := by
  unfold Polyreg.Presentation.selectedAtom Polyreg.Presentation.validAtom
  rw [sel_bAtom]
  constructor
  · rintro ⟨_, hsel⟩; exact hsel
  · intro hlt
    refine ⟨fun t => ?_, hlt⟩
    have ht : t.val = 0 := by
      have h1 : t.val < wncPoly.arity (bAtom p).1 := t.isLt
      have h2 : wncPoly.arity (bAtom p).1 = 1 := rfl
      omega
    show (bAtom p).2 t < w.length
    exact hlt

@[simp] theorem labelOf_bAtom (w : List Step) (p : ℕ) : wncPoly.labelOf w (bAtom p) = b := rfl

@[simp] theorem rankOf_sentinel (w : List Step) : wncPres.rankOf w sentinel = fun _ => 0 := rfl

@[simp] theorem rankOf_bAtom (w : List Step) (p : ℕ) :
    wncPres.rankOf w (bAtom p) = fun _ => height w p := rfl

/-! ## The tie order and the output order on atoms

We read the output order `≺` (`wncPres.wrpOrd`) off the two atom shapes.  The
key facts: the sentinel `≺` a `B`-atom iff `0 ≤ height` of that `B`-atom's
position (rank `0` vs rank `height`, sentinel-first on a tie); a `B`-atom `≺` the
sentinel iff its height is `< 0`; and two `B`-atoms compare by (height, position)
lexicographically. -/

/-- The rank dimension index `0`, as an element of `Fin wncPres.d`. -/
def d0 : Fin wncPres.d := ⟨0, Nat.one_pos⟩

/-- `idxPos` on an atom's components equals `atomPos`. -/
theorem idxPos_eq_atomPos (a : wncPoly.Atom) : idxPos a.1 a.2 = atomPos a := by
  rcases atom_cases a with rfl | ⟨p, rfl⟩
  · show idxPos sentinel.1 sentinel.2 = atomPos sentinel
    rw [atomPos_sentinel]
    rfl
  · show idxPos (bAtom p).1 (bAtom p).2 = atomPos (bAtom p)
    rw [atomPos_bAtom]
    rfl

/-- The tie order on atoms, in normal form. -/
theorem atomOrd_iff (w : List Step) (a b : wncPoly.Atom) :
    wncPoly.atomOrd w a b ↔
      a.1.val < b.1.val ∨ (a.1.val = b.1.val ∧ atomPos a < atomPos b) := by
  show (a.1.val < b.1.val ∨ (a.1.val = b.1.val ∧ idxPos a.1 a.2 < idxPos b.1 b.2)) ↔ _
  rw [idxPos_eq_atomPos, idxPos_eq_atomPos]

/-- The output order `≺` on atoms, in normal form: rank-lex (a 1-D `height`
comparison) then the tie order `χ` (copy-block, position). -/
theorem wrpOrd_iff (w : List Step) (a b : wncPoly.Atom) :
    wncPres.wrpOrd w a b ↔
      wncPres.rankOf w a d0 < wncPres.rankOf w b d0 ∨
        (wncPres.rankOf w a d0 = wncPres.rankOf w b d0 ∧
          (a.1.val < b.1.val ∨ (a.1.val = b.1.val ∧ atomPos a < atomPos b))) := by
  show (WRP.lexLt (wncPres.rankOf w a) (wncPres.rankOf w b) ∨
      (wncPres.rankOf w a = wncPres.rankOf w b ∧ wncPoly.atomOrd w a b)) ↔ _
  rw [lexLt_one, fin1_fun_ext_iff, atomOrd_iff]
  exact Iff.rfl

/-! ### Validity -/

theorem wncPres_wrpOrd_irrefl (w : List Step) (a : wncPoly.Atom) :
    ¬ wncPres.wrpOrd w a a := by
  rw [wrpOrd_iff]; omega

theorem wncPres_valid : wncPres.Valid where
  irrefl := fun w a _ => wncPres_wrpOrd_irrefl w a
  trans := by
    intro w a b c _ _ _ hab hbc
    rw [wrpOrd_iff] at *
    omega
  trichot := by
    intro w a b _ _
    rw [wrpOrd_iff, wrpOrd_iff]
    by_cases hr : wncPres.rankOf w a d0 = wncPres.rankOf w b d0
    · by_cases hcv : a.1.val = b.1.val
      · rcases lt_trichotomy (atomPos a) (atomPos b) with hp | hp | hp
        · exact Or.inl (Or.inr ⟨hr, Or.inr ⟨hcv, hp⟩⟩)
        · -- equal rank, equal copy, equal position ⇒ equal atom
          refine Or.inr (Or.inl ?_)
          rcases copy_val_lt_two a.1 with ha0 | ha1
          · have hb0 : b.1.val = 0 := hcv ▸ ha0
            rw [eq_sentinel_of_val_zero a ha0, eq_sentinel_of_val_zero b hb0]
          · have hb1 : b.1.val = 1 := hcv ▸ ha1
            rw [eq_bAtom_of_val_one a ha1, eq_bAtom_of_val_one b hb1, hp]
        · exact Or.inr (Or.inr (Or.inr ⟨hr.symm, Or.inr ⟨hcv.symm, hp⟩⟩))
      · rcases lt_trichotomy a.1.val b.1.val with hc | hc | hc
        · exact Or.inl (Or.inr ⟨hr, Or.inl hc⟩)
        · exact absurd hc hcv
        · exact Or.inr (Or.inr (Or.inr ⟨hr.symm, Or.inl hc⟩))
    · rcases lt_or_gt_of_ne hr with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))

/-! ## The concrete transduction via a sort

We realise the transduction by sorting the selected atoms (sentinel and every
in-range `B`-atom) and reading off their labels.  The sort key is the triple
`(rankVal, copy, position)` with a reflexive (`≤`) proxy on the position
tie-break (as in `NarayanaSweep.cmpHS'`), so `List.mergeSort` is provably total
and transitive. -/

/-- The numeric rank of an atom: `0` for the sentinel, `height w p` for a
`B`-atom at position `p`. -/
def rankVal (w : List Step) (a : wncPoly.Atom) : ℤ :=
  if a.1.val = 0 then 0 else height w (atomPos a)

@[simp] theorem rankVal_sentinel (w : List Step) : rankVal w sentinel = 0 := by
  simp [rankVal]

@[simp] theorem rankVal_bAtom (w : List Step) (p : ℕ) : rankVal w (bAtom p) = height w p := by
  simp [rankVal]

theorem rankOf_apply_eq_rankVal (w : List Step) (a : wncPoly.Atom) :
    wncPres.rankOf w a d0 = rankVal w a := by
  rcases atom_cases a with rfl | ⟨p, rfl⟩ <;> simp [rankVal]

/-- The lexicographic sort key of an atom: `(rank, copy, position)`. -/
def keyA (w : List Step) (a : wncPoly.Atom) : ℤ × ℕ × ℕ :=
  (rankVal w a, a.1.val, atomPos a)

/-- The reflexive `≤`-proxy lexicographic comparator on keys (cf.
`NarayanaSweep.cmpHS'`): total and transitive. -/
def cmpK (a b : ℤ × ℕ × ℕ) : Bool :=
  if a.1 < b.1 then true
  else if b.1 < a.1 then false
  else if a.2.1 < b.2.1 then true
  else if b.2.1 < a.2.1 then false
  else a.2.2 ≤ b.2.2

/-- The atom comparator: compare keys. -/
def cmpA (w : List Step) (a b : wncPoly.Atom) : Bool := cmpK (keyA w a) (keyA w b)

/-- `cmpK` made `Prop`-shaped: it is exactly the (reflexive) lex order. -/
theorem cmpK_iff (a b : ℤ × ℕ × ℕ) :
    cmpK a b = true ↔
      a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 ≤ b.2.2))) := by
  unfold cmpK
  split_ifs with h1 h2 h3 h4 <;>
    simp only [decide_eq_true_eq, true_iff, false_iff, not_or] <;> omega

theorem cmpK_total (a b : ℤ × ℕ × ℕ) : cmpK a b || cmpK b a := by
  rw [Bool.or_eq_true, cmpK_iff, cmpK_iff]; omega

theorem cmpK_trans (a b c : ℤ × ℕ × ℕ) : cmpK a b → cmpK b c → cmpK a c := by
  rw [cmpK_iff, cmpK_iff, cmpK_iff]; omega

theorem cmpA_total (w : List Step) (a b : wncPoly.Atom) : cmpA w a b || cmpA w b a :=
  cmpK_total _ _

theorem cmpA_trans (w : List Step) (a b c : wncPoly.Atom) :
    cmpA w a b → cmpA w b c → cmpA w a c :=
  cmpK_trans _ _ _

/-- The pre-sort list of selected atoms: the sentinel and every in-range
`B`-atom. -/
def selList (w : List Step) : List wncPoly.Atom :=
  sentinel :: (List.range w.length).map bAtom

/-- The sorted witness atom list. -/
def wncAtoms (w : List Step) : List wncPoly.Atom :=
  (selList w).mergeSort (cmpA w)

/-- The output of the transduction: the sorted labels. -/
def wncD (w : List Step) : List GB := (wncAtoms w).map (wncPoly.labelOf w)

/-! ### Membership in the witness list -/

theorem mem_selList (w : List Step) (a : wncPoly.Atom) :
    a ∈ selList w ↔ a = sentinel ∨ ∃ p, p < w.length ∧ a = bAtom p := by
  unfold selList
  rw [List.mem_cons, List.mem_map]
  constructor
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, List.mem_range.mp hp, rfl⟩
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, List.mem_range.mpr hp, rfl⟩

theorem mem_wncAtoms (w : List Step) (a : wncPoly.Atom) :
    a ∈ wncAtoms w ↔ a ∈ selList w := by
  rw [wncAtoms, List.mem_mergeSort]

/-- **Membership** (`IsOutput` obligation 1): the witness list is exactly the
selected atoms. -/
theorem mem_wncAtoms_iff (w : List Step) (a : wncPoly.Atom) :
    a ∈ wncAtoms w ↔ wncPoly.selectedAtom w a := by
  rw [mem_wncAtoms, mem_selList]
  rcases atom_cases a with rfl | ⟨p, rfl⟩
  · simp only [selectedAtom_sentinel, iff_true]
    exact Or.inl trivial
  · rw [selectedAtom_bAtom]
    constructor
    · rintro (h | ⟨q, hq, hpq⟩)
      · exact (sentinel_ne_bAtom p h.symm).elim
      · rw [bAtom_injective hpq]; exact hq
    · intro hlt; exact Or.inr ⟨p, hlt, rfl⟩

/-- An atom is determined by its copy and position. -/
theorem atom_eq_of_copy_pos {a b : wncPoly.Atom} (hc : a.1.val = b.1.val)
    (hp : atomPos a = atomPos b) : a = b := by
  rcases copy_val_lt_two a.1 with ha | ha
  · have hb : b.1.val = 0 := hc ▸ ha
    rw [eq_sentinel_of_val_zero a ha, eq_sentinel_of_val_zero b hb]
  · have hb : b.1.val = 1 := hc ▸ ha
    rw [eq_bAtom_of_val_one a ha, eq_bAtom_of_val_one b hb, hp]

/-! ### No duplicates -/

theorem selList_nodup (w : List Step) : (selList w).Nodup := by
  unfold selList
  rw [List.nodup_cons]
  refine ⟨?_, (List.nodup_range).map bAtom_injective⟩
  rw [List.mem_map]
  rintro ⟨p, _, hp⟩
  exact sentinel_ne_bAtom p hp.symm

/-- **No duplicates** (`IsOutput` obligation 2). -/
theorem wncAtoms_nodup (w : List Step) : (wncAtoms w).Nodup := by
  rw [wncAtoms]
  exact ((List.mergeSort_perm _ _).nodup_iff).mpr (selList_nodup w)

/-! ### Pairwise sorted -/

/-- For distinct atoms, `cmpA` implies the output order `≺`. -/
theorem cmpA_imp_wrpOrd (w : List Step) {a b : wncPoly.Atom} (hne : a ≠ b)
    (h : cmpA w a b) : wncPres.wrpOrd w a b := by
  rw [cmpA, cmpK_iff] at h
  rw [wrpOrd_iff, rankOf_apply_eq_rankVal, rankOf_apply_eq_rankVal]
  simp only [keyA] at h
  rcases h with hr | ⟨hr, hcp⟩
  · exact Or.inl hr
  · refine Or.inr ⟨hr, ?_⟩
    rcases hcp with hc | ⟨hc, hple⟩
    · exact Or.inl hc
    · refine Or.inr ⟨hc, ?_⟩
      -- equal rank & copy & `atomPos a ≤ atomPos b`; distinctness forces `<`
      rcases lt_or_eq_of_le hple with hlt | heq
      · exact hlt
      · exact absurd (atom_eq_of_copy_pos hc heq) hne

/-- **Pairwise** (`IsOutput` obligation 3): the witness list is `≺`-sorted. -/
theorem wncAtoms_pairwise (w : List Step) :
    (wncAtoms w).Pairwise (wncPres.wrpOrd w) := by
  have hsorted : (wncAtoms w).Pairwise (fun a b => cmpA w a b = true) :=
    List.pairwise_mergeSort (cmpA_trans w) (cmpA_total w) _
  have hpairne : (wncAtoms w).Pairwise (fun a b => a ≠ b) :=
    (wncAtoms_nodup w).pairwise_of_forall_ne (fun a _ b _ hab => hab)
  refine (hsorted.and hpairne).imp (fun {a b} hh => ?_)
  exact cmpA_imp_wrpOrd w hh.2 hh.1

/-! ### `wncD` is the declarative output, hence WRP -/

/-- `wncD w` is the declarative output of the presentation on `w`. -/
theorem wncD_isOutput (w : List Step) : wncPres.IsOutput w (wncD w) :=
  ⟨wncAtoms w, wncAtoms_nodup w, mem_wncAtoms_iff w, wncAtoms_pairwise w, rfl⟩

/-- **The witness transduction is genuinely WRP.** -/
theorem wncD_isWRP : WRP.IsWRP (fun w : List Step => some (wncD w)) :=
  ⟨wncPres, wncPres_valid, fun w _out =>
    ⟨fun h => ⟨trivial, (Option.some.inj h) ▸ wncD_isOutput w⟩,
     fun ⟨_, hout⟩ => congrArg some
       (isOutput_unique wncPres wncPres_valid (wncD_isOutput w) hout)⟩⟩

/-! ## The first-letter characterisation

The first output letter is `g` precisely when the sentinel is the `≺`-minimal
selected atom, which happens precisely when every prefix height is `≥ 0`. -/

/-- The weakly-positive language: every (selected) prefix has nonnegative height.
This is exactly the preimage `wncD⁻¹(wncK)`. -/
def Lnn : Set (List Step) := {w | ∀ i, i < w.length → 0 ≤ height w i}

/-- The witness list is nonempty (it contains the sentinel). -/
theorem wncAtoms_ne_nil (w : List Step) : wncAtoms w ≠ [] := by
  intro h
  have : sentinel ∈ wncAtoms w := (mem_wncAtoms_iff w sentinel).mpr (selectedAtom_sentinel w)
  rw [h] at this
  exact absurd this List.not_mem_nil

/-- The sentinel is `≺` every selected `B`-atom precisely when all heights are
nonnegative. -/
theorem wrpOrd_sentinel_bAtom (w : List Step) (p : ℕ) :
    wncPres.wrpOrd w sentinel (bAtom p) ↔ 0 ≤ height w p := by
  rw [wrpOrd_iff, rankOf_apply_eq_rankVal, rankOf_apply_eq_rankVal,
    rankVal_sentinel, rankVal_bAtom]
  constructor
  · rintro (h | ⟨h, _⟩) <;> omega
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, Or.inl ?_⟩
      show sentinel.1.val < (bAtom p).1.val
      rw [sentinel_fst, bAtom_fst, c0_val, c1_val]
      omega

/-- The head of the sorted witness list is the `≺`-minimum: it is selected and
strictly below every other selected atom. -/
theorem head_wncAtoms_min (w : List Step) :
    ∃ a₀, (wncAtoms w).head? = some a₀ ∧ wncPoly.selectedAtom w a₀ ∧
      ∀ b, wncPoly.selectedAtom w b → b ≠ a₀ → wncPres.wrpOrd w a₀ b := by
  obtain ⟨h, t, hht⟩ := List.exists_cons_of_ne_nil (wncAtoms_ne_nil w)
  refine ⟨h, by rw [hht]; rfl, ?_, ?_⟩
  · exact (mem_wncAtoms_iff w h).mp (by rw [hht]; exact List.mem_cons_self)
  · intro b hb hbh
    have hbmem : b ∈ wncAtoms w := (mem_wncAtoms_iff w b).mpr hb
    have hbt : b ∈ t := by
      rw [hht, List.mem_cons] at hbmem
      rcases hbmem with rfl | hbt
      · exact absurd rfl hbh
      · exact hbt
    have hpw := wncAtoms_pairwise w
    rw [hht, List.pairwise_cons] at hpw
    exact hpw.1 b hbt

/-- **First-letter characterisation.**  The first output letter is `g` precisely
when `w ∈ Lnn`. -/
theorem head_wncD_eq_g_iff (w : List Step) :
    (wncD w).head? = some g ↔ w ∈ Lnn := by
  obtain ⟨a₀, hhead, hsel, hmin⟩ := head_wncAtoms_min w
  have hdhead : (wncD w).head? = some (wncPoly.labelOf w a₀) := by
    rw [wncD, List.head?_map, hhead]
    rfl
  rw [hdhead, Option.some.injEq]
  constructor
  · -- label of min is `g` ⇒ min is sentinel ⇒ all heights ≥ 0
    intro hg
    have ha0 : a₀ = sentinel := by
      rcases atom_cases a₀ with rfl | ⟨p, rfl⟩
      · rfl
      · rw [labelOf_bAtom] at hg; exact absurd hg (by decide)
    intro i hi
    -- `bAtom i` is selected and ≠ sentinel; minimality gives sentinel ≺ bAtom i
    have hbi_sel : wncPoly.selectedAtom w (bAtom i) := (selectedAtom_bAtom w i).mpr hi
    have hbi_ne : bAtom i ≠ a₀ := by rw [ha0]; exact (sentinel_ne_bAtom i).symm
    have hlt := hmin (bAtom i) hbi_sel hbi_ne
    rw [ha0] at hlt
    exact (wrpOrd_sentinel_bAtom w i).mp hlt
  · -- all heights ≥ 0 ⇒ sentinel is the min ⇒ its label `g` is the head
    intro hLnn
    have ha0 : a₀ = sentinel := by
      rcases atom_cases a₀ with rfl | ⟨p, rfl⟩
      · rfl
      · -- a B-atom can't be the min: the sentinel would be ≺ it
        exfalso
        have hp_sel : (bAtom p).1.val = 1 ∧ atomPos (bAtom p) = p := ⟨rfl, atomPos_bAtom p⟩
        -- the B-atom `bAtom p` is selected, so `p < |w|`
        have hplt : p < w.length := (selectedAtom_bAtom w p).mp hsel
        -- sentinel is selected and ≠ bAtom p; minimality of a₀ = bAtom p gives bAtom p ≺ sentinel
        have hsne : sentinel ≠ bAtom p := sentinel_ne_bAtom p
        have hlt := hmin sentinel (selectedAtom_sentinel w) hsne
        -- but Lnn gives sentinel ≺ bAtom p, contradicting validity
        have hsent_lt : wncPres.wrpOrd w sentinel (bAtom p) :=
          (wrpOrd_sentinel_bAtom w p).mpr (hLnn p hplt)
        exact wncPres_wrpOrd_irrefl w sentinel
          (wncPres_valid.trans w sentinel (bAtom p) sentinel
            (selectedAtom_sentinel w) hsel (selectedAtom_sentinel w) hsent_lt hlt)
    rw [ha0]; rfl

/-! ## The regular output language `wncK` and its preimage

`wncK = {y | y.head? = some g}` (strings starting with `g`) is regular: a
three-state `DFA'` that, on the first letter, branches to an accepting state for
`g` and a sink for anything else. -/

/-- The three states of the `DFA'` for `wncK`. -/
inductive KState | start | sawG | sawOther
  deriving DecidableEq

instance : Fintype KState :=
  ⟨⟨{.start, .sawG, .sawOther}, by decide⟩, fun x => by cases x <;> decide⟩

open KState

/-- The `DFA'` recognising "first letter is `g`". -/
def wncKDFA : DFA' GB where
  Q := KState
  delta := fun q y => match q, y with
    | start, GB.g => sawG
    | start, _ => sawOther
    | sawG, _ => sawG
    | sawOther, _ => sawOther
  q0 := start
  F := {sawG}

/-- The run of `wncKDFA` lands in `sawG` exactly when the first letter is `g`. -/
theorem wncKDFA_run (y : List GB) :
    y.foldl wncKDFA.delta wncKDFA.q0 = sawG ↔ y.head? = some g := by
  cases y with
  | nil => simp [wncKDFA]
  | cons x xs =>
    have hstep : wncKDFA.delta wncKDFA.q0 x = (if x = g then sawG else sawOther) := by
      cases x <;> rfl
    rw [List.foldl_cons, hstep, List.head?_cons, Option.some.injEq]
    by_cases hx : x = g
    · subst hx
      -- from `sawG`, every step stays in `sawG`
      have : ∀ l : List GB, l.foldl wncKDFA.delta sawG = sawG := by
        intro l; induction l with
        | nil => rfl
        | cons z zs ih =>
            show List.foldl wncKDFA.delta (wncKDFA.delta sawG z) zs = sawG
            rw [show wncKDFA.delta sawG z = sawG from by cases z <;> rfl]; exact ih
      rw [if_pos rfl, this]
      exact iff_of_true rfl rfl
    · -- from `sawOther`, every step stays in `sawOther` (≠ `sawG`)
      have : ∀ l : List GB, l.foldl wncKDFA.delta sawOther = sawOther := by
        intro l; induction l with
        | nil => rfl
        | cons z zs ih =>
            show List.foldl wncKDFA.delta (wncKDFA.delta sawOther z) zs = sawOther
            rw [show wncKDFA.delta sawOther z = sawOther from by cases z <;> rfl]; exact ih
      rw [if_neg hx, this]
      constructor
      · intro h; exact KState.noConfusion h
      · intro h; exact absurd h hx

/-- The regular output language: strings whose first letter is `g`. -/
def wncK : Set (List GB) := {y | y.head? = some g}

theorem wncK_isRegular : IsRegularLang wncK := by
  refine ⟨wncKDFA, ?_⟩
  ext y
  show wncKDFA.accepts y ↔ y ∈ wncK
  unfold DFA'.accepts wncK
  rw [show (wncKDFA.F : Set KState) = {sawG} from rfl]
  simp only [Set.mem_ofPred_eq]
  exact wncKDFA_run y

/-- **The preimage of `wncK` under `wncD` is exactly `Lnn`.** -/
theorem preimage_eq_Lnn :
    {w : List Step | ∃ out, (fun w => some (wncD w)) w = some out ∧ out ∈ wncK} = Lnn := by
  ext w
  simp only [Set.mem_ofPred_eq, Option.some.injEq]
  constructor
  · rintro ⟨out, rfl, hmem⟩
    exact (head_wncD_eq_g_iff w).mp hmem
  · intro hw
    exact ⟨wncD w, rfl, (head_wncD_eq_g_iff w).mpr hw⟩

/-! ## `Lnn` is not regular (pigeonhole)

We mirror `ZetaNotPolyreg.not_regular_le_family`.  Among the prefixes
`U^0, …, U^N` (`N = #states`), two collide, say `U^p, U^q` with `p < q`.  We
append the common suffix `D^q U`.  The word `U^q D^q U` is in `Lnn` (it never
dips below `0`), but `U^p D^q U` is not (it reaches height `-1` at the strictly
interior position `2p+1`, where the trailing `U` guarantees `2p+1 < length`). -/

/-- The height after `k ≤ n` `U`'s is `k`. -/
theorem height_replicate_U_le (n k : ℕ) (hk : k ≤ n) :
    height (List.replicate n U) k = (k : ℤ) := by
  rw [height_eq_count, List.take_replicate, Nat.min_eq_left hk]
  simp [List.count_replicate]

/-- The witness word `U^a D^b U`. -/
def wit (a b : ℕ) : List Step := List.replicate a U ++ (List.replicate b D ++ [U])

@[simp] theorem wit_length (a b : ℕ) : (wit a b).length = a + b + 1 := by
  simp [wit]; omega

/-- Height of the witness word at position `k`, for `k ≤ a`. -/
theorem height_wit_le_a (a b k : ℕ) (hk : k ≤ a) : height (wit a b) k = (k : ℤ) := by
  rw [wit, height_append_left _ _ _ (by rw [List.length_replicate]; exact hk),
    height_replicate_U_le a k hk]

/-- Height of the witness word at position `a + j`, for `j ≤ b`. -/
theorem height_wit_a_add (a b j : ℕ) (hj : j ≤ b) :
    height (wit a b) (a + j) = (a : ℤ) - j := by
  rw [height_eq_count, wit]
  -- `take (a+j)` of `U^a ++ (D^b ++ [U])` is `U^a ++ D^j`
  have htake : (List.replicate a U ++ (List.replicate b D ++ [U])).take (a + j)
      = List.replicate a U ++ List.replicate j D := by
    rw [List.take_append, List.length_replicate,
      List.take_of_length_le (by rw [List.length_replicate]; omega),
      show a + j - a = j by omega, List.take_append, List.length_replicate,
      List.take_replicate, Nat.min_eq_left hj,
      show j - b = 0 by omega, List.take_zero, List.append_nil]
  rw [htake]
  simp only [List.count_append, List.count_replicate, beq_iff_eq]
  norm_num
  simp

/-- The high witness `U^q D^q U` is weakly positive. -/
theorem wit_qq_mem_Lnn (q : ℕ) : wit q q ∈ Lnn := by
  intro i hi
  rw [wit_length] at hi
  by_cases hia : i ≤ q
  · rw [height_wit_le_a q q i hia]; positivity
  · push Not at hia
    -- write `i = q + j` with `0 < j ≤ q`
    obtain ⟨j, rfl⟩ : ∃ j, i = q + j := ⟨i - q, by omega⟩
    have hj : j ≤ q := by omega
    rw [height_wit_a_add q q j hj]; omega

/-- The low witness `U^p D^q U` (`p < q`) is not weakly positive: it dips to
height `-1` at the interior position `2p+1`. -/
theorem wit_pq_not_mem_Lnn (p q : ℕ) (hpq : p < q) : wit p q ∉ Lnn := by
  intro hmem
  have hpos : 2 * p + 1 < (wit p q).length := by rw [wit_length]; omega
  have hge := hmem (2 * p + 1) hpos
  -- `2p+1 = p + (p+1)`, `p+1 ≤ q`, so height = p - (p+1) = -1
  have hj : p + 1 ≤ q := hpq
  have hh : height (wit p q) (2 * p + 1) = -1 := by
    have : 2 * p + 1 = p + (p + 1) := by omega
    rw [this, height_wit_a_add p q (p + 1) hj]
    push_cast; ring
  rw [hh] at hge
  omega

/-- **`Lnn` is not regular.**  Pigeonhole on the `U`-prefixes: two collide, say
`U^p, U^q` with `p < q`; appending `D^q U` keeps them in the same `DFA'` state,
so they are accepted together — but `U^q D^q U ∈ Lnn` while `U^p D^q U ∉ Lnn`. -/
theorem not_regular_Lnn : ¬ IsRegularLang Lnn := by
  rintro ⟨A, hA⟩
  have := A.finQ
  have := A.decEqQ
  -- state reached after reading `U^k`
  let runU : ℕ → A.Q := fun k => (List.replicate k U).foldl A.delta A.q0
  -- pigeonhole among `U^0 … U^{N}` (`N = card Q`): two collide
  obtain ⟨p, q, hpq, hcol⟩ : ∃ p q, p < q ∧ runU p = runU q := by
    have hcard : (Finset.univ : Finset A.Q).card
        < (Finset.range (Fintype.card A.Q + 1)).card := by simp
    obtain ⟨i, _, j, _, hij, he⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
        (fun a _ => Finset.mem_univ (runU a))
    rcases Nat.lt_or_ge i j with h | h
    · exact ⟨i, j, h, he⟩
    · exact ⟨j, i, lt_of_le_of_ne h hij.symm, he.symm⟩
  -- the run of `wit k q = U^k ++ (D^q U)` factors through `runU k`
  have hfold : ∀ k, (wit k q).foldl A.delta A.q0
      = (List.replicate q D ++ [U]).foldl A.delta (runU k) := by
    intro k; rw [wit, List.foldl_append]
  -- `wit p q` and `wit q q` reach the same final state
  have hrun_eq : (wit p q).foldl A.delta A.q0 = (wit q q).foldl A.delta A.q0 := by
    rw [hfold, hfold, hcol]
  -- hence accepted together
  have hacc_iff : wit p q ∈ Lnn ↔ wit q q ∈ Lnn := by
    rw [← hA]
    show A.accepts _ ↔ A.accepts _
    unfold DFA'.accepts
    rw [hrun_eq]
  -- contradiction
  have h1 : wit q q ∈ Lnn := wit_qq_mem_Lnn q
  have h2 : wit p q ∉ Lnn := wit_pq_not_mem_Lnn p q hpq
  exact h2 (hacc_iff.mpr h1)

/-! ## The main theorem -/

/-- **Theorem `thm:wrp-not-closed` (`thm:wrp-not-closed`, paper.tex), regular-preimage
half.**  There is a genuine WRP transduction `wncD` and a regular output language
`wncK` whose preimage under `wncD` is not regular.  Hence WRP does not have
regular preimages of regular languages.  Axiom-clean (no Büchi, no project
axioms): the witness is a concrete presentation and the non-regularity is a
direct `DFA'` pigeonhole. -/
theorem wrp_not_closed_preimage :
    ∃ (D : List Step → Option (List GB)) (K : Set (List GB)),
      WRP.IsWRP D ∧ IsRegularLang K ∧
      ¬ IsRegularLang {w | ∃ out, D w = some out ∧ out ∈ K} := by
  refine ⟨fun w => some (wncD w), wncK, wncD_isWRP, wncK_isRegular, ?_⟩
  rw [preimage_eq_Lnn]
  exact not_regular_Lnn

end WRPNotClosed
