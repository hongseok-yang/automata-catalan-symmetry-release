/-
# The height sweep is a WRP transduction — the genuine membership half of
# `thm:narayana-sweep`

Formalises component (a) of the paper's `thm:narayana-sweep` (§`sec:narayana-sweep`):
the Narayana height sweep `H` is a weighted-rank polyregular transduction, over
the concrete model of `WRP.lean`.

The presentation is the paper's: ONE copy with one atom per input position, the
one-state height rank source (rank = starting height), and the **right-to-left**
tie order (position descending).  Unlike the zeta map (`ZetaWRP.lean`), no
totalisation is needed: `heightSweep` is a genuine mergeSort by (height
ascending, position descending), so it is faithful on EVERY word and
`WRP.IsWRP (fun w => some (heightSweep w))` holds outright — the strongest form.

The witness atom list for `IsOutput` is the mergeSorted `sweepIdx` triples
themselves, mapped to atoms; the existing `cmpHS'` infrastructure of
`NarayanaSweep.lean` (totality, transitivity, position-nodup, `heightSweep_eq'`)
does the heavy lifting.

Trust base: `[propext, Classical.choice, Quot.sound]` — axiom-clean.
-/
import RequestProject.ZetaWRP
import RequestProject.NarayanaSweep

open MSO Step

/-! ## The presentation -/

/-- The polyregular part: one arity-1 copy selecting EVERY in-range position;
the label is the letter at the position; the tie order is position-DESCENDING
(the paper's right-to-left scan). -/
@[reducible] def hsPoly : Polyreg.Presentation Step Step where
  K := 1
  arity := fun _ => 1
  domain := fun _ => True
  domainDef := ⟨Formula.tru, fun _ => Iff.rfl⟩
  sel := fun _ w ī => ī 0 < w.length
  selDef := fun _ => ⟨.or (.labelEq 0 U) (.labelEq 0 D), fun w ρ => by
    simp only [Formula.sat_or, Formula.sat_labelEq]
    constructor
    · intro h
      rcases hU : w[ρ 0] with _ | _
      · exact Or.inl (by rw [List.getElem?_eq_getElem h, hU])
      · exact Or.inr (by rw [List.getElem?_eq_getElem h, hU])
    · rintro (h | h) <;> exact (List.getElem?_eq_some_iff.mp h).1⟩
  label := fun _ w ī => (w[ī 0]?).getD U
  labelDef := fun c g => by
    rcases g with _ | _
    · refine ⟨.neg (.labelEq 0 D), fun w ρ => ?_⟩
      simp only [Formula.sat_neg, Formula.sat_labelEq]
      rcases hg : w[ρ 0]? with _ | s
      · simp
      · rcases s with _ | _ <;> simp
    · refine ⟨.labelEq 0 D, fun w ρ => ?_⟩
      simp only [Formula.sat_labelEq]
      rcases hg : w[ρ 0]? with _ | s
      · simp
      · rcases s with _ | _ <;> simp
  ord := fun _ _ _ ī ī' => ī' 0 < ī 0
  ordDef := fun c c' => ⟨.lt (Fin.natAdd 1 0) (Fin.castAdd 1 0), fun w ij => Iff.rfl⟩

/-- The WRP presentation: rank = the starting height, via `heightSource`. -/
@[reducible] def hsPres : WRP.Presentation Step Step where
  toPoly := hsPoly
  d := 1
  rank := fun _ w ī => fun _ => height w (ī ⟨0, Nat.one_pos⟩)
  rankReg := fun c => by
    refine ⟨⟨fun _ => 0, [⟨heightSource, 1, ⟨0, Nat.one_pos⟩, fun _ _ _ => 0⟩]⟩, ?_⟩
    intro w ī
    funext x
    simp only [RankTerm.eval, Summand.eval, heightSource_prefixRank,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    cases w[ī ⟨0, Nat.one_pos⟩]? <;> simp

/-! ## The atom toolkit -/

/-- The atom at input position `p`. -/
@[reducible] def hsAtom (p : ℕ) : hsPoly.Atom := ⟨⟨0, Nat.one_pos⟩, fun _ => p⟩

/-- The position coordinate of an atom. -/
@[reducible] def hsPos (a : hsPoly.Atom) : ℕ := a.2 ⟨0, Nat.one_pos⟩

@[simp] theorem hsPos_hsAtom (p : ℕ) : hsPos (hsAtom p) = p := rfl

theorem hsAtom_ext {a b : hsPoly.Atom} (h : hsPos a = hsPos b) : a = b := by
  obtain ⟨c, f⟩ := a
  obtain ⟨c', g⟩ := b
  have hc : c = c' := by
    have h1 : hsPoly.K = 1 := rfl
    apply Fin.ext
    have := c.isLt
    have := c'.isLt
    omega
  cases hc
  have hfg : f = g := by
    funext t
    have ht : t = ⟨0, Nat.one_pos⟩ := by
      apply Fin.ext
      have h1 := t.isLt
      have h2 : hsPoly.arity c = 1 := rfl
      omega
    rw [ht]
    exact h
  rw [hfg]

theorem hsAtom_injective : Function.Injective hsAtom := fun p q h => by
  have := congrArg hsPos h
  simpa using this

theorem hsAtom_eta (a : hsPoly.Atom) : a = hsAtom (hsPos a) :=
  (hsAtom_ext (a := hsAtom (hsPos a)) (b := a) rfl).symm

theorem hs_rankOf_eval (w : List Step) (a : hsPoly.Atom) :
    hsPres.rankOf w a = fun _ => height w (hsPos a) := rfl

@[simp] theorem hs_labelOf_eval (w : List Step) (p : ℕ) :
    hsPoly.labelOf w (hsAtom p) = (w[p]?).getD U := rfl

/-- Selectedness is exactly in-rangeness. -/
theorem hs_selectedAtom_iff (w : List Step) (a : hsPoly.Atom) :
    hsPoly.selectedAtom w a ↔ hsPos a < w.length := by
  constructor
  · rintro ⟨-, hsel⟩
    exact hsel
  · intro h
    refine ⟨fun t => ?_, h⟩
    have ht : t = ⟨0, Nat.one_pos⟩ := by
      apply Fin.ext
      have h1 := t.isLt
      have h2 : hsPoly.arity a.1 = 1 := rfl
      omega
    rw [ht]
    exact h

/-- The order, in omega-ready normal form: height-lex, then position DESCENDING. -/
theorem hs_wrpOrd_iff (w : List Step) (a b : hsPoly.Atom) :
    hsPres.wrpOrd w a b ↔
      (height w (hsPos a) < height w (hsPos b)
        ∨ (height w (hsPos a) = height w (hsPos b) ∧ hsPos b < hsPos a)) := by
  show (WRP.lexLt (hsPres.rankOf w a) (hsPres.rankOf w b)
      ∨ (hsPres.rankOf w a = hsPres.rankOf w b ∧ hsPoly.atomOrd w a b)) ↔ _
  rw [hs_rankOf_eval, hs_rankOf_eval, lexLt_one, fin1_fun_ext_iff]
  exact Iff.rfl

/-! ## Validity -/

theorem hsPres_wrpOrd_irrefl (w : List Step) (a : hsPoly.Atom) :
    ¬ hsPres.wrpOrd w a a := by
  rw [hs_wrpOrd_iff]
  omega

theorem hsPres_valid : hsPres.Valid where
  irrefl := fun w a _ => hsPres_wrpOrd_irrefl w a
  trans := by
    intro w a b c _ _ _ hab hbc
    rw [hs_wrpOrd_iff] at *
    omega
  trichot := by
    intro w a b _ _
    rw [hs_wrpOrd_iff, hs_wrpOrd_iff]
    by_cases heq : height w (hsPos a) = height w (hsPos b)
    · rcases lt_trichotomy (hsPos a) (hsPos b) with hp | hp | hp
      · exact Or.inr (Or.inr (Or.inr ⟨heq.symm, hp⟩))
      · exact Or.inr (Or.inl (hsAtom_ext hp))
      · exact Or.inl (Or.inr ⟨heq, hp⟩)
    · rcases lt_or_gt_of_ne (fun hc => heq hc) with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))

/-! ## The witness atom list: the mergeSorted sweep triples -/

/-- The triple shape: a member of `sweepIdx w` is `(height w p, p, the letter at p)`. -/
theorem mem_sweepIdx_shape {w : List Step} {z : ℤ × ℕ × Step}
    (hz : z ∈ sweepIdx w) :
    z.1 = height w z.2.1 ∧ z.2.1 < w.length ∧ w[z.2.1]? = some z.2.2 := by
  unfold sweepIdx at hz
  rw [List.mem_map] at hz
  obtain ⟨⟨s, i⟩, hi, rfl⟩ := hz
  obtain ⟨hlt, hs⟩ := List.mem_zipIdx' hi
  exact ⟨rfl, hlt, by rw [List.getElem?_eq_getElem hlt, hs]⟩

/-- Every in-range position has a triple in `sweepIdx`. -/
theorem exists_mem_sweepIdx_of_lt {w : List Step} {p : ℕ} (hp : p < w.length) :
    ∃ z ∈ sweepIdx w, z.2.1 = p := by
  have hmem : p ∈ w.zipIdx.map Prod.snd := by
    rw [List.zipIdx_map_snd]
    simp [hp]
  rw [List.mem_map] at hmem
  obtain ⟨pair, hpair, hsnd⟩ := hmem
  exact ⟨(height w pair.2, pair.2, pair.1),
    List.mem_map_of_mem hpair, hsnd⟩

/-- The witness list: the sorted triples, mapped to their atoms. -/
def hsAtoms (w : List Step) : List hsPoly.Atom :=
  ((sweepIdx w).mergeSort cmpHS').map (fun z => hsAtom z.2.1)

/-- **Membership**: the witness list contains exactly the selected atoms. -/
theorem mem_hsAtoms_iff (w : List Step) (a : hsPoly.Atom) :
    a ∈ hsAtoms w ↔ hsPoly.selectedAtom w a := by
  rw [hs_selectedAtom_iff, hsAtoms, List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' := List.mem_mergeSort.mp hz
    exact (mem_sweepIdx_shape hz').2.1
  · intro h
    obtain ⟨z, hz, hzp⟩ := exists_mem_sweepIdx_of_lt h
    exact ⟨z, List.mem_mergeSort.mpr hz, by rw [hzp, ← hsAtom_eta]⟩

/-- **No duplicates**: positions are pairwise distinct after sorting. -/
theorem hsAtoms_nodup (w : List Step) : (hsAtoms w).Nodup := by
  have hperm : (((sweepIdx w).mergeSort cmpHS').map (·.2.1)).Perm
      ((sweepIdx w).map (·.2.1)) :=
    (List.mergeSort_perm _ _).map _
  have hnd : (((sweepIdx w).mergeSort cmpHS').map (·.2.1)).Nodup :=
    hperm.nodup_iff.mpr (nodup_pos_sweepIdx w)
  have : hsAtoms w = (((sweepIdx w).mergeSort cmpHS').map (·.2.1)).map hsAtom := by
    rw [hsAtoms, List.map_map]
    rfl
  rw [this]
  exact hnd.map hsAtom_injective

/-- **Pairwise**: the sorted order is exactly `wrpOrd`. -/
theorem hsAtoms_pairwise (w : List Step) :
    (hsAtoms w).Pairwise (hsPres.wrpOrd w) := by
  rw [hsAtoms, List.pairwise_map]
  have hsorted : (((sweepIdx w).mergeSort cmpHS')).Pairwise (cmpHS' · ·) :=
    List.pairwise_mergeSort cmpHS'_trans cmpHS'_total _
  have hposnd : (((sweepIdx w).mergeSort cmpHS').map (·.2.1)).Nodup :=
    ((List.mergeSort_perm _ _).map _).nodup_iff.mpr (nodup_pos_sweepIdx w)
  have hpairne : (((sweepIdx w).mergeSort cmpHS')).Pairwise
      (fun z z' => z.2.1 ≠ z'.2.1) := by
    rw [← List.pairwise_map (f := fun z : ℤ × ℕ × Step => z.2.1)]
    exact hposnd
  refine (hsorted.and hpairne).imp_of_mem (fun {z z'} hz hz' hzz => ?_)
  obtain ⟨hcmp, hne⟩ := hzz
  have hz1 := mem_sweepIdx_shape (List.mem_mergeSort.mp hz)
  have hz1' := mem_sweepIdx_shape (List.mem_mergeSort.mp hz')
  rw [hs_wrpOrd_iff]
  simp only [hsPos_hsAtom]
  rw [← hz1.1, ← hz1'.1]
  unfold cmpHS' at hcmp
  split_ifs at hcmp with h1 h2
  · exact Or.inl h1
  · simp only [decide_eq_true_eq] at hcmp
    exact Or.inr ⟨by omega, by omega⟩

/-- **The label map**: the witness labels are exactly the height sweep. -/
theorem map_labelOf_hsAtoms (w : List Step) :
    (hsAtoms w).map (hsPoly.labelOf w) = heightSweep w := by
  rw [heightSweep_eq', hsAtoms, List.map_map]
  refine List.map_congr_left ?_
  intro z hz
  have hsh := mem_sweepIdx_shape (List.mem_mergeSort.mp hz)
  show hsPoly.labelOf w (hsAtom z.2.1) = z.2.2
  rw [hs_labelOf_eval, hsh.2.2]
  rfl

/-- **The sweep is the declarative output.** -/
theorem heightSweep_isOutput (w : List Step) :
    hsPres.IsOutput w (heightSweep w) :=
  ⟨hsAtoms w, hsAtoms_nodup w, mem_hsAtoms_iff w, hsAtoms_pairwise w,
    (map_labelOf_hsAtoms w).symm⟩

/-! ## The main theorems -/

/-- **The height sweep is a WRP transduction** (`thm:narayana-sweep`,
component (a), genuine): the strongest form — total, no domain restriction,
no totalisation needed. -/
theorem heightSweep_isWRP : WRP.IsWRP (fun w : List Step => some (heightSweep w)) :=
  ⟨hsPres, hsPres_valid, fun w _out =>
    ⟨fun h => ⟨trivial, (Option.some.inj h) ▸ heightSweep_isOutput w⟩,
     fun ⟨_, hout⟩ => congrArg some
       (isOutput_unique hsPres hsPres_valid (heightSweep_isOutput w) hout)⟩⟩

/-- The realisation form on the Dyck domain, for citation symmetry with
`zetaMap_realisedByWRP`. -/
theorem heightSweep_realisedByWRP :
    ∃ T : List Step → Option (List Step),
      WRP.IsWRP T ∧ Realises T {P | IsDyckPath P} heightSweep :=
  ⟨fun w => some (heightSweep w), heightSweep_isWRP, fun _ _ => rfl⟩
