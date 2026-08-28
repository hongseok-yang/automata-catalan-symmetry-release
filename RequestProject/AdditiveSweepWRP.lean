/-
# Every additive sweep transduction is a stable one-dimensional rank sweep
# (`prop:alw-sweep-swr`) — the GENUINE, axiom-clean theorem

Formalises the paper's `prop:alw-sweep-swr` (`prop:alw-sweep-swr`, paper.tex): for
ARBITRARY integer step weights `ν : Step → ℤ` and a scan direction `dir`, the
additive sweep transduction `Φ_ν` (`additiveSweep` in `AdditiveSweep.lean`)
is a stable one-dimensional rank sweep (`WRP.IsSRR1`), hence WRP.

This is the verbatim generalisation of the height-sweep instance of
`NarayanaWRP.lean`/`SRR1.lean` over the weight family `ν` and the direction
`dir`.  The construction is the paper's:

* ONE copy with one atom per input position, label = the letter at the position;
* the one-state additive rank source with `ω(s) = ν(s)`, whose prefix rank is the
  additive level `ℓ(i) = Σ_{j<i} ν(w_j)` (`additiveSource_prefixRank`);
* rank dimension `d = 1`, rank = the level `ℓ(ī 0)`;
* the scan tie-order: position-descending when `dir = true` (right-to-left),
  position-ascending when `dir = false` (left-to-right).

`heightSweep = additiveSweep (fun | U => 1 | D => -1) true`
(`AdditiveSweep.lean`); the `dir = true` branch here is exactly the height-sweep proof of
`NarayanaWRP.lean`, with `height → additiveLevel`.

Trust base: `[propext, Classical.choice, Quot.sound]` — the rank source is
exhibited explicitly, so no Büchi axiom and no project axioms; axiom-clean.
-/
import RequestProject.SRR1
import RequestProject.AdditiveSweep

open MSO Step

/-! ## The additive level and its rank source -/

/-- The additive level `ℓ(i) = Σ_{j<i} ν(w_j)`, defeq to the inner `level` of
`additiveSweep` (`AdditiveSweep.lean`). -/
def additiveLevel (nu : Step → ℤ) (w : List Step) (i : ℕ) : ℤ :=
  (w.take i).foldl (fun acc t => acc + nu t) 0

/-- The paper's one-state additive rank source with weights `ω(s) = ν(s)`
(`def:rank-source`, the source of `prop:alw-sweep-swr`,
paper.tex). -/
def additiveSource (nu : Step → ℤ) : RankSource Step 1 where
  Q := Unit
  fintypeQ := inferInstance
  q0 := ()
  δ := fun _ _ => ()
  ω := fun _ s _ => nu s

/-- **The bridge**: the additive source's prefix rank is the additive level —
the uniform-in-letter analogue of `heightSource_prefixRank` (`ZetaWRP.lean`). -/
theorem additiveSource_prefixRank (nu : Step → ℤ) (w : List Step) (i : ℕ) :
    (additiveSource nu).prefixRank w i = fun _ => additiveLevel nu w i := by
  funext x
  induction i with
  | zero => simp [RankSource.prefixRank, additiveLevel]
  | succ i ih =>
    rw [RankSource.prefixRank, Finset.sum_range_succ,
      ← RankSource.prefixRank, ih]
    by_cases hi : i < w.length
    · rw [List.getElem?_eq_getElem hi]
      simp only [additiveSource, Option.elim_some]
      rw [additiveLevel, additiveLevel, List.take_add_one,
        List.getElem?_eq_getElem hi, Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    · rw [List.getElem?_eq_none (by omega)]
      rw [additiveLevel, additiveLevel,
        List.take_of_length_le (by omega : w.length ≤ i + 1),
        List.take_of_length_le (by omega : w.length ≤ i)]
      simp

/-! ## The presentation -/

/-- The polyregular part: one arity-1 copy selecting EVERY in-range position; the
label is the letter at the position; the tie order is position-DESCENDING when
`dir = true` (the paper's right-to-left scan) and position-ASCENDING when
`dir = false`. -/
@[reducible] def asPoly (dir : Bool) : Polyreg.Presentation Step Step where
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
  ord := fun _ _ _ ī ī' => if dir then ī' 0 < ī 0 else ī 0 < ī' 0
  ordDef := fun c c' => by
    cases dir
    · exact ⟨.lt (Fin.castAdd 1 0) (Fin.natAdd 1 0), fun w ij => Iff.rfl⟩
    · exact ⟨.lt (Fin.natAdd 1 0) (Fin.castAdd 1 0), fun w ij => Iff.rfl⟩

/-- The WRP presentation: rank = the additive level, via `additiveSource`. -/
@[reducible] def asPres (nu : Step → ℤ) (dir : Bool) : WRP.Presentation Step Step where
  toPoly := asPoly dir
  d := 1
  rank := fun _ w ī => fun _ => additiveLevel nu w (ī ⟨0, Nat.one_pos⟩)
  rankReg := fun c => by
    refine ⟨⟨fun _ => 0, [⟨additiveSource nu, 1, ⟨0, Nat.one_pos⟩, fun _ _ _ => 0⟩]⟩, ?_⟩
    intro w ī
    funext x
    simp only [RankTerm.eval, Summand.eval, additiveSource_prefixRank,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    cases w[ī ⟨0, Nat.one_pos⟩]? <;> simp

/-! ## The atom toolkit -/

/-- The atom at input position `p`. -/
@[reducible] def asAtom (dir : Bool) (p : ℕ) : (asPoly dir).Atom := ⟨⟨0, Nat.one_pos⟩, fun _ => p⟩

/-- The position coordinate of an atom. -/
@[reducible] def asPosOf (dir : Bool) (a : (asPoly dir).Atom) : ℕ := a.2 ⟨0, Nat.one_pos⟩

@[simp] theorem asPosOf_asAtom (dir : Bool) (p : ℕ) : asPosOf dir (asAtom dir p) = p := rfl

theorem asAtom_ext (dir : Bool) {a b : (asPoly dir).Atom}
    (h : asPosOf dir a = asPosOf dir b) : a = b := by
  obtain ⟨c, f⟩ := a
  obtain ⟨c', g⟩ := b
  have hc : c = c' := by
    apply Fin.ext
    have := c.isLt
    have := c'.isLt
    have h1 : (asPoly dir).K = 1 := rfl
    omega
  cases hc
  have hfg : f = g := by
    funext t
    have ht : t = ⟨0, Nat.one_pos⟩ := by
      apply Fin.ext
      have h1 := t.isLt
      have h2 : (asPoly dir).arity c = 1 := rfl
      omega
    rw [ht]
    exact h
  rw [hfg]

theorem asAtom_injective (dir : Bool) : Function.Injective (asAtom dir) := fun p q h => by
  have := congrArg (asPosOf dir) h
  simpa using this

theorem asAtom_eta (dir : Bool) (a : (asPoly dir).Atom) : a = asAtom dir (asPosOf dir a) :=
  (asAtom_ext dir (a := asAtom dir (asPosOf dir a)) (b := a) rfl).symm

theorem as_rankOf_eval (nu : Step → ℤ) (dir : Bool) (w : List Step) (a : (asPoly dir).Atom) :
    (asPres nu dir).rankOf w a = fun _ => additiveLevel nu w (asPosOf dir a) := rfl

@[simp] theorem as_labelOf_eval (dir : Bool) (w : List Step) (p : ℕ) :
    (asPoly dir).labelOf w (asAtom dir p) = (w[p]?).getD U := rfl

/-- Selectedness is exactly in-rangeness. -/
theorem as_selectedAtom_iff (dir : Bool) (w : List Step) (a : (asPoly dir).Atom) :
    (asPoly dir).selectedAtom w a ↔ asPosOf dir a < w.length := by
  constructor
  · rintro ⟨-, hsel⟩
    exact hsel
  · intro h
    refine ⟨fun t => ?_, h⟩
    have ht : t = ⟨0, Nat.one_pos⟩ := by
      apply Fin.ext
      have h1 := t.isLt
      have h2 : (asPoly dir).arity a.1 = 1 := rfl
      omega
    rw [ht]
    exact h

/-- The order, in omega-ready normal form: level-lex, then the `dir`-conditional
position tie order. -/
theorem as_wrpOrd_iff (nu : Step → ℤ) (dir : Bool) (w : List Step) (a b : (asPoly dir).Atom) :
    (asPres nu dir).wrpOrd w a b ↔
      (additiveLevel nu w (asPosOf dir a) < additiveLevel nu w (asPosOf dir b)
        ∨ (additiveLevel nu w (asPosOf dir a) = additiveLevel nu w (asPosOf dir b)
            ∧ (if dir then asPosOf dir b < asPosOf dir a
                else asPosOf dir a < asPosOf dir b))) := by
  show (WRP.lexLt ((asPres nu dir).rankOf w a) ((asPres nu dir).rankOf w b)
      ∨ ((asPres nu dir).rankOf w a = (asPres nu dir).rankOf w b
          ∧ (asPoly dir).atomOrd w a b)) ↔ _
  rw [as_rankOf_eval, as_rankOf_eval, lexLt_one, fin1_fun_ext_iff]
  exact Iff.rfl

/-! ## Validity -/

theorem asPres_wrpOrd_irrefl (nu : Step → ℤ) (dir : Bool) (w : List Step) (a : (asPoly dir).Atom) :
    ¬ (asPres nu dir).wrpOrd w a a := by
  rw [as_wrpOrd_iff]
  cases dir <;> simp

theorem asPres_valid (nu : Step → ℤ) (dir : Bool) : (asPres nu dir).Valid where
  irrefl := fun w a _ => asPres_wrpOrd_irrefl nu dir w a
  trans := by
    intro w a b c _ _ _ hab hbc
    rw [as_wrpOrd_iff] at *
    cases dir <;> simp_all <;> omega
  trichot := by
    intro w a b _ _
    rw [as_wrpOrd_iff, as_wrpOrd_iff]
    by_cases heq : additiveLevel nu w (asPosOf dir a) = additiveLevel nu w (asPosOf dir b)
    · rcases lt_trichotomy (asPosOf dir a) (asPosOf dir b) with hp | hp | hp
      · cases dir <;>
          simp only [Bool.false_eq_true, if_false, if_true]
        · exact Or.inl (Or.inr ⟨heq, hp⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨heq.symm, hp⟩))
      · exact Or.inr (Or.inl (asAtom_ext dir hp))
      · cases dir <;>
          simp only [Bool.false_eq_true, if_false, if_true]
        · exact Or.inr (Or.inr (Or.inr ⟨heq.symm, hp⟩))
        · exact Or.inl (Or.inr ⟨heq, hp⟩)
    · rcases lt_or_gt_of_ne (fun hc => heq hc) with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))

/-! ## The sweep as a sorted normal form -/

/-- The indexed triples `(additive level, position, step)` that `additiveSweep`
sorts. -/
def asSweepIdx (nu : Step → ℤ) (w : List Step) : List (ℤ × ℕ × Step) :=
  w.zipIdx.map (fun p => (additiveLevel nu w p.2, p.2, p.1))

/-- The strict comparator used by `additiveSweep`. -/
def asCmp (dir : Bool) (a b : ℤ × ℕ × Step) : Bool :=
  if a.1 < b.1 then true else if a.1 > b.1 then false
  else (if dir then a.2.1 > b.2.1 else a.2.1 < b.2.1)

/-- A reflexive proxy comparator (`≥`/`≤` on the tie-break): total and
transitive. -/
def asCmp' (dir : Bool) (a b : ℤ × ℕ × Step) : Bool :=
  if a.1 < b.1 then true else if a.1 > b.1 then false
  else (if dir then a.2.1 ≥ b.2.1 else a.2.1 ≤ b.2.1)

theorem additiveSweep_eq (nu : Step → ℤ) (dir : Bool) (w : List Step) :
    additiveSweep nu dir w = ((asSweepIdx nu w).mergeSort (asCmp dir)).map (·.2.2) := by
  unfold additiveSweep asSweepIdx asCmp additiveLevel; rfl

theorem asCmp'_total (dir : Bool) (a b : ℤ × ℕ × Step) :
    asCmp' dir a b || asCmp' dir b a := by
  unfold asCmp'; cases dir <;> (split_ifs <;> simp_all) <;> omega

theorem asCmp'_trans (dir : Bool) (a b c : ℤ × ℕ × Step) :
    asCmp' dir a b → asCmp' dir b c → asCmp' dir a c := by
  unfold asCmp'; cases dir <;> (split_ifs <;> simp_all) <;> omega

theorem asCmp_eq_asCmp'_of_ne_pos (dir : Bool) (a b : ℤ × ℕ × Step) (h : a.2.1 ≠ b.2.1) :
    asCmp dir a b = asCmp' dir a b := by
  unfold asCmp asCmp'; cases dir <;> (split_ifs <;> simp_all) <;> omega

theorem nodup_pos_asSweepIdx (nu : Step → ℤ) (w : List Step) :
    ((asSweepIdx nu w).map (·.2.1)).Nodup := by
  unfold asSweepIdx
  rw [List.map_map]
  have hcomp : ((·.2.1) ∘ fun p : Step × ℕ => (additiveLevel nu w p.2, p.2, p.1))
      = Prod.snd := by
    funext p; rfl
  rw [hcomp, List.zipIdx_map_snd]
  exact List.nodup_range'

theorem nodup_asSweepIdx (nu : Step → ℤ) (w : List Step) : (asSweepIdx nu w).Nodup :=
  (nodup_pos_asSweepIdx nu w).of_map _

/-- A sweep triple is determined by its position. -/
theorem asSweepIdx_eq_of_pos_eq (nu : Step → ℤ) (w : List Step) {a b : ℤ × ℕ × Step}
    (ha : a ∈ asSweepIdx nu w) (hb : b ∈ asSweepIdx nu w) (hpos : a.2.1 = b.2.1) : a = b := by
  unfold asSweepIdx at ha hb
  rw [List.mem_map] at ha hb
  obtain ⟨⟨s, i⟩, hi, rfl⟩ := ha
  obtain ⟨⟨t, j⟩, hj, rfl⟩ := hb
  simp only at hpos
  subst hpos
  obtain ⟨_, hs⟩ := List.mem_zipIdx' hi
  obtain ⟨_, ht⟩ := List.mem_zipIdx' hj
  simp only [Prod.mk.injEq, true_and]
  rw [hs, ht]

/-- `additiveSweep` written via the total proxy comparator `asCmp'`. -/
theorem additiveSweep_eq' (nu : Step → ℤ) (dir : Bool) (w : List Step) :
    additiveSweep nu dir w = ((asSweepIdx nu w).mergeSort (asCmp' dir)).map (·.2.2) := by
  rw [additiveSweep_eq]
  congr 1
  exact mergeSort_congr (asCmp' dir) (asSweepIdx nu w) (asCmp dir) (nodup_asSweepIdx nu w)
    (fun a ha b hb hab => asCmp_eq_asCmp'_of_ne_pos dir a b
      (fun hpos => hab (asSweepIdx_eq_of_pos_eq nu w ha hb hpos)))

/-! ## The witness atom list: the mergeSorted sweep triples -/

/-- The triple shape: a member of `asSweepIdx nu w` is
`(additiveLevel nu w p, p, the letter at p)`. -/
theorem mem_asSweepIdx_shape (nu : Step → ℤ) {w : List Step} {z : ℤ × ℕ × Step}
    (hz : z ∈ asSweepIdx nu w) :
    z.1 = additiveLevel nu w z.2.1 ∧ z.2.1 < w.length ∧ w[z.2.1]? = some z.2.2 := by
  unfold asSweepIdx at hz
  rw [List.mem_map] at hz
  obtain ⟨⟨s, i⟩, hi, rfl⟩ := hz
  obtain ⟨hlt, hs⟩ := List.mem_zipIdx' hi
  exact ⟨rfl, hlt, by rw [List.getElem?_eq_getElem hlt, hs]⟩

/-- Every in-range position has a triple in `asSweepIdx`. -/
theorem exists_mem_asSweepIdx_of_lt (nu : Step → ℤ) {w : List Step} {p : ℕ} (hp : p < w.length) :
    ∃ z ∈ asSweepIdx nu w, z.2.1 = p := by
  have hmem : p ∈ w.zipIdx.map Prod.snd := by
    rw [List.zipIdx_map_snd]
    simp [hp]
  rw [List.mem_map] at hmem
  obtain ⟨pair, hpair, hsnd⟩ := hmem
  exact ⟨(additiveLevel nu w pair.2, pair.2, pair.1),
    List.mem_map_of_mem hpair, hsnd⟩

/-- The witness list: the sorted triples, mapped to their atoms. -/
def asAtoms (nu : Step → ℤ) (dir : Bool) (w : List Step) : List (asPoly dir).Atom :=
  ((asSweepIdx nu w).mergeSort (asCmp' dir)).map (fun z => asAtom dir z.2.1)

/-- **Membership**: the witness list contains exactly the selected atoms. -/
theorem mem_asAtoms_iff (nu : Step → ℤ) (dir : Bool) (w : List Step) (a : (asPoly dir).Atom) :
    a ∈ asAtoms nu dir w ↔ (asPoly dir).selectedAtom w a := by
  rw [as_selectedAtom_iff, asAtoms, List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' := List.mem_mergeSort.mp hz
    exact (mem_asSweepIdx_shape nu hz').2.1
  · intro h
    obtain ⟨z, hz, hzp⟩ := exists_mem_asSweepIdx_of_lt nu h
    exact ⟨z, List.mem_mergeSort.mpr hz, by rw [hzp, ← asAtom_eta]⟩

/-- **No duplicates**: positions are pairwise distinct after sorting. -/
theorem asAtoms_nodup (nu : Step → ℤ) (dir : Bool) (w : List Step) : (asAtoms nu dir w).Nodup := by
  have hperm : (((asSweepIdx nu w).mergeSort (asCmp' dir)).map (·.2.1)).Perm
      ((asSweepIdx nu w).map (·.2.1)) :=
    (List.mergeSort_perm _ _).map _
  have hnd : (((asSweepIdx nu w).mergeSort (asCmp' dir)).map (·.2.1)).Nodup :=
    hperm.nodup_iff.mpr (nodup_pos_asSweepIdx nu w)
  have : asAtoms nu dir w
      = (((asSweepIdx nu w).mergeSort (asCmp' dir)).map (·.2.1)).map (asAtom dir) := by
    rw [asAtoms, List.map_map]
    rfl
  rw [this]
  exact hnd.map (asAtom_injective dir)

/-- **Pairwise**: the sorted order is exactly `wrpOrd`. -/
theorem asAtoms_pairwise (nu : Step → ℤ) (dir : Bool) (w : List Step) :
    (asAtoms nu dir w).Pairwise ((asPres nu dir).wrpOrd w) := by
  rw [asAtoms, List.pairwise_map]
  have hsorted : (((asSweepIdx nu w).mergeSort (asCmp' dir))).Pairwise (asCmp' dir · ·) :=
    List.pairwise_mergeSort (asCmp'_trans dir) (asCmp'_total dir) _
  have hposnd : (((asSweepIdx nu w).mergeSort (asCmp' dir)).map (·.2.1)).Nodup :=
    ((List.mergeSort_perm _ _).map _).nodup_iff.mpr (nodup_pos_asSweepIdx nu w)
  have hpairne : (((asSweepIdx nu w).mergeSort (asCmp' dir))).Pairwise
      (fun z z' => z.2.1 ≠ z'.2.1) := by
    rw [← List.pairwise_map (f := fun z : ℤ × ℕ × Step => z.2.1)]
    exact hposnd
  refine (hsorted.and hpairne).imp_of_mem (fun {z z'} hz hz' hzz => ?_)
  obtain ⟨hcmp, hne⟩ := hzz
  have hz1 := mem_asSweepIdx_shape nu (List.mem_mergeSort.mp hz)
  have hz1' := mem_asSweepIdx_shape nu (List.mem_mergeSort.mp hz')
  rw [as_wrpOrd_iff]
  simp only [asPosOf_asAtom]
  rw [← hz1.1, ← hz1'.1]
  unfold asCmp' at hcmp
  cases dir <;>
    (simp only [Bool.false_eq_true, if_false, if_true] at hcmp ⊢
     split_ifs at hcmp with h1 h2
     · exact Or.inl h1
     · simp only [decide_eq_true_eq] at hcmp
       exact Or.inr ⟨by omega, by omega⟩)

/-- **The label map**: the witness labels are exactly the additive sweep. -/
theorem map_labelOf_asAtoms (nu : Step → ℤ) (dir : Bool) (w : List Step) :
    (asAtoms nu dir w).map ((asPoly dir).labelOf w) = additiveSweep nu dir w := by
  rw [additiveSweep_eq', asAtoms, List.map_map]
  refine List.map_congr_left ?_
  intro z hz
  have hsh := mem_asSweepIdx_shape nu (List.mem_mergeSort.mp hz)
  show (asPoly dir).labelOf w (asAtom dir z.2.1) = z.2.2
  rw [as_labelOf_eval, hsh.2.2]
  rfl

/-- **The sweep is the declarative output.** -/
theorem additiveSweep_isOutput (nu : Step → ℤ) (dir : Bool) (w : List Step) :
    (asPres nu dir).IsOutput w (additiveSweep nu dir w) :=
  ⟨asAtoms nu dir w, asAtoms_nodup nu dir w, mem_asAtoms_iff nu dir w,
    asAtoms_pairwise nu dir w, (map_labelOf_asAtoms nu dir w).symm⟩

/-! ## The scan tie-order -/

/-- The additive-sweep presentation has a genuine scan tie-order: arity 1, the
`dir`-conditional position order, and the (vacuous, `K = 1`) copy order.  The
`dir` Bool of the scan order is the negation of `additiveSweep`'s `rightToLeft`:
`additiveSweep`'s `dir = true` (right-to-left, position-descending) corresponds
to the scan-order direction `false`. -/
theorem asPoly_isScanOrder (dir : Bool) : (asPoly dir).IsScanOrder := by
  refine ⟨fun _ => rfl, !dir, fun _ _ => False, ?_, ?_, ?_, ?_⟩
  · intro c h; exact h
  · intro x y z h _; exact h.elim
  · intro x y
    refine Or.inr (Or.inl (Fin.ext ?_))
    have hx : (x : ℕ) < 1 := x.2
    have hy : (y : ℕ) < 1 := y.2
    omega
  · intro w a b
    simp only [Polyreg.Presentation.atomOrd, Polyreg.Presentation.pos1, asPoly,
      and_false, or_false]
    cases dir <;> rfl

/-! ## The main theorems -/

/-- **`prop:alw-sweep-swr` (`prop:alw-sweep-swr`, paper.tex), genuine.**  Every
additive sweep transduction `Φ_ν`, for ARBITRARY integer step weights `ν` and a
scan direction `dir`, is a stable one-dimensional rank sweep (`WRP.IsSRR1`). -/
theorem additiveSweep_isSRR1 (nu : Step → ℤ) (dir : Bool) :
    WRP.IsSRR1 (fun w : List Step => some (additiveSweep nu dir w)) :=
  ⟨asPres nu dir, asPres_valid nu dir, rfl, asPoly_isScanOrder dir,
   fun w _out =>
     ⟨fun h => ⟨trivial, (Option.some.inj h) ▸ additiveSweep_isOutput nu dir w⟩,
      fun ⟨_, hout⟩ => congrArg some
        (isOutput_unique (asPres nu dir) (asPres_valid nu dir)
          (additiveSweep_isOutput nu dir w) hout)⟩⟩

/-- **`prop:alw-sweep-swr` (`prop:alw-sweep-swr`, paper.tex), consequence.**  Every
additive sweep transduction is WRP, via the inclusion chain `sRR₁ ⊆ RR ⊆ WRP`. -/
theorem additiveSweep_isWRP (nu : Step → ℤ) (dir : Bool) :
    WRP.IsWRP (fun w : List Step => some (additiveSweep nu dir w)) :=
  (additiveSweep_isSRR1 nu dir).isWRP

-- Axiom check (axiom-clean): both depend only on `[propext, Classical.choice, Quot.sound]`.
-- #print axioms additiveSweep_isSRR1
-- #print axioms additiveSweep_isWRP
