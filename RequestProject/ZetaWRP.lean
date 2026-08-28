/-
# The zeta map is a WRP transduction (`thm:zeta-wrp`) — the GENUINE theorem

Formalises the paper's positive theorem (`thm:zeta-wrp`, §`sec:zeta-positive`
of paper.tex): the Haglund zeta map is realised by a weighted-rank
polyregular transduction, over the concrete model of `WRP.lean`.

The presentation is the paper's: the one-state height source (`ω(U) = +1`,
`ω(D) = −1`), two atoms per `U`-position — label `U` at rank `ρ(i)`, label `D`
at rank `ρ(i) + 1` — and the left-to-right (position-only) tie order.

**A subtlety the design phase caught**: the naive statement
`WRP.IsWRP (fun w => some (zetaMap w))` is FALSE.  `zetaMap` runs its levels
over `0 .. maxA + 1`, so on a word with NEGATIVE area-sequence entries the
`U`-emission of such an entry never fires: `zetaMap [D, U] = [D]`, while every
paper-faithful presentation selects both atoms at the `U`-position and outputs
`[U, D]`.  Since the `IsWRP` biconditional forces output agreement on EVERY
word of the (regular) domain and the Dyck language is not regular, no domain
choice rescues the literal statement.  The fix is `zetaSweep`, the
integer-level totalisation (levels from `foldl min` to `foldl max + 1`); it is
WRP outright (`zetaSweep_isWRP`), agrees with `zetaMap` on every word with
nonnegative area sequence — in particular on all Dyck paths — and therefore
realises `zetaMap` on the Dyck domain (`zetaMap_realisedByWRP`), which is
exactly the paper's claim.

Trust base: `[propext, Classical.choice, Quot.sound]` — no Büchi axiom; the
MSO formulas are exhibited directly.
-/
import RequestProject.WRP
import RequestProject.ZetaClassification
import RequestProject.Transducers

open MSO Step

/-! ## Foldl-min preliminaries (mirroring the foldl-max lemmas) -/

theorem foldl_min_le_acc (a : List ℤ) : ∀ acc : ℤ, a.foldl min acc ≤ acc := by
  induction a with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    calc (x :: xs).foldl min acc = xs.foldl min (min acc x) := rfl
      _ ≤ min acc x := ih (min acc x)
      _ ≤ acc := min_le_left _ _

theorem foldl_min_le (a : List ℤ) : ∀ x ∈ a, ∀ acc : ℤ, a.foldl min acc ≤ x := by
  induction a with
  | nil => intro x hx; exact absurd hx (List.not_mem_nil)
  | cons y ys ih =>
    intro x hx acc
    rcases List.mem_cons.mp hx with rfl | hx'
    · calc (x :: ys).foldl min acc = ys.foldl min (min acc x) := rfl
        _ ≤ min acc x := foldl_min_le_acc ys (min acc x)
        _ ≤ x := min_le_right _ _
    · exact ih x hx' (min acc y)

theorem nonneg_foldl_min (a : List ℤ) (h : ∀ x ∈ a, 0 ≤ x) :
    ∀ acc : ℤ, 0 ≤ acc → 0 ≤ a.foldl min acc := by
  induction a with
  | nil => intro acc hacc; simpa using hacc
  | cons x xs ih =>
    intro acc hacc
    have hx : 0 ≤ x := h x List.mem_cons_self
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy)) (min acc x)
      (le_min hacc hx)

theorem foldl_min_eq_zero_of_nonneg (a : List ℤ) (h : ∀ x ∈ a, 0 ≤ x) :
    a.foldl min 0 = 0 :=
  le_antisymm (foldl_min_le_acc a 0) (nonneg_foldl_min a h 0 le_rfl)

/-! ## The one-state height rank source and the prefix-rank bridge -/

/-- The paper's one-state additive rank source computing the height:
`ω(U) = +1`, `ω(D) = −1`. -/
def heightSource : RankSource Step 1 where
  Q := Unit
  fintypeQ := inferInstance
  q0 := ()
  δ := fun _ _ => ()
  ω := fun _ s _ => match s with | U => 1 | D => -1

/-- **The bridge**: the height source's prefix rank is the height function. -/
theorem heightSource_prefixRank (w : List Step) (i : ℕ) :
    heightSource.prefixRank w i = fun _ => height w i := by
  funext x
  induction i with
  | zero => simp [RankSource.prefixRank, height]
  | succ i ih =>
    rw [RankSource.prefixRank, Finset.sum_range_succ,
      ← RankSource.prefixRank, ih]
    by_cases hi : i < w.length
    · rw [List.getElem?_eq_getElem hi]
      rcases hU : w[i] with _ | _
      · rw [height_succ_of_get_U w i hi hU]
        simp [heightSource]
      · rw [height_succ_of_get_D w i hi hU]
        simp [heightSource]
        omega
    · rw [List.getElem?_eq_none (by omega)]
      rw [height_of_length_le w (i + 1) (by omega),
        height_of_length_le w i (by omega)]
      simp

/-! ## Dimension-1 normal forms -/

theorem lexLt_one (x y : Fin 1 → ℤ) : WRP.lexLt x y ↔ x 0 < y 0 := by
  constructor
  · rintro ⟨i, -, hi⟩
    rwa [Fin.fin_one_eq_zero i] at hi
  · intro h
    exact ⟨0, fun j hj => absurd hj (by rw [Fin.fin_one_eq_zero j]; exact lt_irrefl _), h⟩

theorem fin1_fun_ext_iff (f g : Fin 1 → ℤ) : f = g ↔ f 0 = g 0 := by
  constructor
  · intro h; rw [h]
  · intro h
    funext t
    rwa [Fin.fin_one_eq_zero t]

/-! ## The presentation -/

/-- The polyregular part: two arity-1 copies, both selecting the `U`-positions;
copy 0 labelled `U`, copy 1 labelled `D`; position-only tie order; total
domain (the Dyck language is not regular, and the sweep is total anyway). -/
@[reducible] def zetaPoly : Polyreg.Presentation Step Step where
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
  ord := fun _ _ _ ī ī' => ī 0 < ī' 0
  ordDef := fun c c' => ⟨.lt (Fin.castAdd 1 0) (Fin.natAdd 1 0), fun w ij => Iff.rfl⟩

/-- The WRP presentation: rank = height at the position, plus the copy index
(so the `D`-atom of a `U`-position trails its `U`-atom by one level). -/
@[reducible] def zetaPres : WRP.Presentation Step Step where
  toPoly := zetaPoly
  d := 1
  rank := fun c w ī => fun _ => height w (ī ⟨0, Nat.one_pos⟩) + (c.val : ℤ)
  rankReg := fun c => by
    refine ⟨⟨fun _ => (c.val : ℤ),
      [⟨heightSource, 1, ⟨0, Nat.one_pos⟩, fun _ _ _ => 0⟩]⟩, ?_⟩
    intro w ī
    funext x
    simp only [RankTerm.eval, Summand.eval, heightSource_prefixRank,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    cases w[ī ⟨0, Nat.one_pos⟩]? <;> simp <;> ring

/-! ## The atom toolkit -/

/-- Build the `c`-copy atom at word position `p`. -/
@[reducible] def zetaAtom (c : Fin 2) (p : ℕ) : zetaPoly.Atom := ⟨c, fun _ => p⟩

example : zetaPoly.Atom = (Σ _ : Fin 2, Fin 1 → ℕ) := rfl

/-- The (single) position coordinate of an atom. -/
@[reducible] def atomPos (a : zetaPoly.Atom) : ℕ := a.2 ⟨0, Nat.one_pos⟩

@[simp] theorem atomPos_zetaAtom (c : Fin 2) (p : ℕ) : atomPos (zetaAtom c p) = p := rfl

@[simp] theorem labelOf_zetaAtom_zero (w : List Step) (p : ℕ) :
    zetaPoly.labelOf w (zetaAtom 0 p) = U := rfl

@[simp] theorem labelOf_zetaAtom_one (w : List Step) (p : ℕ) :
    zetaPoly.labelOf w (zetaAtom 1 p) = D := rfl

theorem rankOf_eval (w : List Step) (a : zetaPoly.Atom) :
    zetaPres.rankOf w a = fun _ => height w (atomPos a) + (a.1.val : ℤ) := rfl

/-- Atoms are determined by copy and position. -/
theorem zetaAtom_ext {a b : zetaPoly.Atom} (h1 : a.1 = b.1)
    (h2 : atomPos a = atomPos b) : a = b := by
  obtain ⟨c, f⟩ := a
  obtain ⟨c', g⟩ := b
  cases h1
  have hfg : f = g := by
    funext t
    have ht : t = ⟨0, Nat.one_pos⟩ := by
      apply Fin.ext
      have h1 := t.isLt
      have h2 : zetaPoly.arity c = 1 := rfl
      omega
    rw [ht]
    exact h2
  rw [hfg]

theorem zetaAtom_eta (a : zetaPoly.Atom) : a = zetaAtom a.1 (atomPos a) :=
  (zetaAtom_ext (a := zetaAtom a.1 (atomPos a)) (b := a) rfl rfl).symm

/-- Selectedness is exactly "the position carries a `U`". -/
theorem selectedAtom_iff (w : List Step) (a : zetaPoly.Atom) :
    zetaPoly.selectedAtom w a ↔ w[atomPos a]? = some U := by
  constructor
  · rintro ⟨-, hsel⟩
    exact hsel
  · intro h
    refine ⟨fun t => ?_, h⟩
    have ht : t = ⟨0, Nat.one_pos⟩ := by
      apply Fin.ext
      have h1 := t.isLt
      have h2 : zetaPoly.arity a.1 = 1 := rfl
      omega
    rw [ht]
    exact (List.getElem?_eq_some_iff.mp h).1

/-- The order, in omega-ready normal form: rank-lex then position. -/
theorem wrpOrd_iff (w : List Step) (a b : zetaPoly.Atom) :
    zetaPres.wrpOrd w a b ↔
      (height w (atomPos a) + (a.1.val : ℤ) < height w (atomPos b) + (b.1.val : ℤ)
        ∨ (height w (atomPos a) + (a.1.val : ℤ) = height w (atomPos b) + (b.1.val : ℤ)
            ∧ atomPos a < atomPos b)) := by
  show (WRP.lexLt (zetaPres.rankOf w a) (zetaPres.rankOf w b)
      ∨ (zetaPres.rankOf w a = zetaPres.rankOf w b ∧ zetaPoly.atomOrd w a b)) ↔ _
  rw [rankOf_eval, rankOf_eval, lexLt_one, fin1_fun_ext_iff]
  exact Iff.rfl

/-! ## Validity and the generic output-uniqueness lemma -/

theorem zetaPres_wrpOrd_irrefl (w : List Step) (a : zetaPoly.Atom) :
    ¬ zetaPres.wrpOrd w a a := by
  rw [wrpOrd_iff]
  omega

theorem zetaPres_valid : zetaPres.Valid where
  irrefl := fun w a _ => zetaPres_wrpOrd_irrefl w a
  trans := by
    intro w a b c _ _ _ hab hbc
    rw [wrpOrd_iff] at *
    omega
  trichot := by
    intro w a b _ _
    rw [wrpOrd_iff, wrpOrd_iff]
    by_cases heq : height w (atomPos a) + (a.1.val : ℤ)
        = height w (atomPos b) + (b.1.val : ℤ)
    · rcases lt_trichotomy (atomPos a) (atomPos b) with hp | hp | hp
      · exact Or.inl (Or.inr ⟨heq, hp⟩)
      · refine Or.inr (Or.inl (zetaAtom_ext ?_ hp))
        apply Fin.ext
        rw [hp] at heq
        omega
      · exact Or.inr (Or.inr (Or.inr ⟨heq.symm, hp⟩))
    · rcases lt_or_gt_of_ne (fun hc => heq hc) with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))

/-! ## The total sweep and its witness atoms -/

/-- The least level: the minimum of the area sequence against `0`. -/
def zetaLo (w : List Step) : ℤ := (areaSeq w).foldl min 0

/-- The greatest level base: the maximum of the area sequence against `0`. -/
def zetaHi (w : List Step) : ℤ := (areaSeq w).foldl max 0

/-- The number of levels swept. -/
def zetaLevels (w : List Step) : ℕ := (zetaHi w + 2 - zetaLo w).toNat

/-- **The integer-level totalisation of the zeta map**: sweep every level from
`zetaLo` to `zetaHi + 1`, emitting per area entry as `zetaMap` does.  Equal to
`zetaMap` whenever the area sequence is nonnegative (so on all Dyck paths). -/
def zetaSweep (w : List Step) : List Step :=
  (List.range (zetaLevels w)).flatMap fun (k : ℕ) =>
    (areaSeq w).flatMap (zEmit (zetaLo w + (k : ℤ)))

/-- The atoms emitted at level `r`: per `U`-position, the `U`-atom if its
height is `r`, the `D`-atom if its height is `r - 1`. -/
def zetaAtomsAt (w : List Step) (r : ℤ) : List zetaPoly.Atom :=
  (uPositions w).flatMap fun p =>
    if height w p = r then [zetaAtom 0 p]
    else if height w p = r - 1 then [zetaAtom 1 p] else []

/-- The full witness list, level by level. -/
def zetaAtoms (w : List Step) : List zetaPoly.Atom :=
  (List.range (zetaLevels w)).flatMap fun (k : ℕ) =>
    zetaAtomsAt w (zetaLo w + (k : ℤ))

@[simp] theorem zetaAtom_fst (c : Fin 2) (p : ℕ) : (zetaAtom c p).1 = c := rfl

theorem mem_zetaAtomsAt {w : List Step} {r : ℤ} {x : zetaPoly.Atom} :
    x ∈ zetaAtomsAt w r ↔ ∃ p ∈ uPositions w,
      (height w p = r ∧ x = zetaAtom 0 p) ∨ (height w p = r - 1 ∧ x = zetaAtom 1 p) := by
  rw [zetaAtomsAt, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hx⟩
    split_ifs at hx with h1 h2
    · exact ⟨p, hp, Or.inl ⟨h1, List.mem_singleton.mp hx⟩⟩
    · exact ⟨p, hp, Or.inr ⟨h2, List.mem_singleton.mp hx⟩⟩
    · exact absurd hx List.not_mem_nil
  · rintro ⟨p, hp, ⟨h1, rfl⟩ | ⟨h2, rfl⟩⟩
    · exact ⟨p, hp, by rw [if_pos h1]; exact List.mem_singleton.mpr rfl⟩
    · refine ⟨p, hp, ?_⟩
      rw [if_neg (by omega), if_pos h2]
      exact List.mem_singleton.mpr rfl

/-- **Rank constancy**: every atom emitted at level `r` has rank exactly `r`. -/
theorem rankOf_of_mem_zetaAtomsAt {w : List Step} {r : ℤ} {x : zetaPoly.Atom}
    (hx : x ∈ zetaAtomsAt w r) : zetaPres.rankOf w x = fun _ => r := by
  obtain ⟨p, -, ⟨h1, rfl⟩ | ⟨h2, rfl⟩⟩ := mem_zetaAtomsAt.mp hx <;>
  · rw [rankOf_eval]
    funext t
    simp only [atomPos_zetaAtom, Fin.val_zero, Fin.val_one]
    omega

theorem pos_mem_of_mem_zetaAtomsAt {w : List Step} {r : ℤ} {x : zetaPoly.Atom}
    (hx : x ∈ zetaAtomsAt w r) : atomPos x ∈ uPositions w := by
  obtain ⟨p, hp, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := mem_zetaAtomsAt.mp hx <;> simpa

/-- **Labels per level**: mapping `labelOf` over the level-`r` atoms is exactly
the level-`r` block of the sweep. -/
theorem map_labelOf_zetaAtomsAt (w : List Step) (r : ℤ) :
    (zetaAtomsAt w r).map (zetaPoly.labelOf w) = (areaSeq w).flatMap (zEmit r) := by
  rw [areaSeq, List.flatMap_map, zetaAtomsAt, List.map_flatMap]
  have hfun : (fun p => (if height w p = r then [zetaAtom 0 p]
        else if height w p = r - 1 then [zetaAtom 1 p] else []).map
          (zetaPoly.labelOf w))
      = fun p => zEmit r (height w p) := by
    funext p
    rw [zEmit]
    split_ifs with h1 h2 <;> simp
  rw [hfun]

/-! ## The four `IsOutput` obligations -/

/-- **Membership**: the witness list contains exactly the selected atoms. -/
theorem mem_zetaAtoms_iff (w : List Step) (a : zetaPoly.Atom) :
    a ∈ zetaAtoms w ↔ zetaPoly.selectedAtom w a := by
  rw [selectedAtom_iff, zetaAtoms, List.mem_flatMap]
  constructor
  · rintro ⟨k, -, hx⟩
    obtain ⟨p, hp, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := mem_zetaAtomsAt.mp hx <;>
    · obtain ⟨hlt, hU⟩ := mem_uPositions.mp hp
      simp [List.getElem?_eq_getElem hlt, hU]
  · intro h
    have hp : atomPos a ∈ uPositions w := mem_uPositions_of_getElem? h
    have hmem : height w (atomPos a) ∈ areaSeq w := by
      rw [areaSeq]
      exact List.mem_map_of_mem hp
    have hlo : zetaLo w ≤ height w (atomPos a) := foldl_min_le _ _ hmem 0
    have hhi : height w (atomPos a) ≤ zetaHi w := le_foldl_max _ _ hmem 0
    have hlo0 : zetaLo w ≤ 0 := foldl_min_le_acc _ 0
    have hhi0 : (0 : ℤ) ≤ zetaHi w := foldl_max_ge_acc _ 0
    have hlev : (zetaLevels w : ℤ) = zetaHi w + 2 - zetaLo w := by
      rw [zetaLevels, Int.toNat_of_nonneg (by omega)]
    by_cases hc : a.1 = (0 : Fin 2)
    · have hcast : (((height w (atomPos a) - zetaLo w).toNat : ℤ))
          = height w (atomPos a) - zetaLo w := Int.toNat_of_nonneg (by omega)
      have hk : (height w (atomPos a) - zetaLo w).toNat ∈ List.range (zetaLevels w) :=
        List.mem_range.mpr (by omega)
      have heta : a = zetaAtom 0 (atomPos a) := by
        have h0 := zetaAtom_eta a
        rw [hc] at h0
        exact h0
      refine ⟨(height w (atomPos a) - zetaLo w).toNat, hk, mem_zetaAtomsAt.mpr
        ⟨atomPos a, hp, Or.inl ⟨?_, heta⟩⟩⟩
      rw [hcast]
      ring
    · have hc1 : a.1 = (1 : Fin 2) := by
        have h2 : a.1.val < 2 := a.1.isLt
        have h0 : a.1.val ≠ 0 := fun hcc => hc (Fin.ext hcc)
        apply Fin.ext
        show a.1.val = 1
        omega
      have hcast : (((height w (atomPos a) + 1 - zetaLo w).toNat : ℤ))
          = height w (atomPos a) + 1 - zetaLo w := Int.toNat_of_nonneg (by omega)
      have hk : (height w (atomPos a) + 1 - zetaLo w).toNat ∈ List.range (zetaLevels w) :=
        List.mem_range.mpr (by omega)
      have heta : a = zetaAtom 1 (atomPos a) := by
        have h0 := zetaAtom_eta a
        rw [hc1] at h0
        exact h0
      refine ⟨(height w (atomPos a) + 1 - zetaLo w).toNat, hk, mem_zetaAtomsAt.mpr
        ⟨atomPos a, hp, Or.inr ⟨?_, heta⟩⟩⟩
      rw [hcast]
      ring

/-- **Pairwise within a level**: positions strictly increase, ranks are equal. -/
theorem zetaAtomsAt_pairwise (w : List Step) (r : ℤ) :
    (zetaAtomsAt w r).Pairwise (zetaPres.wrpOrd w) := by
  rw [zetaAtomsAt, List.pairwise_flatMap]
  constructor
  · intro p hp
    split_ifs <;> simp
  · refine (uPositions_pairwise_lt w).imp ?_
    intro p q hpq x hx y hy
    have hxe : x = zetaAtom 0 p ∨ x = zetaAtom 1 p := by
      split_ifs at hx with h1 h2
      · exact Or.inl (List.mem_singleton.mp hx)
      · exact Or.inr (List.mem_singleton.mp hx)
      · exact absurd hx List.not_mem_nil
    have hxr : height w (atomPos x) + (x.1.val : ℤ) = r := by
      split_ifs at hx with h1 h2
      · obtain rfl := List.mem_singleton.mp hx
        simp only [atomPos_zetaAtom, Fin.val_zero]
        omega
      · obtain rfl := List.mem_singleton.mp hx
        simp only [atomPos_zetaAtom, Fin.val_one]
        omega
      · exact absurd hx List.not_mem_nil
    have hyr : height w (atomPos y) + (y.1.val : ℤ) = r := by
      split_ifs at hy with h1 h2
      · obtain rfl := List.mem_singleton.mp hy
        simp only [atomPos_zetaAtom, Fin.val_zero]
        omega
      · obtain rfl := List.mem_singleton.mp hy
        simp only [atomPos_zetaAtom, Fin.val_one]
        omega
      · exact absurd hy List.not_mem_nil
    have hxp : atomPos x = p := by
      rcases hxe with rfl | rfl <;> simp
    have hyp : atomPos y = q := by
      split_ifs at hy with h1 h2
      · obtain rfl := List.mem_singleton.mp hy; simp
      · obtain rfl := List.mem_singleton.mp hy; simp
      · exact absurd hy List.not_mem_nil
    rw [wrpOrd_iff]
    omega

/-- **Pairwise globally**: levels strictly increase in rank. -/
theorem zetaAtoms_pairwise (w : List Step) :
    (zetaAtoms w).Pairwise (zetaPres.wrpOrd w) := by
  rw [zetaAtoms, List.pairwise_flatMap]
  refine ⟨fun k _ => zetaAtomsAt_pairwise w _, ?_⟩
  refine List.pairwise_lt_range.imp ?_
  intro k k' hkk x hx y hy
  have hxr := congrFun ((rankOf_eval w x).symm.trans (rankOf_of_mem_zetaAtomsAt hx))
    ⟨0, Nat.one_pos⟩
  have hyr := congrFun ((rankOf_eval w y).symm.trans (rankOf_of_mem_zetaAtomsAt hy))
    ⟨0, Nat.one_pos⟩
  simp only [] at hxr hyr
  rw [wrpOrd_iff]
  have hcast : (k : ℤ) < (k' : ℤ) := by exact_mod_cast hkk
  omega

/-- **No duplicates** (from irreflexivity of the order). -/
theorem zetaAtoms_nodup (w : List Step) : (zetaAtoms w).Nodup := by
  refine (zetaAtoms_pairwise w).imp ?_
  intro a b hab heq
  subst heq
  exact zetaPres_wrpOrd_irrefl w a hab

/-- **The label map**: the witness list's labels are exactly the sweep. -/
theorem map_labelOf_zetaAtoms (w : List Step) :
    (zetaAtoms w).map (zetaPoly.labelOf w) = zetaSweep w := by
  rw [zetaAtoms, zetaSweep, List.map_flatMap]
  have hfun : (fun (k : ℕ) => (zetaAtomsAt w (zetaLo w + (k : ℤ))).map
        (zetaPoly.labelOf w))
      = fun (k : ℕ) => (areaSeq w).flatMap (zEmit (zetaLo w + (k : ℤ))) :=
    funext fun k => map_labelOf_zetaAtomsAt w _
  rw [hfun]

/-- **The sweep is the declarative output.** -/
theorem zetaSweep_isOutput (w : List Step) : zetaPres.IsOutput w (zetaSweep w) :=
  ⟨zetaAtoms w, zetaAtoms_nodup w, mem_zetaAtoms_iff w, zetaAtoms_pairwise w,
    (map_labelOf_zetaAtoms w).symm⟩

/-! ## The main theorems -/

/-- **The totalised zeta sweep is a WRP transduction** — the first genuine
positive membership theorem for the concrete class `WRP.IsWRP`. -/
theorem zetaSweep_isWRP : WRP.IsWRP (fun w : List Step => some (zetaSweep w)) :=
  ⟨zetaPres, zetaPres_valid, fun w _out =>
    ⟨fun h => ⟨trivial, (Option.some.inj h) ▸ zetaSweep_isOutput w⟩,
     fun ⟨_, hout⟩ => congrArg some
       (isOutput_unique zetaPres zetaPres_valid (zetaSweep_isOutput w) hout)⟩⟩

/-- On nonnegative area sequences the totalised sweep IS the zeta map. -/
theorem zetaSweep_eq_zetaMap_of_nonneg (P : List Step)
    (h : ∀ x ∈ areaSeq P, 0 ≤ x) : zetaSweep P = zetaMap P := by
  have hlo : zetaLo P = 0 := foldl_min_eq_zero_of_nonneg _ h
  have hhi : (0 : ℤ) ≤ zetaHi P := foldl_max_ge_acc _ 0
  have hlev : zetaLevels P = (zetaHi P).toNat + 2 := by
    rw [zetaLevels, hlo]
    omega
  rw [zetaMap_eq_zAcc, zetaSweep, hlev, hlo, zAcc]
  have hfun : (fun (k : ℕ) => (areaSeq P).flatMap (zEmit ((0 : ℤ) + (k : ℤ))))
      = zBlock (areaSeq P) := by
    funext k
    rw [zBlock, zero_add]
  rw [hfun]
  rfl

/-- On Dyck paths the totalised sweep IS the zeta map. -/
theorem zetaSweep_eq_zetaMap_of_isDyckPath (P : List Step) (hP : IsDyckPath P) :
    zetaSweep P = zetaMap P :=
  zetaSweep_eq_zetaMap_of_nonneg P (areaSeq_nonneg P hP)

/-- **The zeta map is realised by a WRP transduction on the Dyck domain**
(`thm:zeta-wrp`): the paper's positive theorem, genuinely. -/
theorem zetaMap_realisedByWRP :
    ∃ T : List Step → Option (List Step),
      WRP.IsWRP T ∧ Realises T {P | IsDyckPath P} zetaMap :=
  ⟨fun w => some (zetaSweep w), zetaSweep_isWRP,
   fun P hP => congrArg some (zetaSweep_eq_zetaMap_of_isDyckPath P hP)⟩

/-- The graded form: the realising transduction works on every `DyckPath n`. -/
theorem zetaMap_realisedByWRP_dyckPath (n : ℕ) :
    Realises (fun w => some (zetaSweep w)) (DyckPath n) zetaMap :=
  fun P hP => congrArg some (zetaSweep_eq_zetaMap_of_isDyckPath P hP.1)

/-! ## The obstruction, documented

The naive statement `WRP.IsWRP (fun w => some (zetaMap w))` is FALSE: `zetaMap`
truncates negative levels, so on `[D, U]` it outputs `[D]` while every
paper-faithful presentation outputs `[U, D]` — and `zetaSweep` does. -/

example : zetaMap [D, U] = [D] := by decide

example : zetaSweep [D, U] = [U, D] := by decide

example : zetaSweep [U, U, D, D, U, D] = zetaMap [U, U, D, D, U, D] := by decide
