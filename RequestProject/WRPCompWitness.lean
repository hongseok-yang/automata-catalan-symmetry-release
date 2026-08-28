/-
# The revision's composition witness `D` (`thm:wrp-not-closed`, claim 1)

paper-full-new.tex strengthens `thm:wrp-not-closed` (line 1674): the same
witness map `D` must serve both the regular-preimage failure AND the
composition failure `S ∘ D ∉ WRP` (Appendix A.4, lines 4602–4695).  The old
witness `WRPNotClosed.wncD` emits only the diagnostic block; the revision's
`D` (Appendix A.4, "The map `D`") emits **three blocks**

    D(w)  =  (diagnostic `G`/`B` block, sorted by prefix height)  ‖  #  ‖  w

over the output alphabet `Γ_D = {G, B, #, U, D}` (`GBD` below), the blocks
kept apart by a leading block-tag rank coordinate — which is exactly the
`ccPres` mechanism of the concatenation closure (`WRPClosures.isWRP_concat`),
"exactly as in the concatenation construction of Theorem thm:wrp-closures"
(paper-full-new.tex).

This file builds the revision's `D` from proved ingredients and proves claim 1:

* `idPoly` / `idStep_isWRP` — the identity transduction `w ↦ w` on step words
  is (arity-1, rank-free) polyregular, hence WRP: the verbatim block-2 copy;
* `compD = (relabelled wncD) ‖ # ‖ (relabelled identity)` via
  `isWRP_relabel` + `isWRP_concat`  (`compD_isWRP`);
* `compK = G·Γ_D^*` is regular (`compK_isRegular`, explicit 3-state `DFA'`);
* `head_compD_eq_g_iff`: the first output letter is `G` iff `w ∈ Lnn`
  (inherited from `WRPNotClosed.head_wncD_eq_g_iff`);
* `preimage_compK_eq_Lnn` and the claim-1 package
  `wrp_not_closed_preimage_comp`: `D⁻¹(K) = Lnn` is not regular.

(The Lean `compD` differs from the paper's `D` only at the empty input:
`wncD`'s sentinel copy has arity `0`, so `compD ε = G#` while the revision's
arity-`≥1` convention gives `D(ε) = ε` — see `WRPArityPos.lean`.  Claim 1 is
insensitive to this: `ε ∈ Lnn` on both readings.  So is the composition
clause: `S` maps both `G#` and `ε` to `ε`.)

The composition clause itself (the 2DFT `S`, `S ∘ D = F_{≥0} ∉ WRP`) is
`WRPNotClosedComp.lean`.
-/
import RequestProject.WRPNotClosed
import RequestProject.WRPClosures

open MSO Step WRPNotClosed

namespace WRPComp

/-! ## The output alphabet `Γ_D = {G, B, #, U, D}` (paper-full-new.tex) -/

/-- The revision's five-letter output alphabet for the witness `D`:
`g`/`b` for the diagnostic block, `sep` for `#`, `u`/`d` for the verbatim
input copy. -/
inductive GBD | g | b | sep | u | d
  deriving DecidableEq

instance : Fintype GBD :=
  ⟨⟨{.g, .b, .sep, .u, .d}, by decide⟩, fun x => by cases x <;> decide⟩

/-! ## The identity transduction is WRP

Block 2 of the revision's witness is "a verbatim copy of the input, position
`i` emitting `w_i` […] in input order" (paper-full-new.tex).  We
build it as an arity-1, single-copy, rank-free polyregular presentation:
select every in-range position, label it with its own letter, order by
position. -/

/-- The label class "`the letter at the position is D`" is MSO-definable. -/
private theorem idLabelD :
    MSODefinableRel (Alpha := Step) 1
      (fun w (ī : Fin 1 → ℕ) => (if w[ī ⟨0, Nat.one_pos⟩]? = some D then D else U) = D) := by
  refine ⟨Formula.labelEq 0 D, fun w ρ => ?_⟩
  show (if w[ρ ⟨0, Nat.one_pos⟩]? = some D then D else U) = D ↔ w[ρ ⟨0, Nat.one_pos⟩]? = some D
  by_cases h : w[ρ ⟨0, Nat.one_pos⟩]? = some D
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun hUD => absurd hUD (by decide), fun hD => absurd hD h⟩

/-- The label class "`the letter at the position is U`" (equivalently, on the
two-letter alphabet: not `D`) is MSO-definable. -/
private theorem idLabelU :
    MSODefinableRel (Alpha := Step) 1
      (fun w (ī : Fin 1 → ℕ) => (if w[ī ⟨0, Nat.one_pos⟩]? = some D then D else U) = U) := by
  refine ⟨Formula.neg (Formula.labelEq 0 D), fun w ρ => ?_⟩
  show (if w[ρ ⟨0, Nat.one_pos⟩]? = some D then D else U) = U ↔ ¬ (w[ρ ⟨0, Nat.one_pos⟩]? = some D)
  by_cases h : w[ρ ⟨0, Nat.one_pos⟩]? = some D
  · rw [if_pos h]
    exact ⟨fun hDU => absurd hDU (by decide), fun hn => absurd h hn⟩
  · rw [if_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩

/-- The label classes of the identity presentation are MSO-definable. -/
private theorem idLabelDef (γ : Step) :
    MSODefinableRel (Alpha := Step) 1
      (fun w (ī : Fin 1 → ℕ) => (if w[ī ⟨0, Nat.one_pos⟩]? = some D then D else U) = γ) := by
  cases γ
  · exact idLabelU
  · exact idLabelD

/-- The position order on a pair of arity-1 atoms is MSO-definable. -/
private theorem idOrdDef :
    MSODefinableRel (Alpha := Step) (1 + 1)
      (fun _ (ij : Fin (1 + 1) → ℕ) =>
        ij (Fin.castAdd 1 ⟨0, Nat.one_pos⟩) < ij (Fin.natAdd 1 ⟨0, Nat.one_pos⟩)) :=
  ⟨Formula.lt (Fin.castAdd 1 ⟨0, Nat.one_pos⟩) (Fin.natAdd 1 ⟨0, Nat.one_pos⟩),
   fun _ _ => Iff.rfl⟩

/-- The identity presentation: one copy of arity `1`; every valid position is
selected; the label at `p` is the letter `w_p` (recovered on the two-letter
alphabet as "`D` iff the letter there is `D`"); the tie-order is the position
order. -/
def idPoly : Polyreg.Presentation Step Step where
  K := 1
  arity := fun _ => 1
  domain := fun _ => True
  domainDef := ⟨Formula.tru, fun _ => Iff.rfl⟩
  sel := fun _ _ _ => True
  selDef := fun _ => ⟨Formula.tru, fun _ _ => Iff.rfl⟩
  label := fun _ w ī => if w[ī ⟨0, Nat.one_pos⟩]? = some D then D else U
  labelDef := fun _ γ => idLabelDef γ
  ord := fun _ _ _ ii jj => ii ⟨0, Nat.one_pos⟩ < jj ⟨0, Nat.one_pos⟩
  ordDef := fun _ _ => idOrdDef

/-- The unique copy index of `idPoly`. -/
def idC : Fin idPoly.K := ⟨0, by decide⟩

/-- The arity-1 atom of `idPoly` at position `p`. -/
def idAtom (p : ℕ) : idPoly.Atom := ⟨idC, fun _ => p⟩

/-- The position of an `idPoly` atom. -/
def idPos (a : idPoly.Atom) : ℕ := a.2 ⟨0, Nat.one_pos⟩

@[simp] theorem idPos_idAtom (p : ℕ) : idPos (idAtom p) = p := rfl

/-- Coordinates of an `idPoly` copy form `Fin 1`: there is only `⟨0, _⟩`. -/
theorem fin_arity_eq {c : Fin idPoly.K} (t : Fin (idPoly.arity c)) :
    t = ⟨0, Nat.one_pos⟩ := by
  apply Fin.ext
  show t.val = 0
  have h : t.val < 1 := t.isLt
  omega

/-- `idPoly` has a unique copy. -/
theorem copy_eq (c : Fin idPoly.K) : c = idC := by
  apply Fin.ext
  have h : c.val < 1 := c.isLt
  have h0 : idC.val = 0 := rfl
  omega

/-- Every `idPoly` atom is `idAtom` of its position. -/
theorem eq_idAtom (a : idPoly.Atom) : a = idAtom (idPos a) := by
  obtain ⟨c, ī⟩ := a
  obtain rfl : c = idC := copy_eq c
  exact congrArg (Sigma.mk idC) (funext fun t => by rw [fin_arity_eq t]; rfl)

theorem idAtom_injective : Function.Injective idAtom := fun p q h => by
  have h' := congrArg idPos h
  simpa using h'

/-- Selectedness for `idPoly` is exactly "the position is in range". -/
theorem selectedAtom_idAtom (w : List Step) (p : ℕ) :
    idPoly.selectedAtom w (idAtom p) ↔ p < w.length := by
  constructor
  · rintro ⟨hval, -⟩
    exact hval ⟨0, Nat.one_pos⟩
  · intro hp
    exact ⟨fun _ => hp, trivial⟩

/-- The label of the atom at an in-range position is the letter there. -/
theorem labelOf_idAtom (w : List Step) (p : ℕ) (hp : p < w.length) :
    idPoly.labelOf w (idAtom p) = w[p] := by
  show (if w[p]? = some D then D else U) = w[p]
  rw [List.getElem?_eq_getElem hp]
  cases hw : w[p] with
  | U => rw [if_neg (by simp)]
  | D => rw [if_pos rfl]

/-- The order of `idPoly` on canonical atoms is the position order. -/
theorem atomOrd_idAtom (w : List Step) (p q : ℕ) :
    idPoly.atomOrd w (idAtom p) (idAtom q) ↔ p < q := by
  constructor
  · intro h; exact h
  · intro h; exact h

theorem atomOrd_iff (w : List Step) (a b : idPoly.Atom) :
    idPoly.atomOrd w a b ↔ idPos a < idPos b := by
  conv_lhs => rw [eq_idAtom a, eq_idAtom b]
  exact atomOrd_idAtom w _ _

/-- `idPoly` is valid: the position order is a strict total order on atoms
(atoms at equal positions are equal, the copy and coordinate being unique). -/
theorem idPoly_valid : idPoly.Valid where
  irrefl := fun w a _ hbad => by
    rw [atomOrd_iff] at hbad
    exact lt_irrefl _ hbad
  trans := fun w a b c _ _ _ hab hbc => by
    rw [atomOrd_iff] at hab hbc ⊢
    exact lt_trans hab hbc
  trichot := fun w a b _ _ => by
    rcases lt_trichotomy (idPos a) (idPos b) with h | h | h
    · exact Or.inl ((atomOrd_iff w a b).mpr h)
    · refine Or.inr (Or.inl ?_)
      rw [eq_idAtom a, eq_idAtom b, h]
    · exact Or.inr (Or.inr ((atomOrd_iff w b a).mpr h))

/-- The selected atoms of `idPoly` on `w`, in output order. -/
def idAtoms (w : List Step) : List idPoly.Atom :=
  (List.range w.length).map idAtom

/-- `idPoly` outputs `w` on `w`. -/
theorem idPoly_isOutput (w : List Step) : idPoly.IsOutput w w := by
  refine ⟨idAtoms w, ?_, ?_, ?_, ?_⟩
  · exact List.nodup_range.map idAtom_injective
  · intro a
    unfold idAtoms
    rw [List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (selectedAtom_idAtom w p).mpr (List.mem_range.mp hp)
    · intro hsel
      refine ⟨idPos a, List.mem_range.mpr ?_, (eq_idAtom a).symm⟩
      rw [eq_idAtom a] at hsel
      exact (selectedAtom_idAtom w (idPos a)).mp hsel
  · unfold idAtoms
    exact List.Pairwise.map idAtom
      (fun p q hpq => (atomOrd_idAtom w p q).mpr hpq) List.pairwise_lt_range
  · unfold idAtoms
    rw [List.map_map]
    refine List.ext_getElem (by simp) fun i hi hi' => ?_
    have hlen : i < w.length := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    exact (labelOf_idAtom w i hlen).symm

/-- **The identity transduction `w ↦ w` is WRP** (arity-1, rank-free). -/
theorem idStep_isWRP : WRP.IsWRP (fun w : List Step => some w) := by
  refine WRP.isWRP_of_isPolyregular ⟨idPoly, idPoly_valid, fun w out => ?_⟩
  constructor
  · intro h
    obtain rfl : w = out := Option.some.inj h
    exact ⟨trivial, idPoly_isOutput w⟩
  · rintro ⟨-, hout⟩
    exact congrArg some (idPoly.isOutput_unique idPoly_valid (idPoly_isOutput w) hout)

/-! ## The three-block witness `D` (paper-full-new.tex) -/

/-- Relabel the diagnostic alphabet into `Γ_D`. -/
def relGB : GB → GBD
  | GB.g => GBD.g
  | GB.b => GBD.b
  | GB.u => GBD.u
  | GB.d => GBD.d

/-- Relabel the input alphabet into `Γ_D` (block 2 emits the input verbatim). -/
def relStep : Step → GBD
  | U => GBD.u
  | D => GBD.d

/-- **The revision's witness `D`** (Appendix A.4): diagnostic block, separator
`#`, verbatim input copy. -/
def compD (w : List Step) : List GBD :=
  (wncD w).map relGB ++ [GBD.sep] ++ w.map relStep

/-- `D` is WRP: relabel the two proved WRP blocks into `Γ_D` and concatenate
with the separator `#` — the block-tag construction of `isWRP_concat` is
exactly the paper's leading rank coordinate (paper-full-new.tex). -/
theorem compD_isWRP : WRP.IsWRP (fun w => some (compD w)) := by
  have h1 : WRP.IsWRP (fun w : List Step => some ((wncD w).map relGB)) := by
    simpa using WRPClosures.isWRP_relabel relGB wncD_isWRP
  have h2 : WRP.IsWRP (fun w : List Step => some (w.map relStep)) := by
    simpa using WRPClosures.isWRP_relabel relStep idStep_isWRP
  have h3 := WRPClosures.isWRP_concat (sep := GBD.sep) h1 h2
  convert h3 using 1
  funext w
  rfl

/-! ## The regular language `K = G·Γ_D^*` (paper-full-new.tex) -/

/-- Three states: initial, "first letter was `G`" (accepting sink), "first
letter was not `G`" (rejecting sink). -/
inductive CKState | start | sawG | sawOther
  deriving DecidableEq

instance : Fintype CKState :=
  ⟨⟨{.start, .sawG, .sawOther}, by decide⟩, fun x => by cases x <;> decide⟩

open CKState

/-- The `DFA'` recognising "the first letter is `G`". -/
def compKDFA : DFA' GBD where
  Q := CKState
  delta := fun q y => match q, y with
    | start, GBD.g => sawG
    | start, _ => sawOther
    | sawG, _ => sawG
    | sawOther, _ => sawOther
  q0 := start
  F := {sawG}

theorem compKDFA_run (y : List GBD) :
    y.foldl compKDFA.delta compKDFA.q0 = sawG ↔ y.head? = some GBD.g := by
  cases y with
  | nil => simp [compKDFA]
  | cons x xs =>
    have hstep : compKDFA.delta compKDFA.q0 x = (if x = GBD.g then sawG else sawOther) := by
      cases x <;> rfl
    rw [List.foldl_cons, hstep, List.head?_cons, Option.some.injEq]
    by_cases hx : x = GBD.g
    · subst hx
      have habs : ∀ l : List GBD, l.foldl compKDFA.delta sawG = sawG := by
        intro l; induction l with
        | nil => rfl
        | cons z zs ih =>
          show List.foldl compKDFA.delta (compKDFA.delta sawG z) zs = sawG
          rw [show compKDFA.delta sawG z = sawG from by cases z <;> rfl]
          exact ih
      rw [if_pos rfl, habs]
      exact iff_of_true rfl rfl
    · have habs : ∀ l : List GBD, l.foldl compKDFA.delta sawOther = sawOther := by
        intro l; induction l with
        | nil => rfl
        | cons z zs ih =>
          show List.foldl compKDFA.delta (compKDFA.delta sawOther z) zs = sawOther
          rw [show compKDFA.delta sawOther z = sawOther from by cases z <;> rfl]
          exact ih
      rw [if_neg hx, habs]
      constructor
      · intro h; exact CKState.noConfusion h
      · intro h; exact absurd h hx

/-- The regular output language: strings whose first letter is `G`. -/
def compK : Set (List GBD) := {y | y.head? = some GBD.g}

theorem compK_isRegular : IsRegularLang compK := by
  refine ⟨compKDFA, ?_⟩
  ext y
  show compKDFA.accepts y ↔ y ∈ compK
  unfold DFA'.accepts compK
  rw [show (compKDFA.F : Set CKState) = {sawG} from rfl]
  simp only [Set.mem_ofPred_eq]
  exact compKDFA_run y

/-! ## Claim 1: `D⁻¹(K) = Lnn` is not regular -/

/-- The diagnostic block is never empty (the sentinel is always selected). -/
theorem wncD_ne_nil (w : List Step) : wncD w ≠ [] := by
  obtain ⟨a₀, hhead, -, -⟩ := head_wncAtoms_min w
  intro h
  rw [wncD, List.map_eq_nil_iff] at h
  rw [h] at hhead
  simp at hhead

/-- **First-letter characterisation for `D`** (paper-full-new.tex lines
4651–4664): the first letter of `D(w)` is `G` iff `w ∈ Lnn`. -/
theorem head_compD_eq_g_iff (w : List Step) :
    (compD w).head? = some GBD.g ↔ w ∈ Lnn := by
  have hne : (wncD w).map relGB ≠ [] := by
    simpa using wncD_ne_nil w
  rw [compD, List.append_assoc, List.head?_append_of_ne_nil _ hne, List.head?_map]
  rw [← head_wncD_eq_g_iff w]
  cases hh : (wncD w).head? with
  | none => simp
  | some x => cases x <;> simp [relGB]

/-- **The preimage of `K` under `D` is exactly `Lnn`.** -/
theorem preimage_compK_eq_Lnn :
    {w : List Step | ∃ out, (fun w => some (compD w)) w = some out ∧ out ∈ compK} = Lnn := by
  ext w
  simp only [Set.mem_ofPred_eq, Option.some.injEq]
  constructor
  · rintro ⟨out, rfl, hmem⟩
    exact (head_compD_eq_g_iff w).mp hmem
  · intro hw
    exact ⟨compD w, rfl, (head_compD_eq_g_iff w).mpr hw⟩

/-- **`thm:wrp-not-closed`, claim 1, with the revision's three-block witness**
(paper-full-new.tex, proof lines 4609–4674): there are a WRP map `D`
and a regular language `K` with `D⁻¹(K)` not regular — and this `D` is the one
that also witnesses the composition failure.  Axiom-clean (no Büchi, no
project axioms). -/
theorem wrp_not_closed_preimage_comp :
    ∃ (D : List Step → Option (List GBD)) (K : Set (List GBD)),
      WRP.IsWRP D ∧ IsRegularLang K ∧
      ¬ IsRegularLang {w | ∃ out, D w = some out ∧ out ∈ K} := by
  refine ⟨fun w => some (compD w), compK, compD_isWRP, compK_isRegular, ?_⟩
  rw [preimage_compK_eq_Lnn]
  exact not_regular_Lnn

end WRPComp
