/-
# Elementary closure properties of `WRP` (`thm:wrp-closures`)

Formalisation of Theorem `thm:wrp-closures` (Elementary closure properties,
paper.tex) of "A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.

The class of `WRP` transductions is closed under the everyday transducer
constructions:

* **(i)** restriction to a regular (MSO-definable) input language
  (`isWRP_restrict`);
* **(ii)** finite disjoint unions of output alphabets — the bookkeeping
  operation that keeps atoms produced by different sub-constructions distinguishable
  (`isWRP_disjointUnion`);
* **(iii)** concatenation of two `WRP` outputs with a fixed separator
  (`isWRP_concat`);
* **(iv)** output relabelling (`isWRP_relabel`);
* **(v)** output reversal (`isWRP_reverse`).

Each closure is stated and proved at the `WRP.IsWRP` level: from the given
presentation(s) we build the derived `WRP.Presentation`, prove its `Valid`-ity,
and discharge the `IsOutput` biconditional.

Two robustness facts of the paper's proof are isolated here:

* **(R1)** regular rank terms (`IsRegularRankTerm`) are closed under constants,
  negation, and coordinate-embedding into a larger `ℤ^d` (the rank dimension `d`
  is a free parameter of `def:wrp`); and
* **(R2)** a copy set partitioned into finitely many classes, each carrying its
  own MSO tie-order, with a linear order on the classes, has a single
  MSO-definable strict total order ("earlier class first, then within-class
  order").  Here `(R2)` is realised concretely per construction by the
  `Sum`/block structure of the merged copy set.

Trust base: `[propext, Classical.choice, Quot.sound]` — every theorem in this
file is axiom-clean (no Büchi axiom, no `sorry`).
-/
import RequestProject.WRP
import RequestProject.SliceFasGates
import RequestProject.SliceProfileDischarge

open MSO

namespace WRPClosures

/-! ## Shared MSO helpers

Small re-derivations of the `MSODefinableRel` closure lemmas (also present, but
`private`, in `WRPBoundedRank.lean`): transfer along a pointwise iff, conjunction,
and the FO-variable cylindrifications of `ordDef` formulas. -/

/-- `MSODefinableRel` transfers along a pointwise iff. -/
theorem mso_congr {Alpha : Type*} {k : ℕ} {R S : List Alpha → (Fin k → ℕ) → Prop}
    (h : ∀ w ī, R w ī ↔ S w ī) (hR : MSODefinableRel k R) : MSODefinableRel k S := by
  obtain ⟨φ, hφ⟩ := hR
  exact ⟨φ, fun w ī => (h w ī).symm.trans (hφ w ī)⟩

/-- Fold a list of formulas into a single disjunction. -/
def listOr {Alpha : Type*} {nf : ℕ} (g : List (Formula Alpha nf 0)) : Formula Alpha nf 0 :=
  g.foldr Formula.or (Formula.neg Formula.tru)

theorem sat_listOr {Alpha : Type*} {nf : ℕ} (w : List Alpha) (ρ : Fin nf → ℕ)
    (g : List (Formula Alpha nf 0)) :
    (listOr g).Sat w ρ Fin.elim0 ↔ ∃ φ ∈ g, φ.Sat w ρ Fin.elim0 := by
  unfold listOr
  induction g with
  | nil => simp [Formula.Sat]
  | cons a l ih =>
      simp only [List.foldr_cons, Formula.sat_or, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨φ, hφ, hsat⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨φ, Or.inr hφ, hsat⟩
      · rintro ⟨φ, (rfl | hφ), hsat⟩
        · exact Or.inl hsat
        · exact Or.inr ⟨φ, hφ, hsat⟩

/-- Disjunction over a `Finset` of an `MSODefinableRel`-family at fixed arity. -/
theorem mso_finsetOr {Alpha ι : Type*} {k : ℕ} (s : Finset ι)
    {R : ι → List Alpha → (Fin k → ℕ) → Prop}
    (hR : ∀ x ∈ s, MSODefinableRel k (R x)) :
    MSODefinableRel k (fun w ī => ∃ x ∈ s, R x w ī) := by
  classical
  have hR' : ∀ x : s, MSODefinableRel k (R x.1) := fun x => hR x.1 x.2
  choose φ hφ using hR'
  refine ⟨listOr (s.attach.toList.map (fun x => φ x)), fun w ρ => ?_⟩
  rw [sat_listOr]
  constructor
  · rintro ⟨x, hx, hRx⟩
    exact ⟨φ ⟨x, hx⟩, List.mem_map.mpr ⟨⟨x, hx⟩, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩,
      (hφ ⟨x, hx⟩ w ρ).mp hRx⟩
  · rintro ⟨ψ, hψ, hsat⟩
    rw [List.mem_map] at hψ
    obtain ⟨x, _, rfl⟩ := hψ
    exact ⟨x.1, x.2, (hφ x w ρ).mpr hsat⟩

/-! ## Output existence

Every valid WRP presentation produces a declarative output on every word: the
finitely many selected atoms can be `≺`-sorted (a generic selection sort).  This
is the WRP analogue of `CopiedDischarge.exists_isOutput'`, stated for arbitrary
alphabets. -/

open scoped Classical in
/-- The selected atoms of `w`, over all copies and all valid tuples (a finite set). -/
noncomputable def selAtoms {Alpha Gamma : Type*} (P : WRP.Presentation Alpha Gamma)
    (w : List Alpha) : Finset P.toPoly.Atom :=
  ((Finset.univ : Finset (Fin P.toPoly.K)).sigma (fun c =>
    Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) => Finset.range w.length))).filter
    (fun a => P.toPoly.selectedAtom w a)

open scoped Classical in
theorem mem_selAtoms {Alpha Gamma : Type*} (P : WRP.Presentation Alpha Gamma)
    (w : List Alpha) (a : P.toPoly.Atom) :
    a ∈ selAtoms P w ↔ P.toPoly.selectedAtom w a := by
  rw [selAtoms, Finset.mem_filter]
  refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨?_, h⟩⟩
  rw [Finset.mem_sigma]
  exact ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (h.1 i)⟩

/-- **Output existence**: a valid WRP presentation has a declarative output on
every word (sort the finitely many selected atoms by `≺`). -/
theorem exists_isOutput {Alpha Gamma : Type*} (P : WRP.Presentation Alpha Gamma)
    (hV : P.Valid) (w : List Alpha) : ∃ out, P.IsOutput w out := by
  set L := (selAtoms P w).toList with hLdef
  have hLnd : L.Nodup := Finset.nodup_toList _
  have hLmem : ∀ a, a ∈ L ↔ P.toPoly.selectedAtom w a := fun a => by
    rw [hLdef, Finset.mem_toList, mem_selAtoms]
  obtain ⟨sorted, hsnd, hsmem, hspair⟩ :=
    SliceProfileDischarge.exists_sorted_of_nodup (P.wrpOrd w) L.length L (le_refl _) hLnd
      (fun a ha b hb => hV.trichot _ a b ((hLmem a).mp ha) ((hLmem b).mp hb))
      (fun a ha b hb c hc => hV.trans _ a b c ((hLmem a).mp ha) ((hLmem b).mp hb)
        ((hLmem c).mp hc))
  exact ⟨sorted.map (P.toPoly.labelOf w), sorted, hsnd,
    fun a => (hsmem a).trans (hLmem a), hspair, rfl⟩

/-- On the domain, a valid WRP transduction is defined (`some`). -/
theorem isWRP_some_of_domain {Alpha Gamma : Type*} {T : List Alpha → Option (List Gamma)}
    {P : WRP.Presentation Alpha Gamma} (hV : P.Valid)
    (hT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    {w : List Alpha} (hdom : P.toPoly.domain w) : ∃ out, T w = some out := by
  obtain ⟨out, hout⟩ := exists_isOutput P hV w
  exact ⟨out, (hT w out).mpr ⟨hdom, hout⟩⟩

/-! ## PRIORITY 1 — Output relabelling (`thm:wrp-closures` clause (iv))

"Relabelling composes the label assignment with a fixed letter map, rewriting
only the label formulas; ranks, tie-order, and arities are untouched."
(`thm:wrp-closures`, paper.tex).

We post-compose `P`'s label with `ℓ : Γ → Γ'`.  The selection, rank, and order
are unchanged, so the `≺`-sorted atom list is identical; the output is the old
output with every letter mapped by `ℓ`.  For `labelDef'` we use, per target letter
`g' : Γ'`, the finite disjunction over the preimage `{g : Γ | ℓ g = g'}` of the
original per-letter label formulas (this needs `Γ` finite). -/

/-- The polyregular part of the relabelled presentation: `P.toPoly` with its label
post-composed by `ℓ`.  Selection, ranks, order, domain and arities are untouched. -/
@[reducible] def relabelPoly {Alpha Γ Γ' : Type*} [Fintype Γ] [DecidableEq Γ']
    (P : Polyreg.Presentation Alpha Γ) (ℓ : Γ → Γ') : Polyreg.Presentation Alpha Γ' where
  K := P.K
  arity := P.arity
  domain := P.domain
  domainDef := P.domainDef
  sel := P.sel
  selDef := P.selDef
  label := fun c w ī => ℓ (P.label c w ī)
  labelDef := fun c g' => by
    classical
    -- `ℓ (label c w ī) = g'` ↔ `∃ g ∈ {g | ℓ g = g'}, label c w ī = g`
    refine mso_congr (R := fun w ī => ∃ g ∈ Finset.univ.filter (fun g : Γ => ℓ g = g'),
        P.label c w ī = g) (fun w ī => ?_)
      (mso_finsetOr _ (fun g _ => P.labelDef c g))
    constructor
    · rintro ⟨g, hg, hlab⟩; rw [hlab]; exact (Finset.mem_filter.mp hg).2
    · intro h
      exact ⟨P.label c w ī, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  ord := P.ord
  ordDef := P.ordDef

/-- The WRP presentation of the relabel: the same rank data over `relabelPoly`. -/
@[reducible] def relabelPres {Alpha Γ Γ' : Type*} [Fintype Γ] [DecidableEq Γ']
    (P : WRP.Presentation Alpha Γ) (ℓ : Γ → Γ') : WRP.Presentation Alpha Γ' where
  toPoly := relabelPoly P.toPoly ℓ
  d := P.d
  rank := P.rank
  rankReg := P.rankReg

/-- The atoms, selection, rank, and order of `relabelPres` agree definitionally
with those of `P`. -/
theorem relabelPres_wrpOrd {Alpha Γ Γ' : Type*} [Fintype Γ] [DecidableEq Γ']
    (P : WRP.Presentation Alpha Γ) (ℓ : Γ → Γ') (w : List Alpha)
    (a b : (relabelPres P ℓ).toPoly.Atom) :
    (relabelPres P ℓ).wrpOrd w a b ↔ P.wrpOrd w a b := Iff.rfl

theorem relabelPres_selectedAtom {Alpha Γ Γ' : Type*} [Fintype Γ] [DecidableEq Γ']
    (P : WRP.Presentation Alpha Γ) (ℓ : Γ → Γ') (w : List Alpha)
    (a : (relabelPres P ℓ).toPoly.Atom) :
    (relabelPres P ℓ).toPoly.selectedAtom w a ↔ P.toPoly.selectedAtom w a := Iff.rfl

/-- `relabelPres` is valid whenever `P` is (same order, same selected atoms). -/
theorem relabelPres_valid {Alpha Γ Γ' : Type*} [Fintype Γ] [DecidableEq Γ']
    (P : WRP.Presentation Alpha Γ) (hV : P.Valid) (ℓ : Γ → Γ') :
    (relabelPres P ℓ).Valid where
  irrefl := fun w a ha => hV.irrefl w a ha
  trans := fun w a b c ha hb hc => hV.trans w a b c ha hb hc
  trichot := fun w a b ha hb => hV.trichot w a b ha hb

/-- A `relabelPres`-output is exactly `out.map ℓ` for the (unique) `P`-output `out`
on the same witness atom list. -/
theorem relabelPres_isOutput_of {Alpha Γ Γ' : Type*} [Fintype Γ] [DecidableEq Γ']
    (P : WRP.Presentation Alpha Γ) (ℓ : Γ → Γ') (w : List Alpha) (out' : List Γ')
    (h : (relabelPres P ℓ).IsOutput w out') :
    ∃ out, P.IsOutput w out ∧ out' = out.map ℓ := by
  obtain ⟨atoms, hnd, hmem, hpw, hout'⟩ := h
  refine ⟨atoms.map (P.toPoly.labelOf w),
    ⟨atoms, hnd, fun a => (hmem a).trans (relabelPres_selectedAtom P ℓ w a),
      hpw.imp fun hh => (relabelPres_wrpOrd P ℓ w _ _).mp hh, rfl⟩, ?_⟩
  rw [hout', List.map_map]
  rfl

/-- Conversely, mapping a `P`-output by `ℓ` gives a `relabelPres`-output. -/
theorem relabelPres_isOutput_map {Alpha Γ Γ' : Type*} [Fintype Γ] [DecidableEq Γ']
    (P : WRP.Presentation Alpha Γ) (ℓ : Γ → Γ') (w : List Alpha) (out : List Γ)
    (h : P.IsOutput w out) : (relabelPres P ℓ).IsOutput w (out.map ℓ) := by
  obtain ⟨atoms, hnd, hmem, hpw, rfl⟩ := h
  refine ⟨atoms, hnd, fun a => (hmem a).trans (relabelPres_selectedAtom P ℓ w a).symm,
    hpw.imp fun hh => (relabelPres_wrpOrd P ℓ w _ _).mpr hh, ?_⟩
  rw [List.map_map]
  rfl

/-- **`thm:wrp-closures` (iv) — output relabelling** (`thm:wrp-closures`, paper.tex).
If `T` is `WRP` then so is its post-composition with a fixed letter map
`ℓ : Γ → Γ'`.  (`Γ` finite, `Γ'` with decidable equality, so the per-letter label
formula is a finite disjunction over the preimage of `ℓ`.) -/
theorem isWRP_relabel {Alpha Γ Γ' : Type*} [Fintype Γ] [DecidableEq Γ'] (ℓ : Γ → Γ')
    {T : List Alpha → Option (List Γ)} (h : WRP.IsWRP T) :
    WRP.IsWRP (fun w => (T w).map (List.map ℓ)) := by
  obtain ⟨P, hV, hT⟩ := h
  refine ⟨relabelPres P ℓ, relabelPres_valid P hV ℓ, fun w out' => ?_⟩
  show (T w).map (List.map ℓ) = some out' ↔ _
  constructor
  · intro hout'
    rcases hTw : T w with _ | out
    · rw [hTw] at hout'; exact absurd hout' (by simp)
    · refine ⟨((hT w out).mp hTw).1, ?_⟩
      have hval : out' = out.map ℓ := by
        rw [hTw] at hout'
        exact (Option.some.inj hout').symm
      rw [hval]
      exact relabelPres_isOutput_map P ℓ w out ((hT w out).mp hTw).2
  · rintro ⟨hdom, hOut'⟩
    obtain ⟨out, hPout, rfl⟩ := relabelPres_isOutput_of P ℓ w out' hOut'
    rw [(hT w out).mpr ⟨hdom, hPout⟩]
    rfl

/-! ## PRIORITY 2 — Restriction to an MSO-definable input language
(`thm:wrp-closures` clause (i))

"A regular language is MSO-definable; conjoin each selection formula `φ_c` with
the MSO sentence asserting that the input lies in the regular set."
(`thm:wrp-closures`, paper.tex).  Equivalently — and more economically, since the
domain is itself an MSO sentence — we conjoin the *domain* sentence with the
language sentence: the result is `WRP` and its output is `T(w)` on the language,
undefined off it.  We state the regular language directly as an arity-0
`MSODefinableRel` (the axiom-clean MSO-given form). -/

/-- The polyregular part restricted to the MSO-definable language `L`: the domain
is intersected with `L`, everything else is untouched. -/
@[reducible] def restrictPoly {Alpha Γ : Type*}
    (P : Polyreg.Presentation Alpha Γ) (L : List Alpha → Prop)
    (hL : MSODefinableRel 0 (fun w _ => L w)) : Polyreg.Presentation Alpha Γ where
  K := P.K
  arity := P.arity
  domain := fun w => P.domain w ∧ L w
  domainDef := by
    obtain ⟨φd, hφd⟩ := P.domainDef
    obtain ⟨φL, hφL⟩ := hL
    refine ⟨Formula.and φd φL, fun w => ?_⟩
    rw [Formula.sat_and, ← hφd w]
    exact and_congr_right fun _ => (hφL w Fin.elim0)
  sel := P.sel
  selDef := P.selDef
  label := P.label
  labelDef := P.labelDef
  ord := P.ord
  ordDef := P.ordDef

/-- The WRP presentation restricted to `L`: same rank data over `restrictPoly`. -/
@[reducible] def restrictPres {Alpha Γ : Type*}
    (P : WRP.Presentation Alpha Γ) (L : List Alpha → Prop)
    (hL : MSODefinableRel 0 (fun w _ => L w)) : WRP.Presentation Alpha Γ where
  toPoly := restrictPoly P.toPoly L hL
  d := P.d
  rank := P.rank
  rankReg := P.rankReg

theorem restrictPres_wrpOrd {Alpha Γ : Type*}
    (P : WRP.Presentation Alpha Γ) (L : List Alpha → Prop)
    (hL : MSODefinableRel 0 (fun w _ => L w)) (w : List Alpha)
    (a b : (restrictPres P L hL).toPoly.Atom) :
    (restrictPres P L hL).wrpOrd w a b ↔ P.wrpOrd w a b := Iff.rfl

theorem restrictPres_selectedAtom {Alpha Γ : Type*}
    (P : WRP.Presentation Alpha Γ) (L : List Alpha → Prop)
    (hL : MSODefinableRel 0 (fun w _ => L w)) (w : List Alpha)
    (a : (restrictPres P L hL).toPoly.Atom) :
    (restrictPres P L hL).toPoly.selectedAtom w a ↔ P.toPoly.selectedAtom w a := Iff.rfl

/-- The restricted presentation is valid whenever `P` is. -/
theorem restrictPres_valid {Alpha Γ : Type*}
    (P : WRP.Presentation Alpha Γ) (hV : P.Valid) (L : List Alpha → Prop)
    (hL : MSODefinableRel 0 (fun w _ => L w)) : (restrictPres P L hL).Valid where
  irrefl := fun w a ha => hV.irrefl w a ha
  trans := fun w a b c ha hb hc => hV.trans w a b c ha hb hc
  trichot := fun w a b ha hb => hV.trichot w a b ha hb

/-- The declarative outputs coincide (same atoms, labels, order). -/
theorem restrictPres_isOutput {Alpha Γ : Type*}
    (P : WRP.Presentation Alpha Γ) (L : List Alpha → Prop)
    (hL : MSODefinableRel 0 (fun w _ => L w)) (w : List Alpha) (out : List Γ) :
    (restrictPres P L hL).IsOutput w out ↔ P.IsOutput w out := by
  constructor <;> rintro ⟨atoms, hnd, hmem, hpw, hout⟩
  · exact ⟨atoms, hnd, fun a => (hmem a).trans (restrictPres_selectedAtom P L hL w a),
      hpw.imp fun hh => (restrictPres_wrpOrd P L hL w _ _).mp hh, hout⟩
  · exact ⟨atoms, hnd, fun a => (hmem a).trans (restrictPres_selectedAtom P L hL w a).symm,
      hpw.imp fun hh => (restrictPres_wrpOrd P L hL w _ _).mpr hh, hout⟩

/-- **`thm:wrp-closures` (i) — restriction to a regular input language**
(`thm:wrp-closures`, paper.tex).  If `T` is `WRP` and `L` is an MSO-definable
(equivalently regular) input language, then `w ↦ if L w then T w else none` is
`WRP`.  The construction conjoins `L` into the domain sentence. -/
theorem isWRP_restrict {Alpha Γ : Type*}
    {T : List Alpha → Option (List Γ)} (h : WRP.IsWRP T)
    (L : List Alpha → Prop) [DecidablePred L] (hL : MSODefinableRel 0 (fun w _ => L w)) :
    WRP.IsWRP (fun w => if L w then T w else none) := by
  obtain ⟨P, hV, hT⟩ := h
  refine ⟨restrictPres P L hL, restrictPres_valid P hV L hL, fun w out => ?_⟩
  show (if L w then T w else none) = some out ↔ _
  by_cases hLw : L w
  · rw [if_pos hLw]
    rw [hT w out]
    constructor
    · rintro ⟨hdom, hOut⟩
      exact ⟨⟨hdom, hLw⟩, (restrictPres_isOutput P L hL w out).mpr hOut⟩
    · rintro ⟨⟨hdom, _⟩, hOut⟩
      exact ⟨hdom, (restrictPres_isOutput P L hL w out).mp hOut⟩
  · rw [if_neg hLw]
    constructor
    · intro hbad; exact absurd hbad (by simp)
    · rintro ⟨⟨_, hLw'⟩, _⟩; exact absurd hLw' hLw

/-! ## PRIORITY 3 — Output reversal (`thm:wrp-closures` clause (v))

"Replace every rank `κ` by `−κ`, a regular rank term by (R1), and `χ` by its
converse, which is MSO-definable (swap the two atom arguments in the defining
formula).  Negating every coordinate reverses the lexicographic order on `ℤ^d`,
and the converse tie-order reverses the within-rank comparison, so the emission
order is exactly reversed and the output is the reverse of `T(w)`."
(`thm:wrp-logspace`, paper.tex). -/

/-- The block-swap renaming `Fin (m + n) → Fin (n + m)` sending the first `m`
variables to the *second* block and the last `n` to the *first* block. -/
def swapFin (m n : ℕ) : Fin (m + n) → Fin (n + m) :=
  fun t => Fin.addCases (fun i => Fin.natAdd n i) (fun j => Fin.castAdd m j) t

theorem swapFin_castAdd (m n : ℕ) (i : Fin m) :
    swapFin m n (Fin.castAdd n i) = Fin.natAdd n i := by
  simp [swapFin]

theorem swapFin_natAdd (m n : ℕ) (j : Fin n) :
    swapFin m n (Fin.natAdd m j) = Fin.castAdd m j := by
  simp [swapFin]

/-- **(R2)/converse — the reversed (converse) order is MSO-definable.**
`P.ord c' c` (with its two argument blocks swapped) is definable over the
`arity c + arity c'` free variables of `ord' c c'`. -/
theorem ordRev_mso {Alpha Γ : Type*} (P : Polyreg.Presentation Alpha Γ)
    (c c' : Fin P.K) :
    MSODefinableRel (P.arity c + P.arity c')
      (fun w ij => P.ord c' c w (fun t => ij (Fin.natAdd (P.arity c) t))
        (fun t => ij (Fin.castAdd (P.arity c') t))) := by
  obtain ⟨φ, hφ⟩ := P.ordDef c' c
  refine ⟨SliceFasGates.relabelFO (swapFin (P.arity c') (P.arity c)) φ, fun w ij => ?_⟩
  rw [SliceFasGates.sat_relabelFO, ← hφ w (ij ∘ swapFin (P.arity c') (P.arity c))]
  -- the two atom blocks fed to `φ` match up under the swap:
  -- φ's first block (the `c'`-atom) reads `ij`'s second block, and vice versa
  show P.ord c' c w (fun t => ij (Fin.natAdd (P.arity c) t)) (fun t => ij (Fin.castAdd (P.arity c') t))
    ↔ P.ord c' c w
        (fun t => (ij ∘ swapFin (P.arity c') (P.arity c)) (Fin.castAdd (P.arity c) t))
        (fun t => (ij ∘ swapFin (P.arity c') (P.arity c)) (Fin.natAdd (P.arity c') t))
  have h1 : (fun t => (ij ∘ swapFin (P.arity c') (P.arity c)) (Fin.castAdd (P.arity c) t))
      = fun t => ij (Fin.natAdd (P.arity c) t) := by
    funext t; simp only [Function.comp_apply, swapFin_castAdd]
  have h2 : (fun t => (ij ∘ swapFin (P.arity c') (P.arity c)) (Fin.natAdd (P.arity c') t))
      = fun t => ij (Fin.castAdd (P.arity c') t) := by
    funext t; simp only [Function.comp_apply, swapFin_natAdd]
  rw [h1, h2]

/-- The polyregular part of the reversed presentation: `P.toPoly` with its order
relation replaced by its converse. -/
@[reducible] def reversePoly {Alpha Γ : Type*} (P : Polyreg.Presentation Alpha Γ) :
    Polyreg.Presentation Alpha Γ where
  K := P.K
  arity := P.arity
  domain := P.domain
  domainDef := P.domainDef
  sel := P.sel
  selDef := P.selDef
  label := P.label
  labelDef := P.labelDef
  ord := fun c c' w ī ī' => P.ord c' c w ī' ī
  ordDef := fun c c' => ordRev_mso P c c'

/-- The WRP presentation of the reversal: rank negated (regular by (R1)), order
converted. -/
@[reducible] def reversePres {Alpha Γ : Type*} (P : WRP.Presentation Alpha Γ) :
    WRP.Presentation Alpha Γ where
  toPoly := reversePoly P.toPoly
  d := P.d
  rank := fun c w ī coord => - P.rank c w ī coord
  rankReg := fun c => isRegularRankTerm_neg (P.rankReg c)

/-- The negated lexicographic order is the converse lexicographic order. -/
theorem lexLt_neg {d : ℕ} (x y : Fin d → ℤ) :
    WRP.lexLt (fun coord => - x coord) (fun coord => - y coord) ↔ WRP.lexLt y x := by
  constructor
  · rintro ⟨i, hlt, hi⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · have := hlt j hj; simp only at this; exact (neg_injective this).symm
    · simp only at hi; exact lt_of_neg_lt_neg hi
  · rintro ⟨i, hlt, hi⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · simp only; rw [hlt j hj]
    · simp only; exact neg_lt_neg hi

/-- The negated-rank function of an atom is the negation of its `P`-rank. -/
theorem reversePres_rankOf {Alpha Γ : Type*} (P : WRP.Presentation Alpha Γ)
    (w : List Alpha) (a : (reversePres P).toPoly.Atom) :
    (reversePres P).rankOf w a = fun coord => - P.rankOf w a coord := rfl

/-- **The reversed order is the converse of the original order.**
`reversePres.wrpOrd w a b ↔ P.wrpOrd w b a`. -/
theorem reversePres_wrpOrd {Alpha Γ : Type*} (P : WRP.Presentation Alpha Γ)
    (w : List Alpha) (a b : (reversePres P).toPoly.Atom) :
    (reversePres P).wrpOrd w a b ↔ P.wrpOrd w b a := by
  show (WRP.lexLt ((reversePres P).rankOf w a) ((reversePres P).rankOf w b) ∨
      ((reversePres P).rankOf w a = (reversePres P).rankOf w b ∧
        (reversePres P).toPoly.atomOrd w a b))
    ↔ (WRP.lexLt (P.rankOf w b) (P.rankOf w a) ∨
      (P.rankOf w b = P.rankOf w a ∧ P.toPoly.atomOrd w b a))
  have hlex : WRP.lexLt ((reversePres P).rankOf w a) ((reversePres P).rankOf w b)
      ↔ WRP.lexLt (P.rankOf w b) (P.rankOf w a) := by
    rw [reversePres_rankOf, reversePres_rankOf]; exact lexLt_neg _ _
  have heq : ((reversePres P).rankOf w a = (reversePres P).rankOf w b)
      ↔ (P.rankOf w b = P.rankOf w a) := by
    rw [reversePres_rankOf, reversePres_rankOf]
    constructor
    · intro h; funext coord; have := congrFun h coord
      exact (neg_injective this).symm
    · intro h; funext coord; rw [h]
  -- `atomOrd` of the reversed poly is the converse
  have hord : (reversePres P).toPoly.atomOrd w a b ↔ P.toPoly.atomOrd w b a := Iff.rfl
  exact or_congr hlex (and_congr heq hord)

theorem reversePres_selectedAtom {Alpha Γ : Type*} (P : WRP.Presentation Alpha Γ)
    (w : List Alpha) (a : (reversePres P).toPoly.Atom) :
    (reversePres P).toPoly.selectedAtom w a ↔ P.toPoly.selectedAtom w a := Iff.rfl

/-- The reversed presentation is valid: the converse of a strict total order is a
strict total order. -/
theorem reversePres_valid {Alpha Γ : Type*} (P : WRP.Presentation Alpha Γ)
    (hV : P.Valid) : (reversePres P).Valid where
  irrefl := fun w a ha => by
    rw [reversePres_wrpOrd]; exact hV.irrefl w a ha
  trans := fun w a b c ha hb hc hab hbc => by
    rw [reversePres_wrpOrd] at *
    exact hV.trans w c b a hc hb ha hbc hab
  trichot := fun w a b ha hb => by
    rw [reversePres_wrpOrd, reversePres_wrpOrd]
    rcases hV.trichot w b a hb ha with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h)

/-- The declarative output of the reversal is the reverse of the `P`-output:
witness atom list reversed. -/
theorem reversePres_isOutput_of {Alpha Γ : Type*} (P : WRP.Presentation Alpha Γ)
    (w : List Alpha) (out : List Γ) (h : (reversePres P).IsOutput w out) :
    ∃ out0, P.IsOutput w out0 ∧ out = out0.reverse := by
  obtain ⟨atoms, hnd, hmem, hpw, hout⟩ := h
  refine ⟨atoms.reverse.map (P.toPoly.labelOf w),
    ⟨atoms.reverse, List.nodup_reverse.mpr hnd, ?_, ?_, rfl⟩, ?_⟩
  · intro a; rw [List.mem_reverse]; exact (hmem a).trans (reversePres_selectedAtom P w a)
  · -- pairwise of `P.wrpOrd` on the reversed list, from converse pairwise on `atoms`
    rw [List.pairwise_reverse]
    refine hpw.imp fun {a b} hh => (reversePres_wrpOrd P w a b).mp hh
  · rw [hout, ← List.map_reverse, List.reverse_reverse]
    rfl

theorem reversePres_isOutput_reverse {Alpha Γ : Type*} (P : WRP.Presentation Alpha Γ)
    (w : List Alpha) (out0 : List Γ) (h : P.IsOutput w out0) :
    (reversePres P).IsOutput w out0.reverse := by
  obtain ⟨atoms, hnd, hmem, hpw, rfl⟩ := h
  refine ⟨atoms.reverse, List.nodup_reverse.mpr hnd, ?_, ?_, ?_⟩
  · intro a; rw [List.mem_reverse]; exact (hmem a).trans (reversePres_selectedAtom P w a).symm
  · rw [List.pairwise_reverse]
    refine hpw.imp fun {a b} hh => (reversePres_wrpOrd P w b a).mpr hh
  · rw [List.map_reverse]; rfl

/-- **`thm:wrp-closures` (v) — output reversal** (`thm:wrp-logspace`, paper.tex).
If `T` is `WRP` then so is its output-reversal `w ↦ (T w).map List.reverse`. -/
theorem isWRP_reverse {Alpha Γ : Type*}
    {T : List Alpha → Option (List Γ)} (h : WRP.IsWRP T) :
    WRP.IsWRP (fun w => (T w).map List.reverse) := by
  obtain ⟨P, hV, hT⟩ := h
  refine ⟨reversePres P, reversePres_valid P hV, fun w out => ?_⟩
  show (T w).map List.reverse = some out ↔ _
  constructor
  · intro hout
    rcases hTw : T w with _ | out0
    · rw [hTw] at hout; exact absurd hout (by simp)
    · refine ⟨((hT w out0).mp hTw).1, ?_⟩
      have hval : out = out0.reverse := by
        rw [hTw] at hout
        exact (Option.some.inj hout).symm
      rw [hval]
      exact reversePres_isOutput_reverse P w out0 ((hT w out0).mp hTw).2
  · rintro ⟨hdom, hOut⟩
    obtain ⟨out0, hPout, rfl⟩ := reversePres_isOutput_of P w out hOut
    rw [(hT w out0).mpr ⟨hdom, hPout⟩]
    rfl

/-! ## PRIORITY 4 — Disjoint union of output alphabets (`thm:wrp-closures` clause (ii))

"Take the disjoint union of the copy sets, each copy keeping its selection
formula, rank, and label, the last now valued in the tagged alphabet
`Γ₁ ⊎ Γ₂`; if the parts have different rank dimensions, embed both into a common
`ℤ^d` by (R1), and take `χ` from (R2)." (`thm:wrp-closures`, paper.tex).

We realise (R2) concretely through a dominant **block-index** rank coordinate (the
same device as (iii) below), so the combined output is `f(w)` (tagged left) followed
by `g(w)` (tagged right):
`w ↦ (f w).map Sum.inl ++ (g w).map Sum.inr`.  The merged copy set is `Fin (Kf + Kg)`
split by `Fin.addCases`; the rank is `ℤ^(1 + d_f + d_g)` with coordinate 0 the block
index, coordinates `1 .. d_f` carrying `κ_f` (and `0` on `g`-copies), the rest
carrying `κ_g`. -/

section DisjointUnion

variable {Alpha Γf Γg : Type}

/-- The merged copy set's arity: `Pf.arity` on the left block, `Pg.arity` on the
right block. -/
@[reducible] def duArity (Pf : Polyreg.Presentation Alpha Γf) (Pg : Polyreg.Presentation Alpha Γg) :
    Fin (Pf.K + Pg.K) → ℕ :=
  Fin.addCases (fun cf => Pf.arity cf) (fun cg => Pg.arity cg)

@[simp] theorem duArity_left (Pf : Polyreg.Presentation Alpha Γf)
    (Pg : Polyreg.Presentation Alpha Γg) (cf : Fin Pf.K) :
    duArity Pf Pg (Fin.castAdd Pg.K cf) = Pf.arity cf := by simp [duArity]

@[simp] theorem duArity_right (Pf : Polyreg.Presentation Alpha Γf)
    (Pg : Polyreg.Presentation Alpha Γg) (cg : Fin Pg.K) :
    duArity Pf Pg (Fin.natAdd Pf.K cg) = Pg.arity cg := by simp [duArity]

/-! ### The combined rank layout `ℤ^{1 + (d_f + d_g)}`

Coordinate `0` is the **block index** (`0` on `f`-copies, `1` on `g`-copies); the
remaining `d_f + d_g` coordinates split (`Fin.addCases`) into an `f`-block carrying
`κ_f` and a `g`-block carrying `κ_g`.  `projF`/`projG` are the partial inverse
coordinate maps feeding `isRegularRankTerm_reindex`. -/

/-- Partial coordinate map reading the `f`-block: coordinate `0` (block index) and
the `g`-block map to `none`; the `f`-block maps identically.  The combined rank
dimension is `d_f + d_g + 1`: coordinate `0` is the block index, then the
remaining coordinates split (`Fin.addCases`) into the f-block and the g-block. -/
def projF (df dg : ℕ) (coord : Fin (df + dg + 1)) : Option (Fin df) :=
  Fin.cases none
    (fun j => Fin.addCases (motive := fun _ => Option (Fin df))
      (fun jf => some jf) (fun _ => none) j) coord

/-- Partial coordinate map reading the `g`-block. -/
def projG (df dg : ℕ) (coord : Fin (df + dg + 1)) : Option (Fin dg) :=
  Fin.cases none
    (fun j => Fin.addCases (motive := fun _ => Option (Fin dg))
      (fun _ => none) (fun jg => some jg) j) coord

/-- The block-index unit vector: `b` at coordinate `0`, `0` elsewhere. -/
def blockVec (df dg : ℕ) (b : ℤ) (coord : Fin (df + dg + 1)) : ℤ :=
  Fin.cases b (fun _ => 0) coord

@[simp] theorem blockVec_zero (df dg : ℕ) (b : ℤ) :
    blockVec df dg b 0 = b := by simp [blockVec]

@[simp] theorem projF_zero (df dg : ℕ) : projF df dg 0 = none := by simp [projF]

@[simp] theorem projG_zero (df dg : ℕ) : projG df dg 0 = none := by simp [projG]

@[simp] theorem projF_succ_castAdd (df dg : ℕ) (jf : Fin df) :
    projF df dg (Fin.succ (Fin.castAdd dg jf)) = some jf := by simp [projF]

@[simp] theorem projF_succ_natAdd (df dg : ℕ) (jg : Fin dg) :
    projF df dg (Fin.succ (Fin.natAdd df jg)) = none := by simp [projF]

@[simp] theorem projG_succ_castAdd (df dg : ℕ) (jf : Fin df) :
    projG df dg (Fin.succ (Fin.castAdd dg jf)) = none := by simp [projG]

@[simp] theorem projG_succ_natAdd (df dg : ℕ) (jg : Fin dg) :
    projG df dg (Fin.succ (Fin.natAdd df jg)) = some jg := by simp [projG]

/-- Spread an `f`-rank `v : Fin df → ℤ` into the combined layout at block index `b`:
coordinate `0` gets `b`, the `f`-block gets `v`, the `g`-block gets `0`. -/
def embedF (df dg : ℕ) (b : ℤ) (v : Fin df → ℤ) : Fin (df + dg + 1) → ℤ :=
  fun coord => blockVec df dg b coord + (projF df dg coord).elim 0 v

/-- Spread a `g`-rank `v : Fin dg → ℤ` into the combined layout at block index `b`. -/
def embedG (df dg : ℕ) (b : ℤ) (v : Fin dg → ℤ) : Fin (df + dg + 1) → ℤ :=
  fun coord => blockVec df dg b coord + (projG df dg coord).elim 0 v

@[simp] theorem embedF_zero (df dg : ℕ) (b : ℤ) (v : Fin df → ℤ) :
    embedF df dg b v 0 = b := by simp [embedF]

@[simp] theorem embedG_zero (df dg : ℕ) (b : ℤ) (v : Fin dg → ℤ) :
    embedG df dg b v 0 = b := by simp [embedG]

/-- On the `f`-block (`succ (castAdd jf)`) `embedF` reads `v`. -/
@[simp] theorem embedF_fblock (df dg : ℕ) (b : ℤ) (v : Fin df → ℤ) (jf : Fin df) :
    embedF df dg b v (Fin.succ (Fin.castAdd dg jf)) = v jf := by
  simp [embedF, blockVec]

/-- On the `g`-block `embedF` reads `0`. -/
@[simp] theorem embedF_gblock (df dg : ℕ) (b : ℤ) (v : Fin df → ℤ) (jg : Fin dg) :
    embedF df dg b v (Fin.succ (Fin.natAdd df jg)) = 0 := by
  simp [embedF, blockVec]

@[simp] theorem embedG_fblock (df dg : ℕ) (b : ℤ) (v : Fin dg → ℤ) (jf : Fin df) :
    embedG df dg b v (Fin.succ (Fin.castAdd dg jf)) = 0 := by
  simp [embedG, blockVec]

@[simp] theorem embedG_gblock (df dg : ℕ) (b : ℤ) (v : Fin dg → ℤ) (jg : Fin dg) :
    embedG df dg b v (Fin.succ (Fin.natAdd df jg)) = v jg := by
  simp [embedG, blockVec]

/-- **Cross-block lex.**  An `f`-block embedding (block index `0`) is `lexLt`-below a
`g`-block embedding (block index `1`): they first differ at coordinate `0`. -/
theorem lexLt_embedF_embedG (df dg : ℕ) (vf : Fin df → ℤ) (vg : Fin dg → ℤ) :
    WRP.lexLt (embedF df dg 0 vf) (embedG df dg 1 vg) := by
  refine ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩
  simp

/-- The converse cross-block comparison fails. -/
theorem not_lexLt_embedG_embedF (df dg : ℕ) (vf : Fin df → ℤ) (vg : Fin dg → ℤ) :
    ¬ WRP.lexLt (embedG df dg 1 vg) (embedF df dg 0 vf) := by
  rintro ⟨i, hlt, hi⟩
  -- coordinate `0` already disagrees (`1 ≠ 0`), so `i` cannot be `> 0`; but at `0` it is `1 > 0`
  refine absurd (hlt 0 ?_) (by simp)
  rcases Fin.eq_zero_or_eq_succ i with hi0 | ⟨i', rfl⟩
  · subst hi0; simp at hi
  · exact Fin.succ_pos i'

/-- An `f`-block embedding never equals a `g`-block embedding (block indices differ). -/
theorem embedF_ne_embedG (df dg : ℕ) (vf : Fin df → ℤ) (vg : Fin dg → ℤ) :
    embedF df dg 0 vf ≠ embedG df dg 1 vg := by
  intro h
  have := congrFun h 0
  simp at this

/-! ### General block-index domination (for the 3-block concat (iii)) -/

/-- A lower block index `lexLt`-dominates: the embeddings first differ at coordinate
`0`.  Stated for the four `embed{F,G}`/`embed{F,G}` combinations via the shared
coordinate-`0` value. -/
theorem lexLt_of_block_lt (df dg : ℕ) (x y : Fin (df + dg + 1) → ℤ)
    (h0 : x 0 < y 0) : WRP.lexLt x y :=
  ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h0⟩

theorem not_lexLt_of_block_lt (df dg : ℕ) (x y : Fin (df + dg + 1) → ℤ)
    (h0 : y 0 < x 0) : ¬ WRP.lexLt x y := by
  rintro ⟨i, hlt, hi⟩
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · omega
  · exact absurd (hlt 0 (Fin.succ_pos i')) (by omega)

/-- The combined coordinate carrying `f`-block index `jf`. -/
def fCoord (df dg : ℕ) (jf : Fin df) : Fin (df + dg + 1) := Fin.succ (Fin.castAdd dg jf)

/-- The combined coordinate carrying `g`-block index `jg`. -/
def gCoord (df dg : ℕ) (jg : Fin dg) : Fin (df + dg + 1) := Fin.succ (Fin.natAdd df jg)

theorem fCoord_lt_iff (df dg : ℕ) (jf jf' : Fin df) :
    fCoord df dg jf < fCoord df dg jf' ↔ jf < jf' := by
  unfold fCoord
  rw [Fin.succ_lt_succ_iff]
  constructor
  · intro h
    by_contra hcon
    exact absurd h (not_lt.mpr (by
      rw [Fin.le_def] at *; simpa [Fin.castAdd] using (not_lt.mp hcon)))
  · intro h
    rw [Fin.lt_def] at *; simpa [Fin.castAdd] using h

/-- A combined coordinate below `fCoord df dg jf` is either `0` or another `f`-block
coordinate `fCoord df dg jf₀` with `jf₀ < jf`. -/
theorem lt_fCoord_cases (df dg : ℕ) (jf : Fin df) (i : Fin (df + dg + 1))
    (hi : i < fCoord df dg jf) :
    i = 0 ∨ ∃ jf₀ : Fin df, jf₀ < jf ∧ i = fCoord df dg jf₀ := by
  rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
  · exact Or.inl h0
  · refine Fin.addCases (motive := fun j =>
        Fin.succ j < fCoord df dg jf →
          Fin.succ j = 0 ∨ ∃ jf₀ : Fin df, jf₀ < jf ∧ Fin.succ j = fCoord df dg jf₀)
      ?_ ?_ j hi
    · intro jf₀ hlt
      refine Or.inr ⟨jf₀, ?_, rfl⟩
      rw [← fCoord_lt_iff df dg]
      exact hlt
    · intro jg hlt
      -- a `g`-block coordinate is never `<` an `f`-block coordinate (g-block is to the right)
      exfalso
      unfold fCoord at hlt
      rw [Fin.succ_lt_succ_iff, Fin.lt_def] at hlt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hlt
      have := jf.isLt
      omega

/-- **Within-`f`-block lex equivalence.**  Two `f`-embeddings (same block index)
compare exactly as their underlying `f`-ranks do. -/
theorem lexLt_embedF_iff (df dg : ℕ) (b : ℤ) (vf vf' : Fin df → ℤ) :
    WRP.lexLt (embedF df dg b vf) (embedF df dg b vf') ↔ WRP.lexLt vf vf' := by
  constructor
  · rintro ⟨i, hlt, hi⟩
    -- the witness coordinate `i` lies in the `f`-block (block index and `g`-block tie)
    rcases Fin.eq_zero_or_eq_succ i with hi0 | ⟨j, rfl⟩
    · subst hi0; simp at hi
    · refine Fin.addCases (motive := fun j =>
          embedF df dg b vf (Fin.succ j) < embedF df dg b vf' (Fin.succ j) →
            (∀ k, k < Fin.succ j → embedF df dg b vf k = embedF df dg b vf' k) →
            WRP.lexLt vf vf') ?_ ?_ j hi hlt
      · intro jf hi' hlt'
        refine ⟨jf, fun k hk => ?_, ?_⟩
        · have := hlt' (fCoord df dg k) (by rw [fCoord]; exact (fCoord_lt_iff df dg k jf).mpr hk)
          simpa [fCoord] using this
        · simpa [fCoord] using hi'
      · intro jg hi' _
        -- `g`-block coordinate ties: contradiction
        simp [embedF_gblock] at hi'
  · rintro ⟨jf, hlt, hi⟩
    refine ⟨fCoord df dg jf, fun k hk => ?_, ?_⟩
    · rcases lt_fCoord_cases df dg jf k hk with rfl | ⟨jf₀, hjf₀, rfl⟩
      · simp
      · simp only [fCoord, embedF_fblock]; exact hlt jf₀ hjf₀
    · simpa [fCoord] using hi

theorem gCoord_lt_iff (df dg : ℕ) (jg jg' : Fin dg) :
    gCoord df dg jg < gCoord df dg jg' ↔ jg < jg' := by
  unfold gCoord
  rw [Fin.succ_lt_succ_iff, Fin.lt_def, Fin.lt_def]
  simp [Fin.natAdd]

/-- A combined coordinate below `gCoord df dg jg` is `0`, an `f`-block coordinate, or
a smaller `g`-block coordinate. -/
theorem lt_gCoord_cases (df dg : ℕ) (jg : Fin dg) (i : Fin (df + dg + 1))
    (hi : i < gCoord df dg jg) :
    i = 0 ∨ (∃ jf : Fin df, i = fCoord df dg jf)
      ∨ ∃ jg₀ : Fin dg, jg₀ < jg ∧ i = gCoord df dg jg₀ := by
  rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
  · exact Or.inl h0
  · refine Fin.addCases (motive := fun j =>
        Fin.succ j < gCoord df dg jg →
          Fin.succ j = 0 ∨ (∃ jf : Fin df, Fin.succ j = fCoord df dg jf)
            ∨ ∃ jg₀ : Fin dg, jg₀ < jg ∧ Fin.succ j = gCoord df dg jg₀)
      ?_ ?_ j hi
    · intro jf _
      exact Or.inr (Or.inl ⟨jf, rfl⟩)
    · intro jg₀ hlt
      refine Or.inr (Or.inr ⟨jg₀, ?_, rfl⟩)
      rw [← gCoord_lt_iff df dg]
      exact hlt

/-- **Within-`g`-block lex equivalence.**  Two `g`-embeddings (same block index)
compare exactly as their underlying `g`-ranks do. -/
theorem lexLt_embedG_iff (df dg : ℕ) (b : ℤ) (vg vg' : Fin dg → ℤ) :
    WRP.lexLt (embedG df dg b vg) (embedG df dg b vg') ↔ WRP.lexLt vg vg' := by
  constructor
  · rintro ⟨i, hlt, hi⟩
    rcases Fin.eq_zero_or_eq_succ i with hi0 | ⟨j, rfl⟩
    · subst hi0; simp at hi
    · refine Fin.addCases (motive := fun j =>
          embedG df dg b vg (Fin.succ j) < embedG df dg b vg' (Fin.succ j) →
            (∀ k, k < Fin.succ j → embedG df dg b vg k = embedG df dg b vg' k) →
            WRP.lexLt vg vg') ?_ ?_ j hi hlt
      · intro jf hi' _
        simp [embedG_fblock] at hi'
      · intro jg hi' hlt'
        refine ⟨jg, fun k hk => ?_, ?_⟩
        · have := hlt' (gCoord df dg k) (by rw [gCoord]; exact (gCoord_lt_iff df dg k jg).mpr hk)
          simpa [gCoord] using this
        · simpa [gCoord] using hi'
  · rintro ⟨jg, hlt, hi⟩
    refine ⟨gCoord df dg jg, fun k hk => ?_, ?_⟩
    · rcases lt_gCoord_cases df dg jg k hk with rfl | ⟨jf, rfl⟩ | ⟨jg₀, hjg₀, rfl⟩
      · simp
      · simp [fCoord]
      · simp only [gCoord, embedG_gblock]; exact hlt jg₀ hjg₀
    · simpa [gCoord] using hi

theorem embedF_inj_iff (df dg : ℕ) (b : ℤ) (vf vf' : Fin df → ℤ) :
    embedF df dg b vf = embedF df dg b vf' ↔ vf = vf' := by
  constructor
  · intro h; funext jf; have := congrFun h (fCoord df dg jf); simpa [fCoord] using this
  · intro h; rw [h]

theorem embedG_inj_iff (df dg : ℕ) (b : ℤ) (vg vg' : Fin dg → ℤ) :
    embedG df dg b vg = embedG df dg b vg' ↔ vg = vg' := by
  constructor
  · intro h; funext jg; have := congrFun h (gCoord df dg jg); simpa [gCoord] using this
  · intro h; rw [h]

/-! ### The merged polyregular presentation -/

variable (Pf : Polyreg.Presentation Alpha Γf) (Pg : Polyreg.Presentation Alpha Γg)

/-- Reindex a position tuple along an arity equality `h : a = a'`. -/
@[reducible] def castTuple {a a' : ℕ} (h : a = a') (ī : Fin a' → ℕ) : Fin a → ℕ :=
  fun t => ī (Fin.cast h t)

@[simp] theorem castTuple_castTuple {a a' : ℕ} (h : a = a') (ī : Fin a' → ℕ) :
    castTuple h.symm (castTuple h ī) = ī := by
  subst h; rfl

/-- The merged copy set's selection predicate. -/
@[reducible] def duSel (c : Fin (Pf.K + Pg.K)) (w : List Alpha) (ī : Fin (duArity Pf Pg c) → ℕ) : Prop :=
  Fin.addCases (motive := fun c => (Fin (duArity Pf Pg c) → ℕ) → Prop)
    (fun cf ī => Pf.sel cf w (castTuple (duArity_left Pf Pg cf).symm ī))
    (fun cg ī => Pg.sel cg w (castTuple (duArity_right Pf Pg cg).symm ī)) c ī

/-- The merged label, valued in the tagged alphabet `Γf ⊕ Γg`. -/
@[reducible] def duLabel (c : Fin (Pf.K + Pg.K)) (w : List Alpha) (ī : Fin (duArity Pf Pg c) → ℕ) : Γf ⊕ Γg :=
  Fin.addCases (motive := fun c => (Fin (duArity Pf Pg c) → ℕ) → Γf ⊕ Γg)
    (fun cf ī => Sum.inl (Pf.label cf w (castTuple (duArity_left Pf Pg cf).symm ī)))
    (fun cg ī => Sum.inr (Pg.label cg w (castTuple (duArity_right Pf Pg cg).symm ī))) c ī

/-- MSO-definability transfers across an arity equality (the free FO variables are
reindexed by the bijection `Fin.cast`). -/
theorem mso_cast {a a' : ℕ} (h : a = a') {R : List Alpha → (Fin a → ℕ) → Prop}
    (hR : MSODefinableRel a R) :
    MSODefinableRel a' (fun w ī => R w (castTuple h ī)) := by
  subst h
  refine mso_congr (fun w ī => ?_) hR
  rfl

@[simp] theorem duSel_left (cf : Fin Pf.K) (w : List Alpha) (ī : Fin (duArity Pf Pg _) → ℕ) :
    duSel Pf Pg (Fin.castAdd Pg.K cf) w ī
      = Pf.sel cf w (castTuple (duArity_left Pf Pg cf).symm ī) := by
  simp only [duSel, Fin.addCases_left]

@[simp] theorem duSel_right (cg : Fin Pg.K) (w : List Alpha) (ī : Fin (duArity Pf Pg _) → ℕ) :
    duSel Pf Pg (Fin.natAdd Pf.K cg) w ī
      = Pg.sel cg w (castTuple (duArity_right Pf Pg cg).symm ī) := by
  simp only [duSel, Fin.addCases_right]

@[simp] theorem duLabel_left (cf : Fin Pf.K) (w : List Alpha) (ī : Fin (duArity Pf Pg _) → ℕ) :
    duLabel Pf Pg (Fin.castAdd Pg.K cf) w ī
      = Sum.inl (Pf.label cf w (castTuple (duArity_left Pf Pg cf).symm ī)) := by
  simp only [duLabel, Fin.addCases_left]

@[simp] theorem duLabel_right (cg : Fin Pg.K) (w : List Alpha) (ī : Fin (duArity Pf Pg _) → ℕ) :
    duLabel Pf Pg (Fin.natAdd Pf.K cg) w ī
      = Sum.inr (Pg.label cg w (castTuple (duArity_right Pf Pg cg).symm ī)) := by
  simp only [duLabel, Fin.addCases_right]

/-- The merged ordering relation `χ`: within the `f`-block use `Pf.ord`, within the
`g`-block `Pg.ord`, and across blocks put every `f`-atom before every `g`-atom.
(Cross-block ties never arise in `wrpOrd` since the block-index rank coordinate
already separates the blocks, but a definite choice keeps `ordDef` MSO-clean.) -/
@[reducible] def duOrd (c c' : Fin (Pf.K + Pg.K)) (w : List Alpha)
    (ī : Fin (duArity Pf Pg c) → ℕ) (ī' : Fin (duArity Pf Pg c') → ℕ) : Prop :=
  Fin.addCases (motive := fun c => (Fin (duArity Pf Pg c) → ℕ) → Prop)
    (fun cf ī =>
      Fin.addCases (motive := fun c' => (Fin (duArity Pf Pg c') → ℕ) → Prop)
        (fun cf' ī' => Pf.ord cf cf' w (castTuple (duArity_left Pf Pg cf).symm ī)
          (castTuple (duArity_left Pf Pg cf').symm ī'))
        (fun _ _ => True) c' ī')
    (fun cg ī =>
      Fin.addCases (motive := fun c' => (Fin (duArity Pf Pg c') → ℕ) → Prop)
        (fun _ _ => False)
        (fun cg' ī' => Pg.ord cg cg' w (castTuple (duArity_right Pf Pg cg).symm ī)
          (castTuple (duArity_right Pf Pg cg').symm ī')) c' ī') c ī

@[simp] theorem duOrd_ff (cf cf' : Fin Pf.K) (w : List Alpha)
    (ī : Fin (duArity Pf Pg _) → ℕ) (ī' : Fin (duArity Pf Pg _) → ℕ) :
    duOrd Pf Pg (Fin.castAdd Pg.K cf) (Fin.castAdd Pg.K cf') w ī ī'
      = Pf.ord cf cf' w (castTuple (duArity_left Pf Pg cf).symm ī)
          (castTuple (duArity_left Pf Pg cf').symm ī') := by
  simp only [duOrd, Fin.addCases_left]

@[simp] theorem duOrd_gg (cg cg' : Fin Pg.K) (w : List Alpha)
    (ī : Fin (duArity Pf Pg _) → ℕ) (ī' : Fin (duArity Pf Pg _) → ℕ) :
    duOrd Pf Pg (Fin.natAdd Pf.K cg) (Fin.natAdd Pf.K cg') w ī ī'
      = Pg.ord cg cg' w (castTuple (duArity_right Pf Pg cg).symm ī)
          (castTuple (duArity_right Pf Pg cg').symm ī') := by
  simp only [duOrd, Fin.addCases_right]

@[simp] theorem duOrd_fg (cf : Fin Pf.K) (cg : Fin Pg.K) (w : List Alpha)
    (ī : Fin (duArity Pf Pg _) → ℕ) (ī' : Fin (duArity Pf Pg _) → ℕ) :
    duOrd Pf Pg (Fin.castAdd Pg.K cf) (Fin.natAdd Pf.K cg) w ī ī' = True := by
  simp only [duOrd, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem duOrd_gf (cg : Fin Pg.K) (cf : Fin Pf.K) (w : List Alpha)
    (ī : Fin (duArity Pf Pg _) → ℕ) (ī' : Fin (duArity Pf Pg _) → ℕ) :
    duOrd Pf Pg (Fin.natAdd Pf.K cg) (Fin.castAdd Pg.K cf) w ī ī' = False := by
  simp only [duOrd, Fin.addCases_left, Fin.addCases_right]

/-- MSO-definability of a binary ordering relation transfers across arity
equalities on the two argument blocks. -/
theorem mso_cast2 {af af' bf bf' : ℕ} (hf : af = bf) (hf' : af' = bf')
    {R : List Alpha → (Fin af → ℕ) → (Fin af' → ℕ) → Prop}
    (hR : MSODefinableRel (af + af')
      (fun w ij => R w (fun t => ij (Fin.castAdd af' t)) (fun t => ij (Fin.natAdd af t)))) :
    MSODefinableRel (bf + bf')
      (fun w ij => R w (castTuple hf (fun t => ij (Fin.castAdd bf' t)))
        (castTuple hf' (fun t => ij (Fin.natAdd bf t)))) := by
  subst hf; subst hf'
  exact hR

/-- The merged selection predicate is MSO-definable. -/
theorem duSelDef (c : Fin (Pf.K + Pg.K)) :
    MSODefinableRel (duArity Pf Pg c) (fun w ī => duSel Pf Pg c w ī) := by
  refine Fin.addCases (motive := fun c =>
    MSODefinableRel (duArity Pf Pg c) (fun w ī => duSel Pf Pg c w ī)) ?_ ?_ c
  · intro cf
    refine mso_congr (fun w ī => iff_of_eq (duSel_left Pf Pg cf w ī).symm) ?_
    exact mso_cast (duArity_left Pf Pg cf).symm (Pf.selDef cf)
  · intro cg
    refine mso_congr (fun w ī => iff_of_eq (duSel_right Pf Pg cg w ī).symm) ?_
    exact mso_cast (duArity_right Pf Pg cg).symm (Pg.selDef cg)

/-- Each merged label-class is MSO-definable. -/
theorem duLabelDef (c : Fin (Pf.K + Pg.K)) (g : Γf ⊕ Γg) :
    MSODefinableRel (duArity Pf Pg c) (fun w ī => duLabel Pf Pg c w ī = g) := by
  refine Fin.addCases (motive := fun c =>
    MSODefinableRel (duArity Pf Pg c) (fun w ī => duLabel Pf Pg c w ī = g)) ?_ ?_ c
  · intro cf
    rcases g with gf | gg
    · -- f-copy, target `inl gf`: reduces to `Pf.label cf … = gf`
      refine mso_congr (fun w ī => ?_)
        (mso_cast (duArity_left Pf Pg cf).symm (Pf.labelDef cf gf))
      rw [duLabel_left, Sum.inl.injEq]
    · -- f-copy, target `inr gg`: never holds
      refine mso_congr (R := fun _ _ => False) (fun w ī => ?_)
        ⟨.neg .tru, fun w ρ => by simp⟩
      rw [duLabel_left]; simp
  · intro cg
    rcases g with gf | gg
    · refine mso_congr (R := fun _ _ => False) (fun w ī => ?_)
        ⟨.neg .tru, fun w ρ => by simp⟩
      rw [duLabel_right]; simp
    · refine mso_congr (fun w ī => ?_)
        (mso_cast (duArity_right Pf Pg cg).symm (Pg.labelDef cg gg))
      rw [duLabel_right, Sum.inr.injEq]

/-- The merged ordering relation `χ` is MSO-definable. -/
theorem duOrdDef (c c' : Fin (Pf.K + Pg.K)) :
    MSODefinableRel (duArity Pf Pg c + duArity Pf Pg c')
      (fun w ij => duOrd Pf Pg c c' w (fun t => ij (Fin.castAdd _ t))
        (fun t => ij (Fin.natAdd _ t))) := by
  refine Fin.addCases (motive := fun c => MSODefinableRel (duArity Pf Pg c + duArity Pf Pg c')
      (fun w ij => duOrd Pf Pg c c' w (fun t => ij (Fin.castAdd _ t))
        (fun t => ij (Fin.natAdd _ t)))) ?_ ?_ c
  · intro cf
    refine Fin.addCases (motive := fun c' =>
        MSODefinableRel (duArity Pf Pg (Fin.castAdd Pg.K cf) + duArity Pf Pg c')
          (fun w ij => duOrd Pf Pg (Fin.castAdd Pg.K cf) c' w (fun t => ij (Fin.castAdd _ t))
            (fun t => ij (Fin.natAdd _ t)))) ?_ ?_ c'
    · -- ff: `Pf.ord cf cf'` cylindrified through the casts
      intro cf'
      exact mso_congr (fun w ij => iff_of_eq (duOrd_ff Pf Pg cf cf' w _ _).symm)
        (mso_cast2 (duArity_left Pf Pg cf).symm (duArity_left Pf Pg cf').symm (Pf.ordDef cf cf'))
    · -- fg: constant `True`
      intro cg
      refine mso_congr (R := fun _ _ => True) (fun w ij => ?_) ⟨.tru, fun w ρ => by simp⟩
      rw [duOrd_fg]
  · intro cg
    refine Fin.addCases (motive := fun c' =>
        MSODefinableRel (duArity Pf Pg (Fin.natAdd Pf.K cg) + duArity Pf Pg c')
          (fun w ij => duOrd Pf Pg (Fin.natAdd Pf.K cg) c' w (fun t => ij (Fin.castAdd _ t))
            (fun t => ij (Fin.natAdd _ t)))) ?_ ?_ c'
    · -- gf: constant `False`
      intro cf
      refine mso_congr (R := fun _ _ => False) (fun w ij => ?_) ⟨.neg .tru, fun w ρ => by simp⟩
      rw [duOrd_gf]
    · -- gg: `Pg.ord cg cg'` cylindrified
      intro cg'
      exact mso_congr (fun w ij => iff_of_eq (duOrd_gg Pf Pg cg cg' w _ _).symm)
        (mso_cast2 (duArity_right Pf Pg cg).symm (duArity_right Pf Pg cg').symm (Pg.ordDef cg cg'))

/-- **The merged polyregular presentation** (`thm:wrp-closures` (ii)): the disjoint
union of `Pf`'s and `Pg`'s copy sets, labels tagged into `Γf ⊕ Γg`, domain the
intersection.  (Its `χ` puts every `f`-atom before every `g`-atom; the WRP layer
re-derives this separation via the block-index rank coordinate.) -/
@[reducible] def duPoly : Polyreg.Presentation Alpha (Γf ⊕ Γg) where
  K := Pf.K + Pg.K
  arity := duArity Pf Pg
  domain := fun w => Pf.domain w ∧ Pg.domain w
  domainDef := by
    obtain ⟨φf, hφf⟩ := Pf.domainDef
    obtain ⟨φg, hφg⟩ := Pg.domainDef
    exact ⟨Formula.and φf φg, fun w => by rw [Formula.sat_and, ← hφf, ← hφg]⟩
  sel := duSel Pf Pg
  selDef := duSelDef Pf Pg
  label := duLabel Pf Pg
  labelDef := duLabelDef Pf Pg
  ord := duOrd Pf Pg
  ordDef := duOrdDef Pf Pg

/-- The merged rank: block index at coordinate `0`, then `κ_f` (resp. `κ_g`) embedded
into the `f`-block (resp. `g`-block) of `ℤ^{d_f + d_g + 1}`.  Takes the WRP
presentations `Wf, Wg` (whose poly parts are `Pf, Pg`). -/
@[reducible] def duRank (Wf : WRP.Presentation Alpha Γf) (Wg : WRP.Presentation Alpha Γg)
    (c : Fin (Wf.toPoly.K + Wg.toPoly.K)) (w : List Alpha)
    (ī : Fin (duArity Wf.toPoly Wg.toPoly c) → ℕ) : Fin (Wf.d + Wg.d + 1) → ℤ :=
  Fin.addCases (motive := fun c =>
      (Fin (duArity Wf.toPoly Wg.toPoly c) → ℕ) → (Fin (Wf.d + Wg.d + 1) → ℤ))
    (fun cf ī => embedF Wf.d Wg.d 0
      (Wf.rank cf w (castTuple (duArity_left Wf.toPoly Wg.toPoly cf).symm ī)))
    (fun cg ī => embedG Wf.d Wg.d 1
      (Wg.rank cg w (castTuple (duArity_right Wf.toPoly Wg.toPoly cg).symm ī)))
    c ī

@[simp] theorem duRank_left (Wf : WRP.Presentation Alpha Γf) (Wg : WRP.Presentation Alpha Γg)
    (cf : Fin Wf.toPoly.K) (w : List Alpha) (ī : Fin (duArity Wf.toPoly Wg.toPoly _) → ℕ) :
    duRank Wf Wg (Fin.castAdd Wg.toPoly.K cf) w ī
      = embedF Wf.d Wg.d 0
          (Wf.rank cf w (castTuple (duArity_left Wf.toPoly Wg.toPoly cf).symm ī)) := by
  simp only [duRank, Fin.addCases_left]

@[simp] theorem duRank_right (Wf : WRP.Presentation Alpha Γf) (Wg : WRP.Presentation Alpha Γg)
    (cg : Fin Wg.toPoly.K) (w : List Alpha) (ī : Fin (duArity Wf.toPoly Wg.toPoly _) → ℕ) :
    duRank Wf Wg (Fin.natAdd Wf.toPoly.K cg) w ī
      = embedG Wf.d Wg.d 1
          (Wg.rank cg w (castTuple (duArity_right Wf.toPoly Wg.toPoly cg).symm ī)) := by
  simp only [duRank, Fin.addCases_right]

/-- The merged rank is a regular rank term (R1: constant block index + embedded
sub-rank). -/
theorem duRankReg (Wf : WRP.Presentation Alpha Γf) (Wg : WRP.Presentation Alpha Γg)
    (c : Fin (Wf.toPoly.K + Wg.toPoly.K)) : IsRegularRankTerm (duRank Wf Wg c) := by
  refine Fin.addCases (motive := fun c => IsRegularRankTerm (duRank Wf Wg c)) ?_ ?_ c
  · intro cf
    have hreg : IsRegularRankTerm (fun w ī coord =>
        blockVec Wf.d Wg.d 0 coord + (projF Wf.d Wg.d coord).elim 0
          (Wf.rank cf w (castTuple (duArity_left Wf.toPoly Wg.toPoly cf).symm ī))) := by
      apply isRegularRankTerm_add (isRegularRankTerm_const _)
      exact isRegularRankTerm_reindex
        (isRegularRankTerm_castArg (duArity_left Wf.toPoly Wg.toPoly cf).symm (Wf.rankReg cf))
        (projF Wf.d Wg.d)
    refine ⟨hreg.choose, fun w ī => ?_⟩
    rw [duRank_left]
    funext coord
    rw [embedF]
    exact congrFun (hreg.choose_spec w ī) coord
  · intro cg
    have hreg : IsRegularRankTerm (fun w ī coord =>
        blockVec Wf.d Wg.d 1 coord + (projG Wf.d Wg.d coord).elim 0
          (Wg.rank cg w (castTuple (duArity_right Wf.toPoly Wg.toPoly cg).symm ī))) := by
      apply isRegularRankTerm_add (isRegularRankTerm_const _)
      exact isRegularRankTerm_reindex
        (isRegularRankTerm_castArg (duArity_right Wf.toPoly Wg.toPoly cg).symm (Wg.rankReg cg))
        (projG Wf.d Wg.d)
    refine ⟨hreg.choose, fun w ī => ?_⟩
    rw [duRank_right]
    funext coord
    rw [embedG]
    exact congrFun (hreg.choose_spec w ī) coord

/-- **The merged WRP presentation** (`thm:wrp-closures` (ii)). -/
@[reducible] def duPres (Wf : WRP.Presentation Alpha Γf) (Wg : WRP.Presentation Alpha Γg) :
    WRP.Presentation Alpha (Γf ⊕ Γg) where
  toPoly := duPoly Wf.toPoly Wg.toPoly
  d := Wf.d + Wg.d + 1
  rank := duRank Wf Wg
  rankReg := duRankReg Wf Wg

/-! ### Atom maps and the order correspondence -/

variable (Wf : WRP.Presentation Alpha Γf) (Wg : WRP.Presentation Alpha Γg)

/-- Inject an `f`-atom into the merged copy set (its position tuple reindexed by the
arity equality). -/
@[reducible] def fAtom (a : Wf.toPoly.Atom) : (duPres Wf Wg).toPoly.Atom :=
  ⟨Fin.castAdd Wg.toPoly.K a.1, castTuple (duArity_left Wf.toPoly Wg.toPoly a.1) a.2⟩

/-- Inject a `g`-atom into the merged copy set. -/
@[reducible] def gAtom (b : Wg.toPoly.Atom) : (duPres Wf Wg).toPoly.Atom :=
  ⟨Fin.natAdd Wf.toPoly.K b.1, castTuple (duArity_right Wf.toPoly Wg.toPoly b.1) b.2⟩

/-- Every merged atom is an `f`-atom or a `g`-atom. -/
theorem duAtom_cases (a : (duPres Wf Wg).toPoly.Atom) :
    (∃ a₀ : Wf.toPoly.Atom, a = fAtom Wf Wg a₀) ∨
      (∃ b₀ : Wg.toPoly.Atom, a = gAtom Wf Wg b₀) := by
  obtain ⟨c, ī⟩ := a
  refine Fin.addCases (motive := fun c => ∀ ī : Fin (duArity Wf.toPoly Wg.toPoly c) → ℕ,
      (∃ a₀ : Wf.toPoly.Atom, (⟨c, ī⟩ : (duPres Wf Wg).toPoly.Atom) = fAtom Wf Wg a₀) ∨
        (∃ b₀ : Wg.toPoly.Atom, (⟨c, ī⟩ : (duPres Wf Wg).toPoly.Atom) = gAtom Wf Wg b₀))
    ?_ ?_ c ī
  · intro cf ī
    refine Or.inl ⟨⟨cf, castTuple (duArity_left Wf.toPoly Wg.toPoly cf).symm ī⟩, ?_⟩
    exact Sigma.ext rfl (heq_of_eq (funext fun t => rfl))
  · intro cg ī
    refine Or.inr ⟨⟨cg, castTuple (duArity_right Wf.toPoly Wg.toPoly cg).symm ī⟩, ?_⟩
    exact Sigma.ext rfl (heq_of_eq (funext fun t => rfl))

/-- Validity (all positions in range) of an `f`-atom ↔ validity in `Wf`. -/
theorem validAtom_fAtom (w : List Alpha) (a : Wf.toPoly.Atom) :
    (duPres Wf Wg).toPoly.validAtom w (fAtom Wf Wg a) ↔ Wf.toPoly.validAtom w a := by
  constructor
  · intro hval t
    have := hval (Fin.cast (duArity_left Wf.toPoly Wg.toPoly a.1).symm t)
    simpa [fAtom, castTuple] using this
  · intro hval t
    simpa [fAtom, castTuple] using hval (Fin.cast (duArity_left Wf.toPoly Wg.toPoly a.1) t)

theorem validAtom_gAtom (w : List Alpha) (b : Wg.toPoly.Atom) :
    (duPres Wf Wg).toPoly.validAtom w (gAtom Wf Wg b) ↔ Wg.toPoly.validAtom w b := by
  constructor
  · intro hval t
    have := hval (Fin.cast (duArity_right Wf.toPoly Wg.toPoly b.1).symm t)
    simpa [gAtom, castTuple] using this
  · intro hval t
    simpa [gAtom, castTuple] using hval (Fin.cast (duArity_right Wf.toPoly Wg.toPoly b.1) t)

/-- Selectedness of an `f`-atom in the merge ↔ selectedness in `Wf`. -/
theorem selectedAtom_fAtom (w : List Alpha) (a : Wf.toPoly.Atom) :
    (duPres Wf Wg).toPoly.selectedAtom w (fAtom Wf Wg a) ↔ Wf.toPoly.selectedAtom w a := by
  rw [Polyreg.Presentation.selectedAtom, Polyreg.Presentation.selectedAtom,
    validAtom_fAtom]
  refine and_congr Iff.rfl ?_
  show duSel Wf.toPoly Wg.toPoly (Fin.castAdd Wg.toPoly.K a.1) w (fAtom Wf Wg a).2 ↔ _
  rw [duSel_left]
  simp

/-- Selectedness of a `g`-atom in the merge ↔ selectedness in `Wg`. -/
theorem selectedAtom_gAtom (w : List Alpha) (b : Wg.toPoly.Atom) :
    (duPres Wf Wg).toPoly.selectedAtom w (gAtom Wf Wg b) ↔ Wg.toPoly.selectedAtom w b := by
  rw [Polyreg.Presentation.selectedAtom, Polyreg.Presentation.selectedAtom,
    validAtom_gAtom]
  refine and_congr Iff.rfl ?_
  show duSel Wf.toPoly Wg.toPoly (Fin.natAdd Wf.toPoly.K b.1) w (gAtom Wf Wg b).2 ↔ _
  rw [duSel_right]
  simp

/-- The merged label of an `f`-atom is its `Wf`-label tagged `inl`. -/
theorem labelOf_fAtom (w : List Alpha) (a : Wf.toPoly.Atom) :
    (duPres Wf Wg).toPoly.labelOf w (fAtom Wf Wg a) = Sum.inl (Wf.toPoly.labelOf w a) := by
  show duLabel Wf.toPoly Wg.toPoly (Fin.castAdd Wg.toPoly.K a.1) w (fAtom Wf Wg a).2 = _
  rw [duLabel_left]
  simp [Polyreg.Presentation.labelOf]

/-- The merged label of a `g`-atom is its `Wg`-label tagged `inr`. -/
theorem labelOf_gAtom (w : List Alpha) (b : Wg.toPoly.Atom) :
    (duPres Wf Wg).toPoly.labelOf w (gAtom Wf Wg b) = Sum.inr (Wg.toPoly.labelOf w b) := by
  show duLabel Wf.toPoly Wg.toPoly (Fin.natAdd Wf.toPoly.K b.1) w (gAtom Wf Wg b).2 = _
  rw [duLabel_right]
  simp [Polyreg.Presentation.labelOf]

/-- The merged rank of an `f`-atom is its `Wf`-rank embedded at block index `0`. -/
theorem rankOf_fAtom (w : List Alpha) (a : Wf.toPoly.Atom) :
    (duPres Wf Wg).rankOf w (fAtom Wf Wg a) = embedF Wf.d Wg.d 0 (Wf.rankOf w a) := by
  show duRank Wf Wg (Fin.castAdd Wg.toPoly.K a.1) w (fAtom Wf Wg a).2 = _
  rw [duRank_left]
  simp [WRP.Presentation.rankOf]

/-- The merged rank of a `g`-atom is its `Wg`-rank embedded at block index `1`. -/
theorem rankOf_gAtom (w : List Alpha) (b : Wg.toPoly.Atom) :
    (duPres Wf Wg).rankOf w (gAtom Wf Wg b) = embedG Wf.d Wg.d 1 (Wg.rankOf w b) := by
  show duRank Wf Wg (Fin.natAdd Wf.toPoly.K b.1) w (gAtom Wf Wg b).2 = _
  rw [duRank_right]
  simp [WRP.Presentation.rankOf]

/-- The merged `atomOrd` between two `f`-atoms is `Wf`'s. -/
theorem atomOrd_fAtom_fAtom (w : List Alpha) (a a' : Wf.toPoly.Atom) :
    (duPres Wf Wg).toPoly.atomOrd w (fAtom Wf Wg a) (fAtom Wf Wg a')
      ↔ Wf.toPoly.atomOrd w a a' := by
  show duOrd Wf.toPoly Wg.toPoly (Fin.castAdd Wg.toPoly.K a.1)
    (Fin.castAdd Wg.toPoly.K a'.1) w (fAtom Wf Wg a).2 (fAtom Wf Wg a').2 ↔ _
  rw [duOrd_ff]
  simp [Polyreg.Presentation.atomOrd]

theorem atomOrd_gAtom_gAtom (w : List Alpha) (b b' : Wg.toPoly.Atom) :
    (duPres Wf Wg).toPoly.atomOrd w (gAtom Wf Wg b) (gAtom Wf Wg b')
      ↔ Wg.toPoly.atomOrd w b b' := by
  show duOrd Wf.toPoly Wg.toPoly (Fin.natAdd Wf.toPoly.K b.1)
    (Fin.natAdd Wf.toPoly.K b'.1) w (gAtom Wf Wg b).2 (gAtom Wf Wg b').2 ↔ _
  rw [duOrd_gg]
  simp [Polyreg.Presentation.atomOrd]

/-- **Order within the `f`-block**: the merge orders two `f`-atoms exactly as `Wf`. -/
theorem wrpOrd_fAtom_fAtom (w : List Alpha) (a a' : Wf.toPoly.Atom) :
    (duPres Wf Wg).wrpOrd w (fAtom Wf Wg a) (fAtom Wf Wg a') ↔ Wf.wrpOrd w a a' := by
  show (WRP.lexLt _ _ ∨ (_ = _ ∧ _)) ↔ (WRP.lexLt _ _ ∨ (_ = _ ∧ _))
  rw [rankOf_fAtom, rankOf_fAtom, lexLt_embedF_iff, embedF_inj_iff,
    atomOrd_fAtom_fAtom]

/-- **Order within the `g`-block**: the merge orders two `g`-atoms exactly as `Wg`. -/
theorem wrpOrd_gAtom_gAtom (w : List Alpha) (b b' : Wg.toPoly.Atom) :
    (duPres Wf Wg).wrpOrd w (gAtom Wf Wg b) (gAtom Wf Wg b') ↔ Wg.wrpOrd w b b' := by
  show (WRP.lexLt _ _ ∨ (_ = _ ∧ _)) ↔ (WRP.lexLt _ _ ∨ (_ = _ ∧ _))
  rw [rankOf_gAtom, rankOf_gAtom, lexLt_embedG_iff, embedG_inj_iff,
    atomOrd_gAtom_gAtom]

/-- **Cross-block**: every `f`-atom precedes every `g`-atom. -/
theorem wrpOrd_fAtom_gAtom (w : List Alpha) (a : Wf.toPoly.Atom) (b : Wg.toPoly.Atom) :
    (duPres Wf Wg).wrpOrd w (fAtom Wf Wg a) (gAtom Wf Wg b) := by
  refine Or.inl ?_
  rw [rankOf_fAtom, rankOf_gAtom]
  exact lexLt_embedF_embedG Wf.d Wg.d _ _

/-- **Cross-block**: no `g`-atom precedes any `f`-atom. -/
theorem not_wrpOrd_gAtom_fAtom (w : List Alpha) (a : Wf.toPoly.Atom) (b : Wg.toPoly.Atom) :
    ¬ (duPres Wf Wg).wrpOrd w (gAtom Wf Wg b) (fAtom Wf Wg a) := by
  rw [WRP.Presentation.wrpOrd, rankOf_fAtom, rankOf_gAtom]
  rintro (h | ⟨heq, _⟩)
  · exact not_lexLt_embedG_embedF Wf.d Wg.d _ _ h
  · exact embedF_ne_embedG Wf.d Wg.d _ _ heq.symm

/-- An `f`-atom and a `g`-atom are never equal in the merge. -/
theorem fAtom_ne_gAtom (a : Wf.toPoly.Atom) (b : Wg.toPoly.Atom) :
    fAtom Wf Wg a ≠ gAtom Wf Wg b := by
  intro h
  have hfst := congrArg Sigma.fst h
  -- `castAdd` and `natAdd` images are disjoint: value `< Wf.K` vs `≥ Wf.K`
  have hval : (Fin.castAdd Wg.toPoly.K a.1).val = (Fin.natAdd Wf.toPoly.K b.1).val :=
    congrArg Fin.val hfst
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  have := a.1.isLt
  omega

theorem fAtom_injective : Function.Injective (fAtom Wf Wg) := by
  rintro ⟨c, ī⟩ ⟨c', ī'⟩ h
  have hcast : Fin.castAdd Wg.toPoly.K c = Fin.castAdd Wg.toPoly.K c' := congrArg Sigma.fst h
  have hc : c = c' := Fin.castAdd_inj.mp hcast
  subst hc
  have hī : castTuple (duArity_left Wf.toPoly Wg.toPoly c) ī
      = castTuple (duArity_left Wf.toPoly Wg.toPoly c) ī' :=
    eq_of_heq ((Sigma.mk.injEq ..).mp h).2
  have hiī := congrArg (castTuple (duArity_left Wf.toPoly Wg.toPoly c).symm) hī
  simp only [castTuple_castTuple] at hiī
  exact Sigma.ext rfl (heq_of_eq hiī)

theorem gAtom_injective : Function.Injective (gAtom Wf Wg) := by
  rintro ⟨c, ī⟩ ⟨c', ī'⟩ h
  have hcast : Fin.natAdd Wf.toPoly.K c = Fin.natAdd Wf.toPoly.K c' := congrArg Sigma.fst h
  have hc : c = c' := (Fin.natAdd_inj _).mp hcast
  subst hc
  have hī : castTuple (duArity_right Wf.toPoly Wg.toPoly c) ī
      = castTuple (duArity_right Wf.toPoly Wg.toPoly c) ī' :=
    eq_of_heq ((Sigma.mk.injEq ..).mp h).2
  have hiī := congrArg (castTuple (duArity_right Wf.toPoly Wg.toPoly c).symm) hī
  simp only [castTuple_castTuple] at hiī
  exact Sigma.ext rfl (heq_of_eq hiī)

/-- **Validity of the merge** (`thm:wrp-closures` (ii)): the block-index rank
coordinate separates the two sub-orders, each a strict total order. -/
theorem duPres_valid (hVf : Wf.Valid) (hVg : Wg.Valid) : (duPres Wf Wg).Valid where
  irrefl := by
    intro w x hx hbad
    rcases duAtom_cases Wf Wg x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact hVf.irrefl w a ((selectedAtom_fAtom Wf Wg w a).mp hx)
        ((wrpOrd_fAtom_fAtom Wf Wg w a a).mp hbad)
    · exact hVg.irrefl w b ((selectedAtom_gAtom Wf Wg w b).mp hx)
        ((wrpOrd_gAtom_gAtom Wf Wg w b b).mp hbad)
  trans := by
    intro w x y z hx hy hz hxy hyz
    rcases duAtom_cases Wf Wg x with ⟨a, rfl⟩ | ⟨bx, rfl⟩ <;>
      rcases duAtom_cases Wf Wg y with ⟨ay, rfl⟩ | ⟨by_, rfl⟩ <;>
        rcases duAtom_cases Wf Wg z with ⟨az, rfl⟩ | ⟨bz, rfl⟩
    -- fff
    · exact (wrpOrd_fAtom_fAtom Wf Wg w a az).mpr (hVf.trans w a ay az
        ((selectedAtom_fAtom Wf Wg w a).mp hx) ((selectedAtom_fAtom Wf Wg w ay).mp hy)
        ((selectedAtom_fAtom Wf Wg w az).mp hz)
        ((wrpOrd_fAtom_fAtom Wf Wg w a ay).mp hxy)
        ((wrpOrd_fAtom_fAtom Wf Wg w ay az).mp hyz))
    -- ffg
    · exact wrpOrd_fAtom_gAtom Wf Wg w a bz
    -- fgf: y is g, z is f — yz is gAtom→fAtom, impossible
    · exact absurd hyz (not_wrpOrd_gAtom_fAtom Wf Wg w az by_)
    -- fgg
    · exact wrpOrd_fAtom_gAtom Wf Wg w a bz
    -- gff: xy is gAtom→fAtom, impossible
    · exact absurd hxy (not_wrpOrd_gAtom_fAtom Wf Wg w ay bx)
    -- gfg: xy gAtom→fAtom impossible
    · exact absurd hxy (not_wrpOrd_gAtom_fAtom Wf Wg w ay bx)
    -- ggf: yz gAtom→fAtom impossible
    · exact absurd hyz (not_wrpOrd_gAtom_fAtom Wf Wg w az by_)
    -- ggg
    · exact (wrpOrd_gAtom_gAtom Wf Wg w bx bz).mpr (hVg.trans w bx by_ bz
        ((selectedAtom_gAtom Wf Wg w bx).mp hx) ((selectedAtom_gAtom Wf Wg w by_).mp hy)
        ((selectedAtom_gAtom Wf Wg w bz).mp hz)
        ((wrpOrd_gAtom_gAtom Wf Wg w bx by_).mp hxy)
        ((wrpOrd_gAtom_gAtom Wf Wg w by_ bz).mp hyz))
  trichot := by
    intro w x y hx hy
    rcases duAtom_cases Wf Wg x with ⟨a, rfl⟩ | ⟨bx, rfl⟩ <;>
      rcases duAtom_cases Wf Wg y with ⟨ay, rfl⟩ | ⟨by_, rfl⟩
    · rcases hVf.trichot w a ay ((selectedAtom_fAtom Wf Wg w a).mp hx)
        ((selectedAtom_fAtom Wf Wg w ay).mp hy) with h | h | h
      · exact Or.inl ((wrpOrd_fAtom_fAtom Wf Wg w a ay).mpr h)
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr ((wrpOrd_fAtom_fAtom Wf Wg w ay a).mpr h))
    · exact Or.inl (wrpOrd_fAtom_gAtom Wf Wg w a by_)
    · exact Or.inr (Or.inr (wrpOrd_fAtom_gAtom Wf Wg w ay bx))
    · rcases hVg.trichot w bx by_ ((selectedAtom_gAtom Wf Wg w bx).mp hx)
        ((selectedAtom_gAtom Wf Wg w by_).mp hy) with h | h | h
      · exact Or.inl ((wrpOrd_gAtom_gAtom Wf Wg w bx by_).mpr h)
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr ((wrpOrd_gAtom_gAtom Wf Wg w by_ bx).mpr h))

/-! ### The merged declarative output -/

/-- Given `Wf`-output `outf` (witness `lf`) and `Wg`-output `outg` (witness `lg`), the
merged presentation outputs `outf.map inl ++ outg.map inr`, with witness
`lf.map fAtom ++ lg.map gAtom`. -/
theorem duPres_isOutput_append (w : List Alpha) (outf : List Γf) (outg : List Γg)
    (hf : Wf.IsOutput w outf) (hg : Wg.IsOutput w outg) :
    (duPres Wf Wg).IsOutput w (outf.map Sum.inl ++ outg.map Sum.inr) := by
  obtain ⟨lf, ndf, memf, pwf, rfl⟩ := hf
  obtain ⟨lg, ndg, memg, pwg, rfl⟩ := hg
  refine ⟨lf.map (fAtom Wf Wg) ++ lg.map (gAtom Wf Wg), ?_, ?_, ?_, ?_⟩
  · -- Nodup
    refine List.Nodup.append (ndf.map (fAtom_injective Wf Wg))
      (ndg.map (gAtom_injective Wf Wg)) ?_
    rw [List.disjoint_left]
    intro x hx hx'
    rw [List.mem_map] at hx hx'
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, hb⟩ := hx'
    exact fAtom_ne_gAtom Wf Wg a b hb.symm
  · -- membership: exactly the selected merged atoms
    intro x
    rw [List.mem_append, List.mem_map, List.mem_map]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact (selectedAtom_fAtom Wf Wg w a).mpr ((memf a).mp ha)
      · exact (selectedAtom_gAtom Wf Wg w b).mpr ((memg b).mp hb)
    · intro hx
      rcases duAtom_cases Wf Wg x with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Or.inl ⟨a, (memf a).mpr ((selectedAtom_fAtom Wf Wg w a).mp hx), rfl⟩
      · exact Or.inr ⟨b, (memg b).mpr ((selectedAtom_gAtom Wf Wg w b).mp hx), rfl⟩
  · -- pairwise wrpOrd
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · -- within f-block
      rw [List.pairwise_map]
      exact pwf.imp fun {a a'} hh => (wrpOrd_fAtom_fAtom Wf Wg w a a').mpr hh
    · -- within g-block
      rw [List.pairwise_map]
      exact pwg.imp fun {b b'} hh => (wrpOrd_gAtom_gAtom Wf Wg w b b').mpr hh
    · -- cross-block: every f-atom precedes every g-atom
      intro x hx y hy
      rw [List.mem_map] at hx hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, rfl⟩ := hy
      exact wrpOrd_fAtom_gAtom Wf Wg w a b
  · -- label map: both blocks agree termwise
    rw [List.map_append, List.map_map, List.map_map, List.map_map, List.map_map]
    congr 1
    · apply List.map_congr_left; intro a _
      simp only [Function.comp_apply]; exact (labelOf_fAtom Wf Wg w a).symm
    · apply List.map_congr_left; intro b _
      simp only [Function.comp_apply]; exact (labelOf_gAtom Wf Wg w b).symm

/-- **`thm:wrp-closures` (ii) — disjoint union of output alphabets**
(`thm:wrp-closures`, paper.tex).  For `WRP` transductions `f, g`, the combined
transduction tagging `f`'s output `inl` and `g`'s output `inr` (and undefined where
either is) is `WRP`. -/
theorem isWRP_disjointUnion
    {f : List Alpha → Option (List Γf)} {g : List Alpha → Option (List Γg)}
    (hf : WRP.IsWRP f) (hg : WRP.IsWRP g) :
    WRP.IsWRP (fun w => match f w, g w with
      | some a, some b => some (a.map Sum.inl ++ b.map Sum.inr)
      | _, _ => none) := by
  obtain ⟨Pf, hVf, hPf⟩ := hf
  obtain ⟨Pg, hVg, hPg⟩ := hg
  refine ⟨duPres Pf Pg, duPres_valid Pf Pg hVf hVg, fun w out => ?_⟩
  show (match f w, g w with
      | some a, some b => some (a.map Sum.inl ++ b.map Sum.inr)
      | _, _ => none) = some out ↔ _
  constructor
  · intro hout
    rcases hfw : f w with _ | outf
    · rw [hfw] at hout; exact absurd hout (by simp)
    · rcases hgw : g w with _ | outg
      · rw [hfw, hgw] at hout; exact absurd hout (by simp)
      · rw [hfw, hgw] at hout
        obtain ⟨hdomf, hOf⟩ := (hPf w outf).mp hfw
        obtain ⟨hdomg, hOg⟩ := (hPg w outg).mp hgw
        refine ⟨⟨hdomf, hdomg⟩, ?_⟩
        rw [← Option.some.inj hout]
        exact duPres_isOutput_append Pf Pg w outf outg hOf hOg
  · rintro ⟨⟨hdomf, hdomg⟩, hOut⟩
    -- both domains hold, so both `f` and `g` produce outputs
    obtain ⟨outf, hOf⟩ := isWRP_some_of_domain hVf hPf hdomf
    obtain ⟨outg, hOg⟩ := isWRP_some_of_domain hVg hPg hdomg
    rw [hOf, hOg]
    -- the merged output is the unique declarative output, which is the append
    have hAppend : (duPres Pf Pg).IsOutput w (outf.map Sum.inl ++ outg.map Sum.inr) :=
      duPres_isOutput_append Pf Pg w outf outg ((hPf w outf).mp hOf).2 ((hPg w outg).mp hOg).2
    have : out = outf.map Sum.inl ++ outg.map Sum.inr :=
      isOutput_unique (duPres Pf Pg) (duPres_valid Pf Pg hVf hVg) hOut hAppend
    rw [this]

end DisjointUnion

/-! ## PRIORITY 5 — Concatenation with a fixed separator (`thm:wrp-closures` (iii))

"Form the transduction whose copies are those of `f`, a fresh ... separator copy
`s` ... labelled `#`, and those of `g`.  ... coordinate `0` is a constant block
index (`0` on `f`'s copies, `1` on `s`, `2` on `g`'s copies); ... Take `χ` from
(R2) with the blocks ordered `f < s < g`.  ... The output is `f(w) # g(w)`."
(`thm:wrp-closures`, paper.tex).

We realise the separator copy as an **arity-0** copy: always selected (its empty
position tuple is vacuously valid), labelled `sep`, at block index `1`.  This is a
faithful realisation of "emitted exactly once" that, unlike pinning to input
position `0`, is also correct on the empty input.  The output is
`f(w) ++ [sep] ++ g(w)`, and the domain is `dom(f) ∩ dom(g)`. -/

section Concat

variable {Alpha Γ : Type} (sep : Γ)
variable (Wf Wg : WRP.Presentation Alpha Γ)

/-- Copies: `Pf.K` `f`-copies, one separator copy, `Pg.K` `g`-copies. -/
@[reducible] def ccArity : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K) → ℕ :=
  Fin.addCases (Fin.addCases (fun cf => Wf.toPoly.arity cf) (fun _ => 0))
    (fun cg => Wg.toPoly.arity cg)

/-- Embed an `f`-copy index. -/
@[reducible] def ccF (cf : Fin Wf.toPoly.K) : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K) :=
  Fin.castAdd Wg.toPoly.K (Fin.castAdd 1 cf)

/-- The separator copy index. -/
@[reducible] def ccS : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K) :=
  Fin.castAdd Wg.toPoly.K (Fin.natAdd Wf.toPoly.K 0)

/-- Embed a `g`-copy index. -/
@[reducible] def ccG (cg : Fin Wg.toPoly.K) : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K) :=
  Fin.natAdd (Wf.toPoly.K + 1) cg

@[simp] theorem ccArity_F (cf : Fin Wf.toPoly.K) : ccArity Wf Wg (ccF Wf Wg cf) = Wf.toPoly.arity cf := by
  simp [ccArity, ccF]

@[simp] theorem ccArity_S : ccArity Wf Wg (ccS Wf Wg) = 0 := by simp [ccArity, ccS]

@[simp] theorem ccArity_G (cg : Fin Wg.toPoly.K) : ccArity Wf Wg (ccG Wf Wg cg) = Wg.toPoly.arity cg := by
  simp [ccArity, ccG]

/-- Selection: `f`/`g`-copies inherit; the separator copy is always selected. -/
@[reducible] def ccSel (c : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg c) → ℕ) : Prop :=
  Fin.addCases (motive := fun c => (Fin (ccArity Wf Wg c) → ℕ) → Prop)
    (Fin.addCases (motive := fun c => (Fin (ccArity Wf Wg (Fin.castAdd Wg.toPoly.K c)) → ℕ) → Prop)
      (fun cf ī => Wf.toPoly.sel cf w (castTuple (ccArity_F Wf Wg cf).symm ī))
      (fun _ _ => True))
    (fun cg ī => Wg.toPoly.sel cg w (castTuple (ccArity_G Wf Wg cg).symm ī)) c ī

/-- Label: `f`/`g`-copies inherit; the separator copy is labelled `sep`. -/
@[reducible] def ccLabel (c : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg c) → ℕ) : Γ :=
  Fin.addCases (motive := fun c => (Fin (ccArity Wf Wg c) → ℕ) → Γ)
    (Fin.addCases (motive := fun c => (Fin (ccArity Wf Wg (Fin.castAdd Wg.toPoly.K c)) → ℕ) → Γ)
      (fun cf ī => Wf.toPoly.label cf w (castTuple (ccArity_F Wf Wg cf).symm ī))
      (fun _ _ => sep))
    (fun cg ī => Wg.toPoly.label cg w (castTuple (ccArity_G Wf Wg cg).symm ī)) c ī

@[simp] theorem ccSel_F (cf : Fin Wf.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) :
    ccSel Wf Wg (ccF Wf Wg cf) w ī = Wf.toPoly.sel cf w (castTuple (ccArity_F Wf Wg cf).symm ī) := by
  simp only [ccSel, ccF, Fin.addCases_left]

@[simp] theorem ccSel_S (w : List Alpha) (ī : Fin (ccArity Wf Wg _) → ℕ) :
    ccSel Wf Wg (ccS Wf Wg) w ī = True := by
  simp only [ccSel, ccS, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem ccSel_G (cg : Fin Wg.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) :
    ccSel Wf Wg (ccG Wf Wg cg) w ī = Wg.toPoly.sel cg w (castTuple (ccArity_G Wf Wg cg).symm ī) := by
  simp only [ccSel, ccG, Fin.addCases_right]

@[simp] theorem ccLabel_F (cf : Fin Wf.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) :
    ccLabel sep Wf Wg (ccF Wf Wg cf) w ī
      = Wf.toPoly.label cf w (castTuple (ccArity_F Wf Wg cf).symm ī) := by
  simp only [ccLabel, ccF, Fin.addCases_left]

@[simp] theorem ccLabel_S (w : List Alpha) (ī : Fin (ccArity Wf Wg _) → ℕ) :
    ccLabel sep Wf Wg (ccS Wf Wg) w ī = sep := by
  simp only [ccLabel, ccS, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem ccLabel_G (cg : Fin Wg.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) :
    ccLabel sep Wf Wg (ccG Wf Wg cg) w ī
      = Wg.toPoly.label cg w (castTuple (ccArity_G Wf Wg cg).symm ī) := by
  simp only [ccLabel, ccG, Fin.addCases_right]

/-- The block index of a copy: `0` (f), `1` (separator), `2` (g). -/
def ccBlock (c : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) : ℤ :=
  Fin.addCases (Fin.addCases (fun _ => (0 : ℤ)) (fun _ => 1)) (fun _ => 2) c

@[simp] theorem ccBlock_F (cf : Fin Wf.toPoly.K) : ccBlock Wf Wg (ccF Wf Wg cf) = 0 := by
  simp [ccBlock, ccF]
@[simp] theorem ccBlock_S : ccBlock Wf Wg (ccS Wf Wg) = 1 := by simp [ccBlock, ccS]
@[simp] theorem ccBlock_G (cg : Fin Wg.toPoly.K) : ccBlock Wf Wg (ccG Wf Wg cg) = 2 := by
  simp [ccBlock, ccG]

/-- Order `χ`: within the `f`/`g` blocks inherit the sub-orders, and is `False`
everywhere else.  (Cross-block atoms differ in the block-index rank coordinate, so
the WRP order `≺` separates the blocks by rank and never consults `χ` across blocks;
hence the cross-block value of `χ` is immaterial.  We take `False`.) -/
@[reducible] def ccOrd (c c' : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg c) → ℕ) (ī' : Fin (ccArity Wf Wg c') → ℕ) : Prop :=
  Fin.addCases (motive := fun c => (Fin (ccArity Wf Wg c) → ℕ) → Prop)
    (Fin.addCases
      (motive := fun c => (Fin (ccArity Wf Wg (Fin.castAdd Wg.toPoly.K c)) → ℕ) → Prop)
      (fun cf ī =>
        Fin.addCases (motive := fun c' => (Fin (ccArity Wf Wg c') → ℕ) → Prop)
          (Fin.addCases
            (motive := fun c' => (Fin (ccArity Wf Wg (Fin.castAdd Wg.toPoly.K c')) → ℕ) → Prop)
            (fun cf' ī' => Wf.toPoly.ord cf cf' w (castTuple (ccArity_F Wf Wg cf).symm ī)
              (castTuple (ccArity_F Wf Wg cf').symm ī'))
            (fun _ _ => False))
          (fun _ _ => False) c' ī')
      (fun _ _ => False))
    (fun cg ī =>
      Fin.addCases (motive := fun c' => (Fin (ccArity Wf Wg c') → ℕ) → Prop)
        (fun _ _ => False)
        (fun cg' ī' => Wg.toPoly.ord cg cg' w (castTuple (ccArity_G Wf Wg cg).symm ī)
          (castTuple (ccArity_G Wf Wg cg').symm ī')) c' ī') c ī

@[simp] theorem ccOrd_FF (cf cf' : Fin Wf.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) (ī' : Fin (ccArity Wf Wg _) → ℕ) :
    ccOrd Wf Wg (ccF Wf Wg cf) (ccF Wf Wg cf') w ī ī'
      = Wf.toPoly.ord cf cf' w (castTuple (ccArity_F Wf Wg cf).symm ī)
          (castTuple (ccArity_F Wf Wg cf').symm ī') := by
  simp only [ccOrd, ccF, Fin.addCases_left]

@[simp] theorem ccOrd_GG (cg cg' : Fin Wg.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) (ī' : Fin (ccArity Wf Wg _) → ℕ) :
    ccOrd Wf Wg (ccG Wf Wg cg) (ccG Wf Wg cg') w ī ī'
      = Wg.toPoly.ord cg cg' w (castTuple (ccArity_G Wf Wg cg).symm ī)
          (castTuple (ccArity_G Wf Wg cg').symm ī') := by
  simp only [ccOrd, ccG, Fin.addCases_right]

@[simp] theorem ccOrd_FS (cf : Fin Wf.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) (ī' : Fin (ccArity Wf Wg _) → ℕ) :
    ccOrd Wf Wg (ccF Wf Wg cf) (ccS Wf Wg) w ī ī' = False := by
  simp only [ccOrd, ccF, ccS, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem ccOrd_FG (cf : Fin Wf.toPoly.K) (cg : Fin Wg.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) (ī' : Fin (ccArity Wf Wg _) → ℕ) :
    ccOrd Wf Wg (ccF Wf Wg cf) (ccG Wf Wg cg) w ī ī' = False := by
  simp only [ccOrd, ccF, ccG, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem ccOrd_SF (cf : Fin Wf.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) (ī' : Fin (ccArity Wf Wg _) → ℕ) :
    ccOrd Wf Wg (ccS Wf Wg) (ccF Wf Wg cf) w ī ī' = False := by
  simp only [ccOrd, ccF, ccS, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem ccOrd_SS (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) (ī' : Fin (ccArity Wf Wg _) → ℕ) :
    ccOrd Wf Wg (ccS Wf Wg) (ccS Wf Wg) w ī ī' = False := by
  simp only [ccOrd, ccS, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem ccOrd_SG (cg : Fin Wg.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) (ī' : Fin (ccArity Wf Wg _) → ℕ) :
    ccOrd Wf Wg (ccS Wf Wg) (ccG Wf Wg cg) w ī ī' = False := by
  simp only [ccOrd, ccS, ccG, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem ccOrd_GF (cg : Fin Wg.toPoly.K) (cf : Fin Wf.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) (ī' : Fin (ccArity Wf Wg _) → ℕ) :
    ccOrd Wf Wg (ccG Wf Wg cg) (ccF Wf Wg cf) w ī ī' = False := by
  simp only [ccOrd, ccG, ccF, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem ccOrd_GS (cg : Fin Wg.toPoly.K) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg _) → ℕ) (ī' : Fin (ccArity Wf Wg _) → ℕ) :
    ccOrd Wf Wg (ccG Wf Wg cg) (ccS Wf Wg) w ī ī' = False := by
  simp only [ccOrd, ccG, ccS, Fin.addCases_left, Fin.addCases_right]

/-! ### MSO obligations for the concat presentation -/

/-- A copy of the merged set is an `f`-copy, the separator, or a `g`-copy. -/
theorem ccCopy_cases (c : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) :
    (∃ cf, c = ccF Wf Wg cf) ∨ c = ccS Wf Wg ∨ (∃ cg, c = ccG Wf Wg cg) := by
  refine Fin.addCases (motive := fun c => (∃ cf, c = ccF Wf Wg cf) ∨ c = ccS Wf Wg
      ∨ (∃ cg, c = ccG Wf Wg cg)) ?_ ?_ c
  · intro cfs
    refine Fin.addCases (motive := fun cfs => (∃ cf, Fin.castAdd Wg.toPoly.K cfs = ccF Wf Wg cf)
        ∨ Fin.castAdd Wg.toPoly.K cfs = ccS Wf Wg
        ∨ (∃ cg, Fin.castAdd Wg.toPoly.K cfs = ccG Wf Wg cg)) ?_ ?_ cfs
    · intro cf; exact Or.inl ⟨cf, rfl⟩
    · intro s
      refine Or.inr (Or.inl ?_)
      rw [show s = 0 from Subsingleton.elim _ _]
  · intro cg; exact Or.inr (Or.inr ⟨cg, rfl⟩)

theorem ccSelDef (c : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) :
    MSODefinableRel (ccArity Wf Wg c) (fun w ī => ccSel Wf Wg c w ī) := by
  rcases ccCopy_cases Wf Wg c with ⟨cf, rfl⟩ | rfl | ⟨cg, rfl⟩
  · exact mso_congr (fun w ī => iff_of_eq (ccSel_F Wf Wg cf w ī).symm)
      (mso_cast (ccArity_F Wf Wg cf).symm (Wf.toPoly.selDef cf))
  · refine mso_congr (R := fun _ _ => True) (fun w ī => ?_) ⟨.tru, fun w ρ => by simp⟩
    rw [ccSel_S]
  · exact mso_congr (fun w ī => iff_of_eq (ccSel_G Wf Wg cg w ī).symm)
      (mso_cast (ccArity_G Wf Wg cg).symm (Wg.toPoly.selDef cg))

theorem ccLabelDef [DecidableEq Γ] (c : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) (g : Γ) :
    MSODefinableRel (ccArity Wf Wg c) (fun w ī => ccLabel sep Wf Wg c w ī = g) := by
  rcases ccCopy_cases Wf Wg c with ⟨cf, rfl⟩ | rfl | ⟨cg, rfl⟩
  · refine mso_congr (fun w ī => ?_) (mso_cast (ccArity_F Wf Wg cf).symm (Wf.toPoly.labelDef cf g))
    rw [ccLabel_F]
  · by_cases hsg : sep = g
    · refine mso_congr (R := fun _ _ => True) (fun w ī => ?_) ⟨.tru, fun w ρ => by simp⟩
      rw [ccLabel_S]; simp [hsg]
    · refine mso_congr (R := fun _ _ => False) (fun w ī => ?_) ⟨.neg .tru, fun w ρ => by simp⟩
      rw [ccLabel_S]; simp [hsg]
  · refine mso_congr (fun w ī => ?_) (mso_cast (ccArity_G Wf Wg cg).symm (Wg.toPoly.labelDef cg g))
    rw [ccLabel_G]

/-- The constant-`False` relation is MSO-definable at any arity. -/
theorem mso_false (k : ℕ) : MSODefinableRel k (fun (_ : List Alpha) (_ : Fin k → ℕ) => False) :=
  ⟨.neg .tru, fun w ρ => by simp⟩

theorem ccOrdDef (c c' : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) :
    MSODefinableRel (ccArity Wf Wg c + ccArity Wf Wg c')
      (fun w ij => ccOrd Wf Wg c c' w (fun t => ij (Fin.castAdd _ t))
        (fun t => ij (Fin.natAdd _ t))) := by
  rcases ccCopy_cases Wf Wg c with ⟨cf, rfl⟩ | rfl | ⟨cg, rfl⟩ <;>
    rcases ccCopy_cases Wf Wg c' with ⟨cf', rfl⟩ | rfl | ⟨cg', rfl⟩
  -- FF
  · exact mso_congr (fun w ij => iff_of_eq (ccOrd_FF Wf Wg cf cf' w _ _).symm)
      (mso_cast2 (ccArity_F Wf Wg cf).symm (ccArity_F Wf Wg cf').symm (Wf.toPoly.ordDef cf cf'))
  -- FS
  · exact mso_congr (fun w ij => iff_of_eq (ccOrd_FS Wf Wg cf w _ _).symm) (mso_false _)
  -- FG
  · exact mso_congr (fun w ij => iff_of_eq (ccOrd_FG Wf Wg cf cg' w _ _).symm) (mso_false _)
  -- SF
  · exact mso_congr (fun w ij => iff_of_eq (ccOrd_SF Wf Wg cf' w _ _).symm) (mso_false _)
  -- SS
  · exact mso_congr (fun w ij => iff_of_eq (ccOrd_SS Wf Wg w _ _).symm) (mso_false _)
  -- SG
  · exact mso_congr (fun w ij => iff_of_eq (ccOrd_SG Wf Wg cg' w _ _).symm) (mso_false _)
  -- GF
  · exact mso_congr (fun w ij => iff_of_eq (ccOrd_GF Wf Wg cg cf' w _ _).symm) (mso_false _)
  -- GS
  · exact mso_congr (fun w ij => iff_of_eq (ccOrd_GS Wf Wg cg w _ _).symm) (mso_false _)
  -- GG
  · exact mso_congr (fun w ij => iff_of_eq (ccOrd_GG Wf Wg cg cg' w _ _).symm)
      (mso_cast2 (ccArity_G Wf Wg cg).symm (ccArity_G Wf Wg cg').symm (Wg.toPoly.ordDef cg cg'))

/-! ### The concat polyregular presentation, rank, and WRP presentation -/

/-- The merged polyregular presentation for concatenation. -/
@[reducible] def ccPoly [DecidableEq Γ] : Polyreg.Presentation Alpha Γ where
  K := Wf.toPoly.K + 1 + Wg.toPoly.K
  arity := ccArity Wf Wg
  domain := fun w => Wf.toPoly.domain w ∧ Wg.toPoly.domain w
  domainDef := by
    obtain ⟨φf, hφf⟩ := Wf.toPoly.domainDef
    obtain ⟨φg, hφg⟩ := Wg.toPoly.domainDef
    exact ⟨Formula.and φf φg, fun w => by rw [Formula.sat_and, ← hφf, ← hφg]⟩
  sel := ccSel Wf Wg
  selDef := ccSelDef Wf Wg
  label := ccLabel sep Wf Wg
  labelDef := ccLabelDef sep Wf Wg
  ord := ccOrd Wf Wg
  ordDef := ccOrdDef Wf Wg

/-- The merged rank: block index `0`/`1`/`2` at coordinate `0`, then `κ_f`, `0`, or
`κ_g` embedded into the f-block resp. g-block. -/
@[reducible] def ccRank (c : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg c) → ℕ) : Fin (Wf.d + Wg.d + 1) → ℤ :=
  Fin.addCases (motive := fun c =>
      (Fin (ccArity Wf Wg c) → ℕ) → (Fin (Wf.d + Wg.d + 1) → ℤ))
    (Fin.addCases
      (motive := fun c => (Fin (ccArity Wf Wg (Fin.castAdd Wg.toPoly.K c)) → ℕ)
        → (Fin (Wf.d + Wg.d + 1) → ℤ))
      (fun cf ī => embedF Wf.d Wg.d 0 (Wf.rank cf w (castTuple (ccArity_F Wf Wg cf).symm ī)))
      (fun _ _ => embedF Wf.d Wg.d 1 (fun _ => 0)))
    (fun cg ī => embedG Wf.d Wg.d 2 (Wg.rank cg w (castTuple (ccArity_G Wf Wg cg).symm ī))) c ī

@[simp] theorem ccRank_F (cf : Fin Wf.toPoly.K) (w : List Alpha) (ī : Fin (ccArity Wf Wg _) → ℕ) :
    ccRank Wf Wg (ccF Wf Wg cf) w ī
      = embedF Wf.d Wg.d 0 (Wf.rank cf w (castTuple (ccArity_F Wf Wg cf).symm ī)) := by
  simp only [ccRank, ccF, Fin.addCases_left]

@[simp] theorem ccRank_S (w : List Alpha) (ī : Fin (ccArity Wf Wg _) → ℕ) :
    ccRank Wf Wg (ccS Wf Wg) w ī = embedF Wf.d Wg.d 1 (fun _ => 0) := by
  simp only [ccRank, ccS, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem ccRank_G (cg : Fin Wg.toPoly.K) (w : List Alpha) (ī : Fin (ccArity Wf Wg _) → ℕ) :
    ccRank Wf Wg (ccG Wf Wg cg) w ī
      = embedG Wf.d Wg.d 2 (Wg.rank cg w (castTuple (ccArity_G Wf Wg cg).symm ī)) := by
  simp only [ccRank, ccG, Fin.addCases_right]

theorem ccRankReg (c : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) : IsRegularRankTerm (ccRank Wf Wg c) := by
  rcases ccCopy_cases Wf Wg c with ⟨cf, rfl⟩ | rfl | ⟨cg, rfl⟩
  · have hreg : IsRegularRankTerm (fun w ī coord =>
        blockVec Wf.d Wg.d 0 coord + (projF Wf.d Wg.d coord).elim 0
          (Wf.rank cf w (castTuple (ccArity_F Wf Wg cf).symm ī))) :=
      isRegularRankTerm_add (isRegularRankTerm_const _)
        (isRegularRankTerm_reindex
          (isRegularRankTerm_castArg (ccArity_F Wf Wg cf).symm (Wf.rankReg cf)) (projF Wf.d Wg.d))
    refine ⟨hreg.choose, fun w ī => ?_⟩
    rw [ccRank_F]; funext coord; rw [embedF]; exact congrFun (hreg.choose_spec w ī) coord
  · -- separator: constant rank `embedF 1 0`
    refine ⟨(isRegularRankTerm_const (embedF Wf.d Wg.d 1 (fun _ => 0))).choose, fun w ī => ?_⟩
    rw [ccRank_S]
    exact (isRegularRankTerm_const (embedF Wf.d Wg.d 1 (fun _ => 0))).choose_spec w ī
  · have hreg : IsRegularRankTerm (fun w ī coord =>
        blockVec Wf.d Wg.d 2 coord + (projG Wf.d Wg.d coord).elim 0
          (Wg.rank cg w (castTuple (ccArity_G Wf Wg cg).symm ī))) :=
      isRegularRankTerm_add (isRegularRankTerm_const _)
        (isRegularRankTerm_reindex
          (isRegularRankTerm_castArg (ccArity_G Wf Wg cg).symm (Wg.rankReg cg)) (projG Wf.d Wg.d))
    refine ⟨hreg.choose, fun w ī => ?_⟩
    rw [ccRank_G]; funext coord; rw [embedG]; exact congrFun (hreg.choose_spec w ī) coord

/-- **The concat WRP presentation** (`thm:wrp-closures` (iii)). -/
@[reducible] def ccPres [DecidableEq Γ] : WRP.Presentation Alpha Γ where
  toPoly := ccPoly sep Wf Wg
  d := Wf.d + Wg.d + 1
  rank := ccRank Wf Wg
  rankReg := ccRankReg Wf Wg

/-! ### Atom maps and correspondences -/

variable [DecidableEq Γ]

/-- Inject an `f`-atom. -/
@[reducible] def ccfAtom (a : Wf.toPoly.Atom) : (ccPres sep Wf Wg).toPoly.Atom :=
  ⟨ccF Wf Wg a.1, castTuple (ccArity_F Wf Wg a.1) a.2⟩

/-- The separator atom (arity 0, empty position tuple). -/
@[reducible] def ccsAtom : (ccPres sep Wf Wg).toPoly.Atom :=
  ⟨ccS Wf Wg, castTuple (ccArity_S Wf Wg) Fin.elim0⟩

/-- Inject a `g`-atom. -/
@[reducible] def ccgAtom (b : Wg.toPoly.Atom) : (ccPres sep Wf Wg).toPoly.Atom :=
  ⟨ccG Wf Wg b.1, castTuple (ccArity_G Wf Wg b.1) b.2⟩

/-- Every merged atom is an `f`-atom, the separator, or a `g`-atom. -/
theorem ccAtom_cases (x : (ccPres sep Wf Wg).toPoly.Atom) :
    (∃ a, x = ccfAtom sep Wf Wg a) ∨ x = ccsAtom sep Wf Wg ∨ (∃ b, x = ccgAtom sep Wf Wg b) := by
  obtain ⟨c, ī⟩ := x
  rcases ccCopy_cases Wf Wg c with ⟨cf, rfl⟩ | rfl | ⟨cg, rfl⟩
  · refine Or.inl ⟨⟨cf, castTuple (ccArity_F Wf Wg cf).symm ī⟩, ?_⟩
    exact Sigma.ext rfl (heq_of_eq (funext fun t => rfl))
  · refine Or.inr (Or.inl ?_)
    refine Sigma.ext rfl (heq_of_eq (funext fun t => ?_))
    have hlt : (t : ℕ) < ccArity Wf Wg (ccS Wf Wg) := t.isLt
    rw [ccArity_S] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  · refine Or.inr (Or.inr ⟨⟨cg, castTuple (ccArity_G Wf Wg cg).symm ī⟩, ?_⟩)
    exact Sigma.ext rfl (heq_of_eq (funext fun t => rfl))

theorem ccValidAtom_fAtom (w : List Alpha) (a : Wf.toPoly.Atom) :
    (ccPres sep Wf Wg).toPoly.validAtom w (ccfAtom sep Wf Wg a) ↔ Wf.toPoly.validAtom w a := by
  constructor
  · intro hval t
    exact hval (Fin.cast (ccArity_F Wf Wg a.1).symm t)
  · intro hval t
    exact hval (Fin.cast (ccArity_F Wf Wg a.1) t)

theorem ccValidAtom_gAtom (w : List Alpha) (b : Wg.toPoly.Atom) :
    (ccPres sep Wf Wg).toPoly.validAtom w (ccgAtom sep Wf Wg b) ↔ Wg.toPoly.validAtom w b := by
  constructor
  · intro hval t
    exact hval (Fin.cast (ccArity_G Wf Wg b.1).symm t)
  · intro hval t
    exact hval (Fin.cast (ccArity_G Wf Wg b.1) t)

theorem ccSelectedAtom_fAtom (w : List Alpha) (a : Wf.toPoly.Atom) :
    (ccPres sep Wf Wg).toPoly.selectedAtom w (ccfAtom sep Wf Wg a) ↔ Wf.toPoly.selectedAtom w a := by
  rw [Polyreg.Presentation.selectedAtom, Polyreg.Presentation.selectedAtom, ccValidAtom_fAtom]
  refine and_congr Iff.rfl ?_
  show ccSel Wf Wg (ccF Wf Wg a.1) w (ccfAtom sep Wf Wg a).2 ↔ _
  rw [ccSel_F]; simp

theorem ccSelectedAtom_gAtom (w : List Alpha) (b : Wg.toPoly.Atom) :
    (ccPres sep Wf Wg).toPoly.selectedAtom w (ccgAtom sep Wf Wg b) ↔ Wg.toPoly.selectedAtom w b := by
  rw [Polyreg.Presentation.selectedAtom, Polyreg.Presentation.selectedAtom, ccValidAtom_gAtom]
  refine and_congr Iff.rfl ?_
  show ccSel Wf Wg (ccG Wf Wg b.1) w (ccgAtom sep Wf Wg b).2 ↔ _
  rw [ccSel_G]; simp

/-- The separator atom is always selected. -/
theorem ccSelectedAtom_sAtom (w : List Alpha) :
    (ccPres sep Wf Wg).toPoly.selectedAtom w (ccsAtom sep Wf Wg) := by
  refine ⟨fun t => ?_, ?_⟩
  · have hlt : (t : ℕ) < ccArity Wf Wg (ccS Wf Wg) := t.isLt
    rw [ccArity_S] at hlt; exact absurd hlt (Nat.not_lt_zero _)
  · show ccSel Wf Wg (ccS Wf Wg) w (ccsAtom sep Wf Wg).2
    rw [ccSel_S]; trivial

theorem ccLabelOf_fAtom (w : List Alpha) (a : Wf.toPoly.Atom) :
    (ccPres sep Wf Wg).toPoly.labelOf w (ccfAtom sep Wf Wg a) = Wf.toPoly.labelOf w a := by
  show ccLabel sep Wf Wg (ccF Wf Wg a.1) w (ccfAtom sep Wf Wg a).2 = _
  rw [ccLabel_F]; simp [Polyreg.Presentation.labelOf]

theorem ccLabelOf_gAtom (w : List Alpha) (b : Wg.toPoly.Atom) :
    (ccPres sep Wf Wg).toPoly.labelOf w (ccgAtom sep Wf Wg b) = Wg.toPoly.labelOf w b := by
  show ccLabel sep Wf Wg (ccG Wf Wg b.1) w (ccgAtom sep Wf Wg b).2 = _
  rw [ccLabel_G]; simp [Polyreg.Presentation.labelOf]

theorem ccLabelOf_sAtom (w : List Alpha) :
    (ccPres sep Wf Wg).toPoly.labelOf w (ccsAtom sep Wf Wg) = sep := by
  show ccLabel sep Wf Wg (ccS Wf Wg) w (ccsAtom sep Wf Wg).2 = _
  rw [ccLabel_S]

theorem ccRankOf_fAtom (w : List Alpha) (a : Wf.toPoly.Atom) :
    (ccPres sep Wf Wg).rankOf w (ccfAtom sep Wf Wg a) = embedF Wf.d Wg.d 0 (Wf.rankOf w a) := by
  show ccRank Wf Wg (ccF Wf Wg a.1) w (ccfAtom sep Wf Wg a).2 = _
  rw [ccRank_F]; simp [WRP.Presentation.rankOf]

theorem ccRankOf_gAtom (w : List Alpha) (b : Wg.toPoly.Atom) :
    (ccPres sep Wf Wg).rankOf w (ccgAtom sep Wf Wg b) = embedG Wf.d Wg.d 2 (Wg.rankOf w b) := by
  show ccRank Wf Wg (ccG Wf Wg b.1) w (ccgAtom sep Wf Wg b).2 = _
  rw [ccRank_G]; simp [WRP.Presentation.rankOf]

theorem ccRankOf_sAtom (w : List Alpha) :
    (ccPres sep Wf Wg).rankOf w (ccsAtom sep Wf Wg) = embedF Wf.d Wg.d 1 (fun _ => 0) := by
  show ccRank Wf Wg (ccS Wf Wg) w (ccsAtom sep Wf Wg).2 = _
  rw [ccRank_S]

/-! ### `wrpOrd` characterisations (block index `0 < 1 < 2` dominates) -/

/-- The block coordinate `0` of the concat rank space. -/
def ccZero : Fin (Wf.d + Wg.d + 1) := 0

theorem ccBlockVal_F (w : List Alpha) (a : Wf.toPoly.Atom) :
    (ccPres sep Wf Wg).rankOf w (ccfAtom sep Wf Wg a) (ccZero Wf Wg) = 0 := by
  rw [ccRankOf_fAtom]; exact embedF_zero _ _ _ _
theorem ccBlockVal_S (w : List Alpha) :
    (ccPres sep Wf Wg).rankOf w (ccsAtom sep Wf Wg) (ccZero Wf Wg) = 1 := by
  rw [ccRankOf_sAtom]; exact embedF_zero _ _ _ _
theorem ccBlockVal_G (w : List Alpha) (b : Wg.toPoly.Atom) :
    (ccPres sep Wf Wg).rankOf w (ccgAtom sep Wf Wg b) (ccZero Wf Wg) = 2 := by
  rw [ccRankOf_gAtom]; exact embedG_zero _ _ _ _

theorem ccAtomOrd_ff (w : List Alpha) (a a' : Wf.toPoly.Atom) :
    (ccPres sep Wf Wg).toPoly.atomOrd w (ccfAtom sep Wf Wg a) (ccfAtom sep Wf Wg a')
      ↔ Wf.toPoly.atomOrd w a a' := by
  show ccOrd Wf Wg (ccF Wf Wg a.1) (ccF Wf Wg a'.1) w (ccfAtom sep Wf Wg a).2
    (ccfAtom sep Wf Wg a').2 ↔ _
  rw [ccOrd_FF]; simp [Polyreg.Presentation.atomOrd]

theorem ccAtomOrd_gg (w : List Alpha) (b b' : Wg.toPoly.Atom) :
    (ccPres sep Wf Wg).toPoly.atomOrd w (ccgAtom sep Wf Wg b) (ccgAtom sep Wf Wg b')
      ↔ Wg.toPoly.atomOrd w b b' := by
  show ccOrd Wf Wg (ccG Wf Wg b.1) (ccG Wf Wg b'.1) w (ccgAtom sep Wf Wg b).2
    (ccgAtom sep Wf Wg b').2 ↔ _
  rw [ccOrd_GG]; simp [Polyreg.Presentation.atomOrd]

theorem ccWrpOrd_ff (w : List Alpha) (a a' : Wf.toPoly.Atom) :
    (ccPres sep Wf Wg).wrpOrd w (ccfAtom sep Wf Wg a) (ccfAtom sep Wf Wg a') ↔ Wf.wrpOrd w a a' := by
  show (WRP.lexLt _ _ ∨ (_ = _ ∧ _)) ↔ (WRP.lexLt _ _ ∨ (_ = _ ∧ _))
  rw [ccRankOf_fAtom, ccRankOf_fAtom, lexLt_embedF_iff, embedF_inj_iff, ccAtomOrd_ff]

theorem ccWrpOrd_gg (w : List Alpha) (b b' : Wg.toPoly.Atom) :
    (ccPres sep Wf Wg).wrpOrd w (ccgAtom sep Wf Wg b) (ccgAtom sep Wf Wg b') ↔ Wg.wrpOrd w b b' := by
  show (WRP.lexLt _ _ ∨ (_ = _ ∧ _)) ↔ (WRP.lexLt _ _ ∨ (_ = _ ∧ _))
  rw [ccRankOf_gAtom, ccRankOf_gAtom, lexLt_embedG_iff, embedG_inj_iff, ccAtomOrd_gg]

/-- A lower-block atom `≺`-precedes a higher-block atom (block index at coord 0). -/
theorem ccWrpOrd_block_lt (w : List Alpha) (x y : (ccPres sep Wf Wg).toPoly.Atom)
    (h : (ccPres sep Wf Wg).rankOf w x (ccZero Wf Wg) < (ccPres sep Wf Wg).rankOf w y (ccZero Wf Wg)) :
    (ccPres sep Wf Wg).wrpOrd w x y :=
  Or.inl (lexLt_of_block_lt Wf.d Wg.d _ _ h)

theorem ccNot_wrpOrd_block_lt (w : List Alpha) (x y : (ccPres sep Wf Wg).toPoly.Atom)
    (h : (ccPres sep Wf Wg).rankOf w y (ccZero Wf Wg) < (ccPres sep Wf Wg).rankOf w x (ccZero Wf Wg)) :
    ¬ (ccPres sep Wf Wg).wrpOrd w x y := by
  rw [WRP.Presentation.wrpOrd]
  rintro (hlt | ⟨heq, _⟩)
  · exact not_lexLt_of_block_lt Wf.d Wg.d _ _ h hlt
  · exact absurd (congrFun heq (ccZero Wf Wg)) (by omega)

/-! ### Validity of the concat presentation -/

/-- **Validity** (`thm:wrp-closures` (iii)): block index `0 < 1 < 2` separates the
three blocks, with `Wf`/`Wg` ordering the `f`/`g` blocks. -/
theorem ccPres_valid (hVf : Wf.Valid) (hVg : Wg.Valid) : (ccPres sep Wf Wg).Valid where
  irrefl := by
    intro w x hx hbad
    rcases ccAtom_cases sep Wf Wg x with ⟨a, rfl⟩ | rfl | ⟨b, rfl⟩
    · exact hVf.irrefl w a ((ccSelectedAtom_fAtom sep Wf Wg w a).mp hx)
        ((ccWrpOrd_ff sep Wf Wg w a a).mp hbad)
    · -- separator: equal rank, `ccOrd` separator-self is `False`
      rcases hbad with hlt | ⟨_, hord⟩
      · obtain ⟨i, _, hi⟩ := hlt; exact absurd hi (lt_irrefl _)
      · have : ccOrd Wf Wg (ccS Wf Wg) (ccS Wf Wg) w (ccsAtom sep Wf Wg).2
            (ccsAtom sep Wf Wg).2 := hord
        rw [ccOrd_SS] at this; exact this
    · exact hVg.irrefl w b ((ccSelectedAtom_gAtom sep Wf Wg w b).mp hx)
        ((ccWrpOrd_gg sep Wf Wg w b b).mp hbad)
  trans := by
    intro w x y z hx hy hz hxy hyz
    -- block values are monotone along `≺`; reduce the 27 cases via the block coordinate
    have hbx := ccAtom_cases sep Wf Wg x
    have hby := ccAtom_cases sep Wf Wg y
    have hbz := ccAtom_cases sep Wf Wg z
    -- helper: `≺` implies block x ≤ block y
    have hmono : ∀ p q : (ccPres sep Wf Wg).toPoly.Atom,
        (ccPres sep Wf Wg).wrpOrd w p q →
        (ccPres sep Wf Wg).rankOf w p (ccZero Wf Wg) ≤ (ccPres sep Wf Wg).rankOf w q (ccZero Wf Wg) := by
      intro p q hpq
      by_contra hlt
      push Not at hlt
      exact ccNot_wrpOrd_block_lt sep Wf Wg w p q hlt hpq
    rcases hbx with ⟨a, rfl⟩ | rfl | ⟨b, rfl⟩ <;>
      rcases hbz with ⟨c, rfl⟩ | rfl | ⟨d, rfl⟩
    -- x=f, z=f
    · rcases hby with ⟨ay, rfl⟩ | rfl | ⟨by_, rfl⟩
      · exact (ccWrpOrd_ff sep Wf Wg w a c).mpr (hVf.trans w a ay c
          ((ccSelectedAtom_fAtom sep Wf Wg w a).mp hx) ((ccSelectedAtom_fAtom sep Wf Wg w ay).mp hy)
          ((ccSelectedAtom_fAtom sep Wf Wg w c).mp hz)
          ((ccWrpOrd_ff sep Wf Wg w a ay).mp hxy) ((ccWrpOrd_ff sep Wf Wg w ay c).mp hyz))
      · have := hmono _ _ hyz; rw [ccBlockVal_S, ccBlockVal_F] at this; omega
      · have := hmono _ _ hyz; rw [ccBlockVal_G, ccBlockVal_F] at this; omega
    -- x=f, z=s
    · exact ccWrpOrd_block_lt sep Wf Wg w _ _ (by rw [ccBlockVal_F, ccBlockVal_S]; omega)
    -- x=f, z=g
    · exact ccWrpOrd_block_lt sep Wf Wg w _ _ (by rw [ccBlockVal_F, ccBlockVal_G]; omega)
    -- x=s, z=f
    · have := hmono _ _ hxy; have := hmono _ _ hyz
      rcases hby with ⟨ay, rfl⟩ | rfl | ⟨by_, rfl⟩ <;>
        simp only [ccBlockVal_F, ccBlockVal_S, ccBlockVal_G] at * <;> omega
    -- x=s, z=s
    · have := hmono _ _ hxy; have := hmono _ _ hyz
      rcases hby with ⟨ay, rfl⟩ | rfl | ⟨by_, rfl⟩ <;>
        simp only [ccBlockVal_F, ccBlockVal_S, ccBlockVal_G] at * <;> omega
    -- x=s, z=g
    · exact ccWrpOrd_block_lt sep Wf Wg w _ _ (by rw [ccBlockVal_S, ccBlockVal_G]; omega)
    -- x=g, z=f
    · have := hmono _ _ hxy; have := hmono _ _ hyz
      rcases hby with ⟨ay, rfl⟩ | rfl | ⟨by_, rfl⟩ <;>
        simp only [ccBlockVal_F, ccBlockVal_S, ccBlockVal_G] at * <;> omega
    -- x=g, z=s
    · have := hmono _ _ hxy; have := hmono _ _ hyz
      rcases hby with ⟨ay, rfl⟩ | rfl | ⟨by_, rfl⟩ <;>
        simp only [ccBlockVal_F, ccBlockVal_S, ccBlockVal_G] at * <;> omega
    -- x=g, z=g
    · rcases hby with ⟨ay, rfl⟩ | rfl | ⟨by_, rfl⟩
      · have := hmono _ _ hxy; rw [ccBlockVal_F, ccBlockVal_G] at this; omega
      · have := hmono _ _ hxy; rw [ccBlockVal_S, ccBlockVal_G] at this; omega
      · exact (ccWrpOrd_gg sep Wf Wg w b d).mpr (hVg.trans w b by_ d
          ((ccSelectedAtom_gAtom sep Wf Wg w b).mp hx) ((ccSelectedAtom_gAtom sep Wf Wg w by_).mp hy)
          ((ccSelectedAtom_gAtom sep Wf Wg w d).mp hz)
          ((ccWrpOrd_gg sep Wf Wg w b by_).mp hxy) ((ccWrpOrd_gg sep Wf Wg w by_ d).mp hyz))
  trichot := by
    intro w x y hx hy
    rcases ccAtom_cases sep Wf Wg x with ⟨a, rfl⟩ | rfl | ⟨b, rfl⟩ <;>
      rcases ccAtom_cases sep Wf Wg y with ⟨a', rfl⟩ | rfl | ⟨b', rfl⟩
    -- ff
    · rcases hVf.trichot w a a' ((ccSelectedAtom_fAtom sep Wf Wg w a).mp hx)
        ((ccSelectedAtom_fAtom sep Wf Wg w a').mp hy) with h | h | h
      · exact Or.inl ((ccWrpOrd_ff sep Wf Wg w a a').mpr h)
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr ((ccWrpOrd_ff sep Wf Wg w a' a).mpr h))
    -- fs
    · exact Or.inl (ccWrpOrd_block_lt sep Wf Wg w _ _ (by rw [ccBlockVal_F, ccBlockVal_S]; omega))
    -- fg
    · exact Or.inl (ccWrpOrd_block_lt sep Wf Wg w _ _ (by rw [ccBlockVal_F, ccBlockVal_G]; omega))
    -- sf
    · exact Or.inr (Or.inr (ccWrpOrd_block_lt sep Wf Wg w _ _
        (by rw [ccBlockVal_F, ccBlockVal_S]; omega)))
    -- ss
    · exact Or.inr (Or.inl rfl)
    -- sg
    · exact Or.inl (ccWrpOrd_block_lt sep Wf Wg w _ _ (by rw [ccBlockVal_S, ccBlockVal_G]; omega))
    -- gf
    · exact Or.inr (Or.inr (ccWrpOrd_block_lt sep Wf Wg w _ _
        (by rw [ccBlockVal_F, ccBlockVal_G]; omega)))
    -- gs
    · exact Or.inr (Or.inr (ccWrpOrd_block_lt sep Wf Wg w _ _
        (by rw [ccBlockVal_S, ccBlockVal_G]; omega)))
    -- gg
    · rcases hVg.trichot w b b' ((ccSelectedAtom_gAtom sep Wf Wg w b).mp hx)
        ((ccSelectedAtom_gAtom sep Wf Wg w b').mp hy) with h | h | h
      · exact Or.inl ((ccWrpOrd_gg sep Wf Wg w b b').mpr h)
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr ((ccWrpOrd_gg sep Wf Wg w b' b).mpr h))

/-! ### The merged declarative output -/

/- The copy-index value of each atom kind: `f`-copies are `< Wf.K`, the separator
is `Wf.K`, `g`-copies are `≥ Wf.K + 1`. -/
omit sep [DecidableEq Γ] in
theorem ccF_val (cf : Fin Wf.toPoly.K) : (ccF Wf Wg cf).val = cf.val := by
  simp [ccF, Fin.val_castAdd]
omit sep [DecidableEq Γ] in
theorem ccS_val : (ccS Wf Wg).val = Wf.toPoly.K := by simp [ccS, Fin.val_castAdd, Fin.val_natAdd]
omit sep [DecidableEq Γ] in
theorem ccG_val (cg : Fin Wg.toPoly.K) : (ccG Wf Wg cg).val = Wf.toPoly.K + 1 + cg.val := by
  simp [ccG, Fin.val_natAdd]

theorem ccfAtom_injective : Function.Injective (ccfAtom sep Wf Wg) := by
  rintro ⟨c, ī⟩ ⟨c', ī'⟩ h
  have hval : c.val = c'.val := by
    have := congrArg (Fin.val ∘ Sigma.fst) h
    simpa [ccfAtom, ccF_val] using this
  have hc : c = c' := Fin.ext hval
  subst hc
  have hī : castTuple (ccArity_F Wf Wg c) ī = castTuple (ccArity_F Wf Wg c) ī' :=
    eq_of_heq ((Sigma.mk.injEq ..).mp h).2
  have hiī := congrArg (castTuple (ccArity_F Wf Wg c).symm) hī
  simp only [castTuple_castTuple] at hiī
  exact Sigma.ext rfl (heq_of_eq hiī)

theorem ccgAtom_injective : Function.Injective (ccgAtom sep Wf Wg) := by
  rintro ⟨c, ī⟩ ⟨c', ī'⟩ h
  have hval : c.val = c'.val := by
    have := congrArg (Fin.val ∘ Sigma.fst) h
    simpa [ccgAtom, ccG_val] using this
  have hc : c = c' := Fin.ext hval
  subst hc
  have hī : castTuple (ccArity_G Wf Wg c) ī = castTuple (ccArity_G Wf Wg c) ī' :=
    eq_of_heq ((Sigma.mk.injEq ..).mp h).2
  have hiī := congrArg (castTuple (ccArity_G Wf Wg c).symm) hī
  simp only [castTuple_castTuple] at hiī
  exact Sigma.ext rfl (heq_of_eq hiī)

theorem ccfAtom_ne_sAtom (a : Wf.toPoly.Atom) : ccfAtom sep Wf Wg a ≠ ccsAtom sep Wf Wg := by
  intro h
  have := congrArg (Fin.val ∘ Sigma.fst) h
  simp only [Function.comp_apply, ccfAtom, ccsAtom, ccF_val, ccS_val] at this
  exact absurd a.1.isLt (by omega)

theorem ccfAtom_ne_gAtom (a : Wf.toPoly.Atom) (b : Wg.toPoly.Atom) :
    ccfAtom sep Wf Wg a ≠ ccgAtom sep Wf Wg b := by
  intro h
  have := congrArg (Fin.val ∘ Sigma.fst) h
  simp only [Function.comp_apply, ccfAtom, ccgAtom, ccF_val, ccG_val] at this
  exact absurd a.1.isLt (by omega)

theorem ccsAtom_ne_gAtom (b : Wg.toPoly.Atom) : ccsAtom sep Wf Wg ≠ ccgAtom sep Wf Wg b := by
  intro h
  have := congrArg (Fin.val ∘ Sigma.fst) h
  simp only [Function.comp_apply, ccsAtom, ccgAtom, ccS_val, ccG_val] at this
  omega

/-- Given `Wf`-output `outf` and `Wg`-output `outg`, the concat presentation outputs
`outf ++ [sep] ++ outg` (witness `lf.map ccfAtom ++ ccsAtom :: lg.map ccgAtom`). -/
theorem ccPres_isOutput_append (w : List Alpha) (outf outg : List Γ)
    (hf : Wf.IsOutput w outf) (hg : Wg.IsOutput w outg) :
    (ccPres sep Wf Wg).IsOutput w (outf ++ [sep] ++ outg) := by
  obtain ⟨lf, ndf, memf, pwf, rfl⟩ := hf
  obtain ⟨lg, ndg, memg, pwg, rfl⟩ := hg
  refine ⟨lf.map (ccfAtom sep Wf Wg) ++ ccsAtom sep Wf Wg :: lg.map (ccgAtom sep Wf Wg),
    ?_, ?_, ?_, ?_⟩
  · -- Nodup
    refine List.Nodup.append (ndf.map (ccfAtom_injective sep Wf Wg)) ?_ ?_
    · refine List.nodup_cons.mpr ⟨?_, ndg.map (ccgAtom_injective sep Wf Wg)⟩
      rw [List.mem_map]; rintro ⟨b, _, hb⟩; exact ccsAtom_ne_gAtom sep Wf Wg b hb.symm
    · rw [List.disjoint_left]
      intro x hx hx'
      rw [List.mem_map] at hx
      obtain ⟨a, _, rfl⟩ := hx
      rcases List.mem_cons.mp hx' with hs | hg'
      · exact ccfAtom_ne_sAtom sep Wf Wg a hs
      · rw [List.mem_map] at hg'; obtain ⟨b, _, hb⟩ := hg'
        exact ccfAtom_ne_gAtom sep Wf Wg a b hb.symm
  · -- membership
    intro x
    rw [List.mem_append, List.mem_cons, List.mem_map, List.mem_map]
    constructor
    · rintro (⟨a, ha, rfl⟩ | rfl | ⟨b, hb, rfl⟩)
      · exact (ccSelectedAtom_fAtom sep Wf Wg w a).mpr ((memf a).mp ha)
      · exact ccSelectedAtom_sAtom sep Wf Wg w
      · exact (ccSelectedAtom_gAtom sep Wf Wg w b).mpr ((memg b).mp hb)
    · intro hx
      rcases ccAtom_cases sep Wf Wg x with ⟨a, rfl⟩ | rfl | ⟨b, rfl⟩
      · exact Or.inl ⟨a, (memf a).mpr ((ccSelectedAtom_fAtom sep Wf Wg w a).mp hx), rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨b, (memg b).mpr ((ccSelectedAtom_gAtom sep Wf Wg w b).mp hx), rfl⟩)
  · -- pairwise
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact pwf.imp fun {a a'} hh => (ccWrpOrd_ff sep Wf Wg w a a').mpr hh
    · -- separator :: g-block
      rw [List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [List.mem_map] at hy; obtain ⟨b, _, rfl⟩ := hy
        exact ccWrpOrd_block_lt sep Wf Wg w _ _ (by rw [ccBlockVal_S, ccBlockVal_G]; omega)
      · rw [List.pairwise_map]
        exact pwg.imp fun {b b'} hh => (ccWrpOrd_gg sep Wf Wg w b b').mpr hh
    · -- f-block before separator and g-block
      intro x hx y hy
      rw [List.mem_map] at hx; obtain ⟨a, _, rfl⟩ := hx
      rcases List.mem_cons.mp hy with rfl | hg'
      · exact ccWrpOrd_block_lt sep Wf Wg w _ _ (by rw [ccBlockVal_F, ccBlockVal_S]; omega)
      · rw [List.mem_map] at hg'; obtain ⟨b, _, rfl⟩ := hg'
        exact ccWrpOrd_block_lt sep Wf Wg w _ _ (by rw [ccBlockVal_F, ccBlockVal_G]; omega)
  · -- label map: `outf ++ [sep] ++ outg`
    rw [List.map_append, List.map_cons, List.map_map, List.append_assoc]
    have hf' : lf.map (Wf.toPoly.labelOf w)
        = (lf.map (ccfAtom sep Wf Wg)).map ((ccPres sep Wf Wg).toPoly.labelOf w) := by
      rw [List.map_map]
      exact (List.map_congr_left fun a _ => (ccLabelOf_fAtom sep Wf Wg w a).symm)
    have hg' : lg.map (Wg.toPoly.labelOf w)
        = (lg.map (ccgAtom sep Wf Wg)).map ((ccPres sep Wf Wg).toPoly.labelOf w) := by
      rw [List.map_map]
      exact (List.map_congr_left fun b _ => (ccLabelOf_gAtom sep Wf Wg w b).symm)
    rw [hf', hg', ccLabelOf_sAtom, List.map_map, List.map_map, List.cons_append, List.nil_append]

/-- **`thm:wrp-closures` (iii) — concatenation with a fixed separator**
(`thm:wrp-closures`, paper.tex).  For `WRP` transductions `f, g` (common output alphabet
`Γ`, separator `sep : Γ`), the transduction `w ↦ f(w) ++ [sep] ++ g(w)` (undefined
where either is) is `WRP`. -/
theorem isWRP_concat
    {f g : List Alpha → Option (List Γ)} (hf : WRP.IsWRP f) (hg : WRP.IsWRP g) :
    WRP.IsWRP (fun w => match f w, g w with
      | some a, some b => some (a ++ [sep] ++ b)
      | _, _ => none) := by
  obtain ⟨Pf, hVf, hPf⟩ := hf
  obtain ⟨Pg, hVg, hPg⟩ := hg
  refine ⟨ccPres sep Pf Pg, ccPres_valid sep Pf Pg hVf hVg, fun w out => ?_⟩
  show (match f w, g w with
      | some a, some b => some (a ++ [sep] ++ b)
      | _, _ => none) = some out ↔ _
  constructor
  · intro hout
    rcases hfw : f w with _ | outf
    · rw [hfw] at hout; exact absurd hout (by simp)
    · rcases hgw : g w with _ | outg
      · rw [hfw, hgw] at hout; exact absurd hout (by simp)
      · rw [hfw, hgw] at hout
        obtain ⟨hdomf, hOf⟩ := (hPf w outf).mp hfw
        obtain ⟨hdomg, hOg⟩ := (hPg w outg).mp hgw
        refine ⟨⟨hdomf, hdomg⟩, ?_⟩
        rw [← Option.some.inj hout]
        exact ccPres_isOutput_append sep Pf Pg w outf outg hOf hOg
  · rintro ⟨⟨hdomf, hdomg⟩, hOut⟩
    obtain ⟨outf, hOf⟩ := isWRP_some_of_domain hVf hPf hdomf
    obtain ⟨outg, hOg⟩ := isWRP_some_of_domain hVg hPg hdomg
    rw [hOf, hOg]
    have hAppend : (ccPres sep Pf Pg).IsOutput w (outf ++ [sep] ++ outg) :=
      ccPres_isOutput_append sep Pf Pg w outf outg ((hPf w outf).mp hOf).2 ((hPg w outg).mp hOg).2
    have : out = outf ++ [sep] ++ outg :=
      isOutput_unique (ccPres sep Pf Pg) (ccPres_valid sep Pf Pg hVf hVg) hOut hAppend
    rw [this]

end Concat

end WRPClosures
