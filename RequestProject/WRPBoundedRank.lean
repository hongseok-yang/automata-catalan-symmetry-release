/-
# Bounded ranks collapse `WRP` to `polyreg` (paper §4 minimality)

Formalisation of the bounded-rank boundary of `sec:wrp` ("Two boundaries of
the rank-sort layer") of "A Computational Obstruction to Swapping Area and Dinv"
by Baek, Hwang, La, and Yang:

* `WRPBoundedRank.collapse_of_rank_mso` — the **structural core**
  (`thm:bounded-rank-collapse`, paper.tex, the "(R2)" step):
  *if* the rank values of a WRP presentation are MSO-definable (and confined to a
  finite value set per copy), then the transduction it realises is ordinary
  polyregular.  This piece is **axiom-free**: it only rebuilds the polyregular
  presentation whose tie order is the rank-lex-then-`χ` combination `≺`, and
  shows it is MSO-definable as a finite disjunction of the rank-value formulas.
  Trust base `[propext, Classical.choice, Quot.sound]`.

* `WRPBoundedRank.bounded_rank_collapse` — the full
  `thm:bounded-rank-collapse`: a `WRP` transduction whose explicit rank terms
  have all their sources uniformly **bounded** on the domain is ordinary
  polyregular.  This piece supplies the `hmso` hypothesis of the core via the
  converse-Büchi theorem `SliceMSO.detAuto_state_mso` (a proved theorem,
  so this result is axiom-clean): an augmented automaton (the
  rank source's control state product the running ℤ^d total clamped to the cube
  `{-B,…,B}^d`, with a dead overflow state) carries the prefix rank in its state,
  so each bounded rank value is MSO-definable.

* `WRPBoundedRank.rank_necessary` — Corollary `cor:rank-necessary`
  (`cor:rank-necessary`, paper.tex): the zeta map has no bounded-rank `WRP` presentation
  realising it on the Dyck domain; combining with
  `ZetaNotPolyreg.zetaMap_not_polyregular` would otherwise contradict
  non-polyregularity.

The height source of `thm:zeta-wrp` (`ZetaWRP.zetaPres`) has rank equal to the
path height, which on `D_n` ranges up to `n` and so is genuinely unbounded — the
concrete content of the corollary.
-/
import RequestProject.WRP
import RequestProject.SliceMSO
import RequestProject.SliceFasGates
import RequestProject.SliceRankRegions
import RequestProject.ZetaWRP
import RequestProject.ZetaNotPolyreg

open MSO

namespace WRPBoundedRank

/-! ## Piece (A) — the structural core (axiom-free)

We rebuild the polyregular presentation `P.toPoly` but with its tie order `χ`
replaced by the WRP output order `≺` (rank-lex first, `χ`-ties).  The crux is
that `≺` is again MSO-definable **provided** each per-copy rank value relation
`rank c · = v` is MSO-definable and ranks live in a finite per-copy value set.
-/

variable {Alpha Gamma : Type}

/-- Cylindrify a per-copy rank-value formula on the **left** block of the
combined `arity c + arity c'` free variables: the left `arity c` variables become
`Fin.castAdd` indices, the right ones are ignored. -/
private theorem rankEq_left_mso {P : WRP.Presentation Alpha Gamma}
    (c c' : Fin P.toPoly.K) (v : Fin P.d → ℤ)
    (hmso : MSO.MSODefinableRel (P.toPoly.arity c) (fun w ī => P.rank c w ī = v)) :
    ∃ φ : Formula Alpha (P.toPoly.arity c + P.toPoly.arity c') 0,
      ∀ w (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ),
        (P.rank c w (fun t => ij (Fin.castAdd _ t)) = v) ↔ φ.Sat w ij Fin.elim0 := by
  obtain ⟨φ, hφ⟩ := hmso
  refine ⟨SliceFasGates.relabelFO (Fin.castAdd (P.toPoly.arity c')) φ, fun w ij => ?_⟩
  rw [SliceFasGates.sat_relabelFO]
  exact hφ w (fun t => ij (Fin.castAdd _ t))

/-- Cylindrify a per-copy rank-value formula on the **right** block of the
combined `arity c + arity c'` free variables: the right `arity c'` variables
become `Fin.natAdd` indices, the left ones are ignored. -/
private theorem rankEq_right_mso {P : WRP.Presentation Alpha Gamma}
    (c c' : Fin P.toPoly.K) (v : Fin P.d → ℤ)
    (hmso : MSO.MSODefinableRel (P.toPoly.arity c') (fun w ī => P.rank c' w ī = v)) :
    ∃ φ : Formula Alpha (P.toPoly.arity c + P.toPoly.arity c') 0,
      ∀ w (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ),
        (P.rank c' w (fun t => ij (Fin.natAdd _ t)) = v) ↔ φ.Sat w ij Fin.elim0 := by
  obtain ⟨φ, hφ⟩ := hmso
  refine ⟨SliceFasGates.relabelFO (Fin.natAdd (P.toPoly.arity c)) φ, fun w ij => ?_⟩
  rw [SliceFasGates.sat_relabelFO]
  exact hφ w (fun t => ij (Fin.natAdd _ t))

/-- Fold a list of formulas into a single disjunction. -/
private def listOr {nf : ℕ} (g : List (Formula Alpha nf 0)) : Formula Alpha nf 0 :=
  g.foldr Formula.or (Formula.neg Formula.tru)

private theorem sat_listOr {nf : ℕ} (w : List Alpha) (ρ : Fin nf → ℕ)
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

/-- Fold a `Finset` of formulas into a single disjunction. -/
private noncomputable def finsetOr {ι : Type*} {nf : ℕ} (s : Finset ι)
    (g : ι → Formula Alpha nf 0) : Formula Alpha nf 0 :=
  listOr (s.toList.map g)

private theorem sat_finsetOr {ι : Type*} {nf : ℕ} (w : List Alpha)
    (ρ : Fin nf → ℕ) (s : Finset ι) (g : ι → Formula Alpha nf 0) :
    (finsetOr s g).Sat w ρ Fin.elim0 ↔ ∃ x ∈ s, (g x).Sat w ρ Fin.elim0 := by
  unfold finsetOr
  rw [sat_listOr]
  constructor
  · rintro ⟨φ, hφ, hsat⟩
    rw [List.mem_map] at hφ
    obtain ⟨x, hx, rfl⟩ := hφ
    exact ⟨x, Finset.mem_toList.mp hx, hsat⟩
  · rintro ⟨x, hx, hsat⟩
    exact ⟨g x, List.mem_map.mpr ⟨x, Finset.mem_toList.mpr hx, rfl⟩, hsat⟩

/-- `MSODefinableRel` transfers along a pointwise iff. -/
private theorem mso_congr {k : ℕ} {R S : List Alpha → (Fin k → ℕ) → Prop}
    (h : ∀ w ī, R w ī ↔ S w ī) (hR : MSO.MSODefinableRel k R) :
    MSO.MSODefinableRel k S := by
  obtain ⟨φ, hφ⟩ := hR
  exact ⟨φ, fun w ī => (h w ī).symm.trans (hφ w ī)⟩

/-- Conjunction of two `MSODefinableRel`s at the same arity. -/
private theorem mso_and {k : ℕ} {R S : List Alpha → (Fin k → ℕ) → Prop}
    (hR : MSO.MSODefinableRel k R) (hS : MSO.MSODefinableRel k S) :
    MSO.MSODefinableRel k (fun w ī => R w ī ∧ S w ī) := by
  obtain ⟨φ, hφ⟩ := hR
  obtain ⟨ψ, hψ⟩ := hS
  exact ⟨Formula.and φ ψ, fun w ρ => by rw [Formula.sat_and, ← hφ, ← hψ]⟩

/-- Disjunction over a `Finset` of an `MSODefinableRel`-family at fixed arity. -/
private theorem mso_finsetOr {ι : Type*} {k : ℕ} (s : Finset ι)
    {R : ι → List Alpha → (Fin k → ℕ) → Prop}
    (hR : ∀ x ∈ s, MSO.MSODefinableRel k (R x)) :
    MSO.MSODefinableRel k (fun w ī => ∃ x ∈ s, R x w ī) := by
  classical
  -- pick a formula for each attached element
  have hR' : ∀ x : s, MSO.MSODefinableRel k (R x.1) := fun x => hR x.1 x.2
  choose φ hφ using hR'
  refine ⟨finsetOr s.attach (fun x => φ x), fun w ρ => ?_⟩
  rw [sat_finsetOr]
  constructor
  · rintro ⟨x, hx, hRx⟩
    exact ⟨⟨x, hx⟩, Finset.mem_attach _ _, (hφ ⟨x, hx⟩ w ρ).mp hRx⟩
  · rintro ⟨x, _, hsat⟩
    exact ⟨x.1, x.2, (hφ x w ρ).mpr hsat⟩

/-- The MSO-definability of `lexLt (rank c ī) (rank c' ī')`, as a finite
disjunction over value pairs `(v, v')` of the per-copy value sets with
`WRP.lexLt v v'`, each conjunct being the cylindrified rank-value formulas. -/
private theorem lexLt_rank_mso {P : WRP.Presentation Alpha Gamma}
    (V : ∀ _c, Finset (Fin P.d → ℤ))
    (hmso : ∀ c (v : Fin P.d → ℤ),
      MSO.MSODefinableRel (P.toPoly.arity c) (fun w ī => P.rank c w ī = v))
    (c c' : Fin P.toPoly.K) (hmemc : ∀ w ī, P.rank c w ī ∈ V c)
    (hmemc' : ∀ w ī, P.rank c' w ī ∈ V c') :
    ∃ φ : Formula Alpha (P.toPoly.arity c + P.toPoly.arity c') 0,
      ∀ w (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ),
        WRP.lexLt (P.rank c w (fun t => ij (Fin.castAdd _ t)))
            (P.rank c' w (fun t => ij (Fin.natAdd _ t)))
          ↔ φ.Sat w ij Fin.elim0 := by
  classical
  -- the set of admissible value pairs with `lexLt`
  set pairs : Finset ((Fin P.d → ℤ) × (Fin P.d → ℤ)) :=
    ((V c) ×ˢ (V c')).filter (fun p => WRP.lexLt p.1 p.2) with hpairs
  -- per-pair conjunction
  have hconj : ∀ p : (Fin P.d → ℤ) × (Fin P.d → ℤ),
      ∃ ψ : Formula Alpha (P.toPoly.arity c + P.toPoly.arity c') 0,
        ∀ w ij, (P.rank c w (fun t => ij (Fin.castAdd _ t)) = p.1
            ∧ P.rank c' w (fun t => ij (Fin.natAdd _ t)) = p.2) ↔ ψ.Sat w ij Fin.elim0 := by
    intro p
    obtain ⟨φl, hφl⟩ := rankEq_left_mso c c' p.1 (hmso c p.1)
    obtain ⟨φr, hφr⟩ := rankEq_right_mso c c' p.2 (hmso c' p.2)
    exact ⟨Formula.and φl φr, fun w ij => by
      rw [Formula.sat_and, ← hφl, ← hφr]⟩
  choose ψ hψ using hconj
  refine ⟨finsetOr pairs ψ, fun w ij => ?_⟩
  rw [sat_finsetOr]
  constructor
  · intro hlex
    refine ⟨(P.rank c w (fun t => ij (Fin.castAdd _ t)),
             P.rank c' w (fun t => ij (Fin.natAdd _ t))), ?_,
            (hψ _ w ij).mp ⟨rfl, rfl⟩⟩
    rw [hpairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hmemc w _, hmemc' w _⟩, hlex⟩
  · rintro ⟨p, hp, hsat⟩
    rw [hpairs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨_, hlex⟩ := hp
    obtain ⟨h1, h2⟩ := (hψ p w ij).mpr hsat
    rw [h1, h2]; exact hlex

/-- The MSO-definability of `rank c ī = rank c' ī'`, as a finite disjunction over
the common value set of both copies. -/
private theorem rankEq_rank_mso {P : WRP.Presentation Alpha Gamma}
    (V : ∀ _c, Finset (Fin P.d → ℤ))
    (hmso : ∀ c (v : Fin P.d → ℤ),
      MSO.MSODefinableRel (P.toPoly.arity c) (fun w ī => P.rank c w ī = v))
    (c c' : Fin P.toPoly.K) (hmemc : ∀ w ī, P.rank c w ī ∈ V c) :
    ∃ φ : Formula Alpha (P.toPoly.arity c + P.toPoly.arity c') 0,
      ∀ w (ij : Fin (P.toPoly.arity c + P.toPoly.arity c') → ℕ),
        (P.rank c w (fun t => ij (Fin.castAdd _ t))
            = P.rank c' w (fun t => ij (Fin.natAdd _ t)))
          ↔ φ.Sat w ij Fin.elim0 := by
  classical
  have hconj : ∀ v : Fin P.d → ℤ,
      ∃ ψ : Formula Alpha (P.toPoly.arity c + P.toPoly.arity c') 0,
        ∀ w ij, (P.rank c w (fun t => ij (Fin.castAdd _ t)) = v
            ∧ P.rank c' w (fun t => ij (Fin.natAdd _ t)) = v) ↔ ψ.Sat w ij Fin.elim0 := by
    intro v
    obtain ⟨φl, hφl⟩ := rankEq_left_mso c c' v (hmso c v)
    obtain ⟨φr, hφr⟩ := rankEq_right_mso c c' v (hmso c' v)
    exact ⟨Formula.and φl φr, fun w ij => by rw [Formula.sat_and, ← hφl, ← hφr]⟩
  choose ψ hψ using hconj
  refine ⟨finsetOr (V c) ψ, fun w ij => ?_⟩
  rw [sat_finsetOr]
  constructor
  · intro heq
    refine ⟨P.rank c w (fun t => ij (Fin.castAdd _ t)), hmemc w _,
            (hψ _ w ij).mp ⟨rfl, heq.symm⟩⟩
  · rintro ⟨v, _, hsat⟩
    obtain ⟨h1, h2⟩ := (hψ v w ij).mpr hsat
    rw [h1, h2]

/-- **The crux MSO-definability for `ord'`.**  The WRP output order `≺`, viewed as
a binary relation between copies `c` and `c'`, is MSO-definable in the combined
`arity c + arity c'` free variables: rank-lex (a finite disjunction over
value pairs) or rank-tie-then-`χ` (a finite disjunction over the common value set,
conjoined with the MSO-definable `χ`). -/
private theorem wrpOrd_mso {P : WRP.Presentation Alpha Gamma}
    (V : ∀ _c, Finset (Fin P.d → ℤ))
    (hmem : ∀ c w ī, P.rank c w ī ∈ V c)
    (hmso : ∀ c (v : Fin P.d → ℤ),
      MSO.MSODefinableRel (P.toPoly.arity c) (fun w ī => P.rank c w ī = v))
    (c c' : Fin P.toPoly.K) :
    MSO.MSODefinableRel (P.toPoly.arity c + P.toPoly.arity c')
      (fun w ij =>
        WRP.lexLt (P.rank c w (fun t => ij (Fin.castAdd _ t)))
            (P.rank c' w (fun t => ij (Fin.natAdd _ t)))
          ∨ (P.rank c w (fun t => ij (Fin.castAdd _ t))
              = P.rank c' w (fun t => ij (Fin.natAdd _ t))
            ∧ P.toPoly.ord c c' w (fun t => ij (Fin.castAdd _ t))
                (fun t => ij (Fin.natAdd _ t)))) := by
  obtain ⟨φlex, hφlex⟩ :=
    lexLt_rank_mso V hmso c c' (hmem c) (hmem c')
  obtain ⟨φeq, hφeq⟩ := rankEq_rank_mso V hmso c c' (hmem c)
  obtain ⟨φord, hφord⟩ := P.toPoly.ordDef c c'
  refine ⟨Formula.or φlex (Formula.and φeq φord), fun w ij => ?_⟩
  rw [Formula.sat_or, Formula.sat_and, ← hφlex, ← hφeq, ← hφord]

/-- **Replacing the tie order by `≺`.**  The polyregular presentation `P.toPoly`
with its ordering relation `ord` replaced by the relational form of `P.wrpOrd`
(rank-lex then `χ`).  All other fields (copies, arities, domain, selection,
labels) are unchanged; the new `ordDef` is `wrpOrd_mso`. -/
private def collapsedPoly (P : WRP.Presentation Alpha Gamma)
    (V : ∀ _c, Finset (Fin P.d → ℤ))
    (hmem : ∀ c w ī, P.rank c w ī ∈ V c)
    (hmso : ∀ c (v : Fin P.d → ℤ),
      MSO.MSODefinableRel (P.toPoly.arity c) (fun w ī => P.rank c w ī = v)) :
    Polyreg.Presentation Alpha Gamma where
  K := P.toPoly.K
  arity := P.toPoly.arity
  domain := P.toPoly.domain
  domainDef := P.toPoly.domainDef
  sel := P.toPoly.sel
  selDef := P.toPoly.selDef
  label := P.toPoly.label
  labelDef := P.toPoly.labelDef
  ord := fun c c' w ī ī' =>
    WRP.lexLt (P.rank c w ī) (P.rank c' w ī') ∨
      (P.rank c w ī = P.rank c' w ī' ∧ P.toPoly.ord c c' w ī ī')
  ordDef := fun c c' => wrpOrd_mso V hmem hmso c c'

/-- The collapsed presentation is `Valid` — this is exactly `P.Valid`, since its
`atomOrd` *is* `P.wrpOrd`. -/
private theorem collapsedPoly_valid (P : WRP.Presentation Alpha Gamma) (hV : P.Valid)
    (V : ∀ _c, Finset (Fin P.d → ℤ)) (hmem) (hmso) :
    (collapsedPoly P V hmem hmso).Valid where
  irrefl := fun w a ha => hV.irrefl w a ha
  trans := fun w a b c ha hb hc hab hbc => hV.trans w a b c ha hb hc hab hbc
  trichot := fun w a b ha hb => hV.trichot w a b ha hb

/-- **Piece (A): structural core (`thm:bounded-rank-collapse`, the (R2) step,
paper.tex), axiom-free.**  If, for a valid WRP presentation `P`,
the rank of each copy lands in a finite value set `V c` and each rank-value
relation `rank c · = v` is MSO-definable, then any transduction `T` realised by
`P` is ordinary polyregular. -/
theorem collapse_of_rank_mso
    {Alpha Gamma : Type} {P : WRP.Presentation Alpha Gamma} (hV : P.Valid)
    (V : ∀ _c, Finset (Fin P.d → ℤ))
    (hmem : ∀ c w ī, P.rank c w ī ∈ V c)
    (hmso : ∀ c (v : Fin P.d → ℤ), MSO.MSODefinableRel (P.toPoly.arity c)
              (fun w ī => P.rank c w ī = v))
    {T : List Alpha → Option (List Gamma)}
    (hreal : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)) :
    Polyreg.IsPolyregular T := by
  refine ⟨collapsedPoly P V hmem hmso, collapsedPoly_valid P hV V hmem hmso, fun w out => ?_⟩
  rw [hreal w out]
  -- domain and output match definitionally
  exact Iff.rfl

/-! ## Generic surrogate-rank core (for Piece (C))

Piece (A) sorts by the *true* `P.rank`, whose value relation is MSO-definable only
under the bridge's boundedness hypothesis.  Off the domain the true rank may be
unbounded, so the bridge produces a **surrogate** rank `r` (the augmented
automaton's clamped value) that is MSO-definable *everywhere*, finite-valued, and
**equal to the true rank on domain words**.  This section collapses a presentation
sorting by such a surrogate, requiring only that `r` agree with the true rank on
the selected atoms of domain words (so the declarative outputs coincide there). -/

/-- Strict lexicographic order on `Fin D → ℤ` is irreflexive. -/
private theorem lexLt_irrefl {D : ℕ} (x : Fin D → ℤ) : ¬ WRP.lexLt x x := by
  rintro ⟨i, _, hi⟩; exact lt_irrefl _ hi

/-- Strict lexicographic order on `Fin D → ℤ` is transitive. -/
private theorem lexLt_trans {D : ℕ} {x y z : Fin D → ℤ}
    (hxy : WRP.lexLt x y) (hyz : WRP.lexLt y z) : WRP.lexLt x z := by
  obtain ⟨i, hi, hi'⟩ := hxy
  obtain ⟨j, hj, hj'⟩ := hyz
  rcases lt_trichotomy i j with h | h | h
  · refine ⟨i, fun k hk => ?_, ?_⟩
    · rw [hi k hk, hj k (hk.trans h)]
    · rw [← hj i h]; exact hi'
  · subst h
    exact ⟨i, fun k hk => (hi k hk).trans (hj k hk), hi'.trans hj'⟩
  · refine ⟨j, fun k hk => ?_, ?_⟩
    · rw [hi k (hk.trans h), hj k hk]
    · rw [hi j h]; exact hj'

/-- Lexicographic comparison on `Fin D → ℤ` is trichotomous. -/
private theorem lexLt_trichot {D : ℕ} (x y : Fin D → ℤ) :
    WRP.lexLt x y ∨ x = y ∨ WRP.lexLt y x := by
  classical
  by_cases hxy : x = y
  · exact Or.inr (Or.inl hxy)
  · -- the least index where `x` and `y` differ
    have hex : ∃ i : Fin D, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    let S : Finset (Fin D) := Finset.univ.filter (fun i => x i ≠ y i)
    have hSne : S.Nonempty := by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, by simp [S, hi]⟩
    let i0 := S.min' hSne
    have hi0mem : i0 ∈ S := S.min'_mem hSne
    have hi0ne : x i0 ≠ y i0 := by
      have := hi0mem; simp only [S, Finset.mem_filter] at this; exact this.2
    have hbelow : ∀ k : Fin D, k < i0 → x k = y k := by
      intro k hk
      by_contra hne
      have hkmem : k ∈ S := by simp [S, hne]
      exact absurd (S.min'_le k hkmem) (not_le.mpr hk)
    rcases lt_or_gt_of_ne hi0ne with h | h
    · exact Or.inl ⟨i0, hbelow, h⟩
    · exact Or.inr (Or.inr ⟨i0, fun k hk => (hbelow k hk).symm, h⟩)

/-- The lexicographic combination of a `lexLt`-rank order with a base strict total
order `χ` is itself a strict total order on a set `S` of atoms, **provided** `χ`
is a strict total order on `S`. -/
private structure OrdValid {β : Type*} (S : β → Prop) (R : β → β → Prop) : Prop where
  irrefl : ∀ a, S a → ¬ R a a
  trans : ∀ a b c, S a → S b → S c → R a b → R b c → R a c
  trichot : ∀ a b, S a → S b → R a b ∨ a = b ∨ R b a

/-- The lex-combine `lexLt (r a) (r b) ∨ (r a = r b ∧ χ a b)` is a strict total
order on `S` whenever `χ` is. -/
private theorem lexCombine_ordValid {β : Type*} {D : ℕ} (S : β → Prop)
    (r : β → (Fin D → ℤ)) (χ : β → β → Prop)
    (hχ : OrdValid S χ) :
    OrdValid S (fun a b => WRP.lexLt (r a) (r b) ∨ (r a = r b ∧ χ a b)) where
  irrefl := fun a ha => by
    rintro (h | ⟨_, h⟩)
    · exact lexLt_irrefl _ h
    · exact hχ.irrefl a ha h
  trans := fun a b c ha hb hc hab hbc => by
    rcases hab with hab | ⟨hab1, hab2⟩
    · rcases hbc with hbc | ⟨hbc1, _⟩
      · exact Or.inl (lexLt_trans hab hbc)
      · rw [hbc1] at hab; exact Or.inl hab
    · rcases hbc with hbc | ⟨hbc1, hbc2⟩
      · rw [← hab1] at hbc; exact Or.inl hbc
      · exact Or.inr ⟨hab1.trans hbc1, hχ.trans a b c ha hb hc hab2 hbc2⟩
  trichot := fun a b ha hb => by
    rcases lexLt_trichot (r a) (r b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases hχ.trichot a b ha hb with hc | hc | hc
      · exact Or.inl (Or.inr ⟨h, hc⟩)
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, hc⟩))
    · exact Or.inr (Or.inr (Or.inl h))

/-- Generic cylindrification (left) for an arbitrary surrogate rank `r`. -/
private theorem rEq_left_mso {Alpha Gamma : Type} {Pp : Polyreg.Presentation Alpha Gamma} {D : ℕ}
    (r : (c : Fin Pp.K) → List Alpha → (Fin (Pp.arity c) → ℕ) → (Fin D → ℤ))
    (c c' : Fin Pp.K) (v : Fin D → ℤ)
    (hmso : MSO.MSODefinableRel (Pp.arity c) (fun w ī => r c w ī = v)) :
    ∃ φ : Formula Alpha (Pp.arity c + Pp.arity c') 0,
      ∀ w (ij : Fin (Pp.arity c + Pp.arity c') → ℕ),
        (r c w (fun t => ij (Fin.castAdd _ t)) = v) ↔ φ.Sat w ij Fin.elim0 := by
  obtain ⟨φ, hφ⟩ := hmso
  refine ⟨SliceFasGates.relabelFO (Fin.castAdd (Pp.arity c')) φ, fun w ij => ?_⟩
  rw [SliceFasGates.sat_relabelFO]; exact hφ w (fun t => ij (Fin.castAdd _ t))

/-- Generic cylindrification (right) for an arbitrary surrogate rank `r`. -/
private theorem rEq_right_mso {Alpha Gamma : Type} {Pp : Polyreg.Presentation Alpha Gamma} {D : ℕ}
    (r : (c : Fin Pp.K) → List Alpha → (Fin (Pp.arity c) → ℕ) → (Fin D → ℤ))
    (c c' : Fin Pp.K) (v : Fin D → ℤ)
    (hmso : MSO.MSODefinableRel (Pp.arity c') (fun w ī => r c' w ī = v)) :
    ∃ φ : Formula Alpha (Pp.arity c + Pp.arity c') 0,
      ∀ w (ij : Fin (Pp.arity c + Pp.arity c') → ℕ),
        (r c' w (fun t => ij (Fin.natAdd _ t)) = v) ↔ φ.Sat w ij Fin.elim0 := by
  obtain ⟨φ, hφ⟩ := hmso
  refine ⟨SliceFasGates.relabelFO (Fin.natAdd (Pp.arity c)) φ, fun w ij => ?_⟩
  rw [SliceFasGates.sat_relabelFO]; exact hφ w (fun t => ij (Fin.natAdd _ t))

/-- **Generic `ord'` MSO-definability** for an arbitrary surrogate rank `r` that is
finite-valued (`hmem` into `V`) with MSO-definable value relations (`hmso`).  This
is the `wrpOrd_mso` crux at the level of a bare polyregular presentation `Pp` and
dimension `D`, supplying the `hordDef` field of `surrPoly`. -/
private theorem ordCombine_mso {Alpha Gamma : Type} {Pp : Polyreg.Presentation Alpha Gamma} {D : ℕ}
    (r : (c : Fin Pp.K) → List Alpha → (Fin (Pp.arity c) → ℕ) → (Fin D → ℤ))
    (V : ∀ _c, Finset (Fin D → ℤ))
    (hmem : ∀ c w ī, r c w ī ∈ V c)
    (hmso : ∀ c (v : Fin D → ℤ), MSO.MSODefinableRel (Pp.arity c) (fun w ī => r c w ī = v))
    (c c' : Fin Pp.K) :
    MSO.MSODefinableRel (Pp.arity c + Pp.arity c')
      (fun w ij =>
        WRP.lexLt (r c w (fun t => ij (Fin.castAdd _ t))) (r c' w (fun t => ij (Fin.natAdd _ t)))
          ∨ (r c w (fun t => ij (Fin.castAdd _ t)) = r c' w (fun t => ij (Fin.natAdd _ t))
            ∧ Pp.ord c c' w (fun t => ij (Fin.castAdd _ t)) (fun t => ij (Fin.natAdd _ t)))) := by
  classical
  -- lexLt part
  obtain ⟨φlex, hφlex⟩ : ∃ φ : Formula Alpha (Pp.arity c + Pp.arity c') 0,
      ∀ w ij, WRP.lexLt (r c w (fun t => ij (Fin.castAdd _ t)))
          (r c' w (fun t => ij (Fin.natAdd _ t))) ↔ φ.Sat w ij Fin.elim0 := by
    set pairs : Finset ((Fin D → ℤ) × (Fin D → ℤ)) :=
      ((V c) ×ˢ (V c')).filter (fun p => WRP.lexLt p.1 p.2) with hpairs
    have hconj : ∀ p : (Fin D → ℤ) × (Fin D → ℤ),
        ∃ ψ : Formula Alpha (Pp.arity c + Pp.arity c') 0,
          ∀ w ij, (r c w (fun t => ij (Fin.castAdd _ t)) = p.1
              ∧ r c' w (fun t => ij (Fin.natAdd _ t)) = p.2) ↔ ψ.Sat w ij Fin.elim0 := by
      intro p
      obtain ⟨φl, hφl⟩ := rEq_left_mso r c c' p.1 (hmso c p.1)
      obtain ⟨φr, hφr⟩ := rEq_right_mso r c c' p.2 (hmso c' p.2)
      exact ⟨Formula.and φl φr, fun w ij => by rw [Formula.sat_and, ← hφl, ← hφr]⟩
    choose ψ hψ using hconj
    refine ⟨finsetOr pairs ψ, fun w ij => ?_⟩
    rw [sat_finsetOr]
    constructor
    · intro hlex
      refine ⟨(r c w (fun t => ij (Fin.castAdd _ t)), r c' w (fun t => ij (Fin.natAdd _ t))),
              ?_, (hψ _ w ij).mp ⟨rfl, rfl⟩⟩
      rw [hpairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hmem c w _, hmem c' w _⟩, hlex⟩
    · rintro ⟨p, hp, hsat⟩
      rw [hpairs, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨h1, h2⟩ := (hψ p w ij).mpr hsat
      rw [h1, h2]; exact hp.2
  -- equal-rank part
  obtain ⟨φeq, hφeq⟩ : ∃ φ : Formula Alpha (Pp.arity c + Pp.arity c') 0,
      ∀ w ij, (r c w (fun t => ij (Fin.castAdd _ t)) = r c' w (fun t => ij (Fin.natAdd _ t)))
        ↔ φ.Sat w ij Fin.elim0 := by
    have hconj : ∀ v : Fin D → ℤ,
        ∃ ψ : Formula Alpha (Pp.arity c + Pp.arity c') 0,
          ∀ w ij, (r c w (fun t => ij (Fin.castAdd _ t)) = v
              ∧ r c' w (fun t => ij (Fin.natAdd _ t)) = v) ↔ ψ.Sat w ij Fin.elim0 := by
      intro v
      obtain ⟨φl, hφl⟩ := rEq_left_mso r c c' v (hmso c v)
      obtain ⟨φr, hφr⟩ := rEq_right_mso r c c' v (hmso c' v)
      exact ⟨Formula.and φl φr, fun w ij => by rw [Formula.sat_and, ← hφl, ← hφr]⟩
    choose ψ hψ using hconj
    refine ⟨finsetOr (V c) ψ, fun w ij => ?_⟩
    rw [sat_finsetOr]
    constructor
    · intro heq
      exact ⟨r c w (fun t => ij (Fin.castAdd _ t)), hmem c w _, (hψ _ w ij).mp ⟨rfl, heq.symm⟩⟩
    · rintro ⟨v, _, hsat⟩
      obtain ⟨h1, h2⟩ := (hψ v w ij).mpr hsat
      rw [h1, h2]
  -- combine with the base order
  obtain ⟨φord, hφord⟩ := Pp.ordDef c c'
  refine ⟨Formula.or φlex (Formula.and φeq φord), fun w ij => ?_⟩
  rw [Formula.sat_or, Formula.sat_and, ← hφlex, ← hφeq, ← hφord]

/-- **The surrogate polyregular presentation.**  Built from a given polyregular
presentation `Pp` (the WRP underlying poly part) by replacing only its order
relation `ord` with the lex-combine of the surrogate rank `r` and `Pp.ord`.  All
other fields — copies, arities, domain, selection, labels — are shared
definitionally, so `surrPoly.Atom`, `surrPoly.selectedAtom`, `surrPoly.labelOf`
are definitionally those of `Pp`. -/
private def surrPoly {Alpha Gamma : Type} (Pp : Polyreg.Presentation Alpha Gamma) {D : ℕ}
    (r : (c : Fin Pp.K) → List Alpha → (Fin (Pp.arity c) → ℕ) → (Fin D → ℤ))
    (hordDef : ∀ c c', MSO.MSODefinableRel (Pp.arity c + Pp.arity c')
      (fun w ij =>
        WRP.lexLt (r c w (fun t => ij (Fin.castAdd _ t))) (r c' w (fun t => ij (Fin.natAdd _ t)))
          ∨ (r c w (fun t => ij (Fin.castAdd _ t)) = r c' w (fun t => ij (Fin.natAdd _ t))
            ∧ Pp.ord c c' w (fun t => ij (Fin.castAdd _ t)) (fun t => ij (Fin.natAdd _ t))))) :
    Polyreg.Presentation Alpha Gamma where
  K := Pp.K
  arity := Pp.arity
  domain := Pp.domain
  domainDef := Pp.domainDef
  sel := Pp.sel
  selDef := Pp.selDef
  label := Pp.label
  labelDef := Pp.labelDef
  ord := fun c c' w ī ī' =>
    WRP.lexLt (r c w ī) (r c' w ī') ∨ (r c w ī = r c' w ī' ∧ Pp.ord c c' w ī ī')
  ordDef := hordDef

@[simp] private theorem surrPoly_selectedAtom {Alpha Gamma : Type}
    (Pp : Polyreg.Presentation Alpha Gamma) {D : ℕ} (r) (hordDef)
    (w : List Alpha) (a : Pp.Atom) :
    (surrPoly Pp (D := D) r hordDef).selectedAtom w a ↔ Pp.selectedAtom w a := Iff.rfl

private theorem surrPoly_atomOrd {Alpha Gamma : Type}
    (Pp : Polyreg.Presentation Alpha Gamma) {D : ℕ} (r) (hordDef)
    (w : List Alpha) (a b : Pp.Atom) :
    (surrPoly Pp (D := D) r hordDef).atomOrd w a b
      ↔ WRP.lexLt (r a.1 w a.2) (r b.1 w b.2)
          ∨ (r a.1 w a.2 = r b.1 w b.2 ∧ Pp.atomOrd w a b) := Iff.rfl

/-- **Output congruence against the WRP output.**  `surrPoly.IsOutput` and the WRP
declarative output `P.IsOutput` share the same atoms, selected atoms and labels
(definitionally, since `surrPoly` shares those fields of `P.toPoly`), differing
only in the sort order: `surrPoly.atomOrd` vs `P.wrpOrd`.  When the two orders
agree on every pair of selected atoms of `w`, the two declarative outputs on `w`
coincide. -/
private theorem surrIsOutput_iff_wrpIsOutput {Alpha Gamma : Type}
    {P : WRP.Presentation Alpha Gamma}
    (r : (c : Fin P.toPoly.K) → List Alpha → (Fin (P.toPoly.arity c) → ℕ) → (Fin P.d → ℤ)) (hordDef)
    (w : List Alpha) (out : List Gamma)
    (hagree : ∀ a b : P.toPoly.Atom, P.toPoly.selectedAtom w a → P.toPoly.selectedAtom w b →
      ((surrPoly P.toPoly r hordDef).atomOrd w a b ↔ P.wrpOrd w a b)) :
    (surrPoly P.toPoly r hordDef).IsOutput w out ↔ P.IsOutput w out := by
  constructor
  · rintro ⟨atoms, hnd, hmem, hpw, hout⟩
    refine ⟨atoms, hnd, ?_, ?_, hout⟩
    · intro a; exact (hmem a).trans (surrPoly_selectedAtom P.toPoly r hordDef w a)
    · refine hpw.imp_of_mem ?_
      intro a b ha hb hab
      have hsa : P.toPoly.selectedAtom w a :=
        (surrPoly_selectedAtom P.toPoly r hordDef w a).mp ((hmem a).mp ha)
      have hsb : P.toPoly.selectedAtom w b :=
        (surrPoly_selectedAtom P.toPoly r hordDef w b).mp ((hmem b).mp hb)
      exact (hagree a b hsa hsb).mp hab
  · rintro ⟨atoms, hnd, hmem, hpw, hout⟩
    refine ⟨atoms, hnd, ?_, ?_, hout⟩
    · intro a; exact (hmem a).trans (surrPoly_selectedAtom P.toPoly r hordDef w a).symm
    · refine hpw.imp_of_mem ?_
      intro a b ha hb hab
      have hsa : P.toPoly.selectedAtom w a := (hmem a).mp ha
      have hsb : P.toPoly.selectedAtom w b := (hmem b).mp hb
      exact (hagree a b hsa hsb).mpr hab

/-- `Pp.Valid` repackaged as an `OrdValid` of `Pp.atomOrd` over `selectedAtom w`. -/
private theorem polyValid_ordValid {Alpha Gamma : Type} {Pp : Polyreg.Presentation Alpha Gamma}
    (hV : Pp.Valid) (w : List Alpha) :
    OrdValid (Pp.selectedAtom w) (Pp.atomOrd w) where
  irrefl := fun a ha => hV.irrefl w a ha
  trans := fun a b c ha hb hc hab hbc => hV.trans w a b c ha hb hc hab hbc
  trichot := fun a b ha hb => hV.trichot w a b ha hb

/-- **`surrPoly` is valid.**  Its order is the lex-combine of the surrogate rank
(a `lexLt` strict total order on `Fin D → ℤ`) with the base order `χ`, which is a
strict total order on selected atoms by `Pp.Valid` — so the combine is too. -/
private theorem surrPoly_valid {Alpha Gamma : Type} {Pp : Polyreg.Presentation Alpha Gamma} {D : ℕ}
    (hV : Pp.Valid)
    (r : (c : Fin Pp.K) → List Alpha → (Fin (Pp.arity c) → ℕ) → (Fin D → ℤ)) (hordDef) :
    (surrPoly Pp r hordDef).Valid := by
  have key : ∀ w, OrdValid (Pp.selectedAtom w) ((surrPoly Pp r hordDef).atomOrd w) := by
    intro w
    have := lexCombine_ordValid (Pp.selectedAtom w) (fun a : Pp.Atom => r a.1 w a.2)
      (Pp.atomOrd w) (polyValid_ordValid hV w)
    -- rewrite the order to `surrPoly`'s `atomOrd`
    refine ⟨?_, ?_, ?_⟩
    · intro a ha; rw [surrPoly_atomOrd]; exact this.irrefl a ha
    · intro a b c ha hb hc hab hbc
      rw [surrPoly_atomOrd] at hab hbc ⊢
      exact this.trans a b c ha hb hc hab hbc
    · intro a b ha hb
      rw [surrPoly_atomOrd, surrPoly_atomOrd]
      exact this.trichot a b ha hb
  exact
    { irrefl := fun w a ha => (key w).irrefl a ha
      trans := fun w a b c ha hb hc hab hbc => (key w).trans a b c ha hb hc hab hbc
      trichot := fun w a b ha hb => (key w).trichot a b ha hb }

/-- **Surrogate collapse core.**  If a transduction `T` is realised by a polyregular
presentation `Pp` sorted by some target order whose declarative output is captured
by `outputPred`, and there is a finite-valued, MSO-definable surrogate rank `r`
whose lex-combine with `Pp.ord` agrees with that target order on the selected
atoms of every domain word, then `T` is ordinary polyregular.

We state it in the exact shape produced by the WRP layer: `T` is realised by
`Pp = P.toPoly` with output the WRP declarative output `P.IsOutput` (sort by
`wrpOrd`), and the surrogate's atom order agrees with `wrpOrd` on selected atoms of
domain words. -/
private theorem surrogate_collapse {Alpha Gamma : Type} {P : WRP.Presentation Alpha Gamma}
    (hV : P.toPoly.Valid)
    (r : (c : Fin P.toPoly.K) → List Alpha → (Fin (P.toPoly.arity c) → ℕ) → (Fin P.d → ℤ))
    (V : ∀ _c, Finset (Fin P.d → ℤ))
    (hmem : ∀ c w ī, r c w ī ∈ V c)
    (hmso : ∀ c (v : Fin P.d → ℤ), MSO.MSODefinableRel (P.toPoly.arity c) (fun w ī => r c w ī = v))
    (hagree : ∀ (w : List Alpha), P.toPoly.domain w → ∀ a b : P.toPoly.Atom,
      P.toPoly.selectedAtom w a → P.toPoly.selectedAtom w b →
      ((surrPoly P.toPoly r (fun c c' => ordCombine_mso r V hmem hmso c c')).atomOrd w a b
        ↔ P.wrpOrd w a b))
    {T : List Alpha → Option (List Gamma)}
    (hreal : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)) :
    Polyreg.IsPolyregular T := by
  set hordDef := fun c c' => ordCombine_mso r V hmem hmso c c' with hhord
  set Q := surrPoly P.toPoly r hordDef with hQ
  refine ⟨Q, surrPoly_valid hV r hordDef, fun w out => ?_⟩
  rw [hreal w out]
  constructor
  · rintro ⟨hdom, hp⟩
    exact ⟨hdom, (surrIsOutput_iff_wrpIsOutput r hordDef w out
      (fun a b ha hb => hagree w hdom a b ha hb)).mpr hp⟩
  · rintro ⟨hdom, hp⟩
    exact ⟨hdom, (surrIsOutput_iff_wrpIsOutput r hordDef w out
      (fun a b ha hb => hagree w hdom a b ha hb)).mp hp⟩

/-! ## Piece (B) — the bridge (uses `SliceMSO.detAuto_state_mso`)

A bounded `RankSource` carries its running ℤ^d total in the state of an augmented
finite automaton: the control state of `A` paired with the running vector,
*clamped* to the cube `{-B,…,B}^d` (with a `none` overflow state).  On any word
all of whose prefix ranks are bounded by `B`, the augmented automaton's state
records the exact prefix rank; the converse-Büchi axiom then makes each cube value
MSO-definable in the queried position. -/

section Bridge

variable {Alpha : Type} [Fintype Alpha] {d : ℕ}

/-- The cube `{-B,…,B}` encoded as `Fin (2B+1)`: index `k` represents `k - B`. -/
private def cubeDecode (B : ℕ) (k : Fin (2 * B + 1)) : ℤ := (k : ℤ) - B

/-- Encode an integer `z` as a cube index (clamped, so always valid; the decode is
exact for `|z| ≤ B`). -/
private def cubeEncode (B : ℕ) (z : ℤ) : Fin (2 * B + 1) :=
  ⟨min (2 * B) (z + B).toNat, by omega⟩

private theorem cubeDecode_encode (B : ℕ) (z : ℤ) (h : -(B : ℤ) ≤ z ∧ z ≤ B) :
    cubeDecode B (cubeEncode B z) = z := by
  simp only [cubeDecode, cubeEncode]
  have h2 : min (2 * B) (z + B).toNat = (z + B).toNat := by omega
  rw [h2]
  have h1 : ((z + B).toNat : ℤ) = z + B := by omega
  rw [h1]; ring

/-- The augmented automaton's state: control state of `A` paired with the running
ℤ^d total clamped to the cube (`some`), or the dead overflow state (`none`). -/
private abbrev AugState (A : RankSource Alpha d) (B : ℕ) : Type :=
  A.Q × Option (Fin d → Fin (2 * B + 1))

/-- Decode a (live) augmented value-state to its ℤ^d vector. -/
private def augValue (B : ℕ) (f : Fin d → Fin (2 * B + 1)) : Fin d → ℤ :=
  fun c => cubeDecode B (f c)

/-- The augmented one-step transition: advance the control state, and try to add
the per-letter weight to the clamped vector, going dead on any overflow. -/
private def augStep (A : RankSource Alpha d) (B : ℕ)
    (st : AugState A B) (a : Alpha) : AugState A B :=
  match st.2 with
  | none => (A.δ st.1 a, none)
  | some f =>
      let cand : Fin d → ℤ := fun c => augValue B f c + A.ω st.1 a c
      if _h : ∀ c, -(B : ℤ) ≤ cand c ∧ cand c ≤ B then
        (A.δ st.1 a, some (fun c => cubeEncode B (cand c)))
      else
        (A.δ st.1 a, none)

/-- The augmented deterministic acceptor (acceptance is irrelevant; we only use its
`stateBefore`). -/
private def augAuto (A : RankSource Alpha d) (B : ℕ) : SliceMSO.DetAuto Alpha where
  Q := AugState A B
  fintypeQ := by
    letI := A.fintypeQ
    infer_instance
  q0 := (A.q0, some (fun _ => cubeEncode B 0))
  δ := augStep A B
  accept := fun _ => True

omit [Fintype Alpha] in
/-- One-step unfolding of `augAuto`'s `stateBefore`. -/
private theorem augAuto_stateBefore_succ (A : RankSource Alpha d) (B : ℕ)
    (w : List Alpha) (i : ℕ) (hi : i < w.length) :
    (augAuto A B).stateBefore w (i + 1)
      = augStep A B ((augAuto A B).stateBefore w i) (w[i]) := by
  unfold SliceMSO.DetAuto.stateBefore
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
  rfl

omit [Fintype Alpha] in
/-- **The carry lemma.**  On a word all of whose prefix ranks up to position `i`
are bounded by `B`, the augmented automaton's state at `i` records the exact
control state and the exact (encoded) prefix rank — it never went dead. -/
private theorem augAuto_stateBefore_eq (A : RankSource Alpha d) (B : ℕ)
    (w : List Alpha) :
    ∀ i, (∀ j ≤ i, ∀ c, -(B : ℤ) ≤ A.prefixRank w j c ∧ A.prefixRank w j c ≤ B) →
      (augAuto A B).stateBefore w i
        = (A.stateBefore w i, some (fun c => cubeEncode B (A.prefixRank w i c))) := by
  intro i
  induction i with
  | zero =>
      intro _
      simp only [SliceMSO.DetAuto.stateBefore, List.take_zero, List.foldl_nil]
      have h0 : A.prefixRank w 0 = fun _ => 0 := by
        funext c; simp [RankSource.prefixRank]
      have hsb : A.stateBefore w 0 = A.q0 := by simp [RankSource.stateBefore]
      rw [hsb, h0]
      rfl
  | succ i ih =>
      intro hbound
      by_cases hi : i < w.length
      · -- step forward
        have ihb : ∀ j ≤ i, ∀ c, -(B : ℤ) ≤ A.prefixRank w j c ∧ A.prefixRank w j c ≤ B :=
          fun j hj c => hbound j (le_trans hj (Nat.le_succ i)) c
        have ihstate := ih ihb
        rw [augAuto_stateBefore_succ A B w i hi, ihstate]
        -- compute prefixRank successor
        have hget : w[i]? = some (w[i]) := List.getElem?_eq_getElem hi
        have hpr : A.prefixRank w (i + 1)
            = A.prefixRank w i + A.ω (A.stateBefore w i) (w[i]) :=
          SliceRankAtom.prefixRank_succ A w i hget
        have hsb : A.stateBefore w (i + 1) = A.δ (A.stateBefore w i) (w[i]) :=
          SliceRankAtom.stateBefore_succ A w i hi
        -- the candidate equals the (in-cube) prefix rank at i+1
        have hcand : ∀ c,
            augValue B (fun c => cubeEncode B (A.prefixRank w i c)) c
              + A.ω (A.stateBefore w i) (w[i]) c = A.prefixRank w (i + 1) c := by
          intro c
          rw [hpr]
          simp only [augValue, Pi.add_apply]
          rw [cubeDecode_encode B _ ⟨(ihb i (le_refl i) c).1, (ihb i (le_refl i) c).2⟩]
        have hin : ∀ c, -(B : ℤ) ≤
              (augValue B (fun c => cubeEncode B (A.prefixRank w i c)) c
                + A.ω (A.stateBefore w i) (w[i]) c)
            ∧ (augValue B (fun c => cubeEncode B (A.prefixRank w i c)) c
                + A.ω (A.stateBefore w i) (w[i]) c) ≤ B := by
          intro c
          rw [hcand c]
          exact hbound (i + 1) (le_refl _) c
        -- evaluate `augStep`
        unfold augStep
        simp only []
        rw [dif_pos hin, hsb]
        refine Prod.ext rfl ?_
        show some (fun c => cubeEncode B
            (augValue B (fun c => cubeEncode B (A.prefixRank w i c)) c
              + A.ω (A.stateBefore w i) (w[i]) c))
          = some (fun c => cubeEncode B (A.prefixRank w (i + 1) c))
        congr 1
        funext c
        rw [hcand c]
      · -- past the end: word unchanged, everything stable
        push Not at hi
        have htake : w.take (i + 1) = w.take i := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        have ihb : ∀ j ≤ i, ∀ c, -(B : ℤ) ≤ A.prefixRank w j c ∧ A.prefixRank w j c ≤ B :=
          fun j hj c => hbound j (le_trans hj (Nat.le_succ i)) c
        have ihstate := ih ihb
        have hstateEq : (augAuto A B).stateBefore w (i + 1)
            = (augAuto A B).stateBefore w i := by
          unfold SliceMSO.DetAuto.stateBefore; rw [htake]
        have hsbEq : A.stateBefore w (i + 1) = A.stateBefore w i := by
          unfold RankSource.stateBefore; rw [htake]
        have hprEq : A.prefixRank w (i + 1) = A.prefixRank w i := by
          funext c
          simp only [RankSource.prefixRank]
          rw [Finset.sum_range_succ, List.getElem?_eq_none (by omega), Option.elim_none, add_zero]
        rw [hstateEq, ihstate, hsbEq, hprEq]

/-! ### Observations at a queried coordinate are MSO-definable -/

/-- The augmented automaton's state at the `j`-th queried position is
MSO-definable (in the `k` free variables), by `detAuto_state_mso` relabelled to
the coordinate `j`. -/
private theorem stateAt_mso (A : RankSource Alpha d) (B : ℕ) {k : ℕ} (j : Fin k)
    (s : (augAuto A B).Q) :
    MSO.MSODefinableRel k (fun w ī => (augAuto A B).stateBefore w (ī j) = s) := by
  obtain ⟨φ, hφ⟩ := SliceMSO.detAuto_state_mso (augAuto A B) s
  refine ⟨SliceFasGates.relabelFO (fun _ : Fin 1 => j) φ, fun w ρ => ?_⟩
  rw [SliceFasGates.sat_relabelFO]
  have he : (ρ ∘ (fun _ : Fin 1 => j)) = (fun _ : Fin 1 => ρ j) := by funext x; simp
  rw [he]
  have := hφ w (fun _ : Fin 1 => ρ j)
  simpa using this

/-- The letter at the `j`-th queried position equals `a : Option Alpha` is
MSO-definable: for `a = some b` it is `labelEq`; for `a = none` it is the
negation of the disjunction over the (finite) alphabet of `labelEq`. -/
private theorem letterAt_mso {k : ℕ} (j : Fin k) (a : Option Alpha) :
    MSO.MSODefinableRel k (fun w (ī : Fin k → ℕ) => w[ī j]? = a) := by
  classical
  cases a with
  | some b =>
      exact ⟨Formula.labelEq j b, fun w ρ => by simp [Formula.Sat]⟩
  | none =>
      -- `w[ī j]? = none` ↔ ¬ ∃ b, `w[ī j]? = some b`
      refine ⟨Formula.neg (finsetOr (Finset.univ : Finset Alpha)
        (fun b => Formula.labelEq j b)), fun w ρ => ?_⟩
      rw [Formula.sat_neg, sat_finsetOr]
      constructor
      · intro hnone
        rintro ⟨b, -, hsat⟩
        simp only [Formula.sat_labelEq] at hsat
        rw [hnone] at hsat; exact absurd hsat.symm (Option.some_ne_none b)
      · intro hno
        rcases hb : w[ρ j]? with _ | b
        · exact hb
        · exact absurd ⟨b, Finset.mem_univ b, by simp only [Formula.sat_labelEq]; exact hb⟩ hno

/-! ### The surrogate rank term and its three properties

The surrogate replaces, in every summand of `κ`, the *true* prefix rank /
control-state reads by the augmented automaton's clamped value / state.  On a word
all of whose summand prefix ranks at the queried positions are bounded by `B`, the
surrogate equals the true `κ.eval`; off such words it is a finite-valued junk
default — which is harmless because the §4 collapse only needs agreement on domain
words. -/

/-- The augmented value of a summand, as a function of its augmented automaton's
state at the queried position and the letter there.  Decoding a `(q, some f)` state
gives the clamped prefix rank `augValue B f` (the affine `coeff·ρ + β`); a dead
`(q, none)` state yields the junk default `0`. -/
private def augSummandVal {k : ℕ} (s : Summand Alpha d k) (B : ℕ)
    (st : (augAuto s.A B).Q) (a : Option Alpha) : Fin d → ℤ :=
  match st.2 with
  | some f => fun c => s.coeff * augValue B f c + a.elim 0 (fun b => s.β st.1 b) c
  | none => 0

/-- The surrogate evaluation of a single summand on `(w, ī)`: read the augmented
state and the letter at the queried coordinate, then apply `augSummandVal`. -/
private def augSummandEval {k : ℕ} (s : Summand Alpha d k) (B : ℕ)
    (w : List Alpha) (ī : Fin k → ℕ) : Fin d → ℤ :=
  augSummandVal s B ((augAuto s.A B).stateBefore w (ī s.π)) (w[ī s.π]?)

/-- The finite set of possible surrogate summand values (image of the finite state
× letter product). -/
private noncomputable def augSummandValues {k : ℕ} (s : Summand Alpha d k) (B : ℕ) :
    Finset (Fin d → ℤ) :=
  let _ := (augAuto s.A B).fintypeQ
  Finset.image (fun p : (augAuto s.A B).Q × Option Alpha => augSummandVal s B p.1 p.2)
    Finset.univ

private theorem augSummandEval_mem {k : ℕ} (s : Summand Alpha d k) (B : ℕ)
    (w : List Alpha) (ī : Fin k → ℕ) :
    augSummandEval s B w ī ∈ augSummandValues s B := by
  classical
  let _ := (augAuto s.A B).fintypeQ
  rw [augSummandValues, Finset.mem_image]
  exact ⟨((augAuto s.A B).stateBefore w (ī s.π), w[ī s.π]?), Finset.mem_univ _, rfl⟩

omit [Fintype Alpha] in
/-- **Agreement (single summand).**  If the source `s.A`'s prefix ranks up to the
queried position `ī s.π` are bounded by `B`, the surrogate summand value equals the
true `Summand.eval`. -/
private theorem augSummandEval_eq {k : ℕ} (s : Summand Alpha d k) (B : ℕ)
    (w : List Alpha) (ī : Fin k → ℕ)
    (hb : ∀ j ≤ ī s.π, ∀ c, -(B : ℤ) ≤ s.A.prefixRank w j c ∧ s.A.prefixRank w j c ≤ B) :
    augSummandEval s B w ī = s.eval w ī := by
  have hstate := augAuto_stateBefore_eq s.A B w (ī s.π) hb
  funext c
  rw [augSummandEval, hstate]
  show s.coeff * augValue B (fun c => cubeEncode B (s.A.prefixRank w (ī s.π) c)) c
      + (w[ī s.π]?).elim 0 (fun b => s.β (s.A.stateBefore w (ī s.π)) b) c
    = s.eval w ī c
  have hav : augValue B (fun c => cubeEncode B (s.A.prefixRank w (ī s.π) c)) c
      = s.A.prefixRank w (ī s.π) c := by
    simp only [augValue]
    rw [cubeDecode_encode B _ ⟨(hb (ī s.π) (le_refl _) c).1, (hb (ī s.π) (le_refl _) c).2⟩]
  rw [hav, Summand.eval]

/-- **MSO-definability (single summand).**  For each target value `v`, the relation
`augSummandEval s B w ī = v` is MSO-definable: the finite disjunction over
state×letter observations giving value `v` of the (MSO-definable) observation
formulas. -/
private theorem augSummandEval_mso {k : ℕ} (s : Summand Alpha d k) (B : ℕ)
    (v : Fin d → ℤ) :
    MSO.MSODefinableRel k (fun w ī => augSummandEval s B w ī = v) := by
  classical
  let _ := (augAuto s.A B).fintypeQ
  -- the observations giving value `v`
  set obs : Finset ((augAuto s.A B).Q × Option Alpha) :=
    Finset.univ.filter (fun p => augSummandVal s B p.1 p.2 = v) with hobs
  have hequiv : ∀ w ī, augSummandEval s B w ī = v ↔
      ∃ p ∈ obs, ((augAuto s.A B).stateBefore w (ī s.π) = p.1 ∧ w[ī s.π]? = p.2) := by
    intro w ī
    constructor
    · intro h
      refine ⟨((augAuto s.A B).stateBefore w (ī s.π), w[ī s.π]?), ?_, rfl, rfl⟩
      rw [hobs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h⟩
    · rintro ⟨p, hp, hst, hlet⟩
      rw [hobs, Finset.mem_filter] at hp
      rw [augSummandEval, hst, hlet]; exact hp.2
  have hmso : MSO.MSODefinableRel k
      (fun w ī => ∃ p ∈ obs, ((augAuto s.A B).stateBefore w (ī s.π) = p.1 ∧ w[ī s.π]? = p.2)) := by
    refine mso_finsetOr obs (fun p _ => ?_)
    exact mso_and (stateAt_mso s.A B s.π p.1) (letterAt_mso s.π p.2)
  obtain ⟨φ, hφ⟩ := hmso
  exact ⟨φ, fun w ī => (hequiv w ī).trans (hφ w ī)⟩

/-! ### Aggregating over the summand list -/

/-- The surrogate sum over a list of summands. -/
private def augSumListEval {k : ℕ} (L : List (Summand Alpha d k)) (B : ℕ)
    (w : List Alpha) (ī : Fin k → ℕ) : Fin d → ℤ :=
  (L.map (fun s => augSummandEval s B w ī)).sum

/-- **MSO-definability (summand list).**  For each target `v`, the relation
`augSumListEval L B w ī = v` is MSO-definable, by induction on `L`: split the head
summand's (finite-valued) contribution off and recurse. -/
private theorem augSumListEval_mso {k : ℕ} (L : List (Summand Alpha d k)) (B : ℕ)
    (v : Fin d → ℤ) :
    MSO.MSODefinableRel k (fun w ī => augSumListEval L B w ī = v) := by
  classical
  induction L generalizing v with
  | nil =>
      -- `augSumListEval [] = 0`, so `= v` is the constant `v = 0`
      by_cases h : v = (fun _ => (0 : ℤ))
      · refine ⟨Formula.tru, fun w ī => ?_⟩
        simp only [Formula.sat_tru, iff_true, augSumListEval, List.map_nil, List.sum_nil]
        exact h.symm
      · refine ⟨Formula.neg Formula.tru, fun w ī => ?_⟩
        simp only [Formula.sat_neg, Formula.sat_tru, not_true, iff_false,
          augSumListEval, List.map_nil, List.sum_nil]
        exact fun hc => h hc.symm
  | cons s L ih =>
      -- value = `augSummandEval s + augSumListEval L`; range over the head value
      have hsplit : ∀ w ī, augSumListEval (s :: L) B w ī = v ↔
          ∃ v1 ∈ augSummandValues s B,
            (augSummandEval s B w ī = v1 ∧ augSumListEval L B w ī = (fun c => v c - v1 c)) := by
        intro w ī
        constructor
        · intro h
          refine ⟨augSummandEval s B w ī, augSummandEval_mem s B w ī, rfl, ?_⟩
          funext c
          have : augSummandEval s B w ī c + augSumListEval L B w ī c = v c := by
            have := congrFun h c
            simp only [augSumListEval, List.map_cons, List.sum_cons, Pi.add_apply] at this
            exact this
          omega
        · rintro ⟨v1, _, h1, h2⟩
          funext c
          have e1 : augSummandEval s B w ī c = v1 c := congrFun h1 c
          have e2 : augSumListEval L B w ī c = v c - v1 c := congrFun h2 c
          simp only [augSumListEval, List.map_cons, List.sum_cons, Pi.add_apply] at e2 ⊢
          omega
      refine mso_congr (fun w ī => (hsplit w ī).symm)
        (mso_finsetOr (augSummandValues s B) (R := fun v1 w ī =>
          augSummandEval s B w ī = v1 ∧ augSumListEval L B w ī = (fun c => v c - v1 c))
          (fun v1 _ => mso_and (augSummandEval_mso s B v1) (ih _)))

omit [Fintype Alpha] in
/-- **Agreement (summand list).**  When every summand's prefix ranks at the queried
position are bounded by `B`, the surrogate sum equals the true sum of `Summand.eval`. -/
private theorem augSumListEval_eq {k : ℕ} (L : List (Summand Alpha d k)) (B : ℕ)
    (w : List Alpha) (ī : Fin k → ℕ)
    (hb : ∀ s ∈ L, ∀ j ≤ ī s.π, ∀ c,
      -(B : ℤ) ≤ s.A.prefixRank w j c ∧ s.A.prefixRank w j c ≤ B) :
    augSumListEval L B w ī = (L.map (fun s => s.eval w ī)).sum := by
  rw [augSumListEval]
  congr 1
  refine List.map_congr_left (fun s hs => ?_)
  exact augSummandEval_eq s B w ī (hb s hs)

/-! ### The full surrogate rank term -/

/-- The surrogate evaluation of a whole `RankTerm`: its constant plus the surrogate
sum over its summands. -/
private def augRankEval {k : ℕ} (κ : RankTerm Alpha d k) (B : ℕ)
    (w : List Alpha) (ī : Fin k → ℕ) : Fin d → ℤ :=
  fun c => κ.c0 c + augSumListEval κ.summands B w ī c

/-- **MSO-definability (rank term).**  For each target value `v`,
`augRankEval κ B w ī = v` is MSO-definable. -/
private theorem augRankEval_mso {k : ℕ} (κ : RankTerm Alpha d k) (B : ℕ) (v : Fin d → ℤ) :
    MSO.MSODefinableRel k (fun w ī => augRankEval κ B w ī = v) := by
  refine mso_congr (fun w ī => ?_) (augSumListEval_mso κ.summands B (fun c => v c - κ.c0 c))
  constructor
  · intro h
    funext c; have := congrFun h c; simp only [augRankEval] at this ⊢; omega
  · intro h
    funext c; have := congrFun h c; simp only [augRankEval] at this ⊢; omega

omit [Fintype Alpha] in
/-- **Agreement (rank term).**  When all summand prefix ranks at the queried
positions are bounded by `B`, the surrogate equals the true `κ.eval`. -/
private theorem augRankEval_eq {k : ℕ} (κ : RankTerm Alpha d k) (B : ℕ)
    (w : List Alpha) (ī : Fin k → ℕ)
    (hb : ∀ s ∈ κ.summands, ∀ j ≤ ī s.π, ∀ c,
      -(B : ℤ) ≤ s.A.prefixRank w j c ∧ s.A.prefixRank w j c ≤ B) :
    augRankEval κ B w ī = κ.eval w ī := by
  funext c
  simp only [augRankEval, RankTerm.eval]
  rw [augSumListEval_eq κ.summands B w ī hb]
  have key : (κ.summands.map (fun s => s.eval w ī)).sum c =
      (κ.summands.map (fun s => s.eval w ī c)).sum := by
    induction κ.summands with
    | nil => rfl
    | cons s t ih => simp only [List.map_cons, List.sum_cons, Pi.add_apply, ih]
  rw [key]

/-- The finite set of achievable surrogate **sums** over a summand list (a
Minkowski sum of the per-summand finite value sets). -/
private noncomputable def augSumValues {k : ℕ} (B : ℕ) :
    List (Summand Alpha d k) → Finset (Fin d → ℤ)
  | [] => {fun _ => 0}
  | s :: L =>
      letI : DecidableEq (Fin d → ℤ) := Classical.decEq _
      ((augSummandValues s B) ×ˢ (augSumValues B L)).image (fun p => fun c => p.1 c + p.2 c)

private theorem augSumListEval_mem {k : ℕ} (L : List (Summand Alpha d k)) (B : ℕ)
    (w : List Alpha) (ī : Fin k → ℕ) :
    augSumListEval L B w ī ∈ augSumValues B L := by
  classical
  induction L with
  | nil =>
      simp only [augSumValues, Finset.mem_singleton, augSumListEval, List.map_nil, List.sum_nil]
      rfl
  | cons s L ih =>
      simp only [augSumValues, Finset.mem_image, Finset.mem_product]
      refine ⟨(augSummandEval s B w ī, augSumListEval L B w ī),
        ⟨augSummandEval_mem s B w ī, ih⟩, ?_⟩
      funext c
      simp only [augSumListEval, List.map_cons, List.sum_cons, Pi.add_apply]

/-- The finite value set of a surrogate rank term: the constant shifted by the
achievable sums. -/
private noncomputable def augRankValues {k : ℕ} (κ : RankTerm Alpha d k) (B : ℕ) :
    Finset (Fin d → ℤ) :=
  letI : DecidableEq (Fin d → ℤ) := Classical.decEq _
  (augSumValues B κ.summands).image (fun g => fun c => κ.c0 c + g c)

private theorem augRankEval_mem {k : ℕ} (κ : RankTerm Alpha d k) (B : ℕ)
    (w : List Alpha) (ī : Fin k → ℕ) :
    augRankEval κ B w ī ∈ augRankValues κ B := by
  classical
  simp only [augRankValues, Finset.mem_image]
  exact ⟨augSumListEval κ.summands B w ī, augSumListEval_mem κ.summands B w ī, rfl⟩

end Bridge

/-! ## Piece (C) — assembly -/

/-- **Theorem `thm:bounded-rank-collapse` (`thm:bounded-rank-collapse`, paper.tex).**  A `WRP`
transduction whose explicit rank terms `κ c` have all of their sources uniformly
bounded by `B` on the domain is an ordinary polyregular transduction.

The hypotheses make the boundedness *explicit at the level of rank terms*: `κ c` is
an exhibited `RankTerm` computing `P.rank c`, and every source in every `κ c` keeps
its prefix rank within `{-B,…,B}` on every domain word.  (We also ask the
underlying polyregular tie order `χ` to be a strict total order — `P.toPoly.Valid`
— which the paper's presentations always satisfy and which is needed to make the
surrogate `≺` valid off the domain.) -/
theorem bounded_rank_collapse {Alpha Gamma : Type} [Fintype Alpha]
    {P : WRP.Presentation Alpha Gamma} (_hVwrp : P.Valid) (hVpoly : P.toPoly.Valid)
    (κ : ∀ c, RankTerm Alpha P.d (P.toPoly.arity c))
    (hκ : ∀ c w ī, P.rank c w ī = (κ c).eval w ī)
    (B : ℕ)
    (hB : ∀ c, ∀ s ∈ (κ c).summands, ∀ w, P.toPoly.domain w → ∀ i (coord : Fin P.d),
      -(B : ℤ) ≤ s.A.prefixRank w i coord ∧ s.A.prefixRank w i coord ≤ B)
    {T : List Alpha → Option (List Gamma)}
    (hreal : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)) :
    Polyreg.IsPolyregular T := by
  classical
  -- the surrogate rank: the augmented-automaton evaluation of `κ c`
  set r : (c : Fin P.toPoly.K) → List Alpha → (Fin (P.toPoly.arity c) → ℕ) → (Fin P.d → ℤ) :=
    fun c w ī => augRankEval (κ c) B w ī with hr
  set V : ∀ c, Finset (Fin P.d → ℤ) := fun c => augRankValues (κ c) B with hV
  have hmem : ∀ c w ī, r c w ī ∈ V c := fun c w ī => augRankEval_mem (κ c) B w ī
  have hmso : ∀ c (v : Fin P.d → ℤ),
      MSO.MSODefinableRel (P.toPoly.arity c) (fun w ī => r c w ī = v) :=
    fun c v => augRankEval_mso (κ c) B v
  -- agreement of the surrogate with the true rank on domain words
  have hragree : ∀ c w ī, P.toPoly.domain w → r c w ī = P.rank c w ī := by
    intro c w ī hdom
    rw [hr, hκ c w ī]
    exact augRankEval_eq (κ c) B w ī (fun s hs j _ coord => hB c s hs w hdom j coord)
  -- agreement of the surrogate order with `wrpOrd` on selected atoms of domain words
  have hagree : ∀ (w : List Alpha), P.toPoly.domain w → ∀ a b : P.toPoly.Atom,
      P.toPoly.selectedAtom w a → P.toPoly.selectedAtom w b →
      ((surrPoly P.toPoly r (fun c c' => ordCombine_mso r V hmem hmso c c')).atomOrd w a b
        ↔ P.wrpOrd w a b) := by
    intro w hdom a b _ _
    rw [surrPoly_atomOrd]
    have ha : r a.1 w a.2 = P.rankOf w a := hragree a.1 w a.2 hdom
    have hb : r b.1 w b.2 = P.rankOf w b := hragree b.1 w b.2 hdom
    rw [ha, hb]
    rfl
  exact surrogate_collapse hVpoly r V hmem hmso hagree hreal

/-- **Corollary `cor:rank-necessary` (`cor:rank-necessary`, paper.tex).**  The zeta map
admits no bounded-rank `WRP` presentation realising it on the Dyck domain: any such
presentation would, by `bounded_rank_collapse`, exhibit `ζ` as an ordinary
polyregular transduction, contradicting `ZetaNotPolyreg.zetaMap_not_polyregular`.

We state it as the impossibility of an explicit bounded-rank realiser of the shape
the theorem consumes: a valid `WRP` presentation `P` (with valid underlying tie
order), explicit rank terms `κ` for its ranks, a bound `B`, and a transduction `T`
realised by `P` that realises `ζ` on the Dyck domain. -/
theorem rank_necessary :
    ¬ ∃ (P : WRP.Presentation Step Step) (_ : P.Valid) (_ : P.toPoly.Valid)
        (κ : ∀ c, RankTerm Step P.d (P.toPoly.arity c))
        (_ : ∀ c w ī, P.rank c w ī = (κ c).eval w ī)
        (B : ℕ)
        (_ : ∀ c, ∀ s ∈ (κ c).summands, ∀ w, P.toPoly.domain w → ∀ i (coord : Fin P.d),
          -(B : ℤ) ≤ s.A.prefixRank w i coord ∧ s.A.prefixRank w i coord ≤ B)
        (T : List Step → Option (List Step))
        (_ : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)),
      Realises T {Q | IsDyckPath Q} zetaMap := by
  rintro ⟨P, hVwrp, hVpoly, κ, hκ, B, hB, T, hreal, hreal2⟩
  exact ZetaNotPolyreg.zetaMap_not_polyregular
    ⟨T, bounded_rank_collapse hVwrp hVpoly κ hκ B hB hreal, hreal2⟩

end WRPBoundedRank
