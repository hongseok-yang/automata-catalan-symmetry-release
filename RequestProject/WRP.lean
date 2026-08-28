/-
# Weighted-rank polyregular transductions (WRP)

Formalisation of Definitions 3.10–3.13 (`def:rank-source`, `def:regular-rank-term`, `def:wrp`) of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.

A WRP presentation is a polyregular presentation (`Polyreg.Presentation`)
augmented by a rank dimension `d`, finitely many deterministic additive rank
sources, and for each copy a `d`-dimensional *regular rank term* `κ_c`.  The
output order `≺` first compares ranks lexicographically and breaks ties with the
underlying MSO ordering `χ` (the *tie-order*).  Off the rank layer (`d = 0`) the
class is exactly `Polyreg` (Proposition 3.15).
-/
import RequestProject.Polyregular

open MSO

/-! ## Regular rank terms (general weighted-automaton machinery)

`RankSource`/`Summand`/`RankTerm`/`IsRegularRankTerm` are the ℤ-weighted finite-automaton
definability theory of the paper (Definitions 3.10, 3.12).  They are **general** — purely
parametric over an alphabet `Alpha` and dimensions `d, k`, with no dependence on the WRP
`Presentation` model — so they live at top level rather than under `namespace WRP`
(the rank-counting analogue of `MSO.MSODefinableRel`). -/

section RankTermTheory

variable {Alpha : Type*}

/-! ### Definition 3.10 (`def:rank-source`) — deterministic additive rank source -/

/-- **`def:rank-source` (paper.tex).**  A `d`-dimensional deterministic
additive rank source: a finite-state automaton whose transitions carry `ℤ^d`
weights.  (We take `δ` total, as the paper allows after completing a partial `δ`
with a dead state.) -/
structure RankSource (Alpha : Type*) (d : ℕ) where
  Q : Type
  fintypeQ : Fintype Q
  q0 : Q
  δ : Q → Alpha → Q
  ω : Q → Alpha → (Fin d → ℤ)

namespace RankSource

variable {d : ℕ} (A : RankSource Alpha d)

/-- The state of `A` just before position `i` (after reading the first `i`
letters of `w`). -/
def stateBefore (w : List Alpha) (i : ℕ) : A.Q := (w.take i).foldl A.δ A.q0

/-- **Prefix rank** `ρ_A^w(i) = Σ_{j<i} ω(q_{j-1}, a_j) ∈ ℤ^d`. -/
def prefixRank (w : List Alpha) (i : ℕ) : Fin d → ℤ :=
  fun c => ∑ j ∈ Finset.range i, (w[j]?).elim 0 (fun a => A.ω (A.stateBefore w j) a c)

end RankSource

/-! ### Definition 3.12 (`def:regular-rank-term`) — regular rank term -/

/-- One summand of a regular rank term: a source `A`, an integer coefficient, a
chosen coordinate `π : Fin k`, and a bounded local correction `β` depending only
on the source state just before, and the letter at, the queried position. -/
structure Summand (Alpha : Type*) (d k : ℕ) where
  A : RankSource Alpha d
  coeff : ℤ
  π : Fin k
  β : A.Q → Alpha → (Fin d → ℤ)

/-- Value of a summand at the tuple `ī` on word `w`:
`c_t · ρ_{A_t}(x_{π(t)}) + β_t(q^{A_t}_{x_{π(t)}}, a_{x_{π(t)}})`. -/
def Summand.eval {d k : ℕ} (s : Summand Alpha d k) (w : List Alpha) (ī : Fin k → ℕ) :
    Fin d → ℤ :=
  fun c => s.coeff * s.A.prefixRank w (ī s.π) c +
    (w[ī s.π]?).elim 0 (fun a => s.β (s.A.stateBefore w (ī s.π)) a) c

/-- A `d`-dimensional **regular rank term** on `k`-tuples: a constant `c_0 ∈ ℤ^d`
plus finitely many summands.  This is the rank-term primitive behind the
revision's `def:prefix-additive-rank` (paper.tex); the equivalence is
`PrefixAdditiveRank.isRegularRankTerm_iff_isPrefixAdditiveRank`. -/
structure RankTerm (Alpha : Type*) (d k : ℕ) where
  c0 : Fin d → ℤ
  summands : List (Summand Alpha d k)

/-- Value `κ(ī)` of the rank term. -/
def RankTerm.eval {d k : ℕ} (κ : RankTerm Alpha d k) (w : List Alpha) (ī : Fin k → ℕ) :
    Fin d → ℤ :=
  fun c => κ.c0 c + (κ.summands.map (fun s => s.eval w ī c)).sum

/-- A function `f` is a *regular rank term* when it is the evaluation of some
`RankTerm` (Definition 3.12). -/
def IsRegularRankTerm {d k : ℕ} (f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)) : Prop :=
  ∃ κ : RankTerm Alpha d k, ∀ w ī, f w ī = κ.eval w ī

/-! ### (R1) Robustness of regular rank terms

The (R1) rank-term algebra (`thm:wrp-closures`, paper.tex): regular
rank terms are closed under constants, negation, pointwise
sum, partial coordinate reindexing (the embedding of a `ℤ^d` term into a larger
`ℤ^D`), and argument-tuple `Fin.cast`.  These are **general** facts about
`RankTerm`/`IsRegularRankTerm`, used by the closure constructions, so they live
next to the definitions rather than in a downstream file. -/

/-- **(R1) — constant.**  A constant `ℤ^d` vector (independent of `w` and `ī`) is a
regular rank term: take all coefficients `0` and the constant for `c0`. -/
theorem isRegularRankTerm_const {d k : ℕ} (v : Fin d → ℤ) :
    IsRegularRankTerm (Alpha := Alpha) (k := k) (fun _ _ coord => v coord) := by
  refine ⟨⟨v, []⟩, fun w ī => ?_⟩
  funext coord
  simp [RankTerm.eval]

/-- **(R1) — negation.**  The pointwise negation of a regular rank term is a
regular rank term: negate the constant, every coefficient, and every correction
table. -/
theorem isRegularRankTerm_neg {d k : ℕ}
    {f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)} (hf : IsRegularRankTerm f) :
    IsRegularRankTerm (fun w ī coord => - f w ī coord) := by
  obtain ⟨κ, hκ⟩ := hf
  refine ⟨⟨fun c => - κ.c0 c,
    κ.summands.map (fun s => ⟨s.A, - s.coeff, s.π, fun q a c => - s.β q a c⟩)⟩, fun w ī => ?_⟩
  funext coord
  show - f w ī coord = _
  rw [hκ w ī]
  show - κ.eval w ī coord = (-κ.c0 coord) + _
  rw [RankTerm.eval]
  -- the RHS's summand list is the original list with each `.eval` negated
  have hmapeq : ((κ.summands.map
        (fun s => Summand.mk s.A (- s.coeff) s.π (fun q a c => - s.β q a c))).map
        (fun s => s.eval w ī coord))
      = κ.summands.map (fun s => - s.eval w ī coord) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro s _
    simp only [Function.comp_apply, Summand.eval]
    cases w[ī s.π]?
    · simp
    · simp only [Option.elim]; ring
  rw [hmapeq]
  -- sum of negations = negation of sum
  have hsumneg : ∀ l : List (Summand Alpha d k),
      (l.map (fun s => - s.eval w ī coord)).sum = - (l.map (fun s => s.eval w ī coord)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [hsumneg]
  ring

/-- **(R1) — sum.**  The pointwise sum of two regular rank terms is regular:
concatenate the summand lists and add the constants. -/
theorem isRegularRankTerm_add {d k : ℕ}
    {f g : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)}
    (hf : IsRegularRankTerm f) (hg : IsRegularRankTerm g) :
    IsRegularRankTerm (fun w ī coord => f w ī coord + g w ī coord) := by
  obtain ⟨κf, hκf⟩ := hf
  obtain ⟨κg, hκg⟩ := hg
  refine ⟨⟨fun coord => κf.c0 coord + κg.c0 coord, κf.summands ++ κg.summands⟩, fun w ī => ?_⟩
  funext coord
  show f w ī coord + g w ī coord = _
  rw [hκf w ī, hκg w ī]
  simp only [RankTerm.eval, List.map_append, List.sum_append]
  ring

/-- Reindex a rank source's `ℤ^d` weight output along a **partial** coordinate map
`proj : Fin D → Option (Fin d)`: an output coordinate with `proj coord = some t`
reads `ω … t`; one with `proj coord = none` reads `0`.  (The total map `Fin D → Fin d`
is the special case where `proj` is always `some`.) -/
def RankSource.reindexOut {d D : ℕ} (A : RankSource Alpha d)
    (proj : Fin D → Option (Fin d)) : RankSource Alpha D where
  Q := A.Q
  fintypeQ := A.fintypeQ
  q0 := A.q0
  δ := A.δ
  ω := fun q a coord => (proj coord).elim 0 (A.ω q a)

theorem RankSource.reindexOut_stateBefore {d D : ℕ} (A : RankSource Alpha d)
    (proj : Fin D → Option (Fin d)) (w : List Alpha) (i : ℕ) :
    (A.reindexOut proj).stateBefore w i = A.stateBefore w i := rfl

theorem RankSource.reindexOut_prefixRank {d D : ℕ} (A : RankSource Alpha d)
    (proj : Fin D → Option (Fin d)) (w : List Alpha) (i : ℕ) :
    (A.reindexOut proj).prefixRank w i = fun coord => (proj coord).elim 0 (A.prefixRank w i) := by
  funext coord
  cases hp : proj coord with
  | none =>
      simp only [RankSource.prefixRank, RankSource.reindexOut, hp, Option.elim_none]
      rw [Finset.sum_eq_zero]
      intro x _; cases w[x]? <;> simp
  | some t =>
      simp only [RankSource.prefixRank, RankSource.reindexOut, hp, Option.elim_some]
      apply Finset.sum_congr rfl
      intro x _
      cases w[x]?
      · simp only [Option.elim_none]
      · rfl

/-- **(R1) — partial coordinate reindexing / embedding.**  Spreading a regular
rank term's `ℤ^d` output into a larger `ℤ^D` along a partial coordinate map
`proj : Fin D → Option (Fin d)` (coordinates mapped to `none` become `0`) is again
regular: reindex the constant, each source weight `ω`, and each correction `β`. -/
theorem isRegularRankTerm_reindex {d D k : ℕ}
    {f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)} (hf : IsRegularRankTerm f)
    (proj : Fin D → Option (Fin d)) :
    IsRegularRankTerm (fun w ī coord => (proj coord).elim 0 (f w ī)) := by
  obtain ⟨κ, hκ⟩ := hf
  -- reindex each source's weight function through `proj`, and likewise `c0`/`β`
  refine ⟨⟨fun coord => (proj coord).elim 0 κ.c0,
    κ.summands.map (fun s =>
      ⟨s.A.reindexOut proj, s.coeff, s.π, fun q a coord => (proj coord).elim 0 (s.β q a)⟩)⟩,
    fun w ī => ?_⟩
  funext coord
  show (proj coord).elim 0 (f w ī) = _
  rw [hκ w ī]
  cases hp : proj coord with
  | none =>
      show (0 : ℤ) = _
      rw [RankTerm.eval]
      simp only [hp, Option.elim_none, zero_add]
      rw [List.map_map]
      rw [List.sum_eq_zero]
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨s, _, rfl⟩ := hx
      simp only [Function.comp_apply, Summand.eval, RankSource.reindexOut_prefixRank,
        RankSource.reindexOut_stateBefore, hp, Option.elim_none]
      cases w[ī s.π]? <;> simp [hp]
  | some t =>
      show κ.eval w ī t = _
      rw [RankTerm.eval, RankTerm.eval]
      congr 1
      · simp [hp]
      · rw [List.map_map]
        refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
        simp only [Function.comp_apply, Summand.eval, RankSource.reindexOut_prefixRank,
          RankSource.reindexOut_stateBefore, hp, Option.elim_some]
        cases w[ī s.π]? <;> simp [hp]

/-- **(R1) — argument-tuple reindexing.**  Precomposing a regular rank term's
position-tuple argument with a `Fin.cast` along an arity equality `h : k = k'` is
again regular. -/
theorem isRegularRankTerm_castArg {d k k' : ℕ} (h : k = k')
    {f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)} (hf : IsRegularRankTerm f) :
    IsRegularRankTerm (fun w (ī : Fin k' → ℕ) => f w (fun t => ī (Fin.cast h t))) := by
  subst h
  obtain ⟨κ, hκ⟩ := hf
  exact ⟨κ, fun w ī => by simpa using hκ w (fun t => ī (Fin.cast rfl t))⟩

end RankTermTheory

namespace WRP

variable {Alpha Gamma : Type*}

/-! ### Definition 3.13 (`def:wrp`) — WRP presentation -/

/-- Strict lexicographic order on rank vectors `Fin d → ℤ`. -/
def lexLt {d : ℕ} (x y : Fin d → ℤ) : Prop :=
  ∃ i : Fin d, (∀ j : Fin d, j < i → x j = y j) ∧ x i < y i

/-- **`def:wrp` (paper.tex).**  A WRP presentation: a
polyregular presentation together with a rank dimension and, for each copy, a
regular rank term. -/
structure Presentation (Alpha Gamma : Type*) where
  toPoly : Polyreg.Presentation Alpha Gamma
  d : ℕ
  rank : (c : Fin toPoly.K) → List Alpha → (Fin (toPoly.arity c) → ℕ) → (Fin d → ℤ)
  rankReg : ∀ c, IsRegularRankTerm (rank c)

namespace Presentation

variable (P : Presentation Alpha Gamma)

/-- Atoms of a WRP presentation are the atoms of its underlying polyregular one. -/
def Atom := P.toPoly.Atom

/-- The rank `ℤ^d` of an atom. -/
def rankOf (w : List Alpha) (a : P.toPoly.Atom) : Fin P.d → ℤ := P.rank a.1 w a.2

/-- **The output order `≺` (Definition 3.13).**  Compare ranks lexicographically;
on equal rank, defer to the MSO tie-order `χ` of the polyregular presentation. -/
def wrpOrd (w : List Alpha) (a b : P.toPoly.Atom) : Prop :=
  lexLt (P.rankOf w a) (P.rankOf w b) ∨
    (P.rankOf w a = P.rankOf w b ∧ P.toPoly.atomOrd w a b)

/-- Validity: on every word, `≺` is a strict total order on the selected atoms. -/
structure Valid : Prop where
  irrefl : ∀ w a, P.toPoly.selectedAtom w a → ¬ P.wrpOrd w a a
  trans : ∀ w a b c, P.toPoly.selectedAtom w a → P.toPoly.selectedAtom w b →
    P.toPoly.selectedAtom w c → P.wrpOrd w a b → P.wrpOrd w b c → P.wrpOrd w a c
  trichot : ∀ w a b, P.toPoly.selectedAtom w a → P.toPoly.selectedAtom w b →
    P.wrpOrd w a b ∨ a = b ∨ P.wrpOrd w b a

/-- **Declarative output.**  `out` is the output of the WRP presentation on `w`
iff it lists the labels of the selected atoms in increasing `≺`-order. -/
def IsOutput (w : List Alpha) (out : List Gamma) : Prop :=
  ∃ atoms : List P.toPoly.Atom,
    atoms.Nodup ∧
    (∀ a, a ∈ atoms ↔ P.toPoly.selectedAtom w a) ∧
    atoms.Pairwise (P.wrpOrd w) ∧
    out = atoms.map (P.toPoly.labelOf w)

end Presentation

/-- **`T` is a weighted-rank polyregular transduction** when it is realised by a
valid WRP presentation. -/
def IsWRP (T : List Alpha → Option (List Gamma)) : Prop :=
  ∃ P : Presentation Alpha Gamma, P.Valid ∧
    ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)

/-! ### Proposition 3.15 — WRP extends Polyreg -/

/-- The trivial (`d = 0`) rank term. -/
def zeroRankTerm (k : ℕ) : RankTerm Alpha 0 k := ⟨fun c => c.elim0, []⟩

/-- With rank dimension `0`, every function into `Fin 0 → ℤ` is a regular rank
term (there is only the empty vector). -/
theorem isRegularRankTerm_zero {k : ℕ} (f : List Alpha → (Fin k → ℕ) → (Fin 0 → ℤ)) :
    IsRegularRankTerm f := by
  refine ⟨zeroRankTerm k, fun w ī => ?_⟩
  funext c; exact c.elim0

/-- On `Fin 0 → ℤ` the lexicographic order is empty. -/
theorem lexLt_zero (x y : Fin 0 → ℤ) : ¬ lexLt x y := by
  rintro ⟨i, _⟩; exact i.elim0

/-- **`prop:conservative` (paper.tex).**  `Polyreg ⊆ WRP`: an
ordinary polyregular function is WRP with rank dimension `0`. -/
theorem isWRP_of_isPolyregular {T : List Alpha → Option (List Gamma)}
    (h : Polyreg.IsPolyregular T) : IsWRP T := by
  obtain ⟨P, hValid, hT⟩ := h
  set Q : Presentation Alpha Gamma :=
    ⟨P, 0, fun _ _ _ => Fin.elim0, fun _ => isRegularRankTerm_zero _⟩ with hQ
  -- with `d = 0` the lexicographic rank layer is empty, so `≺` is just `χ`
  have hwrp : ∀ w (a b : Q.toPoly.Atom), Q.wrpOrd w a b ↔ P.atomOrd w a b := by
    intro w a b
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact (lexLt_zero _ _ h).elim
      · exact h
    · intro h; exact Or.inr ⟨funext (fun c => c.elim0), h⟩
  refine ⟨Q, ?_, ?_⟩
  · constructor
    · intro w a ha hbad; exact hValid.irrefl w a ha ((hwrp w a a).mp hbad)
    · intro w a b c ha hb hc hab hbc
      exact (hwrp w a c).mpr
        (hValid.trans w a b c ha hb hc ((hwrp w a b).mp hab) ((hwrp w b c).mp hbc))
    · intro w a b ha hb
      rcases hValid.trichot w a b ha hb with h | h | h
      · exact Or.inl ((hwrp w a b).mpr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((hwrp w b a).mpr h))
  · intro w out
    rw [hT w out]
    constructor
    · rintro ⟨hdom, atoms, hnd, hmem, hpair, hout⟩
      exact ⟨hdom, atoms, hnd, hmem, hpair.imp (fun hh => (hwrp w _ _).mpr hh), hout⟩
    · rintro ⟨hdom, atoms, hnd, hmem, hpair, hout⟩
      exact ⟨hdom, atoms, hnd, hmem, hpair.imp (fun hh => (hwrp w _ _).mp hh), hout⟩

/-! ### Non-vacuity -/

/-- The empty presentation (no copies): realises the everywhere-`[]` transduction. -/
def emptyPres (Alpha Gamma : Type*) : Presentation Alpha Gamma where
  toPoly :=
    { K := 0
      arity := Fin.elim0
      domain := fun _ => True
      domainDef := ⟨Formula.tru, fun _ => Iff.rfl⟩
      sel := fun c => c.elim0
      selDef := fun c => c.elim0
      label := fun c => c.elim0
      labelDef := fun c => c.elim0
      ord := fun c => c.elim0
      ordDef := fun c => c.elim0 }
  d := 0
  rank := fun c => c.elim0
  rankReg := fun c => c.elim0

/-- **Non-vacuity.**  `IsWRP` is inhabited: the constant `[]` transduction is WRP
(via `emptyPres`).  Hence Theorem 8.9 ("no WRP swap") is not vacuously true for
lack of WRP transductions. -/
theorem isWRP_const_nil {Alpha Gamma : Type*} :
    IsWRP (fun _ : List Alpha => (some ([] : List Gamma))) := by
  refine ⟨emptyPres Alpha Gamma,
    ⟨fun _ a _ => a.1.elim0, fun _ a _ _ _ _ _ => a.1.elim0, fun _ a _ _ => a.1.elim0⟩, ?_⟩
  intro w out
  constructor
  · intro h
    obtain rfl : out = [] := (Option.some.inj h).symm
    exact ⟨trivial, [], List.nodup_nil, fun a => a.1.elim0, List.Pairwise.nil, rfl⟩
  · rintro ⟨_, atoms, _, _, _, hout⟩
    have hatoms : atoms = [] := List.eq_nil_iff_forall_not_mem.mpr fun a _ => a.1.elim0
    subst hatoms
    simp only [List.map_nil] at hout
    rw [hout]

end WRP

/-- **Generic output uniqueness**: a valid WRP presentation has at most one
declarative output per word. -/
theorem isOutput_unique {Alpha Gamma : Type*} (P : WRP.Presentation Alpha Gamma)
    (hV : P.Valid) {w : List Alpha} {out₁ out₂ : List Gamma}
    (h₁ : P.IsOutput w out₁) (h₂ : P.IsOutput w out₂) : out₁ = out₂ := by
  obtain ⟨l₁, nd₁, mem₁, pw₁, rfl⟩ := h₁
  obtain ⟨l₂, nd₂, mem₂, pw₂, rfl⟩ := h₂
  have hperm : l₁.Perm l₂ :=
    (List.perm_ext_iff_of_nodup nd₁ nd₂).mpr
      (fun a => (mem₁ a).trans (mem₂ a).symm)
  have hl : l₁ = l₂ := by
    refine hperm.eq_of_pairwise ?_ pw₁ pw₂
    intro a b ha hb hab hba
    have sa := (mem₁ a).mp ha
    have sb := (mem₂ b).mp hb
    exact absurd (hV.trans w a b a sa sb sa hab hba) (hV.irrefl w a sa)
  rw [hl]
