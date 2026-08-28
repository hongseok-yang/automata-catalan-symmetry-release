/-
# Quadratic-time evaluation of scan-order SWR maps (`cor:srr-quadratic`)

Formalisation of Corollary `cor:srr-quadratic` (paper.tex;
proof in Appendix A.2) of "A Computational Obstruction to Swapping Area and Dinv": every SWR (= `WRP.IsSRR1`) map whose selection
and labelling are decided by a single left-to-right finite-state pass — the
choice at each position determined by the prefix ending there
(`PrefixPassData`) — is computable in deterministic time `O(n²)` and
logarithmic space.  The cost model is the multihead bounded-counter machine
`Multihead.MHC` of `thm:wrp-strict-below-logspace`, whose step-indexed run
relation carries an explicit run length; `srr_quadratic` produces a machine
with a verified `SpaceBound`, a `Computes`-characterisation, and a verified
quadratic bound `N ≤ D·(n+1)²` on the length of every halting run.

Σ is instantiated to `Step`, as everywhere in this development.

**Realisation of the paper's unit-cost comparisons.**  The paper's algorithm
performs one left-to-right scan per output letter, comparing each candidate
atom against the last-emitted atom and the best-so-far atom in `O(1)` by
maintaining running rank counters.  In this machine model the comparisons are
realised *exactly* by such running counters, kept as **signed differences**
between the running per-copy rank sums and the currently examined rank level:
the machine enumerates the `O(n)` possible rank values `v` in increasing
order and, inside each level, extracts the fiber in scan order by successive
best-so-far scans; each per-copy running rank is held in signed base-`2W`
form (sign and residue in the finite control, magnitude divided by `2W` in a
dedicated head), so a rank-equality comparison is a single head-coincidence
observation and each per-letter update moves each head at most one cell.
Every scan therefore costs `O(n)` machine steps, the number of scans is
`O(n)` (one per rank level plus one per output letter, the level-change costs
telescoping against the monotone ascent of the examined rank level), and the
total is quadratic — faithful to the paper's bound.  The machine uses `c = 0`
counters, so the logspace `SpaceBound` holds vacuously; all `O(log n)`-bit
registers are two-way heads.

**Contents.**
* `PrefixPassData` — the corollary's hypothesis on selection and labelling.
* `SRRQuadratic.Setup` — the destructured scan-order presentation data.
* Pure layer: the one-dimensional rank formula (`rank1_eq`), the rank
  magnitude bound, the order bridge `wrpOrd_iff`, and the sorted output
  `sortedPairs` with `isOutput_sorted`.
* Machine layer: the signed head-register arithmetic (`repAdd`), the machine
  `mach` with its phase structure, the verified run construction, and the
  step accounting.
* `srr_quadratic`, `srr_quadratic_isLogspaceMH` — the corollary.

Trust: axiom-clean except `SliceMSO.buchi` (used once, for the domain
sentence): `#print axioms srr_quadratic` reports exactly
`[propext, Classical.choice, Quot.sound, SliceMSO.buchi]`.
-/
import RequestProject.Multihead
import RequestProject.SRR1
import RequestProject.PrefixAdditiveRank
import RequestProject.WRPNonemptyRegular

open TwoDFT

/-- The paper's hypothesis "selection and labelling are decided by a single
left-to-right finite-state pass, so the choice at each position is determined
by the prefix ending there" (`cor:srr-quadratic`): a DFA `A` together with
per-copy readouts of selection and label from the state after reading the
prefix ending at the position (inclusive). -/
structure PrefixPassData {Gamma : Type} (P : WRP.Presentation Step Gamma) where
  A : SliceMSO.DetAuto Step
  selSet : Fin P.toPoly.K → A.Q → Bool
  labSet : Fin P.toPoly.K → A.Q → Gamma
  hsel : ∀ c w p, p < w.length →
    (P.toPoly.sel c w (fun _ => p) ↔ selSet c (A.stateBefore w (p+1)) = true)
  hlab : ∀ c w p, p < w.length → P.toPoly.sel c w (fun _ => p) →
    P.toPoly.label c w (fun _ => p) = labSet c (A.stateBefore w (p+1))

namespace SRRQuadratic

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma]

/-- All data of a scan-order (`IsSRR1`) presentation with a prefix-pass
selection/label oracle, destructured once and for all: the presentation, its
validity, `d = 1`, the scan order (`h1`, `dir`, `cord` and its strict-total-
order laws, and the characterisation `hord` of the tie-order), the prefix
pass `pp`, a deterministic acceptor `DA` for the domain (from
`SliceMSO.buchi`), and per-copy prefix-additive rank data `kap` (from
`isPrefixAdditiveRank_of_isRegularRankTerm`). -/
structure Setup (Gamma : Type) [Fintype Gamma] [DecidableEq Gamma] where
  P : WRP.Presentation Step Gamma
  hV : P.Valid
  hd1 : P.d = 1
  h1 : ∀ c, P.toPoly.arity c = 1
  dir : Bool
  cord : Fin P.toPoly.K → Fin P.toPoly.K → Prop
  cordIrr : ∀ c, ¬ cord c c
  cordTrans : ∀ x y z, cord x y → cord y z → cord x z
  cordTotal : ∀ x y, cord x y ∨ x = y ∨ cord y x
  hord : ∀ (w : List Step) (a b : P.toPoly.Atom),
    P.toPoly.atomOrd w a b ↔
      ((if dir then P.toPoly.pos1 h1 a < P.toPoly.pos1 h1 b
        else P.toPoly.pos1 h1 b < P.toPoly.pos1 h1 a)
        ∨ (P.toPoly.pos1 h1 a = P.toPoly.pos1 h1 b ∧ cord a.1 b.1))
  pp : PrefixPassData P
  DA : SliceMSO.DetAuto Step
  hDA : ∀ w, DA.accepts w ↔ P.toPoly.domain w
  kap : ∀ c, PrefixAdditiveRank Step P.d (P.toPoly.arity c)
  hkap : ∀ c w ī, P.rank c w ī = (kap c).eval w ī

variable (S : Setup Gamma)

/-- The number of copies. -/
abbrev Setup.K : ℕ := S.P.toPoly.K

/-- The (unique) argument index of a copy, at arity 1. -/
def idx (c : Fin S.K) : Fin (S.P.toPoly.arity c) :=
  ⟨0, by rw [S.h1 c]; exact Nat.one_pos⟩

/-- The (unique) rank dimension, at `d = 1`. -/
def dim : Fin S.P.d := ⟨0, by rw [S.hd1]; exact Nat.one_pos⟩

/-- The per-copy rank source (the copy's single prefix-additive source). -/
def src (c : Fin S.K) : RankSource Step S.P.d := (S.kap c).A (idx S c)

instance srcQFintype (c : Fin S.K) : Fintype (src S c).Q := (src S c).fintypeQ
instance ppQFintype : Fintype S.pp.A.Q := S.pp.A.fintypeQ
instance daQFintype : Fintype S.DA.Q := S.DA.fintypeQ

/-- The per-copy rank constant (at the unique dimension). -/
def c0v (c : Fin S.K) : ℤ := (S.kap c).c0 (dim S)

/-- The per-copy local correction table (at the unique dimension). -/
def locf (c : Fin S.K) (q : (src S c).Q) (a : Step) : ℤ :=
  (S.kap c).β (idx S c) q a (dim S)

/-- The per-copy transition weight (at the unique dimension). -/
def wf (c : Fin S.K) (q : (src S c).Q) (a : Step) : ℤ :=
  (src S c).ω q a (dim S)

/-- The one-dimensional rank of the atom `(c, p)` on `w`. -/
def rank1 (c : Fin S.K) (w : List Step) (p : ℕ) : ℤ :=
  S.P.rank c w (fun _ => p) (dim S)

/-- The per-copy prefix rank sum (at the unique dimension). -/
def prefS (c : Fin S.K) (w : List Step) (p : ℕ) : ℤ :=
  (src S c).prefixRank w p (dim S)

end SRRQuadratic

namespace SRRQuadratic

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-! ## The one-dimensional rank formula -/

/-- Every argument index of an arity-1 copy is `idx`. -/
theorem eq_idx (c : Fin S.K) (r : Fin (S.P.toPoly.arity c)) : r = idx S c := by
  have h : r.1 < S.P.toPoly.arity c := r.isLt
  have h2 := S.h1 c
  refine Fin.ext ?_
  rw [show (idx S c).1 = 0 from rfl]
  omega

/-- **The one-dimensional rank formula**: at arity 1 and `d = 1` the rank of
the atom `(c, p)` is the copy's constant plus its prefix rank sum plus the
local correction at `p`. -/
theorem rank1_eq (c : Fin S.K) (w : List Step) (p : ℕ) :
    rank1 S c w p = c0v S c + prefS S c w p
      + (w[p]?).elim 0 (fun a => locf S c ((src S c).stateBefore w p) a) := by
  rw [rank1, S.hkap c w (fun _ => p)]
  simp only [PrefixAdditiveRank.eval]
  rw [Finset.sum_eq_single_of_mem (idx S c) (Finset.mem_univ _)
    (fun b _ hb => absurd (eq_idx S c b) hb)]
  cases hw : w[p]? with
  | none => simp [c0v, prefS, src]
  | some a =>
      simp only [Option.elim_some]
      rw [show c0v S c = (S.kap c).c0 (dim S) from rfl]
      rw [show prefS S c w p = ((S.kap c).A (idx S c)).prefixRank w p (dim S) from rfl]
      rw [show locf S c ((src S c).stateBefore w p) a
        = (S.kap c).β (idx S c) (((S.kap c).A (idx S c)).stateBefore w p) a (dim S) from rfl]
      ring

/-! ## Magnitude bounds -/

/-- Per-copy magnitude bound on weights, corrections, and the constant. -/
def Wc (c : Fin S.K) : ℕ :=
  ((Finset.univ : Finset ((src S c).Q × Step)).sup
      (fun qa => (wf S c qa.1 qa.2).natAbs)) ⊔
  ((Finset.univ : Finset ((src S c).Q × Step)).sup
      (fun qa => (locf S c qa.1 qa.2).natAbs)) ⊔
  (c0v S c).natAbs

/-- The global magnitude bound (`≥ 1`). -/
def bigW : ℕ := (Finset.univ : Finset (Fin S.K)).sup (fun c => Wc S c) + 1

theorem bigW_pos : 0 < bigW S := Nat.succ_pos _

theorem Wc_le_bigW (c : Fin S.K) : Wc S c ≤ bigW S :=
  le_trans (Finset.le_sup (Finset.mem_univ c)) (Nat.le_succ _)

theorem wf_abs_le (c : Fin S.K) (q : (src S c).Q) (a : Step) :
    (wf S c q a).natAbs ≤ bigW S :=
  le_trans (le_trans (Finset.le_sup (f := fun qa : (src S c).Q × Step =>
      (wf S c qa.1 qa.2).natAbs) (Finset.mem_univ (q, a)))
    (le_trans le_sup_left le_sup_left)) (Wc_le_bigW S c)

theorem locf_abs_le (c : Fin S.K) (q : (src S c).Q) (a : Step) :
    (locf S c q a).natAbs ≤ bigW S :=
  le_trans (le_trans (Finset.le_sup (f := fun qa : (src S c).Q × Step =>
      (locf S c qa.1 qa.2).natAbs) (Finset.mem_univ (q, a)))
    (le_trans le_sup_right le_sup_left)) (Wc_le_bigW S c)

theorem c0v_abs_le (c : Fin S.K) : (c0v S c).natAbs ≤ bigW S :=
  le_trans (le_trans le_sup_right (Wc_le_bigW S c)) (le_refl _)

/-- Two-sided bound from a `natAbs` bound. -/
theorem two_sided {z : ℤ} {m : ℕ} (h : z.natAbs ≤ m) : -(m : ℤ) ≤ z ∧ z ≤ m := by
  omega

/-- The prefix rank sum is bounded by `W·p`. -/
theorem prefS_bound (c : Fin S.K) (w : List Step) (p : ℕ) :
    -((bigW S : ℤ) * p) ≤ prefS S c w p ∧ prefS S c w p ≤ (bigW S : ℤ) * p := by
  have hterm : ∀ j ∈ Finset.range p,
      -((bigW S : ℤ)) ≤ (w[j]?).elim 0 (fun a => (src S c).ω ((src S c).stateBefore w j) a (dim S))
      ∧ (w[j]?).elim 0 (fun a => (src S c).ω ((src S c).stateBefore w j) a (dim S)) ≤ (bigW S : ℤ) := by
    intro j _
    cases hw : w[j]? with
    | none =>
        simp only [Option.elim_none]
        constructor <;> [exact neg_nonpos_of_nonneg (Int.natCast_nonneg _); exact Int.natCast_nonneg _]
    | some a =>
        simp only [Option.elim_some]
        exact two_sided (wf_abs_le S c ((src S c).stateBefore w j) a)
  unfold prefS RankSource.prefixRank
  constructor
  · calc -((bigW S : ℤ) * p) = ∑ _j ∈ Finset.range p, -(bigW S : ℤ) := by
          rw [Finset.sum_const, Finset.card_range]; ring
      _ ≤ _ := Finset.sum_le_sum (fun j hj => (hterm j hj).1)
  · calc _ ≤ ∑ _j ∈ Finset.range p, (bigW S : ℤ) :=
          Finset.sum_le_sum (fun j hj => (hterm j hj).2)
      _ = (bigW S : ℤ) * p := by rw [Finset.sum_const, Finset.card_range]; ring

/-- **The rank magnitude bound**: `|rank1 c w p| ≤ W·(p + 2)`. -/
theorem rank1_bound (c : Fin S.K) (w : List Step) (p : ℕ) :
    -((bigW S : ℤ) * (p + 2)) ≤ rank1 S c w p ∧ rank1 S c w p ≤ (bigW S : ℤ) * (p + 2) := by
  rw [rank1_eq]
  obtain ⟨hp1, hp2⟩ := prefS_bound S c w p
  obtain ⟨hc1, hc2⟩ := two_sided (c0v_abs_le S c)
  have hloc : -((bigW S : ℤ)) ≤ (w[p]?).elim 0 (fun a => locf S c ((src S c).stateBefore w p) a)
      ∧ (w[p]?).elim 0 (fun a => locf S c ((src S c).stateBefore w p) a) ≤ (bigW S : ℤ) := by
    cases hw : w[p]? with
    | none =>
        simp only [Option.elim_none]
        constructor <;> [exact neg_nonpos_of_nonneg (Int.natCast_nonneg _); exact Int.natCast_nonneg _]
    | some a =>
        simp only [Option.elim_some]
        exact two_sided (locf_abs_le S c ((src S c).stateBefore w p) a)
  constructor <;> nlinarith [hloc.1, hloc.2]

end SRRQuadratic

namespace SRRQuadratic

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-! ## Atoms as (copy, position) pairs; the order bridge -/

/-- The arity-1 atom with copy `c` and (single) position `p`. -/
def mkAtom (c : Fin S.K) (p : ℕ) : S.P.toPoly.Atom := ⟨c, fun _ => p⟩

@[simp] theorem pos1_mkAtom (c : Fin S.K) (p : ℕ) :
    S.P.toPoly.pos1 S.h1 (mkAtom S c p) = p := rfl

@[simp] theorem mkAtom_fst (c : Fin S.K) (p : ℕ) : (mkAtom S c p).1 = c := rfl

/-- Every atom of an arity-1 presentation is `mkAtom` of its copy and `pos1`. -/
theorem atom_eq_mkAtom (a : S.P.toPoly.Atom) :
    a = mkAtom S a.1 (S.P.toPoly.pos1 S.h1 a) := by
  cases a with
  | mk c f =>
      exact congrArg (Sigma.mk c) (funext fun t => by rw [eq_idx S c t]; rfl)

theorem mkAtom_inj {c c' : Fin S.K} {p p' : ℕ}
    (h : mkAtom S c p = mkAtom S c' p') : c = c' ∧ p = p' := by
  obtain ⟨h1, h2⟩ := Sigma.mk.injEq .. ▸ h
  refine ⟨h1, ?_⟩
  subst h1
  have := congrFun (eq_of_heq h2) (idx S c)
  exact this

/-- Selection of the pair `(c, p)`. -/
def selP (w : List Step) (c : Fin S.K) (p : ℕ) : Prop :=
  S.P.toPoly.selectedAtom w (mkAtom S c p)

/-- **The prefix-pass characterisation of selection.** -/
theorem selP_iff (w : List Step) (c : Fin S.K) (p : ℕ) :
    selP S w c p ↔
      p < w.length ∧ S.pp.selSet c (S.pp.A.stateBefore w (p+1)) = true := by
  unfold selP Polyreg.Presentation.selectedAtom
  constructor
  · rintro ⟨hval, hsel⟩
    have hp : p < w.length := hval (idx S c)
    exact ⟨hp, (S.pp.hsel c w p hp).mp hsel⟩
  · rintro ⟨hp, hsel⟩
    exact ⟨fun _ => hp, (S.pp.hsel c w p hp).mpr hsel⟩

/-- **The prefix-pass characterisation of the label.** -/
theorem labelOf_eq (w : List Step) (c : Fin S.K) (p : ℕ) (h : selP S w c p) :
    S.P.toPoly.labelOf w (mkAtom S c p)
      = S.pp.labSet c (S.pp.A.stateBefore w (p+1)) := by
  have hp : p < w.length := ((selP_iff S w c p).mp h).1
  exact S.pp.hlab c w p hp h.2

/-- The scan tie-order on pairs: by position along `dir`, ties by `cord`. -/
def TieLt (x y : Fin S.K × ℕ) : Prop :=
  (if S.dir then x.2 < y.2 else y.2 < x.2) ∨ (x.2 = y.2 ∧ S.cord x.1 y.1)

/-- The full output order on pairs: by rank, ties by the scan tie-order. -/
def keyLt (w : List Step) (x y : Fin S.K × ℕ) : Prop :=
  rank1 S x.1 w x.2 < rank1 S y.1 w y.2 ∨
    (rank1 S x.1 w x.2 = rank1 S y.1 w y.2 ∧ TieLt S x y)

theorem tieLt_irrefl (x : Fin S.K × ℕ) : ¬ TieLt S x x := by
  rintro (h | ⟨-, h⟩)
  · split at h <;> omega
  · exact S.cordIrr _ h

theorem tieLt_trans {x y z : Fin S.K × ℕ}
    (h1 : TieLt S x y) (h2 : TieLt S y z) : TieLt S x z := by
  rcases h1 with h1 | ⟨e1, c1⟩ <;> rcases h2 with h2 | ⟨e2, c2⟩
  · left; split at h1 <;> split at h2 <;> split <;> simp_all <;> omega
  · left; rw [← e2]; exact h1
  · left; rw [e1]; exact h2
  · exact Or.inr ⟨e1.trans e2, S.cordTrans _ _ _ c1 c2⟩

theorem tieLt_total (x y : Fin S.K × ℕ) : TieLt S x y ∨ x = y ∨ TieLt S y x := by
  rcases Nat.lt_trichotomy x.2 y.2 with h | h | h
  · cases hd : S.dir
    · exact Or.inr (Or.inr (Or.inl (by rw [hd]; simpa using h)))
    · exact Or.inl (Or.inl (by rw [hd]; simpa using h))
  · rcases S.cordTotal x.1 y.1 with hc | hc | hc
    · exact Or.inl (Or.inr ⟨h, hc⟩)
    · exact Or.inr (Or.inl (Prod.ext hc h))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, hc⟩))
  · cases hd : S.dir
    · exact Or.inl (Or.inl (by rw [hd]; simpa using h))
    · exact Or.inr (Or.inr (Or.inl (by rw [hd]; simpa using h)))

theorem tieLt_asymm {x y : Fin S.K × ℕ} (h : TieLt S x y) : ¬ TieLt S y x :=
  fun h' => tieLt_irrefl S x (tieLt_trans S h h')

theorem keyLt_trans {w : List Step} {x y z : Fin S.K × ℕ}
    (h1 : keyLt S w x y) (h2 : keyLt S w y z) : keyLt S w x z := by
  rcases h1 with h1 | ⟨e1, t1⟩ <;> rcases h2 with h2 | ⟨e2, t2⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (e2 ▸ h1)
  · exact Or.inl (e1 ▸ h2)
  · exact Or.inr ⟨e1.trans e2, tieLt_trans S t1 t2⟩

theorem keyLt_irrefl {w : List Step} (x : Fin S.K × ℕ) : ¬ keyLt S w x x := by
  rintro (h | ⟨-, h⟩)
  · omega
  · exact tieLt_irrefl S x h

theorem keyLt_asymm {w : List Step} {x y : Fin S.K × ℕ}
    (h : keyLt S w x y) : ¬ keyLt S w y x :=
  fun h' => keyLt_irrefl S x (keyLt_trans S h h')

theorem keyLt_total (w : List Step) (x y : Fin S.K × ℕ) :
    keyLt S w x y ∨ x = y ∨ keyLt S w y x := by
  rcases Int.lt_trichotomy (rank1 S x.1 w x.2) (rank1 S y.1 w y.2) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases tieLt_total S x y with ht | ht | ht
    · exact Or.inl (Or.inr ⟨h, ht⟩)
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, ht⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- Every dimension index is `dim`, at `d = 1`. -/
theorem eq_dim (i : Fin S.P.d) : i = dim S := by
  have h : i.1 < S.P.d := i.isLt
  have h2 := S.hd1
  refine Fin.ext ?_
  rw [show (dim S).1 = 0 from rfl]
  omega

/-- The lexicographic rank order collapses to a single `ℤ` comparison. -/
theorem lexLt_iff (u v : Fin S.P.d → ℤ) :
    WRP.lexLt u v ↔ u (dim S) < v (dim S) := by
  constructor
  · rintro ⟨i, -, hlt⟩
    rwa [eq_dim S i] at hlt
  · intro h
    refine ⟨dim S, fun j hj => ?_, h⟩
    exact absurd (Fin.lt_def.mp hj) (by rw [show (dim S).1 = 0 from rfl]; omega)

/-- The tie-order bridge: `atomOrd` on `mkAtom`s is `TieLt`. -/
theorem atomOrd_iff (w : List Step) (x y : Fin S.K × ℕ) :
    S.P.toPoly.atomOrd w (mkAtom S x.1 x.2) (mkAtom S y.1 y.2) ↔ TieLt S x y := by
  rw [S.hord]
  simp only [pos1_mkAtom, mkAtom_fst]
  exact Iff.rfl

/-- **The order bridge** (`wrpOrd_iff`): the WRP output order on arity-1
atoms is `keyLt` on the corresponding pairs. -/
theorem wrpOrd_iff (w : List Step) (x y : Fin S.K × ℕ) :
    S.P.wrpOrd w (mkAtom S x.1 x.2) (mkAtom S y.1 y.2) ↔ keyLt S w x y := by
  unfold WRP.Presentation.wrpOrd keyLt
  apply or_congr
  · exact lexLt_iff S _ _
  · apply and_congr
    · exact ⟨fun h => congrFun h (dim S),
        fun h => funext fun i => by rw [eq_dim S i]; exact h⟩
    · exact atomOrd_iff S w x y

/-- A `cord`-sorted duplicate-free enumeration of the copies exists. -/
theorem cordList_spec :
    ∃ l : List (Fin S.K), l.Nodup ∧ (∀ c, c ∈ l) ∧ l.Pairwise S.cord := by
  obtain ⟨l, hnd, hmem, hpw⟩ := WRPNonemptyRegular.exists_sorted_of_strictTotal S.cord
    (List.finRange S.K) (fun a _ => S.cordIrr a) (fun a _ b _ c _ => S.cordTrans a b c)
    (fun a _ b _ => S.cordTotal a b)
  exact ⟨l, hnd, fun c => (hmem c).mpr (List.mem_finRange c), hpw⟩

/-- The `cord`-sorted enumeration of the copies. -/
noncomputable def cordList : List (Fin S.K) := Classical.choose (cordList_spec S)

theorem cordList_nodup : (cordList S).Nodup := (Classical.choose_spec (cordList_spec S)).1
theorem cordList_mem (c : Fin S.K) : c ∈ cordList S :=
  (Classical.choose_spec (cordList_spec S)).2.1 c
theorem cordList_sorted : (cordList S).Pairwise S.cord :=
  (Classical.choose_spec (cordList_spec S)).2.2

end SRRQuadratic


namespace SRRQuadratic

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-! ## The sorted output -/

/-- The base of the signed head-register representation (`2W + 1`): strictly
larger than every per-step increment, so the head moves at most one cell per
update and the canonical form (zero has sign `+`) is preserved. -/
def Wtot : ℕ := 2 * bigW S + 1

theorem Wtot_pos : 0 < Wtot S := by
  have := bigW_pos S
  unfold Wtot
  omega

/-- The pair `(c, p)` is selected on `w` with rank exactly `v`. -/
def QSel (w : List Step) (v : ℤ) (c : Fin S.K) (p : ℕ) : Prop :=
  selP S w c p ∧ rank1 S c w p = v

open Classical in
/-- Boolean form of `QSel` (classically decided). -/
noncomputable def qselB (w : List Step) (v : ℤ) (p : ℕ) (c : Fin S.K) : Bool :=
  decide (QSel S w v c p)

theorem qselB_iff (w : List Step) (v : ℤ) (p : ℕ) (c : Fin S.K) :
    qselB S w v p c = true ↔ QSel S w v c p := by
  unfold qselB
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- Positions `0, …, n−1` in scan order (`dir = true`: ascending). -/
def posList (n : ℕ) : List ℕ :=
  if S.dir then List.range n else (List.range n).reverse

theorem mem_posList (n p : ℕ) : p ∈ posList S n ↔ p < n := by
  unfold posList
  split <;> simp

theorem posList_pairwise (n : ℕ) :
    (posList S n).Pairwise (fun p p' => if S.dir then p < p' else p' < p) := by
  unfold posList
  cases hd : S.dir
  · rw [if_neg (by simp), List.pairwise_reverse]
    exact List.pairwise_lt_range.imp (fun {a b} h => by simpa using h)
  · rw [if_pos rfl]
    exact List.pairwise_lt_range.imp (fun {a b} h => by simpa using h)

/-- The selected rank-`v` pairs at position `p`, in `cord` order. -/
noncomputable def cellList (w : List Step) (v : ℤ) (p : ℕ) : List (Fin S.K × ℕ) :=
  ((cordList S).filter (qselB S w v p)).map (fun c => (c, p))

theorem mem_cellList (w : List Step) (v : ℤ) (p : ℕ) (x : Fin S.K × ℕ) :
    x ∈ cellList S w v p ↔ x.2 = p ∧ QSel S w v x.1 p := by
  unfold cellList
  rw [List.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨rfl, (qselB_iff S w v p c).mp (List.of_mem_filter hc)⟩
  · rintro ⟨hp, hq⟩
    refine ⟨x.1, List.mem_filter.mpr
      ⟨cordList_mem S x.1, (qselB_iff S w v p x.1).mpr hq⟩, ?_⟩
    exact Prod.ext rfl hp.symm

theorem cellList_pairwise (w : List Step) (v : ℤ) (p : ℕ) :
    (cellList S w v p).Pairwise (TieLt S) := by
  unfold cellList
  rw [List.pairwise_map]
  exact ((cordList_sorted S).filter _).imp (fun {a b} h => Or.inr ⟨rfl, h⟩)

/-- The rank-`v` fiber of `w`, in scan-tie order. -/
noncomputable def fiber (w : List Step) (v : ℤ) : List (Fin S.K × ℕ) :=
  (posList S w.length).flatMap (fun p => cellList S w v p)

theorem mem_fiber (w : List Step) (v : ℤ) (x : Fin S.K × ℕ) :
    x ∈ fiber S w v ↔ x.2 < w.length ∧ QSel S w v x.1 x.2 := by
  unfold fiber
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨rfl, hq⟩ := (mem_cellList S w v p x).mp hx
    exact ⟨(mem_posList S _ _).mp hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact ⟨x.2, (mem_posList S _ _).mpr hp, (mem_cellList S w v x.2 x).mpr ⟨rfl, hq⟩⟩

theorem fiber_pairwise (w : List Step) (v : ℤ) :
    (fiber S w v).Pairwise (TieLt S) := by
  unfold fiber
  rw [List.pairwise_flatMap]
  refine ⟨fun p _ => cellList_pairwise S w v p, ?_⟩
  refine (posList_pairwise S w.length).imp ?_
  intro p p' hpp x hx y hy
  obtain ⟨hxp, -⟩ := (mem_cellList S w v p x).mp hx
  obtain ⟨hyp, -⟩ := (mem_cellList S w v p' y).mp hy
  exact Or.inl (by rw [hxp, hyp]; exact hpp)

theorem fiber_rank (w : List Step) (v : ℤ) (x : Fin S.K × ℕ) (hx : x ∈ fiber S w v) :
    rank1 S x.1 w x.2 = v := ((mem_fiber S w v x).mp hx).2.2

/-- The number of enumerated rank levels. -/
def numVals (n : ℕ) : ℕ := 2 * Wtot S * (n + 2) - 1

/-- The least enumerated rank level `−(2W(n+2) − 1)`. -/
def vmin (n : ℕ) : ℤ := -((Wtot S : ℤ) * (n + 2) - 1)

/-- The enumerated rank levels, ascending. -/
noncomputable def valueList (n : ℕ) : List ℤ :=
  (List.range (numVals S n)).map (fun t : ℕ => vmin S n + (t : ℤ))

theorem mem_valueList (n : ℕ) (v : ℤ) :
    v ∈ valueList S n ↔ vmin S n ≤ v ∧ v < vmin S n + numVals S n := by
  unfold valueList
  rw [List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [List.mem_range] at ht
    have h0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    have h1 : (t : ℤ) < (numVals S n : ℤ) := by exact_mod_cast ht
    constructor
    · linarith
    · linarith
  · rintro ⟨h1, h2⟩
    have hnn : (0 : ℤ) ≤ v - vmin S n := by linarith
    have hcast : ((v - vmin S n).toNat : ℤ) = v - vmin S n := Int.toNat_of_nonneg hnn
    refine ⟨(v - vmin S n).toNat, List.mem_range.mpr ?_, ?_⟩
    · have hlt : v - vmin S n < (numVals S n : ℤ) := by linarith
      rw [← hcast] at hlt
      exact_mod_cast hlt
    · rw [hcast]
      ring

theorem valueList_pairwise (n : ℕ) : (valueList S n).Pairwise (· < ·) := by
  unfold valueList
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp (fun {a b} h => ?_)
  have : (a : ℤ) < (b : ℤ) := by exact_mod_cast h
  linarith

/-- Every in-range rank value is an enumerated level. -/
theorem rank1_mem_valueList (w : List Step) (c : Fin S.K) (p : ℕ) (hp : p < w.length) :
    rank1 S c w p ∈ valueList S w.length := by
  obtain ⟨h1, h2⟩ := rank1_bound S c w p
  have hW : (1 : ℤ) ≤ (bigW S : ℤ) := by exact_mod_cast bigW_pos S
  have hple : (p : ℤ) + 2 ≤ (w.length : ℤ) + 2 := by
    have : (p : ℤ) < (w.length : ℤ) := by exact_mod_cast hp
    omega
  have hA2 : (bigW S : ℤ) * (p + 2) ≤ (bigW S : ℤ) * (w.length + 2) :=
    mul_le_mul_of_nonneg_left hple (by omega)
  have hA1 : (1 : ℤ) ≤ (bigW S : ℤ) * (w.length + 2) := by nlinarith
  rw [mem_valueList]
  have hWt : (Wtot S : ℤ) * ((w.length : ℤ) + 2)
      = 2 * ((bigW S : ℤ) * (w.length + 2)) + ((w.length : ℤ) + 2) := by
    unfold Wtot
    push_cast
    ring
  have hv : vmin S w.length = -((Wtot S : ℤ) * ((w.length : ℤ) + 2) - 1) := rfl
  have hpos : 0 < 2 * Wtot S * (w.length + 2) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (Wtot_pos S)) (by omega)
  have hnv : (numVals S w.length : ℤ) = 2 * ((Wtot S : ℤ) * ((w.length : ℤ) + 2)) - 1 := by
    unfold numVals
    rw [Nat.cast_sub hpos]
    push_cast
    ring
  have hn2 : (2 : ℤ) ≤ (w.length : ℤ) + 2 := by
    have : (0 : ℤ) ≤ (w.length : ℤ) := Int.natCast_nonneg _
    omega
  rw [hv, hnv]
  constructor
  · linarith
  · linarith

end SRRQuadratic

namespace SRRQuadratic

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- A list pairwise-ordered by an irreflexive relation has no duplicates. -/
private theorem pairwise_nodup {α : Type*} {r : α → α → Prop} (hi : ∀ a, ¬ r a a) :
    ∀ {l : List α}, l.Pairwise r → l.Nodup := by
  intro l h
  induction h with
  | nil => exact List.nodup_nil
  | cons hh _ ih =>
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih⟩
      exact hi _ (hh _ hmem)

/-- The sorted output pairs: rank levels ascending, fibers in scan-tie order. -/
noncomputable def sortedPairs (w : List Step) : List (Fin S.K × ℕ) :=
  (valueList S w.length).flatMap (fun v => fiber S w v)

theorem mem_sortedPairs (w : List Step) (x : Fin S.K × ℕ) :
    x ∈ sortedPairs S w ↔ selP S w x.1 x.2 := by
  unfold sortedPairs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨v, -, hx⟩
    exact ((mem_fiber S w v x).mp hx).2.1
  · intro hsel
    have hp : x.2 < w.length := ((selP_iff S w x.1 x.2).mp hsel).1
    exact ⟨rank1 S x.1 w x.2, rank1_mem_valueList S w x.1 x.2 hp,
      (mem_fiber S w _ x).mpr ⟨hp, hsel, rfl⟩⟩

theorem sortedPairs_pairwise (w : List Step) :
    (sortedPairs S w).Pairwise (keyLt S w) := by
  unfold sortedPairs
  rw [List.pairwise_flatMap]
  constructor
  · intro v _
    refine (fiber_pairwise S w v).imp_of_mem ?_
    intro x y hx hy ht
    exact Or.inr ⟨by rw [fiber_rank S w v x hx, fiber_rank S w v y hy], ht⟩
  · refine (valueList_pairwise S w.length).imp_of_mem ?_
    intro v v' _ _ hvv x hx y hy
    exact Or.inl (by rw [fiber_rank S w v x hx, fiber_rank S w v' y hy]; exact hvv)

theorem sortedPairs_nodup (w : List Step) : (sortedPairs S w).Nodup :=
  pairwise_nodup (fun x => keyLt_irrefl S x) (sortedPairs_pairwise S w)

theorem mkAtom_injective :
    Function.Injective (fun x : Fin S.K × ℕ => mkAtom S x.1 x.2) := by
  intro x y h
  obtain ⟨h1, h2⟩ := mkAtom_inj S h
  exact Prod.ext h1 h2

/-- The declarative output of the presentation on `w`, as labels of the
sorted pairs. -/
noncomputable def outw (w : List Step) : List Gamma :=
  (sortedPairs S w).map (fun x => S.P.toPoly.labelOf w (mkAtom S x.1 x.2))

/-- **The sorted pairs realise the declarative output** (`P.IsOutput`). -/
theorem isOutput_outw (w : List Step) : S.P.IsOutput w (outw S w) := by
  refine ⟨(sortedPairs S w).map (fun x => mkAtom S x.1 x.2), ?_, ?_, ?_, ?_⟩
  · exact List.Nodup.map (mkAtom_injective S) (sortedPairs_nodup S w)
  · intro a
    rw [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_sortedPairs S w x).mp hx
    · intro hsel
      refine ⟨(a.1, S.P.toPoly.pos1 S.h1 a), ?_, (atom_eq_mkAtom S a).symm⟩
      rw [mem_sortedPairs]
      show S.P.toPoly.selectedAtom w (mkAtom S a.1 (S.P.toPoly.pos1 S.h1 a))
      rw [← atom_eq_mkAtom S a]
      exact hsel
  · rw [List.pairwise_map]
    exact (sortedPairs_pairwise S w).imp (fun {x y} h => (wrpOrd_iff S w x y).mpr h)
  · rw [List.map_map]
    rfl

/-! ## The best-so-far recursion (the machine's per-scan decision, purely) -/

/-- The gate "strictly tie-after the last emitted pair" (`none`: no gate). -/
def Lgate (L : Option (Fin S.K × ℕ)) (x : Fin S.K × ℕ) : Prop :=
  match L with
  | none => True
  | some l => TieLt S l x

/-- Qualification in a level-`v` scan with last-emitted `L`. -/
def Qual (w : List Step) (v : ℤ) (L : Option (Fin S.K × ℕ))
    (x : Fin S.K × ℕ) : Prop :=
  QSel S w v x.1 x.2 ∧ Lgate S L x

open Classical in
/-- Boolean form of `Qual` at cell `p` (classically decided). -/
noncomputable def qualB (w : List Step) (v : ℤ) (L : Option (Fin S.K × ℕ))
    (p : ℕ) (c : Fin S.K) : Bool :=
  decide (Qual S w v L (c, p))

theorem qualB_iff (w : List Step) (v : ℤ) (L : Option (Fin S.K × ℕ))
    (p : ℕ) (c : Fin S.K) : qualB S w v L p c = true ↔ Qual S w v L (c, p) := by
  unfold qualB
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- The `cord`-least qualifying copy at cell `p`. -/
noncomputable def bestAt (w : List Step) (v : ℤ) (L : Option (Fin S.K × ℕ))
    (p : ℕ) : Option (Fin S.K) :=
  ((cordList S).filter (qualB S w v L p)).head?

/-- Merge the standing best with the cell winner: `dir = true` keeps the
earlier position, `dir = false` takes the later. -/
def mergeB (b : Option (Fin S.K × ℕ)) (cand : Option (Fin S.K)) (p : ℕ) :
    Option (Fin S.K × ℕ) :=
  match b, cand with
  | b, none => b
  | none, some c => some (c, p)
  | some b, some c => if S.dir then some b else some (c, p)

/-- The best-so-far after scanning cells `< j`. -/
noncomputable def bestUpTo (w : List Step) (v : ℤ) (L : Option (Fin S.K × ℕ)) :
    ℕ → Option (Fin S.K × ℕ)
  | 0 => none
  | j+1 => mergeB S (bestUpTo w v L j) (bestAt S w v L j) j

/-- Tie-minimality of an optional pair over a set of pairs. -/
def IsTieMin (Xset : (Fin S.K × ℕ) → Prop) : Option (Fin S.K × ℕ) → Prop
  | none => ∀ x, ¬ Xset x
  | some b => Xset b ∧ ∀ x, Xset x → x = b ∨ TieLt S b x

theorem isTieMin_unique {Xset : (Fin S.K × ℕ) → Prop} {o₁ o₂ : Option (Fin S.K × ℕ)}
    (h₁ : IsTieMin S Xset o₁) (h₂ : IsTieMin S Xset o₂) : o₁ = o₂ := by
  cases o₁ with
  | none =>
      cases o₂ with
      | none => rfl
      | some b => exact absurd h₂.1 (h₁ b)
  | some b =>
      cases o₂ with
      | none => exact absurd h₁.1 (h₂ b)
      | some b' =>
          rcases h₁.2 b' h₂.1 with h | h
          · rw [h]
          · rcases h₂.2 b h₁.1 with h' | h'
            · rw [h']
            · exact absurd h' (tieLt_asymm S h)

end SRRQuadratic

namespace SRRQuadratic

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

theorem isTieMin_congr {Xset Yset : (Fin S.K × ℕ) → Prop}
    (h : ∀ x, Xset x ↔ Yset x) {o : Option (Fin S.K × ℕ)}
    (ho : IsTieMin S Xset o) : IsTieMin S Yset o := by
  cases o with
  | none => exact fun x hx => ho x ((h x).mpr hx)
  | some b => exact ⟨(h b).mp ho.1, fun x hx => ho.2 x ((h x).mpr hx)⟩

theorem bestAt_none_iff (w : List Step) (v : ℤ) (L : Option (Fin S.K × ℕ)) (p : ℕ) :
    bestAt S w v L p = none ↔ ∀ c, ¬ Qual S w v L (c, p) := by
  unfold bestAt
  rw [List.head?_eq_none_iff]
  constructor
  · intro h c hq
    have hmem : c ∈ (cordList S).filter (qualB S w v L p) :=
      List.mem_filter.mpr ⟨cordList_mem S c, (qualB_iff S w v L p c).mpr hq⟩
    rw [h] at hmem
    exact absurd hmem List.not_mem_nil
  · intro h
    rw [List.filter_eq_nil_iff]
    exact fun c _ hq => h c ((qualB_iff S w v L p c).mp hq)

theorem bestAt_some (w : List Step) (v : ℤ) (L : Option (Fin S.K × ℕ)) (p : ℕ)
    (c : Fin S.K) (h : bestAt S w v L p = some c) :
    Qual S w v L (c, p) ∧ ∀ c', Qual S w v L (c', p) → c' = c ∨ S.cord c c' := by
  unfold bestAt at h
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp h
  have hcmem : c ∈ (cordList S).filter (qualB S w v L p) := by
    rw [hys]
    exact List.mem_cons_self ..
  have hq : Qual S w v L (c, p) :=
    (qualB_iff S w v L p c).mp (List.of_mem_filter hcmem)
  refine ⟨hq, fun c' hq' => ?_⟩
  have h1 : c' ∈ (cordList S).filter (qualB S w v L p) :=
    List.mem_filter.mpr ⟨cordList_mem S c', (qualB_iff S w v L p c').mpr hq'⟩
  rw [hys] at h1
  rcases List.mem_cons.mp h1 with rfl | h1
  · exact Or.inl rfl
  · have hpw : (c :: ys).Pairwise S.cord := hys ▸ ((cordList_sorted S).filter _)
    exact Or.inr ((List.pairwise_cons.mp hpw).1 c' h1)

/-- **The best-so-far recursion is correct**: `bestUpTo j` is the tie-least
qualifying pair among positions `< j`. -/
theorem bestUpTo_spec (w : List Step) (v : ℤ) (L : Option (Fin S.K × ℕ)) :
    ∀ j, IsTieMin S (fun x => Qual S w v L x ∧ x.2 < j) (bestUpTo S w v L j) := by
  intro j
  induction j with
  | zero => exact fun x hx => absurd hx.2 (Nat.not_lt_zero _)
  | succ j ih =>
      show IsTieMin S _ (mergeB S (bestUpTo S w v L j) (bestAt S w v L j) j)
      cases hc : bestAt S w v L j with
      | none =>
          have hnoc := (bestAt_none_iff S w v L j).mp hc
          have hred : mergeB S (bestUpTo S w v L j) none j = bestUpTo S w v L j := by
            cases bestUpTo S w v L j <;> rfl
          rw [hred]
          refine isTieMin_congr S (fun x => ?_) ih
          constructor
          · rintro ⟨hq, hlt⟩
            exact ⟨hq, by omega⟩
          · rintro ⟨hq, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
            · exact ⟨hq, h⟩
            · exfalso
              apply hnoc x.1
              have : x = (x.1, j) := Prod.ext rfl h
              rwa [this] at hq
      | some c =>
          obtain ⟨hqc, hminc⟩ := bestAt_some S w v L j c hc
          cases hb : bestUpTo S w v L j with
          | none =>
              have hnob : ∀ x, ¬ (Qual S w v L x ∧ x.2 < j) := by
                rw [hb] at ih
                exact ih
              show IsTieMin S _ (some (c, j))
              refine ⟨⟨hqc, Nat.lt_succ_self j⟩, fun x hx => ?_⟩
              obtain ⟨hxQ, hxlt⟩ := hx
              have hxj : x.2 = j := by
                rcases Nat.lt_succ_iff_lt_or_eq.mp hxlt with h | h
                · exact absurd ⟨hxQ, h⟩ (hnob x)
                · exact h
              have hxq : Qual S w v L (x.1, j) := by
                have hxx : x = (x.1, j) := Prod.ext rfl hxj
                rwa [hxx] at hxQ
              rcases hminc x.1 hxq with h | h
              · exact Or.inl (Prod.ext h hxj)
              · exact Or.inr (Or.inr ⟨(by omega : (c, j).2 = x.2), h⟩)
          | some b =>
              rw [hb] at ih
              obtain ⟨⟨hqb, hbj⟩, hminb⟩ := ih
              show IsTieMin S _ (if S.dir then some b else some (c, j))
              cases hd : S.dir
              · rw [if_neg (by simp)]
                refine ⟨⟨hqc, Nat.lt_succ_self j⟩, fun x hx => ?_⟩
                obtain ⟨hxQ, hxlt⟩ := hx
                rcases Nat.lt_succ_iff_lt_or_eq.mp hxlt with h | h
                · refine Or.inr (Or.inl ?_)
                  rw [if_neg (by rw [hd]; simp)]
                  omega
                · have hxq : Qual S w v L (x.1, j) := by
                    have hxx : x = (x.1, j) := Prod.ext rfl h
                    rwa [hxx] at hxQ
                  rcases hminc x.1 hxq with h' | h'
                  · exact Or.inl (Prod.ext h' h)
                  · exact Or.inr (Or.inr ⟨(by omega : (c, j).2 = x.2), h'⟩)
              · rw [if_pos rfl]
                refine ⟨⟨hqb, by omega⟩, fun x hx => ?_⟩
                obtain ⟨hxQ, hxlt⟩ := hx
                rcases Nat.lt_succ_iff_lt_or_eq.mp hxlt with h | h
                · exact hminb x ⟨hxQ, h⟩
                · refine Or.inr (Or.inl ?_)
                  rw [if_pos hd]
                  omega

end SRRQuadratic

namespace SRRQuadratic

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- The condition "`L` is the predecessor of the `k`-th fiber element": `L` is
`none` for `k = 0`, and the `(k−1)`-st fiber element otherwise. -/
def LPred (w : List Step) (v : ℤ) (k : ℕ) (L : Option (Fin S.K × ℕ)) : Prop :=
  (k = 0 ∧ L = none) ∨
    ∃ hk : k - 1 < (fiber S w v).length, k ≠ 0 ∧ L = some ((fiber S w v)[k-1])

/-- **The successor lemma**: a full scan with gate `L` (the predecessor of
the `k`-th fiber element) finds exactly the `k`-th fiber element (`none`
when the fiber is exhausted). -/
theorem bestUpTo_at_end (w : List Step) (v : ℤ) (k : ℕ)
    (L : Option (Fin S.K × ℕ)) (hL : LPred S w v k L) :
    bestUpTo S w v L w.length = (fiber S w v)[k]? := by
  have hklen : k ≤ (fiber S w v).length := by
    rcases hL with ⟨rfl, -⟩ | ⟨hk, hne, -⟩
    · exact Nat.zero_le _
    · omega
  refine isTieMin_unique S (bestUpTo_spec S w v L w.length) ?_
  have hset : ∀ x, (Qual S w v L x ∧ x.2 < w.length) ↔ (x ∈ fiber S w v ∧ Lgate S L x) := by
    intro x
    rw [mem_fiber]
    unfold Qual
    tauto
  refine isTieMin_congr S (fun x => (hset x).symm) ?_
  -- the fiber is TieLt-sorted; use positional indexing
  have hpw := fiber_pairwise S w v
  have hget := List.pairwise_iff_getElem.mp hpw
  -- gate characterisation: for `x = fiber[i]`, the gate holds iff `k ≤ i`
  have hgate : ∀ (i : ℕ) (hi : i < (fiber S w v).length),
      Lgate S L ((fiber S w v)[i]) ↔ k ≤ i := by
    intro i hi
    rcases hL with ⟨rfl, rfl⟩ | ⟨hk, hne, rfl⟩
    · exact iff_of_true trivial (Nat.zero_le i)
    · show TieLt S ((fiber S w v)[k-1]) ((fiber S w v)[i]) ↔ k ≤ i
      constructor
      · intro ht
        by_contra hik
        push Not at hik
        rcases Nat.lt_or_ge i (k-1) with h | h
        · exact tieLt_asymm S ht (hget i (k-1) hi hk h)
        · have hik1 : i = k - 1 := by omega
          subst hik1
          exact tieLt_irrefl S _ ht
      · intro hki
        exact hget (k-1) i hk hi (by omega)
  rcases Nat.lt_or_ge k (fiber S w v).length with hlt | hge
  · rw [List.getElem?_eq_getElem hlt]
    refine ⟨⟨List.getElem_mem hlt, (hgate k hlt).mpr le_rfl⟩, ?_⟩
    rintro x ⟨hxmem, hxgate⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxmem
    have hki : k ≤ i := (hgate i hi).mp hxgate
    rcases Nat.eq_or_lt_of_le hki with h | h
    · subst h
      exact Or.inl rfl
    · exact Or.inr (hget k i hlt hi h)
  · rw [List.getElem?_eq_none hge]
    rintro x ⟨hxmem, hxgate⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxmem
    have hki : k ≤ i := (hgate i hi).mp hxgate
    omega

/-- `LPred` advances: after finding the `k`-th element, it is the predecessor
for `k + 1`. -/
theorem lpred_succ (w : List Step) (v : ℤ) (k : ℕ) (x : Fin S.K × ℕ)
    (hx : (fiber S w v)[k]? = some x) :
    LPred S w v (k + 1) (some x) := by
  have hk : k < (fiber S w v).length := by
    by_contra h
    push Not at h
    rw [List.getElem?_eq_none h] at hx
    simp at hx
  right
  refine ⟨by simpa using hk, Nat.succ_ne_zero k, ?_⟩
  rw [List.getElem?_eq_getElem hk] at hx
  simp only [Nat.add_sub_cancel]
  rw [Option.some.injEq]
  exact (Option.some.inj hx).symm

end SRRQuadratic

-- best-so-far recursion and successor lemma)

namespace SRRQuadratic

open Multihead

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-! ## Signed head-register arithmetic

A signed integer `x` with `|x| < Wtot·(n + 2)` is stored as
`repVal (s, r) q = ±(Wtot·q + r)`: sign `s` (`true` = nonnegative) and residue
`r < Wtot` in the finite control, quotient `q` as a head position.  `repAdd`
adds an integer `z` with `|z| < Wtot`, moving the head at most one cell and
preserving the canonical form (zero has sign `+`), so rank-level equality is
one head coincidence plus a state comparison. -/

/-- Sign application (`true` = `+`). -/
def sgn : Bool → ℤ → ℤ
  | true, x => x
  | false, x => -x

@[simp] theorem sgn_true (x : ℤ) : sgn true x = x := rfl
@[simp] theorem sgn_false (x : ℤ) : sgn false x = -x := rfl

/-- A signed residue: sign and residue `< Wtot`. -/
abbrev Rep := Bool × Fin (Wtot S)

/-- The value represented by state part `s` and head position `q`. -/
def repVal (s : Rep S) (q : ℕ) : ℤ := sgn s.1 ((Wtot S : ℤ) * q + s.2)

theorem repVal_mk (sb : Bool) (r : Fin (Wtot S)) (q : ℕ) :
    repVal S (sb, r) q = sgn sb ((Wtot S : ℤ) * q + r) := rfl

/-- Canonical form: zero is represented with sign `+` (and any negative value
has a nonzero magnitude). -/
def RepCanon (s : Rep S) (q : ℕ) : Prop := s.1 = false → (q ≠ 0 ∨ (s.2 : ℕ) ≠ 0)

/-- Clamp an integer into `Fin (Wtot S)` (out-of-range values go to `0`). -/
def finClamp (x : ℤ) : Fin (Wtot S) :=
  if h : 0 ≤ x ∧ x < (Wtot S : ℤ) then ⟨x.toNat, by omega⟩ else ⟨0, Wtot_pos S⟩

theorem finClamp_val (x : ℤ) (h0 : 0 ≤ x) (h1 : x < (Wtot S : ℤ)) :
    ((finClamp S x : Fin (Wtot S)) : ℤ) = x := by
  unfold finClamp
  rw [dif_pos ⟨h0, h1⟩]
  show ((x.toNat : ℕ) : ℤ) = x
  omega

/-- Renormalise value `t` at head position `0` (`|t| < 2·Wtot`). -/
def repFix0 (t : ℤ) : Rep S × HeadMove :=
  if (Wtot S : ℤ) ≤ t then ((true, finClamp S (t - Wtot S)), .right)
  else if 0 ≤ t then ((true, finClamp S t), .stay)
  else if -(Wtot S : ℤ) < t then ((false, finClamp S (-t)), .stay)
  else ((false, finClamp S (-t - Wtot S)), .right)

/-- Renormalise `±(Wtot·q + t)` at head position `q ≥ 1` (`−Wtot < t < 2·Wtot`). -/
def repFixQ (sb : Bool) (t : ℤ) : Rep S × HeadMove :=
  if (Wtot S : ℤ) ≤ t then ((sb, finClamp S (t - Wtot S)), .right)
  else if 0 ≤ t then ((sb, finClamp S t), .stay)
  else ((sb, finClamp S (t + Wtot S)), .left)

/-- **Signed head-register addition**: add `z` (`|z| < Wtot`) to the value
represented by `(s, q)`, observing only the state part `s` and whether the
head is at cell `0` (`qz`). -/
def repAdd (s : Rep S) (qz : Bool) (z : ℤ) : Rep S × HeadMove :=
  match qz, s.1 with
  | true,  true  => repFix0 S ((s.2 : ℤ) + z)
  | true,  false => repFix0 S (-(s.2 : ℤ) + z)
  | false, true  => repFixQ S true ((s.2 : ℤ) + z)
  | false, false => repFixQ S false ((s.2 : ℤ) - z)

theorem repFix0_spec (t : ℤ) (h1 : -(2 * Wtot S : ℤ) < t) (h2 : t < 2 * Wtot S) :
    repVal S (repFix0 S t).1 ((repFix0 S t).2.apply 0) = t
      ∧ RepCanon S (repFix0 S t).1 ((repFix0 S t).2.apply 0) := by
  unfold repFix0
  split_ifs with hA hB hC
  · refine ⟨?_, fun h => absurd h (by simp)⟩
    rw [HeadMove.apply_right, repVal_mk, sgn_true, finClamp_val S _ (by omega) (by omega)]
    push_cast
    ring
  · refine ⟨?_, fun h => absurd h (by simp)⟩
    rw [HeadMove.apply_stay, repVal_mk, sgn_true, finClamp_val S _ (by omega) (by omega)]
    push_cast
    ring
  · constructor
    · rw [HeadMove.apply_stay, repVal_mk, sgn_false, finClamp_val S _ (by omega) (by omega)]
      push_cast
      ring
    · intro _
      right
      have hval := finClamp_val S (-t) (by omega) (by omega)
      intro h0
      rw [h0] at hval
      simp only [Nat.cast_zero] at hval
      omega
  · constructor
    · rw [HeadMove.apply_right, repVal_mk, sgn_false, finClamp_val S _ (by omega) (by omega)]
      push_cast
      ring
    · intro _
      left
      simp

theorem repFixQ_spec (sb : Bool) (t : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (h1 : -(Wtot S : ℤ) < t) (h2 : t < 2 * Wtot S) :
    repVal S (repFixQ S sb t).1 ((repFixQ S sb t).2.apply q)
        = sgn sb ((Wtot S : ℤ) * q + t)
      ∧ RepCanon S (repFixQ S sb t).1 ((repFixQ S sb t).2.apply q) := by
  have hqc : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  unfold repFixQ
  split_ifs with hA hB
  · refine ⟨?_, fun _ => Or.inl (by simp)⟩
    rw [HeadMove.apply_right, repVal_mk, finClamp_val S _ (by omega) (by omega)]
    cases sb <;> simp <;> ring
  · refine ⟨?_, fun _ => Or.inl (by rw [HeadMove.apply_stay]; omega)⟩
    rw [HeadMove.apply_stay, repVal_mk, finClamp_val S _ (by omega) (by omega)]
  · constructor
    · rw [HeadMove.apply_left, repVal_mk, finClamp_val S _ (by omega) (by omega), hcast]
      cases sb <;> simp <;> ring
    · intro _
      right
      have hval := finClamp_val S (t + Wtot S) (by omega) (by omega)
      intro h0
      rw [h0] at hval
      simp only [Nat.cast_zero] at hval
      omega

/-- **Correctness of the signed head-register addition.** -/
theorem repAdd_spec (s : Rep S) (q : ℕ) (qz : Bool) (z : ℤ)
    (hz : z.natAbs < Wtot S) (hc : RepCanon S s q) (hqz : qz = true ↔ q = 0) :
    repVal S (repAdd S s qz z).1 ((repAdd S s qz z).2.apply q)
        = repVal S s q + z
      ∧ RepCanon S (repAdd S s qz z).1 ((repAdd S s qz z).2.apply q) := by
  obtain ⟨sb, r⟩ := s
  have hr : (r : ℕ) < Wtot S := r.isLt
  have hrT : ((r : ℕ) : ℤ) < (Wtot S : ℤ) := by exact_mod_cast hr
  have hrz : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg _
  cases hqzb : qz with
  | true =>
      have hq0 : q = 0 := hqz.mp hqzb
      subst hq0
      cases sb with
      | true =>
          rw [show repAdd S (true, r) true z = repFix0 S ((r : ℤ) + z) from rfl]
          obtain ⟨he, hcan⟩ := repFix0_spec S ((r : ℤ) + z) (by omega) (by omega)
          refine ⟨?_, hcan⟩
          rw [he, repVal_mk, sgn_true]
          push_cast
          ring
      | false =>
          rw [show repAdd S (false, r) true z = repFix0 S (-(r : ℤ) + z) from rfl]
          obtain ⟨he, hcan⟩ := repFix0_spec S (-(r : ℤ) + z) (by omega) (by omega)
          refine ⟨?_, hcan⟩
          rw [he, repVal_mk, sgn_false]
          push_cast
          ring
  | false =>
      have hq0 : q ≠ 0 := fun h => by
        rw [hqzb] at hqz
        exact Bool.false_ne_true (hqz.mpr h)
      have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
      cases sb with
      | true =>
          rw [show repAdd S (true, r) false z = repFixQ S true ((r : ℤ) + z) from rfl]
          obtain ⟨he, hcan⟩ := repFixQ_spec S true ((r : ℤ) + z) q hq1 (by omega) (by omega)
          refine ⟨?_, hcan⟩
          rw [he, sgn_true, repVal_mk, sgn_true]
          ring
      | false =>
          rw [show repAdd S (false, r) false z = repFixQ S false ((r : ℤ) - z) from rfl]
          obtain ⟨he, hcan⟩ := repFixQ_spec S false ((r : ℤ) - z) q hq1 (by omega) (by omega)
          refine ⟨?_, hcan⟩
          rw [he, sgn_false, repVal_mk, sgn_false]
          ring

end SRRQuadratic

namespace SRRQuadratic

open Multihead

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- Base-`Wtot` decomposition is unique. -/
private theorem decomp_unique {T q q' : ℕ} {r r' : ℤ}
    (h : (T : ℤ) * q + r = (T : ℤ) * q' + r')
    (hr0 : 0 ≤ r) (hr1 : r < T) (hr0' : 0 ≤ r') (hr1' : r' < T) :
    q = q' ∧ r = r' := by
  have hT : (0 : ℤ) < T := by omega
  rcases Nat.lt_trichotomy q q' with hq | hq | hq
  · exfalso
    have h1 : (q : ℤ) + 1 ≤ (q' : ℤ) := by exact_mod_cast hq
    nlinarith
  · subst hq
    constructor
    · rfl
    · omega
  · exfalso
    have h1 : (q' : ℤ) + 1 ≤ (q : ℤ) := by exact_mod_cast hq
    nlinarith

/-- **Canonical representations are unique**: two canonical signed
head-registers represent the same value iff their state parts and head
positions agree.  This is what makes the machine's rank-level equality test
(one coincidence bit plus a state comparison) exact. -/
theorem repVal_eq_iff (s s' : Rep S) (q q' : ℕ)
    (hc : RepCanon S s q) (hc' : RepCanon S s' q') :
    repVal S s q = repVal S s' q' ↔ (s = s' ∧ q = q') := by
  constructor
  · intro h
    obtain ⟨sb, r⟩ := s
    obtain ⟨sb', r'⟩ := s'
    have hr : ((r : ℕ) : ℤ) < (Wtot S : ℤ) := by exact_mod_cast r.isLt
    have hr' : ((r' : ℕ) : ℤ) < (Wtot S : ℤ) := by exact_mod_cast r'.isLt
    have hrz : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg _
    have hrz' : (0 : ℤ) ≤ (r' : ℤ) := Int.natCast_nonneg _
    have hqz : (0 : ℤ) ≤ (Wtot S : ℤ) * q :=
      mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hqz' : (0 : ℤ) ≤ (Wtot S : ℤ) * q' :=
      mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hTpos : (0 : ℤ) < (Wtot S : ℤ) := by exact_mod_cast Wtot_pos S
    cases sb <;> cases sb' <;> rw [repVal_mk, repVal_mk] at h
    · -- both negative
      rw [sgn_false, sgn_false, neg_inj] at h
      obtain ⟨hq, hrr⟩ := decomp_unique h hrz hr hrz' hr'
      have : r = r' := Fin.ext (by exact_mod_cast hrr)
      exact ⟨by rw [this], hq⟩
    · -- negative = nonnegative: both zero, contradicting canonicity
      exfalso
      rw [sgn_false, sgn_true] at h
      have hz1 : (Wtot S : ℤ) * q + r = 0 := by omega
      have hq0 : (Wtot S : ℤ) * q = 0 := by omega
      have hr0 : (r : ℤ) = 0 := by omega
      rcases hc rfl with hq' | hr'
      · have : (q : ℤ) = 0 := by
          rcases mul_eq_zero.mp hq0 with h' | h'
          · omega
          · exact h'
        exact hq' (by exact_mod_cast this)
      · exact hr' (by exact_mod_cast hr0)
    · exfalso
      rw [sgn_true, sgn_false] at h
      have hz1 : (Wtot S : ℤ) * q' + r' = 0 := by omega
      have hq0 : (Wtot S : ℤ) * q' = 0 := by omega
      have hr0 : (r' : ℤ) = 0 := by omega
      rcases hc' rfl with hq'' | hr''
      · have : (q' : ℤ) = 0 := by
          rcases mul_eq_zero.mp hq0 with h' | h'
          · omega
          · exact h'
        exact hq'' (by exact_mod_cast this)
      · exact hr'' (by exact_mod_cast hr0)
    · rw [sgn_true, sgn_true] at h
      obtain ⟨hq, hrr⟩ := decomp_unique h hrz hr hrz' hr'
      have : r = r' := Fin.ext (by exact_mod_cast hrr)
      exact ⟨by rw [this], hq⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A head-register holding a rank-magnitude-bounded value sits strictly left
of the right end-marker. -/
theorem repVal_head_lt (s : Rep S) (q : ℕ) (n : ℕ)
    (h1 : -((bigW S : ℤ) * (n + 2)) ≤ repVal S s q)
    (h2 : repVal S s q ≤ (bigW S : ℤ) * (n + 2)) :
    q < n + 1 := by
  have hW : (1 : ℤ) ≤ (bigW S : ℤ) := by exact_mod_cast bigW_pos S
  have habs : (Wtot S : ℤ) * q ≤ (bigW S : ℤ) * (n + 2) := by
    obtain ⟨sb, r⟩ := s
    have hrz : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg _
    cases sb
    · rw [repVal_mk, sgn_false] at h1
      omega
    · rw [repVal_mk, sgn_true] at h2
      omega
  by_contra hq
  push Not at hq
  have hq' : ((n : ℤ) + 1) ≤ (q : ℤ) := by exact_mod_cast hq
  have hWt : (Wtot S : ℤ) = 2 * (bigW S : ℤ) + 1 := by
    unfold Wtot
    push_cast
    ring
  have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg _
  nlinarith

/-- Incrementing a canonical register moves the head right only from a
maximal nonnegative residue (used to keep the level head off `⊣`). -/
theorem Wtot_ge3 : 3 ≤ Wtot S := by
  have := bigW_pos S
  unfold Wtot
  omega

theorem repAdd_one_right (s : Rep S) (qz : Bool)
    (h : (repAdd S s qz 1).2 = HeadMove.right) :
    s.1 = true ∧ (s.2 : ℕ) = Wtot S - 1 := by
  have hT := Wtot_pos S
  have hT3 : (3 : ℤ) ≤ (Wtot S : ℤ) := by exact_mod_cast Wtot_ge3 S
  obtain ⟨sb, r⟩ := s
  have hr : (r : ℕ) < Wtot S := r.isLt
  have hrT : ((r : ℕ) : ℤ) < (Wtot S : ℤ) := by exact_mod_cast hr
  have hrz : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg _
  cases hqzb : qz <;> rw [hqzb] at h <;> cases hsb : sb <;> rw [hsb] at h
  · -- qz = false, sb = false: repFixQ false (r - 1): never right
    exfalso
    rw [show repAdd S (false, r) false 1 = repFixQ S false ((r : ℤ) - 1) from rfl] at h
    unfold repFixQ at h
    split_ifs at h with hA hB
    omega
  · -- qz = false, sb = true: right exactly at the maximal residue
    rw [show repAdd S (true, r) false 1 = repFixQ S true ((r : ℤ) + 1) from rfl] at h
    unfold repFixQ at h
    split_ifs at h with hA hB
    exact ⟨rfl, by show (r : ℕ) = Wtot S - 1; omega⟩
  · -- qz = true, sb = false: `-r + 1 ≥ -(Wtot - 2)`: never right
    exfalso
    rw [show repAdd S (false, r) true 1 = repFix0 S (-(r : ℤ) + 1) from rfl] at h
    unfold repFix0 at h
    split_ifs at h with hA hB hC
    · omega
    · omega
  · rw [show repAdd S (true, r) true 1 = repFix0 S ((r : ℤ) + 1) from rfl] at h
    unfold repFix0 at h
    split_ifs at h with hA hB hC
    · exact ⟨rfl, by show (r : ℕ) = Wtot S - 1; omega⟩
    · exfalso
      omega

/-- A cell at or left of the last letter is not the right end-marker. -/
theorem tapeSym_ne_rmark (w : List Step) (i : ℕ) (h : i ≤ w.length) :
    tapeSym w i ≠ TapeSym.rmark := by
  cases i with
  | zero =>
      rw [tapeSym_zero]
      simp
  | succ k =>
      rw [tapeSym_succ w k (by omega)]
      simp

/-- The right end-marker cell is exactly `≥ |w| + 1`. -/
theorem tapeSym_rmark_iff (w : List Step) (i : ℕ) :
    tapeSym w i = TapeSym.rmark ↔ w.length + 1 ≤ i := by
  constructor
  · intro h
    by_contra hle
    exact tapeSym_ne_rmark w i (by omega) h
  · intro h
    exact tapeSym_ge w i (by omega)

/-- The left end-marker cell is exactly `0`. -/
theorem tapeSym_lmark_iff (w : List Step) (i : ℕ) :
    tapeSym w i = TapeSym.lmark ↔ i = 0 := by
  constructor
  · intro h
    by_contra h0
    cases hi : i with
    | zero => exact h0 hi
    | succ k =>
        rw [hi] at h
        by_cases hk : k < w.length
        · rw [tapeSym_succ w k hk] at h
          simp at h
        · rw [tapeSym_ge w (k+1) (by omega)] at h
          simp at h
  · rintro rfl
    exact tapeSym_zero w

end SRRQuadratic


namespace SRRQuadratic

open Multihead

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-! ## The machine: heads, control state -/

/-- Number of heads: scan, `L`, `B`, level, and one per copy. -/
def numH : ℕ := S.K + 4

/-- The scan head. -/
def scanI : Fin (numH S) := ⟨0, by unfold numH; omega⟩
/-- The last-emitted-position head. -/
def LI : Fin (numH S) := ⟨1, by unfold numH; omega⟩
/-- The best-so-far-position head. -/
def BI : Fin (numH S) := ⟨2, by unfold numH; omega⟩
/-- The rank-level magnitude head. -/
def VI : Fin (numH S) := ⟨3, by unfold numH; omega⟩
/-- The per-copy running-rank magnitude heads. -/
def valI (c : Fin S.K) : Fin (numH S) := ⟨4 + c.val, by unfold numH; omega⟩

/-- Build a per-head assignment from the five head groups. -/
def mkF {α : Type} (s l b v : α) (f : Fin S.K → α) : Fin (numH S) → α := fun i =>
  if _ : i.val = 0 then s else if _ : i.val = 1 then l
  else if _ : i.val = 2 then b else if _ : i.val = 3 then v
  else f ⟨i.val - 4, by have := i.isLt; unfold numH at this; omega⟩

@[simp] theorem mkF_scan {α : Type} (s l b v : α) (f : Fin S.K → α) :
    mkF S s l b v f (scanI S) = s := rfl
@[simp] theorem mkF_L {α : Type} (s l b v : α) (f : Fin S.K → α) :
    mkF S s l b v f (LI S) = l := rfl
@[simp] theorem mkF_B {α : Type} (s l b v : α) (f : Fin S.K → α) :
    mkF S s l b v f (BI S) = b := rfl
@[simp] theorem mkF_V {α : Type} (s l b v : α) (f : Fin S.K → α) :
    mkF S s l b v f (VI S) = v := rfl
@[simp] theorem mkF_val {α : Type} (s l b v : α) (f : Fin S.K → α) (c : Fin S.K) :
    mkF S s l b v f (valI S c) = f c := by
  have h0 : ¬ ((valI S c : Fin (numH S)) : ℕ) = 0 := by show ¬ (4 + (c : ℕ) = 0); omega
  have h1 : ¬ ((valI S c : Fin (numH S)) : ℕ) = 1 := by show ¬ (4 + (c : ℕ) = 1); omega
  have h2 : ¬ ((valI S c : Fin (numH S)) : ℕ) = 2 := by show ¬ (4 + (c : ℕ) = 2); omega
  have h3 : ¬ ((valI S c : Fin (numH S)) : ℕ) = 3 := by show ¬ (4 + (c : ℕ) = 3); omega
  show (if _ : ((valI S c : Fin (numH S)) : ℕ) = 0 then s
    else if _ : ((valI S c : Fin (numH S)) : ℕ) = 1 then l
    else if _ : ((valI S c : Fin (numH S)) : ℕ) = 2 then b
    else if _ : ((valI S c : Fin (numH S)) : ℕ) = 3 then v
    else f ⟨((valI S c : Fin (numH S)) : ℕ) - 4, by
      have := (valI S c).isLt; unfold numH at this; omega⟩) = f c
  rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3]
  congr 1
  apply Fin.ext
  show 4 + (c : ℕ) - 4 = (c : ℕ)
  omega

/-- Every head index is one of the five groups. -/
theorem headIndexCases (a : Fin (numH S)) :
    a = scanI S ∨ a = LI S ∨ a = BI S ∨ a = VI S ∨ ∃ c, a = valI S c := by
  have ha := a.isLt
  unfold numH at ha
  rcases Nat.lt_or_ge a.val 4 with h4 | h4
  · interval_cases h : a.val
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨a.val - 4, by omega⟩, Fin.ext ?_⟩)))
    show a.val = 4 + (a.val - 4)
    omega

/-- Pointwise application of a `mkF` move to a `mkF` position. -/
theorem apply_mkF (ms ml mb mv : HeadMove) (mf : Fin S.K → HeadMove)
    (ps pl pb pv : ℕ) (pf : Fin S.K → ℕ) :
    (fun i => (mkF S ms ml mb mv mf i).apply (mkF S ps pl pb pv pf i))
      = mkF S (ms.apply ps) (ml.apply pl) (mb.apply pb) (mv.apply pv)
          (fun c => (mf c).apply (pf c)) := by
  funext i
  unfold mkF
  split_ifs <;> rfl

/-- The all-stay move. -/
def stayAll : Fin (numH S) → HeadMove := fun _ => .stay

theorem apply_stayAll (pos : Fin (numH S) → ℕ) :
    (fun i => (stayAll S i).apply (pos i)) = pos := rfl

/-- The control tags (phases) of the machine. -/
inductive Tag
  | domScan | reject | vInit | rewindAll | rewindK | scanStart
  | sA | sB | sWalk | sC | parkL | walkL | done
  deriving DecidableEq

instance : Fintype Tag :=
  ⟨⟨{.domScan, .reject, .vInit, .rewindAll, .rewindK, .scanStart,
      .sA, .sB, .sWalk, .sC, .parkL, .walkL, .done}, by decide⟩,
    fun x => by cases x <;> decide⟩

/-- The register part of the control state. -/
structure Reg where
  /-- Domain-acceptor state. -/
  dq : S.DA.Q
  /-- Prefix-pass DFA state. -/
  pq : S.pp.A.Q
  /-- Per-copy rank-source states. -/
  sq : ∀ c : Fin S.K, (src S c).Q
  /-- Sign/residue of the current rank level. -/
  vr : Rep S
  /-- Signs/residues of the per-copy running ranks. -/
  cr : Fin S.K → Rep S
  /-- Copy of the last-emitted atom (`none`: none yet in this level). -/
  lc : Option (Fin S.K)
  /-- Copy of the best-so-far atom (`none`: none yet in this scan). -/
  bc : Option (Fin S.K)
  /-- Cached label of the best-so-far atom. -/
  bl : Option Gamma
  /-- Whether the scan head is strictly right of the `L` head. -/
  pastL : Bool

/-- `Reg` as a product, for the `Fintype` instance. -/
def regEquiv : Reg S ≃ (S.DA.Q × S.pp.A.Q × (∀ c : Fin S.K, (src S c).Q) × Rep S ×
    (Fin S.K → Rep S) × Option (Fin S.K) × Option (Fin S.K) × Option Gamma × Bool) where
  toFun r := (r.dq, r.pq, r.sq, r.vr, r.cr, r.lc, r.bc, r.bl, r.pastL)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1,
    t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (Reg S) := Fintype.ofEquiv _ (regEquiv S).symm

/-- The canonical representation of the constant `c0v c` at head position 0. -/
def repC0 (c : Fin S.K) : Rep S := (decide (0 ≤ c0v S c), finClamp S |c0v S c|)

theorem repC0_spec (c : Fin S.K) :
    repVal S (repC0 S c) 0 = c0v S c ∧ RepCanon S (repC0 S c) 0 := by
  have habs := c0v_abs_le S c
  have hW : bigW S < Wtot S := by unfold Wtot; omega
  have habs2 : (0 : ℤ) ≤ |c0v S c| := abs_nonneg _
  have habs3 : |c0v S c| < (Wtot S : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast (by omega : (c0v S c).natAbs < Wtot S)
  have hclamp := finClamp_val S |c0v S c| habs2 habs3
  constructor
  · rw [show repC0 S c = (decide (0 ≤ c0v S c), finClamp S |c0v S c|) from rfl, repVal_mk]
    by_cases h0 : 0 ≤ c0v S c
    · rw [decide_eq_true h0, sgn_true, Nat.cast_zero, mul_zero, zero_add, hclamp,
        abs_of_nonneg h0]
    · rw [decide_eq_false h0, sgn_false, Nat.cast_zero, mul_zero, zero_add, hclamp,
        abs_of_neg (by omega)]
      ring
  · intro hfalse
    right
    have h0 : ¬ (0 ≤ c0v S c) := by
      intro h
      have ht : (repC0 S c).1 = true := decide_eq_true h
      rw [ht] at hfalse
      simp at hfalse
    intro hzero
    have hz : |c0v S c| = 0 := by
      rw [← hclamp]
      exact_mod_cast hzero
    have := abs_eq_zero.mp hz
    omega

end SRRQuadratic

namespace SRRQuadratic

open Multihead

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-! ## The transition function -/

/-- The (empty) counter-operation assignment. -/
def noOps : Fin 0 → Logspace.CounterOp := fun j => j.elim0

/-- Transition results. -/
abbrev Res := (Tag × Reg S) × (Fin (numH S) → HeadMove) ×
  (Fin 0 → Logspace.CounterOp) × List Gamma

open Classical in
/-- Phase `domScan`: run the domain acceptor left to right; at `⊣` accept
into `vInit` or move to the `reject` sink. -/
noncomputable def etaDom (r : Reg S) (sSc : TapeSym Step) : Option (Res S) :=
  match sSc with
  | .lmark => some ((Tag.domScan, r),
      mkF S .right .stay .stay .stay (fun _ => .stay), noOps, [])
  | .letter a => some ((Tag.domScan, { r with dq := S.DA.δ r.dq a }),
      mkF S .right .stay .stay .stay (fun _ => .stay), noOps, [])
  | .rmark =>
      if S.DA.accept r.dq then some ((Tag.vInit, r), stayAll S, noOps, [])
      else some ((Tag.reject, r), stayAll S, noOps, [])

/-- Phase `vInit`: walk the level head to `⊣` and load the least level
`−(Wtot·(n+1) + (Wtot−1))`. -/
def etaVInit (r : Reg S) (sV : TapeSym Step) : Option (Res S) :=
  match sV with
  | .rmark => some ((Tag.rewindAll,
      { r with vr := (false, ⟨Wtot S - 1, by have := Wtot_pos S; omega⟩) }),
      stayAll S, noOps, [])
  | _ => some ((Tag.vInit, r), mkF S .stay .stay .stay .right (fun _ => .stay), noOps, [])

/-- One backward step of a rewinding head (`⊢` parks it). -/
def mvBack (s : TapeSym Step) : HeadMove := if s = .lmark then .stay else .left

/-- The register reset at the start of a scan. -/
def resetReg (r : Reg S) : Reg S :=
  { r with
    pq := S.pp.A.q0
    sq := fun c => (src S c).q0
    cr := fun c => repC0 S c
    bc := none
    bl := none
    pastL := false }

/-- Phases `rewindAll`/`rewindK`: move the scan, `B`, and per-copy heads
(and, for `rewindAll`, the `L` head) simultaneously back to `⊢`, then reset
the scan registers. -/
def etaRewind (isL : Bool) (r : Reg S) (sSc sL sB : TapeSym Step)
    (sVals : Fin S.K → TapeSym Step) : Option (Res S) :=
  if sSc = .lmark ∧ (isL = true → sL = .lmark) ∧ sB = .lmark ∧ ∀ c, sVals c = .lmark then
    some ((Tag.scanStart, resetReg S r), stayAll S, noOps, [])
  else
    some ((if isL then Tag.rewindAll else Tag.rewindK, r),
      mkF S (mvBack sSc) (if isL then mvBack sL else .stay) (mvBack sB) .stay
        (fun c => mvBack (sVals c)), noOps, [])

/-- Phase `scanStart`: step the scan head onto cell 1. -/
def etaScanStart (r : Reg S) : Option (Res S) :=
  some ((Tag.sA, r), mkF S .right .stay .stay .stay (fun _ => .stay), noOps, [])

/-- Phase `sA` at a letter: add each copy's local correction, so the per-copy
registers hold the full rank of the current position; at `⊣`: emit the cached
best, advance the level, or halt. -/
noncomputable def etaSA (r : Reg S) (sSc sV : TapeSym Step) (qzs : Fin S.K → Bool) :
    Option (Res S) :=
  match sSc with
  | .letter a =>
      some ((Tag.sB, { r with
          cr := fun c => (repAdd S (r.cr c) (qzs c) (locf S c (r.sq c) a)).1 }),
        mkF S .stay .stay .stay .stay
          (fun c => (repAdd S (r.cr c) (qzs c) (locf S c (r.sq c) a)).2), noOps, [])
  | .rmark =>
      match r.bc with
      | some _ => some ((Tag.parkL, r), stayAll S, noOps, r.bl.elim [] (fun g => [g]))
      | none =>
          if r.vr.1 = true ∧ (r.vr.2 : ℕ) = Wtot S - 1 ∧ sV = .rmark then
            some ((Tag.done, r), stayAll S, noOps, [])
          else
            some ((Tag.rewindAll, { r with
                vr := (repAdd S r.vr (sV == .lmark) 1).1
                lc := none }),
              mkF S .stay .stay .stay (repAdd S r.vr (sV == .lmark) 1).2
                (fun _ => .stay), noOps, [])
  | .lmark => none

open Classical in
/-- The Boolean `L`-gate of the cell decision. -/
noncomputable def sbLgate (r : Reg S) (coinSL : Bool) (c : Fin S.K) : Bool :=
  match r.lc with
  | none => true
  | some cL =>
      if S.dir then r.pastL || (coinSL && decide (S.cord cL c))
      else (!r.pastL && !coinSL) || (coinSL && decide (S.cord cL c))

open Classical in
/-- The Boolean cell-qualification test. -/
noncomputable def sbQual (r : Reg S) (a : Step) (coinSL : Bool)
    (coinCV : Fin S.K → Bool) (c : Fin S.K) : Bool :=
  S.pp.selSet c (S.pp.A.δ r.pq a) && (coinCV c && decide (r.cr c = r.vr))
    && sbLgate S r coinSL c

/-- Phase `sB` at a letter: decide the cell — the `cord`-least selected copy
whose rank equals the level and which lies tie-after `L` — and update the
best-so-far. -/
noncomputable def etaSB (r : Reg S) (sSc : TapeSym Step) (coinSL : Bool)
    (coinCV : Fin S.K → Bool) : Option (Res S) :=
  match sSc with
  | .letter a =>
      match ((cordList S).filter (sbQual S r a coinSL coinCV)).head? with
      | none => some ((Tag.sC, r), stayAll S, noOps, [])
      | some cw =>
          if r.bc.isSome && S.dir then some ((Tag.sC, r), stayAll S, noOps, [])
          else some ((Tag.sWalk, { r with
              bc := some cw
              bl := some (S.pp.labSet cw (S.pp.A.δ r.pq a)) }), stayAll S, noOps, [])
  | _ => none

/-- Phase `sWalk`: walk the `B` head right to the scan head. -/
def etaSWalk (r : Reg S) (coinBS : Bool) : Option (Res S) :=
  if coinBS then some ((Tag.sC, r), stayAll S, noOps, [])
  else some ((Tag.sWalk, r), mkF S .stay .stay .right .stay (fun _ => .stay), noOps, [])

/-- Phase `sC` at a letter: restore the per-copy registers to the prefix sum
of the next cell, advance the DFA registers, and step the scan right. -/
def etaSC (r : Reg S) (sSc : TapeSym Step) (coinSL : Bool) (qzs : Fin S.K → Bool) :
    Option (Res S) :=
  match sSc with
  | .letter a =>
      some ((Tag.sA, { r with
          pq := S.pp.A.δ r.pq a
          sq := fun c => (src S c).δ (r.sq c) a
          cr := fun c => (repAdd S (r.cr c) (qzs c)
            (wf S c (r.sq c) a - locf S c (r.sq c) a)).1
          pastL := r.pastL || coinSL }),
        mkF S .right .stay .stay .stay
          (fun c => (repAdd S (r.cr c) (qzs c)
            (wf S c (r.sq c) a - locf S c (r.sq c) a)).2), noOps, [])
  | _ => none

/-- Phase `parkL`: walk the `L` head back to `⊢`. -/
def etaParkL (r : Reg S) (sL : TapeSym Step) : Option (Res S) :=
  if sL = .lmark then some ((Tag.walkL, r), stayAll S, noOps, [])
  else some ((Tag.parkL, r), mkF S .stay .left .stay .stay (fun _ => .stay), noOps, [])

/-- Phase `walkL`: walk the `L` head right to the `B` head, then record the
new last-emitted copy. -/
def etaWalkL (r : Reg S) (coinLB : Bool) : Option (Res S) :=
  if coinLB then some ((Tag.rewindK, { r with lc := r.bc }), stayAll S, noOps, [])
  else some ((Tag.walkL, r), mkF S .stay .right .stay .stay (fun _ => .stay), noOps, [])

/-- The complete transition function (before the end-marker guard). -/
noncomputable def etaCore (q : Tag × Reg S) (syms : Fin (numH S) → TapeSym Step)
    (coin : Fin (numH S) → Fin (numH S) → Bool) : Option (Res S) :=
  match q.1 with
  | Tag.domScan => etaDom S q.2 (syms (scanI S))
  | Tag.reject => none
  | Tag.vInit => etaVInit S q.2 (syms (VI S))
  | Tag.rewindAll => etaRewind S true q.2 (syms (scanI S)) (syms (LI S)) (syms (BI S))
      (fun c => syms (valI S c))
  | Tag.rewindK => etaRewind S false q.2 (syms (scanI S)) (syms (LI S)) (syms (BI S))
      (fun c => syms (valI S c))
  | Tag.scanStart => etaScanStart S q.2
  | Tag.sA => etaSA S q.2 (syms (scanI S)) (syms (VI S))
      (fun c => syms (valI S c) == TapeSym.lmark)
  | Tag.sB => etaSB S q.2 (syms (scanI S)) (coin (scanI S) (LI S))
      (fun c => coin (valI S c) (VI S))
  | Tag.sWalk => etaSWalk S q.2 (coin (BI S) (scanI S))
  | Tag.sC => etaSC S q.2 (syms (scanI S)) (coin (scanI S) (LI S))
      (fun c => syms (valI S c) == TapeSym.lmark)
  | Tag.parkL => etaParkL S q.2 (syms (LI S))
  | Tag.walkL => etaWalkL S q.2 (coin (LI S) (BI S))
  | Tag.done => none

/-- The end-marker guard: refuse any transition that would move a head
reading `⊣` to the right (never fires on the constructed run). -/
def guardR (syms : Fin (numH S) → TapeSym Step) (o : Option (Res S)) : Option (Res S) :=
  match o with
  | none => none
  | some res =>
      if ∀ a, syms a = TapeSym.rmark → res.2.1 a ≠ HeadMove.right then some res else none

theorem guardR_pass (syms : Fin (numH S) → TapeSym Step) (res : Res S)
    (h : ∀ a, syms a = TapeSym.rmark → res.2.1 a ≠ HeadMove.right) :
    guardR S syms (some res) = some res := by
  show (if ∀ a, syms a = TapeSym.rmark → res.2.1 a ≠ HeadMove.right
    then some res else none) = some res
  rw [if_pos h]

/-- The initial registers. -/
noncomputable def initReg : Reg S :=
  { dq := S.DA.q0
    pq := S.pp.A.q0
    sq := fun c => (src S c).q0
    vr := (true, ⟨0, Wtot_pos S⟩)
    cr := fun c => repC0 S c
    lc := none
    bc := none
    bl := none
    pastL := false }

/-- **The machine** (`cor:srr-quadratic`): `K + 4` two-way heads, no
counters. -/
noncomputable def mach : MHC Step Gamma (numH S) 0 where
  Q := Tag × Reg S
  fintypeQ := inferInstance
  q0 := (Tag.domScan, initReg S)
  F := fun q => q.1 = Tag.done
  η := fun q syms coin _ => guardR S syms (etaCore S q syms coin)
  rmark_no_right := by
    intro q syms coin zs res hr a hrm
    unfold guardR at hr
    cases ho : etaCore S q syms coin with
    | none =>
        rw [ho] at hr
        simp at hr
    | some res' =>
        rw [ho] at hr
        have hr' : (if ∀ a, syms a = TapeSym.rmark → res'.2.1 a ≠ HeadMove.right
            then some res' else none) = some res := hr
        split_ifs at hr' with hcond
        obtain rfl := Option.some.inj hr'
        exact hcond a hrm

end SRRQuadratic

namespace SRRQuadratic

open Multihead

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-! ## Single-step infrastructure -/

/-- Machine configurations from tag, registers, head positions. -/
noncomputable def cfg (t : Tag) (r : Reg S) (pos : Fin (numH S) → ℕ) :
    (mach S (Gamma := Gamma)).Config :=
  ((t, r), pos, fun _ => 0)

theorem cnt_eq (cnt cnt' : Fin 0 → ℕ) : cnt = cnt' := funext (fun j => j.elim0)

@[simp] theorem etaCore_domScan (r : Reg S) (syms) (coin) :
    etaCore S (Tag.domScan, r) syms coin = etaDom S r (syms (scanI S)) := rfl
@[simp] theorem etaCore_reject (r : Reg S) (syms) (coin) :
    etaCore S (Tag.reject, r) syms coin = none := rfl
@[simp] theorem etaCore_vInit (r : Reg S) (syms) (coin) :
    etaCore S (Tag.vInit, r) syms coin = etaVInit S r (syms (VI S)) := rfl
@[simp] theorem etaCore_rewindAll (r : Reg S) (syms) (coin) :
    etaCore S (Tag.rewindAll, r) syms coin
      = etaRewind S true r (syms (scanI S)) (syms (LI S)) (syms (BI S))
          (fun c => syms (valI S c)) := rfl
@[simp] theorem etaCore_rewindK (r : Reg S) (syms) (coin) :
    etaCore S (Tag.rewindK, r) syms coin
      = etaRewind S false r (syms (scanI S)) (syms (LI S)) (syms (BI S))
          (fun c => syms (valI S c)) := rfl
@[simp] theorem etaCore_scanStart (r : Reg S) (syms) (coin) :
    etaCore S (Tag.scanStart, r) syms coin = etaScanStart S r := rfl
@[simp] theorem etaCore_sA (r : Reg S) (syms) (coin) :
    etaCore S (Tag.sA, r) syms coin
      = etaSA S r (syms (scanI S)) (syms (VI S))
          (fun c => syms (valI S c) == TapeSym.lmark) := rfl
@[simp] theorem etaCore_sB (r : Reg S) (syms) (coin) :
    etaCore S (Tag.sB, r) syms coin
      = etaSB S r (syms (scanI S)) (coin (scanI S) (LI S))
          (fun c => coin (valI S c) (VI S)) := rfl
@[simp] theorem etaCore_sWalk (r : Reg S) (syms) (coin) :
    etaCore S (Tag.sWalk, r) syms coin = etaSWalk S r (coin (BI S) (scanI S)) := rfl
@[simp] theorem etaCore_sC (r : Reg S) (syms) (coin) :
    etaCore S (Tag.sC, r) syms coin
      = etaSC S r (syms (scanI S)) (coin (scanI S) (LI S))
          (fun c => syms (valI S c) == TapeSym.lmark) := rfl
@[simp] theorem etaCore_parkL (r : Reg S) (syms) (coin) :
    etaCore S (Tag.parkL, r) syms coin = etaParkL S r (syms (LI S)) := rfl
@[simp] theorem etaCore_walkL (r : Reg S) (syms) (coin) :
    etaCore S (Tag.walkL, r) syms coin = etaWalkL S r (coin (LI S) (BI S)) := rfl
@[simp] theorem etaCore_done (r : Reg S) (syms) (coin) :
    etaCore S (Tag.done, r) syms coin = none := rfl

/-- **The single-step rule**: an `etaCore` value together with the end-marker
guard condition yields one machine step. -/
theorem step_one {w : List Step} {t : Tag} {r : Reg S} {pos : Fin (numH S) → ℕ}
    {t' : Tag} {r' : Reg S} {mv : Fin (numH S) → HeadMove} {u : List Gamma}
    (hcore : etaCore S (t, r) (fun i => tapeSym w (pos i)) (fun i j => pos i == pos j)
      = some ((t', r'), mv, noOps, u))
    (hguard : ∀ a, tapeSym w (pos a) = TapeSym.rmark → mv a ≠ HeadMove.right)
    (pos' : Fin (numH S) → ℕ) (hpos : pos' = fun i => (mv i).apply (pos i)) :
    (mach S).StepsN w (cfg S t r pos) u (cfg S t' r' pos') 1 := by
  have hη : (mach S).η (t, r) (fun i => tapeSym w (pos i)) (fun i j => pos i == pos j)
      (fun j => (fun _ : Fin 0 => (0 : ℕ)) j == 0) = some ((t', r'), mv, noOps, u) := by
    show guardR S _ (etaCore S (t, r) _ _) = _
    rw [hcore]
    exact guardR_pass S _ _ hguard
  have h := MHC.StepsN.head (M := mach S) (w := w) hη (MHC.StepsN.refl _)
  rw [List.append_nil] at h
  have hend : (((t', r'), fun i => (mv i).apply (pos i),
      fun j => (Logspace.CounterOp.apply (noOps j) ((fun _ : Fin 0 => (0 : ℕ)) j)))
        : (mach S).Config)
      = cfg S t' r' pos' := by
    unfold cfg
    rw [hpos]
    exact congrArg (fun cn => ((t', r'), fun i => (mv i).apply (pos i), cn)) (cnt_eq _ _)
  rw [hend] at h
  exact h

/-- The generic halting fact: `reject` and `done` configurations are halted. -/
theorem halted_of_core_none {w : List Step} {t : Tag} {r : Reg S}
    {pos : Fin (numH S) → ℕ}
    (h : etaCore S (t, r) (fun i => tapeSym w (pos i)) (fun i j => pos i == pos j) = none) :
    (mach S).Halted w (cfg S t r pos) := by
  show guardR S (fun i => tapeSym w (pos i))
    (etaCore S (t, r) (fun i => tapeSym w (pos i)) (fun i j => pos i == pos j)) = none
  rw [h]
  rfl

theorem halted_done (w : List Step) (r : Reg S) (pos : Fin (numH S) → ℕ) :
    (mach S).Halted w (cfg S Tag.done r pos) :=
  halted_of_core_none S (etaCore_done S r _ _)

theorem halted_reject (w : List Step) (r : Reg S) (pos : Fin (numH S) → ℕ) :
    (mach S).Halted w (cfg S Tag.reject r pos) :=
  halted_of_core_none S (etaCore_reject S r _ _)

end SRRQuadratic

namespace SRRQuadratic

open Multihead

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-! ## Advance lemmas and guard helpers -/

private theorem foldl_take_succ {α β : Type*} (f : β → α → β) (b : β) (w : List α)
    (j : ℕ) (h : j < w.length) :
    (w.take (j+1)).foldl f b = f ((w.take j).foldl f b) w[j] := by
  rw [List.take_succ_eq_append_getElem h, List.foldl_append]
  rfl

theorem da_stateBefore_succ (w : List Step) (j : ℕ) (h : j < w.length) :
    S.DA.stateBefore w (j+1) = S.DA.δ (S.DA.stateBefore w j) w[j] :=
  foldl_take_succ _ _ w j h

theorem pp_stateBefore_succ (w : List Step) (j : ℕ) (h : j < w.length) :
    S.pp.A.stateBefore w (j+1) = S.pp.A.δ (S.pp.A.stateBefore w j) w[j] :=
  foldl_take_succ _ _ w j h

theorem src_stateBefore_succ (c : Fin S.K) (w : List Step) (j : ℕ) (h : j < w.length) :
    (src S c).stateBefore w (j+1) = (src S c).δ ((src S c).stateBefore w j) w[j] :=
  foldl_take_succ _ _ w j h

theorem da_stateBefore_zero (w : List Step) : S.DA.stateBefore w 0 = S.DA.q0 := rfl
theorem pp_stateBefore_zero (w : List Step) : S.pp.A.stateBefore w 0 = S.pp.A.q0 := rfl
theorem src_stateBefore_zero (c : Fin S.K) (w : List Step) :
    (src S c).stateBefore w 0 = (src S c).q0 := rfl

theorem da_accepts_iff_stateBefore (w : List Step) :
    S.DA.accepts w ↔ S.DA.accept (S.DA.stateBefore w w.length) := by
  unfold SliceMSO.DetAuto.accepts SliceMSO.DetAuto.stateBefore
  rw [List.take_length]

theorem prefS_zero (c : Fin S.K) (w : List Step) : prefS S c w 0 = 0 := by
  unfold prefS RankSource.prefixRank
  simp

theorem prefS_succ (c : Fin S.K) (w : List Step) (j : ℕ) (h : j < w.length) :
    prefS S c w (j+1) = prefS S c w j + wf S c ((src S c).stateBefore w j) w[j] := by
  unfold prefS RankSource.prefixRank
  rw [Finset.sum_range_succ, List.getElem?_eq_getElem h]
  rfl

/-- `rank1` at a real position, with the letter explicit. -/
theorem rank1_at (c : Fin S.K) (w : List Step) (j : ℕ) (h : j < w.length) :
    rank1 S c w j = c0v S c + prefS S c w j
      + locf S c ((src S c).stateBefore w j) w[j] := by
  rw [rank1_eq, List.getElem?_eq_getElem h]
  rfl

/-- Magnitude of the running prefix value. -/
theorem crval_bound (c : Fin S.K) (w : List Step) (j : ℕ) (hj : j ≤ w.length) :
    -((bigW S : ℤ) * (w.length + 2)) ≤ c0v S c + prefS S c w j
      ∧ c0v S c + prefS S c w j ≤ (bigW S : ℤ) * (w.length + 2) := by
  obtain ⟨hp1, hp2⟩ := prefS_bound S c w j
  obtain ⟨hc1, hc2⟩ := two_sided (c0v_abs_le S c)
  have hjn : (j : ℤ) ≤ (w.length : ℤ) := by exact_mod_cast hj
  have hmono : (bigW S : ℤ) * j ≤ (bigW S : ℤ) * w.length :=
    mul_le_mul_of_nonneg_left hjn (Int.natCast_nonneg _)
  constructor <;> nlinarith

/-- Magnitude of the tested rank value (prefix value plus local correction). -/
theorem rankval_bound (c : Fin S.K) (w : List Step) (j : ℕ) (hj : j < w.length) :
    -((bigW S : ℤ) * (w.length + 2)) ≤ rank1 S c w j
      ∧ rank1 S c w j ≤ (bigW S : ℤ) * (w.length + 2) := by
  obtain ⟨h1, h2⟩ := rank1_bound S c w j
  have hple : (j : ℤ) + 2 ≤ (w.length : ℤ) + 2 := by
    have : (j : ℤ) < (w.length : ℤ) := by exact_mod_cast hj
    omega
  have hmono : (bigW S : ℤ) * (j + 2) ≤ (bigW S : ℤ) * (w.length + 2) :=
    mul_le_mul_of_nonneg_left hple (Int.natCast_nonneg _)
  constructor <;> linarith

/-- The all-stay guard is trivially discharged. -/
theorem guard_stayAll (syms : Fin (numH S) → TapeSym Step) :
    ∀ a, syms a = TapeSym.rmark → stayAll S a ≠ HeadMove.right := by
  intro a _ h
  exact HeadMove.noConfusion h

/-- The backward-move guard is trivially discharged. -/
theorem mvBack_ne_right (s : TapeSym Step) : mvBack s ≠ HeadMove.right := by
  unfold mvBack
  split_ifs <;> intro h <;> exact HeadMove.noConfusion h

/-- Guard discharge for a `mkF` move set from per-group conditions. -/
theorem guard_mkF {w : List Step} {pos : Fin (numH S) → ℕ}
    (ms ml mb mv : HeadMove) (mf : Fin S.K → HeadMove)
    (hs : tapeSym w (pos (scanI S)) = TapeSym.rmark → ms ≠ HeadMove.right)
    (hl : tapeSym w (pos (LI S)) = TapeSym.rmark → ml ≠ HeadMove.right)
    (hb : tapeSym w (pos (BI S)) = TapeSym.rmark → mb ≠ HeadMove.right)
    (hv : tapeSym w (pos (VI S)) = TapeSym.rmark → mv ≠ HeadMove.right)
    (hf : ∀ c, tapeSym w (pos (valI S c)) = TapeSym.rmark → mf c ≠ HeadMove.right) :
    ∀ a, tapeSym w (pos a) = TapeSym.rmark → mkF S ms ml mb mv mf a ≠ HeadMove.right := by
  intro a ha
  rcases headIndexCases S a with rfl | rfl | rfl | rfl | ⟨c, rfl⟩
  · rw [mkF_scan]; exact hs ha
  · rw [mkF_L]; exact hl ha
  · rw [mkF_B]; exact hb ha
  · rw [mkF_V]; exact hv ha
  · rw [mkF_val]; exact hf c ha

/-- `stay` and `left` never violate the guard. -/
theorem stay_ne_right : HeadMove.stay ≠ HeadMove.right := fun h => HeadMove.noConfusion h
theorem left_ne_right : HeadMove.left ≠ HeadMove.right := fun h => HeadMove.noConfusion h

end SRRQuadratic

namespace SRRQuadratic

open Multihead

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-! ## The scan invariant -/

/-- The `L`-head/registers match the gate parameter. -/
def LMatch (w : List Step) (Lopt : Option (Fin S.K × ℕ)) (j : ℕ)
    (r : Reg S) (pos : Fin (numH S) → ℕ) : Prop :=
  match Lopt with
  | none => r.lc = none ∧ pos (LI S) = 0 ∧ r.pastL = false
  | some l => r.lc = some l.1 ∧ pos (LI S) = l.2 + 1 ∧ l.2 < w.length ∧
      (r.pastL = true ↔ l.2 < j)

/-- The `B`-head/registers match the best-so-far recursion. -/
def BMatch (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ)) (j : ℕ)
    (r : Reg S) (pos : Fin (numH S) → ℕ) : Prop :=
  match bestUpTo S w v Lopt j with
  | none => r.bc = none ∧ pos (BI S) = 0 ∧ r.bl = none
  | some b => r.bc = some b.1 ∧ pos (BI S) = b.2 + 1 ∧
      r.bl = some (S.pp.labSet b.1 (S.pp.A.stateBefore w (b.2 + 1)))

/-- **The scan invariant**: after processing cells `< j` of a level-`v` scan
with gate `Lopt` (scan head on cell `j + 1`, phase `sA`). -/
structure ScanInv (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ))
    (dq : S.DA.Q) (j : ℕ) (r : Reg S) (pos : Fin (numH S) → ℕ) : Prop where
  hj : j ≤ w.length
  hdq : r.dq = dq
  hpq : r.pq = S.pp.A.stateBefore w j
  hsq : ∀ c, r.sq c = (src S c).stateBefore w j
  hvv : repVal S r.vr (pos (VI S)) = v
  hvc : RepCanon S r.vr (pos (VI S))
  hvh : pos (VI S) ≤ w.length + 1
  hcv : ∀ c, repVal S (r.cr c) (pos (valI S c)) = c0v S c + prefS S c w j
  hcc : ∀ c, RepCanon S (r.cr c) (pos (valI S c))
  hsc : pos (scanI S) = j + 1
  hL : LMatch S w Lopt j r pos
  hB : BMatch S w v Lopt j r pos

/-- The `B`-head position determined by the recursion. -/
noncomputable def BPos (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ)) (j : ℕ) : ℕ :=
  match bestUpTo S w v Lopt j with
  | none => 0
  | some b => b.2 + 1

theorem bestUpTo_pos_lt (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ))
    (j : ℕ) (b : Fin S.K × ℕ) (h : bestUpTo S w v Lopt j = some b) : b.2 < j := by
  have hspec := bestUpTo_spec S w v Lopt j
  rw [h] at hspec
  exact hspec.1.2

theorem BPos_le (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ)) (j : ℕ) :
    BPos S w v Lopt j ≤ j := by
  unfold BPos
  cases hb : bestUpTo S w v Lopt j with
  | none => exact Nat.zero_le j
  | some b =>
      show b.2 + 1 ≤ j
      have := bestUpTo_pos_lt S w v Lopt j b hb
      omega

theorem BPos_mono (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ)) (j : ℕ) :
    BPos S w v Lopt j ≤ BPos S w v Lopt (j+1) := by
  have hle := BPos_le S w v Lopt j
  unfold BPos
  show (match bestUpTo S w v Lopt j with | none => 0 | some b => b.2 + 1)
    ≤ (match mergeB S (bestUpTo S w v Lopt j) (bestAt S w v Lopt j) j with
        | none => 0 | some b => b.2 + 1)
  cases hb : bestUpTo S w v Lopt j with
  | none =>
      cases hc : bestAt S w v Lopt j with
      | none => simp [mergeB]
      | some c => simp [mergeB]
  | some b =>
      cases hc : bestAt S w v Lopt j with
      | none => simp [mergeB]
      | some c =>
          show b.2 + 1 ≤ (match (if S.dir then some b else some (c, j)) with
            | none => 0 | some b => b.2 + 1)
          have hlt := bestUpTo_pos_lt S w v Lopt j b hb
          cases hd : S.dir
          · rw [if_neg (by simp)]
            show b.2 + 1 ≤ j + 1
            omega
          · rw [if_pos rfl]

/-- The per-copy head positions are strictly left of `⊣` under the invariant. -/
theorem ScanInv.valhead_lt {w : List Step} {v : ℤ} {Lopt : Option (Fin S.K × ℕ)}
    {dq : S.DA.Q} {j : ℕ} {r : Reg S} {pos : Fin (numH S) → ℕ}
    (H : ScanInv S w v Lopt dq j r pos) (c : Fin S.K) :
    pos (valI S c) < w.length + 1 := by
  obtain ⟨h1, h2⟩ := crval_bound S c w j H.hj
  exact repVal_head_lt S (r.cr c) _ w.length (by rw [H.hcv c]; exact h1)
    (by rw [H.hcv c]; exact h2)

end SRRQuadratic


namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

private theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem sbLgate_iff (w : List Step) (Lopt : Option (Fin S.K × ℕ)) (j : ℕ)
    (r : Reg S) (pos : Fin (numH S) → ℕ)
    (hscan : pos (scanI S) = j + 1) (hL : LMatch S w Lopt j r pos) (c : Fin S.K) :
    (sbLgate S r (pos (scanI S) == pos (LI S)) c = true) ↔ Lgate S Lopt (c, j) := by
  classical
  unfold sbLgate Lgate
  cases hlo : Lopt with
  | none =>
      rw [hlo] at hL
      obtain ⟨hlc, -, -⟩ := hL
      rw [hlc]
      simp
  | some l =>
      rw [hlo] at hL
      obtain ⟨hlc, hlpos, hln, hpast⟩ := hL
      rw [hlc]
      have hcoin : ((pos (scanI S) == pos (LI S)) = true) ↔ l.2 = j := by
        rw [beq_iff_eq, hscan, hlpos]
        omega
      show (if S.dir then _ else _) = true ↔ TieLt S l (c, j)
      unfold TieLt
      cases hd : S.dir
      · rw [if_neg (by simp), if_neg (by simp)]
        constructor
        · intro h
          rcases Bool.or_eq_true_iff.mp h with h | h
          · rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at h
            obtain ⟨hp, hc⟩ := h
            left
            show (c, j).2 < l.2
            have h1 : ¬ (l.2 < j) := fun hh => by rw [hpast.mpr hh] at hp; exact Bool.noConfusion hp
            have h2 : ¬ (l.2 = j) := fun hh => by rw [hcoin.mpr hh] at hc; exact Bool.noConfusion hc
            show j < l.2
            omega
          · rw [Bool.and_eq_true] at h
            obtain ⟨hcv, hcd⟩ := h
            exact Or.inr ⟨hcoin.mp hcv, of_decide_eq_true hcd⟩
        · intro h
          rcases h with h | ⟨he, hcd⟩
          · have hjl : j < l.2 := h
            refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
            rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true']
            constructor
            · cases hpb : r.pastL
              · rfl
              · exfalso
                have := hpast.mp hpb
                omega
            · cases hcb : (pos (scanI S) == pos (LI S))
              · rfl
              · exfalso
                have := hcoin.mp hcb
                omega
          · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
            rw [Bool.and_eq_true]
            exact ⟨hcoin.mpr he, decide_eq_true hcd⟩
      · rw [if_pos rfl, if_pos rfl]
        constructor
        · intro h
          rcases Bool.or_eq_true_iff.mp h with h | h
          · left
            show l.2 < (c, j).2
            exact hpast.mp h
          · rw [Bool.and_eq_true] at h
            obtain ⟨hcv, hcd⟩ := h
            exact Or.inr ⟨hcoin.mp hcv, of_decide_eq_true hcd⟩
        · intro h
          rcases h with h | ⟨he, hcd⟩
          · exact Bool.or_eq_true_iff.mpr (Or.inl (hpast.mpr h))
          · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
            rw [Bool.and_eq_true]
            exact ⟨hcoin.mpr he, decide_eq_true hcd⟩

/-- Correctness of the Boolean cell decision at cell `j`. -/
theorem sbQual_eq_qualB (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ))
    (j : ℕ) (hjn : j < w.length) (r : Reg S) (pos : Fin (numH S) → ℕ)
    (hpq : r.pq = S.pp.A.stateBefore w j)
    (hrank : ∀ c, repVal S (r.cr c) (pos (valI S c)) = rank1 S c w j)
    (hrcan : ∀ c, RepCanon S (r.cr c) (pos (valI S c)))
    (hvv : repVal S r.vr (pos (VI S)) = v)
    (hvc : RepCanon S r.vr (pos (VI S)))
    (hscan : pos (scanI S) = j + 1)
    (hL : LMatch S w Lopt j r pos)
    (c : Fin S.K) :
    sbQual S r w[j] (pos (scanI S) == pos (LI S)) (fun c' => pos (valI S c') == pos (VI S)) c
      = qualB S w v Lopt j c := by
  apply bool_eq_of_iff
  rw [qualB_iff]
  unfold sbQual Qual QSel
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨hsel, hcv, hrveq⟩, hgate⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [selP_iff]
      refine ⟨hjn, ?_⟩
      rw [pp_stateBefore_succ S w j hjn, ← hpq]
      exact hsel
    · have := (repVal_eq_iff S (r.cr c) r.vr (pos (valI S c)) (pos (VI S))
        (hrcan c) hvc).mpr ⟨of_decide_eq_true hrveq, by rwa [beq_iff_eq] at hcv⟩
      rw [hrank c, hvv] at this
      exact this
    · exact (sbLgate_iff S w Lopt j r pos hscan hL c).mp hgate
  · rintro ⟨⟨hsel, hrk⟩, hgate⟩
    have hrveq := (repVal_eq_iff S (r.cr c) r.vr (pos (valI S c)) (pos (VI S))
        (hrcan c) hvc).mp (by rw [hrank c, hvv]; exact hrk)
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [selP_iff] at hsel
      show S.pp.selSet c (S.pp.A.δ r.pq w[j]) = true
      rw [hpq, ← pp_stateBefore_succ S w j hjn]
      exact hsel.2
    · rw [beq_iff_eq]
      exact hrveq.2
    · exact decide_eq_true hrveq.1
    · exact (sbLgate_iff S w Lopt j r pos hscan hL c).mpr hgate

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- Step `sA` of one cell. -/
theorem stepA (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ)) (dq : S.DA.Q)
    (j : ℕ) (r : Reg S) (pos : Fin (numH S) → ℕ)
    (H : ScanInv S w v Lopt dq j r pos) (hjn : j < w.length) :
    ∃ (rA : Reg S) (posA : Fin (numH S) → ℕ),
      (mach S).StepsN w (cfg S Tag.sA r pos) [] (cfg S Tag.sB rA posA) 1 ∧
      rA.dq = r.dq ∧ rA.pq = r.pq ∧ rA.sq = r.sq ∧ rA.vr = r.vr ∧
      rA.lc = r.lc ∧ rA.bc = r.bc ∧ rA.bl = r.bl ∧ rA.pastL = r.pastL ∧
      (∀ c, repVal S (rA.cr c) (posA (valI S c)) = rank1 S c w j
        ∧ RepCanon S (rA.cr c) (posA (valI S c))) ∧
      posA (scanI S) = pos (scanI S) ∧ posA (LI S) = pos (LI S) ∧
      posA (BI S) = pos (BI S) ∧ posA (VI S) = pos (VI S) := by
  set a := w[j] with ha
  set qzs : Fin S.K → Bool := fun c => tapeSym w (pos (valI S c)) == TapeSym.lmark with hqzs
  set rA : Reg S := { r with
    cr := fun c => (repAdd S (r.cr c) (qzs c) (locf S c (r.sq c) a)).1 } with hrA
  set mvA : Fin (numH S) → HeadMove := mkF S .stay .stay .stay .stay
    (fun c => (repAdd S (r.cr c) (qzs c) (locf S c (r.sq c) a)).2) with hmvA
  refine ⟨rA, fun i => (mvA i).apply (pos i), ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- the machine step
    refine step_one S ?_ ?_ _ rfl
    · rw [etaCore_sA]
      show etaSA S r (tapeSym w (pos (scanI S))) (tapeSym w (pos (VI S))) qzs = _
      rw [H.hsc, tapeSym_succ w j hjn]
      rfl
    · rw [hmvA]
      refine guard_mkF S _ _ _ _ _ (fun _ => stay_ne_right) (fun _ => stay_ne_right)
        (fun _ => stay_ne_right) (fun _ => stay_ne_right) (fun c hrm => ?_)
      exact absurd ((tapeSym_rmark_iff w _).mp hrm)
        (by have := ScanInv.valhead_lt S H c; omega)
  · -- the new per-copy values
    intro c
    have hqz : qzs c = true ↔ pos (valI S c) = 0 := by
      rw [hqzs]
      show (tapeSym w (pos (valI S c)) == TapeSym.lmark) = true ↔ _
      rw [beq_iff_eq, tapeSym_lmark_iff]
    have habs : (locf S c (r.sq c) a).natAbs < Wtot S := by
      have h1 := locf_abs_le S c (r.sq c) a
      have h2 : bigW S < Wtot S := by unfold Wtot; omega
      omega
    have hspec := repAdd_spec S (r.cr c) (pos (valI S c)) (qzs c)
      (locf S c (r.sq c) a) habs (H.hcc c) hqz
    have hmv : (fun i => (mvA i).apply (pos i)) (valI S c)
        = (repAdd S (r.cr c) (qzs c) (locf S c (r.sq c) a)).2.apply (pos (valI S c)) := by
      rw [hmvA]
      show ((mkF S HeadMove.stay HeadMove.stay HeadMove.stay HeadMove.stay _) (valI S c)).apply _ = _
      rw [mkF_val]
    have hcr : rA.cr c = (repAdd S (r.cr c) (qzs c) (locf S c (r.sq c) a)).1 := rfl
    rw [hmv, hcr]
    constructor
    · rw [hspec.1, H.hcv c, H.hsq c, rank1_at S c w j hjn]
    · exact hspec.2
  · show (mvA (scanI S)).apply _ = _
    rw [hmvA, mkF_scan]
    rfl
  · show (mvA (LI S)).apply _ = _
    rw [hmvA, mkF_L]
    rfl
  · show (mvA (BI S)).apply _ = _
    rw [hmvA, mkF_B]
    rfl
  · show (mvA (VI S)).apply _ = _
    rw [hmvA, mkF_V]
    rfl

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- The `B`-walk: from `sc − d` to the scan head at `sc`, then into `sC`. -/
theorem stepWalk (w : List Step) (rB : Reg S) :
    ∀ (d : ℕ) (pos : Fin (numH S) → ℕ) (sc : ℕ), pos (scanI S) = sc → sc ≤ w.length →
    pos (BI S) = sc - d → d ≤ sc →
    ∃ pos', (mach S).StepsN w (cfg S Tag.sWalk rB pos) [] (cfg S Tag.sC rB pos') (d + 1) ∧
      pos' (scanI S) = sc ∧ pos' (BI S) = sc ∧ pos' (LI S) = pos (LI S) ∧
      pos' (VI S) = pos (VI S) ∧ (∀ c, pos' (valI S c) = pos (valI S c)) := by
  intro d
  induction d with
  | zero =>
      intro pos sc hsc hscle hB hd
      have hBsc : pos (BI S) = sc := by omega
      have hcore : etaCore S (Tag.sWalk, rB) (fun i => tapeSym w (pos i))
          (fun i j => pos i == pos j) = some ((Tag.sC, rB), stayAll S, noOps, []) := by
        rw [etaCore_sWalk]
        show etaSWalk S rB (pos (BI S) == pos (scanI S)) = _
        rw [show (pos (BI S) == pos (scanI S)) = true by rw [beq_iff_eq, hBsc, hsc]]
        rfl
      exact ⟨pos, step_one S hcore (guard_stayAll S _) pos (by funext i; rfl),
        hsc, hBsc, rfl, rfl, fun c => rfl⟩
  | succ d ih =>
      intro pos sc hsc hscle hB hd
      set mv1 : Fin (numH S) → HeadMove :=
        mkF S .stay .stay .right .stay (fun _ => .stay) with hmv1
      set pos1 : Fin (numH S) → ℕ := fun i => (mv1 i).apply (pos i) with hpos1
      have hstep : (mach S).StepsN w (cfg S Tag.sWalk rB pos) []
          (cfg S Tag.sWalk rB pos1) 1 := by
        refine step_one S ?_ ?_ _ hpos1
        · rw [etaCore_sWalk]
          show etaSWalk S rB (pos (BI S) == pos (scanI S)) = _
          rw [show (pos (BI S) == pos (scanI S)) = false by
            rw [beq_eq_false_iff_ne, hB, hsc]; omega]
          rfl
        · rw [hmv1]
          refine guard_mkF S _ _ _ _ _ (fun _ => stay_ne_right) (fun _ => stay_ne_right)
            (fun hrm => ?_) (fun _ => stay_ne_right) (fun _ _ => stay_ne_right)
          exact absurd ((tapeSym_rmark_iff w _).mp hrm) (by rw [hB]; omega)
      have h1scan : pos1 (scanI S) = sc := by
        rw [hpos1]
        show (mv1 (scanI S)).apply _ = _
        rw [hmv1, mkF_scan]
        exact hsc
      have h1B : pos1 (BI S) = sc - d := by
        rw [hpos1]
        show (mv1 (BI S)).apply _ = _
        rw [hmv1, mkF_B, HeadMove.apply_right, hB]
        omega
      obtain ⟨pos', hrun, hsc', hB', hL', hV', hval'⟩ :=
        ih pos1 sc h1scan hscle h1B (by omega)
      refine ⟨pos', ?_, hsc', hB', ?_, ?_, ?_⟩
      · have h12 := MHC.StepsN.trans hstep hrun
        rw [show d + 1 + 1 = 1 + (d + 1) by omega]
        simpa using h12
      · rw [hL']
        rw [hpos1]
        show (mv1 (LI S)).apply _ = _
        rw [hmv1, mkF_L]
        rfl
      · rw [hV']
        rw [hpos1]
        show (mv1 (VI S)).apply _ = _
        rw [hmv1, mkF_V]
        rfl
      · intro c
        rw [hval' c]
        rw [hpos1]
        show (mv1 (valI S c)).apply _ = _
        rw [hmv1, mkF_val]
        rfl

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- `LMatch` depends only on `lc`, `pastL`, and the `L`-head. -/
theorem LMatch_transfer {w : List Step} {Lopt : Option (Fin S.K × ℕ)} {j : ℕ}
    {r r' : Reg S} {pos pos' : Fin (numH S) → ℕ}
    (hlc : r'.lc = r.lc) (hp : r'.pastL = r.pastL) (hLh : pos' (LI S) = pos (LI S))
    (H : LMatch S w Lopt j r pos) : LMatch S w Lopt j r' pos' := by
  unfold LMatch at H ⊢
  cases Lopt with
  | none => exact ⟨by rw [hlc]; exact H.1, by rw [hLh]; exact H.2.1, by rw [hp]; exact H.2.2⟩
  | some l =>
      obtain ⟨h1, h2, h3, h4⟩ := H
      exact ⟨by rw [hlc]; exact h1, by rw [hLh]; exact h2, h3, by rw [hp]; exact h4⟩

/-- `BMatch` depends only on `bc`, `bl`, and the `B`-head. -/
theorem BMatch_transfer {w : List Step} {v : ℤ} {Lopt : Option (Fin S.K × ℕ)} {j : ℕ}
    {r r' : Reg S} {pos pos' : Fin (numH S) → ℕ}
    (hbc : r'.bc = r.bc) (hbl : r'.bl = r.bl) (hBh : pos' (BI S) = pos (BI S))
    (H : BMatch S w v Lopt j r pos) : BMatch S w v Lopt j r' pos' := by
  unfold BMatch at H ⊢
  cases hb : bestUpTo S w v Lopt j with
  | none =>
      rw [hb] at H
      exact ⟨by rw [hbc]; exact H.1, by rw [hBh]; exact H.2.1, by rw [hbl]; exact H.2.2⟩
  | some b =>
      rw [hb] at H
      exact ⟨by rw [hbc]; exact H.1, by rw [hBh]; exact H.2.1, by rw [hbl]; exact H.2.2⟩

/-- Step `sC` of one cell. -/
theorem stepC (w : List Step) (j : ℕ) (hjn : j < w.length) (r : Reg S)
    (pos : Fin (numH S) → ℕ)
    (hsq : ∀ c, r.sq c = (src S c).stateBefore w j)
    (hrank : ∀ c, repVal S (r.cr c) (pos (valI S c)) = rank1 S c w j)
    (hrcan : ∀ c, RepCanon S (r.cr c) (pos (valI S c)))
    (hscan : pos (scanI S) = j + 1) :
    ∃ (r' : Reg S) (pos' : Fin (numH S) → ℕ),
      (mach S).StepsN w (cfg S Tag.sC r pos) [] (cfg S Tag.sA r' pos') 1 ∧
      r'.dq = r.dq ∧ r'.pq = S.pp.A.δ r.pq w[j] ∧
      (∀ c, r'.sq c = (src S c).stateBefore w (j+1)) ∧ r'.vr = r.vr ∧
      r'.lc = r.lc ∧ r'.bc = r.bc ∧ r'.bl = r.bl ∧
      r'.pastL = (r.pastL || (pos (scanI S) == pos (LI S))) ∧
      (∀ c, repVal S (r'.cr c) (pos' (valI S c)) = c0v S c + prefS S c w (j+1)
        ∧ RepCanon S (r'.cr c) (pos' (valI S c))) ∧
      pos' (scanI S) = j + 2 ∧ pos' (LI S) = pos (LI S) ∧
      pos' (BI S) = pos (BI S) ∧ pos' (VI S) = pos (VI S) := by
  set a := w[j] with ha
  set qzs : Fin S.K → Bool := fun c => tapeSym w (pos (valI S c)) == TapeSym.lmark with hqzs
  set z : Fin S.K → ℤ := fun c => wf S c (r.sq c) a - locf S c (r.sq c) a with hz
  set r' : Reg S := { r with
    pq := S.pp.A.δ r.pq a
    sq := fun c => (src S c).δ (r.sq c) a
    cr := fun c => (repAdd S (r.cr c) (qzs c) (z c)).1
    pastL := r.pastL || ((j + 1 : ℕ) == pos (LI S)) } with hr'
  set mv : Fin (numH S) → HeadMove := mkF S .right .stay .stay .stay
    (fun c => (repAdd S (r.cr c) (qzs c) (z c)).2) with hmv
  have hvallt : ∀ c, pos (valI S c) < w.length + 1 := by
    intro c
    obtain ⟨h1, h2⟩ := rankval_bound S c w j hjn
    exact repVal_head_lt S (r.cr c) _ w.length (by rw [hrank c]; exact h1)
      (by rw [hrank c]; exact h2)
  refine ⟨r', fun i => (mv i).apply (pos i), ?_, rfl, rfl, ?_, rfl, rfl, rfl, rfl,
    (by rw [hscan]), ?_, ?_, ?_, ?_, ?_⟩
  · refine step_one S ?_ ?_ _ rfl
    · rw [etaCore_sC]
      show etaSC S r (tapeSym w (pos (scanI S))) (pos (scanI S) == pos (LI S)) qzs = _
      rw [hscan, tapeSym_succ w j hjn]
      rfl
    · rw [hmv]
      refine guard_mkF S _ _ _ _ _ (fun hrm => ?_) (fun _ => stay_ne_right)
        (fun _ => stay_ne_right) (fun _ => stay_ne_right) (fun c hrm => ?_)
      · exact absurd ((tapeSym_rmark_iff w _).mp hrm) (by rw [hscan]; omega)
      · exact absurd ((tapeSym_rmark_iff w _).mp hrm) (by have := hvallt c; omega)
  · intro c
    show (src S c).δ (r.sq c) a = _
    rw [hsq c, ← src_stateBefore_succ S c w j hjn]
  · intro c
    have hqz : qzs c = true ↔ pos (valI S c) = 0 := by
      rw [hqzs]
      show (tapeSym w (pos (valI S c)) == TapeSym.lmark) = true ↔ _
      rw [beq_iff_eq, tapeSym_lmark_iff]
    have habs : (z c).natAbs < Wtot S := by
      have h1 := wf_abs_le S c (r.sq c) a
      have h2 := locf_abs_le S c (r.sq c) a
      have h3 : bigW S + bigW S < Wtot S := by unfold Wtot; omega
      rw [hz]
      simp only []
      omega
    have hspec := repAdd_spec S (r.cr c) (pos (valI S c)) (qzs c) (z c) habs
      (hrcan c) hqz
    have hmvc : (fun i => (mv i).apply (pos i)) (valI S c)
        = (repAdd S (r.cr c) (qzs c) (z c)).2.apply (pos (valI S c)) := by
      show (mv (valI S c)).apply _ = _
      rw [hmv, mkF_val]
    have hcr : r'.cr c = (repAdd S (r.cr c) (qzs c) (z c)).1 := rfl
    rw [hmvc, hcr]
    constructor
    · rw [hspec.1, hrank c, rank1_at S c w j hjn, prefS_succ S c w j hjn, hz]
      simp only [hsq c]
      ring
    · exact hspec.2
  · show (mv (scanI S)).apply _ = _
    rw [hmv, mkF_scan, HeadMove.apply_right, hscan]
  · show (mv (LI S)).apply _ = _
    rw [hmv, mkF_L]
    rfl
  · show (mv (BI S)).apply _ = _
    rw [hmv, mkF_B]
    rfl
  · show (mv (VI S)).apply _ = _
    rw [hmv, mkF_V]
    rfl

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- Advancing the `L`-match one cell (`pastL` absorbs the coincidence). -/
theorem LMatch_advance {w : List Step} {Lopt : Option (Fin S.K × ℕ)} {j : ℕ}
    {r r' : Reg S} {pos pos' : Fin (numH S) → ℕ}
    (hlc : r'.lc = r.lc)
    (hpl : r'.pastL = (r.pastL || (pos (scanI S) == pos (LI S))))
    (hsc : pos (scanI S) = j + 1) (hLh : pos' (LI S) = pos (LI S))
    (H : LMatch S w Lopt j r pos) : LMatch S w Lopt (j+1) r' pos' := by
  unfold LMatch at H ⊢
  cases Lopt with
  | none =>
      obtain ⟨hlc0, hlh0, hpl0⟩ := H
      refine ⟨by rw [hlc]; exact hlc0, by rw [hLh]; exact hlh0, ?_⟩
      rw [hpl, hpl0, hsc, hlh0]
      show (false || ((j + 1 : ℕ) == 0)) = false
      rw [Bool.false_or, beq_eq_false_iff_ne]
      omega
  | some l =>
      obtain ⟨hlc0, hlh0, hln0, hpl0⟩ := H
      refine ⟨by rw [hlc]; exact hlc0, by rw [hLh]; exact hlh0, hln0, ?_⟩
      rw [hpl, hsc, hlh0]
      rw [Bool.or_eq_true_iff, beq_iff_eq]
      constructor
      · rintro (h | h)
        · have := hpl0.mp h
          omega
        · omega
      · intro h
        rcases Nat.lt_or_ge l.2 j with h' | h'
        · exact Or.inl (hpl0.mpr h')
        · right
          omega

/-- Evaluation of the `sB` decision at cell `j`. -/
theorem coreB_eval (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ))
    (j : ℕ) (hjn : j < w.length) (rA : Reg S) (posA : Fin (numH S) → ℕ)
    (hpq : rA.pq = S.pp.A.stateBefore w j)
    (hrank : ∀ c, repVal S (rA.cr c) (posA (valI S c)) = rank1 S c w j)
    (hrcan : ∀ c, RepCanon S (rA.cr c) (posA (valI S c)))
    (hvv : repVal S rA.vr (posA (VI S)) = v)
    (hvc : RepCanon S rA.vr (posA (VI S)))
    (hscan : posA (scanI S) = j + 1)
    (hL : LMatch S w Lopt j rA posA) :
    etaCore S (Tag.sB, rA) (fun i => tapeSym w (posA i)) (fun i j' => posA i == posA j')
      = (match bestAt S w v Lopt j with
        | none => some ((Tag.sC, rA), stayAll S, noOps, [])
        | some cw =>
            if rA.bc.isSome && S.dir then some ((Tag.sC, rA), stayAll S, noOps, [])
            else some ((Tag.sWalk, { rA with
                bc := some cw
                bl := some (S.pp.labSet cw (S.pp.A.δ rA.pq w[j])) }),
              stayAll S, noOps, [])) := by
  have hq : ∀ c, sbQual S rA w[j] (posA (scanI S) == posA (LI S))
      (fun c' => posA (valI S c') == posA (VI S)) c = qualB S w v Lopt j c :=
    fun c => sbQual_eq_qualB S w v Lopt j hjn rA posA hpq hrank hrcan hvv hvc hscan hL c
  rw [etaCore_sB]
  show etaSB S rA (tapeSym w (posA (scanI S))) (posA (scanI S) == posA (LI S))
    (fun c => posA (valI S c) == posA (VI S)) = _
  rw [hscan] at hq ⊢
  rw [tapeSym_succ w j hjn]
  show (match ((cordList S).filter (sbQual S rA w[j] ((j + 1 : ℕ) == posA (LI S))
      (fun c => posA (valI S c) == posA (VI S)))).head? with
    | none => some ((Tag.sC, rA), stayAll S, noOps, [])
    | some cw =>
        if rA.bc.isSome && S.dir then some ((Tag.sC, rA), stayAll S, noOps, [])
        else some ((Tag.sWalk, { rA with
            bc := some cw
            bl := some (S.pp.labSet cw (S.pp.A.δ rA.pq w[j])) }),
          stayAll S, noOps, [])) = _
  rw [List.filter_congr (fun c _ => hq c)]
  rfl

/-- **One cell of the scan** (`sA`–`sB`–[walk]–`sC`): the invariant advances
one cell, in `3` steps plus the `B`-walk. -/
theorem cell_step (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ))
    (dq : S.DA.Q) (j : ℕ) (r : Reg S) (pos : Fin (numH S) → ℕ)
    (H : ScanInv S w v Lopt dq j r pos) (hjn : j < w.length) :
    ∃ (r' : Reg S) (pos' : Fin (numH S) → ℕ) (len : ℕ),
      (mach S).StepsN w (cfg S Tag.sA r pos) [] (cfg S Tag.sA r' pos') len ∧
      ScanInv S w v Lopt dq (j+1) r' pos' ∧
      len ≤ 4 + (BPos S w v Lopt (j+1) - BPos S w v Lopt j) := by
  obtain ⟨rA, posA, hstepA, hAdq, hApq, hAsq, hAvr, hAlc, hAbc, hAbl, hApastL,
    hAvals, hAsc, hAL, hAB, hAV⟩ := stepA S w v Lopt dq j r pos H hjn
  have hApq' : rA.pq = S.pp.A.stateBefore w j := by rw [hApq, H.hpq]
  have hAsq' : ∀ c, rA.sq c = (src S c).stateBefore w j := by
    intro c
    rw [hAsq]
    exact H.hsq c
  have hAvv : repVal S rA.vr (posA (VI S)) = v := by rw [hAvr, hAV]; exact H.hvv
  have hAvc : RepCanon S rA.vr (posA (VI S)) := by rw [hAvr, hAV]; exact H.hvc
  have hAscan : posA (scanI S) = j + 1 := by rw [hAsc]; exact H.hsc
  have hLA : LMatch S w Lopt j rA posA := LMatch_transfer S hAlc hApastL hAL H.hL
  have hBA : BMatch S w v Lopt j rA posA := BMatch_transfer S hAbc hAbl hAB H.hB
  have hcoreB := coreB_eval S w v Lopt j hjn rA posA hApq' (fun c => (hAvals c).1)
    (fun c => (hAvals c).2) hAvv hAvc hAscan hLA
  cases hbest : bestAt S w v Lopt j with
  | none =>
      have hstepB : (mach S).StepsN w (cfg S Tag.sB rA posA) [] (cfg S Tag.sC rA posA) 1 := by
        refine step_one S ?_ (guard_stayAll S _) posA (by funext i; rfl)
        rw [hcoreB, hbest]
      obtain ⟨r', pos', hstepC, hCdq, hCpq, hCsq, hCvr, hClc, hCbc, hCbl, hCpastL,
        hCvals, hCsc, hCL, hCB, hCV⟩ :=
        stepC S w j hjn rA posA hAsq' (fun c => (hAvals c).1) (fun c => (hAvals c).2) hAscan
      have hmerge : bestUpTo S w v Lopt (j+1) = bestUpTo S w v Lopt j := by
        show mergeB S (bestUpTo S w v Lopt j) (bestAt S w v Lopt j) j = _
        rw [hbest]
        cases bestUpTo S w v Lopt j <;> rfl
      refine ⟨r', pos', 3, ?_, ?_, ?_⟩
      · have h3 := MHC.StepsN.trans (MHC.StepsN.trans hstepA hstepB) hstepC
        simpa using h3
      · refine ⟨by omega, ?_, ?_, hCsq, ?_, ?_, ?_, fun c => (hCvals c).1,
          fun c => (hCvals c).2, hCsc, ?_, ?_⟩
        · rw [hCdq, hAdq, H.hdq]
        · rw [hCpq, hApq', ← pp_stateBefore_succ S w j hjn]
        · rw [hCvr, hCV]
          exact hAvv
        · rw [hCvr, hCV]
          exact hAvc
        · rw [hCV, hAV]
          exact H.hvh
        · exact LMatch_advance S (by rw [hClc, hAlc]) hCpastL hAscan hCL hLA
        · -- BMatch at j+1
          have hBC : BMatch S w v Lopt j r' pos' :=
            BMatch_transfer S (by rw [hCbc, hAbc]) (by rw [hCbl, hAbl])
              (by rw [hCB, hAB]) H.hB
          unfold BMatch at hBC ⊢
          rw [hmerge]
          exact hBC
      · have hBP : BPos S w v Lopt (j+1) = BPos S w v Lopt j := by
          unfold BPos
          rw [hmerge]
        omega
  | some cw =>
      have hlabel : S.pp.labSet cw (S.pp.A.δ rA.pq w[j])
          = S.pp.labSet cw (S.pp.A.stateBefore w (j+1)) := by
        rw [hApq', ← pp_stateBefore_succ S w j hjn]
      by_cases hkeep : (rA.bc.isSome && S.dir) = true
      · -- keep the standing best (`dir = true`, best already set)
        have hkeep' := hkeep
        rw [Bool.and_eq_true] at hkeep'
        obtain ⟨hisSome, hdir⟩ := hkeep'
        have hstepB : (mach S).StepsN w (cfg S Tag.sB rA posA) []
            (cfg S Tag.sC rA posA) 1 := by
          refine step_one S ?_ (guard_stayAll S _) posA (by funext i; rfl)
          rw [hcoreB, hbest]
          show (if (rA.bc.isSome && S.dir) = true
              then some ((Tag.sC, rA), stayAll S, noOps, [])
              else some ((Tag.sWalk, { rA with
                  bc := some cw
                  bl := some (S.pp.labSet cw (S.pp.A.δ rA.pq w[j])) }),
                stayAll S, noOps, []))
            = some ((Tag.sC, rA), stayAll S, noOps, [])
          rw [if_pos hkeep]
        obtain ⟨r', pos', hstepC, hCdq, hCpq, hCsq, hCvr, hClc, hCbc, hCbl, hCpastL,
          hCvals, hCsc, hCL, hCB, hCV⟩ :=
          stepC S w j hjn rA posA hAsq' (fun c => (hAvals c).1) (fun c => (hAvals c).2) hAscan
        have hmerge : bestUpTo S w v Lopt (j+1) = bestUpTo S w v Lopt j := by
          show mergeB S (bestUpTo S w v Lopt j) (bestAt S w v Lopt j) j = _
          rw [hbest]
          cases hbu : bestUpTo S w v Lopt j with
          | none =>
              exfalso
              have hBn := hBA
              unfold BMatch at hBn
              rw [hbu] at hBn
              rw [hBn.1] at hisSome
              exact Bool.noConfusion hisSome
          | some b =>
              show (if S.dir then some b else some (cw, j)) = some b
              rw [if_pos hdir]
        refine ⟨r', pos', 3, ?_, ?_, ?_⟩
        · have h3 := MHC.StepsN.trans (MHC.StepsN.trans hstepA hstepB) hstepC
          simpa using h3
        · refine ⟨by omega, ?_, ?_, hCsq, ?_, ?_, ?_, fun c => (hCvals c).1,
            fun c => (hCvals c).2, hCsc, ?_, ?_⟩
          · rw [hCdq, hAdq, H.hdq]
          · rw [hCpq, hApq', ← pp_stateBefore_succ S w j hjn]
          · rw [hCvr, hCV]
            exact hAvv
          · rw [hCvr, hCV]
            exact hAvc
          · rw [hCV, hAV]
            exact H.hvh
          · exact LMatch_advance S (by rw [hClc, hAlc]) hCpastL hAscan hCL hLA
          · have hBC : BMatch S w v Lopt j r' pos' :=
              BMatch_transfer S (by rw [hCbc]) (by rw [hCbl]) (by rw [hCB]) hBA
            unfold BMatch at hBC ⊢
            rw [hmerge]
            exact hBC
        · have hBP : BPos S w v Lopt (j+1) = BPos S w v Lopt j := by
            unfold BPos
            rw [hmerge]
          omega
      · -- take the candidate: `B` walks to the scan head
        set rB : Reg S := { rA with
          bc := some cw
          bl := some (S.pp.labSet cw (S.pp.A.δ rA.pq w[j])) } with hrB
        have hstepB : (mach S).StepsN w (cfg S Tag.sB rA posA) []
            (cfg S Tag.sWalk rB posA) 1 := by
          refine step_one S ?_ (guard_stayAll S _) posA (by funext i; rfl)
          rw [hcoreB, hbest]
          show (if (rA.bc.isSome && S.dir) = true
              then some ((Tag.sC, rA), stayAll S, noOps, [])
              else some ((Tag.sWalk, { rA with
                  bc := some cw
                  bl := some (S.pp.labSet cw (S.pp.A.δ rA.pq w[j])) }),
                stayAll S, noOps, []))
            = some ((Tag.sWalk, rB), stayAll S, noOps, [])
          rw [if_neg hkeep]
        have hBpos : posA (BI S) = BPos S w v Lopt j := by
          have hBn := hBA
          unfold BMatch at hBn
          unfold BPos
          cases hbu : bestUpTo S w v Lopt j with
          | none => rw [hbu] at hBn; exact hBn.2.1
          | some b => rw [hbu] at hBn; exact hBn.2.1
        have hBle := BPos_le S w v Lopt j
        obtain ⟨posW, hwalk, hWsc, hWB, hWL, hWV, hWvals⟩ :=
          stepWalk S w rB ((j+1) - BPos S w v Lopt j) posA (j+1) hAscan
            (by omega) (by rw [hBpos]; omega) (by omega)
        obtain ⟨r', pos', hstepC, hCdq, hCpq, hCsq, hCvr, hClc, hCbc, hCbl, hCpastL,
          hCvals, hCsc, hCL, hCB, hCV⟩ :=
          stepC S w j hjn rB posW (fun c => hAsq' c)
            (fun c => by rw [hWvals c]; exact (hAvals c).1)
            (fun c => by rw [hWvals c]; exact (hAvals c).2) hWsc
        have hmerge : bestUpTo S w v Lopt (j+1) = some (cw, j) := by
          show mergeB S (bestUpTo S w v Lopt j) (bestAt S w v Lopt j) j = _
          rw [hbest]
          cases hbu : bestUpTo S w v Lopt j with
          | none => rfl
          | some b =>
              show (if S.dir then some b else some (cw, j)) = some (cw, j)
              have hdirf : S.dir = false := by
                have hBn := hBA
                unfold BMatch at hBn
                rw [hbu] at hBn
                cases hd : S.dir
                · rfl
                · exfalso
                  apply hkeep
                  rw [Bool.and_eq_true]
                  refine ⟨?_, hd⟩
                  rw [hBn.1]
                  rfl
              rw [if_neg (by rw [hdirf]; simp)]
        refine ⟨r', pos', 4 + ((j+1) - BPos S w v Lopt j), ?_, ?_, ?_⟩
        · have h4 := MHC.StepsN.trans (MHC.StepsN.trans (MHC.StepsN.trans hstepA hstepB)
            hwalk) hstepC
          have hlen : 1 + 1 + ((j+1) - BPos S w v Lopt j + 1) + 1
              = 4 + ((j+1) - BPos S w v Lopt j) := by omega
          rw [← hlen]
          simpa using h4
        · refine ⟨by omega, ?_, ?_, hCsq, ?_, ?_, ?_, fun c => (hCvals c).1,
            fun c => (hCvals c).2, hCsc, ?_, ?_⟩
          · rw [hCdq]
            show rA.dq = dq
            rw [hAdq, H.hdq]
          · rw [hCpq]
            show S.pp.A.δ rA.pq w[j] = _
            rw [hApq', ← pp_stateBefore_succ S w j hjn]
          · rw [hCvr, hCV, hWV]
            show repVal S rA.vr (posA (VI S)) = v
            exact hAvv
          · rw [hCvr, hCV, hWV]
            show RepCanon S rA.vr (posA (VI S))
            exact hAvc
          · rw [hCV, hWV, hAV]
            exact H.hvh
          · refine LMatch_advance S (r := rA) (r' := r') (pos := posA) (pos' := pos')
              ?_ ?_ hAscan (by rw [hCL, hWL]) hLA
            · rw [hClc]
            · rw [hCpastL, hWsc, hWL, hAscan]
          · unfold BMatch
            rw [hmerge]
            refine ⟨by rw [hCbc], by rw [hCB, hWB], ?_⟩
            rw [hCbl]
            show some (S.pp.labSet cw (S.pp.A.δ rA.pq w[j])) = _
            rw [hlabel]
        · have hBP : BPos S w v Lopt (j+1) = j + 1 := by
            unfold BPos
            rw [hmerge]
          omega

end SRRQuadratic


namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- The `parkL` walk: the `L` head returns to `⊢`, then hands over to `walkL`. -/
theorem parkL_run (w : List Step) (r : Reg S) :
    ∀ (d : ℕ) (pos : Fin (numH S) → ℕ), pos (LI S) = d →
    ∃ pos', (mach S).StepsN w (cfg S Tag.parkL r pos) [] (cfg S Tag.walkL r pos') (d + 1) ∧
      pos' (scanI S) = pos (scanI S) ∧ pos' (LI S) = 0 ∧ pos' (BI S) = pos (BI S) ∧
      pos' (VI S) = pos (VI S) ∧ (∀ c, pos' (valI S c) = pos (valI S c)) := by
  intro d
  induction d with
  | zero =>
      intro pos hL
      have hcore : etaCore S (Tag.parkL, r) (fun i => tapeSym w (pos i))
          (fun i j => pos i == pos j) = some ((Tag.walkL, r), stayAll S, noOps, []) := by
        rw [etaCore_parkL]
        show etaParkL S r (tapeSym w (pos (LI S))) = _
        rw [hL, tapeSym_zero]
        rfl
      exact ⟨pos, step_one S hcore (guard_stayAll S _) pos (by funext i; rfl),
        rfl, hL, rfl, rfl, fun c => rfl⟩
  | succ d ih =>
      intro pos hL
      set mv1 : Fin (numH S) → HeadMove :=
        mkF S .stay .left .stay .stay (fun _ => .stay) with hmv1
      set pos1 : Fin (numH S) → ℕ := fun i => (mv1 i).apply (pos i) with hpos1
      have hstep : (mach S).StepsN w (cfg S Tag.parkL r pos) []
          (cfg S Tag.parkL r pos1) 1 := by
        refine step_one S ?_ ?_ _ hpos1
        · rw [etaCore_parkL]
          show etaParkL S r (tapeSym w (pos (LI S))) = _
          unfold etaParkL
          rw [if_neg (by rw [hL, tapeSym_lmark_iff]; omega)]
        · rw [hmv1]
          exact guard_mkF S _ _ _ _ _ (fun _ => stay_ne_right) (fun _ => left_ne_right)
            (fun _ => stay_ne_right) (fun _ => stay_ne_right) (fun _ _ => stay_ne_right)
      have h1L : pos1 (LI S) = d := by
        rw [hpos1]
        show (mv1 (LI S)).apply _ = _
        rw [hmv1, mkF_L, HeadMove.apply_left, hL]
        omega
      obtain ⟨pos', hrun, hsc', hL', hB', hV', hval'⟩ := ih pos1 h1L
      refine ⟨pos', ?_, ?_, hL', ?_, ?_, ?_⟩
      · have h12 := MHC.StepsN.trans hstep hrun
        rw [show d + 1 + 1 = 1 + (d + 1) by omega]
        simpa using h12
      · rw [hsc', hpos1]
        show (mv1 (scanI S)).apply _ = _
        rw [hmv1, mkF_scan]
        rfl
      · rw [hB', hpos1]
        show (mv1 (BI S)).apply _ = _
        rw [hmv1, mkF_B]
        rfl
      · rw [hV', hpos1]
        show (mv1 (VI S)).apply _ = _
        rw [hmv1, mkF_V]
        rfl
      · intro c
        rw [hval' c, hpos1]
        show (mv1 (valI S c)).apply _ = _
        rw [hmv1, mkF_val]
        rfl

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- The `walkL` walk: the `L` head walks right to the `B` head, then the new
last-emitted copy is recorded. -/
theorem walkL_run (w : List Step) (r : Reg S) :
    ∀ (d : ℕ) (pos : Fin (numH S) → ℕ) (tB : ℕ), pos (BI S) = tB → tB ≤ w.length + 1 →
    pos (LI S) = tB - d → d ≤ tB →
    ∃ pos', (mach S).StepsN w (cfg S Tag.walkL r pos) []
        (cfg S Tag.rewindK { r with lc := r.bc } pos') (d + 1) ∧
      pos' (scanI S) = pos (scanI S) ∧ pos' (LI S) = tB ∧ pos' (BI S) = tB ∧
      pos' (VI S) = pos (VI S) ∧ (∀ c, pos' (valI S c) = pos (valI S c)) := by
  intro d
  induction d with
  | zero =>
      intro pos tB hB hBle hL hd
      have hLB : pos (LI S) = tB := by omega
      have hcore : etaCore S (Tag.walkL, r) (fun i => tapeSym w (pos i))
          (fun i j => pos i == pos j)
          = some ((Tag.rewindK, { r with lc := r.bc }), stayAll S, noOps, []) := by
        rw [etaCore_walkL]
        show etaWalkL S r (pos (LI S) == pos (BI S)) = _
        rw [show (pos (LI S) == pos (BI S)) = true by rw [beq_iff_eq, hLB, hB]]
        rfl
      exact ⟨pos, step_one S hcore (guard_stayAll S _) pos (by funext i; rfl),
        rfl, hLB, hB, rfl, fun c => rfl⟩
  | succ d ih =>
      intro pos tB hB hBle hL hd
      set mv1 : Fin (numH S) → HeadMove :=
        mkF S .stay .right .stay .stay (fun _ => .stay) with hmv1
      set pos1 : Fin (numH S) → ℕ := fun i => (mv1 i).apply (pos i) with hpos1
      have hstep : (mach S).StepsN w (cfg S Tag.walkL r pos) []
          (cfg S Tag.walkL r pos1) 1 := by
        refine step_one S ?_ ?_ _ hpos1
        · rw [etaCore_walkL]
          show etaWalkL S r (pos (LI S) == pos (BI S)) = _
          rw [show (pos (LI S) == pos (BI S)) = false by
            rw [beq_eq_false_iff_ne, hL, hB]; omega]
          rfl
        · rw [hmv1]
          refine guard_mkF S _ _ _ _ _ (fun _ => stay_ne_right) (fun hrm => ?_)
            (fun _ => stay_ne_right) (fun _ => stay_ne_right) (fun _ _ => stay_ne_right)
          exact absurd ((tapeSym_rmark_iff w _).mp hrm) (by rw [hL]; omega)
      have h1L : pos1 (LI S) = tB - d := by
        rw [hpos1]
        show (mv1 (LI S)).apply _ = _
        rw [hmv1, mkF_L, HeadMove.apply_right, hL]
        omega
      have h1B : pos1 (BI S) = tB := by
        rw [hpos1]
        show (mv1 (BI S)).apply _ = _
        rw [hmv1, mkF_B]
        exact hB
      obtain ⟨pos', hrun, hsc', hL', hB', hV', hval'⟩ :=
        ih pos1 tB h1B hBle h1L (by omega)
      refine ⟨pos', ?_, ?_, hL', hB', ?_, ?_⟩
      · have h12 := MHC.StepsN.trans hstep hrun
        rw [show d + 1 + 1 = 1 + (d + 1) by omega]
        simpa using h12
      · rw [hsc', hpos1]
        show (mv1 (scanI S)).apply _ = _
        rw [hmv1, mkF_scan]
        rfl
      · rw [hV', hpos1]
        show (mv1 (VI S)).apply _ = _
        rw [hmv1, mkF_V]
        rfl
      · intro c
        rw [hval' c, hpos1]
        show (mv1 (valI S c)).apply _ = _
        rw [hmv1, mkF_val]
        rfl

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- The parallel rewind: scan, `B`, and per-copy heads (and, for
`rewindAll`, the `L` head) return to `⊢` simultaneously; the transition on
all-`⊢` resets the scan registers and hands over to `scanStart`. -/
theorem rewind_run (w : List Step) (isL : Bool) (tg : Tag) (r : Reg S)
    (htg : (tg = Tag.rewindAll ∧ isL = true) ∨ (tg = Tag.rewindK ∧ isL = false)) :
    ∀ (t : ℕ) (pos : Fin (numH S) → ℕ),
    pos (scanI S) ≤ t → pos (BI S) ≤ t → (∀ c, pos (valI S c) ≤ t) →
    (isL = true → pos (LI S) ≤ t) →
    ∃ pos' len, (mach S).StepsN w (cfg S tg r pos) []
        (cfg S Tag.scanStart (resetReg S r) pos') len ∧ len ≤ t + 1 ∧
      pos' (scanI S) = 0 ∧ pos' (BI S) = 0 ∧ (∀ c, pos' (valI S c) = 0) ∧
      pos' (VI S) = pos (VI S) ∧ (isL = true → pos' (LI S) = 0) ∧
      (isL = false → pos' (LI S) = pos (LI S)) := by
  have hcoreRW : ∀ (pos : Fin (numH S) → ℕ),
      etaCore S (tg, r) (fun i => tapeSym w (pos i)) (fun i j => pos i == pos j)
        = etaRewind S isL r (tapeSym w (pos (scanI S))) (tapeSym w (pos (LI S)))
            (tapeSym w (pos (BI S))) (fun c => tapeSym w (pos (valI S c))) := by
    rcases htg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> intro pos <;> rfl
  have htag : (if isL then Tag.rewindAll else Tag.rewindK) = tg := by
    rcases htg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  intro t
  induction t with
  | zero =>
      intro pos hsc hB hvals hLc
      have hallpos : pos (scanI S) = 0 ∧ pos (BI S) = 0 ∧ (∀ c, pos (valI S c) = 0) := by
        refine ⟨by omega, by omega, fun c => by have := hvals c; omega⟩
      have hcond : tapeSym w (pos (scanI S)) = TapeSym.lmark ∧
          (isL = true → tapeSym w (pos (LI S)) = TapeSym.lmark) ∧
          tapeSym w (pos (BI S)) = TapeSym.lmark ∧
          ∀ c, tapeSym w (pos (valI S c)) = TapeSym.lmark := by
        refine ⟨by rw [tapeSym_lmark_iff]; omega, fun hL => ?_,
          by rw [tapeSym_lmark_iff]; omega,
          fun c => by rw [tapeSym_lmark_iff]; have := hvals c; omega⟩
        have := hLc hL
        rw [tapeSym_lmark_iff]
        omega
      have hcore : etaCore S (tg, r) (fun i => tapeSym w (pos i))
          (fun i j => pos i == pos j)
          = some ((Tag.scanStart, resetReg S r), stayAll S, noOps, []) := by
        rw [hcoreRW pos]
        unfold etaRewind
        rw [if_pos hcond]
      refine ⟨pos, 1, step_one S hcore (guard_stayAll S _) pos (by funext i; rfl),
        le_refl _, hallpos.1, hallpos.2.1, hallpos.2.2, rfl, fun hL => ?_, fun _ => rfl⟩
      have := hLc hL
      omega
  | succ t ih =>
      intro pos hsc hB hvals hLc
      by_cases hall : pos (scanI S) = 0 ∧ (isL = true → pos (LI S) = 0) ∧
          pos (BI S) = 0 ∧ (∀ c, pos (valI S c) = 0)
      · obtain ⟨h1, h2, h3, h4⟩ := hall
        have hcond : tapeSym w (pos (scanI S)) = TapeSym.lmark ∧
            (isL = true → tapeSym w (pos (LI S)) = TapeSym.lmark) ∧
            tapeSym w (pos (BI S)) = TapeSym.lmark ∧
            ∀ c, tapeSym w (pos (valI S c)) = TapeSym.lmark := by
          refine ⟨by rw [tapeSym_lmark_iff]; omega, fun hL => ?_,
            by rw [tapeSym_lmark_iff]; omega,
            fun c => by rw [tapeSym_lmark_iff]; have := h4 c; omega⟩
          have := h2 hL
          rw [tapeSym_lmark_iff]
          omega
        have hcore : etaCore S (tg, r) (fun i => tapeSym w (pos i))
            (fun i j => pos i == pos j)
            = some ((Tag.scanStart, resetReg S r), stayAll S, noOps, []) := by
          rw [hcoreRW pos]
          unfold etaRewind
          rw [if_pos hcond]
        refine ⟨pos, 1, step_one S hcore (guard_stayAll S _) pos (by funext i; rfl),
          by omega, h1, h3, h4, rfl, fun hL => h2 hL, fun _ => rfl⟩
      · -- one parallel backward step
        have hcond : ¬ (tapeSym w (pos (scanI S)) = TapeSym.lmark ∧
            (isL = true → tapeSym w (pos (LI S)) = TapeSym.lmark) ∧
            tapeSym w (pos (BI S)) = TapeSym.lmark ∧
            ∀ c, tapeSym w (pos (valI S c)) = TapeSym.lmark) := by
          intro hc
          apply hall
          refine ⟨(tapeSym_lmark_iff w _).mp hc.1,
            fun hL => (tapeSym_lmark_iff w _).mp (hc.2.1 hL),
            (tapeSym_lmark_iff w _).mp hc.2.2.1,
            fun c => (tapeSym_lmark_iff w _).mp (hc.2.2.2 c)⟩
        set mv1 : Fin (numH S) → HeadMove := mkF S (mvBack (tapeSym w (pos (scanI S))))
          (if isL then mvBack (tapeSym w (pos (LI S))) else .stay)
          (mvBack (tapeSym w (pos (BI S)))) .stay
          (fun c => mvBack (tapeSym w (pos (valI S c)))) with hmv1
        set pos1 : Fin (numH S) → ℕ := fun i => (mv1 i).apply (pos i) with hpos1
        have hmvback : ∀ i : ℕ, (mvBack (tapeSym w i)).apply i = i - 1 := by
          intro i
          unfold mvBack
          by_cases hi : tapeSym w i = TapeSym.lmark
          · rw [if_pos hi, HeadMove.apply_stay]
            rw [tapeSym_lmark_iff] at hi
            omega
          · rw [if_neg hi, HeadMove.apply_left]
        have hstep : (mach S).StepsN w (cfg S tg r pos) [] (cfg S tg r pos1) 1 := by
          refine step_one S ?_ ?_ _ hpos1
          · rw [hcoreRW pos]
            unfold etaRewind
            rw [if_neg hcond, htag]
          · rw [hmv1]
            refine guard_mkF S _ _ _ _ _ (fun _ => mvBack_ne_right _)
              (fun _ => ?_) (fun _ => mvBack_ne_right _) (fun _ => stay_ne_right)
              (fun c _ => mvBack_ne_right _)
            cases isL
            · exact stay_ne_right
            · exact mvBack_ne_right _
        have h1sc : pos1 (scanI S) = pos (scanI S) - 1 := by
          rw [hpos1]
          show (mv1 (scanI S)).apply _ = _
          rw [hmv1, mkF_scan, hmvback]
        have h1B : pos1 (BI S) = pos (BI S) - 1 := by
          rw [hpos1]
          show (mv1 (BI S)).apply _ = _
          rw [hmv1, mkF_B, hmvback]
        have h1vals : ∀ c, pos1 (valI S c) = pos (valI S c) - 1 := by
          intro c
          rw [hpos1]
          show (mv1 (valI S c)).apply _ = _
          rw [hmv1, mkF_val, hmvback]
        have h1V : pos1 (VI S) = pos (VI S) := by
          rw [hpos1]
          show (mv1 (VI S)).apply _ = _
          rw [hmv1, mkF_V]
          rfl
        have h1L : (isL = true → pos1 (LI S) = pos (LI S) - 1) ∧
            (isL = false → pos1 (LI S) = pos (LI S)) := by
          constructor <;> intro hL <;> rw [hpos1] <;>
            (show (mv1 (LI S)).apply _ = _) <;> rw [hmv1, mkF_L, hL]
          · show (mvBack (tapeSym w (pos (LI S)))).apply _ = _
            rw [hmvback]
          · rfl
        obtain ⟨pos', len', hrun, hlen', hsc', hB', hvals', hV', hLt', hLf'⟩ :=
          ih pos1 (by omega) (by omega) (fun c => by rw [h1vals c]; have := hvals c; omega)
            (fun hL => by rw [h1L.1 hL]; have := hLc hL; omega)
        have hfull := MHC.StepsN.trans hstep hrun
        rw [List.nil_append] at hfull
        refine ⟨pos', 1 + len', hfull, by omega, hsc', hB', hvals', ?_, hLt', ?_⟩
        · rw [hV', h1V]
        · intro hL
          rw [hLf' hL, h1L.2 hL]

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- The `scanStart` step: the scan head moves onto cell 1. -/
theorem scanStart_step (w : List Step) (r : Reg S) (pos : Fin (numH S) → ℕ)
    (hsc : pos (scanI S) = 0) :
    ∃ pos', (mach S).StepsN w (cfg S Tag.scanStart r pos) [] (cfg S Tag.sA r pos') 1 ∧
      pos' (scanI S) = 1 ∧ pos' (LI S) = pos (LI S) ∧ pos' (BI S) = pos (BI S) ∧
      pos' (VI S) = pos (VI S) ∧ (∀ c, pos' (valI S c) = pos (valI S c)) := by
  set mv1 : Fin (numH S) → HeadMove :=
    mkF S .right .stay .stay .stay (fun _ => .stay) with hmv1
  refine ⟨fun i => (mv1 i).apply (pos i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine step_one S ?_ ?_ _ rfl
    · rw [etaCore_scanStart]
      rfl
    · rw [hmv1]
      refine guard_mkF S _ _ _ _ _ (fun hrm => ?_) (fun _ => stay_ne_right)
        (fun _ => stay_ne_right) (fun _ => stay_ne_right) (fun _ _ => stay_ne_right)
      rw [hsc, tapeSym_zero] at hrm
      simp at hrm
  · show (mv1 (scanI S)).apply _ = _
    rw [hmv1, mkF_scan, HeadMove.apply_right, hsc]
  · show (mv1 (LI S)).apply _ = _
    rw [hmv1, mkF_L]
    rfl
  · show (mv1 (BI S)).apply _ = _
    rw [hmv1, mkF_B]
    rfl
  · show (mv1 (VI S)).apply _ = _
    rw [hmv1, mkF_V]
    rfl
  · intro c
    show (mv1 (valI S c)).apply _ = _
    rw [hmv1, mkF_val]
    rfl

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- Establishing the scan invariant at cell `0` for a freshly reset scan. -/
theorem scanInv_establish (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ))
    (dq : S.DA.Q) (r₀ : Reg S) (pos : Fin (numH S) → ℕ)
    (hdq : r₀.dq = dq)
    (hpq : r₀.pq = S.pp.A.q0) (hsq : ∀ c, r₀.sq c = (src S c).q0)
    (hcr : ∀ c, r₀.cr c = repC0 S c)
    (hbc : r₀.bc = none) (hbl : r₀.bl = none) (hpl : r₀.pastL = false)
    (hvv : repVal S r₀.vr (pos (VI S)) = v) (hvc : RepCanon S r₀.vr (pos (VI S)))
    (hvh : pos (VI S) ≤ w.length + 1)
    (hsc : pos (scanI S) = 1) (hB : pos (BI S) = 0)
    (hvals : ∀ c, pos (valI S c) = 0)
    (hLm : match Lopt with
      | none => r₀.lc = none ∧ pos (LI S) = 0
      | some l => r₀.lc = some l.1 ∧ pos (LI S) = l.2 + 1 ∧ l.2 < w.length) :
    ScanInv S w v Lopt dq 0 r₀ pos := by
  refine ⟨Nat.zero_le _, hdq, hpq, hsq, hvv, hvc, hvh, ?_, ?_, hsc, ?_, ?_⟩
  · intro c
    rw [hcr c, hvals c, prefS_zero, add_zero]
    exact (repC0_spec S c).1
  · intro c
    rw [hcr c, hvals c]
    exact (repC0_spec S c).2
  · unfold LMatch
    cases hlo : Lopt with
    | none =>
        rw [hlo] at hLm
        exact ⟨hLm.1, hLm.2, hpl⟩
    | some l =>
        rw [hlo] at hLm
        refine ⟨hLm.1, hLm.2.1, hLm.2.2, ?_⟩
        rw [hpl]
        exact iff_of_false (fun h => Bool.noConfusion h) (by omega)
  · unfold BMatch
    show (match (none : Option (Fin S.K × ℕ)) with
      | none => r₀.bc = none ∧ pos (BI S) = 0 ∧ r₀.bl = none
      | some b => r₀.bc = some b.1 ∧ pos (BI S) = b.2 + 1 ∧
          r₀.bl = some (S.pp.labSet b.1 (S.pp.A.stateBefore w (b.2 + 1))))
    exact ⟨hbc, hB, hbl⟩

/-- **The scan**: from the invariant at cell `j` to the end of the tape. -/
theorem scan_run (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ)) (dq : S.DA.Q) :
    ∀ (m j : ℕ), j + m = w.length → ∀ (r : Reg S) (pos : Fin (numH S) → ℕ),
    ScanInv S w v Lopt dq j r pos →
    ∃ r' pos' len, (mach S).StepsN w (cfg S Tag.sA r pos) [] (cfg S Tag.sA r' pos') len ∧
      ScanInv S w v Lopt dq w.length r' pos' ∧
      len + 4 * j + BPos S w v Lopt j ≤ 4 * w.length + BPos S w v Lopt w.length := by
  intro m
  induction m with
  | zero =>
      intro j hj r pos H
      have hjn : j = w.length := by omega
      subst hjn
      exact ⟨r, pos, 0, MHC.StepsN.refl _, H, by omega⟩
  | succ m ih =>
      intro j hj r pos H
      have hjn : j < w.length := by omega
      obtain ⟨r1, pos1, len1, hrun1, H1, hlen1⟩ := cell_step S w v Lopt dq j r pos H hjn
      obtain ⟨r', pos', len', hrun', H', hlen'⟩ := ih (j+1) (by omega) r1 pos1 H1
      have hmono := BPos_mono S w v Lopt j
      refine ⟨r', pos', len1 + len', ?_, H', by omega⟩
      have h := MHC.StepsN.trans hrun1 hrun'
      simpa using h

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- **Round end, emit case**: at `⊣` with a best `b`, the machine emits its
cached label, re-seats `L` on `b`, rewinds, and re-establishes the invariant
at cell `0` with gate `some b`. -/
theorem round_emit (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ))
    (dq : S.DA.Q) (r : Reg S) (pos : Fin (numH S) → ℕ)
    (H : ScanInv S w v Lopt dq w.length r pos)
    (b : Fin S.K × ℕ) (hb : bestUpTo S w v Lopt w.length = some b) :
    ∃ r' pos' len,
      (mach S).StepsN w (cfg S Tag.sA r pos)
        [S.pp.labSet b.1 (S.pp.A.stateBefore w (b.2+1))] (cfg S Tag.sA r' pos') len ∧
      ScanInv S w v (some b) dq 0 r' pos' ∧ len ≤ 3 * w.length + 9 := by
  have hBM := H.hB
  unfold BMatch at hBM
  rw [hb] at hBM
  obtain ⟨hbc, hBpos, hbl⟩ := hBM
  have hb2 : b.2 < w.length := bestUpTo_pos_lt S w v Lopt w.length b hb
  -- (i) the emit step into `parkL`
  have hcoreE : etaCore S (Tag.sA, r) (fun i => tapeSym w (pos i))
      (fun i j => pos i == pos j)
      = some ((Tag.parkL, r), stayAll S, noOps,
          [S.pp.labSet b.1 (S.pp.A.stateBefore w (b.2+1))]) := by
    rw [etaCore_sA]
    show etaSA S r (tapeSym w (pos (scanI S))) (tapeSym w (pos (VI S)))
      (fun c => tapeSym w (pos (valI S c)) == TapeSym.lmark) = _
    rw [H.hsc, tapeSym_ge w _ (by omega)]
    unfold etaSA
    rw [hbc, hbl]
    rfl
  have hstepE : (mach S).StepsN w (cfg S Tag.sA r pos)
      [S.pp.labSet b.1 (S.pp.A.stateBefore w (b.2+1))] (cfg S Tag.parkL r pos) 1 :=
    step_one S hcoreE (guard_stayAll S _) pos (by funext i; rfl)
  -- (ii) park `L`
  obtain ⟨pos2, hrun2, h2sc, h2L, h2B, h2V, h2vals⟩ :=
    parkL_run S w r (pos (LI S)) pos rfl
  -- (iii) walk `L` to `B`
  obtain ⟨pos3, hrun3, h3sc, h3L, h3B, h3V, h3vals⟩ :=
    walkL_run S w r (b.2+1) pos2 (b.2+1) (by rw [h2B, hBpos]) (by omega)
      (by rw [h2L]; omega) (le_refl _)
  -- (iv) rewind (keeping `L`)
  have hvallt : ∀ c, pos (valI S c) < w.length + 1 := fun c => ScanInv.valhead_lt S H c
  obtain ⟨pos4, len4, hrun4, hlen4, h4sc, h4B, h4vals, h4V, -, h4L⟩ :=
    rewind_run S w false Tag.rewindK { r with lc := r.bc } (Or.inr ⟨rfl, rfl⟩)
      (w.length + 1) pos3
      (by rw [h3sc, h2sc, H.hsc])
      (by rw [h3B]; omega)
      (by intro c; rw [h3vals c, h2vals c]; have := hvallt c; omega)
      (by intro h; exact Bool.noConfusion h)
  -- (v) restart the scan
  obtain ⟨pos5, hrun5, h5sc, h5L, h5B, h5V, h5vals⟩ :=
    scanStart_step S w (resetReg S { r with lc := r.bc }) pos4 h4sc
  -- assemble
  refine ⟨resetReg S { r with lc := r.bc }, pos5, 1 + ((pos (LI S)) + 1) + (b.2 + 1 + 1)
    + len4 + 1, ?_, ?_, ?_⟩
  · have h := MHC.StepsN.trans (MHC.StepsN.trans (MHC.StepsN.trans
      (MHC.StepsN.trans hstepE hrun2) hrun3) hrun4) hrun5
    simpa using h
  · refine scanInv_establish S w v (some b) dq _ pos5 ?_ rfl (fun c => rfl) (fun c => rfl)
      rfl rfl rfl ?_ ?_ ?_ h5sc (by rw [h5B, h4B]) (fun c => by rw [h5vals c, h4vals c]) ?_
    · show r.dq = dq
      exact H.hdq
    · show repVal S r.vr (pos5 (VI S)) = v
      rw [h5V, h4V, h3V, h2V]
      exact H.hvv
    · show RepCanon S r.vr (pos5 (VI S))
      rw [h5V, h4V, h3V, h2V]
      exact H.hvc
    · rw [h5V, h4V, h3V, h2V]
      exact H.hvh
    · show (resetReg S { r with lc := r.bc }).lc = some b.1 ∧
        pos5 (LI S) = b.2 + 1 ∧ b.2 < w.length
      refine ⟨?_, ?_, hb2⟩
      · show r.bc = some b.1
        exact hbc
      · rw [h5L, h4L rfl, h3L]
  · -- length accounting
    have hLle : pos (LI S) ≤ w.length := by
      have hLM := H.hL
      unfold LMatch at hLM
      cases hlo : Lopt with
      | none =>
          rw [hlo] at hLM
          rw [hLM.2.1]
          exact Nat.zero_le _
      | some l =>
          rw [hlo] at hLM
          rw [hLM.2.1]
          have := hLM.2.2.1
          omega
    omega

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- The greatest enumerated rank level. -/
def vmaxVal (n : ℕ) : ℤ := (Wtot S : ℤ) * (n + 2) - 1

/-- `etaSA` at the right end-marker. -/
theorem etaSA_rmark (r : Reg S) (sV : TapeSym Step) (qzs : Fin S.K → Bool) :
    etaSA S r TapeSym.rmark sV qzs = (match r.bc with
      | some _ => some ((Tag.parkL, r), stayAll S, noOps, r.bl.elim [] (fun g => [g]))
      | none =>
          if r.vr.1 = true ∧ (r.vr.2 : ℕ) = Wtot S - 1 ∧ sV = TapeSym.rmark
          then some ((Tag.done, r), stayAll S, noOps, [])
          else some ((Tag.rewindAll, { r with
              vr := (repAdd S r.vr (sV == TapeSym.lmark) 1).1
              lc := none }),
            mkF S .stay .stay .stay (repAdd S r.vr (sV == TapeSym.lmark) 1).2
              (fun _ => .stay), noOps, [])) := rfl

theorem repVal_vmax (n : ℕ) :
    repVal S (true, ⟨Wtot S - 1, by have := Wtot_pos S; omega⟩) (n + 1)
      = vmaxVal S n := by
  rw [repVal_mk, sgn_true]
  unfold vmaxVal
  have h1 : ((Wtot S - 1 : ℕ) : ℤ) = (Wtot S : ℤ) - 1 := by
    have := Wtot_pos S
    omega
  show (Wtot S : ℤ) * ((n + 1 : ℕ) : ℤ) + ((Wtot S - 1 : ℕ) : ℤ) = _
  rw [h1]
  push_cast
  ring

/-- **Round end, level-exhausted case**: at `⊣` with no best and `v` below
the maximal level, the machine advances the level, clears `L`, rewinds, and
re-establishes the invariant at cell `0` for level `v + 1`. -/
theorem round_advance (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ))
    (dq : S.DA.Q) (r : Reg S) (pos : Fin (numH S) → ℕ)
    (H : ScanInv S w v Lopt dq w.length r pos)
    (hnone : bestUpTo S w v Lopt w.length = none)
    (hvne : v ≠ vmaxVal S w.length) :
    ∃ r' pos' len, (mach S).StepsN w (cfg S Tag.sA r pos) [] (cfg S Tag.sA r' pos') len ∧
      ScanInv S w (v+1) none dq 0 r' pos' ∧ len ≤ w.length + 4 := by
  have hBM := H.hB
  unfold BMatch at hBM
  rw [hnone] at hBM
  obtain ⟨hbc, hBpos, hbl⟩ := hBM
  -- the done-condition is false
  have hcond : ¬ (r.vr.1 = true ∧ (r.vr.2 : ℕ) = Wtot S - 1
      ∧ tapeSym w (pos (VI S)) = TapeSym.rmark) := by
    rintro ⟨h1, h2, h3⟩
    apply hvne
    have hVn : pos (VI S) = w.length + 1 := by
      have := (tapeSym_rmark_iff w _).mp h3
      have := H.hvh
      omega
    have hrep : r.vr = (true, ⟨Wtot S - 1, by have := Wtot_pos S; omega⟩) := by
      have hsplit : r.vr = (r.vr.1, r.vr.2) := rfl
      rw [hsplit, h1]
      exact congrArg _ (Fin.ext h2)
    rw [← H.hvv, hrep, hVn]
    exact repVal_vmax S w.length
  set qzv : Bool := (tapeSym w (pos (VI S)) == TapeSym.lmark) with hqzv
  set rInc : Reg S := { r with vr := (repAdd S r.vr qzv 1).1, lc := none, bc := none }
    with hrInc
  set mvV : Fin (numH S) → HeadMove :=
    mkF S .stay .stay .stay (repAdd S r.vr qzv 1).2 (fun _ => .stay) with hmvV
  have hqziff : qzv = true ↔ pos (VI S) = 0 := by
    rw [hqzv]
    show (tapeSym w (pos (VI S)) == TapeSym.lmark) = true ↔ _
    rw [beq_iff_eq, tapeSym_lmark_iff]
  have habs1 : (1 : ℤ).natAbs < Wtot S := by
    have := Wtot_ge3 S
    omega
  have hspecV := repAdd_spec S r.vr (pos (VI S)) qzv 1 habs1 H.hvc hqziff
  -- the level-advance step
  have hstepI : (mach S).StepsN w (cfg S Tag.sA r pos) []
      (cfg S Tag.rewindAll rInc (fun i => (mvV i).apply (pos i))) 1 := by
    refine step_one S ?_ ?_ _ rfl
    · rw [etaCore_sA]
      show etaSA S r (tapeSym w (pos (scanI S))) (tapeSym w (pos (VI S))) _ = _
      rw [H.hsc, tapeSym_ge w _ (by omega), etaSA_rmark, hbc]
      show (if r.vr.1 = true ∧ (r.vr.2 : ℕ) = Wtot S - 1
            ∧ tapeSym w (pos (VI S)) = TapeSym.rmark
          then some ((Tag.done, r), stayAll S, noOps, [])
          else some ((Tag.rewindAll, { r with
              vr := (repAdd S r.vr (tapeSym w (pos (VI S)) == TapeSym.lmark) 1).1
              lc := none
              bc := none }),
            mkF S .stay .stay .stay
              (repAdd S r.vr (tapeSym w (pos (VI S)) == TapeSym.lmark) 1).2
              (fun _ => .stay), noOps, []))
        = some ((Tag.rewindAll, rInc), mvV, noOps, [])
      rw [if_neg hcond]
    · rw [hmvV]
      refine guard_mkF S _ _ _ _ _ (fun _ => stay_ne_right) (fun _ => stay_ne_right)
        (fun _ => stay_ne_right) (fun hrm hmv => ?_) (fun _ _ => stay_ne_right)
      obtain ⟨h1, h2⟩ := repAdd_one_right S r.vr qzv hmv
      exact hcond ⟨h1, h2, hrm⟩
  have hVle : (mvV (VI S)).apply (pos (VI S)) ≤ w.length + 1 := by
    rw [hmvV, mkF_V]
    cases hmv : (repAdd S r.vr qzv 1).2
    · rw [HeadMove.apply_left]
      have := H.hvh
      omega
    · rw [HeadMove.apply_stay]
      exact H.hvh
    · rw [HeadMove.apply_right]
      obtain ⟨h1, h2⟩ := repAdd_one_right S r.vr qzv hmv
      have hVn : pos (VI S) ≤ w.length := by
        by_contra hgt
        push Not at hgt
        exact hcond ⟨h1, h2, tapeSym_ge w _ (by omega)⟩
      omega
  -- rewind all heads
  have hvallt : ∀ c, pos (valI S c) < w.length + 1 := fun c => ScanInv.valhead_lt S H c
  obtain ⟨pos4, len4, hrun4, hlen4, h4sc, h4B, h4vals, h4V, h4L, -⟩ :=
    rewind_run S w true Tag.rewindAll rInc (Or.inl ⟨rfl, rfl⟩) (w.length + 1)
      (fun i => (mvV i).apply (pos i))
      (by show (mvV (scanI S)).apply _ ≤ _; rw [hmvV, mkF_scan, HeadMove.apply_stay, H.hsc])
      (by show (mvV (BI S)).apply _ ≤ _; rw [hmvV, mkF_B, HeadMove.apply_stay, hBpos]; omega)
      (by intro c
          show (mvV (valI S c)).apply _ ≤ _
          rw [hmvV, mkF_val, HeadMove.apply_stay]
          have := hvallt c
          omega)
      (by intro _
          show (mvV (LI S)).apply _ ≤ _
          rw [hmvV, mkF_L, HeadMove.apply_stay]
          have hLM := H.hL
          unfold LMatch at hLM
          cases hlo : Lopt with
          | none => rw [hlo] at hLM; rw [hLM.2.1]; omega
          | some l =>
              rw [hlo] at hLM
              rw [hLM.2.1]
              have := hLM.2.2.1
              omega)
  obtain ⟨pos5, hrun5, h5sc, h5L, h5B, h5V, h5vals⟩ :=
    scanStart_step S w (resetReg S rInc) pos4 h4sc
  refine ⟨resetReg S rInc, pos5, 1 + len4 + 1, ?_, ?_, by omega⟩
  · have h := MHC.StepsN.trans (MHC.StepsN.trans hstepI hrun4) hrun5
    simpa using h
  · refine scanInv_establish S w (v+1) none dq _ pos5 ?_ rfl (fun c => rfl) (fun c => rfl)
      rfl rfl rfl ?_ ?_ ?_ h5sc (by rw [h5B, h4B]) (fun c => by rw [h5vals c, h4vals c]) ?_
    · show r.dq = dq
      exact H.hdq
    · show repVal S (repAdd S r.vr qzv 1).1 (pos5 (VI S)) = v + 1
      rw [h5V, h4V]
      show repVal S (repAdd S r.vr qzv 1).1 ((mvV (VI S)).apply (pos (VI S))) = v + 1
      rw [hmvV, mkF_V]
      rw [hspecV.1, H.hvv]
    · show RepCanon S (repAdd S r.vr qzv 1).1 (pos5 (VI S))
      rw [h5V, h4V]
      show RepCanon S (repAdd S r.vr qzv 1).1 ((mvV (VI S)).apply (pos (VI S)))
      rw [hmvV, mkF_V]
      exact hspecV.2
    · rw [h5V, h4V]
      exact hVle
    · show (resetReg S rInc).lc = none ∧ pos5 (LI S) = 0
      exact ⟨rfl, by rw [h5L, h4L rfl]⟩

/-- **Round end, all levels exhausted**: at `⊣` with no best and `v` the
maximal level, the machine halts accepting. -/
theorem round_done (w : List Step) (v : ℤ) (Lopt : Option (Fin S.K × ℕ))
    (dq : S.DA.Q) (r : Reg S) (pos : Fin (numH S) → ℕ)
    (H : ScanInv S w v Lopt dq w.length r pos)
    (hnone : bestUpTo S w v Lopt w.length = none)
    (hv : v = vmaxVal S w.length) :
    (mach S).StepsN w (cfg S Tag.sA r pos) [] (cfg S Tag.done r pos) 1 ∧
      (mach S).Halted w (cfg S Tag.done r pos) ∧
      (mach S).F (Tag.done, r) := by
  have hBM := H.hB
  unfold BMatch at hBM
  rw [hnone] at hBM
  obtain ⟨hbc, hBpos, hbl⟩ := hBM
  -- the level registers must be the maximal-level representation
  have hvmax : r.vr = (true, ⟨Wtot S - 1, by have := Wtot_pos S; omega⟩)
      ∧ pos (VI S) = w.length + 1 := by
    have heq : repVal S r.vr (pos (VI S))
        = repVal S (true, ⟨Wtot S - 1, by have := Wtot_pos S; omega⟩) (w.length + 1) := by
      rw [H.hvv, hv, repVal_vmax]
    have := (repVal_eq_iff S r.vr _ (pos (VI S)) (w.length + 1) H.hvc
      (fun h => Bool.noConfusion h)).mp heq
    exact this
  have hcond : r.vr.1 = true ∧ (r.vr.2 : ℕ) = Wtot S - 1
      ∧ tapeSym w (pos (VI S)) = TapeSym.rmark := by
    rw [hvmax.1, hvmax.2]
    exact ⟨rfl, rfl, tapeSym_ge w _ (by omega)⟩
  have hcoreD : etaCore S (Tag.sA, r) (fun i => tapeSym w (pos i))
      (fun i j => pos i == pos j)
      = some ((Tag.done, r), stayAll S, noOps, []) := by
    rw [etaCore_sA]
    show etaSA S r (tapeSym w (pos (scanI S))) (tapeSym w (pos (VI S))) _ = _
    rw [H.hsc, tapeSym_ge w _ (by omega), etaSA_rmark, hbc]
    show (if r.vr.1 = true ∧ (r.vr.2 : ℕ) = Wtot S - 1
          ∧ tapeSym w (pos (VI S)) = TapeSym.rmark
        then some ((Tag.done, r), stayAll S, noOps, [])
        else some ((Tag.rewindAll, { r with
            vr := (repAdd S r.vr (tapeSym w (pos (VI S)) == TapeSym.lmark) 1).1
            lc := none
            bc := none }),
          mkF S .stay .stay .stay
            (repAdd S r.vr (tapeSym w (pos (VI S)) == TapeSym.lmark) 1).2
            (fun _ => .stay), noOps, []))
      = some ((Tag.done, r), stayAll S, noOps, [])
    rw [if_pos hcond]
  exact ⟨step_one S hcoreD (guard_stayAll S _) pos (by funext i; rfl),
    halted_done S w r pos, rfl⟩

end SRRQuadratic


namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- The output labels of a pair list. -/
noncomputable def labOf (w : List Step) (x : Fin S.K × ℕ) : Gamma :=
  S.P.toPoly.labelOf w (mkAtom S x.1 x.2)

/-- Fiber members' cached machine labels are their declarative labels. -/
theorem fiber_label (w : List Step) (v : ℤ) (x : Fin S.K × ℕ)
    (hx : x ∈ fiber S w v) :
    S.pp.labSet x.1 (S.pp.A.stateBefore w (x.2+1)) = labOf S w x := by
  have hsel : selP S w x.1 x.2 := ((mem_fiber S w v x).mp hx).2.1
  unfold labOf
  rw [labelOf_eq S w x.1 x.2 hsel]

/-- **One value round** (per-level extraction): starting at cell 0 with the
gate at the `k`-th fiber element's predecessor, the machine emits the rest of
the level-`v` fiber and either advances to level `v + 1` or, at the top
level, halts accepting. -/
theorem value_round (w : List Step) (v : ℤ) (dq : S.DA.Q) :
    ∀ (m k : ℕ), k + m = (fiber S w v).length →
    ∀ (Lopt : Option (Fin S.K × ℕ)), LPred S w v k Lopt →
    ∀ (r : Reg S) (pos : Fin (numH S) → ℕ), ScanInv S w v Lopt dq 0 r pos →
    ∃ e len,
      (mach S).StepsN w (cfg S Tag.sA r pos)
        (((fiber S w v).drop k).map (labOf S w)) e len ∧
      len ≤ (m + 1) * (8 * w.length + 13) ∧
      ((v = vmaxVal S w.length ∧ ∃ rd posd, e = cfg S Tag.done rd posd) ∨
       (v ≠ vmaxVal S w.length ∧ ∃ r' pos', e = cfg S Tag.sA r' pos' ∧
          ScanInv S w (v+1) none dq 0 r' pos')) := by
  intro m
  induction m with
  | zero =>
      intro k hk Lopt hLP r pos H
      obtain ⟨rS, posS, lenS, hrunS, HS, hlenS⟩ :=
        scan_run S w v Lopt dq w.length 0 (by omega) r pos H
      have hend : bestUpTo S w v Lopt w.length = (fiber S w v)[k]? :=
        bestUpTo_at_end S w v k Lopt hLP
      rw [List.getElem?_eq_none (by omega)] at hend
      have hdropnil : (fiber S w v).drop k = [] := List.drop_eq_nil_of_le (by omega)
      have hBn := BPos_le S w v Lopt w.length
      by_cases hv : v = vmaxVal S w.length
      · obtain ⟨hstepD, hhalt, hF⟩ := round_done S w v Lopt dq rS posS HS hend hv
        refine ⟨cfg S Tag.done rS posS, lenS + 1, ?_, ?_, Or.inl ⟨hv, rS, posS, rfl⟩⟩
        · have h := MHC.StepsN.trans hrunS hstepD
          rw [hdropnil]
          simpa using h
        · omega
      · obtain ⟨r', pos', lenA, hrunA, H', hlenA⟩ :=
          round_advance S w v Lopt dq rS posS HS hend hv
        refine ⟨cfg S Tag.sA r' pos', lenS + lenA, ?_, ?_,
          Or.inr ⟨hv, r', pos', rfl, H'⟩⟩
        · have h := MHC.StepsN.trans hrunS hrunA
          rw [hdropnil]
          simpa using h
        · omega
  | succ m ih =>
      intro k hk Lopt hLP r pos H
      obtain ⟨rS, posS, lenS, hrunS, HS, hlenS⟩ :=
        scan_run S w v Lopt dq w.length 0 (by omega) r pos H
      have hklen : k < (fiber S w v).length := by omega
      have hend : bestUpTo S w v Lopt w.length = (fiber S w v)[k]? :=
        bestUpTo_at_end S w v k Lopt hLP
      rw [List.getElem?_eq_getElem hklen] at hend
      obtain ⟨rE, posE, lenE, hrunE, HE, hlenE⟩ :=
        round_emit S w v Lopt dq rS posS HS ((fiber S w v)[k]) hend
      have hLP' : LPred S w v (k+1) (some ((fiber S w v)[k])) :=
        lpred_succ S w v k _ (List.getElem?_eq_getElem hklen)
      obtain ⟨e, len', hrun', hlen', hor⟩ :=
        ih (k+1) (by omega) (some ((fiber S w v)[k])) hLP' rE posE HE
      have hBn := BPos_le S w v Lopt w.length
      have hBP0 : BPos S w v Lopt 0 = 0 := rfl
      have hmul : (m + 1 + 1) * (8 * w.length + 13)
          = (m + 1) * (8 * w.length + 13) + (8 * w.length + 13) := by ring
      refine ⟨e, lenS + lenE + len', ?_, ?_, hor⟩
      · have h := MHC.StepsN.trans (MHC.StepsN.trans hrunS hrunE) hrun'
        have hdrop : (fiber S w v).drop k = (fiber S w v)[k] :: (fiber S w v).drop (k+1) :=
          List.drop_eq_getElem_cons hklen
        rw [hdrop, List.map_cons]
        have hlab : S.pp.labSet ((fiber S w v)[k]).1
            (S.pp.A.stateBefore w (((fiber S w v)[k]).2+1)) = labOf S w ((fiber S w v)[k]) :=
          fiber_label S w v _ (List.getElem_mem hklen)
        rw [← hlab]
        simpa using h
      · omega

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

theorem numVals_cast (n : ℕ) :
    (numVals S n : ℤ) = 2 * ((Wtot S : ℤ) * (n + 2)) - 1 := by
  have hpos : 0 < 2 * Wtot S * (n + 2) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (Wtot_pos S)) (by omega)
  unfold numVals
  rw [Nat.cast_sub hpos]
  push_cast
  ring

theorem v_eq_vmax_iff (n t : ℕ) (ht : t < numVals S n) :
    vmin S n + t = vmaxVal S n ↔ t = numVals S n - 1 := by
  have hnv := numVals_cast S n
  have hv : vmin S n = -((Wtot S : ℤ) * (n + 2) - 1) := rfl
  have hvm : vmaxVal S n = (Wtot S : ℤ) * (n + 2) - 1 := rfl
  have htz : (t : ℤ) < (numVals S n : ℤ) := by exact_mod_cast ht
  rw [hv, hvm]
  constructor
  · intro h
    have : (t : ℤ) = (numVals S n : ℤ) - 1 := by
      generalize hT : (Wtot S : ℤ) * (n + 2) = T at h hnv
      omega
    omega
  · intro h
    subst h
    have hc : ((numVals S n - 1 : ℕ) : ℤ) = (numVals S n : ℤ) - 1 := by
      have : 0 < numVals S n := by omega
      omega
    rw [hc]
    generalize hT : (Wtot S : ℤ) * (n + 2) = T at hnv
    omega

/-- **The value loop**: from level `vmin + t` the machine emits the fibers of
all remaining levels in ascending order and halts accepting. -/
theorem value_loop (w : List Step) (dq : S.DA.Q) :
    ∀ (m t : ℕ), t < numVals S w.length → numVals S w.length - 1 - t = m →
    ∀ (r : Reg S) (pos : Fin (numH S) → ℕ),
    ScanInv S w (vmin S w.length + t) none dq 0 r pos →
    ∃ rd posd len,
      (mach S).StepsN w (cfg S Tag.sA r pos)
        (((valueList S w.length).drop t).flatMap (fun v => (fiber S w v).map (labOf S w)))
        (cfg S Tag.done rd posd) len ∧
      len ≤ ((((valueList S w.length).drop t).flatMap (fun v => fiber S w v)).length
          + (numVals S w.length - t)) * (8 * w.length + 13) := by
  intro m
  induction m with
  | zero =>
      intro t ht hm r pos H
      have htlast : t = numVals S w.length - 1 := by omega
      have hvmax : vmin S w.length + t = vmaxVal S w.length :=
        (v_eq_vmax_iff S w.length t ht).mpr htlast
      obtain ⟨e, len, hrun, hlen, hor⟩ :=
        value_round S w (vmin S w.length + t) dq (fiber S w (vmin S w.length + t)).length 0
          (by omega) none (Or.inl ⟨rfl, rfl⟩) r pos H
      rcases hor with ⟨-, rd, posd, rfl⟩ | ⟨hne, -⟩
      · have hlenv : (valueList S w.length).length = numVals S w.length := by
          unfold valueList
          simp
        have htlt : t < (valueList S w.length).length := by omega
        have hgetv : (valueList S w.length)[t] = vmin S w.length + t := by
          simp only [valueList, List.getElem_map, List.getElem_range]
        have hdrop : (valueList S w.length).drop t
            = [vmin S w.length + t] := by
          rw [List.drop_eq_getElem_cons htlt, hgetv,
            List.drop_eq_nil_of_le (by omega)]
        refine ⟨rd, posd, len, ?_, ?_⟩
        · rw [hdrop]
          simpa using hrun
        · rw [hdrop]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hlen ⊢
          have : numVals S w.length - t = 1 := by omega
          rw [this]
          simpa using hlen
      · exact absurd hvmax hne
  | succ m ih =>
      intro t ht hm r pos H
      have hvne : vmin S w.length + t ≠ vmaxVal S w.length := by
        intro heq
        have := (v_eq_vmax_iff S w.length t ht).mp heq
        omega
      obtain ⟨e, len, hrun, hlen, hor⟩ :=
        value_round S w (vmin S w.length + t) dq (fiber S w (vmin S w.length + t)).length 0
          (by omega) none (Or.inl ⟨rfl, rfl⟩) r pos H
      rcases hor with ⟨hveq, -⟩ | ⟨-, r', pos', rfl, H'⟩
      · exact absurd hveq hvne
      · have hnext : vmin S w.length + t + 1 = vmin S w.length + (t + 1 : ℕ) := by
          push_cast
          ring
        rw [hnext] at H'
        obtain ⟨rd, posd, len', hrun', hlen'⟩ :=
          ih (t+1) (by omega) (by omega) r' pos' H'
        have hlenv : (valueList S w.length).length = numVals S w.length := by
          unfold valueList
          simp
        have htlt : t < (valueList S w.length).length := by omega
        have hgetv : (valueList S w.length)[t] = vmin S w.length + t := by
          simp only [valueList, List.getElem_map, List.getElem_range]
        have hdrop : (valueList S w.length).drop t
            = (vmin S w.length + t) :: (valueList S w.length).drop (t+1) := by
          rw [List.drop_eq_getElem_cons htlt, hgetv]
        refine ⟨rd, posd, len + len', ?_, ?_⟩
        · have h := MHC.StepsN.trans hrun hrun'
          rw [hdrop, List.flatMap_cons]
          simpa using h
        · rw [hdrop, List.flatMap_cons, List.length_append]
          have hmul : ((fiber S w (vmin S w.length + t)).length + 1
                + ((((valueList S w.length).drop (t+1)).flatMap
                    (fun v => fiber S w v)).length + (numVals S w.length - (t+1))))
              * (8 * w.length + 13)
              = ((fiber S w (vmin S w.length + t)).length + 1) * (8 * w.length + 13)
                + ((((valueList S w.length).drop (t+1)).flatMap
                    (fun v => fiber S w v)).length + (numVals S w.length - (t+1)))
                  * (8 * w.length + 13) := by ring
          have harith : (((fiber S w (vmin S w.length + t)).length
                + (((valueList S w.length).drop (t+1)).flatMap
                    (fun v => fiber S w v)).length) + (numVals S w.length - t))
              = ((fiber S w (vmin S w.length + t)).length + 1
                + ((((valueList S w.length).drop (t+1)).flatMap
                    (fun v => fiber S w v)).length + (numVals S w.length - (t+1)))) := by
            omega
          rw [harith, hmul]
          omega

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- The domain sweep over the letters. -/
theorem dom_letters (w : List Step) :
    ∀ (m j : ℕ), j + m = w.length → ∀ (r : Reg S) (pos : Fin (numH S) → ℕ),
    r.dq = S.DA.stateBefore w j → pos (scanI S) = j + 1 →
    ∃ r' pos', (mach S).StepsN w (cfg S Tag.domScan r pos) [] (cfg S Tag.domScan r' pos') m ∧
      r'.dq = S.DA.stateBefore w w.length ∧ r'.pq = r.pq ∧ r'.sq = r.sq ∧ r'.vr = r.vr ∧
      r'.cr = r.cr ∧ r'.lc = r.lc ∧ r'.bc = r.bc ∧ r'.bl = r.bl ∧ r'.pastL = r.pastL ∧
      pos' (scanI S) = w.length + 1 ∧ pos' (LI S) = pos (LI S) ∧
      pos' (BI S) = pos (BI S) ∧ pos' (VI S) = pos (VI S) ∧
      (∀ c, pos' (valI S c) = pos (valI S c)) := by
  intro m
  induction m with
  | zero =>
      intro j hj r pos hdq hsc
      have hje : j = w.length := by omega
      subst hje
      exact ⟨r, pos, MHC.StepsN.refl _, hdq, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, hsc, rfl, rfl, rfl, fun c => rfl⟩
  | succ m ih =>
      intro j hj r pos hdq hsc
      have hjn : j < w.length := by omega
      set mv1 : Fin (numH S) → HeadMove :=
        mkF S .right .stay .stay .stay (fun _ => .stay) with hmv1
      set r1 : Reg S := { r with dq := S.DA.δ r.dq w[j] } with hr1
      have hstep : (mach S).StepsN w (cfg S Tag.domScan r pos) []
          (cfg S Tag.domScan r1 (fun i => (mv1 i).apply (pos i))) 1 := by
        refine step_one S ?_ ?_ _ rfl
        · rw [etaCore_domScan]
          show etaDom S r (tapeSym w (pos (scanI S))) = _
          rw [hsc, tapeSym_succ w j hjn]
          rfl
        · rw [hmv1]
          refine guard_mkF S _ _ _ _ _ (fun hrm => ?_) (fun _ => stay_ne_right)
            (fun _ => stay_ne_right) (fun _ => stay_ne_right) (fun _ _ => stay_ne_right)
          exact absurd ((tapeSym_rmark_iff w _).mp hrm) (by rw [hsc]; omega)
      have h1dq : r1.dq = S.DA.stateBefore w (j+1) := by
        show S.DA.δ r.dq w[j] = _
        rw [hdq, ← da_stateBefore_succ S w j hjn]
      have h1sc : (fun i => (mv1 i).apply (pos i)) (scanI S) = (j+1) + 1 := by
        show (mv1 (scanI S)).apply _ = _
        rw [hmv1, mkF_scan, HeadMove.apply_right, hsc]
      obtain ⟨r', pos', hrun, hdq', hpq', hsq', hvr', hcr', hlc', hbc', hbl', hpl',
        hsc', hL', hB', hV', hvals'⟩ :=
        ih (j+1) (by omega) r1 (fun i => (mv1 i).apply (pos i)) h1dq h1sc
      refine ⟨r', pos', ?_, hdq', hpq', hsq', hvr', hcr', hlc', hbc', hbl', hpl',
        hsc', ?_, ?_, ?_, ?_⟩
      · have h := MHC.StepsN.trans hstep hrun
        rw [show m + 1 = 1 + m by omega]
        simpa using h
      · rw [hL']
        show (mv1 (LI S)).apply _ = _
        rw [hmv1, mkF_L]
        rfl
      · rw [hB']
        show (mv1 (BI S)).apply _ = _
        rw [hmv1, mkF_B]
        rfl
      · rw [hV']
        show (mv1 (VI S)).apply _ = _
        rw [hmv1, mkF_V]
        rfl
      · intro c
        rw [hvals' c]
        show (mv1 (valI S c)).apply _ = _
        rw [hmv1, mkF_val]
        rfl

/-- The level-head sweep to `⊣`. -/
theorem vinit_run (w : List Step) (r : Reg S) :
    ∀ (d : ℕ) (pos : Fin (numH S) → ℕ), pos (VI S) = w.length + 1 - d →
    d ≤ w.length + 1 →
    ∃ pos', (mach S).StepsN w (cfg S Tag.vInit r pos) []
        (cfg S Tag.rewindAll
          { r with vr := (false, ⟨Wtot S - 1, by have := Wtot_pos S; omega⟩) } pos')
        (d + 1) ∧
      pos' (scanI S) = pos (scanI S) ∧ pos' (LI S) = pos (LI S) ∧
      pos' (BI S) = pos (BI S) ∧ pos' (VI S) = w.length + 1 ∧
      (∀ c, pos' (valI S c) = pos (valI S c)) := by
  intro d
  induction d with
  | zero =>
      intro pos hV hd
      have hVn : pos (VI S) = w.length + 1 := by omega
      have hcore : etaCore S (Tag.vInit, r) (fun i => tapeSym w (pos i))
          (fun i j => pos i == pos j)
          = some ((Tag.rewindAll,
              { r with vr := (false, ⟨Wtot S - 1, by have := Wtot_pos S; omega⟩) }),
            stayAll S, noOps, []) := by
        rw [etaCore_vInit]
        show etaVInit S r (tapeSym w (pos (VI S))) = _
        rw [hVn, tapeSym_ge w _ (by omega)]
        rfl
      exact ⟨pos, step_one S hcore (guard_stayAll S _) pos (by funext i; rfl),
        rfl, rfl, rfl, hVn, fun c => rfl⟩
  | succ d ih =>
      intro pos hV hd
      set mv1 : Fin (numH S) → HeadMove :=
        mkF S .stay .stay .stay .right (fun _ => .stay) with hmv1
      have hVlt : pos (VI S) ≤ w.length := by omega
      have hstep : (mach S).StepsN w (cfg S Tag.vInit r pos) []
          (cfg S Tag.vInit r (fun i => (mv1 i).apply (pos i))) 1 := by
        refine step_one S ?_ ?_ _ rfl
        · rw [etaCore_vInit]
          show etaVInit S r (tapeSym w (pos (VI S))) = _
          cases hsym : tapeSym w (pos (VI S)) with
          | lmark => rfl
          | letter a => rfl
          | rmark =>
              exact absurd ((tapeSym_rmark_iff w _).mp hsym) (by omega)
        · rw [hmv1]
          refine guard_mkF S _ _ _ _ _ (fun _ => stay_ne_right) (fun _ => stay_ne_right)
            (fun _ => stay_ne_right) (fun hrm => ?_) (fun _ _ => stay_ne_right)
          exact absurd ((tapeSym_rmark_iff w _).mp hrm) (by omega)
      have h1V : (fun i => (mv1 i).apply (pos i)) (VI S) = w.length + 1 - d := by
        show (mv1 (VI S)).apply _ = _
        rw [hmv1, mkF_V, HeadMove.apply_right, hV]
        omega
      obtain ⟨pos', hrun, hsc', hL', hB', hV', hvals'⟩ :=
        ih (fun i => (mv1 i).apply (pos i)) h1V (by omega)
      refine ⟨pos', ?_, ?_, ?_, ?_, hV', ?_⟩
      · have h := MHC.StepsN.trans hstep hrun
        rw [show d + 1 + 1 = 1 + (d + 1) by omega]
        simpa using h
      · rw [hsc']
        show (mv1 (scanI S)).apply _ = _
        rw [hmv1, mkF_scan]
        rfl
      · rw [hL']
        show (mv1 (LI S)).apply _ = _
        rw [hmv1, mkF_L]
        rfl
      · rw [hB']
        show (mv1 (BI S)).apply _ = _
        rw [hmv1, mkF_B]
        rfl
      · intro c
        rw [hvals' c]
        show (mv1 (valI S c)).apply _ = _
        rw [hmv1, mkF_val]
        rfl

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

open Classical in
theorem etaDom_rmark (r : Reg S) :
    etaDom S r TapeSym.rmark
      = (if S.DA.accept r.dq then some ((Tag.vInit, r), stayAll S, noOps, [])
        else some ((Tag.reject, r), stayAll S, noOps, [])) := rfl

theorem repVal_vmin (n : ℕ) :
    repVal S (false, ⟨Wtot S - 1, by have := Wtot_pos S; omega⟩) (n + 1)
      = vmin S n := by
  rw [repVal_mk, sgn_false]
  unfold vmin
  have h1 : ((Wtot S - 1 : ℕ) : ℤ) = (Wtot S : ℤ) - 1 := by
    have := Wtot_pos S
    omega
  show -((Wtot S : ℤ) * ((n + 1 : ℕ) : ℤ) + ((Wtot S - 1 : ℕ) : ℤ)) = _
  rw [h1]
  push_cast
  ring

theorem outw_eq_flatMap (w : List Step) :
    outw S w = (valueList S w.length).flatMap (fun v => (fiber S w v).map (labOf S w)) := by
  unfold outw sortedPairs labOf
  rw [List.map_flatMap]

theorem numVals_pos (n : ℕ) : 0 < numVals S n := by
  have h := Nat.mul_pos (Nat.mul_pos (show 0 < 2 by omega) (Wtot_pos S))
    (show 0 < n + 2 by omega)
  unfold numVals
  have h3 := Wtot_ge3 S
  have : 2 * Wtot S * (n + 2) ≥ 2 * 3 * 2 := by
    apply Nat.mul_le_mul
    · apply Nat.mul_le_mul_left
      exact h3
    · omega
  omega

/-- **The accepting run**: on the domain, the machine runs from the initial
configuration, emits the sorted output, and halts accepting. -/
theorem accept_run (w : List Step) (hdom : S.P.toPoly.domain w) :
    ∃ rd posd len,
      (mach S).StepsN w (mach S).initConfig (outw S w) (cfg S Tag.done rd posd) len ∧
      len ≤ (3 * w.length + 7)
        + ((sortedPairs S w).length + numVals S w.length) * (8 * w.length + 13) := by
  -- step 1: off the left marker
  set mv1 : Fin (numH S) → HeadMove :=
    mkF S .right .stay .stay .stay (fun _ => .stay) with hmv1
  set pos0 : Fin (numH S) → ℕ := fun _ => 0 with hpos0
  have hstep1 : (mach S).StepsN w (cfg S Tag.domScan (initReg S) pos0) []
      (cfg S Tag.domScan (initReg S) (fun i => (mv1 i).apply (pos0 i))) 1 := by
    refine step_one S ?_ ?_ _ rfl
    · rw [etaCore_domScan]
      show etaDom S (initReg S) (tapeSym w (pos0 (scanI S))) = _
      rw [show pos0 (scanI S) = 0 from rfl, tapeSym_zero]
      rfl
    · rw [hmv1]
      refine guard_mkF S _ _ _ _ _ (fun hrm => ?_) (fun _ => stay_ne_right)
        (fun _ => stay_ne_right) (fun _ => stay_ne_right) (fun _ _ => stay_ne_right)
      rw [show pos0 (scanI S) = 0 from rfl, tapeSym_zero] at hrm
      simp at hrm
  -- step 2: the letter sweep
  obtain ⟨r2, pos2, hrun2, h2dq, h2pq, h2sq, h2vr, h2cr, h2lc, h2bc, h2bl, h2pl,
    h2sc, h2L, h2B, h2V, h2vals⟩ :=
    dom_letters S w w.length 0 (by omega) (initReg S) (fun i => (mv1 i).apply (pos0 i))
      rfl (by show (mv1 (scanI S)).apply _ = _; rw [hmv1, mkF_scan]; rfl)
  -- step 3: accept into `vInit`
  have haccept : S.DA.accept r2.dq := by
    rw [h2dq]
    exact (da_accepts_iff_stateBefore S w).mp ((S.hDA w).mpr hdom)
  have hstep3 : (mach S).StepsN w (cfg S Tag.domScan r2 pos2) []
      (cfg S Tag.vInit r2 pos2) 1 := by
    refine step_one S ?_ (guard_stayAll S _) pos2 (by funext i; rfl)
    rw [etaCore_domScan]
    show etaDom S r2 (tapeSym w (pos2 (scanI S))) = _
    rw [h2sc, tapeSym_ge w _ (by omega), etaDom_rmark, if_pos haccept]
  -- step 4: the level-head sweep
  have h2V0 : pos2 (VI S) = w.length + 1 - (w.length + 1) := by
    rw [h2V]
    show (mv1 (VI S)).apply _ = _
    rw [hmv1, mkF_V]
    show pos0 (VI S) = _
    rw [show pos0 (VI S) = 0 from rfl]
    omega
  obtain ⟨pos4, hrun4, h4sc, h4L, h4B, h4V, h4vals⟩ :=
    vinit_run S w r2 (w.length + 1) pos2 h2V0 (le_refl _)
  -- step 5: rewind
  obtain ⟨pos5, len5, hrun5, hlen5, h5sc, h5B, h5vals, h5V, h5L, -⟩ :=
    rewind_run S w true Tag.rewindAll
      { r2 with vr := (false, ⟨Wtot S - 1, by have := Wtot_pos S; omega⟩) }
      (Or.inl ⟨rfl, rfl⟩) (w.length + 1) pos4
      (by rw [h4sc, h2sc])
      (by rw [h4B, h2B]
          show (mv1 (BI S)).apply _ ≤ _
          rw [hmv1, mkF_B]
          show pos0 (BI S) ≤ _
          rw [show pos0 (BI S) = 0 from rfl]
          omega)
      (by intro c
          rw [h4vals c, h2vals c]
          show (mv1 (valI S c)).apply _ ≤ _
          rw [hmv1, mkF_val]
          show pos0 (valI S c) ≤ _
          rw [show pos0 (valI S c) = 0 from rfl]
          omega)
      (by intro _
          rw [h4L, h2L]
          show (mv1 (LI S)).apply _ ≤ _
          rw [hmv1, mkF_L]
          show pos0 (LI S) ≤ _
          rw [show pos0 (LI S) = 0 from rfl]
          omega)
  -- step 6: restart the scan
  obtain ⟨pos6, hrun6, h6sc, h6L, h6B, h6V, h6vals⟩ :=
    scanStart_step S w _ pos5 h5sc
  -- the invariant at level `vmin`
  have hInv : ScanInv S w (vmin S w.length) none (S.DA.stateBefore w w.length) 0
      (resetReg S { r2 with vr := (false, ⟨Wtot S - 1, by have := Wtot_pos S; omega⟩) })
      pos6 := by
    refine scanInv_establish S w (vmin S w.length) none (S.DA.stateBefore w w.length)
      _ pos6 ?_ rfl (fun c => rfl) (fun c => rfl) rfl rfl rfl ?_ ?_ ?_ h6sc
      (by rw [h6B, h5B]) (fun c => by rw [h6vals c, h5vals c]) ?_
    · exact h2dq
    · show repVal S (false, ⟨Wtot S - 1, _⟩) (pos6 (VI S)) = vmin S w.length
      rw [h6V, h5V, h4V]
      exact repVal_vmin S w.length
    · show RepCanon S (false, ⟨Wtot S - 1, _⟩) (pos6 (VI S))
      intro _
      right
      show Wtot S - 1 ≠ 0
      have := Wtot_ge3 S
      omega
    · rw [h6V, h5V, h4V]
    · show (resetReg S _).lc = none ∧ pos6 (LI S) = 0
      constructor
      · show r2.lc = none
        rw [h2lc]
        rfl
      · rw [h6L, h5L rfl]
  -- step 7: the value loop
  have hcast0 : vmin S w.length + ((0 : ℕ) : ℤ) = vmin S w.length := by
    simp
  rw [← hcast0] at hInv
  obtain ⟨rd, posd, lenL, hrunL, hlenL⟩ :=
    value_loop S w (S.DA.stateBefore w w.length) (numVals S w.length - 1) 0
      (numVals_pos S w.length) (by omega) _ pos6 hInv
  -- assemble
  refine ⟨rd, posd, 1 + w.length + 1 + (w.length + 1 + 1) + len5 + (1 + lenL), ?_, ?_⟩
  · have h := MHC.StepsN.trans (MHC.StepsN.trans (MHC.StepsN.trans (MHC.StepsN.trans
      (MHC.StepsN.trans hstep1 hrun2) hstep3) hrun4) hrun5)
      (MHC.StepsN.trans hrun6 hrunL)
    rw [outw_eq_flatMap]
    show (mach S).StepsN w (cfg S Tag.domScan (initReg S) pos0) _ _ _
    simpa using h
  · have hsp : ((valueList S w.length).drop 0).flatMap (fun v => fiber S w v)
        = sortedPairs S w := by
      rw [List.drop_zero]
      rfl
    rw [hsp] at hlenL
    have hnv0 : numVals S w.length - 0 = numVals S w.length := by omega
    rw [hnv0] at hlenL
    omega

/-- **The rejecting run**: off the domain, the machine halts non-accepting
after the domain sweep. -/
theorem reject_run (w : List Step) (hndom : ¬ S.P.toPoly.domain w) :
    ∃ e len,
      (mach S).StepsN w (mach S).initConfig [] e len ∧ (mach S).Halted w e ∧
      ¬ (mach S).F e.1 ∧ len ≤ w.length + 2 := by
  set mv1 : Fin (numH S) → HeadMove :=
    mkF S .right .stay .stay .stay (fun _ => .stay) with hmv1
  set pos0 : Fin (numH S) → ℕ := fun _ => 0 with hpos0
  have hstep1 : (mach S).StepsN w (cfg S Tag.domScan (initReg S) pos0) []
      (cfg S Tag.domScan (initReg S) (fun i => (mv1 i).apply (pos0 i))) 1 := by
    refine step_one S ?_ ?_ _ rfl
    · rw [etaCore_domScan]
      show etaDom S (initReg S) (tapeSym w (pos0 (scanI S))) = _
      rw [show pos0 (scanI S) = 0 from rfl, tapeSym_zero]
      rfl
    · rw [hmv1]
      refine guard_mkF S _ _ _ _ _ (fun hrm => ?_) (fun _ => stay_ne_right)
        (fun _ => stay_ne_right) (fun _ => stay_ne_right) (fun _ _ => stay_ne_right)
      rw [show pos0 (scanI S) = 0 from rfl, tapeSym_zero] at hrm
      simp at hrm
  obtain ⟨r2, pos2, hrun2, h2dq, h2pq, h2sq, h2vr, h2cr, h2lc, h2bc, h2bl, h2pl,
    h2sc, h2L, h2B, h2V, h2vals⟩ :=
    dom_letters S w w.length 0 (by omega) (initReg S) (fun i => (mv1 i).apply (pos0 i))
      rfl (by show (mv1 (scanI S)).apply _ = _; rw [hmv1, mkF_scan]; rfl)
  have hreject : ¬ S.DA.accept r2.dq := by
    rw [h2dq]
    intro hacc
    exact hndom ((S.hDA w).mp ((da_accepts_iff_stateBefore S w).mpr hacc))
  have hstep3 : (mach S).StepsN w (cfg S Tag.domScan r2 pos2) []
      (cfg S Tag.reject r2 pos2) 1 := by
    refine step_one S ?_ (guard_stayAll S _) pos2 (by funext i; rfl)
    rw [etaCore_domScan]
    show etaDom S r2 (tapeSym w (pos2 (scanI S))) = _
    rw [h2sc, tapeSym_ge w _ (by omega), etaDom_rmark, if_neg hreject]
  refine ⟨cfg S Tag.reject r2 pos2, 1 + w.length + 1, ?_, halted_reject S w r2 pos2,
    ?_, by omega⟩
  · have h := MHC.StepsN.trans (MHC.StepsN.trans hstep1 hrun2) hstep3
    show (mach S).StepsN w (cfg S Tag.domScan (initReg S) pos0) [] _ _
    simpa using h
  · show ¬ (Tag.reject = Tag.done)
    intro h
    exact Tag.noConfusion h

end SRRQuadratic

-- and the corollary

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- On the domain the machine computes the sorted output. -/
theorem mach_computes (w : List Step) (hdom : S.P.toPoly.domain w) :
    (mach S).Computes w (outw S w) := by
  obtain ⟨rd, posd, len, hrun, -⟩ := accept_run S w hdom
  exact ⟨cfg S Tag.done rd posd, ⟨len, hrun⟩, halted_done S w rd posd, rfl⟩

/-- Off the domain the machine computes nothing. -/
theorem mach_not_computes (w : List Step) (hndom : ¬ S.P.toPoly.domain w)
    (out : List Gamma) : ¬ (mach S).Computes w out := by
  rintro ⟨e, ⟨N, hs⟩, hh, hF⟩
  obtain ⟨er, lenr, hrunr, hhr, hFr, -⟩ := reject_run S w hndom
  obtain ⟨-, he, -⟩ := MHC.stepsN_unique hs hh hrunr hhr
  rw [he] at hF
  exact hFr hF

/-- **The `Computes` characterisation.** -/
theorem mach_computes_iff (T : List Step → Option (List Gamma))
    (hreal : ∀ w out, T w = some out ↔ (S.P.toPoly.domain w ∧ S.P.IsOutput w out))
    (w : List Step) (out : List Gamma) :
    T w = some out ↔ (mach S).Computes w out := by
  constructor
  · intro hT
    obtain ⟨hdom, hout⟩ := (hreal w out).mp hT
    have : out = outw S w := isOutput_unique S.P S.hV hout (isOutput_outw S w)
    rw [this]
    exact mach_computes S w hdom
  · intro hcomp
    by_cases hdom : S.P.toPoly.domain w
    · have : out = outw S w :=
        MHC.computes_unique hcomp (mach_computes S w hdom)
      rw [this]
      exact (hreal w _).mpr ⟨hdom, isOutput_outw S w⟩
    · exact absurd hcomp (mach_not_computes S w hdom out)

/-- The sorted output has at most `K·n` pairs. -/
theorem sortedPairs_length_le (w : List Step) :
    (sortedPairs S w).length ≤ S.K * w.length := by
  classical
  set allPairs : List (Fin S.K × ℕ) :=
    (List.finRange S.K).flatMap (fun c => (List.range w.length).map (fun p => (c, p)))
    with hall
  have hsub : sortedPairs S w ⊆ allPairs := by
    intro x hx
    have hsel := (mem_sortedPairs S w x).mp hx
    have hp : x.2 < w.length := ((selP_iff S w x.1 x.2).mp hsel).1
    rw [hall]
    rw [List.mem_flatMap]
    refine ⟨x.1, List.mem_finRange x.1, ?_⟩
    rw [List.mem_map]
    exact ⟨x.2, List.mem_range.mpr hp, rfl⟩
  have hlen : allPairs.length = S.K * w.length := by
    rw [hall, List.length_flatMap]
    have hmap : (List.finRange S.K).map
        (fun c => ((List.range w.length).map (fun p => (c, p))).length)
        = List.replicate S.K w.length := by
      rw [show (fun c : Fin S.K => ((List.range w.length).map
          (fun p => (c, p))).length) = (fun _ => w.length) from ?_]
      · rw [List.map_const', List.length_finRange]
      · funext c
        rw [List.length_map, List.length_range]
    rw [hmap, List.sum_replicate, smul_eq_mul]
  rw [← hlen]
  exact (List.subperm_of_subset (sortedPairs_nodup S w) hsub).length_le

end SRRQuadratic

namespace SRRQuadratic

open Multihead TwoDFT

variable {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma] (S : Setup Gamma)

/-- The explicit quadratic constant. -/
def Dconst : ℕ := 13 * (S.K + 4 * Wtot S) + 7

/-- **The quadratic halting-time bound**: every halting run from the initial
configuration has length at most `Dconst · (n+1)²`. -/
theorem halting_len_le (w : List Step) (out : List Gamma) (e : (mach S).Config)
    (N : ℕ) (hs : (mach S).StepsN w (mach S).initConfig out e N)
    (hh : (mach S).Halted w e) :
    N ≤ Dconst S * (w.length + 1) ^ 2 := by
  have hDge : 7 ≤ Dconst S := by
    unfold Dconst
    omega
  have hsq : (w.length + 1) ≤ (w.length + 1) ^ 2 := by nlinarith
  by_cases hdom : S.P.toPoly.domain w
  · obtain ⟨rd, posd, lenA, hrunA, hlenA⟩ := accept_run S w hdom
    obtain ⟨-, -, hN⟩ := MHC.stepsN_unique hs hh hrunA (halted_done S w rd posd)
    have h1 : (sortedPairs S w).length + numVals S w.length
        ≤ (S.K + 4 * Wtot S) * (w.length + 1) := by
      have hsp := sortedPairs_length_le S w
      have hsp2 : S.K * w.length ≤ S.K * (w.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hnv : numVals S w.length ≤ 4 * Wtot S * (w.length + 1) := by
        have hmul : 2 * Wtot S * (w.length + 2) ≤ 2 * Wtot S * (2 * (w.length + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
        have heq : 2 * Wtot S * (2 * (w.length + 1)) = 4 * Wtot S * (w.length + 1) := by
          ring
        unfold numVals
        omega
      have heq2 : (S.K + 4 * Wtot S) * (w.length + 1)
          = S.K * (w.length + 1) + 4 * Wtot S * (w.length + 1) := by ring
      omega
    have h2 : 8 * w.length + 13 ≤ 13 * (w.length + 1) := by omega
    have h3 : 3 * w.length + 7 ≤ 7 * (w.length + 1) := by omega
    calc N = lenA := hN
      _ ≤ (3 * w.length + 7)
          + ((sortedPairs S w).length + numVals S w.length) * (8 * w.length + 13) := hlenA
      _ ≤ 7 * (w.length + 1)
          + ((S.K + 4 * Wtot S) * (w.length + 1)) * (13 * (w.length + 1)) :=
        Nat.add_le_add h3 (Nat.mul_le_mul h1 h2)
      _ = 7 * (w.length + 1) + 13 * (S.K + 4 * Wtot S) * (w.length + 1) ^ 2 := by ring
      _ ≤ Dconst S * (w.length + 1) ^ 2 := by
          unfold Dconst
          have hfin : 7 * (w.length + 1) ≤ 7 * (w.length + 1) ^ 2 :=
            Nat.mul_le_mul_left _ hsq
          have heq3 : (13 * (S.K + 4 * Wtot S) + 7) * (w.length + 1) ^ 2
              = 13 * (S.K + 4 * Wtot S) * (w.length + 1) ^ 2
                + 7 * (w.length + 1) ^ 2 := by ring
          omega
  · obtain ⟨er, lenr, hrunr, hhr, -, hlenr⟩ := reject_run S w hdom
    obtain ⟨-, -, hN⟩ := MHC.stepsN_unique hs hh hrunr hhr
    have : w.length + 2 ≤ 7 * (w.length + 1) ^ 2 := by nlinarith
    have hD2 : 7 * (w.length + 1) ^ 2 ≤ Dconst S * (w.length + 1) ^ 2 :=
      Nat.mul_le_mul_right _ hDge
    omega

/-- The space bound holds vacuously: the machine has no counters. -/
theorem mach_spaceBound : SpaceBound (mach S (Gamma := Gamma)) 1 :=
  fun _ _ _ _ _ j => j.elim0

end SRRQuadratic

open SRRQuadratic in
/-- **Corollary `cor:srr-quadratic`** (paper.tex; proof in
Appendix A.2).  Σ is instantiated to `Step`,
as everywhere in this development.

Every SWR (= `WRP.IsSRR1`) map whose selection and labelling are decided by a
single left-to-right finite-state pass (`PrefixPassData`) is computable by a
deterministic multihead machine within logarithmic space and quadratic time:
the machine `SRRQuadratic.mach` satisfies the logspace `SpaceBound` (it has
no counters — every `O(log n)`-bit register is a two-way head), computes
exactly `T`, and every halting run from the initial configuration takes at
most `D·(n+1)²` steps, with the explicit constant `D = 13·(K + 4·(2W+1)) + 7`.

The paper's `O(1)` unit-cost word comparisons are realised in this
unary-counter-free model by maintaining **signed differences** between the
running per-copy rank sums and the currently examined rank level, in signed
base-`2W+1` form (sign and residue in the finite control, magnitude quotient
in a dedicated head): a rank comparison is a single head coincidence plus a
state comparison, and each per-letter update moves each head at most one
cell.  The machine enumerates the `O(n)` rank levels in increasing order and
extracts each level's fiber in scan order by successive best-so-far scans;
every scan costs `O(n)` steps (the `B`-walks telescope against the monotone
advance of the best-so-far position within a scan, and the level-change
rebase costs telescope against the monotone ascent of the examined level), and
the number of scans is `O(n)` — one per rank level plus one per output
letter — keeping every round at `O(n)` machine steps and the total quadratic,
faithful to the paper's bound. -/
theorem srr_quadratic {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma]
    (T : List Step → Option (List Gamma))
    (P : WRP.Presentation Step Gamma) (hV : P.Valid) (hd1 : P.d = 1)
    (hscan : P.toPoly.IsScanOrder)
    (hreal : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (pp : PrefixPassData P) :
    ∃ (h c C D : ℕ) (M : Multihead.MHC Step Gamma h c),
      Multihead.SpaceBound M C ∧
      (∀ w out, T w = some out ↔ M.Computes w out) ∧
      ∀ w out e N, M.StepsN w M.initConfig out e N → M.Halted w e →
        N ≤ D * (w.length + 1) ^ 2 := by
  obtain ⟨h1, dir, cord, hirr, htrans, htotal, hord⟩ := hscan
  obtain ⟨φ, hφ⟩ := P.toPoly.domainDef
  obtain ⟨DA, hDAφ⟩ := SliceMSO.buchi φ
  set S' : Setup Gamma :=
    { P := P
      hV := hV
      hd1 := hd1
      h1 := h1
      dir := dir
      cord := cord
      cordIrr := hirr
      cordTrans := htrans
      cordTotal := htotal
      hord := hord
      pp := pp
      DA := DA
      hDA := fun w => (hDAφ w).trans (hφ w).symm
      kap := fun c =>
        Classical.choose (isPrefixAdditiveRank_of_isRegularRankTerm (P.rankReg c))
      hkap := fun c =>
        Classical.choose_spec (isPrefixAdditiveRank_of_isRegularRankTerm (P.rankReg c)) }
    with hS'
  exact ⟨numH S', 0, 1, Dconst S', mach S', mach_spaceBound S',
    mach_computes_iff S' T hreal, fun w out e N hs hh => halting_len_le S' w out e N hs hh⟩

open SRRQuadratic in
/-- The packaging corollary: such a `T` is a logspace map of the multihead
model (`Multihead.IsLogspaceMH`). -/
theorem srr_quadratic_isLogspaceMH {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma]
    (T : List Step → Option (List Gamma))
    (P : WRP.Presentation Step Gamma) (hV : P.Valid) (hd1 : P.d = 1)
    (hscan : P.toPoly.IsScanOrder)
    (hreal : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (pp : PrefixPassData P) :
    Multihead.IsLogspaceMH T := by
  obtain ⟨h, c, C, D, M, hSB, hC, -⟩ :=
    srr_quadratic T P hV hd1 hscan hreal pp
  exact ⟨h, c, C, M, hSB, hC⟩

-- Trust check: exactly `[propext, Classical.choice, Quot.sound, SliceMSO.buchi]`.
#print axioms srr_quadratic
