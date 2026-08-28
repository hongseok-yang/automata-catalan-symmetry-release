/-
# WRP ⊆ deterministic logspace (`thm:wrp-logspace`) and the strict separation

This file proves the containment half of `thm:wrp-strict-below-logspace`
(paper.tex): every WRP map is computable by a
deterministic multihead bounded-counter transducer with linearly bounded
counters (`Multihead.IsLogspaceMH`), and combines it with the separation
witness `Multihead.exists_logspaceMH_not_wrp` into the **unconditional**
`wrp_strict_below_logspace`.

The evaluator machine follows the ≺-successor round structure of the paper's
proofs (since the 2026-08-28 revision the Theorem proof uses it too, with the
improved generic bound `O(n^{2k+1})`; one output letter per round): it keeps
the last emitted atom
CUR in a block of heads, sweeps all candidate atoms with a best-so-far block
BEST, compares atoms with the two counters (positive/negative parts of the
rank difference, drained at each lexicographic dimension), breaks rank ties
with the marked tie-order DFA, and emits the label of the round's minimum.

Main results: `wrp_isLogspaceMH`, `wrp_logspace_polytime`,
`wrp_strict_below_logspace`.
-/
import RequestProject.Multihead
import RequestProject.MSOMarkN
import RequestProject.PrefixAdditiveRank
import RequestProject.WRPNonemptyRegular

namespace WRPLogspace

open TwoDFT MSOMarkN
open Logspace (CounterOp)
open Multihead (HeadMove)

/-! ## §1 Pure order theory: first-difference scans of `lexLt`/`wrpOrd` -/

section OrderScan

variable {d : ℕ}

theorem lexLt_of_firstDiff {x y : Fin d → ℤ} (i : Fin d)
    (hpre : ∀ j, j < i → x j = y j) (hlt : x i < y i) : WRP.lexLt x y :=
  ⟨i, hpre, hlt⟩

theorem not_lexLt_of_firstDiff_gt {x y : Fin d → ℤ} (i : Fin d)
    (hpre : ∀ j, j < i → x j = y j) (hgt : y i < x i) : ¬ WRP.lexLt x y := by
  rintro ⟨i', hpre', hlt'⟩
  rcases lt_trichotomy i' i with h | h | h
  · have := hpre i' h; omega
  · subst h; omega
  · have := hpre' i h; omega

theorem not_lexLt_self (x : Fin d → ℤ) : ¬ WRP.lexLt x x := by
  rintro ⟨i, -, hlt⟩; omega

variable {Gamma : Type} (P : WRP.Presentation Step Gamma)

theorem wrpOrd_of_dimLt {w : List Step} {a b : P.toPoly.Atom} (i : Fin P.d)
    (hpre : ∀ j, j < i → P.rankOf w a j = P.rankOf w b j)
    (hlt : P.rankOf w a i < P.rankOf w b i) : P.wrpOrd w a b :=
  Or.inl (lexLt_of_firstDiff i hpre hlt)

theorem not_wrpOrd_of_dimGt {w : List Step} {a b : P.toPoly.Atom} (i : Fin P.d)
    (hpre : ∀ j, j < i → P.rankOf w a j = P.rankOf w b j)
    (hgt : P.rankOf w b i < P.rankOf w a i) : ¬ P.wrpOrd w a b := by
  rintro (h | ⟨heq, -⟩)
  · exact not_lexLt_of_firstDiff_gt i hpre hgt h
  · rw [heq] at hgt; omega

theorem wrpOrd_iff_atomOrd_of_rankEq {w : List Step} {a b : P.toPoly.Atom}
    (heq : P.rankOf w a = P.rankOf w b) :
    P.wrpOrd w a b ↔ P.toPoly.atomOrd w a b := by
  constructor
  · rintro (h | ⟨-, h⟩)
    · rw [heq] at h; exact absurd h (not_lexLt_self _)
    · exact h
  · intro h; exact Or.inr ⟨heq, h⟩

end OrderScan

/-! ## §2 Pure counter-payment theory

The two counters accumulate the positive and negative parts of the signed
rank difference `rank_L − rank_R` of the current dimension.  A signed value
`v` contributed by side `side` (`true` = the left atom) pays `|v|` into the
counter `tgtOf side v` (`true` = the positive counter). -/

section PayTheory

/-- Which counter (`true` = Pos, `false` = Neg) receives the payment `|v|`
contributed with sign `side` (`true`: `+v`, `false`: `-v`). -/
def tgtOf (side : Bool) (v : ℤ) : Bool := if 0 ≤ v then side else !side

/-- Payment into the positive counter. -/
def payP (side : Bool) (v : ℤ) : ℕ := if tgtOf side v then v.natAbs else 0

/-- Payment into the negative counter. -/
def payN (side : Bool) (v : ℤ) : ℕ := if tgtOf side v then 0 else v.natAbs

theorem payP_sub_payN (side : Bool) (v : ℤ) :
    (payP side v : ℤ) - payN side v = if side then v else -v := by
  have habs : ((v.natAbs : ℤ) = v ∧ 0 ≤ v) ∨ ((v.natAbs : ℤ) = -v ∧ v < 0) := by
    rcases le_or_gt 0 v with hv | hv
    · exact Or.inl ⟨Int.natAbs_of_nonneg hv, hv⟩
    · exact Or.inr ⟨by omega, hv⟩
  rcases habs with ⟨he, hv⟩ | ⟨he, hv⟩
  · cases side <;> simp [payP, payN, tgtOf, hv, he]
  · cases side <;> simp [payP, payN, tgtOf, not_le.mpr hv, he]

theorem payP_le (side : Bool) (v : ℤ) : payP side v ≤ v.natAbs := by
  unfold payP; split <;> omega

theorem payN_le (side : Bool) (v : ℤ) : payN side v ≤ v.natAbs := by
  unfold payN; split <;> omega

/-- Exactly one of the two payments is nonzero, and it is `|v|`. -/
theorem payP_add_payN (side : Bool) (v : ℤ) :
    payP side v + payN side v = v.natAbs := by
  unfold payP payN; split <;> omega

end PayTheory

/-! ## §3 Machine-order tuple enumeration

The candidate gadget enumerates the tuples of one copy by incrementing the
last coordinate first, with carries; `succAux`/`tupSucc` is the pure
successor mirroring the head gadget, `tupOrbit` the fuelled orbit from the
all-zero tuple.  `orbit_complete` shows the orbit with fuel
`Fintype.card (Fin k → Fin n)` visits every in-range tuple (the orbit is a
strictly `tupLt`-increasing chain, so it cannot cycle, and every nonzero
in-range tuple has an explicit predecessor). -/

namespace TupEnum

variable (n k : ℕ)

/-- Machine-order tuple successor, coordinate `k-1` fastest: `succAux n k t r`
is the successor considering only coordinates `< r`, with all coordinates
`≥ r` reset to `0` in the result. -/
def succAux (t : Fin k → ℕ) : ℕ → Option (Fin k → ℕ)
  | 0 => none
  | (r + 1) =>
      if h : r < k then
        (if t ⟨r, h⟩ + 1 < n then
          some (fun x => if x.val < r then t x else if x.val = r then t ⟨r, h⟩ + 1 else 0)
         else succAux t r)
      else succAux t r

/-- The tuple successor. -/
def tupSucc (t : Fin k → ℕ) : Option (Fin k → ℕ) := succAux n k t k

/-- The orbit of the successor function, with explicit fuel. -/
def tupOrbit : ℕ → (Fin k → ℕ) → List (Fin k → ℕ)
  | 0, t => [t]
  | (f + 1), t => t :: (match tupSucc n k t with
      | none => []
      | some t' => tupOrbit f t')

/-- Strict lexicographic order (most-significant coordinate first). -/
def tupLt (s t : Fin k → ℕ) : Prop :=
  ∃ j : Fin k, (∀ x, x < j → s x = t x) ∧ s j < t j

theorem tupLt_irrefl (t : Fin k → ℕ) : ¬ tupLt k t t := by
  rintro ⟨j, -, hj⟩; omega

theorem tupLt_trans {s t u : Fin k → ℕ} (h1 : tupLt k s t) (h2 : tupLt k t u) :
    tupLt k s u := by
  obtain ⟨j1, hp1, hl1⟩ := h1
  obtain ⟨j2, hp2, hl2⟩ := h2
  rcases lt_trichotomy j1 j2 with h | h | h
  · exact ⟨j1, fun x hx => (hp1 x hx).trans (hp2 x (hx.trans h)),
      by have := hp2 j1 h; omega⟩
  · subst h; exact ⟨j1, fun x hx => (hp1 x hx).trans (hp2 x hx), by omega⟩
  · exact ⟨j2, fun x hx => (hp1 x (hx.trans h)).trans (hp2 x hx),
      by rw [hp1 j2 h]; omega⟩

theorem succAux_valid {t : Fin k → ℕ} (ht : ∀ x, t x < n) :
    ∀ {r : ℕ} {t' : Fin k → ℕ}, succAux n k t r = some t' → ∀ x, t' x < n := by
  intro r
  induction r with
  | zero => intro t' h; simp [succAux] at h
  | succ r ih =>
      intro t' h x
      rw [succAux] at h
      split at h
      · split at h
        · rename_i hr hlt
          rw [Option.some.injEq] at h
          subst h
          dsimp only
          split
          · exact ht x
          · split
            · omega
            · omega
        · exact ih h x
      · exact ih h x

theorem succAux_tupLt {t : Fin k → ℕ} :
    ∀ {r : ℕ} {t' : Fin k → ℕ}, r ≤ k → succAux n k t r = some t' → tupLt k t t' := by
  intro r
  induction r with
  | zero => intro t' _ h; simp [succAux] at h
  | succ r ih =>
      intro t' hr h
      rw [succAux] at h
      split at h
      · split at h
        · rename_i hrk hlt
          rw [Option.some.injEq] at h
          subst h
          refine ⟨⟨r, hrk⟩, fun x hx => ?_, ?_⟩
          · have : x.val < r := hx
            simp [this]
          · simp
        · exact ih (by omega) h
      · exact ih (by omega) h

/-- The orbit chain ends (reaches a `none`-successor) within fuel `f`. -/
def OrbitEnds : ℕ → (Fin k → ℕ) → Prop
  | 0, t => tupSucc n k t = none
  | (f + 1), t => match tupSucc n k t with
      | none => True
      | some t' => OrbitEnds f t'

theorem mem_tupOrbit_self (f : ℕ) (t : Fin k → ℕ) : t ∈ tupOrbit n k f t := by
  cases f <;> simp [tupOrbit]

theorem orbit_closed {f : ℕ} {t s s' : Fin k → ℕ} (hEnd : OrbitEnds n k f t)
    (hs : s ∈ tupOrbit n k f t) (hsucc : tupSucc n k s = some s') :
    s' ∈ tupOrbit n k f t := by
  induction f generalizing t with
  | zero =>
      simp only [tupOrbit, List.mem_singleton] at hs
      subst hs
      rw [OrbitEnds] at hEnd
      rw [hEnd] at hsucc
      exact absurd hsucc (by simp)
  | succ f ih =>
      rw [OrbitEnds] at hEnd
      cases hcase : tupSucc n k t with
      | none =>
          simp only [tupOrbit, hcase, List.mem_cons, List.not_mem_nil, or_false] at hs
          subst hs
          rw [hcase] at hsucc
          exact absurd hsucc (by simp)
      | some t2 =>
          rw [hcase] at hEnd
          simp only [tupOrbit, hcase, List.mem_cons] at hs ⊢
          rcases hs with rfl | hs'
          · rw [hcase] at hsucc
            injection hsucc with hss
            subst hss
            exact Or.inr (mem_tupOrbit_self n k f t2)
          · exact Or.inr (ih hEnd hs')

theorem orbit_sound {f : ℕ} {t s : Fin k → ℕ} (ht : ∀ x, t x < n)
    (hs : s ∈ tupOrbit n k f t) : ∀ x, s x < n := by
  induction f generalizing t with
  | zero =>
      simp only [tupOrbit, List.mem_singleton] at hs; subst hs; exact ht
  | succ f ih =>
      cases hcase : tupSucc n k t with
      | none =>
          simp only [tupOrbit, hcase, List.mem_cons, List.not_mem_nil, or_false] at hs
          subst hs; exact ht
      | some t2 =>
          simp only [tupOrbit, hcase, List.mem_cons] at hs
          rcases hs with rfl | hs'
          · exact ht
          · exact ih (succAux_valid n k ht hcase) hs'

instance : Trans (tupLt k) (tupLt k) (tupLt k) := ⟨tupLt_trans k⟩

theorem head?_tupOrbit (f : ℕ) (t : Fin k → ℕ) : (tupOrbit n k f t).head? = some t := by
  cases f <;> rfl

theorem orbit_isChain (f : ℕ) (t : Fin k → ℕ) :
    List.IsChain (tupLt k) (tupOrbit n k f t) := by
  induction f generalizing t with
  | zero => exact List.isChain_singleton t
  | succ f ih =>
      cases hcase : tupSucc n k t with
      | none => simp only [tupOrbit, hcase]; exact List.isChain_singleton t
      | some t2 =>
          simp only [tupOrbit, hcase]
          rw [List.isChain_cons]
          refine ⟨?_, ih t2⟩
          intro y hy
          rw [head?_tupOrbit] at hy
          rw [Option.mem_def, Option.some.injEq] at hy
          subst hy
          exact succAux_tupLt n k le_rfl hcase

theorem orbit_nodup (f : ℕ) (t : Fin k → ℕ) : (tupOrbit n k f t).Nodup := by
  have hpw : (tupOrbit n k f t).Pairwise (tupLt k) :=
    (List.isChain_iff_pairwise).mp (orbit_isChain n k f t)
  refine hpw.imp ?_
  intro a b hab heq
  subst heq
  exact tupLt_irrefl k a hab

theorem length_tupOrbit_of_not_ends {f : ℕ} {t : Fin k → ℕ}
    (h : ¬ OrbitEnds n k f t) : (tupOrbit n k f t).length = f + 1 := by
  induction f generalizing t with
  | zero => rfl
  | succ f ih =>
      cases hcase : tupSucc n k t with
      | none => rw [OrbitEnds, hcase] at h; exact absurd trivial h
      | some t2 =>
          rw [OrbitEnds, hcase] at h
          simp only [tupOrbit, hcase, List.length_cons]
          rw [ih h]

theorem orbitEnds_fuel {t : Fin k → ℕ} (ht : ∀ x, t x < n) :
    OrbitEnds n k (Fintype.card (Fin k → Fin n)) t := by
  by_contra hno
  have hlen := length_tupOrbit_of_not_ends n k hno
  set F := Fintype.card (Fin k → Fin n) with hF
  have hnd := orbit_nodup n k F t
  have hsound : ∀ s ∈ tupOrbit n k F t, ∀ x, s x < n :=
    fun s hs => orbit_sound n k ht hs
  set l' : List (Fin k → Fin n) :=
    (tupOrbit n k F t).pmap (fun s hs => fun x => (⟨s x, hs x⟩ : Fin n)) hsound with hl'
  have hnd' : l'.Nodup := by
    refine hnd.pmap ?_
    intro a ha b hb hfab
    funext x
    have := congrFun hfab x
    exact congrArg Fin.val this
  have hle := hnd'.length_le_card
  rw [hl', List.length_pmap, hlen] at hle
  omega

theorem exists_pred {s : Fin k → ℕ} (hval : ∀ x, s x < n) (hne : s ≠ fun _ => 0) :
    ∃ p : Fin k → ℕ, (∀ x, p x < n) ∧ tupLt k p s ∧ tupSucc n k p = some s := by
  obtain ⟨x0, hx0⟩ := Function.ne_iff.mp hne
  have hne' : (Finset.univ.filter (fun x : Fin k => s x ≠ 0)).Nonempty :=
    ⟨x0, by simpa using hx0⟩
  set j := (Finset.univ.filter (fun x : Fin k => s x ≠ 0)).max' hne' with hj
  have hjmem : s j ≠ 0 := by
    have := Finset.max'_mem _ hne'
    rw [← hj] at this
    simpa using this
  have hjmax : ∀ x : Fin k, j < x → s x = 0 := by
    intro x hx
    by_contra hne2
    have hxmem : x ∈ Finset.univ.filter (fun x : Fin k => s x ≠ 0) := by simpa using hne2
    have := Finset.le_max' _ x hxmem
    rw [← hj] at this
    omega
  set p : Fin k → ℕ := fun x => if x < j then s x else if x = j then s j - 1 else n - 1
    with hp
  have hpj : p j = s j - 1 := by rw [hp]; simp
  refine ⟨p, ?_, ⟨j, ?_, ?_⟩, ?_⟩
  · intro x
    rw [hp]
    dsimp only
    by_cases h1 : x < j
    · rw [if_pos h1]; exact hval x
    · rw [if_neg h1]
      by_cases h2 : x = j
      · rw [if_pos h2]; have := hval j; omega
      · rw [if_neg h2]; have := hval j; omega
  · intro x hx
    rw [hp]
    dsimp only
    rw [if_pos hx]
  · rw [hpj]; omega
  · have hstep : ∀ r : ℕ, j.val + 1 ≤ r → r ≤ k →
        succAux n k p r = succAux n k p (j.val + 1) := by
      intro r hr1 hr2
      induction r with
      | zero => omega
      | succ r ih =>
          rcases Nat.eq_or_lt_of_le hr1 with heq | hlt
          · rw [heq]
          · have hrk : r < k := by omega
            have hxj1 : ¬ ((⟨r, hrk⟩ : Fin k) < j) := by
              rw [Fin.lt_def]
              show ¬ (r < j.val)
              omega
            have hxj2 : (⟨r, hrk⟩ : Fin k) ≠ j := by
              intro hc
              have hc' : r = j.val := congrArg Fin.val hc
              omega
            have hpr : p ⟨r, hrk⟩ = n - 1 := by
              rw [hp]
              dsimp only
              rw [if_neg hxj1, if_neg hxj2]
            rw [succAux, dif_pos hrk, hpr, if_neg (by omega)]
            exact ih (by omega) (by omega)
    have hjk : j.val < k := j.isLt
    have hjeq : (⟨j.val, hjk⟩ : Fin k) = j := rfl
    rw [tupSucc, hstep k (by omega) le_rfl, succAux, dif_pos hjk, hjeq, hpj]
    rw [if_pos (by have := hval j; omega)]
    rw [Option.some.injEq]
    funext x
    by_cases h1 : x.val < j.val
    · rw [if_pos h1]
      have h1' : x < j := h1
      rw [hp]
      dsimp only
      rw [if_pos h1']
    · rw [if_neg h1]
      by_cases h2 : x.val = j.val
      · rw [if_pos h2]
        have h2' : x = j := Fin.ext h2
        subst h2'
        omega
      · rw [if_neg h2]
        refine (hjmax x ?_).symm
        rw [Fin.lt_def]
        omega

theorem orbit_complete {s : Fin k → ℕ} (hval : ∀ x, s x < n) :
    s ∈ tupOrbit n k (Fintype.card (Fin k → Fin n)) (fun _ => 0) := by
  by_cases hz : ∀ x : Fin k, s x = 0
  · have : s = fun _ => 0 := funext hz
    subst this
    exact mem_tupOrbit_self n k _ _
  -- n is positive, so the all-zero start tuple is valid
  have hn : 0 < n := by
    push Not at hz
    obtain ⟨x, hx⟩ := hz
    have := hval x
    omega
  have h0val : ∀ x : Fin k, (fun _ => 0 : Fin k → ℕ) x < n := fun _ => hn
  have hEnds := orbitEnds_fuel n k h0val
  -- well-founded induction over the finite valid tuples
  let V := {v : Fin k → ℕ // ∀ x, v x < n}
  have : Finite V := by
    refine Finite.of_injective (fun v : V => fun x => (⟨v.1 x, v.2 x⟩ : Fin n)) ?_
    intro a b hab
    apply Subtype.ext
    funext x
    exact congrArg Fin.val (congrFun hab x)
  let rel : V → V → Prop := fun v w => tupLt k v.1 w.1
  have htr : IsTrans V rel := ⟨fun a b c => tupLt_trans k⟩
  have hirr : Std.Irrefl rel := ⟨fun a => tupLt_irrefl k a.1⟩
  have hwf : WellFounded rel := Finite.wellFounded_of_trans_of_irrefl rel
  have hmain : ∀ v : V, v.1 ∈ tupOrbit n k (Fintype.card (Fin k → Fin n)) (fun _ => 0) := by
    intro v
    refine hwf.induction (C := fun v : V =>
      v.1 ∈ tupOrbit n k (Fintype.card (Fin k → Fin n)) (fun _ => 0)) v ?_
    intro w IH
    by_cases hw0 : w.1 = fun _ => 0
    · rw [hw0]
      exact mem_tupOrbit_self n k _ _
    · obtain ⟨p, hpval, hplt, hpsucc⟩ := exists_pred n k w.2 hw0
      have hpmem := IH ⟨p, hpval⟩ hplt
      exact orbit_closed n k hEnds hpmem hpsucc
  exact hmain ⟨s, hval⟩

end TupEnum

/-! ## §4 The best-so-far fold and the round minimum

Each round scans all candidate atoms keeping the ≺-least qualified one seen
so far; `bestFold_minSpec` shows the fold computes the round minimum
(`MinSpec`), `sorted_minSpec_none`/`sorted_minSpec_succ` show the declarative
sorted output list produces the same minima, so the machine's rounds walk
that list. -/

noncomputable section
open Classical

variable {Gamma : Type} (P : WRP.Presentation Step Gamma)

/-- The candidates that qualify in a round: selected, and `≺`-above the
current atom (all atoms qualify in the first round, `cur? = none`). -/
def Qual (w : List Step) (cur? : Option P.toPoly.Atom) (X : P.toPoly.Atom) : Prop :=
  P.toPoly.selectedAtom w X ∧ ∀ a ∈ cur?, P.wrpOrd w a X

/-- One best-so-far update: replace the accumulator by `X` when `X` qualifies
and strictly precedes it (or there is no accumulator yet). -/
def bestStep (w : List Step) (cur? : Option P.toPoly.Atom)
    (b? : Option P.toPoly.Atom) (X : P.toPoly.Atom) : Option P.toPoly.Atom :=
  if Qual P w cur? X ∧ ∀ b ∈ b?, P.wrpOrd w X b then some X else b?

theorem bestStep_qual {w cur? b?} {X : P.toPoly.Atom}
    (hb : ∀ a, b? = some a → Qual P w cur? a) :
    ∀ a, bestStep P w cur? b? X = some a → Qual P w cur? a := by
  intro a h
  rw [bestStep] at h
  split at h
  · rename_i hcond
    rw [Option.some.injEq] at h
    subst h
    exact hcond.1
  · exact hb a h

/-- The fold invariant: the result of folding `bestStep` over `l` starting
from a qualified accumulator is a qualified atom that is `≺`-least among the
accumulator and the qualified members of `l`. -/
theorem bestFold_go (hV : P.Valid) (w : List Step) (cur? : Option P.toPoly.Atom) :
    ∀ (l : List P.toPoly.Atom) (acc : Option P.toPoly.Atom),
      (∀ a, acc = some a → Qual P w cur? a) →
      (∀ a, l.foldl (bestStep P w cur?) acc = some a →
        Qual P w cur? a ∧ (acc = some a ∨ a ∈ l) ∧
        (∀ b, acc = some b → a = b ∨ P.wrpOrd w a b) ∧
        (∀ X ∈ l, Qual P w cur? X → a = X ∨ P.wrpOrd w a X)) ∧
      (l.foldl (bestStep P w cur?) acc = none →
        acc = none ∧ ∀ X ∈ l, ¬ Qual P w cur? X) := by
  intro l
  induction l with
  | nil =>
      intro acc hacc
      simp only [List.foldl_nil]
      refine ⟨fun a h => ⟨hacc a h, Or.inl h, ?_, by simp⟩, fun h => ⟨h, by simp⟩⟩
      intro b hb
      rw [h, Option.some.injEq] at hb
      exact Or.inl hb
  | cons X t ih =>
      intro acc hacc
      have hacc' : ∀ a, bestStep P w cur? acc X = some a → Qual P w cur? a :=
        bestStep_qual P hacc
      obtain ⟨ihsome, ihnone⟩ := ih (bestStep P w cur? acc X) hacc'
      constructor
      · intro a h
        rw [List.foldl_cons] at h
        obtain ⟨hq, hmem, hvsacc', hvst⟩ := ihsome a h
        by_cases hcond : Qual P w cur? X ∧ ∀ b ∈ acc, P.wrpOrd w X b
        · -- the accumulator was replaced by X
          have hstep : bestStep P w cur? acc X = some X := by
            rw [bestStep, if_pos hcond]
          have haX : a = X ∨ P.wrpOrd w a X := hvsacc' X hstep
          refine ⟨hq, ?_, ?_, ?_⟩
          · rcases hmem with hm | hm
            · rw [hstep] at hm
              exact Or.inr (by simp [Option.some.inj hm])
            · exact Or.inr (List.mem_cons_of_mem _ hm)
          · -- vs the old accumulator: a ≼ X ≺ acc
            intro b hb
            have hXb : P.wrpOrd w X b := hcond.2 b (by rw [hb]; rfl)
            rcases haX with rfl | haX'
            · exact Or.inr hXb
            · refine Or.inr (hV.trans w a X b ?_ ?_ ?_ haX' hXb)
              · exact hq.1
              · exact hcond.1.1
              · exact (hacc b hb).1
          · intro Y hY hqY
            rcases List.mem_cons.mp hY with rfl | hYt
            · exact haX
            · exact hvst Y hYt hqY
        · -- the accumulator was kept
          have hstep : bestStep P w cur? acc X = acc := by
            rw [bestStep, if_neg hcond]
          rw [hstep] at hmem hvsacc'
          refine ⟨hq, ?_, hvsacc', ?_⟩
          · rcases hmem with hm | hm
            · exact Or.inl hm
            · exact Or.inr (List.mem_cons_of_mem _ hm)
          · intro Y hY hqY
            rcases List.mem_cons.mp hY with rfl | hYt
            · -- Y = X failed the test: some acc-atom b with ¬ X ≺ b
              push Not at hcond
              obtain ⟨b, hb, hnXb⟩ := hcond hqY
              have hb' : acc = some b := hb
              have haleb : a = b ∨ P.wrpOrd w a b := hvsacc' b hb'
              have hqb := hacc b hb'
              -- trichotomy between Y and b
              rcases hV.trichot w Y b hqY.1 hqb.1 with hYb | hYb | hbY
              · exact absurd hYb hnXb
              · subst hYb
                rcases haleb with rfl | h
                · exact Or.inl rfl
                · exact Or.inr h
              · rcases haleb with rfl | h
                · exact Or.inr hbY
                · exact Or.inr (hV.trans w a b Y hq.1 hqb.1 hqY.1 h hbY)
            · exact hvst Y hYt hqY
      · intro h
        rw [List.foldl_cons] at h
        obtain ⟨hstepnone, ht⟩ := ihnone h
        have haccnone : acc = none ∧ ¬ Qual P w cur? X := by
          by_cases hcond : Qual P w cur? X ∧ ∀ b ∈ acc, P.wrpOrd w X b
          · rw [bestStep, if_pos hcond] at hstepnone
            exact absurd hstepnone (by simp)
          · rw [bestStep, if_neg hcond] at hstepnone
            subst hstepnone
            push Not at hcond
            refine ⟨rfl, fun hq => ?_⟩
            obtain ⟨b, hb, -⟩ := hcond hq
            simp at hb
        refine ⟨haccnone.1, ?_⟩
        intro Y hY
        rcases List.mem_cons.mp hY with rfl | hYt
        · exact haccnone.2
        · exact ht Y hYt

/-- The specification of the round minimum. -/
def MinSpec (w : List Step) (cur? : Option P.toPoly.Atom)
    (res : Option P.toPoly.Atom) : Prop :=
  (res = none ∧ ∀ X, ¬ Qual P w cur? X) ∨
  (∃ a, res = some a ∧ Qual P w cur? a ∧
    ∀ X, Qual P w cur? X → X = a ∨ P.wrpOrd w a X)

theorem minSpec_unique (hV : P.Valid) {w cur?} {r1 r2 : Option P.toPoly.Atom}
    (h1 : MinSpec P w cur? r1) (h2 : MinSpec P w cur? r2) : r1 = r2 := by
  rcases h1 with ⟨hn1, he1⟩ | ⟨a1, hr1, hq1, hm1⟩
  · rcases h2 with ⟨hn2, -⟩ | ⟨a2, hr2, hq2, -⟩
    · rw [hn1, hn2]
    · exact absurd hq2 (he1 a2)
  · rcases h2 with ⟨-, he2⟩ | ⟨a2, hr2, hq2, hm2⟩
    · exact absurd hq1 (he2 a1)
    · rcases hm1 a2 hq2 with rfl | h12
      · rw [hr1, hr2]
      · rcases hm2 a1 hq1 with rfl | h21
        · rw [hr1, hr2]
        · exact absurd (hV.trans w a1 a2 a1 hq1.1 hq2.1 hq1.1 h12 h21)
            (hV.irrefl w a1 hq1.1)

/-- Folding over a complete candidate list computes the round minimum. -/
theorem bestFold_minSpec (hV : P.Valid) (w : List Step)
    (cur? : Option P.toPoly.Atom) (l : List P.toPoly.Atom)
    (hcompl : ∀ X, Qual P w cur? X → X ∈ l) :
    MinSpec P w cur? (l.foldl (bestStep P w cur?) none) := by
  obtain ⟨hsome, hnone⟩ := bestFold_go P hV w cur? l none (by simp)
  cases hres : l.foldl (bestStep P w cur?) none with
  | none =>
      obtain ⟨-, hall⟩ := hnone hres
      exact Or.inl ⟨rfl, fun X hq => hall X (hcompl X hq) hq⟩
  | some a =>
      obtain ⟨hq, -, -, hmin⟩ := hsome a hres
      refine Or.inr ⟨a, rfl, hq, fun X hq' => ?_⟩
      rcases hmin X (hcompl X hq') hq' with h | h
      · exact Or.inl h.symm
      · exact Or.inr h

/-- The sorted output list also computes round minima: with no current atom
the minimum is the head. -/
theorem sorted_minSpec_none (w : List Step)
    {L : List P.toPoly.Atom}
    (hmem : ∀ a, a ∈ L ↔ P.toPoly.selectedAtom w a)
    (hpw : L.Pairwise (P.wrpOrd w)) :
    MinSpec P w none L.head? := by
  cases L with
  | nil =>
      refine Or.inl ⟨rfl, fun X hq => ?_⟩
      exact (List.not_mem_nil (a := X)).elim ((hmem X).mpr hq.1)
  | cons a t =>
      refine Or.inr ⟨a, rfl, ⟨(hmem a).mp List.mem_cons_self, by simp⟩, ?_⟩
      intro X hq
      have hX : X ∈ a :: t := (hmem X).mpr hq.1
      rcases List.mem_cons.mp hX with rfl | hXt
      · exact Or.inl rfl
      · exact Or.inr ((List.pairwise_cons.mp hpw).1 X hXt)

/-- With current atom `L[i]` the round minimum is `L[i+1]?`. -/
theorem sorted_minSpec_succ (hV : P.Valid) (w : List Step)
    {L : List P.toPoly.Atom}
    (hmem : ∀ a, a ∈ L ↔ P.toPoly.selectedAtom w a)
    (hpw : L.Pairwise (P.wrpOrd w))
    (i : ℕ) (hi : i < L.length) :
    MinSpec P w (some L[i]) L[i+1]? := by
  have hpair : ∀ (j1 j2 : ℕ) (h1 : j1 < L.length) (h2 : j2 < L.length),
      j1 < j2 → P.wrpOrd w L[j1] L[j2] :=
    fun j1 j2 h1 h2 hlt => List.pairwise_iff_getElem.mp hpw j1 j2 h1 h2 hlt
  have hsel : ∀ (j : ℕ) (hj : j < L.length), P.toPoly.selectedAtom w L[j] :=
    fun j hj => (hmem _).mp (List.getElem_mem hj)
  -- a qualified atom sits strictly after position i in L
  have hqualPos : ∀ X, Qual P w (some L[i]) X →
      ∃ (j : ℕ) (hj : j < L.length), i < j ∧ X = L[j] := by
    intro X hq
    obtain ⟨j, hj, hXj⟩ := List.mem_iff_getElem.mp ((hmem X).mpr hq.1)
    refine ⟨j, hj, ?_, hXj.symm⟩
    by_contra hle
    push Not at hle
    have hcur : P.wrpOrd w L[i] X := hq.2 L[i] rfl
    rcases Nat.lt_or_ge j i with hji | hij
    · -- L[j] ≺ L[i] and L[i] ≺ L[j]: contradiction
      have h1 : P.wrpOrd w L[j] L[i] := hpair j i hj hi hji
      rw [← hXj] at hcur
      exact absurd (hV.trans w L[i] L[j] L[i] (hsel i hi) (hsel j hj) (hsel i hi)
        hcur h1) (hV.irrefl w L[i] (hsel i hi))
    · have hji : j = i := by omega
      subst hji
      rw [← hXj] at hcur
      exact absurd hcur (hV.irrefl w L[j] (hsel j hj))
  by_cases hnext : i + 1 < L.length
  · rw [List.getElem?_eq_getElem hnext]
    refine Or.inr ⟨L[i+1], rfl, ⟨hsel _ hnext, ?_⟩, ?_⟩
    · intro a ha
      rw [Option.mem_def, Option.some.injEq] at ha
      subst ha
      exact hpair i (i+1) hi hnext (by omega)
    · intro X hq
      obtain ⟨j, hj, hij, rfl⟩ := hqualPos X hq
      rcases Nat.eq_or_lt_of_le hij with heq | hlt
      · exact Or.inl (by congr 1; omega)
      · exact Or.inr (hpair (i+1) j hnext hj (by omega))
  · rw [List.getElem?_eq_none (by omega)]
    refine Or.inl ⟨rfl, fun X hq => ?_⟩
    obtain ⟨j, hj, hij, rfl⟩ := hqualPos X hq
    omega


/-! ## §5 Extracted evaluation data and the uniform weight bound -/

section EvalDataSec

variable {Gamma : Type}

/-- The automaton/rank data extracted once from a WRP presentation. -/
structure EvalData (P : WRP.Presentation Step Gamma) where
  Mdom : SliceMSO.DetAuto Step
  hdom : ∀ w, Mdom.accepts w ↔ P.toPoly.domain w
  Msel : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))
  hsel : ∀ c w ī, (∀ i, ī i < w.length) →
    ((Msel c).accepts (markAtN _ w ī) ↔ P.toPoly.sel c w ī)
  Mlab : (c : Fin P.toPoly.K) → Gamma → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))
  hlab : ∀ c g w ī, (∀ i, ī i < w.length) →
    ((Mlab c g).accepts (markAtN _ w ī) ↔ P.toPoly.label c w ī = g)
  Mord : (c c' : Fin P.toPoly.K) →
    SliceMSO.DetAuto (MarkedN (P.toPoly.arity c + P.toPoly.arity c'))
  hord : ∀ c c' w ī, (∀ i, ī i < w.length) →
    ((Mord c c').accepts (markAtN _ w ī) ↔
      P.toPoly.ord c c' w (fun t => ī (Fin.castAdd _ t)) (fun t => ī (Fin.natAdd _ t)))
  κ : (c : Fin P.toPoly.K) → PrefixAdditiveRank Step P.d (P.toPoly.arity c)
  hκ : ∀ c w ī, P.rank c w ī = (κ c).eval w ī

/-- Extract the data (Büchi + `markedDFAN_exists` + the prefix-additive normal
form) with `Classical.choice`. -/
def mkEvalData (P : WRP.Presentation Step Gamma) : EvalData P where
  Mdom := Classical.choose (SliceMSO.buchi (Classical.choose P.toPoly.domainDef))
  hdom := fun w => by
    rw [Classical.choose_spec (SliceMSO.buchi (Classical.choose P.toPoly.domainDef)) w]
    exact (Classical.choose_spec P.toPoly.domainDef w).symm
  Msel := fun c =>
    Classical.choose (markedDFAN_exists _ (Classical.choose (P.toPoly.selDef c)))
  hsel := fun c w ī hī => by
    rw [Classical.choose_spec
      (markedDFAN_exists _ (Classical.choose (P.toPoly.selDef c))) w ī hī]
    exact (Classical.choose_spec (P.toPoly.selDef c) w ī).symm
  Mlab := fun c g =>
    Classical.choose (markedDFAN_exists _ (Classical.choose (P.toPoly.labelDef c g)))
  hlab := fun c g w ī hī => by
    rw [Classical.choose_spec
      (markedDFAN_exists _ (Classical.choose (P.toPoly.labelDef c g))) w ī hī]
    exact (Classical.choose_spec (P.toPoly.labelDef c g) w ī).symm
  Mord := fun c c' =>
    Classical.choose (markedDFAN_exists _ (Classical.choose (P.toPoly.ordDef c c')))
  hord := fun c c' w ī hī => by
    rw [Classical.choose_spec
      (markedDFAN_exists _ (Classical.choose (P.toPoly.ordDef c c'))) w ī hī]
    exact (Classical.choose_spec (P.toPoly.ordDef c c') w ī).symm
  κ := fun c => Classical.choose
    (isPrefixAdditiveRank_of_isRegularRankTerm (P.rankReg c))
  hκ := fun c => Classical.choose_spec
    (isPrefixAdditiveRank_of_isRegularRankTerm (P.rankReg c))

variable {P : WRP.Presentation Step Gamma} (E : EvalData P)

/-- Generic hop for nested `Finset.sup` bounds. -/
theorem le_sup_univ_of {α : Type*} [Fintype α] (f : α → ℕ) (x : α) (v : ℕ)
    (h : v ≤ f x) : v ≤ Finset.univ.sup f :=
  le_trans h (Finset.le_sup (Finset.mem_univ x))

/-- Per-copy weight bound. -/
def WbInner (c : Fin P.toPoly.K) : ℕ :=
  max (Finset.univ.sup fun i : Fin P.d => ((E.κ c).c0 i).natAbs)
    (Finset.univ.sup fun r : Fin (P.toPoly.arity c) =>
      let _ := ((E.κ c).A r).fintypeQ
      Finset.univ.sup fun q : ((E.κ c).A r).Q =>
        Finset.univ.sup fun a : Step =>
          Finset.univ.sup fun i : Fin P.d =>
            max (((E.κ c).A r).ω q a i).natAbs ((E.κ c).β r q a i).natAbs)

/-- Uniform bound on all rank weights of the extracted data. -/
def Wb : ℕ := Finset.univ.sup (WbInner E)

theorem c0_le_Wb (c : Fin P.toPoly.K) (i : Fin P.d) :
    ((E.κ c).c0 i).natAbs ≤ Wb E := by
  refine le_sup_univ_of (WbInner E) c _ ?_
  rw [WbInner]
  exact le_max_of_le_left (le_sup_univ_of _ i _ le_rfl)

theorem ω_le_Wb (c : Fin P.toPoly.K) (r : Fin (P.toPoly.arity c))
    (q : ((E.κ c).A r).Q) (a : Step) (i : Fin P.d) :
    (((E.κ c).A r).ω q a i).natAbs ≤ Wb E := by
  let _ := ((E.κ c).A r).fintypeQ
  refine le_sup_univ_of (WbInner E) c _ ?_
  rw [WbInner]
  refine le_max_of_le_right ?_
  refine le_sup_univ_of _ r _ ?_
  refine le_sup_univ_of _ q _ ?_
  refine le_sup_univ_of _ a _ ?_
  refine le_sup_univ_of _ i _ ?_
  exact le_max_left _ _

theorem β_le_Wb (c : Fin P.toPoly.K) (r : Fin (P.toPoly.arity c))
    (q : ((E.κ c).A r).Q) (a : Step) (i : Fin P.d) :
    ((E.κ c).β r q a i).natAbs ≤ Wb E := by
  let _ := ((E.κ c).A r).fintypeQ
  refine le_sup_univ_of (WbInner E) c _ ?_
  rw [WbInner]
  refine le_max_of_le_right ?_
  refine le_sup_univ_of _ r _ ?_
  refine le_sup_univ_of _ q _ ?_
  refine le_sup_univ_of _ a _ ?_
  refine le_sup_univ_of _ i _ ?_
  exact le_max_right _ _

end EvalDataSec

/-! ## §6 Rank-sweep payment sums and the dimension identity -/

section RankSums

variable {Gamma : Type} {P : WRP.Presentation Step Gamma} (E : EvalData P)

/-- The `ω`-contribution of position `j` for one rank source at dimension `i`. -/
def ωAt {D : ℕ} (A : RankSource Step D) (w : List Step) (i : Fin D) (j : ℕ) : ℤ :=
  (w[j]?).elim 0 (fun a => A.ω (A.stateBefore w j) a i)

/-- The `β`-correction read at the marked position `p`. -/
def βAt {D k : ℕ} (κ : PrefixAdditiveRank Step D k) (r : Fin k) (w : List Step)
    (i : Fin D) (p : ℕ) : ℤ :=
  (w[p]?).elim 0 (fun a => κ.β r ((κ.A r).stateBefore w p) a i)

theorem prefixRank_eq_sum_ωAt {D : ℕ} (A : RankSource Step D) (w : List Step)
    (i : Fin D) (p : ℕ) :
    A.prefixRank w p i = ∑ j ∈ Finset.range p, ωAt A w i j := rfl

theorem elim_pi_apply {D : ℕ} (o : Option Step) (f : Step → Fin D → ℤ) (i : Fin D) :
    (o.elim (0 : Fin D → ℤ) f) i = o.elim 0 (fun a => f a i) := by
  cases o <;> rfl

/-- Positive-counter total of one rank-sweep unit (side, copy, coordinate). -/
def uPos (side : Bool) (c : Fin P.toPoly.K) (r : Fin (P.toPoly.arity c))
    (w : List Step) (i : Fin P.d) (p : ℕ) : ℕ :=
  (∑ j ∈ Finset.range p, payP side (ωAt ((E.κ c).A r) w i j))
    + payP side (βAt (E.κ c) r w i p)

/-- Negative-counter total of one rank-sweep unit. -/
def uNeg (side : Bool) (c : Fin P.toPoly.K) (r : Fin (P.toPoly.arity c))
    (w : List Step) (i : Fin P.d) (p : ℕ) : ℕ :=
  (∑ j ∈ Finset.range p, payN side (ωAt ((E.κ c).A r) w i j))
    + payN side (βAt (E.κ c) r w i p)

theorem uPos_sub_uNeg (side : Bool) (c : Fin P.toPoly.K)
    (r : Fin (P.toPoly.arity c)) (w : List Step) (i : Fin P.d) (p : ℕ) :
    (uPos E side c r w i p : ℤ) - uNeg E side c r w i p
      = (if side then (1 : ℤ) else -1) *
          (((E.κ c).A r).prefixRank w p i + βAt (E.κ c) r w i p) := by
  rw [uPos, uNeg, prefixRank_eq_sum_ωAt]
  push_cast
  rw [show ((∑ j ∈ Finset.range p, (payP side (ωAt ((E.κ c).A r) w i j) : ℤ))
        + (payP side (βAt (E.κ c) r w i p) : ℤ))
      - ((∑ j ∈ Finset.range p, (payN side (ωAt ((E.κ c).A r) w i j) : ℤ))
        + (payN side (βAt (E.κ c) r w i p) : ℤ))
    = (∑ j ∈ Finset.range p, ((payP side (ωAt ((E.κ c).A r) w i j) : ℤ)
        - (payN side (ωAt ((E.κ c).A r) w i j) : ℤ)))
      + ((payP side (βAt (E.κ c) r w i p) : ℤ)
        - (payN side (βAt (E.κ c) r w i p) : ℤ)) by
      rw [Finset.sum_sub_distrib]; ring]
  have hterm : ∀ v : ℤ, (payP side v : ℤ) - payN side v = (if side then (1:ℤ) else -1) * v := by
    intro v
    rw [payP_sub_payN]
    cases side <;> simp
  simp only [hterm]
  rw [← Finset.mul_sum]
  ring

/-- Total payments into the positive counter over one whole dimension `i`. -/
def dimPos (cL : Fin P.toPoly.K) (tL : Fin (P.toPoly.arity cL) → ℕ)
    (cR : Fin P.toPoly.K) (tR : Fin (P.toPoly.arity cR) → ℕ)
    (w : List Step) (i : Fin P.d) : ℕ :=
  payP true ((E.κ cL).c0 i) + payP false ((E.κ cR).c0 i)
    + ∑ r, uPos E true cL r w i (tL r) + ∑ r, uPos E false cR r w i (tR r)

/-- Total payments into the negative counter over one whole dimension `i`. -/
def dimNeg (cL : Fin P.toPoly.K) (tL : Fin (P.toPoly.arity cL) → ℕ)
    (cR : Fin P.toPoly.K) (tR : Fin (P.toPoly.arity cR) → ℕ)
    (w : List Step) (i : Fin P.d) : ℕ :=
  payN true ((E.κ cL).c0 i) + payN false ((E.κ cR).c0 i)
    + ∑ r, uNeg E true cL r w i (tL r) + ∑ r, uNeg E false cR r w i (tR r)

/-- **The dimension identity**: the counter difference accumulated over one
dimension is the rank difference of the two atoms at that dimension. -/
theorem dimPos_sub_dimNeg (cL : Fin P.toPoly.K) (tL : Fin (P.toPoly.arity cL) → ℕ)
    (cR : Fin P.toPoly.K) (tR : Fin (P.toPoly.arity cR) → ℕ)
    (w : List Step) (i : Fin P.d) :
    (dimPos E cL tL cR tR w i : ℤ) - dimNeg E cL tL cR tR w i
      = (E.κ cL).eval w tL i - (E.κ cR).eval w tR i := by
  rw [dimPos, dimNeg, PrefixAdditiveRank.eval, PrefixAdditiveRank.eval]
  push_cast
  have hL : ∀ r : Fin (P.toPoly.arity cL),
      (uPos E true cL r w i (tL r) : ℤ) - uNeg E true cL r w i (tL r)
        = ((E.κ cL).A r).prefixRank w (tL r) i + βAt (E.κ cL) r w i (tL r) := by
    intro r
    rw [uPos_sub_uNeg]
    simp
  have hR : ∀ r : Fin (P.toPoly.arity cR),
      (uNeg E false cR r w i (tR r) : ℤ) - uPos E false cR r w i (tR r)
        = ((E.κ cR).A r).prefixRank w (tR r) i + βAt (E.κ cR) r w i (tR r) := by
    intro r
    have := uPos_sub_uNeg E false cR r w i (tR r)
    simp only [if_false, Bool.false_eq_true, neg_mul, one_mul] at this
    omega
  have hc0L := payP_sub_payN true ((E.κ cL).c0 i)
  have hc0R := payP_sub_payN false ((E.κ cR).c0 i)
  simp only [if_true, if_false, Bool.false_eq_true] at hc0L hc0R
  have hsumL : (∑ r, (uPos E true cL r w i (tL r) : ℤ))
      - ∑ r, (uNeg E true cL r w i (tL r) : ℤ)
      = ∑ r, (((E.κ cL).A r).prefixRank w (tL r) i + βAt (E.κ cL) r w i (tL r)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => hL r
  have hsumR : (∑ r, (uNeg E false cR r w i (tR r) : ℤ))
      - ∑ r, (uPos E false cR r w i (tR r) : ℤ)
      = ∑ r, (((E.κ cR).A r).prefixRank w (tR r) i + βAt (E.κ cR) r w i (tR r)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => hR r
  -- eval's β-summand is `βAt` (the `Option.elim` applied pointwise)
  have hβptL : ∀ r, ((w[tL r]?).elim (0 : Fin P.d → ℤ)
      (fun a => (E.κ cL).β r (((E.κ cL).A r).stateBefore w (tL r)) a)) i
      = βAt (E.κ cL) r w i (tL r) := by
    intro r
    rw [elim_pi_apply, βAt]
  have hβptR : ∀ r, ((w[tR r]?).elim (0 : Fin P.d → ℤ)
      (fun a => (E.κ cR).β r (((E.κ cR).A r).stateBefore w (tR r)) a)) i
      = βAt (E.κ cR) r w i (tR r) := by
    intro r
    rw [elim_pi_apply, βAt]
  simp only [hβptL, hβptR]
  omega

end RankSums

/-! ## §7 The evaluator machine: control types, registers, transitions

-/

inductive CmpId | curCand | candBest
  deriving DecidableEq

instance : Fintype CmpId :=
  ⟨⟨{.curCand, .candBest}, by decide⟩, fun x => by cases x <;> decide⟩

inductive JobId (K G : ℕ)
  | dom
  | sel (c : Fin K)
  | lab (c : Fin K) (g : Fin G)
  | ord (π : CmpId) (cL cR : Fin K)
  deriving DecidableEq, Fintype

inductive Cont (K G d kmax : ℕ)
  | domK
  | selK
  | labK (g : Fin G)
  | tieK (π : CmpId)
  | unitK (π : CmpId) (cL cR : Fin K) (i : Fin d) (side : Bool) (r : Fin kmax)
  deriving DecidableEq, Fintype

inductive CmpStage (kmax W : ℕ)
  | c0load (side : Bool)
  | c0pay (side : Bool) (t : Fin (W + 1)) (tgt : Bool)
  | scanU (side : Bool) (r : Fin kmax)
  | payU (side : Bool) (r : Fin kmax) (t : Fin (W + 1)) (tgt : Bool) (ex : Bool)
  | drain
  | zero (tgt : Bool) (v : Bool)
  deriving DecidableEq, Fintype

inductive WalkId | parkCand | parkBest | parkCur | parkCandBest | copyBest | copyCur
  deriving DecidableEq

instance : Fintype WalkId :=
  ⟨⟨{.parkCand, .parkBest, .parkCur, .parkCandBest, .copyBest, .copyCur}, by decide⟩,
    fun x => by cases x <;> decide⟩

inductive Tag (K G d kmax W : ℕ)
  | sweep (J : JobId K G) (κ : Cont K G d kmax)
  | rewind (κ : Cont K G d kmax) (b : Bool)
  | reject
  | accept
  | roundStart
  | candInit
  | candInit2
  | candNext (r : Fin (kmax + 1))
  | candNext2 (r : Fin (kmax + 1))
  | candCarry (r : Fin (kmax + 1))
  | candCarry2 (r : Fin (kmax + 1))
  | cmp (π : CmpId) (cL cR : Fin K) (i : Fin d) (st : CmpStage kmax W)
  | walk (wk : WalkId)
  deriving DecidableEq, Fintype

variable {Gamma : Type} [Fintype Gamma]
variable {P : WRP.Presentation Step Gamma}

/-- The head-block width: the maximum arity over all copies. -/
def kmaxP (P : WRP.Presentation Step Gamma) : ℕ :=
  Finset.univ.sup fun c : Fin P.toPoly.K => P.toPoly.arity c

omit [Fintype Gamma] in
theorem arity_le_kmax (c : Fin P.toPoly.K) : P.toPoly.arity c ≤ kmaxP P :=
  Finset.le_sup (Finset.mem_univ c)

/-- Number of heads: one scan head plus the CUR/CAND/BEST blocks. -/
abbrev hN (P : WRP.Presentation Step Gamma) : ℕ := 3 * kmaxP P + 1

def scanH : Fin (hN P) := ⟨0, by show 0 < 3 * kmaxP P + 1; omega⟩
def curH (r : Fin (kmaxP P)) : Fin (hN P) :=
  ⟨1 + r.val, by show 1 + r.val < 3 * kmaxP P + 1; have := r.2; omega⟩
def candH (r : Fin (kmaxP P)) : Fin (hN P) :=
  ⟨1 + kmaxP P + r.val, by show 1 + kmaxP P + r.val < 3 * kmaxP P + 1; have := r.2; omega⟩
def bestH (r : Fin (kmaxP P)) : Fin (hN P) :=
  ⟨1 + 2 * kmaxP P + r.val,
    by show 1 + 2 * kmaxP P + r.val < 3 * kmaxP P + 1; have := r.2; omega⟩

def sideHead : CmpId → Bool → Fin (kmaxP P) → Fin (hN P)
  | .curCand, true => curH
  | .curCand, false => candH
  | .candBest, true => candH
  | .candBest, false => bestH

def embedA {c : Fin P.toPoly.K} (i : Fin (P.toPoly.arity c)) : Fin (kmaxP P) :=
  ⟨i.val, lt_of_lt_of_le i.2 (arity_le_kmax c)⟩

/-- Arity of each sweep job's marked alphabet. -/
def jobArity (P : WRP.Presentation Step Gamma) :
    JobId P.toPoly.K (Fintype.card Gamma) → ℕ
  | .dom => 0
  | .sel c => P.toPoly.arity c
  | .lab c _ => P.toPoly.arity c
  | .ord _ cL cR => P.toPoly.arity cL + P.toPoly.arity cR

/-- The fixed enumeration of the output alphabet. -/
def γenum (g : Fin (Fintype.card Gamma)) : Gamma := (Fintype.equivFin Gamma).symm g

theorem γenum_injective : Function.Injective (γenum (Gamma := Gamma)) :=
  fun _ _ h => (Fintype.equivFin Gamma).symm.injective h

variable (E : EvalData P)

/-- The deterministic acceptor run by each sweep job. -/
def jobDFA : (J : JobId P.toPoly.K (Fintype.card Gamma)) →
    SliceMSO.DetAuto (MarkedN (jobArity P J))
  | .dom => E.Mdom
  | .sel c => E.Msel c
  | .lab c g => E.Mlab c (γenum g)
  | .ord _ cL cR => E.Mord cL cR

/-- The mark heads of each sweep job. -/
def jobHeads : (J : JobId P.toPoly.K (Fintype.card Gamma)) →
    Fin (jobArity P J) → Fin (hN P)
  | .dom => fun i => i.elim0
  | .sel _ => fun i => candH (embedA i)
  | .lab _ _ => fun i => bestH (embedA i)
  | .ord π _ _ => Fin.addCases (fun i => sideHead π true (embedA i))
      (fun i => sideHead π false (embedA i))


/-! Registers. -/

/-- Index of a rank-sweep register: a copy and one of its coordinates. -/
abbrev RIdx (P : WRP.Presentation Step Gamma) :=
  Σ c : Fin P.toPoly.K, Fin (P.toPoly.arity c)

/-- The rank source attached to a register index. -/
def rsrc (p : RIdx P) : RankSource Step P.d := (E.κ p.1).A p.2

instance instFintypeJobQ (J : JobId P.toPoly.K (Fintype.card Gamma)) :
    Fintype (jobDFA E J).Q := (jobDFA E J).fintypeQ

instance instFintypeRsrcQ (p : RIdx P) : Fintype (rsrc E p).Q := (rsrc E p).fintypeQ

/-- The register: idle, a sweep-DFA state, or a rank-source state. -/
def Reg : Type :=
  Unit ⊕ (Σ J : JobId P.toPoly.K (Fintype.card Gamma), (jobDFA E J).Q)
    ⊕ (Σ p : RIdx P, (rsrc E p).Q)

instance : Fintype (Reg E) := by
  unfold Reg
  infer_instance

def Reg.unit : Reg E := Sum.inl ()
def Reg.job (x : Σ J : JobId P.toPoly.K (Fintype.card Gamma), (jobDFA E J).Q) :
    Reg E := Sum.inr (Sum.inl x)
def Reg.rank (x : Σ p : RIdx P, (rsrc E p).Q) : Reg E := Sum.inr (Sum.inr x)

/-- Project the register onto job `J`'s DFA state. -/
def jobProj (J : JobId P.toPoly.K (Fintype.card Gamma)) : Reg E → Option (jobDFA E J).Q
  | Sum.inr (Sum.inl ⟨J', q⟩) => if h : J' = J then some (h ▸ q) else none
  | _ => none

@[simp] theorem jobProj_job_self (J : JobId P.toPoly.K (Fintype.card Gamma))
    (q : (jobDFA E J).Q) : jobProj E J (Reg.job E ⟨J, q⟩) = some q := by
  show (if h : J = J then some (h ▸ q) else none) = some q
  rw [dif_pos rfl]

/-- Project the register onto rank source `p`'s state. -/
def rankProj (p : RIdx P) : Reg E → Option (rsrc E p).Q
  | Sum.inr (Sum.inr ⟨p', q⟩) => if h : p' = p then some (h ▸ q) else none
  | _ => none

@[simp] theorem rankProj_rank_self (p : RIdx P) (q : (rsrc E p).Q) :
    rankProj E p (Reg.rank E ⟨p, q⟩) = some q := by
  show (if h : p = p then some (h ▸ q) else none) = some q
  rw [dif_pos rfl]

/-- The Boolean acceptance of a job DFA (classical). -/
def acceptB (J : JobId P.toPoly.K (Fintype.card Gamma)) (q : (jobDFA E J).Q) : Bool :=
  decide ((jobDFA E J).accept q)

theorem acceptB_iff (J : JobId P.toPoly.K (Fintype.card Gamma))
    (q : (jobDFA E J).Q) : acceptB E J q = true ↔ (jobDFA E J).accept q := by
  rw [acceptB, decide_eq_true_iff]

/-! Global data and small helpers. -/

/-- Global loop data: current atom's copy, candidate copy, best-so-far copy. -/
abbrev Glob (K : ℕ) : Type := Option (Fin K) × Option (Fin K) × Option (Fin K)

/-- Successor of a copy index. -/
def finSucc {K : ℕ} (c : Fin K) : Option (Fin K) :=
  if h : c.val + 1 < K then some ⟨c.val + 1, h⟩ else none

/-- The full machine state. -/
def EQ : Type := Glob P.toPoly.K ×
  Tag P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P) (Wb E) × Reg E

instance : Fintype (EQ E) := by
  unfold EQ
  infer_instance

def mvStay : Fin (hN P) → HeadMove := fun _ => .stay
def mvOne (x : Fin (hN P)) (m : HeadMove) : Fin (hN P) → HeadMove :=
  fun a => if a = x then m else .stay
def opsKeep : Fin 2 → CounterOp := fun _ => .keep
def ctrIdx (tgt : Bool) : Fin 2 := if tgt then 0 else 1
def opsInc (tgt : Bool) : Fin 2 → CounterOp :=
  fun j => if j = ctrIdx tgt then .inc else .keep
def opsDec (tgt : Bool) : Fin 2 → CounterOp :=
  fun j => if j = ctrIdx tgt then .dec else .keep
def opsDecBoth : Fin 2 → CounterOp := fun _ => .dec

/-! Tag builders. -/

/-- Local abbreviation for this machine's tag type. -/
abbrev TagT (E : EvalData P) : Type :=
  Tag P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P) (Wb E)

/-- Enter the candidate-successor gadget for the current candidate copy. -/
def candNextEntry (g : Glob P.toPoly.K) : Option (TagT E) :=
  g.2.1.map fun c =>
    .candNext ⟨P.toPoly.arity c, Nat.lt_succ_of_le (arity_le_kmax c)⟩

/-- Enter the ≺-comparison of the pair `π` (dimension 0, or the tie sweep when
`d = 0`). -/
def cmpEntryTag (π : CmpId) (cL cR : Fin P.toPoly.K) : TagT E :=
  if hd : 0 < P.d then .cmp π cL cR ⟨0, hd⟩ (.c0load true)
  else .sweep (.ord π cL cR) (.tieK π)

/-- First rank-sweep unit of the right side (or drain if it has none). -/
def firstRTag (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d) : TagT E :=
  if h : 0 < P.toPoly.arity cR then
    .cmp π cL cR i (.scanU false ⟨0, lt_of_lt_of_le h (arity_le_kmax cR)⟩)
  else .cmp π cL cR i .drain

/-- First rank-sweep unit of a dimension. -/
def firstUnitTag (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d) : TagT E :=
  if h : 0 < P.toPoly.arity cL then
    .cmp π cL cR i (.scanU true ⟨0, lt_of_lt_of_le h (arity_le_kmax cL)⟩)
  else firstRTag E π cL cR i

/-- The unit after `(side, r)`. -/
def nextUnitTag (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d)
    (side : Bool) (r : Fin (kmaxP P)) : TagT E :=
  if side then
    (if h : r.val + 1 < P.toPoly.arity cL then
      .cmp π cL cR i (.scanU true ⟨r.val + 1, lt_of_lt_of_le h (arity_le_kmax cL)⟩)
     else firstRTag E π cL cR i)
  else
    (if h : r.val + 1 < P.toPoly.arity cR then
      .cmp π cL cR i (.scanU false ⟨r.val + 1, lt_of_lt_of_le h (arity_le_kmax cR)⟩)
     else .cmp π cL cR i .drain)

/-- After the candidate qualified against CUR: check it against BEST. -/
def bestUpdTag (g : Glob P.toPoly.K) : Option (TagT E) :=
  match g.2.1, g.2.2 with
  | some _, none => some (.walk .parkBest)
  | some ca, some cb => some (cmpEntryTag E .candBest ca cb)
  | none, _ => none

/-- Exit dispatch of the ≺-comparison `π` with verdict `v`. -/
def cmpExit (π : CmpId) (v : Bool) (g : Glob P.toPoly.K) : Option (TagT E) :=
  match π, v with
  | .curCand, true => bestUpdTag E g
  | .curCand, false => candNextEntry E g
  | .candBest, true => some (.walk .parkBest)
  | .candBest, false => candNextEntry E g

/-- Dispatch at the left marker after a sweep/rank rewind. -/
def contStep (κ : Cont P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P)) (b : Bool)
    (g : Glob P.toPoly.K) :
    Option (Glob P.toPoly.K × TagT E × List Gamma) :=
  match κ with
  | .domK =>
      if b then some ((none, none, none), .roundStart, [])
      else some (g, .reject, [])
  | .selK =>
      if b then
        match g.1, g.2.1 with
        | none, _ => (bestUpdTag E g).map fun tg => (g, tg, [])
        | some cu, some ca => some (g, cmpEntryTag E .curCand cu ca, [])
        | some _, none => none
      else (candNextEntry E g).map fun tg => (g, tg, [])
  | .labK gg =>
      if b then some (g, .walk .parkCur, [γenum gg])
      else
        match g.2.2 with
        | some cB =>
            if h : gg.val + 1 < Fintype.card Gamma then
              some (g, .sweep (.lab cB ⟨gg.val + 1, h⟩) (.labK ⟨gg.val + 1, h⟩), [])
            else none
        | none => none
  | .tieK π => (cmpExit E π b g).map fun tg => (g, tg, [])
  | .unitK π cL cR i side r => some (g, nextUnitTag E π cL cR i side r, [])

/-! The walk gadget. -/

def wkLo (P : WRP.Presentation Step Gamma) : WalkId → ℕ
  | .parkCand => 1 + kmaxP P
  | .parkBest => 1 + 2 * kmaxP P
  | .parkCur => 1
  | .parkCandBest => 1 + kmaxP P
  | .copyBest => 1 + 2 * kmaxP P
  | .copyCur => 1

def wkHi (P : WRP.Presentation Step Gamma) : WalkId → ℕ
  | .parkCand => 1 + 2 * kmaxP P
  | .parkBest => 1 + 3 * kmaxP P
  | .parkCur => 1 + kmaxP P
  | .parkCandBest => 1 + 3 * kmaxP P
  | .copyBest => 1 + 3 * kmaxP P
  | .copyCur => 1 + kmaxP P

/-- Membership of a head (by value) in the walked block. -/
def wkIn (wk : WalkId) (v : ℕ) : Prop := wkLo P wk ≤ v ∧ v < wkHi P wk

instance (wk : WalkId) (v : ℕ) : Decidable (wkIn (P := P) wk v) := by
  unfold wkIn
  infer_instance

/-- Park walks move left to `⊢`; copy walks move right to coincidence. -/
def wkPark : WalkId → Bool
  | .parkCand => true
  | .parkBest => true
  | .parkCur => true
  | .parkCandBest => true
  | .copyBest => false
  | .copyCur => false

/-- The partner head a copy walk approaches. -/
def wkPartner (wk : WalkId) (a : Fin (hN P)) : Fin (hN P) :=
  match wk with
  | .copyBest => ⟨a.val - kmaxP P, by have := a.2; omega⟩
  | .copyCur =>
      if h : a.val + 2 * kmaxP P < hN P then ⟨a.val + 2 * kmaxP P, h⟩ else a
  | _ => a

/-- The walk's done condition (all block heads parked / coinciding). -/
def wkDone (wk : WalkId) (syms : Fin (hN P) → TapeSym Step)
    (coin : Fin (hN P) → Fin (hN P) → Bool) : Prop :=
  ∀ a : Fin (hN P), wkIn (P := P) wk a.val →
    (if wkPark wk then syms a = TapeSym.lmark
     else coin a (wkPartner (P := P) wk a) = true)

instance (wk : WalkId) (syms : Fin (hN P) → TapeSym Step)
    (coin : Fin (hN P) → Fin (hN P) → Bool) :
    Decidable (wkDone (P := P) wk syms coin) := by
  unfold wkDone
  infer_instance

/-- The walk's per-head moves. -/
def walkMoves (wk : WalkId) (syms : Fin (hN P) → TapeSym Step)
    (coin : Fin (hN P) → Fin (hN P) → Bool) : Fin (hN P) → HeadMove := fun a =>
  if wkIn (P := P) wk a.val then
    (if wkPark wk then (if syms a = TapeSym.lmark then .stay else .left)
     else (if coin a (wkPartner (P := P) wk a) then .stay else .right))
  else .stay

/-- The walk's exit transition. -/
def wkExit (wk : WalkId) (g : Glob P.toPoly.K) :
    Option (Glob P.toPoly.K × TagT E) :=
  match wk with
  | .parkCand =>
      match g.2.1 with
      | none => none
      | some c =>
          match finSucc c with
          | some c' => some ((g.1, some c', g.2.2), .candInit)
          | none =>
              match g.2.2 with
              | none => some (g, .accept)
              | some cB =>
                  if hg : 0 < Fintype.card Gamma then
                    some (g, .sweep (.lab cB ⟨0, hg⟩) (.labK ⟨0, hg⟩))
                  else none
  | .parkBest => some (g, .walk .copyBest)
  | .copyBest =>
      match g.2.1 with
      | some c => (candNextEntry E (g.1, some c, some c)).map fun tg =>
          ((g.1, some c, some c), tg)
      | none => none
  | .parkCur => some (g, .walk .copyCur)
  | .copyCur => some ((g.2.2, g.2.1, g.2.2), .walk .parkCandBest)
  | .parkCandBest => some ((g.1, g.2.1, none), .roundStart)

/-! The compare-phase transition function. -/

/-- Transition on `cmp` tags. -/
def cmpEta (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d)
    (st : CmpStage (kmaxP P) (Wb E)) (g : Glob P.toPoly.K) (reg : Reg E)
    (syms : Fin (hN P) → TapeSym Step) (coin : Fin (hN P) → Fin (hN P) → Bool)
    (zs : Fin 2 → Bool) :
    Option (EQ E × (Fin (hN P) → HeadMove) × (Fin 2 → CounterOp) × List Gamma) :=
  match st with
  | .c0load side =>
      let cc := if side then cL else cR
      let v := (E.κ cc).c0 i
      some ((g, .cmp π cL cR i
          (.c0pay side ⟨v.natAbs, Nat.lt_succ_of_le (c0_le_Wb E cc i)⟩ (tgtOf side v)),
        reg), mvStay, opsKeep, [])
  | .c0pay side t tgt =>
      if 0 < t.val then
        some ((g, .cmp π cL cR i (.c0pay side ⟨t.val - 1, by omega⟩ tgt), reg),
          mvStay, opsInc tgt, [])
      else if side then
        some ((g, .cmp π cL cR i (.c0load false), reg), mvStay, opsKeep, [])
      else some ((g, firstUnitTag E π cL cR i, reg), mvStay, opsKeep, [])
  | .scanU side r =>
      let cc := if side then cL else cR
      if hcr : r.val < P.toPoly.arity cc then
        match syms scanH with
        | .lmark =>
            some ((g, .cmp π cL cR i (.scanU side r),
              Reg.rank E ⟨⟨cc, ⟨r.val, hcr⟩⟩, (rsrc E ⟨cc, ⟨r.val, hcr⟩⟩).q0⟩),
              mvOne scanH .right, opsKeep, [])
        | .letter a =>
            (rankProj E ⟨cc, ⟨r.val, hcr⟩⟩ reg).map fun qr =>
              if coin scanH (sideHead π side r) then
                let v := (E.κ cc).β ⟨r.val, hcr⟩ qr a i
                ((g, .cmp π cL cR i (.payU side r
                    ⟨v.natAbs, Nat.lt_succ_of_le (β_le_Wb E cc ⟨r.val, hcr⟩ qr a i)⟩
                    (tgtOf side v) true), reg), mvStay, opsKeep, [])
              else
                let v := (rsrc E ⟨cc, ⟨r.val, hcr⟩⟩).ω qr a i
                ((g, .cmp π cL cR i (.payU side r
                    ⟨v.natAbs, Nat.lt_succ_of_le (ω_le_Wb E cc ⟨r.val, hcr⟩ qr a i)⟩
                    (tgtOf side v) false),
                  Reg.rank E ⟨⟨cc, ⟨r.val, hcr⟩⟩, (rsrc E ⟨cc, ⟨r.val, hcr⟩⟩).δ qr a⟩),
                  mvStay, opsKeep, [])
        | .rmark => none
      else none
  | .payU side r t tgt ex =>
      if 0 < t.val then
        some ((g, .cmp π cL cR i (.payU side r ⟨t.val - 1, by omega⟩ tgt ex), reg),
          mvStay, opsInc tgt, [])
      else if ex then
        some ((g, .rewind (.unitK π cL cR i side r) true, reg), mvStay, opsKeep, [])
      else
        some ((g, .cmp π cL cR i (.scanU side r), reg), mvOne scanH .right, opsKeep, [])
  | .drain =>
      match zs 0, zs 1 with
      | true, true =>
          if hi : i.val + 1 < P.d then
            some ((g, .cmp π cL cR ⟨i.val + 1, hi⟩ (.c0load true), reg),
              mvStay, opsKeep, [])
          else some ((g, .sweep (.ord π cL cR) (.tieK π), reg), mvStay, opsKeep, [])
      | true, false => some ((g, .cmp π cL cR i (.zero false true), reg),
          mvStay, opsKeep, [])
      | false, true => some ((g, .cmp π cL cR i (.zero true false), reg),
          mvStay, opsKeep, [])
      | false, false => some ((g, .cmp π cL cR i .drain, reg),
          mvStay, opsDecBoth, [])
  | .zero tgt v =>
      if zs (ctrIdx tgt) then
        (cmpExit E π v g).map fun tg => ((g, tg, reg), mvStay, opsKeep, [])
      else
        some ((g, .cmp π cL cR i (.zero tgt v), reg), mvStay, opsDec tgt, [])

/-! The walk transition and the full raw transition function. -/

def walkEta (wk : WalkId) (g : Glob P.toPoly.K) (reg : Reg E)
    (syms : Fin (hN P) → TapeSym Step) (coin : Fin (hN P) → Fin (hN P) → Bool) :
    Option (EQ E × (Fin (hN P) → HeadMove) × (Fin 2 → CounterOp) × List Gamma) :=
  if wkDone (P := P) wk syms coin then
    (wkExit E wk g).map fun r => ((r.1, r.2, reg), mvStay, opsKeep, [])
  else some ((g, .walk wk, reg), walkMoves (P := P) wk syms coin, opsKeep, [])

/-- The raw transition function (before the end-marker guard). -/
def rawEta (q : EQ E) (syms : Fin (hN P) → TapeSym Step)
    (coin : Fin (hN P) → Fin (hN P) → Bool) (zs : Fin 2 → Bool) :
    Option (EQ E × (Fin (hN P) → HeadMove) × (Fin 2 → CounterOp) × List Gamma) :=
  match q with
  | (g, .sweep J κ, reg) =>
      match syms scanH with
      | .lmark =>
          some ((g, .sweep J κ, Reg.job E ⟨J, (jobDFA E J).q0⟩),
            mvOne scanH .right, opsKeep, [])
      | .letter a =>
          (jobProj E J reg).map fun qj =>
            ((g, .sweep J κ, Reg.job E ⟨J, (jobDFA E J).δ qj
                (mkLetter (jobArity P J) a (fun i => coin scanH (jobHeads J i)))⟩),
              mvOne scanH .right, opsKeep, [])
      | .rmark =>
          (jobProj E J reg).map fun qj =>
            ((g, .rewind κ (acceptB E J qj), reg), mvStay, opsKeep, [])
  | (g, .rewind κ b, reg) =>
      match syms scanH with
      | .lmark => (contStep E κ b g).map fun r => ((r.1, r.2.1, reg), mvStay, opsKeep, r.2.2)
      | _ => some ((g, .rewind κ b, reg), mvOne scanH .left, opsKeep, [])
  | (_, .reject, _) => none
  | (_, .accept, _) => none
  | (g, .roundStart, reg) =>
      if hK : 0 < P.toPoly.K then
        some (((g.1, some ⟨0, hK⟩, g.2.2), .candInit, reg), mvStay, opsKeep, [])
      else some (((g.1, none, g.2.2), .accept, reg), mvStay, opsKeep, [])
  | (g, .candInit, reg) =>
      match g.2.1 with
      | none => none
      | some c =>
          if P.toPoly.arity c = 0 then
            some ((g, .sweep (.sel c) .selK, reg), mvStay, opsKeep, [])
          else
            some ((g, .candInit2, reg),
              (fun a => if 1 + kmaxP P ≤ a.val ∧ a.val < 1 + kmaxP P + P.toPoly.arity c
                then .right else .stay), opsKeep, [])
  | (g, .candInit2, reg) =>
      match g.2.1 with
      | none => none
      | some c =>
          if h0 : 0 < kmaxP P then
            match syms (candH ⟨0, h0⟩) with
            | .rmark => some ((g, .walk .parkCand, reg), mvStay, opsKeep, [])
            | .letter _ => some ((g, .sweep (.sel c) .selK, reg), mvStay, opsKeep, [])
            | .lmark => none
          else none
  | (g, .candNext r, reg) =>
      match g.2.1 with
      | none => none
      | some _ =>
          if hr : 0 < r.val then
            some ((g, .candNext2 r, reg),
              mvOne (candH ⟨r.val - 1, by have := r.2; omega⟩) .right, opsKeep, [])
          else some ((g, .walk .parkCand, reg), mvStay, opsKeep, [])
  | (g, .candNext2 r, reg) =>
      match g.2.1 with
      | none => none
      | some c =>
          if hr : 0 < r.val then
            match syms (candH ⟨r.val - 1, by have := r.2; omega⟩) with
            | .letter _ => some ((g, .sweep (.sel c) .selK, reg), mvStay, opsKeep, [])
            | .rmark => some ((g, .candCarry r, reg), mvStay, opsKeep, [])
            | .lmark => none
          else none
  | (g, .candCarry r, reg) =>
      if hr : 0 < r.val then
        match syms (candH ⟨r.val - 1, by have := r.2; omega⟩) with
        | .lmark => some ((g, .candCarry2 r, reg), mvStay, opsKeep, [])
        | _ => some ((g, .candCarry r, reg),
            mvOne (candH ⟨r.val - 1, by have := r.2; omega⟩) .left, opsKeep, [])
      else none
  | (g, .candCarry2 r, reg) =>
      if hr : 0 < r.val then
        some ((g, .candNext ⟨r.val - 1, by have := r.2; omega⟩, reg),
          mvOne (candH ⟨r.val - 1, by have := r.2; omega⟩) .right, opsKeep, [])
      else none
  | (g, .cmp π cL cR i st, reg) => cmpEta E π cL cR i st g reg syms coin zs
  | (g, .walk wk, reg) => walkEta E wk g reg syms coin

/-- The end-marker guard: a right move on a head reading `⊣` becomes `stay`. -/
def guardMoves (syms : Fin (hN P) → TapeSym Step) (mv : Fin (hN P) → HeadMove) :
    Fin (hN P) → HeadMove := fun a =>
  if syms a = TapeSym.rmark ∧ mv a = HeadMove.right then .stay else mv a

omit [Fintype Gamma] in
theorem guardMoves_eq_of (syms : Fin (hN P) → TapeSym Step)
    (mv : Fin (hN P) → HeadMove)
    (h : ∀ a, mv a = HeadMove.right → syms a ≠ TapeSym.rmark) :
    guardMoves (P := P) syms mv = mv := by
  funext a
  rw [guardMoves]
  by_cases hmv : mv a = HeadMove.right
  · rw [if_neg]
    rintro ⟨hs, -⟩
    exact h a hmv hs
  · rw [if_neg]
    rintro ⟨-, hs⟩
    exact hmv hs

/-- **The WRP evaluator machine.** -/
def evalM : Multihead.MHC Step Gamma (hN P) 2 where
  Q := EQ E
  fintypeQ := inferInstance
  q0 := ((none, none, none), .sweep .dom .domK, Reg.unit E)
  F := fun q => q.2.1 = .accept
  η := fun q syms coin zs => (rawEta E q syms coin zs).map fun r =>
    (r.1, guardMoves (P := P) syms r.2.1, r.2.2)
  rmark_no_right := by
    intro q syms coin zs r hr a hrm
    rw [Option.map_eq_some_iff] at hr
    obtain ⟨r0, -, rfl⟩ := hr
    show guardMoves (P := P) syms r0.2.1 a ≠ HeadMove.right
    rw [guardMoves]
    by_cases hmv : r0.2.1 a = HeadMove.right
    · rw [if_pos ⟨hrm, hmv⟩]
      exact fun hc => by cases hc
    · rw [if_neg (fun hc => hmv hc.2)]
      exact hmv


/-! ## §8 Run helpers, the rewind gadget, and the sweep lemma

-/

variable (E : EvalData P)

/-! Generic tape-symbol facts. -/

theorem tapeSym_eq_lmark_iff {Alpha : Type*} (w : List Alpha) (i : ℕ) :
    tapeSym w i = TapeSym.lmark ↔ i = 0 := by
  constructor
  · intro h
    by_contra hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    by_cases hj : j < w.length
    · rw [tapeSym_succ w j hj] at h
      cases h
    · rw [tapeSym_ge w (j + 1) (by omega)] at h
      cases h
  · rintro rfl
    exact tapeSym_zero w

theorem tapeSym_ne_rmark_of_le {Alpha : Type*} {w : List Alpha} {i : ℕ}
    (h : i ≤ w.length) : tapeSym w i ≠ TapeSym.rmark := by
  intro hc
  cases i with
  | zero => rw [tapeSym_zero] at hc; cases hc
  | succ j =>
      rw [tapeSym_succ w j (by omega)] at hc
      cases hc

theorem foldl_take_succ {α β : Type*} (f : β → α → β) (b : β) (l : List α)
    (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).foldl f b = f ((l.take j).foldl f b) l[j] := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hj]
  rfl

/-! Step and run helpers for the evaluator. -/

/-- One raw-transition step, with explicit successor position/counter forms. -/
theorem stepRaw {w : List Step} {g : Glob P.toPoly.K} {t : TagT E} {reg : Reg E}
    {pos : Fin (hN P) → ℕ} {cnt : Fin 2 → ℕ}
    {q' : EQ E} {mv : Fin (hN P) → HeadMove} {ops : Fin 2 → CounterOp}
    {u out : List Gamma} {pos₂ : Fin (hN P) → ℕ} {cnt₂ : Fin 2 → ℕ}
    {e : (evalM E).Config}
    (hraw : rawEta E (g, t, reg) (fun a => tapeSym w (pos a))
      (fun a b => pos a == pos b) (fun j => cnt j == 0) = some (q', mv, ops, u))
    (hguard : ∀ a, mv a = HeadMove.right → tapeSym w (pos a) ≠ TapeSym.rmark)
    (hpos₂ : (fun a => (mv a).apply (pos a)) = pos₂)
    (hcnt₂ : (fun j => (ops j).apply (cnt j)) = cnt₂)
    (hrest : (evalM E).Steps w (q', pos₂, cnt₂) out e) :
    (evalM E).Steps w ((g, t, reg), pos, cnt) (u ++ out) e := by
  obtain ⟨N, hsN⟩ := hrest
  have hη : (evalM E).η (g, t, reg) (fun a => tapeSym w (pos a))
      (fun a b => pos a == pos b) (fun j => cnt j == 0) = some (q', mv, ops, u) := by
    show (rawEta E (g, t, reg) _ _ _).map _ = _
    rw [hraw, Option.map_some, guardMoves_eq_of _ _ hguard]
  have hsN' : (evalM E).StepsN w
      (q', fun a => (mv a).apply (pos a), fun j => (ops j).apply (cnt j)) out e N := by
    rw [hpos₂, hcnt₂]
    exact hsN
  exact ⟨N + 1, Multihead.MHC.StepsN.head hη hsN'⟩

/-- Transitivity for `Steps`. -/
theorem stepsTrans {w : List Step} {c₁ c₂ c₃ : (evalM E).Config}
    {o₁ o₂ : List Gamma} (h₁ : (evalM E).Steps w c₁ o₁ c₂)
    (h₂ : (evalM E).Steps w c₂ o₂ c₃) : (evalM E).Steps w c₁ (o₁ ++ o₂) c₃ := by
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  exact ⟨N₁ + N₂, h₁.trans h₂⟩

theorem stepsRefl {w : List Step} (c : (evalM E).Config) :
    (evalM E).Steps w c [] c := ⟨0, Multihead.MHC.StepsN.refl c⟩

/-! Move/operation application lemmas. -/

omit [Fintype Gamma] in
theorem apply_mvStay (pos : Fin (hN P) → ℕ) :
    (fun a => ((mvStay (P := P) a).apply (pos a))) = pos := rfl

omit [Fintype Gamma] in
theorem apply_mvOne (x : Fin (hN P)) (m : HeadMove) (pos : Fin (hN P) → ℕ) :
    (fun a => ((mvOne (P := P) x m) a).apply (pos a))
      = Function.update pos x (m.apply (pos x)) := by
  funext a
  rw [mvOne]
  by_cases h : a = x
  · subst h; rw [if_pos rfl, Function.update_self]
  · rw [if_neg h, Function.update_of_ne h]
    rfl

theorem apply_opsKeep (cnt : Fin 2 → ℕ) :
    (fun j => ((opsKeep j).apply (cnt j))) = cnt := rfl

theorem apply_opsInc (tgt : Bool) (cnt : Fin 2 → ℕ) :
    (fun j => ((opsInc tgt j).apply (cnt j)))
      = Function.update cnt (ctrIdx tgt) (cnt (ctrIdx tgt) + 1) := by
  funext j
  rw [opsInc]
  by_cases h : j = ctrIdx tgt
  · subst h; rw [if_pos rfl, Function.update_self]; rfl
  · rw [if_neg h, Function.update_of_ne h]; rfl

theorem apply_opsDec (tgt : Bool) (cnt : Fin 2 → ℕ) :
    (fun j => ((opsDec tgt j).apply (cnt j)))
      = Function.update cnt (ctrIdx tgt) (cnt (ctrIdx tgt) - 1) := by
  funext j
  rw [opsDec]
  by_cases h : j = ctrIdx tgt
  · subst h; rw [if_pos rfl, Function.update_self]; rfl
  · rw [if_neg h, Function.update_of_ne h]; rfl

theorem apply_opsDecBoth (cnt : Fin 2 → ℕ) :
    (fun j => ((opsDecBoth j).apply (cnt j))) = fun j => cnt j - 1 := rfl

/-! Counter pairs. -/

/-- The counter vector `(p, n)`. -/
def c2 (p n : ℕ) : Fin 2 → ℕ := fun j => if j.val = 0 then p else n

@[simp] theorem c2_zero (p n : ℕ) : c2 p n 0 = p := rfl
@[simp] theorem c2_one (p n : ℕ) : c2 p n 1 = n := rfl

theorem ctrIdx_true : ctrIdx true = (0 : Fin 2) := rfl
theorem ctrIdx_false : ctrIdx false = (1 : Fin 2) := rfl

theorem update_c2_zero (p n v : ℕ) : Function.update (c2 p n) (0 : Fin 2) v = c2 v n := by
  funext j
  by_cases h : j = (0 : Fin 2)
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h]
    have : j.val ≠ 0 := fun hc => h (Fin.ext hc)
    rw [c2, c2, if_neg this, if_neg this]

theorem update_c2_one (p n v : ℕ) : Function.update (c2 p n) (1 : Fin 2) v = c2 p v := by
  funext j
  by_cases h : j = (1 : Fin 2)
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h]
    have hj : j.val = 0 := by omega
    rw [c2, c2, if_pos hj, if_pos hj]

theorem c2_ext {cnt : Fin 2 → ℕ} : cnt = c2 (cnt 0) (cnt 1) := by
  funext j
  rcases j with ⟨(_ | _ | n), hj⟩
  · rfl
  · rfl
  · omega


/-! Rewind: walk the scan head home and dispatch. -/

theorem rawEta_rewind_lmark {κ : Cont P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P)}
    {b : Bool} {g : Glob P.toPoly.K} {reg : Reg E}
    {syms : Fin (hN P) → TapeSym Step} {coin : Fin (hN P) → Fin (hN P) → Bool}
    {zs : Fin 2 → Bool} (hs : syms scanH = TapeSym.lmark) :
    rawEta E (g, .rewind κ b, reg) syms coin zs
      = (contStep E κ b g).map fun r => ((r.1, r.2.1, reg), mvStay, opsKeep, r.2.2) := by
  simp only [rawEta]
  rw [hs]
  rfl

theorem rawEta_rewind_step {κ : Cont P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P)}
    {b : Bool} {g : Glob P.toPoly.K} {reg : Reg E}
    {syms : Fin (hN P) → TapeSym Step} {coin : Fin (hN P) → Fin (hN P) → Bool}
    {zs : Fin 2 → Bool} (hs : syms scanH ≠ TapeSym.lmark) :
    rawEta E (g, .rewind κ b, reg) syms coin zs
      = some ((g, .rewind κ b, reg), mvOne scanH .left, opsKeep, []) := by
  rcases hsym : syms scanH with _ | a | _
  · exact absurd hsym hs
  · simp only [rawEta, hsym]; rfl
  · simp only [rawEta, hsym]; rfl

theorem rewind_run {w : List Step}
    {κ : Cont P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P)} {b : Bool}
    {g g' : Glob P.toPoly.K} {t' : TagT E} {o : List Gamma} {reg : Reg E}
    (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) (p : ℕ)
    (hdisp : contStep E κ b g = some (g', t', o)) :
    (evalM E).Steps w ((g, .rewind κ b, reg), Function.update pos scanH p, cnt) o
      ((g', t', reg), Function.update pos scanH 0, cnt) := by
  induction p with
  | zero =>
      have hstep := stepRaw E (w := w)
        (pos := Function.update pos scanH 0) (cnt := cnt)
        (hraw := by
          rw [rawEta_rewind_lmark E (by rw [Function.update_self, tapeSym_zero]), hdisp]
          rfl)
        (hguard := by intro a hmv; cases hmv)
        (hpos₂ := apply_mvStay _)
        (hcnt₂ := apply_opsKeep _)
        (hrest := stepsRefl E ((g', t', reg), Function.update pos scanH 0, cnt))
      simpa using hstep
  | succ p ih =>
      have hstep := stepRaw E (w := w)
        (pos := Function.update pos scanH (p + 1)) (cnt := cnt)
        (hraw := rawEta_rewind_step E (by
          rw [Function.update_self]
          rw [Ne, tapeSym_eq_lmark_iff]
          omega))
        (hguard := by
          intro a hmv
          rw [mvOne] at hmv
          split at hmv <;> cases hmv)
        (hpos₂ := by
          rw [apply_mvOne, Function.update_self, Function.update_idem]
          rfl)
        (hcnt₂ := apply_opsKeep _)
        (hrest := ih)
      simpa using hstep


/-! Sweep-job η-computation lemmas. -/

theorem rawEta_sweep_lmark {J : JobId P.toPoly.K (Fintype.card Gamma)}
    {κ : Cont P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P)}
    {g : Glob P.toPoly.K} {reg : Reg E} {syms : Fin (hN P) → TapeSym Step}
    {coin : Fin (hN P) → Fin (hN P) → Bool} {zs : Fin 2 → Bool}
    (hs : syms scanH = TapeSym.lmark) :
    rawEta E (g, .sweep J κ, reg) syms coin zs
      = some ((g, .sweep J κ, Reg.job E ⟨J, (jobDFA E J).q0⟩),
          mvOne scanH .right, opsKeep, []) := by
  simp only [rawEta, hs]; rfl

theorem rawEta_sweep_letter {J : JobId P.toPoly.K (Fintype.card Gamma)}
    {κ : Cont P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P)}
    {g : Glob P.toPoly.K} {reg : Reg E} {syms : Fin (hN P) → TapeSym Step}
    {coin : Fin (hN P) → Fin (hN P) → Bool} {zs : Fin 2 → Bool} {a : Step}
    (hs : syms scanH = TapeSym.letter a) :
    rawEta E (g, .sweep J κ, reg) syms coin zs
      = (jobProj E J reg).map fun qj =>
          ((g, .sweep J κ, Reg.job E ⟨J, (jobDFA E J).δ qj
              (mkLetter (jobArity P J) a (fun i => coin scanH (jobHeads J i)))⟩),
            mvOne scanH .right, opsKeep, []) := by
  simp only [rawEta, hs]; rfl

theorem rawEta_sweep_rmark {J : JobId P.toPoly.K (Fintype.card Gamma)}
    {κ : Cont P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P)}
    {g : Glob P.toPoly.K} {reg : Reg E} {syms : Fin (hN P) → TapeSym Step}
    {coin : Fin (hN P) → Fin (hN P) → Bool} {zs : Fin 2 → Bool}
    (hs : syms scanH = TapeSym.rmark) :
    rawEta E (g, .sweep J κ, reg) syms coin zs
      = (jobProj E J reg).map fun qj =>
          ((g, .rewind κ (acceptB E J qj), reg), mvStay, opsKeep, []) := by
  simp only [rawEta, hs]; rfl

/-! Mark heads are never the scan head. -/

omit [Fintype Gamma] in
theorem sideHead_val_pos (π : CmpId) (s : Bool) (r : Fin (kmaxP P)) :
    0 < (sideHead (P := P) π s r).val := by
  rcases π <;> rcases s <;> simp [sideHead, curH, candH, bestH]

omit [Fintype Gamma] in
theorem scanH_val : (scanH (P := P)).val = 0 := rfl

theorem jobHeads_ne_scanH (J : JobId P.toPoly.K (Fintype.card Gamma))
    (i : Fin (jobArity P J)) : jobHeads J i ≠ scanH := by
  have hval : 0 < (jobHeads J i).val → jobHeads J i ≠ scanH := by
    intro h hc
    rw [hc, scanH_val] at h
    omega
  apply hval
  rcases J with _ | c | ⟨c, gg⟩ | ⟨π, cL, cR⟩
  · exact i.elim0
  · simp [jobHeads, candH]
  · simp [jobHeads, bestH]
  · refine Fin.addCases ?_ ?_ i
    · intro i'
      simp only [jobHeads, Fin.addCases_left]
      exact sideHead_val_pos π true (embedA i')
    · intro i'
      simp only [jobHeads, Fin.addCases_right]
      exact sideHead_val_pos π false (embedA i')

/-! The forward pass of a sweep. -/

theorem sweep_forward {w : List Step} {J : JobId P.toPoly.K (Fintype.card Gamma)}
    {κ : Cont P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P)}
    {g : Glob P.toPoly.K} {pos : Fin (hN P) → ℕ} {cnt : Fin 2 → ℕ}
    {ī : Fin (jobArity P J) → ℕ}
    (hmark : ∀ i, pos (jobHeads J i) = ī i + 1) :
    ∀ j, j ≤ w.length →
    (evalM E).Steps w
      ((g, .sweep J κ, Reg.job E ⟨J,
          ((markAtN (jobArity P J) w ī).take j).foldl (jobDFA E J).δ (jobDFA E J).q0⟩),
        Function.update pos scanH (j + 1), cnt) []
      ((g, .rewind κ (acceptB E J
          ((markAtN (jobArity P J) w ī).foldl (jobDFA E J).δ (jobDFA E J).q0)),
        Reg.job E ⟨J,
          (markAtN (jobArity P J) w ī).foldl (jobDFA E J).δ (jobDFA E J).q0⟩),
        Function.update pos scanH (w.length + 1), cnt) := by
  intro j
  set L := markAtN (jobArity P J) w ī with hL
  have hLlen : L.length = w.length := markAtN_length _ _ _
  intro hj
  induction hlen : w.length - j generalizing j with
  | zero =>
      have hjn : j = w.length := by omega
      subst hjn
      have htake : L.take w.length = L := by
        rw [← hLlen]
        exact List.take_length
      rw [htake]
      have hs : (fun a => tapeSym w ((Function.update pos scanH (w.length + 1)) a)) scanH
          = TapeSym.rmark := by
        show tapeSym w ((Function.update pos scanH (w.length + 1)) scanH) = TapeSym.rmark
        rw [Function.update_self]
        exact tapeSym_ge w (w.length + 1) (by omega)
      refine stepRaw E (u := []) (out := []) ?_ ?_ (apply_mvStay _) (apply_opsKeep _)
        (stepsRefl E _)
      · rw [rawEta_sweep_rmark E hs]
        simp only [jobProj_job_self, Option.map_some]
        rfl
      · intro a hmv
        cases hmv
  | succ m ih =>
      have hjlt : j < w.length := by omega
      have hjL : j < L.length := by omega
      have hcell : L[j]? = some (mkLetter (jobArity P J) w[j]
          (fun i => decide (j = ī i))) := markAtN_getElem? _ _ _ j hjlt
      have hLj : L[j] = mkLetter (jobArity P J) w[j] (fun i => decide (j = ī i)) := by
        rw [List.getElem?_eq_getElem hjL, Option.some.injEq] at hcell
        exact hcell
      have hs : (fun a => tapeSym w ((Function.update pos scanH (j + 1)) a)) scanH
          = TapeSym.letter w[j] := by
        show tapeSym w ((Function.update pos scanH (j + 1)) scanH) = TapeSym.letter w[j]
        rw [Function.update_self]
        exact tapeSym_succ w j hjlt
      have hmarks : (fun i => ((Function.update pos scanH (j + 1)) scanH
            == (Function.update pos scanH (j + 1)) (jobHeads J i)))
          = fun i => decide (j = ī i) := by
        funext i
        rw [Function.update_self,
          Function.update_of_ne (jobHeads_ne_scanH J i), hmark i]
        show ((j + 1 : ℕ) == ī i + 1) = decide (j = ī i)
        rw [show ((j + 1 : ℕ) == ī i + 1) = decide (j + 1 = ī i + 1) from rfl]
        rw [decide_eq_decide]
        omega
      have hnext' : (evalM E).Steps w
          ((g, .sweep J κ, Reg.job E ⟨J,
              (jobDFA E J).δ ((L.take j).foldl (jobDFA E J).δ (jobDFA E J).q0)
                (mkLetter (jobArity P J) w[j] (fun i =>
                  ((Function.update pos scanH (j + 1)) scanH
                    == (Function.update pos scanH (j + 1)) (jobHeads J i))))⟩),
            Function.update pos scanH (j + 1 + 1), cnt) []
          ((g, .rewind κ (acceptB E J (L.foldl (jobDFA E J).δ (jobDFA E J).q0)),
            Reg.job E ⟨J, L.foldl (jobDFA E J).δ (jobDFA E J).q0⟩),
            Function.update pos scanH (w.length + 1), cnt) := by
        have hfold : (jobDFA E J).δ ((L.take j).foldl (jobDFA E J).δ (jobDFA E J).q0)
              (mkLetter (jobArity P J) w[j] (fun i =>
                ((Function.update pos scanH (j + 1)) scanH
                  == (Function.update pos scanH (j + 1)) (jobHeads J i))))
            = (L.take (j + 1)).foldl (jobDFA E J).δ (jobDFA E J).q0 := by
          rw [hmarks, foldl_take_succ _ _ _ j hjL, hLj]
        rw [hfold]
        exact ih (j + 1) (by omega) (by omega)
      refine stepRaw E (u := []) (out := []) (mv := mvOne scanH .right) ?_ ?_ ?_
        (apply_opsKeep _) hnext'
      · rw [rawEta_sweep_letter E hs]
        simp only [jobProj_job_self, Option.map_some]
        rfl
      · intro a hmv
        simp only [mvOne] at hmv
        split at hmv
        · rename_i ha
          subst ha
          show tapeSym w ((Function.update pos scanH (j + 1)) scanH) ≠ TapeSym.rmark
          rw [Function.update_self, tapeSym_succ w j hjlt]
          intro hc
          cases hc
        · cases hmv
      · rw [apply_mvOne, Function.update_self, Function.update_idem]
        rfl


/-- **The sweep lemma**: from a checkpoint (scan parked at `⊢`) the machine
runs job `J`'s DFA over the marked word and dispatches on its acceptance,
restoring all head positions. -/
theorem sweep_run {w : List Step} (J : JobId P.toPoly.K (Fintype.card Gamma))
    (κ : Cont P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P))
    {g : Glob P.toPoly.K} (regin : Reg E) {pos : Fin (hN P) → ℕ} {cnt : Fin 2 → ℕ}
    (ī : Fin (jobArity P J) → ℕ) (hscan : pos scanH = 0)
    (hmark : ∀ i, pos (jobHeads J i) = ī i + 1) :
    ∃ (b : Bool) (regR : Reg E),
      (b = true ↔ (jobDFA E J).accepts (markAtN (jobArity P J) w ī)) ∧
      ∀ {g' : Glob P.toPoly.K} {t' : TagT E} {o : List Gamma},
        contStep E κ b g = some (g', t', o) →
        (evalM E).Steps w ((g, .sweep J κ, regin), pos, cnt) o ((g', t', regR), pos, cnt) := by
  set L := markAtN (jobArity P J) w ī with hL
  set qf := L.foldl (jobDFA E J).δ (jobDFA E J).q0 with hqf
  refine ⟨acceptB E J qf, Reg.job E ⟨J, qf⟩, ?_, ?_⟩
  · rw [acceptB_iff]
    rfl
  · intro g' t' o hdisp
    -- entry step: `⊢` under the scan head, reset the register, move right
    have hupdid : Function.update pos scanH 0 = pos := by
      rw [← hscan, Function.update_eq_self]
    have hentry : (evalM E).Steps w ((g, .sweep J κ, regin), pos, cnt) []
        ((g, .sweep J κ, Reg.job E ⟨J, (jobDFA E J).q0⟩),
          Function.update pos scanH 1, cnt) := by
      refine stepRaw E (u := []) (out := []) (mv := mvOne scanH .right) ?_ ?_ ?_
        (apply_opsKeep _) (stepsRefl E _)
      · rw [rawEta_sweep_lmark E (by
          show tapeSym w (pos scanH) = TapeSym.lmark
          rw [hscan]
          exact tapeSym_zero w)]
        rfl
      · intro a hmv
        simp only [mvOne] at hmv
        split at hmv
        · rename_i ha
          subst ha
          rw [hscan]
          intro hc
          rw [tapeSym_zero] at hc
          cases hc
        · cases hmv
      · rw [apply_mvOne, hscan]
        rfl
    -- forward pass from position 1 (prefix 0 processed)
    have hfwd := sweep_forward E (w := w) (κ := κ) (g := g) (cnt := cnt) hmark 0 (by omega)
    rw [← hL, ← hqf] at hfwd
    simp only [List.take_zero, List.foldl_nil] at hfwd
    -- rewind home and dispatch
    have hrew := rewind_run E (w := w) (κ := κ) (b := acceptB E J qf)
      (reg := Reg.job E ⟨J, qf⟩) pos cnt (w.length + 1) hdisp
    rw [hupdid] at hrew
    have hall := stepsTrans E hentry (stepsTrans E hfwd hrew)
    simpa using hall


/-! ## §9 The walk gadgets (park and copy) -/

/-! Walk gadgets: η-computation. -/

theorem rawEta_walk_done {wk : WalkId} {g : Glob P.toPoly.K} {reg : Reg E}
    {syms : Fin (hN P) → TapeSym Step} {coin : Fin (hN P) → Fin (hN P) → Bool}
    {zs : Fin 2 → Bool} (hdone : wkDone (P := P) wk syms coin) :
    rawEta E (g, .walk wk, reg) syms coin zs
      = (wkExit E wk g).map fun r => ((r.1, r.2, reg), mvStay, opsKeep, []) := by
  simp only [rawEta, walkEta, if_pos hdone]
  rfl

theorem rawEta_walk_step {wk : WalkId} {g : Glob P.toPoly.K} {reg : Reg E}
    {syms : Fin (hN P) → TapeSym Step} {coin : Fin (hN P) → Fin (hN P) → Bool}
    {zs : Fin 2 → Bool} (hdone : ¬ wkDone (P := P) wk syms coin) :
    rawEta E (g, .walk wk, reg) syms coin zs
      = some ((g, .walk wk, reg), walkMoves (P := P) wk syms coin, opsKeep, []) := by
  simp only [rawEta, walkEta, if_neg hdone]
  rfl

/-- **Park walk**: all block heads walk left to `⊢`, then the exit fires. -/
theorem walk_park_run (wk : WalkId) (hpark : wkPark wk = true) {w : List Step}
    {g g' : Glob P.toPoly.K} {t' : TagT E} {reg : Reg E} {cnt : Fin 2 → ℕ}
    (hexit : wkExit E wk g = some (g', t')) :
    ∀ (pos : Fin (hN P) → ℕ),
    (evalM E).Steps w ((g, .walk wk, reg), pos, cnt) []
      ((g', t', reg), (fun a => if wkIn (P := P) wk a.val then 0 else pos a), cnt) := by
  intro pos
  generalize hm : (∑ a : Fin (hN P), if wkIn (P := P) wk a.val then pos a else 0) = m
  induction m using Nat.strong_induction_on generalizing pos with
  | _ m ih =>
  by_cases hdone : ∀ a : Fin (hN P), wkIn (P := P) wk a.val → pos a = 0
  · -- all parked: dispatch
    have hdone' : wkDone (P := P) wk (fun a => tapeSym w (pos a))
        (fun a b => pos a == pos b) := by
      intro a ha
      rw [hpark, if_pos rfl]
      show tapeSym w (pos a) = TapeSym.lmark
      rw [hdone a ha]
      exact tapeSym_zero w
    have hposeq : (fun a => if wkIn (P := P) wk a.val then 0 else pos a) = pos := by
      funext a
      by_cases ha : wkIn (P := P) wk a.val
      · rw [if_pos ha, hdone a ha]
      · rw [if_neg ha]
    rw [hposeq]
    refine stepRaw E (u := []) (out := []) (mv := mvStay) ?_ ?_ (apply_mvStay _)
      (apply_opsKeep _) (stepsRefl E _)
    · rw [rawEta_walk_done E hdone', hexit]
      rfl
    · intro a hmv
      cases hmv
  · -- some block head is off `⊢`: simultaneous left step
    push Not at hdone
    obtain ⟨a0, ha0in, ha0ne⟩ := hdone
    have hndone : ¬ wkDone (P := P) wk (fun a => tapeSym w (pos a))
        (fun a b => pos a == pos b) := by
      intro hc
      have := hc a0 ha0in
      rw [hpark, if_pos rfl] at this
      have h0 : pos a0 = 0 := (tapeSym_eq_lmark_iff w (pos a0)).mp this
      exact ha0ne h0
    have hmv : (fun a => ((walkMoves (P := P) wk (fun a => tapeSym w (pos a))
          (fun a b => pos a == pos b) a).apply (pos a)))
        = fun a => if wkIn (P := P) wk a.val then pos a - 1 else pos a := by
      funext a
      show (walkMoves (P := P) wk _ _ a).apply (pos a) = _
      rw [walkMoves]
      by_cases ha : wkIn (P := P) wk a.val
      · rw [if_pos ha, if_pos ha, hpark, if_pos rfl]
        by_cases h0 : pos a = 0
        · rw [if_pos (show tapeSym w (pos a) = TapeSym.lmark by
            rw [h0]; exact tapeSym_zero w)]
          show pos a = pos a - 1
          omega
        · rw [if_neg (fun hc => h0 ((tapeSym_eq_lmark_iff w _).mp hc))]
          rfl
      · rw [if_neg ha, if_neg ha]
        rfl
    have hm2 : (∑ a : Fin (hN P), if wkIn (P := P) wk a.val
        then (if wkIn (P := P) wk a.val then pos a - 1 else pos a) else 0) < m := by
      rw [← hm]
      refine Finset.sum_lt_sum (fun a _ => ?_) ⟨a0, Finset.mem_univ a0, ?_⟩
      · by_cases ha : wkIn (P := P) wk a.val
        · rw [if_pos ha, if_pos ha, if_pos ha]
          omega
        · rw [if_neg ha, if_neg ha]
      · rw [if_pos ha0in, if_pos ha0in, if_pos ha0in]
        omega
    have hnext := ih _ hm2 (fun a => if wkIn (P := P) wk a.val then pos a - 1 else pos a) rfl
    have hfin : (fun a => if wkIn (P := P) wk a.val then 0
          else (if wkIn (P := P) wk a.val then pos a - 1 else pos a))
        = fun a => if wkIn (P := P) wk a.val then 0 else pos a := by
      funext a
      by_cases ha : wkIn (P := P) wk a.val
      · rw [if_pos ha, if_pos ha]
      · rw [if_neg ha, if_neg ha, if_neg ha]
    rw [hfin] at hnext
    refine stepRaw E (u := []) (out := [])
      (mv := walkMoves (P := P) wk (fun a => tapeSym w (pos a)) (fun a b => pos a == pos b))
      ?_ ?_ hmv (apply_opsKeep _) hnext
    · exact rawEta_walk_step E hndone
    · intro a hmvr
      rw [walkMoves] at hmvr
      by_cases ha : wkIn (P := P) wk a.val
      · rw [if_pos ha, hpark, if_pos rfl] at hmvr
        split at hmvr <;> cases hmvr
      · rw [if_neg ha] at hmvr
        cases hmvr


/-- **Copy walk**: all block heads walk right until they coincide with their
partner heads (which sit outside the block), then the exit fires. -/
theorem walk_copy_run (wk : WalkId) (hcopy : wkPark wk = false) {w : List Step}
    {g g' : Glob P.toPoly.K} {t' : TagT E} {reg : Reg E} {cnt : Fin 2 → ℕ}
    (hpnotin : ∀ a : Fin (hN P), wkIn (P := P) wk a.val →
      ¬ wkIn (P := P) wk (wkPartner (P := P) wk a).val)
    (hexit : wkExit E wk g = some (g', t')) :
    ∀ (pos : Fin (hN P) → ℕ),
    (∀ a, wkIn (P := P) wk a.val → pos a ≤ pos (wkPartner (P := P) wk a)) →
    (∀ a, wkIn (P := P) wk a.val → pos (wkPartner (P := P) wk a) ≤ w.length + 1) →
    (evalM E).Steps w ((g, .walk wk, reg), pos, cnt) []
      ((g', t', reg),
        (fun a => if wkIn (P := P) wk a.val then pos (wkPartner (P := P) wk a) else pos a),
        cnt) := by
  intro pos
  generalize hm : (∑ a : Fin (hN P),
    if wkIn (P := P) wk a.val then pos (wkPartner (P := P) wk a) - pos a else 0) = m
  induction m using Nat.strong_induction_on generalizing pos with
  | _ m ih =>
  intro hle hbound
  by_cases hdone : ∀ a : Fin (hN P), wkIn (P := P) wk a.val →
      pos a = pos (wkPartner (P := P) wk a)
  · have hdone' : wkDone (P := P) wk (fun a => tapeSym w (pos a))
        (fun a b => pos a == pos b) := by
      intro a ha
      rw [hcopy, if_neg (show ¬ (false = true) by simp), beq_iff_eq]
      exact hdone a ha
    have hposeq : (fun a => if wkIn (P := P) wk a.val
          then pos (wkPartner (P := P) wk a) else pos a) = pos := by
      funext a
      by_cases ha : wkIn (P := P) wk a.val
      · rw [if_pos ha, ← hdone a ha]
      · rw [if_neg ha]
    rw [hposeq]
    refine stepRaw E (u := []) (out := []) (mv := mvStay) ?_ ?_ (apply_mvStay _)
      (apply_opsKeep _) (stepsRefl E _)
    · rw [rawEta_walk_done E hdone', hexit]
      rfl
    · intro a hmv
      cases hmv
  · push Not at hdone
    obtain ⟨a0, ha0in, ha0ne⟩ := hdone
    have hndone : ¬ wkDone (P := P) wk (fun a => tapeSym w (pos a))
        (fun a b => pos a == pos b) := by
      intro hc
      have := hc a0 ha0in
      rw [hcopy, if_neg (show ¬ (false = true) by simp), beq_iff_eq] at this
      exact ha0ne this
    have hmv : (fun a => ((walkMoves (P := P) wk (fun a => tapeSym w (pos a))
          (fun a b => pos a == pos b) a).apply (pos a)))
        = fun a => if wkIn (P := P) wk a.val ∧ pos a ≠ pos (wkPartner (P := P) wk a)
            then pos a + 1 else pos a := by
      funext a
      show (walkMoves (P := P) wk _ _ a).apply (pos a) = _
      rw [walkMoves]
      by_cases ha : wkIn (P := P) wk a.val
      · rw [if_pos ha, hcopy, if_neg (show ¬ (false = true) by simp)]
        by_cases hco : pos a = pos (wkPartner (P := P) wk a)
        · rw [if_pos (by rw [beq_iff_eq]; exact hco),
            if_neg (fun hc => hc.2 hco)]
          rfl
        · rw [if_neg (by rw [beq_iff_eq]; exact hco),
            if_pos ⟨ha, hco⟩]
          rfl
      · rw [if_neg ha, if_neg (fun hc => ha hc.1)]
        rfl
    set pos₂ : Fin (hN P) → ℕ := fun a =>
      if wkIn (P := P) wk a.val ∧ pos a ≠ pos (wkPartner (P := P) wk a)
      then pos a + 1 else pos a with hpos₂
    have hpartner₂ : ∀ a, wkIn (P := P) wk a.val →
        pos₂ (wkPartner (P := P) wk a) = pos (wkPartner (P := P) wk a) := by
      intro a ha
      rw [hpos₂]
      show (if _ then _ else _) = _
      rw [if_neg (fun hc => hpnotin a ha hc.1)]
    have hle₂ : ∀ a, wkIn (P := P) wk a.val →
        pos₂ a ≤ pos₂ (wkPartner (P := P) wk a) := by
      intro a ha
      rw [hpartner₂ a ha, hpos₂]
      show (if _ then _ else _) ≤ _
      by_cases hco : pos a = pos (wkPartner (P := P) wk a)
      · rw [if_neg (fun hc => hc.2 hco)]
        exact hle a ha
      · rw [if_pos ⟨ha, hco⟩]
        have := hle a ha
        omega
    have hbound₂ : ∀ a, wkIn (P := P) wk a.val →
        pos₂ (wkPartner (P := P) wk a) ≤ w.length + 1 := by
      intro a ha
      rw [hpartner₂ a ha]
      exact hbound a ha
    have hm2 : (∑ a : Fin (hN P), if wkIn (P := P) wk a.val
        then pos₂ (wkPartner (P := P) wk a) - pos₂ a else 0) < m := by
      rw [← hm]
      refine Finset.sum_lt_sum (fun a _ => ?_) ⟨a0, Finset.mem_univ a0, ?_⟩
      · by_cases ha : wkIn (P := P) wk a.val
        · rw [if_pos ha, if_pos ha, hpartner₂ a ha, hpos₂]
          show pos (wkPartner (P := P) wk a) - (if _ then _ else _) ≤ _
          by_cases hco : pos a = pos (wkPartner (P := P) wk a)
          · rw [if_neg (fun hc => hc.2 hco)]
          · rw [if_pos ⟨ha, hco⟩]
            omega
        · rw [if_neg ha, if_neg ha]
      · rw [if_pos ha0in, if_pos ha0in, hpartner₂ a0 ha0in, hpos₂]
        show pos (wkPartner (P := P) wk a0) - (if _ then _ else _)
          < pos (wkPartner (P := P) wk a0) - pos a0
        rw [if_pos ⟨ha0in, ha0ne⟩]
        have := hle a0 ha0in
        omega
    have hnext := ih _ hm2 pos₂ rfl hle₂ hbound₂
    have hfin : (fun a => if wkIn (P := P) wk a.val
          then pos₂ (wkPartner (P := P) wk a) else pos₂ a)
        = fun a => if wkIn (P := P) wk a.val
            then pos (wkPartner (P := P) wk a) else pos a := by
      funext a
      by_cases ha : wkIn (P := P) wk a.val
      · rw [if_pos ha, if_pos ha, hpartner₂ a ha]
      · rw [if_neg ha, if_neg ha, hpos₂]
        show (if _ then _ else _) = pos a
        rw [if_neg (fun hc => ha hc.1)]
    rw [hfin] at hnext
    refine stepRaw E (u := []) (out := [])
      (mv := walkMoves (P := P) wk (fun a => tapeSym w (pos a)) (fun a b => pos a == pos b))
      ?_ ?_ hmv (apply_opsKeep _) hnext
    · exact rawEta_walk_step E hndone
    · intro a hmvr
      rw [walkMoves] at hmvr
      by_cases ha : wkIn (P := P) wk a.val
      · rw [if_pos ha, hcopy, if_neg (show ¬ (false = true) by simp)] at hmvr
        by_cases hco : (pos a == pos (wkPartner (P := P) wk a)) = true
        · rw [if_pos hco] at hmvr
          cases hmvr
        · rw [if_neg hco] at hmvr
          rw [beq_iff_eq] at hco
          have hlt : pos a < pos (wkPartner (P := P) wk a) := by
            have := hle a ha
            omega
          have := hbound a ha
          exact tapeSym_ne_rmark_of_le (by omega)
      · rw [if_neg ha] at hmvr
        cases hmvr



/-! ## §10 Compare phase I: payments and the rank-sweep unit

-/

/-! Fin-2 vector extensionality and evaluations. -/

theorem fun2_ext {M : Type*} {f g : Fin 2 → M} (h0 : f 0 = g 0) (h1 : f 1 = g 1) :
    f = g := by
  funext j
  rcases j with ⟨(_ | _ | jj), hj⟩
  · exact h0
  · exact h1
  · omega

theorem apply_opsInc_c2 (tgt : Bool) (a b : ℕ) :
    (fun j => ((opsInc tgt j).apply (c2 a b j)))
      = cond tgt (c2 (a + 1) b) (c2 a (b + 1)) := by
  cases tgt <;> exact fun2_ext rfl rfl

theorem apply_opsDec_c2 (tgt : Bool) (a b : ℕ) :
    (fun j => ((opsDec tgt j).apply (c2 a b j)))
      = cond tgt (c2 (a - 1) b) (c2 a (b - 1)) := by
  cases tgt <;> exact fun2_ext rfl rfl

theorem apply_opsDecBoth_c2 (a b : ℕ) :
    (fun j => ((opsDecBoth j).apply (c2 a b j))) = c2 (a - 1) (b - 1) :=
  fun2_ext rfl rfl

/-! η-equations on `cmp` tags. -/

theorem rawEta_cmp {π : CmpId} {cL cR : Fin P.toPoly.K} {i : Fin P.d}
    {st : CmpStage (kmaxP P) (Wb E)} {g : Glob P.toPoly.K} {reg : Reg E}
    {syms : Fin (hN P) → TapeSym Step} {coin : Fin (hN P) → Fin (hN P) → Bool}
    {zs : Fin 2 → Bool} :
    rawEta E (g, .cmp π cL cR i st, reg) syms coin zs
      = cmpEta E π cL cR i st g reg syms coin zs := by
  simp only [rawEta]

/-- One payment loop: count the target counter up by `v`. -/
theorem pay_run {w : List Step} (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d)
    (side : Bool) (r : Fin (kmaxP P)) (tgt ex : Bool) {g : Glob P.toPoly.K}
    {reg : Reg E} {pos : Fin (hN P) → ℕ} :
    ∀ (v : ℕ) (hv : v < Wb E + 1) (a b : ℕ),
    (evalM E).Steps w
      ((g, .cmp π cL cR i (.payU side r ⟨v, hv⟩ tgt ex), reg), pos, c2 a b) []
      ((g, .cmp π cL cR i (.payU side r ⟨0, Nat.succ_pos _⟩ tgt ex), reg), pos,
        cond tgt (c2 (a + v) b) (c2 a (b + v))) := by
  intro v
  induction v with
  | zero =>
      intro hv a b
      have h0 : cond tgt (c2 (a + 0) b) (c2 a (b + 0)) = c2 a b := by
        cases tgt <;> rfl
      rw [h0]
      exact stepsRefl E _
  | succ v ih =>
      intro hv a b
      have hv' : v < Wb E + 1 := by omega
      have hnext := ih hv' (cond tgt (a + 1) a) (cond tgt b (b + 1))
      have hgoalcnt : cond tgt (c2 (cond tgt (a + 1) a + v) (cond tgt b (b + 1)))
            (c2 (cond tgt (a + 1) a) (cond tgt b (b + 1) + v))
          = cond tgt (c2 (a + (v + 1)) b) (c2 a (b + (v + 1))) := by
        cases tgt
        · show c2 a (b + 1 + v) = c2 a (b + (v + 1))
          rw [show b + 1 + v = b + (v + 1) from by omega]
        · show c2 (a + 1 + v) b = c2 (a + (v + 1)) b
          rw [show a + 1 + v = a + (v + 1) from by omega]
      rw [hgoalcnt] at hnext
      refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsInc tgt) ?_ ?_
        (apply_mvStay _) ?_ hnext
      · rw [rawEta_cmp]
        show cmpEta E π cL cR i (.payU side r ⟨v + 1, hv⟩ tgt ex) g reg _ _ _ = _
        rw [cmpEta]
        rw [if_pos (show 0 < v + 1 by omega)]
        rfl
      · intro a' hmv
        cases hmv
      · rw [apply_opsInc_c2]
        cases tgt <;> rfl


/-- The `c0` payment loop. -/
theorem c0pay_run {w : List Step} (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d)
    (side tgt : Bool) {g : Glob P.toPoly.K} {reg : Reg E} {pos : Fin (hN P) → ℕ} :
    ∀ (v : ℕ) (hv : v < Wb E + 1) (a b : ℕ),
    (evalM E).Steps w
      ((g, .cmp π cL cR i (.c0pay side ⟨v, hv⟩ tgt), reg), pos, c2 a b) []
      ((g, .cmp π cL cR i (.c0pay side ⟨0, Nat.succ_pos _⟩ tgt), reg), pos,
        cond tgt (c2 (a + v) b) (c2 a (b + v))) := by
  intro v
  induction v with
  | zero =>
      intro hv a b
      have h0 : cond tgt (c2 (a + 0) b) (c2 a (b + 0)) = c2 a b := by
        cases tgt <;> rfl
      rw [h0]
      exact stepsRefl E _
  | succ v ih =>
      intro hv a b
      have hv' : v < Wb E + 1 := by omega
      have hnext := ih hv' (cond tgt (a + 1) a) (cond tgt b (b + 1))
      have hgoalcnt : cond tgt (c2 (cond tgt (a + 1) a + v) (cond tgt b (b + 1)))
            (c2 (cond tgt (a + 1) a) (cond tgt b (b + 1) + v))
          = cond tgt (c2 (a + (v + 1)) b) (c2 a (b + (v + 1))) := by
        cases tgt
        · show c2 a (b + 1 + v) = c2 a (b + (v + 1))
          rw [show b + 1 + v = b + (v + 1) from by omega]
        · show c2 (a + 1 + v) b = c2 (a + (v + 1)) b
          rw [show a + 1 + v = a + (v + 1) from by omega]
      rw [hgoalcnt] at hnext
      refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsInc tgt) ?_ ?_
        (apply_mvStay _) ?_ hnext
      · rw [rawEta_cmp]
        show cmpEta E π cL cR i (.c0pay side ⟨v + 1, hv⟩ tgt) g reg _ _ _ = _
        rw [cmpEta]
        rw [if_pos (show 0 < v + 1 by omega)]
        rfl
      · intro a' hmv
        cases hmv
      · rw [apply_opsInc_c2]
        cases tgt <;> rfl


/-! Pointwise contribution rewrites. -/

theorem ωAt_of_lt {D : ℕ} (A : RankSource Step D) {w : List Step} {j : ℕ}
    (hj : j < w.length) (i : Fin D) :
    ωAt A w i j = A.ω (A.stateBefore w j) w[j] i := by
  rw [ωAt, List.getElem?_eq_getElem hj]
  rfl

theorem βAt_of_lt {D k : ℕ} (κc : PrefixAdditiveRank Step D k) (r : Fin k)
    {w : List Step} {p : ℕ} (hp : p < w.length) (i : Fin D) :
    βAt κc r w i p = κc.β r ((κc.A r).stateBefore w p) w[p] i := by
  rw [βAt, List.getElem?_eq_getElem hp]
  rfl

omit [Fintype Gamma] in
theorem cond_pay_c2 (side : Bool) (v : ℤ) (a b : ℕ) :
    cond (tgtOf side v) (c2 (a + v.natAbs) b) (c2 a (b + v.natAbs))
      = c2 (a + payP side v) (b + payN side v) := by
  cases h : tgtOf side v
  · show c2 a (b + v.natAbs) = _
    rw [payP, payN, h]
    rfl
  · show c2 (a + v.natAbs) b = _
    rw [payP, payN, h]
    rfl

theorem stateBefore_zero {D : ℕ} (A : RankSource Step D) (w : List Step) :
    A.stateBefore w 0 = A.q0 := rfl

theorem stateBefore_succ {D : ℕ} (A : RankSource Step D) {w : List Step} {j : ℕ}
    (hj : j < w.length) :
    A.stateBefore w (j + 1) = A.δ (A.stateBefore w j) w[j] := by
  rw [RankSource.stateBefore, RankSource.stateBefore]
  rw [foldl_take_succ A.δ A.q0 w j hj]

omit [Fintype Gamma] in
theorem sideHead_ne_scanH (π : CmpId) (s : Bool) (r : Fin (kmaxP P)) :
    sideHead (P := P) π s r ≠ scanH := by
  intro hc
  have := sideHead_val_pos (P := P) π s r
  rw [hc, scanH_val] at this
  omega

/-- **One rank-sweep unit**: pay the `ω`-prefix and the `β`-correction of the
marked position into the counters, rewind, and move to the next unit. -/
theorem rankUnit_run {w : List Step} (π : CmpId) (cL cR : Fin P.toPoly.K)
    (i : Fin P.d) (side : Bool) (r : Fin (kmaxP P)) {cc : Fin P.toPoly.K}
    (hcc : (if side = true then cL else cR) = cc)
    (hcr : r.val < P.toPoly.arity cc) {g : Glob P.toPoly.K} (reg : Reg E)
    {pos : Fin (hN P) → ℕ} {p : ℕ} (hp : p < w.length)
    (hscan : pos scanH = 0)
    (hmk : pos (sideHead π side r) = p + 1) (a b : ℕ) :
    ∃ regF : Reg E,
    (evalM E).Steps w ((g, .cmp π cL cR i (.scanU side r), reg), pos, c2 a b) []
      ((g, nextUnitTag E π cL cR i side r, regF), pos,
        c2 (a + uPos E side cc ⟨r.val, hcr⟩ w i p)
           (b + uNeg E side cc ⟨r.val, hcr⟩ w i p)) := by
  subst hcc
  -- suffix payment sums
  set sP : ℕ → ℕ := fun j =>
    (∑ j' ∈ Finset.Ico j p, payP side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j'))
    + payP side (βAt (E.κ (if side = true then cL else cR)) ⟨r.val, hcr⟩ w i p) with hsP
  set sN : ℕ → ℕ := fun j =>
    (∑ j' ∈ Finset.Ico j p, payN side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j'))
    + payN side (βAt (E.κ (if side = true then cL else cR)) ⟨r.val, hcr⟩ w i p) with hsN
  -- the forward pass from checkpoint j
  have hfwd : ∀ j, j ≤ p → ∀ a' b' : ℕ,
      (evalM E).Steps w
        ((g, .cmp π cL cR i (.scanU side r), Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩,
            (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j⟩),
          Function.update pos scanH (j + 1), c2 a' b') []
        ((g, .rewind (.unitK π cL cR i side r) true,
            Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩, (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w p⟩),
          Function.update pos scanH (p + 1), c2 (a' + sP j) (b' + sN j)) := by
    intro j
    induction hlen : p - j generalizing j with
    | zero =>
        intro hj a' b'
        have hjp : j = p := by omega
        subst hjp
        have hs : tapeSym w (j + 1) = TapeSym.letter w[j] := tapeSym_succ w j hp
        have hstep1 : (evalM E).Steps w
            ((g, .cmp π cL cR i (.scanU side r), Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩,
                (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j⟩),
              Function.update pos scanH (j + 1), c2 a' b') []
            ((g, .cmp π cL cR i (.payU side r
                ⟨((E.κ (if side = true then cL else cR)).β ⟨r.val, hcr⟩ ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i).natAbs,
                  Nat.lt_succ_of_le (β_le_Wb E (if side = true then cL else cR) ⟨r.val, hcr⟩ _ w[j] i)⟩
                (tgtOf side ((E.κ (if side = true then cL else cR)).β ⟨r.val, hcr⟩
                  ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i)) true),
              Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩, (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j⟩),
              Function.update pos scanH (j + 1), c2 a' b') := by
          refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
            (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
          · rw [rawEta_cmp]
            show cmpEta E π cL cR i (.scanU side r) g _ _ _ _ = _
            rw [cmpEta, dif_pos hcr]
            simp only [Function.update_self, hs, rankProj_rank_self,
              Function.update_of_ne (sideHead_ne_scanH π side r), hmk]
            simp only [if_pos (show ((j + 1 : ℕ) == j + 1) = true from by rw [beq_iff_eq])]
            rfl
          · intro a0 hmv
            cases hmv
        have hstep2 := pay_run E (w := w) π cL cR i side r
          (tgtOf side ((E.κ (if side = true then cL else cR)).β ⟨r.val, hcr⟩
            ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i)) true
          (g := g)
          (reg := Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩, (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j⟩)
          (pos := Function.update pos scanH (j + 1))
          ((E.κ (if side = true then cL else cR)).β ⟨r.val, hcr⟩ ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i).natAbs
          (Nat.lt_succ_of_le (β_le_Wb E (if side = true then cL else cR) ⟨r.val, hcr⟩ _ w[j] i)) a' b'
        have hstep3 : (evalM E).Steps w
            ((g, .cmp π cL cR i (.payU side r ⟨0, Nat.succ_pos _⟩
                (tgtOf side ((E.κ (if side = true then cL else cR)).β ⟨r.val, hcr⟩
                  ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i)) true),
              Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩, (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j⟩),
              Function.update pos scanH (j + 1), c2 (a' + sP j) (b' + sN j)) []
            ((g, .rewind (.unitK π cL cR i side r) true,
              Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩, (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j⟩),
              Function.update pos scanH (j + 1), c2 (a' + sP j) (b' + sN j)) := by
          refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
            (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
          · rw [rawEta_cmp]
            show cmpEta E π cL cR i (.payU side r _ _ true) g _ _ _ _ = _
            rw [cmpEta]
            rw [if_neg (show ¬ (0 < (0 : ℕ)) by omega), if_pos rfl]
          · intro a0 hmv
            cases hmv
        have hcnt : cond (tgtOf side ((E.κ (if side = true then cL else cR)).β ⟨r.val, hcr⟩
              ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i))
              (c2 (a' + ((E.κ (if side = true then cL else cR)).β ⟨r.val, hcr⟩
                ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i).natAbs) b')
              (c2 a' (b' + ((E.κ (if side = true then cL else cR)).β ⟨r.val, hcr⟩
                ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i).natAbs))
            = c2 (a' + sP j) (b' + sN j) := by
          rw [cond_pay_c2]
          simp only [hsP, hsN]
          rw [show (∑ j' ∈ Finset.Ico j j,
              payP side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j')) = 0 from by simp]
          rw [show (∑ j' ∈ Finset.Ico j j,
              payN side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j')) = 0 from by simp]
          rw [βAt_of_lt (E.κ (if side = true then cL else cR)) ⟨r.val, hcr⟩ hp i]
          rw [Nat.zero_add, Nat.zero_add]
          rfl
        rw [hcnt] at hstep2
        have hcomp := stepsTrans E hstep1 (stepsTrans E hstep2 hstep3)
        simpa using hcomp
    | succ m ih =>
        intro hj a' b'
        have hjp : j < p := by omega
        have hjw : j < w.length := by omega
        have hs : tapeSym w (j + 1) = TapeSym.letter w[j] := tapeSym_succ w j hjw
        have hstep1 : (evalM E).Steps w
            ((g, .cmp π cL cR i (.scanU side r), Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩,
                (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j⟩),
              Function.update pos scanH (j + 1), c2 a' b') []
            ((g, .cmp π cL cR i (.payU side r
                ⟨((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).ω
                    ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i).natAbs,
                  Nat.lt_succ_of_le (ω_le_Wb E (if side = true then cL else cR) ⟨r.val, hcr⟩ _ w[j] i)⟩
                (tgtOf side ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).ω
                  ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i)) false),
              Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩, (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).δ
                ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j]⟩),
              Function.update pos scanH (j + 1), c2 a' b') := by
          refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
            (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
          · rw [rawEta_cmp]
            show cmpEta E π cL cR i (.scanU side r) g _ _ _ _ = _
            rw [cmpEta, dif_pos hcr]
            simp only [Function.update_self, hs, rankProj_rank_self,
              Function.update_of_ne (sideHead_ne_scanH π side r), hmk]
            simp only [show ((j + 1 : ℕ) == p + 1) = false from by
              rw [beq_eq_false_iff_ne]
              omega]
            simp only [if_neg (show ¬ (false = true) by simp)]
            rfl
          · intro a0 hmv
            cases hmv
        have hstep2 := pay_run E (w := w) π cL cR i side r
          (tgtOf side ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).ω
            ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i)) false
          (g := g)
          (reg := Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩, (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).δ
            ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j]⟩)
          (pos := Function.update pos scanH (j + 1))
          ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).ω
            ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i).natAbs
          (Nat.lt_succ_of_le (ω_le_Wb E (if side = true then cL else cR) ⟨r.val, hcr⟩ _ w[j] i)) a' b'
        have hstep3 : (evalM E).Steps w
            ((g, .cmp π cL cR i (.payU side r ⟨0, Nat.succ_pos _⟩
                (tgtOf side ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).ω
                  ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i)) false),
              Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩, (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).δ
                ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j]⟩),
              Function.update pos scanH (j + 1),
              c2 (a' + payP side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j))
                 (b' + payN side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j))) []
            ((g, .cmp π cL cR i (.scanU side r),
              Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩,
                (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w (j + 1)⟩),
              Function.update pos scanH (j + 1 + 1),
              c2 (a' + payP side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j))
                 (b' + payN side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j))) := by
          refine stepRaw E (u := []) (out := []) (mv := mvOne scanH .right)
            (ops := opsKeep) ?_ ?_ ?_ (apply_opsKeep _) (stepsRefl E _)
          · rw [rawEta_cmp]
            show cmpEta E π cL cR i (.payU side r _ _ false) g _ _ _ _ = _
            rw [cmpEta]
            rw [if_neg (show ¬ (0 < (0 : ℕ)) by omega),
              if_neg (show ¬ (false = true) by simp)]
            rw [stateBefore_succ (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) hjw]
          · intro a0 hmv
            simp only [mvOne] at hmv
            split at hmv
            · rename_i ha0
              subst ha0
              show tapeSym w ((Function.update pos scanH (j + 1)) scanH) ≠ TapeSym.rmark
              rw [Function.update_self, tapeSym_succ w j hjw]
              intro hc
              cases hc
            · cases hmv
          · rw [apply_mvOne, Function.update_self, Function.update_idem]
            rfl
        have hcnt : cond (tgtOf side ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).ω
              ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i))
              (c2 (a' + ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).ω
                ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i).natAbs) b')
              (c2 a' (b' + ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).ω
                ((rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w j) w[j] i).natAbs))
            = c2 (a' + payP side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j))
                 (b' + payN side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j)) := by
          rw [cond_pay_c2]
          rw [ωAt_of_lt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) hjw i]
        have hnext := ih (j + 1) (by omega) (by omega)
          (a' + payP side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j))
          (b' + payN side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j))
        have hsum : c2 (a' + payP side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j) + sP (j + 1))
              (b' + payN side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j) + sN (j + 1))
            = c2 (a' + sP j) (b' + sN j) := by
          simp only [hsP, hsN]
          rw [Finset.sum_eq_sum_Ico_succ_bot hjp
            (fun j' => payP side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j'))]
          rw [Finset.sum_eq_sum_Ico_succ_bot hjp
            (fun j' => payN side (ωAt (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩) w i j'))]
          congr 1
          · omega
          · omega
        rw [hcnt] at hstep2
        have hall := stepsTrans E hstep1 (stepsTrans E hstep2
          (stepsTrans E hstep3 hnext))
        rw [hsum] at hall
        simpa using hall
  -- entry step: reset the rank register, move the scan head onto the word
  have hentry : (evalM E).Steps w
      ((g, .cmp π cL cR i (.scanU side r), reg), pos, c2 a b) []
      ((g, .cmp π cL cR i (.scanU side r),
        Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩, (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).q0⟩),
        Function.update pos scanH 1, c2 a b) := by
    refine stepRaw E (u := []) (out := []) (mv := mvOne scanH .right)
      (ops := opsKeep) ?_ ?_ ?_ (apply_opsKeep _) (stepsRefl E _)
    · rw [rawEta_cmp]
      show cmpEta E π cL cR i (.scanU side r) g _ _ _ _ = _
      rw [cmpEta, dif_pos hcr]
      simp only [show tapeSym w (pos scanH) = TapeSym.lmark from by
        rw [hscan]
        exact tapeSym_zero w]
    · intro a0 hmv
      simp only [mvOne] at hmv
      split at hmv
      · rename_i ha0
        subst ha0
        rw [hscan]
        intro hc
        rw [tapeSym_zero] at hc
        cases hc
      · cases hmv
    · rw [apply_mvOne, hscan]
      rfl
  have hfwd0 := hfwd 0 (by omega) a b
  have hrew := rewind_run E (w := w) (κ := .unitK π cL cR i side r) (b := true)
    (g := g) (reg := Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩,
      (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w p⟩) pos
    (c2 (a + sP 0) (b + sN 0)) (p + 1)
    (show contStep E (.unitK π cL cR i side r) true g
      = some (g, nextUnitTag E π cL cR i side r, []) from rfl)
  rw [show Function.update pos scanH 0 = pos from by
    rw [← hscan, Function.update_eq_self]] at hrew
  refine ⟨Reg.rank E ⟨⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩, (rsrc E ⟨(if side = true then cL else cR), ⟨r.val, hcr⟩⟩).stateBefore w p⟩, ?_⟩
  have huP : uPos E side (if side = true then cL else cR) ⟨r.val, hcr⟩ w i p = sP 0 := by
    rw [uPos]
    simp only [hsP]
    rw [Finset.range_eq_Ico]
    rfl
  have huN : uNeg E side (if side = true then cL else cR) ⟨r.val, hcr⟩ w i p = sN 0 := by
    rw [uNeg]
    simp only [hsN]
    rw [Finset.range_eq_Ico]
    rfl
  rw [huP, huN]
  have hall := stepsTrans E hentry (stepsTrans E hfwd0 hrew)
  simpa using hall


/-! ## §11 Compare phase II: the unit loops and one whole dimension -/

/-! Unit-loop tags. -/

/-- The tag at the start of right-side unit `r0` (drain when past the arity). -/
def unitTagR (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d) (r0 : ℕ) : TagT E :=
  if h : r0 < P.toPoly.arity cR then
    .cmp π cL cR i (.scanU false ⟨r0, lt_of_lt_of_le h (arity_le_kmax cR)⟩)
  else .cmp π cL cR i .drain

/-- The tag at the start of left-side unit `r0` (move to the right side when
past the arity). -/
def unitTagL (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d) (r0 : ℕ) : TagT E :=
  if h : r0 < P.toPoly.arity cL then
    .cmp π cL cR i (.scanU true ⟨r0, lt_of_lt_of_le h (arity_le_kmax cL)⟩)
  else unitTagR E π cL cR i 0

theorem firstRTag_eq (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d) :
    firstRTag E π cL cR i = unitTagR E π cL cR i 0 := rfl

theorem firstUnitTag_eq (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d) :
    firstUnitTag E π cL cR i = unitTagL E π cL cR i 0 := rfl

theorem nextUnitTag_false (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d)
    (r : Fin (kmaxP P)) :
    nextUnitTag E π cL cR i false r = unitTagR E π cL cR i (r.val + 1) := rfl

theorem nextUnitTag_true (π : CmpId) (cL cR : Fin P.toPoly.K) (i : Fin P.d)
    (r : Fin (kmaxP P)) :
    nextUnitTag E π cL cR i true r = unitTagL E π cL cR i (r.val + 1) := rfl

/-- ℕ-indexed unit payment (0 outside the arity). -/
def uPosN (side : Bool) (c : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c) → ℕ)
    (w : List Step) (i : Fin P.d) (r0 : ℕ) : ℕ :=
  if h : r0 < P.toPoly.arity c then uPos E side c ⟨r0, h⟩ w i (t ⟨r0, h⟩) else 0

def uNegN (side : Bool) (c : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c) → ℕ)
    (w : List Step) (i : Fin P.d) (r0 : ℕ) : ℕ :=
  if h : r0 < P.toPoly.arity c then uNeg E side c ⟨r0, h⟩ w i (t ⟨r0, h⟩) else 0

/-- **The right-side unit loop**: accumulate all remaining right units. -/
theorem unitsR_run {w : List Step} (π : CmpId) (cL cR : Fin P.toPoly.K)
    (i : Fin P.d) {g : Glob P.toPoly.K} {pos : Fin (hN P) → ℕ}
    (tR : Fin (P.toPoly.arity cR) → ℕ) (hvR : ∀ rr, tR rr < w.length)
    (hmkR : ∀ rr : Fin (P.toPoly.arity cR),
      pos (sideHead π false (embedA rr)) = tR rr + 1)
    (hscan : pos scanH = 0) :
    ∀ (r0 : ℕ) (reg : Reg E) (a b : ℕ),
    ∃ regF : Reg E,
    (evalM E).Steps w ((g, unitTagR E π cL cR i r0, reg), pos, c2 a b) []
      ((g, .cmp π cL cR i .drain, regF), pos,
        c2 (a + ∑ r' ∈ Finset.Ico r0 (P.toPoly.arity cR), uPosN E false cR tR w i r')
           (b + ∑ r' ∈ Finset.Ico r0 (P.toPoly.arity cR), uNegN E false cR tR w i r')) := by
  intro r0
  induction hm : P.toPoly.arity cR - r0 generalizing r0 with
  | zero =>
      intro reg a b
      have hge : P.toPoly.arity cR ≤ r0 := by omega
      refine ⟨reg, ?_⟩
      rw [show Finset.Ico r0 (P.toPoly.arity cR) = ∅ from Finset.Ico_eq_empty (by omega)]
      rw [Finset.sum_empty, Finset.sum_empty]
      rw [unitTagR, dif_neg (by omega)]
      exact stepsRefl E _
  | succ m ih =>
      intro reg a b
      have hlt : r0 < P.toPoly.arity cR := by omega
      have hcc : (if false = true then cL else cR) = cR := rfl
      obtain ⟨regF1, hunit⟩ := rankUnit_run E (w := w) π cL cR i false
        ⟨r0, lt_of_lt_of_le hlt (arity_le_kmax cR)⟩ hcc hlt
        (reg := reg) (pos := pos) (p := tR ⟨r0, hlt⟩) (hvR ⟨r0, hlt⟩) hscan
        (hmkR ⟨r0, hlt⟩) a b
      rw [nextUnitTag_false] at hunit
      obtain ⟨regF, hrest⟩ := ih (r0 + 1) (by omega) regF1
        (a + uPos E false cR ⟨r0, hlt⟩ w i (tR ⟨r0, hlt⟩))
        (b + uNeg E false cR ⟨r0, hlt⟩ w i (tR ⟨r0, hlt⟩))
      refine ⟨regF, ?_⟩
      have hsum : ∀ (x : ℕ) (f : ℕ → ℕ),
          x + f r0 + ∑ r' ∈ Finset.Ico (r0 + 1) (P.toPoly.arity cR), f r'
            = x + ∑ r' ∈ Finset.Ico r0 (P.toPoly.arity cR), f r' := by
        intro x f
        rw [Finset.sum_eq_sum_Ico_succ_bot hlt f]
        omega
      have hstart : (evalM E).Steps w ((g, unitTagR E π cL cR i r0, reg), pos, c2 a b)
          [] ((g, .cmp π cL cR i .drain, regF), pos,
            c2 (a + uPos E false cR ⟨r0, hlt⟩ w i (tR ⟨r0, hlt⟩)
                + ∑ r' ∈ Finset.Ico (r0 + 1) (P.toPoly.arity cR), uPosN E false cR tR w i r')
               (b + uNeg E false cR ⟨r0, hlt⟩ w i (tR ⟨r0, hlt⟩)
                + ∑ r' ∈ Finset.Ico (r0 + 1) (P.toPoly.arity cR), uNegN E false cR tR w i r')) := by
        rw [unitTagR, dif_pos hlt]
        have hcomp := stepsTrans E hunit hrest
        simpa using hcomp
      have heq1 : a + uPos E false cR ⟨r0, hlt⟩ w i (tR ⟨r0, hlt⟩)
            + ∑ r' ∈ Finset.Ico (r0 + 1) (P.toPoly.arity cR), uPosN E false cR tR w i r'
          = a + ∑ r' ∈ Finset.Ico r0 (P.toPoly.arity cR), uPosN E false cR tR w i r' := by
        have := hsum a (uPosN E false cR tR w i)
        rw [show uPosN E false cR tR w i r0
          = uPos E false cR ⟨r0, hlt⟩ w i (tR ⟨r0, hlt⟩) from by
            rw [uPosN, dif_pos hlt]] at this
        exact this
      have heq2 : b + uNeg E false cR ⟨r0, hlt⟩ w i (tR ⟨r0, hlt⟩)
            + ∑ r' ∈ Finset.Ico (r0 + 1) (P.toPoly.arity cR), uNegN E false cR tR w i r'
          = b + ∑ r' ∈ Finset.Ico r0 (P.toPoly.arity cR), uNegN E false cR tR w i r' := by
        have := hsum b (uNegN E false cR tR w i)
        rw [show uNegN E false cR tR w i r0
          = uNeg E false cR ⟨r0, hlt⟩ w i (tR ⟨r0, hlt⟩) from by
            rw [uNegN, dif_pos hlt]] at this
        exact this
      rw [heq1, heq2] at hstart
      exact hstart

/-- **The left-side unit loop**: accumulate all remaining left units, landing
at the start of the right-side loop. -/
theorem unitsL_run {w : List Step} (pi : CmpId) (cL cR : Fin P.toPoly.K)
    (i : Fin P.d) {g : Glob P.toPoly.K} {pos : Fin (hN P) → ℕ}
    (tL : Fin (P.toPoly.arity cL) → ℕ) (hvL : ∀ rr, tL rr < w.length)
    (hmkL : ∀ rr : Fin (P.toPoly.arity cL),
      pos (sideHead pi true (embedA rr)) = tL rr + 1)
    (hscan : pos scanH = 0) :
    ∀ (r0 : ℕ) (reg : Reg E) (a b : ℕ),
    ∃ regF : Reg E,
    (evalM E).Steps w ((g, unitTagL E pi cL cR i r0, reg), pos, c2 a b) []
      ((g, unitTagR E pi cL cR i 0, regF), pos,
        c2 (a + ∑ r' ∈ Finset.Ico r0 (P.toPoly.arity cL), uPosN E true cL tL w i r')
           (b + ∑ r' ∈ Finset.Ico r0 (P.toPoly.arity cL), uNegN E true cL tL w i r')) := by
  intro r0
  induction hm : P.toPoly.arity cL - r0 generalizing r0 with
  | zero =>
      intro reg a b
      refine ⟨reg, ?_⟩
      rw [show Finset.Ico r0 (P.toPoly.arity cL) = ∅ from Finset.Ico_eq_empty (by omega)]
      rw [Finset.sum_empty, Finset.sum_empty]
      rw [unitTagL, dif_neg (by omega)]
      exact stepsRefl E _
  | succ m ih =>
      intro reg a b
      have hlt : r0 < P.toPoly.arity cL := by omega
      have hcc : (if true = true then cL else cR) = cL := rfl
      obtain ⟨regF1, hunit⟩ := rankUnit_run E (w := w) pi cL cR i true
        ⟨r0, lt_of_lt_of_le hlt (arity_le_kmax cL)⟩ hcc hlt
        (reg := reg) (pos := pos) (p := tL ⟨r0, hlt⟩) (hvL ⟨r0, hlt⟩) hscan
        (hmkL ⟨r0, hlt⟩) a b
      rw [nextUnitTag_true] at hunit
      obtain ⟨regF, hrest⟩ := ih (r0 + 1) (by omega) regF1
        (a + uPos E true cL ⟨r0, hlt⟩ w i (tL ⟨r0, hlt⟩))
        (b + uNeg E true cL ⟨r0, hlt⟩ w i (tL ⟨r0, hlt⟩))
      refine ⟨regF, ?_⟩
      have hsum : ∀ (x : ℕ) (f : ℕ → ℕ),
          x + f r0 + ∑ r' ∈ Finset.Ico (r0 + 1) (P.toPoly.arity cL), f r'
            = x + ∑ r' ∈ Finset.Ico r0 (P.toPoly.arity cL), f r' := by
        intro x f
        rw [Finset.sum_eq_sum_Ico_succ_bot hlt f]
        omega
      have hstart : (evalM E).Steps w ((g, unitTagL E pi cL cR i r0, reg), pos, c2 a b)
          [] ((g, unitTagR E pi cL cR i 0, regF), pos,
            c2 (a + uPos E true cL ⟨r0, hlt⟩ w i (tL ⟨r0, hlt⟩)
                + ∑ r' ∈ Finset.Ico (r0 + 1) (P.toPoly.arity cL), uPosN E true cL tL w i r')
               (b + uNeg E true cL ⟨r0, hlt⟩ w i (tL ⟨r0, hlt⟩)
                + ∑ r' ∈ Finset.Ico (r0 + 1) (P.toPoly.arity cL), uNegN E true cL tL w i r')) := by
        rw [unitTagL, dif_pos hlt]
        have hcomp := stepsTrans E hunit hrest
        simpa using hcomp
      have heq1 : a + uPos E true cL ⟨r0, hlt⟩ w i (tL ⟨r0, hlt⟩)
            + ∑ r' ∈ Finset.Ico (r0 + 1) (P.toPoly.arity cL), uPosN E true cL tL w i r'
          = a + ∑ r' ∈ Finset.Ico r0 (P.toPoly.arity cL), uPosN E true cL tL w i r' := by
        have := hsum a (uPosN E true cL tL w i)
        rw [show uPosN E true cL tL w i r0
          = uPos E true cL ⟨r0, hlt⟩ w i (tL ⟨r0, hlt⟩) from by
            rw [uPosN, dif_pos hlt]] at this
        exact this
      have heq2 : b + uNeg E true cL ⟨r0, hlt⟩ w i (tL ⟨r0, hlt⟩)
            + ∑ r' ∈ Finset.Ico (r0 + 1) (P.toPoly.arity cL), uNegN E true cL tL w i r'
          = b + ∑ r' ∈ Finset.Ico r0 (P.toPoly.arity cL), uNegN E true cL tL w i r' := by
        have := hsum b (uNegN E true cL tL w i)
        rw [show uNegN E true cL tL w i r0
          = uNeg E true cL ⟨r0, hlt⟩ w i (tL ⟨r0, hlt⟩) from by
            rw [uNegN, dif_pos hlt]] at this
        exact this
      rw [heq1, heq2] at hstart
      exact hstart

omit [Fintype Gamma] in
/-- Reindex an ℕ-truncated unit-sum as a `Fin`-sum. -/
theorem sum_uPosN (side : Bool) (c : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c) → ℕ)
    (w : List Step) (i : Fin P.d) :
    ∑ r' ∈ Finset.Ico 0 (P.toPoly.arity c), uPosN E side c t w i r'
      = ∑ rr : Fin (P.toPoly.arity c), uPos E side c rr w i (t rr) := by
  rw [← Finset.range_eq_Ico]
  rw [Finset.sum_range fun r' => uPosN E side c t w i r']
  refine Finset.sum_congr rfl fun rr _ => ?_
  rw [uPosN, dif_pos rr.2]

omit [Fintype Gamma] in
theorem sum_uNegN (side : Bool) (c : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c) → ℕ)
    (w : List Step) (i : Fin P.d) :
    ∑ r' ∈ Finset.Ico 0 (P.toPoly.arity c), uNegN E side c t w i r'
      = ∑ rr : Fin (P.toPoly.arity c), uNeg E side c rr w i (t rr) := by
  rw [← Finset.range_eq_Ico]
  rw [Finset.sum_range fun r' => uNegN E side c t w i r']
  refine Finset.sum_congr rfl fun rr _ => ?_
  rw [uNegN, dif_pos rr.2]

/-- One whole dimension: the two `c0` payments and both unit loops, ending at
the drain with the dimension's payment totals. -/
theorem dim_run {w : List Step} (pi : CmpId) (cL cR : Fin P.toPoly.K)
    (i : Fin P.d) {g : Glob P.toPoly.K} {pos : Fin (hN P) → ℕ}
    (tL : Fin (P.toPoly.arity cL) → ℕ) (tR : Fin (P.toPoly.arity cR) → ℕ)
    (hvL : ∀ rr, tL rr < w.length) (hvR : ∀ rr, tR rr < w.length)
    (hmkL : ∀ rr : Fin (P.toPoly.arity cL),
      pos (sideHead pi true (embedA rr)) = tL rr + 1)
    (hmkR : ∀ rr : Fin (P.toPoly.arity cR),
      pos (sideHead pi false (embedA rr)) = tR rr + 1)
    (hscan : pos scanH = 0) (reg : Reg E) :
    ∃ regF : Reg E,
    (evalM E).Steps w ((g, .cmp pi cL cR i (.c0load true), reg), pos, c2 0 0) []
      ((g, .cmp pi cL cR i .drain, regF), pos,
        c2 (dimPos E cL tL cR tR w i) (dimNeg E cL tL cR tR w i)) := by
  have hstep1 : (evalM E).Steps w
      ((g, .cmp pi cL cR i (.c0load true), reg), pos, c2 0 0) []
      ((g, .cmp pi cL cR i (.c0pay true
          ⟨((E.κ cL).c0 i).natAbs, Nat.lt_succ_of_le (c0_le_Wb E cL i)⟩
          (tgtOf true ((E.κ cL).c0 i))), reg), pos, c2 0 0) := by
    refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
      (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
    · rw [rawEta_cmp]
      show cmpEta E pi cL cR i (.c0load true) g _ _ _ _ = _
      rw [cmpEta]
      rfl
    · intro a0 hmv
      cases hmv
  have hstep2 := c0pay_run E (w := w) pi cL cR i true (tgtOf true ((E.κ cL).c0 i))
    (g := g) (reg := reg) (pos := pos) ((E.κ cL).c0 i).natAbs
    (Nat.lt_succ_of_le (c0_le_Wb E cL i)) 0 0
  have hc2L : cond (tgtOf true ((E.κ cL).c0 i))
        (c2 (0 + ((E.κ cL).c0 i).natAbs) 0) (c2 0 (0 + ((E.κ cL).c0 i).natAbs))
      = c2 (payP true ((E.κ cL).c0 i)) (payN true ((E.κ cL).c0 i)) := by
    have := cond_pay_c2 true ((E.κ cL).c0 i) 0 0
    rw [this]
    rw [Nat.zero_add, Nat.zero_add]
  rw [hc2L] at hstep2
  have hstep3 : (evalM E).Steps w
      ((g, .cmp pi cL cR i (.c0pay true ⟨0, Nat.succ_pos _⟩
          (tgtOf true ((E.κ cL).c0 i))), reg), pos,
        c2 (payP true ((E.κ cL).c0 i)) (payN true ((E.κ cL).c0 i))) []
      ((g, .cmp pi cL cR i (.c0load false), reg), pos,
        c2 (payP true ((E.κ cL).c0 i)) (payN true ((E.κ cL).c0 i))) := by
    refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
      (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
    · rw [rawEta_cmp]
      show cmpEta E pi cL cR i (.c0pay true _ _) g _ _ _ _ = _
      rw [cmpEta]
      rw [if_neg (show ¬ (0 < (0 : ℕ)) by omega), if_pos rfl]
    · intro a0 hmv
      cases hmv
  have hstep4 : (evalM E).Steps w
      ((g, .cmp pi cL cR i (.c0load false), reg), pos,
        c2 (payP true ((E.κ cL).c0 i)) (payN true ((E.κ cL).c0 i))) []
      ((g, .cmp pi cL cR i (.c0pay false
          ⟨((E.κ cR).c0 i).natAbs, Nat.lt_succ_of_le (c0_le_Wb E cR i)⟩
          (tgtOf false ((E.κ cR).c0 i))), reg), pos,
        c2 (payP true ((E.κ cL).c0 i)) (payN true ((E.κ cL).c0 i))) := by
    refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
      (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
    · rw [rawEta_cmp]
      show cmpEta E pi cL cR i (.c0load false) g _ _ _ _ = _
      rw [cmpEta]
      rfl
    · intro a0 hmv
      cases hmv
  have hstep5 := c0pay_run E (w := w) pi cL cR i false (tgtOf false ((E.κ cR).c0 i))
    (g := g) (reg := reg) (pos := pos) ((E.κ cR).c0 i).natAbs
    (Nat.lt_succ_of_le (c0_le_Wb E cR i))
    (payP true ((E.κ cL).c0 i)) (payN true ((E.κ cL).c0 i))
  have hc2R : cond (tgtOf false ((E.κ cR).c0 i))
        (c2 (payP true ((E.κ cL).c0 i) + ((E.κ cR).c0 i).natAbs)
          (payN true ((E.κ cL).c0 i)))
        (c2 (payP true ((E.κ cL).c0 i))
          (payN true ((E.κ cL).c0 i) + ((E.κ cR).c0 i).natAbs))
      = c2 (payP true ((E.κ cL).c0 i) + payP false ((E.κ cR).c0 i))
           (payN true ((E.κ cL).c0 i) + payN false ((E.κ cR).c0 i)) :=
    cond_pay_c2 false ((E.κ cR).c0 i) _ _
  rw [hc2R] at hstep5
  have hstep6 : (evalM E).Steps w
      ((g, .cmp pi cL cR i (.c0pay false ⟨0, Nat.succ_pos _⟩
          (tgtOf false ((E.κ cR).c0 i))), reg), pos,
        c2 (payP true ((E.κ cL).c0 i) + payP false ((E.κ cR).c0 i))
           (payN true ((E.κ cL).c0 i) + payN false ((E.κ cR).c0 i))) []
      ((g, unitTagL E pi cL cR i 0, reg), pos,
        c2 (payP true ((E.κ cL).c0 i) + payP false ((E.κ cR).c0 i))
           (payN true ((E.κ cL).c0 i) + payN false ((E.κ cR).c0 i))) := by
    refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
      (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
    · rw [rawEta_cmp]
      show cmpEta E pi cL cR i (.c0pay false _ _) g _ _ _ _ = _
      rw [cmpEta]
      rw [if_neg (show ¬ (0 < (0 : ℕ)) by omega),
        if_neg (show ¬ (false = true) by simp), firstUnitTag_eq]
    · intro a0 hmv
      cases hmv
  obtain ⟨regL, hstepL⟩ := unitsL_run E (w := w) pi cL cR i (g := g) (pos := pos)
    tL hvL hmkL hscan 0 reg
    (payP true ((E.κ cL).c0 i) + payP false ((E.κ cR).c0 i))
    (payN true ((E.κ cL).c0 i) + payN false ((E.κ cR).c0 i))
  obtain ⟨regF, hstepR⟩ := unitsR_run E (w := w) pi cL cR i (g := g) (pos := pos)
    tR hvR hmkR hscan 0 regL
    (payP true ((E.κ cL).c0 i) + payP false ((E.κ cR).c0 i)
      + ∑ r' ∈ Finset.Ico 0 (P.toPoly.arity cL), uPosN E true cL tL w i r')
    (payN true ((E.κ cL).c0 i) + payN false ((E.κ cR).c0 i)
      + ∑ r' ∈ Finset.Ico 0 (P.toPoly.arity cL), uNegN E true cL tL w i r')
  refine ⟨regF, ?_⟩
  have hall := stepsTrans E hstep1 (stepsTrans E hstep2 (stepsTrans E hstep3
    (stepsTrans E hstep4 (stepsTrans E hstep5 (stepsTrans E hstep6
      (stepsTrans E hstepL hstepR))))))
  have hPfin : payP true ((E.κ cL).c0 i) + payP false ((E.κ cR).c0 i)
        + ∑ r' ∈ Finset.Ico 0 (P.toPoly.arity cL), uPosN E true cL tL w i r'
        + ∑ r' ∈ Finset.Ico 0 (P.toPoly.arity cR), uPosN E false cR tR w i r'
      = dimPos E cL tL cR tR w i := by
    rw [sum_uPosN, sum_uPosN, dimPos]
  have hNfin : payN true ((E.κ cL).c0 i) + payN false ((E.κ cR).c0 i)
        + ∑ r' ∈ Finset.Ico 0 (P.toPoly.arity cL), uNegN E true cL tL w i r'
        + ∑ r' ∈ Finset.Ico 0 (P.toPoly.arity cR), uNegN E false cR tR w i r'
      = dimNeg E cL tL cR tR w i := by
    rw [sum_uNegN, sum_uNegN, dimNeg]
  rw [hPfin, hNfin] at hall
  simpa using hall


/-! ## §12 Compare phase III: drain, zero-out, and the verdict -/

/-- The dimension-successor tag: next dimension, or the tie sweep after the
last one. -/
def dimTag (pi : CmpId) (cL cR : Fin P.toPoly.K) (i0 : ℕ) : TagT E :=
  if h : i0 < P.d then .cmp pi cL cR ⟨i0, h⟩ (.c0load true)
  else .sweep (.ord pi cL cR) (.tieK pi)

theorem cmpEntryTag_eq (pi : CmpId) (cL cR : Fin P.toPoly.K) :
    cmpEntryTag E pi cL cR = dimTag E pi cL cR 0 := rfl

/-- The drain loop: decrement both counters until one reaches zero. -/
theorem drain_loop {w : List Step} (pi : CmpId) (cL cR : Fin P.toPoly.K)
    (i : Fin P.d) {g : Glob P.toPoly.K} {reg : Reg E} {pos : Fin (hN P) → ℕ} :
    ∀ (m a b : ℕ),
    (evalM E).Steps w ((g, .cmp pi cL cR i .drain, reg), pos, c2 (a + m) (b + m)) []
      ((g, .cmp pi cL cR i .drain, reg), pos, c2 a b) := by
  intro m
  induction m with
  | zero => intro a b; exact stepsRefl E _
  | succ m ih =>
      intro a b
      have hnext := ih a b
      refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsDecBoth) ?_ ?_
        (apply_mvStay _) ?_ hnext
      · rw [rawEta_cmp]
        show cmpEta E pi cL cR i .drain g _ _ _ _ = _
        rw [cmpEta]
        rw [show ((c2 (a + (m + 1)) (b + (m + 1)) 0 == 0)) = false from by
            rw [c2_zero, beq_eq_false_iff_ne]
            omega]
        rw [show ((c2 (a + (m + 1)) (b + (m + 1)) 1 == 0)) = false from by
            rw [c2_one, beq_eq_false_iff_ne]
            omega]
      · intro a0 hmv
        cases hmv
      · rw [apply_opsDecBoth_c2]
        rw [show a + (m + 1) - 1 = a + m from by omega,
          show b + (m + 1) - 1 = b + m from by omega]

/-- The zero-out loop: empty the target counter, then dispatch the verdict. -/
theorem zero_loop {w : List Step} (pi : CmpId) (cL cR : Fin P.toPoly.K)
    (i : Fin P.d) (tgt vd : Bool) {g : Glob P.toPoly.K} {reg : Reg E}
    {pos : Fin (hN P) → ℕ} {tg : TagT E}
    (hexit : cmpExit E pi vd g = some tg) :
    ∀ (v : ℕ),
    (evalM E).Steps w
      ((g, .cmp pi cL cR i (.zero tgt vd), reg), pos,
        c2 (cond tgt v 0) (cond tgt 0 v)) []
      ((g, tg, reg), pos, c2 0 0) := by
  intro v
  induction v with
  | zero =>
      have h00 : (c2 (cond tgt 0 0) (cond tgt 0 0)) = c2 0 0 := by
        cases tgt <;> rfl
      rw [show (cond tgt 0 0 : ℕ) = 0 from by cases tgt <;> rfl]
      refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
        (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
      · rw [rawEta_cmp]
        show cmpEta E pi cL cR i (.zero tgt vd) g _ _ _ _ = _
        rw [cmpEta]
        rw [show ((c2 0 0 (ctrIdx tgt) == 0)) = true from by cases tgt <;> rfl]
        rw [if_pos rfl, hexit]
        rfl
      · intro a0 hmv
        cases hmv
  | succ v ih =>
      refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsDec tgt) ?_ ?_
        (apply_mvStay _) ?_ ih
      · rw [rawEta_cmp]
        show cmpEta E pi cL cR i (.zero tgt vd) g _ _ _ _ = _
        rw [cmpEta]
        rw [show ((c2 (cond tgt (v + 1) 0) (cond tgt 0 (v + 1)) (ctrIdx tgt) == 0))
            = false from by
          cases tgt
          · show ((v + 1 : ℕ) == 0) = false
            rw [beq_eq_false_iff_ne]
            omega
          · show ((v + 1 : ℕ) == 0) = false
            rw [beq_eq_false_iff_ne]
            omega]
        rw [if_neg (show ¬ (false = true) by simp)]
      · intro a0 hmv
        cases hmv
      · rw [apply_opsDec_c2]
        cases tgt
        · show c2 (cond false (v + 1) 0) (cond false 0 (v + 1) - 1) = _
          show c2 0 (v + 1 - 1) = c2 (cond false v 0) (cond false 0 v)
          rfl
        · show c2 (cond true (v + 1) 0 - 1) (cond true 0 (v + 1)) = _
          show c2 (v + 1 - 1) 0 = c2 (cond true v 0) (cond true 0 v)
          rfl

/-- Drain with equal counters: both empty simultaneously; move to the next
dimension (or the tie sweep). -/
theorem drain_run_eq {w : List Step} (pi : CmpId) (cL cR : Fin P.toPoly.K)
    (i : Fin P.d) {g : Glob P.toPoly.K} {reg : Reg E} {pos : Fin (hN P) → ℕ}
    (a : ℕ) :
    (evalM E).Steps w ((g, .cmp pi cL cR i .drain, reg), pos, c2 a a) []
      ((g, dimTag E pi cL cR (i.val + 1), reg), pos, c2 0 0) := by
  have hloop := drain_loop E (w := w) pi cL cR i (g := g) (reg := reg) (pos := pos)
    a 0 0
  rw [show (0 + a) = a from by omega] at hloop
  refine stepsTrans E (o₁ := []) (o₂ := []) hloop ?_
  refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
    (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
  · rw [rawEta_cmp]
    show cmpEta E pi cL cR i .drain g _ _ _ _ = _
    rw [cmpEta]
    rw [show ((c2 0 0 0 == 0)) = true from rfl]
    rw [show ((c2 0 0 1 == 0)) = true from rfl]
    rw [dimTag]
    by_cases hi : i.val + 1 < P.d
    · rw [dif_pos hi, dif_pos hi]
    · rw [dif_neg hi, dif_neg hi]
  · intro a0 hmv
    cases hmv

/-- Drain with a strictly larger positive counter: verdict `false`. -/
theorem drain_run_gt {w : List Step} (pi : CmpId) (cL cR : Fin P.toPoly.K)
    (i : Fin P.d) {g : Glob P.toPoly.K} {reg : Reg E} {pos : Fin (hN P) → ℕ}
    {a b : ℕ} (hab : b < a) {tg : TagT E}
    (hexit : cmpExit E pi false g = some tg) :
    (evalM E).Steps w ((g, .cmp pi cL cR i .drain, reg), pos, c2 a b) []
      ((g, tg, reg), pos, c2 0 0) := by
  have hloop := drain_loop E (w := w) pi cL cR i (g := g) (reg := reg) (pos := pos)
    b (a - b) 0
  rw [show (a - b) + b = a from by omega, show 0 + b = b from by omega] at hloop
  refine stepsTrans E (o₁ := []) (o₂ := []) hloop ?_
  have hstep : (evalM E).Steps w
      ((g, .cmp pi cL cR i .drain, reg), pos, c2 (a - b) 0) []
      ((g, .cmp pi cL cR i (.zero true false), reg), pos, c2 (a - b) 0) := by
    refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
      (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
    · rw [rawEta_cmp]
      show cmpEta E pi cL cR i .drain g _ _ _ _ = _
      rw [cmpEta]
      rw [show ((c2 (a - b) 0 0 == 0)) = false from by
        rw [c2_zero, beq_eq_false_iff_ne]
        omega]
      rw [show ((c2 (a - b) 0 1 == 0)) = true from rfl]
    · intro a0 hmv
      cases hmv
  refine stepsTrans E (o₁ := []) (o₂ := []) hstep ?_
  have hz := zero_loop E (w := w) pi cL cR i true false (g := g) (reg := reg)
    (pos := pos) hexit (a - b)
  exact hz

/-- Drain with a strictly larger negative counter: verdict `true`. -/
theorem drain_run_lt {w : List Step} (pi : CmpId) (cL cR : Fin P.toPoly.K)
    (i : Fin P.d) {g : Glob P.toPoly.K} {reg : Reg E} {pos : Fin (hN P) → ℕ}
    {a b : ℕ} (hab : a < b) {tg : TagT E}
    (hexit : cmpExit E pi true g = some tg) :
    (evalM E).Steps w ((g, .cmp pi cL cR i .drain, reg), pos, c2 a b) []
      ((g, tg, reg), pos, c2 0 0) := by
  have hloop := drain_loop E (w := w) pi cL cR i (g := g) (reg := reg) (pos := pos)
    a 0 (b - a)
  rw [show 0 + a = a from by omega, show (b - a) + a = b from by omega] at hloop
  refine stepsTrans E (o₁ := []) (o₂ := []) hloop ?_
  have hstep : (evalM E).Steps w
      ((g, .cmp pi cL cR i .drain, reg), pos, c2 0 (b - a)) []
      ((g, .cmp pi cL cR i (.zero false true), reg), pos, c2 0 (b - a)) := by
    refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
      (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
    · rw [rawEta_cmp]
      show cmpEta E pi cL cR i .drain g _ _ _ _ = _
      rw [cmpEta]
      rw [show ((c2 0 (b - a) 0 == 0)) = true from rfl]
      rw [show ((c2 0 (b - a) 1 == 0)) = false from by
        rw [c2_one, beq_eq_false_iff_ne]
        omega]
    · intro a0 hmv
      cases hmv
  refine stepsTrans E (o₁ := []) (o₂ := []) hstep ?_
  exact zero_loop E (w := w) pi cL cR i false true (g := g) (reg := reg)
    (pos := pos) hexit (b - a)


/-! ## §13 The full ≺-comparison

-/

omit [Fintype Gamma] in
theorem rankOf_mk (c : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c) → ℕ)
    (w : List Step) (i : Fin P.d) :
    P.rankOf w ⟨c, t⟩ i = (E.κ c).eval w t i := by
  show P.rank c w t i = _
  rw [E.hκ c w t]

/-- Head positions of the tie-order job's combined marks. -/
theorem ord_marks {pos : Fin (hN P) → ℕ} (pi : CmpId) (cL cR : Fin P.toPoly.K)
    (tL : Fin (P.toPoly.arity cL) → ℕ) (tR : Fin (P.toPoly.arity cR) → ℕ)
    (hmkL : ∀ rr : Fin (P.toPoly.arity cL),
      pos (sideHead pi true (embedA rr)) = tL rr + 1)
    (hmkR : ∀ rr : Fin (P.toPoly.arity cR),
      pos (sideHead pi false (embedA rr)) = tR rr + 1) :
    ∀ idx : Fin (jobArity P (.ord pi cL cR)),
      pos (jobHeads (.ord pi cL cR) idx)
        = (Fin.addCases (motive := fun _ => ℕ) tL tR idx) + 1 := by
  intro idx
  refine Fin.addCases ?_ ?_ idx
  · intro rr
    simp only [jobHeads, Fin.addCases_left]
    exact hmkL rr
  · intro rr
    simp only [jobHeads, Fin.addCases_right]
    exact hmkR rr

/-- **The full ≺-comparison**: from the compare entry the machine computes the
Boolean verdict of `wrpOrd` between the two marked atoms and dispatches it. -/
theorem cmp_run {w : List Step} (pi : CmpId) (cL cR : Fin P.toPoly.K)
    {g : Glob P.toPoly.K} {pos : Fin (hN P) → ℕ}
    (tL : Fin (P.toPoly.arity cL) → ℕ) (tR : Fin (P.toPoly.arity cR) → ℕ)
    (hvL : ∀ rr, tL rr < w.length) (hvR : ∀ rr, tR rr < w.length)
    (hmkL : ∀ rr : Fin (P.toPoly.arity cL),
      pos (sideHead pi true (embedA rr)) = tL rr + 1)
    (hmkR : ∀ rr : Fin (P.toPoly.arity cR),
      pos (sideHead pi false (embedA rr)) = tR rr + 1)
    (hscan : pos scanH = 0) (reg : Reg E) :
    ∃ (V : Bool) (regF : Reg E),
      (V = true ↔ P.wrpOrd w ⟨cL, tL⟩ ⟨cR, tR⟩) ∧
      ∀ {tg : TagT E}, cmpExit E pi V g = some tg →
        (evalM E).Steps w ((g, cmpEntryTag E pi cL cR, reg), pos, c2 0 0) []
          ((g, tg, regF), pos, c2 0 0) := by
  rw [cmpEntryTag_eq]
  -- induction over the dimensions
  suffices h : ∀ (i0 : ℕ) (reg : Reg E),
      (∀ j : Fin P.d, j.val < i0 → P.rankOf w ⟨cL, tL⟩ j = P.rankOf w ⟨cR, tR⟩ j) →
      ∃ (V : Bool) (regF : Reg E),
        (V = true ↔ P.wrpOrd w ⟨cL, tL⟩ ⟨cR, tR⟩) ∧
        ∀ {tg : TagT E}, cmpExit E pi V g = some tg →
          (evalM E).Steps w ((g, dimTag E pi cL cR i0, reg), pos, c2 0 0) []
            ((g, tg, regF), pos, c2 0 0) by
    exact h 0 reg (fun j hj => absurd hj (by omega))
  intro i0
  induction hm : P.d - i0 generalizing i0 with
  | zero =>
      intro reg hpre
      have hge : P.d ≤ i0 := by omega
      -- all dimensions agree: tie sweep decides by the MSO order
      have hrkeq : P.rankOf w ⟨cL, tL⟩ = P.rankOf w ⟨cR, tR⟩ := by
        funext j
        exact hpre j (by omega)
      obtain ⟨b, regR, hb, hrun⟩ := sweep_run E (w := w) (.ord pi cL cR) (.tieK pi)
        (g := g) reg (cnt := c2 0 0)
        (Fin.addCases (motive := fun _ => ℕ) tL tR) hscan
        (ord_marks pi cL cR tL tR hmkL hmkR)
      have hbiff : b = true ↔ P.wrpOrd w ⟨cL, tL⟩ ⟨cR, tR⟩ := by
        rw [hb]
        have hrange : ∀ idx, (Fin.addCases (motive := fun _ => ℕ) tL tR idx) < w.length := by
          intro idx
          refine Fin.addCases ?_ ?_ idx
          · intro rr; rw [Fin.addCases_left]; exact hvL rr
          · intro rr; rw [Fin.addCases_right]; exact hvR rr
        have hord := E.hord cL cR w (Fin.addCases (motive := fun _ => ℕ) tL tR) hrange
        show (E.Mord cL cR).accepts (markAtN (P.toPoly.arity cL + P.toPoly.arity cR) w
          (Fin.addCases (motive := fun _ => ℕ) tL tR)) ↔ _
        rw [hord]
        have hsplitL : (fun t => Fin.addCases (motive := fun _ => ℕ) tL tR
            (Fin.castAdd (P.toPoly.arity cR) t)) = tL := by
          funext t
          rw [Fin.addCases_left]
        have hsplitR : (fun t => Fin.addCases (motive := fun _ => ℕ) tL tR
            (Fin.natAdd (P.toPoly.arity cL) t)) = tR := by
          funext t
          rw [Fin.addCases_right]
        rw [hsplitL, hsplitR]
        exact (wrpOrd_iff_atomOrd_of_rankEq P hrkeq).symm
      refine ⟨b, regR, hbiff, ?_⟩
      intro tg hexit
      have hdisp : contStep E (.tieK pi) b g = some (g, tg, []) := by
        show (cmpExit E pi b g).map _ = _
        rw [hexit]
        rfl
      have := hrun hdisp
      rw [show dimTag E pi cL cR i0 = .sweep (.ord pi cL cR) (.tieK pi) from by
        rw [dimTag, dif_neg (by omega)]]
      exact this
  | succ m ih =>
      intro reg hpre
      have hlt : i0 < P.d := by omega
      obtain ⟨regD, hdim⟩ := dim_run E (w := w) pi cL cR ⟨i0, hlt⟩ (g := g)
        (pos := pos) tL tR hvL hvR hmkL hmkR hscan reg
      have hS := dimPos_sub_dimNeg E cL tL cR tR w ⟨i0, hlt⟩
      rw [← rankOf_mk E cL tL w ⟨i0, hlt⟩, ← rankOf_mk E cR tR w ⟨i0, hlt⟩] at hS
      have hpre' : ∀ j : Fin P.d, j < (⟨i0, hlt⟩ : Fin P.d) →
          P.rankOf w ⟨cL, tL⟩ j = P.rankOf w ⟨cR, tR⟩ j := by
        intro j hj
        exact hpre j (by rw [Fin.lt_def] at hj; omega)
      rcases lt_trichotomy (dimPos E cL tL cR tR w ⟨i0, hlt⟩)
        (dimNeg E cL tL cR tR w ⟨i0, hlt⟩) with hcmp | hcmp | hcmp
      · -- S < 0: the left atom is smaller
        have hrk : P.rankOf w ⟨cL, tL⟩ ⟨i0, hlt⟩ < P.rankOf w ⟨cR, tR⟩ ⟨i0, hlt⟩ := by
          omega
        refine ⟨true, regD, ⟨fun _ => wrpOrd_of_dimLt P ⟨i0, hlt⟩ hpre' hrk,
          fun _ => rfl⟩, ?_⟩
        intro tg hexit
        have hdrain := drain_run_lt E (w := w) pi cL cR ⟨i0, hlt⟩ (g := g)
          (reg := regD) (pos := pos) hcmp hexit
        rw [show dimTag E pi cL cR i0 = .cmp pi cL cR ⟨i0, hlt⟩ (.c0load true) from by
          rw [dimTag, dif_pos hlt]]
        have hcomp := stepsTrans E hdim hdrain
        simpa using hcomp
      · -- S = 0: the dimension agrees; move on
        have hrk : P.rankOf w ⟨cL, tL⟩ ⟨i0, hlt⟩ = P.rankOf w ⟨cR, tR⟩ ⟨i0, hlt⟩ := by
          omega
        have hpre2 : ∀ j : Fin P.d, j.val < i0 + 1 →
            P.rankOf w ⟨cL, tL⟩ j = P.rankOf w ⟨cR, tR⟩ j := by
          intro j hj
          by_cases hji : j.val = i0
          · have : j = (⟨i0, hlt⟩ : Fin P.d) := Fin.ext hji
            rw [this]
            exact hrk
          · exact hpre j (by omega)
        obtain ⟨V, regF, hViff, hVrun⟩ := ih (i0 + 1) (by omega) regD hpre2
        refine ⟨V, regF, hViff, ?_⟩
        intro tg hexit
        have hdrain := drain_run_eq E (w := w) pi cL cR ⟨i0, hlt⟩ (g := g)
          (reg := regD) (pos := pos) (dimPos E cL tL cR tR w ⟨i0, hlt⟩)
        rw [show c2 (dimPos E cL tL cR tR w ⟨i0, hlt⟩)
            (dimNeg E cL tL cR tR w ⟨i0, hlt⟩)
          = c2 (dimPos E cL tL cR tR w ⟨i0, hlt⟩)
            (dimPos E cL tL cR tR w ⟨i0, hlt⟩) from by rw [hcmp]] at hdim
        have hnext := hVrun hexit
        rw [show dimTag E pi cL cR i0 = .cmp pi cL cR ⟨i0, hlt⟩ (.c0load true) from by
          rw [dimTag, dif_pos hlt]]
        have hcomp := stepsTrans E hdim (stepsTrans E hdrain hnext)
        simpa using hcomp
      · -- S > 0: the left atom is larger
        have hrk : P.rankOf w ⟨cR, tR⟩ ⟨i0, hlt⟩ < P.rankOf w ⟨cL, tL⟩ ⟨i0, hlt⟩ := by
          omega
        have hnot := not_wrpOrd_of_dimGt P ⟨i0, hlt⟩ hpre' hrk
        refine ⟨false, regD, ⟨fun hc => absurd hc (by simp),
          fun hw => absurd hw hnot⟩, ?_⟩
        intro tg hexit
        have hdrain := drain_run_gt E (w := w) pi cL cR ⟨i0, hlt⟩ (g := g)
          (reg := regD) (pos := pos) hcmp hexit
        rw [show dimTag E pi cL cR i0 = .cmp pi cL cR ⟨i0, hlt⟩ (.c0load true) from by
          rw [dimTag, dif_pos hlt]]
        have hcomp := stepsTrans E hdim hdrain
        simpa using hcomp


/-! ## §14 Structured head positions and walk results -/

/-! Structured head-position vectors. -/

/-- Pad a tuple of copy `c` into a `kmax`-block of cell positions (coordinate
`r` sits on cell `t r + 1`; unused coordinates are parked on `⊢`). -/
def pad (c : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c) → ℕ) :
    Fin (kmaxP P) → ℕ :=
  fun r => if h : r.val < P.toPoly.arity c then t ⟨r.val, h⟩ + 1 else 0

/-- Optional-atom padding (parked when absent). -/
def padO : Option P.toPoly.Atom → Fin (kmaxP P) → ℕ
  | none => fun _ => 0
  | some a => pad a.1 a.2

/-- The structured position vector: scan, CUR block, CAND block, BEST block. -/
def hpos (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) : Fin (hN P) → ℕ := fun x =>
  if h0 : x.val = 0 then s
  else if h1 : x.val < 1 + kmaxP P then cu ⟨x.val - 1, by omega⟩
  else if h2 : x.val < 1 + 2 * kmaxP P then ca ⟨x.val - 1 - kmaxP P, by omega⟩
  else be ⟨x.val - 1 - 2 * kmaxP P, by
    have := x.2
    show x.val - 1 - 2 * kmaxP P < kmaxP P
    have hx : x.val < 3 * kmaxP P + 1 := this
    omega⟩

omit [Fintype Gamma] in
@[simp] theorem hpos_scanH (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) :
    hpos s cu ca be scanH = s := rfl

omit [Fintype Gamma] in
@[simp] theorem hpos_curH (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ)
    (r : Fin (kmaxP P)) : hpos s cu ca be (curH r) = cu r := by
  have hr := r.2
  rw [hpos, curH]
  rw [dif_neg (by omega : ¬ (1 + r.val = 0))]
  rw [dif_pos (by omega : 1 + r.val < 1 + kmaxP P)]
  congr 1
  refine Fin.ext ?_
  show 1 + r.val - 1 = r.val
  omega

omit [Fintype Gamma] in
@[simp] theorem hpos_candH (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ)
    (r : Fin (kmaxP P)) : hpos s cu ca be (candH r) = ca r := by
  have hr := r.2
  rw [hpos, candH]
  rw [dif_neg (by omega : ¬ (1 + kmaxP P + r.val = 0))]
  rw [dif_neg (by omega : ¬ (1 + kmaxP P + r.val < 1 + kmaxP P))]
  rw [dif_pos (by omega : 1 + kmaxP P + r.val < 1 + 2 * kmaxP P)]
  congr 1
  refine Fin.ext ?_
  show 1 + kmaxP P + r.val - 1 - kmaxP P = r.val
  omega

omit [Fintype Gamma] in
@[simp] theorem hpos_bestH (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ)
    (r : Fin (kmaxP P)) : hpos s cu ca be (bestH r) = be r := by
  have hr := r.2
  rw [hpos, bestH]
  rw [dif_neg (by omega : ¬ (1 + 2 * kmaxP P + r.val = 0))]
  rw [dif_neg (by omega : ¬ (1 + 2 * kmaxP P + r.val < 1 + kmaxP P))]
  rw [dif_neg (by omega : ¬ (1 + 2 * kmaxP P + r.val < 1 + 2 * kmaxP P))]
  congr 1
  refine Fin.ext ?_
  show 1 + 2 * kmaxP P + r.val - 1 - 2 * kmaxP P = r.val
  omega

omit [Fintype Gamma] in
theorem update_hpos_scanH (s s' : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) :
    Function.update (hpos s cu ca be) scanH s' = hpos s' cu ca be := by
  funext x
  by_cases hx : x = scanH
  · subst hx
    rw [Function.update_self, hpos_scanH]
  · rw [Function.update_of_ne hx]
    have hxv : x.val ≠ 0 := by
      intro hc
      exact hx (Fin.ext hc)
    rw [hpos, hpos, dif_neg hxv, dif_neg hxv]

omit [Fintype Gamma] in
theorem pad_embedA (c : Fin P.toPoly.K) (t : Fin (P.toPoly.arity c) → ℕ)
    (i : Fin (P.toPoly.arity c)) : pad c t (embedA i) = t i + 1 := by
  rw [pad, embedA]
  rw [dif_pos i.2]

omit [Fintype Gamma] in
theorem pad_le (c : Fin P.toPoly.K) {t : Fin (P.toPoly.arity c) → ℕ} {n : ℕ}
    (ht : ∀ rr, t rr < n) (r : Fin (kmaxP P)) : pad c t r ≤ n := by
  rw [pad]
  split
  · rename_i h
    have := ht ⟨r.val, h⟩
    omega
  · omega

/-! Walk results in structured form. -/

omit [Fintype Gamma] in
theorem walkRes_parkCand (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) :
    (fun x => if wkIn (P := P) .parkCand x.val then 0 else hpos s cu ca be x)
      = hpos s cu (fun _ => 0) be := by
  funext x
  rw [hpos, hpos]
  by_cases h : wkIn (P := P) .parkCand x.val
  · rw [if_pos h]
    rw [wkIn, wkLo, wkHi] at h
    obtain ⟨h1, h2⟩ := h
    have ha : ¬ (x.val = 0) := by omega
    have hb : ¬ (x.val < 1 + kmaxP P) := by omega
    simp only [dif_neg ha, dif_neg hb, dif_pos h2]
  · rw [if_neg h]
    rw [wkIn, wkLo, wkHi] at h
    by_cases h0 : x.val = 0
    · simp only [dif_pos h0]
    · by_cases hc : x.val < 1 + kmaxP P
      · simp only [dif_neg h0, dif_pos hc]
      · have hge : ¬ (x.val < 1 + 2 * kmaxP P) := by omega
        simp only [dif_neg h0, dif_neg hc, dif_neg hge]

omit [Fintype Gamma] in
theorem walkRes_parkBest (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) :
    (fun x => if wkIn (P := P) .parkBest x.val then 0 else hpos s cu ca be x)
      = hpos s cu ca (fun _ => 0) := by
  funext x
  rw [hpos, hpos]
  by_cases h : wkIn (P := P) .parkBest x.val
  · rw [if_pos h]
    rw [wkIn, wkLo, wkHi] at h
    obtain ⟨h1, h2⟩ := h
    have ha : ¬ (x.val = 0) := by omega
    have hb : ¬ (x.val < 1 + kmaxP P) := by omega
    have hc : ¬ (x.val < 1 + 2 * kmaxP P) := by omega
    simp only [dif_neg ha, dif_neg hb, dif_neg hc]
  · rw [if_neg h]
    rw [wkIn, wkLo, wkHi] at h
    have hx := x.2
    have hx' : x.val < 3 * kmaxP P + 1 := hx
    by_cases h0 : x.val = 0
    · simp only [dif_pos h0]
    · by_cases hc : x.val < 1 + kmaxP P
      · simp only [dif_neg h0, dif_pos hc]
      · have hca : x.val < 1 + 2 * kmaxP P := by omega
        simp only [dif_neg h0, dif_neg hc, dif_pos hca]

omit [Fintype Gamma] in
theorem walkRes_parkCur (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) :
    (fun x => if wkIn (P := P) .parkCur x.val then 0 else hpos s cu ca be x)
      = hpos s (fun _ => 0) ca be := by
  funext x
  rw [hpos, hpos]
  by_cases h : wkIn (P := P) .parkCur x.val
  · rw [if_pos h]
    rw [wkIn, wkLo, wkHi] at h
    obtain ⟨h1, h2⟩ := h
    have ha : ¬ (x.val = 0) := by omega
    simp only [dif_neg ha, dif_pos h2]
  · rw [if_neg h]
    rw [wkIn, wkLo, wkHi] at h
    by_cases h0 : x.val = 0
    · simp only [dif_pos h0]
    · have hcu : ¬ (x.val < 1 + kmaxP P) := by omega
      by_cases hca : x.val < 1 + 2 * kmaxP P
      · simp only [dif_neg h0, dif_neg hcu, dif_pos hca]
      · simp only [dif_neg h0, dif_neg hcu, dif_neg hca]

omit [Fintype Gamma] in
theorem walkRes_parkCandBest (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) :
    (fun x => if wkIn (P := P) .parkCandBest x.val then 0 else hpos s cu ca be x)
      = hpos s cu (fun _ => 0) (fun _ => 0) := by
  funext x
  rw [hpos, hpos]
  by_cases h : wkIn (P := P) .parkCandBest x.val
  · rw [if_pos h]
    rw [wkIn, wkLo, wkHi] at h
    obtain ⟨h1, h2⟩ := h
    have ha : ¬ (x.val = 0) := by omega
    have hb : ¬ (x.val < 1 + kmaxP P) := by omega
    by_cases hca : x.val < 1 + 2 * kmaxP P
    · simp only [dif_neg ha, dif_neg hb, dif_pos hca]
    · simp only [dif_neg ha, dif_neg hb, dif_neg hca]
  · rw [if_neg h]
    rw [wkIn, wkLo, wkHi] at h
    have hx' : x.val < 3 * kmaxP P + 1 := x.2
    by_cases h0 : x.val = 0
    · simp only [dif_pos h0]
    · have hcu : x.val < 1 + kmaxP P := by omega
      simp only [dif_neg h0, dif_pos hcu]

omit [Fintype Gamma] in
theorem walkRes_copyBest (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) :
    (fun x => if wkIn (P := P) .copyBest x.val
        then hpos s cu ca be (wkPartner (P := P) .copyBest x) else hpos s cu ca be x)
      = hpos s cu ca ca := by
  funext x
  by_cases h : wkIn (P := P) .copyBest x.val
  · rw [if_pos h]
    have hint : 1 + 2 * kmaxP P ≤ x.val ∧ x.val < 1 + 3 * kmaxP P := by
      rw [wkIn, wkLo, wkHi] at h
      exact h
    obtain ⟨h1, h2⟩ := hint
    have hxeq : x = bestH ⟨x.val - 1 - 2 * kmaxP P, by omega⟩ := by
      refine Fin.ext ?_
      show x.val = 1 + 2 * kmaxP P + (x.val - 1 - 2 * kmaxP P)
      omega
    have hpeq : wkPartner (P := P) .copyBest x
        = candH ⟨x.val - 1 - 2 * kmaxP P, by omega⟩ := by
      rw [wkPartner, candH]
      refine Fin.ext ?_
      show x.val - kmaxP P = 1 + kmaxP P + (x.val - 1 - 2 * kmaxP P)
      omega
    rw [hpeq, hpos_candH]
    conv_rhs => rw [hxeq]
    rw [hpos_bestH]
  · rw [if_neg h]
    rw [wkIn, wkLo, wkHi] at h
    rw [hpos, hpos]
    have hx' : x.val < 3 * kmaxP P + 1 := x.2
    by_cases h0 : x.val = 0
    · simp only [dif_pos h0]
    · by_cases hcu : x.val < 1 + kmaxP P
      · simp only [dif_neg h0, dif_pos hcu]
      · have hca : x.val < 1 + 2 * kmaxP P := by omega
        simp only [dif_neg h0, dif_neg hcu, dif_pos hca]

omit [Fintype Gamma] in
theorem walkRes_copyCur (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) :
    (fun x => if wkIn (P := P) .copyCur x.val
        then hpos s cu ca be (wkPartner (P := P) .copyCur x) else hpos s cu ca be x)
      = hpos s be ca be := by
  funext x
  by_cases h : wkIn (P := P) .copyCur x.val
  · rw [if_pos h]
    have hint : 1 ≤ x.val ∧ x.val < 1 + kmaxP P := by
      rw [wkIn, wkLo, wkHi] at h
      exact h
    obtain ⟨h1, h2⟩ := hint
    have hxeq : x = curH ⟨x.val - 1, by omega⟩ := by
      refine Fin.ext ?_
      show x.val = 1 + (x.val - 1)
      omega
    have hpeq : wkPartner (P := P) .copyCur x = bestH ⟨x.val - 1, by omega⟩ := by
      rw [wkPartner]
      simp only [dif_pos (show x.val + 2 * kmaxP P < hN P by
        show x.val + 2 * kmaxP P < 3 * kmaxP P + 1
        omega)]
      refine Fin.ext ?_
      show x.val + 2 * kmaxP P = 1 + 2 * kmaxP P + (x.val - 1)
      omega
    rw [hpeq, hpos_bestH]
    conv_rhs => rw [hxeq]
    rw [hpos_curH]
  · rw [if_neg h]
    rw [wkIn, wkLo, wkHi] at h
    rw [hpos, hpos]
    have hx' : x.val < 3 * kmaxP P + 1 := x.2
    by_cases h0 : x.val = 0
    · simp only [dif_pos h0]
    · have hcu : ¬ (x.val < 1 + kmaxP P) := by omega
      by_cases hca : x.val < 1 + 2 * kmaxP P
      · simp only [dif_neg h0, dif_neg hcu, dif_pos hca]
      · simp only [dif_neg h0, dif_neg hcu, dif_neg hca]


/-! ## §15 Candidate gadgets: init, successor, carry -/

section CandGadgets

open TupEnum

/-! Candidate-gadget single steps. -/

omit [Fintype Gamma] in
theorem update_hpos_candH (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ)
    (rr : Fin (kmaxP P)) (v : ℕ) :
    Function.update (hpos s cu ca be) (candH rr) v
      = hpos s cu (Function.update ca rr v) be := by
  funext x
  by_cases hx : x = candH rr
  · subst hx
    rw [Function.update_self, hpos_candH, Function.update_self]
  · rw [Function.update_of_ne hx]
    have hrr := rr.2
    rw [hpos, hpos]
    by_cases h0 : x.val = 0
    · rw [dif_pos h0, dif_pos h0]
    · by_cases hcu : x.val < 1 + kmaxP P
      · rw [dif_neg h0, dif_neg h0, dif_pos hcu, dif_pos hcu]
      · by_cases hca : x.val < 1 + 2 * kmaxP P
        · rw [dif_neg h0, dif_neg h0, dif_neg hcu, dif_neg hcu,
            dif_pos hca, dif_pos hca]
          rw [Function.update_of_ne]
          intro hc
          apply hx
          refine Fin.ext ?_
          have := congrArg Fin.val hc
          show x.val = 1 + kmaxP P + rr.val
          simp only [candH] at *
          omega
        · rw [dif_neg h0, dif_neg h0, dif_neg hcu, dif_neg hcu,
            dif_neg hca, dif_neg hca]

theorem step_roundStart_pos {w : List Step} (hK : 0 < P.toPoly.K)
    (gc gb : Option (Fin P.toPoly.K)) (gca : Option (Fin P.toPoly.K)) (reg : Reg E)
    (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) :
    (evalM E).Steps w (((gc, gca, gb), .roundStart, reg), pos, cnt) []
      (((gc, some ⟨0, hK⟩, gb), .candInit, reg), pos, cnt) := by
  refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
    (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
  · simp only [rawEta]
    rw [dif_pos hK]
  · intro a0 hmv
    cases hmv

theorem step_roundStart_zero {w : List Step} (hK : ¬ 0 < P.toPoly.K)
    (gc gb : Option (Fin P.toPoly.K)) (gca : Option (Fin P.toPoly.K)) (reg : Reg E)
    (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) :
    (evalM E).Steps w (((gc, gca, gb), .roundStart, reg), pos, cnt) []
      (((gc, none, gb), .accept, reg), pos, cnt) := by
  refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
    (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
  · simp only [rawEta]
    rw [dif_neg hK]
  · intro a0 hmv
    cases hmv

theorem step_candInit_zero {w : List Step} (c : Fin P.toPoly.K)
    (harz : P.toPoly.arity c = 0)
    (gc gb : Option (Fin P.toPoly.K)) (reg : Reg E)
    (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) :
    (evalM E).Steps w (((gc, some c, gb), .candInit, reg), pos, cnt) []
      (((gc, some c, gb), .sweep (.sel c) .selK, reg), pos, cnt) := by
  refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
    (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
  · simp only [rawEta]
    rw [if_pos harz]
  · intro a0 hmv
    cases hmv

theorem step_candInit_pos {w : List Step} (c : Fin P.toPoly.K)
    (harz : ¬ (P.toPoly.arity c = 0))
    (gc gb : Option (Fin P.toPoly.K)) (reg : Reg E)
    (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) (cnt : Fin 2 → ℕ)
    (hsym : ∀ rr : Fin (kmaxP P), rr.val < P.toPoly.arity c →
      tapeSym w (ca rr) ≠ TapeSym.rmark) :
    (evalM E).Steps w (((gc, some c, gb), .candInit, reg), hpos s cu ca be, cnt) []
      (((gc, some c, gb), .candInit2, reg),
        hpos s cu (fun rr => if rr.val < P.toPoly.arity c then ca rr + 1 else ca rr) be,
        cnt) := by
  refine stepRaw E (u := []) (out := [])
    (mv := fun a => if 1 + kmaxP P ≤ a.val ∧ a.val < 1 + kmaxP P + P.toPoly.arity c
      then .right else .stay) (ops := opsKeep) ?_ ?_ ?_ (apply_opsKeep _)
    (stepsRefl E _)
  · simp only [rawEta]
    rw [if_neg harz]
  · intro a0 hmv
    split at hmv
    · rename_i ha0
      obtain ⟨ha1, ha2⟩ := ha0
      have hars := arity_le_kmax (P := P) c
      have ha0eq : a0 = candH ⟨a0.val - 1 - kmaxP P, by omega⟩ := by
        refine Fin.ext ?_
        show a0.val = 1 + kmaxP P + (a0.val - 1 - kmaxP P)
        omega
      rw [ha0eq, hpos_candH]
      exact hsym _ (by show a0.val - 1 - kmaxP P < P.toPoly.arity c; omega)
    · cases hmv
  · funext x
    show (if 1 + kmaxP P ≤ x.val ∧ x.val < 1 + kmaxP P + P.toPoly.arity c
        then HeadMove.right else HeadMove.stay).apply (hpos s cu ca be x)
      = hpos s cu (fun rr => if rr.val < P.toPoly.arity c then ca rr + 1 else ca rr) be x
    have hars := arity_le_kmax (P := P) c
    by_cases hx : 1 + kmaxP P ≤ x.val ∧ x.val < 1 + kmaxP P + P.toPoly.arity c
    · rw [if_pos hx]
      obtain ⟨h1, h2⟩ := hx
      have hxeq : x = candH ⟨x.val - 1 - kmaxP P, by omega⟩ := by
        refine Fin.ext ?_
        show x.val = 1 + kmaxP P + (x.val - 1 - kmaxP P)
        omega
      rw [hxeq, hpos_candH, hpos_candH]
      rw [if_pos (by show x.val - 1 - kmaxP P < P.toPoly.arity c; omega)]
      rfl
    · rw [if_neg hx]
      show hpos s cu ca be x = _
      rw [hpos, hpos]
      by_cases h0 : x.val = 0
      · rw [dif_pos h0, dif_pos h0]
      · by_cases hcu : x.val < 1 + kmaxP P
        · rw [dif_neg h0, dif_neg h0, dif_pos hcu, dif_pos hcu]
        · by_cases hca : x.val < 1 + 2 * kmaxP P
          · rw [dif_neg h0, dif_neg h0, dif_neg hcu, dif_neg hcu,
              dif_pos hca, dif_pos hca]
            have hnlt : ¬ (x.val - 1 - kmaxP P < P.toPoly.arity c) := by omega
            rw [if_neg hnlt]
          · rw [dif_neg h0, dif_neg h0, dif_neg hcu, dif_neg hcu,
              dif_neg hca, dif_neg hca]

theorem step_candInit2 {w : List Step} (c : Fin P.toPoly.K) (h0k : 0 < kmaxP P)
    (gc gb : Option (Fin P.toPoly.K)) (reg : Reg E)
    (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) (cnt : Fin 2 → ℕ) :
    ((∀ aa, tapeSym w (ca ⟨0, h0k⟩) = TapeSym.letter aa →
      (evalM E).Steps w (((gc, some c, gb), .candInit2, reg), hpos s cu ca be, cnt) []
        (((gc, some c, gb), .sweep (.sel c) .selK, reg), hpos s cu ca be, cnt)) ∧
     (tapeSym w (ca ⟨0, h0k⟩) = TapeSym.rmark →
      (evalM E).Steps w (((gc, some c, gb), .candInit2, reg), hpos s cu ca be, cnt) []
        (((gc, some c, gb), .walk .parkCand, reg), hpos s cu ca be, cnt))) := by
  constructor
  · intro aa hsym
    refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
      (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
    · simp only [rawEta]
      rw [dif_pos h0k]
      rw [show tapeSym w (hpos s cu ca be (candH ⟨0, h0k⟩)) = TapeSym.letter aa from by
        rw [hpos_candH]
        exact hsym]
    · intro a0 hmv
      cases hmv
  · intro hsym
    refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
      (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
    · simp only [rawEta]
      rw [dif_pos h0k]
      rw [show tapeSym w (hpos s cu ca be (candH ⟨0, h0k⟩)) = TapeSym.rmark from by
        rw [hpos_candH]
        exact hsym]
    · intro a0 hmv
      cases hmv

theorem step_candNext_zero {w : List Step} (c : Fin P.toPoly.K)
    (r : Fin (kmaxP P + 1)) (hr : ¬ 0 < r.val)
    (gc gb : Option (Fin P.toPoly.K)) (reg : Reg E)
    (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) :
    (evalM E).Steps w (((gc, some c, gb), .candNext r, reg), pos, cnt) []
      (((gc, some c, gb), .walk .parkCand, reg), pos, cnt) := by
  refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
    (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
  · simp only [rawEta]
    rw [dif_neg hr]
  · intro a0 hmv
    cases hmv

theorem step_candNext_pos {w : List Step} (c : Fin P.toPoly.K)
    (r : Fin (kmaxP P + 1)) (hr : 0 < r.val)
    (gc gb : Option (Fin P.toPoly.K)) (reg : Reg E)
    (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) (cnt : Fin 2 → ℕ)
    (hsym : tapeSym w (ca ⟨r.val - 1, by have := r.2; omega⟩) ≠ TapeSym.rmark) :
    (evalM E).Steps w (((gc, some c, gb), .candNext r, reg), hpos s cu ca be, cnt) []
      (((gc, some c, gb), .candNext2 r, reg),
        hpos s cu (Function.update ca ⟨r.val - 1, by have := r.2; omega⟩
          (ca ⟨r.val - 1, by have := r.2; omega⟩ + 1)) be, cnt) := by
  refine stepRaw E (u := []) (out := [])
    (mv := mvOne (candH ⟨r.val - 1, by have := r.2; omega⟩) .right)
    (ops := opsKeep) ?_ ?_ ?_ (apply_opsKeep _) (stepsRefl E _)
  · simp only [rawEta]
    rw [dif_pos hr]
  · intro a0 hmv
    simp only [mvOne] at hmv
    split at hmv
    · rename_i ha0
      subst ha0
      rw [hpos_candH]
      exact hsym
    · cases hmv
  · rw [apply_mvOne, hpos_candH, update_hpos_candH]
    rfl

theorem step_candNext2 {w : List Step} (c : Fin P.toPoly.K)
    (r : Fin (kmaxP P + 1)) (hr : 0 < r.val)
    (gc gb : Option (Fin P.toPoly.K)) (reg : Reg E)
    (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) (cnt : Fin 2 → ℕ) :
    ((∀ aa, tapeSym w (ca ⟨r.val - 1, by have := r.2; omega⟩) = TapeSym.letter aa →
      (evalM E).Steps w (((gc, some c, gb), .candNext2 r, reg), hpos s cu ca be, cnt) []
        (((gc, some c, gb), .sweep (.sel c) .selK, reg), hpos s cu ca be, cnt)) ∧
     (tapeSym w (ca ⟨r.val - 1, by have := r.2; omega⟩) = TapeSym.rmark →
      (evalM E).Steps w (((gc, some c, gb), .candNext2 r, reg), hpos s cu ca be, cnt) []
        (((gc, some c, gb), .candCarry r, reg), hpos s cu ca be, cnt))) := by
  constructor
  · intro aa hsym
    refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
      (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
    · simp only [rawEta]
      rw [dif_pos hr]
      rw [show tapeSym w (hpos s cu ca be (candH ⟨r.val - 1, by have := r.2; omega⟩))
          = TapeSym.letter aa from by
        rw [hpos_candH]
        exact hsym]
    · intro a0 hmv
      cases hmv
  · intro hsym
    refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
      (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
    · simp only [rawEta]
      rw [dif_pos hr]
      rw [show tapeSym w (hpos s cu ca be (candH ⟨r.val - 1, by have := r.2; omega⟩))
          = TapeSym.rmark from by
        rw [hpos_candH]
        exact hsym]
    · intro a0 hmv
      cases hmv

/-- The carry walk: the incremented coordinate head walks back to `⊢` and is
placed on cell 1, and the gadget moves to the next coordinate. -/
theorem carry_walk {w : List Step} (c : Fin P.toPoly.K)
    (r : Fin (kmaxP P + 1)) (hr : 0 < r.val)
    (gc gb : Option (Fin P.toPoly.K)) (reg : Reg E)
    (s : ℕ) (cu ca be : Fin (kmaxP P) → ℕ) (cnt : Fin 2 → ℕ) :
    ∀ p : ℕ,
    (evalM E).Steps w (((gc, some c, gb), .candCarry r, reg),
        hpos s cu (Function.update ca ⟨r.val - 1, by have := r.2; omega⟩ p) be, cnt) []
      (((gc, some c, gb), .candNext ⟨r.val - 1, by have := r.2; omega⟩, reg),
        hpos s cu (Function.update ca ⟨r.val - 1, by have := r.2; omega⟩ 1) be, cnt) := by
  intro p
  induction p with
  | zero =>
      -- at `⊢`: move to `candCarry2`, then step right onto cell 1
      have hstep1 : (evalM E).Steps w (((gc, some c, gb), .candCarry r, reg),
          hpos s cu (Function.update ca ⟨r.val - 1, by have := r.2; omega⟩ 0) be, cnt) []
          (((gc, some c, gb), .candCarry2 r, reg),
          hpos s cu (Function.update ca ⟨r.val - 1, by have := r.2; omega⟩ 0) be, cnt) := by
        refine stepRaw E (u := []) (out := []) (mv := mvStay) (ops := opsKeep) ?_ ?_
          (apply_mvStay _) (apply_opsKeep _) (stepsRefl E _)
        · simp only [rawEta]
          rw [dif_pos hr]
          rw [show tapeSym w (hpos s cu
              (Function.update ca ⟨r.val - 1, by have := r.2; omega⟩ 0) be
              (candH ⟨r.val - 1, by have := r.2; omega⟩)) = TapeSym.lmark from by
            rw [hpos_candH, Function.update_self]
            exact tapeSym_zero w]
        · intro a0 hmv
          cases hmv
      have hstep2 : (evalM E).Steps w (((gc, some c, gb), .candCarry2 r, reg),
          hpos s cu (Function.update ca ⟨r.val - 1, by have := r.2; omega⟩ 0) be, cnt) []
          (((gc, some c, gb), .candNext ⟨r.val - 1, by have := r.2; omega⟩, reg),
          hpos s cu (Function.update ca ⟨r.val - 1, by have := r.2; omega⟩ 1) be, cnt) := by
        refine stepRaw E (u := []) (out := [])
          (mv := mvOne (candH ⟨r.val - 1, by have := r.2; omega⟩) .right)
          (ops := opsKeep) ?_ ?_ ?_ (apply_opsKeep _) (stepsRefl E _)
        · simp only [rawEta]
          rw [dif_pos hr]
        · intro a0 hmv
          simp only [mvOne] at hmv
          split at hmv
          · rename_i ha0
            subst ha0
            rw [hpos_candH, Function.update_self]
            rw [tapeSym_zero]
            intro hc
            cases hc
          · cases hmv
        · rw [apply_mvOne, hpos_candH, update_hpos_candH, Function.update_self,
            Function.update_idem]
          rfl
      exact stepsTrans E (o₁ := []) (o₂ := []) hstep1 hstep2
  | succ p ih =>
      refine stepRaw E (u := []) (out := [])
        (mv := mvOne (candH ⟨r.val - 1, by have := r.2; omega⟩) .left)
        (ops := opsKeep) ?_ ?_ ?_ (apply_opsKeep _) ih
      · simp only [rawEta]
        rw [dif_pos hr]
        rw [show tapeSym w (hpos s cu
            (Function.update ca ⟨r.val - 1, by have := r.2; omega⟩ (p + 1)) be
            (candH ⟨r.val - 1, by have := r.2; omega⟩)) = tapeSym w (p + 1) from by
          rw [hpos_candH, Function.update_self]]
        cases hcase : tapeSym w (p + 1) with
        | lmark =>
            exact absurd ((tapeSym_eq_lmark_iff w (p + 1)).mp hcase) (by omega)
        | letter aa => rfl
        | rmark => rfl
      · intro a0 hmv
        simp only [mvOne] at hmv
        split at hmv <;> cases hmv
      · rw [apply_mvOne, hpos_candH, Function.update_self, update_hpos_candH,
          Function.update_idem]
        rfl

/-- Zero out all coordinates from `r` upward. -/
def resetAbove {k : ℕ} (t : Fin k → ℕ) (r : ℕ) : Fin k → ℕ :=
  fun x => if x.val < r then t x else 0

omit [Fintype Gamma] in
theorem resetAbove_all {k : ℕ} (t : Fin k → ℕ) : resetAbove t k = t := by
  funext x
  rw [resetAbove, if_pos x.2]

omit [Fintype Gamma] in
theorem resetAbove_zero {k : ℕ} (t : Fin k → ℕ) :
    resetAbove t 0 = fun _ => 0 := by
  funext x
  rw [resetAbove, if_neg (by omega)]

/-- **The candidate-successor gadget**: from `candNext` at coordinate `r`, the
machine reaches the next candidate's selection sweep, or exhausts the copy and
parks. -/
theorem candNext_run {w : List Step} (c : Fin P.toPoly.K)
    (gc gb : Option (Fin P.toPoly.K)) (reg : Reg E)
    (cu be : Fin (kmaxP P) → ℕ) (cnt : Fin 2 → ℕ)
    (t : Fin (P.toPoly.arity c) → ℕ) (hv : ∀ x, t x < w.length) :
    ∀ (r : ℕ) (hrar : r ≤ P.toPoly.arity c),
    (evalM E).Steps w
      (((gc, some c, gb), .candNext ⟨r, by
          have := arity_le_kmax (P := P) c; omega⟩, reg),
        hpos 0 cu (pad c (resetAbove t r)) be, cnt) []
      (match succAux w.length (P.toPoly.arity c) t r with
       | some t' => (((gc, some c, gb), .sweep (.sel c) .selK, reg),
           hpos 0 cu (pad c t') be, cnt)
       | none => (((gc, some c, gb), .walk .parkCand, reg),
           hpos 0 cu (pad c (fun _ => 0)) be, cnt)) := by
  intro r
  induction r with
  | zero =>
      intro hrar
      rw [show succAux w.length (P.toPoly.arity c) t 0 = none from rfl]
      rw [resetAbove_zero]
      exact step_candNext_zero E c _ (by show ¬ (0 < (0 : ℕ)); omega) gc gb reg _ cnt
  | succ r ih =>
      intro hrar
      have hrk : r < P.toPoly.arity c := by omega
      have hark := arity_le_kmax (P := P) c
      -- the tag coordinate index is r
      have hidx : ((⟨r + 1, by omega⟩ : Fin (kmaxP P + 1)).val - 1) = r := rfl
      -- current cell of coordinate r in the reset tuple
      have hcell : pad c (resetAbove t (r + 1)) ⟨r, by omega⟩ = t ⟨r, hrk⟩ + 1 := by
        rw [pad, dif_pos hrk]
        rw [show resetAbove t (r + 1) ⟨r, hrk⟩ = t ⟨r, hrk⟩ from by
          rw [resetAbove]
          rw [if_pos (show ((⟨r, hrk⟩ : Fin (P.toPoly.arity c)).val < r + 1) from
            Nat.lt_succ_self r)]]
      have hstep1 : (evalM E).Steps w
          (((gc, some c, gb), .candNext ⟨r + 1, by omega⟩, reg),
            hpos 0 cu (pad c (resetAbove t (r + 1))) be, cnt) []
          (((gc, some c, gb), .candNext2 ⟨r + 1, by omega⟩, reg),
            hpos 0 cu (Function.update (pad c (resetAbove t (r + 1))) ⟨r, by omega⟩
              (pad c (resetAbove t (r + 1)) ⟨r, by omega⟩ + 1)) be, cnt) :=
        step_candNext_pos E (w := w) c ⟨r + 1, by omega⟩
          (by show 0 < r + 1; omega) gc gb reg 0 cu (pad c (resetAbove t (r + 1))) be cnt
          (by
            show tapeSym w (pad c (resetAbove t (r + 1)) ⟨r, by omega⟩) ≠ TapeSym.rmark
            rw [hcell]
            refine tapeSym_ne_rmark_of_le ?_
            have := hv ⟨r, hrk⟩
            omega)
      rw [succAux]
      rw [dif_pos hrk]
      by_cases hlt : t ⟨r, hrk⟩ + 1 < w.length
      · rw [if_pos hlt]
        -- the incremented head sits on a letter: new candidate found
        have hupd : Function.update (pad c (resetAbove t (r + 1))) ⟨r, by omega⟩
              (pad c (resetAbove t (r + 1)) ⟨r, by omega⟩ + 1)
            = pad c (fun x => if x.val < r then t x else
                if x.val = r then t ⟨r, hrk⟩ + 1 else 0) := by
          funext x
          by_cases hx : x = (⟨r, by omega⟩ : Fin (kmaxP P))
          · subst hx
            rw [Function.update_self, hcell, pad, dif_pos hrk]
            rw [show (if (r : ℕ) < r then t ⟨r, hrk⟩ else
                if (r : ℕ) = r then t ⟨r, hrk⟩ + 1 else 0) = t ⟨r, hrk⟩ + 1 from by
              rw [if_neg (by omega), if_pos rfl]]
          · rw [Function.update_of_ne hx, pad, pad]
            by_cases hxa : x.val < P.toPoly.arity c
            · rw [dif_pos hxa, dif_pos hxa]
              have hxr : x.val ≠ r := by
                intro hc
                exact hx (Fin.ext hc)
              rw [resetAbove]
              by_cases hxlt : x.val < r
              · rw [if_pos (by omega : x.val < r + 1), if_pos hxlt]
              · rw [if_neg (by omega : ¬ (x.val < r + 1)), if_neg hxlt,
                  if_neg hxr]
            · rw [dif_neg hxa, dif_neg hxa]
        rw [hupd] at hstep1
        have hstep2 := (step_candNext2 E (w := w) c ⟨r + 1, by omega⟩
          (by show 0 < r + 1; omega)
          gc gb reg 0 cu (pad c (fun x => if x.val < r then t x else
            if x.val = r then t ⟨r, hrk⟩ + 1 else 0)) be cnt).1
          w[t ⟨r, hrk⟩ + 1]
          (by
            show tapeSym w (pad c (fun x => if x.val < r then t x else
              if x.val = r then t ⟨r, hrk⟩ + 1 else 0) ⟨r, by omega⟩)
              = TapeSym.letter w[t ⟨r, hrk⟩ + 1]
            rw [show pad c (fun x => if x.val < r then t x else
                if x.val = r then t ⟨r, hrk⟩ + 1 else 0) ⟨r, by omega⟩
              = t ⟨r, hrk⟩ + 2 from by
                rw [pad, dif_pos hrk]
                rw [show (if (r : ℕ) < r then t ⟨r, hrk⟩ else
                  if (r : ℕ) = r then t ⟨r, hrk⟩ + 1 else 0) = t ⟨r, hrk⟩ + 1 from by
                  rw [if_neg (by omega), if_pos rfl]]]
            exact tapeSym_succ w (t ⟨r, hrk⟩ + 1) hlt)
        exact stepsTrans E (o₁ := []) (o₂ := []) hstep1 hstep2
      · rw [if_neg hlt]
        -- carry: the head hits the right marker
        have hn : t ⟨r, hrk⟩ + 1 = w.length := by
          have := hv ⟨r, hrk⟩
          omega
        have hupd : Function.update (pad c (resetAbove t (r + 1))) ⟨r, by omega⟩
              (pad c (resetAbove t (r + 1)) ⟨r, by omega⟩ + 1)
            = Function.update (pad c (resetAbove t (r + 1))) ⟨r, by omega⟩
              (w.length + 1) := by
          rw [hcell]
          rw [show t ⟨r, hrk⟩ + 1 + 1 = w.length + 1 from by omega]
        rw [hupd] at hstep1
        have hstep2 := (step_candNext2 E (w := w) c ⟨r + 1, by omega⟩
          (by show 0 < r + 1; omega)
          gc gb reg 0 cu (Function.update (pad c (resetAbove t (r + 1)))
            ⟨r, by omega⟩ (w.length + 1)) be cnt).2
          (by
            show tapeSym w (Function.update (pad c (resetAbove t (r + 1)))
              ⟨r, by omega⟩ (w.length + 1) ⟨r, by omega⟩) = TapeSym.rmark
            rw [Function.update_self]
            exact tapeSym_ge w (w.length + 1) (by omega))
        have hstep3 : (evalM E).Steps w
            (((gc, some c, gb), .candCarry ⟨r + 1, by omega⟩, reg),
              hpos 0 cu (Function.update (pad c (resetAbove t (r + 1)))
                ⟨r, by omega⟩ (w.length + 1)) be, cnt) []
            (((gc, some c, gb), .candNext ⟨r, by omega⟩, reg),
              hpos 0 cu (Function.update (pad c (resetAbove t (r + 1)))
                ⟨r, by omega⟩ 1) be, cnt) :=
          carry_walk E (w := w) c ⟨r + 1, by omega⟩ (by show 0 < r + 1; omega)
            gc gb reg 0 cu (pad c (resetAbove t (r + 1))) be cnt (w.length + 1)
        -- the reset head on cell 1 is the padded reset tuple at r
        have hreset : Function.update (pad c (resetAbove t (r + 1)))
              ⟨r, by omega⟩ 1 = pad c (resetAbove t r) := by
          funext x
          by_cases hx : x = (⟨r, by omega⟩ : Fin (kmaxP P))
          · subst hx
            rw [Function.update_self, pad, dif_pos hrk]
            rw [show resetAbove t r ⟨r, hrk⟩ = 0 from by
              rw [resetAbove]
              rw [if_neg (show ¬ ((⟨r, hrk⟩ : Fin (P.toPoly.arity c)).val < r) from
                Nat.lt_irrefl r)]]
          · rw [Function.update_of_ne hx, pad, pad]
            by_cases hxa : x.val < P.toPoly.arity c
            · rw [dif_pos hxa, dif_pos hxa]
              have hxr : x.val ≠ r := by
                intro hc
                exact hx (Fin.ext hc)
              rw [resetAbove, resetAbove]
              by_cases hxlt : x.val < r
              · rw [if_pos (by omega : x.val < r + 1), if_pos hxlt]
              · rw [if_neg (by omega : ¬ (x.val < r + 1)), if_neg hxlt]
            · rw [dif_neg hxa, dif_neg hxa]
        rw [hreset] at hstep3
        have hnext := ih (by omega)
        have hall := stepsTrans E hstep1 (stepsTrans E hstep2
          (stepsTrans E hstep3 hnext))
        simpa using hall

end CandGadgets

/-! ## §16 The candidate test -/

section CandTest

open TupEnum

/-- Glob of an optional-atom pair of blocks. -/
def globOf (curA bestA : Option P.toPoly.Atom) (ca : Option (Fin P.toPoly.K)) :
    Glob P.toPoly.K :=
  (curA.map Sigma.fst, ca, bestA.map Sigma.fst)

omit [Fintype Gamma] in
theorem copyBest_partner_notin : ∀ a : Fin (hN P), wkIn (P := P) .copyBest a.val →
    ¬ wkIn (P := P) .copyBest (wkPartner (P := P) .copyBest a).val := by
  intro a ha hc
  rw [wkIn, wkLo, wkHi] at ha hc
  rw [wkPartner] at hc
  revert hc
  show ¬ (1 + 2 * kmaxP P ≤ a.val - kmaxP P ∧ a.val - kmaxP P < 1 + 3 * kmaxP P)
  have := a.2
  omega

omit [Fintype Gamma] in
theorem copyCur_partner_notin : ∀ a : Fin (hN P), wkIn (P := P) .copyCur a.val →
    ¬ wkIn (P := P) .copyCur (wkPartner (P := P) .copyCur a).val := by
  intro a ha hc
  rw [wkIn, wkLo, wkHi] at ha hc
  rw [wkPartner] at hc
  by_cases hb : a.val + 2 * kmaxP P < hN P
  · rw [dif_pos hb] at hc
    revert hc
    show ¬ (1 ≤ a.val + 2 * kmaxP P ∧ a.val + 2 * kmaxP P < 1 + kmaxP P)
    omega
  · exfalso
    apply hb
    show a.val + 2 * kmaxP P < 3 * kmaxP P + 1
    omega

/-- Park the BEST block and copy the CAND block onto it. -/
theorem copyBestSeq_run {w : List Step} (c : Fin P.toPoly.K)
    (t : Fin (P.toPoly.arity c) → ℕ) (hv : ∀ x, t x < w.length)
    (gc gbOld : Option (Fin P.toPoly.K)) (be : Fin (kmaxP P) → ℕ) (reg : Reg E)
    (cu : Fin (kmaxP P) → ℕ) :
    (evalM E).Steps w
      (((gc, some c, gbOld), .walk .parkBest, reg), hpos 0 cu (pad c t) be, c2 0 0) []
      (((gc, some c, some c), .candNext
          ⟨P.toPoly.arity c, Nat.lt_succ_of_le (arity_le_kmax c)⟩, reg),
        hpos 0 cu (pad c t) (pad c t), c2 0 0) := by
  have hpark := walk_park_run E .parkBest rfl (w := w)
    (g := (gc, some c, gbOld)) (g' := (gc, some c, gbOld)) (t' := .walk .copyBest)
    (reg := reg) (cnt := c2 0 0) rfl (hpos 0 cu (pad c t) be)
  rw [walkRes_parkBest] at hpark
  have hcopy := walk_copy_run E .copyBest rfl (w := w)
    (g := (gc, some c, gbOld)) (g' := (gc, some c, some c))
    (t' := .candNext ⟨P.toPoly.arity c, Nat.lt_succ_of_le (arity_le_kmax c)⟩)
    (reg := reg) (cnt := c2 0 0) copyBest_partner_notin rfl
    (hpos 0 cu (pad c t) (fun _ => 0))
    (by
      intro a ha
      have hint : 1 + 2 * kmaxP P ≤ a.val ∧ a.val < 1 + 3 * kmaxP P := by
        rw [wkIn, wkLo, wkHi] at ha
        exact ha
      obtain ⟨h1, h2⟩ := hint
      have hxeq : a = bestH ⟨a.val - 1 - 2 * kmaxP P, by omega⟩ := by
        refine Fin.ext ?_
        show a.val = 1 + 2 * kmaxP P + (a.val - 1 - 2 * kmaxP P)
        omega
      rw [hxeq, hpos_bestH]
      exact Nat.zero_le _)
    (by
      intro a ha
      have hint : 1 + 2 * kmaxP P ≤ a.val ∧ a.val < 1 + 3 * kmaxP P := by
        rw [wkIn, wkLo, wkHi] at ha
        exact ha
      obtain ⟨h1, h2⟩ := hint
      have hpeq : wkPartner (P := P) .copyBest a
          = candH ⟨a.val - 1 - 2 * kmaxP P, by omega⟩ := by
        rw [wkPartner, candH]
        refine Fin.ext ?_
        show a.val - kmaxP P = 1 + kmaxP P + (a.val - 1 - 2 * kmaxP P)
        omega
      rw [hpeq, hpos_candH]
      have := pad_le c hv ⟨a.val - 1 - 2 * kmaxP P, by omega⟩
      omega)
  rw [walkRes_copyBest] at hcopy
  exact stepsTrans E (o₁ := []) (o₂ := []) hpark hcopy

/-- **The candidate test**: from the selection sweep of candidate `(c, t)` the
machine updates the best-so-far atom by `bestStep` and reaches the
candidate-successor entry. -/
theorem candTest_run {w : List Step} (c : Fin P.toPoly.K)
    (t : Fin (P.toPoly.arity c) → ℕ) (hv : ∀ x, t x < w.length)
    (curA bestA : Option P.toPoly.Atom)
    (hcurv : ∀ a ∈ curA, ∀ x, a.2 x < w.length)
    (hbestv : ∀ a ∈ bestA, ∀ x, a.2 x < w.length)
    (reg : Reg E) :
    ∃ regF : Reg E,
    (evalM E).Steps w
      ((globOf (P := P) curA bestA (some c), .sweep (.sel c) .selK, reg),
        hpos 0 (padO curA) (pad c t) (padO bestA), c2 0 0) []
      ((globOf (P := P) curA (bestStep P w curA bestA ⟨c, t⟩) (some c),
          .candNext ⟨P.toPoly.arity c, Nat.lt_succ_of_le (arity_le_kmax c)⟩, regF),
        hpos 0 (padO curA) (pad c t) (padO (bestStep P w curA bestA ⟨c, t⟩)),
        c2 0 0) := by
  have hark := arity_le_kmax (P := P) c
  -- the selection sweep
  obtain ⟨b1, reg1, hb1, hrun1⟩ := sweep_run E (w := w) (.sel c) .selK
    (g := globOf (P := P) curA bestA (some c)) reg
    (pos := hpos 0 (padO curA) (pad c t) (padO bestA)) (cnt := c2 0 0) t
    (hpos_scanH _ _ _ _)
    (fun i => by
      show hpos 0 (padO curA) (pad c t) (padO bestA) (candH (embedA i)) = t i + 1
      rw [hpos_candH]
      exact pad_embedA _ _ _)
  have hb1' : b1 = true ↔ P.toPoly.sel c w t := by
    rw [hb1]
    exact E.hsel c w t hv
  -- selected ↔ machine bit (the tuple is in range)
  have hselX : b1 = true ↔ P.toPoly.selectedAtom w ⟨c, t⟩ := by
    rw [hb1']
    constructor
    · intro hs
      exact ⟨hv, hs⟩
    · intro hs
      exact hs.2
  by_cases hsel : P.toPoly.selectedAtom w ⟨c, t⟩
  case neg =>
    -- not selected: the sweep dispatches straight to the successor
    have hb1f : b1 = false := by
      cases hb : b1
      · rfl
      · exact absurd (hselX.mp hb) hsel
    subst hb1f
    have hbs : bestStep P w curA bestA ⟨c, t⟩ = bestA := by
      rw [bestStep, if_neg]
      intro hc
      exact hsel hc.1.1
    rw [hbs]
    refine ⟨reg1, ?_⟩
    refine hrun1 ?_
    show contStep E .selK false (globOf (P := P) curA bestA (some c)) = _
    rw [contStep]
    rw [if_neg (show ¬ (false = true) by simp)]
    rw [show candNextEntry E (globOf (P := P) curA bestA (some c))
        = some (.candNext ⟨P.toPoly.arity c, Nat.lt_succ_of_le (arity_le_kmax c)⟩)
      from rfl]
    rfl
  case pos =>
  have hb1t : b1 = true := hselX.mpr hsel
  subst hb1t
  cases curA with
  | none =>
      cases bestA with
      | none =>
          have hbs : bestStep P w none none ⟨c, t⟩ = some ⟨c, t⟩ := by
            rw [bestStep, if_pos]
            constructor
            · exact ⟨hsel, by simp⟩
            · simp
          rw [hbs]
          have h1 := hrun1 (show contStep E .selK true
            (globOf (P := P) none none (some c))
            = some (globOf (P := P) none none (some c), .walk .parkBest, []) from rfl)
          have h2 := copyBestSeq_run E c t hv none none
            (padO (P := P) none) reg1 (padO (P := P) none)
          refine ⟨reg1, ?_⟩
          have hall := stepsTrans E (o₁ := []) (o₂ := []) h1 h2
          exact hall
      | some bA =>
          obtain ⟨V, regC, hViff, hVrun⟩ := cmp_run E .candBest c bA.1
            (g := globOf (P := P) none (some bA) (some c))
            (pos := hpos 0 (padO (P := P) none) (pad c t) (padO (some bA)))
            t bA.2 hv (hbestv bA rfl)
            (fun rr => by
              show hpos 0 (padO (P := P) none) (pad c t) (padO (some bA))
                (candH (embedA rr)) = t rr + 1
              rw [hpos_candH, pad_embedA])
            (fun rr => by
              show hpos 0 (padO (P := P) none) (pad c t) (padO (some bA))
                (bestH (embedA rr)) = bA.2 rr + 1
              rw [hpos_bestH]
              show pad bA.1 bA.2 (embedA rr) = bA.2 rr + 1
              rw [pad_embedA])
            (hpos_scanH _ _ _ _) reg1
          have h1 := hrun1 (show contStep E .selK true
            (globOf (P := P) none (some bA) (some c))
            = some (globOf (P := P) none (some bA) (some c),
                cmpEntryTag E .candBest c bA.1, []) from rfl)
          by_cases hXb : P.wrpOrd w ⟨c, t⟩ bA
          · have hVt : V = true := hViff.mpr hXb
            subst hVt
            have h2 := hVrun (show cmpExit E .candBest true
              (globOf (P := P) none (some bA) (some c))
              = some (.walk .parkBest) from rfl)
            have hbs : bestStep P w none (some bA) ⟨c, t⟩ = some ⟨c, t⟩ := by
              rw [bestStep, if_pos]
              constructor
              · exact ⟨hsel, by simp⟩
              · intro b hb
                rw [Option.mem_def, Option.some.injEq] at hb
                subst hb
                exact hXb
            rw [hbs]
            have h3 := copyBestSeq_run E c t hv none (some bA.1)
              (padO (some bA)) regC (padO (P := P) none)
            refine ⟨regC, ?_⟩
            have hall := stepsTrans E (o₁ := []) (o₂ := [])
              h1 (stepsTrans E (o₁ := []) (o₂ := []) h2 h3)
            exact hall
          · have hVf : V = false := by
              cases hV : V
              · rfl
              · exact absurd (hViff.mp hV) hXb
            subst hVf
            have h2 := hVrun (show cmpExit E .candBest false
              (globOf (P := P) none (some bA) (some c))
              = some (.candNext ⟨P.toPoly.arity c,
                  Nat.lt_succ_of_le (arity_le_kmax c)⟩) from rfl)
            have hbs : bestStep P w none (some bA) ⟨c, t⟩ = some bA := by
              rw [bestStep, if_neg]
              intro hcond
              exact hXb (hcond.2 bA rfl)
            rw [hbs]
            refine ⟨regC, ?_⟩
            have hall := stepsTrans E (o₁ := []) (o₂ := []) h1 h2
            exact hall
  | some cA =>
      obtain ⟨V0, regC0, hV0iff, hV0run⟩ := cmp_run E .curCand cA.1 c
        (g := globOf (P := P) (some cA) bestA (some c))
        (pos := hpos 0 (padO (some cA)) (pad c t) (padO bestA))
        cA.2 t (hcurv cA rfl) hv
        (fun rr => by
          show hpos 0 (padO (some cA)) (pad c t) (padO bestA)
            (curH (embedA rr)) = cA.2 rr + 1
          rw [hpos_curH]
          show pad cA.1 cA.2 (embedA rr) = cA.2 rr + 1
          rw [pad_embedA])
        (fun rr => by
          show hpos 0 (padO (some cA)) (pad c t) (padO bestA)
            (candH (embedA rr)) = t rr + 1
          rw [hpos_candH, pad_embedA])
        (hpos_scanH _ _ _ _) reg1
      have h1 := hrun1 (show contStep E .selK true
        (globOf (P := P) (some cA) bestA (some c))
        = some (globOf (P := P) (some cA) bestA (some c),
            cmpEntryTag E .curCand cA.1 c, []) from rfl)
      by_cases hcx : P.wrpOrd w cA ⟨c, t⟩
      · have hV0t : V0 = true := hV0iff.mpr hcx
        subst hV0t
        cases bestA with
        | none =>
            have h2 := hV0run (show cmpExit E .curCand true
              (globOf (P := P) (some cA) none (some c))
              = some (.walk .parkBest) from rfl)
            have hbs : bestStep P w (some cA) none ⟨c, t⟩ = some ⟨c, t⟩ := by
              rw [bestStep, if_pos]
              constructor
              · refine ⟨hsel, ?_⟩
                intro a ha
                rw [Option.mem_def, Option.some.injEq] at ha
                subst ha
                exact hcx
              · simp
            rw [hbs]
            have h3 := copyBestSeq_run E c t hv (some cA.1) none
              (padO (P := P) none) regC0 (padO (some cA))
            refine ⟨regC0, ?_⟩
            exact stepsTrans E (o₁ := []) (o₂ := [])
              h1 (stepsTrans E (o₁ := []) (o₂ := []) h2 h3)
        | some bA =>
            have h2 := hV0run (show cmpExit E .curCand true
              (globOf (P := P) (some cA) (some bA) (some c))
              = some (cmpEntryTag E .candBest c bA.1) from rfl)
            obtain ⟨V, regC, hViff, hVrun⟩ := cmp_run E .candBest c bA.1
              (g := globOf (P := P) (some cA) (some bA) (some c))
              (pos := hpos 0 (padO (some cA)) (pad c t) (padO (some bA)))
              t bA.2 hv (hbestv bA rfl)
              (fun rr => by
                show hpos 0 (padO (some cA)) (pad c t) (padO (some bA))
                  (candH (embedA rr)) = t rr + 1
                rw [hpos_candH, pad_embedA])
              (fun rr => by
                show hpos 0 (padO (some cA)) (pad c t) (padO (some bA))
                  (bestH (embedA rr)) = bA.2 rr + 1
                rw [hpos_bestH]
                show pad bA.1 bA.2 (embedA rr) = bA.2 rr + 1
                rw [pad_embedA])
              (hpos_scanH _ _ _ _) regC0
            by_cases hXb : P.wrpOrd w ⟨c, t⟩ bA
            · have hVt : V = true := hViff.mpr hXb
              subst hVt
              have h3 := hVrun (show cmpExit E .candBest true
                (globOf (P := P) (some cA) (some bA) (some c))
                = some (.walk .parkBest) from rfl)
              have hbs : bestStep P w (some cA) (some bA) ⟨c, t⟩ = some ⟨c, t⟩ := by
                rw [bestStep, if_pos]
                constructor
                · refine ⟨hsel, ?_⟩
                  intro a ha
                  rw [Option.mem_def, Option.some.injEq] at ha
                  subst ha
                  exact hcx
                · intro b hb
                  rw [Option.mem_def, Option.some.injEq] at hb
                  subst hb
                  exact hXb
              rw [hbs]
              have h4 := copyBestSeq_run E c t hv (some cA.1) (some bA.1)
                (padO (some bA)) regC (padO (some cA))
              refine ⟨regC, ?_⟩
              exact stepsTrans E (o₁ := []) (o₂ := []) h1
                (stepsTrans E (o₁ := []) (o₂ := []) h2
                  (stepsTrans E (o₁ := []) (o₂ := []) h3 h4))
            · have hVf : V = false := by
                cases hV : V
                · rfl
                · exact absurd (hViff.mp hV) hXb
              subst hVf
              have h3 := hVrun (show cmpExit E .candBest false
                (globOf (P := P) (some cA) (some bA) (some c))
                = some (.candNext ⟨P.toPoly.arity c,
                    Nat.lt_succ_of_le (arity_le_kmax c)⟩) from rfl)
              have hbs : bestStep P w (some cA) (some bA) ⟨c, t⟩ = some bA := by
                rw [bestStep, if_neg]
                intro hcond
                exact hXb (hcond.2 bA rfl)
              rw [hbs]
              refine ⟨regC, ?_⟩
              exact stepsTrans E (o₁ := []) (o₂ := []) h1
                (stepsTrans E (o₁ := []) (o₂ := []) h2 h3)
      · have hV0f : V0 = false := by
          cases hV : V0
          · rfl
          · exact absurd (hV0iff.mp hV) hcx
        subst hV0f
        have h2 := hV0run (show cmpExit E .curCand false
          (globOf (P := P) (some cA) bestA (some c))
          = some (.candNext ⟨P.toPoly.arity c,
              Nat.lt_succ_of_le (arity_le_kmax c)⟩) from rfl)
        have hbs : bestStep P w (some cA) bestA ⟨c, t⟩ = bestA := by
          rw [bestStep, if_neg]
          intro hcond
          exact hcx (hcond.1.2 cA rfl)
        rw [hbs]
        refine ⟨regC0, ?_⟩
        exact stepsTrans E (o₁ := []) (o₂ := []) h1 h2

end CandTest

/-! ## §17 Copy loop and the round's copy sweep -/

section CopyLoop

open TupEnum

omit [Fintype Gamma] in
/-- Validity is preserved by the best-so-far update. -/
theorem bestStep_valid {w : List Step} {curA bestA : Option P.toPoly.Atom}
    {X : P.toPoly.Atom} (hbestv : ∀ a ∈ bestA, ∀ x, a.2 x < w.length)
    (hX : ∀ x, X.2 x < w.length) :
    ∀ a ∈ bestStep P w curA bestA X, ∀ x, a.2 x < w.length := by
  intro a ha
  rw [bestStep] at ha
  split at ha
  · rw [Option.mem_def, Option.some.injEq] at ha
    subst ha
    exact hX
  · exact hbestv a ha

/-- **The candidate loop of one copy**: fold `bestStep` over the successor
orbit, ending parked with the copy exhausted. -/
theorem copyLoop_run {w : List Step} (c : Fin P.toPoly.K)
    (curA : Option P.toPoly.Atom)
    (hcurv : ∀ a ∈ curA, ∀ x, a.2 x < w.length) :
    ∀ (f : ℕ) (t : Fin (P.toPoly.arity c) → ℕ) (bestA : Option P.toPoly.Atom)
      (reg : Reg E),
    (∀ x, t x < w.length) →
    (∀ a ∈ bestA, ∀ x, a.2 x < w.length) →
    OrbitEnds w.length (P.toPoly.arity c) f t →
    ∃ regF : Reg E,
    (evalM E).Steps w
      ((globOf (P := P) curA bestA (some c), .sweep (.sel c) .selK, reg),
        hpos 0 (padO curA) (pad c t) (padO bestA), c2 0 0) []
      ((globOf (P := P) curA
          ((tupOrbit w.length (P.toPoly.arity c) f t).foldl
            (fun acc tt => bestStep P w curA acc ⟨c, tt⟩) bestA) (some c),
        .walk .parkCand, regF),
        hpos 0 (padO curA)
          (pad c (fun _ => 0))
          (padO ((tupOrbit w.length (P.toPoly.arity c) f t).foldl
            (fun acc tt => bestStep P w curA acc ⟨c, tt⟩) bestA)), c2 0 0) := by
  intro f
  induction f with
  | zero =>
      intro t bestA reg hval hbestv hEnds
      rw [show tupOrbit w.length (P.toPoly.arity c) 0 t = [t] from rfl]
      rw [List.foldl_cons, List.foldl_nil]
      obtain ⟨regT, hTest⟩ := candTest_run E c t hval curA bestA hcurv hbestv reg
      have hNext := candNext_run E (w := w) c (curA.map Sigma.fst)
        ((bestStep P w curA bestA ⟨c, t⟩).map Sigma.fst) regT
        (padO curA) (padO (bestStep P w curA bestA ⟨c, t⟩)) (c2 0 0) t hval
        (P.toPoly.arity c) le_rfl
      rw [resetAbove_all] at hNext
      rw [OrbitEnds] at hEnds
      rw [show tupSucc w.length (P.toPoly.arity c) t
        = succAux w.length (P.toPoly.arity c) t (P.toPoly.arity c) from rfl] at hEnds
      rw [hEnds] at hNext
      refine ⟨regT, ?_⟩
      have hall := stepsTrans E (o₁ := []) (o₂ := []) hTest hNext
      exact hall
  | succ f ih =>
      intro t bestA reg hval hbestv hEnds
      obtain ⟨regT, hTest⟩ := candTest_run E c t hval curA bestA hcurv hbestv reg
      have hNext := candNext_run E (w := w) c (curA.map Sigma.fst)
        ((bestStep P w curA bestA ⟨c, t⟩).map Sigma.fst) regT
        (padO curA) (padO (bestStep P w curA bestA ⟨c, t⟩)) (c2 0 0) t hval
        (P.toPoly.arity c) le_rfl
      rw [resetAbove_all] at hNext
      rw [OrbitEnds] at hEnds
      cases hsucc : tupSucc w.length (P.toPoly.arity c) t with
      | none =>
          rw [show succAux w.length (P.toPoly.arity c) t (P.toPoly.arity c)
            = tupSucc w.length (P.toPoly.arity c) t from rfl, hsucc] at hNext
          simp only [tupOrbit, hsucc]
          rw [List.foldl_cons, List.foldl_nil]
          refine ⟨regT, ?_⟩
          exact stepsTrans E (o₁ := []) (o₂ := []) hTest hNext
      | some t2 =>
          rw [hsucc] at hEnds
          rw [show succAux w.length (P.toPoly.arity c) t (P.toPoly.arity c)
            = tupSucc w.length (P.toPoly.arity c) t from rfl, hsucc] at hNext
          have hval2 : ∀ x, t2 x < w.length :=
            succAux_valid w.length (P.toPoly.arity c) hval hsucc
          obtain ⟨regF, hRest⟩ := ih t2 (bestStep P w curA bestA ⟨c, t⟩) regT hval2
            (bestStep_valid hbestv hval) hEnds
          simp only [tupOrbit, hsucc]
          rw [List.foldl_cons]
          refine ⟨regF, ?_⟩
          exact stepsTrans E (o₁ := []) (o₂ := []) hTest
            (stepsTrans E (o₁ := []) (o₂ := []) hNext hRest)

/-- The candidate tuples of one copy (empty when the copy has positive arity
on the empty word). -/
def copyCands (n : ℕ) (c : Fin P.toPoly.K) : List (Fin (P.toPoly.arity c) → ℕ) :=
  if P.toPoly.arity c = 0 ∨ 0 < n then
    tupOrbit n (P.toPoly.arity c)
      (Fintype.card (Fin (P.toPoly.arity c) → Fin n)) (fun _ => 0)
  else []

omit [Fintype Gamma] in
theorem orbitEnds_of_arity_zero {n k F : ℕ} (hk : k = 0) (t : Fin k → ℕ) :
    OrbitEnds n k F t := by
  subst hk
  have hnone : tupSucc n 0 t = none := rfl
  cases F with
  | zero => exact hnone
  | succ F =>
      rw [OrbitEnds, hnone]
      exact trivial

omit [Fintype Gamma] in
theorem pad_of_arity_zero {c : Fin P.toPoly.K} (h : P.toPoly.arity c = 0)
    (t : Fin (P.toPoly.arity c) → ℕ) : pad c t = fun _ => 0 := by
  funext r
  rw [pad, dif_neg (by omega)]

omit [Fintype Gamma] in
theorem candInitBlock_eq_pad (c : Fin P.toPoly.K) :
    (fun rr : Fin (kmaxP P) => if rr.val < P.toPoly.arity c
      then (fun _ : Fin (kmaxP P) => 0) rr + 1 else (fun _ : Fin (kmaxP P) => 0) rr)
    = pad c (fun _ => 0) := by
  funext rr
  rw [pad]
  by_cases h : rr.val < P.toPoly.arity c
  · rw [if_pos h, dif_pos h]
  · rw [if_neg h, dif_neg h]

/-- **One whole copy**: from `candInit`, fold `bestStep` over the copy's
candidates and end parked with the copy exhausted. -/
theorem copyEntry_run {w : List Step} (c : Fin P.toPoly.K)
    (curA bestA : Option P.toPoly.Atom)
    (hcurv : ∀ a ∈ curA, ∀ x, a.2 x < w.length)
    (hbestv : ∀ a ∈ bestA, ∀ x, a.2 x < w.length) (reg : Reg E) :
    ∃ regF : Reg E,
    (evalM E).Steps w
      ((globOf (P := P) curA bestA (some c), .candInit, reg),
        hpos 0 (padO curA) (fun _ => 0) (padO bestA), c2 0 0) []
      ((globOf (P := P) curA
          ((copyCands (P := P) w.length c).foldl
            (fun acc tt => bestStep P w curA acc ⟨c, tt⟩) bestA) (some c),
        .walk .parkCand, regF),
        hpos 0 (padO curA) (pad c (fun _ => 0))
          (padO ((copyCands (P := P) w.length c).foldl
            (fun acc tt => bestStep P w curA acc ⟨c, tt⟩) bestA)), c2 0 0) := by
  by_cases harz : P.toPoly.arity c = 0
  · -- the empty tuple is the unique candidate
    have hstep := step_candInit_zero E (w := w) c harz
      (curA.map Sigma.fst) (bestA.map Sigma.fst) reg
      (hpos 0 (padO curA) (fun _ => 0) (padO bestA)) (c2 0 0)
    have hval : ∀ x : Fin (P.toPoly.arity c), (fun _ => 0 : Fin (P.toPoly.arity c) → ℕ) x < w.length := by
      intro x
      have := x.2
      omega
    obtain ⟨regF, hloop⟩ := copyLoop_run E c curA hcurv
      (Fintype.card (Fin (P.toPoly.arity c) → Fin w.length)) (fun _ => 0) bestA reg
      hval hbestv (orbitEnds_of_arity_zero harz _)
    rw [show copyCands (P := P) w.length c
      = tupOrbit w.length (P.toPoly.arity c)
          (Fintype.card (Fin (P.toPoly.arity c) → Fin w.length)) (fun _ => 0) from by
        rw [copyCands, if_pos (Or.inl harz)]]
    refine ⟨regF, ?_⟩
    have hstep' : (evalM E).Steps w
        ((globOf (P := P) curA bestA (some c), .candInit, reg),
          hpos 0 (padO curA) (fun _ => 0) (padO bestA), c2 0 0) []
        ((globOf (P := P) curA bestA (some c), .sweep (.sel c) .selK, reg),
          hpos 0 (padO curA) (pad c (fun _ => 0)) (padO bestA), c2 0 0) := by
      rw [pad_of_arity_zero harz]
      exact hstep
    exact stepsTrans E (o₁ := []) (o₂ := []) hstep' hloop
  · -- positive arity: raise the block, then test for the empty word
    have h0k : 0 < kmaxP P := by
      have := arity_le_kmax (P := P) c
      omega
    have hstep1 := step_candInit_pos E (w := w) c harz
      (curA.map Sigma.fst) (bestA.map Sigma.fst) reg 0
      (padO curA) (fun _ => 0) (padO bestA) (c2 0 0)
      (fun rr _ => by
        rw [show tapeSym w ((fun _ : Fin (kmaxP P) => 0) rr) = TapeSym.lmark from
          tapeSym_zero w]
        intro hc
        cases hc)
    rw [candInitBlock_eq_pad] at hstep1
    by_cases hn : 0 < w.length
    · -- the zero tuple is a real candidate
      have hcell : pad c (fun _ => 0) ⟨0, h0k⟩ = 1 := by
        rw [pad, dif_pos (show ((⟨0, h0k⟩ : Fin (kmaxP P)).val < P.toPoly.arity c) from
          by show 0 < P.toPoly.arity c; omega)]
      have hstep2 := (step_candInit2 E (w := w) c h0k
        (curA.map Sigma.fst) (bestA.map Sigma.fst) reg 0
        (padO curA) (pad c (fun _ => 0)) (padO bestA) (c2 0 0)).1
        w[0]
        (by
          rw [hcell]
          exact tapeSym_succ w 0 hn)
      obtain ⟨regF, hloop⟩ := copyLoop_run E c curA hcurv
        (Fintype.card (Fin (P.toPoly.arity c) → Fin w.length)) (fun _ => 0) bestA reg
        (fun x => hn) hbestv
        (orbitEnds_fuel w.length (P.toPoly.arity c) (fun x => hn))
      rw [show copyCands (P := P) w.length c
        = tupOrbit w.length (P.toPoly.arity c)
            (Fintype.card (Fin (P.toPoly.arity c) → Fin w.length)) (fun _ => 0) from by
          rw [copyCands, if_pos (Or.inr hn)]]
      refine ⟨regF, ?_⟩
      exact stepsTrans E (o₁ := []) (o₂ := []) hstep1
        (stepsTrans E (o₁ := []) (o₂ := []) hstep2 hloop)
    · -- empty word: no candidates in a positive-arity copy
      have hcell : pad c (fun _ => 0) ⟨0, h0k⟩ = 1 := by
        rw [pad, dif_pos (show ((⟨0, h0k⟩ : Fin (kmaxP P)).val < P.toPoly.arity c) from
          by show 0 < P.toPoly.arity c; omega)]
      have hstep2 := (step_candInit2 E (w := w) c h0k
        (curA.map Sigma.fst) (bestA.map Sigma.fst) reg 0
        (padO curA) (pad c (fun _ => 0)) (padO bestA) (c2 0 0)).2
        (by
          rw [hcell]
          exact tapeSym_ge w 1 (by omega))
      rw [show copyCands (P := P) w.length c = [] from by
        rw [copyCands, if_neg]
        intro hc
        rcases hc with hc | hc
        · exact harz hc
        · exact absurd hc hn]
      rw [List.foldl_nil]
      refine ⟨reg, ?_⟩
      exact stepsTrans E (o₁ := []) (o₂ := []) hstep1 hstep2

omit [Fintype Gamma] in
theorem finSucc_pos {cv : ℕ} (h : cv < P.toPoly.K) (h2 : cv + 1 < P.toPoly.K) :
    finSucc (⟨cv, h⟩ : Fin P.toPoly.K) = some ⟨cv + 1, h2⟩ := by
  rw [finSucc, dif_pos h2]

omit [Fintype Gamma] in
theorem finSucc_last {cv : ℕ} (h : cv < P.toPoly.K) (h2 : ¬ (cv + 1 < P.toPoly.K)) :
    finSucc (⟨cv, h⟩ : Fin P.toPoly.K) = none := by
  rw [finSucc, dif_neg h2]

/-- The per-copy `bestStep` fold. -/
def copyFold (w : List Step) (curA : Option P.toPoly.Atom)
    (acc : Option P.toPoly.Atom) (c : Fin P.toPoly.K) : Option P.toPoly.Atom :=
  (copyCands (P := P) w.length c).foldl (fun a2 tt => bestStep P w curA a2 ⟨c, tt⟩) acc

omit [Fintype Gamma] in
theorem copyCands_sound {n : ℕ} (c : Fin P.toPoly.K) :
    ∀ tt ∈ copyCands (P := P) n c, ∀ x, tt x < n := by
  intro tt htt
  rw [copyCands] at htt
  split at htt
  · rename_i hguard
    refine orbit_sound n (P.toPoly.arity c) (fun x => ?_) htt
    rcases hguard with hz | hn
    · exact absurd x.2 (by omega)
    · exact hn
  · exact absurd htt List.not_mem_nil

omit [Fintype Gamma] in
theorem foldBest_valid {w : List Step} (curA : Option P.toPoly.Atom)
    (c : Fin P.toPoly.K) :
    ∀ (l : List (Fin (P.toPoly.arity c) → ℕ)) (bestA : Option P.toPoly.Atom),
    (∀ a ∈ bestA, ∀ x, a.2 x < w.length) →
    (∀ tt ∈ l, ∀ x, tt x < w.length) →
    ∀ a ∈ l.foldl (fun a2 tt => bestStep P w curA a2 ⟨c, tt⟩) bestA,
      ∀ x, a.2 x < w.length := by
  intro l
  induction l with
  | nil => intro bestA hb _ ; exact hb
  | cons tt ts ihl =>
      intro bestA hb hl
      rw [List.foldl_cons]
      exact ihl _ (bestStep_valid (X := ⟨c, tt⟩) hb (hl tt List.mem_cons_self))
        (fun tt2 htt2 => hl tt2 (List.mem_cons_of_mem _ htt2))

/-- **The copy loop of one round**: process copies `cv, cv+1, …, K-1`; at the
end, halt (accepting) when no candidate qualified, otherwise enter the label
search of the best atom. -/
theorem roundCopies_run {w : List Step} (curA : Option P.toPoly.Atom)
    (hcurv : ∀ a ∈ curA, ∀ x, a.2 x < w.length) (hG : 0 < Fintype.card Gamma) :
    ∀ (m cv : ℕ) (hcv : cv < P.toPoly.K), P.toPoly.K - cv = m + 1 →
    ∀ (bestA : Option P.toPoly.Atom) (reg : Reg E),
    (∀ a ∈ bestA, ∀ x, a.2 x < w.length) →
    (((List.finRange P.toPoly.K).drop cv).foldl (copyFold (P := P) w curA) bestA = none →
      ∃ (glob' : Glob P.toPoly.K) (reg' : Reg E) (pos' : Fin (hN P) → ℕ),
      (evalM E).Steps w
        ((globOf (P := P) curA bestA (some ⟨cv, hcv⟩), .candInit, reg),
          hpos 0 (padO curA) (fun _ => 0) (padO bestA), c2 0 0) []
        ((glob', .accept, reg'), pos', c2 0 0)) ∧
    (∀ bF, ((List.finRange P.toPoly.K).drop cv).foldl (copyFold (P := P) w curA) bestA
        = some bF →
      ∃ (gstale : Option (Fin P.toPoly.K)) (reg' : Reg E),
      (evalM E).Steps w
        ((globOf (P := P) curA bestA (some ⟨cv, hcv⟩), .candInit, reg),
          hpos 0 (padO curA) (fun _ => 0) (padO bestA), c2 0 0) []
        (((curA.map Sigma.fst, gstale, some bF.1),
            .sweep (.lab bF.1 ⟨0, hG⟩) (.labK ⟨0, hG⟩), reg'),
          hpos 0 (padO curA) (fun _ => 0) (padO (some bF)), c2 0 0)) := by
  intro m
  induction m with
  | zero =>
      intro cv hcv hm bestA reg hbestv
      -- last copy
      have hlast : ¬ (cv + 1 < P.toPoly.K) := by omega
      have hdrop : (List.finRange P.toPoly.K).drop cv
          = [(⟨cv, hcv⟩ : Fin P.toPoly.K)] := by
        rw [List.drop_eq_getElem_cons (by rw [List.length_finRange]; omega)]
        rw [List.getElem_finRange]
        rw [show (List.finRange P.toPoly.K).drop (cv + 1) = [] from
          List.drop_of_length_le (by rw [List.length_finRange]; omega)]
        rfl
      rw [hdrop, List.foldl_cons, List.foldl_nil]
      obtain ⟨regC, hcopy⟩ := copyEntry_run E ⟨cv, hcv⟩ curA bestA hcurv hbestv reg
      have hfold : (copyCands (P := P) w.length ⟨cv, hcv⟩).foldl
          (fun acc tt => bestStep P w curA acc ⟨⟨cv, hcv⟩, tt⟩) bestA
        = copyFold (P := P) w curA bestA ⟨cv, hcv⟩ := rfl
      rw [hfold] at hcopy
      constructor
      · intro hnone
        rw [hnone] at hcopy
        -- park exits to accept
        have hpark := walk_park_run E .parkCand rfl (w := w)
          (g := globOf (P := P) curA none (some ⟨cv, hcv⟩))
          (g' := globOf (P := P) curA none (some ⟨cv, hcv⟩)) (t' := .accept)
          (reg := regC) (cnt := c2 0 0)
          (by
            show wkExit E .parkCand (globOf (P := P) curA none (some ⟨cv, hcv⟩))
              = some (globOf (P := P) curA none (some ⟨cv, hcv⟩), .accept)
            simp only [globOf, wkExit]
            rw [show finSucc (⟨cv, hcv⟩ : Fin P.toPoly.K) = none from
              finSucc_last hcv hlast]
            rfl)
          (hpos 0 (padO curA) (pad ⟨cv, hcv⟩ (fun _ => 0)) (padO (P := P) none))
        rw [walkRes_parkCand] at hpark
        refine ⟨globOf (P := P) curA none (some ⟨cv, hcv⟩), regC,
          hpos 0 (padO curA) (fun _ => 0) (padO (P := P) none), ?_⟩
        exact stepsTrans E (o₁ := []) (o₂ := []) hcopy hpark
      · intro bF hsome
        rw [hsome] at hcopy
        have hpark := walk_park_run E .parkCand rfl (w := w)
          (g := globOf (P := P) curA (some bF) (some ⟨cv, hcv⟩))
          (g' := globOf (P := P) curA (some bF) (some ⟨cv, hcv⟩))
          (t' := .sweep (.lab bF.1 ⟨0, hG⟩) (.labK ⟨0, hG⟩))
          (reg := regC) (cnt := c2 0 0)
          (by
            show wkExit E .parkCand (globOf (P := P) curA (some bF) (some ⟨cv, hcv⟩))
              = some (globOf (P := P) curA (some bF) (some ⟨cv, hcv⟩),
                  .sweep (.lab bF.1 ⟨0, hG⟩) (.labK ⟨0, hG⟩))
            simp only [globOf, wkExit, Option.map_some]
            rw [show finSucc (⟨cv, hcv⟩ : Fin P.toPoly.K) = none from
              finSucc_last hcv hlast]
            show (if hg : 0 < Fintype.card Gamma then _ else none) = _
            rw [dif_pos hG])
          (hpos 0 (padO curA) (pad ⟨cv, hcv⟩ (fun _ => 0)) (padO (some bF)))
        rw [walkRes_parkCand] at hpark
        refine ⟨some ⟨cv, hcv⟩, regC, ?_⟩
        exact stepsTrans E (o₁ := []) (o₂ := []) hcopy hpark
  | succ m ih =>
      intro cv hcv hm bestA reg hbestv
      have hnext : cv + 1 < P.toPoly.K := by omega
      have hdrop : (List.finRange P.toPoly.K).drop cv
          = (⟨cv, hcv⟩ : Fin P.toPoly.K) :: (List.finRange P.toPoly.K).drop (cv + 1) := by
        rw [List.drop_eq_getElem_cons (by rw [List.length_finRange]; omega)]
        rw [List.getElem_finRange]
        rfl
      rw [hdrop, List.foldl_cons]
      obtain ⟨regC, hcopy⟩ := copyEntry_run E ⟨cv, hcv⟩ curA bestA hcurv hbestv reg
      have hfold : (copyCands (P := P) w.length ⟨cv, hcv⟩).foldl
          (fun acc tt => bestStep P w curA acc ⟨⟨cv, hcv⟩, tt⟩) bestA
        = copyFold (P := P) w curA bestA ⟨cv, hcv⟩ := rfl
      rw [hfold] at hcopy
      have hbest2v : ∀ a ∈ copyFold (P := P) w curA bestA ⟨cv, hcv⟩,
          ∀ x, a.2 x < w.length := by
        rw [copyFold]
        exact foldBest_valid curA ⟨cv, hcv⟩ _ bestA hbestv (copyCands_sound _)
      -- the copy exits to the next copy's candInit
      have hpark := walk_park_run E .parkCand rfl (w := w)
        (g := globOf (P := P) curA (copyFold (P := P) w curA bestA ⟨cv, hcv⟩)
          (some ⟨cv, hcv⟩))
        (g' := (curA.map Sigma.fst, some ⟨cv + 1, hnext⟩,
          (copyFold (P := P) w curA bestA ⟨cv, hcv⟩).map Sigma.fst))
        (t' := .candInit) (reg := regC) (cnt := c2 0 0)
        (by
          show wkExit E .parkCand (globOf (P := P) curA
              (copyFold (P := P) w curA bestA ⟨cv, hcv⟩) (some ⟨cv, hcv⟩))
            = some ((curA.map Sigma.fst, some ⟨cv + 1, hnext⟩,
                (copyFold (P := P) w curA bestA ⟨cv, hcv⟩).map Sigma.fst),
                .candInit)
          simp only [globOf, wkExit]
          rw [show finSucc (⟨cv, hcv⟩ : Fin P.toPoly.K) = some ⟨cv + 1, hnext⟩ from
            finSucc_pos hcv hnext])
        (hpos 0 (padO curA) (pad ⟨cv, hcv⟩ (fun _ => 0))
          (padO (copyFold (P := P) w curA bestA ⟨cv, hcv⟩)))
      rw [walkRes_parkCand] at hpark
      have hrest := ih (cv + 1) hnext (by omega)
        (copyFold (P := P) w curA bestA ⟨cv, hcv⟩) regC hbest2v
      constructor
      · intro hnone
        obtain ⟨glob', reg', pos', hsteps⟩ := hrest.1 hnone
        refine ⟨glob', reg', pos', ?_⟩
        exact stepsTrans E (o₁ := []) (o₂ := []) hcopy
          (stepsTrans E (o₁ := []) (o₂ := []) hpark hsteps)
      · intro bF hsome
        obtain ⟨gst, reg', hsteps⟩ := hrest.2 bF hsome
        refine ⟨gst, reg', ?_⟩
        exact stepsTrans E (o₁ := []) (o₂ := []) hcopy
          (stepsTrans E (o₁ := []) (o₂ := []) hpark hsteps)

end CopyLoop

/-! ## §18 Label search, emission, and one full round

-/

section RoundRun

open TupEnum

/-- **The label search**: sweep the label acceptors along the enumeration of
`Gamma` until the best atom's label is found, and emit it. -/
theorem labLoop_run {w : List Step} (bF : P.toPoly.Atom)
    (hvB : ∀ x, bF.2 x < w.length) (gcur gstale : Option (Fin P.toPoly.K))
    (cu : Fin (kmaxP P) → ℕ) :
    ∀ (m g0 : ℕ)
      (_hg0 : g0 ≤ ((Fintype.equivFin Gamma) (P.toPoly.label bF.1 w bF.2)).val)
      (hG : g0 < Fintype.card Gamma) (reg : Reg E),
      ((Fintype.equivFin Gamma) (P.toPoly.label bF.1 w bF.2)).val - g0 = m →
    ∃ reg' : Reg E,
    (evalM E).Steps w
      (((gcur, gstale, some bF.1), .sweep (.lab bF.1 ⟨g0, hG⟩) (.labK ⟨g0, hG⟩), reg),
        hpos 0 cu (fun _ => 0) (padO (some bF)), c2 0 0)
      [P.toPoly.label bF.1 w bF.2]
      (((gcur, gstale, some bF.1), .walk .parkCur, reg'),
        hpos 0 cu (fun _ => 0) (padO (some bF)), c2 0 0) := by
  intro m
  induction m with
  | zero =>
      intro g0 hg0 hG reg hm
      -- the label matches here
      have hgeq : (⟨g0, hG⟩ : Fin (Fintype.card Gamma))
          = (Fintype.equivFin Gamma) (P.toPoly.label bF.1 w bF.2) := by
        refine Fin.ext ?_
        show g0 = _
        omega
      obtain ⟨b, regR, hb, hrun⟩ := sweep_run E (w := w) (.lab bF.1 ⟨g0, hG⟩)
        (.labK ⟨g0, hG⟩) (g := (gcur, gstale, some bF.1)) reg
        (pos := hpos 0 cu (fun _ => 0) (padO (some bF))) (cnt := c2 0 0) bF.2
        (hpos_scanH _ _ _ _)
        (fun i => by
          show hpos 0 cu (fun _ => 0) (padO (some bF)) (bestH (embedA i)) = bF.2 i + 1
          rw [hpos_bestH]
          show pad bF.1 bF.2 (embedA i) = bF.2 i + 1
          exact pad_embedA _ _ _)
      have hbt : b = true := by
        rw [hb]
        show (E.Mlab bF.1 (γenum ⟨g0, hG⟩)).accepts
          (markAtN (P.toPoly.arity bF.1) w bF.2)
        rw [E.hlab bF.1 (γenum ⟨g0, hG⟩) w bF.2 hvB]
        rw [hgeq]
        show P.toPoly.label bF.1 w bF.2
          = (Fintype.equivFin Gamma).symm ((Fintype.equivFin Gamma) _)
        rw [Equiv.symm_apply_apply]
      subst hbt
      refine ⟨regR, ?_⟩
      have hdisp : contStep E (.labK ⟨g0, hG⟩) true (gcur, gstale, some bF.1)
          = some ((gcur, gstale, some bF.1), .walk .parkCur,
              [γenum ⟨g0, hG⟩]) := rfl
      have := hrun hdisp
      rw [show γenum (Gamma := Gamma) ⟨g0, hG⟩ = P.toPoly.label bF.1 w bF.2 from by
        rw [γenum, hgeq, Equiv.symm_apply_apply]] at this
      exact this
  | succ m ih =>
      intro g0 hg0 hG reg hm
      obtain ⟨b, regR, hb, hrun⟩ := sweep_run E (w := w) (.lab bF.1 ⟨g0, hG⟩)
        (.labK ⟨g0, hG⟩) (g := (gcur, gstale, some bF.1)) reg
        (pos := hpos 0 cu (fun _ => 0) (padO (some bF))) (cnt := c2 0 0) bF.2
        (hpos_scanH _ _ _ _)
        (fun i => by
          show hpos 0 cu (fun _ => 0) (padO (some bF)) (bestH (embedA i)) = bF.2 i + 1
          rw [hpos_bestH]
          show pad bF.1 bF.2 (embedA i) = bF.2 i + 1
          exact pad_embedA _ _ _)
      have hbf : b = false := by
        cases hbv : b
        · rfl
        · exfalso
          rw [hbv] at hb
          have hacc : (E.Mlab bF.1 (γenum ⟨g0, hG⟩)).accepts
              (markAtN (P.toPoly.arity bF.1) w bF.2) := hb.mp rfl
          rw [E.hlab bF.1 (γenum ⟨g0, hG⟩) w bF.2 hvB] at hacc
          have : (Fintype.equivFin Gamma) (P.toPoly.label bF.1 w bF.2)
              = (⟨g0, hG⟩ : Fin (Fintype.card Gamma)) := by
            rw [hacc]
            rw [show γenum (Gamma := Gamma) ⟨g0, hG⟩
              = (Fintype.equivFin Gamma).symm ⟨g0, hG⟩ from rfl]
            rw [Equiv.apply_symm_apply]
          have hval := congrArg Fin.val this
          simp only at hval
          omega
      subst hbf
      have hG2 : g0 + 1 < Fintype.card Gamma := by
        have := ((Fintype.equivFin Gamma) (P.toPoly.label bF.1 w bF.2)).2
        omega
      obtain ⟨reg', hnext⟩ := ih (g0 + 1) (by omega) hG2 regR (by omega)
      refine ⟨reg', ?_⟩
      have hdisp : contStep E (.labK ⟨g0, hG⟩) false (gcur, gstale, some bF.1)
          = some ((gcur, gstale, some bF.1),
              .sweep (.lab bF.1 ⟨g0 + 1, hG2⟩) (.labK ⟨g0 + 1, hG2⟩), []) := by
        show (if h : g0 + 1 < Fintype.card Gamma then
            some ((gcur, gstale, some bF.1),
              (Tag.sweep (.lab bF.1 ⟨g0 + 1, h⟩) (.labK ⟨g0 + 1, h⟩) :
                TagT E), ([] : List Gamma))
          else none) = _
        rw [dif_pos hG2]
      have hstep := hrun hdisp
      have hall := stepsTrans E (o₁ := []) hstep hnext
      simpa using hall

/-- **After the emission**: CUR is re-pointed at the emitted atom and the CAND
and BEST blocks are parked, returning to the round start. -/
theorem emitSeq_run {w : List Step} (bF : P.toPoly.Atom)
    (hvB : ∀ x, bF.2 x < w.length) (gcur gstale : Option (Fin P.toPoly.K))
    (cu : Fin (kmaxP P) → ℕ) (reg : Reg E) :
    (evalM E).Steps w
      (((gcur, gstale, some bF.1), .walk .parkCur, reg),
        hpos 0 cu (fun _ => 0) (padO (some bF)), c2 0 0) []
      (((some bF.1, gstale, none), .roundStart, reg),
        hpos 0 (padO (some bF)) (fun _ => 0) (fun _ => 0), c2 0 0) := by
  have hpark := walk_park_run E .parkCur rfl (w := w)
    (g := (gcur, gstale, some bF.1)) (g' := (gcur, gstale, some bF.1))
    (t' := .walk .copyCur) (reg := reg) (cnt := c2 0 0) rfl
    (hpos 0 cu (fun _ => 0) (padO (some bF)))
  rw [walkRes_parkCur] at hpark
  have hcopy := walk_copy_run E .copyCur rfl (w := w)
    (g := (gcur, gstale, some bF.1))
    (g' := (some bF.1, gstale, some bF.1)) (t' := .walk .parkCandBest)
    (reg := reg) (cnt := c2 0 0) copyCur_partner_notin rfl
    (hpos 0 (fun _ => 0) (fun _ => 0) (padO (some bF)))
    (by
      intro a ha
      have hint : 1 ≤ a.val ∧ a.val < 1 + kmaxP P := by
        rw [wkIn, wkLo, wkHi] at ha
        exact ha
      obtain ⟨h1, h2⟩ := hint
      have hxeq : a = curH ⟨a.val - 1, by omega⟩ := by
        refine Fin.ext ?_
        show a.val = 1 + (a.val - 1)
        omega
      rw [hxeq, hpos_curH]
      exact Nat.zero_le _)
    (by
      intro a ha
      have hint : 1 ≤ a.val ∧ a.val < 1 + kmaxP P := by
        rw [wkIn, wkLo, wkHi] at ha
        exact ha
      obtain ⟨h1, h2⟩ := hint
      have hpeq : wkPartner (P := P) .copyCur a = bestH ⟨a.val - 1, by omega⟩ := by
        rw [wkPartner]
        rw [dif_pos (show a.val + 2 * kmaxP P < hN P by
          show a.val + 2 * kmaxP P < 3 * kmaxP P + 1
          omega)]
        refine Fin.ext ?_
        show a.val + 2 * kmaxP P = 1 + 2 * kmaxP P + (a.val - 1)
        omega
      rw [hpeq, hpos_bestH]
      show pad bF.1 bF.2 ⟨a.val - 1, by omega⟩ ≤ w.length + 1
      have := pad_le bF.1 hvB ⟨a.val - 1, by omega⟩
      omega)
  rw [walkRes_copyCur] at hcopy
  have hpark2 := walk_park_run E .parkCandBest rfl (w := w)
    (g := (some bF.1, gstale, some bF.1))
    (g' := (some bF.1, gstale, none)) (t' := .roundStart)
    (reg := reg) (cnt := c2 0 0) rfl
    (hpos 0 (padO (some bF)) (fun _ => 0) (padO (some bF)))
  rw [walkRes_parkCandBest] at hpark2
  exact stepsTrans E (o₁ := []) (o₂ := []) hpark
    (stepsTrans E (o₁ := []) (o₂ := []) hcopy hpark2)

/-- The best atom of a whole round. -/
def roundBest (w : List Step) (curA : Option P.toPoly.Atom) : Option P.toPoly.Atom :=
  (List.finRange P.toPoly.K).foldl (copyFold (P := P) w curA) none

omit [Fintype Gamma] in
theorem roundBest_valid {w : List Step} (curA : Option P.toPoly.Atom) :
    ∀ a ∈ roundBest (P := P) w curA, ∀ x, a.2 x < w.length := by
  rw [roundBest]
  generalize hl : List.finRange P.toPoly.K = l
  clear hl
  suffices h : ∀ (l : List (Fin P.toPoly.K)) (bestA : Option P.toPoly.Atom),
      (∀ a ∈ bestA, ∀ x, a.2 x < w.length) →
      ∀ a ∈ l.foldl (copyFold (P := P) w curA) bestA, ∀ x, a.2 x < w.length by
    exact h l none (by simp)
  intro l
  induction l with
  | nil => intro bestA hb; exact hb
  | cons c cs ihl =>
      intro bestA hb
      rw [List.foldl_cons]
      refine ihl _ ?_
      rw [copyFold]
      exact foldBest_valid curA c _ bestA hb (copyCands_sound _)

/-- **One round**: either no candidate qualifies and the machine accepts, or
the round minimum's label is emitted and the machine returns to the round
start with the minimum as the new current atom. -/
theorem round_run {w : List Step} (curA : Option P.toPoly.Atom)
    (hcurv : ∀ a ∈ curA, ∀ x, a.2 x < w.length)
    (gstale : Option (Fin P.toPoly.K)) (reg : Reg E) :
    (roundBest (P := P) w curA = none →
      ∃ (glob' : Glob P.toPoly.K) (reg' : Reg E) (pos' : Fin (hN P) → ℕ),
      (evalM E).Steps w
        (((curA.map Sigma.fst, gstale, none), .roundStart, reg),
          hpos 0 (padO curA) (fun _ => 0) (fun _ => 0), c2 0 0) []
        ((glob', .accept, reg'), pos', c2 0 0)) ∧
    (∀ bF, roundBest (P := P) w curA = some bF →
      ∃ (gstale' : Option (Fin P.toPoly.K)) (reg' : Reg E),
      (evalM E).Steps w
        (((curA.map Sigma.fst, gstale, none), .roundStart, reg),
          hpos 0 (padO curA) (fun _ => 0) (fun _ => 0), c2 0 0)
        [P.toPoly.label bF.1 w bF.2]
        (((some bF.1, gstale', none), .roundStart, reg'),
          hpos 0 (padO (some bF)) (fun _ => 0) (fun _ => 0), c2 0 0)) := by
  by_cases hK : 0 < P.toPoly.K
  case neg =>
    -- no copies at all: accept immediately
    have hstep := step_roundStart_zero E (w := w) hK
      (curA.map Sigma.fst) none gstale reg
      (hpos 0 (padO curA) (fun _ => 0) (fun _ => 0)) (c2 0 0)
    have hempty : roundBest (P := P) w curA = none := by
      rw [roundBest]
      rw [show List.finRange P.toPoly.K = [] from
        List.eq_nil_iff_forall_not_mem.mpr (fun c _ => absurd c.2 (by omega))]
      rfl
    constructor
    · intro _
      exact ⟨(curA.map Sigma.fst, none, none), reg, _, hstep⟩
    · intro bF hsome
      rw [hempty] at hsome
      cases hsome
  case pos =>
  have hG : 0 < Fintype.card Gamma :=
    Fintype.card_pos_iff.mpr ⟨P.toPoly.label ⟨0, hK⟩ w (fun _ => 0)⟩
  have hstep := step_roundStart_pos E (w := w) hK
    (curA.map Sigma.fst) none gstale reg
    (hpos 0 (padO curA) (fun _ => 0) (fun _ => 0)) (c2 0 0)
  have hcopies := roundCopies_run E curA hcurv hG (P.toPoly.K - 1) 0 hK
    (by omega) none reg (by simp)
  have hdrop0 : (List.finRange P.toPoly.K).drop 0 = List.finRange P.toPoly.K := rfl
  rw [hdrop0] at hcopies
  constructor
  · intro hnone
    obtain ⟨glob', reg', pos', hsteps⟩ := hcopies.1 (by rw [← roundBest]; exact hnone)
    refine ⟨glob', reg', pos', ?_⟩
    exact stepsTrans E (o₁ := []) (o₂ := []) hstep hsteps
  · intro bF hsome
    have hvB : ∀ x, bF.2 x < w.length :=
      roundBest_valid curA bF hsome
    obtain ⟨gst, reg', hsteps⟩ := hcopies.2 bF (by rw [← roundBest]; exact hsome)
    obtain ⟨reg2, hlab⟩ := labLoop_run E bF hvB (curA.map Sigma.fst) gst
      (padO curA)
      ((Fintype.equivFin Gamma) (P.toPoly.label bF.1 w bF.2)).val 0
      (by omega) hG reg' (by omega)
    have hemit := emitSeq_run E bF hvB (curA.map Sigma.fst) gst (padO curA) reg2
    refine ⟨gst, reg2, ?_⟩
    have hall := stepsTrans E (o₁ := []) hstep
      (stepsTrans E (o₁ := []) hsteps
        (stepsTrans E (o₂ := []) hlab hemit))
    simpa using hall

end RoundRun

/-! ## §19 Full correctness: the machine computes the WRP output

-/

section FullCorrectness

open TupEnum

/-- All candidate atoms of a word, in machine order. -/
def allCands (w : List Step) : List P.toPoly.Atom :=
  (List.finRange P.toPoly.K).flatMap
    (fun c => (copyCands (P := P) w.length c).map (fun tt => ⟨c, tt⟩))

omit [Fintype Gamma] in
theorem foldl_flatMap' {α β γ : Type*} (l : List α) (f : α → List β)
    (g : γ → β → γ) : ∀ b : γ, (l.flatMap f).foldl g b
      = l.foldl (fun acc c => (f c).foldl g acc) b := by
  induction l with
  | nil => intro b; rfl
  | cons c cs ih =>
      intro b
      rw [List.flatMap_cons, List.foldl_append, List.foldl_cons, ih]

omit [Fintype Gamma] in
theorem roundBest_eq_bestFold (w : List Step) (curA : Option P.toPoly.Atom) :
    roundBest (P := P) w curA
      = (allCands (P := P) w).foldl (bestStep P w curA) none := by
  rw [roundBest, allCands, foldl_flatMap']
  have hfn : copyFold (P := P) w curA
      = fun acc c => ((copyCands (P := P) w.length c).map
          (fun tt => (⟨c, tt⟩ : P.toPoly.Atom))).foldl (bestStep P w curA) acc := by
    funext acc c
    rw [copyFold, List.foldl_map]
  rw [hfn]

omit [Fintype Gamma] in
theorem allCands_complete (w : List Step) (X : P.toPoly.Atom)
    (hX : P.toPoly.validAtom w X) : X ∈ allCands (P := P) w := by
  rw [allCands, List.mem_flatMap]
  refine ⟨X.1, List.mem_finRange _, ?_⟩
  rw [List.mem_map]
  refine ⟨X.2, ?_, rfl⟩
  rw [copyCands]
  by_cases harz : P.toPoly.arity X.1 = 0
  · rw [if_pos (Or.inl harz)]
    have hXz : X.2 = fun _ => 0 := by
      funext x
      exact absurd x.2 (by omega)
    rw [hXz]
    exact mem_tupOrbit_self _ _ _ _
  · have hn : 0 < w.length := by
      have h0 : 0 < P.toPoly.arity X.1 := by omega
      have := hX ⟨0, h0⟩
      omega
    rw [if_pos (Or.inr hn)]
    exact orbit_complete w.length (P.toPoly.arity X.1) hX

omit [Fintype Gamma] in
/-- The round minimum is the `MinSpec`-minimum. -/
theorem roundBest_minSpec (hV : P.Valid) (w : List Step)
    (curA : Option P.toPoly.Atom) :
    MinSpec P w curA (roundBest (P := P) w curA) := by
  rw [roundBest_eq_bestFold]
  refine bestFold_minSpec P hV w curA (allCands (P := P) w) ?_
  intro X hX
  exact allCands_complete w X hX.1.1

/-- **The round induction**: starting a round with the `i`-th sorted atom as
the current one, the machine emits the labels of the remaining atoms and
accepts. -/
theorem rounds_run (hV : P.Valid) {w : List Step} (L : List P.toPoly.Atom)
    (hmem : ∀ a, a ∈ L ↔ P.toPoly.selectedAtom w a)
    (hpw : L.Pairwise (P.wrpOrd w)) :
    ∀ (m i : ℕ) (_ : i ≤ L.length), L.length - i = m →
    ∀ (curA : Option P.toPoly.Atom) (gstale : Option (Fin P.toPoly.K))
      (reg : Reg E),
    (∀ a ∈ curA, ∀ x, a.2 x < w.length) →
    ((i = 0 ∧ curA = none) ∨
      (0 < i ∧ ∃ hlt : i - 1 < L.length, curA = some L[i - 1])) →
    ∃ (glob' : Glob P.toPoly.K) (reg' : Reg E) (pos' : Fin (hN P) → ℕ),
    (evalM E).Steps w
      (((curA.map Sigma.fst, gstale, none), .roundStart, reg),
        hpos 0 (padO curA) (fun _ => 0) (fun _ => 0), c2 0 0)
      ((L.drop i).map (P.toPoly.labelOf w))
      ((glob', .accept, reg'), pos', c2 0 0) := by
  intro m
  induction m with
  | zero =>
      intro i hi hm curA gstale reg hcurv hcurspec
      -- all atoms emitted: the qualifying set is empty and the machine accepts
      have hieq : i = L.length := by omega
      have hspecL : MinSpec P w curA (L[i]?) := by
        rcases hcurspec with ⟨hi0, rfl⟩ | ⟨hipos, hlt, rfl⟩
        · subst hi0
          rw [← List.head?_eq_getElem?]
          exact sorted_minSpec_none P w hmem hpw
        · have hbase := sorted_minSpec_succ P hV w hmem hpw (i - 1) hlt
          rw [show i - 1 + 1 = i from by omega] at hbase
          exact hbase
      rw [show L[i]? = none from List.getElem?_eq_none (by omega)] at hspecL
      have hround := (round_run E curA hcurv gstale reg).1
        (minSpec_unique P hV (roundBest_minSpec hV w curA) hspecL)
      rw [show (L.drop i).map (P.toPoly.labelOf w) = [] from by
        rw [List.drop_of_length_le (by omega)]
        rfl]
      exact hround
  | succ m ih =>
      intro i hi hm curA gstale reg hcurv hcurspec
      have hilt : i < L.length := by omega
      have hspecL : MinSpec P w curA (L[i]?) := by
        rcases hcurspec with ⟨hi0, rfl⟩ | ⟨hipos, hlt, rfl⟩
        · subst hi0
          rw [← List.head?_eq_getElem?]
          exact sorted_minSpec_none P w hmem hpw
        · have hbase := sorted_minSpec_succ P hV w hmem hpw (i - 1) hlt
          rw [show i - 1 + 1 = i from by omega] at hbase
          exact hbase
      rw [List.getElem?_eq_getElem hilt] at hspecL
      have hbest : roundBest (P := P) w curA = some L[i] :=
        minSpec_unique P hV (roundBest_minSpec hV w curA) hspecL
      obtain ⟨gst', reg', hstep⟩ := (round_run E curA hcurv gstale reg).2 L[i] hbest
      have hLiv : P.toPoly.validAtom w L[i] :=
        ((hmem L[i]).mp (List.getElem_mem hilt)).1
      obtain ⟨glob', reg'', pos', hrest⟩ := ih (i + 1) (by omega) (by omega)
        (some L[i]) gst' reg'
        (by
          intro a ha x
          rw [Option.mem_def, Option.some.injEq] at ha
          subst ha
          exact hLiv x)
        (Or.inr ⟨by omega, by
          refine ⟨by omega, ?_⟩
          rfl⟩)
      refine ⟨glob', reg'', pos', ?_⟩
      have hall := stepsTrans E hstep hrest
      rw [show List.drop i L = L[i] :: List.drop (i + 1) L from
        List.drop_eq_getElem_cons hilt]
      rw [List.map_cons]
      exact hall

omit [Fintype Gamma] in
theorem initPos_eq :
    (fun _ : Fin (hN P) => (0 : ℕ))
      = hpos 0 (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  funext x
  rw [hpos]
  by_cases h0 : x.val = 0
  · rw [dif_pos h0]
  · rw [dif_neg h0]
    by_cases h1 : x.val < 1 + kmaxP P
    · rw [dif_pos h1]
    · rw [dif_neg h1]
      by_cases h2 : x.val < 1 + 2 * kmaxP P
      · rw [dif_pos h2]
      · rw [dif_neg h2]

theorem initCnt_eq : (fun _ : Fin 2 => (0 : ℕ)) = c2 0 0 := fun2_ext rfl rfl

theorem halted_accept {w : List Step} (g : Glob P.toPoly.K) (reg : Reg E)
    (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) :
    (evalM E).Halted w ((g, .accept, reg), pos, cnt) := rfl

theorem halted_reject {w : List Step} (g : Glob P.toPoly.K) (reg : Reg E)
    (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) :
    (evalM E).Halted w ((g, .reject, reg), pos, cnt) := rfl

/-- **The machine computes the declarative output on the domain.** -/
theorem evalM_computes_output (hV : P.Valid) {w : List Step}
    (hdom : P.toPoly.domain w) {L : List P.toPoly.Atom}
    (hmem : ∀ a, a ∈ L ↔ P.toPoly.selectedAtom w a)
    (hpw : L.Pairwise (P.wrpOrd w)) :
    (evalM E).Computes w (L.map (P.toPoly.labelOf w)) := by
  obtain ⟨b, regR, hb, hrun⟩ := sweep_run E (w := w) .dom .domK
    (g := (none, none, none)) (Reg.unit E)
    (pos := fun _ => 0) (cnt := fun _ => 0) Fin.elim0 rfl (fun i => i.elim0)
  have hbt : b = true := by
    rw [hb]
    show (E.Mdom).accepts (markAtN 0 w Fin.elim0)
    rw [markAtN_zero]
    exact (E.hdom w).mpr hdom
  subst hbt
  have hstart := hrun (show contStep E .domK true (none, none, none)
    = some ((none, none, none), .roundStart, []) from rfl)
  obtain ⟨glob', reg', pos', hrounds⟩ := rounds_run E hV L hmem hpw
    L.length 0 (by omega) (by omega) none none regR (by simp) (Or.inl ⟨rfl, rfl⟩)
  rw [List.drop_zero] at hrounds
  have hstart' : (evalM E).Steps w (evalM E).initConfig []
      (((none, none, none), .roundStart, regR),
        hpos 0 (padO (P := P) none) (fun _ => 0) (fun _ => 0), c2 0 0) := by
    have hinit : (evalM E).initConfig
        = (((none, none, none), .sweep .dom .domK, Reg.unit E),
            hpos 0 (fun _ => 0) (fun _ => 0) (fun _ => 0), c2 0 0) := by
      rw [show (evalM E).initConfig
        = (((none, none, none), Tag.sweep .dom .domK, Reg.unit E),
            (fun _ => 0 : Fin (hN P) → ℕ), (fun _ => 0 : Fin 2 → ℕ)) from rfl]
      rw [initPos_eq, initCnt_eq]
    rw [hinit]
    rw [initPos_eq, initCnt_eq] at hstart
    exact hstart
  refine ⟨((glob', .accept, reg'), pos', c2 0 0), ?_, halted_accept E _ _ _ _, rfl⟩
  have hall := stepsTrans E hstart' hrounds
  simpa using hall

/-- **Off the domain the machine halts rejecting**, so it computes nothing. -/
theorem evalM_rejects {w : List Step} (hdom : ¬ P.toPoly.domain w) :
    ∀ out, ¬ (evalM E).Computes w out := by
  obtain ⟨b, regR, hb, hrun⟩ := sweep_run E (w := w) .dom .domK
    (g := (none, none, none)) (Reg.unit E)
    (pos := fun _ => 0) (cnt := fun _ => 0) Fin.elim0 rfl (fun i => i.elim0)
  have hbf : b = false := by
    cases hbv : b
    · rfl
    · exfalso
      rw [hbv] at hb
      refine hdom ?_
      have hacc : (E.Mdom).accepts (markAtN 0 w Fin.elim0) := hb.mp rfl
      rw [markAtN_zero] at hacc
      exact (E.hdom w).mp hacc
  subst hbf
  have hreject := hrun (show contStep E .domK false (none, none, none)
    = some ((none, none, none), .reject, []) from rfl)
  intro out ⟨e, ⟨N, hs⟩, hh, hF⟩
  obtain ⟨N₀, hs₀⟩ := hreject
  have hs₀' : (evalM E).StepsN w (evalM E).initConfig []
      (((none, none, none), .reject, regR), fun _ => 0, fun _ => 0) N₀ := hs₀
  have huniq := Multihead.MHC.stepsN_unique hs hh hs₀'
    (halted_reject E _ _ _ _)
  obtain ⟨-, he, -⟩ := huniq
  rw [he] at hF
  cases hF

/-- **The machine computes exactly the WRP output.** -/
theorem evalM_computes_iff (hV : P.Valid) (w : List Step) (out : List Gamma) :
    (P.toPoly.domain w ∧ P.IsOutput w out) ↔ (evalM E).Computes w out := by
  constructor
  · rintro ⟨hdom, L, hnd, hmem, hpw, rfl⟩
    exact evalM_computes_output E hV hdom hmem hpw
  · intro hcomp
    by_cases hdom : P.toPoly.domain w
    · obtain ⟨out₀, hout₀⟩ := WRPNonemptyRegular.exists_isOutput P hV w
      obtain ⟨L, hnd, hmem, hpw, rfl⟩ := hout₀
      have hcomp₀ := evalM_computes_output E hV hdom hmem hpw
      have heq := Multihead.MHC.computes_unique hcomp hcomp₀
      subst heq
      exact ⟨hdom, L, hnd, hmem, hpw, rfl⟩
    · exact absurd hcomp (evalM_rejects E hdom out)

end FullCorrectness

/-! ## §20 The linear space bound -/

section SpaceBound

/-- The linear space constant of the evaluator. -/
def CB : ℕ := 4 * Wb E * (kmaxP P + 1)

/-- Budget of the rank-sweep units after (and including the successors of)
unit `(side, r)`. -/
def potRest (w : List Step) (side : Bool) (r : Fin (kmaxP P)) : ℕ :=
  Wb E * (w.length + 2) *
    (if side then 2 * kmaxP P - 1 - r.val else kmaxP P - 1 - r.val)

/-- The remaining-payment potential of a control state (with the scan head at
cell `s`).  Zero-counter control states carry the full budget. -/
def pot (w : List Step) : TagT E → ℕ → ℕ
  | .cmp _ _ _ _ st, s =>
      (match st with
        | .c0load side => (if side then 2 * Wb E else Wb E)
            + 2 * kmaxP P * Wb E * (w.length + 2)
        | .c0pay side t _ => t.val + (if side then Wb E else 0)
            + 2 * kmaxP P * Wb E * (w.length + 2)
        | .scanU side r => Wb E * (w.length + 2 - s) + potRest E w side r
        | .payU side r t _ _ => t.val + Wb E * (w.length + 1 - s) + potRest E w side r
        | .drain => 0
        | .zero _ _ => 0)
  | .rewind (.unitK _ _ _ _ side r) _, _ => potRest E w side r
  | _, _ => CB E * (w.length + 1)

omit [Fintype Gamma] in
theorem potRest_le (w : List Step) (side : Bool) (r : Fin (kmaxP P)) :
    potRest E w side r ≤ 2 * kmaxP P * Wb E * (w.length + 2) := by
  rw [potRest]
  cases side
  · rw [if_neg (by simp)]
    refine le_trans (Nat.mul_le_mul_left _ (show kmaxP P - 1 - r.val ≤ 2 * kmaxP P
      from by omega)) ?_
    ring_nf
    omega
  · rw [if_pos rfl]
    refine le_trans (Nat.mul_le_mul_left _ (show 2 * kmaxP P - 1 - r.val ≤ 2 * kmaxP P
      from by omega)) ?_
    ring_nf
    omega

omit [Fintype Gamma] in
theorem unitBudget_le (w : List Step) :
    2 * Wb E + 2 * kmaxP P * Wb E * (w.length + 2) ≤ CB E * (w.length + 1) := by
  rw [CB]
  have h1 : 2 * kmaxP P * Wb E * (w.length + 2)
      ≤ 4 * Wb E * kmaxP P * (w.length + 1) := by
    have : w.length + 2 ≤ 2 * (w.length + 1) := by omega
    calc 2 * kmaxP P * Wb E * (w.length + 2)
        ≤ 2 * kmaxP P * Wb E * (2 * (w.length + 1)) :=
          Nat.mul_le_mul_left _ this
      _ = 4 * Wb E * kmaxP P * (w.length + 1) := by ring
  have h2 : 2 * Wb E ≤ 4 * Wb E * (w.length + 1) := by
    have : 1 ≤ w.length + 1 := by omega
    calc 2 * Wb E ≤ 4 * Wb E * 1 := by omega
      _ ≤ 4 * Wb E * (w.length + 1) := Nat.mul_le_mul_left _ this
  calc 2 * Wb E + 2 * kmaxP P * Wb E * (w.length + 2)
      ≤ 4 * Wb E * (w.length + 1) + 4 * Wb E * kmaxP P * (w.length + 1) := by omega
    _ = 4 * Wb E * (kmaxP P + 1) * (w.length + 1) := by ring

/-- Every potential is within the linear budget. -/
theorem pot_le_CB (w : List Step) (t : TagT E) (s : ℕ) :
    pot E w t s ≤ CB E * (w.length + 1) := by
  have hUB := unitBudget_le E w
  have hRle : ∀ side r, potRest E w side r ≤ 2 * kmaxP P * Wb E * (w.length + 2) :=
    potRest_le E w
  cases t with
  | cmp pi cL cR i st =>
      cases st with
      | c0load side =>
          show (if side then 2 * Wb E else Wb E)
            + 2 * kmaxP P * Wb E * (w.length + 2) ≤ _
          cases side
          · rw [if_neg (by simp)]; omega
          · rw [if_pos rfl]; omega
      | c0pay side t tgt =>
          show t.val + (if side then Wb E else 0)
            + 2 * kmaxP P * Wb E * (w.length + 2) ≤ _
          have ht := t.2
          cases side
          · rw [if_neg (by simp)]; omega
          · rw [if_pos rfl]; omega
      | scanU side r =>
          show Wb E * (w.length + 2 - s) + potRest E w side r ≤ _
          have hk : 0 < kmaxP P := by have := r.2; omega
          have h1 : Wb E * (w.length + 2 - s) ≤ Wb E * (w.length + 2) :=
            Nat.mul_le_mul_left _ (by omega)
          have h2 : potRest E w side r
              ≤ Wb E * (w.length + 2) * (2 * kmaxP P - 1) := by
            rw [potRest]
            refine Nat.mul_le_mul_left _ ?_
            cases side
            · rw [if_neg (by simp)]; omega
            · rw [if_pos rfl]; omega
          have h3 : Wb E * (w.length + 2) + Wb E * (w.length + 2) * (2 * kmaxP P - 1)
              = 2 * kmaxP P * Wb E * (w.length + 2) := by
            calc Wb E * (w.length + 2) + Wb E * (w.length + 2) * (2 * kmaxP P - 1)
                = Wb E * (w.length + 2) * (1 + (2 * kmaxP P - 1)) := by ring
              _ = Wb E * (w.length + 2) * (2 * kmaxP P) := by
                  rw [show 1 + (2 * kmaxP P - 1) = 2 * kmaxP P from by omega]
              _ = 2 * kmaxP P * Wb E * (w.length + 2) := by ring
          omega
      | payU side r t tgt ex =>
          show t.val + Wb E * (w.length + 1 - s) + potRest E w side r ≤ _
          have hk : 0 < kmaxP P := by have := r.2; omega
          have ht := t.2
          have h1 : Wb E * (w.length + 1 - s) ≤ Wb E * (w.length + 2) :=
            Nat.mul_le_mul_left _ (by omega)
          have h2 : potRest E w side r
              ≤ Wb E * (w.length + 2) * (2 * kmaxP P - 1) := by
            rw [potRest]
            refine Nat.mul_le_mul_left _ ?_
            cases side
            · rw [if_neg (by simp)]; omega
            · rw [if_pos rfl]; omega
          have h3 : Wb E * (w.length + 2) + Wb E * (w.length + 2) * (2 * kmaxP P - 1)
              = 2 * kmaxP P * Wb E * (w.length + 2) := by
            calc Wb E * (w.length + 2) + Wb E * (w.length + 2) * (2 * kmaxP P - 1)
                = Wb E * (w.length + 2) * (1 + (2 * kmaxP P - 1)) := by ring
              _ = Wb E * (w.length + 2) * (2 * kmaxP P) := by
                  rw [show 1 + (2 * kmaxP P - 1) = 2 * kmaxP P from by omega]
              _ = 2 * kmaxP P * Wb E * (w.length + 2) := by ring
          omega
      | drain => show (0 : ℕ) ≤ _; omega
      | zero tgt v => show (0 : ℕ) ≤ _; omega
  | rewind k b =>
      cases k with
      | unitK pi cL cR i side r =>
          show potRest E w side r ≤ _
          have := hRle side r
          omega
      | domK => exact le_rfl
      | selK => exact le_rfl
      | labK g => exact le_rfl
      | tieK pi => exact le_rfl
  | sweep J k => exact le_rfl
  | reject => exact le_rfl
  | accept => exact le_rfl
  | roundStart => exact le_rfl
  | candInit => exact le_rfl
  | candInit2 => exact le_rfl
  | candNext r => exact le_rfl
  | candNext2 r => exact le_rfl
  | candCarry r => exact le_rfl
  | candCarry2 r => exact le_rfl
  | walk wk => exact le_rfl

/-- Stage bookkeeping: in a `zero` stage the untargeted counter is already
empty; in a `payU` stage the scan head is on the word. -/
def auxT (w : List Step) : TagT E → (Fin (hN P) → ℕ) → (Fin 2 → ℕ) → Prop
  | .cmp _ _ _ _ (.zero tgt _), _, cnt => cnt (ctrIdx (! tgt)) = 0
  | .cmp _ _ _ _ (.payU _ _ _ _ _), pos, _ => pos scanH ≤ w.length
  | _, _, _ => True

/-- The space invariant: bounded heads, and counters plus remaining potential
within the linear budget. -/
def SBInv (w : List Step) (cfg : (evalM E).Config) : Prop :=
  (∀ a, cfg.2.1 a ≤ w.length + 1) ∧
  (cfg.2.2 0 + cfg.2.2 1 + pot E w cfg.1.2.1 (cfg.2.1 scanH)
    ≤ CB E * (w.length + 1)) ∧
  auxT E w cfg.1.2.1 cfg.2.1 cfg.2.2

omit [Fintype Gamma] in
theorem guard_apply_le {w : List Step} {pos : Fin (hN P) → ℕ}
    (mv0 : Fin (hN P) → HeadMove) (hb : ∀ a, pos a ≤ w.length + 1) :
    ∀ a, ((guardMoves (P := P) (fun a => tapeSym w (pos a)) mv0) a).apply (pos a)
      ≤ w.length + 1 := by
  intro a
  rw [guardMoves]
  split
  · exact hb a
  · rename_i hcond
    cases hmv : mv0 a with
    | left =>
        show pos a - 1 ≤ w.length + 1
        have := hb a
        omega
    | stay => exact hb a
    | right =>
        show pos a + 1 ≤ w.length + 1
        have hsym : tapeSym w (pos a) ≠ TapeSym.rmark := by
          intro hc
          exact hcond ⟨hc, hmv⟩
        by_contra hgt
        exact hsym (tapeSym_ge w (pos a) (by omega))

/-- Uniform closing step for control transitions that keep the counters. -/
theorem post_of_zero {w : List Step} {cnt : Fin 2 → ℕ}
    (h0 : cnt 0 = 0) (h1 : cnt 1 = 0) (t' : TagT E) (s' : ℕ) :
    (fun j => (opsKeep j).apply (cnt j)) 0 + (fun j => (opsKeep j).apply (cnt j)) 1
      + pot E w t' s' ≤ CB E * (w.length + 1) := by
  have hk : (fun j => (opsKeep j).apply (cnt j)) = cnt := apply_opsKeep cnt
  rw [hk]
  have := pot_le_CB E w t' s'
  omega

theorem pot_rewind_const {w : List Step}
    (k : Cont P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P)) (b : Bool) (s s' : ℕ) :
    pot E w (.rewind k b) s = pot E w (.rewind k b) s' := by
  cases k <;> rfl

omit [Fintype Gamma] in
theorem pot_unit_step {A B s x y : ℕ} (h : 1 + x ≤ y) :
    A * (B + 2 - s) + A * (B + 2) * x ≤ A * (B + 2) * y := by
  have h1 : A * (B + 2 - s) ≤ A * (B + 2) := Nat.mul_le_mul_left _ (by omega)
  have h2 : A * (B + 2) + A * (B + 2) * x = A * (B + 2) * (1 + x) := by ring
  have h3 : A * (B + 2) * (1 + x) ≤ A * (B + 2) * y := Nat.mul_le_mul_left _ h
  omega

theorem cmpEntryTag_auxT {w : List Step} (pi : CmpId) (cL cR : Fin P.toPoly.K)
    (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) :
    auxT E w (cmpEntryTag E pi cL cR) pos cnt := by
  rw [cmpEntryTag]
  by_cases hd : 0 < P.d
  · rw [dif_pos hd]
    trivial
  · rw [dif_neg hd]
    trivial

theorem candNextEntry_auxT {w : List Step} {g : Glob P.toPoly.K} {tx : TagT E}
    (h : candNextEntry E g = some tx) (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) :
    auxT E w tx pos cnt := by
  rw [candNextEntry] at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨c, -, rfl⟩ := h
  trivial

theorem bestUpdTag_auxT {w : List Step} {g : Glob P.toPoly.K} {tx : TagT E}
    (h : bestUpdTag E g = some tx) (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) :
    auxT E w tx pos cnt := by
  rw [bestUpdTag] at h
  split at h
  · injection h with h1
    subst h1
    trivial
  · injection h with h1
    subst h1
    exact cmpEntryTag_auxT E _ _ _ pos cnt
  · cases h

theorem cmpExit_auxT {w : List Step} {pi : CmpId} {v : Bool} {g : Glob P.toPoly.K}
    {tx : TagT E} (h : cmpExit E pi v g = some tx)
    (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) : auxT E w tx pos cnt := by
  rw [cmpExit.eq_def] at h
  split at h
  · exact bestUpdTag_auxT E h pos cnt
  · exact candNextEntry_auxT E h pos cnt
  · injection h with h1
    subst h1
    trivial
  · exact candNextEntry_auxT E h pos cnt

theorem contStep_target_auxT {w : List Step}
    {k : Cont P.toPoly.K (Fintype.card Gamma) P.d (kmaxP P)} {b : Bool}
    {g gx : Glob P.toPoly.K} {tx : TagT E} {ox : List Gamma}
    (h : contStep E k b g = some (gx, tx, ox))
    (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) : auxT E w tx pos cnt := by
  cases k with
  | domK =>
      rw [contStep] at h
      split at h <;>
      · injection h with h1
        injection h1 with hga h2
        injection h2 with htb
        subst htb
        trivial
  | selK =>
      rw [contStep] at h
      split at h
      · split at h
        · rw [Option.map_eq_some_iff] at h
          obtain ⟨tg, htg, hh⟩ := h
          injection hh with hga h2
          injection h2 with htb
          subst htb
          exact bestUpdTag_auxT E htg pos cnt
        · injection h with h1
          injection h1 with hga h2
          injection h2 with htb
          subst htb
          exact cmpEntryTag_auxT E _ _ _ pos cnt
        · cases h
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨tg, htg, hh⟩ := h
        injection hh with hga h2
        injection h2 with htb
        subst htb
        exact candNextEntry_auxT E htg pos cnt
  | labK gg =>
      rw [contStep] at h
      split at h
      · injection h with h1
        injection h1 with hga h2
        injection h2 with htb
        subst htb
        trivial
      · split at h
        · split at h
          · injection h with h1
            injection h1 with hga h2
            injection h2 with htb
            subst htb
            trivial
          · cases h
        · cases h
  | tieK pi =>
      rw [contStep] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨tg, htg, hh⟩ := h
      injection hh with hga h2
      injection h2 with htb
      subst htb
      exact cmpExit_auxT E htg pos cnt
  | unitK pi cL cR i side r =>
      rw [contStep] at h
      injection h with h1
      injection h1 with hga h2
      injection h2 with htb
      subst htb
      rw [nextUnitTag]
      cases side
      · by_cases h1 : r.val + 1 < P.toPoly.arity cR
        · rw [if_neg (by simp), dif_pos h1]
          trivial
        · rw [if_neg (by simp), dif_neg h1]
          trivial
      · by_cases h1 : r.val + 1 < P.toPoly.arity cL
        · rw [if_pos rfl, dif_pos h1]
          trivial
        · rw [if_pos rfl, dif_neg h1]
          rw [firstRTag]
          by_cases h2 : 0 < P.toPoly.arity cR
          · rw [dif_pos h2]
            trivial
          · rw [dif_neg h2]
            trivial

theorem wkExit_target_auxT {w : List Step} {wk : WalkId} {g gx : Glob P.toPoly.K}
    {tx : TagT E} (h : wkExit E wk g = some (gx, tx))
    (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ) : auxT E w tx pos cnt := by
  cases wk with
  | parkCand =>
      rw [wkExit] at h
      split at h
      · cases h
      · split at h
        · injection h with h1
          injection h1 with hga htb
          subst htb
          trivial
        · split at h
          · injection h with h1
            injection h1 with hga htb
            subst htb
            trivial
          · split at h
            · injection h with h1
              injection h1 with hga htb
              subst htb
              trivial
            · cases h
  | parkBest =>
      rw [wkExit] at h
      injection h with h1
      injection h1 with hga htb
      subst htb
      trivial
  | copyBest =>
      rw [wkExit] at h
      split at h
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨tg, htg, hh⟩ := h
        injection hh with hga htb
        subst htb
        exact candNextEntry_auxT E htg pos cnt
      · cases h
  | parkCur =>
      rw [wkExit] at h
      injection h with h1
      injection h1 with hga htb
      subst htb
      trivial
  | copyCur =>
      rw [wkExit] at h
      injection h with h1
      injection h1 with hga htb
      subst htb
      trivial
  | parkCandBest =>
      rw [wkExit] at h
      injection h with h1
      injection h1 with hga htb
      subst htb
      trivial

omit [Fintype Gamma] in
theorem guard_mvStay {w : List Step} (pos : Fin (hN P) → ℕ) :
    guardMoves (P := P) (fun a => tapeSym w (pos a)) mvStay = mvStay := by
  funext a
  rw [guardMoves]
  split <;> rfl

omit [Fintype Gamma] in
theorem guard_scan_right {w : List Step} (pos : Fin (hN P) → ℕ)
    (hsym : tapeSym w (pos scanH) ≠ TapeSym.rmark) :
    (guardMoves (P := P) (fun a => tapeSym w (pos a)) (mvOne scanH .right) scanH).apply
      (pos scanH) = pos scanH + 1 := by
  rw [guardMoves]
  rw [if_neg]
  · rw [mvOne, if_pos rfl]
    rfl
  · rintro ⟨hc, -⟩
    exact hsym hc

omit [Fintype Gamma] in
theorem tapeSym_letter_le {w : List Step} {s : ℕ} {a : Step}
    (h : tapeSym w s = TapeSym.letter a) : s ≤ w.length := by
  by_contra hgt
  rw [tapeSym_ge w s (by omega)] at h
  cases h

theorem firstUnitTag_pot_le {w : List Step} (pi : CmpId) (cL cR : Fin P.toPoly.K)
    (i : Fin P.d) (s' : ℕ) :
    pot E w (firstUnitTag E pi cL cR i) s'
      ≤ 2 * kmaxP P * Wb E * (w.length + 2) := by
  have hswap : Wb E * (w.length + 2) * (2 * kmaxP P)
      = 2 * kmaxP P * Wb E * (w.length + 2) := by ring
  rw [firstUnitTag]
  by_cases h1 : 0 < P.toPoly.arity cL
  · rw [dif_pos h1]
    show Wb E * (w.length + 2 - s') + potRest E w true _ ≤ _
    rw [potRest, if_pos rfl]
    rw [← hswap]
    refine pot_unit_step ?_
    have h2 := lt_of_lt_of_le h1 (arity_le_kmax cL)
    omega
  · rw [dif_neg h1, firstRTag]
    by_cases h2 : 0 < P.toPoly.arity cR
    · rw [dif_pos h2]
      show Wb E * (w.length + 2 - s') + potRest E w false _ ≤ _
      rw [potRest, if_neg (by simp)]
      rw [← hswap]
      refine pot_unit_step ?_
      have h3 := lt_of_lt_of_le h2 (arity_le_kmax cR)
      omega
    · rw [dif_neg h2]
      show (0 : ℕ) ≤ _
      omega

set_option maxHeartbeats 1000000 in
/-- **Preservation of the space invariant** (control cases; the compare phase
is handled separately). -/
theorem sbinv_preserved {w : List Step} :
    ∀ (q : EQ E) (pos : Fin (hN P) → ℕ) (cnt : Fin 2 → ℕ)
      (q' : EQ E) (mv : Fin (hN P) → HeadMove) (ops : Fin 2 → CounterOp)
      (u : List Gamma),
    SBInv E w (q, pos, cnt) →
    (evalM E).η q (fun a => tapeSym w (pos a)) (fun a b => pos a == pos b)
      (fun j => cnt j == 0) = some (q', mv, ops, u) →
    SBInv E w (q', fun a => (mv a).apply (pos a), fun j => (ops j).apply (cnt j)) := by
  intro q pos cnt q' mv ops u hInv hη
  obtain ⟨hb, hpot, haux⟩ := hInv
  obtain ⟨g, tag, reg⟩ := q
  dsimp only at hb hpot haux
  have hη' : (rawEta E (g, tag, reg) (fun a => tapeSym w (pos a))
      (fun a b => pos a == pos b) (fun j => cnt j == 0)).map
      (fun r => (r.1, guardMoves (P := P) (fun a => tapeSym w (pos a)) r.2.1,
        r.2.2)) = some (q', mv, ops, u) := hη
  rw [Option.map_eq_some_iff] at hη'
  obtain ⟨⟨⟨g2, t2, reg2⟩, mv0, ops0, u0⟩, hraw, heq⟩ := hη'
  injection heq with heq1 heq2
  injection heq2 with heqmv heq3
  injection heq3 with heqops hequ
  subst heq1
  subst heqmv
  subst heqops
  subst hequ
  refine ⟨guard_apply_le mv0 hb, ?_⟩
  cases tag with
  | reject => exact absurd hraw (by simp [rawEta])
  | accept => exact absurd hraw (by simp [rawEta])
  | sweep J k =>
      have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
        have hfull : pot E w (.sweep J k) (pos scanH) = CB E * (w.length + 1) := rfl
        rw [hfull] at hpot
        omega
      simp only [rawEta] at hraw
      repeat' split at hraw
      all_goals try (rw [Option.map_eq_some_iff] at hraw; obtain ⟨qj, -, hraw⟩ := hraw)
      all_goals cases hraw
      all_goals exact ⟨post_of_zero E h00.1 h00.2 _ _, trivial⟩
  | roundStart =>
      have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
        have hfull : pot E w (.roundStart) (pos scanH) = CB E * (w.length + 1) := rfl
        rw [hfull] at hpot
        omega
      simp only [rawEta] at hraw
      repeat' split at hraw
      all_goals cases hraw
      all_goals exact ⟨post_of_zero E h00.1 h00.2 _ _, trivial⟩
  | candInit =>
      have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
        have hfull : pot E w (.candInit) (pos scanH) = CB E * (w.length + 1) := rfl
        rw [hfull] at hpot
        omega
      simp only [rawEta] at hraw
      repeat' split at hraw
      all_goals cases hraw
      all_goals exact ⟨post_of_zero E h00.1 h00.2 _ _, trivial⟩
  | candInit2 =>
      have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
        have hfull : pot E w (.candInit2) (pos scanH) = CB E * (w.length + 1) := rfl
        rw [hfull] at hpot
        omega
      simp only [rawEta] at hraw
      repeat' split at hraw
      all_goals cases hraw
      all_goals exact ⟨post_of_zero E h00.1 h00.2 _ _, trivial⟩
  | candNext r =>
      have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
        have hfull : pot E w (.candNext r) (pos scanH) = CB E * (w.length + 1) := rfl
        rw [hfull] at hpot
        omega
      simp only [rawEta] at hraw
      repeat' split at hraw
      all_goals cases hraw
      all_goals exact ⟨post_of_zero E h00.1 h00.2 _ _, trivial⟩
  | candNext2 r =>
      have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
        have hfull : pot E w (.candNext2 r) (pos scanH) = CB E * (w.length + 1) := rfl
        rw [hfull] at hpot
        omega
      simp only [rawEta] at hraw
      repeat' split at hraw
      all_goals cases hraw
      all_goals exact ⟨post_of_zero E h00.1 h00.2 _ _, trivial⟩
  | candCarry r =>
      have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
        have hfull : pot E w (.candCarry r) (pos scanH) = CB E * (w.length + 1) := rfl
        rw [hfull] at hpot
        omega
      simp only [rawEta] at hraw
      repeat' split at hraw
      all_goals cases hraw
      all_goals exact ⟨post_of_zero E h00.1 h00.2 _ _, trivial⟩
  | candCarry2 r =>
      have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
        have hfull : pot E w (.candCarry2 r) (pos scanH) = CB E * (w.length + 1) := rfl
        rw [hfull] at hpot
        omega
      simp only [rawEta] at hraw
      repeat' split at hraw
      all_goals cases hraw
      all_goals exact ⟨post_of_zero E h00.1 h00.2 _ _, trivial⟩
  | walk wk =>
      have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
        have hfull : pot E w (.walk wk) (pos scanH) = CB E * (w.length + 1) := rfl
        rw [hfull] at hpot
        omega
      simp only [rawEta, walkEta] at hraw
      split at hraw
      · rw [Option.map_eq_some_iff] at hraw
        obtain ⟨⟨gx, tx⟩, hexit, hraw⟩ := hraw
        cases hraw
        exact ⟨post_of_zero E h00.1 h00.2 _ _, wkExit_target_auxT E hexit _ _⟩
      · cases hraw
        exact ⟨post_of_zero E h00.1 h00.2 _ _, trivial⟩
  | rewind k b =>
      simp only [rawEta] at hraw
      split at hraw
      · -- dispatch at the left marker
        rw [Option.map_eq_some_iff] at hraw
        obtain ⟨⟨gx, tx, ox⟩, hcont, hh⟩ := hraw
        injection hh with hh1 hh2
        injection hh2 with hh3 hh4
        injection hh4 with hh5 hh6
        injection hh1 with hg ht
        injection ht with ht1 ht2
        subst hg; subst ht1; subst ht2; subst hh3; subst hh5
        cases k with
        | domK =>
            have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
              have hfull : pot E w (.rewind .domK b) (pos scanH)
                  = CB E * (w.length + 1) := rfl
              rw [hfull] at hpot
              omega
            exact ⟨post_of_zero E h00.1 h00.2 _ _,
              contStep_target_auxT E hcont _ _⟩
        | selK =>
            have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
              have hfull : pot E w (.rewind .selK b) (pos scanH)
                  = CB E * (w.length + 1) := rfl
              rw [hfull] at hpot
              omega
            exact ⟨post_of_zero E h00.1 h00.2 _ _,
              contStep_target_auxT E hcont _ _⟩
        | labK gg =>
            have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
              have hfull : pot E w (.rewind (.labK gg) b) (pos scanH)
                  = CB E * (w.length + 1) := rfl
              rw [hfull] at hpot
              omega
            exact ⟨post_of_zero E h00.1 h00.2 _ _,
              contStep_target_auxT E hcont _ _⟩
        | tieK pi =>
            have h00 : cnt 0 = 0 ∧ cnt 1 = 0 := by
              have hfull : pot E w (.rewind (.tieK pi) b) (pos scanH)
                  = CB E * (w.length + 1) := rfl
              rw [hfull] at hpot
              omega
            exact ⟨post_of_zero E h00.1 h00.2 _ _,
              contStep_target_auxT E hcont _ _⟩
        | unitK pi cL cR i side r =>
            -- next-unit dispatch: the target potential shrinks within the rest
            have hcont' : contStep E (.unitK pi cL cR i side r) b g
                = some (gx, tx, ox) := hcont
            have htx : tx = nextUnitTag E pi cL cR i side r ∧ gx = g := by
              rw [contStep] at hcont'
              injection hcont' with hh
              injection hh with hga hh2
              injection hh2 with htb
              exact ⟨htb.symm, hga.symm⟩
            obtain ⟨htx, hgx⟩ := htx
            subst htx
            subst hgx
            have hsrc : pot E w (.rewind (.unitK pi cL cR i side r) b) (pos scanH)
                = potRest E w side r := rfl
            rw [hsrc] at hpot
            have hops : (fun j => (opsKeep j).apply (cnt j)) = cnt :=
              apply_opsKeep cnt
            rw [hops]
            have htarget : ∀ s', pot E w (nextUnitTag E pi cL cR i side r) s'
                ≤ potRest E w side r := by
              intro s'
              rw [nextUnitTag]
              cases side
              · by_cases h1 : r.val + 1 < P.toPoly.arity cR
                · rw [if_neg (by simp), dif_pos h1]
                  show Wb E * (w.length + 2 - s') + potRest E w false _
                    ≤ potRest E w false r
                  rw [potRest, potRest]
                  rw [if_neg (by simp), if_neg (by simp)]
                  refine pot_unit_step ?_
                  show 1 + (kmaxP P - 1 - (r.val + 1)) ≤ kmaxP P - 1 - r.val
                  have := lt_of_lt_of_le h1 (arity_le_kmax cR)
                  omega
                · rw [if_neg (by simp), dif_neg h1]
                  show (0 : ℕ) ≤ _
                  omega
              · by_cases h1 : r.val + 1 < P.toPoly.arity cL
                · rw [if_pos rfl, dif_pos h1]
                  show Wb E * (w.length + 2 - s') + potRest E w true _
                    ≤ potRest E w true r
                  rw [potRest, potRest]
                  rw [if_pos rfl, if_pos rfl]
                  refine pot_unit_step ?_
                  show 1 + (2 * kmaxP P - 1 - (r.val + 1)) ≤ 2 * kmaxP P - 1 - r.val
                  have h4 := lt_of_lt_of_le h1 (arity_le_kmax cL)
                  have h5 := r.2
                  omega
                · rw [if_pos rfl, dif_neg h1]
                  rw [firstRTag]
                  by_cases h2 : 0 < P.toPoly.arity cR
                  · rw [dif_pos h2]
                    show Wb E * (w.length + 2 - s') + potRest E w false _
                      ≤ potRest E w true r
                    rw [potRest, potRest]
                    rw [if_neg (by simp), if_pos rfl]
                    refine pot_unit_step ?_
                    show 1 + (kmaxP P - 1 - 0) ≤ 2 * kmaxP P - 1 - r.val
                    have h5 := r.2
                    have h6 := lt_of_lt_of_le h2 (arity_le_kmax cR)
                    omega
                  · rw [dif_neg h2]
                    show (0 : ℕ) ≤ _
                    omega
            dsimp only
            have h5 := htarget ((guardMoves (P := P) (fun a => tapeSym w (pos a))
              mvStay scanH).apply (pos scanH))
            refine ⟨by omega, ?_⟩
            -- the next-unit tag never carries the `zero` bookkeeping
            rw [nextUnitTag]
            cases side
            · by_cases h1 : r.val + 1 < P.toPoly.arity cR
              · rw [if_neg (by simp), dif_pos h1]
                trivial
              · rw [if_neg (by simp), dif_neg h1]
                trivial
            · by_cases h1 : r.val + 1 < P.toPoly.arity cL
              · rw [if_pos rfl, dif_pos h1]
                trivial
              · rw [if_pos rfl, dif_neg h1]
                rw [firstRTag]
                by_cases h2 : 0 < P.toPoly.arity cR
                · rw [dif_pos h2]
                  trivial
                · rw [dif_neg h2]
                  trivial
      · -- plain left move: same tag, same potential
        injection hraw with hh
        injection hh with hh1 hh2
        injection hh2 with hh3 hh4
        injection hh4 with hh5 hh6
        injection hh1 with hg ht
        injection ht with ht1 ht2
        subst hg; subst ht1; subst ht2; subst hh3; subst hh5
        have hops : (fun j => (opsKeep j).apply (cnt j)) = cnt :=
          apply_opsKeep cnt
        rw [hops]
        refine ⟨?_, ?_⟩
        · dsimp only
          rw [pot_rewind_const E k b _ (pos scanH)]
          exact hpot
        · exact haux
  | cmp pi cL cR i st =>
      rw [rawEta_cmp] at hraw
      cases st with
      | c0load side =>
          rw [cmpEta] at hraw
          cases hraw
          have hc0 := c0_le_Wb E (if side = true then cL else cR) i
          rw [guard_mvStay, apply_opsKeep]
          refine ⟨?_, trivial⟩
          show cnt 0 + cnt 1 + pot E w (.cmp pi cL cR i (.c0pay side _ _)) _ ≤ _
          have hsrc : pot E w (.cmp pi cL cR i (.c0load side)) (pos scanH)
              = (if side then 2 * Wb E else Wb E)
                + 2 * kmaxP P * Wb E * (w.length + 2) := rfl
          rw [hsrc] at hpot
          cases side
          · show cnt 0 + cnt 1
              + (((E.κ cR).c0 i).natAbs + (0 : ℕ)
                + 2 * kmaxP P * Wb E * (w.length + 2)) ≤ _
            rw [if_neg (by simp)] at hpot
            have hc0' : ((E.κ cR).c0 i).natAbs ≤ Wb E := hc0
            omega
          · show cnt 0 + cnt 1
              + (((E.κ cL).c0 i).natAbs + Wb E
                + 2 * kmaxP P * Wb E * (w.length + 2)) ≤ _
            rw [if_pos rfl] at hpot
            have hc0' : ((E.κ cL).c0 i).natAbs ≤ Wb E := hc0
            omega
      | c0pay side t tgt =>
          rw [cmpEta] at hraw
          split at hraw
          · -- countdown: pay one into the target counter
            rename_i ht
            cases hraw
            rw [guard_mvStay]
            have hsrc : pot E w (.cmp pi cL cR i (.c0pay side t tgt)) (pos scanH)
                = t.val + (if side then Wb E else 0)
                  + 2 * kmaxP P * Wb E * (w.length + 2) := rfl
            rw [hsrc] at hpot
            refine ⟨?_, trivial⟩
            show (fun j => (opsInc tgt j).apply (cnt j)) 0
              + (fun j => (opsInc tgt j).apply (cnt j)) 1
              + (t.val - 1 + (if side then Wb E else 0)
                + 2 * kmaxP P * Wb E * (w.length + 2)) ≤ _
            cases tgt
            · rw [show (fun j => (opsInc false j).apply (cnt j)) 0 = cnt 0 from rfl,
                show (fun j => (opsInc false j).apply (cnt j)) 1 = cnt 1 + 1 from rfl]
              omega
            · rw [show (fun j => (opsInc true j).apply (cnt j)) 0 = cnt 0 + 1 from rfl,
                show (fun j => (opsInc true j).apply (cnt j)) 1 = cnt 1 from rfl]
              omega
          · rename_i ht
            split at hraw
            · -- move to the right c0
              cases hraw
              rw [guard_mvStay, apply_opsKeep]
              have hsrc : pot E w (.cmp pi cL cR i (.c0pay side t tgt)) (pos scanH)
                  = t.val + (if side then Wb E else 0)
                    + 2 * kmaxP P * Wb E * (w.length + 2) := rfl
              rw [hsrc] at hpot
              rename_i hside
              rw [if_pos hside] at hpot
              refine ⟨?_, trivial⟩
              show cnt 0 + cnt 1 + (Wb E + 2 * kmaxP P * Wb E * (w.length + 2)) ≤ _
              omega
            · -- move to the first unit
              cases hraw
              rw [guard_mvStay, apply_opsKeep]
              have hsrc : pot E w (.cmp pi cL cR i (.c0pay side t tgt)) (pos scanH)
                  = t.val + (if side then Wb E else 0)
                    + 2 * kmaxP P * Wb E * (w.length + 2) := rfl
              rw [hsrc] at hpot
              refine ⟨?_, ?_⟩
              · dsimp only
                have := firstUnitTag_pot_le E (w := w) pi cL cR i
                  ((mvStay (P := P) scanH).apply (pos scanH))
                omega
              · rw [firstUnitTag]
                by_cases h1 : 0 < P.toPoly.arity cL
                · rw [dif_pos h1]
                  trivial
                · rw [dif_neg h1, firstRTag]
                  by_cases h2 : 0 < P.toPoly.arity cR
                  · rw [dif_pos h2]
                    trivial
                  · rw [dif_neg h2]
                    trivial
      | scanU side r =>
          rw [cmpEta] at hraw
          by_cases hcr : r.val < P.toPoly.arity (if side = true then cL else cR)
          case neg =>
            rw [dif_neg hcr] at hraw
            cases hraw
          case pos =>
          rw [dif_pos hcr] at hraw
          cases hsym : tapeSym w (pos scanH) with
          | lmark =>
            simp only [hsym] at hraw
            -- left marker: reset the register and move right
            cases hraw
            rw [apply_opsKeep]
            refine ⟨?_, trivial⟩
            have hs' : (guardMoves (P := P) (fun a => tapeSym w (pos a))
                (mvOne scanH .right) scanH).apply (pos scanH) = pos scanH + 1 := by
              refine guard_scan_right pos ?_
              rw [hsym]
              intro hc
              cases hc
            dsimp only
            rw [hs']
            have hsrc : pot E w (.cmp pi cL cR i (.scanU side r)) (pos scanH)
                = Wb E * (w.length + 2 - pos scanH) + potRest E w side r := rfl
            rw [hsrc] at hpot
            show cnt 0 + cnt 1
              + (Wb E * (w.length + 2 - (pos scanH + 1)) + potRest E w side r) ≤ _
            have hmono : Wb E * (w.length + 2 - (pos scanH + 1))
                ≤ Wb E * (w.length + 2 - pos scanH) :=
              Nat.mul_le_mul_left _ (by omega)
            omega
          | letter aa =>
            simp only [hsym] at hraw
            obtain ⟨qr, -, hraw⟩ := Option.map_eq_some_iff.mp hraw
            have hscan_le : pos scanH ≤ w.length := by
              refine tapeSym_letter_le (a := aa) ?_
              exact hsym
            have hsrc : pot E w (.cmp pi cL cR i (.scanU side r)) (pos scanH)
                = Wb E * (w.length + 2 - pos scanH) + potRest E w side r := rfl
            rw [hsrc] at hpot
            have hsplit : Wb E * (w.length + 2 - pos scanH)
                = Wb E * (w.length + 1 - pos scanH) + Wb E := by
              rw [show w.length + 2 - pos scanH
                = (w.length + 1 - pos scanH) + 1 from by omega]
              rw [Nat.mul_succ]
            rw [hsplit] at hpot
            split at hraw
            · -- the marked cell: β payment
              cases hraw
              rw [guard_mvStay, apply_opsKeep]
              have hβ := β_le_Wb E (if side = true then cL else cR) ⟨r.val, hcr⟩ qr aa i
              refine ⟨?_, hscan_le⟩
              dsimp only
              show cnt 0 + cnt 1
                + (((E.κ (if side = true then cL else cR)).β ⟨r.val, hcr⟩ qr aa i).natAbs
                  + Wb E * (w.length + 1 - pos scanH) + potRest E w side r) ≤ _
              omega
            · -- an ω payment
              cases hraw
              rw [guard_mvStay, apply_opsKeep]
              have hω : ((rsrc E ⟨if side = true then cL else cR, ⟨r.val, hcr⟩⟩).ω
                  qr aa i).natAbs ≤ Wb E :=
                ω_le_Wb E (if side = true then cL else cR) ⟨r.val, hcr⟩ qr aa i
              refine ⟨?_, hscan_le⟩
              dsimp only
              show cnt 0 + cnt 1
                + (((rsrc E ⟨if side = true then cL else cR, ⟨r.val, hcr⟩⟩).ω qr aa i).natAbs
                  + Wb E * (w.length + 1 - pos scanH) + potRest E w side r) ≤ _
              omega
          | rmark =>
            simp only [hsym] at hraw
            cases hraw
      | payU side r t tgt ex =>
          rw [cmpEta] at hraw
          have hscan_le : pos scanH ≤ w.length := haux
          split at hraw
          · -- countdown
            rename_i ht
            cases hraw
            have hsrc : pot E w (.cmp pi cL cR i (.payU side r t tgt ex)) (pos scanH)
                = t.val + Wb E * (w.length + 1 - pos scanH) + potRest E w side r := rfl
            rw [hsrc] at hpot
            rw [guard_mvStay]
            refine ⟨?_, hscan_le⟩
            show (fun j => (opsInc tgt j).apply (cnt j)) 0
              + (fun j => (opsInc tgt j).apply (cnt j)) 1
              + (t.val - 1 + Wb E * (w.length + 1 - pos scanH) + potRest E w side r) ≤ _
            cases tgt
            · rw [show (fun j => (opsInc false j).apply (cnt j)) 0 = cnt 0 from rfl,
                show (fun j => (opsInc false j).apply (cnt j)) 1 = cnt 1 + 1 from rfl]
              omega
            · rw [show (fun j => (opsInc true j).apply (cnt j)) 0 = cnt 0 + 1 from rfl,
                show (fun j => (opsInc true j).apply (cnt j)) 1 = cnt 1 from rfl]
              omega
          · rename_i ht
            have hsrc : pot E w (.cmp pi cL cR i (.payU side r t tgt ex)) (pos scanH)
                = t.val + Wb E * (w.length + 1 - pos scanH) + potRest E w side r := rfl
            rw [hsrc] at hpot
            split at hraw
            · -- exit to the rewind
              cases hraw
              rw [guard_mvStay, apply_opsKeep]
              refine ⟨?_, trivial⟩
              show cnt 0 + cnt 1 + potRest E w side r ≤ _
              omega
            · -- back to the scan
              cases hraw
              rw [apply_opsKeep]
              refine ⟨?_, trivial⟩
              have hs' : (guardMoves (P := P) (fun a => tapeSym w (pos a))
                  (mvOne scanH .right) scanH).apply (pos scanH) = pos scanH + 1 := by
                refine guard_scan_right pos ?_
                exact tapeSym_ne_rmark_of_le hscan_le
              dsimp only
              rw [hs']
              show cnt 0 + cnt 1
                + (Wb E * (w.length + 2 - (pos scanH + 1)) + potRest E w side r) ≤ _
              rw [show w.length + 2 - (pos scanH + 1)
                = w.length + 1 - pos scanH from by omega]
              omega
      | drain =>
          rw [cmpEta] at hraw
          have hsrc : pot E w (.cmp pi cL cR i .drain) (pos scanH) = 0 := rfl
          rw [hsrc] at hpot
          split at hraw
          case h_1 hz0 hz1 =>
            have hc0 : cnt 0 = 0 := by
              have := of_decide_eq_true (by exact hz0)
              exact this
            have hc1 : cnt 1 = 0 := by
              have := of_decide_eq_true (by exact hz1)
              exact this
            split at hraw
            · cases hraw
              rw [guard_mvStay]
              exact ⟨post_of_zero E hc0 hc1 _ _, trivial⟩
            · cases hraw
              rw [guard_mvStay]
              exact ⟨post_of_zero E hc0 hc1 _ _, trivial⟩
          case h_2 hz0 hz1 =>
            have hc0 : cnt 0 = 0 := by
              have := of_decide_eq_true (by exact hz0)
              exact this
            cases hraw
            rw [guard_mvStay, apply_opsKeep]
            refine ⟨?_, ?_⟩
            · show cnt 0 + cnt 1 + (0 : ℕ) ≤ _
              omega
            · show cnt (ctrIdx (! false)) = 0
              exact hc0
          case h_3 hz0 hz1 =>
            have hc1 : cnt 1 = 0 := by
              have := of_decide_eq_true (by exact hz1)
              exact this
            cases hraw
            rw [guard_mvStay, apply_opsKeep]
            refine ⟨?_, ?_⟩
            · show cnt 0 + cnt 1 + (0 : ℕ) ≤ _
              omega
            · show cnt (ctrIdx (! true)) = 0
              exact hc1
          case h_4 hz0 hz1 =>
            cases hraw
            rw [guard_mvStay]
            refine ⟨?_, trivial⟩
            dsimp only
            show cnt 0 - 1 + (cnt 1 - 1)
              + pot E w (.cmp pi cL cR i .drain) ((mvStay (P := P) scanH).apply (pos scanH)) ≤ _
            rw [show pot E w (.cmp pi cL cR i .drain)
              ((mvStay (P := P) scanH).apply (pos scanH)) = 0 from rfl]
            omega
      | zero tgt vd =>
          rw [cmpEta] at hraw
          have hsrc : pot E w (.cmp pi cL cR i (.zero tgt vd)) (pos scanH) = 0 := rfl
          rw [hsrc] at hpot
          have hother : cnt (ctrIdx (! tgt)) = 0 := haux
          split at hraw
          · -- exit: dispatch the verdict
            rename_i hz
            have hzz : cnt (ctrIdx tgt) = 0 := by
              have := of_decide_eq_true (by exact hz)
              exact this
            rw [Option.map_eq_some_iff] at hraw
            obtain ⟨tx, hexit, hraw⟩ := hraw
            cases hraw
            rw [guard_mvStay]
            have hc0 : cnt 0 = 0 := by
              cases tgt
              · exact hother
              · exact hzz
            have hc1 : cnt 1 = 0 := by
              cases tgt
              · exact hzz
              · exact hother
            exact ⟨post_of_zero E hc0 hc1 _ _, cmpExit_auxT E hexit _ _⟩
          · -- decrement the target
            cases hraw
            rw [guard_mvStay]
            refine ⟨?_, ?_⟩
            · show (fun j => (opsDec tgt j).apply (cnt j)) 0
                + (fun j => (opsDec tgt j).apply (cnt j)) 1 + (0 : ℕ) ≤ _
              cases tgt
              · rw [show (fun j => (opsDec false j).apply (cnt j)) 0 = cnt 0 from rfl,
                  show (fun j => (opsDec false j).apply (cnt j)) 1 = cnt 1 - 1 from rfl]
                omega
              · rw [show (fun j => (opsDec true j).apply (cnt j)) 0 = cnt 0 - 1 from rfl,
                  show (fun j => (opsDec true j).apply (cnt j)) 1 = cnt 1 from rfl]
                omega
            · show (fun j => (opsDec tgt j).apply (cnt j)) (ctrIdx (! tgt)) = 0
              cases tgt
              · rw [show (fun j => (opsDec false j).apply (cnt j)) (ctrIdx (! false))
                  = cnt 0 from rfl]
                exact hother
              · rw [show (fun j => (opsDec true j).apply (cnt j)) (ctrIdx (! true))
                  = cnt 1 from rfl]
                exact hother


/-- **The evaluator is linearly counter-bounded.** -/
theorem evalM_spaceBound : Multihead.SpaceBound (evalM E) (CB E) := by
  intro w out e N hs j
  have hInv : SBInv E w e := by
    refine Multihead.MHC.stepsN_invariant (P := SBInv E w) ?_ hs ?_
    · intro q pos cnt q' mv ops u hP hη
      exact sbinv_preserved E q pos cnt q' mv ops u hP hη
    · refine ⟨fun a => by show (0 : ℕ) ≤ w.length + 1; omega, ?_, trivial⟩
      show 0 + 0 + pot E w (.sweep .dom .domK) 0 ≤ CB E * (w.length + 1)
      have hfull : pot E w (.sweep .dom .domK) 0 = CB E * (w.length + 1) := rfl
      omega
  obtain ⟨-, hpot, -⟩ := hInv
  rcases j with ⟨(_ | _ | jv), hj⟩
  · show e.2.2 0 ≤ _
    omega
  · show e.2.2 1 ≤ _
    omega
  · omega

end SpaceBound

/-! ## §21 The goal theorems

-/

end

end WRPLogspace

open WRPLogspace in
/-- **`thm:wrp-logspace` (paper.tex; proof App. A.2 lines
4401–4475): every WRP map is deterministic-logspace computable** in the
multihead bounded-counter model.

Formalisation notes.  The paper's input alphabet `Σ` is an arbitrary finite
alphabet; the formalisation instantiates `Σ = Step`, since the repo's
marked-word machinery (`MSOMarkN`) is `Step`-specific — the generalisation is
mechanical.  The verified evaluator uses the ≺-successor round structure (one
output letter per round, keeping the current atom in a head block and
computing each round's minimum with a best-so-far block) — since the
2026-08-28 revision this is the paper's own proof of the theorem (previously
only its Corollary proof; the earlier predecessor-counting proof would also
have exceeded this model's linearly bounded counters at arity `> 1`, and the
successor rounds improve the paper's generic time bound to `O(n^{2k+1})`).
Rank comparisons accumulate the
positive and negative parts of the rank difference of one lexicographic
dimension in the two counters and drain them; rank ties are broken by the
marked tie-order DFA.  The paper's polynomial-time clause is
`Multihead.MHC.halting_length_le` / `computes_halting_length` applied to the
witness (see `wrp_logspace_polytime`). -/
theorem wrp_isLogspaceMH {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma]
    (T : List Step → Option (List Gamma)) (hT : WRP.IsWRP T) :
    Multihead.IsLogspaceMH T := by
  obtain ⟨P, hV, hTiff⟩ := hT
  let E := mkEvalData P
  refine ⟨hN P, 2, CB E, evalM E, evalM_spaceBound E, ?_⟩
  intro w out
  rw [hTiff w out]
  exact evalM_computes_iff E hV w out

open WRPLogspace in
/-- **The polynomial-time clause of `thm:wrp-logspace`**: the witnessing
machine halts within `|Q| · (n+2)^h · (C·(n+1)+1)^c` steps — polynomial in
`n` for fixed machine data (`Multihead.MHC.halting_length_le`). -/
theorem wrp_logspace_polytime {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma]
    (T : List Step → Option (List Gamma)) (hT : WRP.IsWRP T) :
    ∃ (h c C : ℕ) (M : Multihead.MHC Step Gamma h c),
      Multihead.SpaceBound M C ∧ (∀ w out, T w = some out ↔ M.Computes w out) ∧
      ∀ w out e N, M.StepsN w M.initConfig out e N → M.Halted w e →
        N < M.cardQ * (w.length + 2) ^ h * (C * (w.length + 1) + 1) ^ c := by
  obtain ⟨P, hV, hTiff⟩ := hT
  let E := mkEvalData P
  refine ⟨hN P, 2, CB E, evalM E, evalM_spaceBound E, ?_, ?_⟩
  · intro w out
    rw [hTiff w out]
    exact evalM_computes_iff E hV w out
  · intro w out e N hrun hhalt
    exact Multihead.MHC.halting_length_le (evalM_spaceBound E) hrun hhalt

/-- **`thm:wrp-strict-below-logspace` (paper.tex),
UNCONDITIONAL**: every WRP map is deterministic-logspace computable in the
multihead model, and some deterministic-logspace map is not WRP. -/
theorem wrp_strict_below_logspace :
    (∀ T : List Step → Option (List WRPComp.GBD), WRP.IsWRP T →
      Multihead.IsLogspaceMH T) ∧
    ∃ f : List Step → Option (List WRPComp.GBD),
      Multihead.IsLogspaceMH f ∧ ¬ WRP.IsWRP f :=
  ⟨fun T hT => wrp_isLogspaceMH T hT, Multihead.exists_logspaceMH_not_wrp⟩

