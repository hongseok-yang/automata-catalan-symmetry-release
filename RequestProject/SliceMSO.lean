/-
# MSO definability on a one-loop slice is eventually periodic (paper Lemma 6.2)

This **factors** the paper's Lemma 6.2 (finite-state predicates on a regular slice
are Presburger / eventually periodic) into:

* a *proved* automaton fact — acceptance of a deterministic finite acceptor on the
  one-loop slice `pre ++ loop^n ++ suf` is eventually periodic in `n` (from
  `SliceAutomata.iterate_eventuallyPeriodic`); and
* a single clean textbook *axiom* — Büchi–Elgot–Trakhtenbrot: every MSO-definable
  language is recognised by such an acceptor.

The conclusion `mso_slice_eventuallyPeriodic` is the MSO ingredient the remaining
`wrp_slice_profile_affine` axiom needs: as `n` grows the truth of any
MSO-definable selection condition over the slice is eventually periodic.
-/
import RequestProject.MSO
import RequestProject.SliceAutomata

namespace SliceMSO

open MSO

/-- `List.foldl` over `n` copies of a block equals the `n`-fold iterate of the
one-block transition. -/
theorem foldl_replicate_flatten {Alpha Q : Type*} (f : Q → Alpha → Q) (l : List Alpha) :
    ∀ (n : ℕ) (q : Q),
      List.foldl f q (List.replicate n l).flatten = (fun s => List.foldl f s l)^[n] q := by
  intro n
  induction n with
  | zero => intro q; simp
  | succ n ih =>
      intro q
      rw [List.replicate_succ, List.flatten_cons, List.foldl_append, ih,
        Function.iterate_succ_apply]

/-- A deterministic finite acceptor over `Alpha`. -/
structure DetAuto (Alpha : Type*) where
  Q : Type
  fintypeQ : Fintype Q
  q0 : Q
  δ : Q → Alpha → Q
  accept : Q → Prop

/-- Acceptance: run the automaton and test the final state. -/
def DetAuto.accepts {Alpha : Type*} (M : DetAuto Alpha) (w : List Alpha) : Prop :=
  M.accept (List.foldl M.δ M.q0 w)

namespace DetAuto

/-- The automaton accepting the intersection of two deterministic acceptors. -/
def inter {Alpha : Type*} (M N : DetAuto Alpha) : DetAuto Alpha :=
  let _ := M.fintypeQ
  letI := N.fintypeQ
  { Q := M.Q × N.Q
    fintypeQ := inferInstance
    q0 := (M.q0, N.q0)
    δ := fun q a => (M.δ q.1 a, N.δ q.2 a)
    accept := fun q => M.accept q.1 ∧ N.accept q.2 }

theorem foldl_inter {Alpha : Type*} (M N : DetAuto Alpha) (w : List Alpha)
    (q : (inter M N).Q) :
    List.foldl (inter M N).δ q w =
      (List.foldl M.δ q.1 w, List.foldl N.δ q.2 w) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
      exact ih (M.δ q.1 a, N.δ q.2 a)

/-- Product acceptors recognize conjunction. -/
theorem accepts_inter {Alpha : Type*} (M N : DetAuto Alpha) (w : List Alpha) :
    (inter M N).accepts w ↔ M.accepts w ∧ N.accepts w := by
  unfold DetAuto.accepts
  rw [foldl_inter M N w ((inter M N).q0)]
  simp [inter]

/-- The always-accepting deterministic acceptor. -/
def top {Alpha : Type*} : DetAuto Alpha where
  Q := PUnit
  fintypeQ := inferInstance
  q0 := PUnit.unit
  δ := fun q _ => q
  accept := fun _ => True

theorem accepts_top {Alpha : Type*} (w : List Alpha) :
    (top : DetAuto Alpha).accepts w := by
  simp [DetAuto.accepts, top]

/-- Finite intersection of deterministic acceptors. -/
def all {Alpha : Type*} : List (DetAuto Alpha) → DetAuto Alpha
  | [] => top
  | M :: Ms => inter M (all Ms)

/-- Finite intersections recognize finite conjunctions. -/
theorem accepts_all {Alpha : Type*} :
    ∀ (Ms : List (DetAuto Alpha)) (w : List Alpha),
      (all Ms).accepts w ↔ ∀ M ∈ Ms, M.accepts w
  | [], w => by
      simp [all, accepts_top]
  | M :: Ms, w => by
      simp [all, accepts_inter, accepts_all Ms w]

theorem accepts_all_map {Alpha ι : Type*} (xs : List ι) (F : ι → DetAuto Alpha)
    (w : List Alpha) :
    (all (xs.map F)).accepts w ↔ ∀ x ∈ xs, (F x).accepts w := by
  rw [accepts_all]
  constructor
  · intro h x hx
    exact h (F x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h M hM
    rcases List.mem_map.mp hM with ⟨x, hx, rfl⟩
    exact h x hx

end DetAuto

/-- **Proved automaton fact.**  Acceptance on the one-loop slice
`pre ++ loop^n ++ suf` is eventually periodic in the loop count `n`. -/
theorem detAuto_slice_eventuallyPeriodic {Alpha : Type*} (M : DetAuto Alpha)
    (pre loop suf : List Alpha) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ n, m ≤ n →
      (M.accepts (pre ++ (List.replicate (n + p) loop).flatten ++ suf) ↔
       M.accepts (pre ++ (List.replicate n loop).flatten ++ suf)) := by
  have := M.fintypeQ
  obtain ⟨m, p, hp, hper⟩ := SliceAutomata.iterate_eventuallyPeriodic
    (fun s => List.foldl M.δ s loop) (List.foldl M.δ M.q0 pre)
  refine ⟨m, p, hp, fun n hn => ?_⟩
  simp only [DetAuto.accepts, List.foldl_append, foldl_replicate_flatten]
  rw [hper n hn]

/-- **Büchi–Elgot–Trakhtenbrot (taken as an axiom).**  Every MSO-definable language
over words on a **finite alphabet** is recognised by a deterministic finite
acceptor — the textbook statement (Büchi 1960, Elgot 1961, Trakhtenbrot 1962; see
e.g. Thomas, *Languages, automata, and logic*, 1997).  This is the headline
no-swap and inverse-zeta route's only automata axiom; its converse
`detAuto_state_mso` (below) is a proved **theorem** (2026-08-28), so this is the
repo's only automata admission.  The `[Fintype Alpha]` hypothesis keeps the axiom verbatim-citable: every
use site instantiates `Alpha` at a finite marked alphabet (`Step`, `Marked`,
`Marked2`, `MarkedN m`). -/
axiom buchi {Alpha : Type*} [Fintype Alpha] (φ : MSO.Sentence Alpha) :
    ∃ M : DetAuto Alpha, ∀ w, M.accepts w ↔ φ.Sat w Fin.elim0 Fin.elim0

/-- The state of `M` before position `i` (after reading the first `i` letters of
`w`). -/
def DetAuto.stateBefore {Alpha : Type*} (M : DetAuto Alpha) (w : List Alpha) (i : ℕ) : M.Q :=
  (w.take i).foldl M.δ M.q0

/-! ## Converse Büchi–Elgot–Trakhtenbrot: the run predicate is MSO-definable

Formerly the admitted axiom `detAuto_state_mso`; now a **theorem** (2026-08-28),
by the textbook run encoding: existentially quantify one set variable `X_j` per
state, assert that the sets describe the (unique) run — the first position lies
in `X_{q_0}`, each position lies in exactly one `X_j`, and consecutive positions
respect `δ` — and read the answer off `X_{idx q}` at `x` (with the run's final
state recovered from the last position when `x` lies beyond the word). -/

section DetAutoStateMSO

open MSO MSO.Formula

variable {Alpha : Type*}

/-- Finite disjunction of a list of formulas. -/
private def orList {nf ns : ℕ} : List (Formula Alpha nf ns) → Formula Alpha nf ns
  | [] => .neg .tru
  | φ :: l => .or φ (orList l)

private theorem sat_orList (w : List Alpha) {nf ns : ℕ} (ρ : Fin nf → ℕ)
    (σ : Fin ns → Finset ℕ) (l : List (Formula Alpha nf ns)) :
    Sat w ρ σ (orList l) ↔ ∃ φ ∈ l, Sat w ρ σ φ := by
  induction l with
  | nil => simp [orList]
  | cons φ l ih => simp [orList, ih]

/-- Finite conjunction of a list of formulas. -/
private def andList {nf ns : ℕ} : List (Formula Alpha nf ns) → Formula Alpha nf ns
  | [] => .tru
  | φ :: l => .and φ (andList l)

private theorem sat_andList (w : List Alpha) {nf ns : ℕ} (ρ : Fin nf → ℕ)
    (σ : Fin ns → Finset ℕ) (l : List (Formula Alpha nf ns)) :
    Sat w ρ σ (andList l) ↔ ∀ φ ∈ l, Sat w ρ σ φ := by
  induction l with
  | nil => simp [andList]
  | cons φ l ih => simp [andList, ih]

/-- A block of `m` second-order existential quantifiers. -/
private def exSOs {nf : ℕ} : ∀ {m : ℕ}, Formula Alpha nf m → Formula Alpha nf 0
  | 0, φ => φ
  | _ + 1, φ => exSOs (.exSO φ)

private theorem sat_exSOs (w : List Alpha) {nf : ℕ} (ρ : Fin nf → ℕ) :
    ∀ {m : ℕ} (φ : Formula Alpha nf m),
      Sat w ρ Fin.elim0 (exSOs φ) ↔
        ∃ σ : Fin m → Finset ℕ, (∀ j, ∀ x ∈ σ j, x < w.length) ∧ Sat w ρ σ φ := by
  intro m
  induction m with
  | zero =>
      intro φ
      constructor
      · intro h
        exact ⟨Fin.elim0, fun j => j.elim0, h⟩
      · rintro ⟨σ, -, h⟩
        rwa [show σ = Fin.elim0 from funext fun j => j.elim0] at h
  | succ m ih =>
      intro φ
      show Sat w ρ Fin.elim0 (exSOs (.exSO φ)) ↔ _
      rw [ih (.exSO φ)]
      constructor
      · rintro ⟨σ, hσ, S, hS, hsat⟩
        refine ⟨Fin.cons S σ, fun j => ?_, hsat⟩
        refine Fin.cases ?_ ?_ j
        · simpa using hS
        · intro i
          simpa using hσ i
      · rintro ⟨σ', hσ', hsat⟩
        refine ⟨Fin.tail σ', fun j x hx => hσ' j.succ x hx, σ' 0, fun x hx => hσ' 0 x hx, ?_⟩
        rwa [Fin.cons_self_tail]

/-- `stateBefore` at `0` is the initial state. -/
private theorem stateBefore_zero (M : DetAuto Alpha) (w : List Alpha) :
    M.stateBefore w 0 = M.q0 := rfl

/-- `stateBefore` steps by `δ` on in-range positions. -/
private theorem stateBefore_succ (M : DetAuto Alpha) (w : List Alpha) {p : ℕ}
    (hp : p < w.length) :
    M.stateBefore w (p + 1) = M.δ (M.stateBefore w p) w[p] := by
  unfold DetAuto.stateBefore
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hp]
  rfl

/-- `stateBefore` is constant beyond the end of the word. -/
private theorem stateBefore_of_le (M : DetAuto Alpha) (w : List Alpha) {i : ℕ}
    (h : w.length ≤ i) : M.stateBefore w i = M.stateBefore w w.length := by
  unfold DetAuto.stateBefore
  rw [List.take_of_length_le h, List.take_length]

/-- **The semantic run encoding.**  `M.stateBefore w i = q` holds exactly when
some family of position sets `σ : Fin m → Finset ℕ` (`m = |Q|`, states
enumerated by `e`) describes the run — first position in the initial state's
set, exactly one set per position, `δ`-consistency between consecutive
positions — and the answer can be read off: at an in-range `i` from membership
in `q`'s set, at an out-of-range `i` from the last position (or, on the empty
word, from `q = q_0`). -/
private theorem stateBefore_eq_iff_sets (M : DetAuto Alpha) (q : M.Q)
    {m : ℕ} (e : M.Q ≃ Fin m) (w : List Alpha) (i : ℕ) :
    M.stateBefore w i = q ↔
      ∃ σ : Fin m → Finset ℕ,
        (∀ j, ∀ x ∈ σ j, x < w.length) ∧
        ((∀ p, p < w.length → (¬ ∃ p', p' < w.length ∧ p' < p) → p ∈ σ (e M.q0)) ∧
         (∀ p, p < w.length →
            ∃ j, (p ∈ σ j ∧ ∀ j', j' ≠ j → p ∉ σ j')) ∧
         (∀ p, p < w.length → ∀ p', p' < w.length →
            (p < p' ∧ ¬ ∃ r, r < w.length ∧ p < r ∧ r < p') →
            ∀ j a, p ∈ σ j → w[p]? = some a → p' ∈ σ (e (M.δ (e.symm j) a)))) ∧
        ((i < w.length ∧ i ∈ σ (e q)) ∨
         (¬ i < w.length ∧
           ((∃ p, p < w.length ∧ (¬ ∃ p', p' < w.length ∧ p < p') ∧
              ∃ j a, M.δ (e.symm j) a = q ∧ p ∈ σ j ∧ w[p]? = some a) ∨
            (q = M.q0 ∧ ¬ ∃ p, p < w.length)))) := by
  classical
  constructor
  · -- forward: the canonical run sets
    intro hq
    refine ⟨fun j => (Finset.range w.length).filter (fun p => M.stateBefore w p = e.symm j),
      ?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro j x hx
      exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    · -- INIT
      intro p hp hfirst
      have hp0 : p = 0 := by
        by_contra hne
        exact hfirst ⟨0, by omega, by omega⟩
      subst hp0
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, ?_⟩
      rw [stateBefore_zero, Equiv.symm_apply_apply]
    · -- EXACTLY ONE
      intro p hp
      refine ⟨e (M.stateBefore w p), Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hp, (Equiv.symm_apply_apply e _).symm⟩, ?_⟩
      intro j' hne hmem
      have hst := (Finset.mem_filter.mp hmem).2
      exact hne (by rw [hst, Equiv.apply_symm_apply])
    · -- STEP
      rintro p hp p' hp' ⟨hlt, hbetween⟩ j a hmem ha
      have hsucc : p' = p + 1 := by
        by_contra hne
        exact hbetween ⟨p + 1, by omega, by omega, by omega⟩
      subst hsucc
      have hst : M.stateBefore w p = e.symm j := (Finset.mem_filter.mp hmem).2
      have haa : w[p] = a := by
        have := List.getElem?_eq_getElem hp
        rw [this] at ha
        exact Option.some.inj ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp', ?_⟩
      rw [stateBefore_succ M w hp, hst, haa, Equiv.symm_apply_apply]
    · -- ANSWER
      by_cases hi : i < w.length
      · refine Or.inl ⟨hi, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, ?_⟩⟩
        rw [hq, Equiv.symm_apply_apply]
      · refine Or.inr ⟨hi, ?_⟩
        rcases Nat.eq_zero_or_pos w.length with hlen | hlen
        · -- empty word: the run never leaves `q0`
          refine Or.inr ⟨?_, ?_⟩
          · rw [← hq, stateBefore_of_le M w (by omega)]
            unfold DetAuto.stateBefore
            rw [hlen]
            simp [List.take_zero]
          · rintro ⟨p, hp⟩
            omega
        · -- nonempty word: read the final transition off the last position
          refine Or.inl ⟨w.length - 1, by omega, ?_, e (M.stateBefore w (w.length - 1)),
            w[w.length - 1], ?_, ?_, ?_⟩
          · rintro ⟨p', hp', hgt⟩
            omega
          · rw [Equiv.symm_apply_apply, ← stateBefore_succ M w (by omega)]
            rw [show w.length - 1 + 1 = w.length from by omega]
            rw [← stateBefore_of_le M w (by omega : w.length ≤ i)]
            exact hq
          · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
              (Equiv.symm_apply_apply e _).symm⟩
          · exact List.getElem?_eq_getElem (by omega)
  · -- backward: any consistent family describes the run
    rintro ⟨σ, hbdd, ⟨hinit, hone, hstep⟩, hans⟩
    -- the characterisation of the sets, by induction along the word
    have hchar : ∀ p, p < w.length → ∀ j, (p ∈ σ j ↔ M.stateBefore w p = e.symm j) := by
      intro p
      induction p with
      | zero =>
          intro hp j
          have h0 : 0 ∈ σ (e M.q0) := hinit 0 hp (by rintro ⟨p', -, hlt⟩; omega)
          obtain ⟨j₀, hj₀, huniq⟩ := hone 0 hp
          have hj₀eq : j₀ = e M.q0 := by
            by_contra hne
            exact huniq (e M.q0) (fun h => hne h.symm) h0
          constructor
          · intro hmem
            have : j = j₀ := by
              by_contra hne
              exact huniq j hne hmem
            rw [this, hj₀eq, stateBefore_zero, Equiv.symm_apply_apply]
          · intro hst
            have : j = e M.q0 := by
              rw [stateBefore_zero] at hst
              rw [hst, Equiv.apply_symm_apply]
            rw [this, ← hj₀eq]
            exact hj₀
      | succ p ih =>
          intro hp j
          have hplt : p < w.length := by omega
          have hpmem : p ∈ σ (e (M.stateBefore w p)) :=
            (ih hplt (e (M.stateBefore w p))).mpr (Equiv.symm_apply_apply e _).symm
          have hnext : p + 1 ∈ σ (e (M.stateBefore w (p + 1))) := by
            have := hstep p hplt (p + 1) hp
              ⟨by omega, by rintro ⟨r, -, hr1, hr2⟩; omega⟩
              (e (M.stateBefore w p)) w[p] hpmem (List.getElem?_eq_getElem hplt)
            rwa [Equiv.symm_apply_apply, ← stateBefore_succ M w hplt] at this
          obtain ⟨j₁, hj₁, huniq⟩ := hone (p + 1) hp
          have hj₁eq : j₁ = e (M.stateBefore w (p + 1)) := by
            by_contra hne
            exact huniq _ (fun h => hne h.symm) hnext
          constructor
          · intro hmem
            have : j = j₁ := by
              by_contra hne
              exact huniq j hne hmem
            rw [this, hj₁eq, Equiv.symm_apply_apply]
          · intro hst
            have : j = e (M.stateBefore w (p + 1)) := by
              rw [hst, Equiv.apply_symm_apply]
            rw [this, ← hj₁eq]
            exact hj₁
    rcases hans with ⟨hi, hmem⟩ | ⟨hi, hlast | hempty⟩
    · -- in-range answer
      rw [(hchar i hi (e q)).mp hmem, Equiv.symm_apply_apply]
    · -- out-of-range, nonempty word
      obtain ⟨p, hp, hlastp, j, a, hδ, hmem, ha⟩ := hlast
      have hpeq : p = w.length - 1 := by
        by_contra hne
        exact hlastp ⟨p + 1, by omega, by omega⟩
      have hst : M.stateBefore w p = e.symm j := (hchar p hp j).mp hmem
      have haa : w[p] = a := by
        rw [List.getElem?_eq_getElem hp] at ha
        exact Option.some.inj ha
      rw [stateBefore_of_le M w (by omega)]
      rw [show w.length = p + 1 from by omega, stateBefore_succ M w hp, hst, haa]
      exact hδ
    · -- out-of-range, empty word
      obtain ⟨hq0, hnopos⟩ := hempty
      have hlen : w.length = 0 := by
        by_contra hne
        exact hnopos ⟨0, by omega⟩
      rw [stateBefore_of_le M w (by omega)]
      unfold DetAuto.stateBefore
      rw [hlen]
      simp only [List.take_zero, List.foldl_nil]
      exact hq0.symm

/-! ### The object-language rendering of the run encoding -/

private theorem sat_faFO (w : List Alpha) {nf ns : ℕ} (ρ : Fin nf → ℕ)
    (σ : Fin ns → Finset ℕ) (φ : Formula Alpha (nf + 1) ns) :
    Sat w ρ σ (Formula.faFO φ) ↔ ∀ p, p < w.length → Sat w (Fin.cons p ρ) σ φ := by
  simp only [Formula.faFO, Formula.sat_neg, Formula.sat_exFO]
  constructor
  · intro h p hp
    by_contra hn
    exact h ⟨p, hp, hn⟩
  · rintro h ⟨p, hp, hn⟩
    exact hn (h p hp)

private theorem sat_imp (w : List Alpha) {nf ns : ℕ} (ρ : Fin nf → ℕ)
    (σ : Fin ns → Finset ℕ) (φ ψ : Formula Alpha nf ns) :
    Sat w ρ σ (Formula.imp φ ψ) ↔ (Sat w ρ σ φ → Sat w ρ σ ψ) := by
  simp only [Formula.imp, Formula.sat_or, Formula.sat_neg]
  tauto

private theorem cons_at_one2 {β : Type*} (a : β) (ρ : Fin 2 → β) :
    (Fin.cons a ρ : Fin 3 → β) 1 = ρ 0 := rfl

private theorem cons_at_one1 {β : Type*} (a : β) (ρ : Fin 1 → β) :
    (Fin.cons a ρ : Fin 2 → β) 1 = ρ 0 := rfl

private theorem cons_at_two2 {β : Type*} (a : β) (ρ : Fin 2 → β) :
    (Fin.cons a ρ : Fin 3 → β) 2 = ρ 1 := rfl

private theorem cons_at_one3 {β : Type*} (a : β) (ρ : Fin 3 → β) :
    (Fin.cons a ρ : Fin 4 → β) 1 = ρ 0 := rfl

private theorem cons_at_two3 {β : Type*} (a : β) (ρ : Fin 3 → β) :
    (Fin.cons a ρ : Fin 4 → β) 2 = ρ 1 := rfl

/-- "`x` is a valid position": some position equals `x`. -/
private def validF {m : ℕ} : Formula Alpha 1 m := .exFO (Formula.eqPos 0 1)

private theorem sat_validF {m : ℕ} (w : List Alpha) (ρ : Fin 1 → ℕ)
    (σ : Fin m → Finset ℕ) : Sat w ρ σ validF ↔ ρ 0 < w.length := by
  simp only [validF, Formula.sat_exFO, Formula.sat_eqPos, Fin.cons_zero, cons_at_one1]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro h
    exact ⟨ρ 0, h, rfl⟩

/-- INIT: the first position lies in the initial state's set. -/
private def initF (M : DetAuto Alpha) {m : ℕ} (e : M.Q ≃ Fin m) : Formula Alpha 1 m :=
  Formula.faFO (Formula.imp (.neg (.exFO (.lt 0 1))) (.mem 0 (e M.q0)))

private theorem sat_initF (M : DetAuto Alpha) {m : ℕ} (e : M.Q ≃ Fin m)
    (w : List Alpha) (ρ : Fin 1 → ℕ) (σ : Fin m → Finset ℕ) :
    Sat w ρ σ (initF M e) ↔
      ∀ p, p < w.length → (¬ ∃ p', p' < w.length ∧ p' < p) → p ∈ σ (e M.q0) := by
  rw [initF, sat_faFO]
  refine forall_congr' fun p => imp_congr_right fun _ => ?_
  rw [sat_imp]
  simp only [Formula.sat_neg, Formula.sat_exFO, Formula.sat_lt, Formula.sat_mem,
    Fin.cons_zero, cons_at_one2]

/-- EXACTLY ONE: every position lies in exactly one state set. -/
private def oneF {m : ℕ} : Formula Alpha 1 m :=
  Formula.faFO (orList ((List.finRange m).map (fun j =>
    .and (.mem 0 j) (andList ((List.finRange m).map (fun j' =>
      if j' = j then Formula.tru else .neg (.mem 0 j')))))))

private theorem sat_oneF {m : ℕ} (w : List Alpha) (ρ : Fin 1 → ℕ)
    (σ : Fin m → Finset ℕ) :
    Sat w ρ σ oneF ↔
      ∀ p, p < w.length → ∃ j, (p ∈ σ j ∧ ∀ j', j' ≠ j → p ∉ σ j') := by
  rw [oneF, sat_faFO]
  refine forall_congr' fun p => imp_congr_right fun _ => ?_
  rw [sat_orList]
  constructor
  · rintro ⟨φ, hφ, hsat⟩
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.sat_and, Formula.sat_mem, Fin.cons_zero] at hsat
    obtain ⟨hmem, hrest⟩ := hsat
    refine ⟨j, hmem, fun j' hne hmem' => ?_⟩
    have hin := (sat_andList w _ σ _).mp hrest _
      (List.mem_map.mpr ⟨j', List.mem_finRange j', rfl⟩)
    rw [if_neg hne] at hin
    rw [Formula.sat_neg, Formula.sat_mem, Fin.cons_zero] at hin
    exact hin hmem'
  · rintro ⟨j, hmem, huniq⟩
    refine ⟨_, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩, ?_⟩
    rw [Formula.sat_and, Formula.sat_mem, Fin.cons_zero]
    refine ⟨hmem, (sat_andList w _ σ _).mpr ?_⟩
    rintro φ hφ
    obtain ⟨j', -, rfl⟩ := List.mem_map.mp hφ
    by_cases hj' : j' = j
    · rw [if_pos hj']
      trivial
    · rw [if_neg hj']
      rw [Formula.sat_neg, Formula.sat_mem, Fin.cons_zero]
      exact huniq j' hj'

/-- STEP: consecutive positions respect `δ`. -/
private noncomputable def stepF [Fintype Alpha] (M : DetAuto Alpha) {m : ℕ}
    (e : M.Q ≃ Fin m) : Formula Alpha 1 m :=
  Formula.faFO (Formula.faFO (Formula.imp
    (.and (.lt 1 0) (.neg (.exFO (.and (.lt 2 0) (.lt 0 1)))))
    (andList ((List.finRange m).map (fun j =>
      andList (((Finset.univ : Finset Alpha).toList).map (fun a =>
        Formula.imp (.and (.mem 1 j) (.labelEq 1 a))
          (.mem 0 (e (M.δ (e.symm j) a))))))))))

private theorem sat_stepF [Fintype Alpha] (M : DetAuto Alpha) {m : ℕ}
    (e : M.Q ≃ Fin m) (w : List Alpha) (ρ : Fin 1 → ℕ) (σ : Fin m → Finset ℕ) :
    Sat w ρ σ (stepF M e) ↔
      ∀ p, p < w.length → ∀ p', p' < w.length →
        (p < p' ∧ ¬ ∃ r, r < w.length ∧ p < r ∧ r < p') →
        ∀ j a, p ∈ σ j → w[p]? = some a → p' ∈ σ (e (M.δ (e.symm j) a)) := by
  rw [stepF, sat_faFO]
  refine forall_congr' fun p => imp_congr_right fun _ => ?_
  rw [sat_faFO]
  refine forall_congr' fun p' => imp_congr_right fun _ => ?_
  rw [sat_imp]
  simp only [Formula.sat_and, Formula.sat_neg, Formula.sat_exFO, Formula.sat_lt,
    Fin.cons_zero, cons_at_one2, cons_at_one3, cons_at_two3]
  refine imp_congr_right fun _ => ?_
  rw [sat_andList]
  constructor
  · intro h j a hmem ha
    have hj := h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rw [sat_andList] at hj
    have hja := hj _ (List.mem_map.mpr ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), rfl⟩)
    rw [sat_imp, Formula.sat_and, Formula.sat_mem, Formula.sat_labelEq,
      Formula.sat_mem, Fin.cons_zero, cons_at_one2] at hja
    exact hja ⟨hmem, ha⟩
  · intro h φ hφ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hφ
    rw [sat_andList]
    rintro ψ hψ
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hψ
    rw [sat_imp, Formula.sat_and, Formula.sat_mem, Formula.sat_labelEq,
      Formula.sat_mem, Fin.cons_zero, cons_at_one2]
    rintro ⟨hmem, ha⟩
    exact h j a hmem ha

open Classical in
/-- ANSWER: read the state at `x` off the sets — via membership for an
in-range `x`, via the last position (or the empty-word case) beyond. -/
private noncomputable def answerF [Fintype Alpha] (M : DetAuto Alpha) {m : ℕ}
    (e : M.Q ≃ Fin m) (q : M.Q) : Formula Alpha 1 m :=
  .or (.and validF (.mem 0 (e q)))
    (.and (.neg validF)
      (.or (.exFO (.and (.neg (.exFO (.lt 1 0)))
          (orList ((List.finRange m).flatMap (fun j =>
            ((Finset.univ : Finset Alpha).toList).map (fun a =>
              if M.δ (e.symm j) a = q then .and (.mem 0 j) (.labelEq 0 a)
              else .neg .tru))))))
        (if q = M.q0 then .neg (.exFO .tru) else .neg .tru)))

private theorem sat_answerF [Fintype Alpha] (M : DetAuto Alpha) {m : ℕ}
    (e : M.Q ≃ Fin m) (q : M.Q) (w : List Alpha) (ρ : Fin 1 → ℕ)
    (σ : Fin m → Finset ℕ) :
    Sat w ρ σ (answerF M e q) ↔
      ((ρ 0 < w.length ∧ ρ 0 ∈ σ (e q)) ∨
       (¬ ρ 0 < w.length ∧
         ((∃ p, p < w.length ∧ (¬ ∃ p', p' < w.length ∧ p < p') ∧
            ∃ j a, M.δ (e.symm j) a = q ∧ p ∈ σ j ∧ w[p]? = some a) ∨
          (q = M.q0 ∧ ¬ ∃ p, p < w.length)))) := by
  classical
  rw [answerF, Formula.sat_or, Formula.sat_and, Formula.sat_and, Formula.sat_neg,
    sat_validF, Formula.sat_mem, Formula.sat_or]
  refine or_congr Iff.rfl (and_congr Iff.rfl (or_congr ?_ ?_))
  · -- the last-position clause
    rw [Formula.sat_exFO]
    refine exists_congr fun p => and_congr_right fun _ => ?_
    rw [Formula.sat_and, Formula.sat_neg, Formula.sat_exFO, sat_orList]
    refine and_congr ?_ ?_
    · constructor
      · intro h hex
        obtain ⟨p', hp', hgt⟩ := hex
        refine h ⟨p', hp', ?_⟩
        simp only [Formula.sat_lt, Fin.cons_zero, cons_at_one2]
        exact hgt
      · rintro h ⟨p', hp', hgt⟩
        simp only [Formula.sat_lt, Fin.cons_zero, cons_at_one2] at hgt
        exact h ⟨p', hp', hgt⟩
    · constructor
      · rintro ⟨φ, hφ, hsat⟩
        obtain ⟨j, -, hmem2⟩ := List.mem_flatMap.mp hφ
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hmem2
        by_cases hδ : M.δ (e.symm j) a = q
        · rw [if_pos hδ, Formula.sat_and, Formula.sat_mem, Formula.sat_labelEq,
            Fin.cons_zero] at hsat
          exact ⟨j, a, hδ, hsat.1, hsat.2⟩
        · rw [if_neg hδ] at hsat
          exact absurd trivial hsat
      · rintro ⟨j, a, hδ, hmem, ha⟩
        refine ⟨_, List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
          List.mem_map.mpr ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), rfl⟩⟩, ?_⟩
        rw [if_pos hδ, Formula.sat_and, Formula.sat_mem, Formula.sat_labelEq,
          Fin.cons_zero]
        exact ⟨hmem, ha⟩
  · -- the empty-word clause
    by_cases hq0 : q = M.q0
    · rw [if_pos hq0]
      simp only [Formula.sat_neg, Formula.sat_exFO, Formula.sat_tru, and_true]
      constructor
      · intro h
        exact ⟨hq0, h⟩
      · rintro ⟨-, h⟩
        exact h
    · rw [if_neg hq0]
      simp only [Formula.sat_neg, Formula.sat_tru, not_true]
      constructor
      · intro h
        exact h.elim
      · rintro ⟨h, -⟩
        exact hq0 h

end DetAutoStateMSO

/-- **Converse Büchi–Elgot–Trakhtenbrot — now a THEOREM (2026-08-28; formerly
the sixth admitted axiom).**  The run of a deterministic finite automaton is
MSO-definable: for a `DetAuto M` over a finite alphabet and a state `q`, the
predicate "`M` is in state `q` after reading the length-`x` prefix of `w`" is
MSO-definable in the free position variable `x`.  This is the automaton ⇒ MSO
half of Büchi–Elgot–Trakhtenbrot — the converse of `buchi` (the MSO ⇒
automaton half, still admitted).  Proof: the textbook run encoding — one
existential set variable per state pinned by first-position, exactly-one, and
`δ`-consistency conditions (`stateBefore_eq_iff_sets`), rendered in the object
language by the quantifier block `exSOs` and the finite `orList`/`andList`
combinators.  Used by the §4 minimality result `bounded_rank_collapse`
(`WRPBoundedRank.lean`), whose trust base this discharge makes axiom-clean. -/
theorem detAuto_state_mso {Alpha : Type*} [Fintype Alpha] (M : DetAuto Alpha) (q : M.Q) :
    MSO.MSODefinableRel 1 (fun w ī => M.stateBefore w (ī 0) = q) := by
  classical
  let _ := M.fintypeQ
  refine ⟨exSOs (.and (.and (initF M (Fintype.equivFin M.Q))
      (.and oneF (stepF M (Fintype.equivFin M.Q))))
      (answerF M (Fintype.equivFin M.Q) q)), fun w ρ => ?_⟩
  show M.stateBefore w (ρ 0) = q ↔ _
  rw [stateBefore_eq_iff_sets M q (Fintype.equivFin M.Q) w (ρ 0), sat_exSOs]
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  rw [MSO.Formula.sat_and, MSO.Formula.sat_and, MSO.Formula.sat_and,
    sat_initF, sat_oneF, sat_stepF, sat_answerF]

/-- **Lemma 7.2 (`lem:one-loop-finite-state`, MSO side), factored.**  The truth of an MSO sentence on the
one-loop slice `pre ++ loop^n ++ suf` is eventually periodic in the loop count.
Proved from the Büchi axiom together with the proved automaton periodicity. -/
theorem mso_slice_eventuallyPeriodic {Alpha : Type*} [Fintype Alpha] (φ : MSO.Sentence Alpha)
    (pre loop suf : List Alpha) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ n, m ≤ n →
      (φ.Sat (pre ++ (List.replicate (n + p) loop).flatten ++ suf) Fin.elim0 Fin.elim0 ↔
       φ.Sat (pre ++ (List.replicate n loop).flatten ++ suf) Fin.elim0 Fin.elim0) := by
  obtain ⟨M, hM⟩ := buchi φ
  obtain ⟨m, p, hp, hper⟩ := detAuto_slice_eventuallyPeriodic M pre loop suf
  exact ⟨m, p, hp, fun n hn => by rw [← hM, ← hM]; exact hper n hn⟩

end SliceMSO
