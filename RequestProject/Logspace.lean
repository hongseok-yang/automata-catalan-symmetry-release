/-
# Deterministic logspace transductions and the separation half of
# `thm:wrp-strict-below-logspace`

Machine model and separation witness for the revision's Theorem "Below
logspace" (`thm:wrp-strict-below-logspace`, paper.tex,
proof Appendix A.3 lines 4538–4601): `WRP` is a proper subclass of the
word-to-word maps computable in deterministic logspace.

**The model** (`CounterDFT`): a deterministic two-way transducer with a single
head on `⊢w⊣` (reusing `TwoDFT.TapeSym` / `TwoDFT.tapeSym` / `TwoDFT.moveDir`
and the end-marker discipline of `def:2dft`) extended with `c` ℕ-valued
counters supporting increment / decrement / keep and zero-tests.  A machine
whose counters stay `O(n)`-bounded (`SpaceBound`) is exactly a deterministic
`O(log n)`-space word-to-word transducer: each counter of magnitude `O(n)` is
an `O(log n)`-bit register, and conversely an `O(log n)`-bit worktape splits
into constantly many `O(n)`-bounded counters — the classical multihead/counter
characterisation of deterministic logspace (Hartmanis, "On non-determinancy
in simple computing devices", Acta Informatica 1, 1972; cited background,
exactly as the repository treats Engelfriet–Hoogeboom for `thm:eh`).
`IsLogspaceMap` is the resulting class of partial word-to-word maps.

**Contents.**

* `CounterOp` / `CounterDFT` / `Steps` / `Halted` / `Computes` — the model,
  with determinism (`steps_unique`, `computes_unique`), transitivity, a
  generic reachability-invariant lemma (`steps_invariant`), and one-way
  scanning evaluators (`steps_scan_right`, `steps_scan_left`).
* `SpaceBound` / `IsLogspaceMap` — the linear counter bound and the
  logspace-computable partial maps.
* `ofTwoDFT` — every 2DFT is a `CounterDFT` with `c = 0` counters;
  `isLogspaceMap_of_twoDFT`, and `sMap_isLogspace` for the machine `S` of
  `thm:wrp-not-closed`.
* `lspFge0` — a 5-state 1-counter machine computing the separating map
  `F_{≥0}` of Appendix A.3 (scan pass maintaining the prefix height, return
  pass, copy pass); `lspFge0_computes`, `Fge0_isLogspace`.
* `exists_logspace_not_wrp` — **the separation half of
  `thm:wrp-strict-below-logspace`**: a logspace map that is not WRP.
* `wrp_strict_below_logspace_of_evaluator` — the paper-shaped statement,
  relative to the containment `thm:wrp-logspace` as an explicit hypothesis.

Trust: the model theory, `lspFge0_computes` and `Fge0_isLogspace` are
axiom-clean; `exists_logspace_not_wrp` and the packaged statement additionally
admit `SliceMSO.buchi` (inherited from `Fge0_not_isWRP`).
-/
import RequestProject.TwoDFT
import RequestProject.SMapWRP

namespace Logspace

open TwoDFT

variable {Alpha Gamma : Type*} {c : ℕ}

/-! ## Counter operations -/

/-- A per-step operation on one counter: increment, decrement (monus), keep. -/
inductive CounterOp | inc | dec | keep
  deriving DecidableEq

/-- Apply a counter operation to a counter value (`dec` is truncated). -/
def CounterOp.apply : CounterOp → ℕ → ℕ
  | inc, n => n + 1
  | dec, n => n - 1
  | keep, n => n

@[simp] theorem CounterOp.apply_inc (n : ℕ) : CounterOp.inc.apply n = n + 1 := rfl
@[simp] theorem CounterOp.apply_dec (n : ℕ) : CounterOp.dec.apply n = n - 1 := rfl
@[simp] theorem CounterOp.apply_keep (n : ℕ) : CounterOp.keep.apply n = n := rfl

/-! ## The machine -/

open TwoDFT in
/-- **Deterministic bounded-counter two-way transducer.**  A 2DFT head on
`⊢w⊣` (same tape alphabet and end-marker discipline as `def:2dft`) plus `c`
ℕ-valued counters; each transition observes the state, the tape symbol, and
the zero-pattern of the counters, and outputs a new state, a direction, a
counter operation per counter, and an emitted word. -/
structure CounterDFT (Alpha Gamma : Type*) (c : ℕ) where
  Q : Type
  fintypeQ : Fintype Q
  q0 : Q
  F : Q → Prop
  η : Q → TapeSym Alpha → (Fin c → Bool) →
        Option (Q × Bool × (Fin c → CounterOp) × List Gamma)
  /-- End-marker discipline: a transition from `⊢`, if defined, moves right. -/
  lmark_right : ∀ q z r, η q .lmark z = some r → r.2.1 = true
  /-- End-marker discipline: a transition from `⊣`, if defined, moves left. -/
  rmark_left : ∀ q z r, η q .rmark z = some r → r.2.1 = false

namespace CounterDFT

variable (M : CounterDFT Alpha Gamma c)

/-- The step relation, with accumulated emission: a configuration is
`(state, head position, counter values)`; the zero-pattern fed to `η` is
`fun j => cnt j == 0`, and the new counters apply the emitted operations. -/
inductive Steps (w : List Alpha) :
    M.Q × ℕ × (Fin c → ℕ) → List Gamma → M.Q × ℕ × (Fin c → ℕ) → Prop
  | refl (cfg : M.Q × ℕ × (Fin c → ℕ)) : Steps w cfg [] cfg
  | head {q : M.Q} {i : ℕ} {cnt : Fin c → ℕ} {q' : M.Q} {d : Bool}
      {ops : Fin c → CounterOp} {u out : List Gamma} {e : M.Q × ℕ × (Fin c → ℕ)} :
      M.η q (tapeSym w i) (fun j => cnt j == 0) = some (q', d, ops, u) →
      Steps w (q', moveDir i d, fun j => (ops j).apply (cnt j)) out e →
      Steps w (q, i, cnt) (u ++ out) e

/-- A configuration on which `η` is undefined: the run halts there. -/
def Halted (w : List Alpha) (cfg : M.Q × ℕ × (Fin c → ℕ)) : Prop :=
  M.η cfg.1 (tapeSym w cfg.2.1) (fun j => cfg.2.2 j == 0) = none

/-- The computed partial map: the maximal run from `(q₀, 0, 0̄)` is finite,
halts acceptingly, and the emitted words concatenate to `out`. -/
def Computes (w : List Alpha) (out : List Gamma) : Prop :=
  ∃ e, M.Steps w (M.q0, 0, fun _ => 0) out e ∧ M.Halted w e ∧ M.F e.1

end CounterDFT

/-- **The linear counter bound**: along every run from the initial
configuration, every counter stays `≤ C·(n+1)` — i.e. each counter is an
`O(log n)`-bit register.  (The head position needs no bound: the end-marker
discipline keeps it in `[0, n+1]`.) -/
def SpaceBound (M : CounterDFT Alpha Gamma c) (C : ℕ) : Prop :=
  ∀ w out e, M.Steps w (M.q0, 0, fun _ => 0) out e → ∀ j, e.2.2 j ≤ C * (w.length + 1)

/-- **Deterministic-logspace word-to-word maps**: computed by some
bounded-counter two-way transducer whose counters are linearly bounded
(= logarithmically many bits; Hartmanis 1972). -/
def IsLogspaceMap (f : List Alpha → Option (List Gamma)) : Prop :=
  ∃ (c C : ℕ) (M : CounterDFT Alpha Gamma c), SpaceBound M C ∧
    ∀ w out, f w = some out ↔ M.Computes w out

/-! ## Determinism and the reachability invariant -/

namespace CounterDFT

variable {M : CounterDFT Alpha Gamma c}

/-- A configuration with a defined transition has not halted. -/
theorem not_halted_of_step {w : List Alpha} {q : M.Q} {i : ℕ} {cnt : Fin c → ℕ}
    {r : M.Q × Bool × (Fin c → CounterOp) × List Gamma}
    (hη : M.η q (tapeSym w i) (fun j => cnt j == 0) = some r) :
    ¬ M.Halted w (q, i, cnt) := by
  intro hh
  have hnone : M.η q (tapeSym w i) (fun j => cnt j == 0) = none := hh
  rw [hnone] at hη
  simp at hη

/-- Transitivity of the step relation, concatenating emissions. -/
theorem Steps.trans {w : List Alpha} :
    ∀ {c₁ c₂ c₃ : M.Q × ℕ × (Fin c → ℕ)} {o₁ o₂ : List Gamma},
    M.Steps w c₁ o₁ c₂ → M.Steps w c₂ o₂ c₃ → M.Steps w c₁ (o₁ ++ o₂) c₃ := by
  intro c₁ c₂ c₃ o₁ o₂ h₁
  induction h₁ with
  | refl cfg => intro h₂; simpa using h₂
  | head hη _ ih =>
      intro h₂
      rw [List.append_assoc]
      exact Steps.head hη (ih h₂)

/-- **Determinism: the maximal run is unique.**  Two halting runs from the
same configuration have the same emission and the same halting
configuration. -/
theorem steps_unique {w : List Alpha} :
    ∀ {cfg : M.Q × ℕ × (Fin c → ℕ)} {out₁ out₂ : List Gamma}
      {e₁ e₂ : M.Q × ℕ × (Fin c → ℕ)},
    M.Steps w cfg out₁ e₁ → M.Halted w e₁ →
    M.Steps w cfg out₂ e₂ → M.Halted w e₂ →
    out₁ = out₂ ∧ e₁ = e₂ := by
  intro cfg out₁ out₂ e₁ e₂ h₁
  induction h₁ generalizing out₂ e₂ with
  | refl cfg =>
      intro halt₁ h₂ halt₂
      cases h₂ with
      | refl => exact ⟨rfl, rfl⟩
      | head hη _ => exact absurd halt₁ (not_halted_of_step hη)
  | head hη rest ih =>
      intro halt₁ h₂ halt₂
      cases h₂ with
      | refl => exact absurd halt₂ (not_halted_of_step hη)
      | head hη' rest' =>
          rw [hη] at hη'
          injection hη' with htuple
          injection htuple with hq hrest
          injection hrest with hd hrest'
          injection hrest' with hops hu
          subst hq; subst hd; subst hops; subst hu
          obtain ⟨ho, he⟩ := ih halt₁ rest' halt₂
          exact ⟨by rw [ho], he⟩

/-- The computed map is a partial function. -/
theorem computes_unique {w : List Alpha} {out₁ out₂ : List Gamma}
    (h₁ : M.Computes w out₁) (h₂ : M.Computes w out₂) : out₁ = out₂ := by
  obtain ⟨e₁, hs₁, hh₁, -⟩ := h₁
  obtain ⟨e₂, hs₂, hh₂, -⟩ := h₂
  exact (steps_unique hs₁ hh₁ hs₂ hh₂).1

/-- **Reachability invariant**: a property of configurations that holds at the
start and is preserved by every single step holds at the end of any `Steps`
segment.  (Used for the space bound: every reachable configuration is the end
of some `Steps` prefix.) -/
theorem steps_invariant {w : List Alpha} {P : M.Q × ℕ × (Fin c → ℕ) → Prop}
    (hstep : ∀ q i cnt q' d ops u, P (q, i, cnt) →
      M.η q (tapeSym w i) (fun j => cnt j == 0) = some (q', d, ops, u) →
      P (q', moveDir i d, fun j => (ops j).apply (cnt j))) :
    ∀ {cfg e : M.Q × ℕ × (Fin c → ℕ)} {out : List Gamma},
      M.Steps w cfg out e → P cfg → P e := by
  intro cfg e out h
  induction h with
  | refl cfg => exact id
  | head hη _ ih =>
      intro hP
      exact ih (hstep _ _ _ _ _ _ _ hP hη)

end CounterDFT

/-! ## One-way scanning evaluators -/

namespace CounterDFT

variable {M : CounterDFT Alpha Gamma c}

/-- **Rightward scanning** (counter-aware `TwoDFT.steps_scan`): if state `q`
self-loops rightward on every letter of a segment `l` keeping all counters,
emitting `em a` on each `a` (whatever the zero-pattern), then the machine
sweeps the segment emitting `l.flatMap em` with unchanged counters. -/
theorem steps_scan_right {w : List Alpha} {q : M.Q} {em : Alpha → List Gamma}
    {cnt : Fin c → ℕ} (l : List Alpha) (i : ℕ)
    (hcells : ∀ k, (hk : k < l.length) → tapeSym w (i + k) = TapeSym.letter l[k])
    (hloop : ∀ a ∈ l, ∀ z, M.η q (TapeSym.letter a) z
      = some (q, true, fun _ => CounterOp.keep, em a)) :
    M.Steps w (q, i, cnt) (l.flatMap em) (q, i + l.length, cnt) := by
  induction l generalizing i with
  | nil => simpa using Steps.refl (M := M) (w := w) (q, i, cnt)
  | cons a t ih =>
      have hcell0 : tapeSym w i = TapeSym.letter a := by
        have h := hcells 0 (by simp)
        rw [List.getElem_cons_zero] at h
        simpa using h
      have hstep : M.η q (tapeSym w i) (fun j => cnt j == 0)
          = some (q, true, fun _ => CounterOp.keep, em a) := by
        rw [hcell0]
        exact hloop a List.mem_cons_self _
      have hrest : M.Steps w (q, i + 1, cnt) (t.flatMap em)
          (q, (i + 1) + t.length, cnt) := by
        refine ih (i + 1) (fun k hk => ?_)
          (fun a' ha' => hloop a' (List.mem_cons_of_mem _ ha'))
        have h := hcells (k + 1) (by simpa using Nat.succ_lt_succ hk)
        rw [show i + (k + 1) = (i + 1) + k by omega] at h
        simpa using h
      have h := Steps.head (M := M) hstep hrest
      rw [show (i + 1) + t.length = i + (a :: t).length by simp; omega] at h
      simpa using h

/-- **Leftward return scanning**: if state `q` self-loops leftward on every
letter keeping all counters and emitting nothing, then from any position
`i ≤ |w|` the machine returns to the left end marker with unchanged
counters. -/
theorem steps_scan_left {w : List Alpha} {q : M.Q} {cnt : Fin c → ℕ}
    (hloop : ∀ (a : Alpha) (z : Fin c → Bool), M.η q (TapeSym.letter a) z
      = some (q, false, fun _ => CounterOp.keep, ([] : List Gamma))) :
    ∀ i, i ≤ w.length → M.Steps w (q, i, cnt) [] (q, 0, cnt) := by
  intro i
  induction i with
  | zero => intro _; exact Steps.refl (M := M) (w := w) (q, 0, cnt)
  | succ k ih =>
      intro hk
      have hcell : tapeSym w (k + 1) = TapeSym.letter w[k] :=
        tapeSym_succ w k (by omega)
      have hstep : M.η q (tapeSym w (k + 1)) (fun j => cnt j == 0)
          = some (q, false, fun _ => CounterOp.keep, ([] : List Gamma)) := by
        rw [hcell]
        exact hloop _ _
      have hrest : M.Steps w (q, k, cnt) [] (q, 0, cnt) := ih (by omega)
      have h := Steps.head (M := M) hstep hrest
      simpa using h

end CounterDFT

/-! ## Every 2DFT is a counter machine with no counters -/

/-- A 2DFT (`def:2dft`) is a `CounterDFT` with `c = 0` counters: the empty
zero-pattern is ignored and the counter-operation vector is empty. -/
def ofTwoDFT (T : TwoDFT Alpha Gamma) : CounterDFT Alpha Gamma 0 where
  Q := T.Q
  fintypeQ := T.fintypeQ
  q0 := T.q0
  F := T.F
  η := fun q s _ => (T.η q s).map fun r => (r.1, r.2.1, Fin.elim0, r.2.2)
  lmark_right := by
    intro q z r h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨q', d, u⟩, hT, rfl⟩ := h
    exact T.lmark_right q q' d u hT
  rmark_left := by
    intro q z r h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨q', d, u⟩, hT, rfl⟩ := h
    exact T.rmark_left q q' d u hT

/-- Runs of the 2DFT transfer to the counter machine (counters unchanged). -/
theorem ofTwoDFT_steps_of {T : TwoDFT Alpha Gamma} {w : List Alpha} :
    ∀ {p e : T.Q × ℕ} {out : List Gamma}, T.Steps w p out e →
      ∀ cnt : Fin 0 → ℕ,
        (ofTwoDFT T).Steps w (p.1, p.2, cnt) out (e.1, e.2, cnt) := by
  intro p e out h
  induction h with
  | refl p => intro cnt; exact CounterDFT.Steps.refl _
  | @head q i q' d u out' e' hη hrest ih =>
      intro cnt
      have hη' : (ofTwoDFT T).η q (tapeSym w i) (fun j => cnt j == 0)
          = some (q', d, Fin.elim0, u) := by
        show (T.η q (tapeSym w i)).map (fun r => (r.1, r.2.1, Fin.elim0, r.2.2))
            = some (q', d, Fin.elim0, u)
        rw [hη, Option.map_some]
      have goalstep : (ofTwoDFT T).Steps w
          (q', moveDir i d, fun j => ((Fin.elim0 : Fin 0 → CounterOp) j).apply (cnt j))
          out' (e'.1, e'.2, cnt) := by
        have hcnt : (fun j : Fin 0 =>
            ((Fin.elim0 : Fin 0 → CounterOp) j).apply (cnt j)) = cnt :=
          funext fun j => j.elim0
        rw [hcnt]
        exact ih cnt
      exact CounterDFT.Steps.head hη' goalstep

/-- Runs of the counter machine project back to runs of the 2DFT. -/
theorem steps_of_ofTwoDFT {T : TwoDFT Alpha Gamma} {w : List Alpha} :
    ∀ {cfg e : (ofTwoDFT T).Q × ℕ × (Fin 0 → ℕ)} {out : List Gamma},
      (ofTwoDFT T).Steps w cfg out e → T.Steps w (cfg.1, cfg.2.1) out (e.1, e.2.1) := by
  intro cfg e out h
  induction h with
  | refl cfg => exact TwoDFT.Steps.refl _
  | @head q i cnt q' d ops u out' e' hη hrest ih =>
      have hη' : (T.η q (tapeSym w i)).map (fun r => (r.1, r.2.1, Fin.elim0, r.2.2))
          = some (q', d, ops, u) := hη
      obtain ⟨⟨q₁, d₁, u₁⟩, hT, heq⟩ := Option.map_eq_some_iff.mp hη'
      injection heq with hq hrest2
      injection hrest2 with hd hrest3
      injection hrest3 with hops hu
      subst hq; subst hd; subst hu
      exact TwoDFT.Steps.head hT ih

/-- Halting transfers in both directions. -/
theorem ofTwoDFT_halted_iff {T : TwoDFT Alpha Gamma} {w : List Alpha}
    (q : T.Q) (i : ℕ) (cnt : Fin 0 → ℕ) :
    (ofTwoDFT T).Halted w (q, i, cnt) ↔ T.Halted w (q, i) := by
  show (T.η q (tapeSym w i)).map (fun r => (r.1, r.2.1, Fin.elim0, r.2.2)) = none
    ↔ T.η q (tapeSym w i) = none
  exact Option.map_eq_none_iff

/-- The embedded machine computes exactly what the 2DFT computes. -/
theorem ofTwoDFT_computes_iff {T : TwoDFT Alpha Gamma} {w : List Alpha}
    {out : List Gamma} :
    (ofTwoDFT T).Computes w out ↔ T.Computes w out := by
  constructor
  · rintro ⟨e, hs, hh, hF⟩
    exact ⟨(e.1, e.2.1), steps_of_ofTwoDFT hs,
      (ofTwoDFT_halted_iff e.1 e.2.1 e.2.2).mp hh, hF⟩
  · rintro ⟨e, hs, hh, hF⟩
    exact ⟨(e.1, e.2, fun _ => 0), ofTwoDFT_steps_of hs (fun _ => 0),
      (ofTwoDFT_halted_iff e.1 e.2 _).mpr hh, hF⟩

/-- **Every 2DFT-computable map is a logspace map** (with `c = 0` counters the
space bound is vacuous). -/
theorem isLogspaceMap_of_twoDFT {f : List Alpha → Option (List Gamma)}
    (T : TwoDFT Alpha Gamma)
    (hT : ∀ w out, f w = some out ↔ T.Computes w out) : IsLogspaceMap f := by
  refine ⟨0, 0, ofTwoDFT T, ?_, fun w out => (hT w out).trans ofTwoDFT_computes_iff.symm⟩
  intro w out e _ j
  exact j.elim0

/-- The map `sMap` computed by the left-to-right machine `S` of
`thm:wrp-not-closed` is a logspace map (via the 2DFT embedding and
`compS_computes_iff_sMap`). -/
theorem sMap_isLogspace : IsLogspaceMap WRPComp.sMap :=
  isLogspaceMap_of_twoDFT WRPComp.compS
    (fun y out => (WRPComp.compS_computes_iff_sMap y out).symm)

/-! ## The 1-counter machine for `F_{≥0}` (Appendix A.3, lines 4581–4587)

One scan pass maintains the running prefix height in the counter; a `D` read
at counter `0` would drive the height to `-1` *after* that letter, and whether
that violates `Lnn` depends on whether the letter was the last one (`Lnn`
constrains **proper** prefixes only) — hence the pending state.  A genuine
violation sinks (output `ε`); otherwise the head returns to `⊢` and a copy
pass emits the verbatim relabelled input. -/

open Step

/-- States: scanning (height in the counter), pending (a `D` at height `0`
just read), returning left, copying, and the emitless sink. -/
inductive LState | scan | pend | back | copy | sink
  deriving DecidableEq

instance : Fintype LState :=
  ⟨⟨{.scan, .pend, .back, .copy, .sink}, by decide⟩, fun x => by cases x <;> decide⟩

/-- **The 1-counter machine for `F_{≥0}`** (the logspace half of the proof of
`thm:wrp-strict-below-logspace`, paper.tex): scan
right maintaining the height, branch on the zero-test at each `D`, return,
and copy iff no proper prefix went negative. -/
def lspFge0 : CounterDFT Step WRPComp.GBD 1 where
  Q := LState
  fintypeQ := inferInstance
  q0 := LState.scan
  F := fun _ => True
  η := fun q s z => match q, s with
    | LState.scan, TapeSym.lmark =>
        some (LState.scan, true, fun _ => CounterOp.keep, [])
    | LState.scan, TapeSym.letter U =>
        some (LState.scan, true, fun _ => CounterOp.inc, [])
    | LState.scan, TapeSym.letter D =>
        if z ⟨0, Nat.one_pos⟩ then some (LState.pend, true, fun _ => CounterOp.keep, [])
        else some (LState.scan, true, fun _ => CounterOp.dec, [])
    | LState.scan, TapeSym.rmark =>
        some (LState.back, false, fun _ => CounterOp.keep, [])
    | LState.pend, TapeSym.letter _ =>
        some (LState.sink, true, fun _ => CounterOp.keep, [])
    | LState.pend, TapeSym.rmark =>
        some (LState.back, false, fun _ => CounterOp.keep, [])
    | LState.back, TapeSym.letter _ =>
        some (LState.back, false, fun _ => CounterOp.keep, [])
    | LState.back, TapeSym.lmark =>
        some (LState.copy, true, fun _ => CounterOp.keep, [])
    | LState.copy, TapeSym.letter x =>
        some (LState.copy, true, fun _ => CounterOp.keep, [WRPComp.relStep x])
    | LState.sink, TapeSym.letter _ =>
        some (LState.sink, true, fun _ => CounterOp.keep, [])
    | _, _ => none
  lmark_right := by
    intro q z r h
    cases q <;> simp_all <;> (subst h; rfl)
  rmark_left := by
    intro q z r h
    cases q <;> simp_all <;> (subst h; rfl)

@[simp] theorem lspFge0_η_scan_lmark (z : Fin 1 → Bool) :
    lspFge0.η LState.scan TapeSym.lmark z
      = some (LState.scan, true, fun _ => CounterOp.keep, []) := rfl

@[simp] theorem lspFge0_η_scan_U (z : Fin 1 → Bool) :
    lspFge0.η LState.scan (TapeSym.letter U) z
      = some (LState.scan, true, fun _ => CounterOp.inc, []) := rfl

@[simp] theorem lspFge0_η_scan_D (z : Fin 1 → Bool) :
    lspFge0.η LState.scan (TapeSym.letter D) z
      = (if z ⟨0, Nat.one_pos⟩ then some (LState.pend, true, fun _ => CounterOp.keep, [])
         else some (LState.scan, true, fun _ => CounterOp.dec, [])) := rfl

@[simp] theorem lspFge0_η_scan_rmark (z : Fin 1 → Bool) :
    lspFge0.η LState.scan TapeSym.rmark z
      = some (LState.back, false, fun _ => CounterOp.keep, []) := rfl

@[simp] theorem lspFge0_η_pend_lmark (z : Fin 1 → Bool) :
    lspFge0.η LState.pend TapeSym.lmark z = none := rfl

@[simp] theorem lspFge0_η_pend_letter (a : Step) (z : Fin 1 → Bool) :
    lspFge0.η LState.pend (TapeSym.letter a) z
      = some (LState.sink, true, fun _ => CounterOp.keep, []) := rfl

@[simp] theorem lspFge0_η_pend_rmark (z : Fin 1 → Bool) :
    lspFge0.η LState.pend TapeSym.rmark z
      = some (LState.back, false, fun _ => CounterOp.keep, []) := rfl

@[simp] theorem lspFge0_η_back_lmark (z : Fin 1 → Bool) :
    lspFge0.η LState.back TapeSym.lmark z
      = some (LState.copy, true, fun _ => CounterOp.keep, []) := rfl

@[simp] theorem lspFge0_η_back_letter (a : Step) (z : Fin 1 → Bool) :
    lspFge0.η LState.back (TapeSym.letter a) z
      = some (LState.back, false, fun _ => CounterOp.keep, []) := rfl

@[simp] theorem lspFge0_η_back_rmark (z : Fin 1 → Bool) :
    lspFge0.η LState.back TapeSym.rmark z = none := rfl

@[simp] theorem lspFge0_η_copy_lmark (z : Fin 1 → Bool) :
    lspFge0.η LState.copy TapeSym.lmark z = none := rfl

@[simp] theorem lspFge0_η_copy_letter (x : Step) (z : Fin 1 → Bool) :
    lspFge0.η LState.copy (TapeSym.letter x) z
      = some (LState.copy, true, fun _ => CounterOp.keep, [WRPComp.relStep x]) := rfl

@[simp] theorem lspFge0_η_copy_rmark (z : Fin 1 → Bool) :
    lspFge0.η LState.copy TapeSym.rmark z = none := rfl

@[simp] theorem lspFge0_η_sink_lmark (z : Fin 1 → Bool) :
    lspFge0.η LState.sink TapeSym.lmark z = none := rfl

@[simp] theorem lspFge0_η_sink_letter (a : Step) (z : Fin 1 → Bool) :
    lspFge0.η LState.sink (TapeSym.letter a) z
      = some (LState.sink, true, fun _ => CounterOp.keep, []) := rfl

@[simp] theorem lspFge0_η_sink_rmark (z : Fin 1 → Bool) :
    lspFge0.η LState.sink TapeSym.rmark z = none := rfl

/-! ## The runs of `lspFge0` -/

/-- **The scan-pass invariant**: while every prefix height up to `i` is
nonnegative, after reading `⊢` and the first `i` letters the machine is in
`scan` at cell `i + 1` with the counter holding `(height w i).toNat`. -/
theorem lspFge0_scan_steps (w : List Step) :
    ∀ i, i ≤ w.length → (∀ k, k ≤ i → 0 ≤ height w k) →
      lspFge0.Steps w (LState.scan, 0, fun _ => 0) []
        (LState.scan, i + 1, fun _ => (height w i).toNat) := by
  intro i
  induction i with
  | zero =>
      intro _ _
      have hη : lspFge0.η LState.scan (tapeSym w 0)
          (fun j => (fun _ : Fin 1 => (0 : ℕ)) j == 0)
          = some (LState.scan, true, fun _ => CounterOp.keep, []) := by
        rw [tapeSym_zero]
        exact lspFge0_η_scan_lmark _
      have hrefl := CounterDFT.Steps.refl (M := lspFge0) (w := w)
        (LState.scan, 1, fun _ : Fin 1 => (height w 0).toNat)
      have h := CounterDFT.Steps.head hη hrefl
      simpa using h
  | succ i ih =>
      intro hle hpos
      have hi : i < w.length := by omega
      have ihs := ih (by omega) (fun k hk => hpos k (by omega))
      have hcell : tapeSym w (i + 1) = TapeSym.letter w[i] := tapeSym_succ w i hi
      have h0i : 0 ≤ height w i := hpos i (by omega)
      have h0si : 0 ≤ height w (i + 1) := hpos (i + 1) (by omega)
      have h1 := Int.toNat_of_nonneg h0i
      have h2 := Int.toNat_of_nonneg h0si
      cases hwi : w[i] with
      | U =>
          have h3 := height_succ_of_get_U w i hi hwi
          have hη : lspFge0.η LState.scan (tapeSym w (i + 1))
              (fun j => (fun _ : Fin 1 => (height w i).toNat) j == 0)
              = some (LState.scan, true, fun _ => CounterOp.inc, []) := by
            rw [hcell, hwi]
            exact lspFge0_η_scan_U _
          have hrefl := CounterDFT.Steps.refl (M := lspFge0) (w := w)
            (LState.scan, i + 1 + 1, fun _ : Fin 1 => (height w i).toNat + 1)
          have h := CounterDFT.Steps.head hη hrefl
          have htrans := ihs.trans h
          have hcnt : (fun _ : Fin 1 => (height w i).toNat + 1)
              = (fun _ : Fin 1 => (height w (i + 1)).toNat) := by
            funext j
            omega
          rw [hcnt] at htrans
          simpa using htrans
      | D =>
          have h3 := height_succ_of_get_D w i hi hwi
          have hne : (height w i).toNat ≠ 0 := by omega
          have hb : ((height w i).toNat == 0) = false := beq_eq_false_iff_ne.mpr hne
          have hη : lspFge0.η LState.scan (tapeSym w (i + 1))
              (fun j => (fun _ : Fin 1 => (height w i).toNat) j == 0)
              = some (LState.scan, true, fun _ => CounterOp.dec, []) := by
            rw [hcell, hwi]
            simp [hb]
            rfl
          have hrefl := CounterDFT.Steps.refl (M := lspFge0) (w := w)
            (LState.scan, i + 1 + 1, fun _ : Fin 1 => (height w i).toNat - 1)
          have h := CounterDFT.Steps.head hη hrefl
          have htrans := ihs.trans h
          have hcnt : (fun _ : Fin 1 => (height w i).toNat - 1)
              = (fun _ : Fin 1 => (height w (i + 1)).toNat) := by
            funext j
            omega
          rw [hcnt] at htrans
          simpa using htrans

/-- Singleton flat-maps are maps. -/
theorem flatMap_singleton_map (w : List Step) :
    (w.flatMap fun x => [WRPComp.relStep x]) = w.map WRPComp.relStep := by
  induction w with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, ih]

/-- The return-and-copy tail: from `back` at the right end of the word, the
machine returns to `⊢` and the copy pass emits the relabelled input. -/
theorem lspFge0_back_copy (w : List Step) (cnt : Fin 1 → ℕ) :
    lspFge0.Steps w (LState.back, w.length, cnt) (w.map WRPComp.relStep)
      (LState.copy, 1 + w.length, cnt) := by
  have s1 : lspFge0.Steps w (LState.back, w.length, cnt) [] (LState.back, 0, cnt) :=
    CounterDFT.steps_scan_left (fun a z => lspFge0_η_back_letter a z) w.length le_rfl
  have hη : lspFge0.η LState.back (tapeSym w 0) (fun j => cnt j == 0)
      = some (LState.copy, true, fun _ => CounterOp.keep, []) := by
    rw [tapeSym_zero]
    exact lspFge0_η_back_lmark _
  have s2 : lspFge0.Steps w (LState.back, 0, cnt) [] (LState.copy, 1, cnt) := by
    have hrefl := CounterDFT.Steps.refl (M := lspFge0) (w := w) (LState.copy, 1, cnt)
    simpa using CounterDFT.Steps.head hη hrefl
  have s3 : lspFge0.Steps w (LState.copy, 1, cnt)
      (w.flatMap fun x => [WRPComp.relStep x]) (LState.copy, 1 + w.length, cnt) := by
    refine CounterDFT.steps_scan_right w 1 (fun k hk => ?_)
      (fun a _ z => lspFge0_η_copy_letter a z)
    rw [show 1 + k = k + 1 by omega]
    exact tapeSym_succ w k hk
  have h := (s1.trans s2).trans s3
  rw [flatMap_singleton_map w] at h
  simpa using h

/-- The copy pass halts (accepting) at the right end marker. -/
theorem lspFge0_halted_copy (w : List Step) (cnt : Fin 1 → ℕ) :
    lspFge0.Halted w (LState.copy, 1 + w.length, cnt) := by
  show lspFge0.η LState.copy (tapeSym w (1 + w.length)) (fun j => cnt j == 0) = none
  rw [tapeSym_ge w _ (by omega)]
  exact lspFge0_η_copy_rmark _

/-- **Accepting copy run, no pending**: when every prefix height (the final
one included) is nonnegative, the scan pass never meets a `D` at counter `0`,
and the machine copies the input. -/
theorem lspFge0_computes_of_nonneg_all (w : List Step)
    (h : ∀ k, k ≤ w.length → 0 ≤ height w k) :
    lspFge0.Computes w (w.map WRPComp.relStep) := by
  have s0 := lspFge0_scan_steps w w.length le_rfl h
  have hη : lspFge0.η LState.scan (tapeSym w (w.length + 1))
      (fun j => (fun _ : Fin 1 => (height w w.length).toNat) j == 0)
      = some (LState.back, false, fun _ => CounterOp.keep, []) := by
    rw [tapeSym_ge w _ (by omega)]
    exact lspFge0_η_scan_rmark _
  have s1 : lspFge0.Steps w
      (LState.scan, w.length + 1, fun _ => (height w w.length).toNat) []
      (LState.back, w.length, fun _ => (height w w.length).toNat) := by
    have hrefl := CounterDFT.Steps.refl (M := lspFge0) (w := w)
      (LState.back, w.length, fun _ : Fin 1 => (height w w.length).toNat)
    simpa using CounterDFT.Steps.head hη hrefl
  have s2 := lspFge0_back_copy w (fun _ => (height w w.length).toNat)
  have hrun := (s0.trans s1).trans s2
  exact ⟨_, hrun, lspFge0_halted_copy w _, trivial⟩

/-- **Accepting copy run through `pend`**: when every *proper* prefix height
is nonnegative but the full-word height is negative, the last letter is a `D`
read at counter `0`; the pending state then meets `⊣`, so no violation is
recorded (`Lnn` constrains proper prefixes only) and the machine copies the
input. -/
theorem lspFge0_computes_of_lnn_neg_end (w : List Step)
    (hlnn : ∀ i, i < w.length → 0 ≤ height w i)
    (hneg : height w w.length < 0) :
    lspFge0.Computes w (w.map WRPComp.relStep) := by
  have hlen : 1 ≤ w.length := by
    rcases Nat.eq_zero_or_pos w.length with h0 | h
    · exfalso
      rw [h0, height_zero] at hneg
      omega
    · exact h
  have hi1 : w.length - 1 < w.length := by omega
  have hprev : 0 ≤ height w (w.length - 1) := hlnn _ hi1
  have hsucc1 : w.length - 1 + 1 = w.length := by omega
  -- the last letter is a `D` read at height 0
  have hD : w[w.length - 1] = D := by
    cases hwl : w[w.length - 1] with
    | U =>
        exfalso
        have h := height_succ_of_get_U w (w.length - 1) hi1 hwl
        rw [hsucc1] at h
        omega
    | D => rfl
  have hzero : height w (w.length - 1) = 0 := by
    have h := height_succ_of_get_D w (w.length - 1) hi1 hD
    rw [hsucc1] at h
    omega
  -- scan cleanly through the first `|w| - 1` letters
  have s0 := lspFge0_scan_steps w (w.length - 1) (by omega)
    (fun k hk => hlnn k (by omega))
  have hcnt0 : (fun _ : Fin 1 => (height w (w.length - 1)).toNat)
      = (fun _ : Fin 1 => (0 : ℕ)) := by
    funext j
    rw [hzero]
    rfl
  rw [hcnt0, hsucc1] at s0
  -- the final `D` at counter 0 enters `pend`
  have hcell : tapeSym w w.length = TapeSym.letter D := by
    have h := tapeSym_succ w (w.length - 1) hi1
    rw [hsucc1, hD] at h
    exact h
  have hη1 : lspFge0.η LState.scan (tapeSym w w.length)
      (fun j => (fun _ : Fin 1 => (0 : ℕ)) j == 0)
      = some (LState.pend, true, fun _ => CounterOp.keep, []) := by
    rw [hcell]
    simp
    rfl
  have s1 : lspFge0.Steps w (LState.scan, w.length, fun _ => (0 : ℕ)) []
      (LState.pend, w.length + 1, fun _ => (0 : ℕ)) := by
    have hrefl := CounterDFT.Steps.refl (M := lspFge0) (w := w)
      (LState.pend, w.length + 1, fun _ : Fin 1 => (0 : ℕ))
    simpa using CounterDFT.Steps.head hη1 hrefl
  -- `pend` meets `⊣`: no further letter, so no violation — return
  have hη2 : lspFge0.η LState.pend (tapeSym w (w.length + 1))
      (fun j => (fun _ : Fin 1 => (0 : ℕ)) j == 0)
      = some (LState.back, false, fun _ => CounterOp.keep, []) := by
    rw [tapeSym_ge w _ (by omega)]
    exact lspFge0_η_pend_rmark _
  have s2 : lspFge0.Steps w (LState.pend, w.length + 1, fun _ => (0 : ℕ)) []
      (LState.back, w.length, fun _ => (0 : ℕ)) := by
    have hrefl := CounterDFT.Steps.refl (M := lspFge0) (w := w)
      (LState.back, w.length, fun _ : Fin 1 => (0 : ℕ))
    simpa using CounterDFT.Steps.head hη2 hrefl
  have s3 := lspFge0_back_copy w (fun _ => (0 : ℕ))
  have hrun := ((s0.trans s1).trans s2).trans s3
  exact ⟨_, hrun, lspFge0_halted_copy w _, trivial⟩

/-- **Rejecting sink run**: when some *proper* prefix height is negative, the
least violation is a `D` read at counter `0` with a further letter after it;
`pend` sees that letter, sinks, and the machine outputs `ε`. -/
theorem lspFge0_computes_of_not_lnn (w : List Step)
    (hw : ¬ ∀ i, i < w.length → 0 ≤ height w i) :
    lspFge0.Computes w [] := by
  have hex : ∃ i, i < w.length ∧ height w i < 0 := by
    push Not at hw
    obtain ⟨i, hi, hneg⟩ := hw
    exact ⟨i, hi, hneg⟩
  -- the least violating prefix length
  obtain ⟨i0, ⟨hi0len, hi0neg⟩, hmin⟩ :
      ∃ i0, (i0 < w.length ∧ height w i0 < 0) ∧
        ∀ k, k < i0 → ¬ (k < w.length ∧ height w k < 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hpos : ∀ k, k < i0 → 0 ≤ height w k := by
    intro k hk
    by_contra hneg
    exact hmin k hk ⟨by omega, by omega⟩
  have h1 : 1 ≤ i0 := by
    rcases Nat.eq_zero_or_pos i0 with h0 | h
    · exfalso
      rw [h0, height_zero] at hi0neg
      omega
    · exact h
  have hi1 : i0 - 1 < w.length := by omega
  have hprev : 0 ≤ height w (i0 - 1) := hpos _ (by omega)
  have hsucc1 : i0 - 1 + 1 = i0 := by omega
  -- the violating letter is a `D` read at height 0
  have hD : w[i0 - 1] = D := by
    cases hwl : w[i0 - 1] with
    | U =>
        exfalso
        have h := height_succ_of_get_U w (i0 - 1) hi1 hwl
        rw [hsucc1] at h
        omega
    | D => rfl
  have hzero : height w (i0 - 1) = 0 := by
    have h := height_succ_of_get_D w (i0 - 1) hi1 hD
    rw [hsucc1] at h
    omega
  -- clean scan through the first `i0 - 1` letters
  have s0 := lspFge0_scan_steps w (i0 - 1) (by omega) (fun k hk => hpos k (by omega))
  have hcnt0 : (fun _ : Fin 1 => (height w (i0 - 1)).toNat)
      = (fun _ : Fin 1 => (0 : ℕ)) := by
    funext j
    rw [hzero]
    rfl
  rw [hcnt0, hsucc1] at s0
  -- the `D` at counter 0 enters `pend`
  have hcell : tapeSym w i0 = TapeSym.letter D := by
    have h := tapeSym_succ w (i0 - 1) hi1
    rw [hsucc1, hD] at h
    exact h
  have hη1 : lspFge0.η LState.scan (tapeSym w i0)
      (fun j => (fun _ : Fin 1 => (0 : ℕ)) j == 0)
      = some (LState.pend, true, fun _ => CounterOp.keep, []) := by
    rw [hcell]
    simp
    rfl
  have s1 : lspFge0.Steps w (LState.scan, i0, fun _ => (0 : ℕ)) []
      (LState.pend, i0 + 1, fun _ => (0 : ℕ)) := by
    have hrefl := CounterDFT.Steps.refl (M := lspFge0) (w := w)
      (LState.pend, i0 + 1, fun _ : Fin 1 => (0 : ℕ))
    simpa using CounterDFT.Steps.head hη1 hrefl
  -- `pend` sees a further letter (`i0` is a proper-prefix length): sink
  have hcell2 : tapeSym w (i0 + 1) = TapeSym.letter w[i0] := tapeSym_succ w i0 hi0len
  have hη2 : lspFge0.η LState.pend (tapeSym w (i0 + 1))
      (fun j => (fun _ : Fin 1 => (0 : ℕ)) j == 0)
      = some (LState.sink, true, fun _ => CounterOp.keep, []) := by
    rw [hcell2]
    exact lspFge0_η_pend_letter _ _
  have s2 : lspFge0.Steps w (LState.pend, i0 + 1, fun _ => (0 : ℕ)) []
      (LState.sink, i0 + 2, fun _ => (0 : ℕ)) := by
    have hrefl := CounterDFT.Steps.refl (M := lspFge0) (w := w)
      (LState.sink, i0 + 2, fun _ : Fin 1 => (0 : ℕ))
    simpa using CounterDFT.Steps.head hη2 hrefl
  -- sink sweep over the remaining letters
  have s3 : lspFge0.Steps w (LState.sink, i0 + 2, fun _ => (0 : ℕ))
      ((w.drop (i0 + 1)).flatMap fun _ => ([] : List WRPComp.GBD))
      (LState.sink, i0 + 2 + (w.drop (i0 + 1)).length, fun _ => (0 : ℕ)) := by
    refine CounterDFT.steps_scan_right (w.drop (i0 + 1)) (i0 + 2) (fun k hk => ?_)
      (fun a _ z => lspFge0_η_sink_letter a z)
    have hklen : i0 + 1 + k < w.length := by
      rw [List.length_drop] at hk
      omega
    rw [show i0 + 2 + k = (i0 + 1 + k) + 1 by omega, tapeSym_succ w (i0 + 1 + k) hklen]
    congr 1
    exact List.getElem_drop.symm
  have hlen3 : i0 + 2 + (w.drop (i0 + 1)).length = w.length + 1 := by
    rw [List.length_drop]
    omega
  have hnil : ((w.drop (i0 + 1)).flatMap fun _ => ([] : List WRPComp.GBD)) = [] := by
    simp
  rw [hlen3, hnil] at s3
  have hrun := ((s0.trans s1).trans s2).trans s3
  refine ⟨_, hrun, ?_, trivial⟩
  show lspFge0.η LState.sink (tapeSym w (w.length + 1))
      (fun j => (fun _ : Fin 1 => (0 : ℕ)) j == 0) = none
  rw [tapeSym_ge w _ (by omega)]
  exact lspFge0_η_sink_rmark _

/-- **The value computed by `lspFge0` is `F_{≥0}`'s payload** (Appendix A.3,
lines 4581–4587; cf. `compS_computes_compD`): the relabelled input when every
proper prefix height is nonnegative, `ε` otherwise. -/
theorem lspFge0_computes (w : List Step) :
    lspFge0.Computes w
      (if ∀ i, i < w.length → 0 ≤ height w i then w.map WRPComp.relStep else []) := by
  by_cases hw : ∀ i, i < w.length → 0 ≤ height w i
  · rw [if_pos hw]
    by_cases hend : height w w.length < 0
    · exact lspFge0_computes_of_lnn_neg_end w hw hend
    · push Not at hend
      refine lspFge0_computes_of_nonneg_all w (fun k hk => ?_)
      rcases Nat.lt_or_ge k w.length with h | h
      · exact hw k h
      · have hkl : k = w.length := by omega
        rw [hkl]
        exact hend
  · rw [if_neg hw]
    exact lspFge0_computes_of_not_lnn w hw

/-- `lspFge0` computes exactly the map `F_{≥0}`. -/
theorem lspFge0_computes_iff (w : List Step) (out : List WRPComp.GBD) :
    WRPComp.Fge0 w = some out ↔ lspFge0.Computes w out := by
  have hval := lspFge0_computes w
  constructor
  · intro h
    have heq : (if ∀ i, i < w.length → 0 ≤ height w i then w.map WRPComp.relStep else [])
        = out := Option.some.inj h
    rw [← heq]
    exact hval
  · intro h
    have heq := CounterDFT.computes_unique h hval
    show WRPComp.Fge0 w = some out
    rw [show WRPComp.Fge0 w = some (if ∀ i, i < w.length → 0 ≤ height w i
        then w.map WRPComp.relStep else []) from rfl, heq]

/-! ## The space bound -/

/-- A cell holding `⊢` is cell `0`. -/
theorem tapeSym_lmark_pos (w : List Alpha) (i : ℕ)
    (h : tapeSym w i = TapeSym.lmark) : i = 0 := by
  by_contra h0
  unfold tapeSym at h
  rw [if_neg h0] at h
  by_cases h1 : i - 1 < w.length
  · rw [dif_pos h1] at h
    simp at h
  · rw [dif_neg h1] at h
    simp at h

/-- A cell holding a letter lies in `[1, |w|]`. -/
theorem tapeSym_letter_le (w : List Alpha) (i : ℕ) (a : Alpha)
    (h : tapeSym w i = TapeSym.letter a) : i ≠ 0 ∧ i ≤ w.length := by
  constructor
  · intro h0
    rw [h0, tapeSym_zero] at h
    simp at h
  · by_contra hlen
    push Not at hlen
    rw [tapeSym_ge w i hlen] at h
    simp at h

/-- **The space bound for `lspFge0`** (`C = 1`): the counter never exceeds
`|w| + 1`.  Proved by the reachability invariant "the counter is at most
`|w| + 1`, and during the scan phase at most the head position": the only
increment is at a `U`-cell, whose position is at most `|w|`. -/
theorem lspFge0_spaceBound : SpaceBound lspFge0 1 := by
  intro w out e hsteps j
  have hstep : ∀ (q : LState) (i : ℕ) (cnt : Fin 1 → ℕ) (q' : LState) (d : Bool)
      (ops : Fin 1 → CounterOp) (u : List WRPComp.GBD),
      ((∀ j, cnt j ≤ w.length + 1) ∧ (q = LState.scan → ∀ j, cnt j ≤ i)) →
      lspFge0.η q (tapeSym w i) (fun j => cnt j == 0) = some (q', d, ops, u) →
      ((∀ j, (ops j).apply (cnt j) ≤ w.length + 1)
        ∧ (q' = LState.scan → ∀ j, (ops j).apply (cnt j) ≤ moveDir i d)) := by
    intro q i cnt q' d ops u hP hη
    obtain ⟨hbound, hscan⟩ := hP
    cases hs : tapeSym w i with
    | lmark =>
        have hi0 : i = 0 := tapeSym_lmark_pos w i hs
        subst hi0
        rw [hs] at hη
        cases q with
        | scan =>
            simp only [lspFge0_η_scan_lmark] at hη
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hη
            refine ⟨fun j => ?_, fun _ j => ?_⟩
            · simpa using hbound j
            · have h := hscan rfl j
              simp only [CounterOp.apply_keep, moveDir_true]
              omega
        | back =>
            simp only [lspFge0_η_back_lmark] at hη
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hη
            exact ⟨fun j => by simpa using hbound j, fun h => nomatch h⟩
        | pend => simp at hη
        | copy => simp at hη
        | sink => simp at hη
    | letter a =>
        obtain ⟨hi0, hilen⟩ := tapeSym_letter_le w i a hs
        rw [hs] at hη
        cases q with
        | scan =>
            cases a with
            | U =>
                simp only [lspFge0_η_scan_U] at hη
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hη
                refine ⟨fun j => ?_, fun _ j => ?_⟩
                · have h := hscan rfl j
                  simp only [CounterOp.apply_inc]
                  omega
                · have h := hscan rfl j
                  simp only [CounterOp.apply_inc, moveDir_true]
                  omega
            | D =>
                rw [lspFge0_η_scan_D] at hη
                split at hη
                · obtain ⟨rfl, rfl, rfl, rfl⟩ := hη
                  exact ⟨fun j => by simpa using hbound j, fun h => nomatch h⟩
                · obtain ⟨rfl, rfl, rfl, rfl⟩ := hη
                  refine ⟨fun j => ?_, fun _ j => ?_⟩
                  · have h := hbound j
                    simp only [CounterOp.apply_dec]
                    omega
                  · have h := hscan rfl j
                    simp only [CounterOp.apply_dec, moveDir_true]
                    omega
        | pend =>
            simp only [lspFge0_η_pend_letter] at hη
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hη
            exact ⟨fun j => by simpa using hbound j, fun h => nomatch h⟩
        | back =>
            simp only [lspFge0_η_back_letter] at hη
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hη
            exact ⟨fun j => by simpa using hbound j, fun h => nomatch h⟩
        | copy =>
            simp only [lspFge0_η_copy_letter] at hη
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hη
            exact ⟨fun j => by simpa using hbound j, fun h => nomatch h⟩
        | sink =>
            simp only [lspFge0_η_sink_letter] at hη
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hη
            exact ⟨fun j => by simpa using hbound j, fun h => nomatch h⟩
    | rmark =>
        rw [hs] at hη
        cases q with
        | scan =>
            simp only [lspFge0_η_scan_rmark] at hη
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hη
            exact ⟨fun j => by simpa using hbound j, fun h => nomatch h⟩
        | pend =>
            simp only [lspFge0_η_pend_rmark] at hη
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hη
            exact ⟨fun j => by simpa using hbound j, fun h => nomatch h⟩
        | back => simp at hη
        | copy => simp at hη
        | sink => simp at hη
  have hinv := CounterDFT.steps_invariant (M := lspFge0) (w := w)
    (P := fun cfg => (∀ j, cfg.2.2 j ≤ w.length + 1)
      ∧ (cfg.1 = LState.scan → ∀ j, cfg.2.2 j ≤ cfg.2.1))
    hstep hsteps ⟨fun _ => Nat.zero_le _, fun _ _ => Nat.le_refl 0⟩
  have h := hinv.1 j
  omega

/-! ## The separation (`thm:wrp-strict-below-logspace`) -/

/-- **`F_{≥0}` is a deterministic-logspace map** — the "in logspace" half of
the proof of `thm:wrp-strict-below-logspace` (paper.tex, Appendix
A.3 lines 4581–4587: one scan with a height counter and a flag, then a copy
pass): the machine `lspFge0`, with `c = 1` counter and space bound `C = 1`. -/
theorem Fge0_isLogspace : IsLogspaceMap WRPComp.Fge0 :=
  ⟨1, 1, lspFge0, lspFge0_spaceBound, lspFge0_computes_iff⟩

/-- **The separation half of `thm:wrp-strict-below-logspace`**
(paper.tex; proof Appendix A.3 lines 4538–4601): there is
a deterministic-logspace word-to-word map that is not a WRP map — namely
`F_{≥0}`, whose nonempty-output preimage `Lnn \ {ε}` is not regular while
every WRP map has a regular one (`lem:wrp-nonempty-regular`).  Trust: admits
`SliceMSO.buchi` through `Fge0_not_isWRP`. -/
theorem exists_logspace_not_wrp :
    ∃ f : List Step → Option (List WRPComp.GBD), IsLogspaceMap f ∧ ¬ WRP.IsWRP f :=
  ⟨WRPComp.Fge0, Fge0_isLogspace, WRPComp.Fge0_not_isWRP⟩

/-- **Theorem `thm:wrp-strict-below-logspace` (paper.tex),
staged**: `WRP` is a *proper* subclass of the deterministic-logspace
word-to-word maps, formalised relative to the containment hypothesis `hinc`
(mirroring how `thm:two-parameter-semilinearity` is staged over its counting
principle).

`hinc` is exactly Theorem `thm:wrp-logspace` (Logspace evaluation,
paper.tex) specialised to this input/output alphabet pair:
every WRP map is computable in deterministic logspace, i.e. by a
bounded-counter machine of this file.  It remains open in this repository:
a verified evaluator needs DFA-based evaluation of the presentation's MSO
selection/label/order data and a verified selection sort of the atoms by
rank — a major verified-algorithms project.  Its refinement
`cor:srr-quadratic` (line 1587) additionally needs a time-cost model, which
this space-only machine model does not carry.

The strictness half (`exists_logspace_not_wrp`) is proved outright.  Trust:
admits `SliceMSO.buchi` through `Fge0_not_isWRP`. -/
theorem wrp_strict_below_logspace_of_evaluator
    (hinc : ∀ T : List Step → Option (List WRPComp.GBD),
      WRP.IsWRP T → IsLogspaceMap T) :
    (∀ T : List Step → Option (List WRPComp.GBD), WRP.IsWRP T → IsLogspaceMap T) ∧
      ∃ f : List Step → Option (List WRPComp.GBD), IsLogspaceMap f ∧ ¬ WRP.IsWRP f :=
  ⟨hinc, exists_logspace_not_wrp⟩

end Logspace
