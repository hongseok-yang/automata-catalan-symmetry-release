/-
# `thm:wrp-logspace` and `thm:wrp-strict-below-logspace` in the worktape model

`WRPLogspace.lean` proves the logspace theorems of §4 over the multihead
bounded-counter model (`Multihead.IsLogspaceMH`) — the machine model the
paper's proof actually manipulates (two-way heads and linearly bounded
counters, i.e. `O(log n)`-bit registers).  This file restates them over the
**worktape transducer model** (`LogspaceTM.IsLogspaceTM`): a read-only input
tape, one two-way read-write worktape confined to `C·(⌊log₂(n+2)⌋+1)` cells,
and a write-only output tape — the paper's literal "`O(log n)` bits of
working memory beyond a read-only input and a write-only output".

The bridge is the fully proved two-stage simulation
`LogspaceTM.isLogspaceTM_of_isLogspaceMH` (`MHCOneHead.lean` eliminates the
extra heads into distance counters; `MHCToTM.lean` holds the counters in
binary on worktape tracks), so every statement here is a corollary of its
multihead original.  The polynomial-time clause comes generically from the
pigeonhole bound `LogspaceTM.LogTM.halting_length_poly` applied to the
worktape witness.

* `wrp_isLogspaceTM` / `wrp_paper_isLogspaceTM` — the `thm:wrp-logspace`
  containment over `WRP.IsWRP` and over the revision's verbatim `def:wrp`
  class `WRP.IsWRPPaper`.
* `wrp_logspaceTM_polytime` / `wrp_paper_logspaceTM_polytime` — the
  polynomial-time clause: the worktape witness halts within `D·(n+2)^k`
  steps.
* `wrp_strict_below_logspaceTM` / `wrp_strict_below_logspaceTM_paper` —
  `thm:wrp-strict-below-logspace`: WRP is contained in worktape logspace,
  and the worktape-logspace map `F_{≥0}` is not WRP.

Trust base: the containments and polytime clauses are axiom-clean; the
separations admit only `SliceMSO.buchi` (inherited from the multihead
separation witness), exactly as their multihead originals.
-/
import RequestProject.WRPPaperTheorems
import RequestProject.MHCToTM

/-- **`thm:wrp-logspace`, worktape model**: every WRP transduction is
computable by a deterministic worktape transducer whose work head stays
within `C·(⌊log₂(n+2)⌋+1)` cells. -/
theorem wrp_isLogspaceTM {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma]
    (T : List Step → Option (List Gamma)) (hT : WRP.IsWRP T) :
    LogspaceTM.IsLogspaceTM T :=
  LogspaceTM.isLogspaceTM_of_isLogspaceMH (wrp_isLogspaceMH T hT)

/-- `thm:wrp-logspace` over the revision's `def:wrp` class, worktape model. -/
theorem wrp_paper_isLogspaceTM {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma]
    (T : List Step → Option (List Gamma)) (hT : WRP.IsWRPPaper T) :
    LogspaceTM.IsLogspaceTM T :=
  wrp_isLogspaceTM T hT.isWRP

/-- **The polynomial-time clause of `thm:wrp-logspace`, worktape model**: a
worktape witness within the canonical space bound that, whenever it halts,
has run for at most `D·(n+2)^k` steps (`LogspaceTM.LogTM.halting_length_poly`,
the pigeonhole on non-repeating configurations). -/
theorem wrp_logspaceTM_polytime {Gamma : Type} [Fintype Gamma] [DecidableEq Gamma]
    (T : List Step → Option (List Gamma)) (hT : WRP.IsWRP T) :
    ∃ (M : LogspaceTM.LogTM Step Gamma) (C : ℕ),
      LogspaceTM.SpaceBound M (fun n => C * (Nat.log 2 (n + 2) + 1)) ∧
      (∀ w out, T w = some out ↔ M.Computes w out) ∧
      ∃ D k : ℕ, ∀ w out e N, M.StepsN w M.initConfig out e N → M.Halted w e →
        N < D * (w.length + 2) ^ k := by
  obtain ⟨M, C, hSB, hcomp⟩ := wrp_isLogspaceTM T hT
  obtain ⟨D, k, hpoly⟩ := LogspaceTM.LogTM.halting_length_poly hSB
  exact ⟨M, C, hSB, hcomp, D, k, fun w out e N hrun hhalt => hpoly hrun hhalt⟩

/-- The polynomial-time clause over the revision's `def:wrp` class. -/
theorem wrp_paper_logspaceTM_polytime {Gamma : Type} [Fintype Gamma]
    [DecidableEq Gamma] (T : List Step → Option (List Gamma))
    (hT : WRP.IsWRPPaper T) :
    ∃ (M : LogspaceTM.LogTM Step Gamma) (C : ℕ),
      LogspaceTM.SpaceBound M (fun n => C * (Nat.log 2 (n + 2) + 1)) ∧
      (∀ w out, T w = some out ↔ M.Computes w out) ∧
      ∃ D k : ℕ, ∀ w out e N, M.StepsN w M.initConfig out e N → M.Halted w e →
        N < D * (w.length + 2) ^ k :=
  wrp_logspaceTM_polytime T hT.isWRP

/-- **`thm:wrp-strict-below-logspace`, worktape model, UNCONDITIONAL**: every
WRP map is computable in worktape logspace, and the worktape-logspace map
`F_{≥0}` is not WRP. -/
theorem wrp_strict_below_logspaceTM :
    (∀ T : List Step → Option (List WRPComp.GBD), WRP.IsWRP T →
      LogspaceTM.IsLogspaceTM T) ∧
    ∃ f : List Step → Option (List WRPComp.GBD),
      LogspaceTM.IsLogspaceTM f ∧ ¬ WRP.IsWRP f :=
  ⟨fun T hT => wrp_isLogspaceTM T hT,
   ⟨WRPComp.Fge0,
    LogspaceTM.isLogspaceTM_of_isLogspaceMH Multihead.Fge0_isLogspaceMH,
    WRPComp.Fge0_not_isWRP⟩⟩

/-- `thm:wrp-strict-below-logspace` over the revision's `def:wrp` class,
worktape model.  Both halves a fortiori: containment through
`IsWRPPaper ⊆ IsWRP`, separation because `F_{≥0}` is not even in the larger
class. -/
theorem wrp_strict_below_logspaceTM_paper :
    (∀ T : List Step → Option (List WRPComp.GBD), WRP.IsWRPPaper T →
      LogspaceTM.IsLogspaceTM T) ∧
    ∃ f : List Step → Option (List WRPComp.GBD),
      LogspaceTM.IsLogspaceTM f ∧ ¬ WRP.IsWRPPaper f :=
  ⟨fun T hT => wrp_isLogspaceTM T hT.isWRP,
   ⟨WRPComp.Fge0,
    LogspaceTM.isLogspaceTM_of_isLogspaceMH Multihead.Fge0_isLogspaceMH,
    fun h => WRPComp.Fge0_not_isWRP h.isWRP⟩⟩
