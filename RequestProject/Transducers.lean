/-
# Basic language-theoretic notions (§3 of `paper.tex`)

The shared elementary vocabulary of the transducer sections: realisation of a
function by a partial transduction (`Realises`, `def:relative`), deterministic
finite automata (`DFA'`, `def:dfa`) with their languages, and regularity of a
language (`IsRegularLang`, `def:regular-language`).

The transducer *models* themselves live in their own files: `Polygular.lean`
has the polyregular presentations (`Polyreg.IsPolyregular`, `def:polyregular`)
and their arity-1 MSO fragment (`Polyreg.IsRegular`), `WRP.lean` has the
weighted-rank polyregular class (`WRP.IsWRP`, `def:wrp`), `SRR1.lean` the
scan-order fragment (`WRP.IsSRR1`), `TwoDFT.lean` the two-way transducers,
and `Multihead.lean`/`LogspaceTM.lean` the logspace machine models.
-/
import Mathlib
import RequestProject.DyckPath

open Step

/-! ## Realisation -/

/-- **`def:relative` (paper.tex).**
A transduction `T : Alpha* ⇀ Beta*` (a partial map from words to words)
*realises* a function `f : X → Beta*` (where `X ⊆ Alpha*`) if `X ⊆ dom(T)`
and `T(x) = f(x)` for every `x ∈ X`. Its behaviour on inputs outside `X`
is unconstrained. -/
def Realises {Alpha Beta : Type} (T : List Alpha → Option (List Beta))
    (X : Set (List Alpha)) (f : List Alpha → List Beta) : Prop :=
  ∀ x ∈ X, T x = some (f x)

/-! ## Deterministic finite automata -/

/-- **`def:dfa` (paper.tex).**
A deterministic finite automaton (DFA) over alphabet `Alpha`.
A finite set of states, a transition function, an initial state, and
a set of accepting states. -/
structure DFA' (Alpha : Type) where
  Q : Type
  [finQ : Fintype Q]
  [decEqQ : DecidableEq Q]
  delta : Q → Alpha → Q
  q0 : Q
  F : Set Q
  [decF : DecidablePred (· ∈ F)]

/-- A DFA accepts a word if the run from q₀ ends in an accepting state. -/
def DFA'.accepts (A : DFA' Alpha) (w : List Alpha) : Prop :=
  w.foldl A.delta A.q0 ∈ A.F

/-- The language accepted by a DFA. -/
def DFA'.language (A : DFA' Alpha) : Set (List Alpha) :=
  {w | A.accepts w}

/-- **`def:regular-language` (paper.tex).**
A language is *regular* if it is accepted by some DFA. -/
def IsRegularLang {Alpha : Type} (L : Set (List Alpha)) : Prop :=
  ∃ A : DFA' Alpha, A.language = L


