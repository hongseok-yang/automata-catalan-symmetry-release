/-
# Route-B tie counting (§9 tower, F3.9 — the pin-free first-descent count)

The target is `CopiedD4.TieCountAffineBudgeted`: the number
of selected-`U` atoms that precede the first selected-`D` atom in the output order
`≺` is affine-on-residues in `n`, with a period uniform across rows `mS`.

**Why this file (route B).**  A route that *pins* the first-`D`
atom `d*` as a residue-determined descriptor (`BoundaryAnchoredDstar`,
`WholeTupleDstarAtomOrdGate`) forces coverage of `d*` by a finite candidate
list and runs into the boundary-anchoring obstructions.  The paper's Section 9
argument never pins `d*`: it counts "`u ≺` (first `D`)" with the first-`D` atom
left as a *free* Presburger parameter and applies the bounded Presburger counting
principle (Lemma `lem:presburger-counting`) plus the slice arithmetic of
`lem:one-loop-presburger`.  This file develops that pin-free route.

`tie_pred_iff_below_dstar` is the structural bridge: "`u` precedes every selected
`D`" is the same as "`u ≺ d*`", so the `∀ b` quantifier in `TieCountAffineBudgeted`
is genuinely a single first-descent comparison — but it does **not** have to be
discharged by pinning a descriptor; in the pin-free route the comparison stays a
Presburger predicate to be counted.
-/
import RequestProject.CopiedD4

namespace CopiedTieCounting

open WRP Step

/-- **The first-descent bridge.**  For a selected atom `u` and a `wrpOrd`-minimal
selected-`D` atom `dstar`, "`u` precedes every selected-`D` atom" is equivalent to
the single comparison "`u ≺ dstar`".  Pure `P.Valid` (the strict-weak-order laws);
no Büchi, no rank arithmetic.  This is the structural reason the `∀ b` quantifier in
`CopiedD4.TieCountAffineBudgeted` reduces to one first-descent comparison. -/
theorem tie_pred_iff_below_dstar
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (w : List Step) (u dstar : P.toPoly.Atom)
    (husel : P.toPoly.selectedAtom w u)
    (hdsel : P.toPoly.selectedAtom w dstar)
    (hdlabel : P.toPoly.labelOf w dstar = Step.D)
    (hdmin : ∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = Step.D →
      dstar = b ∨ P.wrpOrd w dstar b) :
    P.wrpOrd w u dstar ↔
      (∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = Step.D →
        P.wrpOrd w u b) := by
  constructor
  · intro hud b hbsel hblabel
    rcases hdmin b hbsel hblabel with heq | hdb
    · rwa [heq] at hud
    · exact hV.trans w u dstar b husel hdsel hbsel hud hdb
  · intro hall
    exact hall dstar hdsel hdlabel

end CopiedTieCounting
