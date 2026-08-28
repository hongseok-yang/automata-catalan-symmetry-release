/-
# The §7 `fas` TIE-count assembly (arity-1): the equal-rank semantic reformulation

The corrected TIE route (route steps L4–L7) counts the selected `U`-atoms `a` with
`rank a = dstarRank n` that `atomOrd`-precede the `≺`-minimal selected `D`-atom `d*`.

This file begins that assembly with the **keystone semantic reformulation** `fas_member_eqRank`:
for a selected atom `a` of rank equal to `d*`'s rank, the `fas`-membership clause
"`∀ selected b, label b = U ∨ a ≺ b`" is equivalent to the **equal-rank**-restricted atomOrd
condition "`∀ selected `D`-atom `b` with `rank b = rank d*`, atomOrd a b`".  This is the precise
fact (provable from `P.Valid` alone — no separate `χ` axiom) that makes the TIE gate expressible
in MSO: on the `rank = dstarRank` cell, the equal-rank `D`-atoms are exactly the collinear-cell
members (MSO via residue) plus the finitely-many Case-A boundary atoms (fixed offsets), with no
appeal to `d*`'s identity.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`): pure order theory on `Valid`.
-/
import RequestProject.SliceOutput
import RequestProject.SliceLexOrder

namespace SliceFasTie

open Step

/-- **The equal-rank reformulation** (route step L4/L7 keystone; `Valid`-only).  When `dstar` is the
`≺`-minimal selected `D`-atom and `a` is a selected atom with `rank a = rank dstar`, the `fas`
membership clause collapses to "`a` atomOrd-precedes every selected `D`-atom of rank `= rank dstar`".

Forward: `fas_inner_collapse` gives `a ≺ dstar`, and at equal rank `≺ = atomOrd` (the `lexLt` branch
is killed by `lexLt_irrefl`); for any equal-rank selected `D`-atom `b`, `dstar ≼ b` (min) is `atomOrd`
at equal rank, and `Valid.trans` on the equal-rank stratum gives `atomOrd a b`.  Backward: instantiate
at `b := dstar`. -/
theorem fas_member_eqRank {Alpha : Type*} (P : WRP.Presentation Alpha Step) (hV : P.Valid)
    (w : List Alpha) (dstar : P.toPoly.Atom) (hdsel : P.toPoly.selectedAtom w dstar)
    (hdD : P.toPoly.labelOf w dstar = D)
    (hdmin : ∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = D →
      dstar = b ∨ P.wrpOrd w dstar b)
    (a : P.toPoly.Atom) (hasel : P.toPoly.selectedAtom w a)
    (hrankeq : P.rankOf w a = P.rankOf w dstar) :
    (∀ b, P.toPoly.selectedAtom w b → (P.toPoly.labelOf w b = U ∨ P.wrpOrd w a b)) ↔
      (∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = D →
        P.rankOf w b = P.rankOf w dstar → P.toPoly.atomOrd w a b) := by
  rw [SliceOutput.fas_inner_collapse P hV w dstar hdsel hdD hdmin a hasel]
  -- LHS is now `P.wrpOrd w a dstar`; at equal rank it collapses to `atomOrd a dstar`.
  have hcollapse : P.wrpOrd w a dstar ↔ P.toPoly.atomOrd w a dstar := by
    unfold WRP.Presentation.wrpOrd
    constructor
    · rintro (hlt | ⟨_, h⟩)
      · exact absurd (hrankeq ▸ hlt) (SliceLexOrder.lexLt_irrefl _)
      · exact h
    · intro h; exact Or.inr ⟨hrankeq, h⟩
  rw [hcollapse]
  constructor
  · -- (→) atomOrd a dstar ⇒ ∀ equal-rank selected D-atom b, atomOrd a b
    intro hadstar b hbsel hbD hbrank
    rcases hdmin b hbsel hbD with rfl | hdb
    · exact hadstar
    · have hdb_ord : P.toPoly.atomOrd w dstar b := by
        rcases hdb with hlt | ⟨_, h⟩
        · exact absurd (hbrank ▸ hlt) (SliceLexOrder.lexLt_irrefl _)
        · exact h
      have hwab : P.wrpOrd w a b :=
        hV.trans w a dstar b hasel hdsel hbsel
          (Or.inr ⟨hrankeq, hadstar⟩) (Or.inr ⟨hrankeq.symm ▸ hbrank.symm, hdb_ord⟩)
      rcases hwab with hlt | ⟨_, h⟩
      · exact absurd ((hrankeq.trans hbrank.symm) ▸ hlt) (SliceLexOrder.lexLt_irrefl _)
      · exact h
  · -- (←) instantiate at b := dstar
    intro hall
    exact hall dstar hdsel hdD rfl

end SliceFasTie
