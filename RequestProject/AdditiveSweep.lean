/-
# Additive Sweep Transductions

Formalization of Definition 4.2 and Proposition 4.3 of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.
-/
import RequestProject.DyckPath

open Step

/-! ## Definition 4.2: Additive sweep transduction
(`def:additive-sweep`, paper.tex) -/

/-- **`def:additive-sweep` (paper.tex).**
Fix integer step weights `ν : {U, D} → ℤ` and a scan direction. The
*additive sweep transduction* `Φ_ν` assigns to each step of the input
word `w = w_1 ⋯ w_{2n}` the integer *level* `ℓ(i) = Σ_{j<i} ν(w_j)`,
and outputs the step labels listed by increasing level, ties broken
by the scan direction. -/
def additiveSweep (nu : Step → ℤ) (rightToLeft : Bool) (w : List Step) : List Step :=
  let indexed := w.zipIdx |>.map fun (s, i) =>
    let level := (w.take i).foldl (fun acc t => acc + nu t) 0
    (level, i, s)
  let sorted := indexed.mergeSort (fun a b =>
    if a.1 < b.1 then true
    else if a.1 > b.1 then false
    else if rightToLeft then a.2.1 > b.2.1 else a.2.1 < b.2.1)
  sorted.map fun (_, _, s) => s

/-- The height-level sweep with left-to-right ties. -/
def heightSweepLR (w : List Step) : List Step :=
  additiveSweep (fun | U => 1 | D => -1) false w

/-- The height-level sweep with right-to-left ties (= Narayana sweep). -/
def heightSweepRL (w : List Step) : List Step :=
  additiveSweep (fun | U => 1 | D => -1) true w
/-! ## Example 4.3 (`ex:height-sweep`, paper.tex): Height sweep on UUDUDD -/

/-- **`ex:height-sweep` (paper.tex).**
The height sweep with left-to-right ties on `UUDUDD` gives `UUUDDD`. -/
theorem heightSweepLR_UUDUDD :
    heightSweepLR [U, U, D, U, D, D] = [U, U, U, D, D, D] := by native_decide

/-
The right-to-left height sweep is the same as our `heightSweep`.
-/
theorem heightSweepRL_eq_heightSweep (w : List Step) :
    heightSweepRL w = heightSweep w := by
  rfl
