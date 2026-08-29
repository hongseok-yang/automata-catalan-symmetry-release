/-
# Re-rooted acceptors (§9 tower, Stage C core)

The mechanism of the fibred route: analysing a
word `u ++ w ++ v` with a machine `M` is the same as analysing `w` with `M`
re-rooted through `u` (new start state) and `v` (acceptance read through the
suffix run).  Crucially `reRoot` KEEPS the transition function, so every
δ-derived quantity — the unmarked block maps `bFN`, their iterate periods, the
transition monoid — is literally unchanged: the periods of the copied-slice
analysis are those of the wrapped-flat analysis, independent of the boundary
stretch lengths.  This file is the load-bearing two lemmas; the marked
copied-slice decomposition lives in `CopiedMark.lean`.
-/
import RequestProject.SliceMarkN

open SliceMSO MSOMarkN

namespace SliceReRoot

/-- `M`, re-rooted through a prefix `u` and read out through a suffix `v`:
same states, SAME transition function, shifted start, pulled-back acceptance. -/
def reRoot {Alpha : Type*} (M : DetAuto Alpha) (u v : List Alpha) :
    DetAuto Alpha where
  Q := M.Q
  fintypeQ := M.fintypeQ
  q0 := u.foldl M.δ M.q0
  δ := M.δ
  accept := fun q => M.accept (v.foldl M.δ q)

/-- **The re-rooting identity**: acceptance of the middle word by the
re-rooted machine is acceptance of the full word by the original. -/
theorem accepts_reRoot {Alpha : Type*} (M : DetAuto Alpha) (u v w : List Alpha) :
    (reRoot M u v).accepts w ↔ M.accepts (u ++ w ++ v) := by
  unfold DetAuto.accepts reRoot
  rw [List.foldl_append, List.foldl_append]

/-- **The period-transfer fact** (the heart of `m`-uniformity): the unmarked
block map of a re-rooted marked machine is LITERALLY that of the original —
`bFN` reads only `δ`, which `reRoot` preserves.  Hence the iterate periods of
the copied-slice analysis are those of the wrapped-flat analysis, independent
of the boundary stretches. -/
theorem bFN_reRoot {k : ℕ} (M : DetAuto (MarkedN k))
    (u v : List (MarkedN k)) :
    SliceMarkN.bFN (reRoot M u v) = SliceMarkN.bFN M := rfl

end SliceReRoot
