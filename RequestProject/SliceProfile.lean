/-
# The slice profile set (leaf definition)

`sliceProfile` was born in `NoSwapWRP.lean`; it lives here as a LEAF (importing only
the core path definitions) so that the GA capstone tower can state its discharge
against it without importing `NoSwapWRP` — the adjudicated stage-0.1 import surgery
that prevents the cycle `NoSwapWRP → GA capstone → GA-7 tower → SliceFasAssembly →
NoSwapWRP` when the §7 slice theorem is imported (route GA-8).
-/
import RequestProject.DyckPath

/-- The first-ascent profile set of a transduction `T` on the wrapped-flat slice
`W_n = U(UD)^n D`, `n ≥ 1`. -/
def sliceProfile (T : List Step → Option (List Step)) : Set (ℕ × ℕ) :=
  { p | ∃ n : ℕ, n ≥ 1 ∧ ∃ out, T (wrappedFlat n) = some out ∧
        p = (firstAscent out, tailU out) }
