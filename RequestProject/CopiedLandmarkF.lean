/-
# The FULL-cell landmark decoder (§9 tower, F3.9 — the FG4 fix foundation)

`CopiedLandmark.regionDecodeL` decodes a CORE `RegionSpec` position (the D-atom lands in
the MIDDLE region `mS-1 + r.posAt t n`).  The tie gate
must enumerate the FULL `RegionSpecF` cells — including the SUFFIX `D^{mS-1}` (sufIdx) cells
the core decoder misses (the FG4 undercount).  `regionDecodeLF` covers all three
`RegionSpecF` constructors:
- `core r`  → `regionDecodeL r`         (`x = mS-1 + r.posAt t n`),
- `sufIdx l` → `offsetForm 3 1 (3 + l)` (`x = lastU + 3 + l = mS+2n+1+l` — the key new case),
- `prefIdx q` → `mso_position_eq q` embedded (`x = q`; VACUOUS for D-atoms, prefix is all-`U`,
  but needed so the `_sat` iff holds for every descriptor).
-/
import RequestProject.CopiedLandmark
import RequestProject.CopiedCells

namespace CopiedLandmark

open MSO SliceFasGates SliceFamilyCell CopiedCells

/-- **The full-cell landmark decoder**: every `RegionSpecF` descriptor's copied-slice
position as a landmark-relative MSO formula (`mS`-free syntax; the shift is in the
landmark valuations). -/
noncomputable def regionDecodeLF {B : ℕ} : RegionSpecF B → MSO.Formula Step 4 0
  | .core r => regionDecodeL r
  | .prefIdx q => SliceFasGates.relabelFO (fun _ : Fin 1 => (1 : Fin 4))
      (SliceFasGates.mso_position_eq (Alpha := Step) q).choose
  | .sufIdx l => offsetForm 3 1 (3 + l)

/-- **The full-cell decode pins the coordinate**: at the landmark valuation
`(z, x, firstD, lastU) = (mS+2t, x, mS+1, mS+2(n-1))`, `regionDecodeLF r` holds of `x`
exactly when `x` is the copied-slice position `r` describes at base `t`. -/
theorem regionDecodeLF_sat {B : ℕ} (r : RegionSpecF B) (mS t n x : ℕ)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hBn : B ≤ n) (hz : t < n)
    (hx : x < 2 * (mS + n)) (hv : r.valid mS) :
    ((regionDecodeLF r).Sat (copiedSlice mS n)
        (Fin.cons (mS + 2 * t) (Fin.cons x (Fin.cons (mS + 1)
          (Fin.cons (mS + 2 * (n - 1)) Fin.elim0)))) Fin.elim0
      ↔ x = r.posAt mS t n) := by
  have hlen : (copiedSlice mS n).length = 2 * (mS + n) := length_copiedSlice mS n
  rcases r with r | q | l
  · -- core: delegate to the core decoder
    exact regionDecodeL_sat r mS t n x hm hn hBn hz hx
  · -- prefIdx q (x = q): the absolute-position primitive, embedded into slot 1
    have hq : q < mS - 1 := hv
    show (SliceFasGates.relabelFO (fun _ : Fin 1 => (1 : Fin 4))
        (SliceFasGates.mso_position_eq (Alpha := Step) q).choose).Sat (copiedSlice mS n)
        (Fin.cons (mS + 2 * t) (Fin.cons x (Fin.cons (mS + 1)
          (Fin.cons (mS + 2 * (n - 1)) Fin.elim0)))) Fin.elim0 ↔ x = q
    rw [SliceFasGates.sat_relabelFO]
    have hcomp : ((Fin.cons (mS + 2 * t) (Fin.cons x (Fin.cons (mS + 1)
          (Fin.cons (mS + 2 * (n - 1)) Fin.elim0)))) ∘ (fun _ : Fin 1 => (1 : Fin 4)))
        = (fun _ => x) := by
      funext i; rfl
    rw [hcomp]
    exact (SliceFasGates.mso_position_eq (Alpha := Step) q).choose_spec
      (copiedSlice mS n) x (by rw [hlen]; exact hx)
  · -- sufIdx l (x = mS+2n+1+l = lastU + 3 + l): the key new case
    have hl : l < mS - 1 := hv
    show (offsetForm 3 1 (3 + l)).Sat (copiedSlice mS n)
        (Fin.cons (mS + 2 * t) (Fin.cons x (Fin.cons (mS + 1)
          (Fin.cons (mS + 2 * (n - 1)) Fin.elim0)))) Fin.elim0 ↔ x = mS + 2 * n + 1 + l
    rw [offsetForm_sat 3 1 (3 + l) (copiedSlice mS n) _
      (by rw [hlen]; show mS + 2 * (n - 1) < 2 * (mS + n); omega)
      (by rw [hlen]; show x < 2 * (mS + n); exact hx)]
    show x = (mS + 2 * (n - 1)) + (3 + l) ↔ x = mS + 2 * n + 1 + l
    omega

end CopiedLandmark
