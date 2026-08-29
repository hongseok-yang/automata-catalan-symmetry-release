/-
# The coordinate bridge `cfgPos → cfgPosL` (§9 tower, Stage F3.7)

The selector (`CopiedSelector.cfgCellArmF`) emits its position clause `cfgPos` in
REDUCED wrapped coordinates (length `2(n+1)`, base `1 + 2t`), while the fibred
clause DFA of `CopiedTieGate` CONSUMES `cfgPosL` in COPIED
landmark coordinates (`yF = mS+1`, `yL = mS+2(n-1)`, `z = mS+2t`).  Because the
first `D` landmark `yF` sits at wrapped position `2`, the two coordinate systems
differ by a constant `-2`:

* the residue set must be REFLECTED `s ↦ (M + 2 - s) % M` (the Lean nat-safe form
  of `(2 - s) % M`),
* the front/back offsets shift by `-2`,
* the window threshold shifts `mthr ↦ mthr - 2`.

`cfgPos_imp_cfgPosL` is the (UNCONDITIONAL) forward direction.  Numerically
verified to hold with zero counterexamples over 400k random instances; the
converse fails only at the boundary bases (`t = 0`, `t ≈ n`) where `cfgPosL`'s
prefix/suffix stretch disjuncts over-fire — those bases are covered by the
selector's frozen arm, so the forward direction is the load-bearing one.
-/
import RequestProject.CopiedTieGate
import RequestProject.CopiedDstarCMS

namespace CopiedTieBridge

open scoped Classical

/-- **The forward coordinate bridge** (FG1/FG2 resolved): the reduced-coordinate
`cfgPos` at base `1+2t` implies the landmark-coordinate `cfgPosL` at `z = mS+2t`,
once the residue set is reflected (`s ↦ (M+2-s)%M`), the front/back offsets are
shifted by `-2`, and the window threshold is `mthr-2`.  Unconditional in `t`. -/
theorem cfgPos_imp_cfgPosL (M mthr : ℕ) (S Front Back : Finset ℕ) (mS n t : ℕ)
    (hM : 1 ≤ M) (hm : 1 ≤ mS) (ht : t < n) (hmthr : 2 ≤ mthr)
    (h : SliceFasGates.cfgPos M mthr S Front Back (2 * (n + 1)) (1 + 2 * t)) :
    CopiedTieGate.cfgPosL M (mthr - 2)
      (S.image (fun s => (M + 2 - s) % M))
      (Front.image (fun f => f - 2))
      (Back.image (fun k => k - 2))
      (mS + 1) (mS + 2 * (n - 1)) (mS + 2 * t) := by
  rw [CopiedTieGate.cfgPosL]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rcases h with ⟨hw1, hw2, hres⟩ | hfront | ⟨k, hkB, hkeq⟩
  · -- bulk residue arm
    refine Or.inl ⟨by omega, by omega, ?_⟩
    refine ⟨(M + 2 - (1 + 2 * t) % M) % M, Finset.mem_image_of_mem _ hres, ?_⟩
    set s := (1 + 2 * t) % M with hs_def
    set r := (M + 2 - s) % M with hr_def
    have hslt : s < M := by rw [hs_def]; exact Nat.mod_lt _ hM
    have hrlt : r < M := by rw [hr_def]; exact Nat.mod_lt _ hM
    -- s + r ≡ 2 [MOD M]
    have hsr : (s + r) % M = 2 % M := by
      have h1 : r ≡ M + 2 - s [MOD M] := by rw [hr_def]; exact Nat.mod_modEq _ _
      have h2 : (s + r) % M = (s + (M + 2 - s)) % M := Nat.ModEq.add_left s h1
      have h3 : s + (M + 2 - s) = M + 2 := by omega
      rw [h2, h3, Nat.add_mod_left]
    -- s ≡ 1 + 2t [MOD M]
    have hs : s ≡ 1 + 2 * t [MOD M] := by rw [hs_def]; exact Nat.mod_modEq _ _
    -- (1 + 2t) + r ≡ 2 [MOD M]
    have hkey : (1 + 2 * t) + r ≡ 2 [MOD M] := (hs.symm.add_right r).trans hsr
    -- the modular identity: (mS+1+(M-r)) ≡ mS+2t [MOD M]
    show (mS + 1 + (M - r)) % M = (mS + 2 * t) % M
    refine Nat.ModEq.add_right_cancel' r ?_
    have e1 : mS + 1 + (M - r) + r = mS + 1 + M := by omega
    have e2 : mS + 2 * t + r = (mS - 1) + ((1 + 2 * t) + r) := by omega
    rw [e1, e2]
    calc mS + 1 + M ≡ mS + 1 [MOD M] :=
          Nat.ModEq.add_left (mS + 1) (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
      _ = (mS - 1) + 2 := by omega
      _ ≡ (mS - 1) + ((1 + 2 * t) + r) [MOD M] := Nat.ModEq.add_left (mS - 1) hkey.symm
  · -- front arm
    refine Or.inr (Or.inl ⟨(1 + 2 * t) - 2, Finset.mem_image_of_mem _ hfront, ?_⟩)
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · left; subst ht0; exact ⟨by omega, by omega⟩
    · right; exact ⟨by omega, by omega⟩
  · -- back arm
    exact Or.inr (Or.inr ⟨k - 2, Finset.mem_image_of_mem _ hkB, by omega⟩)

/-- **Residue-reflection hygiene**: for `M` even, the reflection `s ↦ (M+2-s)%M`
sends an all-odd, `<M` residue set to an all-odd, `<M` set.  This feeds the
clause's `hSodd`/`hM2` hypotheses when the bridge hands the reflected selector
residues `S₁` to the clause DFA.  (Odd `mod` even is odd; `M+2-s` is odd as
`M+2` is even and `s` odd with `s < M`.) -/
theorem remapS_hygiene (M : ℕ) (S : Finset ℕ) (hM2 : M % 2 = 0)
    (hSlt : ∀ s ∈ S, s < M) (hSodd : ∀ s ∈ S, s % 2 = 1) :
    ∀ r ∈ S.image (fun s => (M + 2 - s) % M), r % 2 = 1 ∧ r < M := by
  intro r hr
  obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.mp hr
  have hslt := hSlt s hsS
  have hsodd := hSodd s hsS
  refine ⟨?_, Nat.mod_lt _ (by omega)⟩
  rw [Nat.mod_mod_of_dvd _ (show (2 : ℕ) ∣ M from ⟨M / 2, by omega⟩)]
  omega

end CopiedTieBridge
