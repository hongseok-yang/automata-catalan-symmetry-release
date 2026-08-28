/-
# Inverse Zeta Is Not WRP

Formalization of §9 (A second separation: inverse zeta is not a rank sweep)
of "A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.  Stable LaTeX labels in
`paper-full-new.tex` are canonical.
-/
import RequestProject.DyckPath
import RequestProject.Transducers
import RequestProject.Semilinearity

open Step

/-! ## Copied slice (`sec:inverse-zeta`, paper-full-new.tex) -/

/-- **Copied slice (`sec:inverse-zeta`, paper-full-new.tex).**
The *copied slice* `W_{m,n} = U^m (U D)^n D^m`: a flat run `(UD)^n` wrapped in
`U^m … D^m`, a Dyck path of semilength `m + n`.  On this two-parameter family the
inverse zeta has a nonsemilinear first-ascent profile.  (This object is unused
downstream — the §9 inverse-zeta results below are milestone placeholders — but
it is recorded with the paper's actual definition for fidelity.) -/
def copiedSlice (m n : ℕ) : List Step :=
  List.replicate m U ++ (List.replicate n [U, D]).flatten ++ List.replicate m D

/-! ### General height/concatenation infrastructure -/

theorem height_cons_succ (s : Step) (w : List Step) (k : ℕ) :
    height (s :: w) (k + 1)
      = (match s with | U => 1 | D => -1) + height w k := by
  rw [height_eq_count, height_eq_count, List.take_succ_cons]
  rcases s <;> simp <;> ring

theorem height_append_right (P Q : List Step) (k : ℕ) :
    height (P ++ Q) (P.length + k) = height P P.length + height Q k := by
  rw [height_eq_count, height_eq_count, height_eq_count,
    List.take_append, List.take_of_length_le (by omega : P.length ≤ P.length + k),
    Nat.add_sub_cancel_left, List.count_append, List.count_append,
    List.take_length]
  push_cast
  ring

theorem height_append_left (P Q : List Step) {k : ℕ} (hk : k ≤ P.length) :
    height (P ++ Q) k = height P k := by
  unfold height
  rw [List.take_append_of_le_length hk]

/-- Dyck paths are closed under concatenation. -/
theorem isDyckPath_append {P Q : List Step} (hP : IsDyckPath P)
    (hQ : IsDyckPath Q) : IsDyckPath (P ++ Q) := by
  constructor
  · intro k hk
    rcases Nat.lt_or_ge P.length k with h | h
    · rw [show k = P.length + (k - P.length) from by omega, height_append_right,
        hP.2]
      have := hQ.1 (k - P.length) (by simp at hk; omega)
      omega
    · rw [height_append_left P Q h]
      exact hP.1 k h
  · rw [show (P ++ Q).length = P.length + Q.length from by simp,
      height_append_right, hP.2, hQ.2]
    norm_num

/-- Dyck paths are closed under raising: `U ++ P ++ D`. -/
theorem isDyckPath_raise {Q : List Step} (hQ : IsDyckPath Q) :
    IsDyckPath (U :: (Q ++ [D])) := by
  have happfull : height (Q ++ [D]) (Q.length + 1) = height Q Q.length - 1 := by
    rw [show Q.length + 1 = Q.length + 1 from rfl, height_append_right]
    have h1 : height [D] 1 = -1 := by decide
    rw [h1]
    ring
  constructor
  · intro k hk
    rcases k with _ | k
    · rw [height_zero]
    · rw [height_cons_succ]
      have hk' : k ≤ Q.length + 1 := by simp at hk; omega
      rcases Nat.lt_or_ge Q.length k with h | h
      · rw [show k = Q.length + 1 from by omega, happfull, hQ.2]
        norm_num
      · rw [height_append_left Q [D] h]
        have := hQ.1 k h
        simp only []
        omega
  · rw [show (U :: (Q ++ [D])).length = Q.length + 1 + 1 from by simp,
      height_cons_succ, happfull, hQ.2]
    norm_num

/-! ### Basic facts about the copied slice -/

/-- The flat path `(UD)^n` is Dyck. -/
theorem isDyckPath_flat (n : ℕ) :
    IsDyckPath ((List.replicate n [U, D]).flatten) := by
  induction n with
  | zero => exact ⟨fun k hk => by simp at hk; rw [hk, height_zero], by decide⟩
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons]
    have hUD : IsDyckPath [U, D] := by
      constructor
      · intro k hk
        simp at hk
        interval_cases k <;> decide
      · decide
    exact isDyckPath_append hUD ih

theorem copiedSlice_zero (n : ℕ) :
    copiedSlice 0 n = (List.replicate n [U, D]).flatten := by
  unfold copiedSlice
  simp

theorem copiedSlice_succ (m n : ℕ) :
    copiedSlice (m + 1) n = U :: (copiedSlice m n ++ [D]) := by
  unfold copiedSlice
  rw [List.replicate_succ, List.replicate_succ' (n := m) (a := D)]
  simp [List.append_assoc]

/-- The copied slice is a Dyck path. -/
theorem isDyckPath_copiedSlice (m n : ℕ) : IsDyckPath (copiedSlice m n) := by
  induction m with
  | zero => rw [copiedSlice_zero]; exact isDyckPath_flat n
  | succ m ih => rw [copiedSlice_succ]; exact isDyckPath_raise ih

theorem length_copiedSlice (m n : ℕ) :
    (copiedSlice m n).length = 2 * (m + n) := by
  unfold copiedSlice
  simp [List.length_flatten, List.map_replicate]
  ring

/-- At `m = 1` the copied slice is the wrapped-flat slice. -/
theorem copiedSlice_one (n : ℕ) : copiedSlice 1 n = wrappedFlat n := by
  unfold copiedSlice wrappedFlat
  simp

/-- The copied slice lies in `D_{m+n}`. -/
theorem copiedSlice_mem_dyckPath (m n : ℕ) :
    copiedSlice m n ∈ DyckPath (m + n) :=
  ⟨isDyckPath_copiedSlice m n, length_copiedSlice m n⟩
