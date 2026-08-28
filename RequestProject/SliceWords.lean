/-
# `take`/`drop` of the wrapped-flat slice at block boundaries

Foundational list surgery for the slice-specific selection-count reduction: the
prefix of `W_n = U(UD)^n D` up to the start of loop-block `i` is `U(UD)^i`, and the
corresponding suffix is `(UD)^{n-i} D`.  These let us evaluate the forward run
`fwd` and the backward type `tau` (from `SliceCount`) at the block positions of the
slice in terms of the one-block iterate.

All proved from Mathlib + `DyckPath` only; axiom-clean.
-/
import RequestProject.DyckPath

open Step

namespace SliceWords

variable {α : Type*}

theorem length_flatten_replicate (l : List α) (n : ℕ) :
    ((List.replicate n l).flatten).length = n * l.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; ring

theorem take_append_length_add (l rest : List α) (k : ℕ) :
    (l ++ rest).take (l.length + k) = l ++ rest.take k :=
  List.take_length_add_append k

theorem drop_append_length_add (l rest : List α) (k : ℕ) :
    (l ++ rest).drop (l.length + k) = rest.drop k :=
  List.drop_length_add_append k

theorem take_flatten_replicate (l : List α) :
    ∀ i n, i ≤ n →
      ((List.replicate n l).flatten).take (i * l.length) = (List.replicate i l).flatten := by
  intro i
  induction i with
  | zero => intro n _; simp
  | succ i ih =>
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [List.replicate_succ, List.flatten_cons,
        show (i + 1) * l.length = l.length + i * l.length from by ring,
        take_append_length_add, ih m (by omega), ← List.flatten_cons, ← List.replicate_succ]

theorem drop_flatten_replicate (l : List α) :
    ∀ i n, i ≤ n →
      ((List.replicate n l).flatten).drop (i * l.length) = (List.replicate (n - i) l).flatten := by
  intro i
  induction i with
  | zero => intro n _; simp
  | succ i ih =>
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [List.replicate_succ, List.flatten_cons,
        show (i + 1) * l.length = l.length + i * l.length from by ring,
        drop_append_length_add, ih m (by omega), show m + 1 - (i + 1) = m - i from by omega]

/-- Prefix of the slice up to the start of loop-block `i`: `U(UD)^i`. -/
theorem wrappedFlat_take (i n : ℕ) (h : i ≤ n) :
    (wrappedFlat n).take (1 + 2 * i) = [U] ++ (List.replicate i [U, D]).flatten := by
  have hlen : ([U, D] : List Step).length = 2 := rfl
  have hle : 2 * i ≤ ((List.replicate n [U, D]).flatten).length := by
    rw [length_flatten_replicate, hlen]; omega
  have h2 : 2 * i = i * ([U, D] : List Step).length := by rw [hlen]; ring
  have h1 : 1 + 2 * i = ([U] : List Step).length + 2 * i := by simp
  rw [wrappedFlat, List.append_assoc, h1, take_append_length_add,
    List.take_append_of_le_length hle, h2, take_flatten_replicate [U, D] i n h]

/-- Suffix of the slice from the start of loop-block `i`: `(UD)^{n-i} D`. -/
theorem wrappedFlat_drop (i n : ℕ) (h : i ≤ n) :
    (wrappedFlat n).drop (1 + 2 * i) = (List.replicate (n - i) [U, D]).flatten ++ [D] := by
  have hlen : ([U, D] : List Step).length = 2 := rfl
  have hle : 2 * i ≤ ((List.replicate n [U, D]).flatten).length := by
    rw [length_flatten_replicate, hlen]; omega
  have h2 : 2 * i = i * ([U, D] : List Step).length := by rw [hlen]; ring
  have h1 : 1 + 2 * i = ([U] : List Step).length + 2 * i := by simp
  rw [wrappedFlat, List.append_assoc, h1, drop_append_length_add,
    List.drop_append_of_le_length hle, h2, drop_flatten_replicate [U, D] i n h]

end SliceWords
