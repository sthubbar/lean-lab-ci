/-
Split of the sealed statement `leaf_karLemma1_mvt` of
`LeanLab.ExceptionalSet.KaracubaSplit`, that is the proposition `KarLemma1`, into the mean
value bound at the least admissible exponent together with the two steps that carry it to
every larger admissible exponent.

The target statement is unchanged: it is the assembly `leaf_karLemma1_mvt_split` at the end
of this file, proved from the leaves below.
AI wrote the Lean code.
-/
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Leaves -/

/-- LEAF. The mean value bound at the least admissible exponent `b = n l + [n(n+1)/4 + 1]`
of the target: on the unit cube, the integral of the `2b`-th power of the exponential sum in
`n` coefficients is below `(20 n)^((n(n+1)/2) l)` times the power of `P` belonging to that
exponent. One inequality, and the case `b = b_l` of the target; every larger admissible `b`
is reached from it by `leaf_integral_step` and `leaf_rpow_step_identity`. -/
theorem leaf_mvt_threshold :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ P : ℕ, 0 < P →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℕ) <
        (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  sorry

/-- LEAF. One step in the exponent: every summand of the exponential sum has modulus one,
so the sum has modulus at most `P` everywhere on the cube, hence raising the power from `2b`
to `2b + 2` multiplies the integral by at most `P^2`. One inequality. -/
theorem leaf_integral_step :
    ∀ n : ℕ, 12 ≤ n → ∀ b : ℕ, ∀ P : ℕ, 0 < P →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (Nat.succ b) : ℕ) ≤
        (P : ℝ) ^ 2 *
          ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
            ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
              (2 * (b) : ℕ) := by
  sorry

/-- LEAF. The bookkeeping identity of the induction step: for `P > 0` the right hand side
of the target at the exponent `b + 1` is `P^2` times the right hand side at the exponent `b`,
because the exponent of `P` gains exactly `2` and `P^(u + 2) = P^u * P^2`. One identity. -/
theorem leaf_rpow_step_identity :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ b : ℕ, ∀ P : ℕ, 0 < P →
      (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
      (P : ℝ) ^ ((2 * (Nat.succ b) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
        + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) =
        (P : ℝ) ^ 2 *
          ((20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
          (P : ℝ) ^ ((2 * (b) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
            + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l)) := by
  sorry

/-- PROVED from the three leaves. Induction in the exponent from the admissible
`n l + [n(n+1)/4 + 1]` up to `b`: `leaf_integral_step` bounds the growth of the integral by
`P^2` per step, and `leaf_rpow_step_identity` says the right hand side grows by exactly the
same factor. -/
private theorem karLemma1_of_threshold (n l : ℕ) (hn : 12 ≤ n) (hl : 0 < l)
    (P : ℕ) (hP : 0 < P) :
    ∀ b : ℕ, n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) ≤ b →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (b) : ℕ) <
        (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * (b) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  intro b hb
  refine Nat.le_induction (m := n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) ?base ?step b hb
  case base =>
    have h := leaf_mvt_threshold n hn l hl P hP
    simpa using h
  case step =>
    intro m hm ih
    have hstep := leaf_integral_step n hn m P hP
    have hid := leaf_rpow_step_identity n hn l hl m P hP
    have hP2 : (0 : ℝ) < (P : ℝ) ^ 2 := pow_pos (by exact_mod_cast hP) 2
    rw [hid]
    exact lt_of_le_of_lt hstep (mul_lt_mul_of_pos_left ih hP2)

/-- The sealed statement of `leaf_karLemma1_mvt`, from the leaves of this file. -/
theorem leaf_karLemma1_mvt_split : KarLemma1 := by
  intro n hn l hl b hb P hP
  exact karLemma1_of_threshold n l hn hl P hP b hb

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
