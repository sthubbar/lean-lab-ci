/-
Why the withdrawn Theorem 2 of P0056 Xi 2012, arXiv 1206.2148 v1, appears false.
If every element a of A has fractional part {aα} < 1/4, then every a + b with a, b ∈ A has
{(a + b)α} < 1/2, so no n with {nα} ≥ 1/2 lies in A + A. For α = √2 and A the primes with
{p√2} < 1/4, A should have relative density 1/4 in progressions by Vinogradov's
equidistribution of pα, which is NOT proved here, while about half of all even n miss A + A.
Only the elementary obstruction is proved below.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Xi2012

/-- `{(a + b)α} ≤ {aα} + {bα}`. -/
theorem fract_sum_le (α : ℝ) (a b : ℕ) :
    Int.fract (((a + b : ℕ) : ℝ) * α) ≤ Int.fract ((a : ℝ) * α) + Int.fract ((b : ℝ) * α) := by
  have : ((a + b : ℕ) : ℝ) * α = (a : ℝ) * α + (b : ℝ) * α := by push_cast; ring
  rw [this]
  exact Int.fract_add_le _ _

/-- **The Bohr-set obstruction.** If every element of `A` has `{aα} < 1/4`, no `n` with
`{nα} ≥ 1/2` is a sum of two elements of `A`. -/
theorem not_sum_of_bohr (α : ℝ) (A : Set ℕ) (hA : ∀ a ∈ A, Int.fract ((a : ℝ) * α) < 1 / 4)
    (n : ℕ) (hn : 1 / 2 ≤ Int.fract ((n : ℝ) * α)) : ¬ ∃ a ∈ A, ∃ b ∈ A, a + b = n := by
  rintro ⟨a, ha, b, hb, rfl⟩
  have := fract_sum_le α a b
  linarith [hA a ha, hA b hb]

end LeanLab.Xi2012
