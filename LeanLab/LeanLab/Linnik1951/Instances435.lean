/-
P0093 pages 162 and 166. Explicit nonempty instances for the new supply route.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp435a
import LeanLab.Linnik1951.Decomp435b

namespace LeanLab.Linnik1951

/-- P0093 page 162 equation 7.8. The weighted alignment hypothesis
holds for a one term unit weight and zero phase at every positive eta.
This is an actual nonzero norm instance. -/
theorem weighted_alignment_instance435 (η : ℝ) (hη : 0 < η) :
    (1 - η) * (∑ _m ∈ Finset.range 1, (1 : ℝ)) <
      ‖∑ _m ∈ Finset.range 1, (1 : ℂ) *
        Complex.exp ((-(2 * Real.pi * (0 : ℝ)) : ℝ) * Complex.I)‖ := by
  norm_num
  linarith

/-- P0093 page 166 denominator range in equation 9.3. Explicit
 dyadic points have denominator two to eight m between N to one tenth
and N to one seventh when N is two to seventy m. -/
theorem dyadic_system_range435 (m : ℕ) :
    (((2 ^ (70 * m) : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ ((2 ^ (8 * m) : ℕ) : ℝ)) ∧
      (((2 ^ (8 * m) : ℕ) : ℝ) ≤ ((2 ^ (70 * m) : ℕ) : ℝ) ^ (1 / 7 : ℝ)) := by
  push_cast
  have hlow : ((2 : ℝ) ^ (70 * m)) ^ (1 / 10 : ℝ) = (2 : ℝ) ^ (7 * m) := by
    rw [← Real.rpow_natCast 2 (70 * m), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have he : ((70 * m : ℕ) : ℝ) * (1 / 10 : ℝ) = ((7 * m : ℕ) : ℝ) := by
      push_cast
      ring
    rw [he, Real.rpow_natCast]
  have hhigh : ((2 : ℝ) ^ (70 * m)) ^ (1 / 7 : ℝ) = (2 : ℝ) ^ (10 * m) := by
    rw [← Real.rpow_natCast 2 (70 * m), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have he : ((70 * m : ℕ) : ℝ) * (1 / 7 : ℝ) = ((10 * m : ℕ) : ℝ) := by
      push_cast
      ring
    rw [he, Real.rpow_natCast]
  rw [hlow, hhigh]
  constructor <;> apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) <;> omega

/-- P0093 page 166 denominator range in equations 9.1 and 9.3.
For every proposed threshold there are larger N and a positive natural
q in the required denominator interval. This witnesses the numerical
hypotheses only. It does not assume or witness GRH. -/
theorem system_range_unbounded435 (N0 : ℕ) :
    ∃ N q : ℕ, N0 < N ∧ 1 ≤ q ∧
      (N : ℝ) ^ (1 / 10 : ℝ) ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
  let m := N0 + 1
  refine ⟨2 ^ (70 * m), 2 ^ (8 * m), ?_, by exact Nat.succ_le_iff.mpr (by positivity),
    (dyadic_system_range435 m).1, (dyadic_system_range435 m).2⟩
  have hp : 70 * m < 2 ^ (70 * m) := Nat.lt_two_pow_self
  have hm : N0 < 70 * m := by dsimp [m]; omega
  exact hm.trans hp

end LeanLab.Linnik1951
