import LeanLab.Ricci1937.CFactorBounds
import LeanLab.Ricci1937.CParameters

/-!
Ricci 1937, page 83: sieve survivors satisfy the predicate of Theorem C part 2.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
noncomputable section

/-- The full elementary inclusion on page 83, before the count estimate. -/
theorem c2_survivor {g s x n : ℕ} (hg : 1 ≤ g) (hsg : g < s)
    (hx : 1 ≤ x) {C ξ : ℝ} (hC : 1 ≤ C) (hξ : 1 ≤ ξ) (hn : (n : ℝ) ≤ ξ)
    (hsize : (x : ℝ) < C * ξ ^ g)
    (hrough : ∀ p ∈ x.primeFactorsList,
      C * ξ ^ (((s : ℝ) - g) / (2 * s)) < (p : ℝ))
    (hsquare : ∀ p : ℕ, p.Prime → p ^ 2 ∣ x →
      C * ξ ^ ((g : ℝ) / s) < (p : ℝ)) :
    AlmostGT ((2 * s * g - 1) / (s - g))
      ((n : ℝ) ^ (((s : ℝ) - g) / (2 * s))) x ∧
      ∀ p ∈ x.primeFactors, x.factorization p < s := by
  have hξ0 : 0 ≤ ξ := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hsgR : (g : ℝ) < s := by exact_mod_cast hsg
  have hα : 0 ≤ ((s : ℝ) - g) / (2 * s) := by positivity
  have hξα : 1 ≤ ξ ^ (((s : ℝ) - g) / (2 * s)) :=
    Real.one_le_rpow hξ hα
  have hR : 1 ≤ C * ξ ^ (((s : ℝ) - g) / (2 * s)) := by nlinarith
  obtain ⟨hcount, hmult⟩ := c2_survivor_of_bounds hx (by omega) hR
    (mul_nonneg hC0 (Real.rpow_nonneg hξ0 _)) hrough hsquare
    (hsize.trans_le (c2_prime_threshold_power hg hsg hC hξ))
    (hsize.le.trans (c2_square_threshold_power hsg hC hξ))
  refine ⟨almostGT_mono hcount le_rfl ?_, hmult⟩
  calc
    (n : ℝ) ^ (((s : ℝ) - g) / (2 * s)) ≤
        ξ ^ (((s : ℝ) - g) / (2 * s)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hn hα
    _ ≤ C * ξ ^ (((s : ℝ) - g) / (2 * s)) :=
      le_mul_of_one_le_left (Real.rpow_nonneg hξ0 _) hC

example : AlmostGT 2 1 25 ∧
    ∀ p ∈ (25 : ℕ).primeFactors, (25 : ℕ).factorization p < 3 := by
  have hroot : (27 : ℝ) ^ ((1 : ℝ) / 3) = 3 := by
    rw [show (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hrough : ∀ p ∈ (25 : ℕ).primeFactorsList,
      (1 : ℝ) * 27 ^ (((3 : ℝ) - 1) / (2 * 3)) < (p : ℝ) := by
    intro p hp
    norm_num [show Nat.primeFactorsList 25 = [5, 5] by norm_num] at hp
    subst p
    norm_num [hroot]
  have hsquare : ∀ p : ℕ, p.Prime → p ^ 2 ∣ 25 →
      (1 : ℝ) * 27 ^ ((1 : ℝ) / 3) < (p : ℝ) := by
    intro p hp hsq
    have hp2 := hp.two_le
    have hle := Nat.le_of_dvd (by norm_num : 0 < 25) hsq
    have hp5 : p ≤ 5 := by nlinarith
    interval_cases p <;> norm_num [hroot] at *
  have h := c2_survivor (g := 1) (s := 3) (x := 25) (n := 1) (C := 1) (ξ := 27)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simpa using hrough) (by simpa using hsquare)
  simpa using h

end
end LeanLab.Ricci1937
