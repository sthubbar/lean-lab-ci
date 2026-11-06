/-
P0069, pages 12 and 13, logarithmic energy in the dominant case.
The coefficient energy estimate is a named hypothesis throughout.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp437c

namespace LeanLab.BHP1997.Decomp437d
open Classical Complex Thm4 MeanSquareC165 DecompC165c Decomp414a Decomp437c
open scoped BigOperators

/-- Page 12, the logarithmic energy bound can use log x uniformly for F at most x.
The exponent is made nonnegative. No divisor moment estimate is asserted here.
CONDITIONAL on the explicit EnergyLogBound input. -/
theorem energy_log_uniform (henergy : EnergyLogBound)
    (B c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ a : ℕ → ℂ, CoeffBound a B →
    ∀ x F : ℝ, 1 ≤ Real.log x → 2 ≤ F → F ≤ x →
      energy a c1 c2 F ≤ C * Real.log x ^ K := by
  obtain ⟨K0, C0, hC0, he⟩ := henergy B c1 c2 hc1 hc2
  let C := C0 * (1 + Real.log 2 ^ K0)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, |K0|, hC, abs_nonneg _, ?_⟩
  intro a ha x F hx hF hFx
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlF : Real.log 2 ≤ Real.log F := Real.log_le_log (by norm_num) hF
  have hlFx : Real.log F ≤ Real.log x := Real.log_le_log (by linarith) hFx
  have hlx : 0 < Real.log x := by linarith
  have hK : 1 ≤ Real.log x ^ |K0| := Real.one_le_rpow hx (abs_nonneg _)
  have hpow : Real.log F ^ K0 ≤ (1 + Real.log 2 ^ K0) * Real.log x ^ |K0| := by
    by_cases hK0 : 0 ≤ K0
    · have hh : Real.log F ^ K0 ≤ Real.log x ^ |K0| := by
        rw [abs_of_nonneg hK0]
        exact Real.rpow_le_rpow (by linarith) hlFx hK0
      have ht : 0 ≤ Real.log 2 ^ K0 := Real.rpow_nonneg hl2.le _
      nlinarith [Real.rpow_nonneg hlx.le |K0|]
    · have hh : Real.log F ^ K0 ≤ Real.log 2 ^ K0 :=
        Real.rpow_le_rpow_of_nonpos hl2 hlF (le_of_not_ge hK0)
      have ht : 0 ≤ Real.log 2 ^ K0 := Real.rpow_nonneg hl2.le _
      nlinarith
  exact (he a ha F hF).trans (by
    have hh := mul_le_mul_of_nonneg_left hpow hC0.le
    convert hh using 1 <;> dsimp [C] <;> ring)

/-- Page 12, a fixed quadratic upper bound for the norm gives only logarithmically many levels.
This uses the existing exact finite dyadic count. -/
theorem quadratic_level_count {C x : ℝ} (hC : 1 ≤ C) (hx : 1 ≤ x)
    (hlx : 1 ≤ Real.log x) :
    ((dyadicLevels 1 (C * x ^ 2)).card : ℝ) ≤
      ((Real.log C + 2) / Real.log 2 + 2) * Real.log x := by
  have hC0 : 0 < C := by linarith
  have hx0 : 0 < x := by linarith
  have hU : 1 ≤ C * x ^ 2 := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hx)
  have h := dyadic_level_count_le (by norm_num : (0 : ℝ) < 1) hU
  have he : Real.log (C * x ^ 2) = Real.log C + 2 * Real.log x := by
    rw [Real.log_mul hC0.ne' (pow_pos hx0 2).ne', Real.log_pow]
    norm_num
  rw [Real.logb, Real.logb, Real.log_one, zero_div, sub_zero, he] at h
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hh : (Real.log C + 2 * Real.log x) / Real.log 2 + 2 ≤
      ((Real.log C + 2) / Real.log 2 + 2) * Real.log x := by
    apply (le_of_sub_nonneg _)
    have heq : ((Real.log C + 2) / Real.log 2 + 2) * Real.log x -
        ((Real.log C + 2 * Real.log x) / Real.log 2 + 2) =
        (Real.log C / Real.log 2 + 2) * (Real.log x - 1) := by ring
    rw [heq]
    positivity
  exact h.trans hh

/-- Page 12, one nonnegative logarithmic energy exponent controls both energies in 3.4. -/
theorem energy_cubic_log_bound {E C K L : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hL : 1 ≤ L) (he : E ≤ C * L ^ K) :
    E + 16 * E ^ 3 ≤ (C + 16 * C ^ 3) * L ^ (3 * K) := by
  have hL0 : 0 < L := by linarith
  have he1 : E ≤ C * L ^ (3 * K) := he.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) hC)
  have he3 : E ^ 3 ≤ C ^ 3 * L ^ (3 * K) := by
    calc
      _ ≤ (C * L ^ K) ^ 3 := pow_le_pow_left₀ hE he 3
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hL0.le]
        congr 2
        norm_num
        ring
  nlinarith

end LeanLab.BHP1997.Decomp437d
