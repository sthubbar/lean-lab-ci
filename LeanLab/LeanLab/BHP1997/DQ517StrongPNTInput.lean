/-
P0069 page 51, the strong prime number theorem input before display 5.17.
The existing lab strong PNT is for the weighted count psi. Its square root log error
implies every fixed cube root log exponential saving. This does not estimate b0 or
its rough number density terms.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PNTPort.StrongPNT.Bridge
import Mathlib

namespace LeanLab.BHP1997.DQ517StrongPNTInput
open Filter MeasureTheory
open scoped Topology

/-- Page 51 before display 5.17, the square root log error beats every fixed T0 power. -/
theorem eventually_exp_sqrt_log_le {c : ℝ} (hc : 0 < c) (N : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * Real.sqrt (Real.log x)) ≤
        Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  have ht : Tendsto (fun u : ℝ => N * u ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul N
  have hs : ∀ᶠ u : ℝ in atTop, N * u ^ (-(1 / 6 : ℝ)) < c :=
    ht.eventually (eventually_lt_nhds hc)
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have he : Real.sqrt (Real.log x) * Real.log x ^ (-(1 / 6 : ℝ)) =
      Real.log x ^ (1 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hl]
    congr 1
    norm_num
  have hmul : N * Real.log x ^ (1 / 3 : ℝ) ≤ c * Real.sqrt (Real.log x) := by
    calc
      _ = Real.sqrt (Real.log x) * (N * Real.log x ^ (-(1 / 6 : ℝ))) := by
        rw [← he]
        ring
      _ ≤ Real.sqrt (Real.log x) * c :=
        mul_le_mul_of_nonneg_left hx.le (Real.sqrt_nonneg (Real.log x))
      _ = _ := by ring
  apply Real.exp_le_exp.mpr
  linarith

/-- Page 51 before display 5.17, a stretched exponential prefix error for weighted primes. -/
theorem psi_error_stretched (N : ℝ) :
    ∃ C X : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |Chebyshev.psi x - x| ≤ C * x * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  obtain ⟨c, hc, B, hB⟩ := LeanLab.PNTPort.psi_explicit_strong
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((eventually_exp_sqrt_log_le hc N).and (eventually_ge_atTop (2 : ℝ)))
  refine ⟨max B 0, X, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨hE, hx2⟩ := hX x hx
  have hx0 : 0 ≤ x := by linarith
  calc
    _ ≤ B * x * Real.exp (-c * Real.sqrt (Real.log x)) := hB x hx2
    _ ≤ max B 0 * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0) (Real.exp_pos _).le
    _ ≤ max B 0 * x * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hE (mul_nonneg (le_max_right _ _) hx0)

/-- Page 51, the weighted prime error on a moving interval is controlled by its two ends. -/
theorem psi_interval_error_stretched (N : ℝ) :
    ∃ C X : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, X ≤ a → X ≤ b →
      |(Chebyshev.psi b - Chebyshev.psi a) - (b - a)| ≤
        C * b * Real.exp (-N * Real.log b ^ (1 / 3 : ℝ)) +
          C * a * Real.exp (-N * Real.log a ^ (1 / 3 : ℝ)) := by
  obtain ⟨C, X, hC, h⟩ := psi_error_stretched N
  refine ⟨C, X, hC, fun a b ha hb => ?_⟩
  rw [show (Chebyshev.psi b - Chebyshev.psi a) - (b - a) =
    (Chebyshev.psi b - b) - (Chebyshev.psi a - a) by ring]
  exact (abs_sub _ _).trans (add_le_add (h b hb) (h a ha))

end LeanLab.BHP1997.DQ517StrongPNTInput
