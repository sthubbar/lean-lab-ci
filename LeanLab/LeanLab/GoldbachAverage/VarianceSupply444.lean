import LeanLab.GoldbachAverage.Decomp444d
import LeanLab.GoldbachAverage.FourierConsequences444
import LeanLab.GoldbachAverage.BoundedWindow402

/-!
Exact supplied assemblies of the BHMS zero variance and GS Corollary 2 statements.
Sources: BHMS pages 17 to 19 and P0051 pages 19 and 20.
Only the truncated explicit formula and the previously blocked Grosswald input stay cited.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.VarianceSupply444
open MeasureTheory Finset
open Decomp287d Decomp402c Decomp402f

/-- Exact source assembly from the supplies proved in this task.
The BHMS and Corollary 2 assemblies retain their named cited dependencies. -/
theorem low_zero_variance_proved : 1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖lowZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) ≤
        C * h * x ^ (2 * Theta) * Real.log x ^ 4 := by
  intro hlo hhi
  obtain ⟨K, hK, hk⟩ := Decomp444b.low_pair_integral_assembled hlo hhi
  obtain ⟨C, hC, hc⟩ := low_pair_count
  refine ⟨K * C, by positivity, ?_⟩
  intro x h hx hh hhx
  obtain ⟨hi, hb⟩ := hk x h hx hh hhx
  refine ⟨hi, hb.trans ?_⟩
  have hmul := mul_le_mul_of_nonneg_left (hc x h hx hh hhx)
    (show 0 ≤ K * h ^ 2 * x ^ (2 * Theta - 1) by positivity)
  have hx0 : 0 < x := by linarith
  have hh0 : h ≠ 0 := by linarith
  have hp : x ^ (2 * Theta - 1) * x = x ^ (2 * Theta) := by
    have he := Real.rpow_add hx0 (2 * Theta - 1) 1
    have hexp : 2 * Theta - 1 + 1 = 2 * Theta := by ring
    rw [hexp, Real.rpow_one] at he
    exact he.symm
  calc K * h ^ 2 * x ^ (2 * Theta - 1) * lowPairWeight x h
      ≤ (K * h ^ 2 * x ^ (2 * Theta - 1)) * (C * (x / h) * Real.log x ^ 4) := hmul
    _ = (K * C) * h * (x ^ (2 * Theta - 1) * x) * Real.log x ^ 4 := by
      field_simp [hh0]
      <;> ring
    _ = _ := by rw [hp]


example : type_of% Decomp287d.low_zero_variance = type_of% low_zero_variance_proved := rfl

/-- Exact source assembly from the supplies proved in this task.
The BHMS and Corollary 2 assemblies retain their named cited dependencies. -/
theorem high_zero_variance_proved : 1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖highZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) ≤
        C * h * x ^ (2 * Theta) * Real.log x ^ 4 := by
  intro hlo hhi
  obtain ⟨K, hK, hk⟩ := Decomp444c.high_pair_integral_assembled hlo hhi
  obtain ⟨C, hC, hc⟩ := high_pair_count
  refine ⟨K * C, by positivity, ?_⟩
  intro x h hx hh hhx
  obtain ⟨hi, hb⟩ := hk x h hx hh hhx
  refine ⟨hi, hb.trans ?_⟩
  have hx0 : 0 < x := by linarith
  have hp : x ^ (2 * Theta + 1) = x ^ (2 * Theta) * x := by
    rw [Real.rpow_add hx0, Real.rpow_one]
  have hm := mul_le_mul_of_nonneg_left (hc x h hx hh hhx)
    (show 0 ≤ K * x ^ (2 * Theta + 1) by positivity)
  calc _ ≤ (K * x ^ (2 * Theta + 1)) * (C * (h / x) * Real.log x ^ 4) := hm
    _ = _ := by rw [hp]; field_simp


example : type_of% Decomp287d.high_zero_variance = type_of% high_zero_variance_proved := rfl

/-- Exact source assembly from the supplies proved in this task.
The BHMS and Corollary 2 assemblies retain their named cited dependencies. -/
theorem bhms_84_supplied : GSInputs.BHMSShortIntervalVariance := by
  intro hlo hhi
  obtain ⟨K, hK, hs⟩ := Decomp444d.explicit_variance_split_assembled
  obtain ⟨C₁, hC₁, hl⟩ := low_zero_variance_proved hlo hhi
  obtain ⟨C₂, hC₂, hu⟩ := high_zero_variance_proved hlo hhi
  obtain ⟨C₀, hC₀, hb⟩ := BoundedWindow402.bounded_window_variance_proved
  refine ⟨C₀ + K * (C₁ + C₂ + 1), by positivity, ?_⟩
  intro x h hx hh hhx
  let B : ℝ := h * x ^ (2 * Theta) * Real.log x ^ 4
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hxp : x ≤ h * x ^ (2 * Theta) :=
    (Real.self_le_rpow_of_one_le (by linarith : 1 ≤ x)
      (by linarith : 1 ≤ 2 * Theta)).trans
        (le_mul_of_one_le_left (by positivity) hh)
  have hrem : x * Real.log x ^ 4 ≤ B :=
    mul_le_mul_of_nonneg_right hxp (by positivity)
  suffices hmain : (∫ t in x..(2 * x), (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) ≤
      (C₀ + K * (C₁ + C₂ + 1)) * B by
    simpa only [B, mul_assoc] using hmain
  by_cases hh2 : 2 ≤ h
  · have hlb := (hl x h hx hh2 hhx).2
    have hub := (hu x h hx hh2 hhx).2
    have hsum : (∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) +
        (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) + x * Real.log x ^ 4 ≤
        (C₁ + C₂ + 1) * B := by
      dsimp [B] at *
      nlinarith only [hlb, hub, hrem]
    calc _ ≤ K * ((∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) +
          (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) + x * Real.log x ^ 4) :=
        hs x h hx hh2 hhx
      _ ≤ K * ((C₁ + C₂ + 1) * B) := mul_le_mul_of_nonneg_left hsum hK
      _ ≤ (C₀ + K * (C₁ + C₂ + 1)) * B := by
        nlinarith only [mul_nonneg hC₀ hB]
  · have hsml := hb x h hx hh (le_of_lt (lt_of_not_ge hh2))
    calc _ ≤ C₀ * x * Real.log x ^ 4 := hsml
      _ ≤ C₀ * B := by nlinarith only [mul_le_mul_of_nonneg_left hrem hC₀]
      _ ≤ (C₀ + K * (C₁ + C₂ + 1)) * B := by
        have hp : 0 ≤ K * (C₁ + C₂ + 1) := by positivity
        nlinarith only [mul_nonneg hp hB]


example : type_of% Decomp82.bhms_84 = type_of% bhms_84_supplied := rfl

/-- Exact source assembly from the supplies proved in this task.
The BHMS and Corollary 2 assemblies retain their named cited dependencies. -/
theorem gs_corollary2_supplied : 1 / 2 ≤ Theta → Theta < 3 / 4 → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ,
    N₀ ≤ N → ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2
      + 2 * zeroSum (fun ρ => if 1 / 2 ≤ ρ.re then (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) else 0)‖
      ≤ ε * (N : ℝ) ^ ((3 : ℝ) / 2) := by
  exact GSCor2.gs_corollary2_of_bhms
    (Decomp82.error_from_variances Decomp82.grosswald_82 (Decomp82.full_variance_85 Decomp82.grosswald_82 bhms_84_supplied) FourierConsequences444.gallagher_19_proved)


example : type_of% gs_corollary2 = type_of% gs_corollary2_supplied := rfl

end LeanLab.GoldbachAverage.VarianceSupply444
