import LeanLab.GoldbachAverage.Decomp82

/-!
BHMS19, arXiv 1704.06103v2 pages 17 to 19, Lemma 7 in this version.
P0051 cites the published numbering Lemma 8 in its page 20 eq. 84.
The low and high zero ranges and the explicit formula remainder are separated.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp287d
open MeasureTheory

/-- The low zero increment sum, BHMS page 17 psi one in increment form. -/
def lowZeros (x h t : ℝ) : ℂ :=
  zeroSum (fun ρ => if |ρ.im| ≤ x / h then
    (((t + h : ℝ) : ℂ) ^ ρ - (t : ℂ) ^ ρ) / ρ else 0)

/-- The high zero increment sum, BHMS page 17 psi two. -/
def highZeros (x h t : ℝ) : ℂ :=
  zeroSum (fun ρ => if x / h < |ρ.im| ∧ |ρ.im| ≤ x then
    (((t + h : ℝ) : ℂ) ^ ρ - (t : ℂ) ^ ρ) / ρ else 0)

/-- LEAF. BHMS page 17, the explicit formula split and the following integral display.
Specialize to q one and bound the squared remainder by x log to the fourth x. -/
theorem explicit_variance_split : ∃ K : ℝ, 0 ≤ K ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      (∫ t in x..(2 * x), (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) ≤
        K * ((∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) +
          (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) + x * Real.log x ^ 4) := by
  sorry

/-- LEAF. BHMS page 18, the low zero mean square displays.
Use beta at most Theta instead of the stronger B star exponent.
The finite zero sum square is a genuine interval integrable function. -/
theorem low_zero_variance : 1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖lowZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) ≤
        C * h * x ^ (2 * Theta) * Real.log x ^ 4 := by
  sorry

/-- LEAF. BHMS pages 18 and 19, the high zero mean square displays.
Use the symmetric reciprocal ordinate bound and Lemma 3 tail estimate.
The finite zero sum square is a genuine interval integrable function. -/
theorem high_zero_variance : 1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖highZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) ≤
        C * h * x ^ (2 * Theta) * Real.log x ^ 4 := by
  sorry

/-- LEAF. The bounded window extension from BHMS page 17 range h at least two
 to P0051 page 20 eq. 84 range h at least one.
For one at most h at most two, at most three von Mangoldt terms occur.
Their logarithmic bound gives the stated dyadic square estimate. -/
theorem bounded_window_variance : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 1 ≤ h → h ≤ 2 →
      (∫ t in x..(2 * x), (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) ≤
        C * x * Real.log x ^ 4 := by
  sorry

/-- The exact bhms_84 proposition follows from the two zero ranges and the remainder.
CONDITIONAL ON the four OPEN leaves. -/
theorem bhms_84_assembled : GSInputs.BHMSShortIntervalVariance := by
  intro hlo hhi
  obtain ⟨K, hK, hs⟩ := explicit_variance_split
  obtain ⟨C₁, hC₁, hl⟩ := low_zero_variance hlo hhi
  obtain ⟨C₂, hC₂, hu⟩ := high_zero_variance hlo hhi
  obtain ⟨C₀, hC₀, hb⟩ := bounded_window_variance
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

example : type_of% Decomp82.bhms_84 = type_of% bhms_84_assembled := rfl

end LeanLab.GoldbachAverage.Decomp287d
