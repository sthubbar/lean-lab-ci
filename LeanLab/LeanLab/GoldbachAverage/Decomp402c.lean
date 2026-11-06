import LeanLab.GoldbachAverage.Decomp287d
import LeanLab.GoldbachAverage.PairKernel402

/-!
BHMS, arXiv 1704.06103v2 page 18, low zero part of Lemma 7.
The integrated pair kernel and the ordinate pair count are separate leaves.
Every pair weight uses the actual zero multiplicities.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp402c
open MeasureTheory
open Decomp287d

/-- The low ordinate pair kernel on BHMS page 18 after expansion of the square.
Both zero ranges retain the cutoff x over h. -/
def lowPairWeight (x h : ℝ) : ℝ :=
  ∑' ρ : NontrivialZero, ∑' σ : NontrivialZero,
    if |ρ.1.im| ≤ x / h ∧ |σ.1.im| ≤ x / h then
      (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
        (analyticOrderNatAt riemannZeta σ.1 : ℝ) / (1 + |ρ.1.im - σ.1.im|)
    else 0

/-- The pair weight is nonnegative, as in the BHMS page 18 positive kernel display. -/
theorem lowPairWeight_nonneg (x h : ℝ) : 0 ≤ lowPairWeight x h := by
  apply tsum_nonneg
  intro ρ
  apply tsum_nonneg
  intro σ
  split_ifs <;> positivity

/-- LEAF. BHMS page 18, the Cauchy Schwarz step, change of order, and pair integral display.
The zero sum square is interval integrable. Oscillatory power integration gives the pair kernel.
This leaf contains no ordinate count estimate. -/
theorem low_pair_integral : 1 / 2 < Theta → Theta < 1 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖lowZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) ≤
        K * h ^ 2 * x ^ (2 * Theta - 1) * lowPairWeight x h := by
  sorry

/-- LEAF. BHMS page 18, the two final low zero displays using Lemma 6.
Local zero counting bounds the reciprocal separation sum and the number of low ordinates.
The source log cubed bound is weakened to log to the fourth on x at least two. -/
theorem low_pair_count : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      lowPairWeight x h ≤ C * (x / h) * Real.log x ^ 4 := by
  simpa only [lowPairWeight] using PairKernel402.low_pair_count_ts

/-- The exact low_zero_variance target follows from the pair integral and pair count leaves.
CONDITIONAL ON low_pair_integral. -/
theorem low_zero_variance_assembled : 1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖lowZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) ≤
        C * h * x ^ (2 * Theta) * Real.log x ^ 4 := by
  intro hlo hhi
  obtain ⟨K, hK, hk⟩ := low_pair_integral hlo hhi
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

example : type_of% low_zero_variance = type_of% low_zero_variance_assembled := rfl

end LeanLab.GoldbachAverage.Decomp402c
