import LeanLab.GoldbachAverage.TailCount402
import LeanLab.GoldbachAverage.PairKernel402
import LeanLab.GoldbachAverage.Decomp287d

/-!
BHMS, arXiv 1704.06103v2 pages 18 and 19, high zero part of Lemma 7.
The symmetry step leaves an asymmetric reciprocal square tail times a separation kernel.
Its count is proved from the ported tail and the new reciprocal kernel.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp402f
open Finset MeasureTheory
open LeanLab.PNTPort.Selberg
open Decomp287d

/-- The asymmetric high zero kernel in BHMS page 19 after the symmetry step.
The second range is enlarged to all ordinates of absolute value at most x. -/
def highPairWeight (x h : ℝ) : ℝ :=
  ∑' ρ : NontrivialZero,
    if x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x then
      ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / |ρ.1.im| ^ 2) *
        ∑' σ : NontrivialZero, if |σ.1.im| ≤ x then
          (analyticOrderNatAt riemannZeta σ.1 : ℝ) / (1 + |ρ.1.im - σ.1.im|)
        else 0
    else 0

/-- The asymmetric high pair kernel is nonnegative, BHMS page 19. -/
theorem highPairWeight_nonneg (x h : ℝ) : 0 ≤ highPairWeight x h := by
  apply tsum_nonneg
  intro ρ
  split_ifs
  · apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro σ
    split_ifs <;> positivity
  · positivity

/-- The high pair count in BHMS page 19 final display, with log to the fourth.
All zero multiplicities and both ordinate ranges retain their paper meanings. -/
theorem high_pair_count : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      highPairWeight x h ≤ C * (h / x) * Real.log x ^ 4 := by
  classical
  obtain ⟨C, hC, hc⟩ := TailCount402.finite_high_pair_count
  refine ⟨C, hC, ?_⟩
  intro x h hx hh hhx
  let S := (PairKernel402.low_zeros_finite x (by linarith : 0 ≤ x)).toFinset
  let H := S.filter (fun ρ => x / h < |ρ.1.im|)
  have hS (ρ : NontrivialZero) : ρ ∈ S ↔ |ρ.1.im| ≤ x := Set.Finite.mem_toFinset _
  have hH (ρ : NontrivialZero) : ρ ∈ H ↔ x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x := by
    simp only [H, mem_filter, hS, and_comm]
  have hin (ρ : NontrivialZero) :
      (∑' σ : NontrivialZero, if |σ.1.im| ≤ x then
          (analyticOrderNatAt riemannZeta σ.1 : ℝ) / (1 + |ρ.1.im - σ.1.im|) else 0) =
      ∑ σ ∈ S, mz σ.1 / (1 + |ρ.1.im - σ.1.im|) := by
    rw [tsum_eq_sum (s := S) (fun σ hσ => by
      have hn : ¬ |σ.1.im| ≤ x := fun hh => hσ ((hS σ).mpr hh)
      exact if_neg hn)]
    apply sum_congr rfl
    intro σ hσ
    rw [if_pos ((hS σ).mp hσ)]
    rfl
  have he : highPairWeight x h = ∑ ρ ∈ H, (mz ρ.1 / |ρ.1.im| ^ 2) *
      (∑ σ ∈ S, mz σ.1 / (1 + |ρ.1.im - σ.1.im|)) := by
    unfold highPairWeight
    rw [tsum_eq_sum (s := H) (fun ρ hρ => if_neg (fun hh => hρ ((hH ρ).mpr hh)))]
    apply sum_congr rfl
    intro ρ hρ
    rw [if_pos ((hH ρ).mp hρ), hin]
    rfl
  rw [he]
  have hb := hc x h hx hh hhx (H.image (fun ρ => ρ.1)) (S.image (fun ρ => ρ.1))
    (by
      intro ρ hρ
      obtain ⟨σ, hσ, rfl⟩ := mem_image.mp hρ
      exact ⟨σ.2, ((hH σ).mp hσ).1⟩)
    (by
      intro ρ hρ
      obtain ⟨σ, hσ, rfl⟩ := mem_image.mp hρ
      exact ⟨σ.2, (hS σ).mp hσ⟩)
  unfold NontrivialZero at *
  have himage : (∑ ρ ∈ H.image (fun ρ => ρ.1), (mz ρ / |ρ.im| ^ 2) *
      (∑ σ ∈ S.image (fun σ => σ.1), mz σ / (1 + |ρ.im - σ.im|))) =
      ∑ ρ ∈ H, (mz ρ.1 / |ρ.1.im| ^ 2) *
      (∑ σ ∈ S, mz σ.1 / (1 + |ρ.1.im - σ.1.im|)) := by
    rw [sum_image Subtype.val_injective.injOn]
    apply sum_congr rfl
    intro ρ _
    rw [sum_image Subtype.val_injective.injOn]
  rw [himage] at hb
  exact hb

/-- LEAF. BHMS pages 18 and 19, ignore the high increment difference and expand its square.
Integrate the complex powers, compare the two reciprocal ordinate factors by squares,
and use symmetry to obtain the asymmetric high kernel. This contains no tail count. -/
theorem high_pair_integral : 1 / 2 < Theta → Theta < 1 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖highZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) ≤
        K * x ^ (2 * Theta + 1) * highPairWeight x h := by
  sorry

/-- The exact high_zero_variance target follows from the integrated kernel and its proved count.
CONDITIONAL ON high_pair_integral. -/
theorem high_zero_variance_assembled : 1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖highZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) ≤
        C * h * x ^ (2 * Theta) * Real.log x ^ 4 := by
  intro hlo hhi
  obtain ⟨K, hK, hk⟩ := high_pair_integral hlo hhi
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

example : type_of% high_zero_variance = type_of% high_zero_variance_assembled := rfl

end LeanLab.GoldbachAverage.Decomp402f
