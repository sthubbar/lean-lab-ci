/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv math/0201299 pages 29 to 30, display 43 and the moment recurrence.
A sharper block certificate remains an explicit input to the open numerical targets.
-/
import LeanLab.PlattTrudgian2014.LambdaBlocks

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Complex Finset

noncomputable def blockAverage (h : ℕ) (t : ℝ) (ρ : ℂ) (β : ℝ) : ℝ :=
  1 / (2 : ℝ) ^ h * ∑ r ∈ range (2 ^ h), momentIntegrand h t ρ ((β + r) / (2 : ℝ) ^ h)

def BlockBound (h : ℕ) (t F : ℝ) : Prop :=
  ∀ ρ : ℂ, ‖ρ‖ ≤ 1 → ∀ β ∈ Set.Icc (0 : ℝ) 1, blockAverage h t ρ β ≤ F

@[fun_prop]
theorem continuous_blockAverage (h : ℕ) (t : ℝ) (ρ : ℂ) : Continuous (blockAverage h t ρ) := by
  unfold blockAverage
  fun_prop

theorem expMoment_block_eq (L h : ℕ) (t : ℝ) (ρ : ℂ) :
    expMoment (L + h) t ρ =
      ∫ β in (0 : ℝ)..1, momentIntegrand L t ρ β * blockAverage h t ρ β := by
  unfold expMoment
  rw [integral_branches (continuous_momentIntegrand _ _ _) (2 ^ h) (by positivity)]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext β
  simp only [moment_inverse_branch, blockAverage]
  rw [← Finset.mul_sum]
  ring

/-- CONDITIONAL ON the supplied BlockBound certificate. -/
theorem expMoment_block_le (L h : ℕ) (t F : ℝ) (hb : BlockBound h t F)
    {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) : expMoment (L + h) t ρ ≤ F * expMoment L t ρ := by
  rw [expMoment_block_eq]
  have h1 : Continuous (fun β => momentIntegrand L t ρ β * blockAverage h t ρ β) := by fun_prop
  have h2 : Continuous (fun β => F * momentIntegrand L t ρ β) := by fun_prop
  calc
    _ ≤ ∫ β in (0 : ℝ)..1, F * momentIntegrand L t ρ β :=
      intervalIntegral.integral_mono_on (by norm_num) (h1.intervalIntegrable _ _)
        (h2.intervalIntegrable _ _) (fun β hβ => by
          have he := mul_le_mul_of_nonneg_left (hb ρ hρ β hβ)
            (Real.exp_nonneg (t * (ρ * G L β).re))
          simpa only [momentIntegrand, mul_comm] using he)
    _ = F * expMoment L t ρ := by rw [intervalIntegral.integral_const_mul]; rfl

theorem BlockBound_trivial (h : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    BlockBound h t (Real.exp (t * h)) := by
  intro ρ hρ β hβ
  unfold blockAverage
  have hn : (0 : ℝ) < 2 ^ h := by positivity
  have hterm (r : ℕ) : momentIntegrand h t ρ ((β + r) / (2 : ℝ) ^ h) ≤ Real.exp (t * h) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ ht
    calc
      (ρ * G h ((β + r) / (2 : ℝ) ^ h)).re ≤ ‖ρ * G h ((β + r) / (2 : ℝ) ^ h)‖ :=
        Complex.re_le_norm _
      _ = ‖ρ‖ * ‖G h ((β + r) / (2 : ℝ) ^ h)‖ := norm_mul _ _
      _ ≤ 1 * h := mul_le_mul hρ (norm_G_le _ _) (norm_nonneg _) (by norm_num)
      _ = h := one_mul _
  calc
    _ ≤ 1 / (2 : ℝ) ^ h * ∑ r ∈ range (2 ^ h), Real.exp (t * h) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun r _ => hterm r) (by positivity)
    _ = Real.exp (t * h) := by simp

theorem blockAverage_zero_direction (h : ℕ) (t β : ℝ) : blockAverage h t 0 β = 1 := by
  simp [blockAverage, momentIntegrand]

theorem BlockBound_one_le {h : ℕ} {t F : ℝ} (hb : BlockBound h t F) : 1 ≤ F := by
  have hh := hb 0 (by simp) 0 (by constructor <;> norm_num)
  rwa [blockAverage_zero_direction] at hh

/-- CONDITIONAL ON the supplied BlockBound certificate. -/
theorem expMoment_block_iterate (L h n : ℕ) (t F : ℝ) (hb : BlockBound h t F)
    {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) :
    expMoment (L + n * h) t ρ ≤ F ^ n * expMoment L t ρ := by
  have hF : 0 ≤ F := (by norm_num : (0 : ℝ) ≤ 1).trans (BlockBound_one_le hb)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc]
    calc
      _ ≤ F * expMoment (L + n * h) t ρ := expMoment_block_le _ _ _ _ hb hρ
      _ ≤ F * (F ^ n * expMoment L t ρ) := mul_le_mul_of_nonneg_left ih hF
      _ = F ^ (n + 1) * expMoment L t ρ := by ring

theorem expMoment_zero (t : ℝ) (ρ : ℂ) : expMoment 0 t ρ = 1 := by
  simp [expMoment, momentIntegrand, G]

/-- CONDITIONAL ON the supplied BlockBound certificate. -/
theorem expMoment_block_pow (h n : ℕ) (t F : ℝ) (hb : BlockBound h t F)
    {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) : expMoment (n * h) t ρ ≤ F ^ n := by
  simpa only [zero_add, expMoment_zero, mul_one] using expMoment_block_iterate 0 h n t F hb hρ

#print axioms continuous_blockAverage
#print axioms expMoment_block_eq
#print axioms expMoment_block_le
#print axioms BlockBound_trivial

#print axioms blockAverage_zero_direction

#print axioms BlockBound_one_le

#print axioms expMoment_block_iterate

#print axioms expMoment_zero

#print axioms expMoment_block_pow

end LeanLab.PlattTrudgian2014
