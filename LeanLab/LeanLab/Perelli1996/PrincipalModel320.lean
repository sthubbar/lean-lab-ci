/-
Perelli 1996, page 481 equation 2 and page 486 equation 27.
The finite principal model has the paper's logarithmic error scale.
The comparison with the prime sum remains a separate analytic input.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Absolute320
import LeanLab.Perelli1996.PrincipalTail320

namespace LeanLab.Perelli1996.PrincipalModel320
open Finset Real MeasureTheory
noncomputable section

/-- Every finite Ramanujan principal model has a logarithmic central kernel error. -/
theorem finite_model_error :
    ∃ C : ℝ, 0 < C ∧ ∀ m M : ℕ, 0 < m → m ≤ M → ∀ s : Finset ℕ,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ‖(∑ q ∈ s, Series320.coefficient m q) *
          (∫ α in (-δ)..δ, Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) -
        (m : ℂ) * (∑ q ∈ s, Series320.coefficient m q)‖ ≤
        C * (1 + Real.log m) * (1 + 1 / (2 * δ)) := by
  obtain ⟨C, hC, hbound⟩ := Absolute320.sum_norm_le_log
  refine ⟨C, hC, ?_⟩
  intro m M hm hmM s δ hδ hhalf
  have hs : ‖∑ q ∈ s, Series320.coefficient m q‖ ≤ C * (1 + Real.log m) := by
    calc
      _ ≤ ∑ q ∈ s, ‖Series320.coefficient m q‖ := norm_sum_le _ _
      _ ≤ ∑' q : ℕ, ‖Series320.coefficient m q‖ :=
        (Series320.summable_norm_coefficient m hm).sum_le_tsum s (fun _ _ => norm_nonneg _)
      _ ≤ _ := hbound m hm
  have hk := PrincipalTail320.central_coefficient_error M m hmM δ hδ hhalf
  have heq : (∑ q ∈ s, Series320.coefficient m q) *
        (∫ α in (-δ)..δ, Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) -
      (m : ℂ) * (∑ q ∈ s, Series320.coefficient m q) =
      (∑ q ∈ s, Series320.coefficient m q) *
        ((∫ α in (-δ)..δ, Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) - (m : ℂ)) := by ring
  rw [heq, norm_mul]
  exact mul_le_mul hs hk (norm_nonneg _) (by positivity)

/-- At primary radius P over N the finite principal model has error C N log N over P.
Page 481 equation 2, with the prime sum comparison excluded. -/
theorem finite_model_error_scaled (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N P : ℝ, Real.exp 1 ≤ N → 0 < P → P / N ≤ 1 / 2 →
      ∀ m M : ℕ, 0 < m → m ≤ M → (m : ℝ) ≤ c * N → ∀ s : Finset ℕ,
      ‖(∑ q ∈ s, Series320.coefficient m q) *
          (∫ α in (-(P / N))..(P / N), Kernel.T 0 (M + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)) -
        (m : ℂ) * (∑ q ∈ s, Series320.coefficient m q)‖ ≤
        C * N * Real.log N / P := by
  obtain ⟨C, hC, hbound⟩ := finite_model_error
  refine ⟨C * (2 + |Real.log c|), by positivity, ?_⟩
  intro N P hN hP hhalf m M hm hmM hmN s
  have hN0 : 0 < N := (Real.exp_pos 1).trans_le hN
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm := Real.log_le_log hmR hmN
  rw [Real.log_mul hc.ne' hN0.ne'] at hlogm
  have hlog : 1 + Real.log m ≤ (2 + |Real.log c|) * Real.log N := by
    have hprod := mul_nonneg (abs_nonneg (Real.log c)) (sub_nonneg.mpr hL1)
    have hlogc := le_abs_self (Real.log c)
    nlinarith
  have hratio : 2 ≤ N / P := by
    apply (le_div_iff₀ hP).mpr
    have h := (div_le_iff₀ hN0).mp hhalf
    linarith
  have hkernel : 1 + 1 / (2 * (P / N)) ≤ N / P := by
    have heq : 1 / (2 * (P / N)) = N / (2 * P) := by field_simp
    rw [heq]
    have hdiv : N / P = 2 * (N / (2 * P)) := by ring
    linarith
  have hb := hbound m M hm hmM s (P / N) (div_pos hP hN0) hhalf
  calc
    _ ≤ C * (1 + Real.log m) * (1 + 1 / (2 * (P / N))) := hb
    _ ≤ C * ((2 + |Real.log c|) * Real.log N) * (N / P) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlog hC.le) hkernel (by positivity) (by positivity)
    _ = _ := by ring

end
end LeanLab.Perelli1996.PrincipalModel320
