/-
BHP1997, page 52. Discrete partial summation for a normalized upper weight.
The character cancellation estimate remains an explicit input.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp387d

namespace LeanLab.BHP1997.Task387
open Classical

/-- Page 52 normalization, auxiliary finite partial summation. Monotone
weights between one and two cost at most three in a uniform complex
partial sum bound. The cancellation estimate is an explicit input. -/
theorem monotone_rescaling_partial_sum_bound (f : ℕ → ℝ) (g : ℕ → ℂ)
    (n : ℕ) {R : ℝ} (hR : 0 ≤ R) (hf : Monotone f)
    (hb : ∀ i < n, 1 ≤ f i ∧ f i ≤ 2)
    (hg : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, g i‖ ≤ R) :
    ‖∑ i ∈ Finset.range n, f i • g i‖ ≤ 3*R := by
  by_cases hn : n = 0
  · subst n
    simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hR)
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hnlast : n-1 < n := by omega
  have hlast := hb (n-1) hnlast
  have hfirst := hb 0 hn0
  have hd (i : ℕ) : 0 ≤ f (i+1)-f i := sub_nonneg.mpr (hf (Nat.le_succ i))
  rw [Finset.sum_range_by_parts]
  calc
    _ ≤ ‖f (n-1) • ∑ i ∈ Finset.range n, g i‖ +
        ‖∑ i ∈ Finset.range (n-1), (f (i+1)-f i) • ∑ j ∈ Finset.range (i+1), g j‖ :=
      norm_sub_le _ _
    _ ≤ f (n-1)*R + ∑ i ∈ Finset.range (n-1), (f (i+1)-f i)*R := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ f (n-1))]
        exact mul_le_mul_of_nonneg_left (hg n le_rfl) (by linarith)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hd i)]
        exact mul_le_mul_of_nonneg_left (hg (i+1) (by have := Finset.mem_range.mp hi; omega)) (hd i)
    _ = (2*f (n-1)-f 0)*R := by
      rw [← Finset.sum_mul, Finset.sum_range_sub]
      ring
    _ ≤ 3*R := mul_le_mul_of_nonneg_right (by linarith) hR

/-- Pages 3 and 52, auxiliary upper normalization. A variable reciprocal-log
center becomes the exact constant center after logarithmic rescaling.
CONDITIONAL on the uniform raw centered partial sum estimate. -/
theorem logarithmic_center_rescaling (Y : ℝ) (M n : ℕ)
    (c : ℕ → ℂ) (d v : ℂ) {R : ℝ}
    (hY : 2 ≤ Y) (hM : Y ≤ (M : ℝ)) (hN : ((M+(n-1) : ℕ) : ℝ) ≤ 2*Y)
    (hR : 0 ≤ R)
    (hc : ∀ k ≤ n, ‖∑ i ∈ Finset.range k,
      (c (M+i)-d*v/(Real.log (M+i) : ℂ))‖ ≤ R) :
    ‖∑ i ∈ Finset.range n,
      (((Real.log (M+i)/Real.log Y : ℝ) : ℂ)*c (M+i)-d*v/(Real.log Y : ℂ))‖ ≤ 3*R := by
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 < Y := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos hY1
  let f : ℕ → ℝ := fun i => Real.log (M+i)/Real.log Y
  have hMi (i : ℕ) : 1 < (M+i : ℕ) := by
    have : (1 : ℝ) < M+i := by
      have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    exact_mod_cast this
  have hf : Monotone f := by
    intro i j hij
    apply div_le_div_of_nonneg_right _ hlog.le
    apply Real.log_le_log
    · exact_mod_cast (show 0 < M+i by have := hMi i; omega)
    · exact_mod_cast Nat.add_le_add_left hij M
  have hb : ∀ i < n, 1 ≤ f i ∧ f i ≤ 2 := by
    intro i hi
    have hlow : Y ≤ (M+i : ℕ) := by push_cast; exact hM.trans (le_add_of_nonneg_right (Nat.cast_nonneg i))
    have hu : ((M+i : ℕ) : ℝ) ≤ 2*Y := by
      have hin : i ≤ n-1 := by omega
      exact (show ((M+i : ℕ) : ℝ) ≤ (M+(n-1) : ℕ) by exact_mod_cast Nat.add_le_add_left hin M).trans hN
    have he : upperLogFactor Y (M+i) = f i := by
      rw [upperLogFactor, ite_eq_left (show 2 ≤ Y ∧ Y ≤ ((M+i : ℕ) : ℝ) ∧ ((M+i : ℕ) : ℝ) ≤ 2*Y from ⟨hY, hlow, hu⟩)]
      simp only [f, Nat.cast_add]
    simpa only [he] using upper_log_factor_bounds Y (M+i)
  have hh := monotone_rescaling_partial_sum_bound f
    (fun i => c (M+i)-d*v/(Real.log (M+i) : ℂ)) n hR hf hb hc
  have he (i : ℕ) :
      f i • (c (M+i)-d*v/(Real.log (M+i) : ℂ)) =
        ((Real.log (M+i)/Real.log Y : ℝ) : ℂ)*c (M+i)-d*v/(Real.log Y : ℂ) := by
    have hlm : Real.log (M+i) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hMi i))
    have hly : Real.log Y ≠ 0 := ne_of_gt hlog
    have hLm : (Real.log (M+i) : ℂ) ≠ 0 := by exact_mod_cast hlm
    have hLy : (Real.log Y : ℂ) ≠ 0 := by exact_mod_cast hly
    simp only [Complex.real_smul, f, Complex.ofReal_div]
    field_simp
  simpa only [he] using hh

end LeanLab.BHP1997.Task387
