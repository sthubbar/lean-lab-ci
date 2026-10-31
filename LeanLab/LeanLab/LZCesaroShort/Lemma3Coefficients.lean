import LeanLab.LZCesaroShort.Lemma3Comparison

/-!
# The coefficient algebra for P0058 Lemma 3

AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1606.00869v2, page 3, Lemma 3.
The cited proof in arXiv 1011.3198, page 3, uses the weighted Lambda square moment.
These elementary identities isolate that moment without asserting its asymptotic.
All sums below include n equal to zero.
-/

namespace LeanLab.LZCesaroShort

open scoped ArithmeticFunction.vonMangoldt

/-- Absolute convergence of the weighted Lambda square moment. -/
lemma summable_lambda_sq_exp {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => Λ n ^ 2 * Real.exp (-2 * n / N)) := by
  have hc := summable_cS hN
  let S := ∑' n, ‖cS N n‖
  have hsq : Summable (fun n => ‖cS N n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) (hc.mul_left S)
    have hn : ‖cS N n‖ ≤ S := hc.le_tsum n (fun m _ => norm_nonneg _)
    simpa [pow_two] using mul_le_mul_of_nonneg_right hn (norm_nonneg (cS N n))
  refine hsq.congr fun n => ?_
  rw [cS, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  have he : Real.exp (-(n : ℝ) / N) ^ 2 = Real.exp (-2 * n / N) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]

/-- Absolute convergence of the corresponding weighted first moment. -/
lemma summable_lambda_exp_two {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => Λ n * Real.exp (-2 * n / N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (summable_cS hN)
  rw [cS, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le)]
  apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ hN0.le
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Absolute convergence of the geometric moment. -/
lemma summable_exp_two {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => Real.exp (-2 * n / N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Real.summable_pow_mul_exp_neg_nat_mul 0 (by positivity : (0 : ℝ) < 2 / N)
  refine h.congr fun n => ?_
  simp only [pow_zero, one_mul]
  congr 1
  ring

/-- The exact value of the geometric moment including the zero coefficient. -/
lemma tsum_exp_two_eq {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, Real.exp (-2 * n / N)) = 1 / (1 - Real.exp (-2 / (N : ℝ))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hq0 : 0 ≤ Real.exp (-2 / (N : ℝ)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 / (N : ℝ)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by norm_num) hN0
  have he : ∀ n : ℕ, Real.exp (-2 * n / N) = Real.exp (-2 / (N : ℝ)) ^ n := by
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [he]
  rw [tsum_geometric_of_lt_one hq0 hq1, one_div]

/-- Expand the coefficient moment into its square, first and geometric moments. -/
theorem lemma3_moment_decomposition {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, (Λ n - 1) ^ 2 * Real.exp (-2 * n / N)) =
      (∑' n : ℕ, Λ n ^ 2 * Real.exp (-2 * n / N))
        - 2 * (∑' n : ℕ, Λ n * Real.exp (-2 * n / N))
        + 1 / (1 - Real.exp (-2 / (N : ℝ))) := by
  have hs := summable_lambda_sq_exp hN
  have hf := summable_lambda_exp_two hN
  have hg := summable_exp_two hN
  have he : ∀ n : ℕ, (Λ n - 1) ^ 2 * Real.exp (-2 * n / N) =
      (Λ n ^ 2 * Real.exp (-2 * n / N) - 2 * (Λ n * Real.exp (-2 * n / N)))
        + Real.exp (-2 * n / N) := by intro n; ring
  simp_rw [he]
  calc
    _ = (∑' n : ℕ, (Λ n ^ 2 * Real.exp (-2 * n / N) - 2 * (Λ n * Real.exp (-2 * n / N))))
        + (∑' n : ℕ, Real.exp (-2 * n / N)) := (hs.sub (hf.mul_left 2)).tsum_add hg
    _ = ((∑' n : ℕ, Λ n ^ 2 * Real.exp (-2 * n / N))
        - (∑' n : ℕ, 2 * (Λ n * Real.exp (-2 * n / N))))
        + (∑' n : ℕ, Real.exp (-2 * n / N)) := by
      rw [hs.tsum_sub (hf.mul_left 2)]
    _ = _ := by rw [tsum_mul_left, tsum_exp_two_eq hN]

end LeanLab.LZCesaroShort
