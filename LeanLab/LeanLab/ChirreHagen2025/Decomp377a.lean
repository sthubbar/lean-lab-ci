import LeanLab.ChirreHagen2025.Additional122

/-!
P0075 pages 4 and 5, proof of Lemma 2.3, displays 2.8 to 2.10.
The mean value input is Dona, Helfgott and Zuniga Alterman, page 103,
Proposition 2.11. https://doi.org/10.5802/jtnb.1194
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp377a
open MeasureTheory ArithmeticFunction

/-- P0075 page 4, the Selberg weight at xy = T and log y = 2 times 1.278.
Only positive indices at most T are used in the polynomial. -/
noncomputable def selbergWeight (T : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) ≤ T / Real.exp (2 * 1.278) then 1
  else Real.log (T / (n : ℝ)) / (2 * 1.278)

/-- P0075 page 5 display 2.9, the polynomial with the selected parameters. -/
noncomputable def polynomial (T t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊T⌋₊,
    ((vonMangoldt n * selbergWeight T n : ℝ) : ℂ) /
      (n : ℂ) ^ ((1 : ℂ) + t * Complex.I)

/-- P0075 page 5 display 2.8, continuity of the finite polynomial. -/
theorem polynomial_continuous (T : ℝ) : Continuous (polynomial T) := by
  unfold polynomial
  apply continuous_finsetSum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    have : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (show n ≠ 0 by omega)
  have he : Continuous (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by fun_prop
  exact continuous_const.div
    (he.const_cpow (Or.inl hn0))
    (fun t => Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))

/-- P0075 page 5 display 2.9, a safe elementary budget for the mean value input.
Even a constant six in the weighted Mangoldt square sum leaves the printed
minus 8000 term. This asserts no estimate for either arithmetic sum. -/
theorem mean_value_budget (T A B : ℝ) (hT : 10000 ≤ T)
    (hA : A ≤ 0.8053) (hB : B ≤ Real.log T ^ 2 / 2 + 6) :
    (T - 10000 + 4.133) * A + 8.265 * B ≤
      0.8053 * T + 4.1325 * Real.log T ^ 2 - 8000 := by
  have ha := mul_le_mul_of_nonneg_left hA (show 0 ≤ T - 10000 + 4.133 by linarith)
  have hb := mul_le_mul_of_nonneg_left hB (show (0 : ℝ) ≤ 8.265 by norm_num)
  nlinarith

/-- LEAF. P0075 page 5 display 2.9, mean square of the finite polynomial.
The proof uses Proposition 2.11 on page 103 of the cited mean value source,
then Lemma A.1 part 2 and Lemma A.2. There is no zeta error term here. -/
theorem polynomial_mean_square (hRH : RiemannHypothesis) (T : ℝ)
    (hT : 4 * 10 ^ 13 ≤ T) :
    (∫ t in (10 ^ 4 : ℝ)..T, ‖polynomial T t‖ ^ 2) ≤
      0.8053 * T + 4.1325 * Real.log T ^ 2 - 8000 := by
  sorry

/-- LEAF. P0075 pages 4 and 5, displays 2.7 and 2.10.
The zero term uses Lemma 2.2 part 2. The two elementary terms contribute
3.2 over t squared. The parameters are lambda = 1.278 and alpha = log T.
This leaf controls only the error, not the polynomial mean square. -/
theorem remainder_mean_square (hRH : RiemannHypothesis) (T : ℝ)
    (hT : 4 * 10 ^ 13 ≤ T) :
    IntervalIntegrable (fun t : ℝ =>
      ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I) +
        polynomial T t‖ ^ 2) volume (10 ^ 4) T ∧
    (∫ t in (10 ^ 4 : ℝ)..T,
      ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I) +
        polynomial T t‖ ^ 2) ≤
      522.295 * Real.log T ^ 2 + 7 / 10 ^ 12 := by
  sorry

/-- P0075 page 5, the final logarithmic ratio decreases beyond the stated threshold. -/
theorem logarithmic_ratio (T : ℝ) (hT : 4 * 10 ^ 13 ≤ T) :
    Real.log T ^ 2 ≤ (1024 / (4 * 10 ^ 13)) * T := by
  have hT0 : 0 < T := by linarith
  have hb : Real.log (4 * 10 ^ 13 : ℝ) ≤ 32 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc
      (4 * 10 ^ 13 : ℝ) ≤ (2.7 : ℝ) ^ 32 := by norm_num
      _ ≤ Real.exp 1 ^ 32 := by
        gcongr
        exact Real.exp_one_gt_d9.le.trans' (by norm_num)
      _ = Real.exp 32 := by rw [← Real.exp_nat_mul]; norm_num
  have he : Real.exp 2 ≤ (4 * 10 ^ 13 : ℝ) := by
    have h := Real.exp_one_lt_d9.le
    have hh : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [hh]
    nlinarith [Real.exp_pos 1]
  have hr := Real.log_div_sqrt_antitoneOn he (he.trans hT) hT
  have hr0 : 0 ≤ Real.log T / Real.sqrt T := by
    apply div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hrs := pow_le_pow_left₀ hr0 hr 2
  rw [div_pow, div_pow, Real.sq_sqrt hT0.le, Real.sq_sqrt (by norm_num)] at hrs
  have hb0 : 0 ≤ Real.log (4 * 10 ^ 13 : ℝ) := Real.log_nonneg (by norm_num)
  have hb2 := pow_le_pow_left₀ hb0 hb 2
  have hf : Real.log T ^ 2 / T ≤ 1024 / (4 * 10 ^ 13) := by
    apply hrs.trans
    exact div_le_div_of_nonneg_right (by norm_num at hb2 ⊢; exact hb2) (by norm_num)
  exact (div_le_iff₀ hT0).mp hf

/-- P0075 page 5, final arithmetic with eta = ten to the minus fourth. -/
theorem final_arithmetic (T : ℝ) (hT : 4 * 10 ^ 13 ≤ T) :
    (1 + (1 / 10000 : ℝ)) *
        (0.8053 * T + 4.1325 * Real.log T ^ 2 - 8000) +
      (1 + 1 / (1 / 10000 : ℝ)) *
        (522.295 * Real.log T ^ 2 + 7 / 10 ^ 12) ≤ 0.8056 * T := by
  have h := logarithmic_ratio T hT
  nlinarith

/-- P0075 page 5 display 2.8, the proved weighted square inequality.
This is the elementary combination step and has no cited analytic input. -/
theorem weighted_split (T : ℝ) (hT : 10 ^ 4 ≤ T)
    (herr : IntervalIntegrable (fun t : ℝ =>
      ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I) +
        polynomial T t‖ ^ 2) volume (10 ^ 4) T) :
    (∫ t in (10 ^ 4 : ℝ)..T,
      ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I)‖ ^ 2) ≤
    (1 + (1 / 10000 : ℝ)) * (∫ t in (10 ^ 4 : ℝ)..T, ‖polynomial T t‖ ^ 2) +
    (1 + 1 / (1 / 10000 : ℝ)) * (∫ t in (10 ^ 4 : ℝ)..T,
      ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I) +
        polynomial T t‖ ^ 2) := by
  have hp : IntervalIntegrable (fun t => ‖polynomial T t‖ ^ 2) volume (10 ^ 4) T :=
    ((polynomial_continuous T).norm.pow 2).intervalIntegrable (10 ^ 4) T
  have hz := Additional122.logDeriv_sq_intervalIntegrable (10 ^ 4) T (by norm_num) hT
  calc
    _ ≤ ∫ t in (10 ^ 4 : ℝ)..T,
        ((1 + (1 / 10000 : ℝ)) * ‖polynomial T t‖ ^ 2 +
          (1 + 1 / (1 / 10000 : ℝ)) *
            ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I) +
              polynomial T t‖ ^ 2) := by
      apply intervalIntegral.integral_mono hT hz ((hp.const_mul _).add (herr.const_mul _))
      intro t
      let z := deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I)
      let p := polynomial T t
      have htri : ‖z‖ ≤ ‖p‖ + ‖z + p‖ := by
        calc
          ‖z‖ = ‖-p + (z + p)‖ := by congr 1; ring
          _ ≤ ‖-p‖ + ‖z + p‖ := norm_add_le _ _
          _ = _ := by rw [norm_neg]
      have hs := pow_le_pow_left₀ (norm_nonneg z) htri 2
      have hy := two_mul_le_add_mul_sq (a := ‖p‖) (b := ‖z + p‖)
        (show (0 : ℝ) < 1 / 10000 by norm_num)
      change ‖z‖ ^ 2 ≤ _
      nlinarith
    _ = _ := by
      rw [intervalIntegral.integral_add (hp.const_mul _) (herr.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- P0075 Lemma 2.3, exact statement of DecompJ932.leaf_integration_step.
CONDITIONAL ON the two smaller mean-square leaves above. -/
theorem leaf_integration_step : RiemannHypothesis → ∀ T : ℝ, 4 * 10 ^ 13 ≤ T →
  (∫ t in (10 ^ 4 : ℝ)..T,
    ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I)‖ ^ 2)
    ≤ 0.8056 * T := by
  intro hRH T hT
  have he := remainder_mean_square hRH T hT
  apply (weighted_split T (by linarith) he.1).trans
  apply le_trans (add_le_add
    (mul_le_mul_of_nonneg_left (polynomial_mean_square hRH T hT) (by norm_num))
    (mul_le_mul_of_nonneg_left he.2 (by norm_num)))
  exact final_arithmetic T hT

end LeanLab.ChirreHagen2025.Decomp377a
