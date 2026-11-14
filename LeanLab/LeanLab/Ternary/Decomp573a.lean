/-
Helfgott https://arxiv.org/abs/1312.7748v2 pages 50, 51 and 69.
Weighted L2 assembly for the prime and remainder split in Theorem 6.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp420e

namespace LeanLab.Ternary.Task573
open MeasureTheory

/-- The complementary circle domain with the exact open major arcs.
Helfgott page 10 equation 3.5 at delta zero eight and r zero 150000. -/
noncomputable def minorDomain (x : ℝ) : Set ℝ :=
  Set.Ioc (0 : ℝ) 1 \ (⋃ q : ℕ, ⋃ (_h : 1 ≤ q ∧ q ≤ Nat.gcd q 2 * 150000),
    ⋃ a : ℤ, ⋃ (_h : Int.gcd a q = 1),
      Set.Ioo ((a : ℝ) / q - (Nat.gcd q 2 * 8 * 150000 : ℝ) / (2 * q * x))
        ((a : ℝ) / q + (Nat.gcd q 2 * 8 * 150000 : ℝ) / (2 * q * x)))

/-- The large prime part of eta plus, with the paper cutoff p greater than sqrt x.
Helfgott page 50 proof of Theorem 6.3, definition of S one eta plus.
The von Mangoldt coefficient equals log p on prime indices. -/
noncomputable def primeSeries (x α : ℝ) : ℂ :=
  Task420.charSeries (fun n => if n.Prime ∧ Real.sqrt x < (n : ℝ) then
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)
    else 0) α

/-- The remainder after removing the large prime part.
Helfgott page 50 proof of Theorem 6.3, definition of S two eta plus. -/
noncomputable def remainderSeries (x α : ℝ) : ℂ :=
  LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α x - primeSeries x α

/-- The eta star norm weight in the weighted L2 triangle inequality.
Helfgott page 50 proof of Theorem 6.3 and page 60 equation 7.19. -/
noncomputable def starNorm (x α : ℝ) : ℝ :=
  ‖LeanLab.HelfgottArcs.S
    (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
      LeanLab.HelfgottArcs.etaT2 (49 * t)) α x‖

/-- Weighted Young inequality for the two complex summands.
Derived pointwise form of the weighted L2 triangle step on Helfgott page 50. -/
theorem weighted_norm_add_sq (u v : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ‖u + v‖ ^ 2 ≤ (a + b) * (‖u‖ ^ 2 / a + ‖v‖ ^ 2 / b) := by
  have hn := norm_add_le u v
  have hs : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hy : (‖u‖ + ‖v‖) ^ 2 ≤ (a + b) * (‖u‖ ^ 2 / a + ‖v‖ ^ 2 / b) := by
    apply (mul_le_mul_iff_right₀ (mul_pos ha hb)).mp
    field_simp [ha.ne', hb.ne']
    nlinarith [sq_nonneg (b * ‖u‖ - a * ‖v‖)]
  exact hs.trans hy

/-- Integrating the weighted Young bound assembles two weighted second moments.
Helfgott page 50 weighted triangle step, in a form using positive scalar budgets.
CONDITIONAL ON the two moment bounds supplied as hypotheses. -/
theorem weighted_integral_add_sq {μ : Measure ℝ} {u v : ℝ → ℂ} {w : ℝ → ℝ}
    {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) (hw : ∀ t, 0 ≤ w t)
    (hi : Integrable (fun t => w t * ‖u t + v t‖ ^ 2) μ)
    (hu : Integrable (fun t => w t * ‖u t‖ ^ 2) μ)
    (hv : Integrable (fun t => w t * ‖v t‖ ^ 2) μ)
    (hU : (∫ t, w t * ‖u t‖ ^ 2 ∂μ) ≤ a ^ 2 * X)
    (hV : (∫ t, w t * ‖v t‖ ^ 2 ∂μ) ≤ b ^ 2 * X) :
    (∫ t, w t * ‖u t + v t‖ ^ 2 ∂μ) ≤ (a + b) ^ 2 * X := by
  have he (t : ℝ) :
      w t * ((a + b) * (‖u t‖ ^ 2 / a + ‖v t‖ ^ 2 / b)) =
        (a + b) * ((w t * ‖u t‖ ^ 2) / a + (w t * ‖v t‖ ^ 2) / b) := by ring
  have hiR : Integrable
      (fun t => (a + b) * ((w t * ‖u t‖ ^ 2) / a + (w t * ‖v t‖ ^ 2) / b)) μ :=
    ((hu.div_const a).add (hv.div_const b)).const_mul (a + b)
  have hle := integral_mono hi hiR (fun t => by
    rw [← he]
    exact mul_le_mul_of_nonneg_left (weighted_norm_add_sq (u t) (v t) ha hb) (hw t))
  rw [integral_const_mul, integral_add (hu.div_const a) (hv.div_const b),
    integral_div, integral_div] at hle
  have hu' := (div_le_div_of_nonneg_right hU ha.le)
  have hv' := (div_le_div_of_nonneg_right hV hb.le)
  have halg : (a + b) * (a ^ 2 * X / a + b ^ 2 * X / b) = (a + b) ^ 2 * X := by
    field_simp
  exact hle.trans ((mul_le_mul_of_nonneg_left (add_le_add hu' hv')
    (by positivity)).trans_eq halg)

/-- Removing coefficients preserves absolute summability of the prime series.
Derived convergence justification for the split on Helfgott page 50. -/
theorem primeSeries_continuous {x : ℝ} (hx : 0 < x) : Continuous (primeSeries x) := by
  apply Task420.continuous_charSeries
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (Task420.etaPlus_coefficients_summable hx)
  intro n
  split_ifs <;> simp <;> positivity

/-- The full eta plus Fourier sum is continuous at every positive scale.
Derived convergence justification for Helfgott page 50. -/
theorem plusSeries_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (fun α => LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α x) := by
  simp_rw [Task420.S_eq_charSeries]
  exact Task420.continuous_charSeries _ (Task420.etaPlus_coefficients_summable hx)

/-- The remainder Fourier sum is continuous at every positive scale.
Derived convergence justification for Helfgott page 50. -/
theorem remainderSeries_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (remainderSeries x) :=
  (plusSeries_continuous hx).sub (primeSeries_continuous hx)

/-- The eta star norm weight is continuous at every positive scale.
Derived convergence justification for Helfgott page 50. -/
theorem starNorm_continuous {x : ℝ} (hx : 0 < x) : Continuous (starNorm x) := by
  unfold starNorm
  simp_rw [Task420.S_eq_charSeries]
  exact (Task420.continuous_charSeries _ (Task420.etaStar_coefficients_summable hx)).norm

/-- Every continuous Fourier summand has an integrable weighted second moment
on the minor domain. Derived compact interval justification for Helfgott page 50. -/
theorem weighted_moment_integrable {x : ℝ} (hx : 0 < x) {f : ℝ → ℂ}
    (hf : Continuous f) :
    IntegrableOn (fun α => starNorm x α * ‖f α‖ ^ 2) (minorDomain x) := by
  apply (((starNorm_continuous hx).mul (hf.norm.pow 2)).integrableOn_Icc).mono_set
  exact Set.Subset.trans Set.sdiff_subset Set.Ioc_subset_Icc_self

/-- The eta plus sum is exactly the prime series plus its remainder.
Helfgott page 50 proof of Theorem 6.3, before the weighted triangle step. -/
theorem plusSeries_split (x α : ℝ) :
    LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α x =
      primeSeries x α + remainderSeries x α := by
  unfold remainderSeries
  abel

/-- The Fourier integrand norm equals its weighted second moment.
Helfgott page 69 equation 7.49, using the unit norm of the opposite phase. -/
theorem norm_integrand_weighted (N : ℕ) (α : ℝ) :
    ‖Task420.helfgottIntegrand N α‖ =
      starNorm (LeanLab.Helfgott2013.xOf N) α *
        ‖LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α
          (LeanLab.Helfgott2013.xOf N)‖ ^ 2 := by
  unfold Task420.helfgottIntegrand starNorm
  rw [norm_mul, norm_mul, norm_pow]
  have he : ‖LeanLab.HelfgottArcs.e (-(N : ℝ) * α)‖ = 1 := by
    change ‖LeanLab.Ternary.MMS.e (-(N : ℝ) * α)‖ = 1
    exact LeanLab.Ternary.MMS.norm_e _
  rw [he, mul_one, mul_comm]

/-- LEAF. The large prime weighted second moment has the repaired main budget.
Helfgott pages 51 to 54, Theorem 6.3 proof after equation 6.16, and page 69
 equation 7.48 from equations 7.30 and 7.47. Replace the f zero term by
0.071498 from the book 1501.05438 page 274 after equation 14.46.
The repaired scalar M budget is 0.77962 from Helfgott2013.repaired_M.
This leaf concerns only the large prime series and has no remainder term. -/
theorem prime_moment_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∫ α in minorDomain x, starNorm x α * ‖primeSeries x α‖ ^ 2) ≤
      (Real.sqrt (Real.pi / 2) * (0.77962 + 3.5776e-4)) *
        (x ^ 2 / LeanLab.Helfgott2013.κ) := by
  sorry

/-- LEAF. The remainder weighted second moment has the small error budget.
Helfgott pages 50 and 51, Theorem 6.3 proof and the last display on page 51,
with page 63 equations 7.26 and 7.27. This is the L infinity bound on eta star
combined with Parseval for the removed small primes and nonprime powers.
This leaf has no large prime moment or full Fourier integrand bound. -/
theorem remainder_moment_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∫ α in minorDomain x, starNorm x α * ‖remainderSeries x α‖ ^ 2) ≤
      1.0532e-11 * (x ^ 2 / LeanLab.Helfgott2013.κ) := by
  sorry

/-- The two smaller moment leaves imply the exact repaired minor norm budget.
Helfgott page 69 equation 7.48. The domain unfolds to the exact sealed arcs.
CONDITIONAL ON prime_moment_upper and remainder_moment_upper. -/
theorem minor_norm_integral_upper_decomposed (N : ℕ)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∫ α in minorDomain (LeanLab.Helfgott2013.xOf N),
      ‖Task420.helfgottIntegrand N α‖) ≤
        0.97757 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ := by
  let x := LeanLab.Helfgott2013.xOf N
  have hx : 4.9e26 ≤ x := (LeanLab.Helfgott2013.x_bounds (by
    convert hN using 1 <;> norm_num)).1
  have hx0 : 0 < x := by linarith
  let A := Real.sqrt (Real.pi / 2) * (0.77962 + 3.5776e-4)
  let B : ℝ := 1.0532e-11
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by norm_num [B]
  have hU : (∫ α in minorDomain x, starNorm x α * ‖primeSeries x α‖ ^ 2) ≤
      (Real.sqrt A) ^ 2 * (x ^ 2 / LeanLab.Helfgott2013.κ) := by
    rw [Real.sq_sqrt hA.le]
    exact prime_moment_upper x hx
  have hV : (∫ α in minorDomain x, starNorm x α * ‖remainderSeries x α‖ ^ 2) ≤
      (Real.sqrt B) ^ 2 * (x ^ 2 / LeanLab.Helfgott2013.κ) := by
    rw [Real.sq_sqrt hB.le]
    exact remainder_moment_upper x hx
  have hi := weighted_moment_integrable hx0 (plusSeries_continuous hx0)
  simp_rw [plusSeries_split] at hi
  have h := weighted_integral_add_sq (Real.sqrt_pos.mpr hA) (Real.sqrt_pos.mpr hB)
    (fun α => norm_nonneg _) hi
    (weighted_moment_integrable hx0 (primeSeries_continuous hx0))
    (weighted_moment_integrable hx0 (remainderSeries_continuous hx0)) hU hV
  simp_rw [← plusSeries_split] at h
  have hs : (Real.sqrt A + Real.sqrt B) ^ 2 ≤ 0.97757 :=
    LeanLab.Helfgott2013.repaired_minor
  have hX : 0 ≤ x ^ 2 / LeanLab.Helfgott2013.κ := by
    unfold LeanLab.Helfgott2013.κ
    positivity
  simp_rw [norm_integrand_weighted]
  calc
    _ ≤ (Real.sqrt A + Real.sqrt B) ^ 2 * (x ^ 2 / LeanLab.Helfgott2013.κ) := h
    _ ≤ 0.97757 * (x ^ 2 / LeanLab.Helfgott2013.κ) := mul_le_mul_of_nonneg_right hs hX
    _ = _ := by ring

end LeanLab.Ternary.Task573
