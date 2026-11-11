/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 174 to 175, displays 4.11 and 4.12 and their written coefficient proof.
-/
import LeanLab.PlattTrudgian2014.LambdaBlocks
import LeanLab.PlattTrudgian2014.Mixed421
import LeanLab.PlattTrudgian2014.Cosine421
import LeanLab.PlattTrudgian2014.Decomp421e

namespace LeanLab.PlattTrudgian2014

open MeasureTheory

/-- LEAF. P0026 page 174 display 4.11.
The real exponential has an absolutely summable cosine expansion with nonnegative coefficients.
This asserts neither a correlation inequality nor supermultiplicativity. -/
theorem positive_cosine_expansion421 (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k) ∧ Summable (fun k => |a k|) ∧
      ∀ x : ℝ, Real.exp (t * (G L x).re) =
        ∑' k : ℕ, a k * Real.cos (2 * Real.pi * k * x) := by
  exact positive_cosine_expansion_decomposed421 t ht L

/-- LEAF. P0026 page 175, the constant coefficient a zero is the mean.
This is the termwise integral of an absolutely convergent cosine series. -/
theorem cosine_series_integral421 (a : ℕ → ℝ) (ha : Summable (fun k => |a k|)) :
    (∫ x : ℝ in 0..1, ∑' k : ℕ, a k * Real.cos (2 * Real.pi * k * x)) = a 0 := by
  have hb (k : ℕ) (x : ℝ) : ‖a k * Real.cos (2 * Real.pi * k * x)‖ ≤ |a k| := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
  have hs (x : ℝ) : Summable (fun k : ℕ => a k * Real.cos (2 * Real.pi * k * x)) :=
    ha.of_norm_bounded (fun k => hb k x)
  have hm : HasSum (fun k : ℕ => ∫ x : ℝ in 0..1,
      a k * Real.cos (2 * Real.pi * k * x))
      (∫ x : ℝ in 0..1, ∑' k : ℕ, a k * Real.cos (2 * Real.pi * k * x)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun k (_ : ℝ) => |a k|)
    · intro k
      exact (by fun_prop : Continuous (fun x : ℝ =>
        a k * Real.cos (2 * Real.pi * k * x))).aestronglyMeasurable
    · intro k
      exact Filter.Eventually.of_forall fun x hx => hb k x
    · exact Filter.Eventually.of_forall fun x hx => ha
    · exact continuous_const.intervalIntegrable 0 1
    · exact Filter.Eventually.of_forall fun x hx => (hs x).hasSum
  have hc (k : ℕ) : (∫ x : ℝ in 0..1, Real.cos (2 * Real.pi * k * x)) =
      if k = 0 then 1 else 0 := by
    have he (x : ℝ) : Real.cos (2 * Real.pi * k * x) = (phase (((k : ℤ) : ℝ) * x)).re := by
      unfold phase
      rw [Complex.exp_ofReal_mul_I_re]
      push_cast
      congr 1
      ring
    simp_rw [he]
    simpa only [Int.natCast_eq_zero] using phase_integer_integral421 (k : ℤ)
  rw [← hm.tsum_eq]
  simp_rw [intervalIntegral.integral_const_mul, hc]
  simp

/-- LEAF. P0026 page 175, product orthogonality calculation before display 4.12.
The dilation keeps exactly the matching positive frequencies and the constant pair.
No nonnegativity or exponential hypotheses are present. -/
theorem cosine_series_product421 (a b : ℕ → ℝ)
    (ha : Summable (fun k => |a k|)) (hb : Summable (fun k => |b k|))
    (q : ℕ) (hq : 0 < q) :
    (∫ x : ℝ in 0..1,
      (∑' k : ℕ, a k * Real.cos (2 * Real.pi * k * x)) *
        (∑' k : ℕ, b k * Real.cos (2 * Real.pi * k * ((q : ℝ) * x)))) =
      a 0 * b 0 + (1 / 2 : ℝ) * ∑' k : ℕ, a ((k + 1) * q) * b (k + 1) := by
  exact cosine_series_product_proved421 a b ha hb q hq

/-- P0026 page 175 display 4.12, exact existing real moment supermultiplicativity.
All three coefficient and orthogonality leaves above are proved. -/
theorem real_moment_supermultiplicative_decomposed421 (t : ℝ) (ht : 0 ≤ t) (m n : ℕ) :
    (∫ x : ℝ in 0..1, Real.exp (t * (G m x).re)) *
      (∫ x : ℝ in 0..1, Real.exp (t * (G n x).re)) ≤
        ∫ x : ℝ in 0..1, Real.exp (t * (G (m + n) x).re) := by
  obtain ⟨a, ha, has, hae⟩ := positive_cosine_expansion421 t ht m
  obtain ⟨b, hb, hbs, hbe⟩ := positive_cosine_expansion421 t ht n
  have hma : (∫ x : ℝ in 0..1, Real.exp (t * (G m x).re)) = a 0 := by
    simp_rw [hae]
    exact cosine_series_integral421 a has
  have hnb : (∫ x : ℝ in 0..1, Real.exp (t * (G n x).re)) = b 0 := by
    simp_rw [hbe]
    exact cosine_series_integral421 b hbs
  have hprod := cosine_series_product421 a b has hbs (2 ^ m) (by positivity)
  have he (x : ℝ) : Real.exp (t * (G (m + n) x).re) =
      Real.exp (t * (G m x).re) * Real.exp (t * (G n ((2 : ℝ) ^ m * x)).re) := by
    rw [show m + n = n + m by omega, G_add_length, Complex.add_re, mul_add, Real.exp_add]
  rw [hma, hnb]
  calc
    _ ≤ a 0 * b 0 + (1 / 2 : ℝ) * ∑' k : ℕ, a ((k + 1) * 2 ^ m) * b (k + 1) := by
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num)
        (tsum_nonneg fun k => mul_nonneg (ha _) (hb _)))
    _ = _ := by
      rw [← hprod]
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [he, hae, hbe]
      simp only [Nat.cast_pow, Nat.cast_ofNat]

set_option format.width 240
#print axioms positive_cosine_expansion421
#print axioms cosine_series_integral421
#print axioms cosine_series_product421
#print axioms real_moment_supermultiplicative_decomposed421

end LeanLab.PlattTrudgian2014
