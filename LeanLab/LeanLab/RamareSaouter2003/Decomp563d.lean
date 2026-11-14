import Mathlib

/-!
Backlund pp. 346 and 347 displays 8 through 12 and p. 368.
Use five Euler correction terms and the tenth Bernoulli remainder.
The printed two-term majorant is not used.
AI wrote the Lean code. Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp563d
open Real Complex MeasureTheory Polynomial

/-- Backlund p. 367, the same finite H sum as the sealed source file. -/
noncomputable def boundaryH (σ : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc (1 : ℕ) 9, (1 : ℂ) / (n : ℂ) ^ ((σ : ℂ) + 50 * I)) +
    1 / (2 * (10 : ℂ) ^ ((σ : ℂ) + 50 * I))

/-- Backlund p. 346 display 11, the rising factorial in the remainder. -/
noncomputable def rising (s : ℂ) (m : ℕ) : ℂ :=
  ∏ j ∈ Finset.range m, (s + j)

/-- Backlund p. 346 display 8 iterated to order ten, the unshifted periodic Bernoulli polynomial.
The symmetric variable is fract x times one minus fract x. -/
noncomputable def periodicB10 (x : ℝ) : ℝ :=
  let q := Int.fract x * (1 - Int.fract x)
  5 / 66 - (3 / 2) * q ^ 2 - 3 * q ^ 3 - (5 / 2) * q ^ 4 - q ^ 5

/-- Backlund p. 346, the higher-order kernel agrees with Mathlib's Bernoulli normalization. -/
theorem periodicB10_eq_mathlib (x : ℝ) :
    periodicB10 x = Polynomial.eval₂ (Rat.castHom ℝ) (Int.fract x) (Polynomial.bernoulli 10) := by
  have hpoly : Polynomial.bernoulli 10 =
      (Polynomial.X ^ 10 - 5 * Polynomial.X ^ 9 + Polynomial.C (15 / 2) * Polynomial.X ^ 8 -
        7 * Polynomial.X ^ 6 + 5 * Polynomial.X ^ 4 - Polynomial.C (3 / 2) * Polynomial.X ^ 2 +
        Polynomial.C (5 / 66) : ℚ[X]) := by
    have h3 : _root_.bernoulli 3 = (0 : ℚ) := by decide +kernel
    have h4 : _root_.bernoulli 4 = (-1 / 30 : ℚ) := by decide +kernel
    have h5 : _root_.bernoulli 5 = (0 : ℚ) := by decide +kernel
    have h6 : _root_.bernoulli 6 = (1 / 42 : ℚ) := by decide +kernel
    have h7 : _root_.bernoulli 7 = (0 : ℚ) := by decide +kernel
    have h8 : _root_.bernoulli 8 = (-1 / 30 : ℚ) := by decide +kernel
    have h9 : _root_.bernoulli 9 = (0 : ℚ) := by decide +kernel
    have h10 : _root_.bernoulli 10 = (5 / 66 : ℚ) := by decide +kernel
    norm_num [Polynomial.bernoulli, Finset.sum_range_succ, h3, h4, h5, h6, h7, h8, h9, h10, Nat.choose]
    simp only [← Polynomial.C_mul_X_pow_eq_monomial]
    norm_num [Polynomial.C_ofNat]
    ring
  rw [hpoly]
  norm_num [periodicB10]
  ring

/-- Backlund p. 346 display 11, the uniform tenth Bernoulli bound. -/
theorem periodicB10_bound (x : ℝ) : |periodicB10 x| ≤ (5 / 66 : ℝ) := by
  let q := Int.fract x * (1 - Int.fract x)
  have hq0 : 0 ≤ q := mul_nonneg (Int.fract_nonneg _) (by linarith [Int.fract_lt_one x])
  have hq1 : q ≤ 1 / 4 := by dsimp [q]; nlinarith [sq_nonneg (Int.fract x - 1 / 2)]
  have h2 := pow_le_pow_left₀ hq0 hq1 2
  have h3 := pow_le_pow_left₀ hq0 hq1 3
  have h4 := pow_le_pow_left₀ hq0 hq1 4
  have h5 := pow_le_pow_left₀ hq0 hq1 5
  change |5 / 66 - (3 / 2) * q ^ 2 - 3 * q ^ 3 - (5 / 2) * q ^ 4 - q ^ 5| ≤ _
  apply abs_le.mpr
  constructor
  · norm_num at h2 h3 h4 h5
    linarith
  · linarith [sq_nonneg q, pow_nonneg hq0 3, pow_nonneg hq0 4, pow_nonneg hq0 5]

/-- Backlund p. 368, the pole and all five finite Euler correction terms. -/
noncomputable def correction (s : ℂ) : ℂ :=
  (10 : ℂ) ^ (1 - s) / (s - 1) + s / (12 * (10 : ℂ) ^ (s + 1)) -
    rising s 3 / (720 * (10 : ℂ) ^ (s + 3)) +
    rising s 5 / (30240 * (10 : ℂ) ^ (s + 5)) -
    rising s 7 / (1209600 * (10 : ℂ) ^ (s + 7)) +
    rising s 9 / (47900160 * (10 : ℂ) ^ (s + 9))

/-- LEAF. Backlund p. 346 display 8 iterated to five correction terms.
This derived refinement uses the standard unshifted tenth Bernoulli
polynomial. The finite H sum is subtracted explicitly. -/
theorem euler10_identity (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    let s : ℂ := (σ : ℂ) + 50 * I
    riemannZeta s - boundaryH σ = correction s - rising s 10 / 3628800 *
      ∫ x : ℝ in Set.Ioi (10 : ℝ), (periodicB10 x : ℂ) / (x : ℂ) ^ (s + 10) := by
  sorry

/-- Backlund p. 368, uniform complex rising-factorial control. -/
theorem rising_norm_bound (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (m : ℕ) (b : ℝ) (hb : 0 ≤ b) (hmb : 2500 + (m : ℝ) ^ 2 ≤ b ^ 2) :
    ‖rising ((σ : ℂ) + 50 * I) m‖ ≤ b ^ m := by
  unfold rising
  rw [norm_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.range m, b := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      have hcast : (j : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hjm)
      have hnon : 0 ≤ σ + j := by linarith [hσ.1, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have hmax : σ + j ≤ m := by linarith [hσ.2]
      have he : (σ : ℂ) + 50 * I + j = (((σ + j : ℝ) : ℂ) + 50 * I) := by push_cast; ring
      rw [he]
      change ‖(((σ + j : ℝ) : ℂ)) + ((50 : ℝ) : ℂ) * I‖ ≤ b
      rw [Complex.norm_add_mul_I]
      apply (Real.sqrt_le_iff).mpr
      exact ⟨hb, by nlinarith⟩
    _ = b ^ m := by simp

/-- Backlund p. 368, the tenth Bernoulli integrand has an integrable real majorant. -/
theorem tenth_kernel_bound (σ x : ℝ) (hσ : 1 / 2 ≤ σ) (hx : 1 ≤ x) :
    ‖(periodicB10 x : ℂ) / (x : ℂ) ^ (((σ : ℂ) + 50 * I) + 10)‖ ≤
      (5 / 66 : ℝ) * x ^ (-(21 / 2 : ℝ)) := by
  have hxpos : 0 < x := by linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero]
  rw [div_eq_mul_inv, ← Real.rpow_neg hxpos.le]
  exact mul_le_mul (periodicB10_bound x)
    (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (Real.rpow_nonneg hxpos.le _) (by norm_num)

/-- Backlund p. 368, the exact elementary integral for the sharper remainder. -/
theorem tenth_majorant_integral :
    (∫ x : ℝ in Set.Ioi (10 : ℝ), (5 / 66 : ℝ) * x ^ (-(21 / 2 : ℝ))) =
      (5 / 66 : ℝ) / ((19 / 2) * (10 : ℝ) ^ 9 * Real.sqrt 10) := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : -(21 / 2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 10)]
  have hp : (10 : ℝ) ^ (-(21 / 2 : ℝ) + 1) = 1 / ((10 : ℝ) ^ 9 * Real.sqrt 10) := by
    rw [show -(21 / 2 : ℝ) + 1 = -(9 + 1 / 2) by norm_num, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10),
      Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
    rw [← Real.sqrt_eq_rpow]
    norm_num [one_div]
  rw [hp]
  norm_num
  ring

/-- Backlund p. 368, a rational lower bound for every complex power denominator. -/
theorem power_norm_lower (σ : ℝ) (hσ : 1 / 2 ≤ σ) (m : ℕ) :
    (79 / 25 : ℝ) * (10 : ℝ) ^ m ≤
      ‖(10 : ℂ) ^ (((σ : ℂ) + 50 * I) + m)‖ := by
  have hr : (79 / 25 : ℝ) ≤ Real.sqrt 10 := Real.le_sqrt_of_sq_le (by norm_num)
  have hp : Real.sqrt 10 ≤ (10 : ℝ) ^ σ := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ
  change _ ≤ ‖(((10 : ℝ) : ℂ)) ^ (((σ : ℂ) + 50 * I) + m)‖
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 10)]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.natCast_re]
  calc
    _ ≤ (10 : ℝ) ^ σ * (10 : ℝ) ^ m := mul_le_mul_of_nonneg_right (hr.trans hp) (by positivity)
    _ = _ := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 10), Real.rpow_natCast]

/-- Backlund p. 368, one finite Euler correction controlled by rational data. -/
theorem finite_term_bound (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (m : ℕ) (b c : ℝ) (hb : 0 ≤ b) (hc : 0 < c) (hmb : 2500 + (m : ℝ) ^ 2 ≤ b ^ 2) :
    ‖rising ((σ : ℂ) + 50 * I) m /
        ((c : ℂ) * (10 : ℂ) ^ (((σ : ℂ) + 50 * I) + m))‖ ≤
      b ^ m / (c * (79 / 25 : ℝ) * (10 : ℝ) ^ m) := by
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have hp := power_norm_lower σ hσ.1 m
  have hn := rising_norm_bound σ hσ m b hb hmb
  have hd : 0 < c * (79 / 25 : ℝ) * (10 : ℝ) ^ m := by positivity
  apply div_le_div₀ (by positivity) hn hd
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hp hc.le

/-- Backlund p. 368, cancellation between the pole term and the first Euler term. -/
theorem pole_first_bound (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖(10 : ℂ) ^ (1 - ((σ : ℂ) + 50 * I)) / (((σ : ℂ) + 50 * I) - 1) +
      ((σ : ℂ) + 50 * I) / (12 * (10 : ℂ) ^ (((σ : ℂ) + 50 * I) + 1))‖ ≤ 0.069 := by
  let s : ℂ := (σ : ℂ) + 50 * I
  have hs : s - 1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [s] at hi
  have h10 : (10 : ℂ) ≠ 0 := by norm_num
  have he : (10 : ℂ) ^ (1 - s) / (s - 1) + s / (12 * (10 : ℂ) ^ (s + 1)) =
      ((10 : ℂ) ^ s)⁻¹ * ((s * (s - 1) + 1200) / (120 * (s - 1))) := by
    rw [show 1 - s = -s + 1 by ring, Complex.cpow_add _ _ h10,
      Complex.cpow_add _ _ h10, Complex.cpow_neg, Complex.cpow_one]
    field_simp
    ring
  have hr : (s * (s - 1) + 1200).re = σ ^ 2 - σ - 1300 := by simp [s, Complex.mul_re]; ring
  have hi : (s * (s - 1) + 1200).im = 50 * (2 * σ - 1) := by simp [s, Complex.mul_im]; ring
  have hsq : -1 / 4 ≤ σ ^ 2 - σ ∧ σ ^ 2 - σ ≤ 0 := by
    constructor <;> nlinarith [hσ.1, hσ.2, sq_nonneg (σ - 1 / 2)]
  have hnum : ‖s * (s - 1) + 1200‖ ≤ (1302 : ℝ) := by
    have hre : |(s * (s - 1) + 1200).re| ≤ (1301 : ℝ) := by rw [hr]; exact abs_le.mpr ⟨by linarith [hsq.1], by linarith [hsq.2]⟩
    have him : |(s * (s - 1) + 1200).im| ≤ (50 : ℝ) := by rw [hi]; exact abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hR := sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1301) |>.mpr hre
    have hI := sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 50) |>.mpr him
    rw [sq_abs] at hR hI
    have hnorm := Complex.sq_norm (s * (s - 1) + 1200)
    rw [Complex.normSq_apply] at hnorm
    nlinarith [norm_nonneg (s * (s - 1) + 1200)]
  have hden : (50 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simpa [s] using h
  have hp := power_norm_lower σ hσ.1 0
  norm_num at hp
  change ‖(10 : ℂ) ^ (1 - s) / (s - 1) + s / (12 * (10 : ℂ) ^ (s + 1))‖ ≤ _
  rw [he, norm_mul, norm_inv, norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  have hfrac : ‖s * (s - 1) + 1200‖ / (120 * ‖s - 1‖) ≤ (1302 / 6000 : ℝ) := by
    apply div_le_div₀ (by norm_num) hnum (by norm_num : (0 : ℝ) < 6000)
    linarith
  have hinv : ‖(10 : ℂ) ^ s‖⁻¹ ≤ (25 / 79 : ℝ) := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 79 / 25) hp
    simpa only [one_div, inv_div, one_mul] using hh
  have hh := mul_le_mul hinv hfrac (by positivity) (by norm_num : (0 : ℝ) ≤ 25 / 79)
  exact hh.trans (by norm_num)

/-- Backlund p. 368, all finite correction terms fit the repaired budget. -/
theorem correction_bound (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖correction ((σ : ℂ) + 50 * I)‖ ≤ 0.196 := by
  have h0 := pole_first_bound σ hσ
  have h3 := finite_term_bound σ hσ 3 (50.1 : ℝ) 720 (by norm_num) (by norm_num) (by norm_num)
  have h5 := finite_term_bound σ hσ 5 (50.3 : ℝ) 30240 (by norm_num) (by norm_num) (by norm_num)
  have h7 := finite_term_bound σ hσ 7 (50.5 : ℝ) 1209600 (by norm_num) (by norm_num) (by norm_num)
  have h9 := finite_term_bound σ hσ 9 (50.9 : ℝ) 47900160 (by norm_num) (by norm_num) (by norm_num)
  unfold correction
  have h := (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add h0 h3)) h5)) h7)) h9)
  exact h.trans (by norm_num)

/-- Backlund p. 368, the tenth-order integral remainder fits the repaired budget. -/
theorem tenth_remainder_bound (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖rising ((σ : ℂ) + 50 * I) 10 / 3628800 *
      ∫ x : ℝ in Set.Ioi (10 : ℝ), (periodicB10 x : ℂ) /
        (x : ℂ) ^ (((σ : ℂ) + 50 * I) + 10)‖ ≤ 0.084 := by
  have hi : IntegrableOn (fun x : ℝ => (5 / 66 : ℝ) * x ^ (-(21 / 2 : ℝ))) (Set.Ioi (10 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(21 / 2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 10)).const_mul _
  have hiB := norm_integral_le_of_norm_le hi (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact tenth_kernel_bound σ x hσ.1 (by change (10 : ℝ) < x at hx; linarith))
  rw [tenth_majorant_integral] at hiB
  have hroot : (79 / 25 : ℝ) ≤ Real.sqrt 10 := Real.le_sqrt_of_sq_le (by norm_num)
  have hB : (5 / 66 : ℝ) / ((19 / 2) * (10 : ℝ) ^ 9 * Real.sqrt 10) ≤
      (5 / 66 : ℝ) / ((19 / 2) * (10 : ℝ) ^ 9 * (79 / 25)) := by gcongr
  have hprod := rising_norm_bound σ hσ 10 51 (by norm_num) (by norm_num)
  rw [norm_mul, norm_div]
  norm_num only [Complex.norm_ofNat]
  have hh := mul_le_mul (div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 3628800))
    (hiB.trans hB) (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 51 ^ 10 / 3628800)
  exact hh.trans (by norm_num)

/-- Backlund p. 368, the exact original K target with a sharper certified budget.
CONDITIONAL ON euler10_identity. The five-term and remainder budgets are proved. -/
theorem boundaryK (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖riemannZeta ((σ : ℂ) + 50 * I) - boundaryH σ‖ ≤ 0.281 := by
  rw [euler10_identity σ hσ]
  exact ((norm_sub_le _ _).trans (add_le_add (correction_bound σ hσ)
    (tenth_remainder_bound σ hσ))).trans (by norm_num)

end LeanLab.RamareSaouter2003.Decomp563d

#print axioms LeanLab.RamareSaouter2003.Decomp563d.periodicB10_bound
#print axioms LeanLab.RamareSaouter2003.Decomp563d.rising_norm_bound
#print axioms LeanLab.RamareSaouter2003.Decomp563d.tenth_kernel_bound
#print axioms LeanLab.RamareSaouter2003.Decomp563d.tenth_majorant_integral
#print axioms LeanLab.RamareSaouter2003.Decomp563d.euler10_identity

#print axioms LeanLab.RamareSaouter2003.Decomp563d.boundaryH

#print axioms LeanLab.RamareSaouter2003.Decomp563d.rising

#print axioms LeanLab.RamareSaouter2003.Decomp563d.periodicB10

#print axioms LeanLab.RamareSaouter2003.Decomp563d.correction

#print axioms LeanLab.RamareSaouter2003.Decomp563d.power_norm_lower

#print axioms LeanLab.RamareSaouter2003.Decomp563d.finite_term_bound

#print axioms LeanLab.RamareSaouter2003.Decomp563d.pole_first_bound

#print axioms LeanLab.RamareSaouter2003.Decomp563d.correction_bound

#print axioms LeanLab.RamareSaouter2003.Decomp563d.tenth_remainder_bound

#print axioms LeanLab.RamareSaouter2003.Decomp563d.boundaryK

#print axioms LeanLab.RamareSaouter2003.Decomp563d.periodicB10_eq_mathlib
