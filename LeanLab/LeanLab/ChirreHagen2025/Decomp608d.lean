import LeanLab.ChirreHagen2025.Decomp608b
import LeanLab.ChirreHagen2025.Decomp608c
import LeanLab.ChirreHagen2025.Decomp608e
import LeanLab.ChirreHagen2025.Decomp358f

/-!
Berndt 1972 pages 152 to 154, positive Laurent coefficients at a equal to one.
The analytic leaves are explicit. The degree-one Bernoulli exception is separate.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp608d
open MeasureTheory Set Decomp272a Decomp608b Decomp608c

/-- Berndt 1972 page 153, the shifted function f at x minus one when a equals one. -/
noncomputable def berndtKernel (n : ℕ) (x : ℝ) : ℝ :=
  Real.log x ^ n / (x * (n.factorial : ℝ))

/-- LEAF. Berndt 1972 page 153 display 3.1 at a equal to one.
The coefficients c_n equal the Laurent coefficients by page 152. -/
theorem leaf_laurent_integral (n : ℕ) (hn : 1 ≤ n) :
    laurentCoeff n = -((∫ x : ℝ in Ioi 1,
      periodicBernoulli n x * iteratedDeriv n (berndtKernel n) x : ℝ) : ℂ) := by
  sorry

/-- Berndt 1972 page 153 displays 3.2 and 3.3.
The absolute recurrence is Nat.stirlingFirst. The sign is minus one to j. -/
theorem leaf_log_power_derivative (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 1 ≤ x) :
    iteratedDeriv n (berndtKernel n) x =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j *
        ((Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) / j.factorial) *
        (Real.log x ^ j / x ^ (n + 1)) := by
  rw [show berndtKernel n =
    (fun y : ℝ => Real.log y ^ n / (y * (n.factorial : ℝ))) from rfl]
  exact Decomp608e.iteratedDeriv_kernel_formula n (x := x) (lt_of_lt_of_le zero_lt_one hx)

/-! ### Low harmonics at the point one quarter

Writing `t = 1/4 + v`, the first four terms of the Fourier series of the normalized Bernoulli
polynomial are `cos (2πv)`, `-sin (4πv)/2^n`, `-cos (6πv)/3^n` and `sin (8πv)/4^n`. -/

private theorem sin_low_one (t : ℝ) :
    Real.sin (2 * Real.pi * 1 * t) = Real.cos (2 * Real.pi * (t - 1 / 4)) := by
  have h : 2 * Real.pi * 1 * t = Real.pi / 2 + 2 * Real.pi * (t - 1 / 4) := by ring
  rw [h, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

private theorem sin_low_two (t : ℝ) :
    Real.sin (2 * Real.pi * 2 * t) = -Real.sin (4 * Real.pi * (t - 1 / 4)) := by
  have h : 2 * Real.pi * 2 * t = Real.pi + 4 * Real.pi * (t - 1 / 4) := by ring
  rw [h, Real.sin_add, Real.sin_pi, Real.cos_pi]
  ring

private theorem sin_low_three (t : ℝ) :
    Real.sin (2 * Real.pi * 3 * t) = -Real.cos (6 * Real.pi * (t - 1 / 4)) := by
  have h : 2 * Real.pi * 3 * t = 3 * Real.pi / 2 + 6 * Real.pi * (t - 1 / 4) := by ring
  have h2 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
  have h1 : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [h2, Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two,
      Real.cos_pi_div_two]
    ring
  have h3 : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [h2, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.sin_pi_div_two,
      Real.cos_pi_div_two]
    ring
  rw [h, Real.sin_add, h1, h3]
  ring

private theorem sin_low_four (t : ℝ) :
    Real.sin (2 * Real.pi * 4 * t) = Real.sin (8 * Real.pi * (t - 1 / 4)) := by
  have h : 2 * Real.pi * 4 * t = 2 * Real.pi + 8 * Real.pi * (t - 1 / 4) := by ring
  rw [h, Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]
  ring

/-- The quadratic lower bound for `1 - cos` used at odd degrees, coarse version. -/
private theorem sin_sq_lower_coarse (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) :
    15.5 * a ^ 2 ≤ 2 * Real.sin (Real.pi * a) ^ 2 := by
  have hp := Real.pi_gt_d6
  have hp2 : Real.pi ^ 2 ≤ 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have ha2 : a ^ 2 ≤ 1 / 16 := by nlinarith
  have hpnn : 0 ≤ Real.pi ^ 2 := by positivity
  have ha2nn : 0 ≤ a ^ 2 := by positivity
  have hsq : (Real.pi * a) ^ 2 ≤ 0.617 := by
    rw [mul_pow]
    calc Real.pi ^ 2 * a ^ 2 ≤ 9.87 * (1 / 16) :=
          mul_le_mul hp2 ha2 ha2nn (by norm_num)
      _ ≤ 0.617 := by norm_num
  have hpa : 0 ≤ Real.pi * a := by positivity
  have hs := Real.sin_ge_sub_cube (x := Real.pi * a) hpa
  have hstep : (Real.pi * a) ^ 3 / 6 ≤ 0.104 * (Real.pi * a) := by
    have h1 : (Real.pi * a) ^ 2 / 6 ≤ 0.104 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hpa
    calc (Real.pi * a) ^ 3 / 6 = (Real.pi * a) * ((Real.pi * a) ^ 2 / 6) := by ring
      _ ≤ (Real.pi * a) * 0.104 := h2
      _ = 0.104 * (Real.pi * a) := by ring
  have hlin : 0.896 * (Real.pi * a) ≤ Real.sin (Real.pi * a) := by linarith
  have hnn : 0 ≤ 0.896 * (Real.pi * a) := by positivity
  have hsq2 : (0.896 * (Real.pi * a)) ^ 2 ≤ Real.sin (Real.pi * a) ^ 2 :=
    pow_le_pow_left₀ hnn hlin 2
  have hkey : 15.5 * a ^ 2 ≤ 2 * (0.896 * (Real.pi * a)) ^ 2 := by
    have hpi2 : 9.8696 ≤ Real.pi ^ 2 := by nlinarith
    calc 15.5 * a ^ 2 ≤ 2 * 0.896 ^ 2 * 9.8696 * a ^ 2 := by nlinarith
      _ ≤ 2 * 0.896 ^ 2 * Real.pi ^ 2 * a ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ ha2nn
          nlinarith
      _ = 2 * (0.896 * (Real.pi * a)) ^ 2 := by ring
  linarith

/-- The quadratic lower bound for `1 - cos` used at odd degrees, sharp near zero. -/
private theorem sin_sq_lower_fine (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 32) :
    19 * a ^ 2 ≤ 2 * Real.sin (Real.pi * a) ^ 2 := by
  have hp := Real.pi_gt_d6
  have hp2 : Real.pi ^ 2 ≤ 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have ha2 : a ^ 2 ≤ 1 / 1024 := by nlinarith
  have hpnn : 0 ≤ Real.pi ^ 2 := by positivity
  have ha2nn : 0 ≤ a ^ 2 := by positivity
  have hsq : (Real.pi * a) ^ 2 ≤ 0.00965 := by
    rw [mul_pow]
    calc Real.pi ^ 2 * a ^ 2 ≤ 9.87 * (1 / 1024) :=
          mul_le_mul hp2 ha2 ha2nn (by norm_num)
      _ ≤ 0.00965 := by norm_num
  have hpa : 0 ≤ Real.pi * a := by positivity
  have hs := Real.sin_ge_sub_cube (x := Real.pi * a) hpa
  have hstep : (Real.pi * a) ^ 3 / 6 ≤ 0.0017 * (Real.pi * a) := by
    have h1 : (Real.pi * a) ^ 2 / 6 ≤ 0.0017 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hpa
    calc (Real.pi * a) ^ 3 / 6 = (Real.pi * a) * ((Real.pi * a) ^ 2 / 6) := by ring
      _ ≤ (Real.pi * a) * 0.0017 := h2
      _ = 0.0017 * (Real.pi * a) := by ring
  have hlin : 0.9983 * (Real.pi * a) ≤ Real.sin (Real.pi * a) := by linarith
  have hnn : 0 ≤ 0.9983 * (Real.pi * a) := by positivity
  have hsq2 : (0.9983 * (Real.pi * a)) ^ 2 ≤ Real.sin (Real.pi * a) ^ 2 :=
    pow_le_pow_left₀ hnn hlin 2
  have hkey : 19 * a ^ 2 ≤ 2 * (0.9983 * (Real.pi * a)) ^ 2 := by
    have hpi2 : 9.8696 ≤ Real.pi ^ 2 := by nlinarith
    calc 19 * a ^ 2 ≤ 2 * 0.9983 ^ 2 * 9.8696 * a ^ 2 := by nlinarith
      _ ≤ 2 * 0.9983 ^ 2 * Real.pi ^ 2 * a ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ ha2nn
          nlinarith
      _ = 2 * (0.9983 * (Real.pi * a)) ^ 2 := by ring
  linarith

/-- Step one of the tail estimate: a one-step telescoping majorant for `1/m^5`. -/
private lemma one_div_pow_five_le_telescope (j : ℕ) :
    (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ 5 ≤
      (1 / 4) * ((1 : ℝ) / ((j + 4 : ℕ) : ℝ) ^ 4 - 1 / ((j + 5 : ℕ) : ℝ) ^ 4) := by
  set m : ℝ := ((j + 5 : ℕ) : ℝ) with hm
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hm2 : (2 : ℝ) ≤ m := by rw [hm]; push_cast; linarith
  have hc : ((j + 4 : ℕ) : ℝ) = m - 1 := by rw [hm]; push_cast; ring
  have h1 : (0 : ℝ) < m - 1 := by linarith
  have h2 : (0 : ℝ) < m := by linarith
  have hden : (0 : ℝ) < 4 * (m - 1) ^ 4 * m ^ 5 := by positivity
  have key : (1 / 4 : ℝ) * (1 / ((j + 4 : ℕ) : ℝ) ^ 4 - 1 / ((j + 5 : ℕ) : ℝ) ^ 4) -
      (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ 5 =
      (10 * m ^ 3 - 20 * m ^ 2 + 15 * m - 4) / (4 * (m - 1) ^ 4 * m ^ 5) := by
    rw [hc, ← hm]
    field_simp
    ring
  have hnum : (0 : ℝ) ≤ 10 * m ^ 3 - 20 * m ^ 2 + 15 * m - 4 := by
    have hfac : 10 * m ^ 3 - 20 * m ^ 2 + 15 * m - 4 =
        10 * m ^ 2 * (m - 2) + (15 * m - 4) := by ring
    rw [hfac]
    have : (0 : ℝ) ≤ 10 * m ^ 2 * (m - 2) := by
      have := mul_nonneg (sq_nonneg m) (by linarith : (0:ℝ) ≤ m - 2)
      linarith
    linarith
  rw [← sub_nonneg, key]
  exact div_nonneg hnum hden.le

/-- Step two: the telescoped partial sums. -/
private lemma telescope_sum_range (J : ℕ) :
    ∑ j ∈ Finset.range J,
        ((1 : ℝ) / ((j + 4 : ℕ) : ℝ) ^ 4 - 1 / ((j + 5 : ℕ) : ℝ) ^ 4) =
      1 / 4 ^ 4 - 1 / ((J + 4 : ℕ) : ℝ) ^ 4 := by
  induction J with
  | zero => norm_num
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The terms beyond the fifth one, with the uniform geometric decay of the bound. -/
private lemma tail_bound (n : ℕ) (hn : 5 ≤ n) :
    (∑' j : ℕ, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n) ≤ 0.001 / (5 : ℝ) ^ (n - 5) := by
  open Filter in
  have hterm : ∀ j : ℕ,
      (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n ≤
        (1 / (5 : ℝ) ^ (n - 5)) * (1 / ((j + 5 : ℕ) : ℝ) ^ 5) := by
    intro j
    set m : ℝ := ((j + 5 : ℕ) : ℝ) with hm
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hm5 : (5 : ℝ) ≤ m := by rw [hm]; push_cast; linarith
    have hm0 : (0 : ℝ) < m := by linarith
    have hpow : m ^ n = m ^ 5 * m ^ (n - 5) := by
      have h : n = 5 + (n - 5) := by omega
      conv_lhs => rw [h]
      rw [pow_add]
    have hmn : 0 < m ^ (n - 5) := pow_pos hm0 _
    have h2 : (1 : ℝ) / m ^ (n - 5) ≤ 1 / (5 : ℝ) ^ (n - 5) := by
      apply one_div_le_one_div_of_le (pow_pos (by norm_num : (0:ℝ) < 5) _)
      exact pow_le_pow_left₀ (by norm_num) hm5 _
    have h3 : (1 : ℝ) / (5 : ℝ) ^ (n - 5) = 1 / (5 : ℝ) ^ (n - 5) := rfl
    calc (1 : ℝ) / m ^ n = (1 / m ^ 5) * (1 / m ^ (n - 5)) := by
          rw [hpow]; field_simp
      _ ≤ (1 / m ^ 5) * (1 / (5 : ℝ) ^ (n - 5)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 / (5 : ℝ) ^ (n - 5)) * (1 / m ^ 5) := by rw [h3]; ring
  have hsummable : Summable (fun j : ℕ => (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n) := by
    have h := (Real.summable_one_div_nat_pow (p := n)).mpr (by omega)
    exact h.comp_injective (fun a b hab => by simpa using hab)
  have hpartial : ∀ J : ℕ,
      ∑ j ∈ Finset.range J, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n ≤
        0.001 / (5 : ℝ) ^ (n - 5) := by
    intro J
    have h1 : ∑ j ∈ Finset.range J, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n ≤
        (1 / (5 : ℝ) ^ (n - 5)) * ∑ j ∈ Finset.range J,
          (1 / ((j + 5 : ℕ) : ℝ) ^ 5) := by
      calc ∑ j ∈ Finset.range J, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n
          ≤ ∑ j ∈ Finset.range J,
              (1 / (5 : ℝ) ^ (n - 5)) * (1 / ((j + 5 : ℕ) : ℝ) ^ 5) :=
            Finset.sum_le_sum (fun j _ => hterm j)
        _ = (1 / (5 : ℝ) ^ (n - 5)) * ∑ j ∈ Finset.range J,
              (1 / ((j + 5 : ℕ) : ℝ) ^ 5) := (Finset.mul_sum _ _ _).symm
    have h2 : ∑ j ∈ Finset.range J, (1 / ((j + 5 : ℕ) : ℝ) ^ 5) ≤
        (1 / 4) * (1 / 4 ^ 4 - 1 / ((J + 4 : ℕ) : ℝ) ^ 4) := by
      rw [← telescope_sum_range J, Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => one_div_pow_five_le_telescope j)
    have h3 : (0 : ℝ) ≤ 1 / (5 : ℝ) ^ (n - 5) := by positivity
    have h4 : (1 / 4 : ℝ) * (1 / 4 ^ 4 - 1 / ((J + 4 : ℕ) : ℝ) ^ 4) ≤ 1 / 1024 := by
      have hpos : (0 : ℝ) ≤ 1 / ((J + 4 : ℕ) : ℝ) ^ 4 := by positivity
      have heq : (1 / 4 : ℝ) * (1 / 4 ^ 4) = 1 / 1024 := by norm_num
      nlinarith
    calc ∑ j ∈ Finset.range J, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n
        ≤ (1 / (5 : ℝ) ^ (n - 5)) * ((1 / 4) * (1 / 4 ^ 4 - 1 / ((J + 4 : ℕ) : ℝ) ^ 4)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 h3)
      _ ≤ (1 / (5 : ℝ) ^ (n - 5)) * (1 / 1024) := mul_le_mul_of_nonneg_left h4 h3
      _ ≤ 0.001 / (5 : ℝ) ^ (n - 5) := by
          have h5p : (0 : ℝ) < (5 : ℝ) ^ (n - 5) := pow_pos (by norm_num) _
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) h5p]
          nlinarith
  have htend : Tendsto (fun J : ℕ => ∑ j ∈ Finset.range J,
      (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n) atTop
        (nhds (∑' j : ℕ, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n)) :=
    hsummable.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto htend tendsto_const_nhds (Eventually.of_forall hpartial)

/-- The quadratic lower bound for a cosine, from `1 - t^2/2 ≤ cos t`. -/
private theorem cos_lower_quadratic (v : ℝ) :
    1 - 178 * v ^ 2 ≤ Real.cos (6 * Real.pi * v) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := 6 * Real.pi * v)
  have hp : Real.pi ^ 2 ≤ 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  have hsq : (6 * Real.pi * v) ^ 2 / 2 ≤ 178 * v ^ 2 := by
    have he : (6 * Real.pi * v) ^ 2 / 2 = 18 * Real.pi ^ 2 * v ^ 2 := by ring
    rw [he]
    nlinarith
  linarith

/-- The squared sine only sees the absolute value. -/
private theorem sin_sq_abs (v : ℝ) :
    2 * Real.sin (Real.pi * v) ^ 2 = 2 * Real.sin (Real.pi * |v|) ^ 2 := by
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
  · rw [abs_of_nonpos hv]
    rw [show Real.pi * -v = -(Real.pi * v) by ring, Real.sin_neg]
    ring

/-- The size of the two even harmonics kept explicitly. -/
private theorem even_harmonic_coefficient (n : ℕ) (hn : 5 ≤ n) :
    4 * Real.pi / (2 : ℝ) ^ n + 8 * Real.pi / (4 : ℝ) ^ n ≤ 13.39 / (2 : ℝ) ^ n := by
  have hp := Real.pi_lt_d2
  have h2n : (2 : ℝ) ^ 5 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h2ge : (32 : ℝ) ≤ (2 : ℝ) ^ n := by
    have h : ((2:ℝ)) ^ 5 = 32 := by norm_num
    rw [← h]; exact h2n
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h4e : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show (4:ℝ) = 2 * 2 by norm_num, mul_pow]
  have hfac : 4 * Real.pi / (2 : ℝ) ^ n + 8 * Real.pi / (4 : ℝ) ^ n =
      (4 * Real.pi / (2 : ℝ) ^ n) * (1 + 2 / (2 : ℝ) ^ n) := by
    rw [h4e]
    field_simp
    ring
  rw [hfac]
  have hstep1 : 2 / (2 : ℝ) ^ n ≤ 1 / 16 := by
    rw [div_le_iff₀ h2pos]
    nlinarith
  have hstep2 : (4 * Real.pi / (2 : ℝ) ^ n) * (1 + 2 / (2 : ℝ) ^ n) ≤
      (4 * Real.pi / (2 : ℝ) ^ n) * (1 + 1 / 16) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hstep3 : (4 * Real.pi / (2 : ℝ) ^ n) * (1 + 1 / 16) ≤ 13.39 / (2 : ℝ) ^ n := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ h2pos.le
    nlinarith
  linarith

/-- `1/4^n` as a multiple of `1/3^n`. -/
private theorem inv_four_pow_eq (n : ℕ) :
    (1 : ℝ) / (4 : ℝ) ^ n = ((3 : ℝ) / 4) ^ n * (1 / (3 : ℝ) ^ n) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  rw [div_pow]
  field_simp

/-- `1/5^(n-5)` as a multiple of `1/3^n`. -/
private theorem inv_five_pow_eq (n : ℕ) (hn : 5 ≤ n) :
    0.001 / (5 : ℝ) ^ (n - 5) =
      0.001 * ((5 : ℝ) ^ 5 * ((3 : ℝ) / 5) ^ n * (1 / (3 : ℝ) ^ n)) := by
  have h5 : (0 : ℝ) < (5 : ℝ) ^ n := by positivity
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hsplit : (5 : ℝ) ^ n = (5 : ℝ) ^ (n - 5) * (5 : ℝ) ^ 5 := by
    conv_lhs => rw [show n = (n - 5) + 5 by omega]
    rw [pow_add]
  rw [div_pow, hsplit]
  field_simp

/-- The numeric core of the sharp region estimate. -/
private theorem sharp_region_numeric (n : ℕ) (hn : 5 ≤ n) :
    (13.39 / (2 : ℝ) ^ n) ^ 2 / 73.04 + 0.001 / (5 : ℝ) ^ (n - 5) ≤ 1 / (3 : ℝ) ^ n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h34 : ((3 : ℝ) / 4) ^ n ≤ ((3 : ℝ) / 4) ^ 5 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h35 : ((3 : ℝ) / 5) ^ n ≤ ((3 : ℝ) / 5) ^ 5 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h4e : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hsq : (13.39 / (2 : ℝ) ^ n) ^ 2 / 73.04 = 179.2921 / 73.04 * (1 / (4 : ℝ) ^ n) := by
    rw [h4e]
    field_simp
    ring
  rw [hsq, inv_four_pow_eq n, inv_five_pow_eq n hn]
  have key : 179.2921 / 73.04 * ((3 : ℝ) / 4) ^ n +
      0.001 * ((5 : ℝ) ^ 5 * ((3 : ℝ) / 5) ^ n) ≤ 1 := by
    nlinarith [h34, h35]
  have hform : 179.2921 / 73.04 * (((3 : ℝ) / 4) ^ n * (1 / (3 : ℝ) ^ n)) +
      0.001 * ((5 : ℝ) ^ 5 * ((3 : ℝ) / 5) ^ n * (1 / (3 : ℝ) ^ n)) =
      (1 / (3 : ℝ) ^ n) * (179.2921 / 73.04 * ((3 : ℝ) / 4) ^ n +
        0.001 * ((5 : ℝ) ^ 5 * ((3 : ℝ) / 5) ^ n)) := by
    field_simp
  rw [hform]
  exact mul_le_of_le_one_right (by positivity) key

/-- The sharp region `a ≤ 1/32`: the cosine term pays for the tail. -/
private theorem region_sharp (n : ℕ) (hn : 5 ≤ n) (a C : ℝ)
    (hC : C ≤ 13.39 / (2 : ℝ) ^ n) (hCn : 0 ≤ C) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 32) :
    C * a + 0.001 / (5 : ℝ) ^ (n - 5) ≤
      2 * Real.sin (Real.pi * a) ^ 2 + (1 - 178 * a ^ 2) / (3 : ℝ) ^ n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h3ge : (243 : ℝ) ≤ (3 : ℝ) ^ n := by
    have h : (3 : ℝ) ^ 5 ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    have h2 : (3 : ℝ) ^ 5 = 243 := by norm_num
    linarith [h2 ▸ h]
  have hsq : 2 * Real.sin (Real.pi * a) ^ 2 ≥ 19 * a ^ 2 := sin_sq_lower_fine a ha0 ha
  have hfrac : 178 * a ^ 2 / (3 : ℝ) ^ n ≤ 0.74 * a ^ 2 := by
    rw [div_le_iff₀ h3]
    nlinarith [sq_nonneg a]
  have hkey : C * a - 18.26 * a ^ 2 ≤ 1 / (3 : ℝ) ^ n - 0.001 / (5 : ℝ) ^ (n - 5) := by
    have hmain : C ^ 2 / 73.04 ≤ 1 / (3 : ℝ) ^ n - 0.001 / (5 : ℝ) ^ (n - 5) := by
      have h1 : C ^ 2 ≤ (13.39 / (2 : ℝ) ^ n) ^ 2 := pow_le_pow_left₀ hCn hC 2
      have h2 : C ^ 2 / 73.04 ≤ (13.39 / (2 : ℝ) ^ n) ^ 2 / 73.04 :=
        div_le_div_of_nonneg_right h1 (by norm_num)
      have h3' := sharp_region_numeric n hn
      linarith
    have h4 : C * a - 18.26 * a ^ 2 ≤ C ^ 2 / 73.04 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith [sq_nonneg (C - 36.52 * a)]
    nlinarith [sq_nonneg a]
  have hgoal : (1 - 178 * a ^ 2) / (3 : ℝ) ^ n = 1 / (3 : ℝ) ^ n - 178 * a ^ 2 / (3 : ℝ) ^ n := by
    rw [← sub_div]
  rw [hgoal]
  linarith

/-- The coarse region `1/32 ≤ a`: no use of the cosine sign. -/
private theorem region_coarse (n : ℕ) (hn : 5 ≤ n) (a C : ℝ)
    (hC : C ≤ 13.39 / (2 : ℝ) ^ n) (hCn : 0 ≤ C) (ha : 1 / 32 ≤ a) (ha4 : a ≤ 1 / 4) :
    C * a + 0.001 / (5 : ℝ) ^ (n - 5) ≤
      2 * Real.sin (Real.pi * a) ^ 2 + (1 - 178 * a ^ 2) / (3 : ℝ) ^ n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have ha0 : 0 ≤ a := by linarith
  have h2ge : (32 : ℝ) ≤ (2 : ℝ) ^ n := by
    have h' : (2 : ℝ) ^ 5 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    have h2 : (2 : ℝ) ^ 5 = 32 := by norm_num
    linarith [h2 ▸ h']
  have h3ge : (243 : ℝ) ≤ (3 : ℝ) ^ n := by
    have h' : (3 : ℝ) ^ 5 ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    have h2 : (3 : ℝ) ^ 5 = 243 := by norm_num
    linarith [h2 ▸ h']
  have hsq : 2 * Real.sin (Real.pi * a) ^ 2 ≥ 15.5 * a ^ 2 := sin_sq_lower_coarse a ha0 ha4
  have hfrac : 178 * a ^ 2 / (3 : ℝ) ^ n ≤ 0.74 * a ^ 2 := by
    rw [div_le_iff₀ h3]
    nlinarith [sq_nonneg a]
  have hC32 : C ≤ 13.39 / 32 := by
    have h1 : 13.39 / (2 : ℝ) ^ n ≤ 13.39 / 32 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2ge
    linarith
  have hmono : 14.76 * (1 / 32) ^ 2 - C * (1 / 32) ≤ 14.76 * a ^ 2 - C * a := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1 / 32)
      (by linarith : (0 : ℝ) ≤ 14.76 * (a + 1 / 32) - C)]
  have htau : 0.001 / (5 : ℝ) ^ (n - 5) ≤ 0.001 := by
    rw [div_le_iff₀ (by positivity)]
    have h5 : (1 : ℝ) ≤ (5 : ℝ) ^ (n - 5) := one_le_pow₀ (by norm_num)
    nlinarith
  have hval : (14.76 : ℝ) * (1 / 32) ^ 2 = 14.76 / 1024 := by norm_num
  have hCs : C / 32 ≤ 13.39 / 1024 := by
    have h1 : C / 32 ≤ 13.39 / 32 / 32 := div_le_div_of_nonneg_right hC32 (by norm_num)
    have h2 : (13.39 : ℝ) / 32 / 32 = 13.39 / 1024 := by norm_num
    linarith [h2 ▸ h1]
  have hpos3 : (0 : ℝ) < 1 / (3 : ℝ) ^ n := by positivity
  have hfracgoal : (1 - 178 * a ^ 2) / (3 : ℝ) ^ n = 1 / (3 : ℝ) ^ n - 178 * a ^ 2 / (3 : ℝ) ^ n := by
    rw [← sub_div]
  rw [hfracgoal]
  nlinarith [hsq, hfrac, hmono, htau, hCs, hval]

set_option maxHeartbeats 2000000 in
/-- The sine series of Berndt display 3.7 is bounded by one at odd degrees. -/
private theorem abs_tsum_sin_le_one (n : ℕ) (hn : 5 ≤ n) (ho : Odd n)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    |∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ n * Real.sin (2 * Real.pi * m * t)| ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ho
  have hk : k ≠ 0 := by omega
  set v : ℝ := t - 1 / 4 with hv
  set a : ℝ := |v| with ha
  have hav : a ≤ 1 / 4 := by
    rw [ha, abs_le]
    constructor <;> rw [hv] <;> linarith
  have ha0 : 0 ≤ a := by rw [ha]; exact abs_nonneg v
  set C : ℝ := 4 * Real.pi / (2 : ℝ) ^ (2 * k + 1) + 8 * Real.pi / (4 : ℝ) ^ (2 * k + 1)
    with hCdef
  have hCn : 0 ≤ C := by rw [hCdef]; positivity
  have hCbound : C ≤ 13.39 / (2 : ℝ) ^ (2 * k + 1) := by
    rw [hCdef]; exact even_harmonic_coefficient (2 * k + 1) (by omega)
  set F : ℕ → ℝ := fun m => (1 : ℝ) / (m : ℝ) ^ (2 * k + 1) * Real.sin (2 * Real.pi * m * t)
    with hF
  have hFsummable : Summable F := by
    have hbase : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (2 * k + 1)) :=
      (Real.summable_one_div_nat_pow (p := 2 * k + 1)).mpr (by omega)
    refine Summable.of_norm_bounded hbase (fun m => ?_)
    rw [hF, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ) ^ (2 * k + 1))]
    have hs : |Real.sin (2 * Real.pi * m * t)| ≤ 1 := Real.abs_sin_le_one _
    have hnn : (0 : ℝ) ≤ 1 / (m : ℝ) ^ (2 * k + 1) := by positivity
    nlinarith
  have hsplit := hFsummable.sum_add_tsum_nat_add 5
  -- the first five terms
  have hF0 : F 0 = 0 := by simp [hF]
  have hF1 : F 1 = Real.cos (2 * Real.pi * v) := by
    simp only [hF, Nat.cast_one, one_pow, div_one, one_mul, sin_low_one, hv]
  have hF2 : F 2 = -(1 / (2 : ℝ) ^ (2 * k + 1)) * Real.sin (4 * Real.pi * v) := by
    simp only [hF, Nat.cast_ofNat, sin_low_two]
    ring
  have hF3 : F 3 = -(1 / (3 : ℝ) ^ (2 * k + 1)) * Real.cos (6 * Real.pi * v) := by
    simp only [hF, Nat.cast_ofNat, sin_low_three]
    ring
  have hF4 : F 4 = (1 / (4 : ℝ) ^ (2 * k + 1)) * Real.sin (8 * Real.pi * v) := by
    simp only [hF, Nat.cast_ofNat, sin_low_four]
    ring
  have hterms : ∑ m ∈ Finset.range 5, F m =
      Real.cos (2 * Real.pi * v) - (1 / (2 : ℝ) ^ (2 * k + 1)) * Real.sin (4 * Real.pi * v)
        - (1 / (3 : ℝ) ^ (2 * k + 1)) * Real.cos (6 * Real.pi * v)
        + (1 / (4 : ℝ) ^ (2 * k + 1)) * Real.sin (8 * Real.pi * v) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      hF0, hF1, hF2, hF3, hF4]
    ring
  -- the tail
  have htail : |∑' i : ℕ, F (i + 5)| ≤ 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) := by
    have hsum_abs : Summable (fun i : ℕ => ‖F (i + 5)‖) := by
      have hbase : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (2 * k + 1)) :=
        (Real.summable_one_div_nat_pow (p := 2 * k + 1)).mpr (by omega)
      have hcomp : Summable (fun i : ℕ => (1 : ℝ) / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) :=
        hbase.comp_injective (fun x y hxy => by simpa using hxy)
      refine Summable.of_norm_bounded hcomp (fun i => ?_)
      have hval : ‖F (i + 5)‖ = (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
          |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)| := by
        simp only [hF, Real.norm_eq_abs, abs_mul]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1))]
      rw [hval, Real.norm_of_nonneg (by positivity :
        (0 : ℝ) ≤ (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
          |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)|)]
      have hs : |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)| ≤ 1 := Real.abs_sin_le_one _
      have hnn : (0 : ℝ) ≤ 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1) := by positivity
      calc (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
            |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)|
          ≤ (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) * 1 := mul_le_mul_of_nonneg_left hs hnn
        _ = 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1) := mul_one _
    have hcompS : Summable (fun i : ℕ => (1 : ℝ) / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) := by
      have hbase : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (2 * k + 1)) :=
        (Real.summable_one_div_nat_pow (p := 2 * k + 1)).mpr (by omega)
      exact hbase.comp_injective (fun x y hxy => by simpa using hxy)
    calc |∑' i : ℕ, F (i + 5)|
        ≤ ∑' i : ℕ, ‖F (i + 5)‖ := norm_tsum_le_tsum_norm hsum_abs
      _ ≤ ∑' i : ℕ, (1 : ℝ) / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1) := by
          apply Summable.tsum_le_tsum _ hsum_abs hcompS
          intro i
          have hval : ‖F (i + 5)‖ = (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
              |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)| := by
            simp only [hF, Real.norm_eq_abs, abs_mul]
            rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1))]
          rw [hval]
          try rw [Real.norm_of_nonneg (by positivity :
            (0 : ℝ) ≤ (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
              |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)|)]
          have hs : |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)| ≤ 1 := Real.abs_sin_le_one _
          have hnn : (0 : ℝ) ≤ 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1) := by positivity
          calc (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
                |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)|
              ≤ (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) * 1 := mul_le_mul_of_nonneg_left hs hnn
            _ = 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1) := mul_one _
      _ ≤ 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) := tail_bound (2 * k + 1) (by omega)
  -- elementary bounds on the individual harmonics
  have hsin4 : |Real.sin (4 * Real.pi * v)| ≤ 4 * Real.pi * a := by
    rw [ha]
    calc |Real.sin (4 * Real.pi * v)| ≤ |4 * Real.pi * v| := Real.abs_sin_le_abs
      _ = 4 * Real.pi * |v| := by
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
          norm_num
  have hsin8 : |Real.sin (8 * Real.pi * v)| ≤ 8 * Real.pi * a := by
    rw [ha]
    calc |Real.sin (8 * Real.pi * v)| ≤ |8 * Real.pi * v| := Real.abs_sin_le_abs
      _ = 8 * Real.pi * |v| := by
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
          norm_num
  have hcos_eq : Real.cos (2 * Real.pi * v) = 1 - 2 * Real.sin (Real.pi * a) ^ 2 := by
    have hs := Real.sin_sq_eq_half_sub (Real.pi * v)
    have harg : 2 * (Real.pi * v) = 2 * Real.pi * v := by ring
    rw [harg] at hs
    have hsabs : 2 * Real.sin (Real.pi * v) ^ 2 = 2 * Real.sin (Real.pi * a) ^ 2 := by
      rw [ha]; exact sin_sq_abs v
    linarith
  have hcos_nonneg : 0 ≤ Real.cos (2 * Real.pi * v) := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · nlinarith [abs_le.mp hav, Real.pi_pos]
    · nlinarith [abs_le.mp hav, Real.pi_pos]
  -- upper bound for the first five terms
  have hupper : ∑ m ∈ Finset.range 5, F m ≤ 1 - 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) := by
    rw [hterms, hcos_eq]
    have h2 : -(1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v)) ≤
        (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) := by
      have hs : -Real.sin (4 * Real.pi * v) ≤ 4 * Real.pi * a := by
        linarith [neg_abs_le (Real.sin (4 * Real.pi * v)), hsin4]
      calc -(1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v))
          = (1 / (2 : ℝ) ^ (2 * k + 1)) * (-Real.sin (4 * Real.pi * v)) := by ring
        _ ≤ (1 / (2 : ℝ) ^ (2 * k + 1)) * (4 * Real.pi * a) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) := by ring
    have h3 : -(1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v)) ≤
        -((1 - 178 * a ^ 2) / (3 : ℝ) ^ (2 * k + 1)) := by
      have hp : (0 : ℝ) < (3 : ℝ) ^ (2 * k + 1) := by positivity
      have hle : (1 - 178 * a ^ 2) / (3 : ℝ) ^ (2 * k + 1) ≤
          Real.cos (6 * Real.pi * v) / (3 : ℝ) ^ (2 * k + 1) := by
        rw [div_le_div_iff_of_pos_right hp]
        have hc := cos_lower_quadratic v
        have h2' : (1 : ℝ) - 178 * a ^ 2 = 1 - 178 * v ^ 2 := by rw [ha, sq_abs]
        rw [h2']
        exact hc
      have hstep : -(1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v)) =
          -(Real.cos (6 * Real.pi * v) / (3 : ℝ) ^ (2 * k + 1)) := by ring
      rw [hstep]
      exact neg_le_neg hle
    have h4 : 1 / (4 : ℝ) ^ (2 * k + 1) * Real.sin (8 * Real.pi * v) ≤
        (8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1) := by
      have hs : Real.sin (8 * Real.pi * v) ≤ 8 * Real.pi * a := le_trans (le_abs_self _) hsin8
      calc 1 / (4 : ℝ) ^ (2 * k + 1) * Real.sin (8 * Real.pi * v)
          ≤ (1 / (4 : ℝ) ^ (2 * k + 1)) * (8 * Real.pi * a) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = (8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1) := by ring
    have hcomb : C * a = (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) +
        (8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1) := by
      rw [hCdef]; field_simp
    have hreg : C * a + 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) ≤
        2 * Real.sin (Real.pi * a) ^ 2 + (1 - 178 * a ^ 2) / (3 : ℝ) ^ (2 * k + 1) := by
      rcases le_total a (1 / 32) with hle | hgt
      · exact region_sharp (2 * k + 1) (by omega) a C hCbound hCn ha0 hle
      · exact region_coarse (2 * k + 1) (by omega) a C hCbound hCn hgt hav
    linarith [h2, h3, h4, hcomb, hreg]
  -- lower bound for the first five terms
  have hlower : -(1 - 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5)) ≤ ∑ m ∈ Finset.range 5, F m := by
    rw [hterms]
    have h2 : -((4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1)) ≤
        -(1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v)) := by
      have hs : Real.sin (4 * Real.pi * v) ≤ 4 * Real.pi * a := le_trans (le_abs_self _) hsin4
      have hup : 1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v) ≤
          (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) := by
        calc 1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v)
            ≤ (1 / (2 : ℝ) ^ (2 * k + 1)) * (4 * Real.pi * a) :=
              mul_le_mul_of_nonneg_left hs (by positivity)
          _ = (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) := by ring
      exact neg_le_neg hup
    have h3 : -((1 : ℝ) / (3 : ℝ) ^ (2 * k + 1)) ≤
        -(1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v)) := by
      have hc : Real.cos (6 * Real.pi * v) ≤ 1 := Real.cos_le_one _
      have hup : 1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v) ≤
          (1 : ℝ) / (3 : ℝ) ^ (2 * k + 1) := by
        calc 1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v)
            ≤ (1 / (3 : ℝ) ^ (2 * k + 1)) * 1 :=
              mul_le_mul_of_nonneg_left hc (by positivity)
          _ = (1 : ℝ) / (3 : ℝ) ^ (2 * k + 1) := by ring
      exact neg_le_neg hup
    have h4 : -((8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1)) ≤
        1 / (4 : ℝ) ^ (2 * k + 1) * Real.sin (8 * Real.pi * v) := by
      have hs : -(8 * Real.pi * a) ≤ Real.sin (8 * Real.pi * v) := by
        linarith [neg_abs_le (Real.sin (8 * Real.pi * v)), hsin8]
      calc -((8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1))
          = (1 / (4 : ℝ) ^ (2 * k + 1)) * (-(8 * Real.pi * a)) := by ring
        _ ≤ (1 / (4 : ℝ) ^ (2 * k + 1)) * Real.sin (8 * Real.pi * v) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
    have hcomb : C * a = (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) +
        (8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1) := by
      rw [hCdef]; field_simp
    have hCsmall : C * a ≤ 0.12 := by
      have h1 : C ≤ 0.42 := by
        refine hCbound.trans ?_
        have hp2 : (32 : ℝ) ≤ (2 : ℝ) ^ (2 * k + 1) := by
          have h' : (2 : ℝ) ^ 5 ≤ (2 : ℝ) ^ (2 * k + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h2 : (2 : ℝ) ^ 5 = 32 := by norm_num
          linarith [h2 ▸ h']
        have h2 : 13.39 / (2 : ℝ) ^ (2 * k + 1) ≤ 13.39 / 32 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
        linarith
      nlinarith
    have hpos3 : (0 : ℝ) < 1 / (3 : ℝ) ^ (2 * k + 1) := by positivity
    have htau : 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) ≤ 0.001 := by
      rw [div_le_iff₀ (by positivity)]
      have h5 : (1 : ℝ) ≤ (5 : ℝ) ^ (2 * k + 1 - 5) := one_le_pow₀ (by norm_num)
      nlinarith
    have hA : -(4 * Real.pi * a / (2 : ℝ) ^ (2 * k + 1)) - ((1 : ℝ) / (3 : ℝ) ^ (2 * k + 1)) -
        (8 * Real.pi * a / (4 : ℝ) ^ (2 * k + 1)) ≤
        Real.cos (2 * Real.pi * v) - 1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v)
          - 1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v)
          + 1 / (4 : ℝ) ^ (2 * k + 1) * Real.sin (8 * Real.pi * v) := by
      linarith [h2, h3, h4, hcos_nonneg]
    have hB : -(0.12) - ((1 : ℝ) / 243) ≤
        -(4 * Real.pi * a / (2 : ℝ) ^ (2 * k + 1)) - ((1 : ℝ) / (3 : ℝ) ^ (2 * k + 1)) -
          (8 * Real.pi * a / (4 : ℝ) ^ (2 * k + 1)) := by
      have h1 : (1 : ℝ) / (3 : ℝ) ^ (2 * k + 1) ≤ 1 / 243 := by
        apply one_div_le_one_div_of_le (by norm_num)
        have h' : (3 : ℝ) ^ 5 ≤ (3 : ℝ) ^ (2 * k + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h2 : (3 : ℝ) ^ 5 = 243 := by norm_num
        linarith [h2 ▸ h']
      linarith [hcomb, hCsmall, h1]
    have hC'' : -(1 - 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5)) ≤ -(0.12) - ((1 : ℝ) / 243) := by
      linarith [htau]
    linarith [hA, hB, hC'']
  -- assemble
  have hAB : |∑' m : ℕ, F m| ≤ 1 := by
    rw [← hsplit]
    have h1 : |∑ m ∈ Finset.range 5, F m + ∑' i : ℕ, F (i + 5)| ≤
        |∑ m ∈ Finset.range 5, F m| + |∑' i : ℕ, F (i + 5)| := abs_add_le _ _
    have h2 : |∑ m ∈ Finset.range 5, F m| ≤ 1 - 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) := by
      rw [abs_le]
      exact ⟨hlower, hupper⟩
    linarith [h1, h2, htail]
  exact hAB

set_option maxHeartbeats 1000000 in
/-- The normalized Bernoulli bound of Berndt display 3.7 from the sine series. -/
private theorem bernoulli_odd_half (n : ℕ) (hn : 5 ≤ n) (ho : Odd n) (t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    |bernoulliFun n t / (n.factorial : ℝ)| ≤ 2 / (2 * Real.pi) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ho
  have hk : k ≠ 0 := by omega
  have hS := hasSum_one_div_nat_pow_mul_sin (k := k) hk (x := t) ⟨h0, by linarith⟩
  have hT : |∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 * k + 1) * Real.sin (2 * Real.pi * m * t)| ≤ 1 :=
    abs_tsum_sin_le_one (2 * k + 1) (by omega) ⟨k, rfl⟩ t h0 h1
  have hp : (0 : ℝ) < (2 * Real.pi) ^ (2 * k + 1) := by positivity
  have hf : (0 : ℝ) < ((2 * k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hcabs : |(-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k + 1) / 2 /
      ((2 * k + 1).factorial : ℝ)| =
      (2 * Real.pi) ^ (2 * k + 1) / (2 * ((2 * k + 1).factorial : ℝ)) := by
    have hs : |(-1 : ℝ) ^ (k + 1)| = 1 := by
      rw [abs_pow, show |(-1 : ℝ)| = 1 by norm_num, one_pow]
    rw [abs_div, abs_div, abs_mul, hs, abs_of_pos hp, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_pos hf, one_mul, div_div]
  have hB : |bernoulliFun (2 * k + 1) t| *
      |(-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k + 1) / 2 / ((2 * k + 1).factorial : ℝ)| =
      |∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 * k + 1) * Real.sin (2 * Real.pi * m * t)| := by
    rw [← abs_mul, hS.tsum_eq, mul_comm (bernoulliFun (2 * k + 1) t)]
    rfl
  rw [hcabs] at hB
  -- clear the constant
  have hkey : |bernoulliFun (2 * k + 1) t| * (2 * Real.pi) ^ (2 * k + 1) /
      ((2 * k + 1).factorial : ℝ) ≤ 2 := by
    have h1 : |bernoulliFun (2 * k + 1) t| *
        ((2 * Real.pi) ^ (2 * k + 1) / (2 * ((2 * k + 1).factorial : ℝ))) ≤ 1 := by
      rw [hB]; exact hT
    calc |bernoulliFun (2 * k + 1) t| * (2 * Real.pi) ^ (2 * k + 1) /
          ((2 * k + 1).factorial : ℝ) =
        2 * (|bernoulliFun (2 * k + 1) t| *
          ((2 * Real.pi) ^ (2 * k + 1) / (2 * ((2 * k + 1).factorial : ℝ)))) := by
          field_simp
      _ ≤ 2 * 1 := by linarith
      _ = 2 := by ring
  rw [abs_div, abs_of_pos hf]
  have hgoal : |bernoulliFun (2 * k + 1) t| ≤
      (2 / (2 * Real.pi) ^ (2 * k + 1)) * ((2 * k + 1).factorial : ℝ) := by
    have hkey2 : |bernoulliFun (2 * k + 1) t| * (2 * Real.pi) ^ (2 * k + 1) ≤
        2 * ((2 * k + 1).factorial : ℝ) := (div_le_iff₀ hf).mp hkey
    have hstep : |bernoulliFun (2 * k + 1) t| ≤
        (2 * ((2 * k + 1).factorial : ℝ)) / (2 * Real.pi) ^ (2 * k + 1) :=
      (le_div_iff₀ hp).mpr hkey2
    calc |bernoulliFun (2 * k + 1) t| ≤ (2 * ((2 * k + 1).factorial : ℝ)) /
            (2 * Real.pi) ^ (2 * k + 1) := hstep
      _ = (2 / (2 * Real.pi) ^ (2 * k + 1)) * ((2 * k + 1).factorial : ℝ) := by ring
  calc |bernoulliFun (2 * k + 1) t| / ((2 * k + 1).factorial : ℝ)
      ≤ ((2 / (2 * Real.pi) ^ (2 * k + 1)) * ((2 * k + 1).factorial : ℝ)) /
          ((2 * k + 1).factorial : ℝ) := div_le_div_of_nonneg_right hgoal hf.le
    _ = 2 / (2 * Real.pi) ^ (2 * k + 1) := by
        field_simp

/-- LEAF. Berndt 1972 page 154 display 3.7, restricted to odd degrees at least three.
Berndt cites Ostrowski 1969 pages 202 to 206 for the constant two.
The degree-one exception is proved in Decomp608a. -/
theorem leaf_periodicBernoulli_odd (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) (x : ℝ) :
    |periodicBernoulli n x| ≤ 2 / (2 * Real.pi) ^ n := by
  by_cases h3 : n = 3
  · subst n
    exact periodicBernoulli_three_bound x
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ho
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact h3 rfl
    have hy0 : 0 ≤ Int.fract x := Int.fract_nonneg x
    have hy1 : Int.fract x < 1 := Int.fract_lt_one x
    have hper : periodicBernoulli (2 * k + 1) x =
        bernoulliFun (2 * k + 1) (Int.fract x) / ((2 * k + 1).factorial : ℝ) := rfl
    rw [hper]
    rcases le_total (Int.fract x) (1 / 2) with hle | hge
    · exact bernoulli_odd_half (2 * k + 1) (by omega) ⟨k, rfl⟩ _ hy0 hle
    · set y' : ℝ := 1 - Int.fract x with hy'def
      have hy0' : 0 ≤ y' := by rw [hy'def]; linarith
      have hy1' : y' ≤ 1 / 2 := by rw [hy'def]; linarith
      have hsym : bernoulliFun (2 * k + 1) (Int.fract x) = -bernoulliFun (2 * k + 1) y' := by
        have h := bernoulliFun_eval_one_sub (k := 2 * k + 1) (x := y')
        rw [show (1 : ℝ) - y' = Int.fract x by rw [hy'def]; ring] at h
        rw [h]
        have hodd : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
          rw [pow_succ, pow_mul]
          norm_num
        rw [hodd]
        ring
      rw [hsym, neg_div, abs_neg]
      exact bernoulli_odd_half (2 * k + 1) (by omega) ⟨k, rfl⟩ _ hy0' hy1'

/-- Berndt 1972 page 154 display 3.6.
The logarithmic derivative formula is supplied by the polynomial proof. -/
theorem kernel_derivative_majorant (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 1 ≤ x) :
    |iteratedDeriv n (berndtKernel n) x| ≤ logDerivativeMajorant n x := by
  rw [leaf_log_power_derivative n hn x hx]
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), |(-1 : ℝ) ^ j *
        ((Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) / j.factorial) *
        (Real.log x ^ j / x ^ (n + 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ logDerivativeMajorant n x := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      calc
        _ = ((Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) / j.factorial) *
            (Real.log x ^ j / x ^ (n + 1)) := by
          simp [abs_mul, abs_div, abs_pow, abs_of_nonneg hl,
            abs_of_nonneg (show (0 : ℝ) ≤ x by linarith)]
        _ ≤ (n.choose j : ℝ) ^ 2 * (Real.log x ^ j / x ^ (n + 1)) :=
          mul_le_mul_of_nonneg_right (Decomp608a.stirling_coefficient_le_choose_sq n j hjn)
            (by positivity)

/-- Berndt 1972 page 153, the exact first derivative of the degree-one kernel. -/
theorem kernel_one_derivative (x : ℝ) (hx : 0 < x) :
    iteratedDeriv 1 (berndtKernel 1) x = (1 - Real.log x) / x ^ 2 := by
  have heq : berndtKernel 1 = fun y : ℝ => Real.log y / y := by
    funext y
    simp [berndtKernel]
  rw [heq, iteratedDeriv_one]
  have h := ((Real.hasDerivAt_log hx.ne').div (hasDerivAt_id x) hx.ne').deriv
  change deriv (Real.log / id) x = _
  rw [h]
  simp only [id_eq, mul_one, inv_mul_cancel₀ hx.ne']

/-- Berndt 1972 page 154, integral comparison after displays 3.6 and 3.7.
CONDITIONAL ON the Laurent integral leaf. -/
theorem laurentCoeff_norm_le_of_periodic_bound (n : ℕ) (hn : 1 ≤ n)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ x : ℝ, |periodicBernoulli n x| ≤ C / (2 * Real.pi) ^ n) :
    ‖laurentCoeff n‖ ≤ C / ((n : ℝ) * Real.pi ^ n) := by
  rw [leaf_laurent_integral n hn, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hi := (logDerivativeMajorant_integrable n hn).const_mul (C / (2 * Real.pi) ^ n)
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, C / (2 * Real.pi) ^ n * logDerivativeMajorant n x := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hP x) (kernel_derivative_majorant n hn x hx.le)
        (abs_nonneg _) (div_nonneg hC (by positivity))
    _ ≤ C / ((n : ℝ) * Real.pi ^ n) := by
      rw [integral_const_mul]
      exact scaled_integral_logDerivativeMajorant_le n hn C hC

/-- Berndt 1972 page 153 display 3.1, a separate proof for degree one.
CONDITIONAL ON the Laurent integral leaf only. It avoids display 3.7 at degree one. -/
theorem laurentCoeff_one_bound : ‖laurentCoeff 1‖ ≤ (5 / 8 : ℝ) := by
  rw [leaf_laurent_integral 1 (by decide), norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have heq : (∫ x : ℝ in Ioi 1, periodicBernoulli 1 x * iteratedDeriv 1 (berndtKernel 1) x) =
      ∫ x : ℝ in Ioi 1, periodicBernoulli 1 x * ((1 - Real.log x) / x ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [kernel_one_derivative x (lt_trans zero_lt_one hx)]
  rw [heq]
  exact degree_one_remainder_bound _ (fun x _ => periodicBernoulli_one_bound x)

/-- Berndt 1972 Theorem 2, with the exact sealed target statement.
CONDITIONAL ON the Laurent integral and odd Bernoulli leaves. The constant coefficient is reused. -/
theorem laurent_coefficient_bounds :
    ‖laurentCoeff 0‖ ≤ (0.578 : ℝ) ∧
      ∀ n : ℕ, 1 ≤ n → ‖laurentCoeff n‖ ≤
        (if Even n then 4 else 2) / ((n : ℝ) * Real.pi ^ n) := by
  refine ⟨Decomp358f.laurentCoeff_zero_bound, ?_⟩
  intro n hn
  by_cases h1 : n = 1
  · subst n
    norm_num
    apply laurentCoeff_one_bound.trans
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_lt_d2]
  · by_cases he : Even n
    · rw [if_pos he]
      exact laurentCoeff_norm_le_of_periodic_bound n hn 4 (by norm_num)
        (periodicBernoulli_uniform_bound n hn)
    · rw [if_neg he]
      have ho : Odd n := (Nat.even_or_odd n).resolve_left he
      have hn3 : 3 ≤ n := by
        have h2 : n ≠ 2 := by
          rintro rfl
          norm_num at he
        omega
      exact laurentCoeff_norm_le_of_periodic_bound n hn 2 (by norm_num)
        (leaf_periodicBernoulli_odd n hn3 ho)

end LeanLab.ChirreHagen2025.Decomp608d
