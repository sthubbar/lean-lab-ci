/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv math/0201299 page 30 display 43 with h = 2.
The explicit four branch certificate is proved without a cited numerical input.
-/
import LeanLab.PlattTrudgian2014.BlockTwoReal

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Complex Finset

theorem phase_add_quarter (x : ℝ) : phase (x + 1 / 4) = I * phase x := by
  unfold phase
  have he : ((2 * Real.pi * (x + 1 / 4) : ℝ) : ℂ) * I =
      ((2 * Real.pi * x : ℝ) : ℂ) * I + (Real.pi / 2) * I := by push_cast; ring
  rw [he, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  ring

theorem G_length_one (x : ℝ) : G 1 x = phase x := by simp [G_eq_sum_phase]

theorem G_length_two (x : ℝ) : G 2 x = phase x + phase (2 * x) := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, G_succ_doubling, G_length_one]

theorem G_two_quarter (x : ℝ) : G 2 (x + 1 / 4) = I * phase x - phase (2 * x) := by
  rw [G_length_two, phase_add_quarter, show 2 * (x + 1 / 4) = 2 * x + 1 / 2 by ring,
    phase_add_half]
  ring

theorem G_two_half (x : ℝ) : G 2 (x + 1 / 2) = -phase x + phase (2 * x) := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, G_succ_half, G_length_one]

theorem G_two_three_quarters (x : ℝ) :
    G 2 (x + 3 / 4) = -(I * phase x) - phase (2 * x) := by
  rw [show x + 3 / 4 = (x + 1 / 4) + 1 / 2 by ring, G_two_half, phase_add_quarter,
    show 2 * (x + 1 / 4) = 2 * x + 1 / 2 by ring, phase_add_half]
  ring

theorem blockAverage_two_model (t x : ℝ) (ρ : ℂ) :
    blockAverage 2 t ρ (4 * x) =
      1 / 2 * (Real.exp (t * (ρ * phase (2 * x)).re) * Real.cosh (t * (ρ * phase x).re) +
        Real.exp (-(t * (ρ * phase (2 * x)).re)) * Real.cosh (t * (ρ * phase x).im)) := by
  norm_num only [blockAverage, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, add_zero, pow_succ, pow_zero]
  rw [show (4 * x) / (4 : ℝ) = x by ring,
    show (4 * x + 1) / (4 : ℝ) = x + 1 / 4 by ring,
    show (4 * x + 2) / (4 : ℝ) = x + 1 / 2 by ring,
    show (4 * x + 3) / (4 : ℝ) = x + 3 / 4 by ring]
  simp only [momentIntegrand]
  rw [G_two_three_quarters, G_two_half, G_two_quarter, G_length_two]
  have hI : (ρ * (I * phase x)).re = -(ρ * phase x).im := by
    rw [show ρ * (I * phase x) = I * (ρ * phase x) by ring]
    simp
  simp only [mul_add, mul_sub, mul_neg, Complex.add_re, Complex.sub_re, Complex.neg_re,
    hI, sub_eq_add_neg, Real.cosh_eq, Real.exp_add]
  ring

noncomputable def twoBlockFactor (t : ℝ) : ℝ :=
  (Real.exp (2 * t) + 1 + 2 * Real.exp (-t)) / 4

theorem twoBlockFactor_eq (t : ℝ) :
    twoBlockFactor t = 1 / 2 * (Real.exp t * Real.cosh t + Real.exp (-t)) := by
  have he : Real.exp (2 * t) = Real.exp t * Real.exp t := by rw [two_mul, Real.exp_add]
  have hc : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold twoBlockFactor
  rw [Real.cosh_eq]
  nlinarith

theorem BlockBound_two {t : ℝ} (ht : 0 ≤ t) : BlockBound 2 t (twoBlockFactor t) := by
  intro ρ hρ β hβ
  let x := β / 4
  have hm := blockAverage_two_model t x ρ
  rw [show 4 * x = β by dsimp [x]; ring] at hm
  have hz : ‖ρ * phase x‖ ≤ 1 := by simpa only [norm_mul, norm_phase, mul_one] using hρ
  have hu : |(ρ * phase (2 * x)).re| ≤ 1 := by
    calc
      _ ≤ ‖ρ * phase (2 * x)‖ := Complex.abs_re_le_norm _
      _ = ‖ρ‖ := by rw [norm_mul, norm_phase, mul_one]
      _ ≤ 1 := hρ
  have hsq : (ρ * phase x).re ^ 2 + (ρ * phase x).im ^ 2 ≤ 1 := by
    have hn := pow_le_pow_left₀ (norm_nonneg (ρ * phase x)) hz 2
    have he := Complex.sq_norm_sub_sq_re (ρ * phase x)
    nlinarith
  rw [hm, twoBlockFactor_eq]
  exact mul_le_mul_of_nonneg_left (paired_cosh_bound ht hu hsq) (by norm_num)

theorem twoBlockFactor_attained (t : ℝ) : blockAverage 2 t 1 0 = twoBlockFactor t := by
  have hm := blockAverage_two_model t 0 1
  norm_num [phase] at hm
  rw [twoBlockFactor_eq]
  simpa only [mul_one] using hm

#print axioms phase_add_quarter
#print axioms G_length_one
#print axioms G_length_two
#print axioms G_two_quarter
#print axioms G_two_half
#print axioms G_two_three_quarters

#print axioms blockAverage_two_model

#print axioms twoBlockFactor_eq

#print axioms BlockBound_two

#print axioms twoBlockFactor_attained

end LeanLab.PlattTrudgian2014
