/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv math/0201299 Section 7 pages 28 to 30, displays 42 to 44,
and arXiv 1404.5669v2 page 3 displays 4 and 5.
The h = 1 exponential moment bound is an elementary weaker variant.
-/
import LeanLab.PlattTrudgian2014.Lambda

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Complex
open scoped Interval

noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * I)

theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

@[fun_prop]
theorem continuous_phase : Continuous phase := by
  unfold phase
  fun_prop

theorem G_eq_sum_phase (L : ℕ) (x : ℝ) :
    G L x = ∑ j ∈ Finset.range L, phase (2 ^ j * x) := by
  unfold G phase
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  push_cast
  ring

theorem norm_G_le (L : ℕ) (x : ℝ) : ‖G L x‖ ≤ L := by
  rw [G_eq_sum_phase]
  calc
    _ ≤ ∑ j ∈ Finset.range L, ‖phase (2 ^ j * x)‖ := norm_sum_le _ _
    _ = L := by simp [norm_phase]

theorem phase_add_nat (x : ℝ) (n : ℕ) : phase (x + n) = phase x := by
  unfold phase
  have he : ((2 * Real.pi * (x + n) : ℝ) : ℂ) * I =
      ((2 * Real.pi * x : ℝ) : ℂ) * I + (n : ℤ) * (2 * Real.pi * I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem phase_add_half (x : ℝ) : phase (x + 1 / 2) = -phase x := by
  unfold phase
  have he : ((2 * Real.pi * (x + 1 / 2) : ℝ) : ℂ) * I =
      ((2 * Real.pi * x : ℝ) : ℂ) * I + Real.pi * I := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

@[fun_prop]
theorem continuous_G (L : ℕ) : Continuous (G L) := by
  have he : G L = fun x => ∑ j ∈ Finset.range L, phase (2 ^ j * x) :=
    funext (G_eq_sum_phase L)
  rw [he]
  fun_prop

theorem G_add_one (L : ℕ) (x : ℝ) : G L (x + 1) = G L x := by
  simp only [G_eq_sum_phase]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_add, mul_one]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using phase_add_nat (2 ^ j * x) (2 ^ j)

theorem G_succ_doubling (L : ℕ) (x : ℝ) :
    G (L + 1) x = phase x + G L (2 * x) := by
  simp only [G_eq_sum_phase, Finset.sum_range_succ']
  simp only [pow_zero, one_mul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  congr 1
  ring

noncomputable def momentIntegrand (L : ℕ) (t : ℝ) (ρ : ℂ) (x : ℝ) : ℝ :=
  Real.exp (t * (ρ * G L x).re)

noncomputable def expMoment (L : ℕ) (t : ℝ) (ρ : ℂ) : ℝ :=
  ∫ x in (0 : ℝ)..1, momentIntegrand L t ρ x

@[fun_prop]
theorem continuous_momentIntegrand (L : ℕ) (t : ℝ) (ρ : ℂ) :
    Continuous (momentIntegrand L t ρ) := by
  unfold momentIntegrand
  fun_prop

theorem G_succ_half (L : ℕ) (x : ℝ) :
    G (L + 1) (x + 1 / 2) = -phase x + G L (2 * x) := by
  rw [G_succ_doubling, phase_add_half,
    show 2 * (x + 1 / 2) = 2 * x + 1 by ring, G_add_one]

theorem moment_pair (L : ℕ) (t : ℝ) (ρ : ℂ) (x : ℝ) :
    momentIntegrand (L + 1) t ρ x + momentIntegrand (L + 1) t ρ (x + 1 / 2) =
      2 * Real.cosh (t * (ρ * phase x).re) * momentIntegrand L t ρ (2 * x) := by
  simp only [momentIntegrand]
  rw [G_succ_half, G_succ_doubling]
  simp only [mul_add, mul_neg,
    Complex.add_re, Complex.neg_re, Real.exp_add, Real.cosh_eq]
  ring

theorem moment_pair_le (L : ℕ) {t : ℝ} (ht : 0 ≤ t) {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) (x : ℝ) :
    momentIntegrand (L + 1) t ρ x + momentIntegrand (L + 1) t ρ (x + 1 / 2) ≤
      2 * Real.cosh t * momentIntegrand L t ρ (2 * x) := by
  rw [moment_pair]
  have ha : |(ρ * phase x).re| ≤ 1 := by
    calc
      _ ≤ ‖ρ * phase x‖ := Complex.abs_re_le_norm _
      _ = ‖ρ‖ := by rw [norm_mul, norm_phase, mul_one]
      _ ≤ 1 := hρ
  have hc : Real.cosh (t * (ρ * phase x).re) ≤ Real.cosh t := by
    apply Real.cosh_le_cosh.mpr
    simp only [abs_mul, abs_of_nonneg ht]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha ht
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num))
    (Real.exp_nonneg _)

theorem expMoment_succ_le (L : ℕ) {t : ℝ} (ht : 0 ≤ t) {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) :
    expMoment (L + 1) t ρ ≤ Real.cosh t * expMoment L t ρ := by
  let f := momentIntegrand (L + 1) t ρ
  have hf : Continuous f := continuous_momentIntegrand _ _ _
  have hp : Continuous (fun x => f x + f (x + 1 / 2)) := by fun_prop
  have hg : Continuous (fun x => 2 * Real.cosh t * momentIntegrand L t ρ (2 * x)) := by fun_prop
  have hsplit : expMoment (L + 1) t ρ =
      ∫ x in (0 : ℝ)..(1 / 2), (f x + f (x + 1 / 2)) := by
    rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _)
      (by exact (hf.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)]
    have hshift := intervalIntegral.integral_comp_add_right (a := (0 : ℝ))
      (b := (1 / 2 : ℝ)) f (1 / 2)
    norm_num only [zero_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at hshift
    rw [hshift]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
  rw [hsplit]
  calc
    _ ≤ ∫ x in (0 : ℝ)..(1 / 2), 2 * Real.cosh t * momentIntegrand L t ρ (2 * x) :=
      intervalIntegral.integral_mono (by norm_num) (hp.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
        (moment_pair_le L ht hρ)
    _ = Real.cosh t * expMoment L t ρ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left _ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num only [mul_zero, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0),
        smul_eq_mul]
      unfold expMoment
      ring

theorem expMoment_le_cosh_pow (L : ℕ) {t : ℝ} (ht : 0 ≤ t) {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) :
    expMoment L t ρ ≤ Real.cosh t ^ L := by
  induction L with
  | zero => simp [expMoment, momentIntegrand, G, Real.exp_zero]
  | succ L ih =>
    calc
      _ ≤ Real.cosh t * expMoment L t ρ := expMoment_succ_le L ht hρ
      _ ≤ Real.cosh t * Real.cosh t ^ L :=
        mul_le_mul_of_nonneg_left ih (Real.cosh_pos t).le
      _ = Real.cosh t ^ (L + 1) := by ring

#print axioms norm_phase
#print axioms continuous_phase
#print axioms G_eq_sum_phase
#print axioms norm_G_le

#print axioms phase_add_nat

#print axioms phase_add_half

#print axioms continuous_G

#print axioms G_add_one

#print axioms G_succ_doubling

#print axioms continuous_momentIntegrand

#print axioms G_succ_half

#print axioms moment_pair

#print axioms moment_pair_le

#print axioms expMoment_succ_le

#print axioms expMoment_le_cosh_pow

end LeanLab.PlattTrudgian2014
