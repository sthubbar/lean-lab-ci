/-
AI wrote this Lean code for CODEX task58.
Coarse supporting bounds for the lab constant of P0039 equation 3.9.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58Integrands

open Real intervalIntegral MeasureTheory Set Finset

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- A rational upper bound for logarithms at positive arguments above one. -/
theorem log_le_rational {y : ℝ} (hy : 1 ≤ y) : log y ≤ (y ^ 2 - 1) / (2 * y) := by
  let z := (y - 1) / (y + 1)
  have hy0 : 0 < y := by linarith
  have hyp : y + 1 ≠ 0 := by linarith
  have hz0 : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz1 : z < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hform : (1 + z) / (1 - z) = y := by
    dsimp [z]
    field_simp [ne_of_gt hy0]
    <;> ring
  have hs : 1 - z ^ 2 ≠ 0 := by nlinarith
  have h := log_div_le_sum_range_add hz0 hz1 0
  simp only [sum_range_zero, mul_zero, zero_add, pow_one] at h
  rw [hform] at h
  have hid : 2 * (z / (1 - z ^ 2)) = (y ^ 2 - 1) / (2 * y) := by
    rw [← mul_div_assoc, div_eq_div_iff hs (mul_ne_zero (by norm_num) hy0.ne')]
    dsimp [z]
    field_simp [hyp]
    <;> ring
  linarith

/-- Rational majorant at a quadrature endpoint for IB1. -/
def densityUpper (t : ℝ) : ℝ :=
  ((2 - 3 * t) ^ 2 - 1) / (2 * (2 - 3 * t) * (t * (1 - t)))

theorem density_le_upper {t : ℝ} (ht : t ∈ Set.Icc (1 / 10 : ℝ) (1 / 3)) :
    density t ≤ densityUpper t := by
  have hlog := log_le_rational (show 1 ≤ 2 - 3 * t by linarith [ht.2])
  have hd : 0 ≤ t * (1 - t) := mul_nonneg (by linarith [ht.1]) (by linarith [ht.2])
  have h := div_le_div_of_nonneg_right hlog hd
  simpa [density, densityUpper, div_div] using h

/-- A coarse 32 cell bound for the actual integral IB1. -/
theorem IB1_le_coarse : U1435.IB1 ≤ 0.528 := by
  let a : ℕ → ℝ := fun k => 1 / 10 + 7 / 960 * k
  have ha : ∀ k < 32, a k ≤ a (k + 1) := by
    intro k hk
    dsimp [a]
    push_cast
    linarith
  have hgrid : ∀ k ≤ 32, a k ∈ Set.Icc (1 / 10 : ℝ) (1 / 3) := by
    intro k hk
    have hk' : (k : ℝ) ≤ 32 := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    dsimp [a]
    constructor <;> linarith
  have hf : ∀ k < 32, IntervalIntegrable density volume (a k) (a (k + 1)) := by
    intro k hk
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (ha k hk)]
    apply density_continuous.mono
    intro x hx
    exact ⟨(hgrid k (by omega)).1.trans hx.1, hx.2.trans (hgrid (k + 1) (by omega)).2⟩
  have hm : ∀ k < 32, if (false : Bool) then MonotoneOn density (Set.Icc (a k) (a (k + 1)))
      else AntitoneOn density (Set.Icc (a k) (a (k + 1))) := by
    intro k hk
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply density_antitone.mono
    intro x hx
    exact ⟨(hgrid k (by omega)).1.trans hx.1, hx.2.trans (hgrid (k + 1) (by omega)).2⟩
  have h := (riemann_bounds (inc := fun _ => false) ha hf hm).2
  have hsum : (∑ k ∈ range 32, (a (k + 1) - a k) * density (a k)) ≤
      ∑ k ∈ range 32, (a (k + 1) - a k) * densityUpper (a k) := by
    apply sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (density_le_upper (hgrid k (Nat.le_of_lt (mem_range.mp hk))))
      (sub_nonneg.mpr (ha k (mem_range.mp hk)))
  have hnum : (∑ k ∈ range 32, (a (k + 1) - a k) * densityUpper (a k)) ≤ (0.528 : ℝ) := by
    norm_num [a, densityUpper, sum_range_succ]
  have ha0 : a 0 = 1 / 10 := by norm_num [a]
  have ha32 : a 32 = 1 / 3 := by norm_num [a]
  simp only [Bool.false_eq_true, ↓reduceIte, ha0, ha32] at h
  exact h.trans (hsum.trans hnum)


/-- The first positive term in the atanh series bounds the logarithm below. -/
theorem rational_le_log {y : ℝ} (hy : 1 ≤ y) : 2 * (y - 1) / (y + 1) ≤ log y := by
  let z := (y - 1) / (y + 1)
  have hz0 : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz1 : z < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hform : (1 + z) / (1 - z) = y := by
    dsimp [z]
    field_simp
    ring
  have h := sum_range_le_log_div hz0 hz1 1
  norm_num [sum_range_succ] at h
  rw [hform] at h
  dsimp [z] at h
  rw [mul_div_assoc]
  linarith

/-- Rational lower bound at a quadrature endpoint for IB1. -/
def densityLower (t : ℝ) : ℝ :=
  (2 * ((2 - 3 * t) - 1) / ((2 - 3 * t) + 1)) / (t * (1 - t))

theorem density_lower_le {t : ℝ} (ht : t ∈ Set.Icc (1 / 10 : ℝ) (1 / 3)) :
    densityLower t ≤ density t := by
  exact div_le_div_of_nonneg_right
    (rational_le_log (show 1 ≤ 2 - 3 * t by linarith [ht.2]))
    (mul_nonneg (by linarith [ht.1]) (by linarith [ht.2]))

/-- A coarse lower bound using the right endpoints of 32 decreasing cells. -/
theorem coarse_le_IB1 : (0.46 : ℝ) ≤ U1435.IB1 := by
  let a : ℕ → ℝ := fun k => 1 / 10 + 7 / 960 * k
  have ha : ∀ k < 32, a k ≤ a (k + 1) := by
    intro k hk
    dsimp [a]
    push_cast
    linarith
  have hgrid : ∀ k ≤ 32, a k ∈ Set.Icc (1 / 10 : ℝ) (1 / 3) := by
    intro k hk
    have hk' : (k : ℝ) ≤ 32 := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    dsimp [a]
    constructor <;> linarith
  have hf : ∀ k < 32, IntervalIntegrable density volume (a k) (a (k + 1)) := by
    intro k hk
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (ha k hk)]
    apply density_continuous.mono
    intro x hx
    exact ⟨(hgrid k (by omega)).1.trans hx.1, hx.2.trans (hgrid (k + 1) (by omega)).2⟩
  have hm : ∀ k < 32, if (false : Bool) then MonotoneOn density (Set.Icc (a k) (a (k + 1)))
      else AntitoneOn density (Set.Icc (a k) (a (k + 1))) := by
    intro k hk
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply density_antitone.mono
    intro x hx
    exact ⟨(hgrid k (by omega)).1.trans hx.1, hx.2.trans (hgrid (k + 1) (by omega)).2⟩
  have h := (riemann_bounds (inc := fun _ => false) ha hf hm).1
  have hsum : (∑ k ∈ range 32, (a (k + 1) - a k) * densityLower (a (k + 1))) ≤
      ∑ k ∈ range 32, (a (k + 1) - a k) * density (a (k + 1)) := by
    apply sum_le_sum
    intro k hk
    have hk' := mem_range.mp hk
    exact mul_le_mul_of_nonneg_left (density_lower_le (hgrid (k + 1) (by omega)))
      (sub_nonneg.mpr (ha k hk'))
  have hnum : (0.46 : ℝ) ≤
      (∑ k ∈ range 32, (a (k + 1) - a k) * densityLower (a (k + 1))) := by
    norm_num [a, densityLower, sum_range_succ]
  have ha0 : a 0 = 1 / 10 := by norm_num [a]
  have ha32 : a 32 = 1 / 3 := by norm_num [a]
  simp only [Bool.false_eq_true, ↓reduceIte, ha0, ha32] at h
  exact hnum.trans (hsum.trans h)

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.log_le_rational
#print axioms LeanLab.ChenPrimeExceptional.Task58.density_le_upper
#print axioms LeanLab.ChenPrimeExceptional.Task58.IB1_le_coarse

#print axioms LeanLab.ChenPrimeExceptional.Task58.rational_le_log
#print axioms LeanLab.ChenPrimeExceptional.Task58.density_lower_le
#print axioms LeanLab.ChenPrimeExceptional.Task58.coarse_le_IB1
