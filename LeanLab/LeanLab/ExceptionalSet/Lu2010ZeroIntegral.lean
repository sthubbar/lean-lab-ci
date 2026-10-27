/-
P0095 Lu 2010, page 2379 equation 63 and page 2369 equation 39.
CODEX task47, unit U-8102. AI wrote this Lean code. Binary Goldbach is open.
The zero integrals are bounded by 3 N times their two real-part weights.
The bound is elementary for every finite family of exponents in the critical strip.
-/
import LeanLab.ExceptionalSet.Lu2010Eq86Scale

namespace LeanLab.ExceptionalSet.Lu2010ZeroIntegral
open Finset Real
open LeanLab.ExceptionalSet.Lu2010Assembly

/-- The weight assigned to an exponent with real part beta. -/
noncomputable def weight (N : ℕ) (ρ : ℂ) : ℝ := (N : ℝ) ^ (ρ.re - 1)

/-- The t integral with the factor d printed in equation 63. -/
noncomputable def J (N : ℕ) (ρ σ : ℂ) : ℂ :=
  (dd N : ℂ) * ∫ t in aa N..bb N,
    ((t * dd N : ℝ) : ℂ) ^ (ρ - 1) * (((N : ℝ) - t * dd N : ℝ) : ℂ) ^ (σ - 1)

/-- A factor whose real base is at least N over 3 costs at most three times its N weight. -/
theorem power_norm_bound {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : (N : ℝ) / 3 ≤ x)
    (ρ : ℂ) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) :
    ‖(x : ℂ) ^ (ρ - 1)‖ ≤ 3 * weight N ρ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx0 : 0 < x := by linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re]
  have he : (N / 3 : ℝ) ^ (ρ.re - 1) = (N : ℝ) ^ (ρ.re - 1) * (3 : ℝ) ^ (1 - ρ.re) := by
    rw [Real.div_rpow hN0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    congr 1
    ring
  have h3 : (3 : ℝ) ^ (1 - ρ.re) ≤ 3 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (show 1 - ρ.re ≤ 1 by linarith)).trans_eq (Real.rpow_one _)
  calc x ^ (ρ.re - 1) ≤ (N / 3 : ℝ) ^ (ρ.re - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hx (by linarith)
    _ = (N : ℝ) ^ (ρ.re - 1) * (3 : ℝ) ^ (1 - ρ.re) := he
    _ ≤ weight N ρ * 3 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-- Uniform bound for one zero-pair integral. -/
theorem J_bound {N : ℕ} (hN : 1 ≤ N) (ρ σ : ℂ)
    (hρ0 : 0 ≤ ρ.re) (hρ1 : ρ.re ≤ 1) (hσ0 : 0 ≤ σ.re) (hσ1 : σ.re ≤ 1) :
    ‖J N ρ σ‖ ≤ 3 * N * weight N ρ * weight N σ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd0 : 0 < dd N := by unfold dd; positivity
  have had : aa N * dd N = N / 3 := by
    unfold aa dd
    rw [div_mul_eq_mul_div, ← Real.rpow_add hN0]
    norm_num
  have hba := bad_mul N (by omega)
  have hbd : bb N * dd N = 2 * (N : ℝ) / 3 := by nlinarith
  have hab : aa N ≤ bb N := by nlinarith
  have hfun : ∀ t ∈ Set.uIoc (aa N) (bb N),
      ‖((t * dd N : ℝ) : ℂ) ^ (ρ - 1) * (((N : ℝ) - t * dd N : ℝ) : ℂ) ^ (σ - 1)‖ ≤
        9 * weight N ρ * weight N σ := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    have hx : (N : ℝ) / 3 ≤ t * dd N := by nlinarith [ht.1.le]
    have hy : (N : ℝ) / 3 ≤ (N : ℝ) - t * dd N := by nlinarith [ht.2]
    rw [norm_mul]
    have h := mul_le_mul (power_norm_bound hN hx ρ hρ0 hρ1)
      (power_norm_bound hN hy σ hσ0 hσ1) (norm_nonneg _) (by unfold weight; positivity)
    nlinarith
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hfun
  unfold J
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd0.le]
  calc dd N * ‖∫ t in aa N..bb N,
        ((t * dd N : ℝ) : ℂ) ^ (ρ - 1) * (((N : ℝ) - t * dd N : ℝ) : ℂ) ^ (σ - 1)‖
      ≤ dd N * (9 * weight N ρ * weight N σ * |bb N - aa N|) :=
        mul_le_mul_of_nonneg_left hi hd0.le
    _ = 9 * ((bb N - aa N) * dd N) * weight N ρ * weight N σ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring
    _ = _ := by rw [hba]; ring

/-- Summing the absolute zero integrals costs at most the square of their total one-zero weight. -/
theorem sum_J_bound {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) {N : ℕ} (hN : 1 ≤ N)
    (h0 : ∀ i ∈ s, 0 ≤ (ρ i).re) (h1 : ∀ i ∈ s, (ρ i).re ≤ 1) :
    ∑ i ∈ s, ∑ j ∈ s, ‖J N (ρ i) (ρ j)‖ ≤
      3 * N * (∑ i ∈ s, weight N (ρ i)) ^ 2 := by
  calc (∑ i ∈ s, ∑ j ∈ s, ‖J N (ρ i) (ρ j)‖)
      ≤ ∑ i ∈ s, ∑ j ∈ s, 3 * N * weight N (ρ i) * weight N (ρ j) := by
        apply sum_le_sum
        intro i hi
        exact sum_le_sum fun j hj => J_bound hN _ _ (h0 i hi) (h1 i hi) (h0 j hj) (h1 j hj)
    _ = _ := by
      rw [pow_two, sum_mul_sum, mul_sum]
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring

end LeanLab.ExceptionalSet.Lu2010ZeroIntegral

#print axioms LeanLab.ExceptionalSet.Lu2010ZeroIntegral.power_norm_bound
#print axioms LeanLab.ExceptionalSet.Lu2010ZeroIntegral.J_bound
#print axioms LeanLab.ExceptionalSet.Lu2010ZeroIntegral.sum_J_bound
