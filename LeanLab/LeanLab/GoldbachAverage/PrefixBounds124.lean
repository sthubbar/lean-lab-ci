import LeanLab.GoldbachAverage.WeightedMass124
import LeanLab.GoldbachAverage.GeometricTail124

/-!
Coarse prefix bounds used only to prove convergence of the geometric tails in P0051 page 11.
They do not supply the sharp theta variance input.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.PrefixBounds124
open MeasureTheory Filter Set
open FloorVariance82 WeightedMass124

/-- A measurable function with a linear bound has an integrable square and a cubic prefix bound.
Source context: convergence of the prefix sums in P0051 page 11 eq. 56. -/
theorem bounded_square_prefix {F : ℝ → ℝ} (hF : Measurable F)
    {T K h : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) (hh : 0 ≤ h)
    (hb : ∀ t : ℝ, 0 ≤ t → t ≤ T → |F t| ≤ K * (t + h + 1)) :
    IntervalIntegrable (fun t => F t ^ 2) volume 0 T ∧
      0 ≤ (∫ t in (0 : ℝ)..T, F t ^ 2) ∧
      (∫ t in (0 : ℝ)..T, F t ^ 2) ≤ K ^ 2 * T * (T + h + 1) ^ 2 := by
  have hpt : ∀ t ∈ Icc (0 : ℝ) T, F t ^ 2 ≤ K ^ 2 * (T + h + 1) ^ 2 := by
    intro t ht
    have hs : |F t| ≤ K * (T + h + 1) :=
      (hb t ht.1 ht.2).trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hK)
    have hp := pow_le_pow_left₀ (abs_nonneg (F t)) hs 2
    simpa only [sq_abs, mul_pow] using hp
  have hi : IntervalIntegrable (fun t => F t ^ 2) volume 0 T := by
    refine (intervalIntegrable_const (c := K ^ 2 * (T + h + 1) ^ 2)).mono_fun'
      (hF.pow_const 2).aestronglyMeasurable ?_
    rw [Set.uIoc_of_le hT]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt t ⟨ht.1.le, ht.2⟩
  refine ⟨hi, intervalIntegral.integral_nonneg hT (fun _ _ => sq_nonneg _), ?_⟩
  have hm := intervalIntegral.integral_mono_on hT hi intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hm
  nlinarith

/-- Cubic prefix growth suffices for convergence of the half geometric weighted prefix series.
Source context: the sums in P0051 page 11 eq. 56. -/
theorem geometric_cubic_summable (F : ℝ → ℝ) {N h C : ℝ}
    (hN : 0 < N) (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hF0 : ∀ T : ℝ, 0 ≤ T → 0 ≤ F T)
    (hFb : ∀ T : ℝ, 0 ≤ T → F T ≤ C * T * (T + h + 1) ^ 2) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * F (((j : ℝ) + 1) * N)) := by
  have hs : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * ((j : ℝ) + 1) ^ 3) := by
    have ht := (summable_nat_add_iff 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one 3 (r := (1 / 2 : ℝ)) (by norm_num))
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using ht
  refine Summable.of_nonneg_of_le (fun j =>
    mul_nonneg (by positivity) (hF0 _ (by positivity))) ?_
    (hs.mul_left (C * N * (N + h + 1) ^ 2))
  intro j
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg j)
  have hT : 0 ≤ ((j : ℝ) + 1) * N := by positivity
  have hshape : ((j : ℝ) + 1) * N + h + 1 ≤ ((j : ℝ) + 1) * (N + h + 1) := by
    have hm := mul_le_mul_of_nonneg_right hj (show 0 ≤ h + 1 by linarith)
    nlinarith
  have hb := hFb (((j : ℝ) + 1) * N) hT
  have hpoly : F (((j : ℝ) + 1) * N) ≤ C * N * (N + h + 1) ^ 2 * ((j : ℝ) + 1) ^ 3 := by
    calc _ ≤ C * (((j : ℝ) + 1) * N) * (((j : ℝ) + 1) * N + h + 1) ^ 2 := hb
      _ ≤ C * (((j : ℝ) + 1) * N) * (((j : ℝ) + 1) * (N + h + 1)) ^ 2 := by gcongr
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hpoly
    (show 0 ≤ (1 / 2 : ℝ) ^ (j + 1) by positivity)
  convert hm using 1 <;> ring

/-- A coarse linear bound for the psi error, used only for convergence.
Source context: H in P0051 page 3 eq. 15 and page 11. -/
theorem psi_error_linear {t : ℝ} (ht : 0 ≤ t) :
    |Chebyshev.psi t - t| ≤ 8 * (t + 1) := by
  have hp := Chebyshev.psi_le_const_mul_self ht
  have hl : Real.log (4 : ℝ) ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hm := mul_le_mul_of_nonneg_right hl ht
  have hp0 := Chebyshev.psi_nonneg t
  rw [abs_le]
  constructor <;> nlinarith

/-- A coarse linear bound for the short psi error, used only for convergence.
Source context: J in P0051 page 3 eq. 15 and page 11. -/
theorem psi_short_error_linear {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    |Chebyshev.psi (t + h) - Chebyshev.psi t - h| ≤ 8 * (t + h + 1) := by
  have hp1 := Chebyshev.psi_le_const_mul_self (show 0 ≤ t + h by linarith)
  have hp2 := Chebyshev.psi_le_const_mul_self ht
  have hl : Real.log (4 : ℝ) ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hm1 := mul_le_mul_of_nonneg_right hl (show 0 ≤ t + h by linarith)
  have hm2 := mul_le_mul_of_nonneg_right hl ht
  have hp10 := Chebyshev.psi_nonneg (t + h)
  have hp20 := Chebyshev.psi_nonneg t
  rw [abs_le]
  constructor <;> nlinarith

/-- A coarse linear bound for the R increment, used only for convergence.
Source context: eq. 52 and the sums in P0051 page 11. -/
theorem R_increment_linear {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    |psiFloorError (t + h) - psiFloorError t| ≤ 16 * (t + h + 1) := by
  have h1 := R_linear_bound (show 0 ≤ t + h by linarith)
  have h2 := R_linear_bound ht
  have h3 := abs_sub (psiFloorError (t + h)) (psiFloorError t)
  linarith

end LeanLab.GoldbachAverage.PrefixBounds124
