import LeanLab.ChirreHagen2025.Decomp608e
import LeanLab.ChirreHagen2025.Decomp608b
import LeanLab.ChirreHagen2025.Decomp608c
open MeasureTheory Set Filter Polynomial LeanLab.ChirreHagen2025
open Decomp608e Decomp608b Decomp608c

/-!
Berndt 1972 page 153, the boundary and convergence facts used in display 3.1.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp608f

/-- Berndt page 153 before display 3.1, the lower derivatives vanish at one. -/
theorem kernel_derivative_at_one (n k : ℕ) (hk : k < n) :
    iteratedDeriv k (fun x : ℝ => Real.log x ^ n / (x * (n.factorial : ℝ))) 1 = 0 := by
  rw [iteratedDeriv_kernel_eq n k zero_lt_one]
  simp only [Real.log_one, one_pow, div_one]
  rw [← coeff_zero_eq_eval_zero, derivativePoly_coeff]
  simp [signedFirst, Nat.stirlingFirst_eq_zero_of_lt (Nat.succ_lt_succ hk)]

/-- Berndt page 153 display 3.2, finite coefficient form of the derivative. -/
theorem iteratedDeriv_kernel_sum (n k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (fun y : ℝ => Real.log y ^ n / (y * (n.factorial : ℝ))) x =
      ∑ j ∈ Finset.range (n + 1), (derivativePoly n k).coeff j *
        (Real.log x ^ j / x ^ (k + 1)) := by
  have hd : (derivativePoly n k).natDegree ≤ n := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [derivativePoly_coeff, ite_eq_right (by omega)]
  rw [iteratedDeriv_kernel_eq n k hx, eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Berndt page 153 before display 3.1, every derivative tends to zero at infinity. -/
theorem tendsto_kernel_derivative_atTop (n k : ℕ) :
    Tendsto (iteratedDeriv k (fun y : ℝ => Real.log y ^ n / (y * (n.factorial : ℝ))))
      atTop (nhds 0) := by
  have ht (j : ℕ) : Tendsto (fun x : ℝ => (derivativePoly n k).coeff j *
      (Real.log x ^ j / x ^ (k + 1))) atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (j : ℝ)
      (s := ((k + 1 : ℕ) : ℝ)) (by positivity)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast, mul_zero] using h.const_mul ((derivativePoly n k).coeff j)
  have hs := tendsto_finsetSum (Finset.range (n + 1)) (fun j _ => ht j)
  simp only [Finset.sum_const_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (iteratedDeriv_kernel_sum n k hx).symm

/-- The positive-order logarithmic derivatives in Berndt display 3.1 are integrable. -/
theorem kernel_derivative_integrable (n k : ℕ) (hk : 1 ≤ k) :
    IntegrableOn (iteratedDeriv k (fun y : ℝ => Real.log y ^ n / (y * (n.factorial : ℝ))))
      (Ioi 1) := by
  have hs : IntegrableOn (fun x : ℝ => ∑ j ∈ Finset.range (n + 1),
      (derivativePoly n k).coeff j * (Real.log x ^ j / x ^ (k + 1))) (Ioi 1) :=
    integrable_finsetSum _ (fun j _ => (log_moment_integrable k j hk).const_mul _)
  exact hs.congr_fun (fun x hx => (iteratedDeriv_kernel_sum n k
    (lt_trans zero_lt_one hx)).symm) measurableSet_Ioi

/-- Berndt page 153 display 3.1, absolute convergence of the periodic remainder. -/
theorem berndt_integrand_integrable (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (fun x : ℝ => periodicBernoulli n x *
      iteratedDeriv n (fun y : ℝ => Real.log y ^ n / (y * (n.factorial : ℝ))) x) (Ioi 1) := by
  have hg := kernel_derivative_integrable n n hn
  have hm : Measurable (periodicBernoulli n) := by
    unfold periodicBernoulli bernoulliFun
    fun_prop
  apply hg.bdd_mul (c := 4 / (2 * Real.pi) ^ n) hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using periodicBernoulli_uniform_bound n hn x)

end LeanLab.ChirreHagen2025.Decomp608f
