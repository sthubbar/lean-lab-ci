/-
P0069, page 27, equation 4.13. Elementary bounds for the smooth divisor tail.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.MoebiusSieve
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
open Finset ArithmeticFunction
namespace LeanLab.BakerHarmanPintz1997
attribute [local instance] Classical.propDecidable
/-- A finite Rankin bound for the reciprocal divisor tail in equation 4.13. -/
theorem squarefree_divisor_tail_rankin (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {γ : ℝ} (hγ : 0 < γ)
    (s : ℝ) (hs : 0 ≤ s) :
    ∑ d ∈ (∏ p ∈ P, p).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ)), (d : ℝ)⁻¹ ≤
      γ ^ (-s) * ∏ p ∈ P, (1 + (p : ℝ) ^ (s - 1)) := by
  have hprod : ∑ d ∈ (∏ p ∈ P, p).divisors, (d : ℝ) ^ (s - 1) =
      ∏ p ∈ P, (1 + (p : ℝ) ^ (s - 1)) := by
    have he := sum_divisors_prime_product P hP (fun d => (((d : ℝ) ^ (s - 1) : ℝ) : ℂ))
    have hre := congrArg Complex.re he
    simp at hre
    rw [hre, prod_one_add]
    apply sum_congr rfl
    intro T hT
    rw [Real.finsetProd_rpow]
    intro p hp
    exact Nat.cast_nonneg p
  have hterm : ∀ d ∈ (∏ p ∈ P, p).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ)),
      (d : ℝ)⁻¹ ≤ γ ^ (-s) * (d : ℝ) ^ (s - 1) := by
    intro d hd
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors (mem_filter.mp hd).1
    have hpow : γ ^ s ≤ (d : ℝ) ^ s := Real.rpow_le_rpow hγ.le (mem_filter.mp hd).2 hs
    have hγpow : γ ^ s ≠ 0 := (Real.rpow_pos_of_pos hγ s).ne'
    calc
      (d : ℝ)⁻¹ = γ ^ (-s) * (γ ^ s / d) := by
        rw [Real.rpow_neg hγ.le, ← mul_div_assoc, inv_mul_cancel₀ hγpow, one_div]
      _ ≤ γ ^ (-s) * ((d : ℝ) ^ s / d) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hd0.le)
          (Real.rpow_nonneg hγ.le _)
      _ = _ := by rw [Real.rpow_sub hd0, Real.rpow_one]
  calc _ ≤ ∑ d ∈ (∏ p ∈ P, p).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ)), γ ^ (-s) * (d : ℝ) ^ (s - 1) :=
        sum_le_sum hterm
    _ ≤ ∑ d ∈ (∏ p ∈ P, p).divisors, γ ^ (-s) * (d : ℝ) ^ (s - 1) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun d _ _ => mul_nonneg (Real.rpow_nonneg hγ.le _) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
    _ = _ := by rw [← mul_sum, hprod]

/-- The exact smooth divisor window occurring in equation 4.13 on page 27. -/
theorem reciprocal_smooth_tail_rankin (w : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (s : ℝ) (hs : 0 ≤ s) :
    ∑ d ∈ (siftingProduct w).divisors.filter
      (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w), (d : ℝ)⁻¹ ≤
      γ ^ (-s) * ∏ p ∈ primesBelow w, (1 + (p : ℝ) ^ (s - 1)) := by
  calc
    _ ≤ ∑ d ∈ (siftingProduct w).divisors.filter
        (fun d : ℕ => γ ≤ (d : ℝ)), (d : ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          obtain ⟨hd, hlo, _⟩ := mem_filter.mp hd
          exact mem_filter.mpr ⟨hd, hlo⟩
        · intro d _ _
          positivity
    _ ≤ _ := squarefree_divisor_tail_rankin (primesBelow w)
      (fun p hp => (mem_primesBelow.mp hp).1) hγ s hs

open Filter in
/-- Replacing the Euler product by exp w cannot yield the saving in 4.13. -/
theorem coarse_rankin_bound_ge_one_ev (c : ℝ) (hc : 0 < c) : Ev fun x => 1 ≤ x ^ (-c) * Real.exp (wof x) := by
  have ht : Tendsto (fun x : ℝ => Real.log x ^ (9 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp Real.tendsto_log_atTop
  have hb := (isLittleO_rpow_exp_atTop (10 / 9 : ℝ)).bound (one_div_pos.mpr hc)
  obtain ⟨X, hX⟩ := eventually_atTop.mp (ht.eventually hb)
  refine ⟨max X 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have heq : (Real.log x ^ (9 / 10 : ℝ)) ^ (10 / 9 : ℝ) = Real.log x := by
    rw [← Real.rpow_mul hlog]
    norm_num
  have hb' := hX x ((le_max_left _ _).trans hx)
  simp only [heq, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_pos (Real.exp_pos _)] at hb'
  have hcw : Real.log x * c ≤ wof x := by
    apply (le_div_iff₀ hc).mp
    simpa [wof, div_eq_mul_inv, mul_comm] using hb'
  change 1 ≤ x ^ (-c) * Real.exp (wof x)
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_add]
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  nlinarith

#print axioms coarse_rankin_bound_ge_one_ev
#print axioms reciprocal_smooth_tail_rankin
#print axioms squarefree_divisor_tail_rankin
end LeanLab.BakerHarmanPintz1997
