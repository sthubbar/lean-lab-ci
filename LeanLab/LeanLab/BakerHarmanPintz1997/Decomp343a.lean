/-
P0069 page 21, local elementary infrastructure for the nonresonant discretization supply.
The paper cites FGM and does not display the discretization estimate itself.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

namespace LeanLab.BakerHarmanPintz1997.Decomp343a
open Finset MeasureTheory intervalIntegral

/-- Page 21 supply infrastructure. First order Euler summation on one unit interval.
The local sawtooth is x minus the left endpoint. -/
theorem euler_unit (f f' : ℝ → ℂ) (a : ℝ)
    (hf : ContinuousOn f (Set.uIcc a (a + 1)))
    (hd : ∀ x ∈ Set.uIcc a (a + 1), HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f' volume a (a + 1)) :
    f (a + 1) - (∫ x in a..a + 1, f x) =
      ∫ x in a..a + 1, ((x - a : ℝ) : ℂ) * f' x := by
  have hu : ContinuousOn (fun x : ℝ => ((x - a : ℝ) : ℂ)) (Set.uIcc a (a + 1)) := by
    fun_prop
  have hdu : ∀ x ∈ Set.Ioo (min a (a + 1)) (max a (a + 1)),
      HasDerivAt (fun y : ℝ => ((y - a : ℝ) : ℂ)) 1 x := by
    intro x hx
    simpa using ((hasDerivAt_id (x : ℂ)).sub_const (a : ℂ)).comp_ofReal
  have hh := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hf hdu
    (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume a (a + 1)) hi
  simpa using hh.symm

example : (1 : ℂ) - (∫ _x in (1 : ℝ)..2, (1 : ℂ)) =
    ∫ x in (1 : ℝ)..2, ((x - 1 : ℝ) : ℂ) * 0 := by
  norm_num [intervalIntegral.integral_const]

#print axioms euler_unit

/-- Page 21 supply infrastructure. Translate the local sawtooth remainder to a fixed unit cell. -/
theorem euler_unit_shift (f f' : ℝ → ℂ) (a : ℝ)
    (hf : ContinuousOn f (Set.uIcc a (a + 1)))
    (hd : ∀ x ∈ Set.uIcc a (a + 1), HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f' volume a (a + 1)) :
    f (a + 1) - (∫ x in a..a + 1, f x) =
      ∫ u in (0 : ℝ)..1, (u : ℂ) * f' (a + u) := by
  rw [euler_unit f f' a hf hd hi]
  simpa using (integral_comp_add_left
    (fun x : ℝ => ((x - a : ℝ) : ℂ) * f' x) a (a := 0) (b := 1)).symm

/-- Page 21 supply infrastructure. Finite Euler summation with cancellation retained
inside the unit cell integral. -/
theorem euler_sum (f f' : ℝ → ℂ) (a : ℝ) (m : ℕ)
    (hf : ∀ k < m, ContinuousOn f (Set.uIcc (a + k) (a + k + 1)))
    (hd : ∀ k < m, ∀ x ∈ Set.uIcc (a + k) (a + k + 1), HasDerivAt f (f' x) x)
    (hi : ∀ k < m, IntervalIntegrable f' volume (a + k) (a + k + 1))
    (hs : ∀ k < m, IntervalIntegrable
      (fun u : ℝ => (u : ℂ) * f' (a + k + u)) volume 0 1) :
    (∑ k ∈ range m, f (a + k + 1)) - (∫ x in a..a + m, f x) =
      ∫ u in (0 : ℝ)..1, (u : ℂ) * ∑ k ∈ range m, f' (a + k + u) := by
  have hparts := sum_integral_adjacent_intervals (μ := volume) (a := fun k : ℕ => a + k)
    (n := m) (fun k hk => by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using (hf k hk).intervalIntegrable)
  simp only [Nat.cast_zero, add_zero] at hparts
  rw [← hparts, ← sum_sub_distrib]
  simp_rw [mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun k hk => hs k (mem_range.mp hk))]
  apply sum_congr rfl
  intro k hk
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
    euler_unit_shift f f' (a + k) (hf k (mem_range.mp hk))
      (hd k (mem_range.mp hk)) (hi k (mem_range.mp hk))

example : (∑ _k ∈ range 2, (1 : ℂ)) - (∫ _x in (1 : ℝ)..3, (1 : ℂ)) =
    ∫ u in (0 : ℝ)..1, (u : ℂ) * ∑ _k ∈ range 2, (0 : ℂ) := by
  norm_num [intervalIntegral.integral_const]

/-- Page 21 local infrastructure. The centered sawtooth version of first order Euler summation. -/
theorem euler_unit_centered (f f' : ℝ → ℂ) (a : ℝ)
    (hf : ContinuousOn f (Set.uIcc a (a + 1)))
    (hd : ∀ x ∈ Set.uIcc a (a + 1), HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f' volume a (a + 1)) :
    (f a + f (a + 1)) / 2 - (∫ x in a..a + 1, f x) =
      ∫ x in a..a + 1, ((x - a - 1 / 2 : ℝ) : ℂ) * f' x := by
  have hu : ContinuousOn (fun x : ℝ => ((x - a - 1 / 2 : ℝ) : ℂ))
      (Set.uIcc a (a + 1)) := by fun_prop
  have hdu : ∀ x ∈ Set.Ioo (min a (a + 1)) (max a (a + 1)),
      HasDerivAt (fun y : ℝ => ((y - a - 1 / 2 : ℝ) : ℂ)) 1 x := by
    intro x hx
    simpa using (((hasDerivAt_id (x : ℂ)).sub_const (a : ℂ)).sub_const (1 / 2 : ℂ)).comp_ofReal
  have hh := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hf hdu
    (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume a (a + 1)) hi
  simp only [one_mul] at hh
  rw [hh]
  push_cast
  ring

#print axioms euler_unit_centered
#print axioms euler_unit_shift
#print axioms euler_sum
end LeanLab.BakerHarmanPintz1997.Decomp343a
