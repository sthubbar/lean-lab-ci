/-
P0069 page 21, concrete nonempty instances for every task343 supply declaration.
These are source and hypothesis checks requested by the lab rules.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Principal343

namespace LeanLab.BakerHarmanPintz1997.Instances343
open Finset MeasureTheory intervalIntegral Decomp343a Decomp343b Decomp343c Principal343
attribute [local instance] Classical.propDecidable

-- Euler unit, translated unit, and two consecutive cells for a nonconstant polynomial.
example : (((1 : ℝ) + 1 : ℝ) : ℂ) ^ 2 - (∫ x in (1 : ℝ)..(1 + 1), (x : ℂ) ^ 2) =
    ∫ x in (1 : ℝ)..(1 + 1), ((x - 1 : ℝ) : ℂ) * (2 * (x : ℂ)) := by
  apply euler_unit (fun x : ℝ => (x : ℂ) ^ 2) (fun x => 2 * (x : ℂ)) 1
  · fun_prop
  · intro x hx
    simpa using ((hasDerivAt_id (x : ℂ)).pow 2).comp_ofReal
  · apply Continuous.intervalIntegrable
    fun_prop

example : (((1 : ℝ) + 1 : ℝ) : ℂ) ^ 2 - (∫ x in (1 : ℝ)..(1 + 1), (x : ℂ) ^ 2) =
    ∫ u in (0 : ℝ)..1, (u : ℂ) * (2 * ((1 + u : ℝ) : ℂ)) := by
  apply euler_unit_shift (fun x : ℝ => (x : ℂ) ^ 2) (fun x => 2 * (x : ℂ)) 1
  · fun_prop
  · intro x hx
    simpa using ((hasDerivAt_id (x : ℂ)).pow 2).comp_ofReal
  · apply Continuous.intervalIntegrable
    fun_prop

example : (∑ k ∈ range 2, (((1 : ℝ) + k + 1 : ℝ) : ℂ) ^ 2) -
    (∫ x in (1 : ℝ)..(1 + (2 : ℕ)), (x : ℂ) ^ 2) =
    ∫ u in (0 : ℝ)..1, (u : ℂ) * ∑ k ∈ range 2, 2 * (((1 : ℝ) + k + u : ℝ) : ℂ) := by
  apply euler_sum (fun x : ℝ => (x : ℂ) ^ 2) (fun x => 2 * (x : ℂ)) 1 2
  · intro k hk; fun_prop
  · intro k hk x hx
    simpa using ((hasDerivAt_id (x : ℂ)).pow 2).comp_ofReal
  · intro k hk
    apply Continuous.intervalIntegrable
    fun_prop
  · intro k hk
    apply Continuous.intervalIntegrable
    fun_prop

example : (∑ k ∈ range 2, (k : ℂ)) = ∑ k ∈ Icc (0 : ℤ) 1, (k : ℂ) := by
  simpa using range_eq_int_sum (fun x : ℝ => (x : ℂ)) 1

-- Negative frequency at the nonresonant boundary and a noninteger cell shift.
example : ‖∑ k ∈ range 2, ((4 : ℝ) + k + 1 : ℂ) ^ (-(1 : ℂ) * Complex.I)‖ ≤
    8 * Real.pi * 4 / |(1 : ℝ)| :=
  shifted_phase_sum 4 2 (by norm_num) (by norm_num) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (4 : ℂ) ^ (((-3 / 2 : ℝ) : ℂ) - (1 : ℂ) * Complex.I) =
    ((4 : ℝ) ^ (-3 / 2 : ℝ)) • (4 : ℂ) ^ (-(1 : ℂ) * Complex.I) :=
  cpow_amplitude_phase (by norm_num : (0 : ℝ) < 4) (-3 / 2) 1

example : ‖∑ k ∈ range 2, ((4 : ℝ) + k + (1 / 2 : ℝ) : ℂ) ^
    (((-3 / 2 : ℝ) : ℂ) - (1 : ℂ) * Complex.I)‖ ≤
    (4 : ℝ) ^ (-3 / 2 : ℝ) * (8 * Real.pi * 4 / |(1 : ℝ)|) := by
  apply weighted_shifted_phase_sum 4 2 (by norm_num) (1 / 2) (-3 / 2) 1
    (8 * Real.pi * 4 / |(1 : ℝ)|) (by norm_num) (by norm_num) (by positivity)
  intro k hk
  have hm : k ≤ 4 := by omega
  simpa only [Nat.cast_ofNat] using shifted_phase_sum 4 k (by norm_num) hm (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ‖∑ k ∈ range 2, ((1 : ℝ) + k + 0 : ℂ) ^ (-(0 : ℂ) * Complex.I)‖ ≤ 2 :=
  by
    have h := shifted_phase_trivial 1 2 (by norm_num) 0 0 (by norm_num)
    norm_num at h ⊢

example : critical 1 1 = 1 := by simp [critical]
example : criticalDeriv 0 1 = (-1 / 2 : ℂ) := by norm_num [criticalDeriv]
example : HasDerivAt (critical 1) (criticalDeriv 1 1) 1 :=
  critical_hasDerivAt 1 (by norm_num)
example : ‖critical 1 1‖ = (1 : ℝ) ^ (-1 / 2 : ℝ) :=
  critical_norm 1 (by norm_num)
example : ContinuousAt (criticalDeriv 1) 1 := criticalDeriv_continuousAt 1 (by norm_num)

example : ‖∑ k ∈ range 2, criticalDeriv (-4) ((4 : ℝ) + k + (1 / 2 : ℝ))‖ ≤
    64 * (4 : ℝ) ^ (-1 / 2 : ℝ) :=
  shifted_derivative_sum 4 2 (by norm_num) (by norm_num) (1 / 2) (-4)
    (by norm_num) (by norm_num) (by norm_num)

example : (∑ k ∈ range 2, critical 1 ((4 : ℝ) + k + 1)) -
    (∫ y in (4 : ℝ)..6, critical 1 y) =
    ∫ u in (0 : ℝ)..1, (u : ℂ) * ∑ k ∈ range 2, criticalDeriv 1 ((4 : ℝ) + k + u) := by
  simpa only [Nat.cast_ofNat, show (4 : ℝ) + 2 = 6 by norm_num] using critical_euler 4 2 (by norm_num) 1

example : ‖(∑ k ∈ range 2, critical 1 ((4 : ℝ) + k + 1)) -
    (∫ y in (4 : ℝ)..6, critical 1 y)‖ ≤ 64 * (4 : ℝ) ^ (-1 / 2 : ℝ) := by
  simpa only [Nat.cast_ofNat, show (4 : ℝ) + 2 = 6 by norm_num] using integer_discretization 4 2 (by norm_num) (by norm_num) 1 (by norm_num)

example : IntervalIntegrable (critical 1) volume (1 : ℝ) 2 :=
  critical_intervalIntegrable 1 (by norm_num) (by norm_num)
example : ‖∫ y in (1 : ℝ)..2, critical 1 y‖ ≤ (1 : ℝ) ^ (-1 / 2 : ℝ) :=
  short_critical_integral 1 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : (∑ n ∈ Ioc 1 3, (1 : ℂ)) = ∑ k ∈ range 2, (1 : ℂ) := by
  simpa using sum_right_cells (fun _ => (1 : ℂ)) 1 2
example : critical 1 1 = (1 : ℂ) ^ (-1 / 2 : ℂ) * (1 : ℂ) ^ (-(1 : ℂ) * Complex.I) :=
  critical_eq_product 1 (by norm_num)
example : ‖(∑ n ∈ Ioc ⌊(3 / 2 : ℝ)⌋₊ ⌊(5 / 2 : ℝ)⌋₊, critical (-3 / 2) n) -
    (∫ y in (3 / 2 : ℝ)..(5 / 2), critical (-3 / 2) y)‖ ≤
    67 * (3 / 2 : ℝ) ^ (-1 / 2 : ℝ) :=
  real_discretization (3 / 2) (5 / 2) (-3 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- The exact sealed interface is supplied without calling its original placeholder.
example :
  ∃ C_disc : ℝ, 0 ≤ C_disc ∧ ∀ N N1 : ℝ, 1 ≤ N → N ≤ N1 → N1 ≤ 2 * N → ∀ t : ℝ, |t| ≤ N →
  ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ) -
    ∫ y in N..N1, (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
  ≤ C_disc * (N : ℝ) ^ (-1 / 2 : ℝ) := Decomp343c.fgm_discretization_error

example : ((1 : ℂ) ^ 2 + (((1 : ℝ) + 1 : ℝ) : ℂ) ^ 2) / 2 -
    (∫ x in (1 : ℝ)..(1 + 1), (x : ℂ) ^ 2) =
    ∫ x in (1 : ℝ)..(1 + 1), ((x - 1 - 1 / 2 : ℝ) : ℂ) * (2 * (x : ℂ)) := by
  apply euler_unit_centered (fun x : ℝ => (x : ℂ) ^ 2) (fun x => 2 * (x : ℂ)) 1
  · fun_prop
  · intro x hx
    simpa using ((hasDerivAt_id (x : ℂ)).pow 2).comp_ofReal
  · apply Continuous.intervalIntegrable
    fun_prop

example : ‖criticalDeriv 1 1‖ =
    ‖(-1 / 2 : ℂ) - (1 : ℂ) * Complex.I‖ * (1 : ℝ) ^ (-3 / 2 : ℝ) :=
  criticalDeriv_norm 1 (by norm_num)

example : ‖∑ n ∈ Ioc ⌊(4 : ℝ)⌋₊ ⌊(8 : ℝ)⌋₊, critical 4 n‖ ≤
    67 * (4 : ℝ) ^ (-1 / 2 : ℝ) + 5 * (4 : ℝ) ^ (1 / 2 : ℝ) / (1 + |(4 : ℝ)|) :=
  principal_nonresonant_bound 4 8 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ‖∑ n ∈ Ioc ⌊(4 : ℝ)⌋₊ ⌊(8 : ℝ)⌋₊, critical 4 n‖ ≤
    77 * (4 : ℝ) ^ (-1 / 2 : ℝ) :=
  principal_upper_frequency_bound 4 8 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ((8 : ℝ) / 4) * (8 : ℝ) ^ (-1 / 2 : ℝ) ≤
    ∫ y in (8 : ℝ)..(2 * 8), ‖criticalDeriv 8 y‖ :=
  absolute_derivative_budget_lower 8 (by norm_num)

example : ¬ ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N → ∀ t : ℝ, |t| ≤ N →
    (∫ y in N..2 * N, ‖criticalDeriv t y‖) ≤ C * N ^ (-1 / 2 : ℝ) :=
  absolute_derivative_budget_not_uniform

end LeanLab.BakerHarmanPintz1997.Instances343
