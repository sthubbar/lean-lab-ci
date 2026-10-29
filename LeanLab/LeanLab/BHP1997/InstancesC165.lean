/-
P0069, pages 2 and 3. Consistency checks for the new definitions.
These certificates do not prove the uniform analytic constructions.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165b
import LeanLab.BHP1997.Instances132
import LeanLab.BHP1997.MeanSquareC165

namespace LeanLab.BHP1997.InstancesC165
open Classical Complex DecompC165b

/-- Page 3, a positive modulus range with epsilon inside the required
small interval. This also checks the real exponent in Q. -/
theorem sieveQ_two_instance :
    sieveQ (0.00001 : ℝ)
      ((16 : ℝ) ^ (1 / (((11 : ℝ) / 20 + 0.00001) * (2 * (1 / 16 - 1 / 10 ^ 5))))) = 2 := by
  unfold sieveQ
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16)]
  norm_num [← Real.sqrt_eq_rpow]

/-- Page 3, conditions i and ii are consistent. The zero family has
zero density and satisfies them for every epsilon with divisor exponent 1.
The main construction requires positive density and is not proved here. -/
theorem left_conditions_zero (ε : ℝ) :
    LeftConditions ε 1 0 (fun _ _ => 0) := by
  refine ⟨?_, ⟨1, ?_⟩, ?_⟩
  · intro A hA
    refine ⟨1, ?_⟩
    intro x hx q hq hqx χ t ht
    have hx0 : 0 ≤ x := by linarith
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, zero_div, sub_zero,
      Finset.sum_const_zero, norm_zero]
    positivity
  · intro x k
    simp
  · intro A hA
    exact ⟨0, by intros; rfl⟩

/-- Page 3, conditions ii, iii and iv are consistent. The zero family
has zero density and empty exceptional character sets. The actual short
weight construction still requires density greater than 0.05. -/
theorem right_conditions_zero (ε : ℝ) :
    RightConditions ε 1 0 (fun _ _ => 0) := by
  refine ⟨⟨1, ?_⟩, ?_, ⟨fun _ _ _ => ∅, ?_⟩⟩
  · intro x k
    simp
  · intro A hA
    refine ⟨1, ?_⟩
    intro x hx q hq hqx χ t ht
    have hx0 : 0 ≤ x := by linarith
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, zero_div, sub_zero,
      Finset.sum_const_zero, norm_zero]
    positivity
  · intro A hA
    refine ⟨1, ?_⟩
    intro x hx q hq hqx
    have hx0 : 0 ≤ x := by linarith
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    constructor
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · intro z hzl hzu
      simp only [Complex.ofReal_zero, zero_mul, mul_zero, zero_div, sub_zero,
        Finset.sum_const_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
        intervalIntegral.integral_zero]
      positivity

/-- Pages 1 and 2, both new interval definitions have concrete nonempty
instances. This definition check uses epsilon 0.45 so that Y equals x. -/
theorem interval_nonempty_instance :
    (leftInterval (0.45 : ℝ) 2).Nonempty ∧
      (rightInterval (0.45 : ℝ) 2).Nonempty := by
  norm_num [leftInterval, rightInterval]

/-- Page 11, a nonempty polynomial and character instance for both
Lemma 1 Props. Its coefficient energy and polynomial value are exactly 1.
This checks hypotheses and does not assert either uniform analytic bound. -/
theorem mean_square_nonempty_instance :
    ∃ a : ℕ → ℂ, Thm4.CoeffBound a 1 ∧
      MeanSquareC165.energy a 0.25 1 2 = 1 ∧
      Thm4.dirPoly a 0.25 1 2 (1 : DirichletCharacter ℂ 1) (Thm4.half 0) = 1 ∧
      ∃ S : Finset (ℝ × DirichletCharacter ℂ 1), S.Nonempty ∧
        Thm4.WellSpaced S ∧ (∀ p ∈ S, |p.1| ≤ (3 : ℝ)) ∧
        (∀ p ∈ S, (1 / 2 : ℝ) ≤
          ‖Thm4.dirPoly a 0.25 1 2 p.2 (Thm4.half p.1)‖) := by
  let a : ℕ → ℂ := fun n => if n = 1 then 1 else 0
  have hcoeff : Thm4.CoeffBound a 1 := by
    intro n
    by_cases hn : n = 1
    · subst n
      norm_num [a]
    · simp [a, hn]
  have henergy : MeanSquareC165.energy a 0.25 1 2 = 1 := by
    norm_num [MeanSquareC165.energy, a, one_mul, Finset.sum_filter, Finset.sum_range_succ]
  have hpoly : Thm4.dirPoly a 0.25 1 2 (1 : DirichletCharacter ℂ 1) (Thm4.half 0) = 1 := by
    norm_num [Thm4.dirPoly, a, one_mul, Finset.sum_filter, Finset.sum_range_succ]
  refine ⟨a, hcoeff, henergy, hpoly, {(0, 1)}, by simp, ?_, ?_, ?_⟩
  · simp [Thm4.WellSpaced]
  · simp
  · intro p hp
    have heq : p = (0, 1) := by simpa only [Finset.mem_singleton] using hp
    subst p
    rw [hpoly]
    norm_num

end LeanLab.BHP1997.InstancesC165
