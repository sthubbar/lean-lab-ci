import LeanLab.DERZ1997.Decomp576a
import LeanLab.DERZ1997.Decomp576d
import LeanLab.DERZ1997.Decomp576e

/-!
Concrete instances for the task576 supply statements.
Trudgian arXiv:1206.1844v4 pages 4 to 9.
Open analytic hypotheses remain explicit in the statement twins.
AI wrote the Lean code. Goldbach is open.
-/
open Complex Filter Topology Set
open LeanLab.DERZ1997.Decomp576a LeanLab.DERZ1997.Decomp576b
open LeanLab.DERZ1997.Decomp576c LeanLab.DERZ1997.Decomp576d LeanLab.DERZ1997.Decomp576e

example : |(1 : ℝ) + 1 / 4 - 3 / 4| * |1 + 1 / 4 - 1 / 4| ≤ (1 / 2 + 1 / 4) ^ 2 :=
  paired_distance_left576 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : |(1 : ℝ) + 1 / 4 - 3 / 2| * |1 + 1 / 4 - (-1 / 2)| ≤
    (3 / 2) ^ 2 - 3 / 2 - (1 / 4) * (1 + 1 / 4) :=
  paired_distance_right576 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : 2 * Real.log 2 ≤ Real.log ((2 : ℝ) * 1 / 1) + Real.log (2 * 1 / 1) :=
  paired_jensen_weight576 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ N : ℕ → ℕ, StrictMono N ∧
    Tendsto (fun k => (I ^ N k).re / ‖I‖ ^ N k) atTop (𝓝 1) :=
  rosser_power_sequence576 Complex.I_ne_zero

example : 0 < (1 : ℂ).re ∧ |Complex.arg 1| ≤ Real.pi / 4 :=
  near_one_arg576 (by norm_num)

example : ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (2 : ℂ) - 1‖ ≤ 2 / 3 :=
  LFunction_near_one576 _ (by norm_num)

example : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ ≠ 1 := by
  obtain ⟨e⟩ := DirichletCharacter.mulEquiv_units ℂ 3
  let χ := e.symm (-1)
  have hne : χ ≠ 1 := by
    intro hh
    have hh' := congrArg e hh
    simp only [χ, MulEquiv.apply_symm_apply, map_one] at hh'
    have hc := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hh'
    exact (by decide : (-1 : ZMod 3) ≠ 1) hc
  have hprim : χ.IsPrimitive := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp χ.conductor_dvd_level with h | h
    · exact False.elim (hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
    · exact h
  exact ⟨χ, hprim, hne⟩

example : argument576 (1 : DirichletCharacter ℂ 1) 0 = 0 := by
  unfold argument576
  simp only [neg_zero, ofReal_zero, zero_mul, sub_zero, add_zero,
    intervalIntegral.integral_same, mul_zero, zero_add]
  rw [intervalIntegral.integral_symm]
  simp

example : realPartPower576 (1 : DirichletCharacter ℂ 1) 1 0 (5 / 4 : ℂ) = 1 := by
  simp [realPartPower576]

example : ‖LSeries (1 : ℕ → ℂ) ((2 : ℂ) + I * (0 : ℝ))‖ ≤
    ∑' n : ℕ, ‖LSeries.term 1 (2 : ℂ) n‖ :=
  norm_LSeries_vertical576 (fun _ => by simp) (by norm_num) 0

example : (1 / 5 : ℝ) ≤
    ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ((5 / 4 : ℂ) + I * (0 : ℝ))‖ :=
  LFunction_quarter_lower576 _ 0
