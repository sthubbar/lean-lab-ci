/-
Concrete nonvacuity checks for the task80 elementary lemmas.
Sources and parameter choices are recorded in STATEMENTS.md.
These examples do not supply the seven global analytic inputs.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.PrimitiveLocal
import LeanLab.Teravainen2016.ProgressionLifting
import LeanLab.Teravainen2016.DyadicApproximation
import LeanLab.Teravainen2016.VanishingLemma54

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

example : Amenable 216 443 := by
  apply inPStar_amenable (p := 443)
  · exact ⟨by decide +kernel, 1, 21, by norm_num, by norm_num⟩
  · norm_num
  · norm_num
  · norm_num

example : InfinitelyMany3AP (Set.univ : Set ℕ) := by
  apply infinitelyMany3AP_of_middle_thirds
  intro X
  refine ⟨12 * (X + 1), 5 * (X + 1), 6 * (X + 1), 7 * (X + 1),
    ?_, Set.mem_univ _, Set.mem_univ _, Set.mem_univ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try omega
  push_cast
  ring

example : ¬ (3 : ℤ) ∣ (1 : ℤ) ^ 2 + 3 ^ 2 :=
  primitive_sum_no_three_mod_four_prime (by norm_num) Nat.prime_three (by decide)

example : ¬ (4 : ℤ) ∣ (1 : ℤ) ^ 2 + 3 ^ 2 := primitive_sum_not_four_dvd (by norm_num)

example : Irrational (Real.sqrt 2) ∧ 0 < Real.sqrt 2 ∧
    (0 : ℝ) < 1 / 160 ∧ (1 : ℝ) / 160 < 1 / 80 := by
  exact ⟨irrational_sqrt_two, Real.sqrt_pos.mpr (by norm_num), by norm_num, by norm_num⟩

example : max 1 (1 : ℕ) ≤ 2 ∧ 2 ≤ (3 : ℕ) ∧ 3 ≤ 2 * (2 : ℕ) ∧ InP 3 ∧
    distInt ((0 : ℝ) * 3 + 0) ≤ (2 : ℝ) ^ (-(0 : ℝ)) / 2 := by
  refine ⟨by decide, by decide, by decide, ⟨Nat.prime_three, 1, 1, by norm_num⟩, ?_⟩
  norm_num [distInt]

example : ‖integerSieveSum 15 1 1 0 1‖ ≤ 4 := by
  have h := integerSieveSum_norm_le_divisors 15 1 1 0 1 (by decide)
  have hc : (Nat.divisors 15).card = 4 := by decide
  simpa only [hc, Nat.cast_ofNat] using h

example : IsUnit (1 : ZMod 15) ∧ Nat.Coprime 3 5 ∧ 1 < (3 : ℕ) ∧ 1 < (5 : ℕ) :=
  ⟨isUnit_one, by decide, by decide, by decide⟩

end LeanLab.Teravainen2016
