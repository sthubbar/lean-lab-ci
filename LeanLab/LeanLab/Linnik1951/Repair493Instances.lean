/-
P0093 equations 2.1, 2.2, 7.3 and 7.4. Concrete parameter and notation checks.
These examples do not supply GRH or either open analytic estimate.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357f

namespace LeanLab.Linnik1951

example : type_of% @lemma_three_proved357_up111 := lemma_three_decomposed111

example : representationCount111_up111 = representationCount111 := rfl
example : scale111_up111 = scale111 := rfl
example : primePowerCount111_up111 = primePowerCount111 := rfl
example : primeFourier111_up111 = primeFourier111 := rfl
example : powerFourier111_up111 = powerFourier111 := rfl
example : majorArcs280_up111 = majorArcs280 := rfl
example : exceptionalArcs280_up111 = exceptionalArcs280 := rfl
example : goodMinorArcs280_up111 = goodMinorArcs280 := rfl
example : arcContribution280_up111 = arcContribution280 := rfl
example : prime_power_fiber_equiv357_up111 = prime_power_fiber_equiv357 := rfl
example : primeSeriesSplit111 = primeFourier111 := rfl
example : powerSeriesSplit111 = powerFourier111 := rfl
example : majorArcsSplit111 = majorArcs280 := rfl
example : exceptionalArcsSplit111 = exceptionalArcs280 := rfl
example : goodMinorArcsSplit111 = goodMinorArcs280 := rfl
example : arcContributionSplit111 = arcContribution280 := rfl

example : 0 < representationCount111_up111 1 8 := by
  change 0 < representationCount111 1 8
  apply count_pos_of_representation111
  refine ⟨3, 3, by norm_num, by norm_num, fun _ => 1, ?_, ?_⟩
  · intro i
    exact le_rfl
  · norm_num

example : (1 : ℝ) / 2 > 0 ∧ (1 : ℝ) / 2 < 1 := by norm_num
example : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

end LeanLab.Linnik1951
