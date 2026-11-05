/-
A weaker numerical tail bound from page 14 display 47.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp342f

namespace LeanLab.KumchevLiu2007.Task342g

open Task129b Task292a Task292c
open scoped BigOperators

/-- Page 14 below display 50. Dropping smooth support gives only a finite power sum bound. -/
theorem smooth_tail_power_majorant (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ T Q : ℝ,
      (∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q),
        smoothWeight q Q * (localMajorant q / (q : ℝ))) ≤
      K * ∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q), (q : ℝ) ^ (ε - 1) := by
  obtain ⟨K, hK, hb⟩ := Task342b.localMajorant_power_bound ε hε
  refine ⟨K, hK, ?_⟩
  intro T Q
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hmaj0 : 0 ≤ localMajorant q := Finset.prod_nonneg (fun p hp => by positivity)
  have hw : smoothWeight q Q ≤ 1 := by unfold smoothWeight; split <;> norm_num
  calc
    _ ≤ localMajorant q / (q : ℝ) := mul_le_of_le_one_left (by positivity) hw
    _ ≤ K * (q : ℝ) ^ ε / (q : ℝ) := div_le_div_of_nonneg_right (hb q hqpos) hqR.le
    _ = K * (q : ℝ) ^ (ε - 1) := by rw [Real.rpow_sub hqR, Real.rpow_one]; ring

/-- Page 14 smooth tail argument. The majorant obtained by dropping smooth support is not summable. -/
theorem power_majorant_not_summable (ε : ℝ) (hε : 0 < ε) :
    ¬ Summable (fun q : ℕ => (q : ℝ) ^ (ε - 1)) := by
  rw [Real.summable_nat_rpow]
  linarith

end LeanLab.KumchevLiu2007.Task342g
