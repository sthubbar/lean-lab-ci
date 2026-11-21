/-
P0069 Baker Harman Pintz 1997, page 7 display 2.5.
The modulus summation bookkeeping is valid when the interval length is at least one.
The unrestricted sealed helper remains unchanged.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
namespace LeanLab.BHP1997.Task670SummationGrowth
open scoped BigOperators
/-- The page 7 modulus bookkeeping with an explicit growing length condition.
This auxiliary bound applies to any complex modulus terms with the stated budgets. -/
theorem short_modulus_summation_of_length (a : ℕ → ℂ) {x D A C B Y : ℝ}
    (hx : 3 ≤ x) (hB : 0 ≤ B) (hY : 1 ≤ Y)
    (hterm : ∀ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
      ‖a q‖ ≤ C * Real.log x ^ (-(A + 6 * D + 3)) *
        (Real.log x ^ (4 * D) / ((q : ℝ) * Y)) * B) :
    ‖∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, a q‖ ≤
      max 1 C * Real.log x ^ (-A) * B := by
  let L : ℝ := Real.log x
  let M : ℝ := max 1 C
  let K : ℝ := M * L ^ (-(A + 6 * D + 3)) * L ^ (4 * D) * B
  have hL1 : 1 ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx
    dsimp [L]; linarith [Real.log_three_gt_d9]
  have hL : 0 < L := by linarith
  have hM : 0 ≤ M := le_trans (by norm_num) (le_max_left _ _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq (q : ℕ) (hq : q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊) : ‖a q‖ ≤ K := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    have hd : 1 ≤ (q : ℝ) * Y := by nlinarith
    have hw : L ^ (4 * D) / ((q : ℝ) * Y) ≤ L ^ (4 * D) :=
      div_le_self (Real.rpow_nonneg hL.le _) hd
    calc
      _ ≤ C * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / ((q : ℝ) * Y)) * B := hterm q hq
      _ ≤ M * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / ((q : ℝ) * Y)) * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_max_right 1 C) (by positivity)
      _ ≤ K := by dsimp [K]; gcongr
  have hc : ((Finset.Icc 1 ⌊L ^ (2 * D)⌋₊).card : ℝ) ≤ L ^ (2 * D) := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Nat.floor_le (Real.rpow_nonneg hL.le (2 * D))
  have hp : L ^ (2 * D) * L ^ (-(A + 6 * D + 3)) * L ^ (4 * D) =
      L ^ (-A) * L ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL]
    congr 1
    ring
  have hs : L ^ (-3 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊, K := norm_sum_le_of_le _ hq
    _ = ((Finset.Icc 1 ⌊L ^ (2 * D)⌋₊).card : ℝ) * K := by simp
    _ ≤ L ^ (2 * D) * K := mul_le_mul_of_nonneg_right hc hK
    _ = M * L ^ (-A) * L ^ (-3 : ℝ) * B := by dsimp [K]; calc
      _ = M * (L ^ (2 * D) * L ^ (-(A + 6 * D + 3)) * L ^ (4 * D)) * B := by ring
      _ = _ := by rw [hp]; ring
    _ ≤ _ := by dsimp [M, L]; nlinarith [mul_nonneg hM (Real.rpow_nonneg hL.le (-A)), mul_le_mul_of_nonneg_right hs (mul_nonneg (mul_nonneg hM (Real.rpow_nonneg hL.le (-A))) hB)]
end LeanLab.BHP1997.Task670SummationGrowth
