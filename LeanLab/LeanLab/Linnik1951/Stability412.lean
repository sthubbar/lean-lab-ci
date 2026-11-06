/-
P0093 page 165 proof of Lemma 5. Local stability of the damped power series.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Instances376

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 165 proof of Lemma 5, differentiation of the damped
series. The first frequency moment converges absolutely for positive N. -/
theorem weighted_power_summable412 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun m : ℕ => ((2 ^ (m + 1) : ℕ) : ℝ) *
      Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs := Real.summable_pow_mul_exp_neg_nat_mul 1 (r := 1 / (N : ℝ)) (by positivity)
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
  apply (hs.comp_injective hi).congr
  intro m
  simp only [Function.comp_apply, pow_one]
  congr 2
  ring

/-- P0093 page 165 proof of Lemma 5, the uniform derivative majorant.
Split the dyadic first moment at the integer logarithm of N. The initial
geometric sum is at most two N and the tail is at most eight N. -/
theorem weighted_power_bound412 (N : ℕ) (hN : 1 ≤ N) :
    (∑' m : ℕ, ((2 ^ (m + 1) : ℕ) : ℝ) *
      Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)) ≤ 10 * N := by
  let a : ℕ → ℝ := fun m => ((2 ^ (m + 1) : ℕ) : ℝ) *
    Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let L := Nat.log 2 N
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha : Summable a := weighted_power_summable412 N hN
  have hlow : (2 : ℝ) ^ L ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  have hupp : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N).le
  have hcap : (2 : ℝ) ^ (L + 1) ≤ 2 * N := by rw [pow_succ]; linarith
  have hhead : ∑ j ∈ range L, a j ≤ 2 * N := by
    have hgeom (l : ℕ) : ∑ j ∈ range l, (2 : ℝ) ^ (j + 1) = 2 ^ (l + 1) - 2 := by
      induction l with
      | zero => norm_num
      | succ l ih => rw [sum_range_succ, ih, pow_succ (2 : ℝ) (l + 1)]; ring
    calc
      _ ≤ ∑ j ∈ range L, (2 : ℝ) ^ (j + 1) := by
        apply sum_le_sum
        intro j hj
        dsimp [a]
        push_cast
        exact mul_le_of_le_one_right (by positivity)
          (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hNp.le))
      _ = 2 ^ (L + 1) - 2 := hgeom L
      _ ≤ _ := by linarith
  have htail (j : ℕ) : a (j + L) ≤ 4 * N * (1 / 2 : ℝ) ^ j := by
    have hratio : (2 : ℝ) ^ j ≤ ((2 ^ (j + L + 1) : ℕ) : ℝ) / N := by
      apply (le_div_iff₀ hNp).mpr
      push_cast
      rw [show j + L + 1 = j + (L + 1) by omega, pow_add]
      exact mul_le_mul_of_nonneg_left hupp (by positivity)
    have he : ((2 : ℝ) ^ j) ^ 2 / 2 ≤ Real.exp ((2 : ℝ) ^ j) := by
      have h := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ j)
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
    have hx : (0 : ℝ) < 2 ^ j := by positivity
    have hi : (2 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j)) ≤ 2 * (1 / 2 : ℝ) ^ j := by
      calc
        _ = (2 : ℝ) ^ j / Real.exp ((2 : ℝ) ^ j) := by rw [Real.exp_neg]; ring
        _ ≤ 2 / (2 : ℝ) ^ j :=
          (div_le_div_iff₀ (Real.exp_pos _) hx).mpr (by nlinarith)
        _ = _ := by rw [one_div_pow]; ring
    calc
      a (j + L) ≤ ((2 ^ (j + L + 1) : ℕ) : ℝ) * Real.exp (-((2 : ℝ) ^ j)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (by rw [neg_div]; exact neg_le_neg hratio)
      _ = (2 : ℝ) ^ (L + 1) * ((2 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j))) := by
        push_cast
        rw [show j + L + 1 = (L + 1) + j by omega, pow_add]
        ring
      _ ≤ (2 * N) * (2 * (1 / 2 : ℝ) ^ j) := mul_le_mul hcap hi (by positivity) (by positivity)
      _ = _ := by ring
  have htailSum : (∑' j : ℕ, a (j + L)) ≤ 8 * N := by
    have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (4 * (N : ℝ))
    calc
      _ ≤ ∑' j : ℕ, 4 * (N : ℝ) * (1 / 2 : ℝ) ^ j :=
        Summable.tsum_le_tsum htail (ha.comp_injective (add_left_injective L)) hg
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  change (∑' m, a m) ≤ _
  rw [← ha.sum_add_tsum_nat_add L]
  linarith

end LeanLab.Linnik1951
