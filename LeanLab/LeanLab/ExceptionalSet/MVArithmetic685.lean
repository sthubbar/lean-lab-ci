import LeanLab.Perelli1996.NairPrep103
import LeanLab.HeathBrown1985.DivisorEps
/-!
Task685. The uniform divisor weight absorption used in Montgomery and Vaughan
1975, page 363 displays 6.13 and 6.14. The threshold depends on the positive
exponent. The divisor bound is supplied by HeathBrown1985.DivisorEps and the
totient comparison by Perelli1996.NairPrep103.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Task685
open Real Filter
open scoped Topology
set_option maxHeartbeats 100000
/-- The weight n times the divisor count divided by the totient is at most X to delta eventually. -/
theorem divisor_weight_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      (n : ℝ) * n.divisors.card / n.totient ≤ X ^ δ := by
  obtain ⟨k, hk⟩ := exists_nat_gt (4 / δ)
  have hk1 : 1 ≤ k := by
    have : (0 : ℝ) < (k : ℝ) := lt_trans (by positivity) hk
    exact_mod_cast (show 0 < k from by exact_mod_cast this)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have he : (k : ℝ)⁻¹ * 2 ≤ δ / 2 := by
    have hh : 4 < (k : ℝ) * δ := (div_lt_iff₀ hδ).mp hk
    have hi : (k : ℝ) * (k : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hkR.ne'
    nlinarith
  obtain ⟨C, hC, hb⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk1
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0 : ℝ) < δ / 2 by positivity)).eventually_ge_atTop (C ^ 2))
  refine ⟨max X₀ 1, fun X hX n hn hnX => ?_⟩
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hCb : C ^ 2 ≤ X ^ (δ / 2) := hX₀ X ((le_max_left _ _).trans hX)
  calc
    (n : ℝ) * n.divisors.card / n.totient ≤ (n.divisors.card : ℝ) ^ 2 :=
      LeanLab.Perelli1996.Nair103.weight_le_tau_sq n
    _ ≤ (C * (n : ℝ) ^ ((k : ℝ)⁻¹)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) (hb n hn) 2
    _ = C ^ 2 * (n : ℝ) ^ ((k : ℝ)⁻¹ * 2) := by
      rw [mul_pow]
      congr 1
      exact (Real.rpow_mul_natCast (Nat.cast_nonneg n) ((k : ℝ)⁻¹) 2).symm
    _ ≤ C ^ 2 * X ^ (δ / 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      exact (Real.rpow_le_rpow_of_exponent_le hn1 he).trans
        (Real.rpow_le_rpow (Nat.cast_nonneg n) hnX (by positivity))
    _ ≤ X ^ (δ / 2) * X ^ (δ / 2) :=
      mul_le_mul_of_nonneg_right hCb (by positivity)
    _ = X ^ δ := by rw [← Real.rpow_add hXp]; congr 1; ring

end LeanLab.ExceptionalSet.Task685
