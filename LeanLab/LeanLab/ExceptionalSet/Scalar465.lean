import LeanLab.ExceptionalSet.SPLIT_leaf_log_regime
import LeanLab.ExceptionalSet.SPLIT_leaf_sum_large_N

/-!
Exact companions for the cheapest remaining scalar admissions.
Source: P0082 page359 logarithmic parameter regime and page370 Lemma10.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Filter Topology

/-- P0082 page359, elementary logarithmic regime. Exact leaf_log_ge_one type. -/
theorem log_ge_one_supplied (N : ℕ) (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (Real.le_log_iff_exp_le hN0).mpr
  exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)

/-- P0082 page359, the ceiling step of the logarithmic regime. -/
theorem ceil_ge_one_supplied (x : ℝ) (hx : 1 ≤ x) : (1 : ℝ) ≤ (Nat.ceil x : ℝ) :=
  hx.trans (Nat.le_ceil x)

/-- P0082 page359, the ceiling error in the logarithmic regime. -/
theorem ceil_le_two_log_supplied (N : ℕ) (hN : 1 ≤ Real.log N) :
    (Nat.ceil (Real.log N) : ℝ) ≤ 2 * Real.log N := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ Real.log (N : ℝ) by linarith)
  linarith

/-- P0082 page359, elementary growth used to put logarithmic truncations
below powers of F. Exact leaf_two_log_le_rpow type. -/
theorem two_log_le_rpow_supplied (γ : ℝ) (hγ : 1 < γ) (C : ℝ) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 * Real.log N ≤ C * Real.log N ^ γ := by
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (γ - 1)) atTop atTop :=
    (tendsto_rpow_atTop (show 0 < γ - 1 by linarith)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (2 / C))
  refine ⟨max 3 N₀, fun N hN => ?_⟩
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hL : 0 < Real.log (N : ℝ) := by
    have := log_ge_one_supplied N hN3
    linarith
  have hp := hN₀ N ((le_max_right _ _).trans hN)
  rw [Real.rpow_sub_one hL.ne'] at hp
  have hm := (le_div_iff₀ hL).mp hp
  calc
    _ = C * ((2 / C) * Real.log (N : ℝ)) := by field_simp
    _ ≤ C * Real.log (N : ℝ) ^ γ := mul_le_mul_of_nonneg_left hm hC.le

/-- P0082 page370 Lemma10, scalar exponent comparison for the two order
ranges. This is the exact sealed leaf_exponent_mono statement. -/
theorem exponent_mono_supplied (cA c : ℝ) (hc : 0 < c) (hcA : c ≤ cA) (N : ℕ) (hN : 1 ≤ N)
    (k : ℕ) (hk : 0 < k) :
    (N : ℝ) ^ (1 - cA / (k : ℝ) ^ 2) ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  have h := div_le_div_of_nonneg_right hcA (show 0 ≤ (k : ℝ) ^ 2 by positivity)
  linarith

end LeanLab.ExceptionalSet.Supply465
