/-
Source route diagnostic for P0069 page 22 Lemma 7.
Ramachandra 1974 page 88 Theorem 6 retains exp of square root log q at k = 2.
https://www.numdam.org/item/ASNSP_1974_4_1_1-2_81_0/
This file shows that this extra factor cannot be absorbed into a fixed log power.
It does not refute Lemma 7 or assert a paper error.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LeanLab.BakerHarmanPintz1997.Source409
open Filter Topology

/-- Page 88 source route diagnostic. At arbitrarily large natural moduli the extra
exponential square root log factor exceeds every prescribed constant log power. -/
theorem extra_factor_exceeds_log_power (B C : ℝ) (N : ℕ) :
    ∃ q : ℕ, max 2 N ≤ q ∧
      C * Real.log q ^ B < Real.exp (Real.sqrt (Real.log q)) := by
  have hroot : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hlim := (tendsto_exp_div_rpow_atTop (2 * B)).comp hroot
  have hreal : Tendsto (fun x : ℝ => Real.exp (Real.sqrt (Real.log x)) / Real.log x ^ B)
      atTop atTop := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hp : (Real.sqrt (Real.log x)) ^ (2 * B) = Real.log x ^ B := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Real.log_nonneg hx)]
      congr 1
      ring
    simp only [Function.comp_apply, hp]
  have hnat : Tendsto (fun q : ℕ => Real.exp (Real.sqrt (Real.log q)) / Real.log q ^ B)
      atTop atTop := hreal.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ q : ℕ in atTop, max 2 N ≤ q ∧
      C * Real.log q ^ B < Real.exp (Real.sqrt (Real.log q)) := by
    filter_upwards [eventually_ge_atTop (max 2 N), hnat.eventually_gt_atTop C] with q hq hb
    refine ⟨hq, ?_⟩
    have hq2 : 2 ≤ q := (le_max_left _ _).trans hq
    have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
    exact (lt_div_iff₀ (Real.rpow_pos_of_pos (Real.log_pos hq1) B)).mp hb
  exact he.exists

/-- Page 88 source route diagnostic. No fixed power of log bounds the extra factor,
even when restricted to natural moduli and an arbitrary eventual threshold. -/
theorem extra_factor_not_logarithmic :
    ¬ ∃ B C : ℝ, ∃ N : ℕ, ∀ q : ℕ, 2 ≤ q → N ≤ q →
      Real.exp (Real.sqrt (Real.log q)) ≤ C * Real.log q ^ B := by
  rintro ⟨B, C, N, h⟩
  obtain ⟨q, hq, hbad⟩ := extra_factor_exceeds_log_power B C N
  have hh := h q ((le_max_left _ _).trans hq) ((le_max_right _ _).trans hq)
  linarith

#print axioms extra_factor_exceeds_log_power
#print axioms extra_factor_not_logarithmic

end LeanLab.BakerHarmanPintz1997.Source409
