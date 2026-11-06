import LeanLab.Ricci1937.Decomp338ab

/-!
Ricci 1937, the first dimension one mixed block.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary dimension one block power for first memoir page 89 case four.
Second memoir page 115, the mixed variant of formulas 31.3 and 31.4. -/
lemma decomp338_one_dimensional_cutoff_upper (y w : ℕ) (θ ε : ℝ)
    (hy : 2 ≤ y) (hyw : y ≤ w)
    (hmass : θ - ε ≤ ∑ p ∈ (Ioc y w).filter Nat.Prime, (1 : ℝ) / p)
    (hend : 14 / Real.log y ≤ ε) :
    (y : ℝ) ≤ (w : ℝ) ^ Real.exp (-θ + 2 * ε) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
  have hmain := decompJ365_prime_block_upper y w hy hyw
  have hl : θ - 2 * ε ≤ Real.log (Real.log w / Real.log y) := by linarith
  have hexp : Real.exp (θ - 2 * ε) ≤ Real.log w / Real.log y := by
    simpa only [Real.exp_log (div_pos hlw hly)] using Real.exp_le_exp.mpr hl
  have hm := (le_div_iff₀ hly).mp hexp
  have hm' := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-θ + 2 * ε)).le
  have he : Real.exp (-θ + 2 * ε) * Real.exp (θ - 2 * ε) = 1 := by
    rw [← Real.exp_add]
    rw [show (-θ + 2 * ε) + (θ - 2 * ε) = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, he, one_mul] at hm'
  apply (Real.log_le_log_iff hyR (Real.rpow_pos_of_pos hwR _)).mp
  rwa [Real.log_rpow hwR]


/-- Auxiliary actual first endpoint power for first memoir page 89 case four.
Below v the trivial v bound suffices. Above v the block has dimension one.
Second memoir page 115, mixed variant after 31.3 and 31.4. -/
lemma decomp338_case_four_first_power (h Y v t : ℕ) (hY : 4 ≤ Y)
    (hYv : Y ≤ v) (hvt : v ≤ t) (hvpow : (v : ℝ) ≤ (t : ℝ) ^ (1 / 4 : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 14 / Real.log y ≤ ε) :
    (decomp338GreedyCutoff (decomp338EncodedGap h v t) Y t 0 : ℝ) ≤
      max (Y : ℝ) ((t : ℝ) ^ exp (-0.90 + 2 * ε)) := by
  let H := decomp338EncodedGap h v t
  let y := decomp338GreedyCutoff H Y t 0
  obtain ⟨hyY, hyt, _⟩ := decomp338_greedy_step_bounds H Y t 0 (hYv.trans hvt)
  change (y : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ exp (-0.90 + 2 * ε))
  by_cases hyv : y ≤ v
  · have hexp : (1 / 4 : ℝ) ≤ exp (-0.90 + 2 * ε) := by
      have h4 : exp (0.90 : ℝ) ≤ 4 := (exp_le_exp.mpr (by norm_num : (0.90 : ℝ) ≤ 1)).trans
        (by linarith [exp_one_lt_d9])
      have hh : (1 / 4 : ℝ) ≤ exp (-0.90 : ℝ) := by
        rw [exp_neg]
        simpa using inv_anti₀ (exp_pos (0.90 : ℝ)) h4
      exact hh.trans (exp_le_exp.mpr (by linarith))
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
    exact (le_trans (by exact_mod_cast hyv) (hvpow.trans
      (Real.rpow_le_rpow_of_exponent_le ht1 hexp))).trans (le_max_right _ _)
  · have hvy : v < y := by omega
    have hm := decomp338_greedy_step_mass_lower H Y t 0 (hYv.trans hvt) (hYv.trans_lt hvy)
    change (decomp305HeadMass 0 : ℝ) / 100 - 2 / (y : ℝ) <
      ∑ p ∈ (Ioc y t).filter Nat.Prime, nuN H p at hm
    rw [decomp338_mixed_high_block h y t v t hvy.le le_rfl] at hm
    have herr := hsmall y hyY
    have hlo : 0.90 - ε ≤ ∑ p ∈ (Ioc y t).filter Nat.Prime, (1 : ℝ) / p := by
      have heq : (decomp305HeadMass 0 : ℝ) / 100 = 0.90 := by norm_num [decomp305HeadMass]
      rw [heq] at hm
      linarith
    exact (decomp338_one_dimensional_cutoff_upper y t 0.90 ε (by omega) hyt hlo herr.2).trans
      (le_max_right _ _)

end
end LeanLab.Ricci1937
