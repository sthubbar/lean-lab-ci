import LeanLab.Ricci1937.Decomp338u

/-!
Ricci 1937, shifted mixed endpoint power estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary shifted cutoff power from the mixed mass estimate.
First memoir page 89 cases two and three, and second memoir page 115 after formulas 31.3 and 31.4.
The high logarithmic mass contributes the additional positive shift omega. -/
lemma decomp338_mixed_block_cutoff_upper (h y v w t : ℕ) (θ ε ω : ℝ)
    (hy : 2 ≤ y) (hyv : y ≤ v) (hvw : v ≤ w) (hwt : w ≤ t)
    (hmass : θ - ε ≤ ∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p)
    (hend : 28 / Real.log y + 14 / Real.log v ≤ ε)
    (hshift : ω ≤ Real.log (Real.log w / Real.log v)) :
    (y : ℝ) ≤ (w : ℝ) ^ Real.exp (-(θ + ω) / 2 + ε) := by
  have hyw : y ≤ w := hyv.trans hvw
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
  have hmain := decomp338_mixed_mass_upper h y v w t hy hyv hvw hwt
  have hlv : 0 < Real.log v := Real.log_pos (by exact_mod_cast (by omega : 1 < v))
  have hlogs :
      2 * Real.log (Real.log v / Real.log y) + Real.log (Real.log w / Real.log v) =
        2 * Real.log (Real.log w / Real.log y) - Real.log (Real.log w / Real.log v) := by
    simp only [Real.log_div hlv.ne' hly.ne', Real.log_div hlw.ne' hlv.ne',
      Real.log_div hlw.ne' hly.ne']
    ring
  rw [hlogs] at hmain
  have hl : (θ + ω) / 2 - ε ≤ Real.log (Real.log w / Real.log y) := by linarith
  have hexp : Real.exp ((θ + ω) / 2 - ε) ≤ Real.log w / Real.log y := by
    simpa only [Real.exp_log (div_pos hlw hly)] using Real.exp_le_exp.mpr hl
  have hm := (le_div_iff₀ hly).mp hexp
  have hm' := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-(θ + ω) / 2 + ε)).le
  have he : Real.exp (-(θ + ω) / 2 + ε) * Real.exp ((θ + ω) / 2 - ε) = 1 := by
    rw [← Real.exp_add]
    rw [show (-(θ + ω) / 2 + ε) + ((θ + ω) / 2 - ε) = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, he, one_mul] at hm'
  apply (Real.log_le_log_iff hyR (Real.rpow_pos_of_pos hwR _)).mp
  rwa [Real.log_rpow hwR]

/-- Auxiliary actual shifted first endpoint bound for first memoir page 89 cases two and three.
Second memoir page 115, the unnumbered display referring to formulas 31.3 and 31.4.
The shift is retained in the first exponent rather than discarded by a dimension two bound. -/
lemma decomp338_mixed_first_power_max (h Y v t : ℕ) (hY : 4 ≤ Y)
    (hYv : Y ≤ v) (hvt : v ≤ t) (ε ω : ℝ)
    (hhigh : (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 0.90)
    (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 42 / Real.log y ≤ ε)
    (hshift : ω ≤ Real.log (Real.log t / Real.log v)) :
    (decomp338GreedyCutoff (decomp338EncodedGap h v t) Y t 0 : ℝ) ≤
      max (Y : ℝ) ((t : ℝ) ^ exp (-(0.90 + ω) / 2 + ε)) := by
  let H := decomp338EncodedGap h v t
  let y := decomp338GreedyStep H Y t 0
  obtain ⟨hyY, hyt, hmass⟩ := decomp338_greedy_step_bounds H Y t 0 (hYv.trans hvt)
  have hyv : y ≤ v := decomp338_mixed_first_cutoff_le h Y v t hYv hvt hhigh
  change (y : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ exp (-(0.90 + ω) / 2 + ε))
  by_cases heq : y = Y
  · rw [heq]
    exact le_max_left _ _
  · have hyY' : Y < y := by omega
    have hm := decomp338_greedy_step_mass_lower H Y t 0 (hYv.trans hvt) hyY'
    have herr := hsmall y hyY
    have hlo : 0.90 - ε ≤ ∑ p ∈ (Ioc y t).filter Nat.Prime, nuN H p := by
      norm_num [decomp305HeadMass] at hm
      linarith
    have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
    have hlog : Real.log y ≤ Real.log v :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast hyv)
    have hdiv : 14 / Real.log v ≤ 14 / Real.log y :=
      div_le_div_of_nonneg_left (by norm_num) hly hlog
    have hend : 28 / Real.log y + 14 / Real.log v ≤ ε := by
      have he : 28 / Real.log y + 14 / Real.log y = 42 / Real.log y := by ring
      linarith
    have hp := decomp338_mixed_block_cutoff_upper h y v t t 0.90 ε ω
      (by omega) hyv hvt le_rfl hlo hend hshift
    exact hp.trans (le_max_right _ _)

end
end LeanLab.Ricci1937
