import LeanLab.AlmostPrimeSums.Base243
import LeanLab.AlmostPrimeSums.Lower243

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Supply decomposition of sumSAq_upper. The original file stays sealed.
The double remainder and finite sieve application are separated from the
weighted prime sum limit in BJS pp. 52 to 54 equations 164 to 174.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Decomp243b

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527a LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.AlmostPrimeSums.Decomp243a

noncomputable section

/-- LEAF. The moving upper sieve coefficient has its prime integral limit.
For every fixed positive B, summing F of the level parameter over q minus one
converges to exp gamma times log six divided by two.
BJS p. 54 equation 173, with logarithmic level and a vanishing level loss.
The limiting integral is chen_upper_prime_integral. This statement contains
no sifted count, no distribution hypothesis and no Chen main scale. -/
theorem primeCoefficient_limit (B : ℝ) (hB : 0 < B) :
    Tendsto (fun N : ℕ => primeCoefficient N B) atTop
      (𝓝 (exp eulerMascheroniConstant * log 6 / 2)) := by
  exact LeanLab.AlmostPrimeSums.Lower243.primeCoefficient_limit B hB

/-- LEAF. The summed finite upper sieve application before prime summation.
LevelBV supplies a positive logarithmic level and a fixed error constant.
BJS pp. 52 to 54 equations 164 to 172. The main term still contains the
moving weighted prime sum and does not state the coefficient log six. -/
theorem summed_sieve_application (h : LevelBV) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ,
      Even N → N₀ ≤ N →
      (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ summedMain N B + C * sieveError N := by
  -- The attempted conversion from the normalized upper bound failed with a type mismatch.
  -- See PROGRESS.md for the exact error and the missing analytic bridge.
  sorry

/-- The normalized summed main term has coefficient log six once the prime
coefficient limit is supplied. Derived from BJS p. 54 equations 173 to 174.
This converter has no open theorem in its proof. -/
theorem summedMain_ratio_of_primeCoefficient (B : ℝ)
    (hprime : Tendsto (fun N : ℕ => primeCoefficient N B) atTop
      (𝓝 (exp eulerMascheroniConstant * log 6 / 2))) :
    Tendsto (fun N : ℕ => summedMain N B / Mchen N) atTop (𝓝 (log 6)) := by
  have h := ((idealMass_ratio (1 / 8) (by norm_num) (by norm_num)).mul hprime).div_const 2
  have hv : 1 / (2 * exp eulerMascheroniConstant * (1 / 8)) *
      (exp eulerMascheroniConstant * log 6 / 2) / 2 = log 6 := by
    field_simp
    ring
  rw [hv] at h
  apply h.congr'
  filter_upwards with N
  dsimp [summedMain]
  ring

/-- Exact supply for the sealed sumSAq_upper statement.
CONDITIONAL ON LevelBV and the remaining summed_sieve_application leaf. -/
theorem sumSAq_upper (h : LevelBV) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ (log 6 + η) * Mchen N := by
  obtain ⟨B, C, hB, _, N₀, hN₀⟩ := summed_sieve_application h
  apply upper_from_limits (summedMain · B) sieveError Mchen
    (fun N => (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2)
    (log 6) C
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact Mchen_pos N hN
  · exact summedMain_ratio_of_primeCoefficient B (primeCoefficient_limit B hB)
  · exact sieveError_ratio
  · filter_upwards [eventually_ge_atTop N₀] with N hN hEven
    exact hN₀ N hEven hN

end
end LeanLab.AlmostPrimeSums.Decomp243b
