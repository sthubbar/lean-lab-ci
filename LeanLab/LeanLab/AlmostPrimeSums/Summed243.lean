import LeanLab.AlmostPrimeSums.Kernel243
import LeanLab.AlmostPrimeSums.Decomp243b

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
The alternate upper envelope assembly from BJS pp. 53 to 54.
Moved with its exact statement to keep the coefficient limit import acyclic.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Kernel243

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.AlmostPrimeSums.Decomp243a
open LeanLab.AlmostPrimeSums.Decomp243b
open LeanLab.AlmostPrimeSums.Prime243

noncomputable section

/-- Exact supply for sumSAq_upper using only the finite sieve application.
CONDITIONAL ON LevelBV and summed_sieve_application. The separate admitted
primeCoefficient_limit leaf is not used by this supply. -/
theorem sumSAq_upper (h : LevelBV) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ (log 6 + η) * Mchen N := by
  obtain ⟨B, C, hB, _, N₀, hN₀⟩ := summed_sieve_application h
  let a : ℕ → ℝ := fun N => idealMass N (1 / 8) * kernelEnvelope N B / 2
  have ha : Tendsto (fun N => a N / Mchen N) atTop (𝓝 (log 6)) := by
    have hh := ((idealMass_ratio (1 / 8) (by norm_num) (by norm_num)).mul
      (kernelEnvelope_limit B)).div_const 2
    have hv : 1 / (2 * exp eulerMascheroniConstant * (1 / 8)) *
        (exp eulerMascheroniConstant * log 6 / 2) / 2 = log 6 := by field_simp; ring
    rw [hv] at hh
    apply hh.congr'
    filter_upwards with N
    dsimp [a]
    ring
  apply upper_from_limits a sieveError Mchen
    (fun N => (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2)
    (log 6) C
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact Mchen_pos N hN
  · exact ha
  · exact sieveError_ratio
  · filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (2 : ℕ),
      primeCoefficient_le_envelope B hB] with N hN hN2 hcoeff hEven
    have hmass : 0 ≤ idealMass N (1 / 8) := by
      dsimp [idealMass]
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))))
        (sieveProduct_pos _ _).le
    have hm : summedMain N B ≤ a N := by
      dsimp [summedMain, a]
      gcongr
    exact (hN₀ N hEven hN).trans (by linarith [hm])

end
end LeanLab.AlmostPrimeSums.Kernel243
