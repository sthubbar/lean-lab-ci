import LeanLab.AlmostPrimeSums.Instances243
import LeanLab.AlmostPrimeSums.Kernel243
import LeanLab.AlmostPrimeSums.Summed243
import LeanLab.AlmostPrimeSums.Double243

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Nonempty source domains for the prime and double kernel calculations.
-/

open Finset Real Filter Topology
open LeanLab.ChenExplicit.D1552
open LeanLab.AlmostPrimeSums.Decomp1527c LeanLab.AlmostPrimeSums.Decomp243b
open LeanLab.AlmostPrimeSums.Prime243 LeanLab.AlmostPrimeSums.Abel243

#check (prime_endpoint_error 3 7 (by norm_num) (by norm_num))
#check (prime_interval_error 3 7 (by norm_num) (by norm_num))
#check (prime_interval_uniform 1 (by norm_num))
#check (logarithmic_kernel_bound 3 7 (log 8) (by norm_num) (by norm_num)
  (log_lt_log (by norm_num) (by norm_num)))
#check (LeanLab.AlmostPrimeSums.PrimeCount243.primeCounting_real_upper 1 (by norm_num))
#check (LeanLab.AlmostPrimeSums.PrimeCount243.primeCounting_triple_uniform 1 (by norm_num))
#check (LeanLab.AlmostPrimeSums.Kernel243.primeCoefficient_upper 1 (by norm_num) 1 (by norm_num))
#check (LeanLab.AlmostPrimeSums.Double243.double_kernel_upper_eventual 1 (by norm_num))

example : (∑ p ∈ primesIco 3 7, (1 : ℝ) / p) ≤
    (∫ t in (3 : ℝ)..7, 1 / (t * log t)) + 6 / log 3 := by
  have hh := prime_abel_antitone_bound 3 7 (by norm_num) (by norm_num) (primesIco 3 7)
    (by intro p hp; exact ⟨(mem_filter.mp hp).2.1, (mem_filter.mp hp).2.2,
      Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp).1)⟩)
    (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
    (by intro t ht; exact hasDerivAt_const t 1)
    continuousOn_const (by norm_num) (by intro t ht; norm_num)
  simpa using hh

#check (hP_prime_sum_coarse 100 2 (by norm_num) (by norm_num) 2 3
  (by norm_num) (by norm_num) (by apply log_pos; norm_num) ({2} : Finset ℕ)
  (by intro q hq; simp only [mem_singleton] at hq; subst q; norm_num))

#check (chen_weight_sum_coarse 6 2 3 (by norm_num) (by norm_num) (by norm_num)
  (by have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); norm_num at hh ⊢; linarith)
  ({2} : Finset ℕ)
  (by intro q hq; simp only [mem_singleton] at hq; subst q; norm_num)
  (fun t : ℝ => log (2 - 3 * (log t / 6)) / ((1 - log t / 6) * 6))
  (by intro t ht; rfl))

example : ∃ N : ℕ, exp (exp 36) < (N : ℝ) ∧ ∃ p, p ∈ middlePrimes N := by
  have hpow : Tendsto (fun n : ℕ => n ^ 24) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hbig := (tendsto_natCast_atTop_atTop.comp hpow).eventually_gt_atTop (exp (exp (36 : ℝ)))
  obtain ⟨n, hN, hn⟩ := (hbig.and (eventually_ge_atTop (2 : ℕ))).exists
  have hn0 : 0 < n := by omega
  have hn3 : n ^ 3 ≠ 0 := pow_ne_zero _ (by omega)
  obtain ⟨p, hprime, hp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (n ^ 3) hn3
  have hn5 : 2 < n ^ 5 := by
    have hh := Nat.pow_le_pow_left hn (5 : ℕ)
    norm_num at hh
    omega
  have hp8 : p < n ^ 8 := by
    have hmul := Nat.mul_lt_mul_of_pos_left hn5 (pow_pos hn0 3)
    have heq : n ^ 3 * n ^ 5 = n ^ 8 := by ring
    rw [heq] at hmul
    omega
  have hcut : ((n ^ 24 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) = (n ^ 3 : ℕ) := by
    rw [Nat.cast_pow, ← rpow_natCast, ← rpow_mul (Nat.cast_nonneg n)]
    norm_num [rpow_ofNat]
  have hupp : ((n ^ 24 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) = (n ^ 8 : ℕ) := by
    rw [Nat.cast_pow, ← rpow_natCast, ← rpow_mul (Nat.cast_nonneg n)]
    norm_num [rpow_ofNat]
  refine ⟨n ^ 24, hN, p, ?_⟩
  simp only [middlePrimes, hcut, hupp, Nat.ceil_natCast, mem_filter, mem_range]
  exact ⟨hp8, hprime, by exact_mod_cast hp.le⟩

example : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ) ≤
      ((∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) + 1) *
        ((N : ℝ) / log N) := by
  simpa using LeanLab.AlmostPrimeSums.Double243.triple_mass_upper 1 (by norm_num)

#check (LeanLab.AlmostPrimeSums.Kernel243.sumSAq_upper :
  LevelBV → ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
    (LeanLab.ChenExplicit.sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
      ≤ (log 6 + η) * Mchen N)
