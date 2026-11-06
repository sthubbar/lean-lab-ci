import LeanLab.AlmostPrimeSums.Lower243
import LeanLab.AlmostPrimeSums.Decomp243b

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Concrete domains for the lower Abel estimates and the exact coefficient limit.
-/

open Finset Real Filter Topology
open LeanLab.ChenExplicit.D1552
open LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.AlmostPrimeSums.Lower243

#check (logarithmic_kernel_lower 3 7 (log 8) (by norm_num) (by norm_num)
  (log_lt_log (by norm_num) (by norm_num)))
#check (primeCoefficient_limit 1 (by norm_num))
#check (LeanLab.AlmostPrimeSums.Decomp243b.primeCoefficient_limit 1 (by norm_num))

example : (∫ t in (3 : ℝ)..7, 1 / (t * log t)) - 12 / log 3 ≤
    ∑ p ∈ primesIco 3 7, (1 : ℝ) / p := by
  have h3 := Port1527c.Mertens.intervalIntegrable_one_div_mul_log (x := (3 : ℝ)) (by norm_num)
  have h7 := Port1527c.Mertens.intervalIntegrable_one_div_mul_log (x := (7 : ℝ)) (by norm_num)
  have hh := prime_abel_monotone_lower 3 7 (by norm_num) (by norm_num)
    (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
    (by intro t ht; exact hasDerivAt_const t 1) continuousOn_const
    (by norm_num) (by norm_num) (by intro t ht; norm_num) (h3.symm.trans h7)
  simpa using hh
