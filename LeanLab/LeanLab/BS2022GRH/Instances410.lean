/- AI wrote this Lean code for CODEX task410.
Concrete elementary domains for journal Lemma 10 p. 1227.
Goldbach is open. -/
import LeanLab.BS2022GRH.Density410

namespace LeanLab.BS2022GRH.Instances410
open Real Finset

/-- The divisor correction has simultaneous small, large and eligible primes.
This witnesses the finite domain in Nathanson Theorem 10.3 p. 277. -/
theorem correction_nonvacuous : ∃ (n : ℕ) (x : ℝ),
    0 < n ∧ Even n ∧ 2 < x ∧
    3 ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < x) ∧
    11 ∈ n.primeFactors.filter (fun p : ℕ => x ≤ (p : ℝ)) ∧
    5 ∈ DecompC169a.primesBelow n x ∧
    7 ∉ DecompC169a.primesBelow n x := by
  refine ⟨66, 7, by norm_num, by decide, by norm_num, ?_, ?_, ?_, ?_⟩
  · simp only [mem_filter, Nat.mem_primeFactors]
    norm_num
  · simp only [mem_filter, Nat.mem_primeFactors]
    norm_num
  · norm_num [DecompC169a.primesBelow]
  · norm_num [DecompC169a.primesBelow]

/-- A concrete consistent scalar domain for the journal lower error budget. -/
theorem budget_nonvacuous : ∃ x L : ℝ, 64 ≤ x ∧ 8 ≤ L ∧ log x = L / 8 := by
  have h := pow_div_factorial_le_exp (x := (8 : ℝ)) (by norm_num) 3
  norm_num [Nat.factorial] at h
  refine ⟨exp 8, 64, by linarith, by norm_num, ?_⟩
  rw [log_exp]
  norm_num

/-- The large even elementary domain of the sealed density bound is inhabited.
This asserts neither GRH nor an analytic prime product estimate. -/
theorem target_nonvacuous : ∃ n : ℕ,
    (4e18 : ℝ) ≤ n ∧ Even n ∧ 0 < DecompC169a.density n := by
  refine ⟨4000000000000000000, by norm_num, by decide, ?_⟩
  have hev : Even (4000000000000000000 : ℕ) := by decide
  apply prod_pos
  intro p hp
  obtain ⟨_, hprime, hpn, _⟩ := mem_filter.mp hp
  have hp3 : 3 ≤ p := by
    have hp2 := hprime.two_le
    have hne : p ≠ 2 := fun h => hpn (h ▸ hev.two_dvd)
    omega
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hlt : (1 : ℝ) / (p - 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  linarith

/-- The target also has an elementary domain with a strictly positive lower
bound. This checks the nontrivial regime of journal Lemma 10 p. 1227. -/
theorem target_positive_domain : ∃ n : ℕ,
    (4e18 : ℝ) ≤ n ∧ Even n ∧
    0 < 8 * UNfull n / log n * (1 - 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) := by
  refine ⟨2 ^ 128, by norm_num, by decide, ?_⟩
  have hlog : log (((2 ^ 128 : ℕ) : ℝ)) = 128 * log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, log_pow]
    norm_num
  have hroot : (((2 ^ 128 : ℕ) : ℝ)) ^ (1 / 16 : ℝ) = 256 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [rpow_natCast]
  have hU : 0 < UNfull (2 ^ 128) := lt_of_lt_of_le
    (by norm_num : (0 : ℝ) < 2 / 5) (two_fifths_le_UNfull _)
  have hL : 0 < log (((2 ^ 128 : ℕ) : ℝ)) := by
    rw [hlog]
    linarith [log_two_gt_d9]
  have hfactor : 0 < 1 - 0.62 * log (((2 ^ 128 : ℕ) : ℝ)) /
      (((2 ^ 128 : ℕ) : ℝ)) ^ (1 / 16 : ℝ) := by
    rw [hroot, hlog]
    linarith [log_two_lt_d9]
  exact mul_pos (div_pos (mul_pos (by norm_num) hU) hL) hfactor

end LeanLab.BS2022GRH.Instances410
#print axioms LeanLab.BS2022GRH.Instances410.correction_nonvacuous
#print axioms LeanLab.BS2022GRH.Instances410.budget_nonvacuous
#print axioms LeanLab.BS2022GRH.Instances410.target_nonvacuous

#print axioms LeanLab.BS2022GRH.Instances410.target_positive_domain
