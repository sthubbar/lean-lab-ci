import LeanLab.AlmostPrimeSums.Tail586

/-!
AI wrote this Lean code for CODEX task586. Goldbach is open.
Concrete instances for the finite prerequisites in Tail586.
The instances check the source roles recorded in STATEMENTS.md.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real BoundingSieve

/-- The squarefree number six lies above four to the power one and has
more than one distinct prime factor. Derived counting instance for
Heath Brown p. 34 and BJS p. 10 equation 28. -/
theorem count_instance586 :
    Squarefree 6 ∧ (∀ p ∈ (6 : ℕ).primeFactors, (p : ℝ) < 4) ∧
      (4 : ℝ) ^ (1 : ℝ) < 6 ∧ (1 : ℝ) < ((6 : ℕ).primeFactors.card : ℝ) := by
  have hs : Squarefree 6 := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.squarefree_mul_iff]
    exact ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  have hf : (6 : ℕ).primeFactors = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
  have hP : ∀ p ∈ (6 : ℕ).primeFactors, (p : ℝ) < 4 := by
    norm_num [hf]
  refine ⟨hs, hP, by norm_num, ?_⟩
  exact primeFactors_card_gt_of_rpow_lt586 hs (by norm_num) hP (by norm_num)

/-- At d equal to six and D equal to twenty, the lower Rosser gate
fails and its leading product exceeds twenty over sixteen. Derived
instance of Heath Brown p. 34 and BJS p. 10 equation 28. -/
theorem gate_instance586 :
    (∃ m < (decPrimes 6).length, (false = true ↔ m % 2 = 0) ∧
      (20 : ℝ) ≤ (((decPrimes 6).take m).prod : ℝ) *
        ((decPrimes 6).getD m 0 : ℝ) ^ 3) ∧
      (20 : ℝ) / 4 ^ 2 < (((decPrimes 6).take 2).prod : ℝ) := by
  have hs : Squarefree 6 := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.squarefree_mul_iff]
    exact ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  have hf : (6 : ℕ).primeFactors = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
  have hpr : decPrimes 6 = [3, 2] := by
    rw [decPrimes, hf]
    have he : ({2, 3} : Finset ℕ) = insert 3 {2} := by ext n; simp [or_comm]
    rw [he, Finset.sort_insert (· ≥ ·) (by simp) (by simp)]
    simp
  have hweight : rosserWeight 20 false 6 = 0 := by
    apply ite_eq_right
    rintro ⟨_, h⟩
    have hh := h 1 (by simp [hpr]) (by norm_num)
    norm_num [hpr] at hh
  have hmu : (ArithmeticFunction.moebius 6 : ℝ) ≠ 0 := by
    exact_mod_cast ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs
  constructor
  · apply exists_failed_rosser_gate586 hs 20 false
    rw [hweight]
    exact hmu.symm
  · apply failed_gate_leading_product586 (d := 6) (m := 1)
      (by norm_num) (by norm_num) (by simp [hpr]) count_instance586.2.1
    norm_num [hpr]

/-- The single prime density sieve has normalized nontrivial Selberg
mass one half. Derived normalization instance for Opera de Cribro
p. 67 before equation 6.65. -/
theorem mass_instance586 :
    ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ LinearDensity s (log 2) ∧
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => 1 ≤ n.primeFactors.card),
          s.selbergTerms n) = 1 / 2 := by
  obtain ⟨s, hP, _, hnu, hden, _⟩ := single_prime_density_instance
  have hd : (2 : ℕ).divisors = {1, 2} := by decide
  refine ⟨s, hP, hden, ?_⟩
  norm_num [hP, hd, s.selbergTerms_apply, hnu, Nat.prime_two.primeFactors,
    Finset.sum_filter]

/-- A positive mass and a positive index satisfy the exponential Stirling
threshold. Derived scalar instance for Opera de Cribro p. 68 equation 6.75. -/
theorem scalar_instance586 :
    exp 2 * (1 : ℝ) ≤ (8 : ℕ) ∧
      (1 : ℝ) ^ 8 / (8 : ℕ).factorial ≤ exp (-(8 : ℝ)) := by
  have he : exp 2 = (exp 1) ^ 2 := by rw [← exp_nat_mul]; norm_num
  have hscale : exp 2 * (1 : ℝ) ≤ (8 : ℕ) := by
    rw [he]
    have hx : exp 1 ≤ (11 / 4 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have hsq := pow_le_pow_left₀ (exp_pos 1).le hx 2
    norm_num at hsq
    rw [he] at hsq
    norm_num only [Nat.cast_ofNat, mul_one]
    linarith
  exact ⟨hscale, factorial_mass_le_exp586 1 (by norm_num) 8 (by decide) hscale⟩

end LeanLab.AlmostPrimeSums.Decomp1527b
