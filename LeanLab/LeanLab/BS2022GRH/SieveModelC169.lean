/- AI wrote this Lean code for CODEX task169.
Finite sieve model for A, journal pp. 1227 to 1229. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC169a
import LeanLab.BS2022GRH.Decomp148f

namespace LeanLab.BS2022GRH.SieveModelC169
open Real Finset Classical DecompC169a Decomp148f
noncomputable section

/-- The general sieve prime set specializes to the P primes of Theorem 5. -/
theorem prime_set_eq (n : ℕ) (z : ℝ) :
    siftingPrimes {p : ℕ | p.Prime ∧ ¬ p ∣ n} z = primesBelow n z := by
  ext p
  simp [siftingPrimes, primesBelow, and_assoc]

/-- The finite prime condition equals the paper's NoSmallP predicate. -/
theorem sifting_condition (n m : ℕ) (z : ℝ) :
    (∀ p ∈ siftingPrimes {p : ℕ | p.Prime ∧ ¬ p ∣ n} z, ¬ p ∣ m) ↔
      U7153.NoSmallP n z m := by
  rw [prime_set_eq]
  constructor
  · intro h p hp hpz hpn
    apply h p
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr hpz), hp, hpn, hpz⟩
  · intro h p hp
    obtain ⟨_, hprime, hpn, hpz⟩ := mem_filter.mp hp
    exact h p hprime hpz hpn

/-- The actual sifted indicator sum is exactly SA, p. 1229. -/
theorem sifted_indicator (n : ℕ) :
    sifted (U7153.Aset n) (fun m => if m ∈ U7153.Aset n then 1 else 0)
      {p : ℕ | p.Prime ∧ ¬ p ∣ n} (U7153.zz n) = (U7153.SA n : ℝ) := by
  unfold sifted U7153.SA
  simp_rw [sifting_condition]
  calc
    _ = ∑ m ∈ (U7153.Aset n).filter (U7153.NoSmallP n (U7153.zz n)), (1 : ℝ) := by
      apply sum_congr rfl
      intro m hm
      rw [if_pos (mem_filter.mp hm).1]
    _ = _ := by simp

/-- The model main mass is V at z times cardinality of A, p. 1229. -/
theorem main_mass_indicator (n : ℕ) :
    mainMass (U7153.Aset n) (fun m => if m ∈ U7153.Aset n then 1 else 0)
      {p : ℕ | p.Prime ∧ ¬ p ∣ n} (fun _ p => 1 / ((p : ℝ) - 1)) (U7153.zz n) =
      density n * ((U7153.Aset n).card : ℝ) := by
  unfold mainMass
  rw [prime_set_eq]
  calc
    _ = ∑ _m ∈ U7153.Aset n, density n := by
      apply sum_congr rfl
      intro m hm
      dsimp only
      rw [if_pos hm, one_mul]
      rfl
    _ = _ := by simp [mul_comm]

/-- On squarefree divisors the product density is one over phi, p. 1229. -/
theorem squarefree_model (d : ℕ) (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)) = 1 / (d.totient : ℝ) := by
  have hφ : d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hd,
      Nat.div_self (Nat.pos_of_ne_zero hd.ne_zero), one_mul]
  have hφR : (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
    rw [hφ, Nat.cast_prod]
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  simp_rw [one_div]
  rw [prod_inv_distrib, ← hφR]

/-- The finite divisor error is exactly the residue r on squarefree d, p. 1229. -/
theorem divisor_error_indicator (n d : ℕ) (hd : Squarefree d) :
    divisorError (U7153.Aset n) (fun m => if m ∈ U7153.Aset n then 1 else 0)
      (fun _ p => 1 / ((p : ℝ) - 1)) d = residue n d := by
  have hmass : (∑ m ∈ U7153.Aset n, if m ∈ U7153.Aset n then (1 : ℝ) else 0) =
      ((U7153.Aset n).card : ℝ) := by simp
  have hdiv : (∑ m ∈ (U7153.Aset n).filter (fun m => d ∣ m),
      if m ∈ U7153.Aset n then (1 : ℝ) else 0) =
      (((U7153.Aset n).filter (fun m => d ∣ m)).card : ℝ) := by
    calc
      _ = ∑ _m ∈ (U7153.Aset n).filter (fun m => d ∣ m), (1 : ℝ) := by
        apply sum_congr rfl
        intro m hm
        rw [if_pos (mem_filter.mp hm).1]
      _ = _ := by simp
  unfold divisorError residue
  simp_rw [squarefree_model d hd]
  rw [← sum_mul, hmass, hdiv]
  ring

end
end LeanLab.BS2022GRH.SieveModelC169

#print axioms LeanLab.BS2022GRH.SieveModelC169.prime_set_eq
#print axioms LeanLab.BS2022GRH.SieveModelC169.sifting_condition
#print axioms LeanLab.BS2022GRH.SieveModelC169.sifted_indicator
#print axioms LeanLab.BS2022GRH.SieveModelC169.main_mass_indicator
#print axioms LeanLab.BS2022GRH.SieveModelC169.squarefree_model
#print axioms LeanLab.BS2022GRH.SieveModelC169.divisor_error_indicator
