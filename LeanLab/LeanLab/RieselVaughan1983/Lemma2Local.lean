import LeanLab.RieselVaughan1983.Lemma2Convolution

/-!
The prime power values in equations 2.5 and 2.6 on page 46.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.Lemma2

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

lemma divideByN_multiplicative (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative) :
    (divideByN f).IsMultiplicative := by
  refine ⟨by simp [divideByN_apply, hf.map_one], fun {a b} hab => ?_⟩
  simp only [divideByN_apply, hf.map_mul_of_coprime hab, Nat.cast_mul, div_mul_div_comm]

lemma sieveCoeff_multiplicative : sieveCoeff.IsMultiplicative := by
  exact isMultiplicative_moebius.intCast.ppow.pmul
    (IsMultiplicative.prodPrimeFactors localWeight)

lemma g_multiplicative : g.IsMultiplicative :=
  (sieveCoeff_multiplicative.mul
    (divideByN_multiplicative _ isMultiplicative_moebius.intCast)).mul
      (divideByN_multiplicative _ isMultiplicative_moebius.intCast)

lemma sieveCoeff_one : sieveCoeff 1 = 1 := sieveCoeff_multiplicative.map_one

lemma sieveCoeff_prime (p : ℕ) (hp : p.Prime) : sieveCoeff p = localWeight p := by
  simp [sieveCoeff, ppow_apply (by omega : 0 < 2), prodPrimeFactors_apply hp.ne_zero,
    moebius_apply_prime hp, hp.primeFactors]

lemma sieveCoeff_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) :
    sieveCoeff (p ^ k) = 0 := by
  simp [sieveCoeff, ppow_apply (by omega : 0 < 2),
    moebius_apply_prime_pow hp (by omega : k ≠ 0), show k ≠ 1 by omega]

lemma mul_inverse_prime_succ (f : ArithmeticFunction ℝ) (p k : ℕ) (hp : p.Prime) :
    (f * inverseReciprocal) (p ^ (k + 1)) = f (p ^ (k + 1)) - f (p ^ k) / p := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => f a * inverseReciprocal b),
    Nat.sum_divisors_prime_pow hp,
    sum_range_succ', sum_range_succ']
  have hz : ∑ j ∈ range k,
      f (p ^ (k + 1) / p ^ (j + 1 + 1)) * inverseReciprocal (p ^ (j + 1 + 1)) = 0 := by
    apply sum_eq_zero
    intro j _
    simp [inverseReciprocal, divideByN_apply,
      moebius_apply_prime_pow hp (by omega : j + 1 + 1 ≠ 0), show j + 1 + 1 ≠ 1 by omega]
  rw [hz]
  have hd : p ^ (k + 1) / p = p ^ k := by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  simp only [zero_add, pow_zero, pow_one, Nat.div_one, hd, inverseReciprocal,
    divideByN_apply, intCoe_apply, moebius_apply_one, moebius_apply_prime hp, Int.cast_one,
    Int.cast_neg, Nat.cast_one, div_one, mul_one]
  ring

lemma g_prime (p : ℕ) (hp : p.Prime) : g p = localWeight p - 2 / p := by
  have h := mul_inverse_prime_succ (sieveCoeff * inverseReciprocal) p 0 hp
  have h' := mul_inverse_prime_succ sieveCoeff p 0 hp
  simp only [zero_add, pow_one, pow_zero] at h h'
  change (sieveCoeff * inverseReciprocal * inverseReciprocal) p = _
  rw [h, h', mul_apply_one, sieveCoeff_one, sieveCoeff_prime p hp]
  simp [inverseReciprocal, divideByN_apply]
  ring

lemma g_prime_pow_two_step (p k : ℕ) (hp : p.Prime) :
    g (p ^ (k + 2)) = sieveCoeff (p ^ (k + 2)) -
      2 * sieveCoeff (p ^ (k + 1)) / p + sieveCoeff (p ^ k) / (p : ℝ) ^ 2 := by
  have h := mul_inverse_prime_succ (sieveCoeff * inverseReciprocal) p (k + 1) hp
  have h' := mul_inverse_prime_succ sieveCoeff p (k + 1) hp
  have h'' := mul_inverse_prime_succ sieveCoeff p k hp
  change (sieveCoeff * inverseReciprocal * inverseReciprocal) (p ^ (k + 2)) = _
  rw [show k + 2 = k + 1 + 1 by omega, h, h', h'']
  ring

lemma g_two : g 2 = 0 := by
  rw [g_prime 2 Nat.prime_two]
  norm_num [localWeight]

lemma g_four : g 4 = -3 / 4 := by
  have h4 : sieveCoeff 4 = 0 := by
    simpa using sieveCoeff_prime_pow 2 2 Nat.prime_two (by omega)
  have h := g_prime_pow_two_step 2 0 Nat.prime_two
  norm_num [h4, sieveCoeff_prime 2 Nat.prime_two, sieveCoeff_one, localWeight] at h
  simpa only [neg_div] using h

lemma g_eight : g 8 = 1 / 4 := by
  have h4 : sieveCoeff 4 = 0 := by
    simpa using sieveCoeff_prime_pow 2 2 Nat.prime_two (by omega)
  have h8 : sieveCoeff 8 = 0 := by
    simpa using sieveCoeff_prime_pow 2 3 Nat.prime_two (by omega)
  have h := g_prime_pow_two_step 2 1 Nat.prime_two
  norm_num [h4, h8, sieveCoeff_prime 2 Nat.prime_two, localWeight] at h
  exact h

lemma g_prime_pow_ge_four (p k : ℕ) (hp : p.Prime) (hk : 4 ≤ k) : g (p ^ k) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [g_prime_pow_two_step p j hp,
    sieveCoeff_prime_pow p (j + 2) hp (by omega),
    sieveCoeff_prime_pow p (j + 1) hp (by omega),
    sieveCoeff_prime_pow p j hp (by omega)]
  ring

lemma g_odd_prime (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    g p = 4 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2' : (2 : ℝ) < p := by exact_mod_cast hp2
  rw [g_prime p hp, localWeight, if_neg (by omega)]
  field_simp [hp0, sub_ne_zero.mpr hp2'.ne']
  ring

lemma g_odd_prime_sq (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    g (p ^ 2) = (-3 * (p : ℝ) - 2) / ((p : ℝ) ^ 2 * ((p : ℝ) - 2)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2' : (2 : ℝ) < p := by exact_mod_cast hp2
  have h := g_prime_pow_two_step p 0 hp
  norm_num only [zero_add, pow_zero, pow_one, sieveCoeff_one] at h
  rw [h, sieveCoeff_prime_pow p 2 hp (by omega), sieveCoeff_prime p hp]
  simp only [localWeight, if_neg (by omega : p ≠ 2)]
  field_simp [hp0, sub_ne_zero.mpr hp2'.ne']
  ring

lemma g_odd_prime_cube (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    g (p ^ 3) = 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 2)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2' : (2 : ℝ) < p := by exact_mod_cast hp2
  have h := g_prime_pow_two_step p 1 hp
  norm_num only [Nat.reduceAdd, pow_one] at h
  rw [h, sieveCoeff_prime_pow p 3 hp (by omega),
    sieveCoeff_prime_pow p 2 hp (by omega), sieveCoeff_prime p hp]
  simp only [localWeight, if_neg (by omega : p ≠ 2)]
  field_simp [hp0, sub_ne_zero.mpr hp2'.ne']
  ring

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.divideByN_multiplicative
#print axioms LeanLab.RieselVaughan1983.Lemma2.sieveCoeff_multiplicative
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_multiplicative
#print axioms LeanLab.RieselVaughan1983.Lemma2.sieveCoeff_one
#print axioms LeanLab.RieselVaughan1983.Lemma2.sieveCoeff_prime
#print axioms LeanLab.RieselVaughan1983.Lemma2.sieveCoeff_prime_pow
#print axioms LeanLab.RieselVaughan1983.Lemma2.mul_inverse_prime_succ
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_prime
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_prime_pow_two_step
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_two
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_four
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_eight
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_prime_pow_ge_four
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_odd_prime
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_odd_prime_sq
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_odd_prime_cube
