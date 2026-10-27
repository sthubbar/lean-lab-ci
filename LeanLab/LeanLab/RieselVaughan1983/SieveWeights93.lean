import LeanLab.RieselVaughan1983.Lemma3Weighted
import LeanLab.RieselVaughan1983.Lemma5Final

/-! Elementary weights for equation 3.12 and the trivial case in Lemma 5.
AI wrote the Lean code. Binary Goldbach is OPEN. -/
namespace LeanLab.RieselVaughan1983.SieveWeights93
open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
noncomputable section

/-- The prime factor in equation 3.12 for even n. -/
def localFactor (n p : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)

/-- The squarefree coefficient in equation 3.12. -/
def coefficient (n q : ℕ) : ℝ :=
  (μ q : ℝ) ^ 2 * ∏ p ∈ q.primeFactors, localFactor n p

/-- Equation 3.12, for an even n. -/
def Sn (n : ℕ) (z : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊z⌋₊, coefficient n q / (1 + (q : ℝ) / z)

lemma localFactor_nonneg (n p : ℕ) (hn : Even n) (hp : p.Prime) :
    0 ≤ localFactor n p := by
  unfold localFactor
  split_ifs with hd
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact div_nonneg zero_le_one (by linarith)
  · have hne : p ≠ 2 := by intro he; subst p; exact hd hn.two_dvd
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (lt_of_le_of_ne hp.two_le (Ne.symm hne))
    exact div_nonneg (by norm_num) (by linarith)

lemma coefficient_nonneg (n q : ℕ) (hn : Even n) : 0 ≤ coefficient n q := by
  apply mul_nonneg (sq_nonneg _)
  apply prod_nonneg
  intro p hp
  exact localFactor_nonneg n p hn (Nat.prime_of_mem_primeFactors hp)

lemma coefficient_one (n : ℕ) : coefficient n 1 = 1 := by
  simp [coefficient]

lemma Sn_pos (n : ℕ) (hn : Even n) (z : ℝ) (hz : 1 ≤ z) : 0 < Sn n z := by
  have hz0 : 0 < z := by linarith
  have hm : 1 ∈ Icc 1 ⌊z⌋₊ := mem_Icc.mpr ⟨le_rfl, Nat.le_floor (by simpa using hz)⟩
  have hs := single_le_sum (s := Icc 1 ⌊z⌋₊)
    (f := fun q : ℕ => coefficient n q / (1 + (q : ℝ) / z))
    (fun q _ => div_nonneg (coefficient_nonneg n q hn) (by positivity)) hm
  rw [coefficient_one] at hs
  have hp : 0 < (1 : ℝ) / (1 + (1 : ℝ) / z) := by positivity
  exact hp.trans_le (by simpa [Sn, Lemma3.S2] using hs)

lemma S2_pos (z : ℝ) (hz : 1 ≤ z) : 0 < Lemma3.S2 z := by
  have hz0 : 0 < z := by linarith
  have hm : 1 ∈ Icc 1 ⌊z⌋₊ := mem_Icc.mpr ⟨le_rfl, Nat.le_floor (by simpa using hz)⟩
  have hs := single_le_sum (s := Icc 1 ⌊z⌋₊)
    (f := fun q : ℕ => Lemma2.sieveCoeff q / (1 + (q : ℝ) / z))
    (fun q _ => div_nonneg (Lemma3.sieveCoeff_nonneg q) (by positivity)) hm
  rw [Lemma2.sieveCoeff_one] at hs
  have hp : 0 < (1 : ℝ) / (1 + (1 : ℝ) / z) := by positivity
  exact hp.trans_le (by simpa [Sn, Lemma3.S2] using hs)

lemma one_le_wt (n : ℕ) : 1 ≤ wt n := by
  unfold wt
  apply one_le_prod₀
  intro p hp
  have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
  exact (le_div_iff₀ (by linarith)).mpr (by linarith)

lemma prime_pair_odd_shift (h : ℕ) (hh : ¬ Even h) (p : ℕ)
    (hp : p.Prime) (hph : (p + h).Prime) : p = 2 := by
  by_contra hp2
  have hph2 : p + h ≠ 2 := by have := hp.two_le; omega
  obtain ⟨a, ha⟩ := hp.odd_of_ne_two hp2
  obtain ⟨b, hb⟩ := hph.odd_of_ne_two hph2
  have hab : a ≤ b := by omega
  apply hh
  exact ⟨b - a, by omega⟩

lemma odd_shift_count (x : ℝ) (h : ℕ) (hh : ¬ Even h) :
    (#((Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + h).Prime)) : ℝ) ≤ 1 := by
  have hs : (Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + h).Prime) ⊆ {2} := by
    intro p hp
    have hp' := (mem_filter.mp hp).2
    simpa using prime_pair_odd_shift h hh p hp'.1 hp'.2
  exact_mod_cast (card_le_card hs)

lemma localFactor_two (p : ℕ) (hp : p.Prime) : localFactor 2 p = Lemma2.localWeight p := by
  by_cases he : p = 2
  · subst p
    norm_num [localFactor, Lemma2.localWeight]
  · have hd : ¬ p ∣ 2 := by
      intro hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact hp.ne_one h1
      · exact he h2
    simp [localFactor, Lemma2.localWeight, he, hd]

lemma coefficient_two (q : ℕ) (hq : q ≠ 0) : coefficient 2 q = Lemma2.sieveCoeff q := by
  unfold coefficient
  rw [Lemma2.sieveCoeff, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.ppow_apply (by norm_num : 0 < 2),
    ArithmeticFunction.prodPrimeFactors_apply hq]
  congr 1
  apply prod_congr rfl
  intro p hp
  exact localFactor_two p (Nat.prime_of_mem_primeFactors hp)

lemma Sn_two (z : ℝ) : Sn 2 z = Lemma3.S2 z := by
  apply sum_congr rfl
  intro q hq
  rw [coefficient_two q (by have := (mem_Icc.mp hq).1; omega)]

lemma comparison_two (z : ℝ) : Lemma3.S2 z / wt 2 = Sn 2 z := by
  rw [Sn_two]
  have hf : (2 : ℕ).primeFactors.filter (2 < ·) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp
    rw [Nat.prime_two.primeFactors, mem_singleton] at hp
    omega
  simp only [wt, hf, prod_empty, div_one]

end
end LeanLab.RieselVaughan1983.SieveWeights93

#print axioms LeanLab.RieselVaughan1983.SieveWeights93.localFactor_nonneg
#print axioms LeanLab.RieselVaughan1983.SieveWeights93.coefficient_nonneg
#print axioms LeanLab.RieselVaughan1983.SieveWeights93.coefficient_one
#print axioms LeanLab.RieselVaughan1983.SieveWeights93.Sn_pos
#print axioms LeanLab.RieselVaughan1983.SieveWeights93.S2_pos
#print axioms LeanLab.RieselVaughan1983.SieveWeights93.one_le_wt
#print axioms LeanLab.RieselVaughan1983.SieveWeights93.prime_pair_odd_shift
#print axioms LeanLab.RieselVaughan1983.SieveWeights93.odd_shift_count

#print axioms LeanLab.RieselVaughan1983.SieveWeights93.localFactor_two
#print axioms LeanLab.RieselVaughan1983.SieveWeights93.coefficient_two
#print axioms LeanLab.RieselVaughan1983.SieveWeights93.Sn_two
#print axioms LeanLab.RieselVaughan1983.SieveWeights93.comparison_two
