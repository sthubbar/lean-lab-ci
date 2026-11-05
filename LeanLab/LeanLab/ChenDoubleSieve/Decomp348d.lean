import LeanLab.ChenDoubleSieve.Decomp348b
import LeanLab.ChenDoubleSieve.Decomp348c
import LeanLab.ChenDoubleSieve.Decomp315a

/-!
Elementary coprimality removal for the prime pair limits in equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, page 39, display after equation 10.5.
The large prime divisor bound gives the logarithmic error used in the paper.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275

/-- The even asymptotic filter is nontrivial. -/
theorem evenAtTop_neBot : NeBot evenAtTop := by
  exact frequently_iff_neBot.1 Nat.frequently_even

/-- Every local factor is positive when N is even. -/
theorem lowerDensity_pos {N : ℕ} (hEven : Even N) : 0 < lowerDensity N := by
  apply Finset.prod_pos
  intro p hp
  have hs := Wu41.mem_PS.mp hp
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hs.2.2.2) hEven.two_dvd
  have hpgt : (2 : ℝ) < p := by exact_mod_cast (lt_of_le_of_ne hs.1.two_le (Ne.symm hp2))
  have hden : 0 < (p : ℝ) - 1 := by linarith
  have hi : 1 / ((p : ℝ) - 1) < 1 := (div_lt_one hden).2 (by linarith)
  linarith

/-- The local density is at most one for even N. -/
theorem lowerDensity_le_one {N : ℕ} (hEven : Even N) : lowerDensity N ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro p hp
    have hs := Wu41.mem_PS.mp hp
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hs.2.2.2) hEven.two_dvd
    have hpgt : (2 : ℝ) < p := by exact_mod_cast (lt_of_le_of_ne hs.1.two_le (Ne.symm hp2))
    have hi : 1 / ((p : ℝ) - 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    linarith
  · intro p hp
    have hs := Wu41.mem_PS.mp hp
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hs.1.two_le
    have hi : 0 ≤ 1 / ((p : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
    linarith

/-- The scaled density has a positive finite instance at every even N above one. -/
theorem scaledDensity_pos {N : ℕ} (hEven : Even N) (hN : 2 ≤ N) :
    0 < scaledDensity N := by
  apply div_pos _ (CN_pos N)
  apply mul_pos _ (lowerDensity_pos hEven)
  exact log_pos (by exact_mod_cast (show 1 < N by omega))

/-- Reciprocals of any subset of the positive integers up to N obey the harmonic bound. -/
theorem reciprocal_sum_le (P : Finset ℕ) (N : ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p ∧ p ≤ N) :
    (∑ p ∈ P, 1 / (p : ℝ)) ≤ 1 + log N := by
  calc
    (∑ p ∈ P, 1 / (p : ℝ)) ≤ ∑ p ∈ Finset.Icc 1 N, 1 / (p : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Finset.mem_Icc.mpr (hP p hp)
      · intro p _ _
        positivity
    _ = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp
    _ ≤ 1 + log N := harmonic_le_one_add_log N

/-- The reciprocal mass of large prime divisors of N has an explicit elementary bound. -/
theorem exceptional_reciprocal_sum (P : Finset ℕ) {N : ℕ} (hN : 0 < N)
    {z : ℝ} (hz : 0 < z) (hP : ∀ p ∈ P, p.Prime ∧ z ≤ p) :
    (∑ p ∈ P.filter (fun p => ¬ p.Coprime N), 1 / (p : ℝ)) ≤
      (log N / log 2) / z := by
  have hsub : P.filter (fun p => ¬ p.Coprime N) ⊆ N.primeFactors := by
    intro p hp
    obtain ⟨hpP, hbad⟩ := mem_filter.mp hp
    have hprime := (hP p hpP).1
    have hdvd : p ∣ N := by
      simpa only [hprime.coprime_iff_not_dvd, not_not] using hbad
    exact Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hN.ne'⟩
  calc
    _ ≤ ∑ _p ∈ P.filter (fun p => ¬ p.Coprime N), 1 / z := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hz (hP p (mem_filter.mp hp).1).2
    _ = ((P.filter (fun p => ¬ p.Coprime N)).card : ℝ) / z := by simp [div_eq_mul_inv]
    _ ≤ (N.primeFactors.card : ℝ) / z :=
      div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hz.le
    _ ≤ (log N / log 2) / z :=
      div_le_div_of_nonneg_right (Task315.primeFactors_card_log hN) hz.le

/-- Reciprocal mass of a finite set of ordered pairs. -/
def pairMass (P : Finset (ℕ × ℕ)) : ℝ :=
  ∑ q ∈ P, 1 / ((q.1 : ℝ) * q.2)

/-- The pairs removed by the coprimality restriction. -/
def badPairs (N : ℕ) (P Q : Finset ℕ) : Finset (ℕ × ℕ) :=
  (P ×ˢ Q).filter (fun q => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N)

/-- Reciprocal mass over a rectangle factors into its two marginal sums. -/
theorem pairMass_product (P Q : Finset ℕ) :
    pairMass (P ×ˢ Q) = (∑ p ∈ P, 1 / (p : ℝ)) * (∑ q ∈ Q, 1 / (q : ℝ)) := by
  simp only [pairMass, Finset.sum_product, one_div, mul_inv]
  rw [Finset.sum_mul_sum]

/-- Enlarging a pair domain only increases its reciprocal mass. -/
theorem pairMass_mono {P Q : Finset (ℕ × ℕ)} (h : P ⊆ Q) : pairMass P ≤ pairMass Q := by
  exact sum_le_sum_of_subset_of_nonneg h (by intros; positivity)

/-- The bad pairs are the union of the two bad coordinate rectangles. -/
theorem badPairs_eq (N : ℕ) (P Q : Finset ℕ) :
    badPairs N P Q = (P.filter (fun p => ¬ p.Coprime N) ×ˢ Q) ∪
      (P ×ˢ Q.filter (fun q => ¬ q.Coprime N)) := by
  ext q
  simp only [badPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_union]
  tauto

/-- The bad pair reciprocal mass is controlled by the two marginal errors. -/
theorem badPairs_mass_le (P Q : Finset ℕ) {N : ℕ} (hN : 0 < N)
    {z : ℝ} (hz : 0 < z)
    (hP : ∀ p ∈ P, p.Prime ∧ z ≤ p ∧ p ≤ N)
    (hQ : ∀ q ∈ Q, q.Prime ∧ z ≤ q ∧ q ≤ N) :
    pairMass (badPairs N P Q) ≤ 2 * ((log N / log 2) / z) * (1 + log N) := by
  have hbadP := exceptional_reciprocal_sum P hN hz (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩)
  have hbadQ := exceptional_reciprocal_sum Q hN hz (fun q hq => ⟨(hQ q hq).1, (hQ q hq).2.1⟩)
  have hsumP := reciprocal_sum_le P N (fun p hp => ⟨(hP p hp).1.one_le, (hP p hp).2.2⟩)
  have hsumQ := reciprocal_sum_le Q N (fun q hq => ⟨(hQ q hq).1.one_le, (hQ q hq).2.2⟩)
  have hlog : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast hN)
  have hmain : 0 ≤ (log N / log 2) / z := by positivity
  rw [badPairs_eq]
  calc
    _ ≤ pairMass (P.filter (fun p => ¬ p.Coprime N) ×ˢ Q) +
        pairMass (P ×ˢ Q.filter (fun q => ¬ q.Coprime N)) := by
      let A := P.filter (fun p => ¬ p.Coprime N) ×ˢ Q
      let C := P ×ˢ Q.filter (fun q => ¬ q.Coprime N)
      have he := Finset.sum_union_inter (s₁ := A) (s₂ := C)
        (f := fun q : ℕ × ℕ => 1 / ((q.1 : ℝ) * q.2))
      have hp : 0 ≤ pairMass (A ∩ C) := sum_nonneg (by intros; positivity)
      change pairMass (A ∪ C) ≤ pairMass A + pairMass C
      change pairMass (A ∪ C) + pairMass (A ∩ C) = pairMass A + pairMass C at he
      linarith
    _ = (∑ p ∈ P.filter (fun p => ¬ p.Coprime N), 1 / (p : ℝ)) *
          (∑ q ∈ Q, 1 / (q : ℝ)) +
        (∑ p ∈ P, 1 / (p : ℝ)) *
          (∑ q ∈ Q.filter (fun q => ¬ q.Coprime N), 1 / (q : ℝ)) := by
      rw [pairMass_product, pairMass_product]
    _ ≤ ((log N / log 2) / z) * (1 + log N) +
        (1 + log N) * ((log N / log 2) / z) := by
      apply add_le_add
      · exact mul_le_mul hbadP hsumQ (sum_nonneg (by intros; positivity)) hmain
      · exact mul_le_mul hsumP hbadQ (sum_nonneg (by intros; positivity)) (by linarith)
    _ = _ := by ring

/-- At most one over kappa distinct prime divisors can exceed N to kappa. -/
theorem large_prime_divisor_card {N : ℕ} (hN : 2 ≤ N) (P : Finset ℕ)
    (hsub : P ⊆ N.primeFactors) {κ : ℝ} (hκ : 0 < κ)
    (hP : ∀ p ∈ P, (N : ℝ) ^ κ ≤ p) : (P.card : ℝ) ≤ 1 / κ := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hprod : (∏ p ∈ P, p) ≤ N := by
    calc
      (∏ p ∈ P, p) ≤ ∏ p ∈ N.primeFactors, p := by
        apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
        · intros; exact Nat.zero_le _
        · intro p hp _
          exact (Nat.mem_primeFactors.mp hp).1.one_le
      _ ≤ N := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N)
  have hprodR : (∏ p ∈ P, (p : ℝ)) ≤ N := by
    simpa only [Nat.cast_prod] using (Nat.cast_le (α := ℝ).mpr hprod)
  have hpow : ((N : ℝ) ^ κ) ^ P.card ≤ N := by
    calc
      _ = ∏ _p ∈ P, (N : ℝ) ^ κ := by simp
      _ ≤ ∏ p ∈ P, (p : ℝ) := Finset.prod_le_prod₀ (by intros; positivity) hP
      _ ≤ N := hprodR
  have hl := log_le_log (pow_pos (rpow_pos_of_pos hpos _) _) hpow
  rw [log_pow, log_rpow hpos] at hl
  apply (le_div_iff₀ hκ).2
  nlinarith

/-- A power cutoff removes the extra logarithm from the exceptional marginal bound. -/
theorem exceptional_reciprocal_sum_sharp (P : Finset ℕ) {N : ℕ} (hN : 2 ≤ N)
    {κ : ℝ} (hκ : 0 < κ)
    (hP : ∀ p ∈ P, p.Prime ∧ (N : ℝ) ^ κ ≤ p) :
    (∑ p ∈ P.filter (fun p => ¬ p.Coprime N), 1 / (p : ℝ)) ≤
      1 / (κ * (N : ℝ) ^ κ) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz : 0 < (N : ℝ) ^ κ := rpow_pos_of_pos hpos _
  have hsub : P.filter (fun p => ¬ p.Coprime N) ⊆ N.primeFactors := by
    intro p hp
    obtain ⟨hpP, hbad⟩ := mem_filter.mp hp
    have hprime := (hP p hpP).1
    have hdvd : p ∣ N := by
      simpa only [hprime.coprime_iff_not_dvd, not_not] using hbad
    exact Nat.mem_primeFactors.mpr ⟨hprime, hdvd, by omega⟩
  have hc := large_prime_divisor_card hN _ hsub hκ
    (fun p hp => (hP p (mem_filter.mp hp).1).2)
  calc
    _ ≤ ∑ _p ∈ P.filter (fun p => ¬ p.Coprime N), 1 / (N : ℝ) ^ κ := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hz (hP p (mem_filter.mp hp).1).2
    _ = ((P.filter (fun p => ¬ p.Coprime N)).card : ℝ) / (N : ℝ) ^ κ := by
      simp [div_eq_mul_inv]
    _ ≤ (1 / κ) / (N : ℝ) ^ κ := div_le_div_of_nonneg_right hc hz.le
    _ = _ := by rw [div_div]

end LeanLab.ChenDoubleSieve.Task348
