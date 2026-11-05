/-
AI wrote this Lean code. Codex task355.
Binary Goldbach is open.
Source: Halupczok 2008 pages 12 to 18.
Finite CRT domination is proved. The local prime product estimate remains OPEN.
-/
import LeanLab.Tolev2009.Decomp314b
import LeanLab.Tolev2009.CRT355

open Finset Real
namespace LeanLab.Tolev2009.Decomp355a
open LeanLab.Tolev2009.Faithful LeanLab.Tolev2009.Decomp314b

/-- Halupczok page 18, the three pairwise gcds divided by the common gcd. -/
noncomputable def gcdWeight (k : Fin 3 → ℕ) : ℝ :=
  ((Nat.gcd (k 0) (k 1) : ℝ) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2)) /
    Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2)

/-- Halupczok page 18, the residue independent coefficient envelope before totients. -/
noncomputable def rawWeight (k : Fin 3 → ℕ) : ℝ :=
  gcdWeight k * ∏ i : Fin 3, ((k i).divisors.card : ℝ) ^ 4

/-- Halupczok pages 16 to 17, a finite product of prime power first moments.
The exponent cutoff Q contains every prime power dividing an integer at most Q. -/
noncomputable def primeProduct (k l : Fin 3 → ℕ) (N Q : ℕ) : ℝ :=
  ∏ p ∈ (range (Q + 1)).filter Nat.Prime,
    (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖)

/-- LEAF. Halupczok pages 12 to 14, Propositions 1 and 2 with the totient factors.
This is the finite CRT multiplicativity identity for the explicit coefficient. -/
theorem ssTerm_multiplicative (k l : Fin 3 → ℕ) (N m n : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : Nat.Coprime m n) :
    ssTerm k l N (m * n) = ssTerm k l N m * ssTerm k l N n := by
  exact CRT355.ssTerm_mul k l N m n hk hl hm hn hmn

/-- Halupczok page 16, a finite Euler bound for any nonnegative multiplicative function. -/
theorem finite_euler_bound (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (hf0 : ∀ n, 0 ≤ f n) (Q : ℕ) :
    ∑ n ∈ Icc 1 Q, f n ≤
      ∏ p ∈ (range (Q + 1)).filter Nat.Prime, (1 + ∑ j ∈ Icc 1 Q, f (p ^ j)) := by
  let P := (range (Q + 1)).filter Nat.Prime
  let M := ∏ p ∈ P, p ^ Q
  have hp (p : ℕ) (h : p ∈ P) : p.Prime := (mem_filter.mp h).2
  have hM : M ≠ 0 := by
    exact prod_ne_zero_iff.mpr (fun p h => pow_ne_zero _ (hp p h).ne_zero)
  have hsub : Icc 1 Q ⊆ M.divisors := by
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have hP : n.primeFactors ⊆ P := by
      intro p hpn
      refine mem_filter.mpr ⟨mem_range.mpr ?_, Nat.prime_of_mem_primeFactors hpn⟩
      have hpn' := Nat.le_of_dvd (by omega : 0 < n) (Nat.dvd_of_mem_primeFactors hpn)
      have := (mem_Icc.mp hn).2
      omega
    have hd := Nat.dvd_prod_primeFactors_pow_self hn0
    rw [← prod_pow] at hd
    apply Nat.mem_divisors.mpr ⟨hd.trans ?_, hM⟩
    apply dvd_trans (prod_dvd_prod_of_dvd _ _ (fun p _ => pow_dvd_pow p (mem_Icc.mp hn).2))
    exact prod_dvd_prod_of_subset _ _ _ hP
  have hpair : (P : Set ℕ).Pairwise (fun p q => Nat.Coprime (p ^ Q) (q ^ Q)) := by
    intro p hp' q hq' hpq
    exact ((Nat.coprime_primes (hp p hp') (hp q hq')).mpr hpq).pow Q Q
  calc
    _ ≤ ∑ n ∈ M.divisors, f n :=
      sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf0 n)
    _ = (f * ArithmeticFunction.zeta) M := by rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = ∏ p ∈ P, (f * ArithmeticFunction.zeta) (p ^ Q) :=
      ArithmeticFunction.IsMultiplicative.map_prod (fun p => p ^ Q)
        (hf.mul ArithmeticFunction.isMultiplicative_zeta.natCast) P hpair
    _ = _ := by
      apply prod_congr rfl
      intro p hp'
      rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow (hp p hp')]
      have he : range (Q + 1) = insert 0 (Icc 1 Q) := by
        ext j
        simp only [mem_range, mem_insert, mem_Icc]
        omega
      rw [he, sum_insert (by simp), pow_zero, hf.map_one]

/-- Halupczok page 16, finite Euler domination of the first absolute coefficients.
The finite CRT multiplicativity identity is proved. -/
theorem finite_euler_domination (k l : Fin 3 → ℕ) (N Q : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) :
    ∑ q ∈ Icc 1 Q, (q : ℝ) * ‖ssTerm k l N q‖ ≤ primeProduct k l N Q := by
  let f : ArithmeticFunction ℝ := ⟨fun q => (q : ℝ) * ‖ssTerm k l N q‖, by simp⟩
  have hf : f.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simp [f, ssTerm_one hk hl]
    · intro m n hmn
      by_cases hm : m = 0
      · subst m; simp
      by_cases hn : n = 0
      · subst n; simp
      change ((m * n : ℕ) : ℝ) * ‖ssTerm k l N (m * n)‖ =
        ((m : ℝ) * ‖ssTerm k l N m‖) * ((n : ℝ) * ‖ssTerm k l N n‖)
      rw [ssTerm_multiplicative k l N m n hk hl (by omega) (by omega) hmn, norm_mul]
      push_cast
      ring
  exact finite_euler_bound f hf (fun q => by change 0 ≤ (q : ℝ) * ‖ssTerm k l N q‖; positivity) Q

/-- LEAF. Halupczok pages 14 to 18, the prime power cases and products A to D.
The auxiliary scale X bounds the fixed moduli and N. The result is uniform in Q.
Noncompatible residues have zero coefficients and satisfy the same upper bound. -/
theorem local_product_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k l : Fin 3 → ℕ) (N : ℕ) (X : ℝ),
      (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) → Odd N →
      (N : ℝ) ≤ X → (∀ i, (k i : ℝ) ≤ X) → 1 ≤ Real.log X →
      ∀ Q : ℕ, primeProduct k l N Q ≤ C * rawWeight k * Real.log X ^ 11 := by
  sorry

/-- Halupczok page 18, the arithmetic envelope is nonnegative. -/
theorem rawWeight_nonneg (k : Fin 3 → ℕ) : 0 ≤ rawWeight k := by
  unfold rawWeight gcdWeight
  positivity

/-- Halupczok page 18, positive moduli give a positive arithmetic denominator. -/
theorem phiProduct_pos (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) : 0 < phiProduct k := by
  apply prod_pos
  intro i _
  exact_mod_cast Nat.totient_pos.mpr (by have := hk i; omega)

/-- Halupczok page 11 and page 18, the first weighted coefficient is nonzero. -/
theorem weightedCoeff_one (k l : Fin 3 → ℕ) (N : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) :
    weightedCoeff k l N 1 = 1 / phiProduct k := by
  simp [weightedCoeff, ssTerm_one hk hl]

/-- Halupczok page 18, every summable admissible coefficient moment is positive.
This implication has a summability premise and has clean axioms on its own. -/
theorem coefficientMass_pos_of_summable (k l : Fin 3 → ℕ) (N : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hs : Summable (fun q : ℕ => weightedCoeff k l N q)) : 0 < coefficientMass k l N := by
  have hp : 0 < weightedCoeff k l N 1 := by
    rw [weightedCoeff_one k l N hk hl]
    exact one_div_pos.mpr (phiProduct_pos k hk)
  exact hp.trans_le (hs.le_tsum 1 (fun q _ => weightedCoeff_nonneg k l N q))

/-- Halupczok page 18, remove the zero term before using positive partial moments. -/
theorem range_sum_le_positive (f : ℕ → ℝ) (h0 : f 0 = 0)
    (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    ∑ q ∈ range Q, f q ≤ ∑ q ∈ Icc 1 Q, f q := by
  have he : ∑ q ∈ Icc 1 Q, f q = ∑ q ∈ range (Q + 1), f q := by
    apply sum_subset
    · intro q hq
      exact mem_range.mpr (by have := mem_Icc.mp hq; omega)
    · intro q hq hn
      have hq0 : q = 0 := by
        have := mem_range.mp hq
        simp only [mem_Icc, not_and, not_le] at hn
        omega
      simpa [hq0] using h0
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun q _ _ => hf q)

/-- Halupczok page 18, bounded raw partial moments imply weighted convergence.
This generic transfer uses no unproved coefficient estimate. -/
theorem summable_of_raw_bound (k l : Fin 3 → ℕ) (N : ℕ) (C : ℝ)
    (hC : ∀ Q : ℕ, ∑ q ∈ Icc 1 Q, (q : ℝ) * ‖ssTerm k l N q‖ ≤ C) :
    Summable (fun q : ℕ => weightedCoeff k l N q) := by
  have hs : Summable (fun q : ℕ => (q : ℝ) * ‖ssTerm k l N q‖) := by
    apply summable_of_sum_range_le (fun q => mul_nonneg (Nat.cast_nonneg q) (norm_nonneg _))
    intro Q
    exact (range_sum_le_positive _ (by simp)
      (fun q => mul_nonneg (Nat.cast_nonneg q) (norm_nonneg _)) Q).trans (hC Q)
  exact hs.div_const _

/-- Exact supply for the sealed weighted coefficient convergence leaf.
CONDITIONAL ON local_product_bound only. -/
theorem weighted_coeff_summable (k l : Fin 3 → ℕ) (N : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) (hN : Odd N) :
    Summable (fun q : ℕ => weightedCoeff k l N q) := by
  obtain ⟨C, hC, hb⟩ := local_product_bound
  let X : ℝ := max (Real.exp 1) (max (N : ℝ) (∑ i : Fin 3, (k i : ℝ)))
  have hNX : (N : ℝ) ≤ X := (le_max_left _ _).trans (le_max_right _ _)
  have hkX : ∀ i, (k i : ℝ) ≤ X := by
    intro i
    exact (single_le_sum (fun j _ => Nat.cast_nonneg (k j)) (mem_univ i)).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hX : 0 < X := (Real.exp_pos 1).trans_le (le_max_left _ _)
  have hL : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX).mpr (le_max_left _ _)
  apply summable_of_raw_bound k l N (C * rawWeight k * Real.log X ^ 11)
  intro Q
  exact (finite_euler_domination k l N Q hk hl).trans (hb k l N X hk hl hN hNX hkX hL Q)

/-- Halupczok page 18, the same finite estimates control the actual infinite moment.
CONDITIONAL ON local_product_bound, with an explicit auxiliary scale. -/
theorem coefficientMass_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k l : Fin 3 → ℕ) (N : ℕ) (X : ℝ),
      (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) → Odd N →
      (N : ℝ) ≤ X → (∀ i, (k i : ℝ) ≤ X) → 1 ≤ Real.log X →
      coefficientMass k l N ≤ C * Real.log X ^ 11 * (rawWeight k / phiProduct k) := by
  obtain ⟨C, hC, hb⟩ := local_product_bound
  refine ⟨C, hC, fun k l N X hk hl hN hNX hkX hL => ?_⟩
  have hs := weighted_coeff_summable k l N hk hl hN
  unfold coefficientMass
  apply hs.tsum_le_of_sum_range_le
  intro Q
  calc
    _ ≤ (∑ q ∈ Icc 1 Q, (q : ℝ) * ‖ssTerm k l N q‖) / phiProduct k := by
      rw [sum_div]
      exact range_sum_le_positive (fun q => weightedCoeff k l N q)
        (by simp [weightedCoeff]) (weightedCoeff_nonneg k l N) Q
    _ ≤ (C * rawWeight k * Real.log X ^ 11) / phiProduct k :=
      div_le_div_of_nonneg_right
        ((finite_euler_domination k l N Q hk hl).trans (hb k l N X hk hl hN hNX hkX hL Q))
        (phiProduct_nonneg k)
    _ = _ := by ring

end LeanLab.Tolev2009.Decomp355a
