import LeanLab.Xi2012.PrimeDivisorClosure

/-!
Xi 2012, arXiv 1206.2148v1, page 7 equation 14.
The weighted sums agree on primes. Their difference is bounded by the
non-prime part of Chebyshev psi. Mathlib supplies its square-root bound.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Xi2012.NatEncoding

open Finset

/-- The paper's e of n times alpha. -/
noncomputable def fourierPhase (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * (n : ℝ) * α : ℝ) : ℂ) * Complex.I)

/-- The selected-prime sum, with a general complex weight. -/
noncomputable def primeWeightedSum (A : Finset ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ p ∈ A, (Real.log p : ℂ) * f p

/-- The sum over positive integers up to x with a divisor in A. -/
noncomputable def closureWeightedSum (A : Finset ℕ) (x : ℕ) (f : ℕ → ℂ) : ℂ := by
  classical
  exact ∑ n ∈ (Icc 1 x).filter (HasPrimeDivisorIn A),
    (ArithmeticFunction.vonMangoldt n : ℂ) * f n

/-- The Fourier weights in equation 14 have norm 1. -/
theorem norm_fourierPhase (α : ℝ) (n : ℕ) : ‖fourierPhase α n‖ = 1 := by
  simp [fourierPhase, Complex.norm_exp]

/-- Selected primes cancel exactly. The remaining mass is at most psi minus theta. -/
theorem weighted_diff_le_psi_sub_theta (A : Finset ℕ) (x : ℕ)
    (hA : ∀ p ∈ A, Nat.Prime p ∧ p ≤ x) (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖closureWeightedSum A x f - primeWeightedSum A f‖ ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  classical
  have hsets : ((Icc 1 x).filter (HasPrimeDivisorIn A)).filter Nat.Prime = A := by
    ext n
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨⟨_hn1, _hnx⟩, hcl⟩, hp⟩
      exact (hasPrimeDivisorIn_prime_iff A (fun p hp => (hA p hp).1) hp).mp hcl
    · intro hn
      have hp := (hA n hn).1
      exact ⟨⟨⟨hp.one_lt.le, (hA n hn).2⟩, ⟨n, hn, dvd_rfl⟩⟩, hp⟩
  have hprime :
      (∑ n ∈ ((Icc 1 x).filter (HasPrimeDivisorIn A)).filter Nat.Prime,
        (ArithmeticFunction.vonMangoldt n : ℂ) * f n) = primeWeightedSum A f := by
    rw [hsets]
    unfold primeWeightedSum
    apply Finset.sum_congr rfl
    intro n hn
    rw [ArithmeticFunction.vonMangoldt_apply_prime (hA n hn).1]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Icc 1 x).filter (HasPrimeDivisorIn A)) Nat.Prime
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * f n)
  have hdiff : closureWeightedSum A x f - primeWeightedSum A f =
      ∑ n ∈ ((Icc 1 x).filter (HasPrimeDivisorIn A)).filter (fun n => ¬ Nat.Prime n),
        (ArithmeticFunction.vonMangoldt n : ℂ) * f n := by
    unfold closureWeightedSum
    rw [← hsplit, hprime]
    ring
  have hI : Icc 1 x = Ioc 0 ⌊(x : ℝ)⌋₊ := by
    ext n
    simp only [mem_Icc, mem_Ioc, Nat.floor_natCast]
    omega
  rw [hdiff]
  calc
    ‖∑ n ∈ ((Icc 1 x).filter (HasPrimeDivisorIn A)).filter (fun n => ¬ Nat.Prime n),
        (ArithmeticFunction.vonMangoldt n : ℂ) * f n‖ ≤
      ∑ n ∈ ((Icc 1 x).filter (HasPrimeDivisorIn A)).filter (fun n => ¬ Nat.Prime n),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * f n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ ((Icc 1 x).filter (HasPrimeDivisorIn A)).filter (fun n => ¬ Nat.Prime n),
        ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (hf n)
    _ ≤ ∑ n ∈ (Icc 1 x).filter (fun n => ¬ Nat.Prime n),
        ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [mem_filter] at hn ⊢
        exact ⟨hn.1.1, hn.2⟩
      · intro _ _ _
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Chebyshev.psi x - Chebyshev.theta x := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, ← hI]

/-- Page 7 equation 14, uniformly in the selected prime set and the phase. -/
theorem equation14 : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : Finset ℕ) (x : ℕ), (∀ p ∈ A, Nat.Prime p ∧ p ≤ x) →
      ∀ α : ℝ,
        ‖closureWeightedSum A x (fourierPhase α) -
          primeWeightedSum A (fourierPhase α)‖ ≤ C * Real.sqrt x := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C 0, le_max_right _ _, fun A x hA α => ?_⟩
  calc
    ‖closureWeightedSum A x (fourierPhase α) -
        primeWeightedSum A (fourierPhase α)‖ ≤
      Chebyshev.psi x - Chebyshev.theta x :=
        weighted_diff_le_psi_sub_theta A x hA _ (fun n => (norm_fourierPhase α n).le)
    _ ≤ C * Real.sqrt x := hC x
    _ ≤ max C 0 * Real.sqrt x :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)

end LeanLab.Xi2012.NatEncoding
