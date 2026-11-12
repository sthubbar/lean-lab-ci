/-
PP1993 page 44 display 3: separate prime weights from the Fourier operator.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
The weighted short interval estimate is a derived Brun Titchmarsh input.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp489g

namespace LeanLab.Languasco2004.Decomp489d
open Finset Real MeasureTheory Decomp279b Decomp413a
open scoped ArithmeticFunction.vonMangoldt
noncomputable section

/-- LEAF. Page 44 display 3 cites Brun Titchmarsh without printing its
statement. This is the derived short interval Mangoldt form needed here.
It must be checked against the cited source before its admission is removed. -/
theorem short_mangoldt_input :
  ∀ ε : ℝ, 0 < ε → ∃ C N₀ : ℝ, 0 < C ∧ ∀ N Y : ℝ,
    N₀ ≤ N → N ^ ε ≤ Y → Y ≤ N →
      (∑ n ∈ Ioc ⌊N - Y⌋₊ ⌊N⌋₊, Λ n) ≤ C * Y := by sorry

/-- Page 44 display 3: each squared Mangoldt weight is at most log N
 times its unsquared weight when its index is positive and at most N. -/
theorem mangoldt_square_le {N : ℝ} {n : ℕ} (hn : 1 ≤ n) (hnN : (n : ℝ) ≤ N) :
    (Λ n) ^ 2 ≤ Real.log N * Λ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : Λ n ≤ Real.log N :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnN)
  nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]

/-- Page 44 display 3: summing the pointwise square estimate for S1.
The short prime weight input is kept as an explicit premise. -/
theorem firstWeight_of_mangoldt {N Y C : ℝ} (hN : 1 ≤ N)
    (hsum : (∑ n ∈ Ioc ⌊N - Y⌋₊ ⌊N⌋₊, Λ n) ≤ C * Y) :
    firstWeight N Y ≤ C * Y * Real.log N := by
  have hpoint : ∀ n ∈ Ioc ⌊N - Y⌋₊ ⌊N⌋₊, (Λ n) ^ 2 ≤ Real.log N * Λ n := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hn
    apply mangoldt_square_le (by omega)
    exact (show (n : ℝ) ≤ (⌊N⌋₊ : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith))
  calc firstWeight N Y ≤ ∑ n ∈ Ioc ⌊N - Y⌋₊ ⌊N⌋₊, Real.log N * Λ n :=
      Finset.sum_le_sum hpoint
    _ = Real.log N * ∑ n ∈ Ioc ⌊N - Y⌋₊ ⌊N⌋₊, Λ n := by rw [Finset.mul_sum]
    _ ≤ Real.log N * (C * Y) := mul_le_mul_of_nonneg_left hsum (Real.log_nonneg hN)
    _ = C * Y * Real.log N := by ring

/-- Page 44 display 3: the full S2 weight bound follows from Mathlib's
Chebyshev bound and does not require a short interval input. -/
theorem secondWeight_bound {N Y : ℝ} (hN : 1 ≤ N) (hY : 0 ≤ Y) (hYN : Y ≤ N) :
    secondWeight Y ≤ (Real.log 4 + 4) * Y * Real.log N := by
  have hpoint : ∀ n ∈ Icc 1 ⌊Y⌋₊, (Λ n) ^ 2 ≤ Real.log N * Λ n := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    apply mangoldt_square_le hlo
    exact ((show (n : ℝ) ≤ (⌊Y⌋₊ : ℝ) by exact_mod_cast hhi).trans (Nat.floor_le hY)).trans hYN
  have hsum : (∑ n ∈ Icc 1 ⌊Y⌋₊, Λ n) = Chebyshev.psi Y := by
    rw [Chebyshev.psi]
    congr 1
  calc secondWeight Y ≤ ∑ n ∈ Icc 1 ⌊Y⌋₊, Real.log N * Λ n := Finset.sum_le_sum hpoint
    _ = Real.log N * Chebyshev.psi Y := by rw [← Finset.mul_sum, hsum]
    _ ≤ Real.log N * ((Real.log 4 + 4) * Y) :=
      mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self hY) (Real.log_nonneg hN)
    _ = (Real.log 4 + 4) * Y * Real.log N := by ring

/-- LEAF. Page 44 display 3: the finite Fourier kernel comparison followed
by Cauchy Schwarz and Parseval, before any prime weight estimate.
This elementary operator leaf is independent of the cited density results. -/
theorem short_coefficient_operator :
    ∀ N Y H B K : ℝ, 16 ≤ H → 0 ≤ K →
      (∀ ξ : ℝ, kernelMass N Y H B ξ ≤ K) →
      (∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even,
        ‖minorCoefficient N Y H B m‖ ^ 2) ^ 2 ≤
        firstWeight N Y ^ 2 * secondWeight Y * K := by
  intro N Y H B K hH hK hk
  have hfinite := Decomp489g.finite_kernel_energy N Y H B K hH hK hk
  have hfirst := FiniteParseval489.first_minor_energy_le N Y H B
  have hsecond := FiniteParseval489.second_minor_energy_le N Y H B
  have hfirst0 : 0 ≤ ∫ x in minorDomain N Y H B, ‖firstSum N Y x‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hsecond0 : 0 ≤ ∫ x in minorDomain N Y H B, ‖secondSum Y x‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hweight :
      (∫ x in minorDomain N Y H B, ‖firstSum N Y x‖ ^ 2) ^ 2 *
        (∫ x in minorDomain N Y H B, ‖secondSum Y x‖ ^ 2) ≤
        firstWeight N Y ^ 2 * secondWeight Y :=
    mul_le_mul (pow_le_pow_left₀ hfirst0 hfirst 2) hsecond hsecond0 (sq_nonneg _)
  exact hfinite.trans (mul_le_mul_of_nonneg_right hweight hK)

#print axioms firstWeight
#print axioms secondWeight
#print axioms short_mangoldt_input
#print axioms mangoldt_square_le
#print axioms firstWeight_of_mangoldt
#print axioms secondWeight_bound
#print axioms short_coefficient_operator
end
end LeanLab.Languasco2004.Decomp489d
