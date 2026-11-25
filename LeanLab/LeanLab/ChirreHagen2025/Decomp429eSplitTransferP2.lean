import LeanLab.ChirreHagen2025.Decomp429eSplitTransfer

/-!
Second split of `Decomp429eSplitTransfer.mangoldt_partial_summation_identity`,
burst-20261122, session S123. Ramare 2013 page 118 and JRT 2023 page 3 proof of
Lemma 9. The identity is assembled from a finite partial summation identity up to x,
integrability of (psi t - t)/t^2 on (1, infinity), and the constant identity
1 + gamma + integral over (1, infinity) of (psi t - t)/t^2 = 0.
The assembly step, splitting the integral at x and evaluating the integral of 1/t,
is proved here. AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2
open ArithmeticFunction MeasureTheory Set

/-- Ramare 2013 page 118, Abel partial summation of the Mangoldt sum with weight
1/n, written as psi x / x plus the integral over (1, x] of psi t / t^2. PROVED S123 by
Mathlib's Abel summation `sum_mul_eq_sub_sub_integral_mul`. -/
theorem mangoldt_abel_finite (x : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      Chebyshev.psi x / x + ∫ t in Set.Ioc 1 x, Chebyshev.psi t / t ^ 2 := by
  have hx1 : (1 : ℝ) ≤ x := hx
  have hfl : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have hA := sum_mul_eq_sub_sub_integral_mul (fun n : ℕ => (vonMangoldt n : ℝ))
    (f := fun t : ℝ => t⁻¹) (a := 1) (b := x) zero_le_one hx1
    (fun t ht => differentiableAt_inv (by linarith [ht.1]))
    (by
      have : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc 1 x) := by
        apply ContinuousOn.neg
        apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
        intro t ht; have : (1:ℝ) ≤ t := ht.1; exact pow_ne_zero 2 (lt_of_lt_of_le one_pos this).ne'
      refine (this.integrableOn_Icc).congr_fun (fun t _ => ?_) measurableSet_Icc
      simp [deriv_inv])
  have hL : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      ∑ k ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊x⌋₊, (fun t : ℝ => t⁻¹) (k : ℝ) * (vonMangoldt k : ℝ) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc hfl]
    simp [div_eq_inv_mul]
  rw [hL, hA, ← Chebyshev.psi_eq_sum_Icc]
  have h01 : (∑ k ∈ Finset.Icc 0 ⌊(1 : ℝ)⌋₊, (vonMangoldt k : ℝ)) = 0 := by
    simp [Finset.sum_Icc_succ_top]
  rw [h01]
  have hI : (∫ t in Set.Ioc 1 x, deriv (fun t : ℝ => t⁻¹) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (vonMangoldt k : ℝ)) =
      -∫ u in Set.Ioc 1 x, Chebyshev.psi u / u ^ 2 := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [deriv_inv, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [hI]
  simp [div_eq_inv_mul]

/-- LEAF: Ramare 2013 page 118, the prime number theorem with error term, used to make
the improper integral of (psi t - t)/t^2 over (1, infinity) absolutely convergent.
Class HARD. -/
theorem psi_error_integrableOn :
    IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) (Set.Ioi 1) := by
  sorry

/-- LEAF: JRT 2023 page 3 proof of Lemma 9, the constant identity
1 + gamma + integral over (1, infinity) of (psi t - t)/t^2 = 0. Class HARD. -/
theorem psi_error_integral_const :
    ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2 =
      -1 - Real.eulerMascheroniConstant := by
  sorry

/-- Exact statement of `Decomp429eSplitTransfer.mangoldt_partial_summation_identity`.
CONDITIONAL ON the three LEAFs above. -/
theorem mangoldt_partial_summation_identity_of_leaves (x : ℝ) (hx : 100000 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      Real.log x - Real.eulerMascheroniConstant + (Chebyshev.psi x - x) / x -
        ∫ t in Set.Ioi x, (Chebyshev.psi t - t) / t ^ 2 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hI := psi_error_integrableOn
  have hIoc : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) (Set.Ioc 1 x) :=
    hI.mono_set Set.Ioc_subset_Ioi_self
  have hIoi : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) (Set.Ioi x) :=
    hI.mono_set (Set.Ioi_subset_Ioi hx1)
  have hsplit : ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2 =
      (∫ t in Set.Ioc 1 x, (Chebyshev.psi t - t) / t ^ 2) +
        ∫ t in Set.Ioi x, (Chebyshev.psi t - t) / t ^ 2 := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx1]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc hIoi
  have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 1 x) := by
    have : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) :=
      continuousOn_inv₀.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1])
    exact (this.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hlog : ∫ t in Set.Ioc 1 x, t⁻¹ = Real.log x := by
    rw [← intervalIntegral.integral_of_le hx1, integral_inv_of_pos one_pos hx0, div_one]
  have hpt : ∫ t in Set.Ioc 1 x, Chebyshev.psi t / t ^ 2 =
      ∫ t in Set.Ioc 1 x, ((Chebyshev.psi t - t) / t ^ 2 + t⁻¹) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have ht0 : t ≠ 0 := by linarith [ht.1]
    field_simp
    ring
  have hadd : ∫ t in Set.Ioc 1 x, ((Chebyshev.psi t - t) / t ^ 2 + t⁻¹) =
      (∫ t in Set.Ioc 1 x, (Chebyshev.psi t - t) / t ^ 2) + ∫ t in Set.Ioc 1 x, t⁻¹ :=
    integral_add hIoc hinv
  rw [mangoldt_abel_finite x hx1, hpt, hadd, hlog]
  have hc := psi_error_integral_const
  rw [hsplit] at hc
  have hxx : (Chebyshev.psi x - x) / x = Chebyshev.psi x / x - 1 := by
    field_simp
  rw [hxx]
  linarith

end LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2

#print axioms LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2.mangoldt_partial_summation_identity_of_leaves
#print axioms LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2.mangoldt_abel_finite
