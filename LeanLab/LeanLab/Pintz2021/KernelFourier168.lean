import LeanLab.Pintz2021.DifferenceTask53
import LeanLab.Pintz2021.WeightedKernelsTask08
import LeanLab.Pintz2021.Truncation168

/-!
Finite Fourier evaluation behind P0054 page 6 display 2.11.
The proof extends the task53 diagonal identity to two supplied coefficient sequences.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.KernelFourier168

open Complex Finset MeasureTheory MinorArcs
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher

/-- Orthogonality identifies the coefficient of the conjugated product. -/
theorem mixed_coefficient (a b : ℕ → ℂ) (K m : ℕ) :
    coef (fun β => (∑ n ∈ range K, a n * e (n * β)) *
      (starRingEnd ℂ) (∑ n ∈ range K, b n * e (n * β))) m =
      ∑ n1 ∈ range K, ∑ n2 ∈ range K,
        if n1 = n2 + m then a n1 * (starRingEnd ℂ) (b n2) else 0 := by
  unfold coef
  have hpt : ∀ β : ℝ,
      (∑ n ∈ range K, a n * e (n * β)) *
        (starRingEnd ℂ) (∑ n ∈ range K, b n * e (n * β)) * e (-(m * β)) =
      ∑ n1 ∈ range K, ∑ n2 ∈ range K,
        (a n1 * (starRingEnd ℂ) (b n2)) *
          e ((((n1 : ℤ) - n2 - m : ℤ) : ℝ) * β) := by
    intro β
    rw [map_sum, sum_mul_sum, sum_mul]
    apply sum_congr rfl
    intro n1 _
    rw [sum_mul]
    apply sum_congr rfl
    intro n2 _
    rw [map_mul, ← e_neg]
    have he : e ((((n1 : ℤ) - n2 - m : ℤ) : ℝ) * β) =
        e (n1 * β) * e (-(n2 * β)) * e (-(m * β)) := by
      rw [← e_add, ← e_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  simp_rw [hpt]
  have hc : ∀ n1 n2 : ℕ, Continuous fun β : ℝ =>
      (a n1 * (starRingEnd ℂ) (b n2)) *
        e ((((n1 : ℤ) - n2 - m : ℤ) : ℝ) * β) :=
    fun n1 n2 => continuous_const.mul (continuous_e_mul _)
  rw [intervalIntegral.integral_finsetSum fun n1 _ =>
    (continuous_finsetSum _ fun n2 _ => hc n1 n2).intervalIntegrable _ _]
  apply sum_congr rfl
  intro n1 _
  rw [intervalIntegral.integral_finsetSum fun n2 _ => (hc n1 n2).intervalIntegrable _ _]
  apply sum_congr rfl
  intro n2 _
  rw [intervalIntegral.integral_const_mul, integral_e_int]
  by_cases h : n1 = n2 + m
  · simp [h]
  · have hz : ((n1 : ℤ) - n2 - m : ℤ) ≠ 0 := by omega
    simp [h, hz]

/-- The exact positive integer coefficient in the exceptional zero polynomial. -/
noncomputable def zeroWeight (X1 X : ℝ) (ρ : ℂ) (n : ℕ) : ℂ :=
  if 0 < n ∧ X1 < n ∧ (n : ℝ) ≤ X then (n : ℂ) ^ (ρ - 1) else 0

/-- The finite exponential polynomial T of a supplied exceptional parameter. -/
noncomputable def zeroPolynomial (X1 X : ℝ) (ρ : ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ range (⌊X⌋₊ + 1), zeroWeight X1 X ρ n * e (n * α)

/-- The exact difference kernel is the mixed finite Fourier coefficient. -/
theorem kernel_eq_coefficient (X1 : ℝ) {X : ℝ} (hX : 0 ≤ X) (ρ σ : ℂ) (m : ℕ) :
    coef (fun α => zeroPolynomial X1 X ρ α *
      (starRingEnd ℂ) (zeroPolynomial X1 X σ α)) m =
        WeightedKernelsTask08.weightedKernel X1 X ρ σ m true := by
  unfold zeroPolynomial
  rw [mixed_coefficient]
  have hi : Ico 1 (⌊X⌋₊ + 1) = Icc 1 ⌊X⌋₊ := by
    ext n
    simp only [mem_Ico, mem_Icc]
    omega
  have hz : ∀ z : ℂ, zeroWeight X1 X z 0 = 0 := by
    intro z
    simp [zeroWeight]
  simp_rw [sum_range_eq_add_Ico _ (Nat.succ_pos ⌊X⌋₊)]
  simp only [hz, zero_mul, map_zero, mul_zero, ite_self, sum_const_zero, zero_add, hi]
  simp only [WeightedKernelsTask08.weightedKernel, WeightedKernelsTask08.kernelPairs,
    sum_filter, sum_product, ↓reduceIte]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro l hl
  have hw : ∀ n ∈ Icc 1 ⌊X⌋₊, ∀ z : ℂ,
      zeroWeight X1 X z n = if X1 < n then (n : ℂ) ^ (z - 1) else 0 := by
    intro n hn z
    obtain ⟨hn0, hnX⟩ := mem_Icc.mp hn
    have hnpos : 0 < n := by omega
    have hnX' : (n : ℝ) ≤ X :=
      (by exact_mod_cast hnX : (n : ℝ) ≤ ⌊X⌋₊).trans (Nat.floor_le hX)
    simp [zeroWeight, hnpos, hnX']
  have hc : (starRingEnd ℂ) ((l : ℂ) ^ (σ - 1)) =
      (l : ℂ) ^ ((starRingEnd ℂ) σ - 1) := by
    simpa using (Complex.cpow_conj (l : ℂ) (σ - 1)
      (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)).symm
  have hrel : (k : ℤ) - l = (m : ℤ) ↔ k = l + m := by omega
  rw [hw k hk ρ, hw l hl σ]
  by_cases hk1 : X1 < k <;> by_cases hl1 : X1 < l <;> by_cases hm : k = l + m <;>
    simp [hk1, hl1, hm, hrel, hc]

/-- Each exceptional zero polynomial is continuous on the real line. -/
theorem continuous_zeroPolynomial (X1 X : ℝ) (ρ : ℂ) :
    Continuous (zeroPolynomial X1 X ρ) := by
  unfold zeroPolynomial
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_e_mul _)

/-- A finite mixture of exceptional zero pairs has exactly the discrete kernel coefficients. -/
theorem finite_model_coefficient (F : Finset (State1581.ExcPair × State1581.ExcPair))
    (A : State1581.ExcPair × State1581.ExcPair → ℂ)
    (X1 : ℝ) {X : ℝ} (hX : 0 ≤ X) (m : ℕ) :
    coef (fun α => ∑ p ∈ F, A p *
      (zeroPolynomial X1 X p.1.ρ α * (starRingEnd ℂ) (zeroPolynomial X1 X p.2.ρ α))) m =
      ∑ p ∈ F, A p * WeightedKernelsTask08.weightedKernel X1 X p.1.ρ p.2.ρ m true := by
  have hc : ∀ p : State1581.ExcPair × State1581.ExcPair,
      Continuous (fun α : ℝ => A p *
        (zeroPolynomial X1 X p.1.ρ α * (starRingEnd ℂ) (zeroPolynomial X1 X p.2.ρ α)) *
          e (-(m * α))) := by
    intro p
    exact (continuous_const.mul ((continuous_zeroPolynomial _ _ _).mul
      (Complex.continuous_conj.comp (continuous_zeroPolynomial _ _ _)))).mul
        (by simpa [neg_mul] using continuous_e_mul (-(m : ℝ)))
  unfold coef
  simp_rw [sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun p _ => (hc p).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro p _
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  simp_rw [← mul_assoc]
  change A p * coef (fun α => zeroPolynomial X1 X p.1.ρ α *
    (starRingEnd ℂ) (zeroPolynomial X1 X p.2.ρ α)) m = _
  rw [kernel_eq_coefficient X1 hX]

/-- The supplied S prime and multiplicities give precisely the existing finite main term. -/
theorem mainTermPrime_coefficient (E : Finset State1581.ExcPair)
    (Sg : State1581.ExcPair → State1581.ExcPair → ℕ → ℂ)
    (ε : ℝ) {X : ℝ} (hX : 0 ≤ X) (m : ℕ) :
    coef (fun α => ∑ p ∈ E ×ˢ E,
      (((State1581.mult p.1 * State1581.mult p.2 : ℕ) : ℂ) *
        (State1581.Asign p.1 : ℂ) * (State1581.Asign p.2 : ℂ) * Sg p.1 p.2 m) *
          (zeroPolynomial (State1581.X1 ε X) X p.1.ρ α *
            (starRingEnd ℂ) (zeroPolynomial (State1581.X1 ε X) X p.2.ρ α))) m =
      DecompJ281.mainTermPrime (E : Set State1581.ExcPair) Sg ε X m := by
  rw [finite_model_coefficient _ _ _ hX, Truncation168.mainTermPrime_eq_sum]
  rfl

end LeanLab.Pintz2021.KernelFourier168

#print axioms LeanLab.Pintz2021.KernelFourier168.mixed_coefficient

#print axioms LeanLab.Pintz2021.KernelFourier168.kernel_eq_coefficient

#print axioms LeanLab.Pintz2021.KernelFourier168.continuous_zeroPolynomial
#print axioms LeanLab.Pintz2021.KernelFourier168.finite_model_coefficient
#print axioms LeanLab.Pintz2021.KernelFourier168.mainTermPrime_coefficient
