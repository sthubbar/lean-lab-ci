import LeanLab.LanguascoPerelli1996.FiniteEnergy108
import LeanLab.LanguascoPerelli1996.Band108

/-!
The character zero sum specialization of P0071 page 354 display 11.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Correlation108
open Complex Real MeasureTheory

/-- Page 349. The sealed pairSum equals the corresponding finite double sum. -/
theorem pairSum_eq_sum {q : ℕ} [NeZero q] (X T : ℝ) (χ₁ χ₂ : DirichletCharacter ℂ q) :
    pairSum X T χ₁ χ₂ =
      ∑ ρ₁ ∈ (Zeros108.ntZeros_finite χ₁ T).toFinset,
        ∑ ρ₂ ∈ (Zeros108.ntZeros_finite χ₂ T).toFinset,
          ((mult χ₁ ρ₁ * mult χ₂ ρ₂ : ℕ) : ℂ) *
            Complex.exp (Complex.I * ((ρ₁.im - ρ₂.im : ℝ) : ℂ) * (Real.log X : ℂ)) *
            (w (ρ₁.im - ρ₂.im) : ℂ) := by
  classical
  unfold pairSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (Zeros108.ntZeros_finite χ₁ T)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [finsum_mem_eq_finite_toFinset_sum _ (Zeros108.ntZeros_finite χ₂ T)]

/-- LEAF. Page 354 display 11 for the sealed character correlation function.
The integrability assertion and identity do not require GRH. -/
theorem correlation_identity {X : ℝ} (hX : 0 < X) (T : ℝ)
    (q : ℕ) [NeZero q] (a : ℕ) :
    Integrable (fun v : ℝ => ‖zSum (X * Real.exp v) (-1) T q a‖ ^ 2 * Real.exp (-2 * |v|)) ∧
      ((∫ v : ℝ, ‖zSum (X * Real.exp v) (-1) T q a‖ ^ 2 *
        Real.exp (-2 * |v|) : ℝ) : ℂ) = F X T q a := by
  classical
  let s : Finset (Σ _χ : DirichletCharacter ℂ q, ℂ) :=
    Finset.univ.sigma (fun χ => (Zeros108.ntZeros_finite χ T).toFinset)
  let c : (Σ _χ : DirichletCharacter ℂ q, ℂ) → ℂ := fun i =>
    i.1 (a : ZMod q) * tau i.1⁻¹ * (mult i.1 i.2 : ℂ) *
      Complex.exp (Complex.I * (i.2.im : ℂ) * (Real.log X : ℂ))
  let γ : (Σ _χ : DirichletCharacter ℂ q, ℂ) → ℝ := fun i => i.2.im
  have hneg : {ρ : ℂ | |ρ.im| ≤ (-1 : ℝ)} = ∅ := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    linarith [abs_nonneg ρ.im]
  have hsum : ∀ v : ℝ, (∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)) =
      zSum (X * Real.exp v) (-1) T q a := by
    intro v
    rw [Band108.zSum_eq_sum]
    simp only [s, c, γ, Finset.sum_sigma, hneg, Set.sdiff_empty]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [Real.log_mul hX.ne' (Real.exp_pos v).ne', Real.log_exp,
      Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  have hpair : (∑ i ∈ s, ∑ j ∈ s, c i * starRingEnd ℂ (c j) * (w (γ i - γ j) : ℂ)) =
      F X T q a := by
    unfold F
    simp only [s, c, γ, Finset.sum_sigma, pairSum_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ₁ hχ₁
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ₂ hχ₂
    apply Finset.sum_congr rfl
    intro ρ₁ hρ₁
    apply Finset.sum_congr rfl
    intro ρ₂ hρ₂
    simp only [map_mul, map_natCast, ← Complex.exp_conj, Complex.conj_I,
      Complex.conj_ofReal, Nat.cast_mul, Complex.ofReal_sub]
    calc
      _ = χ₁ (a : ZMod q) * starRingEnd ℂ (χ₂ (a : ZMod q)) * tau χ₁⁻¹ *
          starRingEnd ℂ (tau χ₂⁻¹) * ((mult χ₁ ρ₁ : ℂ) * (mult χ₂ ρ₂ : ℂ)) *
          (Complex.exp (Complex.I * ρ₁.im * (Real.log X : ℂ)) *
            Complex.exp (-Complex.I * ρ₂.im * (Real.log X : ℂ))) *
          (w (ρ₁.im - ρ₂.im) : ℂ) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        have hphase : Complex.exp (Complex.I * ρ₁.im * (Real.log X : ℂ) +
            -Complex.I * ρ₂.im * (Real.log X : ℂ)) =
            Complex.exp (Complex.I * ((ρ₁.im : ℂ) - (ρ₂.im : ℂ)) * (Real.log X : ℂ)) := by
          congr 1
          ring
        rw [hphase]
        ring
  obtain ⟨hi, heq⟩ := FiniteEnergy108.finite_energy_identity s c γ
  simp only [hsum] at hi heq
  exact ⟨hi, heq.trans hpair⟩

end LeanLab.LanguascoPerelli1996.Correlation108
