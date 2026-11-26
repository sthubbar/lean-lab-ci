/-
P0068 Zhan 1991, page 268, first inequality of the proof of Proposition 3: the LEAF
`cauchy_311_leaf_S9` of SPLIT_prop3_311_S9.lean, PROVED. Burst 20261124, session S9, unit
B-extra-1. Cauchy's inequality in `t` for each character, by Hölder with exponents `2, 2`, then
Cauchy's inequality over the characters. AI-written Lean code, Claude. Checked only by the Lean
kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.SPLIT_prop3_311_S9

namespace LeanLab.Zhan1991
open Finset Real MeasureTheory

noncomputable section

/-- `F_J(1/2 + it, χ)` of page 268 is continuous in `t`. -/
theorem FJ311_continuous_S9 {q : ℕ} (Nv : Fin 20 → ℝ) (J : Finset (Fin 20))
    (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => FJ311 Nv J χ (1 / 2 + t * Complex.I)) := by
  unfold FJ311 fj
  apply continuous_finsetProd
  intro j _
  apply continuous_finsetSum
  intro n hn
  have hn1 : 1 ≤ n := by
    simp only [dyad, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1.1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))

/-- Cauchy's inequality for integrals over `(a, b]` of continuous nonnegative functions. -/
theorem integral_cauchy_Ioc_S9 (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t) (a b : ℝ) :
    ∫ t in Set.Ioc a b, f t * g t ≤
      Real.sqrt (∫ t in Set.Ioc a b, f t ^ 2) * Real.sqrt (∫ t in Set.Ioc a b, g t ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hfm : MemLp f (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) := by
    rw [h2]
    exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
      ((hf.pow 2).integrableOn_Ioc)
  have hgm : MemLp g (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) := by
    rw [h2]
    exact (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
      ((hg.pow 2).integrableOn_Ioc)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Set.Ioc a b)) hpq
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0) hfm hgm
  simp only [Real.rpow_two] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h

/-- PROVED: the LEAF `cauchy_311_leaf_S9`, page 268, first inequality of the proof of
Proposition 3. Same statement. -/
theorem cauchy_311_proof_S9 (Nv : Fin 20 → ℝ) (q : ℕ) [NeZero q] (J1 : Finset (Fin 20))
    (T1 H : ℝ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Ioc T1 (T1 + H), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ Real.sqrt (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + H), ‖FJ311 Nv J1 χ (1 / 2 + t * Complex.I)‖ ^ 2) *
        Real.sqrt (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + H), ‖FJ311 Nv J1ᶜ χ (1 / 2 + t * Complex.I)‖ ^ 2) := by
  have hsplit : ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖ =
        ‖FJ311 Nv J1 χ (1 / 2 + t * Complex.I)‖ * ‖FJ311 Nv J1ᶜ χ (1 / 2 + t * Complex.I)‖ := by
    intro χ t
    rw [← norm_mul]
    unfold Fprod FJ311
    rw [Finset.prod_mul_prod_compl]
  calc _ = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + H),
            ‖FJ311 Nv J1 χ (1 / 2 + t * Complex.I)‖ * ‖FJ311 Nv J1ᶜ χ (1 / 2 + t * Complex.I)‖ := by
        simp only [hsplit]
    _ ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          Real.sqrt (∫ t in Set.Ioc T1 (T1 + H), ‖FJ311 Nv J1 χ (1 / 2 + t * Complex.I)‖ ^ 2) *
          Real.sqrt (∫ t in Set.Ioc T1 (T1 + H), ‖FJ311 Nv J1ᶜ χ (1 / 2 + t * Complex.I)‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro χ _
        exact integral_cauchy_Ioc_S9 _ _ (FJ311_continuous_S9 Nv J1 χ).norm
          (FJ311_continuous_S9 Nv J1ᶜ χ).norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) _ _
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _
          (fun χ => integral_nonneg (fun _ => by positivity))
          (fun χ => integral_nonneg (fun _ => by positivity))

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.integral_cauchy_Ioc_S9
#print axioms LeanLab.Zhan1991.cauchy_311_proof_S9
