/-
Elementary bounds for the maximal character mean used at P0088 page 17.
The resulting bound is too weak in the intermediate conductor range.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp557a
import LeanLab.PNTPort.PsiChi.Final

namespace LeanLab.KumchevLiu2007.Task634

open Real Complex MeasureTheory Task557a
open scoped BigOperators Topology

/-- Davenport chapter 28 page 162, the endpoint character maximum is at most
the ordinary Chebyshev function. -/
theorem primitiveMax_le_psi {q : ℕ} [NeZero q] (T : ℝ)
    (χ : DirichletCharacter ℂ q) : primitiveMax T χ ≤ Chebyshev.psi T := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro v (rfl | ⟨x, _, hxT, rfl⟩)
  · exact Chebyshev.psi_nonneg T
  · exact (LeanLab.PNTPort.PsiChi.norm_psiChi_le χ x).trans (Chebyshev.psi_mono hxT)

/-- Davenport chapter 28 page 162, a weak maximal mean bound from Chebyshev
and the one term instance of the proved multiplicative large sieve. -/
theorem maximal_character_mean_trivial (T : ℝ) (hT : 0 ≤ T) (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter
        (fun χ => χ.IsPrimitive), primitiveMax T χ) ≤
      (1 + 2 * (Q : ℝ) ^ 2) * (Real.log 4 + 4) * T := by
  classical
  have hw := Task557a.large_sieve hQ (fun _ => (1 : ℂ)) 0 1
  have hI : Finset.Ioc (0 : ℤ) (0 + ((1 : ℕ) : ℤ)) = {1} := by decide
  rw [hI] at hw
  simp only [Finset.sum_singleton, one_mul, Int.cast_one, map_one, norm_one, one_pow,
    Nat.cast_one, mul_one] at hw
  calc
    _ ≤ ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
        ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter
          (fun χ => χ.IsPrimitive), Chebyshev.psi T := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro χ hχ
      exact primitiveMax_le_psi T χ
    _ = Chebyshev.psi T * (∑ k ∈ Finset.range Q,
        ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
          ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter
            (fun χ => χ.IsPrimitive), (1 : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      ring
    _ ≤ Chebyshev.psi T * (1 + 2 * (Q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hw (Chebyshev.psi_nonneg T)
    _ ≤ ((Real.log 4 + 4) * T) * (1 + 2 * (Q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self hT) (by positivity)
    _ = _ := by ring

/-- Davenport chapter 28 page 162, the target maximal mean bound holds in
the elementary range where Q is at most the square of log T. -/
theorem maximal_character_mean_log_range (T : ℝ) (hT : 2 ≤ T) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQlog : (Q : ℝ) ≤ Real.log T ^ 2) :
    (∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter
        (fun χ => χ.IsPrimitive), primitiveMax T χ) ≤
      (3 * (Real.log 4 + 4)) *
        (T + T ^ (5 / 6 : ℝ) * Q + Real.sqrt T * (Q : ℝ) ^ 2) *
          Real.log (2 * T * Q) ^ 4 := by
  have hT0 : 0 < T := by linarith
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hL : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlog : Real.log T ≤ Real.log (2 * T * Q) :=
    Real.log_le_log hT0 (by nlinarith)
  have hpow : Real.log T ^ 4 ≤ Real.log (2 * T * Q) ^ 4 :=
    pow_le_pow_left₀ hL hlog 4
  have hQsq : (Q : ℝ) ^ 2 ≤ Real.log T ^ 4 := by
    have h := pow_le_pow_left₀ hQ0 hQlog 2
    nlinarith
  have hOne : 1 ≤ Real.log T ^ 4 := by
    nlinarith [sq_nonneg ((Q : ℝ) - 1)]
  have hw : 1 + 2 * (Q : ℝ) ^ 2 ≤ 3 * Real.log (2 * T * Q) ^ 4 := by
    linarith
  have hC : 0 ≤ Real.log 4 + 4 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  have hmain : T ≤ T + T ^ (5 / 6 : ℝ) * Q + Real.sqrt T * (Q : ℝ) ^ 2 := by
    have ha : 0 ≤ T ^ (5 / 6 : ℝ) * Q := by positivity
    have hb : 0 ≤ Real.sqrt T * (Q : ℝ) ^ 2 := by positivity
    linarith
  calc
    _ ≤ (1 + 2 * (Q : ℝ) ^ 2) * (Real.log 4 + 4) * T :=
      maximal_character_mean_trivial T hT0.le Q hQ
    _ ≤ (3 * Real.log (2 * T * Q) ^ 4) * (Real.log 4 + 4) * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw hC) hT0.le
    _ = (3 * (Real.log 4 + 4)) * T * Real.log (2 * T * Q) ^ 4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmain (by positivity)) (by positivity)

end LeanLab.KumchevLiu2007.Task634

#print axioms LeanLab.KumchevLiu2007.Task634.primitiveMax_le_psi
#print axioms LeanLab.KumchevLiu2007.Task634.maximal_character_mean_trivial
#print axioms LeanLab.KumchevLiu2007.Task634.maximal_character_mean_log_range
