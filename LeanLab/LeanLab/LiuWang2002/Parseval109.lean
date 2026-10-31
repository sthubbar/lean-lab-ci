import LeanLab.LiuWang2002.Vaughan109

/-! Finite Parseval for the exponential sum in the proof on page 174.
AI wrote the Lean code. Binary Goldbach is open. -/

namespace LeanLab.LiuWang2002.Parseval109
open MeasureTheory Real Vaughan109
open scoped ComplexConjugate

/-- A finite real coefficient Fourier sum on the circle of period one. -/
noncomputable def circleSum (s : Finset ℕ) (w : ℕ → ℝ) : C(AddCircle (1 : ℝ), ℂ) :=
  ∑ n ∈ s, (w n : ℂ) • fourier (n : ℤ)

/-- Parseval for a finite coefficient sum, the identity used on page 174. -/
theorem finite_parseval (s : Finset ℕ) (w : ℕ → ℝ) :
    (∫ x : AddCircle (1 : ℝ), ‖circleSum s w x‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ n ∈ s, (w n) ^ 2 := by
  have ho := (orthonormal_fourier (T := (1 : ℝ))).comp (fun n : ℕ => (n : ℤ)) (by intro a b h; change (a : ℤ) = (b : ℤ) at h; exact_mod_cast h)
  have hi := ho.inner_sum (fun n => (w n : ℂ)) (fun n => (w n : ℂ)) s
  have heq : ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (circleSum s w) =
      ∑ n ∈ s, (w n : ℂ) • (fourierLp (T := (1 : ℝ)) 2 (n : ℤ)) := by
    simp [circleSum, map_sum, map_smul, fourierLp]
  change inner ℂ (∑ n ∈ s, (w n : ℂ) • fourierLp (T := (1 : ℝ)) 2 (n : ℤ))
    (∑ n ∈ s, (w n : ℂ) • fourierLp (T := (1 : ℝ)) 2 (n : ℤ)) = _ at hi
  rw [← heq, MeasureTheory.ContinuousMap.inner_toLp] at hi
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, map_sum,
    map_pow, Complex.conj_ofReal, ← Complex.ofReal_mul] at hi
  rw [integral_complex_ofReal] at hi
  apply Complex.ofReal_injective
  simpa [pow_two] using hi

/-- The circle sum lifts to the real exponential sum, display 3.8 on page 144. -/
theorem circleSum_coe (N c α : ℝ) :
    circleSum (Finset.range (Nat.floor N + 1))
      (fun n => if c * N ≤ (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0)
      (α : AddCircle (1 : ℝ)) = S N c α := by
  unfold circleSum S weightedSum
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, fourier_coe_apply,
    div_one, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp
  congr 2
  push_cast
  ring
  all_goals simp

/-- Parseval on the unit interval for the actual sum S, page 174. -/
theorem second_moment (N c : ℝ) :
    (∫ α in Set.Icc (0 : ℝ) 1, ‖S N c α‖ ^ 2) =
      ∑ n ∈ Finset.range (Nat.floor N + 1),
        (if c * N ≤ (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0) ^ 2 := by
  have hi := finite_parseval (Finset.range (Nat.floor N + 1))
    (fun n => if c * N ≤ (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0)
  rw [AddCircle.integral_haarAddCircle] at hi
  norm_num only [inv_one, one_smul] at hi
  have hp := AddCircle.integral_preimage (1 : ℝ) (0 : ℝ)
    (fun x => ‖circleSum (Finset.range (Nat.floor N + 1))
      (fun n => if c * N ≤ (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0) x‖ ^ 2)
  norm_num only [zero_add] at hp
  simp_rw [circleSum_coe] at hp
  rw [integral_Icc_eq_integral_Ioc, hp]
  exact hi

/-- The sum of Lambda squared is bounded by log N times psi N, page 174. -/
theorem square_mass_le (N c : ℝ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range (Nat.floor N + 1),
      (if c * N ≤ (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0) ^ 2) ≤
    log N * ∑ n ∈ Finset.range (Nat.floor N + 1), ArithmeticFunction.vonMangoldt n := by
  have hN0 : 0 ≤ N := by linarith
  have hl : 0 ≤ log N := log_nonneg hN
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  by_cases hnzero : n = 0
  · subst n
    simp
  have hnp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hnzero
  have hnf : n ≤ Nat.floor N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hnN : (n : ℝ) ≤ N := (by exact_mod_cast hnf : (n : ℝ) ≤ Nat.floor N).trans (Nat.floor_le hN0)
  have hv : ArithmeticFunction.vonMangoldt n ≤ log N :=
    ArithmeticFunction.vonMangoldt_le_log.trans (log_le_log hnp hnN)
  split_ifs
  · nlinarith [mul_le_mul_of_nonneg_right hv hn0]
  · simpa using mul_nonneg hl hn0

/-- The mean value input of Constants.final_chain with named objects, page 174. -/
theorem second_moment_le (N c : ℝ) (hN : 1 ≤ N) :
    (∫ α in Set.Icc (0 : ℝ) 1, ‖S N c α‖ ^ 2) ≤
      log N * ∑ n ∈ Finset.range (Nat.floor N + 1), ArithmeticFunction.vonMangoldt n := by
  rw [second_moment]
  exact square_mass_le N c hN

end LeanLab.LiuWang2002.Parseval109

#print axioms LeanLab.LiuWang2002.Parseval109.finite_parseval
#print axioms LeanLab.LiuWang2002.Parseval109.circleSum_coe

#print axioms LeanLab.LiuWang2002.Parseval109.second_moment
#print axioms LeanLab.LiuWang2002.Parseval109.square_mass_le
#print axioms LeanLab.LiuWang2002.Parseval109.second_moment_le
