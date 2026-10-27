/-
P0022, pages 371 to 373. Concrete parameters for the new bridges.
These local witnesses do not assert RH or a global cited analytic input.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.KanieckiGap.RealIntervals127
import LeanLab.KanieckiGap.IntervalTransfer127

namespace LeanLab.KanieckiGap.Instances127

open Real

/-- Page 371. The successor of seven is eleven, used only to check the branch at seven. -/
theorem nextPrime_seven : KanieckiGap.nextPrime 7 = 11 := by
  unfold KanieckiGap.nextPrime
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  intro n hn ⟨hlo, hp⟩
  interval_cases n <;> norm_num at hlo hp

/-- Page 371. The real gap definition at seven and a half sees the gap from seven to eleven. -/
theorem real_lam_seven_half_ge : 4 ≤ LeanLab.Kaniecki1995.lam 7.5 := by
  have h := LeanLab.Kaniecki1995.gap_le_lam (p := 7) (x := 7.5)
    (by norm_num) (by norm_num) (by norm_num)
  rw [Decomp127.nextPrime_eq, nextPrime_seven] at h
  exact h

/-- Page 371. The floor identity fails near the special branch at seven.
This is a representation check and asserts no error in the paper. -/
theorem not_floor_identity :
    LeanLab.Kaniecki1995.lam 7.5 ≠ KanieckiGap.lam ⌊(7.5 : ℝ)⌋₊ := by
  have h := real_lam_seven_half_ge
  norm_num [KanieckiGap.lam] at *
  omega

/-- Page 371. The middle interval range has a concrete natural argument. -/
theorem middle_range_parameters :
    (72630000000000 : ℕ) < 72630000000001 ∧
      (72630000000001 : ℝ) ≤ Real.exp 78.5 := by
  constructor
  · norm_num
  · have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he 50
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    have he' : Real.exp 50 ≤ Real.exp 78.5 := Real.exp_le_exp.mpr (by norm_num)
    linarith

/-- Pages 372 and 373. The last analytic range has a concrete natural argument. -/
theorem large_range_parameters :
    Real.exp 78.5 < (⌊Real.exp 79⌋₊ : ℝ) ∧
      (⌊Real.exp 79⌋₊ : ℝ) ≤ LeanLab.Kaniecki1995.n0 := by
  constructor
  · have he : Real.exp 79 = Real.exp 78.5 * Real.exp 0.5 := by
      rw [← Real.exp_add]
      norm_num
    have hhalf := Real.add_one_le_exp (0.5 : ℝ)
    have hlow := Real.add_one_le_exp (78.5 : ℝ)
    have hround := Nat.lt_floor_add_one (Real.exp 79)
    nlinarith
  · apply (Nat.floor_le (Real.exp_pos 79).le).trans
    apply Real.exp_le_exp.mpr
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 7
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    have h7 : Real.exp 7 ≤ Real.exp 11.503 := Real.exp_le_exp.mpr (by norm_num)
    linarith

/-- Page 371, Lemma 6. The real threshold has the required natural floor. -/
theorem lemma6_threshold_instance :
    ⌊(2300000000 : ℝ)⌋₊ = 2300000000 ∧ (23 * 10 ^ 8 : ℕ) ≤ 2300000000 := by
  norm_num

/-- Page 373. The general even residual lemma has a concrete interval input and n. -/
theorem residual_instance :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Even (22 - (p + q)) ∧
      4 ≤ 22 - (p + q) ∧ 22 - (p + q) ≤ 18 + 4 ∧
      22 = (p + q) + (22 - (p + q)) := by
  exact PaperAssembly127.even_residual PaperAssembly127.interval_instance
    (by decide : Even 22) (by norm_num) (by norm_num)

end LeanLab.KanieckiGap.Instances127

#print axioms LeanLab.KanieckiGap.Instances127.nextPrime_seven
#print axioms LeanLab.KanieckiGap.Instances127.real_lam_seven_half_ge
#print axioms LeanLab.KanieckiGap.Instances127.not_floor_identity
#print axioms LeanLab.KanieckiGap.Instances127.middle_range_parameters
#print axioms LeanLab.KanieckiGap.Instances127.large_range_parameters
#print axioms LeanLab.KanieckiGap.Instances127.lemma6_threshold_instance
#print axioms LeanLab.KanieckiGap.Instances127.residual_instance
