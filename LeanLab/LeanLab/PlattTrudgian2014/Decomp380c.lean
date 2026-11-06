/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 173 to 175, Theorem 2 part b.
-/
import LeanLab.PlattTrudgian2014.Decomp281b
import LeanLab.PlattTrudgian2014.Scalars380
import LeanLab.PlattTrudgian2014.BlockPressure
import LeanLab.PlattTrudgian2014.RealMoments380

namespace LeanLab.PlattTrudgian2014

open MeasureTheory

/-- LEAF. P0026 page 175 display 4.12 and its written cosine coefficient proof.
Real exponential moments are supermultiplicative in the length.
This statement contains no dyadic quadrature or pressure bound. -/
theorem real_moment_supermultiplicative380 (t : ℝ) (ht : 0 ≤ t) (m n : ℕ) :
    (∫ x : ℝ in 0..1, Real.exp (t * (G m x).re)) *
      (∫ x : ℝ in 0..1, Real.exp (t * (G n x).re)) ≤
        ∫ x : ℝ in 0..1, Real.exp (t * (G (m + n) x).re) := by
  sorry

/-- LEAF. P0026 page 174 display 4.10 and its nonnegative coefficient proof.
Also HBP arXiv math/0201299 pages 29 to 31, displays 43 to 46, at direction one.
The finite dyadic branch average is largest at zero. There is no length L moment bound. -/
theorem dyadic_branch_max380 (t : ℝ) (M : ℕ) (ht : 0 ≤ t) (hM : 0 < M)
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    blockAverage M t 1 β ≤ dyadicMoment281 t M := by
  sorry

/-- P0026 pages 173 to 174 displays 4.5 to 4.10.
CONDITIONAL ON the finite branch maximum, with the moment iteration proved here. -/
theorem dyadic_block_upper380 (t : ℝ) (M : ℕ) (ht : 0 ≤ t) (hM : 0 < M)
    (L : ℕ) :
    (∫ x : ℝ in 0..1, Real.exp (t * (G L x).re)) ≤
      Real.exp (t * M) * Real.exp ((Real.log (dyadicMoment281 t M) / M) * L) := by
  let F := dyadicMoment281 t M
  have hF1 : 1 ≤ F := by
    have hcont := continuous_blockAverage M t 1
    have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (hcont.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
      (fun β hβ => dyadic_branch_max380 t M ht hM β hβ)
    have he := expMoment_block_eq 0 M t 1
    simp only [zero_add, momentIntegrand, G, Finset.range_zero, Finset.sum_empty, mul_zero,
      Complex.zero_re, Real.exp_zero, one_mul] at he
    have hmean : 1 ≤ expMoment M t 1 := by
      simpa only [expMoment, momentIntegrand, one_mul] using real_exp_moment_one_le380 t M
    rw [← he] at hi
    have hf : expMoment M t 1 ≤ F := by simpa [F] using hi
    exact hmean.trans hf
  have hF : 0 ≤ F := le_trans (by norm_num) hF1
  have hstep (n : ℕ) : expMoment (n + M) t 1 ≤ F * expMoment n t 1 := by
    rw [expMoment_block_eq]
    have hc : Continuous (fun β : ℝ => momentIntegrand n t 1 β * blockAverage M t 1 β) := by fun_prop
    have hd : Continuous (fun β : ℝ => F * momentIntegrand n t 1 β) := by fun_prop
    calc
      _ ≤ ∫ β : ℝ in 0..1, F * momentIntegrand n t 1 β :=
        intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable _ _)
          (hd.intervalIntegrable _ _) (fun β hβ => by
            have hh := mul_le_mul_of_nonneg_left (dyadic_branch_max380 t M ht hM β hβ)
              (Real.exp_nonneg (t * (1 * G n β).re))
            simpa only [momentIntegrand, mul_comm] using hh)
      _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl
  have hiter (r n : ℕ) : expMoment (r + n * M) t 1 ≤ F ^ n * expMoment r t 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc]
      calc
        _ ≤ F * expMoment (r + n * M) t 1 := hstep _
        _ ≤ F * (F ^ n * expMoment r t 1) := mul_le_mul_of_nonneg_left ih hF
        _ = _ := by ring
  have hm := hiter (L % M) (L / M)
  have he : L % M + L / M * M = L := by simpa only [Nat.mul_comm] using Nat.mod_add_div L M
  rw [he] at hm
  have hrem : expMoment (L % M) t 1 ≤ Real.exp (t * M) := by
    apply (expMoment_trivial _ ht (by simp : ‖(1 : ℂ)‖ ≤ 1)).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.mod_lt L hM).le) ht
  have hfp : 0 < F := lt_of_lt_of_le (by norm_num) hF1
  have hlog : 0 ≤ Real.log F := Real.log_nonneg hF1
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hpow : F ^ (L / M) ≤ Real.exp ((Real.log F / M) * L) := by
    rw [show F ^ (L / M) = Real.exp (((L / M : ℕ) : ℝ) * Real.log F) by
      rw [Real.exp_nat_mul, Real.exp_log hfp], Real.exp_le_exp]
    rw [show Real.log F / M * L = ((L : ℝ) * Real.log F) / M by ring, le_div_iff₀ hMr]
    have hq : (((L / M : ℕ) : ℝ) * M) ≤ L := by exact_mod_cast Nat.div_mul_le_self L M
    nlinarith [mul_le_mul_of_nonneg_left hq hlog]
  have hfin := hm.trans ((mul_le_mul_of_nonneg_left hrem (pow_nonneg hF _)).trans
    (mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg (t * M))))
  simpa only [expMoment, momentIntegrand, one_mul, mul_comm, F] using hfin

/-- P0026 Theorem 2 part b, exactly the existing finite dyadic pressure conclusion.
CONDITIONAL ON supermultiplicativity and the dyadic block envelope. -/
theorem dyadic_real_moment_bound_decomposed380 (t : ℝ) (M : ℕ) (ht : 0 ≤ t) (hM : 0 < M)
    (L : ℕ) :
    (∫ x : ℝ in 0..1, Real.exp (t * (G L x).re)) ≤
      Real.exp ((Real.log (dyadicMoment281 t M) / M) * L) := by
  apply supermultiplicative_remove_prefactor380
    (fun n => ∫ x : ℝ in 0..1, Real.exp (t * (G n x).re)) (Real.exp (t * M))
    (Real.log (dyadicMoment281 t M) / M)
  · simp [G]
  · intro n
    exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => Real.exp_nonneg _)
  · exact real_moment_supermultiplicative380 t ht
  · exact dyadic_block_upper380 t M ht hM

set_option format.width 240
#print axioms real_moment_supermultiplicative380
#print axioms dyadic_branch_max380
#print axioms dyadic_block_upper380
#print axioms dyadic_real_moment_bound_decomposed380

end LeanLab.PlattTrudgian2014
