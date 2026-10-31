/-
AI wrote this Lean code for CODEX task105.
P0004 page 26 section 3.16 and page 28 absolute convergence argument.
Uniform absolute tails for every r at least three.
Binary Goldbach is OPEN.
-/
import LeanLab.HardyLittlewood1923.U1468SingR

set_option maxHeartbeats 600000

namespace LeanLab.HardyLittlewood1923.Tail105

open Real Finset
open scoped ArithmeticFunction.Moebius
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.U1444
open LeanLab.HardyLittlewood1923.U1468
open LeanLab.PNTPort.Vinogradov (hS hS_apply)

/-- The higher singular series term is dominated by the ternary term.
P0004 page 28, the absolute convergence argument after equation 3.232. -/
theorem term_domination {r : ℕ} (hr : 3 ≤ r) (n q : ℕ) :
    |fR r n q| ≤ |singTerm n q| := by
  have hratio : |(μ q : ℝ) / (q.totient : ℝ)| ≤ 1 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · have hphi : (1 : ℝ) ≤ q.totient := by
        exact_mod_cast Nat.totient_pos.mpr hq
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg q.totient : (0 : ℝ) ≤ q.totient)]
      apply (div_le_one (by positivity : (0 : ℝ) < q.totient)).mpr
      have hmu : |(μ q : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
      exact hmu.trans hphi
  rw [fR_apply (by omega), singTerm, abs_mul, abs_mul, abs_pow, abs_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (abs_nonneg _) hratio hr) (abs_nonneg _)

/-- All higher singular series have the same uniform absolute tail envelope.
P0004 page 26 section 3.16, sufficient bound from the lab's weighted envelope. -/
theorem absolute_tail {r : ℕ} (hr : 3 ≤ r) (n : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑' i : ℕ, |fR r n (i + (Q + 1))| ≤ Real.exp 8 / Real.sqrt Q := by
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr (by exact_mod_cast hQ)
  have hs : Summable (fun i => hS n (i + (Q + 1))) :=
    (summable_nat_add_iff (Q + 1)).mpr (summable_hS n)
  have hf : Summable (fun i => |fR r n (i + (Q + 1))|) := by
    simpa only [Real.norm_eq_abs] using
      (summable_nat_add_iff (Q + 1)).mpr (summable_norm_fR hr n)
  have hle (i : ℕ) : |fR r n (i + (Q + 1))| ≤ hS n (i + (Q + 1)) / Real.sqrt Q := by
    refine (term_domination hr n _).trans ?_
    rw [singTerm_eq_fS, le_div_iff₀ hsQ, hS_apply]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.sqrt_le_sqrt
    exact_mod_cast (by omega : Q ≤ i + (Q + 1))
  have htail : ∑' i, hS n (i + (Q + 1)) ≤ Real.exp 8 := by
    have hsplit := (summable_hS n).sum_add_tsum_nat_add (Q + 1)
    have hhead : 0 ≤ ∑ i ∈ range (Q + 1), hS n i :=
      sum_nonneg fun i _ => hS_nonneg n i
    have htotal := tsum_hS_le n
    linarith
  calc ∑' i : ℕ, |fR r n (i + (Q + 1))|
      ≤ ∑' i : ℕ, hS n (i + (Q + 1)) / Real.sqrt Q := hf.tsum_le_tsum hle (hs.div_const _)
    _ = (∑' i : ℕ, hS n (i + (Q + 1))) / Real.sqrt Q := tsum_div_const
    _ ≤ Real.exp 8 / Real.sqrt Q := div_le_div_of_nonneg_right htail hsQ.le

/-- A uniform truncation bound for S_r at every positive cutoff.
P0004 page 26 section 3.16, with the lab's sufficient square root tail. -/
theorem partial_sub_singR {r : ℕ} (hr : 3 ≤ r) (n : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    |∑ q ∈ Icc 1 Q, fR r n q - singR r n| ≤ Real.exp 8 / Real.sqrt Q := by
  have hf : Summable (fun q => fR r n q) := (summable_norm_fR hr n).of_norm
  have htail : Summable (fun i => |fR r n (i + (Q + 1))|) := by
    simpa only [Real.norm_eq_abs] using
      (summable_nat_add_iff (Q + 1)).mpr (summable_norm_fR hr n)
  rw [singR_eq_tsum (r := r) (by omega) n]
  rw [← hf.sum_add_tsum_nat_add (Q + 1), sum_range_succ_eq_Icc _ (by simp)]
  rw [show ∀ a b : ℝ, a - (a + b) = -b by intros; ring, abs_neg]
  calc |∑' i : ℕ, fR r n (i + (Q + 1))|
      ≤ ∑' i : ℕ, |fR r n (i + (Q + 1))| := by
        simpa only [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f := fun i : ℕ => fR r n (i + (Q + 1)))
            (by simpa only [Real.norm_eq_abs] using htail)
    _ ≤ Real.exp 8 / Real.sqrt Q := absolute_tail hr n hQ

#print axioms term_domination
#print axioms absolute_tail
#print axioms partial_sub_singR

end LeanLab.HardyLittlewood1923.Tail105
