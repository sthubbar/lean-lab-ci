/-
Vaughan 1977 page 95 equation 2.10.
https://doi.org/10.1515/crll.1977.290.93
The lower constant bound reuses the existing rounded chain through 10000.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ChenExplicit.TwinCUpper

open Finset Real
open scoped Classical

namespace LeanLab.SchnirelmannBounds.Vaughan1977Constant
open LeanLab.ChenExplicit LeanLab.ChenExplicit.TwinCUpper

/-- The rounded chain step exceeds the exact step by at most one. -/
theorem rounded_step_le (a n : ℕ) (hn : 3 ≤ n) :
    (((a * ((n - 1) * (n - 1) - 1) + (n - 1) * (n - 1) - 1) /
      ((n - 1) * (n - 1)) : ℕ) : ℝ) ≤ (a : ℝ) * gT n + 1 := by
  let q := (n - 1) * (n - 1)
  have hq : 4 ≤ q := by dsimp [q]; nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hqr : (q : ℝ) = ((n : ℝ) - 1)^2 := by
    dsimp [q]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hdiv := Nat.div_mul_le_self (a * (q - 1) + q - 1) q
  have hcast : (((a * (q - 1) + q - 1) / q : ℕ) : ℝ) * (q : ℝ) ≤
      (a : ℝ) * ((q : ℝ) - 1) + (q : ℝ) - 1 := by
    have h := Nat.cast_le (α := ℝ).mpr hdiv
    push_cast [Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_sub (by omega : 1 ≤ a * (q - 1) + q)] at h
    exact h
  change (((a * (q - 1) + q - 1) / q : ℕ) : ℝ) ≤ _
  rw [gT_eq hn, ← hqr]
  apply (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < q)).mp
  have heq : ((a : ℝ) * (((q : ℝ) - 1) / (q : ℝ)) + 1) * (q : ℝ) =
      (a : ℝ) * ((q : ℝ) - 1) + (q : ℝ) := by
    field_simp
  rw [heq]
  linarith

/-- The total rounding error of the existing chain is at most its length. -/
theorem chain_rounding_error (n : ℕ) :
    (chainA n : ℝ) ≤ (10^15 : ℝ) * ∏ k ∈ (range n).filter oddP, gT k + n := by
  induction n with
  | zero => norm_num [chainA]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hn : oddP n
    · rw [ite_eq_left hn, Finset.prod_insert (by simp)]
      have hstep : step (chainA n) n =
          (chainA n * ((n - 1) * (n - 1) - 1) + (n - 1) * (n - 1) - 1) /
            ((n - 1) * (n - 1)) := by
        unfold step
        rw [ite_eq_left (by simp [(primeB_iff n).mpr hn.1, hn.2])]
      have hround := rounded_step_le (chainA n) n hn.2
      have hg0 : 0 ≤ gT n := (gT_pos hn.2).le
      have hg1 : gT n ≤ 1 := by
        unfold gT
        have : 0 ≤ 1 / ((n : ℝ) - 1)^2 := by positivity
        linarith
      have hmul := mul_le_mul_of_nonneg_right ih hg0
      have hnle := mul_le_mul_of_nonneg_left hg1 (Nat.cast_nonneg (α := ℝ) n)
      rw [chainA, hstep]
      push_cast
      nlinarith
    · rw [ite_eq_right hn]
      have hstep : step (chainA n) n = chainA n := by
        unfold step
        rw [ite_eq_right]
        intro h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact hn ⟨(primeB_iff n).mp h.1, h.2⟩
      rw [chainA, hstep]
      push_cast
      linarith

/-- A lower head bound from the existing kernel certificate and its rounding error. -/
theorem constant_head_lower :
    (0.66016829649 : ℝ) ≤ ∏ k ∈ (range 10000).filter oddP, gT k := by
  have h := chain_rounding_error 10000
  rw [chain_last] at h
  norm_num at h
  linarith

/-- The reciprocal square tail used after the cutoff 10000. -/
theorem constant_tail_square :
    ∑' n : ℕ, 1 / ((n : ℝ) + 9999)^2 ≤ 1 / 9998 := by
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 9998) (n := N + 9998)
    (by norm_num) (by omega)
  have heq : (∑ n ∈ range N, 1 / ((n : ℝ) + 9999)^2) =
      ∑ i ∈ Ioc 9998 (N + 9998), ((i : ℝ)^2)⁻¹ := by
    refine Finset.sum_bij (fun n _ => n + 9999) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [mem_range] at hn
      exact mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro a ha b hb hab
      omega
    · intro i hi
      refine ⟨i - 9999, mem_range.mpr (by have := mem_Ioc.mp hi; omega), by
        have := mem_Ioc.mp hi; omega⟩
    · intro n hn
      push_cast
      simp only [one_div]
  rw [heq]
  exact h.trans (by rw [one_div]; exact sub_le_self _ (by positivity))

/-- Vaughan equation 2.10 lower half with the existing twin constant definition. -/
theorem twinC_gt_06601 : (0.6601 : ℝ) < twinC := by
  rw [twinC_eq_exp, ← summable_aT.sum_add_tsum_nat_add 10000, Real.exp_add, exp_head', filter_eq]
  have htail : -(101 / 100 : ℝ) * (1 / 9998) ≤ ∑' n, aT (n + 10000) := by
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 9999)^2) := by
      have h := (summable_nat_add_iff 10000).mpr summable_inv_sub_one_sq
      refine h.congr (fun n => ?_)
      push_cast
      ring_nf
    have hpoint (n : ℕ) : -(101 / 100 : ℝ) * (1 / ((n : ℝ) + 9999)^2) ≤ aT (n + 10000) := by
      have h := aT_tail_ge (n + 9900)
      have he1 : ((n + 9900 : ℕ) : ℝ) + 99 = (n : ℝ) + 9999 := by push_cast; ring
      have he2 : n + 9900 + 100 = n + 10000 := by omega
      rw [he1, he2] at h
      exact h
    have h := Summable.tsum_le_tsum hpoint (hs.mul_left _)
      ((summable_nat_add_iff 10000).mpr summable_aT)
    rw [tsum_mul_left] at h
    nlinarith [constant_tail_square]
  have he : 1 - (101 / 100 : ℝ) * (1 / 9998) ≤ Real.exp (∑' n, aT (n + 10000)) := by
    have h := Real.add_one_le_exp (∑' n, aT (n + 10000))
    linarith
  have hprod := mul_le_mul constant_head_lower he (by norm_num)
    (show 0 ≤ ∏ k ∈ (range 10000).filter oddP, gT k from
      (by norm_num : (0 : ℝ) ≤ 0.66016829649).trans constant_head_lower)
  exact lt_of_lt_of_le (by norm_num) hprod

example : (chainA 0 : ℝ) = 10^15 := by norm_num [chainA]
example : (0.6601 : ℝ) < 0.66016829649 * (1 - (101/100 : ℝ) / 9998) := by norm_num

end LeanLab.SchnirelmannBounds.Vaughan1977Constant

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Constant.rounded_step_le

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Constant.chain_rounding_error

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Constant.constant_head_lower

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Constant.constant_tail_square

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Constant.twinC_gt_06601
