import LeanLab.RieselVaughan1983.Lemma2MassBounds
import LeanLab.RieselVaughan1983.Lemma2Statements
import LeanLab.RieselVaughan1983.Lemma2Error

/-!
Absolute convergence of H at minus one third and equation 3.7 on page 50.
AI wrote the Lean code. Binary Goldbach is OPEN.
The coarse upper bound here does not certify equation 2.8 on page 46.
-/

namespace LeanLab.RieselVaughan1983.Lemma2

open Finset Real Filter Topology

noncomputable section

def massMajorant (n : ℕ) : ℝ :=
  29 * (n : ℝ) ^ (-(4 / 3 : ℝ)) + if n = 2 then localMass 2 else 0

def massBudget : ℝ := ∑' n : ℕ, massMajorant n

lemma massMajorant_nonneg (n : ℕ) : 0 ≤ massMajorant n := by
  unfold massMajorant
  apply add_nonneg
  · positivity
  · split_ifs
    · exact localMass_nonneg 2
    · exact le_rfl

lemma massMajorant_summable : Summable massMajorant := by
  have hs : Summable (fun n : ℕ => 29 * (n : ℝ) ^ (-(4 / 3 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(4 / 3 : ℝ) < -1)).mul_left 29
  exact hs.add (hasSum_ite_eq (2 : ℕ) (localMass 2)).summable

lemma localMass_le_majorant (p : ℕ) (hp : p.Prime) : localMass p ≤ massMajorant p := by
  by_cases h2 : p = 2
  · subst p
    change localMass 2 ≤ 29 * (2 : ℝ) ^ (-(4 / 3 : ℝ)) + localMass 2
    have h := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(4 / 3 : ℝ))
    linarith
  · simpa [massMajorant, h2] using localMass_le p hp
      (lt_of_le_of_ne hp.two_le (Ne.symm h2))

lemma mass_prime_pow_hasSum (p : ℕ) (hp : p.Prime) :
    HasSum (fun e : ℕ => mass (p ^ e)) (1 + localMass p) := by
  have hz : ∀ e ∉ ({0, 1, 2, 3} : Finset ℕ), mass (p ^ e) = 0 := by
    intro e he
    have he4 : 4 ≤ e := by
      simp only [mem_insert, mem_singleton, not_or] at he
      omega
    simp [mass, g_prime_pow_ge_four p e hp he4]
  convert hasSum_sum_of_ne_finset_zero hz using 1
  · simp [localMass, mass_one, add_assoc]
  · infer_instance

lemma mass_prime_pow_summable_norm (p : ℕ) (hp : p.Prime) :
    Summable (fun e : ℕ => ‖mass (p ^ e)‖) := by
  simpa [Real.norm_eq_abs] using (mass_prime_pow_hasSum p hp).summable.abs

lemma smooth_mass_hasSum (N : ℕ) :
    HasSum (fun m : N.smoothNumbers => mass m)
      (∏ p ∈ N.primesBelow, (1 + localMass p)) := by
  have H := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := mass) mass_one (fun h => mass_mul h)
    (fun hp => mass_prime_pow_summable_norm _ hp) N).2
  convert H using 1
  apply prod_congr rfl
  intro p hp
  exact ((mass_prime_pow_hasSum p (Nat.prime_of_mem_primesBelow hp)).tsum_eq).symm

lemma mass_product_le (N : ℕ) :
    ∏ p ∈ N.primesBelow, (1 + localMass p) ≤ Real.exp massBudget := by
  have hs : ∑ p ∈ N.primesBelow, localMass p ≤ massBudget := by
    calc _ ≤ ∑ p ∈ N.primesBelow, massMajorant p :=
          sum_le_sum (fun p hp => localMass_le_majorant p (Nat.prime_of_mem_primesBelow hp))
      _ ≤ massBudget := sum_le_hasSum _ (fun n _ => massMajorant_nonneg n)
          massMajorant_summable.hasSum
  calc ∏ p ∈ N.primesBelow, (1 + localMass p) ≤
        ∏ p ∈ N.primesBelow, Real.exp (localMass p) := by
          apply prod_le_prod₀
          · intro p _; linarith [localMass_nonneg p]
          · intro p _; linarith [Real.add_one_le_exp (localMass p)]
    _ = Real.exp (∑ p ∈ N.primesBelow, localMass p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp massBudget := Real.exp_le_exp.mpr hs

lemma sum_range_mass_le (N : ℕ) : ∑ n ∈ range N, mass n ≤ Real.exp massBudget := by
  have H := (hasSum_subtype_iff_indicator (f := mass) (s := (N.smoothNumbers : Set ℕ))).mp
    (smooth_mass_hasSum N)
  have hi : ∑ n ∈ range N, mass n =
      ∑ n ∈ range N, (N.smoothNumbers : Set ℕ).indicator mass n := by
    apply sum_congr rfl
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [Set.indicator_apply]; split_ifs <;> simp [mass_zero]
    · rw [Set.indicator_of_mem]
      exact Nat.mem_smoothNumbers_of_lt hn0 (mem_range.mp hn)
  rw [hi]
  calc _ ≤ ∏ p ∈ N.primesBelow, (1 + localMass p) := by
        apply sum_le_hasSum _ _ H
        intro n _
        by_cases hn : n ∈ (N.smoothNumbers : Set ℕ)
        · rw [Set.indicator_of_mem hn]; exact mass_nonneg n
        · rw [Set.indicator_of_notMem hn]
    _ ≤ Real.exp massBudget := mass_product_le N

/-- Weighted absolute convergence in the paper's H. -/
theorem mass_summable : Summable mass :=
  summable_of_sum_range_le mass_nonneg sum_range_mass_le

lemma H_le_exp_budget : H (-(1 / 3 : ℝ)) ≤ Real.exp massBudget := by
  have h : (∑' n : ℕ, mass n) ≤ Real.exp massBudget :=
    le_of_tendsto mass_summable.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall sum_range_mass_le)
  simpa only [H, neg_neg, mass] using h

lemma one_le_H : 1 ≤ H (-(1 / 3 : ℝ)) := by
  have h := le_hasSum mass_summable.hasSum 1 (fun n _ => mass_nonneg n)
  simpa [H, mass, g_multiplicative.map_one] using h

/-- Equation 3.7 for the paper's g, with no cited input. -/
theorem eq37 (y : ℝ) (hy : 0 < y) :
    |∑' m : ℕ, g m * lem1E stieltjes1 (y / m)| <
      1641 / 1000 * y ^ (-(1 / 3 : ℝ)) * H (-(1 / 3 : ℝ)) := by
  have hs : Summable (fun m : ℕ => |g m| * (m : ℝ) ^ (1 / 3 : ℝ)) :=
    mass_summable.congr (fun m => rfl)
  have h := weighted_error_bound (fun m => g m) (by simp)
    (by rw [g_multiplicative.map_one]; norm_num) hs y hy
  simpa only [H, neg_neg] using h

lemma massBudget_ge_29 : (29 : ℝ) ≤ massBudget := by
  have h := le_hasSum massMajorant_summable.hasSum 1 (fun n _ => massMajorant_nonneg n)
  simpa [massMajorant, massBudget] using h

/-- The convergence bound is too large to certify the printed H upper bound. -/
lemma coarse_upper_gt_251 : (2510128 / 10000 : ℝ) < Real.exp massBudget := by
  have he := Real.quadratic_le_exp_of_nonneg (x := (29 : ℝ)) (by norm_num)
  have hm := Real.exp_le_exp.mpr massBudget_ge_29
  norm_num at he
  linarith

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.massMajorant_nonneg
#print axioms LeanLab.RieselVaughan1983.Lemma2.massMajorant_summable
#print axioms LeanLab.RieselVaughan1983.Lemma2.localMass_le_majorant
#print axioms LeanLab.RieselVaughan1983.Lemma2.mass_prime_pow_hasSum
#print axioms LeanLab.RieselVaughan1983.Lemma2.mass_prime_pow_summable_norm
#print axioms LeanLab.RieselVaughan1983.Lemma2.smooth_mass_hasSum
#print axioms LeanLab.RieselVaughan1983.Lemma2.mass_product_le
#print axioms LeanLab.RieselVaughan1983.Lemma2.sum_range_mass_le
#print axioms LeanLab.RieselVaughan1983.Lemma2.mass_summable
#print axioms LeanLab.RieselVaughan1983.Lemma2.H_le_exp_budget
#print axioms LeanLab.RieselVaughan1983.Lemma2.one_le_H
#print axioms LeanLab.RieselVaughan1983.Lemma2.eq37
#print axioms LeanLab.RieselVaughan1983.Lemma2.massBudget_ge_29
#print axioms LeanLab.RieselVaughan1983.Lemma2.coarse_upper_gt_251
