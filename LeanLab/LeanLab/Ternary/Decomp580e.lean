/-
Helfgott https://arxiv.org/abs/1312.7748v2 page 44 Corollary 5.7.
Passing a finite coefficient L2 estimate to an absolutely summable series.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp420e
import LeanLab.Helfgott2013.Decomp1538b

namespace LeanLab.Ternary.Task580
open MeasureTheory Filter
open LeanLab.Ternary.MMS

/-- Finite coefficient L2 bounds pass to the absolutely summable character series.
Helfgott page 44 Corollary 5.7, the passage from finite prime supported sequences
to the stated l one and l two interface.
CONDITIONAL ON the explicit finite coefficient bounds. -/
theorem charSeries_l2_of_finset_bounds (a : ℕ → ℂ)
    (ha : Summable fun n => ‖a n‖) (ha2 : Summable fun n => ‖a n‖ ^ 2)
    {S : Set ℝ} (hS : S ⊆ Set.Ioc (0 : ℝ) 1) (C : ℝ)
    (hfinite : ∀ A : Finset ℕ,
      (∫ α in S, ‖∑ n ∈ A, a n * e ((n : ℝ) * α)‖ ^ 2) ≤
        C * ∑ n ∈ A, ‖a n‖ ^ 2) :
    (∫ α in S, ‖Task420.charSeries a α‖ ^ 2) ≤ C * ∑' n, ‖a n‖ ^ 2 := by
  let B : ℝ := ∑' n, ‖a n‖
  have hbound (A : Finset ℕ) (α : ℝ) : ‖∑ n ∈ A, a n * e ((n : ℝ) * α)‖ ≤ B := by
    calc
      _ ≤ ∑ n ∈ A, ‖a n * e ((n : ℝ) * α)‖ := norm_sum_le _ _
      _ = ∑ n ∈ A, ‖a n‖ := by simp only [norm_mul, norm_e, mul_one]
      _ ≤ B := ha.sum_le_tsum A (fun n hn => norm_nonneg _)
  have hmeas (A : Finset ℕ) : AEStronglyMeasurable
      (fun α : ℝ => ‖∑ n ∈ A, a n * e ((n : ℝ) * α)‖ ^ 2) (volume.restrict S) := by
    have hc : Continuous (fun α : ℝ => ‖∑ n ∈ A, a n * e ((n : ℝ) * α)‖ ^ 2) := by
      unfold e
      fun_prop
    exact hc.aestronglyMeasurable.restrict
  have hdom : IntegrableOn (fun _ : ℝ => B ^ 2) S :=
    (continuous_const.integrableOn_Icc).mono_set (hS.trans Set.Ioc_subset_Icc_self)
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict S) (l := atTop)
    (F := fun (A : Finset ℕ) (α : ℝ) => ‖∑ n ∈ A, a n * e ((n : ℝ) * α)‖ ^ 2)
    (f := fun α => ‖Task420.charSeries a α‖ ^ 2) (fun _ => B ^ 2)
    (Eventually.of_forall hmeas)
    (Eventually.of_forall fun A => Eventually.of_forall fun α => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound A α) 2)
    hdom
    (Eventually.of_forall fun α => by
      have hs : Summable fun n => a n * e ((n : ℝ) * α) := by
        apply Summable.of_norm
        simpa only [norm_mul, norm_e, mul_one] using ha
      simpa only [Task420.charSeries, Function.comp_def, Pi.pow_def,
        SummationFilter.unconditional] using
          ((continuous_norm.pow 2).tendsto _).comp hs.hasSum)
  exact le_of_tendsto_of_tendsto' hconv (tendsto_const_nhds.mul ha2.hasSum) hfinite

/-- The natural index Parseval identity from the existing integer series theorem.
Helfgott page 51 last display and page 48 Proposition 6.2 proof.
This independent adapter avoids the import cycle through Decomp573b. -/
theorem charSeries_parseval (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) :
    (∫ α in Set.Ioc (0 : ℝ) 1, ‖Task420.charSeries a α‖ ^ 2) = ∑' n, ‖a n‖ ^ 2 := by
  let c : ℤ → ℂ := fun n => if 0 ≤ n then a n.toNat else 0
  have hcpos (n : ℕ) : c n = a n := by simp [c]
  have hcneg (n : ℕ) : c (-(n + 1)) = 0 := by
    have hnot : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
    simp only [c, hnot, ite_false]
  have hc : Summable fun n : ℤ => ‖c n‖ := by
    apply Summable.of_nat_of_neg_add_one
    · simpa only [hcpos] using ha
    · simp only [hcneg, norm_zero, summable_zero]
  have hphase (α : ℝ) :
      (∑' n : ℤ, c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))) =
        Task420.charSeries a α := by
    have hpos : Summable fun n : ℕ => c n *
        Complex.exp (2 * Real.pi * Complex.I * (α * (n : ℤ) : ℝ)) := by
      apply Summable.of_norm
      simpa [hcpos, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im] using ha
    have hneg : Summable fun n : ℕ => c (-(n + 1)) *
        Complex.exp (2 * Real.pi * Complex.I * (α * (-(n + 1) : ℤ) : ℝ)) := by
      simp only [hcneg, zero_mul, summable_zero]
    rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ =>
      c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))) hpos hneg]
    simp only [hcpos, hcneg, zero_mul, tsum_zero, add_zero]
    unfold Task420.charSeries LeanLab.Ternary.MMS.e
    apply tsum_congr
    intro n
    congr 2
    push_cast
    ring
  have h := (LeanLab.Helfgott2013.U1538.hasSum_norm_sq_exp c hc).nat_add_neg_add_one
  have hnat : HasSum (fun n : ℕ => ‖a n‖ ^ 2)
      (∫ α in (0 : ℝ)..1, ‖Task420.charSeries a α‖ ^ 2) := by
    simpa only [hcpos, hcneg, norm_zero, zero_pow (by decide : 2 ≠ 0),
      add_zero, hphase] using h
  simpa only [intervalIntegral.integral_of_le zero_le_one] using hnat.tsum_eq.symm

end LeanLab.Ternary.Task580
