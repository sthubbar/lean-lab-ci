import LeanLab.RamareSaouter2003.Decomp359d
import LeanLab.RamareSaouter2003.Decomp1531a

/-!
P0099 pp. 15 and 16, Lemma 4, and p. 19, display 13.
The proper leaves are convergence at one scale and subtraction for one zero.
The assembly retains the exact zero_series_difference statement.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp378a
open Real Smooth L3Zeta Decomp290c
open LeanLab.PNTPort.ExplicitPsi1

/-- LEAF. P0099 p. 16, integration by parts in the proof of Lemma 4.
The reciprocal rho times rho plus one weight is summable with actual multiplicities.
This bridges the already proved PNTPort zero convergence theorem. -/
theorem reciprocal_product_summable :
    Summable (fun i : ZI => 1 / ‖(i.1 : ℂ) * ((i.1 : ℂ) + 1)‖) := by
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hw, div_eq_mul_inv, one_mul] using summable_hw

/-- LEAF. P0099 p. 16, the integration by parts bound used for Lemma 4.
Only the norm of one integrated term at a single scale is bounded.
The derivative weight is the first derivative of the actual smoothing polynomial. -/
theorem single_scale_norm_bound (m : ℕ) (A δ : ℝ) (hm : 2 ≤ m)
    (hA : 2 ≤ A) (hδ : 0 < δ) (i : ZI) :
    ‖∫ t in (0 : ℝ)..1,
      (((A * (1 + δ * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
        (i.1 : ℂ) * (fm m t : ℂ)‖ ≤
      (A * ((1 + δ) ^ 2 / δ *
        ∫ t in (0 : ℝ)..1, |iteratedDeriv 1 (fm m) t|)) *
          (1 / ‖(i.1 : ℂ) * ((i.1 : ℂ) + 1)‖) := by
  let ρ : ℂ := (i.1 : ℂ)
  have h0 : 0 ≤ ρ.re := (bZ_mem i).1
  have h1 : ρ.re ≤ 1 := (bZ_mem i).2
  have hs : ρ ≠ -1 := by
    intro hh
    rw [hh] at h0
    norm_num at h0
  have hd (t : ℝ) : HasDerivAt (fm m) (iteratedDeriv 1 (fm m) t) t := by
    rw [iteratedDeriv_one]
    exact ((Decomp1531a.contDiff_fm m).differentiable (by simp) t).hasDerivAt
  have hdc : Continuous (iteratedDeriv 1 (fm m)) :=
    (Decomp1531a.contDiff_fm m).continuous_iteratedDeriv 1 (by simp)
  have hb := Decomp1531a.iteratedDeriv_fm_boundary (m := m) (k := 0) (by omega)
  simp only [iteratedDeriv_zero] at hb
  have hibp := Decomp1531a.ibp_cpow_step hs hδ hd hdc hb.1 hb.2
  have hI : ‖∫ t in (0 : ℝ)..1,
      (((1 + δ * t : ℝ) : ℂ) ^ (ρ + 1)) *
        ((iteratedDeriv 1 (fm m) t : ℝ) : ℂ)‖ ≤
      (1 + δ) ^ 2 * ∫ t in (0 : ℝ)..1, |iteratedDeriv 1 (fm m) t| := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    · apply Filter.Eventually.of_forall
      intro t ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      simpa using (Decomp1531a.norm_cpow_shift_le h0 h1 hδ.le ⟨ht.1.le, ht.2⟩ 1)
    · exact (continuous_const.mul hdc.abs).intervalIntegrable 0 1
  have hfactor : (∫ t in (0 : ℝ)..1,
      (((A * (1 + δ * t) : ℝ) : ℂ) ^ ρ) / ρ * (fm m t : ℂ)) =
      ((A : ℂ) ^ ρ / ρ) *
        ∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ ρ) * (fm m t : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hb : 0 ≤ 1 + δ * t := by nlinarith [ht.1]
    dsimp only
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by linarith : 0 ≤ A) hb]
    ring
  have hApow : ‖(A : ℂ) ^ ρ‖ ≤ A := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < A)]
    calc _ ≤ A ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) h1
         _ = A := Real.rpow_one A
  change ‖∫ t in (0 : ℝ)..1,
    (((A * (1 + δ * t) : ℝ) : ℂ) ^ ρ) / ρ * (fm m t : ℂ)‖ ≤ _
  rw [hfactor, hibp, norm_mul, norm_mul, norm_div, norm_neg, norm_div, norm_one,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  calc
    _ ≤ (A / ‖ρ‖) * (1 / (‖ρ + 1‖ * δ) *
        ((1 + δ) ^ 2 * ∫ t in (0 : ℝ)..1, |iteratedDeriv 1 (fm m) t|)) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right hApow (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_left hI (by positivity)
      · positivity
      · positivity
    _ = _ := by
      simp only [norm_mul, div_eq_mul_inv, mul_inv_rev]
      ring

/-- LEAF. P0099 p. 16, absolute convergence before the limit in Lemma 4.
This is one integrated zero series at one affine scale, not its subtraction. -/
theorem single_scale_summable (m : ℕ) (A δ : ℝ) (hm : 2 ≤ m)
    (hA : 2 ≤ A) (hδ : 0 < δ) :
    Summable (fun i : ZI => ∫ t in (0 : ℝ)..1,
      (((A * (1 + δ * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
        (i.1 : ℂ) * (fm m t : ℂ)) := by
  exact Summable.of_norm_bounded
    (reciprocal_product_summable.mul_left _) (single_scale_norm_bound m A δ hm hA hδ)

/-- LEAF. P0099 p. 19, display 13, for a single actual zero.
The pointwise integral subtraction and the already proved factorization suffice. -/
theorem single_zero_difference (m : ℕ) (X u : ℝ) (hX : 0 < X) (hu : 0 < u)
    (i : ZI) :
    (∫ t in (0 : ℝ)..1,
      (((X * Real.exp u * (1 + m * u * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
        (i.1 : ℂ) * (fm m t : ℂ)) -
    (∫ t in (0 : ℝ)..1,
      (((X * (1 + m * u * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
        (i.1 : ℂ) * (fm m t : ℂ)) = zeroTerm m X u i := by
  have hδ : 0 ≤ (m : ℝ) * u := by positivity
  have hint (A : ℝ) (hA : 0 < A) : IntervalIntegrable (fun t : ℝ =>
      (((A * (1 + m * u * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
        (i.1 : ℂ) * (fm m t : ℂ)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    apply ContinuousOn.mul
    · apply ContinuousOn.div_const
      intro t ht
      apply ContinuousAt.continuousWithinAt
      apply (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ?_)).comp_of_eq
        (by fun_prop : ContinuousAt (fun t : ℝ => A * (1 + m * u * t)) t) rfl
      have : 0 ≤ (m : ℝ) * u * t := mul_nonneg hδ ht.1
      positivity
    · exact (Complex.continuous_ofReal.comp (continuous_fm m)).continuousOn
  rw [← intervalIntegral.integral_sub (hint (X * Real.exp u) (by positivity)) (hint X hX)]
  unfold zeroTerm
  rw [← Decomp1531a.zero_term_factor (i.1 : ℂ) hX hδ u (fm m)]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [show X * Real.exp u * (1 + m * u * t) =
    Real.exp u * (1 + m * u * t) * X by ring,
    show X * (1 + m * u * t) = (1 + m * u * t) * X by ring]
  ring

/-- P0099 p. 19, display 13. The exact existing zero_series_difference target.
Both single-scale series converge unconditionally by the proved norm bound. -/
theorem zero_series_difference (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    (∑' i : ZI, ∫ t in (0 : ℝ)..1,
      (((X * Real.exp u * (1 + m * u * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
        (i.1 : ℂ) * (fm m t : ℂ)).re -
    (∑' i : ZI, ∫ t in (0 : ℝ)..1,
      (((X * (1 + m * u * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
        (i.1 : ℂ) * (fm m t : ℂ)).re =
      (∑' i : ZI, zeroTerm m X u i).re := by
  have hδ : 0 < (m : ℝ) * u := mul_pos (by exact_mod_cast (by omega : 0 < m)) hu
  have hX2 : 2 ≤ X := by linarith
  have hXE : 2 ≤ X * Real.exp u := by
    have he := Real.one_le_exp hu.le
    nlinarith
  have ht := single_scale_summable m (X * Real.exp u) (m * u) hm hXE hδ
  have hb := single_scale_summable m X (m * u) hm hX2 hδ
  rw [← Complex.sub_re, ← ht.tsum_sub hb]
  congr 1
  apply tsum_congr
  exact single_zero_difference m X u (by linarith) hu

end LeanLab.RamareSaouter2003.Decomp378a

#print axioms LeanLab.RamareSaouter2003.Decomp378a.reciprocal_product_summable
#print axioms LeanLab.RamareSaouter2003.Decomp378a.single_scale_norm_bound
#print axioms LeanLab.RamareSaouter2003.Decomp378a.single_scale_summable
#print axioms LeanLab.RamareSaouter2003.Decomp378a.single_zero_difference
#print axioms LeanLab.RamareSaouter2003.Decomp378a.zero_series_difference
