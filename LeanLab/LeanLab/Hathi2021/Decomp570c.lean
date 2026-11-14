/-
Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4, pages 196 to 199.
Independent supply for the remaining arc leaf. It does not import its parent.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp570a

open Finset Real MeasureTheory Filter Topology
open LeanLab.Hathi2021.Decomp319a

namespace LeanLab.Hathi2021.Decomp570c

/-- Page 199. The first factor in the Cauchy and Schwarz estimate. -/
noncomputable def primeFactor (n₁ n₂ : ℕ) (α : ℝ × ℝ) : ℝ :=
  ‖S n₁ n₁ α.1‖ * ‖S n₁ n₂ α.2‖ * ‖G n₁ (α.1 + α.2)‖ ^ 2

/-- Page 199. The second factor in the Cauchy and Schwarz estimate. -/
noncomputable def squareFactor (n₁ n₂ : ℕ) (α : ℝ × ℝ) : ℝ :=
  ‖T n₁ n₁ α.1‖ ^ 2 * ‖T n₁ n₂ α.2‖ ^ 2 * ‖G n₁ (α.1 + α.2)‖ ^ 14

/-- Page 199, Kong and Liu reference 5 Lemma 2.3. The first mean value. -/
noncomputable def primeMoment (n₁ n₂ : ℕ) : ℝ :=
  ∫ α in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, primeFactor n₁ n₂ α ^ 2

/-- Pages 196 and 199. The prime square fourth moment with G to power 28. -/
noncomputable def squareMoment (n₁ n₂ : ℕ) : ℝ :=
  ∫ α in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, squareFactor n₁ n₂ α ^ 2

/-- Page 199. Both moment factors are continuous. -/
theorem continuous_factors (n₁ n₂ : ℕ) :
    Continuous (primeFactor n₁ n₂) ∧ Continuous (squareFactor n₁ n₂) := by
  unfold primeFactor squareFactor S T G e
  constructor <;> fun_prop

/-- Page 199. Both moment integrals are nonnegative. -/
theorem moments_nonneg (n₁ n₂ : ℕ) :
    0 ≤ primeMoment n₁ n₂ ∧ 0 ≤ squareMoment n₁ n₂ := by
  constructor <;> apply integral_nonneg <;> intro α <;> exact sq_nonneg _

/-- LEAF. Hu page 199, Kong and Liu reference 5 Lemma 2.3.
This mean value does not involve the remaining arc or prime square factor. -/
theorem kong_liu_prime_moment (C : ℝ) (hC : 1 < C) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      primeMoment n₁ n₂ ≤ (3058869 / 10000 : ℝ) *
        ((n₁ : ℝ) * n₂ * L n₁ ^ 4) := by
  sorry

/-- LEAF. Hu pages 196 to 199, the I display after the singular series sum.
The displayed leading constant 383000 is kept as an open input.
The prior bound 128 squared times 23.39 does not imply this constant.
This mean value contains no prime linear factor and no remaining arc. -/
theorem hu_square_moment (C η : ℝ) (hC : 1 < C) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      squareMoment n₁ n₂ ≤ (383000 + η) *
        ((n₁ : ℝ) * n₂ * L n₁ ^ 28) := by
  sorry

/-- Page 199. The rounded square moment constant is strictly below
128 squared times the preceding singular series constant. -/
theorem square_moment_rounding_gap :
    (383000 : ℝ) < 128 ^ 2 * (2339 / 100) := by
  norm_num

/-- Page 199. Even the rounded moment constants give a square strictly
above the square of the printed final constant. This is a method gap. -/
theorem final_constant_rounding_gap :
    (108238 / 10 : ℝ) ^ 2 < (3058869 / 10000) * 383000 := by
  norm_num


/-- Page 199. Cauchy and Schwarz bounds the integral of the two factors
by the square roots of their moments. -/
theorem factor_integral_le (n₁ n₂ : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      primeFactor n₁ n₂ α * squareFactor n₁ n₂ α) ≤
        Real.sqrt (primeMoment n₁ n₂) * Real.sqrt (squareMoment n₁ n₂) := by
  let U := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  obtain ⟨hf, hg⟩ := continuous_factors n₁ n₂
  have hfc : IntegrableOn (fun α => primeFactor n₁ n₂ α ^ 2) U :=
    (hf.pow 2).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hgc : IntegrableOn (fun α => squareFactor n₁ n₂ α ^ 2) U :=
    (hg.pow 2).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hflp := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hfc
  have hglp := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hgc
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall (fun α => show 0 ≤ primeFactor n₁ n₂ α by
      unfold primeFactor; positivity))
    (Filter.Eventually.of_forall (fun α => show 0 ≤ squareFactor n₁ n₂ α by
      unfold squareFactor; positivity))
    (by simpa using hflp) (by simpa using hglp)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, primeMoment, squareMoment, U] using h

/-- Page 199. Outside the large G region, 66 factors of G are bounded
by lambda times L. The remaining 16 factors split as 2 plus 14. -/
theorem remaining_integrand_norm_le (n₁ n₂ : ℕ) (α : ℝ × ℝ)
    (hα : α ∉ exceptional n₁) :
    ‖integrand n₁ n₂ α‖ ≤ ((PairLinnik.lam : ℝ) * L n₁) ^ 66 *
      (primeFactor n₁ n₂ α * squareFactor n₁ n₂ α) := by
  have hG : ‖G n₁ (α.1 + α.2)‖ ≤ (PairLinnik.lam : ℝ) * L n₁ :=
    le_of_lt (lt_of_not_ge hα)
  have hp := pow_le_pow_left₀ (norm_nonneg (G n₁ (α.1 + α.2))) hG 66
  calc
    ‖integrand n₁ n₂ α‖ = ‖G n₁ (α.1 + α.2)‖ ^ 66 *
        (primeFactor n₁ n₂ α * squareFactor n₁ n₂ α) := by
      simp only [integrand, norm_mul, norm_pow, norm_e, mul_one,
        primeFactor, squareFactor]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (by
      unfold primeFactor squareFactor; positivity)

/-- Page 199. The absolute real arc contribution is bounded by the full
factor integral after taking out the 66 small G factors. -/
theorem remaining_arc_factor_bound (n₁ n₂ : ℕ) :
    |R3 n₁ n₂| ≤ ((PairLinnik.lam : ℝ) * L n₁) ^ 66 *
      (∫ α in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
        primeFactor n₁ n₂ α * squareFactor n₁ n₂ α) := by
  let U := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  let A := U ∩ ((major n₁ n₂)ᶜ ∩ (exceptional n₁)ᶜ)
  let f := fun α => primeFactor n₁ n₂ α * squareFactor n₁ n₂ α
  let c : ℝ := ((PairLinnik.lam : ℝ) * L n₁) ^ 66
  have hA : MeasurableSet A :=
    (measurableSet_Icc.prod measurableSet_Icc).inter
      ((measurableSet_major n₁ n₂).compl.inter (measurableSet_exceptional n₁).compl)
  have hAU : A ⊆ U := Set.inter_subset_left
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨hpf, hsf⟩ := continuous_factors n₁ n₂
  have hfc : Continuous f := hpf.mul hsf
  have hfi : IntegrableOn f U :=
    hfc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hcfi : IntegrableOn (fun α => c * f α) A :=
    (show IntegrableOn (fun α => c * f α) U volume from hfi.const_mul c).mono_set hAU
  have hf0 : ∀ α, 0 ≤ f α := by
    intro α; dsimp [f, primeFactor, squareFactor]; positivity
  calc
    |R3 n₁ n₂| ≤ ‖∫ α in A, integrand n₁ n₂ α‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∫ α in A, ‖integrand n₁ n₂ α‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ α in A, c * f α := by
      apply setIntegral_mono_on
        ((integrableOn_integrand n₁ n₂).mono_set hAU).norm
        hcfi hA
      intro α hα
      exact remaining_integrand_norm_le n₁ n₂ α hα.2.2
    _ = c * ∫ α in A, f α := integral_const_mul _ _
    _ ≤ c * ∫ α in U, f α := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact setIntegral_mono_set hfi (Filter.Eventually.of_forall hf0)
        (Filter.Eventually.of_forall hAU)

/-- Page 199. The complete geometric and integral estimate for R3.
No arithmetic mean value estimate is used in this inequality. -/
theorem remaining_arc_moment_bound (n₁ n₂ : ℕ) :
    |R3 n₁ n₂| ≤ ((PairLinnik.lam : ℝ) * L n₁) ^ 66 *
      (Real.sqrt (primeMoment n₁ n₂) * Real.sqrt (squareMoment n₁ n₂)) := by
  exact (remaining_arc_factor_bound n₁ n₂).trans
    (mul_le_mul_of_nonneg_left (factor_integral_le n₁ n₂) (by positivity))


/-- LEAF. Hu page 199, the last Cauchy and Schwarz estimate.
This is the missing joint moment refinement required by the sealed constant.
The two printed separate constants do not prove it, as the rounding gap
above shows. It contains no remaining arc and no power 82 integrand. -/
theorem joint_moment_rounding_reserve (C η : ℝ) (hC : 1 < C) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      primeMoment n₁ n₂ * squareMoment n₁ n₂ ≤
        ((108238 / 10 + η) * ((n₁ : ℝ) * n₂ * L n₁ ^ 16)) ^ 2 := by
  sorry

/-- Page 199. A bound on the product of the two moments controls the
square root product, including the zero moment cases. -/
theorem sqrt_moments_le (n₁ n₂ : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (h : primeMoment n₁ n₂ * squareMoment n₁ n₂ ≤ B ^ 2) :
    Real.sqrt (primeMoment n₁ n₂) * Real.sqrt (squareMoment n₁ n₂) ≤ B := by
  obtain ⟨hp, hq⟩ := moments_nonneg n₁ n₂
  rw [← Real.sqrt_mul hp]
  exact (Real.sqrt_le_iff).2 ⟨hB, h⟩

/-- Page 199. CONDITIONAL ON the missing joint moment refinement.
This has the exact statement of the sealed remaining arc leaf. -/
theorem remaining_arc_upper (C δ : ℝ) (hC : 1 < C) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      |R3 n₁ n₂| ≤ ((108238 / 10) * (PairLinnik.lam : ℝ) ^ (82 - 16) + δ) *
        scale n₁ n₂ := by
  let a : ℝ := (PairLinnik.lam : ℝ) ^ 66
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let η : ℝ := δ / (a + 1)
  have hη : 0 < η := div_pos hδ (by positivity)
  obtain ⟨N, hN⟩ := joint_moment_rounding_reserve C η hC hη
  refine ⟨max 16 N, ?_⟩
  intro n₁ n₂ ho₁ ho₂ hn hlt hratio
  have h16 : 16 ≤ n₁ := ((le_max_left _ _).trans hn).trans hlt.le
  have hL : 0 ≤ L n₁ := (Decomp115.logScale_pos n₁ h16).le
  have hm := hN n₁ n₂ ho₁ ho₂ ((le_max_right _ _).trans hn) hlt hratio
  have hroot := sqrt_moments_le n₁ n₂
    ((108238 / 10 + η) * ((n₁ : ℝ) * n₂ * L n₁ ^ 16)) (by positivity) hm
  have hcoef : η * a ≤ δ := by
    have he : η * (a + 1) = δ := div_mul_cancel₀ δ (by positivity : a + 1 ≠ 0)
    nlinarith
  calc
    |R3 n₁ n₂| ≤ ((PairLinnik.lam : ℝ) * L n₁) ^ 66 *
        (Real.sqrt (primeMoment n₁ n₂) * Real.sqrt (squareMoment n₁ n₂)) :=
      remaining_arc_moment_bound n₁ n₂
    _ ≤ ((PairLinnik.lam : ℝ) * L n₁) ^ 66 *
        ((108238 / 10 + η) * ((n₁ : ℝ) * n₂ * L n₁ ^ 16)) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = ((108238 / 10) * a + η * a) * scale n₁ n₂ := by
      dsimp [a, scale]
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa [a] using add_le_add_left hcoef ((108238 / 10) * a))
      (scale_nonneg n₁ n₂)

end LeanLab.Hathi2021.Decomp570c
