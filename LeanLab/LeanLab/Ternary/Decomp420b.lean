/-
Helfgott https://arxiv.org/abs/1312.7748v2, pages 10, 62 and 69 to 70.
Separate Fourier inversion from the actual major and minor arc estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp420e

namespace LeanLab.Ternary.Task420
open Finset MeasureTheory

/-- The periodic major arcs M with delta zero eight and r zero 150000.
Helfgott page 10, equation 3.5. The gcd with two combines the odd and even cases.
All integer numerators include the translates needed on the circle.
Both endpoints are excluded as in the printed open intervals. -/
noncomputable def helfgottMajorArcs (x : ℝ) : Set ℝ :=
  ⋃ q : ℕ, ⋃ (_h : 1 ≤ q ∧ q ≤ Nat.gcd q 2 * 150000),
    ⋃ a : ℤ, ⋃ (_h : Int.gcd a q = 1),
      Set.Ioo ((a : ℝ) / q - (Nat.gcd q 2 * 8 * 150000 : ℝ) / (2 * q * x))
        ((a : ℝ) / q + (Nat.gcd q 2 * 8 * 150000 : ℝ) / (2 * q * x))

/-- The major arcs form a measurable set.
Helfgott page 10, equation 3.5, represented by a countable union of intervals. -/
theorem measurableSet_helfgottMajorArcs (x : ℝ) : MeasurableSet (helfgottMajorArcs x) := by
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro hq
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro ha
  exact measurableSet_Ioo

/-- The major arcs contain zero at every positive scale.
Helfgott page 10, equation 3.5, with numerator zero and denominator one. -/
theorem zero_mem_helfgottMajorArcs {x : ℝ} (hx : 0 < x) :
    (0 : ℝ) ∈ helfgottMajorArcs x := by
  simp only [helfgottMajorArcs, Set.mem_iUnion]
  refine ⟨1, by norm_num, 0, by norm_num, ?_⟩
  norm_num
  exact hx

/-- A major arc lower bound loses at most the complementary Fourier norm integral.
Helfgott page 70, the first display, before inserting the numerical budgets. -/
theorem re_integral_ge_major_sub_norm {s M : Set ℝ} {F : ℝ → ℂ}
    (hM : MeasurableSet M) (hF : IntegrableOn F s) {A B : ℝ}
    (hmaj : A ≤ (∫ α in s ∩ M, F α).re)
    (hmin : (∫ α in s \ M, ‖F α‖) ≤ B) :
    A - B ≤ (∫ α in s, F α).re := by
  rw [← integral_inter_add_sdiff hM hF, Complex.add_re]
  have hn := norm_integral_le_integral_norm F
    (μ := MeasureTheory.volume.restrict (s \ M))
  have hr := (abs_le.mp (Complex.abs_re_le_norm (∫ α in s \ M, F α))).1
  linarith

/-- LEAF. Fourier inversion identifies the actual weighted count with the circle integral.
Helfgott page 69, equation 7.49, using the absolutely convergent smoothing sums
introduced in section 1.1 and the weights fixed on pages 56 and 59.
This leaf has no major arc estimate, minor arc estimate or positive lower bound. -/
theorem helfgott_fourier_identity (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    IntegrableOn (helfgottIntegrand N) (Set.Ioc (0 : ℝ) 1) ∧
      (Task379.weightedTotal N (Task379.helfgottTripleWeight N) : ℂ) =
        ∫ α in Set.Ioc (0 : ℝ) 1, helfgottIntegrand N α := by
  exact helfgott_fourier_identity_decomposed N hN

/-- LEAF. The actual major arcs have the printed positive contribution.
Helfgott page 62, equation 7.25, from the character expansion in section 3
and the estimates of the cited major arcs paper 1305.2897v4.
Only the real part is needed because the conjugate arcs give a real total. -/
theorem helfgott_major_integral_lower (N : ℕ) (ho : Odd N)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    1.058259 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ ≤
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
        helfgottIntegrand N α).re := by
  sorry

/-- The Fourier norm of `helfgottIntegrand` factors into the squared `η+` sum norm
and the `η*` sum norm because the opposite phase has unit norm.
Helfgott page 69, equation 7.49, taking absolute values on the minor arcs. -/
theorem norm_helfgottIntegrand (N : ℕ) (α : ℝ) :
    ‖helfgottIntegrand N α‖ =
      ‖LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α
          (LeanLab.Helfgott2013.xOf N)‖ ^ 2 *
        ‖LeanLab.HelfgottArcs.S
          (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
            LeanLab.HelfgottArcs.etaT2 (49 * t)) α
          (LeanLab.Helfgott2013.xOf N)‖ := by
  unfold helfgottIntegrand
  have he : LeanLab.HelfgottArcs.e (-(N : ℝ) * α) = LeanLab.Ternary.MMS.e (-(N : ℝ) * α) := rfl
  rw [norm_mul, norm_mul, norm_pow, he, LeanLab.Ternary.MMS.norm_e, mul_one]

/-- At `N ≥ 10 ^ 27`, the Fourier integrand is integrable on the minor arcs.
Helfgott page 69, equation 7.49, restricted to the minor arc complement. -/
theorem integrableOn_helfgottIntegrand_minor (N : ℕ)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    IntegrableOn (helfgottIntegrand N)
      (Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N)) :=
  (helfgott_fourier_identity N hN).1.mono_set Set.sdiff_subset

/-- At `N ≥ 10 ^ 27`, the norm of the Fourier integrand is integrable on the minor arcs.
Helfgott page 69, equation 7.48, integrability of the minor arc norm integrand. -/
theorem integrableOn_norm_helfgottIntegrand_minor (N : ℕ)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    IntegrableOn (fun α => ‖helfgottIntegrand N α‖)
      (Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N)) :=
  (integrableOn_helfgottIntegrand_minor N hN).norm

/-- The repaired scalar minor arc total bound: replacing the printed `0.77593` by the repaired
`0.77962` from `Slip.repaired_M` and combining with `Slip.repaired_minor` upgrades the Section 7.3
Cauchy-Schwarz arithmetic of `SectionSeven.minor_total` to the repaired constant `0.97757`.
Helfgott page 69, equation 7.48, and 1501.05438v2 page 274. -/
theorem repaired_minor_total {M T P : ℝ} (hM : M ≤ 0.77962)
    (hT : T ≤ 3.5776e-4) (hP : P ≤ Real.sqrt (Real.pi / 2))
    (hM0 : 0 ≤ M) (hT0 : 0 ≤ T) (_hP0 : 0 ≤ P) :
    (Real.sqrt (P * (M + T)) + Real.sqrt 1.0532e-11) ^ 2 ≤ (0.97757 : ℝ) := by
  have h1 : P * (M + T) ≤ Real.sqrt (Real.pi / 2) * (0.77962 + 3.5776e-4) :=
    mul_le_mul hP (by linarith) (by positivity) (by positivity)
  have h2 : Real.sqrt (P * (M + T)) ≤
      Real.sqrt (Real.sqrt (Real.pi / 2) * (0.77962 + 3.5776e-4)) :=
    Real.sqrt_le_sqrt h1
  have h3 : (Real.sqrt (P * (M + T)) + Real.sqrt 1.0532e-11) ^ 2 ≤
      (Real.sqrt (Real.sqrt (Real.pi / 2) * (0.77962 + 3.5776e-4)) +
        Real.sqrt 1.0532e-11) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  exact h3.trans LeanLab.Helfgott2013.repaired_minor

/-- Conditional minor arc integral bound from an explicit scalar minor arc factor `c` bounded by
the repaired Section 7.3 inputs `M`, `T`, and `P`.
Helfgott page 69, equation 7.48, CONDITIONAL ON the analytic minor arc integral estimate. -/
theorem helfgott_minor_norm_integral_upper_of_repaired_inputs (N : ℕ)
    {M T P c : ℝ} (hM : M ≤ 0.77962) (hT : T ≤ 3.5776e-4)
    (hP : P ≤ Real.sqrt (Real.pi / 2)) (hM0 : 0 ≤ M) (hT0 : 0 ≤ T) (hP0 : 0 ≤ P)
    (hc : c ≤ (Real.sqrt (P * (M + T)) + Real.sqrt 1.0532e-11) ^ 2)
    (hInt : (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
      ‖helfgottIntegrand N α‖) ≤
        c * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ) :
    (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
      ‖helfgottIntegrand N α‖) ≤
        0.97757 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ := by
  have hrep : c ≤ 0.97757 := hc.trans (repaired_minor_total hM hT hP hM0 hT0 hP0)
  have hκ : (0 : ℝ) ≤ LeanLab.Helfgott2013.κ := by
    unfold LeanLab.Helfgott2013.κ; norm_num
  have hmul : c * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ ≤
      0.97757 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hrep (sq_nonneg _)) hκ
  exact hInt.trans hmul

/-- LEAF. The corrected minor arc budget bounds the integral of the Fourier norm.
Helfgott page 69, equation 7.48, with the corrected f zero coefficient from
the book 1501.05438 page 274 and the lab theorem repaired_minor.
The derived coefficient 0.97757 is used instead of the original 0.97392.
This leaf supplies cancellation only on the complementary arcs. -/
theorem helfgott_minor_norm_integral_upper (N : ℕ)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
      ‖helfgottIntegrand N α‖) ≤
        0.97757 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ := by
  sorry

/-- The exact existing weighted total lower bound follows from the three smaller leaves.
Helfgott page 70, first display, with the repaired minor arc budget.
CONDITIONAL ON helfgott_fourier_identity, helfgott_major_integral_lower and
helfgott_minor_norm_integral_upper. -/
theorem helfgott_weighted_total_lower_decomposed (N : ℕ) (ho : Odd N)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    0.08068 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ ≤
      Task379.weightedTotal N (Task379.helfgottTripleWeight N) := by
  obtain ⟨hint, hid⟩ := helfgott_fourier_identity N hN
  have hmaj := helfgott_major_integral_lower N ho hN
  have hmin := helfgott_minor_norm_integral_upper N hN
  have hbound := re_integral_ge_major_sub_norm
    (measurableSet_helfgottMajorArcs (LeanLab.Helfgott2013.xOf N)) hint hmaj hmin
  rw [← hid, Complex.ofReal_re] at hbound
  unfold LeanLab.Helfgott2013.κ at hbound ⊢
  nlinarith [sq_nonneg (LeanLab.Helfgott2013.xOf N)]

/-- The exact sealed Helfgott threshold from the four refined analytic leaves.
Helfgott page 70. CONDITIONAL ON the three Fourier leaves and etaPlus_abs_le. -/
theorem helfgott_analytic_decomposed : TernaryAbove (10 ^ 27) := by
  intro N ho hN
  have hN' : (1e27 : ℝ) ≤ N := by convert hN using 1 <;> norm_num
  have hgap := (LeanLab.Helfgott2013.repaired_chain hN'
    (helfgott_weighted_total_lower_decomposed N ho hN)
    (helfgott_discarded_upper_decomposed N hN)).2.2
  exact Task379.isTernarySum_of_weighted_gap hgap

end LeanLab.Ternary.Task420
