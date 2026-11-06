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
