/-
Helfgott https://arxiv.org/abs/1312.7748v2 pages 50, 51 and 63.
Independent remainder moment split. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp580a
import LeanLab.Ternary.Decomp580b
import LeanLab.Ternary.Decomp580d

namespace LeanLab.Ternary.Task580
open MeasureTheory

/-- The complementary circle domain with the exact open major arcs.
Helfgott page 10 equation 3.5 at delta zero eight and r zero 150000. -/
noncomputable def minorDomain (x : ℝ) : Set ℝ :=
  Set.Ioc (0 : ℝ) 1 \ (⋃ q : ℕ, ⋃ (_h : 1 ≤ q ∧ q ≤ Nat.gcd q 2 * 150000),
    ⋃ a : ℤ, ⋃ (_h : Int.gcd a q = 1),
      Set.Ioo ((a : ℝ) / q - (Nat.gcd q 2 * 8 * 150000 : ℝ) / (2 * q * x))
        ((a : ℝ) / q + (Nat.gcd q 2 * 8 * 150000 : ℝ) / (2 * q * x)))

/-- The large prime part of eta plus, with the paper cutoff p greater than sqrt x.
Helfgott page 50 proof of Theorem 6.3, definition of S one eta plus.
The von Mangoldt coefficient equals log p on prime indices. -/
noncomputable def primeSeries (x α : ℝ) : ℂ :=
  Task420.charSeries (fun n => if n.Prime ∧ Real.sqrt x < (n : ℝ) then
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)
    else 0) α

/-- The remainder after removing the large prime part.
Helfgott page 50 proof of Theorem 6.3, definition of S two eta plus. -/
noncomputable def remainderSeries (x α : ℝ) : ℂ :=
  LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α x - primeSeries x α


/-- The coefficients removed from the large prime series.
Helfgott page 50 definition of S two eta plus. -/
noncomputable def remainderCoeff (x : ℝ) (n : ℕ) : ℂ :=
  if n.Prime ∧ Real.sqrt x < (n : ℝ) then 0 else
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)

/-- The removed coefficients remain absolutely summable.
Helfgott page 51 justification of the remainder Parseval step. -/
theorem remainderCoeff_summable {x : ℝ} (hx : 0 < x) :
    Summable fun n => ‖remainderCoeff x n‖ := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (Task420.etaPlus_coefficients_summable hx)
  intro n
  unfold remainderCoeff
  split_ifs <;> simp <;> positivity

/-- The remainder is the character series of the removed coefficients.
Helfgott page 50 definition of S two and page 51 Parseval step. -/
theorem remainderSeries_eq_charSeries {x : ℝ} (hx : 0 < x) (α : ℝ) :
    remainderSeries x α = Task420.charSeries (remainderCoeff x) α := by
  have ha : Summable fun n : ℕ =>
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ) *
          LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ := by
    simpa only [norm_mul, LeanLab.Ternary.MMS.norm_e, mul_one] using
      Task420.etaPlus_coefficients_summable hx
  have hp : Summable fun n : ℕ =>
      ‖(if n.Prime ∧ Real.sqrt x < (n : ℝ) then
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ) else 0) *
          LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ha
    intro n
    split_ifs <;> simp <;> positivity
  unfold remainderSeries primeSeries
  rw [Task420.S_eq_charSeries]
  unfold Task420.charSeries
  rw [← ha.of_norm.tsum_sub hp.of_norm]
  apply tsum_congr
  intro n
  unfold remainderCoeff
  split_ifs <;> simp

/-- LEAF. The nonprime indices have the stated coefficient square budget.
Helfgott v2 page 51 nonprime power estimate and book page 267 bounds for
C eta plus zero and one, combined on page 268 equation 14.28.
This excludes all prime indices and has no small prime contribution. -/
theorem nonprime_coeff_square_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∑' n : ℕ, if ¬n.Prime then
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)‖ ^ 2 else 0) ≤
      (2.33744 * (2 + Real.log x) + 0.44937) * Real.sqrt x := by
  sorry

/-- LEAF. The indices at most sqrt x have the small coefficient square budget.
Helfgott v2 page 51 small index estimate, with the corrected coefficient
0.60581 from book page 268 before equation 14.28.
This contains no index above sqrt x and no eta star factor. -/
theorem small_index_coeff_square_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∑' n : ℕ, if (n : ℝ) ≤ Real.sqrt x then
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)‖ ^ 2 else 0) ≤
      0.60581 * Real.sqrt x * Real.log x := by
  sorry

/-- The two arithmetic coefficient bounds give the required E budget.
Helfgott page 63 equation 7.26 and book page 268 equation 14.28.
CONDITIONAL ON nonprime_coeff_square_upper and small_index_coeff_square_upper. -/
theorem remainderCoeff_square_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∑' n : ℕ, ‖remainderCoeff x n‖ ^ 2) ≤ 8.4031e-12 * x := by
  have hx0 : 0 < x := by linarith
  let c : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
    (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)
  have hc : Summable fun n => ‖c n‖ := Task420.etaPlus_coefficients_summable hx0
  have hdiag : Function.Injective (fun n : ℕ => (n, n)) := by
    intro m n h
    exact (Prod.mk.inj h).1
  have hcsq : Summable fun n => ‖c n‖ ^ 2 := by
    simpa only [Function.comp_def, norm_mul, ← pow_two] using
      (hc.mul_norm hc).comp_injective hdiag
  have hnp : Summable fun n => if ¬n.Prime then ‖c n‖ ^ 2 else 0 := by
    apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) _ hcsq
    intro n
    split_ifs <;> simp <;> positivity
  have hsmall : Summable fun n : ℕ => if (n : ℝ) ≤ Real.sqrt x then ‖c n‖ ^ 2 else 0 := by
    apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) _ hcsq
    intro n
    split_ifs <;> simp <;> positivity
  have hrem : Summable fun n => ‖remainderCoeff x n‖ ^ 2 := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hcsq
    intro n
    unfold remainderCoeff
    split_ifs <;> simp [c] <;> positivity
  have hpoint (n : ℕ) : ‖remainderCoeff x n‖ ^ 2 ≤
      (if ¬n.Prime then ‖c n‖ ^ 2 else 0) +
        (if (n : ℝ) ≤ Real.sqrt x then ‖c n‖ ^ 2 else 0) := by
    by_cases hp : n.Prime
    · by_cases hs : (n : ℝ) ≤ Real.sqrt x
      · simp [remainderCoeff, c, hp, hs, not_lt.mpr hs]
      · simp [remainderCoeff, hp, hs, lt_of_not_ge hs]
    · by_cases hs : (n : ℝ) ≤ Real.sqrt x
      · simp [remainderCoeff, c, hp, hs]
        positivity
      · simp [remainderCoeff, c, hp, hs]
  have hsum := hrem.tsum_le_tsum hpoint (hnp.add hsmall)
  rw [hnp.tsum_add hsmall] at hsum
  have harith := add_le_add (nonprime_coeff_square_upper x hx)
    (small_index_coeff_square_upper x hx)
  calc
    _ ≤ (∑' n : ℕ, if ¬n.Prime then ‖c n‖ ^ 2 else 0) +
        (∑' n : ℕ, if (n : ℝ) ≤ Real.sqrt x then ‖c n‖ ^ 2 else 0) := hsum
    _ ≤ (2.33744 * (2 + Real.log x) + 0.44937) * Real.sqrt x +
        0.60581 * Real.sqrt x * Real.log x := harith
    _ = (2.94325 * Real.log x + 5.12425) * Real.sqrt x := by ring
    _ ≤ (2.94325 * Real.log x + 5.12426) * Real.sqrt x :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg x)
    _ ≤ 8.4029e-12 * x := book_E_bound hx
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) hx0.le

/-- Parseval converts the removed coefficient budget into the full circle L2 bound.
Helfgott page 51 last display and page 63 equation 7.26.
CONDITIONAL ON the two arithmetic coefficient leaves. -/
theorem remainder_circle_l2 (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∫ α in Set.Ioc (0 : ℝ) 1, ‖remainderSeries x α‖ ^ 2) ≤ 8.4031e-12 * x := by
  have hx0 : 0 < x := by linarith
  simp_rw [remainderSeries_eq_charSeries hx0]
  rw [charSeries_parseval _ (remainderCoeff_summable hx0)]
  exact remainderCoeff_square_upper x hx

/-- The remainder series is continuous at positive scales.
Helfgott page 51 justification of integration over the circle. -/
theorem remainderSeries_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (remainderSeries x) := by
  have h := Task420.continuous_charSeries _ (remainderCoeff_summable hx)
  have heq : remainderSeries x = Task420.charSeries (remainderCoeff x) :=
    funext (remainderSeries_eq_charSeries hx)
  rw [heq]
  exact h

/-- The star norm weight is continuous at positive scales.
Helfgott page 50 weighted triangle step. -/
theorem starNorm_continuous {x : ℝ} (hx : 0 < x) : Continuous (starNorm x) := by
  unfold starNorm starWeight
  simp_rw [Task420.S_eq_charSeries]
  exact (Task420.continuous_charSeries _ (Task420.etaStar_coefficients_summable hx)).norm

/-- The two independent smaller leaves supply the exact remainder moment budget.
Helfgott page 51 last display and page 63 equation 7.27.
CONDITIONAL ON star_mass_error and the two arithmetic coefficient leaves.
The definitions unfold to the assigned sealed remainder statement. -/
theorem remainder_moment_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∫ α in minorDomain x, starNorm x α * ‖remainderSeries x α‖ ^ 2) ≤
      1.0532e-11 * (x ^ 2 / LeanLab.Helfgott2013.κ) := by
  have hx0 : 0 < x := by linarith
  let C := (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x / LeanLab.Helfgott2013.κ
  have hC : 0 ≤ C := by dsimp [C, LeanLab.Helfgott2013.κ]; positivity
  have hi : IntegrableOn (fun α => ‖remainderSeries x α‖ ^ 2) (Set.Ioc (0 : ℝ) 1) :=
    ((remainderSeries_continuous hx0).norm.pow 2).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hsub : minorDomain x ⊆ Set.Ioc (0 : ℝ) 1 := Set.sdiff_subset
  have hmono := setIntegral_mono_set hi
    (Filter.Eventually.of_forall (fun α => sq_nonneg ‖remainderSeries x α‖))
    (Filter.Eventually.of_forall hsub)
  have hweighted : IntegrableOn (fun α => starNorm x α * ‖remainderSeries x α‖ ^ 2)
      (minorDomain x) :=
    (((starNorm_continuous hx0).mul ((remainderSeries_continuous hx0).norm.pow 2)).integrableOn_Icc).mono_set
      (hsub.trans Set.Ioc_subset_Icc_self)
  have hle := integral_mono hweighted ((hi.mono_set hsub).const_mul C)
    (fun α => mul_le_mul_of_nonneg_right (starNorm_uniform x hx α) (sq_nonneg _))
  rw [integral_const_mul] at hle
  calc
    _ ≤ C * (∫ α in minorDomain x, ‖remainderSeries x α‖ ^ 2) := hle
    _ ≤ C * (∫ α in Set.Ioc (0 : ℝ) 1, ‖remainderSeries x α‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmono hC
    _ ≤ C * (8.4031e-12 * x) :=
      mul_le_mul_of_nonneg_left (remainder_circle_l2 x hx) hC
    _ = ((Real.sqrt (Real.pi / 2) + 1.9075e-8) * 8.4031e-12) *
        (x ^ 2 / LeanLab.Helfgott2013.κ) := by dsimp [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right LeanLab.Helfgott2013.SE_coeff
      (by unfold LeanLab.Helfgott2013.κ; positivity)

/-- The copied minor domain equals the complement of the real radius arcs.
Helfgott page 10 equation 3.5 at delta eight and radius 150000. -/
theorem minorDomain_eq_majorArcs_complement (x : ℝ) :
    minorDomain x = Set.Ioc (0 : ℝ) 1 \ majorArcs x 8 150000 := by
  have hbound (q : ℕ) : q ≤ Nat.gcd q 2 * 150000 ↔
      (q : ℝ) ≤ Nat.gcd q 2 * 150000 := by norm_cast
  ext α
  simp only [minorDomain, majorArcs, Set.mem_sdiff, Set.mem_iUnion, hbound]

/-- The exact minor domain is measurable.
Helfgott page 50 weighted moments outside the open arcs. -/
theorem minorDomain_measurable (x : ℝ) : MeasurableSet (minorDomain x) := by
  rw [minorDomain_eq_majorArcs_complement]
  exact measurableSet_Ioc.diff (majorArcs_isOpen x 8 150000).measurableSet

end LeanLab.Ternary.Task580
