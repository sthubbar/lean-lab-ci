import LeanLab.HelfgottMajor.Decomp389a

/-!
Split of `very_low_zero_count`, the very low zero paragraph of the major arcs paper.

The count of the strip zeros of a primitive character, weighted by multiplicity, is
cut into four steps.  The truncation height does not matter once it is at least one,
so the sum is the multiplicity count of the zeros of absolute imaginary part at most
one.  That count is the classical explicit count at height one, kept with the
archimedean term and with the coefficient `1 / π` of the height term at height one.
The last step is the arithmetic that turns `1 / π` into `0.819` and the archimedean
term into `16.8`.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp389a

open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- LEAF. Summability step.  The strip zeros of the character below the height `T` are
counted with multiplicity, and this weighted count is a summable family: the zeros in a
bounded part of the strip are finitely many, so the term has finite support and the sum
is a genuine absolutely convergent sum. -/
theorem very_low_count_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) := by
  sorry

/-- LEAF. Height step.  The very low count is the indicator of `|im| ≤ 1` applied to the
multiplicity, so for `T ≥ 1` the truncation at height `T` is invisible: the sum is the
multiplicity count of those zeros of the strip that have absolute imaginary part at most
one, and the larger index set contributes nothing outside it. -/
theorem very_low_count_le_strip_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, veryLowCountTerm χ T ρ) ≤
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) := by
  classical
  have hL : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, veryLowCountTerm χ T ρ) =
      ∑' z : ℂ, {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.indicator
        (fun z => Set.indicator {z : ℂ | |z.im| ≤ 1}
          (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) z) z := by
    rw [← tsum_subtype {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
      (fun z => Set.indicator {z : ℂ | |z.im| ≤ 1}
        (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) z)]
    refine tsum_congr fun ρ => ?_
    by_cases h : |ρ.val.im| ≤ 1 <;> simp [veryLowCountTerm, Set.indicator, h]
  have hR : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) =
      ∑' z : ℂ, {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1}.indicator
        (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) z := by
    rw [← tsum_subtype {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1}
      (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ))]
    exact tsum_congr fun ρ => rfl
  have key : (∑' z : ℂ, {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.indicator
        (fun z => Set.indicator {z : ℂ | |z.im| ≤ 1}
          (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) z) z) =
      ∑' z : ℂ, {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1}.indicator
        (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) z := by
    refine tsum_congr fun z => ?_
    by_cases h1 : z ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1}
    · have h2 : z ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} :=
        ⟨h1.1, h1.2.1, h1.2.2.1, le_trans h1.2.2.2 hT⟩
      rw [Set.indicator_of_mem h2]
      rw [Set.indicator_of_mem (show z ∈ {w : ℂ | |w.im| ≤ 1} from h1.2.2.2)]
      rw [Set.indicator_of_mem h1]
    · by_cases h2 : z ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
      · rw [Set.indicator_of_mem h2, Set.indicator_of_notMem h1]
        have him : ¬ |z.im| ≤ 1 := fun h => h1 ⟨h2.1, h2.2.1, h2.2.2.1, h⟩
        simp [Set.indicator, him]
      · rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem h1]
  rw [hL, hR, key]

/-- LEAF. Counting step.  The multiplicity count of the zeros of the primitive character in
the critical strip with absolute imaginary part at most one is bounded by the explicit count
at height one: the archimedean term `log (q / (2 π e)) / π` at height one, the half of
`log q` coming from the `q` dependence of the count, and the absolute constant `17.7`. -/
theorem strip_count_at_one_le_explicit (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ≤
    (1 / π) * log (q / (2 * π * exp 1)) + 0.5 * log q + 17.7 := by
  sorry

/-- LEAF. Arithmetic step.  The explicit count at height one is at most the printed budget:
`1 / π` is at most `0.319`, and `0.9 π` is at most `log 2 + log π + 1`, so the coefficient
of `log q` drops below `0.819` and the constant `17.7 - log (2 π e) / π` drops below `16.8`.
This step holds for every nonzero modulus and carries no character. -/
theorem explicit_count_arithmetic (q : ℕ) [NeZero q] :
    (1 / π) * log (q / (2 * π * exp 1)) + 0.5 * log q + 17.7 ≤ 0.819 * log q + 16.8 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hpi0 : (0 : ℝ) < π := pi_pos
  have hpi1 : (3.1415 : ℝ) < π := pi_gt_d4
  have hpi2 : π < 3.1416 := pi_lt_d4
  have hlog2 : (0.6931471803 : ℝ) < log 2 := log_two_gt_d9
  have hlog3 : (1.0986122885 : ℝ) < log 3 := log_three_gt_d9
  have hlogpi : (1.1436 : ℝ) < log π := by
    have hsplit : log π = log 3 + log (π / 3) := by
      rw [← log_mul (by norm_num) (by positivity)]
      ring_nf
    have hthird : (0 : ℝ) < π / 3 := by linarith
    have hlow : (1 : ℝ) - (π / 3)⁻¹ ≤ log (π / 3) := one_sub_inv_le_log_of_pos hthird
    have hinv : (π / 3)⁻¹ ≤ 3 / 3.1415 := by
      rw [inv_le_comm₀ hthird (by norm_num)]
      nlinarith
    rw [hsplit]
    linarith
  have hL : log (2 * π * exp 1) = 1 + log 2 + log π := by
    rw [log_mul (by positivity) (exp_pos 1).ne', log_mul (by norm_num) hpi0.ne', log_exp]
    ring
  have hsplit' : log (q / (2 * π * exp 1)) = log q - log (2 * π * exp 1) :=
    log_div hq0.ne' (by positivity)
  have hlogq : 0 ≤ log q := log_nonneg hq1
  have hcoef : 0.5 + 1 / π ≤ 0.819 := by
    have hinv : 1 / π ≤ 1 / 3.1415 :=
      one_div_le_one_div_of_le (by norm_num) hpi1.le
    linarith
  have hB : 0.9 * π < 1 + log 2 + log π := by nlinarith
  have hconst : (0.9 : ℝ) ≤ (1 / π) * (1 + log 2 + log π) := by
    have hmul : 0.9 * π * (1 / π) ≤ (1 + log 2 + log π) * (1 / π) :=
      mul_le_mul_of_nonneg_right hB.le (by positivity)
    have hsimp : 0.9 * π * (1 / π) = (0.9 : ℝ) := by field_simp
    nlinarith
  rw [hsplit', hL]
  have hstep : (1 / π) * (log q - (1 + log 2 + log π)) + 0.5 * log q + 17.7 =
      (0.5 + 1 / π) * log q - (1 / π) * (1 + log 2 + log π) + 17.7 := by
    field_simp
    ring
  rw [hstep]
  have h1 : (0.5 + 1 / π) * log q ≤ 0.819 * log q := by nlinarith
  nlinarith

/-- The very low zero count, assembled from the four steps above. -/
theorem very_low_zero_count_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) ∧
      (∑' ρ, veryLowCountTerm χ T ρ) ≤ 0.819 * log q + 16.8 := by
  refine ⟨very_low_count_summable q χ hχ T hT, ?_⟩
  exact (very_low_count_le_strip_count q χ T hT).trans
    ((strip_count_at_one_le_explicit q χ hχ).trans (explicit_count_arithmetic q))

end LeanLab.HelfgottMajor.Decomp389a
