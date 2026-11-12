import LeanLab.HelfgottMajor.SPLIT_negative_sampling_raw

/-!
Split of `negative_mass_bulk_le` in `LeanLab.HelfgottMajor.SPLIT_negative_sampling_raw`
into three leaves.

The sealed statement bounds the negative middle zero mass restricted to ordinates at most
minus three halves, that is the whole negative half above the short window, by two Cauchy
Schwarz comparisons against the negative critical line energy and the negative derivative
energy, each against an unevaluated finite logarithmic weight integral.

The split separates the jobs the sealed statement does at once. The first leaf is the
sampling step: the multiplicity weighted sum of the Gaussian Mellin norms at the zeros of
the negative half is at most the two height integrals of the same weights taken over the
line, one against the mean weight and one against the derivative weight. It produces
linear weights and no square root factor. The second and third leaves are the two Cauchy
Schwarz comparisons of those two height integrals against the line energy and the
derivative energy; they involve no character, no zero and no multiplicity.

`negative_mass_bulk_le_split` assembles the sealed statement from the three leaves: the
summand is rewritten on the critical line, the two height integrals are bounded, and the
bounds are added. It has no sorry of its own. All three leaves are OPEN.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3. The sampling step of the negative half. The multiplicity weighted sum of
the Gaussian Mellin norms over the zeros with ordinate at most minus three halves and
absolute ordinate at most `T` is at most the two height integrals over the positive
ordinates from one to `T`: the critical line norm against the mean weight divided by
`2 * π`, and the derivative norm against the shifted log weight. Both integrals are left
in place and neither energy, neither square root and neither endpoint value enters. -/
theorem negative_bulk_mass_integral (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)} (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  sorry

/-- LEAF 2 of 3. Cauchy Schwarz on the height interval against the critical line energy of
the negative half. The mean weight integral of the critical line norms divided by
`2 * π` is at most the square root of the negative line energy times the square root of the
squared mean weight integral. Only the interval from one to `T` inside the positive half
line is used, so no character hypothesis and no zero hypothesis enters. -/
theorem negative_bulk_main_weight_cauchy (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) ≤
      sqrt (lineEnergy δ (-1)) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) := by
  sorry

/-- LEAF 3 of 3. Cauchy Schwarz on the height interval against the derivative energy of the
negative half. The integral of the derivative norms against the shifted log weight is at
most the square root of the negative derivative energy times the square root of the squared
shifted weight integral. As in the second leaf, no character and no zero enters, and no
critical line energy is used. -/
theorem negative_bulk_error_weight_cauchy (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) ≤
      sqrt (derivativeEnergy δ (-1)) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) := by
  sorry

/-- The sealed statement of `negative_mass_bulk_le`, assembled from the three leaves. The
critical line hypothesis rewrites every summand to the multiplicity weighted Mellin norm at
the ordinate, the sampling leaf bounds the sum by the two height integrals, and the two
Cauchy Schwarz leaves bound those integrals by the two energies. -/
theorem negative_mass_bulk_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ) ≤
      sqrt (lineEnergy δ (-1)) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      sqrt (derivativeEnergy δ (-1)) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) := by
  classical
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ =
      Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)} (fun ρ => mellinMassTerm χ δ ρ.val) ρ := by
    intro ρ
    have hz := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2
    have hρeq : ρ.val = (1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I := by
      refine Complex.ext ?_ ?_
      · simpa using hz
      · simp
    by_cases hp : ρ.val.im ≤ -(3 / 2)
    · rw [Set.indicator_of_mem (show ρ ∈ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} |
          ρ.val.im ≤ -(3 / 2)} from hp),
        Set.indicator_of_mem (show ρ ∈ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} |
          ρ.val.im ≤ -(3 / 2)} from hp)]
      rw [mellinMassTerm]
      have him : ∀ r : ℝ, ((1 / 2 : ℂ) + (r : ℂ) * Complex.I).im = r := by
        intro r
        simp
      rw [hρeq, him]
    · rw [Set.indicator_of_notMem (show ρ ∉ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} |
          ρ.val.im ≤ -(3 / 2)} from hp),
        Set.indicator_of_notMem (show ρ ∉ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} |
          ρ.val.im ≤ -(3 / 2)} from hp)]
  rw [tsum_congr hpt]
  exact (negative_bulk_mass_integral q χ hχ δ T hT hlarge hzeros).trans
    (add_le_add (negative_bulk_main_weight_cauchy q δ T hT)
      (negative_bulk_error_weight_cauchy q δ T hT))

end LeanLab.HelfgottMajor.Decomp431a

#print axioms LeanLab.HelfgottMajor.Decomp431a.negative_mass_bulk_le_split
#print axioms LeanLab.HelfgottMajor.Decomp431a.negative_bulk_mass_integral
#print axioms LeanLab.HelfgottMajor.Decomp431a.negative_bulk_main_weight_cauchy
#print axioms LeanLab.HelfgottMajor.Decomp431a.negative_bulk_error_weight_cauchy
