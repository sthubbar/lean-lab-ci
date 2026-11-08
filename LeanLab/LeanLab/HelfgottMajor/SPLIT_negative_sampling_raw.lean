import LeanLab.HelfgottMajor.Decomp431a

/-!
Split of `negative_sampling_raw` in `LeanLab.HelfgottMajor.Decomp431a` into three leaves.

The sealed statement bounds the negative half of the middle zero mass by the negative
critical line energy, the negative derivative energy, and the endpoint value at height one,
each against an unevaluated finite logarithmic weight integral.

The split separates the several jobs that the sealed statement does at once.
`negative_mass_eq_signed_line_sum` puts every sampled zero on the critical line, so that the
mass becomes the sum of the multiplicity weighted Gaussian Mellin norms at the ordinates of
the negative half. `negative_mass_bulk_le` estimates the zeros of height at least three
halves by Cauchy Schwarz against the two negative energies. `negative_mass_bottom_le`
charges the zeros whose height lies between one and three halves to the endpoint value,
which is what the small height count behind the constant `0.15 * log q + 3.389` covers.

All three leaves are OPEN. `negative_sampling_raw_split` assembles the sealed statement from
them and has no sorry of its own; the partition of the ordinate range and the summability
of the pieces are proved there.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3. The critical line step of the negative half. Every zero counted by
`negativeMass` lies in the strip, below height `T`, and above minus `T`, so the critical
line hypothesis rewrites its real part to `1 / 2`, and the mass becomes the sum of the
multiplicity weighted Gaussian Mellin norms at the ordinates of the negative half. This is
a rewriting identity: it estimates nothing and uses no energy. -/
theorem negative_mass_eq_signed_line_sum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    negativeMass χ δ T =
      ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ := by
  unfold negativeMass
  apply tsum_congr
  intro ρ
  by_cases h : ρ.val.im < -1
  · have hz := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2
    have hρeq : ρ.val = (1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I := by
      apply Complex.ext <;> simp [hz]
    simp [Set.indicator, h, mellinMassTerm]
    left
    congr 2
    rw [hρeq]
    norm_num
  · simp [Set.indicator, h]

/-- LEAF 2 of 3. The bulk of the negative half: the zeros of height at most minus three
halves and at least minus `T`. The two Cauchy Schwarz comparisons against the negative line
energy and the negative derivative energy are made here, with both logarithmic weight
integrals left unevaluated. No endpoint value and no positive energy enters. -/
theorem negative_mass_bulk_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
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
  sorry

/-- LEAF 3 of 3. The bottom of the negative half: the zeros of height between three halves
and one. Their count at height one is what the constant `0.15 * log q + 3.389` bounds, so
the whole block is charged to the single endpoint value at the critical point `1 / 2 - i`.
No energy integral and no positive half enters. -/
theorem negative_mass_bottom_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ) ≤
      ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) := by
  sorry

/-- The sealed statement of `negative_sampling_raw`, assembled from the three leaves.
The ordinate range of the negative half is split at minus three halves, which is the
disjoint union of the bulk and the bottom block, and each block is estimated separately.
-/
theorem negative_sampling_raw_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    negativeMass χ δ T ≤
      sqrt (lineEnergy δ (-1)) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      sqrt (derivativeEnergy δ (-1)) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) := by
  classical
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) := by
    apply (Zeros269.low_zero_terms_summable χ δ 1 T hzeros).norm.congr
    intro ρ
    simp [zeroTerm, mellinMassTerm, nsmul_eq_mul]
  have hg : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) := by
    refine hm.congr (fun ρ => ?_)
    have hz := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2
    have hρeq : ρ.val = (1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I := by
      apply Complex.ext <;> simp [hz]
    rw [mellinMassTerm, hρeq]
    simp
  have hsplit :
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
          Set.indicator {ρ | ρ.val.im < -1}
            (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
              ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ) =
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ) +
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
              Set.indicator {ρ | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                  ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ) := by
    rw [← (hg.indicator {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | ρ.val.im ≤ -(3 / 2)}).tsum_add
          (hg.indicator {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} | -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1})]
    apply tsum_congr
    intro ρ
    by_cases h1 : ρ.val.im ≤ -(3 / 2)
    · have h3 : ρ.val.im < -1 := by linarith
      have h2 : ¬(-(3 / 2) < ρ.val.im ∧ ρ.val.im < -1) := fun h => by linarith [h.1]
      simp [Set.indicator, h1, h3]
    · by_cases h2 : -(3 / 2) < ρ.val.im ∧ ρ.val.im < -1
      · have h3 : ρ.val.im < -1 := h2.2
        simp [Set.indicator, h1, h2]
      · have h3 : ¬ρ.val.im < -1 := fun h => h2 ⟨by linarith, h⟩
        simp [Set.indicator, h1, h3]
  rw [negative_mass_eq_signed_line_sum q χ δ T hzeros, hsplit]
  exact add_le_add (negative_mass_bulk_le q χ hχ δ T hT hlarge hzeros)
    (negative_mass_bottom_le q χ hχ δ T hT hlarge hzeros)

end LeanLab.HelfgottMajor.Decomp431a
