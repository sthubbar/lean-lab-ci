import LeanLab.HelfgottMajor.Gaussian123Base

/-!
Decomposition of the tail mass step `SplitGaussian123.tail_mass_of_corollary` for
FREE-nv-glm5 task3527.

The argument has three elementary pieces. First, each Mellin mass above the height cutoff
is bounded by the multiplicity times the two branch envelope. Second, the resulting mass
series is summable by the unit shell count. Third, the total mass is compared with the two
tail integrals. The first two pieces are proved here. The last comparison is the remaining
LEAF for another worker.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real LeanLab.HelfgottArcs

section DecompF3527

/-- LEAF. One tail zero has Mellin mass at most its analytic multiplicity times 4.226 and
the sum of the exponential and Gaussian envelope branches at the height of the zero. The
Gaussian branch is absent when the shift is zero. -/
theorem tail_mass_pointwise_leaf {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
      mellinMassTerm χ δ ρ.val ≤
        4.226 * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (Real.exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else
              Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
  intro ρ
  have hz := zero_mass_le_envelope χ δ T hT hcor ρ
  have he := corEnvelope_le δ ρ.val.im
  calc
    mellinMassTerm χ δ ρ.val ≤
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (4.226 * corEnvelope δ ρ.val.im) := hz
    _ = 4.226 * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          corEnvelope δ ρ.val.im := by ring
    _ ≤ 4.226 * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (Real.exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else
              Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) :=
      mul_le_mul_of_nonneg_left he (by positivity)

/-- LEAF. The multiplicity weighted Mellin mass of all zeros above the height cutoff is a
summable series. The summability follows from the polynomial unit shell count and the
pointwise envelope estimate. -/
theorem tail_mass_summable_leaf {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) := by
  exact tail_mass_summable_of_corollary q χ hχ δ T hT hcor

/-- LEAF. The total multiplicity weighted Mellin mass above the height cutoff is at most
4.226 times the exponential tail integral plus the Gaussian tail integral. The hypothesis
is the pointwise comparison with the two branch envelope, so this leaf contains only the
global zero-sum and tail-integral comparison. -/
theorem tail_mass_bound_leaf {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hpoint : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
      mellinMassTerm χ δ ρ.val ≤
        4.226 * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (Real.exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else
              Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) := by
  sorry

/-- Assembly of the split for FREE-nv-glm5 task3527. The statement of
`SplitGaussian123.tail_mass_of_corollary` is copied character for character. The proof
combines the proved summability leaf with the global comparison leaf. -/
theorem tail_mass_of_corollary_F3527 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) := by
  have hpoint := tail_mass_pointwise_leaf q χ δ T hT hcor
  refine ⟨tail_mass_summable_leaf q χ hχ δ T hT hzeros hcor, ?_⟩
  exact tail_mass_bound_leaf χ δ T hpoint

end DecompF3527

end LeanLab.HelfgottMajor.SplitGaussian123
