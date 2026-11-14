import LeanLab.HelfgottMajor.Gaussian123Base

/-!
Split of the zero tail mass bound `tail_mass_of_corollary` of
`LeanLab.HelfgottMajor.Gaussian123Base`, the step bounding the multiplicity weighted Mellin
mass of the nontrivial zeros of `L(s, χ)` above height `T`.

The target has two halves: that mass family is summable, and its total is at most `4.226`
times the sum of the two tail integrals `TailIntegral123.expTailIntegral` and
`TailIntegral123.gaussianTailIntegral`. The split isolates

* the pointwise size of one zero's mass against the two branch decay envelopes, which follows
  from the saddle point hypothesis `hcor` of the target and the branch decomposition of the
  envelope,
* the summability of the exponentially decaying branch weighted by the analytic multiplicity,
* the summability of the Gaussian branch weighted by the analytic multiplicity,
* the budget of the whole mass series against the two density weighted tail integrals.

The first is proved here from `zero_mass_le_envelope` and `corEnvelope_le` of the imported
file. The other three stay open. The assembly `tail_mass_of_corollary_split` gets the
summability half by termwise comparison against the two branch families, and takes the budget
half from the fourth leaf.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real LeanLab.HelfgottArcs

section RouteBurst9Split

/-- LEAF: PROVED. Pointwise step. A zero of the critical strip whose imaginary part has
absolute value above `T` contributes at most `4.226` times its analytic multiplicity times the
sum of the two decay branches, the exponential branch and, when the shift is nonzero, the
Gaussian branch. Proved from the saddle point bound `hcor` through `zero_mass_le_envelope`, and
from the branch decomposition of the envelope `corEnvelope_le`. Nonzero multiplicity and the
zero shift case are both covered. -/
theorem tail_mass_pointwise_envelope (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
      mellinMassTerm χ δ ρ.val ≤
        4.226 * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) := by
  intro ρ
  have h1 := zero_mass_le_envelope χ δ T hT hcor ρ
  have h2 := corEnvelope_le δ ρ.val.im
  have hm : (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) :=
    Nat.cast_nonneg _
  calc mellinMassTerm χ δ ρ.val
      ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (4.226 * corEnvelope δ ρ.val.im) := h1
    _ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (4.226 * (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hm
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = 4.226 * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) := by
        rw [← mul_assoc, mul_comm _ 4.226, mul_assoc]

/-- LEAF: OPEN. Exponential branch summability. The multiplicity weighted exponential decay of
the zero heights above `T` is summable: the strip zeros up to a height grow like the height
times the logarithm of the height times the modulus, so the exponential decay wins. This is the
convergence half of the branch that carries the count against the exponential tail integral. -/
theorem exp_branch_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        exp (-0.1598 * |ρ.val.im|)) := by
  sorry

/-- LEAF: OPEN. Gaussian branch summability. The multiplicity weighted Gaussian decay of the
zero heights above `T` is summable. At zero shift the branch is identically zero, so the
statement is immediate there; for nonzero shift the decay in the height is even faster than in
the exponential branch. -/
theorem gaussian_branch_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) := by
  sorry

/-- LEAF: OPEN. Budget step. The total multiplicity weighted Mellin mass of the zeros above
height `T` is at most `4.226` times the sum of the two density weighted tail integrals. This is
the step that sums the mass against the ordinate density `TailIntegral123.countDensity`, with
the multiplicity kept as a weight. It drops the summability half of the target. -/
theorem tail_mass_budget (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (δ T : ℝ) (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) := by
  sorry

/-- The tail mass bound, assembled from the four smaller steps. The pointwise envelope bound
majorises the mass summand by `4.226` times the multiplicity weighted sum of the two branches,
the two branch families are summable, so the mass family is summable by comparison. The budget
half is the fourth leaf. Neither the target theorem nor its companion is used. -/
theorem tail_mass_of_corollary_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
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
  classical
  have hpoint := tail_mass_pointwise_envelope q χ δ T hT hcor
  have hs1 := exp_branch_summable q χ T
  have hs2 := gaussian_branch_summable q χ δ T
  have henv : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
        4.226 * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)))) := by
    have h := (hs1.add hs2).mul_left 4.226
    simpa only [mul_add] using h
  have hmass : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) := by
    refine Summable.of_norm_bounded henv (fun ρ => ?_)
    rw [Real.norm_of_nonneg (by simp only [mellinMassTerm]; positivity)]
    exact hpoint ρ
  exact ⟨hmass, tail_mass_budget q χ hχ δ T hT hzeros⟩

end RouteBurst9Split

end LeanLab.HelfgottMajor.SplitGaussian123
