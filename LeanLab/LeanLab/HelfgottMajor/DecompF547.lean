import LeanLab.HelfgottMajor.Gaussian123Base

/-!
Split of the tail mass step `SplitGaussian123.tail_mass_of_corollary` of Gaussian123Base.lean,
FREE-nv-mistral task547. No existing file is edited.

The target bounds the multiplicity weighted Mellin mass of the zeros of L of s and chi whose
imaginary part lies above the height T, summed over both signs, against the two tail
integrals of TailIntegral123. The proof of the target runs in three steps, and this file
carries one leaf per step.

1. Pairing step. The two sided mass is summable and is at most 4.226 times the one sided
   sum, over zeros with positive imaginary part, of the multiplicity times the two branch
   envelope sum. This step pairs each zero with its reflected partner and applies the
   pointwise envelope estimate of the twisted Gaussian Mellin transform; it leaves no
   comparison with any zero count.
2. Exponential branch counting. The one sided multiplicity weighted exponential decay of the
   zero heights is summable and is at most the exponential tail integral, whose integrand is
   the exponential decay against the density one over two pi log of q t over two pi plus one
   over four t.
3. Gaussian branch counting. The same for the Gaussian branch, absent at zero shift, against
   the Gaussian tail integral.

The assembly `tail_mass_of_corollary_F547` has the statement of the target character for
character and is proved from the three leaves with no gap of its own: the pairing bound is
chained with the split of the envelope sum into its two branches and the two counting
bounds. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real

section DecompF547

/-- LEAF. Pairing step. The multiplicity weighted Mellin mass of the strip zeros above
height T, taken over both signs of the imaginary part, is summable and totals at most 4.226
times the one sided envelope sum, where the one sided envelope sum runs over the strip zeros
with positive imaginary part above T and weights the multiplicity of each zero by the two
branch envelope sum exp of minus 0.1598 t plus, away from zero shift, exp of minus 0.1065
times the square of t over pi abs delta. This is the step that pairs each zero with its
reflected partner and applies the pointwise envelope estimate of the twisted Gaussian Mellin
transform; after it, only the comparison of a one sided weighted zero count against the two
tail integrals remains. -/
theorem paired_mass_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            (Real.exp (-0.1598 * ρ.val.im) +
              if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2))) := by
  sorry

/-- LEAF. Exponential branch counting. The one sided count of the strip zeros above height T,
weighted by the analytic multiplicity and the exponential decay of the height, is summable
and totals at most the exponential tail integral, whose integrand is the same exponential
decay against the density one over two pi times log of q t over two pi plus one over four t.
No hypothesis beyond the modulus: the exponential decay alone must absorb the zero count. -/
theorem exp_branch_count_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ≤
      TailIntegral123.expTailIntegral q T := by
  sorry

/-- LEAF. Gaussian branch counting. The one sided count of the strip zeros above height T,
weighted by the analytic multiplicity and the Gaussian decay of the height, is summable and
totals at most the Gaussian tail integral, whose integrand is the same Gaussian decay against
the density one over two pi times log of q t over two pi plus one over four t. The branch is
absent at zero shift, where the tail integral is zero and the weighted sum is the zero
series. -/
theorem gaussian_branch_count_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) ≤
      TailIntegral123.gaussianTailIntegral q δ T := by
  sorry

/-- Assembly of the split, FREE-nv-mistral task547. The statement of
`SplitGaussian123.tail_mass_of_corollary` character for character, proved from the three
leaves with no gap of its own: the pairing bound is chained with the split of the one sided
envelope sum into its two branches and the two counting bounds. -/
theorem tail_mass_of_corollary_F547 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
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
  obtain ⟨hsumP, hboundP⟩ := paired_mass_le q χ δ T hT
  obtain ⟨hsumE, hboundE⟩ := exp_branch_count_le q χ T
  obtain ⟨hsumG, hboundG⟩ := gaussian_branch_count_le q χ δ T hT
  -- the one sided envelope sum splits exactly into the two weighted branches
  have hcongr : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
      (ZeroCount1623.mult χ ρ.val : ℝ) *
        (Real.exp (-0.1598 * ρ.val.im) +
          if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) =
        (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im) +
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2) := by
    intro ρ
    ring
  have hsumEnv : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
        (ZeroCount1623.mult χ ρ.val : ℝ) *
          (Real.exp (-0.1598 * ρ.val.im) +
            if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2))) :=
    (hsumE.add hsumG).congr fun ρ => (hcongr ρ).symm
  have hsplit : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
        (ZeroCount1623.mult χ ρ.val : ℝ) *
          (Real.exp (-0.1598 * ρ.val.im) +
            if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2))) =
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
            (ZeroCount1623.mult χ ρ.val : ℝ) *
              if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) := by
    refine (tsum_congr fun ρ => hcongr ρ).trans ?_
    exact hsumE.tsum_add hsumG
  refine ⟨hsumP, hboundP.trans ?_⟩
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left (add_le_add hboundE hboundG) (by norm_num)

end DecompF547

end LeanLab.HelfgottMajor.SplitGaussian123
