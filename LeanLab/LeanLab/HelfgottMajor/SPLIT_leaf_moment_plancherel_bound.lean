import LeanLab.HelfgottMajor.SPLIT_gaussian_moment_sum_bound

/-!
Split of the open Gaussian moment bound `leaf_moment_plancherel_bound` of this folder.

The target bounds the zero sum `gaussianMomentSum χ δ T`, which carries the weight
`multiplicity * |im ρ| * ‖gaussianMellin δ ρ‖ ^ 2` over the zeros of `L χ` in the strip
`0 < re < 1` with `1 < |im ρ| ≤ T`, by `(Sec45.nTwo + Sec45.nLog) * T`.

The split has three steps.  Every zero in the index set has `|im ρ| ≤ T`, so the height
factor can be pulled out of the sum and replaced by `T`, at the price of dropping the
weight `|im ρ|`.  The threshold `1 < |im ρ|` is a nonnegative cutoff, so dropping it only
increases the mass.  The remaining mass, the sum of multiplicities times squared Mellin
norms, is the discrete Plancherel quantity that the two closed-form `L2` energies
`Sec45.nTwo` and `Sec45.nLog` of the Gaussian profile dominate.  Multiplying the resulting
bound by the nonnegative height `T` gives the target.  Each step is a separate leaf ending
in `sorry`; the assembly `leaf_moment_plancherel_bound_split` below uses only those leaves.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- LEAF. Height pull-out.  Every zero in the index set satisfies `|im ρ| ≤ T`, the
multiplicity is a nonnegative natural number and the squared Mellin norm is nonnegative, so
the weighted zero sum is at most `T` times the zero sum in which the weight `|im ρ|` is
replaced by `1`.  No information about the Mellin norms is used, only the height window and
nonnegativity; the statement is empty (both sides `0`) when the window holds no zero. -/
theorem leaf_moment_height_pullout (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    gaussianMomentSum χ δ T ≤
      T * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
  have hT0 : 0 ≤ T := by linarith
  -- Use the fact that the index set is finite to get summability
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} := by
    classical
    exact Fintype.ofFinite (ZeroCount1623.stripZeros_finite χ T).to_subtype
  -- Unfold the definition of gaussianMomentSum
  simp only [gaussianMomentSum] at *
  -- The sum over the subtype is the same as the sum over ZeroIdx
  have h₁ : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, Set.indicator {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * |ρ.val.im| * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) = ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, Set.indicator {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * |ρ.val.im| * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := rfl
  rw [h₁]
  -- Use tsum_le_tsum with pointwise inequality
  have h₂ : ∀ (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}), Set.indicator {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * |ρ.val.im| * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ ≤ T * (Set.indicator {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
    intro ρ
    by_cases h : |ρ.val.im| ≤ 1
    · -- Case: |ρ.val.im| ≤ 1, indicator is 0
      simp [Set.indicator, h]
      <;> positivity
    · -- Case: |ρ.val.im| > 1, indicator is 1
      have h₃ : 0 ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) := by positivity
      have h₄ : 0 ≤ ‖gaussianMellin δ ρ.val‖ ^ 2 := by positivity
      have h₅ : 0 ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2 := by positivity
      have h₆ : |ρ.val.im| ≤ T := ρ.property.2.2.2
      simp [Set.indicator, h] at *
      <;>
      (try norm_num at *) <;>
      (try nlinarith) <;>
      (try
        {
          have h₇ : 0 ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * |ρ.val.im| * ‖gaussianMellin δ ρ.val‖ ^ 2 := by positivity
          have h₈ : (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * |ρ.val.im| * ‖gaussianMellin δ ρ.val‖ ^ 2 = ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) * |ρ.val.im| := by ring
          rw [h₈]
          have h₉ : ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) * |ρ.val.im| ≤ ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) * T := by
            exact mul_le_mul_of_nonneg_left h₆ (by positivity)
          nlinarith
        })
  -- Sum the pointwise inequality
  have h₃ : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, Set.indicator {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * |ρ.val.im| * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, T * (Set.indicator {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
    apply tsum_le_tsum
    · -- Summability of LHS
      apply Summable.of_finite
    · -- Summability of RHS
      apply Summable.of_finite
    · -- Pointwise inequality
      intro ρ
      exact h₂ ρ
  -- Factor out T from the RHS sum
  have h₄ : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, T * (Set.indicator {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)) = T * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, Set.indicator {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
    rw [tsum_mul_left]
  rw [h₄] at h₃
  exact h₃

/-- LEAF. Cutoff removal.  The cutoff `1 < |im ρ|` contributes the factor `1` on the zeros it
keeps and `0` on the zeros with `|im ρ| ≤ 1`, whose contribution is nonnegative; so the
indicator can be dropped and the mass can only grow.  This is a termwise comparison of two
sums over the same index set, with no estimate of the Mellin norms. -/
theorem leaf_moment_mass_indicator_le_full (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2 := by
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} := by
    classical
    exact Fintype.ofFinite (ZeroCount1623.stripZeros_finite χ T).to_subtype
  -- Use tsum_le_tsum with pointwise inequality
  have h₁ : ∀ (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}), Set.indicator {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2 := by
    intro ρ
    by_cases h : |ρ.val.im| ≤ 1
    · -- Case: |ρ.val.im| ≤ 1, indicator is 0
      simp [Set.indicator, h]
      <;> positivity
    · -- Case: |ρ.val.im| > 1, indicator is 1
      simp [Set.indicator, h]
      <;> ring_nf
  -- Sum the pointwise inequality
  have h₂ : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, Set.indicator {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * ‖gaussianMellin δ ρ.val‖ ^ 2 := by
    apply tsum_le_tsum
    · -- Summability of LHS
      apply Summable.of_finite
    · -- Summability of RHS
      apply Summable.of_finite
    · -- Pointwise inequality
      intro ρ
      exact h₁ ρ
  simpa using h₂

/-- LEAF. Plancherel mass bound.  The sum over the strip zeros of the multiplicity times the
squared Mellin norm of the Gaussian profile at that zero is at most the sum of the two
squared `L2` energies of the profile, `Sec45.nTwo` and the log-weighted `Sec45.nLog`.  This
is the discrete sampling estimate that turns the two closed forms of the Gaussian energies
into a bound on the zero sum; it is uniform in the height window `|im ρ| ≤ T` and holds
trivially when the window is empty. -/
theorem leaf_moment_full_mass_plancherel (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2) ≤
    Sec45.nTwo + Sec45.nLog := by
  sorry

/-- Assembly of the split: pull the height `T` out of the zero sum, drop the unit cutoff and
use the Plancherel mass bound, then move the two energies past the height. -/
theorem leaf_moment_plancherel_bound_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    gaussianMomentSum χ δ T ≤ (Sec45.nTwo + Sec45.nLog) * T := by
  set M : ℝ :=
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ with hM
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have h1 : gaussianMomentSum χ δ T ≤ T * M := by
    simpa only [hM] using leaf_moment_height_pullout q χ δ T hT
  have h2 : M ≤ Sec45.nTwo + Sec45.nLog := by
    rw [hM]
    exact le_trans (leaf_moment_mass_indicator_le_full q χ δ T)
      (leaf_moment_full_mass_plancherel q χ δ T)
  calc gaussianMomentSum χ δ T ≤ T * M := h1
    _ ≤ T * (Sec45.nTwo + Sec45.nLog) := mul_le_mul_of_nonneg_left h2 hT0
    _ = (Sec45.nTwo + Sec45.nLog) * T := mul_comm _ _

end LeanLab.HelfgottMajor.DecompJ1153