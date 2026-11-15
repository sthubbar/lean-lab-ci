/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character:
assembly of the principal density of the normalized lower short weight from its three terms,
the inactive clipping and partial summation against the lab factor.
No new definition, nothing left open in this file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.LowerPrincipal517b
import LeanLab.BHP1997.LowerPrincipal517c

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators
set_option maxHeartbeats 400000

/-- P0069 page 51, display 5.17: at `m = Z ^ s` the prime term has density `1 / log m`, which
is the `1 / s` term of `V(s)` over `log Z`. So the raw coefficient minus its local density is
the sum of the three term discrepancies of 5.15. -/
private theorem rawLower_sub_density (ω : ℝ → ℝ) (ε x : ℝ) (m : ℕ)
    (hZ : Real.log (scaleZ ε x) ≠ 0) :
    rawLower ε x m -
        lowerDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x) =
      (primeWeight m - 1 / Real.log (m : ℝ)) -
        (lowerTwoTerms ε x m -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x)) -
        (lowerFourTerms ε x m -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x)) := by
  have h1 : 1 / (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x) =
      1 / Real.log (m : ℝ) := by
    by_cases hm : Real.log (m : ℝ) = 0
    · simp [hm]
    · field_simp
  unfold rawLower lowerDensityAt
  rw [sub_div, sub_div, h1]
  ring

/-- P0069 page 51, display 5.17 with no character, for the normalized coefficient: the prime
term and the E2 and E4 terms of 5.15 each have their local density on every prefix of J, the
factor turns the total density into the constant `v0 / log Y`, and partial summation against
the factor, of variation at most one, costs a factor two. CONDITIONAL on the open leaves
`leaf_two_rough_density`, `leaf_four_rough_density`, `leaf_density_slope` and
`leaf_factor_increment`. -/
theorem lower_principal_density_of_leaves (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((lowerShortWeight ω ε x m : ℂ) - lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, h1⟩ := prime_density_prefix hε hε8 A hA
  obtain ⟨C2, h2⟩ := leaf_two_rough_density ω hω hz hε hε8 A hA
  obtain ⟨C3, h3⟩ := leaf_four_rough_density ω hω hz hε hε8 A hA
  obtain ⟨Cc, hc⟩ := factor_density_center ω hω hz hε hε8
  obtain ⟨Cv, hv⟩ := Decomp514a.leaf_factor_variation ω hω hz hε hε8
  refine ⟨max (max (max C1 C2) (max C3 Cc)) (max (max Cv 1) (2 * (C1 + C2 + C3))),
    fun x hx t ht => ?_⟩
  have hx1 : C1 ≤ x :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hx)
  have hx2 : C2 ≤ x :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hx)
  have hx3 : C3 ≤ x :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_left _ _).trans hx)
  have hxc : Cc ≤ x :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_left _ _).trans hx)
  have hxv : Cv ≤ x :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans ((le_max_right _ _).trans hx)
  have hxone : 1 ≤ x :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans ((le_max_right _ _).trans hx)
  have hK : 2 * (C1 + C2 + C3) ≤
      max (max (max C1 C2) (max C3 Cc)) (max (max Cv 1) (2 * (C1 + C2 + C3))) :=
    (le_max_right _ _).trans (le_max_right _ _)
  generalize max (max (max C1 C2) (max C3 Cc)) (max (max Cv 1) (2 * (C1 + C2 + C3))) = C
    at hx hK
  have hx0 : 0 < x := by linarith
  have hY1 : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hxone (by linarith)
  have hZ : Real.log (scaleZ ε x) ≠ 0 := by
    have : 0 < Real.log (scaleZ ε x) := Real.log_pos (by unfold scaleZ shortY; linarith)
    exact this.ne'
  have hscale : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (Real.log_nonneg hxone) _)
  -- the three term discrepancies of 5.15
  have hχ : ∀ m : ℕ, (1 : DirichletCharacter ℂ 1) (m : ZMod 1) = 1 := by
    intro m
    have hm : (m : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hm, map_one]
  have hp : ∀ u : ℝ, u ≤ 2 * x ^ (11 / 20 + ε) →
      ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u),
        (((primeWeight m - 1 / Real.log (m : ℝ)) -
        (lowerTwoTerms ε x m -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x)) -
        (lowerFourTerms ε x m -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x)) : ℝ) : ℂ) * (1 : DirichletCharacter ℂ 1) (m : ZMod 1)‖ ≤
        (C1 + C2 + C3) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
    intro u hu
    simp only [hχ, mul_one]
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have e1 := h1 x hx1 u hu
    have e2 := h2 x hx2 u hu
    have e3 := h3 x hx3 u hu
    have t1 := abs_sub (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u),
        (primeWeight m - 1 / Real.log (m : ℝ)) -
      ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u),
        (lowerTwoTerms ε x m -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x)))
      (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u),
        (lowerFourTerms ε x m -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x)))
    have t2 := abs_sub (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u),
        (primeWeight m - 1 / Real.log (m : ℝ)))
      (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u),
        (lowerTwoTerms ε x m -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x)))
    linarith
  have hR : 0 ≤ (C1 + C2 + C3) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
    (norm_nonneg _).trans (hp t ht)
  have hb := Decomp514a.normalized_term_bound ω ε x (1 : DirichletCharacter ℂ 1) _ hR ht hp (hv x hxv)
  have hsum : ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      ((lowerShortWeight ω ε x m : ℂ) - lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε))) =
      ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        ((lowerFactor ω ε x m * ((primeWeight m - 1 / Real.log (m : ℝ)) -
        (lowerTwoTerms ε x m -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x)) -
        (lowerFourTerms ε x m -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))) : ℝ) : ℂ) * (1 : DirichletCharacter ℂ 1) (m : ZMod 1) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hcm := hc x hxc m (Finset.mem_filter.mp hm).1
    rw [hχ, mul_one, ← rawLower_sub_density ω ε x m hZ, mul_sub, hcm]
    unfold lowerShortWeight
    push_cast
    ring
  rw [hsum]
  calc _ ≤ 2 * ((C1 + C2 + C3) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A))) := hb
    _ = (2 * (C1 + C2 + C3)) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
    _ ≤ C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_right hK hscale
    _ = _ := by ring

end LeanLab.BHP1997.LowerShortC165
