import LeanLab.HelfgottMajor.Decomp269b

/-!
P0014 Lemma 4.5, pages 40 to 42, used by Proposition 4.6 on page 43.
The zero count reduction and the two improper integral estimates remain OPEN.
The source display 4.34 gives the factor 4.226, used throughout this file.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123

/-- The density in the zero count integral of display 4.35 on page 41. -/
noncomputable def countDensity (q t : ℝ) : ℝ :=
  1 / (2 * π) * log (q * t / (2 * π)) + 1 / (4 * t)

/-- The exponential integral estimated in display 4.36 on page 41. -/
noncomputable def expTailIntegral (q T : ℝ) : ℝ :=
  ∫ t in Set.Ioi T, exp (-0.1598 * t) * countDensity q t

/-- The Gaussian integral of display 4.40 on page 42. Its branch is absent at zero shift. -/
noncomputable def gaussianTailIntegral (q δ T : ℝ) : ℝ :=
  if δ = 0 then 0 else
    ∫ t in Set.Ioi T, exp (-0.1065 * (t / (π * |δ|)) ^ 2) * countDensity q t

/-- LEAF. Page 41, displays 4.33 to 4.35 and Corollary 3.2.
The decay envelope gives absolute convergence as well as the Mellin mass bound.
Replacing the piecewise envelope by the sum of its two nonnegative branches enlarges it.
-/
theorem tail_mass_integral (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (expTailIntegral q T + gaussianTailIntegral q δ T) := by
  sorry

/-- LEAF. Page 41, display 4.36. This estimates only the exponential integral. -/
theorem exp_integral_bound (q : ℕ) [NeZero q] (T : ℝ) (hT : 100 ≤ T) :
    expTailIntegral q T ≤
      1.0242 * log (q * T / (2 * π)) * exp (-0.1598 * T) := by
  sorry

/-- LEAF. Page 42, displays 4.37 to 4.41. This estimates only the nonzero shift Gaussian integral. -/
theorem gaussian_integral_bound (q : ℕ) [NeZero q] (δ T : ℝ) (hδ : δ ≠ 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    gaussianTailIntegral q δ T ≤
      0.18787 * |δ| * log (q * T / (2 * π)) *
        exp (-0.1065 * (T / (π * |δ|)) ^ 2) := by
  sorry

/-- Exactly Decomp269a.high_zero_bound, from the three smaller analytic leaves.
The proof has no sorry of its own. The zero shift is handled without dividing by the shift.
-/
theorem high_zero_bound (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖highZeros χ δ x T‖ ≤
      log (q * T / (2 * π)) *
        (4.329 * exp (-0.1598 * T) +
          0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x := by
  obtain ⟨hs, hm⟩ := tail_mass_integral q χ hχ δ T hT hzeros
  apply Zeros269.high_zero_bound_of_mellin_sum χ δ x T _ hx hs
  change (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤ _
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have he := exp_integral_bound q T hT100
  have hg : gaussianTailIntegral q δ T ≤
      0.18787 * |δ| * log (q * T / (2 * π)) *
        exp (-0.1065 * (T / (π * |δ|)) ^ 2) := by
    by_cases hδ : δ = 0
    · simp [hδ, gaussianTailIntegral]
    · exact gaussian_integral_bound q δ T hδ hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hlog : 0 ≤ log ((q : ℝ) * T / (2 * π)) := by
    apply log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pi_lt_four]
  calc
    _ ≤ 4.226 * (expTailIntegral q T + gaussianTailIntegral q δ T) := hm
    _ ≤ 4.226 * (1.0242 * log (q * T / (2 * π)) * exp (-0.1598 * T) +
        0.18787 * |δ| * log (q * T / (2 * π)) *
          exp (-0.1065 * (T / (π * |δ|)) ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add he hg) (by norm_num)
    _ ≤ _ := by
      nlinarith [mul_nonneg hlog (exp_pos (-0.1598 * T)).le,
        mul_nonneg hlog (mul_nonneg (abs_nonneg δ)
          (exp_pos (-0.1065 * (T / (π * |δ|)) ^ 2)).le)]

/-- The exact original Gaussian target, assembled from the finer low and high decompositions.
The active OPEN inputs are the explicit formula, two low zero ranges and three tail estimates.
This proof does not call Decomp123.gaussian_explicit_estimate or the two intermediate sorry targets.
-/
theorem gaussian_explicit_estimate (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    MajorShape etaHeart χ δ x (gaussianError q δ x T) := by
  exact Decomp269a.gaussian_estimate_of_components x hx q χ δ T
    (Decomp269a.explicit_formula_remainder x hx q χ hχ δ T hT hzeros)
    (Decomp269b.low_zero_bound x hx q χ hχ δ T hT hzeros)
    (Decomp269c.high_zero_bound x hx q χ hχ δ T hT hzeros)

/-- Theorem 1.1 using the finer Gaussian decomposition and the existing numerical error bound.
Source pages 56 and 57. CONDITIONAL ON HelfgottInput and the six active analytic leaves.
-/
theorem theorem_1_1 : Theorem11 := by
  intro hG x hx q _ hq χ hχ δ hδ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hq' : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hδ' : |δ| ≤ 1200000 / (q : ℝ) := by norm_num at hδ ⊢; exact hδ
  have hx' : (1e8 : ℝ) ≤ x := by norm_num at hx ⊢; exact hx
  have hz := verified_zeros hG q hq χ hχ
  have hp := gaussian_explicit_estimate x (by linarith) q χ hχ δ (1e8 / q)
    (height_conditions hq1 hq' hδ').2 hz
  have hb := error_bound hq1 hq' hδ' hx'
  unfold MajorShape at hp ⊢
  exact hp.trans (mul_le_mul_of_nonneg_right hb (by linarith))


end LeanLab.HelfgottMajor.Decomp269c
