import Mathlib

/-!
PREP 2026-11-21, route step `MainLemma41Split123.vertical_integral_bound`, part A.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, pages 33 and 34,
displays 4.8, 4.9 and 4.10: the functional equation of L'/L on re s = -1/2 written with the
digamma function, and the Binet bound psi(z) = log z + O*(10/27) on re z = 3/2.
Leaves carry the doc tag LEAF; `psi_sub_log_le` and `fe_line` are assembled here without
sorry of their own. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121VIPointwiseA
open Complex MeasureTheory Set

/-- LEAF: P0014 page 33, display 4.9, specialised to s = -1/2 + iτ. From the reflection
formula `Complex.digamma_one_sub` and the duplication formula `Complex.digamma_two_mul`
of Mathlib: -(1/2)(ψ((s+κ)/2) + ψ((1-s+κ)/2)) = -ψ(1-s) + log 2 + (π/2) cot(π(s+κ)/2).
Class EASY: two Mathlib identities and pole side conditions at real parts ±1/4, 3/4.
PROVED here. -/
theorem digamma_line_identity (τ : ℝ) (κ : ℕ) (hκ : κ = 0 ∨ κ = 1) :
    -(1 / 2 : ℂ) * (digamma (((-1 / 2 : ℂ) + τ * I + κ) / 2) +
        digamma ((1 - ((-1 / 2 : ℂ) + τ * I) + κ) / 2)) =
      -digamma (1 - ((-1 / 2 : ℂ) + τ * I)) + Complex.log 2 +
        ((Real.pi / 2 : ℝ) : ℂ) * cot ((Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + κ) / 2) := by
  set s : ℂ := (-1 / 2 : ℂ) + τ * I with hs
  have hsre : s.re = -1 / 2 := by simp [hs]
  have hdup : digamma (1 - s) = (1 / 2) * (digamma ((1 - s) / 2) + digamma (1 - s / 2)) +
      Complex.log 2 := by
    have h := digamma_two_mul (s := (1 - s) / 2) (by
      intro m hm
      have hr := congrArg Complex.re hm
      simp only [Complex.mul_re, Complex.div_re, Complex.sub_re, Complex.one_re, hsre] at hr
      norm_num at hr
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      linarith)
    rw [show 2 * ((1 - s) / 2) = 1 - s by ring, show (1 - s) / 2 + 1 / 2 = 1 - s / 2 by ring] at h
    exact h
  rcases hκ with rfl | rfl
  · have href := digamma_one_sub (s := s / 2) (by
      intro n hn
      have hr := congrArg Complex.re hn
      simp only [Complex.div_re, hsre, Complex.intCast_re] at hr
      norm_num at hr
      have h1 : (n : ℝ) < 0 := by linarith
      have h2 : (-1 : ℝ) < n := by linarith
      have h3 : n < 0 := by exact_mod_cast h1
      have h4 : -1 < n := by exact_mod_cast h2
      omega)
    rw [show (Real.pi : ℂ) * (s + ((0 : ℕ) : ℂ)) / 2 = Real.pi * (s / 2) by push_cast; ring]
    simp only [Nat.cast_zero, add_zero]
    rw [hdup]
    push_cast
    linear_combination (1 / 2 : ℂ) * href
  · have href := digamma_one_sub (s := (s + 1) / 2) (by
      intro n hn
      have hr := congrArg Complex.re hn
      simp only [Complex.div_re, Complex.add_re, Complex.one_re, hsre, Complex.intCast_re] at hr
      norm_num at hr
      have h1 : (n : ℝ) < 1 := by linarith
      have h2 : (0 : ℝ) < n := by linarith
      have h3 : n < 1 := by exact_mod_cast h1
      have h4 : 0 < n := by exact_mod_cast h2
      omega)
    rw [show (Real.pi : ℂ) * (s + ((1 : ℕ) : ℂ)) / 2 = Real.pi * ((s + 1) / 2) by push_cast; ring]
    rw [show 1 - (s + 1) / 2 = (1 - s) / 2 by ring] at href
    rw [show (1 - s + ((1 : ℕ) : ℂ)) / 2 = 1 - s / 2 by push_cast; ring,
      show s + ((1 : ℕ) : ℂ) = s + 1 by push_cast; ring]
    rw [hdup]
    push_cast
    linear_combination (1 / 2 : ℂ) * href

/-- LEAF: P0014 page 33, display 4.8, from IK04 Thm. 4.15, on the line s = -1/2 + iτ, with
the gamma factor of parity κ written through ψ: L'/L(s, χ) = log(π/q) - (1/2)ψ((s+κ)/2)
- (1/2)ψ((1-s+κ)/2) - L'/L(1-s, χ bar). The lab already has the logarithmic derivative of
the functional equation, `LeanLab.Linnik.ExplicitFormula.logDeriv_fe_left`, and the gamma
factor logDeriv `logDeriv_Gammaℝ`; this leaf is their combination.
Class MEDIUM: one idea, unfold `gammaFactor` by parity and combine two lab lemmas. -/
theorem fe_digamma {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (τ : ℝ) (κ : ℕ) (hκ : (χ.Even ∧ κ = 0) ∨ (χ.Odd ∧ κ = 1)) :
    deriv χ.LFunction ((-1 / 2 : ℂ) + τ * I) / χ.LFunction ((-1 / 2 : ℂ) + τ * I) =
      ((Real.log (Real.pi / q) : ℝ) : ℂ)
        - (1 / 2 : ℂ) * (digamma (((-1 / 2 : ℂ) + τ * I + κ) / 2) +
            digamma ((1 - ((-1 / 2 : ℂ) + τ * I) + κ) / 2))
        - logDeriv (χ⁻¹).LFunction (1 - ((-1 / 2 : ℂ) + τ * I)) := by
  sorry

/-- LEAF: P0014 page 34, display 4.10, first line, which the paper takes from OLBC10
(5.9.15) and GR00 (3.411.1): Binet's second formula for the digamma function,
ψ(z) = log z - 1/(2z) - 2 ∫_0^∞ t dt / ((t² + z²)(e^{2πt} - 1)) for re z above 0.
CITED-LEFT: the paper gives no proof. Class HARD: a full Binet formula port. -/
theorem binet_formula (z : ℂ) (hz : 0 < z.re) :
    digamma z = Complex.log z - 1 / (2 * z) -
      2 * ∫ t in Ioi (0 : ℝ),
        (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * Real.pi * t) : ℂ) - 1)) := by
  sorry

/-- LEAF: P0014 page 34, display 4.10, the remark before it: if re z = 3/2 then
|t² + z²| ≥ 9/4 for all real t. Class EASY: a polynomial inequality in t² and (im z)².
PROVED here. -/
theorem nine_fourths_le_norm (z : ℂ) (hz : z.re = 3 / 2) (t : ℝ) :
    9 / 4 ≤ ‖(t : ℂ) ^ 2 + z ^ 2‖ := by
  have hre : ((t : ℂ) ^ 2 + z ^ 2).re = t ^ 2 + 9 / 4 - z.im ^ 2 := by
    simp [sq, hz]; ring
  have him : ((t : ℂ) ^ 2 + z ^ 2).im = 3 * z.im := by
    simp [sq, hz]; ring
  have hn : ‖(t : ℂ) ^ 2 + z ^ 2‖ ^ 2 = (t ^ 2 + 9 / 4 - z.im ^ 2) ^ 2 + (3 * z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
  have hsq : (9 / 4 : ℝ) ^ 2 ≤ ‖(t : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
    rw [hn]; nlinarith [sq_nonneg (t ^ 2 - z.im ^ 2), sq_nonneg t, sq_nonneg z.im]
  nlinarith [norm_nonneg ((t : ℂ) ^ 2 + z ^ 2)]

/-- LEAF: P0014 page 34, display 4.10, fourth line: ∫_0^∞ t/(e^{2πt} - 1) dt =
Γ(2)ζ(2)/(2π)² = 1/24. Class MEDIUM: one Mathlib search for the Bose integral
∫ t^{s-1}/(e^t - 1) = Γ(s)ζ(s), or a direct geometric series and termwise integration. -/
theorem bose_integral :
    ∫ t in Ioi (0 : ℝ), t / (Real.exp (2 * Real.pi * t) - 1) = 1 / 24 := by
  sorry

/-- LEAF: P0014 page 34, display 4.10, second to fifth lines: with |t² + z²| ≥ 9/4 and the
Bose integral 1/24, the Binet remainder 2|∫_0^∞ t dt / ((t² + z²)(e^{2πt} - 1))| is at most
2 (4/9)(1/24) = 1/27. Class MEDIUM: norm of integral below integral of norm, integrability
of the dominating function, and the given hypotheses. -/
theorem binet_remainder_le (z : ℂ) (hz : z.re = 3 / 2)
    (hden : ∀ t : ℝ, 9 / 4 ≤ ‖(t : ℂ) ^ 2 + z ^ 2‖)
    (hbose : ∫ t in Ioi (0 : ℝ), t / (Real.exp (2 * Real.pi * t) - 1) = 1 / 24) :
    ‖2 * ∫ t in Ioi (0 : ℝ),
        (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * Real.pi * t) : ℂ) - 1))‖ ≤ 1 / 27 := by
  sorry

/-- P0014 page 34, display 4.10, last line: ψ(z) = log z + O*(10/27) on re z = 3/2.
Assembled from the leaves `binet_formula`, `nine_fourths_le_norm`, `bose_integral` and
`binet_remainder_le`, with |1/(2z)| ≤ 1/3. -/
theorem psi_sub_log_le (z : ℂ) (hz : z.re = 3 / 2) :
    ‖digamma z - Complex.log z‖ ≤ 10 / 27 := by
  have hpos : 0 < z.re := by rw [hz]; norm_num
  have hB := binet_remainder_le z hz (nine_fourths_le_norm z hz) bose_integral
  rw [binet_formula z hpos]
  set J := 2 * ∫ t in Ioi (0 : ℝ),
        (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * Real.pi * t) : ℂ) - 1))
  have hnz : 3 / 2 ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rw [hz] at this; norm_num at this ⊢; linarith
  have h1 : ‖1 / (2 * z)‖ ≤ 1 / 3 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  calc ‖Complex.log z - 1 / (2 * z) - J - Complex.log z‖ = ‖-(1 / (2 * z)) + -J‖ := by
        congr 1; ring
    _ ≤ ‖1 / (2 * z)‖ + ‖J‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_neg, norm_neg]
    _ ≤ 1 / 3 + 1 / 27 := add_le_add h1 hB
    _ = 10 / 27 := by norm_num

/-- P0014 page 33, displays 4.8 and 4.9 together, on s = -1/2 + iτ: L'/L(s, χ) =
log(π/q) - ψ(1-s) + log 2 + (π/2) cot(π(s+κ)/2) - L'/L(1-s, χ bar).
Assembled from the leaves `fe_digamma` and `digamma_line_identity`. -/
theorem fe_line {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (τ : ℝ) (κ : ℕ) (hκ : (χ.Even ∧ κ = 0) ∨ (χ.Odd ∧ κ = 1)) :
    deriv χ.LFunction ((-1 / 2 : ℂ) + τ * I) / χ.LFunction ((-1 / 2 : ℂ) + τ * I) =
      ((Real.log (Real.pi / q) : ℝ) : ℂ)
        + (-digamma (1 - ((-1 / 2 : ℂ) + τ * I)) + Complex.log 2 +
          ((Real.pi / 2 : ℝ) : ℂ) * cot ((Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + κ) / 2))
        - logDeriv (χ⁻¹).LFunction (1 - ((-1 / 2 : ℂ) + τ * I)) := by
  have hκ' : κ = 0 ∨ κ = 1 := by rcases hκ with h | h <;> simp [h.2]
  rw [fe_digamma hχ τ κ hκ, ← digamma_line_identity τ κ hκ']
  ring

end LeanLab.HelfgottMajor.Prep1121VIPointwiseA
