import LeanLab.HelfgottMajor.Zeros269

/-!
P0014 Lemma 4.4, pages 38 to 40, used by Proposition 4.6 on page 43.
The written proof separates zeros below height 1 from the remaining low zeros.
The two analytic ranges stay OPEN. The partition and arithmetic are checked separately.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269b
open Real LeanLab.HelfgottArcs Decomp269a

/-- The multiplicity weighted Mellin norm in Lemma 4.4, pages 38 and 39. -/
noncomputable def mellinMassTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ : ℝ) (ρ : ℂ) : ℝ :=
  (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) * ‖gaussianMellin δ ρ‖

/-- The part of the low Mellin mass with absolute imaginary part at most 1, page 39. -/
noncomputable def veryLowMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | |ρ.val.im| ≤ 1} (fun ρ => mellinMassTerm χ δ ρ.val) ρ

/-- The part of the low Mellin mass with absolute imaginary part greater than 1, pages 39 and 40. -/
noncomputable def middleMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ (fun ρ => mellinMassTerm χ δ ρ.val) ρ

/-- The partition at height 1 used in the proof of Lemma 4.4 on page 39.
CONDITIONAL ON hzeros for the summability of the low terms.
-/
theorem mass_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, mellinMassTerm χ δ ρ.val) =
      veryLowMass χ δ T + middleMass χ δ T := by
  classical
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) := by
    apply (Zeros269.low_zero_terms_summable χ δ 1 T hzeros).norm.congr
    intro ρ
    simp [zeroTerm, mellinMassTerm, nsmul_eq_mul]
  unfold veryLowMass middleMass
  rw [← (hm.indicator _).tsum_add (hm.indicator _)]
  apply tsum_congr
  intro ρ
  by_cases h : |ρ.val.im| ≤ 1 <;> simp [Set.indicator, h]

/-- LEAF. Page 39, the very low zero paragraph, using displays 4.25, 4.26 and 4.30.
The Gaussian half moment bound 2.15581 is from display 4.42 on page 43.
This counts only the zeros below height 1 and does not estimate the middle range.
-/
theorem very_low_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    veryLowMass χ δ T ≤ 2.15581 * (0.819 * log q + 16.8) := by
  sorry

/-- LEAF. Pages 39 and 40, display 4.32 and the final Cauchy-Schwarz estimate.
The Gaussian moments are those in display 4.42 on page 43.
This estimates only zeros with absolute imaginary part greater than 1 and at most T.
-/
theorem middle_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  sorry

/-- Exactly Decomp269a.low_zero_bound, assembled from the two smaller analytic ranges.
The proof has no sorry of its own. The quantitative analytic leaves remain OPEN.
-/
theorem low_zero_bound (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38) * sqrt x := by
  apply Zeros269.low_zero_bound_of_mellin_sum χ δ x T (by linarith) hzeros
  change (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, mellinMassTerm χ δ ρ.val) ≤ _
  rw [mass_split χ δ T hzeros]
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hv := very_low_mass_bound q χ hχ δ T hT1 hzeros
  have hm := middle_mass_bound q χ hχ δ T hT1 hzeros
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hlogqT : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have ha := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0_log
    (mul_nonneg (sqrt_nonneg T) hlogqT)
  have hb := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0 (sqrt_nonneg T)
  obtain ⟨hc, hd⟩ := Sec45.coef_logq
  nlinarith

end LeanLab.HelfgottMajor.Decomp269b
