import LeanLab.HelfgottMajor.Decomp269b

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- The sum of 1/|ρ.im| over zeros with 1 < |ρ.im| ≤ T. -/
noncomputable def invImSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) / |ρ.val.im|) ρ

/-- The sum of |ρ.im| * ‖gaussianMellin δ ρ‖^2 over zeros with 1 < |ρ.im| ≤ T. -/
noncomputable def gaussianMomentSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * |ρ.val.im| * ‖gaussianMellin δ ρ.val‖^2) ρ

/-- LEAF. Page 40, display 4.31. Cauchy-Schwarz inequality for sums over zeros. -/
theorem middle_mass_cauchy_schwarz (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    middleMass χ δ T ≤ sqrt (invImSum χ T) * sqrt (gaussianMomentSum χ δ T) := by
  sorry

/-- LEAF. Page 43, display 4.42. Plancherel L2 identities yielding nTwo and nLog bounds. -/
theorem gaussian_moment_sum_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    sqrt (gaussianMomentSum χ δ T) ≤ sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T := by
  sorry

/-- LEAF. Page 40. Riemann-Stieltjes zero count error integrals. -/
theorem inv_im_sum_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    sqrt (invImSum χ T) * (sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T) ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  sorry

/-- Assembly. Exactly Decomp269b.middle_mass_bound. -/
theorem middle_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  have h1 := middle_mass_cauchy_schwarz q χ δ T hT
  have h2 := gaussian_moment_sum_bound q χ δ T hT
  have h3 := inv_im_sum_bound q χ hχ T hT hzeros
  have h_sqrt_nonneg : 0 ≤ sqrt (invImSum χ T) := sqrt_nonneg _
  have h4 := mul_le_mul_of_nonneg_left h2 h_sqrt_nonneg
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
