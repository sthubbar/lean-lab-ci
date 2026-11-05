import LeanLab.Linnik.Decomp335b

/-!
U-1619 audit of Linnik/Decomp307a `poisson_window_localization`, audit defect filed 20261105T0144Z.
AI wrote this Lean code. Binary Goldbach is open.

Filed worry, the factor log^2 x * r against 1/r: CLEARED. Since u = r log x >= A >= 1, the gain
x^(-(C - C') r) = exp(-(C - C') u) absorbs u^2 once C >= C' + 1, so enlarging C is enough.

Real defect, by hand, not a refutation: the leaf allows r up to 1/4 for every D. Page 335 removes
prime powers and the terms below x by taking k about K r log x with K >= 2 e D, which makes the
lower bound x^(-2 K r log D) up to constants. The prime square terms have size x^(-1/2). So the
route needs r small in terms of D, as Gallagher has r small. For r near 1/4 the series bound can
be carried by the prime powers, and nothing bounds the prime window from below. Not refuted.

The repair adds r₁ depending on E, D, eta. The assembly has its own r₀, so it takes the minimum and
its statement does not change. Proved here. `repaired_of_old` shows the repair is only a weakening.
-/

namespace LeanLab.Linnik.Audit1619
open Finset Complex LeanLab.Linnik.Decomp307a LeanLab.Linnik.Decomp1532b

/-- The repaired leaf: as `poisson_window_localization`, with r at most r₁, a constant chosen with
A, B, C, c after E, D, eta. -/
def RepairedWindow : Prop :=
    ∀ E D η : ℝ, 1 ≤ E → 1 ≤ D → 0 < η →
      ∃ r₁ A B C c : ℝ, 0 < r₁ ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
        ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
          |v| ≤ T → 1 / Real.log T ≤ r → r ≤ r₁ →
          (∀ M : ℕ, E * r * Real.log T ≤ M →
            ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
              η / (D ^ k * r) ≤
                ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
                  (n : ℂ) ^ (1 + I * v)) * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖) →
          ∀ x : ℝ, T ^ A ≤ x → ∃ k : ℕ,
            c * x ^ (-C * r) * Real.log x ^ 2 * r ≤
              ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ B⌋₊,
                (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) *
                  primeWindowCoefficient χ x v n‖ -
                Decomp1532b2.poissonKernel k (r * Real.log (x ^ B)) * ‖primeDetector χ x (x ^ B) v‖

/-- The repair is implied by the old leaf, at r₁ = 1/4. -/
theorem repaired_of_old : RepairedWindow := by
  intro E D η hE hD hη
  obtain ⟨A, B, C, c, hA, hB, hC, hc, h⟩ := poisson_window_localization E D η hE hD hη
  exact ⟨1 / 4, A, B, C, c, by norm_num, hA, hB, hC, hc, h⟩

/-- The sealed statement of `Decomp335b.gallagher_zero_detector_of_turan`, from the repaired leaf. -/
theorem detector_of_repaired (hw : RepairedWindow)
    (hpower : ∀ n M : ℕ, 0 < n → n ≤ M → ∀ z : Fin n → ℂ, (∃ i, 1 ≤ ‖z i‖) →
      ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖) :
    ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
  unfold RepairedWindow at hw
  obtain ⟨r₀, E, D, η, hr₀, hr₀hi, hE, hD, hη, hseries⟩ :=
    LeanLab.Linnik.Decomp335a.poisson_series_detector_of_turan hpower
  obtain ⟨r₁, A, B, C, c, hr₁, hA, hB, hC, hc, hwindow⟩ := hw E D η hE hD hη
  refine ⟨min r₀ r₁, A, B, C, c, lt_min hr₀ hr₁, (min_le_left _ _).trans hr₀hi,
    hA, hB, hC, hc, ?_⟩
  intro T hT q hq hqT χ v r hv hχ hrlo hrhi hz x hx
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hl).trans_le hrlo
  have hx1 : 1 ≤ x :=
    (Real.one_le_rpow (by linarith : 1 ≤ T) (by linarith : 0 ≤ A)).trans hx
  have hxy : x ≤ x ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hB.le
  obtain ⟨k, hk⟩ := hwindow T hT q hqT χ v r hv hrlo (hrhi.trans (min_le_right _ _))
    (hseries T hT q hqT χ v r hv hχ hrlo (hrhi.trans (min_le_left _ _)) hz) x hx
  have hh := hk.trans (prime_poisson_partial_summation χ k v hr.le hx1 hxy)
  exact (mul_le_mul_iff_right₀ hr).mp (by simpa only [mul_comm r] using hh)

end LeanLab.Linnik.Audit1619

#print axioms LeanLab.Linnik.Audit1619.repaired_of_old
#print axioms LeanLab.Linnik.Audit1619.detector_of_repaired
