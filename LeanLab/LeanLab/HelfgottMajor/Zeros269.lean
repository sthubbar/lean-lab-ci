import LeanLab.HelfgottMajor.Gaussian269
import Mathlib.Analysis.Meromorphic.Divisor

/-!
Finite support for the low zero terms used by Lemma 4.4 of P0014, pages 38 and 39.
This is a convergence prerequisite, not the quantitative zero count estimate.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Zeros269
open Real LeanLab.HelfgottArcs Decomp269a

/-- The low zero terms are summable under the source critical line hypothesis.
Source P0014 Lemma 4.4, pages 38 and 39. CONDITIONAL ON hzeros.+-/
theorem low_zero_terms_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => zeroTerm χ δ x ρ.val) := by
  let K : Set ℂ := (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I) '' Set.Icc (-T) T
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKsub : K ⊆ ({1}ᶜ : Set ℂ) := by
    rintro z ⟨t, _, rfl⟩
    change (1 / 2 : ℂ) + (t : ℂ) * Complex.I ≠ 1
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  have ha0 : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro s hs
    exact (χ.differentiableAt_LFunction s (.inl hs)).differentiableWithinAt
  have ha := ha0.mono hKsub
  have hfin := (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) K).finiteSupport hK
  apply summable_of_hasFiniteSupport
  apply (hfin.preimage (f := Subtype.val) Subtype.val_injective.injOn).subset
  intro ρ hρ
  have hm : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val ≠ 0 := by
    intro h
    simp [Function.mem_support, zeroTerm, h] at hρ
  have hr := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2
  have hmem : ρ.val ∈ K := by
    refine ⟨ρ.val.im, abs_le.mp ρ.property.2.2.2, ?_⟩
    apply Complex.ext
    · simpa using hr.symm
    · simp
  change MeromorphicOn.divisor (DirichletCharacter.LFunction χ) K ρ.val ≠ 0
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha hmem]
  cases ho : analyticOrderAt (DirichletCharacter.LFunction χ) ρ.val <;>
    simp_all [analyticOrderNatAt]

/-- The critical line gives the square root x factor in the proof of Proposition 4.6, page 43.
This is pointwise and uses no quantitative zero estimate.
-/
theorem zero_term_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x : ℝ) (hx : 0 < x) (ρ : ℂ) (hρ : ρ.re = 1 / 2) :
    ‖zeroTerm χ δ x ρ‖ =
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
        ‖gaussianMellin δ ρ‖ * sqrt x := by
  rw [zeroTerm, RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, hρ, ← sqrt_eq_rpow]
  ring

/-- The low zero estimate follows from the actual Mellin norm sum of Lemma 4.4, pages 38 to 43.
CONDITIONAL ON hzeros and hbudget. This does not prove the cited quantitative bound hbudget.
-/
theorem low_zero_bound_of_mellin_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T : ℝ) (hx : 0 < x)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hbudget : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖) ≤
      2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) :
    ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) *
        sqrt x := by
  unfold lowZeros
  calc
    _ ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, ‖zeroTerm χ δ x ρ.val‖ :=
      norm_tsum_le_tsum_norm (low_zero_terms_summable χ δ x T hzeros).norm
    _ = ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖) * sqrt x := by
      apply tsum_congr
      intro ρ
      exact zero_term_norm χ δ x hx ρ.val
        (hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2)
    _ = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖) * sqrt x := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (sqrt_nonneg x)

/-- The high zero step on page 43 follows from a summable Mellin mass budget.
CONDITIONAL ON hsum and hbudget. No quantitative tail estimate is proved here.
-/
theorem high_zero_bound_of_mellin_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T B : ℝ) (hx : 1 ≤ x)
    (hsum : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖))
    (hbudget : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖) ≤ B) :
    ‖highZeros χ δ x T‖ ≤ B * x := by
  have hx0 : 0 < x := by linarith
  have hpoint : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, ‖zeroTerm χ δ x ρ.val‖ ≤
        ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖) * x := by
    intro ρ
    rw [zeroTerm, RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hp : x ^ ρ.val.re ≤ x := by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hx ρ.property.2.2.1.le
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp
      (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  have hz := (hsum.mul_right x).of_norm_bounded hpoint
  unfold highZeros
  calc
    _ ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, ‖zeroTerm χ δ x ρ.val‖ :=
      norm_tsum_le_tsum_norm hz.norm
    _ ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖) * x := hz.norm.tsum_le_tsum hpoint (hsum.mul_right x)
    _ = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖) * x := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hx0.le

end LeanLab.HelfgottMajor.Zeros269
