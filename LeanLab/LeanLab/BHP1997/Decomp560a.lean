/-
P0069 page 22 Lemma 8, Rademacher reference 28.
Independent split of the ordinary Gamma quotient comparison.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace LeanLab.BHP1997.Decomp560a
open Complex Set Filter MeasureTheory Asymptotics
open scoped Topology

/-- Rademacher page 197 display 5.1, the ordinary Gamma quotient as complex data. -/
noncomputable def gammaRatio (Q : ℝ) (s : ℂ) : ℂ :=
  Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) /
    Complex.Gamma ((Q : ℂ) / 2 + s / 2)

/-- Euler's integral bounds the complex Gamma function in the positive half plane.
Auxiliary estimate for Rademacher page 197 display 5.1. -/
theorem norm_Gamma_le_real {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ = _
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- Compact real Gamma bounds give a height-independent upper bound on positive strips.
Auxiliary estimate for Rademacher page 197 display 5.1. -/
theorem Gamma_bounded_on_positive_strip {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Complex.Gamma z‖ ≤ C := by
  have hc : ContinuousOn Real.Gamma (Icc a b) := by
    apply ContinuousOn.mono Real.differentiableOn_Gamma_Ioi.continuousOn
    intro x hx
    exact ha.trans_le hx.1
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  refine ⟨Real.Gamma x, Real.Gamma_pos_of_pos (ha.trans_le hx.1), ?_⟩
  intro z hza hzb
  exact (norm_Gamma_le_real (ha.trans_le hza)).trans (hmax ⟨hza, hzb⟩)

/-- Rademacher page 197 after display 5.1, the quotient is regular on the closed strip.
The reciprocal Gamma function fills its zeros at the poles of Gamma. -/
theorem gammaRatio_diffContOnCl {Q : ℝ} (hQ : 0 ≤ Q) :
    DiffContOnCl ℂ (gammaRatio Q) (Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  apply DifferentiableOn.diffContOnCl
  intro s hs
  have hs' : s.re ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    have hh : closure (Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2)) ⊆
        Complex.re ⁻¹' Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      closure_minimal (by intro z hz; exact ⟨hz.1.le, hz.2.le⟩)
        (isClosed_Icc.preimage Complex.continuous_re)
    exact hh hs
  have hn : 0 < ((Q : ℂ) / 2 + (1 - s) / 2).re := by
    simp
    linarith [hs'.2]
  have hd := (Complex.hasDerivAt_Gamma_of_re_pos hn).differentiableAt.comp s
    (show DifferentiableAt ℂ (fun s : ℂ => (Q : ℂ) / 2 + (1 - s) / 2) s by fun_prop)
  have hi := Complex.differentiable_one_div_Gamma.differentiableAt.comp s
    (show DifferentiableAt ℂ (fun s : ℂ => (Q : ℂ) / 2 + s / 2) s by fun_prop)
  convert (hd.mul hi).differentiableWithinAt using 1
  ext z
  simp [gammaRatio, div_eq_mul_inv]

/-- The exponential formula bounds the complex sine by exponential imaginary height.
Auxiliary estimate for the Gamma reflection formula used in page 197 display 5.1. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h1 : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  have h2 : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have hh := (norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))).trans
    (add_le_add h1 h2)
  norm_num
  simp only [neg_mul] at hh
  linarith

/-- Away from the real axis, each positive integer shift can only increase the Gamma norm.
Auxiliary recurrence estimate for Rademacher page 197 display 5.1. -/
theorem Gamma_norm_le_nat_shift {z : ℂ} (ht : 1 ≤ |z.im|) (n : ℕ) :
    ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 1 ≤ ‖z + n‖ := by
      have hh := Complex.abs_im_le_norm (z + n)
      simp only [add_im, natCast_im, add_zero] at hh
      exact ht.trans hh
    have hne : z + n ≠ 0 := by
      intro he
      rw [he, norm_zero] at hn
      norm_num at hn
    calc
      _ ≤ ‖Complex.Gamma (z + n)‖ := ih
      _ ≤ ‖z + n‖ * ‖Complex.Gamma (z + n)‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hn
      _ = ‖Complex.Gamma (z + (n + 1 : ℕ))‖ := by
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne, norm_mul]

/-- Gamma reflection expresses its reciprocal through a positive-height reflected Gamma value.
Source DLMF 5.5.3, auxiliary to Rademacher page 197 display 5.1. -/
theorem reciprocal_Gamma_reflection {z : ℂ} (ht : 1 ≤ |z.im|) :
    (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi := by
  have him : z.im ≠ 0 := by intro he; norm_num [he] at ht
  have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (by
    intro n he
    apply him
    have hh := congrArg Complex.im he
    simpa using hh)
  have hsin : Complex.sin (Real.pi * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k he
    have hh := congrArg Complex.im he
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, intCast_im, intCast_re,
      mul_zero] at hh
    exact him ((mul_eq_zero.mp hh).resolve_left Real.pi_ne_zero)
  have hp : Complex.Gamma z * (Complex.Gamma (1 - z) * Complex.sin (Real.pi * z)) = Real.pi := by
    rw [← mul_assoc, Complex.Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ hsin]
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).mpr
  calc
    _ = (Complex.Gamma z)⁻¹ *
        (Complex.Gamma z * (Complex.Gamma (1 - z) * Complex.sin (Real.pi * z))) := by rw [hp]
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hΓ, one_mul]

/-- Recurrence and reflection bound reciprocal Gamma at large height on each fixed strip.
Source DLMF 5.5.1 and 5.5.3, auxiliary to Rademacher page 197 display 5.1. -/
theorem reciprocal_Gamma_high_strip {a b : ℝ} (hab : a ≤ b) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      ‖(Complex.Gamma z)⁻¹‖ ≤ A * Real.exp (Real.pi * |z.im|) := by
  obtain ⟨n, hn⟩ := exists_nat_gt b
  obtain ⟨C, hC, hupper⟩ := Gamma_bounded_on_positive_strip
    (a := 1 - b + n) (b := 1 - a + n) (by linarith) (by linarith)
  refine ⟨C / Real.pi, by positivity, ?_⟩
  intro z hza hzb ht
  have href : ‖Complex.Gamma (1 - z)‖ ≤ C := by
    refine (Gamma_norm_le_nat_shift (z := 1 - z) (by simpa using ht) n).trans ?_
    apply hupper <;> simp <;> linarith
  have hsin : ‖Complex.sin (Real.pi * z)‖ ≤ Real.exp (Real.pi * |z.im|) := by
    simpa [abs_mul, Real.pi_pos.le] using norm_sin_le_exp_abs_im (Real.pi * z)
  rw [reciprocal_Gamma_reflection ht, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ (C * Real.exp (Real.pi * |z.im|)) / Real.pi := by
      gcongr
    _ = _ := by ring

/-- A crude reciprocal bound sufficient in place of DLMF 5.11.9 for Rademacher
page 197 display 5.1. Reflection and recurrence prove exponential strip growth.
The proof uses compactness only for Gamma at bounded height. -/
theorem leaf_reciprocal_Gamma_strip {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (B * |z.im|) := by
  obtain ⟨A, hA, hlarge⟩ := reciprocal_Gamma_high_strip hab
  let S : Set ℂ := Icc a b ×ℂ Icc (-1 : ℝ) 1
  have hS : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  have hSne : S.Nonempty := by
    refine ⟨(a : ℂ), ?_⟩
    change ((a : ℂ).re ∈ Icc a b) ∧ ((a : ℂ).im ∈ Icc (-1 : ℝ) 1)
    simp only [ofReal_re, ofReal_im]
    exact ⟨⟨le_rfl, hab⟩, by norm_num⟩
  have hc : ContinuousOn (fun z : ℂ => ‖(Complex.Gamma z)⁻¹‖) S :=
    Complex.differentiable_one_div_Gamma.continuous.norm.continuousOn
  obtain ⟨w, hw, hmax⟩ := hS.exists_isMaxOn hSne hc
  let C : ℝ := A + ‖(Complex.Gamma w)⁻¹‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, Real.pi, hC, Real.pi_pos, ?_⟩
  intro z hza hzb
  have hAC : A ≤ C := by dsimp [C]; linarith [norm_nonneg ((Complex.Gamma w)⁻¹)]
  by_cases ht : 1 ≤ |z.im|
  · exact (hlarge z hza hzb ht).trans
      (mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le)
  · have hz : z ∈ S := by
      change z.re ∈ Icc a b ∧ z.im ∈ Icc (-1 : ℝ) 1
      exact ⟨⟨hza, hzb⟩, (abs_le.mp (le_of_lt (lt_of_not_ge ht)))⟩
    have he : 1 ≤ Real.exp (Real.pi * |z.im|) := Real.one_le_exp (by positivity)
    calc
      _ ≤ ‖(Complex.Gamma w)⁻¹‖ := hmax hz
      _ ≤ C := by dsimp [C]; linarith
      _ ≤ C * Real.exp (Real.pi * |z.im|) := le_mul_of_one_le_right hC.le he

/-- The reciprocal Stirling strip estimate implies linear exponential growth of the quotient.
Auxiliary step for Rademacher page 197 display 5.1.
CONDITIONAL ON the explicit reciprocal Gamma strip estimate. -/
theorem gammaRatio_exponential_growth {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ a b : ℝ, 0 < a → a ≤ b →
      ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
        ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (B * |z.im|)) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ s : ℂ,
      -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
        ‖gammaRatio Q s‖ ≤ C * Real.exp (B * |s.im|) := by
  obtain ⟨A, hA, hupper⟩ := Gamma_bounded_on_positive_strip
    (a := Q / 2 + 1 / 4) (b := Q / 2 + 3 / 4) (by linarith) (by linarith)
  obtain ⟨C, B, hC, hB, hrec⟩ := hrec (Q / 2 + 3 / 4) (Q / 2 + 5 / 4)
    (by linarith) (by linarith)
  refine ⟨A * C * (Q + 1), B / 2 + 1, by positivity, by positivity, ?_⟩
  intro s hsl hsu
  let w : ℂ := (Q : ℂ) / 2 + s / 2
  have hu : ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2)‖ ≤ A :=
    hupper _ (by simp; linarith) (by simp; linarith)
  have hi : ‖(Complex.Gamma (w + 1))⁻¹‖ ≤ C * Real.exp (B * (|s.im| / 2)) := by
    have hh := hrec (w + 1) (by simp [w]; linarith) (by simp [w]; linarith)
    simpa [w, abs_div] using hh
  have hw : ‖w‖ ≤ (Q + 1) * (|s.im| + 1) := by
    have hh := Complex.norm_le_abs_re_add_abs_im w
    have hre : |w.re| ≤ Q / 2 + 1 / 4 := by
      apply abs_le.mpr
      simp [w]
      constructor <;> linarith
    have him : |w.im| = |s.im| / 2 := by simp [w, abs_div]
    rw [him] at hh
    nlinarith [abs_nonneg s.im, mul_nonneg hQ (abs_nonneg s.im)]
  have hden : ‖(Complex.Gamma w)⁻¹‖ ≤
      ((Q + 1) * (|s.im| + 1)) * (C * Real.exp (B * (|s.im| / 2))) := by
    rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one, norm_mul]
    exact mul_le_mul hw hi (norm_nonneg _) (by positivity)
  calc
    ‖gammaRatio Q s‖ = ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2)‖ *
        ‖(Complex.Gamma w)⁻¹‖ := by simp [gammaRatio, w, div_eq_mul_inv]
    _ ≤ A * (((Q + 1) * (|s.im| + 1)) * (C * Real.exp (B * (|s.im| / 2)))) :=
      mul_le_mul hu hden (norm_nonneg _) hA.le
    _ ≤ A * (((Q + 1) * Real.exp |s.im|) * (C * Real.exp (B * (|s.im| / 2)))) := by
      gcongr
      exact Real.add_one_le_exp _
    _ = (A * C * (Q + 1)) * Real.exp ((B / 2 + 1) * |s.im|) := by
      rw [show (B / 2 + 1) * |s.im| = |s.im| + B * (|s.im| / 2) by ring,
        Real.exp_add]
      ring

/-- Rademacher page 197 Lemma 1, quotient growth needed for the maximum principle.
The proof uses Gamma recurrence, reflection and Euler's integral, with no analytic input. -/
theorem gammaRatio_strip_growth {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ s : ℂ,
      -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
        ‖gammaRatio Q s‖ ≤ C * Real.exp (B * |s.im|) := by
  exact gammaRatio_exponential_growth hQ (fun a b ha hab => leaf_reciprocal_Gamma_strip ha hab)

/-- Rademacher page 197, Lemma 1, the right boundary equality follows from conjugation. -/
theorem gamma_ratio_right_edge {Q : ℝ} (hQ : 0 ≤ Q) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) /
      Complex.Gamma ((Q : ℂ) / 2 + s / 2)‖ = 1 := by
  let w : ℂ := (Q : ℂ) / 2 + s / 2
  have hw : 0 < w.re := by simp [w, hs]; linarith
  have he : (Q : ℂ) / 2 + (1 - s) / 2 = (starRingEnd ℂ) w := by
    apply Complex.ext <;> simp [w, Complex.div_re, Complex.div_im, hs] <;> ring
  rw [he, Complex.Gamma_conj, norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hw))

/-- Rademacher page 197 display 5.2, the left boundary follows from Gamma recurrence. -/
theorem gamma_ratio_left_edge {Q : ℝ} (hQ : 0 ≤ Q) {s : ℂ} (hs : s.re = -(1 / 2 : ℝ)) :
    ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) /
      Complex.Gamma ((Q : ℂ) / 2 + s / 2)‖ ≤ ‖(Q : ℂ) + 1 + s‖ / 2 := by
  let w : ℂ := (Q : ℂ) / 2 + s / 2
  by_cases hG : Complex.Gamma w = 0
  · change ‖_ / Complex.Gamma w‖ ≤ _
    rw [hG, div_zero, norm_zero]
    positivity
  have hw : w ≠ 0 := by intro h; apply hG; rw [h, Complex.Gamma_zero]
  have he : (Q : ℂ) / 2 + (1 - s) / 2 = (starRingEnd ℂ) (w + 1) := by
    apply Complex.ext <;> simp [w, Complex.div_re, Complex.div_im, hs] <;> ring
  have hn : ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) / Complex.Gamma w‖ = ‖w‖ := by
    rw [he, Complex.Gamma_conj, Complex.norm_div, Complex.norm_conj,
      Complex.Gamma_add_one w hw, norm_mul, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hG)]
  change ‖_ / Complex.Gamma w‖ ≤ _
  rw [hn]
  have hw2 : ‖w‖ ^ 2 = (Q / 2 - 1 / 4) ^ 2 + (s.im / 2) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [w, hs]
    ring
  have hv2 : (‖(Q : ℂ) + 1 + s‖ / 2) ^ 2 = (Q / 2 + 1 / 4) ^ 2 + (s.im / 2) ^ 2 := by
    rw [div_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [hs]
    ring
  nlinarith [norm_nonneg w, norm_nonneg ((Q : ℂ) + 1 + s)]

/-- LEAF. Rademacher pages 192 and 193 Theorem 1, displays 2.2, 2.3 and 2.32.
Specialize to a equal to minus one half, b equal to one half, gamma equal to
minus one and delta equal to zero. Replace Q by Q plus one and multiply the
analytic multiplier by exp of one half minus s times log two.
This is a harmonic boundary construction with no Gamma function. OPEN. -/
theorem leaf_strip_multiplier {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ φ : ℂ → ℂ,
      DiffContOnCl ℂ φ (Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ s : ℂ,
        -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
          ‖φ s‖ ≤ C * (|s.im| + 1) ^ c) ∧
      (∀ s : ℂ, s.re = -(1 / 2 : ℝ) → ‖φ s‖ = (‖(Q : ℂ) + 1 + s‖ / 2)⁻¹) ∧
      (∀ s : ℂ, s.re = 1 / 2 → ‖φ s‖ = 1) ∧
      (∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
        (‖(Q : ℂ) + 1 + s‖ / 2) ^ (s.re - 1 / 2) ≤ ‖φ s‖) := by
  sorry

/-- Rademacher page 195 after display 3.8, the constant-bound maximum step.
CONDITIONAL ON explicit linear exponential growth and the two boundary bounds. -/
theorem exponential_strip_maximum {f : ℂ → ℂ} {C B M : ℝ}
    (hf : DiffContOnCl ℂ f (Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hC : 0 < C) (hB : 0 < B)
    (hg : ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
      ‖f s‖ ≤ C * Real.exp (B * |s.im|))
    (hl : ∀ s : ℂ, s.re = -(1 / 2 : ℝ) → ‖f s‖ ≤ M)
    (hr : ∀ s : ℂ, s.re = 1 / 2 → ‖f s‖ ≤ M)
    {s : ℂ} (hsl : -(1 / 2 : ℝ) ≤ s.re) (hsu : s.re ≤ 1 / 2) :
    ‖f s‖ ≤ M := by
  have he : ∀ᶠ x : ℝ in atTop, x ≤ Real.exp ((Real.pi / 2) * x) := by
    have hh := (isLittleO_rpow_exp_pos_mul_atTop (1 : ℝ) Real.pi_div_two_pos).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hh] with x hx
    simp only [Real.rpow_one, Real.norm_eq_abs, Real.abs_exp, one_mul] at hx
    exact (le_abs_self x).trans hx
  have hb : ∃ c < Real.pi / (1 / 2 - -(1 / 2 : ℝ)), ∃ D : ℝ,
      f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2))]
          fun z => Real.exp (D * Real.exp (c * |z.im|)) := by
    refine ⟨Real.pi / 2, by norm_num; linarith [Real.pi_pos], B,
      Asymptotics.IsBigO.of_bound C ?_⟩
    have he' : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop,
        |z.im| ≤ Real.exp ((Real.pi / 2) * |z.im|) := tendsto_comap.eventually he
    have hs' : ∀ᶠ z : ℂ in 𝓟 (Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2)),
        z.re ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := Filter.eventually_principal.mpr (by intro z hz; exact hz)
    filter_upwards [he'.filter_mono inf_le_left, hs'.filter_mono inf_le_right] with z hz hs
    simp only [Real.norm_eq_abs, Real.abs_exp]
    exact (hg z hs.1.le hs.2.le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz hB.le)) hC.le)
  exact PhragmenLindelof.vertical_strip hf hb hl hr hsl hsu

/-- Rademacher page 197 Lemma 1 display 5.1, exact assembly of the independent split.
CONDITIONAL ON the harmonic multiplier.
There is no direct admission in this proof and the sealed target is not imported. -/
theorem rademacher_gamma_ratio :
    ∀ Q : ℝ, 0 ≤ Q → ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
      ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) /
        Complex.Gamma ((Q : ℂ) / 2 + s / 2)‖ ≤
        (‖(Q : ℂ) + 1 + s‖ / 2) ^ (1 / 2 - s.re) := by
  intro Q hQ s hsl hsu
  obtain ⟨A, B, hA, hB, hg⟩ := gammaRatio_strip_growth hQ
  obtain ⟨φ, hφ, ⟨C, c, hC, hc, hpg⟩, hpl, hpr, hlow⟩ := leaf_strip_multiplier hQ
  have hf : DiffContOnCl ℂ (fun z => φ z * gammaRatio Q z)
      (Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    simpa only [smul_eq_mul] using hφ.smul (gammaRatio_diffContOnCl hQ)
  have hfg (z : ℂ) (hzl : -(1 / 2 : ℝ) ≤ z.re) (hzu : z.re ≤ 1 / 2) :
      ‖φ z * gammaRatio Q z‖ ≤ (C * A) * Real.exp ((B + c) * |z.im|) := by
    have hp : (|z.im| + 1) ^ c ≤ Real.exp (c * |z.im|) := by
      calc
        _ ≤ (Real.exp |z.im|) ^ c := Real.rpow_le_rpow (by positivity)
          (Real.add_one_le_exp _) hc.le
        _ = _ := by rw [← Real.exp_mul, mul_comm]
    rw [norm_mul]
    calc
      _ ≤ (C * (|z.im| + 1) ^ c) * (A * Real.exp (B * |z.im|)) :=
        mul_le_mul (hpg z hzl hzu) (hg z hzl hzu) (norm_nonneg _) (by positivity)
      _ ≤ (C * Real.exp (c * |z.im|)) * (A * Real.exp (B * |z.im|)) := by gcongr
      _ = _ := by rw [show (B + c) * |z.im| = c * |z.im| + B * |z.im| by ring,
        Real.exp_add]; ring
  have hleft (z : ℂ) (hz : z.re = -(1 / 2 : ℝ)) : ‖φ z * gammaRatio Q z‖ ≤ 1 := by
    have hb : 0 < ‖(Q : ℂ) + 1 + z‖ / 2 := by
      have hh := Complex.abs_re_le_norm ((Q : ℂ) + 1 + z)
      simp only [add_re, ofReal_re, one_re, hz] at hh
      have hp : 0 < Q + 1 + -(1 / 2 : ℝ) := by linarith
      rw [abs_of_pos hp] at hh
      linarith
    rw [norm_mul, hpl z hz]
    calc
      _ ≤ (‖(Q : ℂ) + 1 + z‖ / 2)⁻¹ * (‖(Q : ℂ) + 1 + z‖ / 2) :=
        mul_le_mul_of_nonneg_left (gamma_ratio_left_edge hQ hz) (inv_nonneg.mpr hb.le)
      _ = 1 := inv_mul_cancel₀ hb.ne'
  have hright (z : ℂ) (hz : z.re = 1 / 2) : ‖φ z * gammaRatio Q z‖ ≤ 1 := by
    rw [norm_mul, hpr z hz, gammaRatio, gamma_ratio_right_edge hQ hz]
    norm_num
  have hmax := exponential_strip_maximum hf (mul_pos hC hA) (add_pos hB hc)
    hfg hleft hright hsl hsu
  rw [norm_mul] at hmax
  have hbase : 0 < ‖(Q : ℂ) + 1 + s‖ / 2 := by
    have hh := Complex.abs_re_le_norm ((Q : ℂ) + 1 + s)
    simp only [add_re, ofReal_re, one_re] at hh
    have hp : 0 < Q + 1 + s.re := by linarith
    rw [abs_of_pos hp] at hh
    linarith
  have hp : ‖gammaRatio Q s‖ * (‖(Q : ℂ) + 1 + s‖ / 2) ^ (s.re - 1 / 2) ≤ 1 := by
    calc
      _ ≤ ‖φ s‖ * ‖gammaRatio Q s‖ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hlow s hsl hsu) (norm_nonneg _)
      _ ≤ 1 := hmax
  have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hbase (s.re - 1 / 2))).mpr hp
  change ‖gammaRatio Q s‖ ≤ _
  convert hh using 1
  rw [show (1 / 2 : ℝ) - s.re = -(s.re - 1 / 2) by ring, Real.rpow_neg hbase.le]
  simp only [one_div]

end LeanLab.BHP1997.Decomp560a
