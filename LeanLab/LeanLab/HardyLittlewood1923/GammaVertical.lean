import LeanLab.PNTPort.ZetaZeros.GammaBounds

/-!
AI wrote this Lean code for CODEX task52.
The target is the Gamma estimate used on paper P0004 page 19 in equation 2.825.
The normalized Gamma function gives the sharp polynomial exponent on the strip.
-/

open Complex Real Set Filter MeasureTheory
open scoped ComplexConjugate

namespace LeanLab.HardyLittlewood1923.Task52

/-- The half line estimate with both signs of the height. -/
theorem gamma_half_abs (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (π * |t| / 2) ≤ √(2 * π) := by
  by_cases ht : 0 ≤ t
  · simpa [abs_of_nonneg ht] using
      LeanLab.PNTPort.ZetaZeros.norm_Gamma_half_mul_exp_le t
  · have hc : (1 / 2 : ℂ) + (-t : ℝ) * I = conj (1 / 2 + t * I) := by
      apply Complex.ext <;> simp
    have h := LeanLab.PNTPort.ZetaZeros.norm_Gamma_half_mul_exp_le (-t)
    rw [hc, Complex.Gamma_conj, norm_conj] at h
    simpa [abs_of_neg (lt_of_not_ge ht)] using h

noncomputable def gammaNormalized (s : ℂ) : ℂ :=
  Complex.Gamma s * Complex.exp ((1 / 2 - s) * Complex.log (s + 1))

lemma norm_gammaNormalized {s : ℂ} (hs : 0 < s.re) :
    ‖gammaNormalized s‖ = ‖Complex.Gamma s‖ *
      ‖s + 1‖ ^ (1 / 2 - s.re) * Real.exp (s.im * Complex.arg (s + 1)) := by
  have hn : 0 < ‖s + 1‖ := by
    apply norm_pos_iff.mpr
    intro h
    have h' := congr_arg Complex.re h
    simp at h'
    linarith
  rw [gammaNormalized, norm_mul, Complex.norm_exp]
  have he : (((1 / 2 : ℂ) - s) * Complex.log (s + 1)).re =
      Real.log ‖s + 1‖ * (1 / 2 - s.re) + s.im * Complex.arg (s + 1) := by
    simp [Complex.mul_re, Complex.log_re, Complex.log_im]
    ring
  rw [he, Real.exp_add, ← Real.rpow_def_of_pos hn]
  ring

lemma height_arg_le {s : ℂ} (hs : 0 ≤ s.re) :
    s.im * Complex.arg (s + 1) ≤ π * |s.im| / 2 := by
  have ha : |Complex.arg (s + 1)| ≤ π / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (by simp; linarith)
  calc s.im * Complex.arg (s + 1) ≤ |s.im * Complex.arg (s + 1)| := le_abs_self _
    _ = |s.im| * |Complex.arg (s + 1)| := abs_mul _ _
    _ ≤ |s.im| * (π / 2) := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
    _ = π * |s.im| / 2 := by ring

lemma gammaNormalized_half (t : ℝ) :
    ‖gammaNormalized (1 / 2 + t * I)‖ ≤ √(2 * π) := by
  rw [norm_gammaNormalized (by norm_num)]
  have hre : ((1 / 2 : ℂ) + t * I).re = 1 / 2 := by simp
  have him : ((1 / 2 : ℂ) + t * I).im = t := by simp
  rw [hre, him, sub_self, Real.rpow_zero, mul_one]
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
    simpa using height_arg_le (s := (1 / 2 : ℂ) + t * I) (by norm_num)))
      (norm_nonneg _)).trans (gamma_half_abs t)

lemma gammaNormalized_three_half (t : ℝ) :
    ‖gammaNormalized (3 / 2 + t * I)‖ ≤ √(2 * π) := by
  have hG : Complex.Gamma (3 / 2 + t * I) =
      (1 / 2 + t * I) * Complex.Gamma (1 / 2 + t * I) := by
    rw [show (3 / 2 + t * I : ℂ) = (1 / 2 + t * I) + 1 by ring]
    exact Complex.Gamma_add_one _ (by
      intro h
      have h' := congr_arg Complex.re h
      norm_num at h')
  have hn : ‖(1 / 2 + t * I : ℂ)‖ ≤ ‖(3 / 2 + t * I : ℂ) + 1‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    simp [Complex.normSq_apply]
    nlinarith
  have hp : 0 < ‖(3 / 2 + t * I : ℂ) + 1‖ := by
    apply norm_pos_iff.mpr
    intro h
    have h' := congr_arg Complex.re h
    norm_num at h'
  rw [norm_gammaNormalized (by norm_num), hG, norm_mul]
  have hre : ((3 / 2 : ℂ) + t * I).re = 3 / 2 := by simp
  have him : ((3 / 2 : ℂ) + t * I).im = t := by simp
  rw [hre, him, show (1 / 2 : ℝ) - 3 / 2 = -1 by norm_num, Real.rpow_neg_one]
  have he : Real.exp (t * Complex.arg ((3 / 2 : ℂ) + t * I + 1)) ≤
      Real.exp (π * |t| / 2) := Real.exp_le_exp.mpr (by
    simpa using height_arg_le (s := (3 / 2 : ℂ) + t * I) (by norm_num))
  calc _ ≤ ‖(1 / 2 + t * I : ℂ)‖ * ‖Complex.Gamma (1 / 2 + t * I)‖ *
        ‖(3 / 2 + t * I : ℂ) + 1‖⁻¹ * Real.exp (π * |t| / 2) := by gcongr
    _ = (‖(1 / 2 + t * I : ℂ)‖ / ‖(3 / 2 + t * I : ℂ) + 1‖) *
        (‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (π * |t| / 2)) := by ring
    _ ≤ 1 * √(2 * π) := mul_le_mul ((div_le_one hp).mpr hn) (gamma_half_abs t)
        (by positivity) (by norm_num)
    _ = _ := one_mul _

lemma gammaNormalized_differentiable {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ gammaNormalized s := by
  have hn : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    rw [hn] at hs
    simp at hs
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hl : s + 1 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp
    linarith
  exact (Complex.differentiableAt_Gamma s hn).mul
    (Complex.differentiableAt_exp.comp s
      (((differentiableAt_const _).sub differentiableAt_id).mul
        ((Complex.differentiableAt_log hl).comp s
          (differentiableAt_id.add_const 1))))

/-- A sharp polynomial Gamma bound before the elementary angle estimate. -/
theorem gammaNormalized_le {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    ‖gammaNormalized s‖ ≤ √(2 * π) := by
  have hcl : closure (Complex.re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2)) ⊆
      {z : ℂ | 0 < z.re} := by
    have hsub : Complex.re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2) ⊆
        Complex.re ⁻¹' Icc (1 / 2 : ℝ) (3 / 2) := preimage_mono Ioo_subset_Icc_self
    have hc := closure_minimal hsub (isClosed_Icc.preimage Complex.continuous_re)
    intro z hz
    have hz' := hc hz
    simp only [mem_preimage, mem_Icc] at hz'
    simp only [mem_setOf_eq]
    linarith [hz'.1]
  have hd : DiffContOnCl ℂ gammaNormalized (Complex.re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2)) :=
    DifferentiableOn.diffContOnCl (fun z hz =>
      (gammaNormalized_differentiable (hcl hz)).differentiableWithinAt)
  let K : ℝ := Real.Gamma (1 / 2) + Real.Gamma (3 / 2)
  have hK : 0 ≤ K := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    dsimp [K]
    positivity
  have hB : ∃ c < π / ((3 / 2 : ℝ) - 1 / 2), ∃ B,
      gammaNormalized =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2))]
          fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1, by have := Real.pi_gt_three; norm_num; linarith, π / 2, ?_⟩
    refine Asymptotics.IsBigO.of_bound K ?_
    refine Filter.eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)
    simp only [mem_preimage, mem_Ioo] at hz
    rw [norm_gammaNormalized (by linarith), Real.norm_of_nonneg (Real.exp_pos _).le]
    have hG := LeanLab.PNTPort.ZetaZeros.norm_Gamma_strip_le hz.1.le hz.2.le
    have hn : 1 ≤ ‖z + 1‖ := by
      have h := Complex.re_le_norm (z + 1)
      simp at h
      linarith [hz.1]
    have hp : ‖z + 1‖ ^ (1 / 2 - z.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
    have he : z.im * Complex.arg (z + 1) ≤ π / 2 * Real.exp (1 * |z.im|) := by
      have ha := height_arg_le (s := z) (by linarith)
      have hb := Real.add_one_le_exp |z.im|
      have hc := Real.pi_pos
      rw [one_mul]
      nlinarith
    calc _ ≤ K * 1 * Real.exp (π / 2 * Real.exp (1 * |z.im|)) :=
        mul_le_mul (mul_le_mul hG hp (by positivity) hK) (Real.exp_le_exp.mpr he)
          (by positivity) (by positivity)
      _ = _ := by ring
  refine PhragmenLindelof.vertical_strip hd hB (fun z hz => ?_) (fun z hz => ?_) h1 h2
  · have he : z = 1 / 2 + z.im * I := by apply Complex.ext <;> simp [hz]
    rw [he]
    exact gammaNormalized_half z.im
  · have he : z = 3 / 2 + z.im * I := by apply Complex.ext <;> simp [hz]
    rw [he]
    exact gammaNormalized_three_half z.im

lemma arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.arg z = Real.arctan (z.im / z.re) := by
  have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  exact (Real.arctan_eq_of_tan_eq (Complex.tan_arg z) (abs_lt.mp ha)).symm

lemma height_arctan_lower {a : ℝ} (ha : 0 < a) (t : ℝ) :
    π * |t| / 2 - a ≤ t * Real.arctan (t / a) := by
  have hp : ∀ u : ℝ, 0 ≤ u → π * u / 2 - a ≤ u * Real.arctan (u / a) := by
    intro u hu
    rcases hu.eq_or_lt with rfl | hu
    · simp
      linarith
    have hd : (a / u)⁻¹ = u / a := by field_simp
    have he := Real.arctan_inv_of_pos (div_pos ha hu)
    rw [hd] at he
    have hb := mul_le_mul_of_nonneg_left (Real.arctan_le_self (div_pos ha hu).le) hu.le
    have hc : u * (a / u) = a := by field_simp
    rw [hc] at hb
    rw [he]
    nlinarith
  by_cases ht : 0 ≤ t
  · simpa [abs_of_nonneg ht] using hp t ht
  · have h := hp (-t) (by linarith)
    simpa [abs_of_neg (lt_of_not_ge ht), neg_div, Real.arctan_neg] using h

lemma height_arg_lower {s : ℂ} (hs : 0 < s.re) :
    π * |s.im| / 2 - (s.re + 1) ≤ s.im * Complex.arg (s + 1) := by
  rw [arg_eq_arctan_of_re_pos (by simp; linarith : 0 < (s + 1).re)]
  simpa using height_arctan_lower (by linarith : 0 < s.re + 1) s.im

/-- The Gamma vertical line estimate with the sharp polynomial exponent. -/
theorem gamma_vertical {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    ‖Complex.Gamma s‖ ≤ √(2 * π) * Real.exp (5 / 2) *
      ‖s + 1‖ ^ (s.re - 1 / 2) * Real.exp (-(π * |s.im| / 2)) := by
  have hs : 0 < s.re := by linarith
  have hn : 0 < ‖s + 1‖ := by
    apply norm_pos_iff.mpr
    intro he
    have he' := congr_arg Complex.re he
    simp at he'
    linarith
  have h := mul_le_mul_of_nonneg_right (gammaNormalized_le h1 h2)
    (show 0 ≤ ‖s + 1‖ ^ (s.re - 1 / 2) *
      Real.exp (-(s.im * Complex.arg (s + 1))) by positivity)
  rw [norm_gammaNormalized hs] at h
  have hc : ‖s + 1‖ ^ (1 / 2 - s.re) * ‖s + 1‖ ^ (s.re - 1 / 2) = 1 := by
    rw [← Real.rpow_add hn]
    simp
  have he : Real.exp (s.im * Complex.arg (s + 1)) *
      Real.exp (-(s.im * Complex.arg (s + 1))) = 1 := by rw [← Real.exp_add]; simp
  have hbase : ‖Complex.Gamma s‖ ≤ √(2 * π) * ‖s + 1‖ ^ (s.re - 1 / 2) *
      Real.exp (-(s.im * Complex.arg (s + 1))) := by
    calc _ = (‖Complex.Gamma s‖ * ‖s + 1‖ ^ (1 / 2 - s.re) *
          Real.exp (s.im * Complex.arg (s + 1))) *
          (‖s + 1‖ ^ (s.re - 1 / 2) * Real.exp (-(s.im * Complex.arg (s + 1)))) := by
            rw [show (‖Complex.Gamma s‖ * ‖s + 1‖ ^ (1 / 2 - s.re) *
              Real.exp (s.im * Complex.arg (s + 1))) *
              (‖s + 1‖ ^ (s.re - 1 / 2) * Real.exp (-(s.im * Complex.arg (s + 1)))) =
              ‖Complex.Gamma s‖ * (‖s + 1‖ ^ (1 / 2 - s.re) * ‖s + 1‖ ^ (s.re - 1 / 2)) *
              (Real.exp (s.im * Complex.arg (s + 1)) * Real.exp (-(s.im * Complex.arg (s + 1)))) by ring]
            rw [hc, he, mul_one, mul_one]
      _ ≤ _ := by convert h using 1 <;> ring
  have hb : Real.exp (-(s.im * Complex.arg (s + 1))) ≤
      Real.exp (5 / 2) * Real.exp (-(π * |s.im| / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [height_arg_lower hs]
  calc _ ≤ _ := hbase
    _ ≤ √(2 * π) * ‖s + 1‖ ^ (s.re - 1 / 2) *
        (Real.exp (5 / 2) * Real.exp (-(π * |s.im| / 2))) := by gcongr
    _ = _ := by ring

/-- The Gamma kernel has exponential decay in every right half plane sector. -/
theorem gamma_kernel_bound {s z : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2)
    (hz : z ≠ 0) :
    ‖Complex.Gamma s * z ^ (-s)‖ ≤ √(2 * π) * Real.exp (5 / 2) *
      ‖z‖ ^ (-s.re) * ‖s + 1‖ ^ (s.re - 1 / 2) *
        Real.exp (-((π / 2 - |Complex.arg z|) * |s.im|)) := by
  have hc : ‖z ^ (-s)‖ = ‖z‖ ^ (-s.re) * Real.exp (Complex.arg z * s.im) := by
    rw [Complex.norm_cpow_of_ne_zero hz]
    simp [Real.exp_neg, div_eq_mul_inv]
  rw [norm_mul, hc]
  have he : -(π * |s.im| / 2) + Complex.arg z * s.im ≤
      -((π / 2 - |Complex.arg z|) * |s.im|) := by
    have ha : Complex.arg z * s.im ≤ |Complex.arg z| * |s.im| := by
      calc _ ≤ |Complex.arg z * s.im| := le_abs_self _
        _ = _ := abs_mul _ _
    nlinarith
  calc _ ≤ (√(2 * π) * Real.exp (5 / 2) * ‖s + 1‖ ^ (s.re - 1 / 2) *
          Real.exp (-(π * |s.im| / 2))) *
          (‖z‖ ^ (-s.re) * Real.exp (Complex.arg z * s.im)) := by
            exact mul_le_mul_of_nonneg_right (gamma_vertical h1 h2) (by positivity)
    _ = √(2 * π) * Real.exp (5 / 2) * ‖z‖ ^ (-s.re) * ‖s + 1‖ ^ (s.re - 1 / 2) *
        Real.exp (-(π * |s.im| / 2) + Complex.arg z * s.im) := by
          rw [Real.exp_add]
          ring
    _ ≤ _ := by gcongr

/-- Positive real part gives a positive decay rate. -/
theorem kernel_decay_pos {z : ℂ} (hz : 0 < z.re) :
    0 < π / 2 - |Complex.arg z| := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  linarith

#print axioms gamma_half_abs
#print axioms norm_gammaNormalized
#print axioms height_arg_le
#print axioms gammaNormalized_half
#print axioms gammaNormalized_three_half
#print axioms gammaNormalized_differentiable
#print axioms gammaNormalized_le
#print axioms arg_eq_arctan_of_re_pos
#print axioms height_arctan_lower
#print axioms height_arg_lower
#print axioms gamma_vertical
#print axioms gamma_kernel_bound
#print axioms kernel_decay_pos

end LeanLab.HardyLittlewood1923.Task52
