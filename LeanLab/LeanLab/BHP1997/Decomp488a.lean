/-
P0069, Lemma 9, pages 22 and 23. CODEX task165.
The contour and cited L-function bounds remain OPEN.
The final assembly is CONDITIONAL on the named leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp132b
import LeanLab.BHP1997.KernelC165
import Mathlib.Analysis.Complex.RemovableSingularity
import LeanLab.DERZ1997.Perron136
import LeanLab.PNTPort.StrongPNT.ResidueCalcOnRectangles

namespace LeanLab.BHP1997.DecompC165a
open Classical Complex MeanValue132

/-- Page 23, the weighted fourth moment before the spacing sum is bounded.
The integral range is enlarged to twice T as in the second display. -/
noncomputable def weightedMoment {q : ℕ} [NeZero q] (T : ℝ)
    (S : Finset (ℝ × DirichletCharacter ℂ q)) : ℝ :=
  ∑ p ∈ S, ∫ u in (-2 * T)..(2 * T),
    ‖p.2.LFunction (Thm4.half u)‖ ^ 4 / (1 + |p.1 - u|)

/-- LEAF. Page 22, Lemma 7, first display. Ramachandra reference 26
supplies the fourth moment for all characters. CITED and OPEN. -/
theorem all_character_fourth_moment : MeanValue132.Lemma7 := by
  sorry

/-- LEAF. Page 22, the convexity input behind Rademacher reference 28.
The conductor and height exponent is half of one minus sigma, plus epsilon.
Source: Rademacher, Math. Z. 72, pages 192 to 204. CITED and OPEN. -/
theorem rademacher_convexity :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 →
        (σ : ℂ) + t * Complex.I ≠ 1 →
        ‖χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤
          C * (((q : ℝ) * (|t| + 1)) ^ ((1 - σ) / 2 + ε) +
            1 / ‖(σ : ℂ) + t * Complex.I - 1‖) := by
  sorry

/-- Page 22, Lemma 8, second display. The weaker printed exponent follows
from the stronger cited convexity input. CONDITIONAL on rademacher_convexity. -/
theorem rademacher_strip_bound : MeanValue132.Lemma8 := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := rademacher_convexity ε hε
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ σ t hσ0 hσ1 hne
  have hbase : 1 ≤ (q : ℝ) * (|t| + 1) := by
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [abs_nonneg t]
  refine (hbound q hq χ σ t hσ0 hσ1 hne).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact add_le_add (Real.rpow_le_rpow_of_exponent_le hbase (by linarith)) le_rfl

namespace Contour230

open MeasureTheory Filter Asymptotics Set Real
open scoped Topology

/-- Pages 22 and 23, the subtracted Perron kernel with its removable value. -/
noncomputable def kernel (a b : ℝ) : ℂ → ℂ :=
  dslope (fun z : ℂ => Complex.exp (Real.log a * z) - Complex.exp (Real.log b * z)) 0
/-- Pages 22 and 23, the subtracted kernel is entire, including at zero. -/
theorem kernel_entire (a b : ℝ) : Differentiable ℂ (kernel a b) := by
  rw [← differentiableOn_univ]
  apply (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr
  fun_prop

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem kernel_zero (a b : ℝ) : kernel a b 0 = (Real.log a - Real.log b : ℝ) := by
  unfold kernel
  rw [dslope_same]
  have ha := (Complex.hasDerivAt_exp (Real.log a * (0 : ℂ))).comp 0
    ((hasDerivAt_id (0 : ℂ)).const_mul (Real.log a : ℂ))
  have hb := (Complex.hasDerivAt_exp (Real.log b * (0 : ℂ))).comp 0
    ((hasDerivAt_id (0 : ℂ)).const_mul (Real.log b : ℂ))
  convert (ha.sub hb).deriv using 1 <;> first | rfl | simp

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem kernel_eq (a b : ℝ) {z : ℂ} (hz : z ≠ 0) : kernel a b z =
    (Complex.exp (Real.log a * z) - Complex.exp (Real.log b * z)) / z := by
  simp [kernel, dslope_of_ne _ hz, slope_def_field]

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem safe_height {T t : ℝ} (hT : 2 ≤ T) :
    ∃ H : ℝ, (H = T / 2 ∨ H = 3 * T / 4) ∧
      T / 2 ≤ H ∧ H ≤ 3 * T / 4 ∧ 1 / 4 ≤ |t - H| ∧ 1 / 4 ≤ |t + H| := by
  by_cases h : 1 / 4 ≤ |t - T / 2| ∧ 1 / 4 ≤ |t + T / 2|
  · exact ⟨T / 2, Or.inl rfl, le_rfl, by linarith, h⟩
  · refine ⟨3 * T / 4, Or.inr rfl, by linarith, le_rfl, ?_, ?_⟩
    all_goals simp only [not_and_or, not_le] at h
    all_goals rcases h with h | h
    all_goals have hh := abs_lt.mp h
    all_goals apply le_abs.mpr
    all_goals first | left; linarith | right; linarith

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem kernel_integral (a b : ℝ) (z : ℂ) : kernel a b z =
    ∫ v in (Real.log b)..(Real.log a), Complex.exp (z * v) := by
  by_cases hz : z = 0
  · subst z
    rw [kernel_zero]
    simp
  · rw [kernel_eq a b hz, integral_exp_mul_complex hz]
    congr 2 <;> congr 1 <;> ring

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem kernel_log_bound (a b u : ℝ) : ‖kernel a b ((u : ℂ) * I)‖ ≤ |Real.log a - Real.log b| := by
  rw [kernel_integral]
  have hn : ∀ v ∈ Set.uIoc (Real.log b) (Real.log a),
      ‖Complex.exp (((u : ℂ) * I) * v)‖ ≤ 1 := by
    intro v _
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hn

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem kernel_tail_bound (a b : ℝ) {u : ℝ} (hu : u ≠ 0) :
    ‖kernel a b ((u : ℂ) * I)‖ ≤ 2 / |u| := by
  have hz : (u : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) I_ne_zero
  rw [kernel_eq a b hz, norm_div]
  have hn (v : ℝ) : ‖Complex.exp ((v : ℂ) * ((u : ℂ) * I))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have ht := norm_sub_le (Complex.exp (Real.log a * ((u : ℂ) * I)))
    (Complex.exp (Real.log b * ((u : ℂ) * I)))
  rw [hn, hn] at ht
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
    show (1 : ℝ) + 1 = 2 by norm_num] using
    div_le_div_of_nonneg_right ht (norm_nonneg ((u : ℂ) * I))

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem half_cutoff_iff (N : ℝ) (n : ℕ) :
    (n : ℝ) < (⌊N⌋₊ : ℝ) + 1 / 2 ↔ n ≤ ⌊N⌋₊ := by
  constructor
  · intro hn
    by_contra h
    have hh : ⌊N⌋₊ + 1 ≤ n := by omega
    have hr : (⌊N⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hh
    linarith
  · intro hn
    have hr : (n : ℝ) ≤ ⌊N⌋₊ := by exact_mod_cast hn
    linarith

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem half_endpoint_ne (N : ℝ) (n : ℕ) : (⌊N⌋₊ : ℝ) + 1 / 2 ≠ n := by
  intro h
  by_cases hn : n ≤ ⌊N⌋₊
  · have hr : (n : ℝ) ≤ ⌊N⌋₊ := by exact_mod_cast hn
    linarith
  · have hh : ⌊N⌋₊ + 1 ≤ n := by omega
    have hr : (⌊N⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hh
    linarith

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem half_endpoint_gap (N : ℝ) (n : ℕ) : 1 / 2 ≤ |(⌊N⌋₊ : ℝ) + 1 / 2 - n| := by
  by_cases hn : n ≤ ⌊N⌋₊
  · have hr : (n : ℝ) ≤ ⌊N⌋₊ := by exact_mod_cast hn
    exact le_abs.mpr (Or.inl (by linarith))
  · have hh : ⌊N⌋₊ + 1 ≤ n := by omega
    have hr : (⌊N⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hh
    exact le_abs.mpr (Or.inr (by linarith))

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem kernel_strip_bound (a b : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖kernel a b z‖ ≤
      (Real.exp (Real.log a * z.re) + Real.exp (Real.log b * z.re)) / ‖z‖ := by
  rw [kernel_eq a b hz, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg z)
  simpa [Complex.norm_exp, Complex.mul_re] using
    norm_sub_le (Complex.exp (Real.log a * z)) (Complex.exp (Real.log b * z))

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem kernel_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℂ} (hz : z ≠ 0) :
    kernel a b z = ((a : ℂ) ^ z - (b : ℂ) ^ z) / z := by
  rw [kernel_eq a b hz, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne'),
    ← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le]

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem kernel_half_log_bound {a : ℝ} (ha : 1 ≤ a) (u : ℝ) :
    ‖kernel a (1 / 2) ((u : ℂ) * I)‖ ≤ Real.log (2 * a) := by
  have ha0 : 0 < a := by linarith
  have he : Real.log a - Real.log (1 / 2) = Real.log (2 * a) := by
    rw [Real.log_mul (by norm_num) ha0.ne']
    norm_num [Real.log_div]
    ring
  have hlog : 0 ≤ Real.log (2 * a) := Real.log_nonneg (by linarith)
  simpa only [he, abs_of_nonneg hlog] using kernel_log_bound a (1 / 2) u

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem half_endpoint_bounds (N : ℝ) (hN : 2 ≤ N) :
    2 ≤ (⌊N⌋₊ : ℝ) + 1 / 2 ∧
      (⌊N⌋₊ : ℝ) + 1 / 2 ≤ N + 1 / 2 ∧
      N - 1 / 2 < (⌊N⌋₊ : ℝ) + 1 / 2 := by
  have hf : (2 : ℕ) ≤ ⌊N⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ N)).mpr (by exact_mod_cast hN)
  have hf' : (2 : ℝ) ≤ ⌊N⌋₊ := by exact_mod_cast hf
  have hlow := Nat.floor_le (by linarith : 0 ≤ N)
  have hhigh := Nat.lt_floor_add_one N
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem half_endpoint_log_le {x N : ℝ} (hx : 2 ≤ x) (hN : 2 ≤ N) (hNx : N ≤ x) :
    Real.log (2 * ((⌊N⌋₊ : ℝ) + 1 / 2)) ≤ 3 * Real.log x := by
  have ha := half_endpoint_bounds N hN
  have hax : 2 * ((⌊N⌋₊ : ℝ) + 1 / 2) ≤ 4 * x := by linarith
  have hlog := Real.log_le_log (by positivity : 0 < 2 * ((⌊N⌋₊ : ℝ) + 1 / 2)) hax
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by linarith : x ≠ 0)] at hlog
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

/-- Pages 22 and 23, auxiliary regular contour for display 3.36. -/
theorem safe_height_window {T t : ℝ} (hT : 2 ≤ T) (ht : |t| ≤ T) :
    ∃ H : ℝ, (H = T / 2 ∨ H = 3 * T / 4) ∧
      1 ≤ H ∧ H ≤ T ∧ 1 / 4 ≤ |t - H| ∧ 1 / 4 ≤ |t + H| ∧
      ∀ u ∈ Set.Icc (-H) H, |t + u| ≤ 2 * T := by
  obtain ⟨H, hchoice, hlow, hhigh, hminus, hplus⟩ := safe_height (t := t) hT
  refine ⟨H, hchoice, by linarith, by linarith, hminus, hplus, ?_⟩
  intro u hu
  have hu' : |u| ≤ H := abs_le.mpr hu
  exact (abs_add_le t u).trans (by linarith)

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem fourth_holder {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hf : MemLp f 4 μ) (hg : MemLp g (ENNReal.ofReal (4 / 3 : ℝ)) μ) :
    (∫ u, f u * g u ∂μ) ^ 4 ≤
      (∫ u, f u ^ 4 ∂μ) * (∫ u, g u ^ (4 / 3 : ℝ) ∂μ) ^ 3 := by
  have hc : (4 : ℝ).HolderConjugate (4 / 3) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hc hf0 hg0 (by simpa using hf) hg
  have hfg0 : 0 ≤ ∫ u, f u * g u ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [hf0, hg0] with u hu hv; exact mul_nonneg hu hv)
  have hA : 0 ≤ ∫ u, f u ^ (4 : ℝ) ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [hf0] with u hu; exact Real.rpow_nonneg hu _)
  have hB : 0 ≤ ∫ u, g u ^ (4 / 3 : ℝ) ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [hg0] with u hu; exact Real.rpow_nonneg hu _)
  have hp := pow_le_pow_left₀ hfg0 hh 4
  rw [mul_pow] at hp
  have heA : ((∫ u, f u ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ))) ^ 4 =
      ∫ u, f u ^ (4 : ℝ) ∂μ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    norm_num
  have heB : ((∫ u, g u ^ (4 / 3 : ℝ) ∂μ) ^ (1 / (4 / 3 : ℝ))) ^ 4 =
      (∫ u, g u ^ (4 / 3 : ℝ) ∂μ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
    norm_num
  rw [heA, heB] at hp
  simpa using hp

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem continuous_memLp_interval (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (p : ENNReal) :
    MemLp f p (volume.restrict (Set.Ioc a b)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hf.norm).bddAbove
  apply MemLp.of_bound hf.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact hC ⟨u, ⟨hu.1.le, hu.2⟩, rfl⟩

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem interval_fourth_holder {a b : ℝ} (hab : a ≤ b) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ u, 0 ≤ f u) (hg0 : ∀ u, 0 ≤ g u) :
    (∫ u in a..b, f u * g u) ^ 4 ≤
      (∫ u in a..b, f u ^ 4) * (∫ u in a..b, g u ^ (4 / 3 : ℝ)) ^ 3 := by
  simp only [intervalIntegral.integral_of_le hab]
  exact fourth_holder (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (continuous_memLp_interval f hf a b 4)
    (continuous_memLp_interval g hg a b _)

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem weighted_fourth_holder {a b : ℝ} (hab : a ≤ b) (F K : ℝ → ℂ) (w : ℝ → ℝ)
    (hF : Continuous F) (hK : Continuous K) (hw : Continuous w) (hw0 : ∀ u, 0 < w u) :
    ‖∫ u in a..b, F u * K u‖ ^ 4 ≤
      (∫ u in a..b, ‖F u‖ ^ 4 / w u) *
        (∫ u in a..b, ‖K u‖ ^ (4 / 3 : ℝ) * w u ^ (1 / 3 : ℝ)) ^ 3 := by
  let f : ℝ → ℝ := fun u => ‖F u‖ / w u ^ (1 / 4 : ℝ)
  let g : ℝ → ℝ := fun u => ‖K u‖ * w u ^ (1 / 4 : ℝ)
  have hwp (u : ℝ) : 0 < w u ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (hw0 u) _
  have hfc : Continuous f := hF.norm.div
    (hw.rpow_const (fun u => Or.inl (hw0 u).ne')) (fun u => (hwp u).ne')
  have hgc : Continuous g := hK.norm.mul
    (hw.rpow_const (fun u => Or.inl (hw0 u).ne'))
  have hf0 (u : ℝ) : 0 ≤ f u := div_nonneg (norm_nonneg _) (hwp u).le
  have hg0 (u : ℝ) : 0 ≤ g u := mul_nonneg (norm_nonneg _) (hwp u).le
  have hh := interval_fourth_holder hab f g hfc hgc hf0 hg0
  have hfg (u : ℝ) : f u * g u = ‖F u * K u‖ := by
    dsimp [f, g]
    rw [norm_mul]
    calc
      _ = (‖F u‖ / w u ^ (1 / 4 : ℝ) * w u ^ (1 / 4 : ℝ)) * ‖K u‖ := by ring
      _ = _ := by rw [div_mul_cancel₀ _ (hwp u).ne']
  have hf4 (u : ℝ) : f u ^ 4 = ‖F u‖ ^ 4 / w u := by
    dsimp [f]
    rw [div_pow]
    have hp : (w u ^ (1 / 4 : ℝ)) ^ 4 = w u := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hw0 u).le]
      norm_num
    rw [hp]
  have hgq (u : ℝ) : g u ^ (4 / 3 : ℝ) =
      ‖K u‖ ^ (4 / 3 : ℝ) * w u ^ (1 / 3 : ℝ) := by
    dsimp [g]
    rw [Real.mul_rpow (norm_nonneg _) (hwp u).le, ← Real.rpow_mul (hw0 u).le]
    norm_num
  simp_rw [hfg, hf4, hgq] at hh
  exact (pow_le_pow_left₀ (norm_nonneg _) (intervalIntegral.norm_integral_le_integral_norm hab) 4).trans hh

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem shifted_weight_integral_le (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ u, 0 ≤ f u)
    {T H t : ℝ} (hT : 0 ≤ T) (hH : 0 ≤ H) (hHT : H ≤ T) (ht : |t| ≤ T) :
    (∫ u in (-H)..H, f (t + u) / (1 + |u|)) ≤
      ∫ v in (-2 * T)..(2 * T), f v / (1 + |t - v|) := by
  let g : ℝ → ℝ := fun v => f v / (1 + |t - v|)
  have hgc : Continuous g := hf.div (by fun_prop) (by intro u; positivity)
  have he (u : ℝ) : f (t + u) / (1 + |u|) = g (t + u) := by
    dsimp [g]
    congr 2
    have he : t - (t + u) = -u := by ring
    rw [he, abs_neg]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_add_left]
  apply intervalIntegral.integral_mono_interval
    (show -2 * T ≤ t + -H by linarith [(abs_le.mp ht).1])
    (show t + -H ≤ t + H by linarith)
    (show t + H ≤ 2 * T by linarith [(abs_le.mp ht).2])
    (Filter.Eventually.of_forall (fun v => div_nonneg (hf0 v) (by positivity)))
    (hgc.intervalIntegrable _ _)

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem critical_line_continuous {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (fun u : ℝ => χ.LFunction (Thm4.half u)) := by
  have hh : Continuous (fun u : ℝ => Thm4.half u) := by unfold Thm4.half; fun_prop
  apply continuous_iff_continuousAt.mpr
  intro u
  have hne : Thm4.half u ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num [Thm4.half] at hre
  exact (χ.differentiableAt_LFunction _ (.inl hne)).continuousAt.comp hh.continuousAt

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem smooth_kernel_bound {a : ℝ} (ha : 1 ≤ a) (u : ℝ) :
    ‖kernel a (1 / 2) ((u : ℂ) * I)‖ ≤
      3 * Real.log (2 * a) / (1 + Real.log (2 * a) * |u|) := by
  have hL : 0 ≤ Real.log (2 * a) := Real.log_nonneg (by linarith)
  have hk := kernel_half_log_bound ha u
  have ht : ‖kernel a (1 / 2) ((u : ℂ) * I)‖ * |u| ≤ 2 := by
    by_cases hu : u = 0
    · simp [hu]
    · exact (le_div_iff₀ (abs_pos.mpr hu)).mp (kernel_tail_bound a (1 / 2) hu)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left ht hL]

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem holder_tail_majorant {u k : ℝ} (hu : 1 ≤ u) (hk : 0 ≤ k) (hku : k ≤ 2 / u) :
    k ^ (4 / 3 : ℝ) * (1 + u) ^ (1 / 3 : ℝ) ≤ 4 / u := by
  have hu0 : 0 < u := by linarith
  have hq : 0 ≤ (4 / 3 : ℝ) := by norm_num
  have hc : 0 ≤ (1 / 3 : ℝ) := by norm_num
  have hh : k ^ (4 / 3 : ℝ) * (1 + u) ^ (1 / 3 : ℝ) ≤
      (2 / u) ^ (4 / 3 : ℝ) * (2 * u) ^ (1 / 3 : ℝ) := by
    gcongr
    linarith
  have hp : u ^ (1 / 3 : ℝ) / u ^ (4 / 3 : ℝ) = 1 / u := by
    rw [← Real.rpow_sub hu0]
    norm_num [Real.rpow_neg_one]
  have h2 : (2 : ℝ) ^ (4 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 4 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  calc
    _ ≤ (2 / u) ^ (4 / 3 : ℝ) * (2 * u) ^ (1 / 3 : ℝ) := hh
    _ = ((2 : ℝ) ^ (4 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ)) *
        (u ^ (1 / 3 : ℝ) / u ^ (4 / 3 : ℝ)) := by
      rw [Real.div_rpow (by norm_num) hu0.le, Real.mul_rpow (by norm_num) hu0.le]
      ring
    _ ≤ 4 / u := by rw [hp]; simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hu0.le)

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem near_power_integral {L : ℝ} (hL : 0 < L) :
    (∫ u in (0 : ℝ)..1, (1 + L * u) ^ (-4 / 3 : ℝ)) ≤ 3 / L := by
  have hscale := intervalIntegral.integral_comp_mul_add (fun x : ℝ => x ^ (-4 / 3 : ℝ))
    (a := 0) (b := 1) hL.ne' 1
  simp only [mul_zero, zero_add, mul_one, smul_eq_mul] at hscale
  have hi : (∫ v in (1 : ℝ)..(L + 1), v ^ (-4 / 3 : ℝ)) =
      3 * (1 - (L + 1) ^ (-1 / 3 : ℝ)) := by
    rw [integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
    · norm_num
      ring
    · rw [Set.uIcc_of_le (by linarith)]
      simp only [Set.mem_Icc, not_and_or, not_le]
      exact Or.inl (by norm_num)
  rw [hi] at hscale
  have he : (∫ u in (0 : ℝ)..1, (1 + L * u) ^ (-4 / 3 : ℝ)) =
      L⁻¹ * (3 * (1 - (L + 1) ^ (-1 / 3 : ℝ))) := by
    simpa [mul_comm, mul_left_comm, mul_assoc, add_comm] using hscale
  rw [he]
  have hp : 0 ≤ (L + 1) ^ (-1 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc
    _ ≤ L⁻¹ * 3 := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hL.le)
    _ = 3 / L := by ring

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem holder_near_majorant {L u k : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hk : 0 ≤ k) (hku : k ≤ 3 * L / (1 + L * u)) :
    k ^ (4 / 3 : ℝ) * (1 + u) ^ (1 / 3 : ℝ) ≤
      18 * L ^ (4 / 3 : ℝ) * (1 + L * u) ^ (-4 / 3 : ℝ) := by
  have hL0 : 0 < L := by linarith
  have hd : 0 < 1 + L * u := by positivity
  have hw : (1 + u) ^ (1 / 3 : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  have h3 : (3 : ℝ) ^ (4 / 3 : ℝ) ≤ 9 := by
    calc
      _ ≤ (3 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 9 := by norm_num
  calc
    _ ≤ (3 * L / (1 + L * u)) ^ (4 / 3 : ℝ) * 2 := by gcongr
    _ = 2 * (3 : ℝ) ^ (4 / 3 : ℝ) * L ^ (4 / 3 : ℝ) *
        (1 + L * u) ^ (-4 / 3 : ℝ) := by
      rw [Real.div_rpow (by positivity) hd.le, Real.mul_rpow (by norm_num) hL0.le,
        neg_div, Real.rpow_neg hd.le]
      ring
    _ ≤ 18 * L ^ (4 / 3 : ℝ) * (1 + L * u) ^ (-4 / 3 : ℝ) := by gcongr; linarith

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem kernel_conj (a b : ℝ) (z : ℂ) : kernel a b (star z) = star (kernel a b z) := by
  change kernel a b (starRingEnd ℂ z) = starRingEnd ℂ (kernel a b z)
  by_cases hz : z = 0
  · subst z
    simp [kernel_zero]
  · have hz' : starRingEnd ℂ z ≠ 0 := by
      intro h
      have hh := congrArg (starRingEnd ℂ) h
      exact hz (by simpa using hh)
    rw [kernel_eq a b hz', kernel_eq a b hz]
    simp only [map_div₀, map_sub, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem near_kernel_weight {a : ℝ} (ha : 1 ≤ a) (hL : 1 ≤ Real.log (2 * a)) :
    (∫ u in (0 : ℝ)..1,
      ‖kernel a (1 / 2) ((u : ℂ) * I)‖ ^ (4 / 3 : ℝ) *
        (1 + |u|) ^ (1 / 3 : ℝ)) ≤ 54 * Real.log (2 * a) := by
  let L := Real.log (2 * a)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hkc : Continuous (fun u : ℝ => kernel a (1 / 2) ((u : ℂ) * I)) :=
    (kernel_entire a (1 / 2)).continuous.comp (by fun_prop)
  have hfc : Continuous (fun u : ℝ => ‖kernel a (1 / 2) ((u : ℂ) * I)‖ ^ (4 / 3 : ℝ) *
        (1 + |u|) ^ (1 / 3 : ℝ)) := by
    apply Continuous.mul
    · exact hkc.norm.rpow_const (fun _ => Or.inr (by norm_num))
    · exact (continuous_const.add continuous_id.abs).rpow_const (fun _ => Or.inr (by norm_num))
  have hgc : ContinuousOn (fun u : ℝ => (1 + L * u) ^ (-4 / 3 : ℝ)) (Set.Icc 0 1) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro u hu
    left
    have : 0 < 1 + L * u := by nlinarith [hu.1]
    exact this.ne'
  have hgi := hgc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hb : (∫ u in (0 : ℝ)..1,
      ‖kernel a (1 / 2) ((u : ℂ) * I)‖ ^ (4 / 3 : ℝ) * (1 + |u|) ^ (1 / 3 : ℝ)) ≤
      18 * L ^ (4 / 3 : ℝ) * (∫ u in (0 : ℝ)..1, (1 + L * u) ^ (-4 / 3 : ℝ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num) (hfc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      (hgi.const_mul _)
    intro u hu
    rw [abs_of_nonneg hu.1]
    apply holder_near_majorant hL hu.1 hu.2 (norm_nonneg _)
    simpa [L, abs_of_nonneg hu.1] using smooth_kernel_bound ha u
  have hp : L ^ (4 / 3 : ℝ) / L = L ^ (1 / 3 : ℝ) := by
    calc
      _ = L ^ (4 / 3 : ℝ) / L ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub hL0]; norm_num
  have hroot : L ^ (1 / 3 : ℝ) ≤ L := by
    calc
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = L := Real.rpow_one _
  calc
    _ ≤ 18 * L ^ (4 / 3 : ℝ) * (3 / L) :=
      hb.trans (mul_le_mul_of_nonneg_left (near_power_integral hL0) (by positivity))
    _ = 54 * L ^ (1 / 3 : ℝ) := by calc
      _ = 54 * (L ^ (4 / 3 : ℝ) / L) := by ring
      _ = _ := by rw [hp]
    _ ≤ 54 * L := by gcongr

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem tail_kernel_weight {a H : ℝ} (hH : 1 ≤ H) :
    (∫ u in (1 : ℝ)..H,
      ‖kernel a (1 / 2) ((u : ℂ) * I)‖ ^ (4 / 3 : ℝ) *
        (1 + |u|) ^ (1 / 3 : ℝ)) ≤ 4 * Real.log H := by
  have hkc : Continuous (fun u : ℝ => kernel a (1 / 2) ((u : ℂ) * I)) :=
    (kernel_entire a (1 / 2)).continuous.comp (by fun_prop)
  have hfc : Continuous (fun u : ℝ => ‖kernel a (1 / 2) ((u : ℂ) * I)‖ ^ (4 / 3 : ℝ) *
        (1 + |u|) ^ (1 / 3 : ℝ)) := by
    apply Continuous.mul
    · exact hkc.norm.rpow_const (fun _ => Or.inr (by norm_num))
    · exact (continuous_const.add continuous_id.abs).rpow_const (fun _ => Or.inr (by norm_num))
  have hgc : ContinuousOn (fun u : ℝ => 4 / u) (Set.Icc 1 H) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro u hu
    change u ≠ 0
    linarith [hu.1]
  have hb : (∫ u in (1 : ℝ)..H,
      ‖kernel a (1 / 2) ((u : ℂ) * I)‖ ^ (4 / 3 : ℝ) * (1 + |u|) ^ (1 / 3 : ℝ)) ≤
      ∫ u in (1 : ℝ)..H, 4 / u := by
    apply intervalIntegral.integral_mono_on hH (hfc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      (hgc.intervalIntegrable_of_Icc hH)
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    rw [abs_of_pos hu0]
    apply holder_tail_majorant hu.1 (norm_nonneg _)
    simpa only [abs_of_pos hu0] using kernel_tail_bound a (1 / 2) hu0.ne'
  have he : (∫ u in (1 : ℝ)..H, 4 / u) = 4 * Real.log H := by
    simp_rw [div_eq_mul_one_div (4 : ℝ)]
    rw [intervalIntegral.integral_const_mul,
      integral_one_div_of_pos (by norm_num : (0 : ℝ) < 1) (by linarith)]
    simp
  exact hb.trans_eq he

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem kernel_norm_neg (a b u : ℝ) : ‖kernel a b ((-u : ℝ) * I)‖ = ‖kernel a b ((u : ℂ) * I)‖ := by
  have he : ((-u : ℝ) : ℂ) * I = star ((u : ℂ) * I) := by simp
  rw [he, kernel_conj, norm_star]

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem kernel_weight_mass {a H : ℝ} (ha : 1 ≤ a) (hL : 1 ≤ Real.log (2 * a)) (hH : 1 ≤ H) :
    (∫ u in (-H)..H,
      ‖kernel a (1 / 2) ((u : ℂ) * I)‖ ^ (4 / 3 : ℝ) *
        (1 + |u|) ^ (1 / 3 : ℝ)) ≤ 108 * Real.log (2 * a) + 8 * Real.log H := by
  let f : ℝ → ℝ := fun u => ‖kernel a (1 / 2) ((u : ℂ) * I)‖ ^ (4 / 3 : ℝ) *
    (1 + |u|) ^ (1 / 3 : ℝ)
  have hkc : Continuous (fun u : ℝ => kernel a (1 / 2) ((u : ℂ) * I)) :=
    (kernel_entire a (1 / 2)).continuous.comp (by fun_prop)
  have hfc : Continuous f := by
    apply Continuous.mul
    · exact hkc.norm.rpow_const (fun _ => Or.inr (by norm_num))
    · exact (continuous_const.add continuous_id.abs).rpow_const (fun _ => Or.inr (by norm_num))
  have heven (u : ℝ) : f (-u) = f u := by
    dsimp [f]
    rw [kernel_norm_neg, abs_neg]
  have hneg : (∫ u in (-H)..(0 : ℝ), f u) = ∫ u in (0 : ℝ)..H, f u := by
    have hh := intervalIntegral.integral_comp_neg f (a := 0) (b := H)
    simpa only [heven, neg_zero] using hh.symm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hfc.intervalIntegrable (μ := MeasureTheory.volume) (-H) 0) (hfc.intervalIntegrable (μ := MeasureTheory.volume) 0 H)
  have hsplit' := intervalIntegral.integral_add_adjacent_intervals
    (hfc.intervalIntegrable (μ := MeasureTheory.volume) 0 1) (hfc.intervalIntegrable (μ := MeasureTheory.volume) 1 H)
  have hnear := near_kernel_weight ha hL
  have htail := tail_kernel_weight (a := a) hH
  change (∫ u in (-H)..H, f u) ≤ _
  change (∫ u in (0 : ℝ)..1, f u) ≤ _ at hnear
  change (∫ u in (1 : ℝ)..H, f u) ≤ _ at htail
  linarith

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem kernel_weight_log_bound {x N H : ℝ} (hx : 2 ≤ x) (hN : 2 ≤ N) (hNx : N ≤ x)
    (hH : 1 ≤ H) (hHx : H ≤ x) :
    (∫ u in (-H)..H,
      ‖kernel ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) ((u : ℂ) * I)‖ ^ (4 / 3 : ℝ) *
        (1 + |u|) ^ (1 / 3 : ℝ)) ≤ 332 * Real.log x := by
  have ha := (half_endpoint_bounds N hN).1
  have hL : 1 ≤ Real.log (2 * ((⌊N⌋₊ : ℝ) + 1 / 2)) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (show (4 : ℝ) ≤ 2 * ((⌊N⌋₊ : ℝ) + 1 / 2) by linarith)
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_gt_d9]
  have hb := kernel_weight_mass (a := (⌊N⌋₊ : ℝ) + 1 / 2) (by linarith) hL hH
  have hlogN := half_endpoint_log_le hx hN hNx
  have hlogH := Real.log_le_log (by linarith : 0 < H) hHx
  linarith

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
noncomputable def rawLineIntegral {q : ℕ} [NeZero q] (N H : ℝ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ u in (-H)..H,
    χ.LFunction (Thm4.half (t + u)) * kernel ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) ((u : ℂ) * I)

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem rawLineIntegral_fourth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x N T H t : ℝ}
    (hx : 2 ≤ x) (hN : 2 ≤ N) (hNx : N ≤ x) (hT : 2 ≤ T) (hTx : T ≤ x)
    (hH : 1 ≤ H) (hHT : H ≤ T) (ht : |t| ≤ T) :
    ‖rawLineIntegral N H χ t‖ ^ 4 ≤
      (332 : ℝ) ^ 3 * Real.log x ^ (3 : ℝ) *
        (∫ v in (-2 * T)..(2 * T), ‖χ.LFunction (Thm4.half v)‖ ^ 4 / (1 + |t - v|)) := by
  let F : ℝ → ℂ := fun u => χ.LFunction (Thm4.half (t + u))
  let K : ℝ → ℂ := fun u => kernel ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) ((u : ℂ) * I)
  have hFc : Continuous F := (critical_line_continuous χ).comp (by fun_prop)
  have hKc : Continuous K := (kernel_entire _ _).continuous.comp (by fun_prop)
  have hh := weighted_fourth_holder (show -H ≤ H by linarith) F K (fun u => 1 + |u|)
    hFc hKc (by fun_prop) (fun _ => by positivity)
  have hs := shifted_weight_integral_le (fun v => ‖χ.LFunction (Thm4.half v)‖ ^ 4)
    ((critical_line_continuous χ).norm.pow 4) (fun _ => pow_nonneg (norm_nonneg _) _)
    (by linarith : 0 ≤ T) (by linarith : 0 ≤ H) hHT ht
  have hk := kernel_weight_log_bound hx hN hNx hH (hHT.trans hTx)
  have hcoef : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_le_one (by positivity)).mpr (by linarith [Real.pi_gt_three])
  have hnorm : ‖rawLineIntegral N H χ t‖ ≤ ‖∫ u in (-H)..H, F u * K u‖ := by
    unfold rawLineIntegral
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hcoef
  have hm0 : 0 ≤ ∫ u in (-H)..H, ‖K u‖ ^ (4 / 3 : ℝ) * (1 + |u|) ^ (1 / 3 : ℝ) :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  have hg0 : 0 ≤ ∫ v in (-2 * T)..(2 * T),
      ‖χ.LFunction (Thm4.half v)‖ ^ 4 / (1 + |t - v|) :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  calc
    _ ≤ ‖∫ u in (-H)..H, F u * K u‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hnorm 4
    _ ≤ _ := hh
    _ ≤ (∫ v in (-2 * T)..(2 * T), ‖χ.LFunction (Thm4.half v)‖ ^ 4 / (1 + |t - v|)) *
        (332 * Real.log x) ^ 3 := by
      apply mul_le_mul hs (pow_le_pow_left₀ hm0 hk 3) (pow_nonneg hm0 3) hg0
    _ = _ := by norm_num only [Real.rpow_ofNat, mul_pow]; ring

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
noncomputable def height (T t : ℝ) : ℝ :=
  if hT : 2 ≤ T then (safe_height (t := t) hT).choose else T / 2

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem height_spec {T t : ℝ} (hT : 2 ≤ T) :
    (height T t = T / 2 ∨ height T t = 3 * T / 4) ∧
      1 ≤ height T t ∧ height T t ≤ T ∧
      1 / 4 ≤ |t - height T t| ∧ 1 / 4 ≤ |t + height T t| := by
  simp only [height, dif_pos hT]
  obtain ⟨hc, hl, hu, hm, hp⟩ := (safe_height (t := t) hT).choose_spec
  exact ⟨hc, by linarith, by linarith, hm, hp⟩

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
noncomputable def lineIntegral {q : ℕ} [NeZero q] (N T : ℝ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ := rawLineIntegral N (height T t) χ t

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem lineIntegral_fourth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x N T t : ℝ}
    (hx : 2 ≤ x) (hN : 2 ≤ N) (hNx : N ≤ x) (hT : 2 ≤ T) (hTx : T ≤ x)
    (ht : |t| ≤ T) :
    ‖lineIntegral N T χ t‖ ^ 4 ≤
      (332 : ℝ) ^ 3 * Real.log x ^ (3 : ℝ) *
        (∫ v in (-2 * T)..(2 * T), ‖χ.LFunction (Thm4.half v)‖ ^ 4 / (1 + |t - v|)) := by
  exact rawLineIntegral_fourth χ hx hN hNx hT hTx (height_spec hT).2.1
    (height_spec hT).2.2.1 ht

/-- Pages 22 and 23, auxiliary regular contour and weighted Holder step. -/
theorem lineIntegral_sum {q : ℕ} [NeZero q] (S : Finset (ℝ × DirichletCharacter ℂ q)) {x N T : ℝ}
    (hx : 2 ≤ x) (hN : 2 ≤ N) (hNx : N ≤ x) (hT : 2 ≤ T) (hTx : T ≤ x)
    (ht : ∀ p ∈ S, |p.1| ≤ T) :
    (∑ p ∈ S, ‖lineIntegral N T p.2 p.1‖ ^ 4) ≤
      (332 : ℝ) ^ 3 * Real.log x ^ (3 : ℝ) *
        LeanLab.BHP1997.DecompC165a.weightedMoment T S := by
  have hh := Finset.sum_le_sum (s := S) (fun p hp =>
    lineIntegral_fourth p.2 hx hN hNx hT hTx (ht p hp))
  simpa only [← Finset.mul_sum, LeanLab.BHP1997.DecompC165a.weightedMoment] using hh

/- Adapted from Prove2Me Zeta23.Analytic.residueTheorem_finset,
accepted submission bc862ddb-25d3-4932-b1a0-c42e3c46234d by Community Bot,
accepted 2026-09-03. Source https://beta.prove2.me . Apache 2.0.
The lab PNTPort rectangle API supplies the existing Apache 2.0 prerequisites
from PrimeNumberTheoremAnd. Changes: namespace and prerequisite names,
plus current Mathlib set-difference names. AI adapted the Lean code. -/
/-- Pages 22 and 23, finite simple principal parts on a rectangle. -/
theorem residueTheorem_finset {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (S : Finset ℂ) (A : ℂ → ℂ)
    (hS : ∀ p ∈ S, Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ (S : Set ℂ)))
    (near : ∀ p ∈ S, (f - fun s => A p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = ∑ p ∈ S, A p := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty =>
    simp only [Finset.coe_empty, Set.sdiff_empty] at fHolo
    rw [Finset.sum_empty]
    show (1 / (2 * π * I)) • RectangleIntegral f z w = 0
    rw [fHolo.vanishesOnRectangle subset_rfl, smul_zero]
  | @insert p S hpS ih =>
    have hp : Rectangle z w ∈ 𝓝 p := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, Rectangle z w ∈ 𝓝 q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    -- the principal part at p, the remainder f₁, and its extension f₂ across p
    set P : ℂ → ℂ := fun s => A p / (s - p) with hP
    set f₁ : ℂ → ℂ := f - P with hf₁
    set f₂ : ℂ → ℂ := Function.update f₁ p (limUnder (𝓝[≠] p) f₁) with hf₂
    have hPdiff : ∀ s, s ≠ p → DifferentiableAt ℂ P s := by
      intro s hs
      have : s - p ≠ 0 := sub_ne_zero.mpr hs
      simp only [hP]
      fun_prop (disch := assumption)
    have hf₁holo : HolomorphicOn f₁ (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) := by
      refine fHolo.sub ?_
      intro s hs
      apply (hPdiff s ?_).differentiableWithinAt
      intro h
      apply hs.2
      simp [h]
    have hSclosed : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
    have hRS : Rectangle z w \ (S : Set ℂ) ∈ 𝓝 p := by
      apply Filter.inter_mem hp
      exact hSclosed.isOpen_compl.mem_nhds (by simpa using hpS)
    obtain ⟨U, hU, hbdd⟩ := IsBigO_to_BddAbove (near p (Finset.mem_insert_self p S))
    have hV : U ∩ (Rectangle z w \ (S : Set ℂ)) ∈ 𝓝 p := Filter.inter_mem hU hRS
    have hf₁V : DifferentiableOn ℂ f₁ ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p}) := by
      apply hf₁holo.mono
      rintro s ⟨⟨_, hsR, hsS⟩, hsp⟩
      refine ⟨hsR, ?_⟩
      simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
      exact ⟨by simpa using hsp, by simpa using hsS⟩
    have hbddV : BddAbove (norm ∘ f₁ '' ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p})) :=
      hbdd.mono (image_mono (Set.sdiff_subset_sdiff_left inter_subset_left))
    have hf₂V : DifferentiableOn ℂ f₂ (U ∩ (Rectangle z w \ (S : Set ℂ))) :=
      differentiableOn_update_limUnder_of_bddAbove hV hf₁V hbddV
    have hf₂eq : ∀ s, s ≠ p → f₂ s = f₁ s := fun s hs => Function.update_of_ne hs _ _
    -- f₂ is holomorphic on the rectangle minus the remaining poles
    have hf₂holo : HolomorphicOn f₂ (Rectangle z w \ (S : Set ℂ)) := by
      intro s hs
      by_cases hsp : s = p
      · rw [hsp]
        exact (hf₂V.differentiableAt hV).differentiableWithinAt
      · have h1 : DifferentiableWithinAt ℂ f₁
            (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) s :=
          hf₁holo s ⟨hs.1, by
            simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
            exact ⟨hsp, by simpa using hs.2⟩⟩
        have hset : (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ))
            = (Rectangle z w \ (S : Set ℂ)) ∩ {p}ᶜ := by
          ext x
          simp only [Finset.coe_insert, Set.mem_sdiff, mem_insert_iff, Finset.mem_coe, not_or,
            mem_inter_iff, mem_compl_iff, mem_singleton_iff]
          tauto
        rw [hset] at h1
        have hpc : {p}ᶜ ∈ 𝓝[Rectangle z w \ (S : Set ℂ)] s :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hsp)
        rw [differentiableWithinAt_inter' hpc] at h1
        refine h1.congr_of_eventuallyEq ?_ (hf₂eq s hsp)
        filter_upwards [hpc] with x hx
        exact hf₂eq x hx
    -- the principal parts at the other poles are unchanged
    have near₂ : ∀ q ∈ S, (f₂ - fun s => A q / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
      intro q hq
      have hqp : q ≠ p := fun h => hpS (h ▸ hq)
      have hev : ((f - fun s => A q / (s - q)) - P)
          =ᶠ[𝓝[≠] q] (f₂ - fun s => A q / (s - q)) := by
        have : {p}ᶜ ∈ 𝓝[≠] q :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hqp)
        filter_upwards [this] with s hs
        simp only [Pi.sub_apply, hf₂eq s hs, hf₁]
        ring
      have hPO : P =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
        have hc : ContinuousAt P q := (hPdiff q hqp).continuousAt
        exact (hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
      exact ((near q (Finset.mem_insert_of_mem hq)).sub hPO).congr' hev EventuallyEq.rfl
    have ih' := ih hS' hf₂holo near₂
    -- on the border, f = f₂ + P
    have hborder : EqOn f (f₂ + P) (RectangleBorder z w) := by
      intro s hs
      have hsp : s ≠ p := fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds hp (h ▸ hs)
      simp only [Pi.add_apply, hf₂eq s hsp, hf₁, Pi.sub_apply, sub_add_cancel]
    have hbS : ∀ s ∈ RectangleBorder z w, s ∈ Rectangle z w \ (S : Set ℂ) := fun s hs =>
      ⟨rectangleBorder_subset_rectangle z w hs,
        fun hsS => not_mem_rectangleBorder_of_rectangle_mem_nhds (hS' s hsS) hs⟩
    have hi₂ : RectangleBorderIntegrable f₂ z w :=
      ContinuousOn.rectangleBorder_integrable (hf₂holo.continuousOn.mono hbS)
    have hiP : RectangleBorderIntegrable P z w := by
      apply ContinuousOn.rectangleBorder_integrable
      intro s hs
      have hsp : s ≠ p := fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds hp (h ▸ hs)
      exact (hPdiff s hsp).continuousAt.continuousWithinAt
    rw [RectangleIntegral'_congr hborder, Finset.sum_insert hpS]
    show (1 / (2 * π * I)) • RectangleIntegral (f₂ + P) z w = _
    rw [RectangleBorderIntegrable.add hi₂ hiP, smul_add]
    show RectangleIntegral' f₂ z w + RectangleIntegral' P z w = _
    rw [ih', ResidueTheoremInRectangle hre him hp, add_comm]

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem simple_pole_regular_part (G : ℂ → ℂ) (hG : Differentiable ℂ G) (p : ℂ) :
    (fun w => G w / (w - p) - G p / (w - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hd : Differentiable ℂ (dslope G p) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr hG.differentiableOn
  have hb : dslope G p =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (hd.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  apply hb.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hwp : w ≠ p := hw
  rw [dslope_of_ne _ hwp, slope_def_field]
  ring

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem quotient_rectangle (G : ℂ → ℂ) (hG : Differentiable ℂ G) (p : ℂ)
    {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => G s / (s - p)) z w = G p := by
  have hHolo : HolomorphicOn (fun s => G s / (s - p))
      (Rectangle z w \ ({p} : Finset ℂ)) := by
    intro s hs
    have hsp : s ≠ p := by simpa using hs.2
    have hd : DifferentiableAt ℂ (fun z : ℂ => z - p) s := by fun_prop
    exact ((hG s).div hd (sub_ne_zero.mpr hsp)).differentiableWithinAt
  have hS : ∀ r ∈ ({p} : Finset ℂ), Rectangle z w ∈ 𝓝 r := by
    intro r hr
    simpa only [Finset.mem_singleton.mp hr] using hp
  have hnear : ∀ r ∈ ({p} : Finset ℂ),
      ((fun s => G s / (s - p)) - fun s => G p / (s - r)) =O[𝓝[≠] r] (1 : ℂ → ℂ) := by
    intro r hr
    have hrp := Finset.mem_singleton.mp hr
    subst r
    exact simple_pole_regular_part G hG p
  have hh := residueTheorem_finset hre him ({p} : Finset ℂ) (fun _ => G p) hS hHolo hnear
  simpa using hh

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem principal_regularized_entire {q : ℕ} [NeZero q] (a b t : ℝ) :
    Differentiable ℂ (fun w : ℂ =>
      DirichletCharacter.LFunctionTrivChar₁ q (Thm4.half t + w) *
        kernel a b w) := by
  apply Differentiable.mul
  · exact (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).comp
      (by fun_prop)
  · exact kernel_entire a b

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem principal_regularization {q : ℕ} [NeZero q] (a b t : ℝ) {w : ℂ} (hw : w ≠ 1 - Thm4.half t) :
    (1 : DirichletCharacter ℂ q).LFunction (Thm4.half t + w) *
        kernel a b w =
      (DirichletCharacter.LFunctionTrivChar₁ q (Thm4.half t + w) *
        kernel a b w) / (w - (1 - Thm4.half t)) := by
  have hs : Thm4.half t + w ≠ 1 := by
    intro hs
    apply hw
    linear_combination hs
  rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs]
  change _ = ((Thm4.half t + w - 1) *
    (1 : DirichletCharacter ℂ q).LFunction (Thm4.half t + w) * _) / _
  have he : Thm4.half t + w - 1 = w - (1 - Thm4.half t) := by ring
  rw [he]
  field_simp

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem principal_residue_factor_le (q : ℕ) : ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)‖ ≤ 1 := by
  calc
    _ ≤ ∏ p ∈ q.primeFactors, ‖(1 - (p : ℂ)⁻¹)‖ := Finset.norm_prod_le _ _
    _ ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p hp
        exact norm_nonneg _
      · intro p hp
        have hp1 : (1 : ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
        have hreal : (1 - (p : ℂ)⁻¹) = ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
        rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        · have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
          linarith
        · exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp1)

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
noncomputable def integrand {q : ℕ} [NeZero q] (a b : ℝ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (w : ℂ) : ℂ :=
  χ.LFunction (Thm4.half t + w) * kernel a b w

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem nonprincipal_integrand_entire {q : ℕ} [NeZero q] (a b t : ℝ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Differentiable ℂ (integrand a b χ t) := by
  exact ((DirichletCharacter.differentiable_LFunction hχ).comp (by fun_prop)).mul
    (kernel_entire a b)

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem nonprincipal_rectangle {q : ℕ} [NeZero q] (a b t c H : ℝ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    (∫ σ in (0 : ℝ)..c, integrand a b χ t ((σ : ℂ) - H * I)) -
      (∫ σ in (0 : ℝ)..c, integrand a b χ t ((σ : ℂ) + H * I)) +
      I * (∫ u in (-H)..H, integrand a b χ t ((c : ℂ) + u * I)) -
      I * (∫ u in (-H)..H, integrand a b χ t ((u : ℂ) * I)) = 0 := by
  have hd : Differentiable ℂ (integrand a b χ t) :=
    ((DirichletCharacter.differentiable_LFunction hχ).comp (by fun_prop)).mul
      (kernel_entire a b)
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand a b χ t) (-((H : ℂ) * I)) ((c : ℂ) + H * I) hd.differentiableOn
  simpa [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, smul_eq_mul, sub_eq_add_neg] using hh

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem residue_kernel_bound {a : ℝ} (ha : 1 ≤ a) (t : ℝ) :
    ‖kernel a (1 / 2) (1 - Thm4.half t)‖ ≤
      6 * Real.sqrt a / (1 + |t|) := by
  let p : ℂ := 1 - Thm4.half t
  have hp_re : p.re = (1 / 2 : ℝ) := by simp [p, Thm4.half]; norm_num
  have hp_im : p.im = -t := by simp [p, Thm4.half]
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp_re; norm_num at hp_re
  have hnr : (1 / 2 : ℝ) ≤ ‖p‖ := by
    have h := Complex.abs_re_le_norm p
    rw [hp_re] at h
    norm_num at h ⊢
    exact h
  have hni : |t| ≤ ‖p‖ := by simpa only [hp_im, abs_neg] using Complex.abs_im_le_norm p
  have hden : 1 + |t| ≤ 3 * ‖p‖ := by linarith
  have ha0 : 0 < a := by linarith
  have hsqrt : Real.sqrt (1 / 2 : ℝ) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
  have hnum : ‖(a : ℂ) ^ p - ((1 / 2 : ℝ) : ℂ) ^ p‖ ≤ 2 * Real.sqrt a := by
    calc
      _ ≤ ‖(a : ℂ) ^ p‖ + ‖((1 / 2 : ℝ) : ℂ) ^ p‖ := norm_sub_le _ _
      _ = Real.sqrt a + Real.sqrt (1 / 2 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ha0,
          Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hp_re,
          ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      _ ≤ _ := by linarith
  change ‖kernel a (1 / 2) p‖ ≤ _
  rw [kernel_cpow ha0 (by norm_num) hp0, norm_div]
  have hnorm : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  apply (div_le_div_iff₀ hnorm (by positivity : 0 < 1 + |t|)).mpr
  have hx := mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ 1 + |t|)
  have hy := mul_le_mul_of_nonneg_left hden (show 0 ≤ 2 * Real.sqrt a by positivity)
  nlinarith

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem principal_integrand_near {q : ℕ} [NeZero q] (a b t : ℝ) :
    (fun w : ℂ => integrand a b (1 : DirichletCharacter ℂ q) t w -
      (∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)) *
        kernel a b (1 - Thm4.half t) /
          (w - (1 - Thm4.half t))) =O[𝓝[≠] (1 - Thm4.half t)] (1 : ℂ → ℂ) := by
  let G : ℂ → ℂ := fun w => DirichletCharacter.LFunctionTrivChar₁ q (Thm4.half t + w) *
    kernel a b w
  have hG : Differentiable ℂ G := principal_regularized_entire a b t
  have hh := simple_pole_regular_part G hG (1 - Thm4.half t)
  have he : G (1 - Thm4.half t) = (∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)) *
      kernel a b (1 - Thm4.half t) := by
    dsimp [G]
    rw [add_sub_cancel, DirichletCharacter.LFunctionTrivChar₁, Function.update_self]
  apply hh.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [he]
  have hwp : w ≠ 1 - Thm4.half t := hw
  have hp := principal_regularization a b t hwp (q := q)
  change _ = integrand a b (1 : DirichletCharacter ℂ q) t w - _
  rw [← hp]
  rfl

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem perron_difference_bound {N c H : ℝ} {n : ℕ} (hn : 0 < n) (hc : 0 < c) (hH : 0 < H)
 :
    ‖(LeanLab.DERZ1997.Decomp1529b.perronI (((⌊N⌋₊ : ℝ) + 1 / 2) / n) c H -
        LeanLab.DERZ1997.Decomp1529b.perronI ((1 / 2 : ℝ) / n) c H) - (if n ≤ ⌊N⌋₊ then 1 else 0)‖ ≤
      (((⌊N⌋₊ : ℝ) + 1 / 2) / n) ^ c /
          (Real.pi * H * |Real.log (((⌊N⌋₊ : ℝ) + 1 / 2) / n)|) +
        ((1 / 2 : ℝ) / n) ^ c / (Real.pi * H * |Real.log ((1 / 2 : ℝ) / n)|) := by
  have hne := half_endpoint_ne N n
  have hcut := half_cutoff_iff N n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < (⌊N⌋₊ : ℝ) + 1 / 2 := by positivity
  have hu1 : ((⌊N⌋₊ : ℝ) + 1 / 2) / n ≠ 1 := by
    intro h
    apply hne
    exact (div_eq_one_iff_eq hn0.ne').mp h
  have hl1 : (1 / 2 : ℝ) / n ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq hn0.ne']
    linarith
  have hu := LeanLab.DERZ1997.Perron136.perron_remainder_bound
    (div_pos ha hn0) hu1 hc hH
  have hl := LeanLab.DERZ1997.Perron136.perron_remainder_bound
    (div_pos (by norm_num : (0 : ℝ) < 1 / 2) hn0) hl1 hc hH
  have hbranch : 1 < ((⌊N⌋₊ : ℝ) + 1 / 2) / n ↔ n ≤ ⌊N⌋₊ := by
    rw [lt_div_iff₀ hn0, one_mul]
    exact hcut
  have hlow : ¬1 < (1 / 2 : ℝ) / n := by
    rw [lt_div_iff₀ hn0, one_mul]
    linarith
  simp only [hbranch, hlow, ite_false, sub_zero] at hu hl
  have ht := norm_sub_le
    (LeanLab.DERZ1997.Decomp1529b.perronI (((⌊N⌋₊ : ℝ) + 1 / 2) / n) c H - (if n ≤ ⌊N⌋₊ then 1 else 0))
    (LeanLab.DERZ1997.Decomp1529b.perronI ((1 / 2 : ℝ) / n) c H)
  have he : (LeanLab.DERZ1997.Decomp1529b.perronI (((⌊N⌋₊ : ℝ) + 1 / 2) / n) c H -
        LeanLab.DERZ1997.Decomp1529b.perronI ((1 / 2 : ℝ) / n) c H) - (if n ≤ ⌊N⌋₊ then 1 else 0) =
      (LeanLab.DERZ1997.Decomp1529b.perronI (((⌊N⌋₊ : ℝ) + 1 / 2) / n) c H -
        (if n ≤ ⌊N⌋₊ then 1 else 0)) - LeanLab.DERZ1997.Decomp1529b.perronI ((1 / 2 : ℝ) / n) c H := by ring
  rw [he]
  exact ht.trans (add_le_add hu hl)

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem epsilon_loss_unbounded {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → y ^ (1 / 2 + ε) ≤ C * y ^ (1 / 2 : ℝ) := by
  rintro ⟨C, hC⟩
  let B := max (C + 1) 2
  have hB : 1 ≤ B := by dsimp [B]; linarith [le_max_right (C + 1) (2 : ℝ)]
  have hB0 : 0 < B := by linarith
  let y := B ^ (1 / ε)
  have hy : 1 ≤ y := Real.one_le_rpow hB (by positivity)
  have hy0 : 0 < y := by linarith
  have hp : y ^ ε = B := by
    dsimp [y]
    rw [← Real.rpow_mul hB0.le, one_div_mul_cancel hε.ne', Real.rpow_one]
  have hh := hC y hy
  rw [Real.rpow_add hy0, hp] at hh
  have hroot : 0 < y ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hy0 _
  have hbC : B ≤ C := (mul_le_mul_iff_right₀ hroot).mp (by simpa only [mul_comm] using hh)
  have := le_max_left (C + 1) (2 : ℝ)
  change C + 1 ≤ B at this
  linarith

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem ordered_log_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) / a ≤ Real.log (a / b) := by
  calc
    (a - b) / a = 1 - (a / b)⁻¹ := by field_simp
    _ ≤ _ := Real.one_sub_inv_le_log_of_pos (div_pos ha hb)

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem abs_log_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a - b| / max a b ≤ |Real.log (a / b)| := by
  rcases le_total b a with hba | hab
  · rw [max_eq_left hba, abs_of_nonneg (sub_nonneg.mpr hba),
      abs_of_nonneg (Real.log_nonneg ((one_le_div hb).mpr hba))]
    exact ordered_log_lower ha hb
  · rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.mpr hab),
      abs_of_nonpos (Real.log_nonpos (div_nonneg ha.le hb.le) ((div_le_one hb).mpr hab))]
    have hh := ordered_log_lower hb ha
    rw [Real.log_div hb.ne' ha.ne', Real.log_div ha.ne' hb.ne'] at *
    convert hh using 1 <;> ring

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem inverse_log_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    1 / |Real.log (a / b)| ≤ max a b / |a - b| := by
  have hgap : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hlog : 0 < |Real.log (a / b)| := abs_pos.mpr
    (Real.log_ne_zero_of_pos_of_ne_one (div_pos ha hb) (by
      intro h
      exact hab ((div_eq_one_iff_eq hb.ne').mp h)))
  have hmax : 0 < max a b := lt_of_lt_of_le ha (le_max_left _ _)
  have hh := (div_le_iff₀ hmax).mp (abs_log_lower ha hb)
  apply (div_le_div_iff₀ hlog hgap).mpr
  simpa only [one_mul, mul_one, mul_comm] using hh

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem perron_pseries_bound {δ : ℝ} (hδ : 0 < δ) :
    (∑' n : ℕ, (n : ℝ) ^ (-1 - δ)) ≤ 1 + 1 / δ := by
  let f : ℝ → ℝ := fun u => u ^ (-1 - δ)
  have ha : AntitoneOn f (Set.Ici (1 : ℝ)) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (by exact lt_of_lt_of_le zero_lt_one ha) hab (by linarith)
  have hi : IntegrableOn f (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hn (u : ℝ) (hu : u ∈ Set.Ioi (1 : ℝ)) : 0 ≤ f u := Real.rpow_nonneg (by exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hu.le) _
  have ht := AntitoneOn.tsum_comp_add_le_integral (f := f) 1 (by simpa using ha) (by simpa using hi) (by simpa using hn)
  have he : (∫ u in Set.Ioi (1 : ℝ), f u) = 1 / δ := by
    dsimp [f]
    rw [integral_Ioi_rpow_of_lt (by linarith : -1 - δ < -1) (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.one_rpow]
    ring
  simp only [Nat.cast_one] at ht
  rw [he] at ht
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - δ)) := Real.summable_nat_rpow.mpr (by linarith)
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hz : (-1 - δ : ℝ) ≠ 0 := by linarith
  have hfirst : ∑ n ∈ Finset.range 2, (n : ℝ) ^ (-1 - δ) = 1 := by
    norm_num [Finset.sum_range_succ, Real.zero_rpow hz]
  rw [hfirst] at hsplit
  change (∑' n : ℕ, (n : ℝ) ^ (-1 - δ)) ≤ _
  change (∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-1 - δ)) ≤ _ at ht
  rw [← hsplit]
  simpa only [show ∀ n : ℕ, n + 1 + 1 = n + 2 by omega] using add_le_add (le_refl (1 : ℝ)) ht

/-- Pages 22 and 23, auxiliary principal contour and Perron line estimate. -/
theorem principal_rectangle {q : ℕ} [NeZero q] (a b t : ℝ) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 (1 - Thm4.half t)) :
    RectangleIntegral' (integrand a b (1 : DirichletCharacter ℂ q) t) z w =
      (∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)) * kernel a b (1 - Thm4.half t) := by
  let G : ℂ → ℂ := fun s => DirichletCharacter.LFunctionTrivChar₁ q (Thm4.half t + s) * kernel a b s
  have hG : Differentiable ℂ G := principal_regularized_entire a b t
  have hh := quotient_rectangle G hG (1 - Thm4.half t) hre him hp
  have heq : EqOn (integrand a b (1 : DirichletCharacter ℂ q) t)
      (fun s => G s / (s - (1 - Thm4.half t))) (RectangleBorder z w) := by
    intro s hs
    have hsp : s ≠ 1 - Thm4.half t := by
      intro h
      exact not_mem_rectangleBorder_of_rectangle_mem_nhds hp (h ▸ hs)
    exact principal_regularization a b t hsp
  rw [RectangleIntegral'_congr heq, hh]
  dsimp [G]
  rw [show Thm4.half t + (1 - Thm4.half t) = 1 by ring,
    DirichletCharacter.LFunctionTrivChar₁, Function.update_self]

/-- Pages 22 and 23, auxiliary principal contour and Perron line estimate. -/
theorem principal_rectangle_outside {q : ℕ} [NeZero q] (a b t : ℝ) {z w : ℂ}
    (hp : 1 - Thm4.half t ∉ Rectangle z w) :
    RectangleIntegral' (integrand a b (1 : DirichletCharacter ℂ q) t) z w = 0 := by
  let G : ℂ → ℂ := fun s => DirichletCharacter.LFunctionTrivChar₁ q (Thm4.half t + s) * kernel a b s
  have hG : Differentiable ℂ G := principal_regularized_entire a b t
  have hh : HolomorphicOn (fun s => G s / (s - (1 - Thm4.half t))) (Rectangle z w) := by
    intro s hs
    have hsp : s ≠ 1 - Thm4.half t := by intro h; exact hp (h ▸ hs)
    have hd : DifferentiableAt ℂ (fun v : ℂ => v - (1 - Thm4.half t)) s := by fun_prop
    exact ((hG s).div hd (sub_ne_zero.mpr hsp)).differentiableWithinAt
  have heq : EqOn (integrand a b (1 : DirichletCharacter ℂ q) t)
      (fun s => G s / (s - (1 - Thm4.half t))) (RectangleBorder z w) := by
    intro s hs
    have hsp : s ≠ 1 - Thm4.half t := by
      intro h
      exact hp (h ▸ rectangleBorder_subset_rectangle z w hs)
    exact principal_regularization a b t hsp
  rw [RectangleIntegral'_congr heq, RectangleIntegral', hh.vanishesOnRectangle subset_rfl, smul_zero]

/-- Pages 22 and 23, auxiliary principal contour and Perron line estimate. -/
theorem principal_residue_bound (q : ℕ) {a : ℝ} (ha : 1 ≤ a) (t : ℝ) :
    ‖(∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)) * kernel a (1 / 2) (1 - Thm4.half t)‖ ≤
      6 * Real.sqrt a / (1 + |t|) := by
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖kernel a (1 / 2) (1 - Thm4.half t)‖ :=
      mul_le_mul_of_nonneg_right (principal_residue_factor_le q) (norm_nonneg _)
    _ ≤ _ := by simpa using residue_kernel_bound ha t

/-- Pages 22 and 23, auxiliary principal contour and Perron line estimate. -/
theorem half_endpoint_residue_bound (q : ℕ) {N : ℝ} (hN : 2 ≤ N) (t : ℝ) :
    ‖(∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)) *
      kernel ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) (1 - Thm4.half t)‖ ≤
        12 * Real.sqrt N / (1 + |t|) := by
  have ha := half_endpoint_bounds N hN
  have hroot : Real.sqrt ((⌊N⌋₊ : ℝ) + 1 / 2) ≤ 2 * Real.sqrt N := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt (show 0 ≤ N by linarith)]
  calc
    _ ≤ 6 * Real.sqrt ((⌊N⌋₊ : ℝ) + 1 / 2) / (1 + |t|) :=
      principal_residue_bound q (by linarith) t
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith

/-- Pages 22 and 23, auxiliary principal contour and Perron line estimate. -/
theorem LFunction_right_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {δ t : ℝ} (hδ : 0 < δ) :
    ‖χ.LFunction (((1 + δ : ℝ) : ℂ) + t * Complex.I)‖ ≤ 1 + 1 / δ := by
  let s : ℂ := ((1 + δ : ℝ) : ℂ) + t * Complex.I
  have hs : 1 < s.re := by simp [s]; linarith
  have hre : s.re = 1 + δ := by simp [s]
  rw [χ.LFunction_eq_LSeries hs]
  have hsum := χ.LSeriesSummable_of_one_lt_re hs
  have hnorm : Summable (fun n => ‖LSeries.term (χ ·) s n‖) := hsum.norm
  have hmaj : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - δ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hterm (n : ℕ) : ‖LSeries.term (χ ·) s n‖ ≤ (n : ℝ) ^ (-1 - δ) := by
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (by linarith : (-1 - δ : ℝ) ≠ 0)]
    · simp only [Nat.ne_of_gt hn, ite_false, hre]
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
      have hp : (n : ℝ) ^ (-1 - δ) = 1 / (n : ℝ) ^ (1 + δ) := by
        rw [show (-1 - δ : ℝ) = -(1 + δ) by ring, Real.rpow_neg hn0.le, one_div]
      rw [hp]
      exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  calc
    _ ≤ ∑' n, ‖LSeries.term (χ ·) s n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-1 - δ) := hsum.norm.tsum_le_tsum hterm hmaj
    _ ≤ _ := perron_pseries_bound hδ

/-- Pages 22 and 23, auxiliary principal contour and Perron line estimate. -/
theorem perron_right_line_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x t : ℝ} (hx : 2 ≤ x) :
    ‖χ.LFunction (((1 + 1 / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ≤ 3 * Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hh := LFunction_right_bound χ (δ := 1 / Real.log x) (t := t) (by positivity)
  simp only [one_div_one_div] at hh
  have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  linarith [Real.log_two_gt_d9]

/-- Pages 22 and 23, auxiliary principal contour and Perron line estimate. -/
theorem perron_abscissa_pos {x : ℝ} (hx : 2 ≤ x) : 0 < 1 / 2 + 1 / Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  positivity

/-- Pages 22 and 23, auxiliary principal contour and Perron line estimate. -/
theorem perron_growth_bound {x a : ℝ} (hx : 2 ≤ x) (ha : 0 < a) (hax : a ≤ 2 * x) :
    a ^ (1 / 2 + 1 / Real.log x) ≤ Real.exp 2 * Real.sqrt a := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog : Real.log a ≤ 2 * Real.log x := by
    have hh := Real.log_le_log ha hax
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne'] at hh
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx]
  have hp : a ^ (1 / Real.log x) ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos ha]
    apply Real.exp_le_exp.mpr
    rw [mul_one_div, div_le_iff₀ hl]
    exact hlog
  rw [Real.rpow_add ha, ← Real.sqrt_eq_rpow]
  exact (mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg a)).trans_eq (mul_comm _ _)

/-- Page 22, the right vertical line in the Perron formula before 3.36. -/
noncomputable def rightIntegral {q : ℕ} [NeZero q] (x N T : ℝ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ u in (-height T t)..height T t,
    integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t
      (((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + u * I)

/-- Page 22, termwise right line integrals for the Perron formula before 3.36. -/
noncomputable def perronSeries {q : ℕ} [NeZero q] (x N T : ℝ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∑' n : ℕ,
    ∫ u in (-height T t)..height T t,
      LSeries.term (χ ·) (Thm4.half t +
        (((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + u * I)) n *
      kernel ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2)
        (((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + u * I)

/-- Page 22, the symmetric half integer gaps in the summed Perron remainder. -/
theorem half_gap_sum_eq (m : ℕ) :
    (∑ n ∈ Finset.range (2 * m + 2), 1 / |(m : ℝ) + 1 / 2 - n|) =
      2 * ∑ k ∈ Finset.range (m + 1), 1 / ((k : ℝ) + 1 / 2) := by
  let f : ℕ → ℝ := fun n => 1 / |(m : ℝ) + 1 / 2 - n|
  have hleft : (∑ n ∈ Finset.range (m + 1), f n) =
      ∑ k ∈ Finset.range (m + 1), 1 / ((k : ℝ) + 1 / 2) := by
    rw [← Finset.sum_range_reflect f (m + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k ≤ m := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    change 1 / |(m : ℝ) + 1 / 2 - ((m + 1 - 1 - k : ℕ) : ℝ)| = _
    rw [Nat.add_sub_cancel, Nat.cast_sub hkm]
    have he : (m : ℝ) + 1 / 2 - ((m : ℝ) - k) = (k : ℝ) + 1 / 2 := by ring
    rw [he, abs_of_pos (by positivity)]
  have hright : (∑ k ∈ Finset.range (m + 1), f (m + 1 + k)) =
      ∑ k ∈ Finset.range (m + 1), 1 / ((k : ℝ) + 1 / 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f]
    push_cast
    have he : (m : ℝ) + 1 / 2 - (m + 1 + k) = -((k : ℝ) + 1 / 2) := by ring
    rw [he, abs_neg, abs_of_pos (by positivity)]
  change (∑ n ∈ Finset.range (2 * m + 2), f n) = _
  rw [show 2 * m + 2 = (m + 1) + (m + 1) by omega,
    Finset.sum_range_add, hleft, hright]
  ring

/-- Page 22, a logarithmic bound for the near-cutoff half integer gaps. -/
theorem half_gap_sum_le (m : ℕ) :
    (∑ n ∈ Finset.range (2 * m + 2), 1 / |(m : ℝ) + 1 / 2 - n|) ≤
      4 * (1 + Real.log (m + 1)) := by
  rw [half_gap_sum_eq]
  have hh : (∑ k ∈ Finset.range (m + 1), 1 / ((k : ℝ) + 1 / 2)) ≤
      2 * (harmonic (m + 1) : ℝ) := by
    rw [harmonic]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [one_div, le_mul_inv_iff₀ (by positivity : (0 : ℝ) < k + 1)]
    rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < k + 1 / 2)]
    norm_num
    linarith [(show (0 : ℝ) ≤ k from Nat.cast_nonneg k)]
  have hl := harmonic_le_one_add_log (m + 1)
  push_cast at hl
  linarith

/-- Page 22, the near-cutoff gap sum with the uniform log x scale. -/
theorem half_endpoint_gap_sum_log {x N : ℝ}
    (hx : 2 ≤ x) (hN : 2 ≤ N) (hNx : N ≤ x) :
    (∑ n ∈ Finset.range (2 * ⌊N⌋₊ + 2),
      1 / |(⌊N⌋₊ : ℝ) + 1 / 2 - n|) ≤ 16 * Real.log x := by
  have hf : (⌊N⌋₊ : ℝ) ≤ N := Nat.floor_le (by linarith)
  have hlog : Real.log ((⌊N⌋₊ : ℝ) + 1) ≤ Real.log (2 * x) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : x ≠ 0)] at hlog
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hgap := half_gap_sum_le ⌊N⌋₊
  nlinarith [Real.log_two_gt_d9]

/-- Page 22, a summable local majorant for the Perron remainders near the cutoff. -/
theorem near_perron_term_bound {a n c : ℝ} (ha : 0 < a) (hn : 0 < n)
    (hc : 0 ≤ c) (hc2 : c ≤ 2) (han : a / 2 ≤ n) (hna : n ≤ 2 * a)
    (hne : a ≠ n) :
    n ^ (-1 / 2 : ℝ) * (a / n) ^ c / |Real.log (a / n)| ≤
      16 * Real.sqrt a / |a - n| := by
  have har : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hnr : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hroot : Real.sqrt a ≤ 2 * Real.sqrt n := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hn.le]
  have hninv : n ^ (-1 / 2 : ℝ) ≤ 2 / Real.sqrt a := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hn.le,
      ← Real.sqrt_eq_rpow, ← one_div]
    exact (div_le_div_iff₀ hnr har).mpr (by simpa using hroot)
  have hratio : a / n ≤ 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hpow : (a / n) ^ c ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ c := Real.rpow_le_rpow (by positivity) hratio hc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc2
      _ = 4 := by norm_num
  have hlog := inverse_log_bound ha hn hne
  have hgap : 0 < |a - n| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hlog' : 1 / |Real.log (a / n)| ≤ 2 * a / |a - n| :=
    hlog.trans (div_le_div_of_nonneg_right (max_le (by linarith) hna) hgap.le)
  have hnum : n ^ (-1 / 2 : ℝ) * (a / n) ^ c ≤ (2 / Real.sqrt a) * 4 :=
    mul_le_mul hninv hpow (by positivity) (by positivity)
  calc
    _ = (n ^ (-1 / 2 : ℝ) * (a / n) ^ c) * (1 / |Real.log (a / n)|) := by ring
    _ ≤ ((2 / Real.sqrt a) * 4) * (2 * a / |a - n|) :=
      mul_le_mul hnum hlog' (by positivity) (by positivity)
    _ = 16 * Real.sqrt a / |a - n| := by
      have hs := Real.sq_sqrt ha.le
      field_simp
      nlinarith

/-- Page 22, the Perron remainder away from the upper cutoff. -/
theorem far_perron_term_bound {a n c : ℝ} (ha : 0 < a) (hn : 0 < n)
    (hfar : n ≤ a / 2 ∨ 2 * a ≤ n) :
    n ^ (-1 / 2 : ℝ) * (a / n) ^ c / |Real.log (a / n)| ≤
      2 * a ^ c * n ^ (-1 / 2 - c) := by
  have hne : a ≠ n := by
    intro he
    subst n
    rcases hfar with h | h <;> linarith
  have hgap : 0 < |a - n| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hlog : 1 / |Real.log (a / n)| ≤ 2 := by
    apply (inverse_log_bound ha hn hne).trans
    rw [div_le_iff₀ hgap]
    rcases hfar with h | h
    · rw [max_eq_left (by linarith : n ≤ a), abs_of_nonneg (by linarith : 0 ≤ a - n)]
      linarith
    · rw [max_eq_right (by linarith : a ≤ n), abs_of_nonpos (by linarith : a - n ≤ 0)]
      linarith
  have hpow : n ^ (-1 / 2 : ℝ) * (a / n) ^ c = a ^ c * n ^ (-1 / 2 - c) := by
    rw [Real.div_rpow ha.le hn.le]
    calc
      _ = a ^ c * (n ^ (-1 / 2 : ℝ) * n ^ (-c)) := by rw [Real.rpow_neg hn.le]; ring
      _ = _ := by rw [← Real.rpow_add hn]; congr 1
  calc
    _ = (n ^ (-1 / 2 : ℝ) * (a / n) ^ c) * (1 / |Real.log (a / n)|) := by ring
    _ ≤ (n ^ (-1 / 2 : ℝ) * (a / n) ^ c) * 2 :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by rw [hpow]; ring

/-- Page 22, the full numerical upper-endpoint sum in the Perron remainder. -/
theorem summed_upper_numeric_remainders (m : ℕ) (hm : 2 ≤ m) {x : ℝ}
    (hmx : (m : ℝ) ≤ x) :
    let a : ℝ := (m : ℝ) + 1 / 2
    let c : ℝ := 1 / 2 + 1 / Real.log x
    Summable (fun n : ℕ => (n : ℝ) ^ (-1 / 2 : ℝ) * (a / n) ^ c /
      |Real.log (a / n)|) ∧
    (∑' n : ℕ, (n : ℝ) ^ (-1 / 2 : ℝ) * (a / n) ^ c /
      |Real.log (a / n)|) ≤
        (512 + 12 * Real.exp 2) * Real.sqrt m * Real.log x := by
  classical
  let a : ℝ := (m : ℝ) + 1 / 2
  let c : ℝ := 1 / 2 + 1 / Real.log x
  let F : ℕ → ℝ := fun n => (n : ℝ) ^ (-1 / 2 : ℝ) * (a / n) ^ c /
    |Real.log (a / n)|
  let S := Finset.range (2 * m + 2)
  let G : ℕ → ℝ := fun n => if n ∈ S then 16 * Real.sqrt a / |a - n| else 0
  let P : ℕ → ℝ := fun n => (n : ℝ) ^ (-1 - 1 / Real.log x)
  change Summable F ∧ (∑' n, F n) ≤ _
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 2 ≤ x := hmR.trans hmx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc2 : c ≤ 2 := by
    have hh : 1 / Real.log x ≤ 3 / 2 := (div_le_iff₀ hl).mpr (by linarith [Real.log_two_gt_d9])
    dsimp [c]; linarith
  have hroot : Real.sqrt a ≤ 2 * Real.sqrt m := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity)
    dsimp [a]
    nlinarith
  have hgrowth : a ^ c ≤ Real.exp 2 * Real.sqrt a :=
    perron_growth_bound hx ha (by dsimp [a]; linarith)
  have hP : Summable P := Real.summable_nat_rpow.mpr (by linarith [one_div_pos.mpr hl])
  have hPsum : (∑' n, P n) ≤ 3 * Real.log x := by
    have hp := perron_pseries_bound (one_div_pos.mpr hl)
    simp only [one_div_one_div] at hp
    dsimp [P]
    linarith [Real.log_two_gt_d9]
  have hG : Summable G := summable_of_ne_finset_zero (s := S) (by intro n hn; simp [G, hn])
  have hGsum : (∑' n, G n) ≤ 256 * Real.sqrt a * Real.log x := by
    have heq : (∑' n, G n) = 16 * Real.sqrt a *
        ∑ n ∈ Finset.range (2 * m + 2), 1 / |(m : ℝ) + 1 / 2 - n| := by
      rw [tsum_eq_sum (s := S) (by intro n hn; simp [G, hn]), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [G, hn, ite_true]
      dsimp [a]
      ring
    rw [heq]
    have hh := half_endpoint_gap_sum_log (N := (m : ℝ)) hx hmR hmx
    simp only [Nat.floor_natCast] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 16 * Real.sqrt a by positivity)
    nlinarith
  have hdom (n : ℕ) : F n ≤ G n + 2 * a ^ c * P n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F, Real.zero_rpow (by norm_num : (-1 / 2 : ℝ) ≠ 0)]
      positivity
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hne : a ≠ n := by simpa only [Nat.floor_natCast] using half_endpoint_ne (m : ℝ) n
    by_cases hlow : a / 2 ≤ n
    · by_cases hmem : n ∈ S
      · have hnr : n ≤ 2 * m + 1 := by have := Finset.mem_range.mp hmem; omega
        have hnrR : (n : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hnr
        have hh := near_perron_term_bound ha hnR hc hc2 hlow
          (show (n : ℝ) ≤ 2 * a by dsimp [a]; linarith) hne
        change _ ≤ _ at hh
        have hfar0 : 0 ≤ 2 * a ^ c * P n := by dsimp [P]; positivity
        simpa only [F, G, hmem, ite_true] using hh.trans (le_add_of_nonneg_right hfar0)
      · have hnr : 2 * m + 2 ≤ n := by
          have : ¬ n < 2 * m + 2 := by simpa [S] using hmem
          omega
        have hnrR : 2 * (m : ℝ) + 2 ≤ n := by exact_mod_cast hnr
        have hh := far_perron_term_bound ha hnR (c := c)
          (Or.inr (show 2 * a ≤ n by dsimp [a]; linarith))
        have hexp : -1 / 2 - c = -1 - 1 / Real.log x := by dsimp [c]; ring
        simpa only [F, G, hmem, ite_false, zero_add, P, hexp] using hh
    · have hh := far_perron_term_bound ha hnR (c := c) (Or.inl (le_of_not_ge hlow))
      have hexp : -1 / 2 - c = -1 - 1 / Real.log x := by dsimp [c]; ring
      rw [hexp] at hh
      have hG0 : 0 ≤ G n := by dsimp [G]; split_ifs <;> positivity
      exact hh.trans (le_add_of_nonneg_left hG0)
  have hmajor : Summable (fun n => G n + 2 * a ^ c * P n) := hG.add (hP.mul_left _)
  have hF : Summable F := Summable.of_nonneg_of_le (by intro n; dsimp [F]; positivity) hdom hmajor
  refine ⟨hF, ?_⟩
  have hsum := hF.tsum_le_tsum hdom hmajor
  rw [hG.tsum_add (hP.mul_left _), tsum_mul_left] at hsum
  have hfar : 2 * a ^ c * (∑' n, P n) ≤ 6 * Real.exp 2 * Real.sqrt a * Real.log x := by
    have hh := mul_le_mul hgrowth hPsum
      (tsum_nonneg (fun n => by dsimp [P]; positivity)) (by positivity)
    nlinarith
  have hscale : 0 ≤ Real.log x := hl.le
  have htotal : (∑' n, F n) ≤ (256 + 6 * Real.exp 2) * Real.sqrt a * Real.log x := by linarith
  have hh := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ (256 + 6 * Real.exp 2) * Real.log x by positivity)
  nlinarith

/-- Page 22, the numerical lower-endpoint sum for the subtracted Perron kernel. -/
theorem summed_lower_numeric_remainders {x : ℝ} (hx : 2 ≤ x) :
    let c : ℝ := 1 / 2 + 1 / Real.log x
    Summable (fun n : ℕ => (n : ℝ) ^ (-1 / 2 : ℝ) * ((1 / 2 : ℝ) / n) ^ c /
      |Real.log ((1 / 2 : ℝ) / n)|) ∧
    (∑' n : ℕ, (n : ℝ) ^ (-1 / 2 : ℝ) * ((1 / 2 : ℝ) / n) ^ c /
      |Real.log ((1 / 2 : ℝ) / n)|) ≤ 6 * Real.log x := by
  let c : ℝ := 1 / 2 + 1 / Real.log x
  let F : ℕ → ℝ := fun n => (n : ℝ) ^ (-1 / 2 : ℝ) * ((1 / 2 : ℝ) / n) ^ c /
    |Real.log ((1 / 2 : ℝ) / n)|
  let P : ℕ → ℝ := fun n => (n : ℝ) ^ (-1 - 1 / Real.log x)
  change Summable F ∧ (∑' n, F n) ≤ _
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hp : (1 / 2 : ℝ) ^ c ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) hc
  have hP : Summable P := Real.summable_nat_rpow.mpr (by linarith [one_div_pos.mpr hl])
  have hPsum : (∑' n, P n) ≤ 3 * Real.log x := by
    have hh := perron_pseries_bound (one_div_pos.mpr hl)
    simp only [one_div_one_div] at hh
    dsimp [P]
    linarith [Real.log_two_gt_d9]
  have hdom (n : ℕ) : F n ≤ 2 * P n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F]
      dsimp [P]
      positivity
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hh := far_perron_term_bound (a := 1 / 2) (by norm_num) hnR (c := c)
      (Or.inr (by linarith))
    have hexp : -1 / 2 - c = -1 - 1 / Real.log x := by dsimp [c]; ring
    rw [hexp] at hh
    have ht : 2 * (1 / 2 : ℝ) ^ c * P n ≤ 2 * P n := by
      have hmul := mul_le_mul_of_nonneg_right hp (show 0 ≤ P n by dsimp [P]; positivity)
      linarith
    exact hh.trans ht
  have hmajor : Summable (fun n => 2 * P n) := hP.mul_left _
  have hF : Summable F := Summable.of_nonneg_of_le (by intro n; dsimp [F]; positivity) hdom hmajor
  refine ⟨hF, ?_⟩
  have hh := hF.tsum_le_tsum hdom hmajor
  rw [tsum_mul_left] at hh
  linarith

/-- Page 22, identify a termwise right integral with the two existing Perron kernels. -/
theorem term_integral_perron {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : 0 < n) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (H t : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ u in (-H)..H, LSeries.term (χ ·)
        (Thm4.half t + ((c : ℂ) + u * I)) n * kernel a b ((c : ℂ) + u * I)) =
      LSeries.term (χ ·) (Thm4.half t) n *
        (LeanLab.DERZ1997.Decomp1529b.perronI (a / n) c H -
          LeanLab.DERZ1997.Decomp1529b.perronI (b / n) c H) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hz (u : ℝ) : (c : ℂ) + u * I ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have hcont (y : ℝ) (hy : 0 < y) :
      Continuous (fun u : ℝ => (y : ℂ) ^ ((c : ℂ) + u * I) / ((c : ℂ) + u * I)) := by
    simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
    apply Continuous.div (by fun_prop) (by fun_prop) hz
  have hpoint (u : ℝ) : LSeries.term (χ ·) (Thm4.half t + ((c : ℂ) + u * I)) n *
      kernel a b ((c : ℂ) + u * I) = LSeries.term (χ ·) (Thm4.half t) n *
        (((a / n : ℝ) : ℂ) ^ ((c : ℂ) + u * I) / ((c : ℂ) + u * I) -
          ((b / n : ℝ) : ℂ) ^ ((c : ℂ) + u * I) / ((c : ℂ) + u * I)) := by
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne',
      kernel_cpow ha hb (hz u), Complex.cpow_add _ _ hnC]
    push_cast
    have hdiva := Complex.div_cpow_ofReal_nonneg ha.le hnR.le ((c : ℂ) + u * I)
    have hdivb := Complex.div_cpow_ofReal_nonneg hb.le hnR.le ((c : ℂ) + u * I)
    have hnc : ((n : ℝ) : ℂ) = (n : ℂ) := by norm_cast
    rw [hnc] at hdiva hdivb
    rw [hdiva, hdivb]
    field_simp
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    ((hcont (a / n) (div_pos ha hnR)).intervalIntegrable _ _)
    ((hcont (b / n) (div_pos hb hnR)).intervalIntegrable _ _)]
  unfold LeanLab.DERZ1997.Decomp1529b.perronI
  push_cast
  ring

/-- Page 22, express the regular right-line series through the existing Perron kernels. -/
theorem perronSeries_eq_tsum_kernels {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 2 ≤ x) (N T t : ℝ) :
    perronSeries x N T χ t = ∑' n : ℕ,
      LSeries.term (χ ·) (Thm4.half t) n *
        (LeanLab.DERZ1997.Decomp1529b.perronI
          (((⌊N⌋₊ : ℝ) + 1 / 2) / n) (1 / 2 + 1 / Real.log x) (height T t) -
        LeanLab.DERZ1997.Decomp1529b.perronI
          ((1 / 2 : ℝ) / n) (1 / 2 + 1 / Real.log x) (height T t)) := by
  unfold perronSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact term_integral_perron χ hn (by positivity) (by norm_num)
      (perron_abscissa_pos hx) _ _

/-- LEAF. Page 22, Perron formula before display 3.36.
Sum the termwise remainders at the half integer endpoints.
The numerical sums and existing termwise Perron bound supply this leaf.
This proof uses no contour shift or L-series interchange. -/
theorem summed_perron_remainders :
    ∃ C : ℝ, 0 < C ∧ ∀ x N T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x →
        ‖partialSum N χ t - perronSeries x N T χ t‖ ≤
          C * Real.log x * (Real.sqrt N / T) := by
  classical
  let K : ℝ := 518 + 12 * Real.exp 2
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro x N T q _ χ t hx hN hNx hT hTx
  let m := ⌊N⌋₊
  let a : ℝ := (m : ℝ) + 1 / 2
  let c : ℝ := 1 / 2 + 1 / Real.log x
  let H : ℝ := height T t
  let U : ℕ → ℝ := fun n => (n : ℝ) ^ (-1 / 2 : ℝ) * (a / n) ^ c / |Real.log (a / n)|
  let V : ℕ → ℝ := fun n => (n : ℝ) ^ (-1 / 2 : ℝ) * ((1 / 2 : ℝ) / n) ^ c /
    |Real.log ((1 / 2 : ℝ) / n)|
  let B : ℕ → ℝ := fun n => (U n + V n) / (Real.pi * H)
  let cf : ℕ → ℂ := fun n => LSeries.term (χ ·) (Thm4.half t) n
  let R : ℕ → ℂ := fun n =>
    LeanLab.DERZ1997.Decomp1529b.perronI (a / n) c H -
      LeanLab.DERZ1997.Decomp1529b.perronI ((1 / 2 : ℝ) / n) c H
  let D : ℕ → ℂ := fun n => cf n * (if n ≤ m then 1 else 0)
  let E : ℕ → ℂ := fun n => cf n * (R n - (if n ≤ m then 1 else 0))
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hc : 0 < c := perron_abscissa_pos hx
  have hH : 0 < H := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (height_spec hT).2.1
  have hm : 2 ≤ m := (Nat.le_floor_iff (by linarith : 0 ≤ N)).mpr (by exact_mod_cast hN)
  have hmN : (m : ℝ) ≤ N := Nat.floor_le (by linarith)
  obtain ⟨hU, hUb⟩ := summed_upper_numeric_remainders m hm (hmN.trans hNx)
  obtain ⟨hV, hVb⟩ := summed_lower_numeric_remainders hx
  change Summable U at hU
  change Summable V at hV
  change (∑' n, U n) ≤ (512 + 12 * Real.exp 2) * Real.sqrt m * Real.log x at hUb
  change (∑' n, V n) ≤ 6 * Real.log x at hVb
  have hB : Summable B := (hU.add hV).div_const _
  have hcf (n : ℕ) : ‖cf n‖ ≤ (n : ℝ) ^ (-1 / 2 : ℝ) := by
    dsimp [cf]
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [ite_true, Nat.cast_zero]
      exact Real.rpow_nonneg (by norm_num) _
    · simp only [Nat.ne_of_gt hn, ite_false]
      have hre : (Thm4.half t).re = (1 / 2 : ℝ) := by simp [Thm4.half]
      rw [hre, show (-1 / 2 : ℝ) = -(1 / 2) by ring,
        Real.rpow_neg (by positivity : (0 : ℝ) ≤ n)]
      simpa only [one_div] using div_le_div_of_nonneg_right (χ.norm_le_one _)
        (show 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) by positivity)
  have hbound (n : ℕ) : ‖E n‖ ≤ B n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [E, cf, B, U, V]
    have hh := perron_difference_bound (N := N) hn hc hH
    change ‖R n - (if n ≤ m then 1 else 0)‖ ≤ _ at hh
    calc
      _ = ‖cf n‖ * ‖R n - (if n ≤ m then 1 else 0)‖ := norm_mul _ _
      _ ≤ (n : ℝ) ^ (-1 / 2 : ℝ) *
          ((a / n) ^ c / (Real.pi * H * |Real.log (a / n)|) +
            ((1 / 2 : ℝ) / n) ^ c / (Real.pi * H * |Real.log ((1 / 2 : ℝ) / n)|)) :=
        mul_le_mul (hcf n) hh (norm_nonneg _) (by positivity)
      _ = B n := by dsimp [B, U, V]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
  have hE : Summable E := hB.of_norm_bounded hbound
  have hDzero : ∀ n ∉ Finset.Icc 1 m, D n = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hnp
    · simp [D, cf]
    · have hnm : ¬ n ≤ m := by
        intro hnm
        exact hn (Finset.mem_Icc.mpr ⟨by omega, hnm⟩)
      simp [D, hnm]
  have hD : Summable D := summable_of_ne_finset_zero hDzero
  have hDsum : (∑' n, D n) = partialSum N χ t := by
    rw [tsum_eq_sum hDzero]
    unfold partialSum
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnm⟩ := Finset.mem_Icc.mp hn
    dsimp [D, cf]
    rw [if_pos hnm, mul_one, LSeries.term_of_ne_zero (by omega)]
  have hseries : perronSeries x N T χ t = (∑' n, E n) + partialSum N χ t := by
    rw [perronSeries_eq_tsum_kernels χ hx N T t]
    have hpoint (n : ℕ) : cf n * R n = E n + D n := by dsimp [E, D]; ring
    change (∑' n, cf n * R n) = _
    simp_rw [hpoint]
    rw [hE.tsum_add hD, hDsum]
  have hnorm : ‖partialSum N χ t - perronSeries x N T χ t‖ ≤ ∑' n, B n := by
    rw [hseries, show partialSum N χ t - ((∑' n, E n) + partialSum N χ t) =
      -(∑' n, E n) by ring, norm_neg]
    exact (norm_tsum_le_tsum_norm hE.norm).trans (hE.norm.tsum_le_tsum hbound hB)
  have hroot := Real.sqrt_le_sqrt hmN
  have hsN : 1 ≤ Real.sqrt N := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ N by linarith)
    simpa using hh
  have hUbN : (∑' n, U n) ≤ (512 + 12 * Real.exp 2) * Real.sqrt N * Real.log x := by
    exact hUb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hroot (by positivity)) hl.le)
  have hVbN : (∑' n, V n) ≤ 6 * Real.sqrt N * Real.log x := by
    have hh := mul_nonneg (sub_nonneg.mpr hsN) hl.le
    nlinarith
  have hsum : (∑' n, B n) ≤ K * Real.sqrt N * Real.log x / (Real.pi * H) := by
    dsimp [B]
    rw [tsum_div_const, hU.tsum_add hV]
    apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp [K]
    linarith
  have hHT : T / 2 ≤ H := by
    rcases (height_spec (t := t) hT).1 with hh | hh <;> change H = _ at hh <;> rw [hh] <;> linarith
  have hden : T ≤ Real.pi * H := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ K * Real.sqrt N * Real.log x / (Real.pi * H) := hnorm.trans hsum
    _ ≤ K * Real.sqrt N * Real.log x / T :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hden
    _ = _ := by ring


end Contour230
end LeanLab.BHP1997.DecompC165a
