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

/-- LEAF. Page 22, Perron formula and display 3.36, with the half integer
upper endpoint and the subtracted lower endpoint one half. The function J
is the explicit regular critical line integral at the safe chosen height.
Remaining work: summing the termwise Perron remainders, interchanging the
L-series and integral, and uniform horizontal bounds. Titchmarsh reference
30, Theorem 3.19, and Rademacher reference 28. CITED and OPEN. -/
theorem regularized_perron_bound (h8 : MeanValue132.Lemma8) :
    ∃ C : ℝ, 0 < C ∧ ∀ x N T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x → |t| ≤ T →
        ‖partialSum N χ t‖ ≤ ‖lineIntegral N T χ t‖ +
          C * Real.log x * (Real.sqrt q / Real.sqrt T) +
          C * Real.log x * (Real.sqrt N / T) +
          C * (if χ = 1 then Real.sqrt N / (1 + |t|) else 0) := by
  sorry

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

end Contour230

/-- Pages 22 and 23, display 3.36 and the weighted fourth moment.
The regular kernel, chosen height and complete Holder estimate are proved.
This exact sealed conclusion is CONDITIONAL on regularized_perron_bound.
The uniform pointwise contour error remains OPEN. -/
theorem contour_holder (h8 : MeanValue132.Lemma8) :
    ∃ C : ℝ, 0 < C ∧ ∀ x N T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        ∃ J : ℝ × DirichletCharacter ℂ q → ℂ,
          (∑ p ∈ S, ‖J p‖ ^ 4) ≤ C * Real.log x ^ (3 : ℝ) * weightedMoment T S ∧
          ∀ p ∈ S, ‖partialSum N p.2 p.1‖ ≤ ‖J p‖ +
            C * Real.log x * (Real.sqrt q / Real.sqrt T) +
            C * Real.log x * (Real.sqrt N / T) +
            C * (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0) := by
  obtain ⟨Ce, hCe, hpoint⟩ := Contour230.regularized_perron_bound h8
  let C := max Ce ((332 : ℝ) ^ 3)
  have hC : 0 < C := lt_of_lt_of_le hCe (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro x N T q _ S hx hN hNx hT hTx hq hqx hspace htimes
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  refine ⟨fun p => Contour230.lineIntegral N T p.2 p.1, ?_, ?_⟩
  · have hm := Contour230.lineIntegral_sum S hx hN hNx hT hTx htimes
    have hw0 : 0 ≤ weightedMoment T S := by
      unfold weightedMoment
      apply Finset.sum_nonneg
      intro p hp
      apply intervalIntegral.integral_nonneg (by linarith)
      intro u hu
      positivity
    have hc := mul_le_mul_of_nonneg_right (le_max_right Ce ((332 : ℝ) ^ 3))
      (show 0 ≤ Real.log x ^ (3 : ℝ) * weightedMoment T S by positivity)
    exact hm.trans (by simpa only [mul_assoc] using hc)
  · intro p hp
    have h0 : Ce ≤ C := le_max_left _ _
    have h1 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ Real.log x * (Real.sqrt q / Real.sqrt T) by positivity)
    have h2 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ Real.log x * (Real.sqrt N / T) by positivity)
    have h3 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0) by
        split_ifs <;> positivity)
    have hh := hpoint x N T q p.2 p.1 hx hN hNx hT hTx hq hqx (htimes p hp)
    simp only [mul_assoc] at hh ⊢
    exact hh.trans (add_le_add (add_le_add (add_le_add (le_refl _) h1) h2) h3)

/-- LEAF. Page 23, fourth and fifth displays. Rearrange by character,
bound the kernel with Spacing132.kernel_le_ten_log and apply Lemma 7
at 2T with ambient scale 2x. Absorb log 2x into a constant times log x.
CONDITIONAL on Lemma 7. The finite spacing and integration step is proved. -/
theorem spaced_weighted_moment (h7 : MeanValue132.Lemma7) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 < C ∧ ∀ x T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      2 ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        weightedMoment T S ≤ C * ((q : ℝ) * T * Real.log x ^ B) := by
  obtain ⟨B, C, hB, hC, h7⟩ := h7
  refine ⟨B + 1, 20 * C * (2 : ℝ) ^ B, by linarith, by positivity, ?_⟩
  intro x T q _ S hx hT hTx hq hqx hspace htimes
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hcont (χ : DirichletCharacter ℂ q) :
      Continuous (fun u : ℝ => ‖χ.LFunction (Thm4.half u)‖ ^ 4) := by
    have hh : Continuous (fun u : ℝ => Thm4.half u) := by
      unfold Thm4.half
      fun_prop
    have hc : Continuous (fun u : ℝ => χ.LFunction (Thm4.half u)) := by
      apply continuous_iff_continuousAt.mpr
      intro u
      have hne : Thm4.half u ≠ 1 := by
        intro heq
        have hre := congrArg Complex.re heq
        norm_num [Thm4.half] at hre
      exact (χ.differentiableAt_LFunction _ (.inl hne)).continuousAt.comp hh.continuousAt
    exact hc.norm.pow 4
  have hk := KernelC165.weighted_kernel_integral S
    (fun χ u => ‖χ.LFunction (Thm4.half u)‖ ^ 4) hcont
    (fun χ u => pow_nonneg (norm_nonneg _) 4) hx (by linarith) hTx hspace htimes
  have hm := h7 (2 * x) (2 * T) q (by linarith) (by linarith)
    (by linarith) hq (by linarith)
  have hlog2 : Real.log (2 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0)]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hlog20 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hp : Real.log (2 * x) ^ B ≤ (2 : ℝ) ^ B * Real.log x ^ B := by
    calc
      Real.log (2 * x) ^ B ≤ (2 * Real.log x) ^ B := Real.rpow_le_rpow hlog20 hlog2 hB
      _ = _ := Real.mul_rpow (by norm_num) hlog.le
  have hexp : Real.log x ^ (B + 1) = Real.log x ^ B * Real.log x := by
    rw [Real.rpow_add hlog, Real.rpow_one]
  calc
    weightedMoment T S ≤ 10 * Real.log x *
        ∑ χ : DirichletCharacter ℂ q, ∫ u in (-2 * T)..(2 * T),
          ‖χ.LFunction (Thm4.half u)‖ ^ 4 := hk
    _ ≤ 10 * Real.log x * (C * (q : ℝ) * (2 * T) * Real.log (2 * x) ^ B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [neg_mul] using hm
    _ ≤ 10 * Real.log x * (C * (q : ℝ) * (2 * T) *
        ((2 : ℝ) ^ B * Real.log x ^ B)) := by
      gcongr
    _ = 20 * C * (2 : ℝ) ^ B * ((q : ℝ) * T * Real.log x ^ (B + 1)) := by
      rw [hexp]
      ring


/-- Page 23, collecting constants proves the exact perron_input statement.
CONDITIONAL on the three OPEN leaves. No direct sorry. -/
theorem perron_input :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 < C ∧ ∀ x N T : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        ∃ J : ℝ × DirichletCharacter ℂ q → ℂ,
          (∑ p ∈ S, ‖J p‖ ^ 4) ≤ C * ((q : ℝ) * T * Real.log x ^ B) ∧
          ∀ p ∈ S, ‖partialSum N p.2 p.1‖ ≤ ‖J p‖ +
            C * Real.log x * (Real.sqrt q / Real.sqrt T) +
            C * Real.log x * (Real.sqrt N / T) +
            C * (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0) := by
  obtain ⟨C0, hC0, hcontour⟩ := contour_holder rademacher_strip_bound
  obtain ⟨B, C1, hB, hC1, hmoment⟩ := spaced_weighted_moment all_character_fourth_moment
  let C := max C0 (C0 * C1)
  have hC : 0 < C := lt_of_lt_of_le hC0 (le_max_left _ _)
  refine ⟨B + 3, C, by linarith, hC, ?_⟩
  intro x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨J, hJ, hpoint⟩ := hcontour x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  refine ⟨J, ?_, ?_⟩
  · have hW := hmoment x T q S hx hT hTx hq hqx hspace htimes
    have hprod : Real.log x ^ (3 : ℝ) * Real.log x ^ B = Real.log x ^ (B + 3) := by
      rw [← Real.rpow_add hlog]
      congr 1
      ring
    calc
      (∑ p ∈ S, ‖J p‖ ^ 4) ≤ C0 * Real.log x ^ (3 : ℝ) * weightedMoment T S := hJ
      _ ≤ C0 * Real.log x ^ (3 : ℝ) * (C1 * ((q : ℝ) * T * Real.log x ^ B)) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
      _ = (C0 * C1) * ((q : ℝ) * T * Real.log x ^ (B + 3)) := by
        calc
          _ = (C0 * C1) * ((q : ℝ) * T *
              (Real.log x ^ (3 : ℝ) * Real.log x ^ B)) := by ring
          _ = _ := by rw [hprod]
      _ ≤ C * ((q : ℝ) * T * Real.log x ^ (B + 3)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · intro p hp
    have h0 : C0 ≤ C := le_max_left _ _
    have h1 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ Real.log x * (Real.sqrt q / Real.sqrt T) by positivity)
    have h2 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ Real.log x * (Real.sqrt N / T) by positivity)
    have h3 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0) by
        split_ifs <;> positivity)
    have hpbound := hpoint p hp
    simp only [mul_assoc] at hpbound ⊢
    by_cases hχ : p.2 = 1
    · simp only [hχ, ite_true] at hpbound h3 ⊢
      exact hpbound.trans (add_le_add (add_le_add (add_le_add (le_refl _) h1) h2) h3)
    · simp only [hχ, ite_false] at hpbound h3 ⊢
      exact hpbound.trans (add_le_add (add_le_add (add_le_add (le_refl _) h1) h2) h3)

/-- Page 23, the existing finite fourth-power assembly with the new
Perron decomposition. CONDITIONAL on its named analytic leaves. -/
theorem lemma9 : MeanValue132.Lemma9 := by
  obtain ⟨B, C, hB, hC, hinput⟩ := perron_input
  refine ⟨B, 64 * max C (C ^ 4), hB, by positivity, ?_⟩
  intro x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  obtain ⟨J, hJ, hpoint⟩ := hinput x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  have hs := Decomp132b.fourth_moment_sum S (fun p => partialSum N p.2 p.1) J
    (fun _ => C * Real.log x * (Real.sqrt q / Real.sqrt T))
    (fun _ => C * Real.log x * (Real.sqrt N / T))
    (fun p => C * (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0)) hpoint
  rw [Decomp132b.error_sum x N T C (by linarith) (by linarith) S] at hs
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hmain : 0 ≤ (q : ℝ) * T * Real.log x ^ B := by positivity
  have hrem : 0 ≤ remainder x N T S := by
    unfold remainder
    apply add_nonneg
    · positivity
    · apply mul_nonneg (sq_nonneg _)
      apply Finset.sum_nonneg
      intro p hp
      split_ifs <;> positivity
  have h1 := mul_le_mul_of_nonneg_right (le_max_left C (C ^ 4)) hmain
  have h2 := mul_le_mul_of_nonneg_right (le_max_right C (C ^ 4)) hrem
  nlinarith

end LeanLab.BHP1997.DecompC165a
