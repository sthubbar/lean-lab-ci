import LeanLab.PNTPort.ExplicitPsi1.Log2Pi

/-!
# P0053 Lemma 1 at real `z`: the constant `-log 2π`

Lab proof, unit U-6500, CLOUD 20261020T1415Z-cloud44. AI wrote this file. Known mathematics.

Languasco-Zaccagnini, A Cesàro average of Goldbach numbers, arXiv 1206.0251v1, Forum Math. 27
(2015), Lemma 1 prints `S̃(z) = 1/z - Σ_ρ z^{-ρ} Γ(ρ) + E(a, y)` with `E(a, y) ≪ |z|^{1/2}` for
`|y| ≤ a`, `z = a + iy`. The constant `-ζ'/ζ(0) = -log 2π` of the explicit formula is missing
there; Languasco's survey, arXiv 1606.00860 §6, corrects it to `E ≪ 1 + |z|^{1/2}`, and
arXiv 1806.04930 Lemma 1 writes the `-log 2π` term out.

Here, from the lab's explicit formula for `ψ₁` with all zeros, PNTPort/ExplicitPsi1:

* `stilde_real`: for every real `a > 0`,
  `|S̃(a) - (1/a - log 2π - Σ_ρ m(ρ) Γ(ρ) a^{-ρ})| ≤ K a^{1/2}`, unconditional;
* `lemma1_printed_real_false`: the printed bound `E(a, 0) ≪ a^{1/2}` fails.

Binary Goldbach is open.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage.LZ2012

open LeanLab.PNTPort.ExplicitPsi1

/-- The nontrivial zeros, as a type. -/
abbrev NZ := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- `S̃(a) = Σ_n Λ(n) e^{-na}`. -/
def St (a : ℝ) : ℝ := ∑' n : ℕ, Λ n * Real.exp (-(a * n))

/-- `ψ₁(x) = Σ_n Λ(n) max(0, x - n)`. -/
def psi1r (x : ℝ) : ℝ := ∑' n : ℕ, Λ n * max 0 (x - n)

/-- The zero term of `ψ₁`: `m(ρ) x^{ρ+1}/(ρ(ρ + 1))`. -/
def wt (x : ℝ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))

/-- `W(x) = Σ_ρ m(ρ) x^{ρ+1}/(ρ(ρ + 1))`. -/
def W (x : ℝ) : ℂ := ∑' ρ : NZ, wt x ρ.1

/-- The zero term of `S̃`: `m(ρ) Γ(ρ) a^{-ρ}`. -/
def gt (a : ℝ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt riemannZeta ρ : ℂ) * (Gamma ρ * ((1 / a : ℝ) : ℂ) ^ ρ)

lemma summable_hw_NZ : Summable (fun ρ : NZ => hw ρ.1) := by
  have h := summable_hw
  rw [Zall_eq] at h
  exact h

lemma hw_nonneg (ρ : ℂ) : 0 ≤ hw ρ := by unfold hw; positivity

/-! ### Real Laplace integrals -/

lemma intOn_rpow {s a : ℝ} (hs : -1 < s) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x ^ s * Real.exp (-(a * x))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hs one_pos ha
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

lemma integral_rpow {s a : ℝ} (hs : -1 < s) (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), x ^ s * Real.exp (-(a * x)) = (1 / a) ^ (s + 1) * Real.Gamma (s + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := s + 1) (by linarith) ha
  simpa using h

/-- `∫_0^∞ max(0, x - c) e^{-ax} dx = e^{-ac}/a²` for `c ≥ 0`. -/
lemma lap_shift {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    ∫ x in Ioi (0 : ℝ), max 0 (x - c) * Real.exp (-(a * x)) = Real.exp (-(a * c)) / a ^ 2 := by
  set h : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun t => t * Real.exp (-(a * (t + c))))
  have e1 : (Ioi (0 : ℝ)).indicator (fun x => max 0 (x - c) * Real.exp (-(a * x))) =
      fun x => h (x - c) := by
    funext x
    simp only [h, Set.indicator, mem_Ioi]
    by_cases hx : 0 < x
    · by_cases hxc : 0 < x - c
      · rw [if_pos hx, if_pos hxc, max_eq_right hxc.le]; ring_nf
      · rw [if_pos hx, if_neg hxc, max_eq_left (not_lt.mp hxc)]; ring
    · rw [if_neg hx, if_neg (by intro h'; exact hx (by linarith))]
  rw [← integral_indicator measurableSet_Ioi, e1, integral_sub_right_eq_self (fun x => h x) c,
    integral_indicator measurableSet_Ioi]
  have e2 : ∀ t : ℝ, t * Real.exp (-(a * (t + c))) =
      Real.exp (-(a * c)) * (t ^ (1 : ℝ) * Real.exp (-(a * t))) := by
    intro t
    rw [Real.rpow_one, show -(a * (t + c)) = -(a * c) + -(a * t) by ring, Real.exp_add]; ring
  simp_rw [e2]
  rw [integral_const_mul, integral_rpow (by norm_num) ha]
  rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.Gamma_two, show (2 : ℝ) = (2 : ℕ) by norm_num,
    Real.rpow_natCast]
  field_simp

lemma intOn_shift {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    IntegrableOn (fun x : ℝ => max 0 (x - c) * Real.exp (-(a * x))) (Ioi 0) := by
  refine Integrable.mono' (intOn_rpow (s := 1) (by norm_num) ha) ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    exact max_le (le_of_lt hx) (by linarith)

/-! ### `S̃(a)` as a Laplace transform of `ψ₁` -/

lemma vonMangoldt_le (n : ℕ) : Λ n ≤ (n : ℝ) ^ 1 := by
  rw [pow_one]
  calc Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    _ ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · exact (Real.log_le_sub_one_of_pos (by exact_mod_cast h)).trans (by linarith)

lemma summable_St {a : ℝ} (ha : 0 < a) : Summable (fun n : ℕ => Λ n * Real.exp (-(a * n))) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Real.summable_pow_mul_exp_neg_nat_mul 1 ha)
  rw [neg_mul_eq_neg_mul]
  exact mul_le_mul_of_nonneg_right (vonMangoldt_le n) (Real.exp_pos _).le

lemma St_eq {a : ℝ} (ha : 0 < a) :
    St a = a ^ 2 * ∫ x in Ioi (0 : ℝ), psi1r x * Real.exp (-(a * x)) := by
  have hF : ∀ n : ℕ, Integrable (fun x : ℝ => Λ n * (max 0 (x - n) * Real.exp (-(a * x))))
      (volume.restrict (Ioi (0 : ℝ))) := fun n => (intOn_shift ha n.cast_nonneg).const_mul _
  have hI : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), ‖Λ n * (max 0 (x - n) * Real.exp (-(a * x)))‖ =
      Λ n * Real.exp (-(a * n)) / a ^ 2 := by
    intro n
    have : ∀ x : ℝ, ‖Λ n * (max 0 (x - n) * Real.exp (-(a * x)))‖ =
        Λ n * (max 0 (x - n) * Real.exp (-(a * x))) := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (mul_nonneg (le_max_left _ _) (Real.exp_pos _).le)
    simp_rw [this]
    rw [integral_const_mul, lap_shift ha n.cast_nonneg]; ring
  have hsum := integral_tsum_of_summable_integral_norm hF (by
    simp_rw [hI]; exact (summable_St ha).div_const _)
  have e : ∀ x : ℝ, psi1r x * Real.exp (-(a * x)) =
      ∑' n : ℕ, Λ n * (max 0 (x - n) * Real.exp (-(a * x))) := by
    intro x; rw [psi1r, ← tsum_mul_right]; congr 1; funext n; ring
  simp_rw [e]
  rw [← hsum]
  have e2 : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), Λ n * (max 0 (x - n) * Real.exp (-(a * x))) =
      Λ n * Real.exp (-(a * n)) / a ^ 2 := by
    intro n; rw [integral_const_mul, lap_shift ha n.cast_nonneg]; ring
  simp_rw [e2]
  rw [tsum_div_const, St]
  field_simp


/-! ### The zero side -/

lemma NZ_countable : Countable NZ := by
  have hc : Zall.Countable := by
    refine (Set.countable_iUnion fun n : ℕ => (zeros_rect_finite 2 n).countable).mono ?_
    intro ρ hρ
    rw [Set.mem_iUnion]
    refine ⟨⌈|ρ.im|⌉₊, ?_, hρ.1⟩
    rw [mem_rect (by norm_num) (by positivity)]
    have hc := Nat.le_ceil |ρ.im|
    exact ⟨⟨hρ.2, by linarith [Zall_re_lt hρ]⟩, abs_le.mp hc⟩
  rw [Zall_eq] at hc
  exact hc.to_subtype

attribute [local instance] NZ_countable

lemma norm_wt_le {x : ℝ} (hx : 0 ≤ x) (ρ : NZ) : ‖wt x ρ.1‖ ≤ (x + 1) ^ 2 * hw ρ.1 := by
  have hre0 := ρ.2.2.1
  have hre1 := ρ.2.2.2
  have hpow : ‖(x : ℂ) ^ (ρ.1 + 1)‖ ≤ (x + 1) ^ 2 := by
    rcases eq_or_lt_of_le hx with h0 | hpos
    · rw [← h0, ofReal_zero, zero_cpow (by intro e; have := congr_arg re e; simp at this; linarith)]
      simp only [norm_zero]; positivity
    · rw [norm_cpow_eq_rpow_re_of_pos hpos]
      have hα : (ρ.1 + 1).re = ρ.1.re + 1 := by simp
      rw [hα]
      calc x ^ (ρ.1.re + 1) ≤ (x + 1) ^ (ρ.1.re + 1) :=
            Real.rpow_le_rpow hx (by linarith) (by linarith)
        _ ≤ (x + 1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = (x + 1) ^ 2 := by norm_cast
  unfold wt hw
  rw [norm_mul, norm_div, Complex.norm_natCast]
  calc (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * (‖(x : ℂ) ^ (ρ.1 + 1)‖ / ‖ρ.1 * (ρ.1 + 1)‖)
      = ‖(x : ℂ) ^ (ρ.1 + 1)‖ * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1 * (ρ.1 + 1)‖) := by
        ring
    _ ≤ (x + 1) ^ 2 * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1 * (ρ.1 + 1)‖) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)

lemma continuous_wt (ρ : NZ) : Continuous fun x : ℝ => wt x ρ.1 := by
  unfold wt
  have := continuous_ofReal_cpow_const (y := ρ.1 + 1) (by simp; linarith [ρ.2.2.1])
  exact (this.div_const _).const_mul _

lemma W_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt W x := by
  have h : ContinuousOn W (Icc 0 (x + 1)) := by
    apply continuousOn_tsum (fun ρ => (continuous_wt ρ).continuousOn)
      (summable_hw_NZ.mul_left ((x + 1 + 1) ^ 2))
    intro ρ u hu
    refine (norm_wt_le hu.1 ρ).trans ?_
    gcongr
    · exact hw_nonneg _
    · linarith [hu.1]
    · linarith [hu.2]
  exact h.continuousAt (Icc_mem_nhds hx (by linarith))

lemma norm_W_le {x : ℝ} (hx : 0 ≤ x) : ‖W x‖ ≤ (x + 1) ^ 2 * ∑' ρ : NZ, hw ρ.1 :=
  tsum_of_norm_bounded (summable_hw_NZ.hasSum.mul_left _) (fun ρ => norm_wt_le hx ρ)

lemma psi1r_continuous : Continuous psi1r := by
  rw [continuous_iff_continuousAt]
  intro x
  set M : ℕ := ⌊|x|⌋₊ + 1
  have hxM : x < M := by
    have := Nat.lt_floor_add_one |x|
    push_cast [M]; linarith [le_abs_self x]
  have hev : (fun y : ℝ => ∑ n ∈ Finset.range M, Λ n * max 0 (y - n)) =ᶠ[𝓝 x] psi1r := by
    filter_upwards [Iio_mem_nhds hxM] with y hy
    rw [psi1r, tsum_eq_sum]
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have : y - n ≤ 0 := by
      have : (M : ℝ) ≤ n := by exact_mod_cast hn
      linarith [mem_Iio.mp hy]
    rw [max_eq_left this, mul_zero]
  exact ContinuousAt.congr (by fun_prop) hev

/-- `(x + 1)² e^{-ax}` is integrable on `(0, ∞)`. -/
lemma intOn_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (x + 1) ^ 2 * Real.exp (-(a * x))) (Ioi 0) := by
  have h := ((intOn_rpow (s := 2) (by norm_num) ha).add
    ((intOn_rpow (s := 1) (by norm_num) ha).const_mul 2)).add (intOn_rpow (s := 0) (by norm_num) ha)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, Real.rpow_zero, Real.rpow_one, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
  ring

lemma integral_wt {a : ℝ} (ha : 0 < a) (ρ : NZ) :
    ∫ x in Ioi (0 : ℝ), wt x ρ.1 * (Real.exp (-(a * x)) : ℂ) =
      (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (Gamma ρ.1 * (1 / (a : ℂ)) ^ (ρ.1 + 2)) := by
  have h0 : ρ.1 ≠ 0 := fun h => by have := ρ.2.2.1; rw [h] at this; simp at this
  have h1 : ρ.1 + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith [ρ.2.2.1]
  have e : ∀ x : ℝ, wt x ρ.1 * (Real.exp (-(a * x)) : ℂ) =
      ((analyticOrderNatAt riemannZeta ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1))) *
        ((x : ℂ) ^ (ρ.1 + 2 - 1) * cexp (-((a : ℂ) * x))) := by
    intro x
    rw [show ρ.1 + 2 - 1 = ρ.1 + 1 by ring, ofReal_exp]
    push_cast
    unfold wt; ring
  simp_rw [e]
  rw [integral_const_mul, integral_cpow_mul_exp_neg_mul_Ioi (by simp; linarith [ρ.2.2.1]) ha]
  rw [show ρ.1 + 2 = ρ.1 + 1 + 1 by ring, Gamma_add_one _ h1, Gamma_add_one _ h0]
  push_cast
  field_simp

lemma integrable_wt {a : ℝ} (ha : 0 < a) (ρ : NZ) :
    Integrable (fun x : ℝ => wt x ρ.1 * (Real.exp (-(a * x)) : ℂ)) (volume.restrict (Ioi (0 : ℝ))) := by
  refine Integrable.mono' ((intOn_sq ha).mul_const (hw ρ.1)) ?_ ?_
  · exact ((continuous_wt ρ).mul (by fun_prop)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have := norm_wt_le (le_of_lt hx) ρ
    calc ‖wt x ρ.1‖ * Real.exp (-(a * x)) ≤ (x + 1) ^ 2 * hw ρ.1 * Real.exp (-(a * x)) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = (x + 1) ^ 2 * Real.exp (-(a * x)) * hw ρ.1 := by ring

lemma integral_W {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), W x * (Real.exp (-(a * x)) : ℂ) =
      ∑' ρ : NZ, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (Gamma ρ.1 * (1 / (a : ℂ)) ^ (ρ.1 + 2)) := by
  set C := ∫ x in Ioi (0 : ℝ), (x + 1) ^ 2 * Real.exp (-(a * x))
  have hsum : Summable fun ρ : NZ =>
      ∫ x in Ioi (0 : ℝ), ‖wt x ρ.1 * (Real.exp (-(a * x)) : ℂ)‖ := by
    refine Summable.of_nonneg_of_le (fun ρ => integral_nonneg fun x => norm_nonneg _)
      (fun ρ => ?_) (summable_hw_NZ.mul_left C)
    rw [← integral_mul_const]
    refine setIntegral_mono_on (integrable_wt ha ρ).norm ((intOn_sq ha).mul_const _)
      measurableSet_Ioi fun x hx => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc ‖wt x ρ.1‖ * Real.exp (-(a * x)) ≤ (x + 1) ^ 2 * hw ρ.1 * Real.exp (-(a * x)) :=
          mul_le_mul_of_nonneg_right (norm_wt_le (le_of_lt hx) ρ) (Real.exp_pos _).le
      _ = (x + 1) ^ 2 * Real.exp (-(a * x)) * hw ρ.1 := by ring
  have := integral_tsum_of_summable_integral_norm (integrable_wt ha) hsum
  simp_rw [integral_wt ha] at this
  rw [this]
  congr 1; funext x
  rw [W, tsum_mul_right]

/-! ### The remainder and the assembly -/

/-- `E(x) = ψ₁(x) - (x²/2 - x log 2π - W(x))`. -/
def Er (x : ℝ) : ℂ :=
  (psi1r x : ℂ) - ((x : ℂ) ^ 2 / 2 - x * Real.log (2 * Real.pi) - W x)

lemma psi1r_eq {x : ℝ} (hx : 0 < x) :
    (psi1r x : ℂ) = x * ∑' n : ℕ, (Λ n : ℂ) * PNTPort.ZetaZeros.w1 (n / x) := by
  rw [psi1r, ofReal_tsum, ← tsum_mul_left]
  congr 1; funext n
  unfold PNTPort.ZetaZeros.w1
  have : x * max 0 (1 - n / x) = max 0 (x - n) := by
    rw [mul_max_of_nonneg _ _ hx.le, mul_zero, mul_sub, mul_one, mul_div_cancel₀ _ hx.ne']
  rw [← this]; push_cast; ring

lemma xZ_eq {x : ℝ} (hx : 0 < x) : (x : ℂ) * ∑' ρ : NZ, zterm x ρ.1 = W x := by
  rw [W, ← tsum_mul_left]
  apply tsum_congr; intro ρ
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [zterm, wt]
  rw [cpow_add _ _ hx0, cpow_one]; ring

lemma Er_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → ‖Er x‖ ≤ K * x ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hK⟩ := explicit_formula_psi1_log2pi
  refine ⟨|K|, abs_nonneg K, fun x hx => ?_⟩
  have hb := hK x hx
  have e : Er x = (x : ℂ) * (∑' n : ℕ, (Λ n : ℂ) * PNTPort.ZetaZeros.w1 (n / x) -
      (x / 2 - Real.log (2 * Real.pi) -
        ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}, zterm x ρ.1)) := by
    rw [Er, psi1r_eq hx, ← xZ_eq hx]; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  have e2 : x * x ^ (-1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_one_add' hx.le (by norm_num)]; norm_num
  calc x * ‖_‖ ≤ x * (K * x ^ (-1 / 2 : ℝ)) := by gcongr
    _ ≤ x * (|K| * x ^ (-1 / 2 : ℝ)) := by
        gcongr; exact le_abs_self K
    _ = |K| * (x * x ^ (-1 / 2 : ℝ)) := by ring
    _ = |K| * x ^ (1 / 2 : ℝ) := by rw [e2]

lemma Er_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt Er x := by
  unfold Er
  have h1 : ContinuousAt (fun y : ℝ => (psi1r y : ℂ)) x :=
    (continuous_ofReal.comp psi1r_continuous).continuousAt
  have h2 := W_continuousAt hx
  exact h1.sub ((by fun_prop : ContinuousAt (fun y : ℝ =>
    (y : ℂ) ^ 2 / 2 - y * Real.log (2 * Real.pi)) x).sub h2)

lemma integrable_Er {a : ℝ} (ha : 0 < a) {K : ℝ}
    (hK : ∀ x : ℝ, 0 < x → ‖Er x‖ ≤ K * x ^ (1 / 2 : ℝ)) :
    Integrable (fun x : ℝ => Er x * (Real.exp (-(a * x)) : ℂ)) (volume.restrict (Ioi (0 : ℝ))) := by
  refine Integrable.mono' ((intOn_rpow (s := 1 / 2) (by norm_num) ha).const_mul K) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    exact ((Er_continuousAt hx).mul (by fun_prop)).continuousWithinAt
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc ‖Er x‖ * Real.exp (-(a * x)) ≤ K * x ^ (1 / 2 : ℝ) * Real.exp (-(a * x)) :=
          mul_le_mul_of_nonneg_right (hK x hx) (Real.exp_pos _).le
      _ = K * (x ^ (1 / 2 : ℝ) * Real.exp (-(a * x))) := by ring

lemma integral_poly {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), ((x : ℂ) ^ 2 / 2 - x * Real.log (2 * Real.pi)) * (Real.exp (-(a * x)) : ℂ) =
      1 / (a : ℂ) ^ 3 - Real.log (2 * Real.pi) / (a : ℂ) ^ 2 := by
  have e : ∀ x : ℝ, ((x : ℂ) ^ 2 / 2 - x * Real.log (2 * Real.pi)) * (Real.exp (-(a * x)) : ℂ) =
      (((1 / 2) * (x ^ (2 : ℝ) * Real.exp (-(a * x))) -
        Real.log (2 * Real.pi) * (x ^ (1 : ℝ) * Real.exp (-(a * x))) : ℝ) : ℂ) := by
    intro x
    rw [Real.rpow_one, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    push_cast; ring
  simp_rw [e]
  rw [integral_complex_ofReal, integral_sub ((intOn_rpow (by norm_num) ha).const_mul _)
    ((intOn_rpow (by norm_num) ha).const_mul _), integral_const_mul, integral_const_mul,
    integral_rpow (by norm_num) ha, integral_rpow (by norm_num) ha]
  rw [show (2 : ℝ) + 1 = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial,
    show (1 : ℝ) + 1 = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  rw [show ((2 : ℕ) : ℝ) + 1 = (3 : ℕ) by norm_num, show ((1 : ℕ) : ℝ) + 1 = (2 : ℕ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast]
  simp [Nat.factorial]
  field_simp

/-- **P0053 Lemma 1 at real `z`, corrected.** For every `a > 0`,
`|S̃(a) - (1/a - log 2π - Σ_ρ m(ρ) Γ(ρ) a^{-ρ})| ≤ K a^{1/2}`. Unconditional. -/
theorem stilde_real : ∃ K : ℝ, ∀ a : ℝ, 0 < a →
    ‖(St a : ℂ) - (1 / (a : ℂ) - Real.log (2 * Real.pi) -
      ∑' ρ : NZ, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (Gamma ρ.1 * (1 / (a : ℂ)) ^ ρ.1))‖
      ≤ K * a ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := Er_bound
  refine ⟨K * Real.Gamma (3 / 2), fun a ha => ?_⟩
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  -- the Laplace transform, split into its three parts
  have hpoly : IntegrableOn (fun x : ℝ => ((x : ℂ) ^ 2 / 2 - x * Real.log (2 * Real.pi)) *
      (Real.exp (-(a * x)) : ℂ)) (Ioi 0) := by
    refine Integrable.mono' (((intOn_rpow (s := 2) (by norm_num) ha).const_mul (1 / 2)).add
      ((intOn_rpow (s := 1) (by norm_num) ha).const_mul (Real.log (2 * Real.pi)))) ?_ ?_
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
      have hx0 : 0 < x := hx
      have hL : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
      simp only [Pi.add_apply]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Real.rpow_one, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
      have hn : ‖(x : ℂ) ^ 2 / 2 - x * Real.log (2 * Real.pi)‖ ≤ 1 / 2 * x ^ 2 +
          Real.log (2 * Real.pi) * x := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_div, norm_pow, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos hx0, abs_of_nonneg hL]
        norm_num; linarith
      calc ‖(x : ℂ) ^ 2 / 2 - x * Real.log (2 * Real.pi)‖ * Real.exp (-(a * x))
          ≤ (1 / 2 * x ^ 2 + Real.log (2 * Real.pi) * x) * Real.exp (-(a * x)) :=
            mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
        _ = _ := by ring
  have hWi : Integrable (fun x : ℝ => W x * (Real.exp (-(a * x)) : ℂ))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' ((intOn_sq ha).mul_const (∑' ρ : NZ, hw ρ.1)) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      exact ((W_continuousAt hx).mul (by fun_prop)).continuousWithinAt
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc ‖W x‖ * Real.exp (-(a * x)) ≤ (x + 1) ^ 2 * (∑' ρ : NZ, hw ρ.1) * Real.exp (-(a * x)) :=
            mul_le_mul_of_nonneg_right (norm_W_le (le_of_lt hx)) (Real.exp_pos _).le
        _ = (x + 1) ^ 2 * Real.exp (-(a * x)) * ∑' ρ : NZ, hw ρ.1 := by ring
  have hEi := integrable_Er ha hK
  have hsplit : ∀ x : ℝ, (psi1r x : ℂ) * (Real.exp (-(a * x)) : ℂ) =
      ((x : ℂ) ^ 2 / 2 - x * Real.log (2 * Real.pi)) * (Real.exp (-(a * x)) : ℂ) -
        W x * (Real.exp (-(a * x)) : ℂ) + Er x * (Real.exp (-(a * x)) : ℂ) := by
    intro x; unfold Er; ring
  have hSt : (St a : ℂ) = (a : ℂ) ^ 2 *
      ∫ x in Ioi (0 : ℝ), (psi1r x : ℂ) * (Real.exp (-(a * x)) : ℂ) := by
    rw [St_eq ha, ofReal_mul, ofReal_pow, ← integral_complex_ofReal]
    simp only [ofReal_mul]
  have hI : ∫ x in Ioi (0 : ℝ), (psi1r x : ℂ) * (Real.exp (-(a * x)) : ℂ) =
      (1 / (a : ℂ) ^ 3 - Real.log (2 * Real.pi) / (a : ℂ) ^ 2) -
        ∑' ρ : NZ, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
          (Gamma ρ.1 * (1 / (a : ℂ)) ^ (ρ.1 + 2)) +
        ∫ x in Ioi (0 : ℝ), Er x * (Real.exp (-(a * x)) : ℂ) := by
    simp_rw [hsplit]
    have h1 := integral_add (hpoly.sub hWi) hEi
    simp only [Pi.sub_apply] at h1
    rw [h1, integral_sub hpoly hWi, integral_poly ha, integral_W ha]
  -- `a² (1/a)^{ρ+2} = (1/a)^ρ`
  have hpow : ∀ ρ : ℂ, (a : ℂ) ^ 2 * (1 / (a : ℂ)) ^ (ρ + 2) = (1 / (a : ℂ)) ^ ρ := by
    intro ρ
    rw [cpow_add _ _ (one_div_ne_zero ha0), show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
    field_simp
  have hmain : (St a : ℂ) - (1 / (a : ℂ) - Real.log (2 * Real.pi) -
      ∑' ρ : NZ, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (Gamma ρ.1 * (1 / (a : ℂ)) ^ ρ.1)) =
      (a : ℂ) ^ 2 * ∫ x in Ioi (0 : ℝ), Er x * (Real.exp (-(a * x)) : ℂ) := by
    rw [hSt, hI, mul_add, mul_sub, ← tsum_mul_left]
    have e3 : ∀ ρ : NZ, (a : ℂ) ^ 2 * ((analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
        (Gamma ρ.1 * (1 / (a : ℂ)) ^ (ρ.1 + 2))) =
        (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (Gamma ρ.1 * (1 / (a : ℂ)) ^ ρ.1) := by
      intro ρ; rw [← hpow ρ.1]; ring
    simp_rw [e3]
    field_simp
    ring
  rw [hmain, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hb : ‖∫ x in Ioi (0 : ℝ), Er x * (Real.exp (-(a * x)) : ℂ)‖ ≤
      ∫ x in Ioi (0 : ℝ), K * (x ^ (1 / 2 : ℝ) * Real.exp (-(a * x))) := by
    refine norm_integral_le_of_norm_le ((intOn_rpow (by norm_num) ha).const_mul K) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc ‖Er x‖ * Real.exp (-(a * x)) ≤ K * x ^ (1 / 2 : ℝ) * Real.exp (-(a * x)) :=
          mul_le_mul_of_nonneg_right (hK x hx) (Real.exp_pos _).le
      _ = K * (x ^ (1 / 2 : ℝ) * Real.exp (-(a * x))) := by ring
  rw [integral_const_mul, integral_rpow (by norm_num) ha] at hb
  have hr : a ^ 2 * (1 / a) ^ ((1 / 2 : ℝ) + 1) = a ^ (1 / 2 : ℝ) := by
    rw [one_div, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le, ← Real.rpow_natCast,
      ← Real.rpow_add ha]
    norm_num
  calc a ^ 2 * ‖∫ x in Ioi (0 : ℝ), Er x * (Real.exp (-(a * x)) : ℂ)‖
      ≤ a ^ 2 * (K * ((1 / a) ^ ((1 / 2 : ℝ) + 1) * Real.Gamma (1 / 2 + 1))) := by gcongr
    _ = K * Real.Gamma (3 / 2) * (a ^ 2 * (1 / a) ^ ((1 / 2 : ℝ) + 1)) := by norm_num; ring
    _ = K * Real.Gamma (3 / 2) * a ^ (1 / 2 : ℝ) := by rw [hr]

/-- **Lemma 1 as printed, at `y = 0`**: `E(a, 0) ≪ |z|^{1/2} = a^{1/2}` for all `a > 0`, where
`E(a, 0) = S̃(a) - 1/a + Σ_ρ a^{-ρ} Γ(ρ)`, zeros with multiplicity. Kept as a `def`, not asserted. -/
def Lemma1PrintedReal : Prop :=
  ∃ C : ℝ, ∀ a : ℝ, 0 < a →
    ‖(St a : ℂ) - (1 / (a : ℂ) -
      ∑' ρ : NZ, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (Gamma ρ.1 * (1 / (a : ℂ)) ^ ρ.1))‖
      ≤ C * a ^ (1 / 2 : ℝ)

/-- **The printed Lemma 1 of P0053 is false**: `E(a, 0) → -log 2π`, not `0`, as `a → 0`. The
correction, `E ≪ 1 + |z|^{1/2}`, is Languasco's survey arXiv 1606.00860 §6. -/
theorem lemma1_printed_real_false : ¬ Lemma1PrintedReal := by
  rintro ⟨C, hC⟩
  obtain ⟨K, hK⟩ := stilde_real
  set L := Real.log (2 * Real.pi)
  have hL : 0 < L := Real.log_pos (by linarith [Real.pi_gt_three])
  set D := |C| + |K| + 1
  have hD : 0 < D := by positivity
  set a := (L / (2 * D)) ^ 2
  have ha : 0 < a := by positivity
  have hsa : a ^ (1 / 2 : ℝ) = L / (2 * D) := by
    rw [show a = (L / (2 * D)) ^ (2 : ℝ) by rw [Real.rpow_two], ← Real.rpow_mul (by positivity)]
    norm_num
  have h1 := hC a ha
  have h2 := hK a ha
  have e : -(L : ℂ) = ((St a : ℂ) - (1 / (a : ℂ) -
      ∑' ρ : NZ, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (Gamma ρ.1 * (1 / (a : ℂ)) ^ ρ.1))) -
      ((St a : ℂ) - (1 / (a : ℂ) - L -
      ∑' ρ : NZ, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (Gamma ρ.1 * (1 / (a : ℂ)) ^ ρ.1))) := by
    ring
  have h3 : L ≤ C * a ^ (1 / 2 : ℝ) + K * a ^ (1 / 2 : ℝ) := by
    have := norm_sub_le (((St a : ℂ) - (1 / (a : ℂ) -
      ∑' ρ : NZ, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (Gamma ρ.1 * (1 / (a : ℂ)) ^ ρ.1))))
      ((St a : ℂ) - (1 / (a : ℂ) - L -
      ∑' ρ : NZ, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (Gamma ρ.1 * (1 / (a : ℂ)) ^ ρ.1)))
    rw [← e, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL] at this
    linarith
  rw [hsa] at h3
  have h4 : C * (L / (2 * D)) + K * (L / (2 * D)) ≤ D * (L / (2 * D)) := by
    have hp : 0 ≤ L / (2 * D) := by positivity
    have : C + K ≤ D := by
      have := le_abs_self C; have := le_abs_self K; simp only [D]; linarith
    nlinarith
  have h5 : D * (L / (2 * D)) = L / 2 := by field_simp
  linarith

end LeanLab.GoldbachAverage.LZ2012
