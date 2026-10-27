/-
Tao 2012, the cutoff `η₁` of (8.1) and two of its norms, with the printed step after
Proposition 8.3 that uses them. arXiv 1201.6656v4, Section 8, read 2026-10-18 by run
20261018T0503Z-16389 through Claude in Chrome.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.

(8.1) defines `η₁(t) = (1 - 10 dist(t, [0.2, 0.8]))₊`. The lab writes it in closed form,
`max 0 (min 1 (min (10 t - 1) (9 - 10 t)))`, which is the same function: 1 on [0.2, 0.8],
`10 t - 1` on [0.1, 0.2], `9 - 10 t` on [0.8, 0.9], and 0 elsewhere.
-/
import Mathlib

namespace LeanLab.Tao2012.Eta1
open intervalIntegral

/-- `η₁`, (8.1), in closed form. -/
noncomputable def η₁ (t : ℝ) : ℝ := max 0 (min 1 (min (10 * t - 1) (9 - 10 * t)))

theorem η₁_continuous : Continuous η₁ := by
  unfold η₁; fun_prop

/-- (8.1) symmetry: `η₁(1 - t) = η₁(t)`. MATCHES the paper. -/
theorem η₁_symm (t : ℝ) : η₁ (1 - t) = η₁ t := by
  unfold η₁
  rw [show 10 * (1 - t) - 1 = 9 - 10 * t by ring, show 9 - 10 * (1 - t) = 10 * t - 1 by ring,
    min_comm (9 - 10 * t)]

theorem η₁_zero_left {t : ℝ} (h : t ≤ 0.1) : η₁ t = 0 := by
  unfold η₁
  apply max_eq_left
  exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (by linarith))

theorem η₁_zero_right {t : ℝ} (h : 0.9 ≤ t) : η₁ t = 0 := by
  unfold η₁
  apply max_eq_left
  exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (by linarith))

theorem η₁_up {t : ℝ} (h1 : 0.1 ≤ t) (h2 : t ≤ 0.2) : η₁ t = 10 * t - 1 := by
  unfold η₁
  rw [min_eq_left (by linarith : 10 * t - 1 ≤ 9 - 10 * t), min_eq_right (by linarith),
    max_eq_right (by linarith)]

theorem η₁_flat {t : ℝ} (h1 : 0.2 ≤ t) (h2 : t ≤ 0.8) : η₁ t = 1 := by
  unfold η₁
  rw [min_eq_left (le_min (by linarith) (by linarith)), max_eq_right (by norm_num)]

theorem η₁_down {t : ℝ} (h1 : 0.8 ≤ t) (h2 : t ≤ 0.9) : η₁ t = 9 - 10 * t := by
  unfold η₁
  rw [min_eq_right (by linarith : 9 - 10 * t ≤ 10 * t - 1), min_eq_right (by linarith),
    max_eq_right (by linarith)]

/-- Integral of a function equal to `g` on `[a, b]`. -/
theorem integral_eq_on {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t, a ≤ t → t ≤ b → f t = g t) : ∫ t in a..b, f t = ∫ t in a..b, g t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact h t ht.1 ht.2

/-- Split `[0, 1]` at the four corners of `η₁`. -/
theorem split {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ t in (0 : ℝ)..1, f t = (∫ t in (0 : ℝ)..0.1, f t) + (∫ t in (0.1 : ℝ)..0.2, f t) +
      (∫ t in (0.2 : ℝ)..0.8, f t) + (∫ t in (0.8 : ℝ)..0.9, f t) +
      (∫ t in (0.9 : ℝ)..1, f t) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => hf.intervalIntegrable a b
  rw [integral_add_adjacent_intervals (hi 0 0.1) (hi 0.1 0.2),
    integral_add_adjacent_intervals (hi 0 0.2) (hi 0.2 0.8),
    integral_add_adjacent_intervals (hi 0 0.8) (hi 0.8 0.9),
    integral_add_adjacent_intervals (hi 0 0.9) (hi 0.9 1)]

/-- (8.4): `‖η₁‖₁ = 7/10`, the integral over `[0, 1]`, which holds the support. MATCHES. -/
theorem η₁_L1 : ∫ t in (0 : ℝ)..1, η₁ t = 7 / 10 := by
  rw [split η₁_continuous,
    integral_eq_on (by norm_num) (fun t _ h2 => η₁_zero_left h2),
    integral_eq_on (by norm_num) (fun t h1 h2 => η₁_up h1 h2),
    integral_eq_on (by norm_num) (fun t h1 h2 => η₁_flat h1 h2),
    integral_eq_on (by norm_num) (fun t h1 h2 => η₁_down h1 h2),
    integral_eq_on (by norm_num) (fun t h1 _ => η₁_zero_right h1)]
  simp [integral_sub, mul_comm]
  norm_num

/-- (8.2): `‖η₁‖₂² = 2/3`. MATCHES. -/
theorem η₁_L2sq : ∫ t in (0 : ℝ)..1, η₁ t ^ 2 = 2 / 3 := by
  have hi : ∀ (c : ℝ) (n : ℕ) (a b : ℝ),
      IntervalIntegrable (fun t : ℝ => c * t ^ n) MeasureTheory.volume a b :=
    fun c n a b => (continuous_const.mul (continuous_pow n)).intervalIntegrable a b
  have hq : ∀ c1 c2 a b : ℝ, ∫ t in a..b, (100 * t ^ 2 - c1 * t + c2) =
      100 * ((b ^ 3 - a ^ 3) / 3) - c1 * ((b ^ 2 - a ^ 2) / 2) + c2 * (b - a) := by
    intro c1 c2 a b
    have e1 : IntervalIntegrable (fun t : ℝ => c1 * t) MeasureTheory.volume a b := by
      simpa using hi c1 1 a b
    rw [integral_add ((hi 100 2 a b).sub e1) intervalIntegrable_const,
      integral_sub (hi 100 2 a b) e1, integral_const_mul, integral_const_mul, integral_pow,
      integral_id, integral_const]
    simp; ring
  have p0 : ∫ t in (0 : ℝ)..0.1, η₁ t ^ 2 = 0 := by
    rw [integral_eq_on (g := fun _ => (0 : ℝ)) (by norm_num)
      (fun t _ h2 => by simp [η₁_zero_left h2])]; simp
  have p1 : ∫ t in (0.1 : ℝ)..0.2, η₁ t ^ 2 = 1 / 30 := by
    rw [integral_eq_on (g := fun t => 100 * t ^ 2 - 20 * t + 1) (by norm_num)
      (fun t h1 h2 => by rw [η₁_up h1 h2]; ring), hq]; norm_num
  have p2 : ∫ t in (0.2 : ℝ)..0.8, η₁ t ^ 2 = 0.6 := by
    rw [integral_eq_on (g := fun _ => (1 : ℝ)) (by norm_num)
      (fun t h1 h2 => by simp [η₁_flat h1 h2])]; simp; norm_num
  have p3 : ∫ t in (0.8 : ℝ)..0.9, η₁ t ^ 2 = 1 / 30 := by
    rw [integral_eq_on (g := fun t => 100 * t ^ 2 - 180 * t + 81) (by norm_num)
      (fun t h1 h2 => by rw [η₁_down h1 h2]; ring), hq]; norm_num
  have p4 : ∫ t in (0.9 : ℝ)..1, η₁ t ^ 2 = 0 := by
    rw [integral_eq_on (g := fun _ => (0 : ℝ)) (by norm_num)
      (fun t h1 _ => by simp [η₁_zero_right h1])]; simp
  rw [split (f := fun t => η₁ t ^ 2) (η₁_continuous.pow 2), p0, p1, p2, p3, p4]
  norm_num

/-- The step after Proposition 8.3 at `t = 0`: `∫ η₁(s) η₁(1 - s) ds = ∫ η₁² = 2/3`. -/
theorem η₁_conv_zero : ∫ s in (0 : ℝ)..1, η₁ s * η₁ (1 - s) = 2 / 3 := by
  simp_rw [η₁_symm, ← pow_two]
  exact η₁_L2sq

/-- FINDING: the paper prints `∫ η₁(s) η₁(1 - s - t/K) ds = 1 + O*(10/K)` with `K = 10^3`;
at `t = 0` the integral is `2/3`, and `|2/3 - 1| > 10/K`. The right constant is `2/3`,
which is what Proposition 8.3 needs, so the main result is not affected. -/
theorem printed_conv_false :
    10 / (1000 : ℝ) < |(∫ s in (0 : ℝ)..1, η₁ s * η₁ (1 - s)) - 1| := by
  rw [η₁_conv_zero]; norm_num [abs_of_neg]

end LeanLab.Tao2012.Eta1
