/-
U-1578, PC 20261027T1215Z-9234, T3 CONNECTION SWEEP, idea I-0137.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here is progress on it.

Connection: Perelli 1996, P0083, Rev. Mat. Iberoam. 12, uses Huxley's zero density
exponent A = 12/5 in its display (21) only through the sup in display (25),
  sup over 1/2 ≤ σ < 1 of N^{2σ-1} · (N/𝔔)^{A(1-σ)},
with 𝔔 = H^{k/2} for Theorem 1 and Q = H^k for Theorem 2, display (32).
The sup is below N^{1-δ} iff A · c < 2, c the exponent of the zero counting base.
This is the template of Bhowmik-Grimmelt, P0029, Theorem 6.2, θ > 1 - 2/A.
Chen arXiv 2507.08296 gives A = 7/3 for Σ_{χ mod q} N(σ,T,χ), uniformly in q.
So Perelli's ranges N^{1/(3k)} and N^{1/(6k)} become N^{2/(7k)} and N^{1/(7k)}.

This file proves the exponent arithmetic; the analytic statement is CONDITIONAL.
-/
import Mathlib

namespace LeanLab.Routes.U1578

/-- Theorem 1 threshold for h, where H = N^h: h > 2(1 - 2/A)/k. -/
noncomputable def thr1 (A k : ℝ) : ℝ := 2 * (1 - 2 / A) / k

/-- Theorem 2 threshold: h > (1 - 2/A)/k. -/
noncomputable def thr2 (A k : ℝ) : ℝ := (1 - 2 / A) / k

/-- The exponent of N in Perelli's display (25) at abscissa σ. -/
def expo (A c σ : ℝ) : ℝ := (2 * σ - 1) + A * c * (1 - σ)

/-- Plain math: 2σ - 1 + A c (1 - σ) = 1 - (2 - A c)(1 - σ). -/
theorem expo_eq (A c σ : ℝ) : expo A c σ = 1 - (2 - A * c) * (1 - σ) := by
  unfold expo; ring

/-- Plain math: if A c < 2 then for every σ ≤ 1 - η, η > 0, the exponent is at most
1 - (2 - A c) η, a uniform power saving. PROVED. -/
theorem expo_saving {A c σ η : ℝ} (hAc : A * c < 2) (hσ : σ ≤ 1 - η) :
    expo A c σ ≤ 1 - (2 - A * c) * η := by
  rw [expo_eq]
  have h1 : η ≤ 1 - σ := by linarith
  have h2 : 0 < 2 - A * c := by linarith
  nlinarith

/-- Plain math: if A c ≥ 2 the exponent is at least 1 for every σ ≤ 1, so no saving.
PROVED; this is the sharpness of the condition. -/
theorem expo_no_saving {A c σ : ℝ} (hAc : 2 ≤ A * c) (hσ : σ ≤ 1) :
    1 ≤ expo A c σ := by
  rw [expo_eq]; nlinarith

/-- Plain math, Theorem 1 geometry: for A, k > 0 and h > thr1 A k, the base
exponent c = 1 - k h / 2 of N/𝔔, 𝔔 = H^{k/2}, satisfies A c < 2. PROVED. -/
theorem thm1_condition {A k h : ℝ} (hA : 0 < A) (hk : 0 < k) (hh : thr1 A k < h) :
    A * (1 - k * h / 2) < 2 := by
  unfold thr1 at hh
  rw [div_lt_iff₀ hk] at hh
  have : A * (2 * (1 - 2 / A)) = 2 * A - 4 := by field_simp; ring
  nlinarith

/-- Plain math, Theorem 2 geometry: h > thr2 A k gives A (1 - k h) < 2. PROVED. -/
theorem thm2_condition {A k h : ℝ} (hA : 0 < A) (hk : 0 < k) (hh : thr2 A k < h) :
    A * (1 - k * h) < 2 := by
  unfold thr2 at hh
  rw [div_lt_iff₀ hk] at hh
  have : A * (1 - 2 / A) = A - 2 := by field_simp
  nlinarith

/-- Huxley 12/5 reproduces Perelli's printed ranges 1/(3k) and 1/(6k). PROVED. -/
theorem huxley_reproduces (k : ℝ) :
    thr1 (12 / 5) k = 1 / (3 * k) ∧ thr2 (12 / 5) k = 1 / (6 * k) := by
  unfold thr1 thr2
  by_cases hk : k = 0
  · simp [hk]
  · constructor <;> (field_simp; ring)

/-- Chen's 7/3 gives 2/(7k) and 1/(7k). PROVED. -/
theorem chen_values (k : ℝ) :
    thr1 (7 / 3) k = 2 / (7 * k) ∧ thr2 (7 / 3) k = 1 / (7 * k) := by
  unfold thr1 thr2
  by_cases hk : k = 0
  · simp [hk]
  · constructor <;> (field_simp; ring)

/-- Guth-Maynard's 30/13, known only for q = 1, would give 4/(15k) and 2/(15k). PROVED
as arithmetic. -/
theorem gm_values (k : ℝ) :
    thr1 (30 / 13) k = 4 / (15 * k) ∧ thr2 (30 / 13) k = 2 / (15 * k) := by
  unfold thr1 thr2
  by_cases hk : k = 0
  · simp [hk]
  · constructor <;> (field_simp; ring)

/-- The new ranges are strictly wider for every degree k ≥ 1. PROVED. -/
theorem chen_beats_huxley {k : ℝ} (hk : 0 < k) :
    2 / (7 * k) < 1 / (3 * k) ∧ 1 / (7 * k) < 1 / (6 * k) := by
  constructor
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith

/-- The analytic content, stated abstractly. `DensityInput A` stands for
Σ_{χ mod q} N(σ,T,χ) ≪ (qT)^{A(1-σ)+ε} for q ≤ (log T)^C, together with a log-free
bound near σ = 1 that covers the T^ε. `PerelliThm1 k h` stands for Perelli's
mean square Σ |R(F(n)) - F(n)𝔖(F(n))|² ≪ H N² L^{-A'} for H = N^{h}.
`PerelliTemplate` is the reading that Perelli's proof uses A only through the sup of
display (25): density A and A(1 - k h/2) < 2 give Theorem 1 at h. -/
def PerelliTemplate (DensityInput : ℝ → Prop) (PerelliThm1 : ℝ → ℝ → Prop) : Prop :=
  ∀ A k h : ℝ, 0 < A → 0 < k → DensityInput A → A * (1 - k * h / 2) < 2 → PerelliThm1 k h

/-- CONDITIONAL ON PerelliTemplate and DensityInput (7/3), Chen 2507.08296:
Perelli's Theorem 1 holds for every H = N^h with h > 2/(7k). -/
theorem perelli_thm1_chen (DensityInput : ℝ → Prop) (PerelliThm1 : ℝ → ℝ → Prop)
    (hT : PerelliTemplate DensityInput PerelliThm1) (hD : DensityInput (7 / 3))
    {k h : ℝ} (hk : 0 < k) (hh : 2 / (7 * k) < h) : PerelliThm1 k h := by
  apply hT (7 / 3) k h (by norm_num) hk hD
  apply thm1_condition (by norm_num) hk
  rw [(chen_values k).1]; exact hh

/-- Vacuity: the saving lemma fires with a real margin at A = 7/3, c = 1 - 0.29/2,
σ = 5/7, η = 2/7: exponent at most 1 - 0.0024 η. -/
theorem saving_vacuity :
    (7 / 3 : ℝ) * (1 - 1 * (29 / 100) / 2) < 2 ∧
      expo (7 / 3) (1 - 1 * (29 / 100) / 2) (5 / 7) < 1 := by
  constructor
  · norm_num
  · unfold expo; norm_num

/-- Vacuity of the conditional: with the trivially true props the hypotheses hold and
the conclusion is reached at k = 1, h = 0.29 > 2/7. -/
theorem conditional_vacuity : (fun (_ _ : ℝ) => True) 1 (29 / 100) := perelli_thm1_chen (fun _ => True) (fun _ _ => True)
    (fun _ _ _ _ _ _ _ => trivial) trivial (k := 1) (h := 29 / 100) one_pos (by norm_num)

/-- Vacuity of the sharpness lemma: at Huxley's A = 12/5 and h = 0.29 < 1/3, k = 1,
the condition fails, so Huxley could not give h = 0.29. -/
theorem sharp_vacuity : 2 ≤ (12 / 5 : ℝ) * (1 - 1 * (29 / 100) / 2) := by norm_num

end LeanLab.Routes.U1578
