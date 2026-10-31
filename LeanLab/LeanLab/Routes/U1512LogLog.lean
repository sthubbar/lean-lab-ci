/-
Unit U-1512, T3 MOONSHOT, run PC 20261025T0803Z-22023. AI-written Lean code, Claude.
Checked only by the Lean kernel. KNOWN mathematics in substance: Goldston 1990, Glasgow Math. J.
32, gets `[N, N + (2 + ε) log N]` under RH and `J(N,h) ~ h N log(N/h)`, a form of Montgomery's
pair correlation conjecture. Binary Goldbach is OPEN; nothing here is progress on it.

Route R-5001 interpolated: a pair correlation strength mean square WITH A LOSS FACTOR `Φ`,
`J_θ(X, δ) ≤ A δ log(1/δ) Φ(1/δ) X²`, named `PCLoss`, gives a Goldbach number in
`(x, x + 9.71 A Φ(x) log x]`. With `Φ = max 1 (log log)` this is `O(log x log log x)`,
which is `o(log² x)` by `loglog_isLittleO`. RH alone gives only `Φ ≍ log`, Selberg's bound.

* `goldbach_of_Mbound`: the weighted Section 5 core at `δ = 9.71 A M / x` for any `M`. PROVED,
  as an implication from the mean-square hypothesis at the 17 scales.
* `goldbach_of_PCLoss`: CONDITIONAL ON `PCLoss Φ A X₀ δ₀`.
* `goldbach_loglog`: CONDITIONAL ON `PCLoss phiLL A X₀ δ₀`.
* `loglog_isLittleO`: `log x · log log x = o(log² x)`. PROVED.
-/
import Mathlib
import LeanLab.ChirreHagen2025.PairCorr

namespace LeanLab.Routes.U1512
open Real Chebyshev Filter Asymptotics
open LeanLab.ChirreHagen2025

/-- The weighted core with an arbitrary size parameter `M` in place of `log x`. -/
theorem goldbach_of_Mbound {A M x : ℝ} (hA : 0 < A) (hM : 0 < M) (hx32 : 32 ≤ x)
    (hJ : ∀ j, Jtheta (s16 j * x) (9.71 * A * M / x)
      ≤ A * (9.71 * A * M / x) * M * (s16 j * x) ^ 2) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 9.71 * A * M := by
  have hxpos : 0 < x := by linarith
  set h := 9.71 * A * M with hh
  set δ := h / x with hδ
  have hδpos : 0 < δ := by positivity
  have hδx : δ * x = h := by rw [hδ]; field_simp
  set B := A * δ * M with hBdef
  have hB : 0 ≤ B := by positivity
  obtain ⟨n, hn, h1n, h2n⟩ := goldbach_of_Jbound hδpos hx32 hB hJ (by
    have e2 : δ ^ 2 * ((x / 2) ^ 3 - (x / 16) ^ 3) / 3
        = (δ * x ^ 2) * ((δ * x) * (1 / 8 - 1 / 4096) / 3) := by ring
    have e1 : B * x ^ 2 * 0.4036 = (δ * x ^ 2) * (A * 0.4036 * M) := by
      rw [hBdef]; ring
    rw [e1, e2]
    apply mul_lt_mul_of_pos_left _ (by positivity)
    rw [hδx, hh]
    have : 0 < A * M := mul_pos hA hM
    nlinarith)
  exact ⟨n, hn, h1n, by rw [← hδx]; exact h2n⟩

/-- CONDITIONAL INPUT, unproved: a pair correlation strength mean square with loss `Φ`. For
`Φ = 1` this is the hypothesis of `goldbach_log_of_PC`, of the strength of Montgomery's pair
correlation conjecture under RH; for `Φ ≍ log` it is Selberg's bound under RH. -/
def PCLoss (Φ : ℝ → ℝ) (A X₀ δ₀ : ℝ) : Prop :=
  ∀ X δ : ℝ, X₀ ≤ X → 0 < δ → δ ≤ δ₀ →
    Jtheta X δ ≤ A * δ * (Real.log (1 / δ) * Φ (1 / δ)) * X ^ 2

/-- CONDITIONAL ON `PCLoss Φ A X₀ δ₀`: a Goldbach number in `(x, x + 9.71 A Φ(x) log x]`. -/
theorem goldbach_of_PCLoss {Φ : ℝ → ℝ} {A X₀ δ₀ : ℝ} (hA : 0 < A) (hδ₀ : δ₀ ≤ 1)
    (hΦ0 : ∀ t, 1 ≤ t → 0 < Φ t) (hΦm : ∀ s t, 1 ≤ s → s ≤ t → Φ s ≤ Φ t)
    (hPC : PCLoss Φ A X₀ δ₀) {x : ℝ} (hx : 2 * X₀ ≤ x) (hx32 : 32 ≤ x)
    (h1 : 1 ≤ 9.71 * A * (Real.log x * Φ x))
    (hδ₀x : 9.71 * A * (Real.log x * Φ x) ≤ δ₀ * x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 9.71 * A * (Real.log x * Φ x) := by
  have hxpos : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hΦx : 0 < Φ x := hΦ0 x (by linarith)
  set M := Real.log x * Φ x with hMdef
  have hM : 0 < M := mul_pos hL hΦx
  apply goldbach_of_Mbound hA hM hx32
  intro j
  set δ := 9.71 * A * M / x with hδ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ δ₀ := by rw [hδ, div_le_iff₀ hxpos]; linarith
  have hinv1 : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδpos, one_mul]; linarith
  have hinvx : 1 / δ ≤ x := by
    rw [hδ, one_div_div, div_le_iff₀ (by positivity)]; nlinarith
  have hlog0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg hinv1
  have hlogx : Real.log (1 / δ) ≤ Real.log x := Real.log_le_log (by linarith) hinvx
  have hΦle : Φ (1 / δ) ≤ Φ x := hΦm _ _ hinv1 hinvx
  have hΦd : 0 < Φ (1 / δ) := hΦ0 _ hinv1
  have hb := s16_bounds j
  have hX : X₀ ≤ s16 j * x := by nlinarith
  have hJ := hPC _ δ hX hδpos hδle
  have hprod : Real.log (1 / δ) * Φ (1 / δ) ≤ M :=
    mul_le_mul hlogx hΦle hΦd.le hL.le
  refine le_trans hJ ?_
  have : 0 ≤ A * δ := by positivity
  have hsq : 0 ≤ (s16 j * x) ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod this) hsq
  linarith

/-- The loss factor `max 1 (log log t)`. -/
noncomputable def phiLL (t : ℝ) : ℝ := max 1 (Real.log (Real.log t))

theorem phiLL_pos (t : ℝ) : 0 < phiLL t := lt_of_lt_of_le one_pos (le_max_left _ _)

theorem phiLL_mono {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) : phiLL s ≤ phiLL t := by
  unfold phiLL
  rcases eq_or_lt_of_le hs with h | h
  · have h0 : Real.log (Real.log s) = 0 := by rw [← h]; simp
    exact max_le (le_max_left _ _) (by rw [h0]; exact zero_le_one.trans (le_max_left _ _))
  · apply max_le_max le_rfl
    apply Real.log_le_log (Real.log_pos h) (Real.log_le_log (by linarith) hst)

/-- CONDITIONAL ON `PCLoss phiLL A X₀ δ₀`: Goldbach numbers in intervals of length
`9.71 A log x · max 1 (log log x)`, which is `o(log² x)`. -/
theorem goldbach_loglog {A X₀ δ₀ : ℝ} (hA : 0 < A) (hδ₀ : δ₀ ≤ 1) (hPC : PCLoss phiLL A X₀ δ₀)
    {x : ℝ} (hx : 2 * X₀ ≤ x) (hx32 : 32 ≤ x)
    (h1 : 1 ≤ 9.71 * A * (Real.log x * phiLL x))
    (hδ₀x : 9.71 * A * (Real.log x * phiLL x) ≤ δ₀ * x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 9.71 * A * (Real.log x * phiLL x) :=
  goldbach_of_PCLoss hA hδ₀ (fun t _ => phiLL_pos t) (fun _ _ hs hst => phiLL_mono hs hst)
    hPC hx hx32 h1 hδ₀x

/-- `log x · max 1 (log log x) = o(log² x)`, so `goldbach_loglog` beats the order `log² x`. -/
theorem loglog_isLittleO :
    (fun x : ℝ => Real.log x * phiLL x) =o[atTop] (fun x : ℝ => Real.log x ^ 2) := by
  have hll : (fun x : ℝ => phiLL x) =o[atTop] (fun x : ℝ => Real.log x) := by
    have h1 : (fun x : ℝ => Real.log (Real.log x)) =o[atTop] (fun x : ℝ => Real.log x) :=
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    have h2 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] (fun x : ℝ => Real.log x) :=
      (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto Real.tendsto_log_atTop
    refine IsLittleO.of_bound fun c hc => ?_
    filter_upwards [h1.bound hc, h2.bound hc] with x hx1 hx2
    unfold phiLL
    rcases le_total 1 (Real.log (Real.log x)) with h | h
    · rw [max_eq_right h]; exact hx1
    · rw [max_eq_left h]; exact hx2
  have := (isBigO_refl (fun x : ℝ => Real.log x) atTop).mul_isLittleO hll
  simpa [pow_two] using this

/-- Vacuity check for `goldbach_of_Mbound`'s arithmetic: with `A = 1`, `M = 1`, `x = 64`, the
step `δ = 9.71/64` is a positive real at most `1`. -/
example : (0 : ℝ) < 9.71 * 1 * 1 / 64 ∧ 9.71 * 1 * 1 / 64 ≤ (1 : ℝ) := by norm_num

end LeanLab.Routes.U1512
