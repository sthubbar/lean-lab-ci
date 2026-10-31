/-
T3 route R-5001, unit U-5026. The weighted Section 5 of Weighted.lean with any mean-square bound.
`goldbach_of_Jbound` is the reusable core: Theorem 3 style bounds `J_θ(s_j x, δ) ≤ B (s_j x)²`
at the 17 scales `s_j x` and `0.4036 B x² < δ² ((x/2)³ - (x/16)³)/3` force a Goldbach number in
`(x, x + δ x]`. `goldbach_log_of_PC` applies it to a hypothesis of pair-correlation strength,
`J_θ(X, δ) ≤ A δ log(1/δ) X²`, which is NOT known, even under RH; under it the interval
length drops from `log² x` to `9.71 A log x`. Goldston 1990 already gets `(2 + ε) log N` from such
input with a Fejér kernel; this is the explicit pairing version, a map entry, not progress on
Goldbach, which is open.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ChirreHagen2025.Weighted

namespace LeanLab.ChirreHagen2025
open Real Chebyshev

/-- The core of the weighted argument, for any bound `B` at the scales. -/
theorem goldbach_of_Jbound {x δ B : ℝ} (hδ : 0 < δ) (hx : 32 ≤ x) (hB : 0 ≤ B)
    (hJ : ∀ j, Jtheta (s16 j * x) δ ≤ B * (s16 j * x) ^ 2)
    (hc : B * x ^ 2 * 0.4036 < δ ^ 2 * ((x / 2) ^ 3 - (x / 16) ^ 3) / 3) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + δ * x := by
  by_contra hno
  have hlow := weighted_lower (x := x) (h := δ * x) s16 hδ le_rfl s16_mono
    (by simp [s16]) (fun j => by linarith [(s16_bounds j).2])
    (fun j => by nlinarith [(s16_bounds j).2]) hno 16
  have hs16 : s16 16 = 15 / 16 := by simp [s16]; norm_num
  rw [hs16, show (1 - 15 / 16 : ℝ) * x = x / 16 by ring] at hlow
  have hF1 : 0 ≤ ∫ y in (1 : ℝ)..x / 16, F δ y :=
    intervalIntegral.integral_nonneg (by linarith) (fun y _ => sq_nonneg _)
  have hGB : ∀ j, Gs δ x s16 j ≤ x ^ 2 * B * s16 j ^ 2 := by
    intro j
    have e : Jtheta (s16 j * x) δ = Gs δ x s16 j := rfl
    have := hJ j
    rw [e] at this
    calc Gs δ x s16 j ≤ B * (s16 j * x) ^ 2 := this
      _ = x ^ 2 * B * s16 j ^ 2 := by ring
  have hup := abelSum_mono (fun j => wt (s16 j)) (Gs δ x s16) (fun j => x ^ 2 * B * s16 j ^ 2)
    wt_antitone (fun j => sq_nonneg _) hGB 16
  have hfac : abelSum (fun j => wt (s16 j)) (fun j => x ^ 2 * B * s16 j ^ 2) 16
      = x ^ 2 * B * abelSum (fun j => wt (s16 j)) (fun j => s16 j ^ 2) 16 := by
    simp only [abelSum]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hfac] at hup
  have hxB : 0 ≤ x ^ 2 * B := by positivity
  have := mul_le_mul_of_nonneg_left U16_lt.le hxB
  linarith

/-- Under a pair-correlation strength mean-square bound `J_θ(X, δ) ≤ A δ log(1/δ) X²` for
`X ≥ X₀`, `0 < δ ≤ δ₀ ≤ 1`, a Goldbach number lies in `(x, x + 9.71 A log x]` whenever
`x ≥ 2 X₀`, `x ≥ 32`, `1 ≤ 9.71 A log x ≤ δ₀ x`. CONDITIONAL on that unproved bound. -/
theorem goldbach_log_of_PC {A X₀ δ₀ : ℝ} (hA : 0 < A) (hδ₀ : δ₀ ≤ 1)
    (hJ : ∀ X δ : ℝ, X₀ ≤ X → 0 < δ → δ ≤ δ₀ → Jtheta X δ ≤ A * δ * Real.log (1 / δ) * X ^ 2)
    {x : ℝ} (hx : 2 * X₀ ≤ x) (hx32 : 32 ≤ x) (h1 : 1 ≤ 9.71 * A * Real.log x)
    (hδ₀x : 9.71 * A * Real.log x ≤ δ₀ * x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 9.71 * A * Real.log x := by
  have hxpos : 0 < x := by linarith
  set h := 9.71 * A * Real.log x with hh
  set δ := h / x with hδ
  have hδpos : 0 < δ := by positivity
  have hδx : δ * x = h := by rw [hδ]; field_simp
  have hδle : δ ≤ δ₀ := by rw [hδ, div_le_iff₀ hxpos]; linarith
  -- `0 ≤ log(1/δ) ≤ log x`
  have hlog0 : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hδpos]; linarith
  have hlogx : Real.log (1 / δ) ≤ Real.log x := by
    apply Real.log_le_log (by positivity)
    rw [hδ, one_div_div, div_le_iff₀ (by linarith)]; nlinarith
  set B := A * δ * Real.log (1 / δ) with hBdef
  have hB : 0 ≤ B := by positivity
  have hJs : ∀ j, Jtheta (s16 j * x) δ ≤ B * (s16 j * x) ^ 2 := by
    intro j
    have hb := s16_bounds j
    have hX : X₀ ≤ s16 j * x := by nlinarith
    exact hJ _ δ hX hδpos hδle
  obtain ⟨n, hn, h1n, h2n⟩ := goldbach_of_Jbound hδpos hx32 hB hJs (by
    have e2 : δ ^ 2 * ((x / 2) ^ 3 - (x / 16) ^ 3) / 3
        = (δ * x ^ 2) * ((δ * x) * (1 / 8 - 1 / 4096) / 3) := by ring
    have e1 : B * x ^ 2 * 0.4036 = (δ * x ^ 2) * (A * 0.4036 * Real.log (1 / δ)) := by
      rw [hBdef]; ring
    rw [e1, e2]
    apply mul_lt_mul_of_pos_left _ (by positivity)
    rw [hδx, hh]
    have hL : 0 < Real.log x := by
      have := Real.log_lt_log (by norm_num) (show (1 : ℝ) < x by linarith)
      simpa using this
    nlinarith [mul_le_mul_of_nonneg_left hlogx hA.le])
  exact ⟨n, hn, h1n, by rw [← hδx]; exact h2n⟩

/-- Vacuity test for `goldbach_of_Jbound`'s numerical hypothesis: it can hold, e.g. with
`x = 64`, `δ = 1`, `B = 1`. -/
example : (1 : ℝ) * 64 ^ 2 * 0.4036 < 1 ^ 2 * ((64 / 2) ^ 3 - (64 / 16) ^ 3) / 3 := by norm_num

end LeanLab.ChirreHagen2025
