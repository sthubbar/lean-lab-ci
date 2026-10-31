/-
P0071 Languasco and Perelli 1996, Lemma 1, page 354, read from the page images of
papers/P0071.pdf. Unit U-5095, CLOUD 20261019T0213Z-cloud14.

Lemma 1: `∫_{αX}^{βX} |Σ_χ χ(a)τ(χ̄) Σ_{|γ|≤T} y^{iγ}|² dy ≪ X F(X, T; q, a)`, by `y = Xe^v` and (11),
`F = ∫ |Σ(X, T, v)|² e^{-2|v|} dv`, for constants `0 < c ≤ α < β ≤ C`.
PROVED, in abstract form for any continuous `g ≥ 0` standing for the integrand:
`subst`, `∫_{αX}^{βX} g(y) dy = X ∫_{log α}^{log β} g(Xe^v) e^v dv`; `exp_le`, `e^v ≤ e^{3K} e^{-2|v|}`
for `|v| ≤ K`; `lemma1`, `∫_{αX}^{βX} g ≤ e^{3K} X ∫_{log α}^{log β} g(Xe^v) e^{-2|v|} dv` with
`K = max(|log α|, |log β|)`, the implied constant depending only on `c, C`, as the paper's
`α, β` do. With `g(y) = |Σ y^{iγ}|²`, `g(Xe^v) = |Σ(X, T, v)|²`, and the last integral is at most
`F` by (11). MATCH. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.LanguascoPerelli1996.Lemma1
open Real intervalIntegral

theorem subst {g : ℝ → ℝ} (hg : Continuous g) {X α β : ℝ} (hX : 0 < X) (hα : 0 < α) (hβ : 0 < β) :
    ∫ y in α * X..β * X, g y = X * ∫ v in Real.log α..Real.log β, g (X * Real.exp v) * Real.exp v := by
  have hd : ∀ v ∈ Set.uIcc (Real.log α) (Real.log β),
      HasDerivAt (fun v => X * Real.exp v) (X * Real.exp v) v :=
    fun v _ => (Real.hasDerivAt_exp v).const_mul X
  have hc : ContinuousOn (fun v => X * Real.exp v) (Set.uIcc (Real.log α) (Real.log β)) :=
    (continuous_const.mul Real.continuous_exp).continuousOn
  have key := integral_comp_mul_deriv hd hc hg
  simp only [Function.comp, Real.exp_log hα, Real.exp_log hβ] at key
  rw [mul_comm α X, mul_comm β X, ← key, ← integral_const_mul]
  congr 1; ext v; ring

theorem exp_le {v K : ℝ} (hv : |v| ≤ K) : Real.exp v ≤ Real.exp (3 * K) * Real.exp (-2 * |v|) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := le_abs_self v
  linarith

theorem lemma1 {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ y, 0 ≤ g y) {X α β : ℝ} (hX : 0 < X)
    (hα : 0 < α) (hαβ : α ≤ β) :
    ∫ y in α * X..β * X, g y ≤
      Real.exp (3 * max |Real.log α| |Real.log β|) * X *
        ∫ v in Real.log α..Real.log β, g (X * Real.exp v) * Real.exp (-2 * |v|) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  rw [subst hg hX hα hβ]
  set K := max |Real.log α| |Real.log β|
  have hle : Real.log α ≤ Real.log β := Real.log_le_log hα hαβ
  have hcont1 : Continuous fun v => g (X * Real.exp v) * Real.exp v :=
    (hg.comp (continuous_const.mul Real.continuous_exp)).mul Real.continuous_exp
  have hcont2 : Continuous fun v => g (X * Real.exp v) * Real.exp (-2 * |v|) :=
    (hg.comp (continuous_const.mul Real.continuous_exp)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
  have hmono : ∫ v in Real.log α..Real.log β, g (X * Real.exp v) * Real.exp v ≤
      ∫ v in Real.log α..Real.log β, Real.exp (3 * K) * (g (X * Real.exp v) * Real.exp (-2 * |v|)) := by
    apply integral_mono_on hle (hcont1.intervalIntegrable _ _)
      ((hcont2.intervalIntegrable _ _).const_mul _)
    intro v hv
    have hvK : |v| ≤ K := by
      rw [abs_le]
      constructor
      · have : -K ≤ Real.log α := by
          have := neg_abs_le (Real.log α); have := le_max_left |Real.log α| |Real.log β|; linarith
        linarith [hv.1]
      · have : Real.log β ≤ K := le_trans (le_abs_self _) (le_max_right _ _)
        linarith [hv.2]
    have := exp_le hvK
    have h0 := hg0 (X * Real.exp v)
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  rw [integral_const_mul] at hmono
  have hX' : 0 ≤ X := hX.le
  nlinarith [mul_le_mul_of_nonneg_left hmono hX']

end LeanLab.LanguascoPerelli1996.Lemma1
