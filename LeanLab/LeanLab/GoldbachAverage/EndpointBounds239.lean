import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Elementary specialization of the remainder scale in BHMS page 7 Lemma 4,
https://arxiv.org/abs/1704.06103v2, at q one and T equal to x.
This does not supply the unsmoothed explicit formula.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.GoldbachAverage.EndpointBounds239

/-- On the endpoint window, the printed remainder scale is at most 51 log squared x. -/
theorem source_remainder_le (x u : ℝ) (hx : 2 ≤ x) (hu : u ∈ Set.Icc x (3 * x)) :
    Real.log 2 * Real.log u + (u / x) * Real.log (u * x) ^ 2 ≤
      51 * Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hu0 : 0 < u := by linarith [hu.1]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith [hu.1])
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hl3 : Real.log 3 ≤ 2 * Real.log x := by
    calc
      Real.log 3 ≤ Real.log (x * x) := Real.log_le_log (by norm_num) (by nlinarith)
      _ = 2 * Real.log x := by rw [Real.log_mul hx0.ne' hx0.ne']; ring
  have hlu3 : Real.log u ≤ 3 * Real.log x := by
    calc
      Real.log u ≤ Real.log (3 * x) := Real.log_le_log hu0 hu.2
      _ = Real.log 3 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ 3 * Real.log x := by linarith
  have hlprod0 : 0 ≤ Real.log (u * x) :=
    Real.log_nonneg (by nlinarith [hu.1])
  have hlprod : Real.log (u * x) ≤ 4 * Real.log x := by
    rw [Real.log_mul hu0.ne' hx0.ne']
    linarith
  have hs : Real.log (u * x) ^ 2 ≤ 16 * Real.log x ^ 2 := by
    have := pow_le_pow_left₀ hlprod0 hlprod 2
    nlinarith
  have hd : u / x ≤ 3 := (div_le_iff₀ hx0).mpr (by linarith [hu.2])
  have hfirst : Real.log 2 * Real.log u ≤ 3 * Real.log x ^ 2 := by
    nlinarith [mul_le_mul hl2 hlu3 hlu hlx]
  have hsecond : (u / x) * Real.log (u * x) ^ 2 ≤ 48 * Real.log x ^ 2 := by
    nlinarith [mul_le_mul hd hs (sq_nonneg (Real.log (u * x))) (by norm_num : (0 : ℝ) ≤ 3)]
  linarith

/-- A uniform source remainder gives the endpoint window bound.
CONDITIONAL ON the displayed source remainder estimate. -/
theorem endpoint_bound_of_source_remainder (E : ℝ → ℝ → ℂ)
    (h : ∃ A : ℂ, ∃ K : ℝ, 0 ≤ K ∧ ∀ T u : ℝ,
      2 ≤ T → 2 ≤ u →
        ‖E T u - A‖ ≤
          K * (Real.log 2 * Real.log u + (u / T) * Real.log (u * T) ^ 2)) :
    ∃ A : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x u : ℝ,
      2 ≤ x → u ∈ Set.Icc x (3 * x) →
        ‖E x u - A‖ ≤ C * Real.log x ^ 2 := by
  obtain ⟨A, K, hK, hE⟩ := h
  refine ⟨A, 51 * K, by positivity, ?_⟩
  intro x u hx hu
  calc
    ‖E x u - A‖ ≤
        K * (Real.log 2 * Real.log u + (u / x) * Real.log (u * x) ^ 2) :=
      hE x u hx (hx.trans hu.1)
    _ ≤ K * (51 * Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_left (source_remainder_le x u hx hu) hK
    _ = (51 * K) * Real.log x ^ 2 := by ring

end LeanLab.GoldbachAverage.EndpointBounds239
