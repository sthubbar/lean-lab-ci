/-
Shared input bridge, INPUTS.md rank 1: an explicit bound on Chebyshev's θ gives primes in short
windows. Elementary; uses Mathlib's `Chebyshev.theta`.
AI-written Lean code, Claude, run 20261018T2303Z-8776. Checked only by the Lean kernel.
-/
import Mathlib

open Finset Real

namespace LeanLab.Common.ThetaWindow

/-- If `θ` grows from `x` to `y`, there is a prime in `(x, y]`. -/
theorem exists_prime_of_theta_lt {x y : ℝ} (hx : 0 ≤ x) (h : Chebyshev.theta x < Chebyshev.theta y) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  by_contra hno
  push Not at hno
  have hxy : x ≤ y := by
    by_contra hlt
    push Not at hlt
    have := Chebyshev.theta_mono hlt.le
    linarith
  have heq : Chebyshev.theta y ≤ Chebyshev.theta x := by
    unfold Chebyshev.theta
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [mem_filter, mem_Ioc] at hp ⊢
      obtain ⟨⟨hp0, hpy⟩, hpp⟩ := hp
      refine ⟨⟨hp0, ?_⟩, hpp⟩
      have hy0 : 0 ≤ y := hx.trans hxy
      have hpyR : (p : ℝ) ≤ y := (Nat.le_floor_iff hy0).1 hpy
      have hpx : (p : ℝ) ≤ x := by
        by_contra hc
        push Not at hc
        exact absurd hpyR (not_le.mpr (hno p hpp hc))
      exact (Nat.le_floor_iff hx).2 hpx
    · intro p _ _
      exact Real.log_natCast_nonneg p
  linarith

/-- **The bridge**: if `|θ(t) - t| ≤ E t` for every `t ≥ x₀`, then for `x₀ ≤ x < y` with
`y - x > E x + E y` there is a prime in `(x, y]`. -/
theorem prime_window_of_theta_bound {E : ℝ → ℝ} {x0 : ℝ} (hx00 : 0 ≤ x0)
    (hθ : ∀ t, x0 ≤ t → |Chebyshev.theta t - t| ≤ E t) {x y : ℝ} (hx : x0 ≤ x) (hxy : x ≤ y)
    (hgap : E x + E y < y - x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  have ax := abs_le.mp (hθ x hx)
  have ay := abs_le.mp (hθ y (hx.trans hxy))
  exact exists_prime_of_theta_lt (hx00.trans hx) (by linarith [ax.2, ay.1])

/-- Relative form: if `|θ(t) - t| ≤ η t` for `t ≥ x₀` with `0 ≤ η < 1`, then for `x ≥ x₀`
and `δ > 2η/(1-η)` there is a prime in `(x, (1 + δ) x]`. -/
theorem prime_window_relative {η δ x0 : ℝ} (hx00 : 0 < x0) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hδ : 2 * η < δ * (1 - η))
    (hθ : ∀ t, x0 ≤ t → |Chebyshev.theta t - t| ≤ η * t) {x : ℝ} (hx : x0 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ (1 + δ) * x := by
  have hxpos : 0 < x := hx00.trans_le hx
  have hδ0 : 0 < δ := by
    by_contra h; push Not at h
    have : δ * (1 - η) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by linarith)
    linarith
  apply prime_window_of_theta_bound (E := fun t => η * t) hx00.le hθ hx (by nlinarith)
  have : 2 * η * x < δ * (1 - η) * x := mul_lt_mul_of_pos_right hδ hxpos
  nlinarith

end LeanLab.Common.ThetaWindow
