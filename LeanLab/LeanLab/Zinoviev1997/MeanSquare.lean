/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261019T2314Z-cloud29, unit U-5791, paper P0097.

# Zinoviev 1997, (3.17) with Lemma 1.5: the mean square of the smoothed prime sum

`S_M(α) = Σ_{1 ≤ n ≤ M} Λ(n) e^{-n/N} e(nα)`, the truncations of Zinoviev's `S`, p. 335, up to the
sign of `α`, which does not change `∫₀¹ |S|²`. `mean_square_le`: for every natural `N ≥ 10^20` and
every `M`, `∫₀¹ |S_M(α)|² dα ≤ 0.96 N ln N`, by Parseval, `Common.CircleOrth.parseval_norm`, and
`lemma15`. This is the bound (3.16) and (3.17) feed into Theorem 3.4, PROVED unconditional, for the
full prime power sum that Parseval gives. Binary Goldbach is OPEN.
-/
import LeanLab.Zinoviev1997.Lemma15
import LeanLab.Common.CircleOrth

namespace LeanLab.Zinoviev1997
open Real Finset ArithmeticFunction LeanLab.CircleOrth

/-- The coefficients `Λ(n) e^{-n/N}` on `ℤ`. -/
noncomputable def coef (N : ℕ) (n : ℤ) : ℂ := ((Λ n.toNat * Real.exp (-n / N) : ℝ) : ℂ)

/-- The frequencies `1, …, M` in `ℤ`. -/
def freqs (M : ℕ) : Finset ℤ := (Icc 1 M).map Nat.castEmbedding

theorem coef_sq (N n : ℕ) :
    ‖coef N (n : ℤ)‖ ^ 2 = Λ n ^ 2 * Real.exp (-2 * n / N) := by
  unfold coef
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Int.toNat_natCast, mul_pow, ← Real.exp_nat_mul]
  congr 2; push_cast; ring

/-- **Mean square**, (3.17) with Lemma 1.5: `∫₀¹ |S_M(α)|² dα ≤ 0.96 N ln N`. -/
theorem mean_square_le (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) (M : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖LeanLab.CircleOrth.S (freqs M) (coef N) α‖ ^ 2 ≤ 0.96 * N * Real.log N := by
  rw [parseval_norm, freqs, Finset.sum_map]
  simp only [Nat.castEmbedding_apply]
  simp_rw [coef_sq]
  exact lemma15 N hN M

end LeanLab.Zinoviev1997
