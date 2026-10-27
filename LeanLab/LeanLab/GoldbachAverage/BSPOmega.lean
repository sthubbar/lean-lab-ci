/-
P0050 Bhowmik and Schlage-Puchta 2010, arXiv 0806.3295v3, Theorem 1.1, the Ω part, read
2026-10-17: "Suppose that the RH is true. Then Σ_{n ≤ x} G(n) = x²/2 + H(x) + Ω(x log log x)",
H(x) = −2 Σ_ρ x^{1+ρ}/(ρ(1+ρ)); the paper explains Ω as: the error cannot be o(x log log x).
Read here over integers N: our reading, not the paper's. Under RH, x²/2 moves by O(x) and H(x)
by O(x^{1/2} log² x) between x and ⌊x⌋, by splitting the zero sum at height x, so the two forms
agree; that argument is not formalized. Cited with `sorry`.
PROVED, zero sorry: under this Ω result the error E(N) is not O(N); so the Languasco-Zaccagnini
O(N log³ N) and the paper's O(N log⁵ N) cannot be improved to O(N).
AI-written Lean code, Claude, run 20261017T0903Z-2557. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.GoldbachAverage.Links

open Filter

noncomputable section
namespace LeanLab.GoldbachAverage

/-- The error is `o(N log log N)`. -/
def ErrSmallO : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → E N ≤ ε * N * Real.log (Real.log N)

/-- **Bhowmik-Schlage-Puchta Theorem 1.1, Ω part**, cited: under RH the error is not
`o(N log log N)`. -/
theorem bsp_omega : RiemannHypothesis → ¬ ErrSmallO := by sorry

/-- An `O(N)` error would be `o(N log log N)`. -/
theorem errSmallO_of_linear (h : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → E N ≤ K * N) : ErrSmallO := by
  obtain ⟨K, hK⟩ := h
  intro ε hε
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (hll.eventually_ge_atTop (|K| / ε))
  refine ⟨max N1 2, fun N hN => ?_⟩
  have h2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hl := hN1 N (le_trans (le_max_left _ _) hN)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hKe : |K| ≤ ε * Real.log (Real.log N) := by
    rw [div_le_iff₀ hε] at hl; linarith
  calc E N ≤ K * N := hK N h2
    _ ≤ |K| * N := mul_le_mul_of_nonneg_right (le_abs_self K) hN0
    _ ≤ ε * Real.log (Real.log N) * N := mul_le_mul_of_nonneg_right hKe hN0
    _ = ε * N * Real.log (Real.log N) := by ring

/-- **Under RH and the cited Ω result, the error is not `O(N)`**, zero sorry beyond the
citation. -/
theorem not_linear_of_bsp_omega (hO : ¬ ErrSmallO) :
    ¬ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → E N ≤ K * N :=
  fun h => hO (errSmallO_of_linear h)

theorem not_linear_of_RH (hRH : RiemannHypothesis) :
    ¬ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → E N ≤ K * N :=
  not_linear_of_bsp_omega (bsp_omega hRH)

end LeanLab.GoldbachAverage
