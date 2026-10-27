/-
P0075, unit U-6363, track T1, CLOUD 20261020T1125Z-cloud41, 2026-10-20.
The paper's Theorem 1, a Goldbach number in `(x, x + 123 log² x)` for every `x ≥ 2` under RH,
in the exact form of Statements.lean `theorem1`, from the zero inputs of SmoothTheorem2.lean:
`goldbach_578_of_zeros` for `x ≥ 3`, and the 4·10^18 even check for `2 ≤ x < 3`.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ChirreHagen2025.SmoothGoldbach

namespace LeanLab.ChirreHagen2025
open SmoothT2

theorem theorem1_of_zeros {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ)
    (hH : RiemannHypothesis → HadamardK γ) (h14 : Ordinates14 γ) (hL : Lemma26 γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 123 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 0.69 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  rcases lt_or_ge x 3 with h3 | h3
  · obtain ⟨n, hn, h1, h2⟩ := small_of hEv x hx (by linarith)
    exact ⟨n, hn, h1, by nlinarith⟩
  · obtain ⟨n, hn, h1, h2⟩ := goldbach_578_of_zeros hE hH h14 hL hEv hS hRH x h3
    exact ⟨n, hn, h1, by nlinarith⟩

end LeanLab.ChirreHagen2025
