/-
P0075 line, T2, unit U-6358, I-5170, CLOUD 20261020T1125Z-cloud41, 2026-10-20.
Composition: theorem2_smooth_of feeds goldbach_578_of_smooth, so under RH a Goldbach number
lies in every `(x, x + 5.78 log² x)`, `x ≥ 3`, CONDITIONAL ON the zero inputs ExplicitA,
HadamardK, Lemma26, Ordinates14 for the zeros under RH, on SchoenfeldTheta and on the
4·10^18 even check.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ChirreHagen2025.SmoothJ
import LeanLab.ChirreHagen2025.Lemma24

namespace LeanLab.ChirreHagen2025
open SmoothT2

theorem goldbach_578_of_zeros {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ)
    (hH : RiemannHypothesis → HadamardK γ) (h14 : Ordinates14 γ) (hL : Lemma26 γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 5.78 * Real.log x ^ 2 :=
  goldbach_578_of_smooth (fun hRH => theorem2_smooth_of (hE hRH) (hH hRH) h14 hL) hEv hS

end LeanLab.ChirreHagen2025
