/-
P0075 line, T2, unit U-1348, I-5171, PC run 20261021T0403Z-14344, 2026-10-21.
Composition of `goldbach_445_of_J` of U1348Goldbach.lean with SmoothT2.theorem2_u6806 of
U6806Theorem2.lean, and of `goldbach_449_of_J` with theorem2_u6759 of U6759Theorem2.lean.
NOT BUILT in run 20261021T0403Z-14344: the U6806 and U6759 diagonal files are over 1 MB and were
not in the cloud workspace; the main thread builds this file in the repo. The bodies are the
one-line pattern of goldbach_451_of_u6806 with the J theorem renamed.
Under RH, a Goldbach number in `(x, x + 4.45 log² x)` for every `x ≥ 3`, CONDITIONAL ON ExplicitA,
HadamardK, Ordinates14, BPTN, SchoenfeldTheta and the 4·10^18 even check; no ZeroSumSharp.
AI-written Lean code, Claude. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.ChirreHagen2025.U1348Goldbach
import LeanLab.ChirreHagen2025.U6806Theorem2
import LeanLab.ChirreHagen2025.U6759Theorem2

namespace LeanLab.ChirreHagen2025.U1348
open Real Chebyshev
open LeanLab.ChirreHagen2025

theorem goldbach_445_of_u6806 {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ)
    (hN : RiemannHypothesis → Lemma26B.BPTN γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.45 * Real.log x ^ 2 :=
  goldbach_445_of_J (fun hRH => SmoothT2.theorem2_u6806 (hE hRH) (hH hRH) h14 (hN hRH)) hEv hS

theorem goldbach_449_of_u6759 {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ)
    (hN : RiemannHypothesis → Lemma26B.BPTN γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.49 * Real.log x ^ 2 :=
  goldbach_449_of_J (fun hRH => SmoothT2.theorem2_u6759 (hE hRH) (hH hRH) h14 (hN hRH)) hEv hS

end LeanLab.ChirreHagen2025.U1348
