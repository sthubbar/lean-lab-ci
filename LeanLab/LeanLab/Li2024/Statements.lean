/-
P0027, Runbo Li, On Chen's theorem, Goldbach's conjecture and almost prime twins, arXiv 2405.05727.
Versions, checked 2026-10-16 from the arXiv PDFs: v1 1.253, v2 1.267, v3 of 22 May 2024 1.733 with
Theorem 1.3 at 1.238, all titled without II; v4 of 31 May 2025, titled ... almost prime twins II,
Theorem 1.1 1.9728 and Theorem 1.3 1.2759. The lab states the bound with the constant as a
parameter, and the v3 and v4 claims as cited `sorry`.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ChenExplicit.Reductions

open Finset
open scoped ArithmeticFunction.Omega

noncomputable section
namespace LeanLab.Li2024
open LeanLab.ChenExplicit

/-- `D_{1,2}(N) = #{p ≤ N : N - p = P₂}`, `P₂` having at most two prime factors with
multiplicity. `0` is not a `P₂` in Mathlib, so `p = N` never counts. -/
def D12 (N : ℕ) : ℕ := by
  classical exact #{p ∈ range (N + 1) | p.Prime ∧ Nat.IsAtMostAlmostPrime 2 (N - p)}

/-- `C(N) = ∏_{p ∣ N, p > 2} (p-1)/(p-2) · ∏_{p > 2} (1 - 1/(p-1)²)`. -/
def C (N : ℕ) : ℝ :=
  (∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))) * twinC

/-- Theorem 1.1 with constant `c`: for all sufficiently large even `N`,
`D_{1,2}(N) ≥ c C(N) N / log² N`. -/
def LiBound (c : ℝ) : Prop :=
  ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N → c * C N * N / Real.log N ^ 2 ≤ D12 N

/-- Theorem 1.1, v3: `c = 1.733`. -/
def theorem1_1_v3_stmt : Prop := LiBound 1.733

/-- Theorem 1.1, v4: `c = 1.9728`. -/
def theorem1_1_v4_stmt : Prop := LiBound 1.9728

/-- `π_{1,2}(x) = #{p ≤ x : p + 2 = P₂}`. -/
def pi12 (x : ℕ) : ℕ := by
  classical exact #{p ∈ range (x + 1) | p.Prime ∧ Nat.IsAtMostAlmostPrime 2 (p + 2)}

/-- Theorem 1.3, v3: for all large `x`, `π_{1,2}(x) ≥ 1.238 C₂ x / log² x`, `C₂ = 2 ∏_{p>2}(1 - 1/(p-1)²)`. -/
def theorem1_3_stmt : Prop := ∃ x0 : ℕ, ∀ x : ℕ, x0 ≤ x →
    1.238 * (2 * twinC) * x / Real.log x ^ 2 ≤ pi12 x

/-- Theorem 1.3, v4: constant `1.2759`. -/
def theorem1_3_v4_stmt : Prop := ∃ x0 : ℕ, ∀ x : ℕ, x0 ≤ x →
    1.2759 * (2 * twinC) * x / Real.log x ^ 2 ≤ pi12 x

end LeanLab.Li2024
