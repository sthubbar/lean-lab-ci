-- Repo encoding of P0070 from cloud runs, copied under namespace B by PC run 20261020T0603Z-352, unit U-1182, unchanged otherwise.
/-
P0070 A. Perelli and J. Pintz, "On the exceptional set for the 2k-twin primes problem",
Compositio Math. 82 (1992), 355-372. Read 2026-10-18 from the open numdam copy
numdam.org/item/CM_1992__82_3_355_0.pdf, pages 355 and 356, formulas from the rendered page
images, since the numdam text layer drops displayed formulas.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach and the twin prime conjecture are OPEN. The Theorem is unconditional but its
constants are ineffective, by Siegel's theorem.

Readings: `k` is a positive integer, page 355, so the sum in (3) runs over integers
`k ≥ 1` with `V ≤ k ≤ V + H`. `L = log N`. A bound `≪_{ε,A}` becomes `∃ K N₀, ∀ N ≥ N₀`,
uniform in `H` and `V`.
-/
import Mathlib

namespace LeanLab.PerelliPintz1992.B
open Finset Real
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- `Ψ(N, 2k) = ∑_{N ≤ m, n ≤ 2N, n - m = 2k} Λ(m) Λ(n)`, page 355. -/
def Psi (N k : ℕ) : ℝ :=
  ∑ m ∈ Icc N (2 * N), if m + 2 * k ≤ 2 * N then Λ m * Λ (m + 2 * k) else 0

/-- `𝔖(2k) = 2 ∏_{p > 2} (1 - 1/(p-1)²) ∏_{p | k, p > 2} (p-1)/(p-2)`, page 355. -/
def Sing (k : ℕ) : ℝ :=
  2 * (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)) *
    ∏ p ∈ k.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- The error in conjecture (1): `Ψ(N, 2k) - 𝔖(2k)(N - 2k)`. -/
def Delta (N k : ℕ) : ℝ := Psi N k - Sing k * ((N : ℝ) - 2 * k)

/-- The `k` of (3): integers `k ≥ 1` with `V ≤ k ≤ V + H`. -/
def Ks (V H : ℝ) : Finset ℕ := (Icc ⌈V⌉₊ ⌊V + H⌋₊).filter (1 ≤ ·)

/-- The Theorem, page 356, eq. (3): for `0 < ε < 1/2`, `A > 0`, `N^{1/2+ε} < H < N/4` and
`0 ≤ V < N/4`, `∑_{k=V}^{V+H} |Ψ(N,2k) - 𝔖(2k)(N-2k)|² ≪_{ε,A} H N² L^{-A}`. -/
def Theorem : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ A : ℝ, 0 < A → ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ H V : ℝ, (N : ℝ) ^ (1 / 2 + ε) < H → H < N / 4 → 0 ≤ V → V < N / 4 →
      ∑ k ∈ Ks V H, Delta N k ^ 2 ≤ K * H * (N : ℝ) ^ 2 * Real.log N ^ (-A)

/-- The Corollary, page 356: for `A, B > 0` and `0 ≤ V < N/4`, (1) holds for all
`V ≤ k ≤ V + H` but `O(H L^{-B})` exceptions, provided `N^{1/2+ε} < H < N/4`. Encoded with an
explicit constant `C₁` in the `O(N L^{-A})` of (1) and `C₂` in the exception count. -/
def Corollary : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ A B : ℝ, 0 < A → 0 < B → ∃ C₁ C₂ : ℝ, ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → ∀ H V : ℝ, (N : ℝ) ^ (1 / 2 + ε) < H → H < N / 4 → 0 ≤ V → V < N / 4 →
      (((Ks V H).filter (fun k => C₁ * N * Real.log N ^ (-A) < |Delta N k|)).card : ℝ) ≤
        C₂ * H * Real.log N ^ (-B)


/-- Wolke's function `Ψ₂(N, 2k) = ∑_{2k < n ≤ N} Λ(n) Λ(n - 2k)`, page 355. -/
def Psi2 (N k : ℕ) : ℝ := ∑ n ∈ Ioc (2 * k) N, Λ n * Λ (n - 2 * k)

end

end LeanLab.PerelliPintz1992.B

