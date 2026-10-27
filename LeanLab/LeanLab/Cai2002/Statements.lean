/-
P0044, Y. C. Cai, Chen's theorem with small primes, Acta Math. Sinica English Series 18 (2002),
no. 3, 597-604. Read from copies/P0044.pdf, text layer, 2026-10-18.
AI-written Lean code, Claude, run 20261018T2303Z-8776. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here proves it.

Cited analytic inputs and the paper's integral evaluations are `Prop` definitions, so no `sorry`
appears: anything that uses them takes them as hypotheses and is CONDITIONAL.
-/
import Mathlib
import LeanLab.ChenExplicit.Statements

open Finset
noncomputable section
namespace LeanLab.Cai2002

/-- `C(N) = ∏_{p > 2} (1 - 1/(p-1)²) · ∏_{p ∣ N, p > 2} (p-1)/(p-2)`, p. 597. -/
def C (N : ℕ) : ℝ :=
  LeanLab.ChenExplicit.twinC *
    ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- `S(N, θ)`, equation (1.2), p. 597: the number of primes `p ≤ N^θ` with `N - p` a `P₂`,
an almost prime with at most two prime factors. `p < N` is imposed so `N - p ≥ 1`. -/
def S (N : ℕ) (θ : ℝ) : ℕ := by
  classical exact
    #{p ∈ range N | Nat.Prime p ∧ (((p : ℕ) : ℝ) ≤ (N : ℝ) ^ θ) ∧ Nat.IsAtMostAlmostPrime 2 (N - p)}

/-- The Theorem, p. 597-598: for `θ = 0.95` and every sufficiently large even `N`,
`S(N, θ) > 0.01 C(N) N^θ / log² N`. Stated, not proved. -/
def MainTheorem : Prop :=
  ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
    0.01 * C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2 < (S N 0.95 : ℝ)

/-! ### The weights of Lemma 5, p. 599-600, for a set of cutoffs `z₁ ≤ z₂`
In the paper `z₁ = N^{1/11}` and `z₂ = N^{1/3.29}`. -/

/-- `ρ₁(a)`: the number of primes `p ∣ a` with `z₁ ≤ p < z₂`. Coprimality with `N` is
assumed of `a` in Lemma 5, so it is not repeated here. -/
def rho1 (z1 z2 : ℝ) (a : ℕ) : ℕ := by
  classical exact #{p ∈ a.primeFactors | z1 ≤ ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) < z2}

/-- `ρ₂(a) = 1` if `a = p₁p₂p₃` with `z₁ ≤ p₁ < z₂ ≤ p₂ < p₃`, else `0`. -/
def rho2 (z1 z2 : ℝ) (a : ℕ) : ℕ := by
  classical exact
    if ∃ p1 p2 p3 : ℕ, p1.Prime ∧ p2.Prime ∧ p3.Prime ∧ a = p1 * p2 * p3 ∧
        z1 ≤ (p1 : ℝ) ∧ (p1 : ℝ) < z2 ∧ z2 ≤ (p2 : ℝ) ∧ p2 < p3 then 1 else 0

/-- `ρ₃(a) = 1` if `a = p₁p₂p₃` with `z₂ ≤ p₁ < p₂ < p₃`, else `0`. -/
def rho3 (z2 : ℝ) (a : ℕ) : ℕ := by
  classical exact
    if ∃ p1 p2 p3 : ℕ, p1.Prime ∧ p2.Prime ∧ p3.Prime ∧ a = p1 * p2 * p3 ∧
        z2 ≤ (p1 : ℝ) ∧ p1 < p2 ∧ p2 < p3 then 1 else 0

/-- `λ(a) = 1` if `v₂(a) ≤ 2`, the number of prime factors with multiplicity, else `0`. -/
def lam (a : ℕ) : ℕ := by
  classical exact if Nat.IsAtMostAlmostPrime 2 a then 1 else 0

/-! ### Cited inputs, as `Prop`s -/

/-- The lower bound (4.4): `8/θ² (log(5.5θ-1) + ∫₂^{5.5θ-2} log(s-1)/s · log((5.5θ-1)/(s+1)) ds)
≥ 12.9897` at `θ = 0.95`. Reproduced in Python as 12.98978, not proved in Lean. -/
def Eq44Const : Prop :=
  let θ : ℝ := 0.95
  12.9897 ≤ 8 / θ ^ 2 * (Real.log (5.5 * θ - 1) +
    ∫ s in (2 : ℝ)..(5.5 * θ - 2), Real.log (s - 1) / s * Real.log ((5.5 * θ - 1) / (s + 1)))

/-- The upper bound (4.7): `8/θ² (log((11θ-2)/(3.29θ-2)) + ∫₂^{5.5θ-2} log(s-1)/s ·
log((5.5θ-1)(5.5θ-1-s)/(s+1)) ds) ≤ 18.7347`. Reproduced as 18.73461. -/
def Eq47Const : Prop :=
  let θ : ℝ := 0.95
  8 / θ ^ 2 * (Real.log ((11 * θ - 2) / (3.29 * θ - 2)) +
    ∫ s in (2 : ℝ)..(5.5 * θ - 2),
      Real.log (s - 1) / s * Real.log ((5.5 * θ - 1) * (5.5 * θ - 1 - s) / (s + 1))) ≤ 18.7347

/-- The upper bound (4.14): `8/(2θ-1) ∫_{2.29}^{10} log(2.29 - 3.29/(t+1))/t dt ≤ 6.8086`.
Reproduced as 6.80844. -/
def Eq414Const : Prop :=
  let θ : ℝ := 0.95
  8 / (2 * θ - 1) * ∫ t in (2.29 : ℝ)..10, Real.log (2.29 - 3.29 / (t + 1)) / t ≤ 6.8086

/-- The upper bound (4.15): `8/(2θ-1) ∫₂^{2.29} log(t-1)/t dt ≤ 0.1564`. Reproduced as 0.156286. -/
def Eq415Const : Prop :=
  let θ : ℝ := 0.95
  8 / (2 * θ - 1) * ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t ≤ 0.1564

end LeanLab.Cai2002
