/-
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Statement only: Theorem 6 of Bordignon, Johnston, Starichkova, arXiv 2207.09452 (P0009), v6,
"The linear-sieve, explicit version", Section 2, equations (3)-(11) and Table 1, as a
`def ... : Prop`. Nothing is proved about it here; it is a HYPOTHESIS. It is not used in the
proved implication `BJS3_of_sieveBounds` of Assembly.lean, which starts from the paper's
Theorems 44, 50, 51, the three applications of Theorem 6 to the sets of Section 5.
Two deliberate deviations, each recorded in BRIDGE.md:
* the paper's strict `<` and `>` in (5), (6) are weakened to `≤`, because for `a ≡ 0` both sides
  of (5) and (6) are `0`, so the strict form is false for that degenerate input;
* Table 1 is read as "for every `ε ⩽ 1/k` the constants of row `k` work", the reading the paper
  uses when it applies row `k = 100000` with `ε = 1.452 · 10⁻⁷` in Theorems 44, 50, 51 and says
  `C₁, C₂` decrease in `ε⁻¹`.
-/
import Mathlib

open Finset Real

noncomputable section
namespace LeanLab.ChenExplicit

/-- `h(s)` of equation (7): `e^{-2}` on `[1,2]`, `e^{-s}` on `[2,3]`, `3 s⁻¹ e^{-s}` for `s ⩾ 3`. -/
def hSieve (s : ℝ) : ℝ :=
  if s ≤ 2 then exp (-2) else if s ≤ 3 then exp (-s) else 3 * s⁻¹ * exp (-s)

/-- The delay differential system (8) for the linear sieve functions `F, f`:
`F(s) = 2e^γ/s, f(s) = 0` on `(0, 2]`, `(sF(s))' = f(s−1)`, `(sf(s))' = F(s−1)` for `s > 2`,
with `F, f` continuous on `(0, ∞)`. Continuity at `s = 2` is what makes the solution unique. -/
def IsLinearSieveFns (F f : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, 0 < s → s ≤ 2 → F s = 2 * exp eulerMascheroniConstant / s ∧ f s = 0) ∧
  ContinuousOn F (Set.Ioi 0) ∧ ContinuousOn f (Set.Ioi 0) ∧
  ∀ s : ℝ, 2 < s → HasDerivAt (fun t => t * F t) (f (s - 1)) s ∧
    HasDerivAt (fun t => t * f t) (F (s - 1)) s

/-- Table 1 of BJS: rows `(ε⁻¹, C₁(ε), C₂(ε))`. -/
def table1 : List (ℕ × ℕ × ℕ) :=
  [(74, 631, 630), (76, 559, 559), (78, 504, 504), (80, 461, 461), (85, 386, 386),
   (90, 336, 337), (95, 302, 302), (100, 276, 277), (120, 218, 219), (140, 189, 190),
   (160, 172, 173), (180, 161, 162), (200, 153, 154), (300, 133, 134), (400, 125, 126),
   (500, 121, 122), (600, 118, 119), (700, 116, 117), (800, 115, 116), (900, 114, 115),
   (1000, 113, 114), (2000, 109, 110), (10000, 106, 108), (100000, 106, 107)]

open Classical in
/-- The primes of `P` below `z`, whose product is `P(z)`. -/
def primesBelowIn (P : Set ℕ) (z : ℝ) : Finset ℕ := (range ⌈z⌉₊).filter (· ∈ P)

open Classical in
/-- **BJS Theorem 6, the explicit linear sieve**, for given solutions `F, f` of (8).
`A = {a(n)}`, `a ⩾ 0`, finitely supported on `n ⩾ 1`; `P` a set of primes; `z ⩾ 2`;
`g n` multiplicative with `0 ⩽ g n p < 1` on `P`; `Q ⊆ P` finite with (4),
`∏_{p ∈ P∖Q, u ⩽ p < z} (1 − g_n(p))⁻¹ < (1+ε) log z / log u` for all `n` and `1 < u < z`.
Then with `s = log D / log z`, `X_A` of (9), `r(d)` of (3), `R` of (10):
(5) for `D ⩾ z`, `S(A,P,z) ⩽ (F(s) + ε C₁ e² h(s)) X_A + R`;
(6) for `D ⩾ z²`, `S(A,P,z) ⩾ (f(s) − ε C₂ e² h(s)) X_A − R`. -/
def Theorem6 (F f : ℝ → ℝ) : Prop :=
  ∀ k C₁ C₂ : ℕ, (k, C₁, C₂) ∈ table1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (k : ℝ) →
  ∀ (supp : Finset ℕ) (a : ℕ → ℝ), 0 ∉ supp → (∀ n, 0 ≤ a n) → (∀ n ∉ supp, a n = 0) →
  ∀ P : Set ℕ, (∀ p ∈ P, p.Prime) →
  ∀ z : ℝ, 2 ≤ z →
  ∀ g : ℕ → ArithmeticFunction ℝ, (∀ n, (g n).IsMultiplicative) →
    (∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) →
  ∀ Q : Finset ℕ, (∀ q ∈ Q, q ∈ P) →
  (∀ n : ℕ, ∀ u : ℝ, 1 < u → u < z →
    ∏ p ∈ (primesBelowIn P z).filter (fun p => p ∉ Q ∧ u ≤ (p : ℝ)), (1 - g n p)⁻¹ <
      (1 + ε) * (log z / log u)) →
  ∀ D : ℝ,
    let PP : ℕ := ∏ p ∈ primesBelowIn P z, p
    let s : ℝ := log D / log z
    let S : ℝ := ∑ n ∈ supp, if Nat.Coprime n PP then a n else 0
    let XA : ℝ := ∑ n ∈ supp, a n * ∏ p ∈ primesBelowIn P z, (1 - g n p)
    let r : ℕ → ℝ := fun d => (∑ n ∈ supp, if d ∣ n then a n else 0) - ∑ n ∈ supp, a n * g n d
    let R : ℝ := ∑ d ∈ PP.divisors.filter (fun d : ℕ => (d : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D), |r d|
    (z ≤ D → S ≤ (F s + ε * C₁ * exp 2 * hSieve s) * XA + R) ∧
    (z ^ 2 ≤ D → (f s - ε * C₂ * exp 2 * hSieve s) * XA - R ≤ S)

/-- Theorem 6 for the linear sieve functions, whatever solution of (8) is chosen. -/
def Theorem6Stmt : Prop := ∀ F f : ℝ → ℝ, IsLinearSieveFns F f → Theorem6 F f

end LeanLab.ChenExplicit
