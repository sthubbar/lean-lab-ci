import LeanLab.Cai2002.MainConditional
open Finset Real

noncomputable section
namespace PalomarChallenge.Cai2002

/-! ### BJS Theorem 6, lab `LeanLab.ChenExplicit` -/

/-- `h(s)` of BJS equation 7. Lab: `ChenExplicit.hSieve`. -/
def hSieve (s : ℝ) : ℝ :=
  if s ≤ 2 then exp (-2) else if s ≤ 3 then exp (-s) else 3 * s⁻¹ * exp (-s)

/-- The delay differential system, BJS equation 8. Lab: `ChenExplicit.IsLinearSieveFns`. -/
def IsLinearSieveFns (F f : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, 0 < s → s ≤ 2 → F s = 2 * exp eulerMascheroniConstant / s ∧ f s = 0) ∧
  ContinuousOn F (Set.Ioi 0) ∧ ContinuousOn f (Set.Ioi 0) ∧
  ∀ s : ℝ, 2 < s → HasDerivAt (fun t => t * F t) (f (s - 1)) s ∧
    HasDerivAt (fun t => t * f t) (F (s - 1)) s

/-- BJS Table 1. Lab: `ChenExplicit.table1`. -/
def table1 : List (ℕ × ℕ × ℕ) :=
  [(74, 631, 630), (76, 559, 559), (78, 504, 504), (80, 461, 461), (85, 386, 386),
   (90, 336, 337), (95, 302, 302), (100, 276, 277), (120, 218, 219), (140, 189, 190),
   (160, 172, 173), (180, 161, 162), (200, 153, 154), (300, 133, 134), (400, 125, 126),
   (500, 121, 122), (600, 118, 119), (700, 116, 117), (800, 115, 116), (900, 114, 115),
   (1000, 113, 114), (2000, 109, 110), (10000, 106, 108), (100000, 106, 107)]

open Classical in
/-- The primes of `P` below `z`. Lab: `ChenExplicit.primesBelowIn`. -/
def primesBelowIn (P : Set ℕ) (z : ℝ) : Finset ℕ := (range ⌈z⌉₊).filter (· ∈ P)

open Classical in
/-- BJS Theorem 6, equations 3 to 11, for given solutions `F, f`, with the two recorded
deviations of the lab, weak inequalities and the Table 1 reading. Lab: `ChenExplicit.Theorem6`. -/
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

/-- BJS Theorem 6 for every solution of system 8. Lab: `ChenExplicit.Theorem6Stmt`. -/
def Theorem6Stmt : Prop := ∀ F f : ℝ → ℝ, IsLinearSieveFns F f → Theorem6 F f

/-! ### Wu 1993 Lemma 4, uniform form, lab `LeanLab.Cai2002` -/

/-- `Li x = ∫₂ˣ dt / log t`. Lab: `Cai2002.li118`. -/
def li118 (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- Primes `r` coprime to `N` with `N - N^0.95 < e r < N` and `d ∣ N - e r`, page 603.
Lab: `Cai2002.switchedLocalCount337`. -/
def switchedLocalCount337 (N e d : ℕ) : ℕ :=
  ((range N).filter (fun r => r.Prime ∧ r.Coprime N ∧
    (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) < (e * r : ℕ) ∧ e * r < N ∧ d ∣ N - e * r)).card

/-- The Li mass for one product `e`, pages 602 to 603. Lab: `Cai2002.switchedLiTerm337`. -/
def switchedLiTerm337 (N e : ℕ) : ℝ :=
  li118 ((N : ℝ) / e) - li118 (((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e)

/-- The level `D = N^0.45 / log^B N` of page 603. Lab: `Cai2002.sw2Level337`. -/
def sw2Level337 (N : ℕ) (B : ℝ) : ℝ := (N : ℝ) ^ (0.45 : ℝ) / log N ^ B

/-- The coprime part of the remainder R1 at modulus `d` for a support `E`, page 603
display 4.10. Lab: `Cai2002.swWu337`. -/
def swWu337 (N d : ℕ) (E : Finset ℕ) : ℝ :=
  |∑ e ∈ E.filter (fun e => e.Coprime d),
    ((switchedLocalCount337 N e d : ℝ) - switchedLiTerm337 N e / d.totient)|

/-- Wu 1993 Lemma 4, page 599 of Cai, θ = 0.95, uniform in `N` and in the support `E` of
positive integers below `N^(2/3)`. Lab: the statement of `Cai2002.leaf337_wu_uniform`, as the
Prop `Cai2002.WuUniformStmt`. -/
def WuUniformStmt : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
      (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
      (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
        K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A

/-! ### The Theorem, lab `LeanLab.Cai2002.Statements` -/

/-- The twin prime constant `∏_{p>2} (1 - 1/(p-1)²)`. Lab: `ChenExplicit.twinC`. -/
def twinC : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- `C(N)`, page 597. Lab: `Cai2002.C`. -/
def C (N : ℕ) : ℝ :=
  twinC * ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- `S(N, θ)`, equation 1.2, page 597: primes `p ≤ N^θ`, `p < N`, with `N - p` having at most
two prime factors counted with multiplicity. Lab: `Cai2002.S`. -/
def S (N : ℕ) (θ : ℝ) : ℕ := by
  classical exact
    #{p ∈ range N | Nat.Prime p ∧ (((p : ℕ) : ℝ) ≤ (N : ℝ) ^ θ) ∧ Nat.IsAtMostAlmostPrime 2 (N - p)}

/-- P0044, the Theorem of pages 597 to 598, CONDITIONAL ON BJS Theorem 6 as `h6` and Wu 1993
Lemma 4 in the uniform form as `hwu`: for every sufficiently large even `N`,
`S(N, 0.95) > 0.01 C(N) N^0.95 / log² N`.
This is `LeanLab.Cai2002.cai2002_main_theorem_conditional` with `MainTheorem` unfolded. -/
theorem cai2002 (h6 : Theorem6Stmt) (hwu : WuUniformStmt) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      0.01 * C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2 < (S N 0.95 : ℝ) := by
  exact LeanLab.Cai2002.cai2002_main_theorem_conditional h6 hwu

end PalomarChallenge.Cai2002

namespace PalomarChallenge.Cai2002
example : Theorem6Stmt = LeanLab.ChenExplicit.Theorem6Stmt := rfl
example : WuUniformStmt = LeanLab.Cai2002.WuUniformStmt := rfl
example : (∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      0.01 * C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2 < (S N 0.95 : ℝ)) =
    LeanLab.Cai2002.MainTheorem := rfl
end PalomarChallenge.Cai2002
#print axioms PalomarChallenge.Cai2002.cai2002
