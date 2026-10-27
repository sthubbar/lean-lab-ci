/-
P0022, L. Kaniecki, On Šnirelman's constant under the Riemann hypothesis,
Acta Arith. 72 (1995), 361-374. Definitions and statements, checked on page images.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here proves it.

Status of every item is in `STATEMENTS.md`. Cited inputs are `Prop` definitions, so no
`sorry` appears: theorems that use them take them as hypotheses and are CONDITIONAL.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.SchnirelmannConstant.Defs

namespace LeanLab.Kaniecki1995
open Real Complex Finset
open scoped ArithmeticFunction.vonMangoldt

/-! ### Parameters and the functions `f₁, …, f₇` of Lemmas 4 and 5, pages 364, 365, 368 -/

/-- `n₀ = e^{e^{11.503}}`, the Chen-Wang bound, p. 361 and p. 371. -/
noncomputable def n0 : ℝ := Real.exp (Real.exp 11.503)

/-- `σ = 1/2 + ac/log T`, Lemma 4, p. 364. -/
noncomputable def sig (a c T : ℝ) : ℝ := 1 / 2 + a * c / Real.log T

/-- `f₁(T) = 504/(T log T) · (1/(1 - 7.02/T))²`, p. 365. -/
noncomputable def f1 (T : ℝ) : ℝ := 504 / (T * Real.log T) * (1 / (1 - 7.02 / T)) ^ 2

/-- `f₂ = π/(1-σ/T) · (1/(4a²c²) - 0.144/log² T)`, p. 365. -/
noncomputable def f2 (a c T : ℝ) : ℝ :=
  π / (1 - sig a c T / T) * (1 / (4 * a ^ 2 * c ^ 2) - 0.144 / Real.log T ^ 2)

/-- `f₃`, p. 365. -/
noncomputable def f3 (a c T α : ℝ) : ℝ :=
  (α ^ 2 * π / (1 - sig a c T / T) + (2 + 1 / T) ^ 2 *
    (α ^ 2 / T ^ (α - 1) + 2 * α / (T ^ (α - 1) * Real.log T) +
      2 / (T ^ (α - 1) * Real.log T ^ 2))) *
  ((Real.exp (-c) + Real.exp (-(a * c))) / (2 * (a - 1) * c)) ^ 2

/-- `β` of (14), p. 368, with `x = T^{1/a}` so that `T = x^a`. -/
noncomputable def beta (a c T : ℝ) : ℝ :=
  (Real.exp (-(a * c)) * (T ^ (1 / a)) ^ (a / 2) + Real.exp (-c) * (T ^ (1 / a)) ^ (1 / 2 : ℝ) +
    1 / ((T ^ (1 / a)) ^ sig a c T * ((T ^ (1 / a)) ^ 2 - 1)) +
    1 / ((T ^ (1 / a)) ^ (a * sig a c T) * ((T ^ (1 / a)) ^ (2 * a) - 1))) / T ^ (1 / 2 : ℝ)

/-- `f₄ = a²β²(1+1/T)^{2σ} / (8232 (a-1)² log⁴ T)`, p. 365. -/
noncomputable def f4 (a c T : ℝ) : ℝ :=
  a ^ 2 * beta a c T ^ 2 * (1 + 1 / T) ^ (2 * sig a c T) / (8232 * (a - 1) ^ 2 * Real.log T ^ 4)

/-- `f₅ = ((a-1)c / ((a-1)c - e^{-c} - e^{-ac}))²`, p. 365. -/
noncomputable def f5 (a c : ℝ) : ℝ :=
  ((a - 1) * c / ((a - 1) * c - Real.exp (-c) - Real.exp (-(a * c)))) ^ 2

/-- `f = f₁ + (Σ_{j=2}^4 f_j^{1/2})² f₅`, p. 364. -/
noncomputable def fK (a c T α : ℝ) : ℝ :=
  f1 T + (√(f2 a c T) + √(f3 a c T α) + √(f4 a c T)) ^ 2 * f5 a c

/-- `f₆`, p. 368. -/
noncomputable def f6 (a c T : ℝ) : ℝ :=
  π / ((1 - sig a c T / T) * Real.log T ^ 2) *
    (0.886 + Real.log T ^ 2 / (8 * T * a ^ 2 * c ^ 2) + Real.log T / (4 * T ^ 2 * a * c))

/-- `f₇ = 4.51π / ((1-σ/T) log² T)`, p. 368. -/
noncomputable def f7 (a c T : ℝ) : ℝ := 4.51 * π / ((1 - sig a c T / T) * Real.log T ^ 2)

/-- The parameters of Section 3, p. 372: `a = 1.96745`, `c = 1.32149`. -/
noncomputable def aK : ℝ := 1.96745
noncomputable def cK : ℝ := 1.32149

/-! ### Prime gaps: `λ(x)`, p. 371 -/

/-- The least prime larger than `p`. -/
noncomputable def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- `λ(x) = 2` for `0 < x ≤ 7`, `max_{p ≤ x} (p' - p)` for `x > 7`, p. 371. -/
noncomputable def lam (x : ℝ) : ℕ :=
  if x ≤ 7 then 2 else ((range (⌊x⌋₊ + 1)).filter Nat.Prime).sup (fun p => nextPrime p - p)

/-- The right side of Lemma 6: `(1/4π) √((1 + 1/16597) x) log² x`. -/
noncomputable def gL6 (x : ℝ) : ℝ := 1 / (4 * π) * √((1 + 1 / 16597) * x) * Real.log x ^ 2

/-! ### The weights `Λ_{x,a}`, p. 362, and the integrals of Lemmas 4, 5 and Section 3 -/

/-- `Λ_{x,a}(n) = Λ(n)` for `n ≤ x`, `Λ(n) log(x^a/n) / ((a-1) log x)` for `x ≤ n ≤ x^a`. -/
noncomputable def LamXA (x a : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) ≤ x then Λ n else Λ n * Real.log (x ^ a / n) / ((a - 1) * Real.log x)

/-- `ζ'/ζ`. -/
noncomputable def logDerivZeta (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

/-- The kernel `|(e^{δ(σ+it)} - 1)/(σ+it)|²` with `e^δ = 1 + 1/T`. -/
noncomputable def kern (T σ t : ℝ) : ℝ :=
  ‖(Complex.exp ((Real.log (1 + 1 / T) : ℂ) * ((σ : ℂ) + t * I)) - 1) / ((σ : ℂ) + t * I)‖ ^ 2

/-- The left side of (8), Lemma 4. -/
noncomputable def lemma4Int (T σ : ℝ) : ENNReal :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (kern T σ t * ‖logDerivZeta ((σ : ℂ) + t * I)‖ ^ 2)

/-- The integrand `|(θ(y + y/T) - θ(y) - y/T)/y^{1/2+σ}|²` of (17) and of `J`. -/
noncomputable def thetaIntegrand (T σ y : ℝ) : ℝ :=
  ((Chebyshev.theta (y + y / T) - Chebyshev.theta y - y / T) / y ^ (1 / 2 + σ)) ^ 2

/-- `I` of (17), Lemma 5: the integral over `y > 1`. -/
noncomputable def IInt (T σ : ℝ) : ENNReal :=
  ∫⁻ y in Set.Ioi (1 : ℝ), ENNReal.ofReal (thetaIntegrand T σ y)

/-- `J` of Section 3, p. 372: the integral over `y > 2`. -/
noncomputable def JInt (T σ : ℝ) : ENNReal :=
  ∫⁻ y in Set.Ioi (2 : ℝ), ENNReal.ofReal (thetaIntegrand T σ y)

/-- `[x, x+h]` contains a sum of two odd primes. -/
def HasOddPairSumIn (x h : ℝ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ x ≤ ((p + q : ℕ) : ℝ) ∧ ((p + q : ℕ) : ℝ) ≤ x + h

/-! ### The lemmas of Section 2, as statements -/

/-- Lemma 3, p. 363, explicit form of Selberg's bound for `ζ'/ζ` under RH. -/
def Lemma3 : Prop :=
  RiemannHypothesis → ∀ x a c t : ℝ, 1 < x → 1 < a → 0 < c → 14 ≤ t →
    1 / 2 + c / Real.log x ≤ 3 / 4 → Real.exp (-c) + Real.exp (-(a * c)) < (a - 1) * c →
    ‖logDerivZeta (((1 / 2 + c / Real.log x : ℝ) : ℂ) + t * I)‖ ≤
      (a - 1) * c / ((a - 1) * c - Real.exp (-c) - Real.exp (-(a * c))) *
        (‖∑ n ∈ (range ⌈x ^ a⌉₊).filter (fun n : ℕ => 0 < n ∧ (n : ℝ) < x ^ a),
            ((LamXA x a n : ℝ) : ℂ) / (n : ℂ) ^ (((1 / 2 + c / Real.log x : ℝ) : ℂ) + t * I)‖ +
          (Real.exp (-c) + Real.exp (-(a * c))) / (2 * (a - 1) * c) * Real.log t +
          1 / ((a - 1) * t ^ 2 * Real.log x) *
            (Real.exp (-(a * c)) * x ^ (a / 2) + Real.exp (-c) * x ^ (1 / 2 : ℝ) +
              1 / (x ^ (1 / 2 + c / Real.log x) * (x ^ 2 - 1)) +
              1 / (x ^ (a * (1 / 2 + c / Real.log x)) * (x ^ (2 * a) - 1))))

/-- Lemma 4, pp. 364-365, inequality (8). -/
def Lemma4 : Prop :=
  RiemannHypothesis → ∀ a c T α : ℝ, 7.02 < T → 0 < c → 1 < α → 1 < a → sig a c T ≤ 3 / 4 →
    lemma4Int T (sig a c T) ≤ ENNReal.ofReal (fK a c T α * Real.log T ^ 2 / T)

/-- Lemma 5, p. 368, inequality (17), with the hypotheses of Lemma 4. -/
def Lemma5 : Prop :=
  RiemannHypothesis → ∀ a c T α : ℝ, 7.02 < T → 0 < c → 1 < α → 1 < a → sig a c T ≤ 3 / 4 →
    IInt T (sig a c T) ≤ ENNReal.ofReal
      (1 / π * (√(fK a c T α) + √(f6 a c T) + √(f7 a c T)) ^ 2 * Real.log T ^ 2 / T)

/-- Lemma 6, p. 371, from Schoenfeld 1976 Theorems 10 and 12: under RH,
`λ(x) < (1/4π) √((1 + 1/16597) x) log² x` for `x ≥ 2.3 · 10^9`. -/
def Lemma6 : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 2.3e9 ≤ x → (lam x : ℝ) < gL6 x

/-- Lemma 7 as printed, p. 371: every interval `(x, x + λ(λ(x)))`, `x > 4`, contains a sum of
two odd primes. It is FALSE at `x = 6`, see `not_lemma7_printed`. -/
def Lemma7Printed : Prop :=
  ∀ x : ℝ, 4 < x → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧
    x < ((p + q : ℕ) : ℝ) ∧ ((p + q : ℕ) : ℝ) < x + (lam (lam x) : ℝ)

/-! ### Other inputs used in Section 3 -/

/-- [16] Young-Potler 1989, as used on p. 371: the maximal gap between primes up to
`7.263 · 10^13` is at most 778. -/
def YoungPotler : Prop := (lam 72630000000000 : ℝ) ≤ 778

/-- [14] Sinisalo 1993: even Goldbach up to `4 · 10^11`. -/
def Sinisalo : Prop := EvenGoldbachUpTo (4 * 10 ^ 11)

/-- [1] Chen-Wang 1989, as used on p. 371: every odd `n ≥ n₀` is a sum of three primes. -/
def ChenWang : Prop := ∀ n : ℕ, Odd n → n0 ≤ n → IsTernarySum n

/-- Inequality (23), p. 372, the paper's own measure argument with the sets `A, B, C` of
p. 371: if `[x, x+h]` holds no sum of two odd primes, `h ≥ 7`, `h ≤ 2e^{-12} x`,
`1.6 ≤ a ≤ 2`, `1 ≤ c ≤ 1.5`, `T = 2x/h`, `σ = 1/2 + ac/log T`,
then `J ≥ x^{2(1-σ)} / (2T²)`. -/
def Eq23 : Prop :=
  ∀ x h a c : ℝ, 7 ≤ h → h ≤ 2 * Real.exp (-12) * x → 1.6 ≤ a → a ≤ 2 → 1 ≤ c → c ≤ 1.5 →
    ¬ HasOddPairSumIn x h →
    ENNReal.ofReal (x ^ (2 * (1 - sig a c (2 * x / h))) / (2 * (2 * x / h) ^ 2)) ≤
      JInt (2 * x / h) (sig a c (2 * x / h))

/-- The conclusion of the interval part of Section 3, p. 373: every interval
`[x, x + 1.4045 · 10^12]`, `x ≤ n₀`, contains a sum of two odd primes. -/
def IntervalProperty : Prop :=
  ∀ x : ℕ, (x : ℝ) ≤ n0 → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ x ≤ p + q ∧
    p + q ≤ x + 1404500000000

/-! ### The paper's Theorem, p. 362, as statements -/

/-- Odd part of the Theorem, same shape as `SchnirelmannBounds.kaniecki_odd`. -/
def TheoremOdd : Prop :=
  RiemannHypothesis → ∀ n : ℕ, Odd n → 1 < n → SchnirelmannConstant.AtMostPrimes 5 n

/-- Even part of the Theorem, same shape as `SchnirelmannBounds.kaniecki_even`. -/
def TheoremEven : Prop :=
  RiemannHypothesis → (∃ G2 : ℕ, 1405 * 10 ^ 9 < G2 ∧ EvenGoldbachUpTo G2) →
    ∀ n : ℕ, Even n → SchnirelmannConstant.AtMostPrimes 4 n

/-- The Remark, p. 373: under RH, for `x ≥ e^{84000}` every `[x, x + 144 log² x]` contains a
sum of two primes. -/
def RemarkStatement : Prop :=
  RiemannHypothesis → ∀ x : ℝ, Real.exp 84000 ≤ x → HasOddPairSumIn x (144 * Real.log x ^ 2)

/-! ### Lemma 7 as printed fails at `x = 6`, PROVED -/

theorem lam_of_le_seven {x : ℝ} (hx : x ≤ 7) : lam x = 2 := by simp [lam, hx]

/-- QUESTION, PRELIMINARY: Lemma 7 as printed, p. 371, is false at `x = 6`.
`λ(6) = 2` and `λ(2) = 2`, and the open interval `(6, 8)` contains no even number. The proof's
step `p₂ - (x - p₁) < λ(x - p₁)` fails for small `x - p₁`. Section 3 only uses the lemma for
large `x` and with closed intervals, so the Theorem is not affected. -/
theorem not_lemma7_printed : ¬ Lemma7Printed := by
  intro h
  obtain ⟨p, q, hp, hq, hop, hoq, h1, h2⟩ := h 6 (by norm_num)
  have e1 : lam 6 = 2 := lam_of_le_seven (by norm_num)
  have e2 : lam 2 = 2 := lam_of_le_seven (by norm_num)
  rw [e1, show ((2 : ℕ) : ℝ) = 2 by norm_num, e2] at h2
  push_cast at h1 h2
  have h1' : 6 < p + q := by exact_mod_cast h1
  have h2' : p + q < 8 := by exact_mod_cast (by linarith : ((p : ℝ) + q) < 8)
  have hpq : p + q = 7 := by omega
  have : Even (p + q) := Odd.add_odd hop hoq
  rw [hpq] at this
  exact absurd this (by decide)

end LeanLab.Kaniecki1995

#print axioms LeanLab.Kaniecki1995.lam_of_le_seven
#print axioms LeanLab.Kaniecki1995.not_lemma7_printed
