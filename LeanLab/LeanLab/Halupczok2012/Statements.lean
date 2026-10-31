/-
P0077 K. Halupczok, "Goldbach's problem with primes in arithmetic progressions and in short
intervals", arXiv 1212.4406 (v1, 18 Dec 2012).
Statements of Theorems 2, 6, 7 (mean value theorems of Bombieri-Vinogradov type) and of
Corollaries 1, 2, 3, 4 (ternary and binary Goldbach with almost-twin primes in short intervals),
with cheap links proved.
Not encoded: Theorem 1, whose singular series T(n,q1,a1,q2,a2) is only given at the end of
Section 3 by a case split; Theorems 3, 4, 5, which are cited results of Perelli-Pintz-Salerno,
Kawada and Perelli-Pintz; Lemmas 1, 2 (large sieve type inequalities); Conjecture 1.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.
Cited results are `sorry`; everything else below is proved with zero sorry.

Conventions, following the paper's notation section.
* `[X, X+Y]` is the set of integers `m` with `X < m ≤ X + Y`.
* `P_s` is a positive integer with at most `s` prime factors, counted with multiplicity (`Ω`).
* `L = log Y`.
* Every `≪`, `≫`, `≍` in a hypothesis is encoded by a universally quantified constant `c > 0`;
  every `≪` in a conclusion by an existential constant `C`, and "sufficiently large" by an
  existential threshold `Y0`. These may depend on `A`, the `ε`'s, the hypothesis constants and,
  where the paper says "fixed", on the fixed residue `a`. `B = B(A)` is existential after `A`.
-/
import Mathlib
import LeanLab.Common.Goldbach

open Finset
open scoped Classical

namespace LeanLab.Halupczok2012

/-! ### Basic objects -/

/-- `m` is a `P_s`: a positive integer with at most `s` prime factors, with multiplicity. -/
def IsP (s m : ℕ) : Prop := 0 < m ∧ ArithmeticFunction.cardFactors m ≤ s

/-- The integers `k` in the paper's interval `[X, X+R]`, that is `X < k ≤ X + R`. -/
noncomputable def kRange (X R : ℝ) : Finset ℕ :=
  (Icc 0 ⌈X + R⌉₊).filter (fun k => X < k ∧ (k : ℝ) ≤ X + R)

/-- `∑_{p2 + p3 = m, p2 ∈ [X2, X2+Y]} log p2 log p3`, with the extra condition `p2 ≡ a2 (q2)`. -/
noncomputable def binSumAP (X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (m : ℕ) : ℝ :=
  ∑ p ∈ (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ X2 < p ∧ (p : ℝ) ≤ X2 + Y ∧
      (p : ℤ) ≡ a2 [ZMOD q2]),
    Real.log p * Real.log ((m - p : ℕ) : ℝ)

/-- `∑_{p2 + p3 = m, p2 ∈ [X2, X2+Y]} log p2 log p3`. -/
noncomputable def binSum (X2 Y : ℝ) (m : ℕ) : ℝ := binSumAP X2 Y 1 0 m

/-- The twin prime type constant `∏_{p ≠ 2} (1 - 1/(p-1)^2)`, as a `tprod` over all primes.
The product converges absolutely, so `tprod` is its value. -/
noncomputable def twinC : ℝ :=
  ∏' p : Nat.Primes, (if (p : ℕ) = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- The binary singular series `S(r)` of the paper, display (2). -/
noncomputable def S (r : ℕ) : ℝ :=
  if Even r then 2 * twinC * ∏ p ∈ r.primeFactors.filter (· ≠ 2), (((p : ℝ) - 1) / ((p : ℝ) - 2))
  else 0

/-- The singular series `S(r,q,a)` of the paper, display (1). -/
noncomputable def Sqa (r q : ℕ) (a : ℤ) : ℝ :=
  if Even r ∧ Int.gcd a q = 1 ∧ Int.gcd (a - r) q = 1 then S (r * q) / (Nat.totient q) else 0

/-- The ternary singular series `T(n,q,a)` with one prime in an arithmetic progression,
as displayed after Theorem 2, written as a `tprod` over all primes of the local factor. -/
noncomputable def T (n q : ℕ) (a : ℤ) : ℝ :=
  (1 / (Nat.totient q : ℝ)) * ∏' p : Nat.Primes,
    (if ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ∣ q) ∨ (¬ ((p : ℕ) : ℤ) ∣ (n - a) ∧ (p : ℕ) ∣ q) then
        1 - 1 / ((p : ℝ) - 1) ^ 2
      else if ¬ (p : ℕ) ∣ n ∧ ¬ (p : ℕ) ∣ q then 1 + 1 / ((p : ℝ) - 1) ^ 3
      else (p : ℝ) / ((p : ℝ) - 1))

/-- `∑_{p1+p2+p3 = n, p_i ∈ [X_i, X_i+Y_i], p1 ≡ a (q)} log p1 log p2 log p3`. -/
noncomputable def ternSum (n : ℕ) (X1 Y1 X2 Y2 : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ x ∈ ((range (n + 1)) ×ˢ (range (n + 1))).filter (fun x =>
      x.1.Prime ∧ x.2.Prime ∧ x.1 + x.2 ≤ n ∧ (n - x.1 - x.2).Prime ∧
      X1 < x.1 ∧ (x.1 : ℝ) ≤ X1 + Y1 ∧ X2 < x.2 ∧ (x.2 : ℝ) ≤ X2 + Y2 ∧ (x.1 : ℤ) ≡ a [ZMOD q]),
    Real.log x.1 * Real.log x.2 * Real.log ((n - x.1 - x.2 : ℕ) : ℝ)

/-! ### Theorem 6, binary, Kawada approach -/

/-- The left side of Theorem 6:
`∑_{q1 ≤ Q1} ∑_{k1 ∈ [X1,X1+Y], 2k1 ≡ a1 (q1)} ∑_{q2 ≤ Q2} |∑ log p2 log p3 - S(2k1,q2,a2) Y|`.
The outer absolute value of the paper is redundant since the inner terms are nonnegative. -/
noncomputable def thm6LHS (X1 X2 Y Q1 Q2 : ℝ) (a1 a2 : ℤ) : ℝ :=
  ∑ q1 ∈ Icc 1 ⌊Q1⌋₊, ∑ k ∈ (kRange X1 Y).filter (fun k => ((2 * k : ℕ) : ℤ) ≡ a1 [ZMOD q1]),
    ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y|

/-- Theorem 6: let `X1^{2/3+ε} ≪ Y ≤ X1`, `Y ≤ X2 ≤ 2X1 - Y`, `Q1 ≪ Y^{3/2} X1^{-1/2}`,
`Q2 ≪ Y X2^{-1/2} L^{-B}`. Then for fixed integers `a1 ≤ X1`, `a2`, the left side is
`≪ Y^2 L^{-A}`. -/
def Theorem6 : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧
  ∀ c1 c2 c3 : ℝ, 0 < c1 → 0 < c2 → 0 < c3 → ∀ a1 a2 : ℤ, ∃ C Y0 : ℝ,
  ∀ X1 X2 Y Q1 Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y → Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
    1 ≤ Q1 → Q1 ≤ c2 * Y ^ (3 / 2 : ℝ) * X1 ^ (-(1 / 2) : ℝ) →
    1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) → (a1 : ℝ) ≤ X1 →
    thm6LHS X1 X2 Y Q1 Q2 a1 a2 ≤ C * Y ^ 2 * Real.log Y ^ (-A)

/-- Theorem 6, cited. -/
theorem theorem_6 : Theorem6 := by sorry

/-! ### Theorem 7, binary, Perelli-Pintz approach -/

/-- The inner quantity of Theorem 7 for a modulus `q` and residue `a`:
`∑_{k1 ∈ [X1,X1+R], 2k1 ≡ a (q)} (∑_{p2+p3=2k1, p2 ∈ [X2,X2+Y]} log p2 log p3 - S(2k1) Y)`. -/
noncomputable def thm7Inner (X1 X2 Y R : ℝ) (q a : ℕ) : ℝ :=
  ∑ k ∈ (kRange X1 R).filter (fun k => 2 * k ≡ a [MOD q]), (binSum X2 Y (2 * k) - S (2 * k) * Y)

/-- Theorem 7, main part: `X2 ≥ Y ≫ X2^{7/12+ε1}`, `Y^{1/3+ε2} ≪ R ≤ Y`, `Q ≪ R^{3/2} X1^{-1/2}`,
and `Y ≍ 2X1 - X2 - Y ≥ 0`; for a fixed positive integer `a ≤ X1`,
`∑_{q ≤ Q} |thm7Inner| ≪ R Y L^{-A}`.
READING: the paper prints `Y ≍ X1 - X2 - Y`; we encode `Y ≍ 2X1 - X2 - Y`, the condition of
Theorem 5 from which Theorem 7 is derived, and the one Theorem 2's proof uses. -/
def Theorem7 : Prop :=
  ∀ A ε1 ε2 : ℝ, 0 < A → 0 < ε1 → 0 < ε2 →
  ∀ c1 c2 c3 c4 c5 : ℝ, 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → 0 < c5 → ∀ a : ℕ, 0 < a →
  ∃ C Y0 : ℝ, ∀ X1 X2 Y R Q : ℝ, Y0 ≤ R →
    Y ≤ X2 → c1 * X2 ^ (7 / 12 + ε1) ≤ Y → c2 * Y ^ (1 / 3 + ε2) ≤ R → R ≤ Y →
    1 ≤ Q → Q ≤ c3 * R ^ (3 / 2 : ℝ) * X1 ^ (-(1 / 2) : ℝ) →
    0 ≤ 2 * X1 - X2 - Y → c4 * Y ≤ 2 * X1 - X2 - Y → 2 * X1 - X2 - Y ≤ c5 * Y → (a : ℝ) ≤ X1 →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, |thm7Inner X1 X2 Y R q a| ≤ C * R * Y * Real.log Y ^ (-A)

/-- Theorem 7, cited. -/
theorem theorem_7 : Theorem7 := by sorry

/-- Theorem 7, supplement: for `Q ≪ R^{1/2}`, the bound holds with `max_{a (q)}` after the sum
over `q`. The maximum is encoded by quantifying over every choice `a : ℕ → ℕ` of residues. -/
def Theorem7Max : Prop :=
  ∀ A ε1 ε2 : ℝ, 0 < A → 0 < ε1 → 0 < ε2 →
  ∀ c1 c2 c3 c4 c5 : ℝ, 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → 0 < c5 →
  ∃ C Y0 : ℝ, ∀ X1 X2 Y R Q : ℝ, Y0 ≤ R →
    Y ≤ X2 → c1 * X2 ^ (7 / 12 + ε1) ≤ Y → c2 * Y ^ (1 / 3 + ε2) ≤ R → R ≤ Y →
    1 ≤ Q → Q ≤ c3 * R ^ (1 / 2 : ℝ) →
    0 ≤ 2 * X1 - X2 - Y → c4 * Y ≤ 2 * X1 - X2 - Y → 2 * X1 - X2 - Y ≤ c5 * Y →
    ∀ a : ℕ → ℕ, ∑ q ∈ Icc 1 ⌊Q⌋₊, |thm7Inner X1 X2 Y R q (a q)| ≤ C * R * Y * Real.log Y ^ (-A)

/-- Theorem 7 supplement, cited. -/
theorem theorem_7_max : Theorem7Max := by sorry

/-! ### Theorem 2, ternary, one prime in an AP, two primes in short intervals -/

/-- The common hypotheses of Theorem 2, with hypothesis constants `c`, `B`, and `L = log Y2`. -/
def Thm2Hyp (ε ε1 ε2 B : ℝ) (c : Fin 7 → ℝ) (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ) : Prop :=
  Odd n ∧ Y1 ≤ X1 ∧ c 0 * X1 ^ (3 / 5 + ε1) ≤ Y1 ∧ Y2 ≤ X2 ∧ c 1 * X2 ^ (7 / 12 + ε2) ≤ Y2 ∧
  c 2 * Y2 ^ (1 / 3 + ε) ≤ Y1 ∧ Y1 ≤ c 3 * Y2 ∧
  0 ≤ (n : ℝ) - X1 - Y1 - X2 - Y2 ∧ c 4 * Y2 ≤ (n : ℝ) - X1 - Y1 - X2 - Y2 ∧
  (n : ℝ) - X1 - Y1 - X2 - Y2 ≤ c 5 * Y2 ∧
  1 ≤ Q ∧ Q ≤ c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) * Real.log Y2 ^ (-B)

/-- Theorem 2: under `Thm2Hyp`, `Q ≪ Y1^{3/2} (n - X1)^{-1/2}` and a fixed integer
`a ≤ n - X1 - Y1`,
`∑_{q ≤ Q} |∑_{p1+p2+p3=n, p_i ∈ [X_i,X_i+Y_i], p1 ≡ a (q)} log p1 log p2 log p3
  - T(n,q,a) Y1 Y2| ≪ Y1 Y2 L^{-A}`.
READING: the sum over `q` is restricted to `(a, q) = 1`. For `(a, q) > 1` the paper's `T(n,q,a)`
is in general nonzero while the prime sum is empty for `q < X1`, see `prime_cong_noncoprime`;
the proof says it assumes `(q, a) = 1` without loss of generality. -/
def Theorem2 : Prop :=
  ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 → ∃ B : ℝ, 0 < B ∧
  ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∀ c7 : ℝ, 0 < c7 → ∀ a : ℤ, ∃ C Y0 : ℝ,
  ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 → Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q →
    Q ≤ c7 * Y1 ^ (3 / 2 : ℝ) * ((n : ℝ) - X1) ^ (-(1 / 2) : ℝ) → (a : ℝ) ≤ (n : ℝ) - X1 - Y1 →
    ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      |ternSum n X1 Y1 X2 Y2 q a - T n q a * Y1 * Y2| ≤ C * Y1 * Y2 * Real.log Y2 ^ (-A)

/-- Theorem 2, cited. -/
theorem theorem_2 : Theorem2 := by sorry

/-- Theorem 2, supplement: with `Q ≪ Y1^{1/2}` instead of `Q ≪ Y1^{3/2}(n - X1)^{-1/2}`, the
maximum over reduced residues `a (q)` may be inserted after the sum over `q`. Encoded by
quantifying over every choice `a : ℕ → ℤ` of reduced residues. -/
def Theorem2Max : Prop :=
  ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 → ∃ B : ℝ, 0 < B ∧
  ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∀ c7 : ℝ, 0 < c7 → ∃ C Y0 : ℝ,
  ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 → Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q →
    Q ≤ c7 * Y1 ^ (1 / 2 : ℝ) →
    ∀ a : ℕ → ℤ, (∀ q, Int.gcd (a q) q = 1) →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, |ternSum n X1 Y1 X2 Y2 q (a q) - T n q (a q) * Y1 * Y2|
      ≤ C * Y1 * Y2 * Real.log Y2 ^ (-A)

/-- Theorem 2 supplement, cited. -/
theorem theorem_2_max : Theorem2Max := by sorry

/-! ### The corollaries -/

/-- The conclusion of Corollary 1: `n = p1 + p2 + p3` with `p_i ∈ [X_i, X_i + Y]`, `i = 1, 2`,
and `(p1 + 2)(p2 + 2) = P_9`. -/
def Cor1Sol (n : ℕ) (X1 X2 Y : ℝ) : Prop :=
  ∃ p1 p2 p3 : ℕ, p1.Prime ∧ p2.Prime ∧ p3.Prime ∧ p1 + p2 + p3 = n ∧
    X1 < p1 ∧ (p1 : ℝ) ≤ X1 + Y ∧ X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y ∧ IsP 9 ((p1 + 2) * (p2 + 2))

/-- Corollary 1: for `Y` large, odd `n ≢ 1 (6)` with `n ≥ X1 + X2 + 2Y` and `n ≪ X1 Y`,
`X1^{θ1} = Y`, `(n - X1)^{θ2} = Y`, `θ_i ≥ 0.933`, the equation has a `Cor1Sol` solution.
`X^θ = Y` with `θ ≥ 0.933` is written `X^{0.933} ≤ Y`.
READING: we add `Y ≤ X1` and `Y ≤ X2`, the standing hypotheses `X_i ≥ Y` of Theorem 1, from
which the corollary is deduced; the corollary itself does not repeat them. -/
def Corollary1 : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Y0 : ℝ, ∀ (X1 X2 Y : ℝ) (n : ℕ), Y0 ≤ Y → Odd n → n % 6 ≠ 1 →
    X1 + X2 + 2 * Y ≤ n → (n : ℝ) ≤ c * X1 * Y →
    X1 ^ (0.933 : ℝ) ≤ Y → Y ≤ X1 → ((n : ℝ) - X1) ^ (0.933 : ℝ) ≤ Y → Y ≤ X2 →
    Cor1Sol n X1 X2 Y

/-- Corollary 1, cited. -/
theorem corollary_1 : Corollary1 := by sorry

/-- The even numbers `2k1`, `k1 ∈ [X1, X1+Y]`, `2k1 ≢ 2 (6)`, that are not `p2 + p3` with
`p2 + 2 = P_3`, `p2 ∈ [X2, X2+Y]`. -/
noncomputable def cor2Exc (X1 X2 Y : ℝ) : ℕ :=
  #((kRange X1 Y).filter (fun k => (2 * k) % 6 ≠ 2 ∧
    ¬ ∃ p2 p3 : ℕ, p2.Prime ∧ p3.Prime ∧ p2 + p3 = 2 * k ∧ IsP 3 (p2 + 2) ∧
      X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y))

/-- Corollary 2: for all but `O(Y L^{-A})` even `2k1 ≢ 2 (6)` with `k1 ∈ [X1, X1+Y]`,
`2k1 = p2 + p3` with `p2 + 2 = P_3`, `p2 ∈ [X2, X2+Y]`, where `X2^θ = Y`, `θ ≥ 0.861`,
`X2 + Y ≤ 2X1 ≪ Y^{3/2-ε}`. READING: `Y ≤ X2`, i.e. `θ ≤ 1`, is added, the paper's
definition of a short interval. -/
def Corollary2 : Prop :=
  ∀ A ε c : ℝ, 0 < A → 0 < ε → 0 < c → ∃ C Y0 : ℝ, ∀ X1 X2 Y : ℝ, Y0 ≤ Y →
    X2 ^ (0.861 : ℝ) ≤ Y → Y ≤ X2 → X2 + Y ≤ 2 * X1 → 2 * X1 ≤ c * Y ^ (3 / 2 - ε) →
    (cor2Exc X1 X2 Y : ℝ) ≤ C * Y * Real.log Y ^ (-A)

/-- Corollary 2, cited. -/
theorem corollary_2 : Corollary2 := by sorry

/-- The conclusion of Corollary 3: `n = p1 + p2 + p3`, `p1 + 2 = P_2`, `p2 + 2 = P_3`,
`p_i ∈ [X_i, X_i + Y]`. -/
def Cor3Sol (n : ℕ) (X1 X2 Y : ℝ) : Prop :=
  ∃ p1 p2 p3 : ℕ, p1.Prime ∧ p2.Prime ∧ p3.Prime ∧ p1 + p2 + p3 = n ∧
    X1 < p1 ∧ (p1 : ℝ) ≤ X1 + Y ∧ X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y ∧ IsP 2 (p1 + 2) ∧ IsP 3 (p2 + 2)

/-- Corollary 3: `X1^{θ1} = Y = X2^{θ2}` large, `θ1 ≥ 0.971`, `θ2 ≥ 0.861`; odd `n ≢ 1 (6)` with
`X1 + X2 + 2Y ≤ n ≪ Y^{3/2-ε}`. Then a `Cor3Sol` solution exists.
READING: `Y ≤ X_i`, i.e. `θ_i ≤ 1`, is added, the paper's definition of a short interval. -/
def Corollary3 : Prop :=
  ∀ ε c : ℝ, 0 < ε → 0 < c → ∃ Y0 : ℝ, ∀ (X1 X2 Y : ℝ) (n : ℕ), Y0 ≤ Y →
    X1 ^ (0.971 : ℝ) ≤ Y → Y ≤ X1 → X2 ^ (0.861 : ℝ) ≤ Y → Y ≤ X2 →
    Odd n → n % 6 ≠ 1 → X1 + X2 + 2 * Y ≤ n → (n : ℝ) ≤ c * Y ^ (3 / 2 - ε) →
    Cor3Sol n X1 X2 Y

/-- Corollary 3, cited. -/
theorem corollary_3 : Corollary3 := by sorry

/-- `Λ3 = 4 - log(27/7)/log 3`. -/
noncomputable def Λ3 : ℝ := 4 - Real.log (27 / 7) / Real.log 3

/-- The admissible exponent range of Corollary 4: either `1 ≥ θ1 ≥ 0.861`,
`1 ≥ η > (1 + 1/θ1)^{-1}`, or `0.5 ≥ η ≥ 0.463`, `1 ≥ θ1 > 1/min(1/η - 1, (3 - 1/η) Λ3 / 2)`. -/
def Cor4Range (θ1 η : ℝ) : Prop :=
  (0.861 ≤ θ1 ∧ θ1 ≤ 1 ∧ (1 + 1 / θ1)⁻¹ < η ∧ η ≤ 1) ∨
  (0.463 ≤ η ∧ η ≤ 0.5 ∧ θ1 ≤ 1 ∧ 1 / min (1 / η - 1) ((3 - 1 / η) * Λ3 / 2) < θ1)

/-- The conclusion of Corollary 4: `n = p1 + p2 + p3`, `p1 + 2 = P_3`, `p_i ∈ [X_i, X_i+Y_i]`. -/
def Cor4Sol (n : ℕ) (X1 Y1 X2 Y2 : ℝ) : Prop :=
  ∃ p1 p2 p3 : ℕ, p1.Prime ∧ p2.Prime ∧ p3.Prime ∧ p1 + p2 + p3 = n ∧
    X1 < p1 ∧ (p1 : ℝ) ≤ X1 + Y1 ∧ X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y2 ∧ IsP 3 (p1 + 2)

/-- Corollary 4: `X1^{θ1} = Y1` large, `X2^{θ2} = Y2`, `θ2 > 3/5`, `Y2^η ≪ Y1 ≪ Y2`,
odd `n ≢ 1 (6)` with `Y2 ≍ n - X1 - X2 - Y1 - Y2 > 0`, and `(θ1, η)` in `Cor4Range`.
Then a `Cor4Sol` solution exists. READING: `θ2 ≤ 1` is added, the paper's definition of a
short interval and Theorem 2's hypothesis `X2 ≥ Y2`. -/
def Corollary4 : Prop :=
  ∀ θ1 θ2 η : ℝ, 3 / 5 < θ2 → θ2 ≤ 1 → Cor4Range θ1 η →
  ∀ c1 c2 c3 c4 : ℝ, 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → ∃ Y0 : ℝ,
  ∀ (X1 X2 Y1 Y2 : ℝ) (n : ℕ), 1 < X1 → 1 < X2 → Y1 = X1 ^ θ1 → Y2 = X2 ^ θ2 → Y0 ≤ Y1 →
    c1 * Y2 ^ η ≤ Y1 → Y1 ≤ c2 * Y2 → Odd n → n % 6 ≠ 1 →
    0 < (n : ℝ) - X1 - X2 - Y1 - Y2 → c3 * Y2 ≤ (n : ℝ) - X1 - X2 - Y1 - Y2 →
    (n : ℝ) - X1 - X2 - Y1 - Y2 ≤ c4 * Y2 → Cor4Sol n X1 Y1 X2 Y2

/-- Corollary 4, cited. -/
theorem corollary_4 : Corollary4 := by sorry

/-! ## Proved links, zero sorry -/

/-- `P_s` is monotone in `s`. -/
theorem isP_mono {s t m : ℕ} (h : s ≤ t) (hm : IsP s m) : IsP t m :=
  ⟨hm.1, hm.2.trans h⟩

/-- A prime is a `P_1`. -/
theorem isP_prime {p : ℕ} (hp : p.Prime) : IsP 1 p :=
  ⟨hp.pos, by rw [ArithmeticFunction.cardFactors_apply_prime hp]⟩

/-- `P_s · P_t = P_{s+t}`. -/
theorem isP_mul {s t a b : ℕ} (ha : IsP s a) (hb : IsP t b) : IsP (s + t) (a * b) := by
  refine ⟨Nat.mul_pos ha.1 hb.1, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul ha.1.ne' hb.1.ne']
  exact Nat.add_le_add ha.2 hb.2

/-- A `Cor3Sol` solution is a `Cor1Sol` solution: `P_2 · P_3 = P_5`, a `P_9`. -/
theorem cor1Sol_of_cor3Sol {n : ℕ} {X1 X2 Y : ℝ} (h : Cor3Sol n X1 X2 Y) : Cor1Sol n X1 X2 Y := by
  obtain ⟨p1, p2, p3, h1, h2, h3, hs, a, b, c, d, e, f⟩ := h
  exact ⟨p1, p2, p3, h1, h2, h3, hs, a, b, c, d, isP_mono (by norm_num) (isP_mul e f)⟩

/-- A `Cor1Sol` solution makes `n` a sum of three primes. -/
theorem ternary_of_cor1Sol {n : ℕ} {X1 X2 Y : ℝ} (h : Cor1Sol n X1 X2 Y) : IsTernarySum n := by
  obtain ⟨p1, p2, p3, h1, h2, h3, hs, -⟩ := h
  exact ⟨p1, p2, p3, h1, h2, h3, hs⟩

/-- A `Cor3Sol` solution makes `n` a sum of three primes. -/
theorem ternary_of_cor3Sol {n : ℕ} {X1 X2 Y : ℝ} (h : Cor3Sol n X1 X2 Y) : IsTernarySum n :=
  ternary_of_cor1Sol (cor1Sol_of_cor3Sol h)

/-- A `Cor4Sol` solution makes `n` a sum of three primes. -/
theorem ternary_of_cor4Sol {n : ℕ} {X1 Y1 X2 Y2 : ℝ} (h : Cor4Sol n X1 Y1 X2 Y2) :
    IsTernarySum n := by
  obtain ⟨p1, p2, p3, h1, h2, h3, hs, -⟩ := h
  exact ⟨p1, p2, p3, h1, h2, h3, hs⟩

/-- A `k` counted as non exceptional in Corollary 2 makes `2k` a Goldbach sum. -/
theorem goldbach_of_cor2_sol {k : ℕ} {X2 Y : ℝ}
    (h : ∃ p2 p3 : ℕ, p2.Prime ∧ p3.Prime ∧ p2 + p3 = 2 * k ∧ IsP 3 (p2 + 2) ∧
      X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y) : IsGoldbachSum (2 * k) := by
  obtain ⟨p2, p3, h2, h3, hs, -⟩ := h
  exact ⟨p2, p3, h2, h3, hs⟩

/-- Necessity of `n ≢ 1 (6)` in Corollaries 1, 3, 4: for `n ≡ 1 (6)`, every representation
`n = p1 + p2 + p3` with `3 ∤ (p1 + 2)(p2 + 2)` uses the prime `3`. So the sieve on
`(p1+2)(p2+2)` meets the local obstruction at `3` that the paper mentions, `ω(3)/3 = 1`. -/
theorem three_used_ternary {n p1 p2 p3 : ℕ} (hn : n % 6 = 1)
    (h1 : p1.Prime) (h2 : p2.Prime) (h3 : p3.Prime) (hs : p1 + p2 + p3 = n)
    (h : ¬ 3 ∣ (p1 + 2) * (p2 + 2)) : p1 = 3 ∨ p2 = 3 ∨ p3 = 3 := by
  have ha : ¬ 3 ∣ p1 + 2 := fun hd => h (dvd_mul_of_dvd_left hd _)
  have hb : ¬ 3 ∣ p2 + 2 := fun hd => h (dvd_mul_of_dvd_right hd _)
  have : 3 ∣ p1 ∨ 3 ∣ p2 ∨ 3 ∣ p3 := by omega
  rcases this with d | d | d
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h1).mp d).symm
  · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h2).mp d).symm)
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h3).mp d).symm)

/-- Necessity of `2k1 ≢ 2 (6)` in Corollary 2: for `m ≡ 2 (6)`, every `m = p2 + p3` with
`3 ∤ p2 + 2` uses the prime `3`. -/
theorem three_used_binary {m p2 p3 : ℕ} (hm : m % 6 = 2) (h2 : p2.Prime) (h3 : p3.Prime)
    (hs : p2 + p3 = m) (h : ¬ 3 ∣ p2 + 2) : p2 = 3 ∨ p3 = 3 := by
  have : 3 ∣ p2 ∨ 3 ∣ p3 := by omega
  rcases this with d | d
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h2).mp d).symm
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h3).mp d).symm

/-- Support for the reading of Theorem 2: if a prime `d` divides both `q` and `a`, then a prime
`p1 ≡ a (q)` equals `d`. So for `(a, q) > 1` and `q < X1` the prime sum in Theorem 2 is empty. -/
theorem prime_cong_noncoprime {p1 q d : ℕ} {a : ℤ} (hp : p1.Prime) (hd : d.Prime)
    (hc : (p1 : ℤ) ≡ a [ZMOD q]) (hdq : d ∣ q) (hda : (d : ℤ) ∣ a) : p1 = d := by
  have h1 : (q : ℤ) ∣ a - p1 := (Int.ModEq.dvd hc)
  have h2 : (d : ℤ) ∣ a - p1 := (Int.natCast_dvd_natCast.mpr hdq).trans h1
  have h3 : (d : ℤ) ∣ (p1 : ℤ) := by
    have := dvd_sub hda h2
    simpa using this
  exact ((Nat.prime_dvd_prime_iff_eq hd hp).mp (Int.natCast_dvd_natCast.mp h3)).symm

/-- `S(r) = 0` for odd `r`. -/
theorem S_odd {r : ℕ} (h : ¬ Even r) : S r = 0 := by simp [S, h]

/-- `S(r,q,a) = 0` unless `(a, q) = 1`. -/
theorem Sqa_noncoprime {r q : ℕ} {a : ℤ} (h : Int.gcd a q ≠ 1) : Sqa r q a = 0 := by
  simp [Sqa, h]

/-! ### Small kernel examples -/

/-- `45 = 11 + 17 + 17` with `13 = P_1 ⊆ P_2`, `19 = P_1 ⊆ P_3`, `11 ∈ [10, 12]`,
`17 ∈ [16, 18]`: an instance of the conclusion of Corollary 3. `45 ≡ 3 (6)`. -/
theorem cor3Sol_45 : Cor3Sol 45 10 16 2 := by
  refine ⟨11, 17, 17, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num,
    isP_mono (by norm_num) (isP_prime (by norm_num)),
    isP_mono (by norm_num) (isP_prime (by norm_num))⟩

/-- Hence also an instance of the conclusion of Corollary 1. -/
theorem cor1Sol_45 : Cor1Sol 45 10 16 2 := cor1Sol_of_cor3Sol cor3Sol_45

/-- `25 ≡ 1 (6)`: `25 = 11 + 11 + 3` has `3 ∤ 13 · 13`, and uses the prime `3`,
as `three_used_ternary` forces. -/
example : 25 % 6 = 1 ∧ 11 + 11 + 3 = 25 ∧ ¬ 3 ∣ (11 + 2) * (11 + 2) := by decide

end LeanLab.Halupczok2012
