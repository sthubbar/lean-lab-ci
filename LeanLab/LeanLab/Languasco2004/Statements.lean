/-
P0089 A. Languasco, "The exceptional set in short intervals for two additive problems with
primes: a survey", Riv. Mat. Univ. Parma (7) 3* (2004), 223-231. Read 2026-10-18 from the open
copy rivmat.unipr.it/fulltext/2004-3s/pdf/13.pdf, pages 223 to 229, formulas from the rendered
page images, since the text layer garbles the exponents.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach and the Hardy-Littlewood conjecture are OPEN. Every theorem below is quoted by
the survey; Theorems 1.8 and 2.4 are the author's own, from his papers [10] and [11].

Readings. A G-number is an even number that is a sum of two primes; `E` is the set of even
`n > 2` that are not G-numbers; `E(X, H) = E ∩ [X, X + H]`. An HL-number for `k ≥ 2` is
`p + m^k` with `p` prime and `m` a positive integer; QUESTION: the survey says "a k-th power of an
integer" and does not say whether `m = 0` is allowed, the Lean takes `m ≥ 1`. `E_k` is the set of
integers that are neither HL-numbers nor `k`-th powers. The theorems put no upper bound on `H`,
and neither does the Lean: an added `H ≤ X` made the `∃ δ` theorems vacuous for large `δ`, caught by
VERIFY 2026-10-18. `≪` becomes `∃ C X₀, ∀ X ≥ X₀`; "effectively computable `δ`"
becomes `∃ δ > 0`, effectivity not encoded.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.Languasco2004
open Finset Real

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `n ∈ E`: even, `n > 2`, not a sum of two primes. -/
def InE (n : ℕ) : Prop := Even n ∧ 2 < n ∧ ¬ IsGoldbachSum n

/-- `|E(X, H)|`, the exceptions in `[X, X + H]`. -/
def EXH (X H : ℝ) : ℕ := ((Finset.range (⌊X + H⌋₊ + 1)).filter
  (fun n : ℕ => X ≤ (n : ℝ) ∧ (n : ℝ) ≤ X + H ∧ InE n)).card

/-- `|E(X)|`, the exceptions in `[1, X]`. -/
def EX (X : ℝ) : ℕ := EXH 1 (X - 1)

/-- HL-number: `p + m^k`, `p` prime, `m ≥ 1`. -/
def IsHL (k n : ℕ) : Prop := ∃ p m : ℕ, p.Prime ∧ 1 ≤ m ∧ p + m ^ k = n

/-- `n ∈ E_k`: neither an HL-number nor a `k`-th power. -/
def InEk (k n : ℕ) : Prop := ¬ IsHL k n ∧ ¬ ∃ m : ℕ, m ^ k = n

/-- `|E_k(X, H)|`. -/
def EkXH (k : ℕ) (X H : ℝ) : ℕ := ((Finset.range (⌊X + H⌋₊ + 1)).filter
  (fun n : ℕ => X ≤ (n : ℝ) ∧ (n : ℝ) ≤ X + H ∧ InEk k n)).card

/-- Log-power saving for `H ≥ X^a`: for every `A > 0`, `|E(X,H)| ≪ H log^{-A} X`. -/
def LogSaving (e : ℝ → ℝ → ℕ) (a : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X₀ : ℝ, ∀ X H : ℝ, X₀ ≤ X → X ^ a ≤ H →
    (e X H : ℝ) ≤ C * H * Real.log X ^ (-A)

/-- Power saving: `|E(X,H)| ≪ H^{1-η}` for `H ≥ X^a`. -/
def PowerSaving (e : ℝ → ℝ → ℕ) (a η : ℝ) : Prop :=
  ∃ C X₀ : ℝ, ∀ X H : ℝ, X₀ ≤ X → X ^ a ≤ H → (e X H : ℝ) ≤ C * H ^ (1 - η)

/-- Theorem 1.1, Montgomery-Vaughan 1975: `|E(X)| ≪ X^{1-δ}` for some `δ > 0`. -/
def Thm11 : Prop := ∃ δ C X₀ : ℝ, 0 < δ ∧ ∀ X : ℝ, X₀ ≤ X → (EX X : ℝ) ≤ C * X ^ (1 - δ)

/-- Theorem 1.5, Jia 1996: for `A, ε > 0`, `|E(X,H)| ≪ H log^{-A} X` for `H ≥ X^{7/108+ε}`. -/
def Thm15 : Prop := ∀ ε : ℝ, 0 < ε → LogSaving EXH (7 / 108 + ε)

/-- Theorem 1.6, Perelli-Pintz 1993: the same for `0 < ε < 5/6` and `H ≥ X^{7/36+ε}`. -/
def Thm16 : Prop := ∀ ε : ℝ, 0 < ε → ε < 5 / 6 → LogSaving EXH (7 / 36 + ε)

/-- Theorem 1.7, Luo-Yao and Yao, as corrected: `|E(X,H)| ≪ H^{1-δ}` for `H ≥ X^{7/12+2δ}`. -/
def Thm17 : Prop := ∃ δ : ℝ, 0 < δ ∧ PowerSaving EXH (7 / 12 + 2 * δ) δ

/-- Theorem 1.8, Languasco [10]: `|E(X,H)| ≪ H^{1-δ/600}` for `H ≥ X^{7/24+7δ}`. -/
def Thm18 : Prop := ∃ δ : ℝ, 0 < δ ∧ PowerSaving EXH (7 / 24 + 7 * δ) (δ / 600)

/-- Theorem 2.2, Perelli-Pintz and Mikawa: `|E_2(X,H)| ≪ H log^{-A} X` for `H ≥ X^{7/24+ε}`. -/
def Thm22 : Prop := ∀ ε : ℝ, 0 < ε → LogSaving (EkXH 2) (7 / 24 + ε)

/-- Theorem 2.3, Perelli-Zaccagnini: `|E_k(X,H)| ≪ H log^{-A} X` for
`H ≥ X^{7/12 (1-1/k) + ε}`, `k ≥ 2`. -/
def Thm23 : Prop := ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε →
  LogSaving (EkXH k) (7 / 12 * (1 - 1 / (k : ℝ)) + ε)

/-- Theorem 2.4, Languasco [11]: for `k ≥ 2`, `K = 2^{k-2}`, some `δ > 0`,
`|E_k(X,H)| ≪ H^{1-δ/(5K)}` for `H ≥ X^{7/12 (1-1/k) + δ}`. -/
def Thm24 : Prop := ∀ k : ℕ, 2 ≤ k → ∃ δ : ℝ, 0 < δ ∧
  PowerSaving (EkXH k) (7 / 12 * (1 - 1 / (k : ℝ)) + δ) (δ / (5 * 2 ^ (k - 2)))

end

end LeanLab.Languasco2004
