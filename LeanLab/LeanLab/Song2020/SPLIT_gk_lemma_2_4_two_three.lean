/-
AI wrote the Lean code. Open Math OS repair of claude/Song2020-gk_lemma_2_4_two_three, 2026-11-13.

Song 2020, https://arxiv.org/pdf/2012.06322, printed pages 4 through 8, the S1 lane.
This file holds the two cited paper steps of the S1 bound that Song2020/Decomp139.lean
assembles: the page 5 partial summation reduction from bounds on the von Mangoldt
exponential sums to a bound on the truncated prime sum, and the page 7 per u Vaughan
display. The gate rejected the branch because the repair had put those two steps, with
their sorries, into the existing file Decomp139.lean, which may never gain a sorry. They
now sit here as LEAF theorems, and Decomp139.lean imports this file and proves its own
S1 estimate from them, so every statement of Decomp139.lean is unchanged.
The definitions these two steps are stated with moved here with them, text unchanged.
-/
import LeanLab.Song2020.Characteristic139

namespace LeanLab.Song2020.Decomp139

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Pages 4 and 5. The truncated Fourier polynomial of Lemma 1. -/
def fourier (a : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) : ℂ :=
  ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), a H h * eC (h * x)

/-- Pages 4 and 5. S1 with negative Fourier frequencies as in the defined sawtooth. -/
def truncatedSum (a : ℕ → ℤ → ℂ) (H : ℕ) (γ : ℝ) (n : ℕ) (y α : ℝ) : ℂ :=
  ∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
    (fourier a H (-((p : ℝ) + 1) ^ γ) - fourier a H (-(p : ℝ) ^ γ))
/-- Page 5. The truncated subwindow of the prime window: the integers x with
x minus n over 3 less than y in absolute value and x at most t. Partial summation over the
window produces sums over these initial segments. -/
def subWindow (n : ℕ) (y t : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t)

/-- Page 5. The von Mangoldt weighted exponential sum of the paper, the sum of
Lambda of x times e of alpha x plus h x to the gamma, over an initial segment of the window. -/
def lambdaSum (γ : ℝ) (n : ℕ) (y α : ℝ) (h : ℤ) (t : ℝ) : ℂ :=
  ∑ x ∈ subWindow n y t,
    (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)

/-- Page 8, first display. The ten monomials of the per h bound for
x to the minus epsilon times Sigma 1 plus Sigma 2 plus Sigma 3, with x replaced by n,
which is legitimate since x is of size n over 3 on the window. The argument k stands for
the absolute value of h. -/
def perH (γ n y k : ℝ) : ℝ :=
  n ^ (1 - γ / 4) * k ^ (-(1 : ℝ) / 4) + n ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) +
  n ^ (γ / 2 - 1) * y * k ^ ((1 : ℝ) / 2) +
  n ^ ((γ + 2) / 6) * y ^ ((1 : ℝ) / 3) * k ^ ((1 : ℝ) / 6) +
  n ^ (γ / 4) * y ^ ((1 : ℝ) / 2) * k ^ ((1 : ℝ) / 4) +
  n ^ (γ / 8 + 1 / 2) * y ^ ((1 : ℝ) / 4) * k ^ ((1 : ℝ) / 8) +
  n ^ ((γ + 6) / 10) * y ^ ((1 : ℝ) / 5) * k ^ ((1 : ℝ) / 10) +
  n ^ (γ / 10 + 2 / 5) * y ^ ((2 : ℝ) / 5) * k ^ ((1 : ℝ) / 10) +
  n ^ (3 * γ / 10) * y ^ ((3 : ℝ) / 5) * k ^ ((3 : ℝ) / 10) +
  n ^ (3 * γ / 14 + 2 / 7) * y ^ ((3 : ℝ) / 7) * k ^ ((3 : ℝ) / 14)

/-- LEAF: Song 2020, page 5, the displays from "For S1, we first observe" to "We have shown
so far": partial summation in the weight c x to the 1 minus gamma, the bound a_h at most K over
h, the bound of e of h times the gamma difference by h x to the gamma minus 1, and the passage
from primes to the von Mangoldt function. This form keeps the initial segments that partial
summation really produces, drops the paper's log saving, writes the prime power error as
K H n to the 1/2, and carries n to the epsilon on the B sum for y close to n/3. Any bound B on
the von Mangoldt sums for 1 at most |h| at most H then bounds S1. -/
theorem s1_lambda_reduction :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ a : ℕ → ℤ → ℂ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
            ∀ H : ℕ, 1 ≤ H → ∀ B : ℤ → ℝ,
              (∀ h : ℤ, h ≠ 0 → |h| ≤ (H : ℤ) → ∀ t : ℝ, ‖lambdaSum γ n y α h t‖ ≤ B h) →
              ‖truncatedSum a H γ n y α‖ ≤
                C * K * ((n : ℝ) ^ (3 / 2 - γ) + (H : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) +
                  (n : ℝ) ^ ε * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ)))) := by
  sorry

/-- LEAF: Song 2020, page 7, the display after "Choosing v = (n/u)^{1/2}": for every Vaughan
parameter u with 1 at most u at most n, x to the minus epsilon times Sigma 1 plus Sigma 2 plus
Sigma 3 is bounded by six monomials in n, y and the absolute value k of h. Published inputs:
Dirichlet approximation with q at most log n and the Ramanujan sum splitting, page 5; the
Vaughan identity, page 5; Iwaniec and Kowalski Corollary 8.13 for Sigma 1, page 6; Graham and
Kolesnik Lemma 2.5 for T(R,S), page 6; Iwaniec and Kowalski Corollary 8.13 for the inner r sum
and Graham and Kolesnik Lemma 2.4 for L, page 7. -/
theorem vaughan_per_u :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u : ℝ, 1 ≤ u → u ≤ n →
            ‖lambdaSum γ n y α h t‖ ≤ C * (n : ℝ) ^ ε *
              ((n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((3 : ℝ) / 4) +
                u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  sorry

end

end LeanLab.Song2020.Decomp139
