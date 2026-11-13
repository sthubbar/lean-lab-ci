/-
AI wrote the Lean code. OMOS repair of claude/Song2020-lambda_sum_per_h, 2026-11-13.
Source: https://arxiv.org/pdf/2012.06322, printed pages 5 through 8.
The three analytic leaves that Decomp139 carried as sorry are stated in this new file, so
that the existing file Decomp139 gains no sorry and proves its steps from these leaves.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Characteristic139

namespace LeanLab.Song2020.SPLIT_lambda_sum_per_h

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Pages 4 and 5. The truncated Fourier polynomial of Lemma 1, copied from Decomp139 so
that the leaves below can be stated without importing the file that imports this one. -/
def fourier (a : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) : ℂ :=
  ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), a H h * eC (h * x)

/-- Pages 4 and 5. S1 with negative Fourier frequencies as in the defined sawtooth, copied
from Decomp139. -/
def truncatedSum (a : ℕ → ℤ → ℂ) (H : ℕ) (γ : ℝ) (n : ℕ) (y α : ℝ) : ℂ :=
  ∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
    (fourier a H (-((p : ℝ) + 1) ^ γ) - fourier a H (-(p : ℝ) ^ γ))

/-- Page 5. The truncated subwindow of the prime window, copied from Decomp139. -/
def subWindow (n : ℕ) (y t : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t)

/-- Page 5. The von Mangoldt weighted exponential sum of the paper, copied from
Decomp139. -/
def lambdaSum (γ : ℝ) (n : ℕ) (y α : ℝ) (h : ℤ) (t : ℝ) : ℂ :=
  ∑ x ∈ subWindow n y t,
    (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)

/-- Page 8, first display. The ten monomials of the per h bound, copied from
Decomp139. -/
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

/-- LEAF: Song 2020, page 5, from "For S1, we first observe" to "We have shown so
far": partial summation in the weight c x to the 1 minus gamma with a_h at most K over h,
the bound of e of h times the difference of (x+1) to the gamma and x to the gamma minus 1
by h x to the gamma minus 1, and the passage from primes to the von Mangoldt function. The
initial segments that partial summation produces are kept, the log saving is dropped, the
prime power error is written as K H n to the 1/2, and n to the epsilon absorbs the
|h| log n variation of the weight when y is close to n/3. -/
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

/-- LEAF: Song 2020, page 7, the display after "Choosing v = (n/u)^{1/2}": for every
Vaughan parameter u with 1 at most u at most n, n to the minus epsilon times Sigma 1 plus
Sigma 2 plus Sigma 3 is at most six monomials in n, y, u and the absolute value of h.
Published inputs: Dirichlet approximation and the Ramanujan sum splitting, page 5; the
Vaughan identity, Lemma 3.2, page 5; Iwaniec and Kowalski Corollary 8.13 for Sigma 1,
page 6; Graham and Kolesnik Lemma 2.5 for T(R,S), page 6, with Corollary 8.13 for the
inner r sum and Lemma 2.4 for L, page 7. -/
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

/-- LEAF: Graham and Kolesnik, Van der Corput's Method of Exponential Sums, Lemma 2.4,
with two positive and three negative powers, as Song 2020 applies it on page 8 to choose u:
some u in the range 1 to U makes the five term sum at most the six pairwise balances plus
the endpoint values. -/
theorem gk_lemma_2_4_two_three (a₁ a₂ b₁ b₂ b₃ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P₁ P₂ Q₁ Q₂ Q₃ : ℝ, 0 ≤ P₁ → 0 ≤ P₂ → 0 ≤ Q₁ → 0 ≤ Q₂ → 0 ≤ Q₃ →
      ∀ U : ℝ, 1 ≤ U → ∃ u : ℝ, 1 ≤ u ∧ u ≤ U ∧
        P₁ * u ^ a₁ + P₂ * u ^ a₂ + Q₁ * u ^ (-b₁) + Q₂ * u ^ (-b₂) + Q₃ * u ^ (-b₃) ≤
          C * ((P₁ ^ b₁ * Q₁ ^ a₁) ^ (1 / (a₁ + b₁)) + (P₁ ^ b₂ * Q₂ ^ a₁) ^ (1 / (a₁ + b₂)) +
            (P₁ ^ b₃ * Q₃ ^ a₁) ^ (1 / (a₁ + b₃)) + (P₂ ^ b₁ * Q₁ ^ a₂) ^ (1 / (a₂ + b₁)) +
            (P₂ ^ b₂ * Q₂ ^ a₂) ^ (1 / (a₂ + b₂)) + (P₂ ^ b₃ * Q₃ ^ a₂) ^ (1 / (a₂ + b₃)) +
            P₁ + P₂ + Q₁ * U ^ (-b₁) + Q₂ * U ^ (-b₂) + Q₃ * U ^ (-b₃)) := by
  sorry

end

end LeanLab.Song2020.SPLIT_lambda_sum_per_h
