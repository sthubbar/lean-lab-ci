/-
AI wrote the Lean code. CODEX task139, 2026-10-27, leaf module split by OMOS repair 20261113.
Supply leaves for the S1 estimate on printed pages 5 through 8 of Song 2020, and the
definitions the two leaves are stated with, kept in the namespace of Decomp139 so that
every statement there elaborates unchanged.
Source: https://arxiv.org/pdf/2012.06322.
Binary Goldbach is open.
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

end

end LeanLab.Song2020.Decomp139

namespace LeanLab.Song2020.S1Leaves139

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Song2020.Decomp139
open scoped Classical

noncomputable section

/-
Song 2020, page 5, the displays from "For S1, we first observe" to
"We have shown so far": partial summation in the weight c x to the 1 minus gamma,
the bound a_h at most K over h for the Fourier coefficients, the bound of
e of h times the difference of x plus 1 to the gamma and x to the gamma minus 1
by h x to the gamma minus 1, and the passage from primes to the von Mangoldt function.
The paper writes the maximum over centred windows and a saving 1 over log n; this form
keeps instead the initial segments that partial summation really produces, drops the
log saving, and writes out the prime power error as K H n to the 1/2, which the
paper absorbs into its O of n to the 3/2 minus gamma. Any bound B on the von Mangoldt
sums for 1 at most |h| at most H then bounds S1. The factor n to the epsilon on the B sum
was added in the check of 2026-11-12: for y close to n/3 the window reaches down to small x,
and the total variation of the partial summation weight x to the 1 minus gamma times
e of h times the gamma difference minus 1 is then of size |h| log n, not |h|; the paper's
y is a power of n below 1, where this loss does not arise, and n to the epsilon absorbs it.
-/

/-- LEAF: Song 2020 page 5, the reduction of S1 to von Mangoldt sums: partial summation
in the weight, the coefficient bound a_h, the gamma difference derivative bound and the
passage from primes to Lambda. The full text of the step, with its decisions, is in the
block comment just above. -/
theorem s1_lambda_reduction139 :
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

/-
Song 2020, pages 5 to 8, the per h estimate displayed at the top of page 8:
x to the minus epsilon times Sigma 1 plus Sigma 2 plus Sigma 3 is bounded by the ten
monomials of perH at k equal to the absolute value of h. Published inputs, in the order the
paper applies them: Dirichlet approximation of alpha by a over q with q at most log n and the
splitting into the Ramanujan type sums S of a plus b and q, page 5; the Vaughan identity,
the paper's Lemma 3.2 with u v at most n, page 5; Iwaniec and Kowalski Corollary 8.13 for
the type I sum Sigma 1, page 6; dyadic division of Sigma 2 and Sigma 3 into the bilinear
sums T of R and S, page 6; Graham and Kolesnik Lemma 2.5, the Weyl differencing
inequality for T of R and S, page 6; Iwaniec and Kowalski Corollary 8.13 for the inner sum
over r, page 7; and Graham and Kolesnik Lemma 2.4 for the choices of L, v and u, pages 7
and 8.
-/

/-- LEAF: Song 2020 pages 5 to 8, the per h estimate: x to the minus epsilon times
Sigma 1 plus Sigma 2 plus Sigma 3 is bounded by the ten monomials of perH. Published
inputs: Dirichlet approximation, the Vaughan identity, Iwaniec and Kowalski Corollary
8.13, Graham and Kolesnik Lemmas 2.4 and 2.5. The full text is in the block comment
just above. -/
theorem lambda_sum_per_h139 :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ,
            ‖lambdaSum γ n y α h t‖ ≤ C * (n : ℝ) ^ ε * perH γ n y |(h : ℝ)| := by
  sorry

end

end LeanLab.Song2020.S1Leaves139
