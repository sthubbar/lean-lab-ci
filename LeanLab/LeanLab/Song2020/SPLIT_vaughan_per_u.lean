/-
AI wrote the Lean code. OMOS repair of claude/Song2020-vaughan_per_u, 2026-11-13.
Source: https://arxiv.org/pdf/2012.06322, printed pages 5 through 8.
The two analytic steps that Decomp139 carried as sorry are stated in this new file, so that
the existing file Decomp139 gains no sorry and proves its own steps from these leaves.
The definitions the leaves mention are copied here verbatim from Decomp139, since this file
cannot import the file that imports it; Decomp139 transfers a leaf to its own statements by
unfolding the two copies, which have the same bodies.

s1_lambda_reduction, page 5, the displays from "For S1, we first observe" to "We have shown
so far": partial summation in the weight c x to the 1 minus gamma, the bound a_h at most K
over h for the Fourier coefficients, the bound of e of h times the difference of x plus 1 to
the gamma and x to the gamma minus 1 by h x to the gamma minus 1, and the passage from primes
to the von Mangoldt function. The paper writes the maximum over centred windows and a saving
1 over log n; this form keeps instead the initial segments that partial summation really
produces, drops the log saving, and writes out the prime power error as K H n to the 1/2,
which the paper absorbs into its O of n to the 3/2 minus gamma. Any bound B on the von
Mangoldt sums for 1 at most |h| at most H then bounds S1. The factor n to the epsilon on the
B sum was added in the check of 2026-11-12: for y close to n/3 the window reaches down to
small x, and the total variation of the partial summation weight x to the 1 minus gamma times
e of h times the gamma difference minus 1 is then of size |h| log n, not |h|; the paper's y is
a power of n below 1, where this loss does not arise, and n to the epsilon absorbs it.

vaughan_uv, pages 5 to 7, the bounds for the three Vaughan pieces with both parameters u and v
free, 1 at most u, 1 at most v and u v at most n, before the choice v = (n/u)^{1/2}: the
Sigma 1 display of page 6, u |h|^{1/2} x^{gamma/2-1} y plus x^{1-gamma/2} |h|^{-1/2}, with its
log squared factor absorbed in n to the epsilon, plus the display for x^{-epsilon} times
Sigma 2 plus Sigma 3 on page 7, n v^{-1/2} plus n^{1/2} (u v)^{1/2} plus the four u and h
monomials. Here x is replaced by n, since x is of size n over 3. Published inputs: Dirichlet
approximation and the Ramanujan sum splitting, page 5; the Vaughan identity, the paper's
Lemma 3.2, page 5; Iwaniec and Kowalski Corollary 8.13 for Sigma 1, page 6; dyadic division
into T(R,S) and Graham and Kolesnik Lemma 2.5, page 6; Iwaniec and Kowalski Corollary 8.13 for
the inner r sum and Graham and Kolesnik Lemma 2.4 for L, page 7.

Binary Goldbach is open.
-/
import LeanLab.Song2020.Characteristic139

namespace LeanLab.Song2020.SPLIT_vaughan_per_u

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

/-- LEAF: Song 2020, page 5, from "For S1, we first observe" to "We have shown so far":
partial summation over the prime window with a_h at most K over h reduces S1 to the von
Mangoldt sums over an initial segment, with n to the epsilon absorbing the weight variation
when y is close to n/3. The header of this file carries the full reading. -/
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

/-- LEAF: Song 2020, pages 6 and 7, with u and v both free: the Sigma 1 display and the
display for x to the minus epsilon times Sigma 2 plus Sigma 3, before the choice
v = (n/u)^{1/2}. The header of this file carries the full reading. -/
theorem vaughan_uv :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → u * v ≤ n →
            ‖lambdaSum γ n y α h t‖ ≤ C * (n : ℝ) ^ ε *
              (u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
                (n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2) +
                (n : ℝ) * v ^ (-(1 : ℝ) / 2) + (n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2) +
                (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  sorry

end

end LeanLab.Song2020.SPLIT_vaughan_per_u
