import LeanLab.ExceptionalSet.EvenSupplyJ200

/-!
The one open input of `DecompJ200.leaf_major_even_coefficient`, P0082 Lemma 7, pages 362 to 364.
Source: J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, https://doi.org/10.5802/aif.1621.

The proof of Lemma 7 has three parts.
1. Lemma 5, pages 360 to 362, displays (16) to (19): the mean of the error envelopes `r₁, r₂`
   of Lemma 3 over the window. Proved in `EvenSupplyJ200.error_mean`, CONDITIONAL ON `Lemma4`.
2. Display (22), page 364: few `n` have `(ν_n, r)` large when `r > ℰ^{1/7}`. Proved in
   `EvenSupplyJ200.large_gcd_from_lemma4`, CONDITIONAL ON `Lemma4`.
3. The pointwise lower bound in cases (i), (ii a), (ii b) and (ii d), from Lemma 2 and Lemma 3,
   which the paper takes from Montgomery and Vaughan 1975 [MV]. This is the LEAF below.

`EvenSupplyJ200.even_coefficient_from_inputs` assembles the three parts. The leaf statement is
the hypothesis `hpoint` of that theorem and of `Decomp467b`, and is word for word the existing
leaf `Supply465.leaf_pointwise` of `Decomp465a`, which `DecompJ200` cannot import.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.LEAFEvenCoefficientInputs

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.EvenSupplyJ200 (window divisorError)

/-- LEAF. CITED-dependent. P0082 pages 362 to 364, proof of Lemma 7, cases (i), (ii a), (ii b)
and (ii d), display (20) with the Γ errors `r₁, r₂` of Lemma 3 kept as the explicit envelope
`divisorError` of displays (14) and (15), and display (21).
Here `r` is the conductor of the exceptional character modulo at most `P = X^{6δ}`, or `r = 1`
when there is none, case (i). For the even one `ν_n + j` of `ν_n, ν_n + 1`, at most `X`, one has
`R₁(ν_n + j) ≫ X ℰ^{-1/10}` up to `X` times the error envelope, unless `r > ℰ^{1/7}` and
`(ν_n + j, r) ≥ r/24`; that remaining case (ii c) is the one display (22) counts, since an empty
product in (21) forces `(ν_n, r)` to be at least a fixed fraction of `r`, with `r = 2^k u`, `u` odd
squarefree and `k ≤ 3`; the fraction `1/24` is exactly the paper's, page 363 case (ii c),
checked on the PDF page. The analytic content is Lemma 2 and Lemma 3 of the
paper, page 358, which the paper cites from [MV] H. L. Montgomery and R. C. Vaughan, The
exceptional set in Goldbach's problem, Acta Arith. 27 (1975) 353-370, sections 6 and 8, together
with the bound (10) for `1 - β̃` and the singular series facts (11) to (13).
No counting and no first moment estimate is included. Same statement as
`Supply465.leaf_pointwise`. -/
theorem leaf_pointwise (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) ∧
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              ((r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) ∨
                (Int.gcd (nu γ n + j) r : ℝ) < (r : ℝ) / 24) →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  sorry

end LeanLab.ExceptionalSet.LEAFEvenCoefficientInputs
