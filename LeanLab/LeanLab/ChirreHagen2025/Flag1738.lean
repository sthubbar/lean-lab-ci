import LeanLab.ChirreHagen2025.Decomp429e

/-!
Flag unit U-1738, run 20261120-flags3, ChirreHagen2025, paper P0075.
Source: JRT 2023 page 3 Lemma 9 and page 4 Lemma 10, Ramare 2013 pages 118 to 120.

Part A. Verdict on the Gemini flag. The flag says `Decomp429e.mangoldt_psi_transfer`
is FALSE. Its evidence is that Ramare's page 120 auxiliary integral comparison, and so
the printed bound for the zero tail, fails at large log x. That is a fault of one proof
step, already proved in `Audit391b.not_printed_auxiliary_integral_bound`. It is not a
counterexample to the sealed inequality, which speaks about the actual weighted Mangoldt
sum. By the explicit formula, the left side minus the psi term is minus the sum over zeros
of x to the rho minus one over rho times rho minus one, plus terms bounded by log 2 pi over x.
Under RH that zero sum is at most 0.0462 over the square root of x, inside the 0.047 budget,
so the sealed statement holds under RH with room to spare and no negation can be proved.
The flag is wrong as a FALSE flag. The statement stays OPEN.

Part B. The transfer is accepted as a NAMED HYPOTHESIS, with a match theorem, and the
consumer `Decomp358d.mangoldt_large_range`, restated in Decomp429e, is proved below from
it and the two cited pure psi estimates as explicit arguments. CONDITIONAL, never PROVED.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.ChirreHagen2025.Flag1738

open ArithmeticFunction LeanLab.ChirreHagen2025.Decomp429e

/-- Named hypothesis, the exact sealed statement of `Decomp429e.mangoldt_psi_transfer`.
Twin: for every real x at least 100000, the sum of Lambda of n over n for n up to x,
minus log x, plus Euler's constant, is at most the relative psi error, plus 0.047 over
the square root of x, plus log 2 pi plus 0.0001 over x, plus the zero tail error.
Source JRT page 3 Lemma 9, proof in Ramare 2013 pages 118 to 120. CITED. -/
def MangoldtPsiTransferF1738 : Prop :=
  ∀ x : ℝ, 100000 ≤ x →
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) - Real.log x +
        Real.eulerMascheroniConstant ≤
      |Chebyshev.psi x - x| / x + 0.047 / Real.sqrt x +
        (Real.log (2 * Real.pi) + 0.0001) / x + zeroTailError x

/-- Named hypothesis, sealed `Decomp429e.psi_finite_range`, JRT page 3 Lemma 7,
Buthe Theorem 2. CITED. -/
def PsiFiniteRangeF1738 : Prop :=
  ∀ x : ℝ, 100000 ≤ x → x ≤ 10 ^ 19 → |Chebyshev.psi x - x| ≤ 0.94 * Real.sqrt x

/-- Named hypothesis, sealed `Decomp429e.psi_logarithmic_error`, JRT page 2 Lemma 6,
Broadbent and collaborators Table 15. CITED. -/
def PsiLogErrorF1738 : Prop :=
  ∀ x : ℝ, 100000 ≤ x → |Chebyshev.psi x - x| ≤ 0.64673 * x / Real.log x ^ 2

/-- Match check: the named hypothesis is exactly the sealed transfer statement.
Depends on the sealed open leaf and only checks the match. -/
theorem transfer_match_f1738 : MangoldtPsiTransferF1738 :=
  fun x hx => mangoldt_psi_transfer x hx

/-- Match check for the finite range psi leaf. -/
theorem finite_match_f1738 : PsiFiniteRangeF1738 :=
  fun x hx hxt => psi_finite_range x hx hxt

/-- Match check for the logarithmic psi leaf. -/
theorem log_match_f1738 : PsiLogErrorF1738 :=
  fun x hx => psi_logarithmic_error x hx

/-- Vacuity instance: the hypothesis range is nonempty, and the finite psi range too. -/
theorem vacuity_f1738 : ∃ x : ℝ, 100000 ≤ x ∧ x ≤ 10 ^ 19 := ⟨100000, le_rfl, by norm_num⟩

/-- Consumer, the exact statement of `Decomp429e.mangoldt_large_range`, which is
`Decomp358d.mangoldt_large_range`. CONDITIONAL ON the three named hypotheses. -/
theorem mangoldt_large_range_f1738 (hT : MangoldtPsiTransferF1738)
    (hF : PsiFiniteRangeF1738) (hL : PsiLogErrorF1738) (m : ℕ) (hm : 100000 ≤ m) :
    (∑ n ∈ Finset.Icc 1 m, vonMangoldt n / (n : ℝ)) ≤
      Real.log (m : ℝ) - Real.eulerMascheroniConstant +
        0.67 / Real.log (m : ℝ) ^ 2 := by
  have hm' : (100000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hpsi : |Chebyshev.psi m - (m : ℝ)| / (m : ℝ) ≤
      if (m : ℝ) ≤ 10 ^ 19 then 0.94 / Real.sqrt m else 0.64673 / Real.log (m : ℝ) ^ 2 := by
    split_ifs with hsmall
    · have hp := hF m hm' hsmall
      calc
        _ ≤ (0.94 * Real.sqrt m) / (m : ℝ) :=
          div_le_div_of_nonneg_right hp hm0.le
        _ = _ := by
          field_simp
          nlinarith [Real.sq_sqrt hm0.le]
    · have hp := hL m hm'
      have hh := div_le_div_of_nonneg_right hp hm0.le
      convert hh using 1 <;> field_simp
  have htransfer := hT m hm'
  simp only [Nat.floor_natCast] at htransfer
  have hbudget := transfer_numeric_budget m hm'
  linarith

end LeanLab.ChirreHagen2025.Flag1738
