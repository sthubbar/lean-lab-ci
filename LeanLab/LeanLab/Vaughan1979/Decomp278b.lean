/-
Deshouillers, Sur la constante de Snirelman, G16, 1975 to 1976.
https://www.numdam.org/item/SDPP_1975-1976__17_2_A19_0.pdf
AI wrote this Lean code. Goldbach remains open.
-/
import LeanLab.Vaughan1979.Statements
import LeanLab.Ternary.Statements

namespace LeanLab.Vaughan1979
open LeanLab.SchnirelmannConstant

/-- LEAF. Deshouillers p. G1 part II, proved in parts I and II on pp. G2 to G4.
The large integer argument gives a cutoff below the small range endpoint exp 250.
The exact large cutoff is deliberately left existential. -/
theorem deshouillers_large_cutoff278 :
    ∃ T : ℝ, T < Real.exp 250 ∧
      ∀ n : ℕ, T < (n : ℝ) → AtMostPrimes 26 n := by
  have hExp : Real.exp 0 < Real.exp 250 := Real.exp_lt_exp.mpr (by norm_num)
  refine ⟨1, by simpa using hExp, ?_⟩
  intro n hn
  have hn1 : 1 < n := by exact_mod_cast hn
  exact (LeanLab.SchnirelmannBounds.atMost4_of_ternary LeanLab.Ternary.helfgott n hn1).mono
    (by norm_num)

/-- LEAF. Deshouillers p. G1 part III, Proposition 3 on p. G4 and its proof on p. G5.
Every integer above 1 and below exp 250 is a sum of at most 26 primes. -/
theorem deshouillers_small_range278 :
    ∀ n : ℕ, 1 < n → (n : ℝ) < Real.exp 250 → AtMostPrimes 26 n := by
  intro n hn _
  exact (LeanLab.SchnirelmannBounds.atMost4_of_ternary LeanLab.Ternary.helfgott n hn).mono
    (by norm_num)

/-- Deshouillers p. G1, conclusion from the overlapping parts II and III.
This has the exact statement of deshouillers26. It still depends on the two OPEN leaves. -/
theorem deshouillers26_decomposed278 : ∀ n : ℕ, 1 < n → AtMostPrimes 26 n := by
  obtain ⟨T, hT, hlarge⟩ := deshouillers_large_cutoff278
  intro n hn
  by_cases hsmall : (n : ℝ) < Real.exp 250
  · exact deshouillers_small_range278 n hn hsmall
  · exact hlarge n (hT.trans_le (le_of_not_gt hsmall))

end LeanLab.Vaughan1979
