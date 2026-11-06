import LeanLab.Halupczok2012.Decomp398a
import LeanLab.Halupczok2012.U1510Final

/-!
Supply decomposition for the sealed theorem_2.
The binary input is already split into major arc and minor arc energies.
This file splits the short interval distribution input at x to the 1 over 100.
Source: Perelli Pintz Salerno 1984 pages 530 to 538, especially display 5 on page 531.
The fixed small exponent follows the Huxley Iwaniec range printed on page 530.
https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0/
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp398c

open Finset
open scoped Classical

/-- LEAF. PPS1984 pages 530 to 531, the small modulus range removed before display 5.
At theta equal to 3 over 5, the printed Huxley Iwaniec range allows any fixed
modulus exponent below 1 over 20. Use 1 over 100 and cover longer windows.
Only the small moduli occur in this estimate. -/
theorem small_moduli :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ)),
        ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A) := by
  sorry

/-- LEAF. PPS1984 page 531 display 6 through page 538, the remaining modulus range.
The Heath Brown identity and the two polynomial estimates treat the moduli
above x to the 1 over 100 in the remaining part of the printed argument. -/
theorem large_moduli :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧ ∃ C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      Q ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => x ^ (1 / 100 : ℝ) < (q : ℝ)),
        ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A) := by
  sorry

/-- The two disjoint modulus ranges give the existing uniform PPS input. -/
theorem pps_uniform : PPS1984Uniform := by
  intro A ε hA hε
  obtain ⟨Cs, xs, hs⟩ := small_moduli A ε hA hε
  obtain ⟨B, hB, Cl, xl, hl⟩ := large_moduli A ε hA hε
  refine ⟨B, hB, Cs + Cl, max xs xl, ?_⟩
  intro x y Q hx hxy hyx hQ a h z ha hh hz
  have hsmall := hs x y Q ((le_max_left _ _).trans hx) hxy hyx a h z ha hh hz
  have hlarge := hl x y Q ((le_max_right _ _).trans hx) hxy hyx hQ a h z ha hh hz
  have he := sum_filter_add_sum_filter_not (Icc 1 ⌊Q⌋₊)
    (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ)) (fun q => ppsTerm (z q) (h q) q (a q))
  simp only [not_le] at he
  rw [← he]
  nlinarith

/-- Exact statement of the sealed theorem_2.
The proof reuses U1495 and U1496 and has no new reduction gap. -/
theorem theorem2 : Theorem2 :=
  theorem2_U1496 (theorem3_of_uniform pps_uniform) Decomp398a.pp1993_goldbach

end LeanLab.Halupczok2012.Decomp398c
