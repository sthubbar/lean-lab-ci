import LeanLab.Halupczok2012.Decomp398a
import LeanLab.Halupczok2012.U1510Final
import LeanLab.Halupczok2012.Resplit398c

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

/-- `ppsTerm` is an absolute value, hence nonnegative for every choice of `z`, `h`, `q`, `a`. -/
lemma ppsTerm_nonneg (z h : ℝ) (q : ℕ) (a : ℤ) : 0 ≤ ppsTerm z h q a := by
  exact abs_nonneg _

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

/-- The uniform PPS input, now from the re-split leaves of Resplit398c, which follow the cut
of PPS1984 page 531 on the conductor, displays 4, 5 and 6. The modulus cut of `small_moduli`
and `large_moduli` above does not match the paper and is no longer on the route;
the old wiring proof is kept in notes/burst-20261122/Halupczok2012-398c-resplit.md. -/
theorem pps_uniform : PPS1984Uniform :=
  Resplit398c.pps_uniform_of_leaves

/-- Exact statement of the sealed theorem_2.
The proof reuses U1495 and U1496 and has no new reduction gap. -/
theorem theorem2 : Theorem2 :=
  theorem2_U1496 (theorem3_of_uniform pps_uniform) Decomp398a.pp1993_goldbach

end LeanLab.Halupczok2012.Decomp398c
