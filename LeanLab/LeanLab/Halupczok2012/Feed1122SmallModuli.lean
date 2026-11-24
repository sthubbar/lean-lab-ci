import LeanLab.Halupczok2012.U1495PPS

/-!
Feed split of `Decomp398c.small_moduli`, burst-20261122.
Source: Perelli Pintz Salerno 1984 pages 530 to 531, the small modulus range
removed before display 5, which rests on the Huxley Iwaniec short interval range
for primes in progressions printed on page 530.
https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0/
The moduli at most x to the 1 over 100 are split at a power of log x into the
Siegel Walfisz range and the zero density range. Both leaves are sums of
nonnegative terms over sub ranges of the parent range.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Feed1122SmallModuli

open Finset
open scoped Classical

/-- LEAF: PPS1984 page 530, the Siegel Walfisz part of the small modulus range,
moduli at most a fixed power of log x, short interval prime number theorem in
progressions with y at least x to the 3 over 5 plus epsilon. Class HARD. -/
theorem siegel_walfisz_range :
    ∀ A D ε : ℝ, 0 < A → 0 < ε → ∃ C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∑ q ∈ ((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ))).filter
          (fun q : ℕ => (q : ℝ) ≤ Real.log x ^ D),
        ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A) := by
  sorry

/-- LEAF: PPS1984 pages 530 to 531, the zero density part of the small modulus range,
moduli between a power of log x and x to the 1 over 100, Huxley Iwaniec range at
theta 3 over 5 with the exceptional zero handled by Siegel. Class HARD. -/
theorem zero_density_range :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ D C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∑ q ∈ ((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ))).filter
          (fun q : ℕ => Real.log x ^ D < (q : ℝ)),
        ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A) := by
  sorry

/-- The two leaves give `Decomp398c.small_moduli`, same statement. -/
theorem small_moduli_of_leaves :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ)),
        ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A) := by
  intro A ε hA hε
  obtain ⟨D, C2, x2, h2⟩ := zero_density_range A ε hA hε
  obtain ⟨C1, x1, h1⟩ := siegel_walfisz_range A D ε hA hε
  refine ⟨C1 + C2, max x1 x2, ?_⟩
  intro x y Q hx hxy hyx a h z ha hh hz
  have hs1 := h1 x y Q ((le_max_left _ _).trans hx) hxy hyx a h z ha hh hz
  have hs2 := h2 x y Q ((le_max_right _ _).trans hx) hxy hyx a h z ha hh hz
  have he := sum_filter_add_sum_filter_not
    ((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ)))
    (fun q : ℕ => (q : ℝ) ≤ Real.log x ^ D) (fun q => ppsTerm (z q) (h q) q (a q))
  simp only [not_le] at he
  rw [← he]
  have hr : (C1 + C2) * y * Real.log x ^ (-A) =
      C1 * y * Real.log x ^ (-A) + C2 * y * Real.log x ^ (-A) := by ring
  linarith

end LeanLab.Halupczok2012.Feed1122SmallModuli

#print axioms LeanLab.Halupczok2012.Feed1122SmallModuli.small_moduli_of_leaves
