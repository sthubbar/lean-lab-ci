import LeanLab.HelfgottMajor.SPLIT_vonMangoldt_tsum_eleven_tenths_le

/-!
# Split of `psi_le_rosser_schoenfeld` (`HelfgottMajor/SPLIT_vonMangoldt_tsum_eleven_tenths_le`)

The target is Rosser and Schoenfeld 1962, Theorem 12, display 3.35 on page 71:
`ψ(x) ≤ 1.03883 x` for `x > 0`.  Its proof, page 77 of the paper, has two ranges:

* `x ≤ 2000`: "By comparison with Gram's Table of `ψ(x)`, Theorem 12 was verified for
  `x ≤ 2000`", the maximum of `ψ(x)/x` there being taken at `x = 113`; since `ψ` is constant
  between integers this is a finite check on `N ≤ 2000`, leaf `psi_le_of_le_two_thousand`;
* `2000 ≤ x`: "one can complete the proof of Theorem 12 by proving that `ψ(x) ≤ 1.03882 x`
  for `2000 ≤ x`", from Theorem 18, Table III and display 4.12, leaf
  `psi_le_of_two_thousand_le`.

The reduction from real `x` to `⌊x⌋` and the assembly are proved here.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.SplitPsiRosserSchoenfeld

open Real

/-- LEAF: Rosser and Schoenfeld 1962, page 77, the range `x ≤ 2000` of Theorem 12, verified there
against Gram's table; on integers `N ≤ 2000`, `ψ(N) = log lcm(1, ..., N) ≤ 1.03883 N`, tight at
`N = 113` where `ψ(113)/113 = 1.038826...`.  MEDIUM: a finite computation, for instance as
`lcm(1, ..., N) ≤ exp(1.03883 N)` with rational bounds on `exp`. -/
theorem psi_le_of_le_two_thousand (N : ℕ) (hN : N ≤ 2000) :
    Chebyshev.psi N ≤ 1.03883 * N := by
  sorry

/-- LEAF: Rosser and Schoenfeld 1962, page 77, the range `2000 ≤ x` of Theorem 12,
`ψ(x) ≤ 1.03882 x`, from their Theorem 18, Table III and display 4.12, resting on the explicit
zeros of `ζ` below height 21 and an explicit zero free region.  HARD. -/
theorem psi_le_of_two_thousand_le (x : ℝ) (hx : 2000 ≤ x) :
    Chebyshev.psi x ≤ 1.03882 * x := by
  sorry

/-- `ψ` is constant between integers: `ψ(x) = ψ(⌊x⌋)`, since Mathlib's `Chebyshev.psi x` is the sum
of `Λ(n)` over `0 < n ≤ ⌊x⌋`. -/
theorem psi_eq_psi_floor (x : ℝ) : Chebyshev.psi x = Chebyshev.psi (⌊x⌋₊ : ℝ) := by
  rw [Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast]

/-- The parent leaf `psi_le_rosser_schoenfeld`, verbatim, from the two range leaves. -/
theorem psi_le_rosser_schoenfeld_split (x : ℝ) (hx : 0 < x) :
    Chebyshev.psi x ≤ 1.03883 * x := by
  by_cases h : 2000 ≤ x
  · have := psi_le_of_two_thousand_le x h
    linarith
  · have h' : x ≤ 2000 := (not_le.mp h).le
    have hfl : ⌊x⌋₊ ≤ 2000 := by
      have := Nat.floor_le_floor h'
      simpa using this
    rw [psi_eq_psi_floor]
    refine (psi_le_of_le_two_thousand _ hfl).trans ?_
    have := Nat.floor_le hx.le
    linarith

end LeanLab.HelfgottMajor.SplitPsiRosserSchoenfeld
