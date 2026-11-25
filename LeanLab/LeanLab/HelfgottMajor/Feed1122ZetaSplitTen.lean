import LeanLab.HelfgottMajor.Feed1122ZetaEM6

/-!
# Split of `zeta_zero_free_seven_half_fourteen` at height `21/2`, burst 20261122 S137

`Feed1122ZetaEM6` leaves the HARD LEAF `zeta_zero_free_seven_half_fourteen`: no zero of `ζ` in
the open strip has ordinate in `(15/2, 14]`, Helfgott arXiv 1305.2897v4 Section 4.6 page 56 with
Platt's verification and the first zero tables of Gram 1903 and Backlund 1914.

This file cuts that window at `21/2`, where a cheaper certificate is in reach.

* LEAF MEDIUM `zeta_zero_free_seven_half_ten_half`, the window `(15/2, 21/2]`. Proof plan, S137
  numerics: write `ζ(s) = 1 + 2^(-s) H(s)` with `H(s) = Σ_{n ≥ 2} (n/2)^(-s)`. At a zero
  `|ζ(s) - 1| = 1`, so `|H(s)| = 2^σ ≥ 1 + 2σ/3`. The Euler Maclaurin formula from `n = 2`,
  Edwards 1974 Chapter 6, gives `H(s) = 2/(s-1) + 1/2 + Σ_{j ≤ k} B_{2j}/(2j)! (s)_{2j-1} 2^(1-2j)`
  up to an error at most `∏_{j<2k} |s+j| |B_{2k}| / (2k)! · 2^(1-2k) / (σ + 2k - 1)`, with no
  phase factor left. With `k = 6` the main term plus the error stays below `1 + 2σ/3` on
  `[0,1] × [15/2, 21/2]`, margin about `0.05` near `21/2`, so the proof is a polynomial box
  certificate like those of `Feed1122ZetaFourSix` and `Feed1122ZetaEM6`, plus six more
  integrations by parts on `(2, ∞)`.
* LEAF HARD `zeta_zero_free_ten_half_fourteen`, the window `(21/2, 14]`. Here `|ζ(s) - 1|`
  exceeds `1` near `σ = 0`, so the two term splitting fails and certified enclosures of
  `3^(-s)` and later terms are needed.
* PROVED assembly `zeta_zero_free_seven_half_fourteen_s137`, exactly the statement of
  `Feed1122ZetaEM6.zeta_zero_free_seven_half_fourteen`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaSplitTen

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], and the
first zero tables of `ζ`, Gram 1903 and Backlund 1914, read on the window `(15/2, 21/2]`: no zero
of `ζ` in the open strip has ordinate in `(15/2, 21/2]`. Class MEDIUM: the file header gives a
phase free proof by the Euler Maclaurin formula from `n = 2` with six Bernoulli terms and a
polynomial box certificate, margin about `0.05`, S137 numerics. -/
theorem zeta_zero_free_seven_half_ten_half (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 15 / 2 < ρ.im) : 21 / 2 < ρ.im := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], and the
first zero tables of `ζ`, Gram 1903 and Backlund 1914: no zero of `ζ` in the open strip has
ordinate in `(21/2, 14]`; the first ordinate is `14.1347…`. Class HARD: a certified zero free
rectangle needing enclosures of `n^(-s)` for `n ≥ 3`. -/
theorem zeta_zero_free_ten_half_fourteen (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 21 / 2 < ρ.im) : 14 < ρ.im := by
  sorry

/-- `Feed1122ZetaEM6.zeta_zero_free_seven_half_fourteen`, exactly its statement, from the two
leaves of this file. -/
theorem zeta_zero_free_seven_half_fourteen_s137 (ρ : ℂ) (h0 : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him : 15 / 2 < ρ.im) : 14 < ρ.im :=
  zeta_zero_free_ten_half_fourteen ρ h0 hre0 hre1
    (zeta_zero_free_seven_half_ten_half ρ h0 hre0 hre1 him)

end LeanLab.HelfgottMajor.Feed1122ZetaSplitTen
