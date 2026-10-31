/-
AI-written Lean code, Claude, 2026-10-19, run 20261019T1703Z-20733, unit U-1087, T1, P0027.
R. Li, On Chen's theorem, Goldbach's conjecture and almost prime twins II, arXiv 2405.05727 v4,
read in Claude in Chrome, and the version of record, Mathematical Reports 2026, imar.ro, read
by WebFetch; both carry the two slips below.
Slip 1, Section 5 final display: it subtracts S'₁₇, S'₁₈, S'₁₉, which Lemma 3.2 does not define;
Lemma 3.2 ends at S'₁₆, and the printed 5.1036 is the sixteen-term value, `final_combination_t13`.
Slip 2, (44) to (46): with the printed G₂ < 5.81637 of (49), the integrals give
S'₁₂ ≤ 1.9609569, S'₁₃ ≤ 1.6991135, S'₁₄ ≤ 0.1522132 by mpmath quadrature, above the printed
1.960955, 1.699112, 0.152213; the printed values match G₂ ≈ 5.816363, so the author's G₂ was
sharper than the printed bound. `t13_survives` shows Theorem 1.3's 5.1036 holds with the
bounds that do follow from the printed G₂ rounded up to 1.960957, 1.699114, 0.152214.
Both slips are cosmetic: the main result survives. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Li2024.Slips

/-- Theorem 1.3's final combination with the S'₁₂, S'₁₃, S'₁₄ bounds that follow from the printed
G₂ < 5.81637, each rounded up at the sixth decimal: still ≥ 5.1036. -/
theorem t13_survives :
    (5.1036 : ℝ) ≤ (3 * 6.737439 + 4.011646 + 0.875194 + 1.917212 + 0.282826) -
      (2 * 7.410929 + 2 * 0.925271 + 0.111039 + 1.169696 + 1.960957 + 1.699114 +
        2 * 0.152214 + 0.031709 + 0.245969) := by norm_num

/-- With any nonnegative S'₁₇, S'₁₈, S'₁₉, the printed nineteen-term display is at most the
sixteen-term combination of Lemma 3.2, so dropping the three undefined terms loses nothing. -/
theorem extra_terms_harmless {L a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    L - (a + b + c) ≤ L := by linarith

/-- The printed bounds are below what G₂ < 5.81637 gives: a margin check, the quadrature values
rounded down at the seventh decimal exceed the printed ones. -/
theorem printed_below : (1.960955 : ℝ) < 1.9609568 ∧ (1.699112 : ℝ) < 1.6991134 ∧
    (0.152213 : ℝ) < 0.1522131 := by norm_num

end LeanLab.Li2024.Slips
