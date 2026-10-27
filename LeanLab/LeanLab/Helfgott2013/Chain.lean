/-
P0001 H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2, Section 7:
the major arc total (7.24) and (7.25), the minor arc total (7.48) and the conclusion of
Section 7.4 joined into one implication between real numbers. Every analytic input of the
paper is a hypothesis; only the arithmetic linking them is proved.

AI-written Lean code, Claude, 2026-10-18, cloud session 20261018T1720Z-cloud5.
Checked only by the Lean kernel. Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Helfgott2013.SectionSeven

namespace LeanLab.Helfgott2013
open Real

/-- Section 7 from the analytic inputs to the last display. For odd `N ≥ 10^27`, `x` as in
(7.14):
* `hC`, (7.24): `C₀ C_{η◦,η*} ≥ 1.058298/κ`;
* `hMaj`, (7.24): the major arc integral `I_maj` is `C₀ C x² + O*(7.881 · 10^-7 x²)`;
* `hMin`, (7.48) and Theorem 6.3: the minor arc part `I_min` satisfies
  `|I_min| ≤ Z ≤ 0.97392 x²/κ`;
* `hE`, (7.50) with [RS62]: the part `E` with some `nᵢ` even or non-prime is at most
  `7.3306 N^{3/2} log N`.
Then the odd prime part `I_maj + I_min − E` is at least `0.000422 N² > 0`. PROVED as an
implication; the paper's analytic results are the hypotheses. -/
theorem section7_chain {N C Imaj Imin Z E : ℝ} (hN : 1e27 ≤ N)
    (hC : 1.058298 / κ ≤ C)
    (hMaj : |Imaj - C * xOf N ^ 2| ≤ 7.881e-7 * xOf N ^ 2)
    (hMin : |Imin| ≤ Z) (hZ : Z ≤ 0.97392 * xOf N ^ 2 / κ)
    (hE : E ≤ 7.3306 * N ^ (3 / 2 : ℝ) * Real.log N) :
    0.000422 * N ^ 2 ≤ Imaj + Imin - E ∧ 0 < Imaj + Imin - E := by
  have hx2 : 0 ≤ xOf N ^ 2 := sq_nonneg _
  have hk0 : (0 : ℝ) < κ := by unfold κ; norm_num
  -- (7.25): `I_maj ≥ 1.058259 x²/κ`
  have h1 := (abs_le.mp hMaj).1
  have hCx : 1.058298 / κ * xOf N ^ 2 ≤ C * xOf N ^ 2 := mul_le_mul_of_nonneg_right hC hx2
  have hmt := major_total
  have hmt' : 1.058259 / κ * xOf N ^ 2 ≤ (1.058298 / κ - 7.881e-7) * xOf N ^ 2 :=
    mul_le_mul_of_nonneg_right hmt hx2
  have hMaj' : 1.058259 * xOf N ^ 2 / κ ≤ Imaj := by
    have e : 1.058259 * xOf N ^ 2 / κ = 1.058259 / κ * xOf N ^ 2 := by ring
    rw [e]; nlinarith
  have hMin' : |Imin| ≤ 0.97392 * xOf N ^ 2 / κ := le_trans hMin hZ
  have hT := arcs_combine hMaj' hMin'
  exact conclusion_chain hN hT hE

end LeanLab.Helfgott2013
