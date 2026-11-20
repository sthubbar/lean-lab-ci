import LeanLab.BS2022GRH.Flag1735
import LeanLab.BS2022GRH.DecompC169c

/-! AI wrote the Lean code. Goldbach is open.

Flag unit U-1735, run 20261120-flags2, part b, folder BS2022GRH.

Part 1. Named hypothesis for Broadbent et al. 2026, arXiv 2608.01498v1,
Table 2 p. 39, row log x0 equal to 40, column eta1, value 8.5536e-7.
Those values use Buthe's method as corrected in the Bhattacharjee thesis, p. 2.
Part 2. That row gives the printed BKLNW row 37 bound on every t at least 10^19,
the only range where DecompC169c uses ThetaInputs224.theta_table15_37.
Part 3. The large endpoint lower bound of Lemma 6 with the same constant
1.107533e-7, proved from the corrected row and the two other cited theta leaves,
all passed as explicit named hypotheses. -/

namespace LeanLab.BS2022GRH.Flag1735b
open Real Finset Classical LeanLab.BS2022GRH.Flag1735

/-- Named hypothesis. Plain math: for every x greater than e to the 40, the
absolute value of theta x minus x is at most 8.5536e-7 x over log x.
Source: Broadbent et al. 2026, arXiv 2608.01498v1, Table 2 p. 39, row 40,
column eta1. Vacuity: this is ThetaRow at exp 40, a nonempty range. -/
def Broadbent2026Row40 : Prop :=
  ∀ x : ℝ, exp 40 < x → |Chebyshev.theta x - x| ≤ 8.5536e-7 * x / log x

/-- Named hypothesis: the BKLNW Table 15 row log of 6e11, the exact statement of
ThetaInputs224.theta_table15_6e11. -/
def ThetaTable15Row6e11 : Prop :=
  ∀ x : ℝ, 6e11 < x → |Chebyshev.theta x - x| ≤ 6.9322e-5 * x / log x

/-- Named hypothesis: Buthe 2018 Theorem 2, the exact statement of
ThetaInputs224.theta_buthe_1e19. -/
def Buthe2018Thm2 : Prop :=
  ∀ x : ℝ, 1 ≤ x → x ≤ 1e19 → (0.05 : ℝ) * sqrt x < x - Chebyshev.theta x

theorem match_row6e11 : ThetaTable15Row6e11 ↔ ∀ x : ℝ, 6e11 < x →
    |Chebyshev.theta x - x| ≤ 6.9322e-5 * x / log x := Iff.rfl

theorem match_buthe : Buthe2018Thm2 ↔ ∀ x : ℝ, 1 ≤ x → x ≤ 1e19 →
    (0.05 : ℝ) * sqrt x < x - Chebyshev.theta x := Iff.rfl

theorem exp40_lt_1e19 : exp 40 < (1e19 : ℝ) := by
  calc exp 40 < exp (log (1e19 : ℝ)) := exp_lt_exp.mpr (by
        linarith [LowerMertens224.log_split_lower])
    _ = 1e19 := exp_log (by norm_num)

/-- The corrected row gives the printed row 37 bound for every t at least 10^19. -/
theorem row37_on_1e19 (h : Broadbent2026Row40) (t : ℝ) (ht : (1e19 : ℝ) ≤ t) :
    |Chebyshev.theta t - t| ≤ 8.6315e-7 * t / log t := by
  have hx : exp 40 < t := lt_of_lt_of_le exp40_lt_1e19 ht
  have hpos : 0 < t := lt_trans (exp_pos 40) hx
  have hlog : 0 < log t := log_pos (by linarith)
  refine le_trans (h t hx) ?_
  apply div_le_div_of_nonneg_right _ hlog.le
  exact mul_le_mul_of_nonneg_right (by norm_num) hpos.le

/-- CONDITIONAL route: the large endpoint lower bound of Lemma 6, p. 1219 display 3,
with the sealed constant 1.107533e-7, from the corrected 2026 row. -/
theorem reciprocal_lower_infinite_corrected (h40 : Broadbent2026Row40)
    (h6 : ThetaTable15Row6e11) (hb : Buthe2018Thm2) (x : ℝ) (hx : 1e12 < x) :
    log (log x) + DecompC169c.mertensConstant - 1.107533e-7 ≤
      ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p := by
  apply LowerMertens224.inclusive_to_strict_lower DecompC169c.mertensConstant
    1.107533e-7 1e12 (by norm_num) _ hx
  intro y hy
  apply LowerMertens224.reciprocal_lower_inclusive DecompC169c.mertensConstant
    DecompC169c.reciprocal_limit hy
  · intro t ht
    exact h6 t (by linarith)
  · intro t ht
    exact row37_on_1e19 h40 t ht
  · intro t ht ht1
    have h := hb t (by linarith) ht1
    nlinarith [sqrt_nonneg t]

end LeanLab.BS2022GRH.Flag1735b
