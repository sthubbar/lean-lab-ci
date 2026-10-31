/-
P0023 Liu, Wang 2002, Acta Arith. 105, 133-175, Theorem 1: every odd integer `≥ e^3100`
is a sum of three primes. The paper's text was NOT obtained in this session; the IMPAN
download link given by EuDML, https://www.impan.pl/download/pdf/aa105-2-3, returns 404.
This file proves only the explicit numerics around the printed threshold `e^3100`:
* `2.055 · 10^1346 < e^3100 < 2.056 · 10^1346`, certifying the lab's `≈ 2.055 · 10^1346`;
* `e^3100 < 10^1347`, so Liu-Wang's printed bound implies the bound `V = 10^1347` announced in
  T. Z. Wang's HKU seminar abstract of 18 October 2001;
* Helfgott 1312.7748 p. 3 rounds Liu-Wang to `2 · 10^1346`; that is smaller than `e^3100`,
  already proved as `HelfgottOverview.liuWang_rounding`, not duplicated here.
AI-written Lean code, Claude, 2026-10-20, session 20261020T1914Z-cloud49, unit U-6715.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Ternary.Statements

namespace LeanLab.LiuWang2002
open LeanLab.Ternary

theorem e_hi : Real.exp 1 ≤ ((27182818286 : ℕ) : ℝ) / 10 ^ 10 := by
  have := Real.exp_one_lt_d9; push_cast; norm_num at this ⊢; linarith

theorem e_lo : ((27182818283 : ℕ) : ℝ) / 10 ^ 10 ≤ Real.exp 1 := by
  have := Real.exp_one_gt_d9; push_cast; norm_num at this ⊢; linarith

/-- `e^m ≤ (a / 10^d)^m` from `e ≤ a / 10^d`. -/
theorem exp_nat_le {a d m : ℕ} (he : Real.exp 1 ≤ (a : ℝ) / 10 ^ d) :
    Real.exp m ≤ (a : ℝ) ^ m / 10 ^ (d * m) := by
  rw [← Real.exp_one_pow, pow_mul, ← div_pow]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le he m

/-- `(a / 10^d)^m ≤ e^m` from `a / 10^d ≤ e`. -/
theorem exp_nat_ge {a d m : ℕ} (he : (a : ℝ) / 10 ^ d ≤ Real.exp 1) :
    (a : ℝ) ^ m / 10 ^ (d * m) ≤ Real.exp m := by
  rw [← Real.exp_one_pow, pow_mul, ← div_pow]
  exact pow_le_pow_left₀ (by positivity) he m

/-- Integer certificate for a lower bound `c · 10^k < e^m`. -/
theorem lt_exp_nat {m d a c k : ℕ} (he : (a : ℝ) / 10 ^ d ≤ Real.exp 1)
    (h : c * 10 ^ k * 10 ^ (d * m) < a ^ m) : (c : ℝ) * 10 ^ k < Real.exp m := by
  have hR : (c : ℝ) * 10 ^ k * 10 ^ (d * m) < (a : ℝ) ^ m := by exact_mod_cast h
  refine lt_of_lt_of_le ?_ (exp_nat_ge he)
  rw [lt_div_iff₀ (by positivity)]
  exact hR

/-- Integer certificate for an upper bound `e^m < c · 10^k`. -/
theorem exp_nat_lt {m d a c k : ℕ} (he : Real.exp 1 ≤ (a : ℝ) / 10 ^ d)
    (h : a ^ m < c * 10 ^ k * 10 ^ (d * m)) : Real.exp m < (c : ℝ) * 10 ^ k := by
  have hR : (a : ℝ) ^ m < (c : ℝ) * 10 ^ k * 10 ^ (d * m) := by exact_mod_cast h
  refine lt_of_le_of_lt (exp_nat_le he) ?_
  rw [div_lt_iff₀ (by positivity)]
  exact hR

/-- `2.055 · 10^1346 < e^3100`. PROVED, kernel integer check. -/
theorem exp3100_gt : (2055 : ℝ) * 10 ^ 1343 < Real.exp 3100 := by
  have := lt_exp_nat (m := 3100) (d := 10) (a := 27182818283) (c := 2055) (k := 1343) e_lo
    (by decide +kernel)
  simpa using this

/-- `e^3100 < 2.056 · 10^1346`. PROVED, kernel integer check. -/
theorem exp3100_lt : Real.exp 3100 < (2056 : ℝ) * 10 ^ 1343 := by
  have := exp_nat_lt (m := 3100) (d := 10) (a := 27182818286) (c := 2056) (k := 1343) e_hi
    (by decide +kernel)
  simpa using this

/-- `10^1346 < e^3100 < 10^1347`: Liu-Wang's threshold has 1347 decimal digits. PROVED. -/
theorem exp3100_digits : (10 : ℝ) ^ 1346 < Real.exp 3100 ∧ Real.exp 3100 < 10 ^ 1347 := by
  constructor
  · refine lt_trans ?_ exp3100_gt
    rw [show (10 : ℝ) ^ 1346 = 10 ^ 3 * 10 ^ 1343 by rw [← pow_add]]
    gcongr; norm_num
  · refine exp3100_lt.trans ?_
    rw [show (10 : ℝ) ^ 1347 = 10 ^ 4 * 10 ^ 1343 by rw [← pow_add]]
    gcongr; norm_num

/-- Liu-Wang's printed `e^3100` implies T. Z. Wang's 2001 announced `V = 10^1347`.
A link: it takes Liu-Wang's theorem as its hypothesis. -/
theorem wang2001_of_liuWang (h : TernaryAbove (Real.exp 3100)) :
    TernaryAbove ((10 : ℝ) ^ 1347) :=
  ternaryAbove_mono exp3100_digits.2.le h

/-- Liu-Wang's range from Helfgott's analytic range, sharpened to `10^1347`. CONDITIONAL ON
Helfgott's `TernaryAbove (10^27)`, cited as `Ternary.helfgott_analytic`. -/
theorem wang2001_of_helfgott (h : TernaryAbove (10 ^ 27)) : TernaryAbove ((10 : ℝ) ^ 1347) :=
  wang2001_of_liuWang (liuWang_of_helfgott h)

/-- The reduction that motivated Liu-Wang: their range plus a verification up to `10^1347`
gives ternary Goldbach. A link, CONDITIONAL ON both hypotheses; such a verification was and is
far beyond computation, which is why Helfgott's `10^27` was needed. -/
theorem ternaryGoldbach_of_liuWang (hLW : TernaryAbove (Real.exp 3100))
    (hV : TernaryGoldbachUpTo (10 ^ 1347)) : TernaryGoldbach := by
  intro n ho h7
  rcases le_or_gt ((10 : ℝ) ^ 1347) n with hbig | hsmall
  · exact wang2001_of_liuWang hLW n ho hbig
  · have : n < 10 ^ 1347 := by exact_mod_cast hsmall
    exact hV n ho h7 this.le

end LeanLab.LiuWang2002

#print axioms LeanLab.LiuWang2002.exp3100_gt
#print axioms LeanLab.LiuWang2002.exp3100_lt
#print axioms LeanLab.LiuWang2002.exp3100_digits
#print axioms LeanLab.LiuWang2002.wang2001_of_liuWang
#print axioms LeanLab.LiuWang2002.wang2001_of_helfgott
#print axioms LeanLab.LiuWang2002.ternaryGoldbach_of_liuWang
