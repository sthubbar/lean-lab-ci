/-
P0022, pages 361 and 371 to 373. Elementary comparisons of cited inputs.
The large ternary input is still cited after a change of threshold.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.KanieckiGap.HSW127
import LeanLab.Ternary.Statements

namespace LeanLab.KanieckiGap.InputReductions127

/-- Page 371. The Corollary 1 right side is strictly larger than the
Schoenfeld61 right side, so a bound comparison cannot give the latter. -/
theorem cor1_bound_larger {x : ℝ} (hx : 1 < x) :
    KanieckiGap.B x < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
  have hlog := Real.log_pos hx
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  unfold KanieckiGap.B
  apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 8 * Real.pi)).mpr
  nlinarith [mul_pos hsqrt hlog]

/-- Page 361, the Chen-Wang cutoff. The later Liu-Wang cutoff exp 3100
is below exp of exp 11.503. -/
theorem liuWang_threshold_le : Real.exp 3100 ≤ LeanLab.Kaniecki1995.n0 := by
  unfold LeanLab.Kaniecki1995.n0
  apply Real.exp_le_exp.mpr
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) he 9
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have h9 : Real.exp 9 ≤ Real.exp 11.503 := Real.exp_le_exp.mpr (by norm_num)
  linarith

/-- Pages 361 and 373, reference 1. The stronger later Liu-Wang theorem
supplies the older large ternary input. CONDITIONAL ON Liu-Wang. -/
theorem chenWang_of_liuWang (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100)) :
    LeanLab.Kaniecki1995.ChenWang :=
  LeanLab.Ternary.ternaryAbove_mono liuWang_threshold_le hLW

/-- Page 373. The modern even verification input includes the finite range
needed by the original paper. CONDITIONAL ON that verification input. -/
theorem finite_even_of_modern (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    EvenGoldbachUpTo (1405 * 10 ^ 9) := by
  intro n hn h4 hhi
  exact hE n hn h4 (by omega)

/-- Pages 364 to 373. Original guarded interval route, with the older
Chen-Wang input supplied by Liu-Wang and the finite range supplied by the
modern even verification. CONDITIONAL ON the named analytic, zero count,
finite table and large ternary inputs, and RH. -/
theorem theorem_hsw_liuWang
    (h4 : LeanLab.Kaniecki1995.L5.Lemma4G)
    (hP : LeanLab.Kaniecki1995.U7152.Parseval18BC)
    (hNz : LeanLab.Dudek2014.SigmaH.HSWN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hHz : LeanLab.PNTPort.ExplicitPsi1.FirstDiff.HSWHead14 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hY : KanieckiGap.YoungPotler)
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100))
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    RiemannHypothesis →
      (∀ n : ℕ, Odd n → 1 < n → LeanLab.SchnirelmannConstant.AtMostPrimes 5 n) ∧
      (∀ n : ℕ, Even n → LeanLab.SchnirelmannConstant.AtMostPrimes 4 n) :=
  HSW127.theorem_hsw_lemma4_parseval h4 hP hNz hHz h14 hY
    (chenWang_of_liuWang hLW) (finite_even_of_modern hE)

end LeanLab.KanieckiGap.InputReductions127

#print axioms LeanLab.KanieckiGap.InputReductions127.cor1_bound_larger
#print axioms LeanLab.KanieckiGap.InputReductions127.liuWang_threshold_le
#print axioms LeanLab.KanieckiGap.InputReductions127.chenWang_of_liuWang
#print axioms LeanLab.KanieckiGap.InputReductions127.finite_even_of_modern
#print axioms LeanLab.KanieckiGap.InputReductions127.theorem_hsw_liuWang
