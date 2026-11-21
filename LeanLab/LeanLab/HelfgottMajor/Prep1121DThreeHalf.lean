import LeanLab.HelfgottMajor.Prep1121VIPointwise

/-!
PREP 2026-11-21 deepening pass p2, route step `MainLemma41Split123.vertical_integral_bound`.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 34, display 4.11,
the comparison of Dirichlet series |L'/L(w, χ)| ≤ Σ Λ(n) n^(-3/2) = |ζ'(3/2)/ζ(3/2)| on
re w = 3/2. The parent leaf `Prep1121VIPointwise.logDeriv_three_half_le` is proved here
with its exact statement; the termwise comparison is the argument of
`LeanLab.Linnik.ExplicitFormula.logDeriv_L_three_half_le`, repeated with the constant named.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DThreeHalf
open Complex

/-- P0014 page 34, display 4.11: the constant of the comparison is
Σ Λ(n) n^(-3/2) = |ζ'(3/2)/ζ(3/2)|, because every term Λ(n) n^(-3/2) is a nonnegative real,
so the sum of the norms is the norm of the sum, and the sum is -ζ'(3/2)/ζ(3/2) by
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`. PROVED here with `Complex.ofReal_tsum`. -/
theorem tsum_norm_vonMangoldt_eq :
    ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ =
      ‖deriv riemannZeta (3 / 2) / riemannZeta (3 / 2)‖ := by
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (3 / 2 : ℂ)) (by norm_num)
  have hterm : ∀ n, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n
      = ((‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ : ℝ) :
        ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n),
        ← Complex.ofReal_div,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  rw [← norm_neg, ← neg_div, ← hL, LSeries, tsum_congr hterm, ← Complex.ofReal_tsum,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]

/-- P0014 page 34, display 4.11: exact statement of the parent leaf
`Prep1121VIPointwise.logDeriv_three_half_le`. -/
theorem logDeriv_three_half_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (τ : ℝ) :
    ‖logDeriv χ.LFunction (1 - ((-1 / 2 : ℂ) + τ * I))‖ ≤
      ‖deriv riemannZeta (3 / 2) / riemannZeta (3 / 2)‖ := by
  rw [← tsum_norm_vonMangoldt_eq]
  have hsum : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hsumN : Summable fun n =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ :=
    summable_norm_iff.mpr hsum
  set s : ℂ := 1 - ((-1 / 2 : ℂ) + τ * I) with hs
  have hre : 1 < s.re := by simp [hs]; norm_num
  have hconv : -deriv χ.LFunction s / χ.LFunction s =
      LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hre
    rw [DirichletCharacter.LFunction_eq_LSeries χ hre]
    convert h.symm using 3
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  have hpt : ∀ n, ‖LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ ≤
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · exact le_rfl
    · have hsr : s.re = (3 / 2 : ℂ).re := by simp [hs]; norm_num
      rw [hsr]
      gcongr
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hsum2 : Summable fun n =>
      ‖LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumN
  rw [logDeriv_apply, ← norm_neg, ← neg_div, hconv, LSeries]
  exact (norm_tsum_le_tsum_norm hsum2).trans (hsum2.tsum_le_tsum hpt hsumN)

end LeanLab.HelfgottMajor.Prep1121DThreeHalf
