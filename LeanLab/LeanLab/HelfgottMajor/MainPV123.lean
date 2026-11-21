import LeanLab.HelfgottMajor.MainHyps123
import LeanLab.HelfgottMajor.Residue123
import LeanLab.HelfgottMajor.ResidueZeros123
import LeanLab.HelfgottMajor.Lemma41Corrected123

/-!
HELFGOTT MAIN THEOREM burst, session CLOUD-burst20261120c, unit pv, 2026-11-21. P0014,
Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, pages 36 and 37.

Sorry-free twins of the four sealed declarations that rest on the LEAF
`PolyaVinogradov123.polya_vinogradov_4_20`, display 4.20. Each twin has the exact statement of
its sealed declaration with a first argument `hPV : MainHyps123.PolyaVinogradov420`, the named
hypothesis for display 4.20, and the same proof with the leaf replaced by `hPV`. Every other
lemma used is sealed and does not depend on the leaf.

The twins are CONDITIONAL ON `MainHyps123.PolyaVinogradov420`, which is Pomerance 2011,
Integers 11, Theorem 1, cited and not proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MainPV123
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- PROVED, CONDITIONAL ON `MainHyps123.PolyaVinogradov420`. Twin of
`Residue123.charSumMax_le`, P0014 display 4.21: M(q) is at most q^(4/5). -/
theorem charSumMax_le_of_PV (hPV : MainHyps123.PolyaVinogradov420)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤ (q : ℝ) ^ (4 / 5 : ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  by_cases h32 : (q : ℝ) ≤ 32
  · exact (Residue123.charSumMax_le_half χ (Residue123.ne_one_of_isPrimitive χ hχ hq)).trans
      (Residue123.half_le_rpow q hqpos h32)
  · push_neg at h32
    have h33 : (33 : ℝ) ≤ q := by
      have : 32 < q := by exact_mod_cast h32
      exact_mod_cast (show 33 ≤ q by omega)
    have hpv := hPV q χ hχ hq
    split_ifs at hpv
    · exact hpv.trans (Residue123.pv_even_le q h33)
    · exact hpv.trans (Residue123.pv_odd_le q h33)

/-- PROVED, CONDITIONAL ON `MainHyps123.PolyaVinogradov420`. Twin of
`Residue123.log_derivative_norm_le_of_zeros`, P0014 Lemma 4.2 with display 4.21. -/
theorem log_derivative_norm_le_of_zeros_of_PV (hPV : MainHyps123.PolyaVinogradov420)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2) :
    ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
      2 * Real.log q + 15.07017 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqpos : (0 : ℝ) < q := by linarith
  have hL := Residue123.lemma_4_2 χ hχ hq hzeros
  have hM := charSumMax_le_of_PV hPV χ hχ hq
  have hM0 := Residue123.charSumMax_nonneg χ
  have hlogM : Real.log (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤ 4 / 5 * Real.log q := by
    rcases hM0.lt_or_eq with hpos | hzero
    · calc Real.log (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤ Real.log ((q : ℝ) ^ (4 / 5 : ℝ)) :=
            Real.log_le_log hpos hM
        _ = 4 / 5 * Real.log q := Real.log_rpow hqpos _
    · rw [← hzero, Real.log_zero]
      have := Real.log_nonneg hq1
      linarith
  linarith

/-- PROVED, CONDITIONAL ON `MainHyps123.PolyaVinogradov420`. Twin of
`ResidueZeros123.residue_log_derivative_bound_of_zeros`, P0014 pages 36 and 37, the display
before 4.23. -/
theorem residue_log_derivative_bound_of_zeros_of_PV (hPV : MainHyps123.PolyaVinogradov420)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2) :
    ‖((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
      deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
      3 * log q + 15.289 := by
  have h3 := three_le_conductor χ hχ hq
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h3
  have hscal := log_two_pi_div_add_gamma_abs_le (q : ℝ) hq3
  have hquot := log_derivative_norm_le_of_zeros_of_PV hPV χ hχ hq hzeros
  have hconst := page37_constant_budget
  refine le_trans (norm_sub_le _ _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  linarith

/-- PROVED, CONDITIONAL ON `MainHyps123.PolyaVinogradov420`. Twin of
`Lemma41Corrected123.residue_main_conj_bound_of_zeros`, P0014 display 4.23, page 37, for the
main part of the corrected residue. -/
theorem residue_main_conj_bound_of_zeros_of_PV (hPV : MainHyps123.PolyaVinogradov420)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2) :
    ‖(if q = 1 then ((log (2 * π) : ℝ) : ℂ) else
        ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
          (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
            DirichletCharacter.LFunction χ 1))‖ ≤ 3 * log q + 15.289 := by
  by_cases hq : q = 1
  · subst hq
    rw [if_pos rfl, Complex.norm_real, Real.norm_eq_abs, Nat.cast_one, log_one,
      abs_of_nonneg (log_nonneg (by nlinarith [pi_gt_three]))]
    have h := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * π)
    nlinarith [pi_lt_four]
  · rw [if_neg hq]
    have hconj : ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
        (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
          DirichletCharacter.LFunction χ 1) =
        (starRingEnd ℂ) (((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
          deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1) := by
      rw [map_sub, Complex.conj_ofReal]
    rw [hconj, Complex.norm_conj]
    exact residue_log_derivative_bound_of_zeros_of_PV hPV χ hχ hq hzeros

/-! ## Match checks: each twin applied to the named-match proof has the sealed type. -/

example : type_of% @Residue123.charSumMax_le =
    type_of% (@charSumMax_le_of_PV MainHyps123.polya_vinogradov_named_match) := rfl
example : type_of% @Residue123.log_derivative_norm_le_of_zeros =
    type_of% (@log_derivative_norm_le_of_zeros_of_PV MainHyps123.polya_vinogradov_named_match) :=
  rfl
example : type_of% @ResidueZeros123.residue_log_derivative_bound_of_zeros =
    type_of% (@residue_log_derivative_bound_of_zeros_of_PV
      MainHyps123.polya_vinogradov_named_match) := rfl
example : type_of% @Lemma41Corrected123.residue_main_conj_bound_of_zeros =
    type_of% (@residue_main_conj_bound_of_zeros_of_PV
      MainHyps123.polya_vinogradov_named_match) := rfl

end LeanLab.HelfgottMajor.MainPV123

#print axioms LeanLab.HelfgottMajor.MainPV123.charSumMax_le_of_PV
#print axioms LeanLab.HelfgottMajor.MainPV123.log_derivative_norm_le_of_zeros_of_PV
#print axioms LeanLab.HelfgottMajor.MainPV123.residue_log_derivative_bound_of_zeros_of_PV
#print axioms LeanLab.HelfgottMajor.MainPV123.residue_main_conj_bound_of_zeros_of_PV
