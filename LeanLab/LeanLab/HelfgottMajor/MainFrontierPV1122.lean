import LeanLab.HelfgottMajor.Decomp123
import LeanLab.HelfgottMajor.Lemma41Frontier1122
import LeanLab.HelfgottMajor.PV420Wire1122

/-!
Route burst S68, burst-20261122, tag main-frontier-pv.
Copy of `MainFrontier1122`, P0014 Theorem 1.1 chain, with the display 4.20 input taken from
`PV420Wire1122.polya_vinogradov_4_20`, which rests only on the HARD LEAFs
`PVEvenTrunc1122.cot_tail` and `PVOddTrunc1122.odd_truncated_large`, instead of
`PV420Split1122.polya_vinogradov_4_20`, which rests on four LEAFs. Every other line is the proof of
`MainFrontier1122`, itself a copy of the sealed chain from `Decomp123.theorem_1_1` with the
Lemma 4.1 leaf replaced by `Lemma41Frontier1122.lemma_4_1_gaussian_corrected_frontier`.
Named inputs that remain: `SplitGaussian123.tail_mass_of_corollary`, BLOCKED, and
`ZeroCount1623.book_zero_count`. No new sorry.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MainFrontierPV1122
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123
open LeanLab.HelfgottMajor

/-- P0014 display 4.21, pages 36 and 37, M(q) at most q^(4/5). Copy of Residue123.charSumMax_le with the sealed PV leaf replaced by PV420Wire1122.polya_vinogradov_4_20. -/
theorem charSumMax_le_frontier {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
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
    have hpv := PV420Wire1122.polya_vinogradov_4_20 χ hχ hq
    split_ifs at hpv
    · exact hpv.trans (Residue123.pv_even_le q h33)
    · exact hpv.trans (Residue123.pv_odd_le q h33)

example : type_of% @charSumMax_le_frontier = type_of% @Residue123.charSumMax_le := rfl

/-- P0014 pages 36 and 37, Lemma 4.2 with display 4.21. Copy of the Residue123 proof through charSumMax_le_frontier. -/
theorem log_derivative_norm_le_of_zeros_frontier {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2) :
    ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
      2 * Real.log q + 15.07017 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqpos : (0 : ℝ) < q := by linarith
  have hL := Residue123.lemma_4_2 χ hχ hq hzeros
  have hM := charSumMax_le_frontier χ hχ hq
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

example : type_of% @log_derivative_norm_le_of_zeros_frontier = type_of% @Residue123.log_derivative_norm_le_of_zeros := rfl

/-- P0014 pages 36 and 37, the display before 4.23. Copy of the ResidueZeros123 proof. -/
theorem residue_log_derivative_bound_of_zeros_frontier {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2) :
    ‖((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
      deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
      3 * log q + 15.289 := by
  have h3 := three_le_conductor χ hχ hq
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h3
  have hscal := log_two_pi_div_add_gamma_abs_le (q : ℝ) hq3
  have hquot := log_derivative_norm_le_of_zeros_frontier χ hχ hq hzeros
  have hconst := page37_constant_budget
  refine le_trans (norm_sub_le _ _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  linarith

example : type_of% @residue_log_derivative_bound_of_zeros_frontier = type_of% @ResidueZeros123.residue_log_derivative_bound_of_zeros := rfl

/-- P0014 display 4.23, page 37. Copy of the Lemma41Corrected123 proof. -/
theorem residue_main_conj_bound_of_zeros_frontier {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
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
    exact residue_log_derivative_bound_of_zeros_frontier χ hχ hq hzeros

example : type_of% @residue_main_conj_bound_of_zeros_frontier = type_of% @Lemma41Corrected123.residue_main_conj_bound_of_zeros := rfl

/-- P0014 page 44, proof of Proposition 4.6, corrected explicit formula. Copy of the Lemma41Corrected123 proof with the sealed Lemma 4.1 leaf replaced by Lemma41Frontier1122.lemma_4_1_gaussian_corrected_frontier. -/
theorem explicit_formula_remainder_corrected_frontier (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 + log x ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  classical
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hz58 : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2 :=
    fun s h0 h1 h2 h3 => hzeros s h0 h1 h2 (by linarith)
  obtain ⟨c, hc, hE⟩ := Lemma41Frontier1122.lemma_4_1_gaussian_corrected_frontier x hx q χ hχ δ T hT
  refine ⟨_, ?_, hE.trans ?_⟩
  · have h1 := residue_main_conj_bound_of_zeros_frontier χ hχ hz58
    have h2 := Lemma41Terms.c0_gauss (abs_nonneg δ)
    have h0 : 0 ≤ log x := log_nonneg hx
    have h3 : ‖(if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0)‖ ≤ log x := by
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      · simpa using h0
    refine (norm_add_le _ _).trans ?_
    have h4 := norm_add_le
      (if q = 1 then ((log (2 * π) : ℝ) : ℂ) else
        ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
          (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
            DirichletCharacter.LFunction χ 1))
      (if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0)
    linarith [abs_nonneg δ]
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    have hl : 0 ≤ log (q : ℝ) + 6.01 := by linarith [log_nonneg hq1]
    have hr := Lemma41Terms.repaired (abs_nonneg δ)
    apply div_le_div_of_nonneg_right _ (sqrt_nonneg x)
    exact mul_le_mul_of_nonneg_left hr hl

example : type_of% @explicit_formula_remainder_corrected_frontier = type_of% @Lemma41Corrected123.explicit_formula_remainder_corrected := rfl

/-- P0014 Proposition 4.6, pages 43 and 44, display 4.43 with the factor 6 repair. Copy of the Lemma41Corrected123 proof. -/
theorem gaussian_explicit_estimate_corrected_frontier (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x :=
  Lemma41Corrected123.assembly_of_components_corrected x hx q χ δ T
    (explicit_formula_remainder_corrected_frontier x hx q χ hχ δ T hT hzeros)
    (Lemma41Corrected123.low_zero_bound_slack x hx q χ hχ δ T hT hzeros)
    (SplitGaussian123.high_zero_bound x hx q χ hχ δ T hT hzeros)

example : type_of% @gaussian_explicit_estimate_corrected_frontier = type_of% @Lemma41Corrected123.gaussian_explicit_estimate_corrected := rfl

/-- P0014 Proposition 4.6, display 4.43, in the Decomp123 form. Copy of the Decomp123 proof. -/
theorem gaussian_explicit_estimate_frontier (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    MajorShape etaHeart χ δ x (Decomp123.gaussianError q δ x T) := by
  unfold MajorShape Decomp123.gaussianError
  exact gaussian_explicit_estimate_corrected_frontier x hx q χ hχ δ T hT hzeros

example : type_of% @gaussian_explicit_estimate_frontier = type_of% @Decomp123.gaussian_explicit_estimate := rfl

/-- P0014 Theorem 1.1, page 3, proof on pages 56 and 57. Copy of the Decomp123 proof through the frontier chain. CONDITIONAL ON HelfgottInput as a hypothesis of Theorem11, and on the remaining sealed inputs named in the file header. -/
theorem theorem_1_1_frontier : Decomp123.Theorem11 := by
  intro hG x hx q _ hq χ hχ δ hδ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hq' : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hδ' : |δ| ≤ 1200000 / (q : ℝ) := by norm_num at hδ ⊢; exact hδ
  have hx' : (1e8 : ℝ) ≤ x := by norm_num at hx ⊢; exact hx
  have hz := Decomp123.verified_zeros hG q hq χ hχ
  have hp := gaussian_explicit_estimate_frontier x (by linarith) q χ hχ δ (1e8 / q)
    (Decomp123.height_conditions hq1 hq' hδ').2 hz
  have hb := Decomp123.error_bound hq1 hq' hδ' hx'
  unfold MajorShape at hp ⊢
  exact hp.trans (mul_le_mul_of_nonneg_right hb (by linarith))

example : type_of% @theorem_1_1_frontier = type_of% @Decomp123.theorem_1_1 := rfl

end LeanLab.HelfgottMajor.MainFrontierPV1122

#print axioms LeanLab.HelfgottMajor.MainFrontierPV1122.charSumMax_le_frontier
#print axioms LeanLab.HelfgottMajor.MainFrontierPV1122.log_derivative_norm_le_of_zeros_frontier
#print axioms LeanLab.HelfgottMajor.MainFrontierPV1122.residue_log_derivative_bound_of_zeros_frontier
#print axioms LeanLab.HelfgottMajor.MainFrontierPV1122.residue_main_conj_bound_of_zeros_frontier
#print axioms LeanLab.HelfgottMajor.MainFrontierPV1122.explicit_formula_remainder_corrected_frontier
#print axioms LeanLab.HelfgottMajor.MainFrontierPV1122.gaussian_explicit_estimate_corrected_frontier
#print axioms LeanLab.HelfgottMajor.MainFrontierPV1122.gaussian_explicit_estimate_frontier
#print axioms LeanLab.HelfgottMajor.MainFrontierPV1122.theorem_1_1_frontier
