import LeanLab.HelfgottMajor.Decomp389a
import LeanLab.HelfgottMajor.BookP1617

/-!
Small qT in the middle range of P0014 Lemma 4.4, pages 38 to 40.
The book proof of Lemma 16.10 requires qT at least 2 pi exp 2.
The elementary zero count estimate covers the complementary range.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp389c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- The multiplicity counting summand N of T in display 4.26 on page 38. -/
noncomputable def stripCountTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}) : ℝ :=
  (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)

/-- LEAF. Page 38, displays 4.25 and 4.26, the upper side of the classical count formula.
This counts all strip zeros up to T and estimates no Mellin value.
-/
theorem strip_zero_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (stripCountTerm χ T) ∧
      (∑' ρ, stripCountTerm χ T ρ) ≤
        T / π * log ((q : ℝ) * T / (2 * π * exp 1)) +
          0.5 * log ((q : ℝ) * T) + 17.7 := by
  sorry

/-- The critical line half moment bounds the middle mass by the total multiplicity count.
CONDITIONAL ON hzeros and the supplied count summability. Pages 39 and 40, display 4.30.
-/
theorem middle_mass_le_count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcount : Summable (stripCountTerm χ T)) :
    middleMass χ δ T ≤ 2.15581 * ∑' ρ, stripCountTerm χ T ρ := by
  classical
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) := by
    apply (Zeros269.low_zero_terms_summable χ δ 1 T hzeros).norm.congr
    intro ρ
    simp [zeroTerm, mellinMassTerm, nsmul_eq_mul]
  unfold middleMass
  rw [← tsum_mul_left]
  apply (hm.indicator _).tsum_le_tsum _ (hcount.mul_left 2.15581)
  intro ρ
  have hρ : 0 ≤ stripCountTerm χ T ρ := Nat.cast_nonneg _
  by_cases h : |ρ.val.im| ≤ 1
  · simp [Set.indicator, h]
    positivity
  · simp only [Set.indicator, Set.mem_compl_iff, Set.mem_ofPred_eq, h, not_false_eq_true,
      ite_true, mellinMassTerm, stripCountTerm]
    have hz := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2
    have hb := Decomp389a.mellin_critical_norm_le δ ρ.val hz
      HalfMoment389.gaussian_half_moment_bound
    simpa only [stripCountTerm, mul_comm] using mul_le_mul_of_nonneg_left hb hρ

/-- A coarse lower bound for the positive square root T coefficient on page 40.
This is used only to cover the small qT range without the book lower height assumption.
-/
theorem middle_constant_ge :
    (15 : ℝ) ≤ 17.21 * sqrt Sec45.nLog -
      log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo := by
  have hNL : (1 : ℝ) ≤ Sec45.nLog := by
    unfold Sec45.nLog
    have hg : 0 ≤ eulerMascheroniConstant := by
      have := LeanLab.Helfgott2013.GammaFine.gamma_gt_fine
      linarith
    have hl : 0 ≤ log 2 := log_nonneg (by norm_num)
    have hl1 := log_two_gt_d9
    have hp := pi_gt_three
    have hs : (1.7 : ℝ) ≤ sqrt π := by linarith [Sec45.sqrt_pi_gt]
    have hb : (10 : ℝ) ≤ π ^ 2 + 2 * eulerMascheroniConstant ^ 2 +
        8 * eulerMascheroniConstant * log 2 + 8 * log 2 ^ 2 := by
      nlinarith [mul_nonneg hg hl, sq_nonneg eulerMascheroniConstant]
    calc
      (1 : ℝ) ≤ 1.7 / 16 * 10 := by norm_num
      _ ≤ _ := mul_le_mul (by linarith : (1.7 : ℝ) / 16 ≤ sqrt π / 16) hb
        (by norm_num) (by positivity)
  have hL : (1 : ℝ) ≤ sqrt Sec45.nLog :=
    (Real.le_sqrt (by norm_num) Sec45.nLog_nonneg).mpr (by simpa using hNL)
  have hN := Sec45.sqrt_nTwo_lt
  have hN0 := sqrt_nonneg Sec45.nTwo
  obtain ⟨hC0, hC⟩ := BookP1617.K_bds
  have hprod : log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo ≤ 2.3378771 * 0.941397 :=
    mul_le_mul hC.le hN.le hN0 (by norm_num)
  nlinarith

/-- Small qT is covered by the classical count formula and the scalar half moment.
This is the small height branch of the exact middle mass statement on page 40.
-/
theorem small_middle_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hsmall : (q : ℝ) * T ≤ 2 * π * exp 2)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT0 : 0 < (q : ℝ) * T := mul_pos hq0 hT0
  have he2 : exp 2 < (8 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_pos 1]
  have hcap : 2 * π * exp 2 ≤ (64 : ℝ) := by
    have hh := mul_le_mul pi_lt_four.le he2.le (exp_pos 2).le (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  have hT64 : T ≤ 64 := by nlinarith
  have hs0 := sqrt_nonneg T
  have hsq := sq_sqrt hT0.le
  have hs8 : sqrt T ≤ 8 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num; exact hT64⟩
  have hTs : T ≤ 8 * sqrt T := by nlinarith
  have hlogqT : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have hlogmul : log ((q : ℝ) * T) = log (q : ℝ) + log T := log_mul hq0.ne' hT0.ne'
  have hlogT : log T ≤ T := by linarith [log_le_sub_one_of_pos hT0]
  have hratio : log ((q : ℝ) * T / (2 * π * exp 1)) ≤ 1 := by
    apply (log_le_iff_le_exp (by positivity)).mpr
    rw [div_le_iff₀ (by positivity)]
    have he : exp 1 * (2 * π * exp 1) = 2 * π * exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
      ring
    rwa [he]
  obtain ⟨hcount, hbudget⟩ := strip_zero_count q χ hχ T hT
  have hm := middle_mass_le_count χ δ T hzeros hcount
  have hcount' : (∑' ρ, stripCountTerm χ T ρ) ≤ T / π +
      0.5 * (log (q : ℝ) + T) + 17.7 := by
    have hh := mul_le_mul_of_nonneg_left hratio (div_nonneg hT0.le pi_pos.le)
    rw [hlogmul] at hbudget
    linarith
  have hdiv : T / π ≤ T / 3 := by
    exact div_le_div_of_nonneg_left hT0.le (by norm_num) pi_gt_three.le
  have hmain : 0 ≤ (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log ((q : ℝ) * T) := by
    positivity
  have hc := mul_le_mul_of_nonneg_right middle_constant_ge hs0
  nlinarith

end LeanLab.HelfgottMajor.Decomp389c
