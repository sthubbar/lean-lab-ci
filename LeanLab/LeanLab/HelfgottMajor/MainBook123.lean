import LeanLab.HelfgottMajor.Lemma41Corrected123
import LeanLab.HelfgottMajor.MainHyps123

/-!
HELFGOTT MAIN THEOREM burst, session CLOUD-burst20261120c, unit book, 2026-11-21.
P0014, Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4.

Conditional twins of every sealed declaration between the open leaf
`ZeroCount1623.book_zero_count` and `Lemma41Corrected123.low_zero_bound_slack`. Each twin has the
exact sealed statement with one more first argument `hB : MainHyps123.BookZeroCount`, and the
sealed proof with the leaf replaced by `hB`. No sorry, no new definition, no axiom.

The chain is
- ZeroCount1623.zero_count_two_sided, arxiv_zero_count, very_low_count
- SplitGaussian123.very_low_mass_bound, in Gaussian123Base
- Decomp526a.signed_count_bound
- MiddleSlack123.middle_mass_bound_slack
- Lemma41Corrected123.low_zero_bound_slack
ZeroCount1623.strip_count also rests on the leaf; it is not on the chain but gets a twin too.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MainBook123

section ZeroCount
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation
open LeanLab.HelfgottMajor.ZeroCount1623

variable {q : ℕ} [NeZero q]

/-- Twin of `ZeroCount1623.zero_count_two_sided`, CONDITIONAL ON `MainHyps123.BookZeroCount`. -/
theorem zero_count_two_sided_of_book (hB : MainHyps123.BookZeroCount)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hT : 1 ≤ T) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ)) - 2 * bookMain q T| ≤
      2 * bookError q T := by
  have hχi : χ⁻¹.IsPrimitive := by
    simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hχ
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  obtain ⟨ε, hε, hgap⟩ := exists_gap χ T
  set N := ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) with hN
  have hev : ∀ᶠ t in 𝓝[>] T, |N - 2 * bookMain q t| ≤ 2 * bookError q t := by
    have hmem : Ioo T (T + ε) ∈ 𝓝[>] T := Ioo_mem_nhdsGT (by linarith)
    filter_upwards [hmem] with t ht
    have ht1 : 1 ≤ t := hT.trans ht.1.le
    have he := hgap t ht.1 ht.2
    have hnot : ∀ ρ ∈ stripZeros χ t, |ρ.im| ≠ t := by
      intro ρ hρ h
      rw [he] at hρ
      have := hρ.2.2.2
      linarith [ht.1]
    have hs := two_sided_split χ (by linarith) hnot
    have hNt : N = bookCount χ t + bookCount χ⁻¹ t := by
      rw [hN, ← sum_eq_of_strip_eq χ he, hs]
    have h1 := abs_le.mp (hB q χ hχ ht1)
    have h2 := abs_le.mp (hB q χ⁻¹ hχi ht1)
    rw [hNt, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hcont1 : ContinuousAt (fun t ↦ bookMain q t) T := by
    unfold bookMain
    have hne : (q : ℝ) * T / (2 * Real.pi * Real.exp 1) ≠ 0 :=
      div_ne_zero (mul_ne_zero hq0 (by linarith)) (by positivity)
    exact ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) hne)
  have hcont2 : ContinuousAt (fun t ↦ bookError q t) T := by
    unfold bookError
    have hne : (q : ℝ) * T ≠ 0 := mul_ne_zero hq0 (by linarith)
    exact ContinuousAt.add (ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) hne))
      (by fun_prop)
  have hL : Tendsto (fun t ↦ |N - 2 * bookMain q t|) (𝓝[>] T) (𝓝 |N - 2 * bookMain q T|) :=
    ((continuousAt_const.sub (continuousAt_const.mul hcont1)).abs).tendsto.mono_left
      nhdsWithin_le_nhds
  have hR : Tendsto (fun t ↦ 2 * bookError q t) (𝓝[>] T) (𝓝 (2 * bookError q T)) :=
    (continuousAt_const.mul hcont2).tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hL hR hev

/-- Twin of `ZeroCount1623.arxiv_zero_count`, CONDITIONAL ON `MainHyps123.BookZeroCount`. -/
theorem arxiv_zero_count_of_book (hB : MainHyps123.BookZeroCount)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hT : 1 ≤ T) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ)) -
      T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
        0.5 * Real.log ((q : ℝ) * T) + 17.7 := by
  have h := zero_count_two_sided_of_book hB χ hχ hT
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  have he : 2 * bookMain q T =
      T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) := by
    unfold bookMain
    ring
  rw [he] at h
  refine h.trans ?_
  unfold bookError
  linarith

/-- Twin of `ZeroCount1623.very_low_count`, CONDITIONAL ON `MainHyps123.BookZeroCount`. -/
theorem very_low_count_of_book (hB : MainHyps123.BookZeroCount)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : ZeroIdx χ T, Set.indicator {ρ : ZeroIdx χ T | |ρ.val.im| ≤ 1}
        (fun ρ => (mult χ ρ.val : ℝ)) ρ) ≤ 0.819 * Real.log q + 16.8 := by
  have hpt : ∀ ρ : ZeroIdx χ T, Set.indicator {ρ : ZeroIdx χ T | |ρ.val.im| ≤ 1}
      (fun ρ => (mult χ ρ.val : ℝ)) ρ = lowTerm χ ρ.val := by
    intro ρ
    by_cases h : |ρ.val.im| ≤ 1 <;> simp [Set.indicator, lowTerm, h]
  have hsub : (stripZeros_finite χ 1).toFinset ⊆ (stripZeros_finite χ T).toFinset := by
    intro ρ hρ
    have hρ' := (stripZeros_finite χ 1).mem_toFinset.mp hρ
    exact (stripZeros_finite χ T).mem_toFinset.mpr
      ⟨hρ'.1, hρ'.2.1, hρ'.2.2.1, hρ'.2.2.2.trans hT⟩
  have hzero : ∀ ρ ∈ (stripZeros_finite χ T).toFinset,
      ρ ∉ (stripZeros_finite χ 1).toFinset → lowTerm χ ρ = 0 := by
    intro ρ hT' hn
    have hρ' := (stripZeros_finite χ T).mem_toFinset.mp hT'
    have hh : ¬ |ρ.im| ≤ 1 := fun h => hn
      ((stripZeros_finite χ 1).mem_toFinset.mpr ⟨hρ'.1, hρ'.2.1, hρ'.2.2.1, h⟩)
    simp [lowTerm, hh]
  have hsame : (∑ ρ ∈ (stripZeros_finite χ 1).toFinset, lowTerm χ ρ) =
      ∑ ρ ∈ (stripZeros_finite χ 1).toFinset, (mult χ ρ : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    unfold lowTerm
    rw [ite_eq_left ((stripZeros_finite χ 1).mem_toFinset.mp hρ).2.2.2]
  have hreduce : (∑' ρ : ZeroIdx χ T, Set.indicator {ρ : ZeroIdx χ T | |ρ.val.im| ≤ 1}
      (fun ρ => (mult χ ρ.val : ℝ)) ρ) =
      ∑ ρ ∈ (stripZeros_finite χ 1).toFinset, (mult χ ρ : ℝ) :=
    (tsum_congr hpt).trans ((tsum_zeroIdx χ T (lowTerm χ)).trans
      ((Finset.sum_subset hsub hzero).symm.trans hsame))
  rw [hreduce]
  have h := (abs_le.mp (arxiv_zero_count_of_book hB χ hχ (le_refl (1 : ℝ)))).2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (q : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < q).ne'
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  simp only [mul_one] at h
  rw [Real.log_div hq0 (by positivity)] at h
  have hl := log_two_pi_e_ge
  have hpi := Real.pi_gt_d4
  have hpi2 := Real.pi_lt_d4
  have hip : (1 : ℝ) / Real.pi ≤ 0.319 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith
  have hip2 : (0.3183 : ℝ) ≤ 1 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]; nlinarith
  have hA : 1 / Real.pi * Real.log q ≤ 0.319 * Real.log q :=
    mul_le_mul_of_nonneg_right hip hlq
  have hB' : 0.3183 * (2.8294 : ℝ) ≤ 1 / Real.pi * Real.log (2 * Real.pi * Real.exp 1) :=
    mul_le_mul hip2 hl (by norm_num) (by positivity)
  have hexp : 1 / Real.pi * (Real.log q - Real.log (2 * Real.pi * Real.exp 1)) =
      1 / Real.pi * Real.log q - 1 / Real.pi * Real.log (2 * Real.pi * Real.exp 1) := by ring
  rw [hexp] at h
  have hnum : (0.9 : ℝ) ≤ 0.3183 * 2.8294 := by norm_num
  linarith

/-- Twin of `ZeroCount1623.strip_count`, CONDITIONAL ON `MainHyps123.BookZeroCount`. -/
theorem strip_count_of_book (hB : MainHyps123.BookZeroCount)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : ZeroIdx χ T, (mult χ ρ.val : ℝ)) ≤
      T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) +
        0.5 * Real.log ((q : ℝ) * T) + 17.7 := by
  have e : (∑' ρ : ZeroIdx χ T, (mult χ ρ.val : ℝ)) =
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) :=
    tsum_zeroIdx χ T (fun z => (mult χ z : ℝ))
  rw [e]
  have h := (abs_le.mp (arxiv_zero_count_of_book hB χ hχ hT)).2
  linarith

end ZeroCount

section Gaussian
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- Twin of `SplitGaussian123.very_low_mass_bound`, in Gaussian123Base, CONDITIONAL ON
`MainHyps123.BookZeroCount`. -/
theorem very_low_mass_bound_of_book (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    veryLowMass χ δ T ≤ 2.15581 * (0.819 * log q + 16.8) := by
  classical
  haveI := ZeroCount1623.zeroIdx_finite χ T
  have hc := very_low_count_of_book hB χ hχ T hT
  calc
    veryLowMass χ δ T ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, 2.15581 *
          Set.indicator {ρ : ZeroCount1623.ZeroIdx χ T | |ρ.val.im| ≤ 1}
            (fun ρ => (ZeroCount1623.mult χ ρ.val : ℝ)) ρ := by
      unfold veryLowMass
      apply Summable.tsum_le_tsum _ Summable.of_finite Summable.of_finite
      intro ρ
      by_cases h : |ρ.val.im| ≤ 1
      · simp only [Set.indicator, Set.mem_setOf_eq, h, if_true]
        have hre := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1
          ρ.property.2.2.2
        have hn := mellin_critical_norm_le δ ρ.val hre
        unfold mellinMassTerm
        rw [mul_comm (2.15581 : ℝ)]
        exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
      · simp [Set.indicator, h]
    _ = 2.15581 * ∑' ρ : ZeroCount1623.ZeroIdx χ T,
          Set.indicator {ρ : ZeroCount1623.ZeroIdx χ T | |ρ.val.im| ≤ 1}
            (fun ρ => (ZeroCount1623.mult χ ρ.val : ℝ)) ρ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by norm_num)

/-- Twin of `Decomp526a.signed_count_bound`, CONDITIONAL ON `MainHyps123.BookZeroCount`. -/
theorem signed_count_bound_of_book (hB : MainHyps123.BookZeroCount)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (ε t : ℝ) (ht : 1 ≤ t) :
    |ZeroCount1623.bookCount (if ε = 1 then χ else χ⁻¹) t -
      ZeroCount1623.bookMain q t| ≤ ZeroCount1623.bookError q t := by
  split_ifs
  · exact hB q χ hχ ht
  · apply hB q _ _ ht
    simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hχ

end Gaussian

section Middle
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123
open MeasureTheory LeanLab.HelfgottMajor LeanLab.HelfgottMajor.Decomp389b
  LeanLab.HelfgottMajor.Decomp526a Set
open LeanLab.HelfgottMajor.MiddleSlack123

/-- Twin of `MiddleSlack123.middle_mass_bound_slack`, CONDITIONAL ON
`MainHyps123.BookZeroCount`. -/
theorem middle_mass_bound_slack_of_book (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT100 : 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) - 2 := by
  have hT : 2 ≤ T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT : 0 < (q : ℝ) * T := mul_pos hq0 hT0
  have he2 : exp 2 < (8 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_pos 1]
  have hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T := by
    have hh := mul_le_mul pi_lt_four.le he2.le (exp_pos 2).le (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  have hlog : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq
  have hs : (10 : ℝ) ≤ sqrt T := (le_sqrt (by norm_num) hT0.le).mpr (by nlinarith)
  have hW : sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) ≤
      sqrt T * log ((q : ℝ) * T) := by
    apply (Sampling431.main_weight_root_bound (q : ℝ) T hq0 hT1 hlarge).trans
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg T)
    rw [log_div hqT.ne' (by positivity)]
    have hc := BookP1617.K_bds
    linarith
  have hV := Sampling431.error_weight_root_bound (q : ℝ) T hq0 hT1 hlarge
  have hpos := one_sign_finite_sampling q χ δ T 1 hT1 (Or.inl rfl) hzeros
    (fun t ht => signed_count_bound_of_book hB χ hχ 1 t ht)
  have hneg := one_sign_finite_sampling q χ δ T (-1) hT1 (Or.inr rfl) hzeros
    (fun t ht => signed_count_bound_of_book hB χ hχ (-1) t ht)
  have hE := gaussian_line_energy_bound δ
  have hD := gaussian_derivative_energy_bound δ
  have hEp : (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) ≤
      0.565 * sqrt Sec45.nTwo := by
    have hp : 0 < sqrt π := by positivity
    calc
      _ ≤ (2 * sqrt π * sqrt Sec45.nTwo) / (2 * π) :=
        div_le_div_of_nonneg_right hE (by positivity)
      _ = sqrt Sec45.nTwo / sqrt π := by
        rw [show 2 * π = 2 * sqrt π * sqrt π by nlinarith [sq_sqrt pi_pos.le]]
        field_simp
      _ ≤ _ := by
        rw [div_le_iff₀ hp]
        nlinarith [mul_nonneg (sqrt_nonneg Sec45.nTwo)
          (show (0 : ℝ) ≤ 0.565 * sqrt π - 1 by linarith [Sec45.sqrt_pi_gt])]
  have hDp : sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      3.546 * sqrt Sec45.nLog := by
    apply hD.trans
    nlinarith [mul_nonneg (sqrt_nonneg Sec45.nLog)
      (show (0 : ℝ) ≤ 3.546 - 2 * sqrt π by linarith [Sec45.sqrt_pi_lt])]
  have htpos := gaussian_endpoint_trace δ T 1 hT (Or.inl rfl)
  have htneg := gaussian_endpoint_trace δ T (-1) hT (Or.inr rfl)
  have htrace : ‖gaussianMellin δ ((1 / 2 : ℂ) + (1 * T : ℝ) * Complex.I)‖ +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (-1 * T : ℝ) * Complex.I)‖ ≤
      3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) := by
    have hh := add_le_add htpos htneg
    have hpd : 2 * sqrt π * (sqrt Sec45.nTwo + sqrt Sec45.nLog) ≤
        3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) :=
      mul_le_mul_of_nonneg_right (by linarith [Sec45.sqrt_pi_lt]) (by positivity)
    nlinarith
  have hepos := mellin_critical_norm_le δ ((1 / 2 : ℂ) + (1 : ℂ) * Complex.I) (by norm_num)
  have heneg := mellin_critical_norm_le δ ((1 / 2 : ℂ) + (-1 : ℂ) * Complex.I) (by norm_num)
  have hsample : middleMass χ δ T ≤
      (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      (sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1))) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + (1 : ℂ) * Complex.I)‖ +
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (-1 : ℂ) * Complex.I)‖) *
        (0.15 * log (q : ℝ) + 3.389) +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + (1 * T : ℝ) * Complex.I)‖ +
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (-1 * T : ℝ) * Complex.I)‖) *
        (0.15 * log ((q : ℝ) * T) + 3.389) := by
    rw [middle_mass_signed_split]
    norm_num only [Complex.ofReal_one, Complex.ofReal_neg] at hpos hneg
    convert add_le_add hpos hneg using 1 <;> ring
  have hcoarse : middleMass χ δ T ≤
      (0.565 * sqrt Sec45.nTwo + 0.532 * sqrt Sec45.nLog) * sqrt T * log ((q : ℝ) * T) +
      11.497 * sqrt Sec45.nLog * sqrt T + 2.15581 * (0.3 * log (q : ℝ) + 6.778) +
      3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) *
        (0.15 * log ((q : ℝ) * T) + 3.389) := by
    calc
      _ ≤ 0.565 * sqrt Sec45.nTwo * (sqrt T * log ((q : ℝ) * T)) +
          (3.546 * sqrt Sec45.nLog) * ((0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T) +
          (2 * 2.15581) * (0.15 * log (q : ℝ) + 3.389) +
          3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) *
            (0.15 * log ((q : ℝ) * T) + 3.389) := by
        apply hsample.trans
        gcongr <;> linarith
      _ ≤ _ := by
        have h1 : 0 ≤ sqrt Sec45.nLog * sqrt T * log ((q : ℝ) * T) := by positivity
        have h2 : 0 ≤ sqrt Sec45.nLog * sqrt T := by positivity
        nlinarith
  have habs := finite_endpoint_absorption_slack (sqrt T) (log ((q : ℝ) * T))
    (log (q : ℝ)) hs hlog hlogq
  linarith

end Middle

section Low
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- Twin of `Lemma41Corrected123.low_zero_bound_slack`, CONDITIONAL ON
`MainHyps123.BookZeroCount` and on nothing else. P0014 Lemma 4.4, display 4.29 on page 39, as
applied on page 43, with two units of slack on sqrt x. -/
theorem low_zero_bound_slack_of_book (hB : MainHyps123.BookZeroCount)
    (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38 - 2) * sqrt x := by
  apply low_zero_bound_of_mass χ δ x T _ (by linarith) hzeros
  rw [mass_split χ δ T]
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hv := very_low_mass_bound_of_book hB q χ hχ δ T hT1 hzeros
  have hm := middle_mass_bound_slack_of_book hB q χ hχ δ T hT100 hzeros
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hlogqT : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have ha := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0_log
    (mul_nonneg (sqrt_nonneg T) hlogqT)
  have hb := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0 (sqrt_nonneg T)
  obtain ⟨hc, hd⟩ := Sec45.coef_logq
  nlinarith

end Low

/-! ### Match checks. Each twin, fed the sealed leaf, has exactly the sealed type. -/

example : type_of% @ZeroCount1623.zero_count_two_sided :=
  fun {q} [_] => @zero_count_two_sided_of_book q _ MainHyps123.book_zero_count_named_match
example : type_of% @ZeroCount1623.arxiv_zero_count :=
  fun {q} [_] => @arxiv_zero_count_of_book q _ MainHyps123.book_zero_count_named_match
example : type_of% @ZeroCount1623.very_low_count :=
  fun {q} [_] => @very_low_count_of_book q _ MainHyps123.book_zero_count_named_match
example : type_of% @ZeroCount1623.strip_count :=
  fun {q} [_] => @strip_count_of_book q _ MainHyps123.book_zero_count_named_match
example : type_of% @SplitGaussian123.very_low_mass_bound :=
  @very_low_mass_bound_of_book MainHyps123.book_zero_count_named_match
example : type_of% @Decomp526a.signed_count_bound :=
  @signed_count_bound_of_book MainHyps123.book_zero_count_named_match
example : type_of% @MiddleSlack123.middle_mass_bound_slack :=
  @middle_mass_bound_slack_of_book MainHyps123.book_zero_count_named_match
example : type_of% @Lemma41Corrected123.low_zero_bound_slack :=
  @low_zero_bound_slack_of_book MainHyps123.book_zero_count_named_match

end LeanLab.HelfgottMajor.MainBook123

#print axioms LeanLab.HelfgottMajor.MainBook123.zero_count_two_sided_of_book
#print axioms LeanLab.HelfgottMajor.MainBook123.very_low_mass_bound_of_book
#print axioms LeanLab.HelfgottMajor.MainBook123.signed_count_bound_of_book
#print axioms LeanLab.HelfgottMajor.MainBook123.middle_mass_bound_slack_of_book
#print axioms LeanLab.HelfgottMajor.MainBook123.low_zero_bound_slack_of_book
