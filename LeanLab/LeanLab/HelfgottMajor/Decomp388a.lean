import LeanLab.HelfgottMajor.DecompJ1153
import LeanLab.HelfgottMajor.Inverse388

/-!
Inverse height sums from the zero count in P0014, page 38, display 4.26.
The quantitative zero count input is explicit. The last theorem has the exact sealed type.
This file does not use either OPEN theorem in DecompJ1153.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- A nontrivial zero contributes its analytic multiplicity below height t.
Source P0014 page 38, the count used in display 4.26.
-/
noncomputable def zeroWeight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ρ : ℂ) : ℝ :=
  Set.indicator {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ t}
      (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ρ

/-- The multiplicity weighted number of nontrivial zeros up to height t.
Source P0014 page 38, the definition preceding display 4.26.
-/
noncomputable def zeroCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) : ℝ := ∑' ρ : ℂ, zeroWeight χ t ρ

/-- Multiplicity weights have finite support under the supplied critical line hypothesis.
This justifies finite partial summation on page 38 for the restricted low zero set.
-/
theorem zero_weight_finite_support {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (Function.support (zeroWeight χ T)).Finite := by
  let K : Set ℂ := (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I) '' Set.Icc (-T) T
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKsub : K ⊆ ({1}ᶜ : Set ℂ) := by
    rintro z ⟨t, _, rfl⟩
    change (1 / 2 : ℂ) + (t : ℂ) * Complex.I ≠ 1
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  have ha0 : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro s hs
    exact (χ.differentiableAt_LFunction s (.inl hs)).differentiableWithinAt
  have ha := ha0.mono hKsub
  have hfin := (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) K).finiteSupport hK
  apply hfin.subset
  intro ρ hρ
  have hmem : DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ T := by
    by_contra hh
    exact hρ (by
      simp only [zeroWeight, Set.indicator_apply, Set.mem_ofPred_eq]
      exact ite_eq_right hh)
  have hm : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
    intro h
    exact hρ (by simp [zeroWeight, h])
  have hr := hzeros ρ hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2
  have hmemK : ρ ∈ K := by
    refine ⟨ρ.im, abs_le.mp hmem.2.2.2, ?_⟩
    apply Complex.ext
    · simpa using hr.symm
    · simp
  change MeromorphicOn.divisor (DirichletCharacter.LFunction χ) K ρ ≠ 0
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha hmemK]
  cases ho : analyticOrderAt (DirichletCharacter.LFunction χ) ρ <;>
    simp_all [analyticOrderNatAt]

/-- LEAF. Page 38, display 4.26 with 4.25.
The upper side of the explicit zero count cited from Rosser and McCurley.
The negative logarithmic constant is retained for reuse at height 1.
-/
theorem zero_count_explicit_upper (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  sorry

/-- The loose upper count follows from display 4.26 by dropping a negative constant.
Source P0014 page 38. This depends on the explicit count leaf.
-/
theorem zero_count_upper (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) :
    zeroCount χ t ≤ t / π * log (q * t) + 0.5 * log (q * t) + 17.7 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have ht0 : 0 < t := by linarith
  have h := zero_count_explicit_upper q χ hχ t ht
  rw [log_div (mul_pos hq ht0).ne' (by positivity)] at h
  have hc : 0 ≤ log (2 * π * exp 1) := by
    rw [log_mul (by positivity) (by positivity), log_exp]
    have := LeanLab.HelfgottMajor.log_two_pi_gt
    linarith
  have hs : 0 ≤ t / π := div_nonneg ht0.le pi_pos.le
  nlinarith [mul_nonneg hs hc]

/-- The explicit count at height 1 has the coefficients printed on page 39.
Source P0014 displays 4.25 and 4.26 and the first count bound in Lemma 4.4.
-/
theorem count_one_arithmetic (q : ℝ) (hq : 1 ≤ q) :
    1 / π * log (q / (2 * π * exp 1)) + 0.5 * log q + 17.7 ≤
      0.819 * log q + 16.8 := by
  have hq0 : 0 < q := by linarith
  have hl : 0 ≤ log q := log_nonneg hq
  have hc : (1 : ℝ) / π ≤ 0.319 := by
    rw [div_le_iff₀ pi_pos]
    nlinarith [pi_gt_d20]
  have hmain : log q / π ≤ 0.319 * log q := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using mul_le_mul_of_nonneg_right hc hl
  have hconstant : (0.9 : ℝ) ≤ (log (2 * π) + 1) / π := by
    rw [le_div_iff₀ pi_pos]
    have := LeanLab.HelfgottMajor.log_two_pi_gt
    have := pi_lt_d20
    linarith
  rw [log_div hq0.ne' (by positivity), log_mul (by positivity) (by positivity), log_exp]
  calc
    _ = log q / π + 0.5 * log q + 17.7 - (log (2 * π) + 1) / π := by ring
    _ ≤ 0.819 * log q + 16.8 := by linarith

/-- Page 38, partial summation in the proof of Lemma 4.3.
The elementary conversion from a supplied zero count is proved here.
The loose quadratic follows by replacing log qt by log qT and using pi at least 2.
-/
theorem inverse_sum_of_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcount : ∀ t : ℝ, 1 ≤ t → t ≤ T →
      zeroCount χ t ≤ t / π * log (q * t) + 0.5 * log (q * t) + 17.7) :
    invImSum χ T ≤ 0.5 * log (q * T) ^ 2 + log (q * T) + 17.7 := by
  classical
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 0 ≤ log (q * T) := log_nonneg (by nlinarith)
  have hlogT : log T ≤ log (q * T) := log_le_log hT0 (by nlinarith)
  have hlogT0 : 0 ≤ log T := log_nonneg hT
  have hfin := zero_weight_finite_support χ T hzeros
  let s : Finset ℂ := hfin.toFinset.filter (fun ρ => 1 < |ρ.im|)
  have hs (ρ : ℂ) (hρ : ρ ∈ s) : 1 < |ρ.im| ∧ |ρ.im| ≤ T := by
    have hm : zeroWeight χ T ρ ≠ 0 := hfin.mem_toFinset.mp (Finset.mem_filter.mp hρ).1
    have hp : DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
        ρ.re < 1 ∧ |ρ.im| ≤ T := by
      by_contra hh
      exact hm (by
        simp only [zeroWeight, Set.indicator_apply, Set.mem_ofPred_eq]
        exact ite_eq_right hh)
    exact ⟨(Finset.mem_filter.mp hρ).2, hp.2.2.2⟩
  have hinv : invImSum χ T = ∑ ρ ∈ s, zeroWeight χ T ρ / |ρ.im| := by
    let A : Set ℂ := {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
    calc
      invImSum χ T = ∑' ρ : A,
          (if 1 < |ρ.val.im| then
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) / |ρ.val.im|
           else 0) := by
        unfold invImSum
        apply tsum_congr
        intro ρ
        simp only [Set.indicator_apply, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
      _ = ∑' ρ : ℂ, A.indicator (fun ρ => if 1 < |ρ.im| then
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / |ρ.im| else 0) ρ :=
        tsum_subtype A (fun ρ : ℂ => if 1 < |ρ.im| then
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / |ρ.im| else 0)
      _ = ∑' ρ : ℂ, if 1 < |ρ.im| then zeroWeight χ T ρ / |ρ.im| else 0 := by
        apply tsum_congr
        intro ρ
        by_cases hρ : ρ ∈ A <;> by_cases hi : 1 < |ρ.im| <;>
          simp [zeroWeight, A, hρ, hi] at *
      _ = ∑ ρ ∈ s, (if 1 < |ρ.im| then zeroWeight χ T ρ / |ρ.im| else 0) := by
        apply tsum_eq_sum
        intro ρ hρ
        by_cases hi : 1 < |ρ.im|
        · rw [ite_eq_left hi]
          have hm : zeroWeight χ T ρ = 0 := by
            by_contra hh
            apply hρ
            exact Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hh, hi⟩
          rw [hm, zero_div]
        · rw [ite_eq_right hi]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [ite_eq_left (hs ρ hρ).1]
  have hcount' : ∀ t : ℝ, 1 ≤ t → t ≤ T →
      (∑ ρ ∈ s, if |ρ.im| ≤ t then zeroWeight χ T ρ else 0) ≤
        (log (q * T) / π) * t + (0.5 * log (q * T) + 17.7) := by
    intro t ht htT
    have ht0 : 0 < t := by linarith
    have hlog : log (q * t) ≤ log (q * T) :=
      log_le_log (mul_pos hq0 ht0) (mul_le_mul_of_nonneg_left htT hq0.le)
    have hcut (ρ : ℂ) : (if |ρ.im| ≤ t then zeroWeight χ T ρ else 0) = zeroWeight χ t ρ := by
      by_cases hh : |ρ.im| ≤ t
      · have hhT := hh.trans htT
        simp [hh, zeroWeight, Set.indicator_apply, hhT]
      · simp [hh, zeroWeight, Set.indicator_apply]
    have hsum : Summable (zeroWeight χ t) := summable_of_hasFiniteSupport
      (zero_weight_finite_support χ t (fun ρ hz h0 h1 hh => hzeros ρ hz h0 h1 (hh.trans htT)))
    have hc : (∑ ρ ∈ s, zeroWeight χ t ρ) ≤ zeroCount χ t := by
      apply hsum.sum_le_tsum
      intro ρ _
      unfold zeroWeight
      simp only [Set.indicator_apply]
      split_ifs <;> positivity
    simp_rw [hcut]
    apply hc.trans ((hcount t ht htT).trans ?_)
    have htpi : 0 ≤ t / π := div_nonneg ht0.le pi_pos.le
    have heq : log (q * T) / π * t = t / π * log (q * T) := by ring
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hlog htpi]
  have hb := Inverse388.reciprocal_sum_le_of_count s (fun ρ : ℂ => |ρ.im|)
    (zeroWeight χ T) T (log (q * T) / π) (0.5 * log (q * T) + 17.7)
    hT hs hcount'
  rw [← hinv] at hb
  have ha : log (q * T) / π ≤ 0.5 * log (q * T) := by
    rw [div_le_iff₀ pi_pos]
    have hp : 2 ≤ π := by have := pi_gt_three; linarith
    nlinarith [mul_nonneg hL (sub_nonneg.mpr hp)]
  have ha0 : 0 ≤ log (q * T) / π := div_nonneg hL pi_pos.le
  nlinarith [mul_le_mul_of_nonneg_left hlogT ha0,
    mul_le_mul_of_nonneg_right ha (show 0 ≤ 1 + log (q * T) by linarith)]

/-- The square root of the loose quadratic zero count budget is at most L plus 5.
This is elementary arithmetic after the page 38 partial summation step.
-/
theorem sqrt_quadratic_budget (L : ℝ) (hL : 0 ≤ L) :
    sqrt (0.5 * L ^ 2 + L + 17.7) ≤ L + 5 := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [sq_nonneg L]

/-- The logarithmic Gaussian norm is at least the ordinary Gaussian norm.
Source P0014 page 43, the two closed forms in display 4.42.
-/
theorem nTwo_le_nLog : Sec45.nTwo ≤ Sec45.nLog := by
  have hp := Real.pi_gt_three
  have hg := LeanLab.Helfgott2013.GammaFine.gamma_gt_fine
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hs := Real.sqrt_nonneg π
  have hb : 8 ≤ π ^ 2 + 2 * eulerMascheroniConstant ^ 2 +
      8 * eulerMascheroniConstant * log 2 + 8 * log 2 ^ 2 := by
    nlinarith [sq_nonneg eulerMascheroniConstant, sq_nonneg (log 2),
      mul_nonneg (show 0 ≤ eulerMascheroniConstant by linarith) hl.le]
  unfold Sec45.nTwo Sec45.nLog
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hb)]

/-- The logarithm appearing in the page 40 coefficient is at most 3.
The estimate uses 2 pi at most 8 and log 2 less than 0.7.
-/
theorem log_gaussian_coefficient_le_three : log (2 * π * sqrt (exp 1)) ≤ 3 := by
  rw [log_mul (by positivity) (by positivity), Real.log_sqrt (exp_pos 1).le, log_exp]
  have hp : 2 * π ≤ (2 : ℝ) ^ 3 := by have := Real.pi_lt_four; norm_num; linarith
  have hl := log_le_log (by positivity : 0 < 2 * π) hp
  rw [log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have htwo := Real.log_two_lt_d9
  linarith

/-- Five times the leading norm coefficient fits inside the constant height coefficient.
Source P0014 page 40, final bound in the proof of Lemma 4.4, with display 4.42.
-/
theorem five_norms_le_height_coefficient :
    5 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) ≤
      17.21 * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo := by
  have h := Real.sqrt_le_sqrt nTwo_le_nLog
  have ha := Real.sqrt_nonneg Sec45.nTwo
  have hb := Real.sqrt_nonneg Sec45.nLog
  have hc := mul_le_mul_of_nonneg_right log_gaussian_coefficient_le_three ha
  nlinarith

/-- The sealed inverse sum inequality follows from a supplied zero count.
Source P0014 page 38 display 4.26 and page 40 final coefficient.
This is CONDITIONAL ON hcount and hzeros.
-/
theorem inv_im_sum_bound_of_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcount : ∀ t : ℝ, 1 ≤ t → t ≤ T →
      zeroCount χ t ≤ t / π * log (q * t) + 0.5 * log (q * t) + 17.7) :
    sqrt (invImSum χ T) * (sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T) ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hL : 0 ≤ log (q * T) := log_nonneg (by nlinarith)
  have hi := inverse_sum_of_count q χ T hT hzeros hcount
  have hs := (Real.sqrt_le_sqrt hi).trans (sqrt_quadratic_budget _ hL)
  have hc := mul_le_mul_of_nonneg_right five_norms_le_height_coefficient (sqrt_nonneg T)
  have htail : 0 ≤ 2.15581 * (0.5 * log q + 17.7) := by
    have := log_nonneg hq
    positivity
  have hm := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T by positivity)
  nlinarith

/-- Exactly DecompJ1153.inv_im_sum_bound, using the smaller zero count leaf.
The final assembly calls the smaller OPEN count input.
-/
theorem inv_im_sum_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    sqrt (invImSum χ T) * (sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T) ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  exact inv_im_sum_bound_of_count q χ T hT hzeros
    (fun t ht _ => zero_count_upper q χ hχ t ht)

end LeanLab.HelfgottMajor.Decomp388a
