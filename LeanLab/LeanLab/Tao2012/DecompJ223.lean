import Mathlib
import LeanLab.Tao2012.Decomp1555a
import LeanLab.Tao2012.Cor48

namespace LeanLab.Tao2012.DecompJ223

open Real Finset MeasureTheory
open LeanLab.Tao2012.Decomp1555
open LeanLab.Tao2012.Cor48

/-- The cutoff function `1_{[0, 1]}`. -/
noncomputable def one_Icc : ℝ → ℝ := fun t => if t ∈ Set.Icc (0:ℝ) 1 then 1 else 0

private lemma one_Icc_mem {t : ℝ} (h : t ∈ Set.Icc (0:ℝ) 1) : one_Icc t = 1 := by
  simp [one_Icc, h]

private lemma abs_one_Icc (t : ℝ) : |one_Icc t| ≤ 1 := by
  unfold one_Icc
  split_ifs <;> norm_num

/-- LEAF. Tao 2012, page 16, Lemma 4.2 proof. The fundamental theorem of calculus
rewrites the smooth cutoff `η(n/x)` as the integral of `- (1/x) η'(y/x)` on `[n, x]`. -/
theorem eta_eq_integral (η : ℝ → ℝ) (h_diff : ContDiff ℝ 1 η) (h_supp : Function.support η ⊆ Set.Icc 0 1)
    (x : ℝ) (hx : 1 ≤ x) (n : ℕ) (hn : (n : ℝ) ≤ x) :
    η (n / x) = - (1 / x) * ∫ y in (n:ℝ)..x, deriv η (y / x) := by
  have H : ∫ y in (n:ℝ)..x, deriv (fun y => η (y / x)) y = η (x / x) - η (n / x) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => η (y / x)) (f' := fun y => deriv (fun y => η (y / x)) y)
    · intro y _
      exact (ContDiff.differentiable h_diff (by decide) |>.comp (differentiable_id.div_const x)).differentiableAt.hasDerivAt
    · exact ((ContDiff.continuous_deriv (h_diff.comp (contDiff_id.div_const x)) (by decide)).intervalIntegrable _ _)
  have hc : Continuous η := h_diff.continuous
  have eta_1_eq_0 : η 1 = 0 := by
    have h2 : Filter.Tendsto η (nhdsWithin (1:ℝ) (Set.Ioi 1)) (nhds 0) := by
      have h_eq : ∀ᶠ x_1 in nhdsWithin (1:ℝ) (Set.Ioi 1), (fun _ => (0:ℝ)) x_1 = η x_1 := by
        apply Filter.eventually_iff_exists_mem.mpr
        use Set.Ioi 1
        constructor
        · exact self_mem_nhdsWithin
        · intro x_1 hx_1
          have : x_1 ∉ Set.Icc (0:ℝ) 1 := by
            intro h
            have hx_gt : x_1 > 1 := hx_1
            have hx_le : x_1 ≤ 1 := h.2
            linarith
          have : x_1 ∉ Function.support η := fun h => this (h_supp h)
          exact (not_not.mp this).symm
      exact Filter.Tendsto.congr' h_eq tendsto_const_nhds
    have h3 : Filter.Tendsto η (nhdsWithin (1:ℝ) (Set.Ioi 1)) (nhds (η 1)) := hc.tendsto 1 |>.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique h3 h2
  have hx_pos : 0 < x := by linarith
  have h_x_div_x : x / x = 1 := div_self (ne_of_gt hx_pos)
  have H2 : ∫ y in (n:ℝ)..x, (1 / x) * deriv η (y / x) = η (x / x) - η (n / x) := by
    have H_deriv : ∀ y, deriv (fun y => η (y / x)) y = (1 / x) * deriv η (y / x) := by
      intro y
      have h_diff_eta : DifferentiableAt ℝ η (y / x) := (ContDiff.differentiable h_diff (by decide)).differentiableAt
      have h_diff_div : DifferentiableAt ℝ (fun y => y / x) y := (differentiable_id.div_const x).differentiableAt
      have : deriv (fun y => η (y / x)) y = deriv η (y / x) * deriv (fun y => y / x) y :=
        HasDerivAt.deriv (HasDerivAt.comp y h_diff_eta.hasDerivAt h_diff_div.hasDerivAt)
      rw [this]
      have h_div : deriv (fun y => y / x) y = 1 / x := by
        have H_id : deriv (fun y => y / x) y = deriv (fun y => y * (1 / x)) y := by
          congr 1
          ext y_1
          ring
        rw [H_id, deriv_mul_const differentiable_id.differentiableAt]
        have H_id_eval : deriv (fun y => y) y = 1 := deriv_id y
        rw [H_id_eval]
        ring
      rw [h_div]
      ring
    simp_rw [H_deriv] at H
    exact H
  rw [h_x_div_x, eta_1_eq_0] at H2
  have h_int : ∫ y in (n:ℝ)..x, (1 / x) * deriv η (y / x) = (1 / x) * ∫ y in (n:ℝ)..x, deriv η (y / x) := by
    exact intervalIntegral.integral_const_mul (1 / x) (fun y => deriv η (y / x))
  rw [h_int] at H2
  linarith

/-- A smooth cutoff supported in `[0,1]`, used for the counterexample to `S_eq_integral`. -/
private noncomputable def counterEta : ℝ → ℝ :=
  (⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (1 / 2 : ℝ)).toFun

/-- The specialized identity in `S_eq_integral` has a checked counterexample. -/
theorem S_eq_integral_counterexample :
    ¬ (ContDiff ℝ 1 counterEta →
        Function.support counterEta ⊆ Set.Icc (0:ℝ) 1 →
        LeanLab.Tao2012.Cor48.S counterEta 1 ⌊(3:ℝ)⌋₊ 3 0 =
          - (1 / 3 : ℂ) * ∫ y in (0:ℝ)..3,
            ((deriv counterEta (y / 3) : ℝ) : ℂ) * LeanLab.Tao2012.Cor48.S one_Icc 1 ⌊y⌋₊ y 0) := by
  intro h
  have hdiff : ContDiff ℝ 1 counterEta := by
    exact (⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (1 / 2 : ℝ)).contDiff (n := 1)
  have hsupp : Function.support counterEta ⊆ Set.Icc (0:ℝ) 1 := by
    unfold counterEta
    rw [(⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (1 / 2 : ℝ)).support_eq]
    intro t ht
    have hdist : dist t (1 / 2 : ℝ) < 1 / 2 := Metric.mem_ball.mp ht
    have habs : |t - 1 / 2| < 1 / 2 := by simpa [Real.dist_eq] using hdist
    rw [abs_lt] at habs
    exact ⟨by linarith, by linarith⟩
  have htwo : counterEta (2 / 3) = 1 := by
    apply (⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (1 / 2 : ℝ)).one_of_mem_closedBall
    rw [Metric.mem_closedBall]
    simp [Real.dist_eq]
    norm_num
  have hlhs : LeanLab.Tao2012.Cor48.S counterEta 1 ⌊(3:ℝ)⌋₊ 3 0 = (Real.log 2 : ℂ) := by
    unfold LeanLab.Tao2012.Cor48.S
    norm_num [Finset.sum_range_succ, htwo,
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)]
  have hrhs : ∫ y in (0:ℝ)..3, ((deriv counterEta (y / 3) : ℝ) : ℂ) *
      LeanLab.Tao2012.Cor48.S one_Icc 1 ⌊y⌋₊ y 0 = 0 := by
    have hne : ∀ᵐ y : ℝ ∂volume, y ≠ 3 := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    have hc := intervalIntegral.integral_congr_ae (μ := volume) (a := 0) (b := 3)
      (f := fun y : ℝ => ((deriv counterEta (y / 3) : ℝ) : ℂ) *
        LeanLab.Tao2012.Cor48.S one_Icc 1 ⌊y⌋₊ y 0) (g := fun _ : ℝ => (0 : ℂ)) ?_
    simpa using hc
    filter_upwards [hne] with y hy
    intro hyu
    rw [Set.uIoc_of_le (by norm_num)] at hyu
    have hy3 : y < 3 := by
      rcases hyu.2.eq_or_lt with rfl | h
      · exact (hy rfl).elim
      · exact h
    have hz : LeanLab.Tao2012.Cor48.S one_Icc 1 ⌊y⌋₊ y 0 = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp only [mem_range] at hn
      have hfloor : ⌊y⌋₊ < 3 := (Nat.floor_lt (le_of_lt hyu.1)).2 hy3
      have hn2 : n < 2 := by omega
      interval_cases n <;> simp [ArithmeticFunction.vonMangoldt_apply]
    simp [hz]
  have heq := h hdiff hsupp
  rw [hlhs, hrhs] at heq
  simp only [mul_zero] at heq
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  have hclog : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast hlog
  exact hclog heq

/-- LEAF. Tao 2012, page 16, Lemma 4.2 proof. Summation by parts identity for `S`.
This substitutes the integral form of `η(n/x)` and exchanges the sum and the integral. -/
theorem S_eq_integral (η : ℝ → ℝ) (h_diff : ContDiff ℝ 1 η) (h_supp : Function.support η ⊆ Set.Icc 0 1)
    (q : ℕ) (x α : ℝ) (hx : 1 ≤ x) :
    S η q ⌊x⌋₊ x α = - (1 / x) * ∫ y in (0:ℝ)..x, ((deriv η (y / x) : ℝ) : ℂ) * S one_Icc q ⌊y⌋₊ y α := by
  sorry

/-- LEAF. Tao 2012, page 16, Lemma 4.2 proof. The integral norm inequality.
The norm of the integral is bounded by the integral of the norm, which is then bounded by
taking the supremum over the truncated sums. -/
private lemma S_norm_bound (q : ℕ) (x α : ℝ) (hx : 1 ≤ x) {y : ℝ} (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    ‖S one_Icc q ⌊y⌋₊ y α‖ ≤
      ∑ n ∈ range (⌊x⌋₊),
        |ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0)| := by
  have hexp : ∀ n : ℕ, ‖Complex.exp (2 * π * Complex.I * α * (n : ℂ))‖ = 1 := by
    intro n
    have h1 : Complex.exp (2 * π * Complex.I * (α : ℂ) * (n : ℂ))
        = Complex.exp (((2 * π * α * n : ℝ)) * Complex.I) := by
      congr 1
      push_cast
      ring
    rw [h1, Complex.norm_exp_ofReal_mul_I]
  rcases hy0.eq_or_lt with h | h
  · subst h
    have hz : S one_Icc q ⌊(0:ℝ)⌋₊ 0 α = 0 := by
      simp [LeanLab.Tao2012.Cor48.S]
    rw [hz, norm_zero]
    exact sum_nonneg fun n _ => abs_nonneg _
  · refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ n ∈ range (⌊y⌋₊),
        ‖(((ArithmeticFunction.vonMangoldt n : ℝ) * (if Nat.Coprime n q then 1 else 0) *
            one_Icc ((n : ℝ) / y) : ℝ) : ℂ) * Complex.exp (2 * π * Complex.I * α * (n : ℂ))‖
          ≤ |ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0)| := by
      intro n hn
      have hc : |one_Icc ((n : ℝ) / y)| ≤ 1 := abs_one_Icc _
      calc ‖(((ArithmeticFunction.vonMangoldt n : ℝ) * (if Nat.Coprime n q then 1 else 0) *
              one_Icc ((n : ℝ) / y) : ℝ) : ℂ) * Complex.exp (2 * π * Complex.I * α * (n : ℂ))‖
          = |ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0) * one_Icc ((n : ℝ) / y)| := by
            rw [norm_mul, hexp n, mul_one]
            exact RCLike.norm_ofReal _
        _ = |ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0)| *
              |one_Icc ((n : ℝ) / y)| := by rw [abs_mul]
        _ ≤ |ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0)| * 1 :=
            mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        _ = _ := mul_one _
    refine (sum_le_sum hterm).trans ?_
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => abs_nonneg _)
    intro n hn
    simp only [mem_range] at hn ⊢
    have hfl : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hyx
    exact lt_of_lt_of_le hn hfl

private lemma S_repr (q : ℕ) (x α : ℝ) (hx : 1 ≤ x) {y : ℝ} (hy0 : 0 < y) (hyx : y ≤ x) :
    S one_Icc q ⌊y⌋₊ y α =
      ∑ n ∈ range (⌊x⌋₊),
        ((ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0) : ℝ) : ℂ) *
          (if ((n : ℝ) + 1) ≤ y then 1 else 0) * Complex.exp (2 * π * Complex.I * α * (n : ℂ)) := by
  have hfl : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hyx
  have hsub : range (⌊y⌋₊) ⊆ range (⌊x⌋₊) := by
    intro n hn
    simp only [mem_range] at hn ⊢
    exact lt_of_lt_of_le hn hfl
  have hL : S one_Icc q ⌊y⌋₊ y α =
      ∑ n ∈ range (⌊y⌋₊),
        ((ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0) : ℝ) : ℂ) *
          Complex.exp (2 * π * Complex.I * α * (n : ℂ)) := by
    unfold LeanLab.Tao2012.Cor48.S
    refine sum_congr rfl fun n hn => ?_
    simp only [mem_range] at hn
    have hny : (n : ℝ) < y := by
      have h1 : ((n + 1 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
      have h3 : (n : ℝ) + 1 ≤ (⌊y⌋₊ : ℝ) := by push_cast at h1; exact h1
      have h4 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
      linarith
    have hmem : (n : ℝ) / y ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg (Nat.cast_nonneg n) hy0.le, by rw [div_le_one hy0]; exact hny.le⟩
    rw [one_Icc_mem hmem, mul_one]
  have hR : (∑ n ∈ range (⌊x⌋₊),
        ((ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0) : ℝ) : ℂ) *
          (if ((n : ℝ) + 1) ≤ y then 1 else 0) * Complex.exp (2 * π * Complex.I * α * (n : ℂ)))
      = ∑ n ∈ range (⌊y⌋₊),
        ((ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0) : ℝ) : ℂ) *
          Complex.exp (2 * π * Complex.I * α * (n : ℂ)) := by
    have h1 : (∑ n ∈ range (⌊y⌋₊),
        ((ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0) : ℝ) : ℂ) *
          (if ((n : ℝ) + 1) ≤ y then 1 else 0) * Complex.exp (2 * π * Complex.I * α * (n : ℂ)))
        = ∑ n ∈ range (⌊x⌋₊),
        ((ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0) : ℝ) : ℂ) *
          (if ((n : ℝ) + 1) ≤ y then 1 else 0) * Complex.exp (2 * π * Complex.I * α * (n : ℂ)) := by
      refine sum_subset hsub ?_
      intro n hn hn2
      simp only [mem_range] at hn hn2
      have hnn : ⌊y⌋₊ ≤ n := by omega
      have hge : (⌊y⌋₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnn
      have h2 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
      have h4 : ¬ ((n : ℝ) + 1 ≤ y) := by linarith
      simp [h4]
    rw [← h1]
    refine sum_congr rfl fun n hn => ?_
    simp only [mem_range] at hn
    have hny : (n : ℝ) + 1 ≤ y := by
      have h1 : ((n + 1 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
      have h2 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
      push_cast at h1
      linarith
    rw [if_pos hny, mul_one]
  rw [hL, hR]

private lemma deriv_eq_zero_off (η : ℝ → ℝ) (h_diff : ContDiff ℝ 1 η)
    (h_supp : Function.support η ⊆ Set.Icc 0 1) {t : ℝ} (ht : t ∉ Set.Icc (0:ℝ) 1) :
    deriv η t = 0 := by
  have hne : ∀ s ∉ Set.Icc (0:ℝ) 1, η s = 0 := fun s hs =>
    Function.notMem_support.mp fun h => hs (h_supp h)
  rcases lt_or_ge t 0 with h | h
  · have hzero : η =ᶠ[nhds t] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds h] with s hs
      simp only [Set.mem_Iio] at hs
      exact hne s (fun hmem => by simp only [Set.mem_Icc] at hmem; linarith [hmem.1, hs])
    rw [hzero.deriv_eq]
    simp
  · have h1 : 1 < t := by
      rcases lt_or_ge 1 t with h1 | h1
      · exact h1
      · exact absurd ⟨h, h1⟩ ht
    have hzero : η =ᶠ[nhds t] (fun _ => (0:ℝ)) := by
      filter_upwards [Ioi_mem_nhds h1] with s hs
      simp only [Set.mem_Ioi] at hs
      exact hne s (fun hmem => by simp only [Set.mem_Icc] at hmem; linarith [hmem.2, hs])
    rw [hzero.deriv_eq]
    simp

theorem norm_S_le (η : ℝ → ℝ) (h_diff : ContDiff ℝ 1 η) (h_supp : Function.support η ⊆ Set.Icc 0 1)
    (q : ℕ) (x α : ℝ) (hx : 1 ≤ x) :
    ‖- (1 / x) * ∫ y in (0:ℝ)..x, ((deriv η (y / x) : ℝ) : ℂ) * S one_Icc q ⌊y⌋₊ y α‖ ≤
      (∫ t, |deriv η t|) * ⨆ y ∈ Set.Icc 0 x, ‖S one_Icc q ⌊y⌋₊ y α‖ := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx0
  have hdc : Continuous fun y : ℝ => deriv η (y / x) :=
    (h_diff.continuous_deriv (by decide)).comp (continuous_id.div_const x)
  have hfc : Continuous fun y : ℝ => ((deriv η (y / x) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hdc
  set M := ⨆ y ∈ Set.Icc (0:ℝ) x, ‖S one_Icc q ⌊y⌋₊ y α‖ with hM
  have hBsum : (0:ℝ) ≤ ∑ n ∈ range (⌊x⌋₊),
      |ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0)| :=
    sum_nonneg fun n _ => abs_nonneg _
  have hBdd : BddAbove (Set.range fun y : ℝ =>
      ⨆ (_ : y ∈ Set.Icc (0:ℝ) x), ‖S one_Icc q ⌊y⌋₊ y α‖) := by
    refine ⟨∑ n ∈ range (⌊x⌋₊),
      |ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0)|, ?_⟩
    rintro _ ⟨y, rfl⟩
    by_cases hy : y ∈ Set.Icc (0:ℝ) x
    · haveI : Nonempty (y ∈ Set.Icc (0:ℝ) x) := ⟨hy⟩
      exact ciSup_le fun _ => S_norm_bound q x α hx hy.1 hy.2
    · haveI : IsEmpty (y ∈ Set.Icc (0:ℝ) x) := ⟨fun h => hy h⟩
      have h0 : (⨆ (_ : y ∈ Set.Icc (0:ℝ) x), ‖S one_Icc q ⌊y⌋₊ y α‖) ≤
          ∑ n ∈ range (⌊x⌋₊),
            |ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0)| := by
        rw [iSup_of_empty', Real.sSup_empty]
        exact hBsum
      exact h0
  have hMle : ∀ y ∈ Set.Icc (0:ℝ) x, ‖S one_Icc q ⌊y⌋₊ y α‖ ≤ M := by
    intro y hy
    have hinner : ‖S one_Icc q ⌊y⌋₊ y α‖ ≤
        ⨆ (_ : y ∈ Set.Icc (0:ℝ) x), ‖S one_Icc q ⌊y⌋₊ y α‖ := by
      haveI : Nonempty (y ∈ Set.Icc (0:ℝ) x) := ⟨hy⟩
      refine le_ciSup (f := fun _ : (y ∈ Set.Icc (0:ℝ) x) => ‖S one_Icc q ⌊y⌋₊ y α‖) ?_ hy
      exact ⟨‖S one_Icc q ⌊y⌋₊ y α‖, by rintro _ ⟨hh, rfl⟩; exact le_rfl⟩
    refine hinner.trans ?_
    rw [hM]
    exact le_ciSup hBdd y
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hMle 0 ⟨le_rfl, hx0.le⟩)
  set G : ℝ → ℂ := fun y => ∑ n ∈ range (⌊x⌋₊),
    ((ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0) : ℝ) : ℂ) *
      (if ((n : ℝ) + 1) ≤ y then 1 else 0) * Complex.exp (2 * π * Complex.I * α * (n : ℂ)) with hG
  have hGmeas : Measurable G := by
    rw [hG]
    refine Finset.measurable_sum _ fun n hn => ?_
    refine Measurable.mul_const (Measurable.const_mul ?_ _) _
    exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const
  have hIntG : IntervalIntegrable
      (fun y : ℝ => ((deriv η (y / x) : ℝ) : ℂ) * G y) volume (0:ℝ) x := by
    refine IntervalIntegrable.mono_fun'
      (f := fun y : ℝ => ((deriv η (y / x) : ℝ) : ℂ) * G y)
      (g := fun y : ℝ => ‖deriv η (y / x)‖ *
        (∑ n ∈ range (⌊x⌋₊),
          |ArithmeticFunction.vonMangoldt n * (if Nat.Coprime n q then 1 else 0)|)) ?_ ?_ ?_
    · exact (hdc.norm.mul_const _).intervalIntegrable 0 x
    · exact (Measurable.mul hfc.measurable hGmeas).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with y hy
      rw [Set.uIoc_of_le hx0.le] at hy
      have hGy : G y = S one_Icc q ⌊y⌋₊ y α := (S_repr q x α hx hy.1 hy.2).symm
      have hcast : ‖((deriv η (y / x) : ℝ) : ℂ)‖ = |deriv η (y / x)| := RCLike.norm_ofReal _
      rw [norm_mul, hGy, hcast, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (S_norm_bound q x α hx hy.1.le hy.2) (abs_nonneg _)
  have hInt : IntervalIntegrable
      (fun y : ℝ => ((deriv η (y / x) : ℝ) : ℂ) * S one_Icc q ⌊y⌋₊ y α) volume (0:ℝ) x := by
    refine hIntG.congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with y hy
    rw [Set.uIoc_of_le hx0.le] at hy
    rw [hG, S_repr q x α hx hy.1 hy.2]
  have hmaj : IntervalIntegrable (fun y : ℝ => ‖deriv η (y / x)‖ * M) volume (0:ℝ) x :=
    (hdc.norm.mul_const M).intervalIntegrable 0 x
  have hmono : ∫ y in (0:ℝ)..x, ‖((deriv η (y / x) : ℝ) : ℂ) * S one_Icc q ⌊y⌋₊ y α‖
      ≤ ∫ y in (0:ℝ)..x, ‖deriv η (y / x)‖ * M := by
    refine intervalIntegral.integral_mono_on hx0.le hInt.norm hmaj ?_
    intro y hy
    have hcast : ‖((deriv η (y / x) : ℝ) : ℂ)‖ = |deriv η (y / x)| := RCLike.norm_ofReal _
    rw [norm_mul, hcast, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hMle y hy) (abs_nonneg _)
  have hsubst : ∫ y in (0:ℝ)..x, ‖deriv η (y / x)‖ * M
      = x * ((∫ t in (0:ℝ)..1, |deriv η t|) * M) := by
    rw [intervalIntegral.integral_mul_const]
    simp only [Real.norm_eq_abs]
    rw [intervalIntegral.integral_comp_div (f := fun t : ℝ => |deriv η t|) hxne]
    simp only [zero_div, div_self hxne, smul_eq_mul]
    ring
  have hsupp : ∫ t in (0:ℝ)..1, |deriv η t| = ∫ t, |deriv η t| := by
    have e1 : ∫ t in (0:ℝ)..1, |deriv η t| = ∫ t in Set.Ioc (0:ℝ) 1, |deriv η t| :=
      intervalIntegral.integral_of_le (by norm_num)
    have e2 : ∫ t in Set.Ioc (0:ℝ) 1, |deriv η t| = ∫ t in Set.Icc (0:ℝ) 1, |deriv η t| :=
      (MeasureTheory.integral_Icc_eq_integral_Ioc).symm
    have e3 : ∫ t in Set.Icc (0:ℝ) 1, |deriv η t| = ∫ t, |deriv η t| :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht => by rw [deriv_eq_zero_off η h_diff h_supp ht]; simp)
    rw [e1, e2, e3]
  have hnormK : ‖((1 : ℂ) / (x : ℂ))‖ = 1 / x := by
    rw [norm_div, norm_one]
    have hcast : ‖((x : ℝ) : ℂ)‖ = |x| := RCLike.norm_ofReal _
    rw [hcast, abs_of_pos hx0]
  have hstep1 : ‖- ((1 : ℂ) / (x : ℂ)) * ∫ y in (0:ℝ)..x,
        ((deriv η (y / x) : ℝ) : ℂ) * S one_Icc q ⌊y⌋₊ y α‖
      = (1 / x) * ‖∫ y in (0:ℝ)..x, ((deriv η (y / x) : ℝ) : ℂ) * S one_Icc q ⌊y⌋₊ y α‖ := by
    rw [norm_mul, norm_neg, hnormK]
  rw [hstep1]
  have hpos : (0:ℝ) < 1 / x := by positivity
  have hnormint : ‖∫ y in (0:ℝ)..x, ((deriv η (y / x) : ℝ) : ℂ) * S one_Icc q ⌊y⌋₊ y α‖
      ≤ ∫ y in (0:ℝ)..x, ‖deriv η (y / x)‖ * M :=
    (intervalIntegral.norm_integral_le_integral_norm hx0.le).trans hmono
  refine (mul_le_mul_of_nonneg_left hnormint hpos.le).trans ?_
  rw [hsubst]
  have hval : (1 / x) * (x * ((∫ t in (0:ℝ)..1, |deriv η t|) * M))
      = (∫ t in (0:ℝ)..1, |deriv η t|) * M := by
    rw [show (1 / x : ℝ) * (x * ((∫ t in (0:ℝ)..1, |deriv η t|) * M))
        = ((1 / x) * x) * ((∫ t in (0:ℝ)..1, |deriv η t|) * M) by ring]
    rw [one_div, inv_mul_cancel₀ hxne, one_mul]
  rw [hval, hsupp]


/-- CITED. Tao 2012, page 16, Lemma 4.2, summation by parts for the smoothed prime sum.
Assembled from its leaves with no sorry. -/
theorem lemma4_2 (η : ℝ → ℝ) (h_diff : ContDiff ℝ 1 η) (h_supp : Function.support η ⊆ Set.Icc 0 1)
    (q : ℕ) (hq : 1 ≤ q) (x : ℝ) (hx : 1 ≤ x) (α : ℝ) :
      ‖S η q ⌊x⌋₊ x α‖ ≤ (∫ t, |deriv η t|) * ⨆ y ∈ Set.Icc 0 x, ‖S one_Icc q ⌊y⌋₊ y α‖ := by
  rw [S_eq_integral η h_diff h_supp q x α hx]
  exact norm_S_le η h_diff h_supp q x α hx

end LeanLab.Tao2012.DecompJ223
