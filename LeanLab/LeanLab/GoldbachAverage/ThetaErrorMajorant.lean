import LeanLab.GoldbachAverage.GSTheorem3Bound

/-!
The nonnegative majorant version of the theta layer reduction.
P0051 arXiv 2110.14250v2 page 4 eq. 18 and page 6 eq. 33.
This preserves the paper's distinction between the complex error and its majorant.
The local mean square input is explicit.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.ThetaLayers
open Complex Finset Filter MeasureTheory Set
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov LeanLab.LZCesaroShort

/-- The nonnegative majorant costs one logarithm in the layer sum. -/
theorem Emajorant_bound_of_local (a : ℝ) (ha : 0 ≤ a)
    (hlocal : ∃ K : ℝ, 0 ≤ K ∧
      ∀ N : ℕ, 2 ≤ N → ∀ ξ : ℝ, 1 / (N : ℝ) ≤ ξ → ξ ≤ 1 / 2 →
        ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2 ≤
          K * (N : ℝ) ^ a * ξ * (1 + Real.log N) ^ 4) :
    ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
      Emajorant N (Real.exp (-(1 / (N : ℝ)))) ≤ K * (N : ℝ) ^ a * Real.log N ^ 5 := by
  obtain ⟨K₁, hK₁0, hl⟩ := hlocal
  refine ⟨30 * (324 * K₁ + 16384), fun N hN2 => ?_⟩
  have hN : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set P := (N : ℝ) ^ a with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast hN) ha
  have hP0 : 0 ≤ P := by positivity
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  set r := Real.exp (-(1 / (N : ℝ))) with hr
  set L := Real.log N with hL
  have hlog2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hN2r
  have hL0 : 0 < L := by linarith
  set f : ℝ → ℝ := fun α => 2 * ‖St N α - 1 / zz N α‖ ^ 2 + 162 with hf
  set g : ℝ → ℝ := fun α => ‖IGenN N (1 / r) (-α)‖ with hg
  have hfc : Continuous f := (continuous_const.mul (continuous_St_sub hN)).add continuous_const
  have hf0 : ∀ α, 0 ≤ f α := fun α => by simp only [hf]; positivity
  have hgc : Continuous g := continuous_IGenN_norm N (1 / r)
  have hgG : ∀ α ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), g α ≤ 6 * LeanLab.PNTPort.Vinogradov.G (N : ℝ) α := fun α hα =>
    norm_IGenN_le hN (abs_le.mpr ⟨hα.1, hα.2⟩)
  set M := Nat.log 2 N + 1 with hM
  have hKM : (N : ℝ) ≤ 2 ^ M := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
    exact_mod_cast this.le
  -- step 1: the norm of the integral
  have step1 : Emajorant N r ≤ ∫ α in (-(1 / 2 : ℝ))..(1 / 2), g α * f α := by
    have hr0 : 0 < r := Real.exp_pos _
    have hr1 : r < 1 := by
      rw [hr, Real.exp_lt_one_iff]
      have := one_div_pos.mpr hN0
      linarith
    rw [Emajorant_eq_sym]
    apply intervalIntegral.integral_mono_on (by norm_num)
      (((continuous_FE N hr0 hr1).norm).intervalIntegrable (μ := volume) _ _)
      ((hgc.mul hfc).intervalIntegrable (μ := volume) _ _)
    intro α hα
    have hα' : |α| ≤ 1 / 2 := abs_le.mpr ⟨hα.1, hα.2⟩
    unfold FE
    rw [norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_psi_sub_I_sq_le hN hα') (norm_nonneg _)
  -- step 2: the dyadic layers
  have step2 := integral_G_le (H := N) (K := M) hN (by exact_mod_cast hKM) hfc hf0 hgc
    (by norm_num : (0 : ℝ) ≤ 6) hgG
  -- step 3: each layer
  have hlayer : ∀ k ∈ range (M + 1), 6 * (2 * (N : ℝ) / 2 ^ k) *
      ∫ α in (-xi N k)..(xi N k), f α ≤ 6 * (4 * K₁ * P * (1 + L) ^ 4 + 648) := by
    intro k _
    set ξ := xi N k with hξ
    have hξh : ξ ≤ 1 / 2 := xi_le_half N k
    have hξk : ξ ≤ (2 : ℝ) ^ k / N := xi_le N k
    have hξl : 1 / (N : ℝ) ≤ ξ := by
      rw [hξ]; unfold xi; apply le_min
      · apply div_le_div_of_nonneg_right _ hN0.le; exact one_le_pow₀ (by norm_num)
      · rw [div_le_iff₀ hN0]; linarith
    have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξl
    have hint : ∫ α in (-ξ)..ξ, f α =
        2 * (∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2) + 162 * (2 * ξ) := by
      simp only [hf]
      rw [intervalIntegral.integral_add (((continuous_St_sub hN).intervalIntegrable _ _).const_mul 2)
        intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
        smul_eq_mul]
      ring
    have hl1 := hl N hN2 ξ hξl hξh
    have hA : 2 * (N : ℝ) / 2 ^ k * ξ ≤ 2 := by
      have hξN : ξ * N ≤ 2 ^ k := (le_div_iff₀ hN0).mp hξk
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hB0 : 0 ≤ 2 * (N : ℝ) / 2 ^ k := by positivity
    rw [hint]
    have hstep : 2 * (N : ℝ) / 2 ^ k * (2 * (∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2) + 162 * (2 * ξ))
        ≤ 4 * K₁ * P * (1 + L) ^ 4 + 648 := by
      have e1 : 2 * (N : ℝ) / 2 ^ k * (2 * ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2) ≤
          4 * K₁ * P * (1 + L) ^ 4 := by
        have := mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ 2 * (2 * (N : ℝ) / 2 ^ k))
        have e2 : 2 * (2 * (N : ℝ) / 2 ^ k) * (K₁ * P * ξ * (1 + L) ^ 4) =
            2 * K₁ * P * (2 * (N : ℝ) / 2 ^ k * ξ) * (1 + L) ^ 4 := by ring
        rw [e2] at this
        have h5 : 2 * K₁ * P * (2 * (N : ℝ) / 2 ^ k * ξ) * (1 + L) ^ 4 ≤
            2 * K₁ * P * 2 * (1 + L) ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hA (by positivity)
        nlinarith
      have e3 : 2 * (N : ℝ) / 2 ^ k * (162 * (2 * ξ)) ≤ 648 := by nlinarith
      nlinarith
    nlinarith
  -- assemble
  have hsum : ∑ k ∈ range (M + 1), 6 * (2 * (N : ℝ) / 2 ^ k) * ∫ α in (-xi N k)..(xi N k), f α
      ≤ (M + 1) * (6 * (4 * K₁ * P * (1 + L) ^ 4 + 648)) := by
    calc _ ≤ ∑ _k ∈ range (M + 1), 6 * (4 * K₁ * P * (1 + L) ^ 4 + 648) := sum_le_sum hlayer
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hMl : (M : ℝ) + 1 ≤ 5 * L := by
    have h := natLog_le N hN
    have h23 : (2 : ℝ) / 3 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
    have hL23 : (2 : ℝ) / 3 ≤ L := le_trans h23 hL2
    have a : Real.log N / Real.log 2 ≤ 2 * L := by
      rw [div_le_iff₀ (by linarith)]
      have : L = Real.log N := rfl
      nlinarith
    have hM' : (M : ℝ) = Nat.log 2 N + 1 := by rw [hM]; push_cast; ring
    rw [hM']
    linarith
  have hlog4 : (1 + L) ^ 4 ≤ 81 * L ^ 4 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + L)
      (by linarith : 1 + L ≤ 3 * L) 4
    nlinarith only [h]
  have hL4 : (1 / 16 : ℝ) ≤ L ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by linarith : (1 / 2 : ℝ) ≤ L) 4
    norm_num at h
    exact h
  have hconst : (648 : ℝ) ≤ 16384 * P * L ^ 4 := by
    have hPL : L ^ 4 ≤ P * L ^ 4 := le_mul_of_one_le_left (by positivity) hP1
    nlinarith
  have hterm : 4 * K₁ * P * (1 + L) ^ 4 + 648 ≤
      (324 * K₁ + 16384) * P * L ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hlog4 (by positivity : 0 ≤ 4 * K₁ * P)
    nlinarith
  have hfin : ((M : ℝ) + 1) * (6 * (4 * K₁ * P * (1 + L) ^ 4 + 648)) ≤
      30 * (324 * K₁ + 16384) * P * L ^ 5 := by
    calc _ ≤ (5 * L) * (6 * (4 * K₁ * P * (1 + L) ^ 4 + 648)) :=
            mul_le_mul_of_nonneg_right hMl (by positivity)
      _ ≤ (5 * L) * (6 * ((324 * K₁ + 16384) * P * L ^ 4)) := by
            gcongr
      _ = _ := by ring
  push_cast at hsum ⊢
  calc Emajorant N r ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ _ := hsum
    _ ≤ _ := hfin

end LeanLab.GoldbachAverage.ThetaLayers
