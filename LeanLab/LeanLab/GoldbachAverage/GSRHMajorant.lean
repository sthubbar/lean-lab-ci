import LeanLab.GoldbachAverage.GSTheorem3Bound

/-!
P0051 arXiv 2110.14250v2, Theorem 4 page 4.
The RH layer proof bounds the paper's nonnegative majorant directly.
The psi estimate then follows from the proved Theorem 3 inequality.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage
open Complex Finset Filter MeasureTheory Set
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov LeanLab.LZCesaroShort

/-- Theorem 4's nonnegative majorant bound under RH. -/
theorem Emajorant_bound_RH (hRH : RiemannHypothesis) : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    Emajorant N (Real.exp (-(1 / (N : ℝ)))) ≤ K * N * Real.log N ^ 3 := by
  obtain ⟨K₁, hK₁0, hl⟩ := lemma1_full hRH
  refine ⟨30 * (40 * K₁ + 1400), fun N hN2 => ?_⟩
  have hN : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
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
      ∫ α in (-xi N k)..(xi N k), f α ≤ 6 * (4 * K₁ * N * (1 + L) ^ 2 + 648) := by
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
    have hl1 := hl N hN ξ (by
      have : 1 / (2 * (N : ℝ)) ≤ 1 / N := by
        apply one_div_le_one_div_of_le hN0; linarith
      linarith) hξh
    have hlog : (1 + Real.log (2 * N * ξ)) ^ 2 ≤ (1 + L) ^ 2 := by
      have h1 : 1 ≤ 2 * N * ξ := by
        have := (div_le_iff₀ hN0).mp hξl
        nlinarith
      have h2 : 2 * N * ξ ≤ N := by nlinarith
      have h3 := Real.log_nonneg h1
      have h4 := Real.log_le_log (by linarith) h2
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hA : 2 * (N : ℝ) / 2 ^ k * ξ ≤ 2 := by
      have hξN : ξ * N ≤ 2 ^ k := (le_div_iff₀ hN0).mp hξk
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hB0 : 0 ≤ 2 * (N : ℝ) / 2 ^ k := by positivity
    rw [hint]
    have hstep : 2 * (N : ℝ) / 2 ^ k * (2 * (∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2) + 162 * (2 * ξ))
        ≤ 4 * K₁ * N * (1 + L) ^ 2 + 648 := by
      have e1 : 2 * (N : ℝ) / 2 ^ k * (2 * ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2) ≤
          4 * K₁ * N * (1 + L) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ 2 * (2 * (N : ℝ) / 2 ^ k))
        have e2 : 2 * (2 * (N : ℝ) / 2 ^ k) * (K₁ * N * ξ * (1 + Real.log (2 * N * ξ)) ^ 2) =
            2 * K₁ * N * (2 * (N : ℝ) / 2 ^ k * ξ) * (1 + Real.log (2 * N * ξ)) ^ 2 := by ring
        rw [e2] at this
        have h5 : 2 * K₁ * N * (2 * (N : ℝ) / 2 ^ k * ξ) * (1 + Real.log (2 * N * ξ)) ^ 2 ≤
            2 * K₁ * N * 2 * (1 + L) ^ 2 := by
          have hk0 : 0 ≤ 2 * K₁ * N := by positivity
          calc 2 * K₁ * N * (2 * (N : ℝ) / 2 ^ k * ξ) * (1 + Real.log (2 * N * ξ)) ^ 2
              ≤ 2 * K₁ * N * 2 * (1 + Real.log (2 * N * ξ)) ^ 2 := by
                apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
                exact mul_le_mul_of_nonneg_left hA hk0
            _ ≤ 2 * K₁ * N * 2 * (1 + L) ^ 2 :=
                mul_le_mul_of_nonneg_left hlog (by positivity)
        nlinarith
      have e3 : 2 * (N : ℝ) / 2 ^ k * (162 * (2 * ξ)) ≤ 648 := by nlinarith
      nlinarith
    nlinarith
  -- assemble
  have hsum : ∑ k ∈ range (M + 1), 6 * (2 * (N : ℝ) / 2 ^ k) * ∫ α in (-xi N k)..(xi N k), f α
      ≤ (M + 1) * (6 * (4 * K₁ * N * (1 + L) ^ 2 + 648)) := by
    calc _ ≤ ∑ _k ∈ range (M + 1), 6 * (4 * K₁ * N * (1 + L) ^ 2 + 648) := sum_le_sum hlayer
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
  have hfin := fin_alg hK₁0 hN2r (by linarith) hMl
  push_cast at hsum hfin ⊢
  calc Emajorant N r ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ _ := hsum
    _ ≤ _ := hfin

/-- Theorem 4's psi bound follows from the majorant estimate and Theorem 3. -/
theorem gs_theorem4_psi (hRH : RiemannHypothesis) : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
    |Chebyshev.psi N - N| ≤ C * Real.sqrt N * Real.log N ^ 2 := by
  obtain ⟨K, hK⟩ := Emajorant_bound_RH hRH
  refine ⟨Real.sqrt (120 * max K 0), fun N hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hu : Emajorant N (Real.exp (-(1 / (N : ℝ)))) ≤ max K 0 * N * Real.log N ^ 3 := by
    refine (hK N hN).trans ?_
    gcongr
    exact le_max_left K 0
  have hsq : (Chebyshev.psi N - N) ^ 2 ≤
      (Real.sqrt (120 * max K 0) * Real.sqrt N * Real.log N ^ 2) ^ 2 := by
    calc _ ≤ 120 * Emajorant N (Real.exp (-(1 / (N : ℝ)))) * Real.log N :=
            gs_theorem3_bound_sq N hN
      _ ≤ 120 * (max K 0 * N * Real.log N ^ 3) * Real.log N :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num)) hl0
      _ = _ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hN0]
        ring
  have hsqabs : |Chebyshev.psi N - N| ^ 2 ≤
      (Real.sqrt (120 * max K 0) * Real.sqrt N * Real.log N ^ 2) ^ 2 := by
    rwa [sq_abs]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp hsqabs

/-- The two conclusions of Theorem 4 with their original logarithmic powers. -/
theorem gs_theorem4_proved (hRH : RiemannHypothesis) : ∃ C1 C2 : ℝ,
    (∀ N : ℕ, 2 ≤ N → Emajorant N (Real.exp (-(1 / (N : ℝ)))) ≤ C1 * N * Real.log N ^ 3) ∧
    (∀ N : ℕ, 2 ≤ N → |Chebyshev.psi N - N| ≤ C2 * Real.sqrt N * Real.log N ^ 2) := by
  obtain ⟨C1, h1⟩ := Emajorant_bound_RH hRH
  obtain ⟨C2, h2⟩ := gs_theorem4_psi hRH
  exact ⟨C1, C2, h1, h2⟩

end LeanLab.GoldbachAverage
