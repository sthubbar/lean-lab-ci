/-
Supply for the minor family in P0029 page 27, display 7.8.
Separate the bare smoothed fourth moment from the bRhat weighted contribution.
Both OPEN obligations retain the printed logarithm power five.
The sealed Decomp150d file is unchanged.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp328a
import LeanLab.BhowmikGrimmelt2026.PartialSums261
import LeanLab.BhowmikGrimmelt2026.SharpSupported261

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The minor arc coefficient with multiplier one. -/
noncomputable def minorBare328 (ϕ : ℝ → ℝ) (X N : ℕ) (ϑ : ℝ) : ℂ := by
  classical
  exact ∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
    Sphi ϕ N α ^ 2 * ee (-(N * α))

/-- The remaining minor coefficient, with multiplier negative bRhat. -/
noncomputable def minorWeighted328 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  minorError150 ϕ G X N ϑ η - minorBare328 ϕ X N ϑ

/-- The weighted minor remainder is exactly the coefficient with negative bRhat.
All integrals are justified by continuity before subtracting. -/
theorem minorWeighted_eq_integral328 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (ϕ : ℝ → ℝ) {X : ℕ} (hX : 2 ≤ X) (N : ℕ) (ϑ : ℝ)
    {η : ℝ} (hη : 0 < η) :
    minorWeighted328 ϕ G X N ϑ η =
      -(∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
        (fun α => Sphi ϕ N α ^ 2 * bRhat G ((X : ℝ) ^ ϑ)
          (fun q => η * X * q / (X : ℝ) ^ ϑ) α * ee (-(N * α))) α) := by
  classical
  let P : ℝ → Prop := MajorArc X ((X : ℝ) ^ ϑ)
  let f : ℝ → ℂ := fun α => Sphi ϕ N α ^ 2 *
    (1 - bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))
  let g : ℝ → ℂ := fun α => Sphi ϕ N α ^ 2 * ee (-(N * α))
  have he : Continuous (fun α : ℝ => ee (-(N * α))) :=
    ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
  have hf : Continuous f :=
    (((continuous_Sphi ϕ N).pow 2).mul (continuous_error_multiplier328 hG hX ϑ hη)).mul he
  have hg : Continuous g := ((continuous_Sphi ϕ N).pow 2).mul he
  have hs : MeasurableSet {α | ¬ P α} := (measurableSet_majorArc84 X ((X : ℝ) ^ ϑ)).compl
  have hmask (u : ℝ → ℂ) : {α | ¬ P α}.indicator u = (fun α => if P α then 0 else u α) := by
    funext α
    by_cases hm : P α <;> simp [Set.indicator, hm]
  have hif : IntervalIntegrable (fun α => if P α then 0 else f α) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    rw [← hmask f]
    exact hf.integrableOn_Ioc.indicator hs
  have hig : IntervalIntegrable (fun α => if P α then 0 else g α) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    rw [← hmask g]
    exact hg.integrableOn_Ioc.indicator hs
  unfold minorWeighted328 minorError150 minorBare328
  rw [← intervalIntegral.integral_sub hif hig, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro α hα
  by_cases hm : P α
  · have hm' : MajorArc X ((X : ℝ) ^ ϑ) α := hm
    simp [P, f, g, Set.indicator, hm']
  · have hm' : ¬ MajorArc X ((X : ℝ) ^ ϑ) α := hm
    simp [P, f, g, Set.indicator, hm']
    ring

/-- The bare minor family has the correct power budget with the proved log power nine.
This does not discharge the printed log power five obligation. -/
theorem minor_bare_log9_328 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 ≤
        C * ((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) *
          X * Real.log X ^ 9 := by
  classical
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  refine ⟨192 * (48600 : ℝ) ^ 2 * (L : ℝ) ^ 4, by positivity, ?_⟩
  intro X hX
  let R : ℝ := (X : ℝ) ^ ϑ
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < R := by linarith
  have hRX : R ≤ X := by
    calc
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = _ := Real.rpow_one _
  let W : ℝ → ℂ := fun α => if MajorArc X R α then 0 else 1
  let U : ℝ := (L : ℝ) *
    (48600 * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) * Real.log X ^ 4)
  have hW : Measurable W :=
    measurable_const.ite (measurableSet_majorArc84 X R) measurable_const
  have hWB (α : ℝ) : ‖W α‖ ≤ (1 : ℝ) := by
    by_cases hm : MajorArc X R α <;> simp [W, hm]
  have hsup (n : ℕ) (hn : n ≤ X) (α : ℝ) (hne : W α ≠ 0) : ‖Sphi ϕ n α‖ ≤ U := by
    have hm : ¬ MajorArc X R α := by
      intro hh
      exact hne (by simp [W, hh])
    exact Sphi_minor261 hϕ hL hX hR1 hRX hn hm
  have hfam := supported_family_sharp261 hϕ hL hX hW (by norm_num : (0 : ℝ) ≤ 1)
    (by dsimp [U]; positivity : 0 ≤ U) hWB hsup
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) =
      minorBare328 ϕ X N ϑ := by
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases hm : MajorArc X R α <;> simp [W, minorBare328, R, hm]
  have hA2 : ((X : ℝ) / Real.sqrt R) ^ 2 = (X : ℝ) ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hRp.le]
  have hD2 : ((X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 = (X : ℝ) ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
    norm_num
  have hsq : ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 ≤
      2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) := by
    rw [← hA2, ← hD2]
    nlinarith only [sq_nonneg ((X : ℝ) / Real.sqrt R - (X : ℝ) ^ (4 / 5 : ℝ))]
  simp_rw [heq] at hfam
  calc
    _ ≤ 96 * (1 : ℝ) ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X := hfam
    _ = 96 * (48600 : ℝ) ^ 2 * (L : ℝ) ^ 4 *
        ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 * X * Real.log X ^ 9 := by
      dsimp [U]
      ring
    _ ≤ 96 * (48600 : ℝ) ^ 2 * (L : ℝ) ^ 4 *
        (2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ))) * X * Real.log X ^ 9 := by
      gcongr
    _ = _ := by dsimp [R]; ring

/-- The proved logarithm power nine cannot be replaced by power five using a constant alone.
This is a bound comparison, not a refutation of the minor family leaf. -/
theorem log9_not_uniformly_log5_328 (C : ℝ) (hC : 0 ≤ C) :
    ∃ X : ℕ, 2 ≤ X ∧ C * Real.log (X : ℝ) ^ 5 < Real.log X ^ 9 := by
  obtain ⟨X, hX⟩ := exists_nat_gt (max 2 (Real.exp (C + 2)))
  have hX2 : (2 : ℝ) < X := (le_max_left _ _).trans_lt hX
  have hX2' : 2 ≤ X := by exact_mod_cast hX2.le
  have hlog := Real.log_lt_log (Real.exp_pos (C + 2)) ((le_max_right _ _).trans_lt hX)
  rw [Real.log_exp] at hlog
  have hlog1 : 1 ≤ Real.log (X : ℝ) := by linarith
  have hlog4 : C < Real.log (X : ℝ) ^ 4 :=
    (by linarith : C < Real.log (X : ℝ)).trans_le (le_self_pow₀ hlog1 (by norm_num : (4 : ℕ) ≠ 0))
  have hh := mul_lt_mul_of_pos_right hlog4 (pow_pos (by linarith : 0 < Real.log (X : ℝ)) 5)
  refine ⟨X, hX2', ?_⟩
  convert hh using 1 <;> ring

/-- LEAF. Page 27, the smoothed minor fourth moment step in the proof of 7.8.
OPEN bare coefficient estimate. There is no major weight or eta parameter.
This is the actual varying smoothing family with logarithm power five. -/
theorem minor_bare_family328 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  classical
  obtain ⟨C, hC, hbound⟩ := smoothed_family_bound261 hϕ
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2pow4 : 0 < (Real.log (2 : ℝ)) ^ 4 := pow_pos hlog2pos 4
  refine ⟨C / (Real.log (2 : ℝ)) ^ 4, by positivity, ?_⟩
  intro X hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hlogXpos : 0 < Real.log (X : ℝ) := by
    refine lt_of_lt_of_le ?_ (Real.log_le_log ?_ hX1)
    · exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
    · norm_num
  have hlog_le : Real.log (X : ℝ) ≤ Real.log (X : ℝ) ^ 5 / (Real.log (2 : ℝ)) ^ 4 := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hX1
      have hlog2gt : (1 / 2 : ℝ) < Real.log (2 : ℝ) := by
        have := Real.log_two_gt_d9
        linarith
      linarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 4
    have hh := mul_le_mul_of_nonneg_right hp hlogX
    have hpos : 0 < (Real.log (2 : ℝ)) ^ 4 := hlog2pow4
    calc
      Real.log (X : ℝ) = Real.log (X : ℝ) * 1 := by ring
      _ ≤ Real.log (X : ℝ) * ((Real.log (X : ℝ)) ^ 4 / (Real.log (2 : ℝ)) ^ 4) := by
        refine mul_le_mul_of_nonneg_left ?_ hlogX
        have hdiv : 1 ≤ (Real.log (X : ℝ)) ^ 4 / (Real.log (2 : ℝ)) ^ 4 := by
          refine (one_le_div ?_).mpr hp
          exact hlog2pow4
        exact hdiv
      _ = Real.log (X : ℝ) ^ 5 / (Real.log (2 : ℝ)) ^ 4 := by ring
  have hbound' := hbound X hX (fun α => if MajorArc X ((X : ℝ) ^ ϑ) α then (0 : ℂ) else 1)
    (measurable_const.ite (measurableSet_majorArc84 X ((X : ℝ) ^ ϑ)) measurable_const)
    1 (by norm_num) (by
      intro α
      by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α
      · simp [hm]
      · simp [hm])
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
        (if MajorArc X ((X : ℝ) ^ ϑ) α then (0 : ℂ) else 1) * ee (-(N * α))) =
      minorBare328 ϕ X N ϑ := by
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α
    · simp [minorBare328, hm]
    · simp [minorBare328, hm]
  simp_rw [heq] at hbound'
  have hR : (X : ℝ) ^ ϑ ≥ 1 := Real.one_le_rpow hX1 hϑ.le
  have hRpos : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < X)) ϑ
  have hcoeff : 1 ≤ ((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ) := by
    have h1 : 0 ≤ ((X : ℝ) ^ ϑ)⁻¹ := inv_nonneg.mpr hR
    have h2 : 0 ≤ (X : ℝ) ^ (-(2 / 5) : ℝ) := by positivity
    nlinarith
  calc
    ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 ≤
      C * (X : ℝ) ^ 3 * Real.log (X : ℝ) := hbound'
    _ ≤ C * (X : ℝ) ^ 3 * (Real.log (X : ℝ) ^ 5 / (Real.log (2 : ℝ)) ^ 4) :=
      mul_le_mul_of_nonneg_left hlog_le (by positivity)
    _ = (C / (Real.log (2 : ℝ)) ^ 4) * (X : ℝ) ^ 3 * Real.log (X : ℝ) ^ 5 := by ring
    _ ≤ (C / (Real.log (2 : ℝ)) ^ 4) * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
        (X : ℝ) ^ 3 * Real.log (X : ℝ) ^ 5 := by
      gcongr
      exact hcoeff

/-- LEAF. Page 27, the bounded bRhat multiplier step in the minor part of 7.8.
OPEN weighted coefficient estimate. The bare coefficient is removed.
The full weight remainder and the printed logarithm power five remain obligations. -/
theorem minor_weighted_family328 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorWeighted328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  classical
  obtain ⟨C, hC, hbound⟩ := smoothed_family_bound261 hϕ
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2pow4 : 0 < (Real.log (2 : ℝ)) ^ 4 := pow_pos hlog2pos 4
  -- Get a uniform bound for bRhat from GThat_bound
  obtain ⟨D, hD, hGT⟩ := GThat_bound hG.supp hG.smooth (1 : ℝ)
  have hbRhat_bound (α : ℝ) : ‖bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α‖ ≤ 2 * D := by
    -- We need to show this bound holds for all α, not just those in the major arc
    -- The GThat_bound gives us a bound for T ≥ 1
    -- We need to relate bRhat to GThat
    sorry
  sorry

/-- Exact minor_family150 statement assembled from the bare and weighted pieces.
CONDITIONAL ON minor_bare_family328 and minor_weighted_family328. -/
theorem minor_family_supply328 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := minor_bare_family328 hϕ ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := minor_weighted_family328 hϕ hG ϑ hϑ hϑ'
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hbare := h₁ X hX
  have hweighted := h₂ X hX η hη hη1 hscale
  have hsplit := coefficient_split328 (Finset.Icc 1 X)
    (fun N => minorError150 ϕ G X N ϑ η) (fun N => minorBare328 ϕ X N ϑ)
  dsimp [minorWeighted328] at hweighted
  nlinarith

/-- The actual minor family has the printed power budget with log power one when R is below two.
The only discrete weight term is bounded uniformly. No power five leaf is used. -/
theorem minor_family_single_denominator328 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → (X : ℝ) ^ ϑ < 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X := by
  classical
  obtain ⟨D, hD, hGT⟩ := GThat_bound hG.supp hG.smooth (1 : ℝ)
  obtain ⟨C, hC, hfamily⟩ := smoothed_family_bound261 hϕ
  let B : ℝ := 1 + 2 * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨2 * C * B ^ 2, by positivity, ?_⟩
  intro X hX hR2 η hη hη1 hscale
  let R : ℝ := (X : ℝ) ^ ϑ
  let T : ℝ := η * X / R
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < R := by linarith
  have hT1 : 1 ≤ T := by
    apply (le_div_iff₀ hRp).mpr
    change 10 * R ^ 2 ≤ η * X at hscale
    nlinarith [sq_nonneg (R - 1)]
  have hTp : 0 < T := by linarith
  have hb (α : ℝ) :
      ‖bRhat G R (fun q => η * X * q / R) α‖ ≤ 2 * D := by
    rw [bRhat_single_denominator328 hG hR1 hR2 _ (by positivity)]
    have ht := hGT T α hT1
    have hp1 : (1 + T * intDist α) ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [intDist_nonneg α]) (by norm_num)
    have hp2 : T ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
    have heq : η * X * (1 : ℕ) / R = T := by dsimp [T]; simp
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) hD.le]
  let W : ℝ → ℂ := fun α => if MajorArc X R α then 0 else
    1 - bRhat G R (fun q => η * X * q / R) α
  have hW : Measurable W := measurable_const.ite (measurableSet_majorArc84 X R)
    (continuous_error_multiplier328 hG hX ϑ hη).measurable
  have hWB (α : ℝ) : ‖W α‖ ≤ B := by
    by_cases hm : MajorArc X R α
    · simp only [W, if_pos hm, norm_zero]
      exact hB
    · simp only [W, if_neg hm]
      have hh := norm_sub_le (1 : ℂ) (bRhat G R (fun q => η * X * q / R) α)
      rw [norm_one] at hh
      exact hh.trans (by dsimp [B]; linarith [hb α])
  have hfam := hfamily X hX W hW B hB hWB
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) =
        minorError150 ϕ G X N ϑ η := by
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases hm : MajorArc X R α <;> simp [W, R, hm]
  simp_rw [heq] at hfam
  have hinv : (1 / 2 : ℝ) ≤ R⁻¹ := by
    simpa only [one_div] using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      hRp hR2.le
  have hpower : 0 ≤ (X : ℝ) ^ (-(2 / 5) : ℝ) := by positivity
  have hcoeff : 1 ≤ 2 * (R⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) := by linarith
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hh := mul_le_mul_of_nonneg_right hcoeff
    (by positivity : 0 ≤ C * B ^ 2 * (X : ℝ) ^ 3 * Real.log X)
  change (∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) ≤
    (2 * C * B ^ 2) * (R⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X
  nlinarith

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.minorBare328
#print axioms LeanLab.BhowmikGrimmelt2026.minorWeighted328
#print axioms LeanLab.BhowmikGrimmelt2026.minor_bare_family328
#print axioms LeanLab.BhowmikGrimmelt2026.minor_weighted_family328
#print axioms LeanLab.BhowmikGrimmelt2026.minor_family_supply328

#print axioms LeanLab.BhowmikGrimmelt2026.minorWeighted_eq_integral328

#print axioms LeanLab.BhowmikGrimmelt2026.minor_bare_log9_328

#print axioms LeanLab.BhowmikGrimmelt2026.log9_not_uniformly_log5_328

#print axioms LeanLab.BhowmikGrimmelt2026.minor_family_single_denominator328
