import LeanLab.LZCesaroShort.Sec5Proof

/-!
# P0058 Section 5 under RH for every `1 ≤ H ≤ N`

Lab proof, unit U-6210, CLOUD 20261020T0817Z-cloud38. AI wrote this file: `lz_sec5_rh_proved` of
`Sec5Proof.lean` with `1 ≤ H` in place of `2 ≤ H`; its proof never used `H ≥ 2`. CONDITIONAL
ON RiemannHypothesis only. Binary Goldbach is OPEN.
-/

open Finset Complex
open scoped ArithmeticFunction.vonMangoldt Chebyshev

noncomputable section
namespace LeanLab.LZCesaroShort

open PNTPort.ExplicitPsi1

/-- **Section 5 for every `1 ≤ H ≤ N`**, CONDITIONAL ON RH only. -/
theorem sec5_rh_one (hRH : RiemannHypothesis) : ∃ N₀ : ℕ, ∃ K : ℝ, ∀ N H : ℕ, N₀ ≤ N → 1 ≤ H → H ≤ N →
    ‖ZH N H / (H : ℂ)‖ ≤ K * (H * Real.sqrt N * Real.log N ^ 2 + N) := by
  obtain ⟨C1, hC1, hZ1⟩ := zero_sum_inv_bound
  set SH := ∑' ρ : Zall, hw ρ with hSH
  have hSH0 : 0 ≤ SH := tsum_nonneg fun ρ => hw_nonneg ρ
  refine ⟨3, 18 * C1 + 96 * SH, fun N H hN hH2 hHN => ?_⟩
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hH2r : (1 : ℝ) ≤ H := by exact_mod_cast hH2
  have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hN1 : 1 ≤ N := by omega
  set T : ℝ := (N : ℝ) ^ 2 / H with hT
  have hHpos : (0 : ℝ) < H := by linarith
  have hTN : (N : ℝ) ≤ T := by rw [hT, le_div_iff₀ hHpos]; nlinarith
  have hT1 : 1 ≤ T := by linarith
  set A : ℝ := (H : ℝ) ^ 2 * (2 * N) ^ (1 / 2 : ℝ) with hA
  set B : ℝ := 4 * (2 * (N : ℝ)) ^ 3 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  set g : Zall → ℝ := fun ρ => ‖(analyticOrderNatAt riemannZeta ρ.1 : ℂ) * Dz N H ρ.1‖ with hg
  have hre : ∀ ρ : Zall, ρ.1.re = 1 / 2 := fun ρ => rh_re hRH ρ.2
  have hgB : ∀ ρ : Zall, g ρ ≤ B * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 3) := by
    intro ρ
    simp only [hg, norm_mul, Complex.norm_natCast]
    have hρ : ρ.1 ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} := by
      rw [← Zall_eq]; exact ρ.2
    have := Dz_bound_B hHN hN1 hρ.2.1 hρ.2.2
    calc (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * ‖Dz N H ρ.1‖
        ≤ (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * (B / ‖ρ.1‖ ^ 3) := by gcongr
      _ = B * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 3) := by ring
  have hhalf : ∀ ρ : Zall, 1 / 2 ≤ ‖ρ.1‖ := fun ρ => by
    rw [← hre ρ]; exact (le_abs_self _).trans (abs_re_le_norm _)
  have hcube : ∀ ρ : Zall, ∀ t : ℝ, 0 < t → t ≤ ‖ρ.1‖ →
      (analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 3 ≤
        (1 / t) * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2) := by
    intro ρ t ht htρ
    have hn : 0 < ‖ρ.1‖ := by linarith
    rw [show ‖ρ.1‖ ^ 3 = ‖ρ.1‖ * ‖ρ.1‖ ^ 2 by ring, ← div_div]
    rw [show (1 / t) * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2) =
      (analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2 / t by ring, div_right_comm]
    apply div_le_div_of_nonneg_left (by positivity) ht htρ
  have hgsum : Summable g := by
    refine Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) (fun ρ => ?_)
      (summable_hw.mul_left (B * 2 * 3))
    refine (hgB ρ).trans ?_
    have := hcube ρ (1 / 2) (by norm_num) (hhalf ρ)
    have h3 := inv_sq_le_hw (hre ρ)
    calc B * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 3)
        ≤ B * ((1 / (1 / 2)) * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2)) := by
          gcongr
      _ ≤ B * ((1 / (1 / 2)) * (3 * hw ρ.1)) := by gcongr
      _ = B * 2 * 3 * hw ρ.1 := by ring
  -- the split bound for every finite partial sum
  have hpart : ∀ u : Finset Zall, ∑ ρ ∈ u, g ρ ≤
      A * (C1 * (Real.log T + 1) ^ 2) + B / T * (3 * SH) := by
    intro u
    rw [← Finset.sum_filter_add_sum_filter_not u (fun ρ => ‖ρ.1‖ ≤ T)]
    apply add_le_add
    · calc ∑ ρ ∈ u.filter (fun ρ => ‖ρ.1‖ ≤ T), g ρ
          ≤ ∑ ρ ∈ u.filter (fun ρ => ‖ρ.1‖ ≤ T),
              A * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖) := by
            apply sum_le_sum; intro ρ _
            simp only [hg, norm_mul, Complex.norm_natCast]
            have := Dz_bound_A hHN hN1 (hre ρ)
            calc (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * ‖Dz N H ρ.1‖
                ≤ (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * (A / ‖ρ.1‖) := by gcongr
              _ = A * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖) := by ring
        _ = A * ∑ ρ ∈ (u.filter (fun ρ => ‖ρ.1‖ ≤ T)).map (Function.Embedding.subtype _),
              (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
            rw [Finset.sum_map, Finset.mul_sum]; rfl
        _ ≤ A * ∑ ρ ∈ (zeros_rect_finite 2 T).toFinset,
              (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
            gcongr
            intro ρ hρ
            rw [Finset.mem_map] at hρ
            obtain ⟨⟨ρ', hρ'Z⟩, hρ'u, rfl⟩ := hρ
            rw [Finset.mem_filter] at hρ'u
            rw [Set.Finite.mem_toFinset]
            have hre1 := Zall_re_lt hρ'Z
            have him : |ρ'.im| ≤ T := le_trans (abs_im_le_norm _) hρ'u.2
            refine ⟨(mem_rect (by norm_num) (by linarith)).mpr
              ⟨⟨hρ'Z.2, by simp; linarith⟩, abs_le.mp ?_⟩, hρ'Z.1⟩
            simpa using him
        _ ≤ A * (C1 * (Real.log T + 1) ^ 2) := by gcongr; exact hZ1 T hT1
    · calc ∑ ρ ∈ u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ T), g ρ
          ≤ ∑ ρ ∈ u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ T), B / T * (3 * hw ρ.1) := by
            apply sum_le_sum; intro ρ hρ
            rw [Finset.mem_filter] at hρ
            refine (hgB ρ).trans ?_
            have := hcube ρ T (by linarith) (le_of_lt (lt_of_not_ge hρ.2))
            have h3 := inv_sq_le_hw (hre ρ)
            calc B * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 3)
                ≤ B * ((1 / T) * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2)) := by
                  gcongr
              _ ≤ B * ((1 / T) * (3 * hw ρ.1)) := by gcongr
              _ = B / T * (3 * hw ρ.1) := by ring
        _ = B / T * (3 * ∑ ρ ∈ u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ T), hw ρ.1) := by
            rw [Finset.mul_sum, Finset.mul_sum]
        _ ≤ B / T * (3 * SH) := by
            gcongr
            exact summable_hw.sum_le_tsum _ (fun ρ _ => hw_nonneg ρ)
  have htsum : ∑' ρ, g ρ ≤ A * (C1 * (Real.log T + 1) ^ 2) + B / T * (3 * SH) :=
    Real.tsum_le_of_sum_le (fun ρ => norm_nonneg _) hpart
  have hZH : ZH N H = ∑' ρ : Zall, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * Dz N H ρ.1 := by
    have e : (∑' ρ : Zall, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * Dz N H ρ.1) =
        ∑' ρ : NontrivialZero, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * Dz N H ρ.1 := by
      rw [Zall_eq]; rfl
    rw [e]; rfl
  have hnorm : ‖ZH N H‖ ≤ A * (C1 * (Real.log T + 1) ^ 2) + B / T * (3 * SH) := by
    rw [hZH]
    exact (norm_tsum_le_tsum_norm hgsum).trans htsum
  -- the final arithmetic
  have hlogN : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlogT : Real.log T ≤ 2 * Real.log N := by
    rw [hT, Real.log_div (by positivity) hHpos.ne', Real.log_pow]
    have : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    push_cast; linarith
  have hL : (Real.log T + 1) ^ 2 ≤ 9 * Real.log N ^ 2 := by
    have : 0 ≤ Real.log T := Real.log_nonneg hT1
    nlinarith
  have hsq : (2 * (N : ℝ)) ^ (1 / 2 : ℝ) ≤ 2 * Real.sqrt N := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    gcongr
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hHpos]
  refine hnorm.trans ?_
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have e1 : A * (C1 * (Real.log T + 1) ^ 2) ≤ 18 * C1 * (H * Real.sqrt N * Real.log N ^ 2) * H := by
    rw [hA]
    calc (H : ℝ) ^ 2 * (2 * N) ^ (1 / 2 : ℝ) * (C1 * (Real.log T + 1) ^ 2)
        ≤ (H : ℝ) ^ 2 * (2 * Real.sqrt N) * (C1 * (9 * Real.log N ^ 2)) := by gcongr
      _ = 18 * C1 * (H * Real.sqrt N * Real.log N ^ 2) * H := by ring
  have e2 : B / T * (3 * SH) = 96 * SH * N * H := by
    rw [hB, hT]; field_simp; ring
  have : 0 ≤ H * Real.sqrt N * Real.log N ^ 2 := by positivity
  calc A * (C1 * (Real.log T + 1) ^ 2) + B / T * (3 * SH)
      ≤ 18 * C1 * (H * Real.sqrt N * Real.log N ^ 2) * H + 96 * SH * N * H := by rw [e2]; linarith
    _ ≤ (18 * C1 + 96 * SH) * (H * Real.sqrt N * Real.log N ^ 2 + N) * H := by
        have : 0 ≤ 18 * C1 * N * H := by positivity
        have : 0 ≤ 96 * SH * (H * Real.sqrt N * Real.log N ^ 2) * H := by positivity
        nlinarith

end LeanLab.LZCesaroShort
