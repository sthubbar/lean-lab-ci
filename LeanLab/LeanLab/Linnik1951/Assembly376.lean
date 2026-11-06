/-
P0093 pages 158 to 169. Assemble the refined supply inputs with the proved arithmetic tail.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Arithmetic376
import LeanLab.Linnik1951.Decomp376b
import LeanLab.Linnik1951.Decomp376c
import LeanLab.Linnik1951.Decomp376d
import LeanLab.Linnik1951.Decomp376f
import LeanLab.Linnik1951.Decomp357j

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997

/-- P0093 Page 158 final sentence. Exact negative outer statement by character reflection. CONDITIONAL only on outer_to_kernels376 after the two real kernel bounds are proved. -/
theorem mellin_negative_far_refined376 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..-(4 / (N : ℝ)),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 10 := by
  obtain ⟨B, hB, N0, hpos⟩ := mellin_positive_far_decomposed376 hG
  refine ⟨B, hB, N0, ?_⟩
  intro N hN q hq hqt χ hχ
  have hstar : star χ ≠ 1 := by
    intro h
    apply hχ
    simpa only [star_star, star_one] using congrArg star h
  rw [← intervalIntegral.integral_comp_neg]
  simp_rw [character_norm_reflect357]
  exact hpos N hN q hq hqt (star χ) hstar

/-- P0093 Page 159 equation 5.2. Exact MellinBound280 assembly through the refined central and outer estimates. CONDITIONAL on the stated analytic leaves. -/
theorem mellin_bound_refined376 (hG : LeanLab.DERZ1997.GRH) : MellinBound280 := by
  obtain ⟨B0, hB0, N0, h0⟩ := mellin_near_decomposed376 hG
  obtain ⟨Bp, hBp, Np, hp⟩ := mellin_positive_far_decomposed376 hG
  obtain ⟨Bm, hBm, Nm, hm⟩ := mellin_negative_far_refined376 hG
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨Bm + B0 + Bp, by positivity, max 1 (max L (max N0 (max Np Nm))), ?_⟩
  intro N hN q hq hqt χ hχ
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hLN : L < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have h0N : N0 < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hpN : Np < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hN
  have hmN : Nm < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hN
  have hlog : 1 ≤ Real.log N := by
    have hLNreal : (L : ℝ) < (N : ℝ) := by exact_mod_cast hLN
    have hh := Real.log_le_log (Real.exp_pos 1) (hL.trans hLNreal).le
    simpa only [Real.log_exp] using hh
  have h6 : Real.log N ^ 6 ≤ Real.log N ^ 13 :=
    pow_le_pow_right₀ hlog (by norm_num)
  have h10 : Real.log N ^ 10 ≤ Real.log N ^ 13 :=
    pow_le_pow_right₀ hlog (by norm_num)
  have hcont : Continuous (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) :=
    (continuous_character_prime357 χ N (by omega)).norm.pow 2
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (-(4 / (N : ℝ))))
    (hcont.intervalIntegrable (-(4 / (N : ℝ))) (4 / (N : ℝ)))
  have hadd' := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (4 / (N : ℝ)))
    (hcont.intervalIntegrable (4 / (N : ℝ)) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))))
  rw [← hadd', ← hadd]
  have b0 := (h0 N h0N q hq hqt χ hχ).trans
    (mul_le_mul_of_nonneg_left h6 (by positivity))
  have bp := (hp N hpN q hq hqt χ hχ).trans
    (mul_le_mul_of_nonneg_left h10 (by positivity))
  have bm := (hm N hmN q hq hqt χ hχ).trans
    (mul_le_mul_of_nonneg_left h10 (by positivity))
  calc
    _ ≤ Bm * N / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 +
        B0 * N / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 +
        Bp * N / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 :=
      add_le_add (add_le_add bm b0) bp
    _ = _ := by ring

/-- P0093 Page 168 equations 10.6 and 10.7. Exact major_error280 statement. The arithmetic replacement is proved. CONDITIONAL on the two finite local expansion leaves, GRH and Mellin. -/
theorem major_error_refined376 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - mainTerm111 k N| ≤
        ε * scale111 k N := by
  obtain ⟨Na, ha⟩ := major_to_truncated_decomposed376 hG hM k hk (ε / 2) (by positivity)
  obtain ⟨Nt, ht⟩ := truncated_to_main_proved376 k hk (ε / 2) (by positivity)
  refine ⟨max Na Nt, ?_⟩
  intro N hev hN
  have hA := ha N hev (lt_of_le_of_lt (le_max_left _ _) hN)
  have hT := ht N hev (lt_of_le_of_lt (le_max_right _ _) hN)
  calc
    _ ≤ |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| +
        |truncatedMain357 k N - mainTerm111 k N| := abs_sub_le _ _ _
    _ ≤ ε / 2 * scale111 k N + ε / 2 * scale111 k N := add_le_add hA hT
    _ = _ := by ring

/-- P0093 Page 166 equation 9.2. Exact exceptional_error280 statement through the refined interval cover and doubled system mass. CONDITIONAL on these analytic and geometric inputs. -/
theorem exceptional_error_refined376 (hG : LeanLab.DERZ1997.GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ k : ℕ, 3 ≤ k →
      ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |arcContribution280 k N (exceptionalArcs280 N η)| ≤ ε * scale111 k N := by
  obtain ⟨η, hη, hη1, C, hC, Nc, hc⟩ := exceptional_prime_mass_decomposed376 hG
  obtain ⟨A, hA, Na, ha⟩ := power_uniform_log357
  refine ⟨η, hη, hη1, ?_⟩
  intro k hk ε hε
  obtain ⟨Ne, he⟩ := power_saving_negligible357 (Real.exp 1 * A ^ k * C)
    (1 / 100) (by positivity) (by norm_num) k ε hε
  refine ⟨max 2 (max Nc (max Na Ne)), ?_⟩
  intro N hev hN
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hcN : Nc < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have haN : Na < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have heN : Ne < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hscale : (N : ℝ) ≤ scale111 k N := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast h2.le)
    have hr : 1 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hl)
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hr)
  have hbound := arc_abs_le_prime_mass357 k N (by omega) (exceptionalArcs280 N η)
    (fun α hα => hα.1) (measurable_exceptional357 N (by omega) η)
    (A * Real.log N) (mul_nonneg hA.le hlog) (fun α _ => ha N haN α)
  calc
    _ ≤ Real.exp 1 * (A * Real.log N) ^ k *
        (C * (N : ℝ) ^ (1 - (1 / 100 : ℝ))) :=
      hbound.trans (mul_le_mul_of_nonneg_left (hc N hcN) (by positivity))
    _ = (Real.exp 1 * A ^ k * C) * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) * Real.log N ^ k := by
      rw [mul_pow]; ring
    _ ≤ ε * N := he N heN
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale hε.le

/-- P0093 Page 168 after equation 10.7. Exact error_bound111 statement assembled through the task376 supply leaves. The singular tail and remaining minor estimate are proved. CONDITIONAL on the remaining explicit inputs. -/
theorem error_bound_refined376 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 ∧
      ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |(representationCount111 k N : ℝ) - mainTerm111 k N| ≤
          5 * C * scale111 k N * (1 - η) ^ (k - 2) := by
  obtain ⟨η, hη, hη1, hE⟩ := exceptional_error_refined376 hG
  obtain ⟨C, hC, hR⟩ := minor_error_proved357 η hη hη1 (fun N α hα => good_minor_power_bound280 N η α hα)
  refine ⟨C, η, hC, hη, hη1, ?_⟩
  intro k hk
  have hr : 0 < (1 - η) ^ (k - 2) := pow_pos (by linarith) _
  have hε : 0 < C * (1 - η) ^ (k - 2) := mul_pos hC hr
  obtain ⟨NM, hM⟩ := major_error_refined376 hG (mellin_bound_refined376 hG) k hk _ hε
  obtain ⟨NE, hE⟩ := hE k hk _ hε
  obtain ⟨NR, hR⟩ := hR k hk
  refine ⟨max 1 (max NM (max NE NR)), ?_⟩
  intro N hev hN
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hm : NM < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have he : NE < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hg : NR < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hmajor := hM N hev hm
  have hexc := hE N hev he
  have hminor := hR N hev hg
  have hs := (scale_pos111 k N h1).le
  have hid := circle_partition_decomposed357 k N (by omega) η
  have htri := abs_add_le
    (arcContribution280 k N (majorArcs280 N) - mainTerm111 k N)
    (arcContribution280 k N (exceptionalArcs280 N η))
  have htri' := abs_add_le
    ((arcContribution280 k N (majorArcs280 N) - mainTerm111 k N) +
      arcContribution280 k N (exceptionalArcs280 N η))
    (arcContribution280 k N (goodMinorArcs280 N η))
  have heq : (representationCount111 k N : ℝ) - mainTerm111 k N =
    ((arcContribution280 k N (majorArcs280 N) - mainTerm111 k N) +
      arcContribution280 k N (exceptionalArcs280 N η)) +
      arcContribution280 k N (goodMinorArcs280 N η) := by rw [hid]; ring
  rw [heq]
  nlinarith [mul_nonneg (mul_nonneg hC.le hs) hr.le]

open LeanLab.Linnik LeanLab.DERZ1997

/-- P0093 Pages 168 and 169. Exact original GRH existence conclusion through the refined error bound. This remains CONDITIONAL on the remaining explicit inputs. -/
theorem linnik1951_refined376 : GRH → ∃ K, AllLargeEven (LinnikAtMost K) := by
  intro hG
  obtain ⟨C, η, hC, hη, hη1, he⟩ := error_bound_refined376 hG
  obtain ⟨c, hc, hm⟩ := main_lower111
  obtain ⟨k, hk, hkc⟩ := choose_exponent111 hC hc hη hη1
  obtain ⟨Ne, he⟩ := he k hk
  obtain ⟨Nm, hm⟩ := hm k hk
  refine ⟨k, max 1 (max Ne Nm), ?_⟩
  intro N hev hN
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNe : Ne < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNm : Nm < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have he' := he N hev hNe
  have hpos : 0 < (representationCount111 k N : ℝ) :=
    positive_of_error111 (scale_pos111 k N h1) hkc (hm N hev hNm) (by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using he')
  exact atMost_of_exact (representation_of_count_pos111 (by exact_mod_cast hpos))

end LeanLab.Linnik1951
