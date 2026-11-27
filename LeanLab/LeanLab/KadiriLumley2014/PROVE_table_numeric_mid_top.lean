/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 5 display 2.24, page 9 display 2.60,
page 10 Lemma 3.1 and Table 2 on page 13. ROUTE BURST S10 burst-20261124, step tablehighf.
This file proves the two MEDIUM numeric leaves endpoint_mid_numeric_S10 of step tablehighc and
endpoint_top_numeric_S10 of step tablehighb for rows 58, 59, 60 and 150, under new names with
the identical statements. Method: the higher factor F is bounded by the lab's Lemma 3.1 bound
higher_factor_bound, whose square root factor is at most q = 11/10 and whose sqrt(2m + 1) is at
least j = 11; the factor (e^u + 1) / (e^u - 1) is at most 3 / u; X^(-1/2) is at most 1 / s with
s^2 at most 2.718^n (1 - u) / (1 + delta). The remaining rational inequality is checked by
decide +kernel. Exact rational margins: the top product is about 3.2e-122 on rows 58 to 60 and
5.6e-128 on row 150; the middle product is about 3.1e-13, 1.6e-13, 9.6e-14 and 1.5e-30.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.PROVE_table_numeric_env_high

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open scoped ComplexConjugate
open Task64

/-- The higher factor of display 2.24 times (e^u + 1) / ((e^u - 1) delta^m) is at most
q (2m + 1)! / (m! j) times 3 / (u delta^m), from Lemma 3.1 on page 10. -/
theorem factor_le_S10f (m : ℕ) {δ u q j : ℝ} (hδ : 0 < δ) (hu : 0 < u) (hu2 : u ≤ 1 / 2)
    (hq : 0 ≤ q) (hQ : ((1 + δ) ^ (2 * m + 3) - 1) / (δ * (2 * m + 3)) ≤ q ^ 2)
    (hj : 0 < j) (hj2 : j ^ 2 ≤ 2 * m + 1) :
    higherFactor m δ * (Real.exp u + 1) / ((Real.exp u - 1) * δ ^ m) ≤
      q * ((2 * m + 1).factorial : ℝ) / ((m.factorial : ℝ) * j) * 3 / (u * δ ^ m) := by
  have hF := higher_factor_bound m hδ
  have hlam : lambdaHigher m δ ≤ q * ((2 * m + 1).factorial : ℝ) / ((m.factorial : ℝ) * j) := by
    unfold lambdaHigher
    have h1 : Real.sqrt (((1 + δ) ^ (2 * m + 3) - 1) / (δ * (2 * m + 3))) ≤ q :=
      (Real.sqrt_le_sqrt hQ).trans_eq (Real.sqrt_sq hq)
    have h2 : j ≤ Real.sqrt (2 * m + 1) := Real.le_sqrt_of_sq_le hj2
    apply div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)
      (mul_le_mul_of_nonneg_left h2 (by positivity))
  have he1 : Real.exp u ≤ 1 / (1 - u) :=
    Real.exp_bound_div_one_sub_of_interval hu.le (by linarith)
  have he2 : 1 / (1 - u) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hEu : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hE : (Real.exp u + 1) / ((Real.exp u - 1) * δ ^ m) ≤ 3 / (u * δ ^ m) :=
    div_le_div₀ (by norm_num) (by linarith) (by positivity)
      (mul_le_mul_of_nonneg_right hEu (by positivity))
  have hE0 : 0 ≤ (Real.exp u + 1) / ((Real.exp u - 1) * δ ^ m) := by
    have : 0 < Real.exp u - 1 := lt_of_lt_of_le hu hEu
    positivity
  have hB0 : 0 ≤ q * ((2 * m + 1).factorial : ℝ) / ((m.factorial : ℝ) * j) := by positivity
  rw [mul_div_assoc]
  calc higherFactor m δ * ((Real.exp u + 1) / ((Real.exp u - 1) * δ ^ m))
      ≤ (q * ((2 * m + 1).factorial : ℝ) / ((m.factorial : ℝ) * j)) * (3 / (u * δ ^ m)) :=
        mul_le_mul (hF.trans hlam) hE hE0 hB0
    _ = _ := by ring

/-- X^(1/2 - 1) is at most 1 / s when s^2 is at most X. -/
theorem rpow_half_le_S10f {X s : ℝ} (hs : 0 < s) (hsX : s ^ 2 ≤ X) :
    X ^ ((1 : ℝ) / 2 - 1) ≤ 1 / s := by
  have hX : 0 < X := lt_of_lt_of_le (by positivity) hsX
  rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, Real.rpow_neg hX.le, ← Real.sqrt_eq_rpow,
    one_div]
  exact inv_anti₀ hs (Real.le_sqrt_of_sq_le hsX)

/-- s^2 is at most the row endpoint X = e^n / (e^u (1 + delta)) when
s^2 (1 + delta) is at most 2.718^n (1 - u). -/
theorem sq_le_endpoint_S10f {r : PrintedRow} (hL0 : r.logIndex ≠ 0) {s : ℝ}
    (hδ0 : (0 : ℝ) ≤ r.deltaQ) (hu0 : (0 : ℝ) < r.uQ) (hu1 : (r.uQ : ℝ) < 1)
    (hsX : s ^ 2 * (1 + (r.deltaQ : ℝ)) ≤ (2718 / 1000 : ℝ) ^ r.logIndex * (1 - (r.uQ : ℝ))) :
    s ^ 2 ≤ rowEndpointX r := by
  have hXeq : rowEndpointX r =
      Real.exp (r.logIndex : ℝ) / (Real.exp (r.uQ : ℝ) * (1 + (r.deltaQ : ℝ))) := by
    unfold rowEndpointX PrintedRow.threshold
    rw [if_neg hL0]
  have hden : 0 < Real.exp (r.uQ : ℝ) * (1 + (r.deltaQ : ℝ)) := by positivity
  rw [hXeq, le_div_iff₀ hden]
  have he1 : Real.exp (r.uQ : ℝ) ≤ 1 / (1 - r.uQ) :=
    Real.exp_bound_div_one_sub_of_interval hu0.le hu1
  have he2 : (2718 / 1000 : ℝ) ^ r.logIndex ≤ Real.exp (r.logIndex : ℝ) := by
    rw [← Real.exp_one_pow]
    apply pow_le_pow_left₀ (by norm_num)
    have := Real.exp_one_gt_d9
    norm_num at this ⊢
    linarith
  have h1u : 0 < 1 - (r.uQ : ℝ) := by linarith
  have hs2 : (0 : ℝ) ≤ s ^ 2 * (1 + (r.deltaQ : ℝ)) := by positivity
  have h3 : s ^ 2 * (1 + (r.deltaQ : ℝ)) * Real.exp (r.uQ : ℝ) ≤
      s ^ 2 * (1 + (r.deltaQ : ℝ)) * (1 / (1 - r.uQ)) :=
    mul_le_mul_of_nonneg_left he1 hs2
  have h2 : s ^ 2 * (1 + (r.deltaQ : ℝ)) * (1 / (1 - r.uQ)) ≤ Real.exp (r.logIndex : ℝ) := by
    rw [mul_one_div, div_le_iff₀ h1u]
    nlinarith [mul_le_mul_of_nonneg_right he2 h1u.le]
  nlinarith

/-- Real facts about one row used by both numeric leaves. -/
theorem row_reals_S10f {r : PrintedRow} (hr : r ∈ tableTwo) :
    (0 : ℝ) < r.deltaQ ∧ (0 : ℝ) < r.uQ ∧ (r.uQ : ℝ) ≤ 1 / 2 := by
  have hs := table_small_steps r hr
  refine ⟨by exact_mod_cast hs.1, ?_, ?_⟩
  · have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  · have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    have h2 : ((0.0001 : ℚ) : ℝ) ≤ 1 / 2 := by norm_num
    linarith

/-- Per row form of the top numeric leaf, from rational facts about one row. -/
theorem top_numeric_of_row_S10f {r : PrintedRow} (hr : r ∈ tableTwo) (q j : ℚ) (hq : 0 ≤ q)
    (hj : 0 < j)
    (hQ : ((1 + r.deltaQ) ^ (2 * r.m + 3) - 1) / (r.deltaQ * (2 * r.m + 3)) ≤ q ^ 2)
    (hj2 : j ^ 2 ≤ 2 * r.m + 1)
    (hnum : q * ((2 * r.m + 1).factorial : ℚ) / ((r.m.factorial : ℚ) * j) * 3 /
        (r.uQ * r.deltaQ ^ r.m) * (1 / (3000000000000 : ℚ) ^ r.m) ≤ 1 / 100000) :
    higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) / ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        (1 / (3000000000000 : ℝ) ^ r.m) ≤ 1 / 100000 := by
  obtain ⟨hδ, hu, hu2⟩ := row_reals_S10f hr
  have hC := factor_le_S10f r.m (q := (q : ℝ)) (j := (j : ℝ)) hδ hu hu2 (by exact_mod_cast hq)
    (by exact_mod_cast hQ) (by exact_mod_cast hj) (by exact_mod_cast hj2)
  have hN : ((q : ℝ) * ((2 * r.m + 1).factorial : ℝ) / ((r.m.factorial : ℝ) * j) * 3 /
      ((r.uQ : ℝ) * (r.deltaQ : ℝ) ^ r.m) * (1 / (3000000000000 : ℝ) ^ r.m) ≤ 1 / 100000) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hnum
    push_cast at h ⊢
    linarith
  exact (mul_le_mul_of_nonneg_right hC (by positivity)).trans hN

/-- Per row form of the middle numeric leaf, from rational facts about one row. -/
theorem mid_numeric_of_row_S10f {r : PrintedRow} (hr : r ∈ tableTwo) (hL0 : r.logIndex ≠ 0)
    (q j s : ℚ) (hq : 0 ≤ q) (hj : 0 < j) (hs0 : 0 < s)
    (hQ : ((1 + r.deltaQ) ^ (2 * r.m + 3) - 1) / (r.deltaQ * (2 * r.m + 3)) ≤ q ^ 2)
    (hj2 : j ^ 2 ≤ 2 * r.m + 1)
    (hsX : s ^ 2 * (1 + r.deltaQ) ≤ (2718 / 1000) ^ r.logIndex * (1 - r.uQ))
    (hnum : q * ((2 * r.m + 1).factorial : ℚ) / ((r.m.factorial : ℚ) * j) * 3 /
        (r.uQ * r.deltaQ ^ r.m) * (1 / (30610000000 : ℚ) ^ r.m) * (1 / s) ≤ 1 / 100000) :
    higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) / ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        (1 / (30610000000 : ℝ) ^ r.m) * rowEndpointX r ^ ((1 : ℝ) / 2 - 1) ≤ 1 / 100000 := by
  obtain ⟨hδ, hu, hu2⟩ := row_reals_S10f hr
  have hC := factor_le_S10f r.m (q := (q : ℝ)) (j := (j : ℝ)) hδ hu hu2 (by exact_mod_cast hq)
    (by exact_mod_cast hQ) (by exact_mod_cast hj) (by exact_mod_cast hj2)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs0
  have hsq : (s : ℝ) ^ 2 ≤ rowEndpointX r := by
    refine sq_le_endpoint_S10f hL0 hδ.le hu (by linarith) ?_
    have h := (Rat.cast_le (K := ℝ)).mpr hsX
    push_cast at h ⊢
    linarith
  have hXs := rpow_half_le_S10f hsR hsq
  have hN : ((q : ℝ) * ((2 * r.m + 1).factorial : ℝ) / ((r.m.factorial : ℝ) * j) * 3 /
      ((r.uQ : ℝ) * (r.deltaQ : ℝ) ^ r.m) * (1 / (30610000000 : ℝ) ^ r.m) * (1 / (s : ℝ)) ≤
        1 / 100000) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hnum
    push_cast at h ⊢
    linarith
  have hC0 : 0 ≤ higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
      ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) := by
    have he : 0 < Real.exp (r.uQ : ℝ) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
    exact div_nonneg (mul_nonneg (higherFactor_nonneg_S10 r.m hδ.le) (by positivity))
      (mul_pos he (pow_pos hδ _)).le
  have hA := mul_le_mul_of_nonneg_right hC (by positivity :
    (0 : ℝ) ≤ 1 / (30610000000 : ℝ) ^ r.m)
  have hA0 : 0 ≤ higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
      ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) * (1 / (30610000000 : ℝ) ^ r.m) := by
    positivity
  have hB0 := hA0.trans hA
  exact (mul_le_mul hA hXs (Real.rpow_nonneg (by nlinarith) _) hB0).trans hN

/-- PROVED form of the MEDIUM leaf endpoint_top_numeric_S10 of step tablehighb, page 9 display
2.60 with sigma = 1 at H = 3e12, rows 58, 59, 60 and 150 of Table 2 on page 13, with the
identical statement. -/
theorem endpoint_top_numeric_S10_proved {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) / ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        (1 / (3000000000000 : ℝ) ^ r.m) ≤ 1 / 100000 := by
  have hr' := hr
  simp only [tableTwo, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at hhigh <;> try omega
  all_goals
    exact top_numeric_of_row_S10f hr' (11 / 10) 11 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- PROVED form of the MEDIUM leaf endpoint_mid_numeric_S10 of step tablehighc, rows 58, 59, 60
and 150 of Table 2 on page 13, with the identical statement. -/
theorem endpoint_mid_numeric_S10_proved {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) / ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        (1 / (30610000000 : ℝ) ^ r.m) * rowEndpointX r ^ ((1 : ℝ) / 2 - 1) ≤ 1 / 100000 := by
  have hr' := hr
  simp only [tableTwo, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at hhigh <;> try omega
  · exact mid_numeric_of_row_S10f hr' (by decide) (11 / 10) 11 (3 * 10 ^ 12)
      (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact mid_numeric_of_row_S10f hr' (by decide) (11 / 10) 11 (6 * 10 ^ 12)
      (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact mid_numeric_of_row_S10f hr' (by decide) (11 / 10) 11 (10 ^ 13)
      (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact mid_numeric_of_row_S10f hr' (by decide) (11 / 10) 11 (10 ^ 30)
      (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- Assembly: the exact statement of endpoint_mid_height_zero_sum_high_S10 with the proof of
step tablehighc repeated and its numeric leaf replaced by the proved form above. CONDITIONAL ON
the HARD leaves verified_height_three_e12_S10 and endpoint_mid_power_tail_S10. -/
theorem endpoint_mid_height_zero_sum_high_split_S10f {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000 ∧ |ρ.1.im| ≤ 3000000000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ ≤ 1 / 100000 := by
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hX : 0 < rowEndpointX r := by
    unfold rowEndpointX PrintedRow.threshold
    have hne : r.logIndex ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    positivity
  have he : 0 < Real.exp (r.uQ : ℝ) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hC : 0 ≤ higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
      ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) :=
    div_nonneg (mul_nonneg (higherFactor_nonneg_S10 r.m hδ.le) (by positivity))
      (mul_pos he (pow_pos hδ _)).le
  have hXh : 0 ≤ rowEndpointX r ^ ((1 : ℝ) / 2 - 1) := Real.rpow_nonneg hX.le _
  have hsub : s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000 ∧ |ρ.1.im| ≤ 3000000000000) =
      (s.filter (fun ρ => |ρ.1.im| ≤ 3000000000000)).filter
        (fun ρ => ¬ |ρ.1.im| ≤ 30610000000) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun ρ _ => and_comm)
  rw [hsub]
  set C := higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
      ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) with hCdef
  calc ∑ ρ ∈ (s.filter (fun ρ => |ρ.1.im| ≤ 3000000000000)).filter
          (fun ρ => ¬ |ρ.1.im| ≤ 30610000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ
      ≤ ∑ ρ ∈ (s.filter (fun ρ => |ρ.1.im| ≤ 3000000000000)).filter
          (fun ρ => ¬ |ρ.1.im| ≤ 30610000000),
          C * ((analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (r.m + 1)) *
            rowEndpointX r ^ ((1 : ℝ) / 2 - 1) := by
        refine Finset.sum_le_sum (fun ρ hρ => ?_)
        have hρ1 := Finset.mem_filter.mp hρ
        have hρ2 := (Finset.mem_filter.mp hρ1.1).2
        have hre := verified_height_three_e12_S10 ρ hρ2
        have h := zeroSummand_le_rpow_S10 r.m hδ hu hX.le ρ (by linarith [hρ1.2])
        rw [hre] at h
        exact h
    _ = C * (∑ ρ ∈ (s.filter (fun ρ => |ρ.1.im| ≤ 3000000000000)).filter
          (fun ρ => ¬ |ρ.1.im| ≤ 30610000000),
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (r.m + 1)) *
            rowEndpointX r ^ ((1 : ℝ) / 2 - 1) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ C * (1 / (30610000000 : ℝ) ^ r.m) * rowEndpointX r ^ ((1 : ℝ) / 2 - 1) := by
        gcongr
        exact endpoint_mid_power_tail_S10 hr hhigh _
    _ ≤ 1 / 100000 := endpoint_mid_numeric_S10_proved hr hhigh

/-- Assembly: the exact statement of endpoint_top_height_zero_tail_high_S10 with the proof of
step tablehighb repeated and its numeric leaf replaced by the proved form above. CONDITIONAL ON
the HARD leaf endpoint_top_power_tail_S10. -/
theorem endpoint_top_height_zero_tail_high_split_S10f {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 3000000000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ ≤ 1 / 100000 := by
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hδ1 : (r.deltaQ : ℝ) ≤ 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.1
    have h2 : ((0.0001 : ℚ) : ℝ) ≤ 1 := by norm_num
    linarith
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hu1 : (r.uQ : ℝ) ≤ 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    have h2 : ((0.0001 : ℚ) : ℝ) ≤ 1 := by norm_num
    linarith
  have hX : 1 ≤ rowEndpointX r := by
    unfold rowEndpointX PrintedRow.threshold
    have hne : r.logIndex ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    have hexpu : Real.exp (r.uQ : ℝ) ≤ 3 := by
      have := Real.exp_le_exp.mpr hu1
      have h3 := Real.exp_one_lt_d9
      linarith
    have hden : 0 < Real.exp (r.uQ : ℝ) * (1 + (r.deltaQ : ℝ)) := by positivity
    have hthr : (59 : ℝ) ≤ Real.exp (r.logIndex : ℝ) := by
      have h1 := Real.add_one_le_exp (r.logIndex : ℝ)
      have h2 : (58 : ℝ) ≤ r.logIndex := by exact_mod_cast hhigh
      linarith
    rw [le_div_iff₀ hden]
    nlinarith
  have he : 0 < Real.exp (r.uQ : ℝ) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hC : 0 ≤ higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
      ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) :=
    div_nonneg (mul_nonneg (higherFactor_nonneg_S10 r.m hδ.le) (by positivity))
      (mul_pos he (pow_pos hδ _)).le
  calc ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 3000000000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ
      ≤ ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 3000000000000),
          higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
            ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
          ((analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (r.m + 1)) := by
        refine Finset.sum_le_sum (fun ρ hρ => ?_)
        have hρ' := (Finset.mem_filter.mp hρ).2
        exact zeroSummand_le_top_S10 r.m hδ hu hX ρ (by linarith)
    _ = higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
          ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 3000000000000),
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (r.m + 1) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
          ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        (1 / (3000000000000 : ℝ) ^ r.m) :=
        mul_le_mul_of_nonneg_left (endpoint_top_power_tail_S10 hr hhigh s) hC
    _ ≤ 1 / 100000 := endpoint_top_numeric_S10_proved hr hhigh

/-- Assembly: the exact statement of table_endpoint_budget_high, with all three numeric leaves of
steps tablehighb, tablehighc and tablehighd now PROVED. CONDITIONAL ON the HARD leaves
endpoint_low_height_envelope_high_S10, verified_height_three_e12_S10,
endpoint_mid_power_tail_S10 and endpoint_top_power_tail_S10. -/
theorem table_endpoint_budget_high_numeric_closed_S10f {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)) := by
  have hL0 : 0 ≤ highRowEnvelopeBudgetS10 r.logIndex := by
    simpa using endpoint_low_height_envelope_high_S10 hr hhigh ∅
  have hZ : zeroError r.m r.deltaQ r.uQ (rowEndpointX r) ≤
      highRowEnvelopeBudgetS10 r.logIndex + 1 / 100000 + 1 / 100000 := by
    unfold zeroError
    refine tsum_le_of_sum_le' (by linarith) (fun s => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => |ρ.1.im| ≤ 30610000000)]
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000))
      (fun ρ => |ρ.1.im| ≤ 3000000000000)]
    rw [Finset.filter_filter]
    have h1 := endpoint_low_height_envelope_high_S10 hr hhigh s
    have h2 := endpoint_mid_height_zero_sum_high_split_S10f hr hhigh s
    have h3 := endpoint_top_height_zero_tail_high_split_S10f hr hhigh
      (s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000))
    linarith
  have hs := table_small_steps r hr
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hX : 0 < rowEndpointX r := by
    unfold rowEndpointX
    have := Real.exp_pos (r.uQ : ℝ)
    have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
    have hth : 0 < r.threshold := by
      unfold PrintedRow.threshold
      split_ifs
      · norm_num [evenBase]
      · exact Real.exp_pos _
    positivity
  have hE : 0 < Real.exp (r.uQ : ℝ) - 1 := by
    have := Real.add_one_lt_exp hu.ne'
    linarith
  have hP : 0 < (Real.exp r.uQ - 1) * rowEndpointX r := mul_pos hE hX
  refine (endpoint_budget_numeric_env_high_S10_proved hr hhigh).trans_le ?_
  apply mul_le_mul_of_nonneg_left _ hP.le
  linarith

#print axioms factor_le_S10f
#print axioms rpow_half_le_S10f
#print axioms sq_le_endpoint_S10f
#print axioms top_numeric_of_row_S10f
#print axioms mid_numeric_of_row_S10f
#print axioms endpoint_top_numeric_S10_proved
#print axioms endpoint_mid_numeric_S10_proved
#print axioms endpoint_mid_height_zero_sum_high_split_S10f
#print axioms endpoint_top_height_zero_tail_high_split_S10f
#print axioms table_endpoint_budget_high_numeric_closed_S10f

end LeanLab.KadiriLumley2014.Task92
