/-
KEEP GOING unit S5-07e, CLOUD S5 burst-20261127, stacked on S5-07d.
P0082 Bruedern and Perelli 1998, §7, pp. 369 to 370, displays (40) and (41), with Lemma 4.

With `leaf_s5_07d_average_multiplier` proved in place in `SPLIT_s5_S5_07d_coeff.lean`, every
LEAF made by units S5-07, S5-07b, S5-07c and S5-07d is now proved, but each one in the file
below the one that states it.  This file closes the chain without a sorry: it repeats the three
assembly proofs of `SPLIT_s5_S5_07c_fourier`, `SPLIT_s5_S5_07b_squarewave` and
`SPLIT_s5_S5_07_smoothed`, word for word, with each sorry'd leaf replaced by its proof.

The end result is `leaf_signed_smoothed_expansion_of_lemma4`: the statement of
`leaf_signed_smoothed_expansion` of `SPLIT_feed1122p2_leaf_signed_fourier_large_translate`, with
the named hypothesis `Lemma4` of P0082 p. 359 as its only premise.  So that leaf is
CONDITIONAL ON Lemma4, the cited equidistribution input, and on nothing else.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_s5_S5_07d_coeff

namespace LeanLab.ExceptionalSet.U1539

open Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

private theorem s5_07e_eC_add2 (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

private theorem s5_07e_norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have : (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- `leaf_s5_07b_fourier_hasSum`, sorry free: the proof of
`leaf_s5_07b_fourier_hasSum_of_leaves` with `leaf_s5_07c_coeff_of_leaves` for the leaf. -/
theorem s5_07e_fourier_hasSum (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4) (y : ℝ) :
    HasSum (fun h : ℤ => s5SqCoeff Δ h * eC (h / 2 * y)) (s5AvgWave Δ y) := by
  have : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩
  have hp := s5_07c_periodic Δ hΔ₀
  set f : C(AddCircle (2 : ℝ), ℂ) :=
    ⟨hp.lift, continuous_coinduced_dom.mpr (s5_07c_continuous Δ hΔ₀)⟩ with hfdef
  have hfour : ∀ (n : ℤ) (x : ℝ), fourier n (x : AddCircle (2 : ℝ)) = eC (n / 2 * x) := by
    intro n x
    rw [fourier_coe_apply]
    unfold eC
    congr 1
    push_cast
    ring
  have hfc : ∀ n : ℤ, fourierCoeff f n = s5SqCoeff Δ n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral f n 0, zero_add, ← leaf_s5_07c_coeff_of_leaves Δ hΔ₀ hΔ₁ n,
      Complex.real_smul]
    congr 1
    · norm_num
    · apply intervalIntegral.integral_congr
      intro x _
      simp only [hfdef, ContinuousMap.coe_mk, Function.Periodic.lift_coe, smul_eq_mul]
      rw [hfour]
      congr 2
      push_cast
      ring
  have hsum : Summable (fourierCoeff f) := by
    have : fourierCoeff f = s5SqCoeff Δ := funext hfc
    rw [this]; exact s5_07c_summable Δ hΔ₀
  have H := (hasSum_fourier_series_of_summable hsum).mapL
    (ContinuousMap.evalCLM ℂ ((y : ℝ) : AddCircle (2 : ℝ)))
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, hfc, smul_eq_mul] at H
  have hval : f ((y : ℝ) : AddCircle (2 : ℝ)) = s5AvgWave Δ y := by
    simp only [hfdef, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
  rw [hval] at H
  convert H using 2 with n
  rw [hfour]

/-- `leaf_s5_07_square_wave_truncation`, sorry free: the proof of
`leaf_s5_07_square_wave_truncation_of_leaves` with `s5_07e_fourier_hasSum` for the leaf. -/
theorem s5_07e_square_wave_truncation (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4)
    (H : ℤ) (hH : 1 ≤ H) :
    ∃ b : ℤ → ℂ, (∀ h : ℤ, ‖b h‖ ≤ 2 / (|(h : ℝ)| + 1)) ∧ ∀ y : ℝ,
      ‖(-1 : ℂ) ^ ⌊y⌋ - ∑ h ∈ Finset.Icc (-H) H, b h * eC (h / 2 * y)‖
          ≤ 2 + 1 / (H * Δ) ∧
        (Δ ≤ Int.fract y → Int.fract y ≤ 1 - Δ →
          ‖(-1 : ℂ) ^ ⌊y⌋ - ∑ h ∈ Finset.Icc (-H) H, b h * eC (h / 2 * y)‖
            ≤ 1 / (H * Δ)) := by
  refine ⟨s5SqCoeff Δ, s5_07b_coeff_le Δ hΔ₀, fun y => ?_⟩
  set I := Finset.Icc (-H) H with hI
  set f : ℤ → ℂ := fun h => s5SqCoeff Δ h * eC (h / 2 * y) with hf
  have hsum := s5_07e_fourier_hasSum Δ hΔ₀ hΔ₁ y
  -- the tail bound for the limit
  have htail : ‖s5AvgWave Δ y - ∑ h ∈ I, f h‖ ≤ 1 / (H * Δ) := by
    have ht : Tendsto (fun t : Finset ℤ => ∑ h ∈ t, f h) atTop (𝓝 (s5AvgWave Δ y)) := hsum
    have ht2 : Tendsto (fun t : Finset ℤ => ‖∑ h ∈ t, f h - ∑ h ∈ I, f h‖) atTop
        (𝓝 ‖s5AvgWave Δ y - ∑ h ∈ I, f h‖) := (ht.sub_const _).norm
    apply le_of_tendsto ht2
    filter_upwards [eventually_ge_atTop I] with t hIt
    rw [← Finset.sum_sdiff hIt, add_sub_cancel_right]
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ h ∈ t \ I, ‖f h‖ ≤ ‖s5SqCoeff Δ h‖ := by
      intro h _
      rw [hf]; simp only
      rw [norm_mul, s5_07e_norm_eC, mul_one]
    refine (Finset.sum_le_sum hle).trans ?_
    apply s5_07b_tail Δ hΔ₀ H hH
    intro h hh
    rw [Finset.mem_sdiff, hI, Finset.mem_Icc, not_and_or, not_le, not_le] at hh
    rcases hh.2 with h1 | h1
    · exact lt_abs.mpr (Or.inr (by omega))
    · exact lt_abs.mpr (Or.inl h1)
  have hpos : 0 ≤ 1 / (H * Δ) := by
    have : (0 : ℝ) < H := by exact_mod_cast hH
    positivity
  have hsplit : (-1 : ℂ) ^ ⌊y⌋ - ∑ h ∈ I, f h
      = ((-1 : ℂ) ^ ⌊y⌋ - s5AvgWave Δ y) + (s5AvgWave Δ y - ∑ h ∈ I, f h) := by ring
  have hw : ‖(-1 : ℂ) ^ ⌊y⌋‖ = 1 := by rw [norm_zpow, norm_neg, norm_one, one_zpow]
  refine ⟨?_, fun h1 h2 => ?_⟩
  · rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le ((-1 : ℂ) ^ ⌊y⌋) (s5AvgWave Δ y)
    have := s5_07b_avg_norm_le Δ y hΔ₀
    linarith
  · rw [← s5_07b_avg_eq_wave Δ y hΔ₀ h1 h2]
    exact htail

/-- `leaf_signed_smoothed_expansion` CONDITIONAL ON Lemma4 only: the proof of
`leaf_signed_smoothed_expansion_of_leaves` with `s5_07e_square_wave_truncation` for the leaf
and the hypothesis `hL4` for the cited `U1539.lemma4`. -/
theorem leaf_signed_smoothed_expansion_of_lemma4 (hL4 : Lemma4) (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ F γ N ^ δ →
        ∃ c : ℤ → ℝ, (∀ h : ℤ, |c h| ≤ 2 / (|(h : ℝ)| + 1)) ∧
          ‖∑ n ∈ Finset.Ioc (N / 2) N, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖
            ≤ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2 +
              ∑ h ∈ Finset.Icc (-⌊calE γ κ N⌋) ⌊calE γ κ N⌋,
                |c h| * ‖∑ n ∈ Finset.Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖ := by
  obtain ⟨κ', B, hκ', hcount⟩ := near_integer_count_of_lemma4 hL4 γ hγ₁ hγ₂
  refine ⟨κ', hκ', fun κ hκ hκle => ?_⟩
  set g : ℝ := 3 - 2 * γ with hg
  have hg0 : 0 < g := by linarith
  set T : ℝ := 20 + 24 * |B| with hT
  have hT1 : 1 ≤ T := by have := abs_nonneg B; linarith
  set A : ℝ := (6 * Real.log T / κ) ^ g⁻¹ with hA
  refine ⟨⌈Real.exp A⌉₊ + 2, fun N hN α _ => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hNA : Real.exp A ≤ (N : ℝ) := by
    have := Nat.le_ceil (Real.exp A)
    have h' : (⌈Real.exp A⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : _ ≤ N)
    linarith
  have hlogA : A ≤ Real.log N := by
    rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos _) hNA
  have hA0 : 0 ≤ A := Real.rpow_nonneg (div_nonneg (by
    have := Real.log_nonneg hT1; linarith) hκ.le) _
  set L := Real.log (N : ℝ) ^ g with hL
  have hL0 : 0 ≤ L := Real.rpow_nonneg (le_trans hA0 hlogA) _
  have hLT : 6 * Real.log T / κ ≤ L := by
    have h1 : ((6 * Real.log T / κ) ^ g⁻¹) ^ g ≤ L :=
      Real.rpow_le_rpow hA0 hlogA hg0.le
    rwa [Real.rpow_inv_rpow (div_nonneg (by have := Real.log_nonneg hT1; linarith) hκ.le)
      hg0.ne'] at h1
  have hx : 6 * Real.log T ≤ κ * L := by
    have := mul_le_mul_of_nonneg_left hLT hκ.le
    have h6 : κ * (6 * Real.log T / κ) = 6 * Real.log T := by field_simp
    linarith
  set s := Real.exp (κ * L / 6) with hs
  have hsT : T ≤ s := by
    rw [hs, ← Real.exp_log (by linarith : (0 : ℝ) < T)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hs20 : 20 ≤ s := by have := abs_nonneg B; linarith
  have hspos : 0 < s := by linarith
  have hE : calE γ κ N = s ^ 6 := by
    unfold calE; rw [hs, ← Real.exp_nat_mul]; congr 1; rw [hL]; push_cast; ring
  have hE3 : calE γ κ N ^ (-(1 / 3 : ℝ)) = (s ^ 2)⁻¹ := by
    unfold calE
    rw [← Real.exp_mul, hs, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1; rw [hL]; push_cast; ring
  have hexpB : Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) ≤ (s ^ 6)⁻¹ := by
    rw [← hE]; unfold calE; rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    rw [← hg, ← hL]
    nlinarith
  set E := calE γ κ N with hEdef
  set H : ℤ := ⌊E⌋ with hHdef
  have hEge : (20 : ℝ) ≤ E := by
    rw [hE]
    have : s ≤ s ^ 6 := by
      calc s = s ^ 1 := (pow_one s).symm
        _ ≤ s ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hH1 : 1 ≤ H := by
    rw [hHdef]; exact Int.le_floor.mpr (by push_cast; linarith)
  have hHR : E / 2 ≤ (H : ℝ) := by
    have := Int.lt_floor_add_one E
    rw [← hHdef] at this; linarith
  set Δ : ℝ := (s ^ 3)⁻¹ with hΔ
  have hs3 : (8000 : ℝ) ≤ s ^ 3 := by nlinarith
  have hΔ₀ : 0 < Δ := by positivity
  have hΔ₁ : Δ ≤ 1 / 4 := by
    rw [hΔ]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  obtain ⟨b, hb, hbw⟩ := s5_07e_square_wave_truncation Δ hΔ₀ hΔ₁ H hH1
  refine ⟨fun h => ‖b h‖, fun h => by rw [abs_of_nonneg (norm_nonneg _)]; exact hb h, ?_⟩
  simp only [abs_of_nonneg (norm_nonneg _)]
  -- the expansion
  set S := Finset.Ioc (N / 2) N with hSdef
  set I := Finset.Icc (-H) H with hIdef
  set err : ℕ → ℂ := fun n =>
    (-1 : ℂ) ^ (nu γ n) - ∑ h ∈ I, b h * eC (h / 2 * F γ n) with herr
  have hsplit : ∑ n ∈ S, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)
      = ∑ h ∈ I, b h * ∑ n ∈ S, eC ((α + h / 2) * F γ n) +
        ∑ n ∈ S, err n * eC (α * F γ n) := by
    have : ∀ n ∈ S, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)
        = ∑ h ∈ I, b h * eC ((α + h / 2) * F γ n) + err n * eC (α * F γ n) := by
      intro n _
      rw [herr]
      simp only
      have hh : ∀ h ∈ I, b h * eC ((α + h / 2) * F γ n)
          = b h * eC (h / 2 * F γ n) * eC (α * F γ n) := by
        intro h _
        rw [mul_assoc, ← s5_07e_eC_add2]; congr 2; ring
      rw [Finset.sum_congr rfl hh, ← Finset.sum_mul]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun h _ => (Finset.mul_sum _ _ _).symm)
  rw [hsplit]
  have hmain : ‖∑ h ∈ I, b h * ∑ n ∈ S, eC ((α + h / 2) * F γ n)‖
      ≤ ∑ h ∈ I, ‖b h‖ * ‖∑ n ∈ S, eC ((α + h / 2) * F γ n)‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun h _ => norm_mul _ _)
  -- the error sum
  set near := S.filter (fun n : ℕ => ¬ (Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - Δ))
    with hnear
  have herrn : ∀ n ∈ S, ‖err n * eC (α * F γ n)‖
      ≤ 1 / (H * Δ) + 2 * (if n ∈ near then 1 else 0) := by
    intro n hn
    rw [norm_mul, s5_07e_norm_eC, mul_one]
    obtain ⟨hall, hfar⟩ := hbw (F γ n)
    have hnu : nu γ n = ⌊F γ n⌋ := rfl
    simp only [herr, hnu]
    by_cases hmem : n ∈ near
    · rw [if_pos hmem]; linarith
    · rw [if_neg hmem]
      have : Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - Δ := by
        by_contra hc; exact hmem (Finset.mem_filter.mpr ⟨hn, hc⟩)
      linarith [hfar this.1 this.2]
  have hcnt : ∑ n ∈ S, (1 / (H * Δ) + 2 * (if n ∈ near then (1 : ℝ) else 0))
      = S.card * (1 / (H * Δ)) + 2 * near.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
  have herrsum : ‖∑ n ∈ S, err n * eC (α * F γ n)‖
      ≤ S.card * (1 / (H * Δ)) + 2 * near.card := by
    rw [← hcnt]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum herrn)
  have hnearc := hcount N hN2 Δ hΔ₀ hΔ₁
  have hScard : (S.card : ℝ) ≤ N := by
    have : S.card ≤ N := by
      rw [hSdef, Nat.card_Ioc]; omega
    exact_mod_cast this
  -- numerics in `s`
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hHΔ : 1 / (H * Δ) ≤ 2 * (s ^ 3)⁻¹ := by
    have hHpos : (0 : ℝ) < H := by exact_mod_cast hH1
    rw [div_le_iff₀ (by positivity)]
    have h1 : s ^ 6 / 2 ≤ (H : ℝ) := by rw [← hE]; exact hHR
    have h2 : 2 * (s ^ 3)⁻¹ * (H * Δ) = 2 * H * ((s ^ 3)⁻¹ * (s ^ 3)⁻¹) := by rw [hΔ]; ring
    rw [h2]
    have h3 : (s ^ 3)⁻¹ * (s ^ 3)⁻¹ = (s ^ 6)⁻¹ := by
      rw [← mul_inv]; congr 1; ring
    rw [h3]
    have h4 : 2 * (s ^ 6 / 2) * (s ^ 6)⁻¹ = 1 := by field_simp
    have h5 : 0 ≤ (s ^ 6)⁻¹ := by positivity
    nlinarith
  have hBpart : 2 * (B * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)))
      ≤ 2 * (|B| * N * (s ^ 6)⁻¹) := by
    have he0 : 0 ≤ Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) := (Real.exp_pos _).le
    have : B * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ))
        ≤ |B| * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self B) hN0) he0
    have h2 : |B| * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) ≤ |B| * N * (s ^ 6)⁻¹ :=
      mul_le_mul_of_nonneg_left hexpB (mul_nonneg (abs_nonneg B) hN0)
    linarith
  -- final comparison: 4 N s⁻³ + 4 |B| N s⁻⁶ ≤ N s⁻² / 2
  have hfin : (N : ℝ) * (2 * (s ^ 3)⁻¹) + 2 * (Δ * N + 2 * (|B| * N * (s ^ 6)⁻¹))
      ≤ N * (s ^ 2)⁻¹ / 2 := by
    have key := s5_07_numeric s |B| (abs_nonneg B) (by linarith)
    calc (N : ℝ) * (2 * (s ^ 3)⁻¹) + 2 * (Δ * N + 2 * (|B| * N * (s ^ 6)⁻¹))
        = N * (4 * (s ^ 3)⁻¹ + 4 * |B| * (s ^ 6)⁻¹) := by rw [hΔ]; ring
      _ ≤ N * ((s ^ 2)⁻¹ / 2) := mul_le_mul_of_nonneg_left key hN0
      _ = N * (s ^ 2)⁻¹ / 2 := by ring
  have hfull : ‖∑ n ∈ S, err n * eC (α * F γ n)‖ ≤ N * E ^ (-(1 / 3 : ℝ)) / 2 := by
    rw [hEdef, hE3]
    have hc1 : S.card * (1 / (H * Δ)) ≤ (N : ℝ) * (2 * (s ^ 3)⁻¹) := by
      apply mul_le_mul hScard hHΔ (by positivity) hN0
    have hc2 : (near.card : ℝ) ≤ Δ * N + 2 * (|B| * N * (s ^ 6)⁻¹) := by
      rw [hnear]; linarith
    linarith
  calc ‖∑ h ∈ I, b h * ∑ n ∈ S, eC ((α + h / 2) * F γ n) +
        ∑ n ∈ S, err n * eC (α * F γ n)‖
      ≤ ‖∑ h ∈ I, b h * ∑ n ∈ S, eC ((α + h / 2) * F γ n)‖ +
        ‖∑ n ∈ S, err n * eC (α * F γ n)‖ := norm_add_le _ _
    _ ≤ _ := by rw [add_comm (N * E ^ (-(1 / 3 : ℝ)) / 2)]; linarith

/-- Twin checks: the sorry free theorems have the types of the leaves they replace. -/
example : type_of% @leaf_s5_07b_fourier_hasSum := @s5_07e_fourier_hasSum
example : type_of% @leaf_s5_07_square_wave_truncation := @s5_07e_square_wave_truncation
example : Lemma4 → type_of% @leaf_signed_smoothed_expansion :=
  fun hL4 => leaf_signed_smoothed_expansion_of_lemma4 hL4

end LeanLab.ExceptionalSet.U1539
