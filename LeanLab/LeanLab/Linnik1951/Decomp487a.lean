/-
P0093 route supplies for Assembly376.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_central_kernel_mass442
import LeanLab.Linnik1951.Decomp376b

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 158 before equation 4.8. The abstract central estimate uses the proved absolute kernel mass. No character transfer or GRH is used. -/
theorem lemma2_central_proved487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
        ∀ α : ℝ, |α| ≤ 4 / (N : ℝ) →
          ‖mellinU1622 N M α‖ ≤ B * (N : ℝ) / Real.sqrt R * Real.log N ^ 3 := by
  obtain ⟨C, hC, N0, hc⟩ := central_kernel_mass442_split
  refine ⟨(1 / (2 * Real.pi)) * B0 * C, by positivity, max 1 N0, ?_⟩
  intro N hN R hR1 hR M hM α hα
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hRp : 0 < R := by linarith
  have hRN : R ≤ N := by
    calc R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hR
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
      _ = N := Real.rpow_one _
  obtain ⟨hI, hm⟩ := hc N (by omega) α hα
  have hl : 0 ≤ Real.log N ^ 3 := pow_nonneg (Real.log_nonneg hNr) 3
  calc
    _ ≤ (1 / (2 * Real.pi)) * B0 *
        (∫ t : ℝ, ‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
      mellin_kernel_domination442 N α B0 hB0.le M hM hI
    _ ≤ (1 / (2 * Real.pi)) * B0 * (C * Real.sqrt N * Real.log N ^ 3) := by
      gcongr
    _ ≤ (1 / (2 * Real.pi)) * B0 * (C * ((N : ℝ) / Real.sqrt R) * Real.log N ^ 3) := by
      gcongr
      exact sqrt_scale442 N R hNp hRp hRN
    _ = _ := by ring

/-- P0093 pages 158 and 159 before equation 4.8 and at equation 5.1. Exact central_pointwise376 statement. CONDITIONAL only on mellin_transfer1622 and its GRH hypothesis. -/
theorem central_pointwise487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ,
          |α| ≤ 4 / (N : ℝ) →
            ‖characterPrime280 χ N α‖ ^ 2 ≤
              B * (N : ℝ) ^ 2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
  obtain ⟨B0, hB0, D, hD, Nt, ht⟩ := mellin_transfer1622 hG
  obtain ⟨C, hC, Nc, hc⟩ := lemma2_central_proved487 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨2 * C ^ 2 + 2 * D ^ 2, by positivity, max 8 (max L (max Nt Nc)), ?_⟩
  intro N hN q hq hqt χ hχ α hα
  have h8 : 8 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNt : Nt < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNc : Nc < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hl : 1 ≤ Real.log N := by
    have hLR : (L : ℝ) < N := by exact_mod_cast hLN
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hLR).le
  set R := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hR
  obtain ⟨hR1, hR2⟩ := qtau_range1622 N q (by omega) hq hqt
  have hRp : 0 < R := by dsimp [R]; positivity
  have hRN : R ≤ N := by
    have := four_rpow1622 N (by omega)
    change R ≤ (N : ℝ) ^ (2 / 7 : ℝ) at hR2
    have : 0 ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by positivity
    linarith
  obtain ⟨M, hM, hm⟩ := ht N hNt q hq hqt χ hχ
  have hU := hc N hNc R hR1 hR2 M hM α hα
  have hsq : ‖mellinU1622 N M α‖ ^ 2 ≤ C ^ 2 * ((N : ℝ) ^ 2 / R * Real.log N ^ 6) := by
    calc
      _ ≤ (C * (N : ℝ) / Real.sqrt R * Real.log N ^ 3) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hU 2
      _ = _ := by
        rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hRp.le]
        ring
  have herror : (D * Real.sqrt N) ^ 2 ≤ D ^ 2 * ((N : ℝ) ^ 2 / R * Real.log N ^ 6) := by
    rw [mul_pow, Real.sq_sqrt hNr.le]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg D)
    have hn : (N : ℝ) ≤ (N : ℝ) ^ 2 / R := by
      rw [le_div_iff₀ hRp]
      nlinarith
    exact hn.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hl))
  have hh := norm_sq_le_of_near1622 (hm α)
  change _ ≤ (2 * C ^ 2 + 2 * D ^ 2) * (N : ℝ) ^ 2 / R * Real.log N ^ 6
  calc
    _ ≤ 2 * ‖mellinU1622 N M α‖ ^ 2 + 2 * (D * Real.sqrt N) ^ 2 := hh
    _ ≤ 2 * (C ^ 2 * ((N : ℝ) ^ 2 / R * Real.log N ^ 6)) +
        2 * (D ^ 2 * ((N : ℝ) ^ 2 / R * Real.log N ^ 6)) :=
      add_le_add (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (mul_le_mul_of_nonneg_left herror (by norm_num))
    _ = _ := by ring

/-- P0093 page 158 equation 4.8. Exact central integral supply with the clean Gamma kernel mass. CONDITIONAL only on mellin_transfer1622 and GRH. -/
theorem mellin_near487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in -(4 / (N : ℝ))..(4 / (N : ℝ)),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
  obtain ⟨B, hB, N0, hb⟩ := central_pointwise487 hG
  refine ⟨8 * B, by positivity, max 1 N0, ?_⟩
  intro N hN q hq hqt χ hχ
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcont : Continuous (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) :=
    (continuous_character_prime357 χ N (by omega)).norm.pow 2
  have hab : -(4 / (N : ℝ)) ≤ 4 / (N : ℝ) := by
    have : 0 ≤ 4 / (N : ℝ) := by positivity
    linarith
  calc
    _ ≤ ∫ _α in -(4 / (N : ℝ))..(4 / (N : ℝ)),
        B * (N : ℝ) ^ 2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
      apply intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
        intervalIntegrable_const
      intro α hα
      exact hb N hN0 q hq hqt χ hχ α (abs_le.mpr hα)
    _ = _ := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hd : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≠ 0 := by positivity
      field_simp [hNp.ne', hd]
      <;> ring

/-- P0093 page 158 equation 4.8 at a general radius. CONDITIONAL only on mellin_transfer1622 and GRH. The absolute Gamma kernel bound is proved. -/
theorem mellin_central_general487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ α in -(4 / (N : ℝ))..(4 / (N : ℝ)), ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / R * Real.log N ^ 6 := by
  obtain ⟨B0, hB0, B, hB, Nt, ht⟩ := mellin_transfer1622 hG
  obtain ⟨C, hC, Nc, hc⟩ := lemma2_central_proved487 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨16 * C ^ 2 + 16 * B ^ 2, by positivity, max 8 (max L (max Nt Nc)), ?_⟩
  intro N hN q hq hqt χ hχ R hR1 hR
  have h8 : 8 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have htN : Nt < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hcN : Nc < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRpos : (0 : ℝ) < R := by linarith
  have hlog : 1 ≤ Real.log N := by
    have hLNreal : (L : ℝ) < (N : ℝ) := by exact_mod_cast hLN
    have hh := Real.log_le_log (Real.exp_pos 1) (hL.trans hLNreal).le
    simpa only [Real.log_exp] using hh
  have hRN : R ≤ N := by
    have := four_rpow1622 N (by omega)
    have h0 : 0 ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by positivity
    linarith
  obtain ⟨M, hM, hA⟩ := ht N htN q hq hqt χ hχ
  have hcont : Continuous (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) :=
    (continuous_character_prime357 χ N (by omega)).norm.pow 2
  set K : ℝ := (2 * C ^ 2 + 2 * B ^ 2) * ((N : ℝ) ^ 2 / R * Real.log N ^ 6) with hK
  have hpt : ∀ α ∈ Set.Icc (-(4 / (N : ℝ))) (4 / (N : ℝ)),
      ‖characterPrime280 χ N α‖ ^ 2 ≤ K := by
    intro α hα
    have hU := hc N hcN R hR1 hR M hM α (abs_le.mpr ⟨hα.1, hα.2⟩)
    have hS := norm_sq_le_of_near1622 (hA α)
    have hs : (0 : ℝ) < Real.sqrt R := Real.sqrt_pos.mpr hRpos
    have hUsq : ‖mellinU1622 N M α‖ ^ 2 ≤ C ^ 2 * ((N : ℝ) ^ 2 / R * Real.log N ^ 6) := by
      calc ‖mellinU1622 N M α‖ ^ 2 ≤ (C * (N : ℝ) / Real.sqrt R * Real.log N ^ 3) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hU 2
        _ = _ := by
          rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hRpos.le]
          ring
    have hBsq : (B * Real.sqrt N) ^ 2 ≤ B ^ 2 * ((N : ℝ) ^ 2 / R * Real.log N ^ 6) := by
      rw [mul_pow, Real.sq_sqrt hNr.le]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : (N : ℝ) ≤ (N : ℝ) ^ 2 / R := by
        rw [le_div_iff₀ hRpos]
        nlinarith
      have h2 : 1 ≤ Real.log N ^ 6 := one_le_pow₀ hlog
      have h3 : 0 ≤ (N : ℝ) ^ 2 / R := by positivity
      nlinarith
    rw [hK]
    nlinarith
  have hle : -(4 / (N : ℝ)) ≤ 4 / (N : ℝ) := by
    have : 0 < 4 / (N : ℝ) := by positivity
    linarith
  have hint : (∫ α in -(4 / (N : ℝ))..(4 / (N : ℝ)), ‖characterPrime280 χ N α‖ ^ 2) ≤
      K * (4 / (N : ℝ) - -(4 / (N : ℝ))) := by
    calc _ ≤ ∫ _α in -(4 / (N : ℝ))..(4 / (N : ℝ)), K :=
          intervalIntegral.integral_mono_on hle (hcont.intervalIntegrable _ _)
            intervalIntegrable_const hpt
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  refine hint.trans (le_of_eq ?_)
  rw [hK]
  field_simp
  ring

end LeanLab.Linnik1951
