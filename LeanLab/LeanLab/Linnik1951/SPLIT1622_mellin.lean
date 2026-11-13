/-
Unit U-1622. Source faithful re-cut of the Mellin square bounds of P0093.
Replaces the dead pointwise splits in SPLIT_mellin_near357 and SPLIT_mellin_positive_far357.
The original scan of pages 156 to 159 controls the statements.
AI wrote the Lean code. Binary Goldbach is open.

Lemma 2 of page 156 is abstract. Its two steps carry no GRH and no primes.
The transfer leaf is the only place GRH enters. The assembly proves the exact types
of mellin_near357, mellin_positive_far357 and MellinBound280, and the same bound at
any radius 1 over R, which section 9 needs at radius 2 over q tau.
-/
import LeanLab.Linnik1951.Repair493MellinData
import LeanLab.Linnik1951.SPLIT_central_kernel_mass442

namespace LeanLab.Linnik1951

/-- LEAF. P0093 page 159 before equation 5.1, with the zero free half plane under
GRH and ln L of order ln cubed on the line. For a nonprincipal character, A_chi
equals the Mellin integral of ln L up to the prime power sum. That sum is pointwise
at most B times the square root of N. It is not displayed on page 159, see the
FINDING in PROGRESS. No integral over alpha occurs. -/
theorem mellin_transfer1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, LineBound1622 N B0 M ∧ ∀ α : ℝ,
            ‖characterPrime280 χ N α - mellinU1622 N M α‖ ≤ B * Real.sqrt N := by
  sorry

/-- LEAF. P0093 page 158 display before equation 4.8, on the central interval
only. For any coefficient with the line bound, U is at most B times N over the
square root of R times ln cubed N when |alpha| is at most 4 over N. Here R stands
for q tau. No GRH, no primes. -/
theorem lemma2_central1622 (B0 : ℝ) (hB0 : 0 < B0) :
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

/-- LEAF. P0093 page 158 equations 4.4 to 4.7. For any coefficient with the line
bound, the square integral of U from 4 over N to 1 over R is at most B times N_0
times ln to the seventh, where N_0 is N over R times ln cubed N. U is square
integrable there. Here R stands for q tau. No GRH, no primes. -/
theorem lemma2_outer1622 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
        IntervalIntegrable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2) MeasureTheory.volume
          (4 / (N : ℝ)) (1 / R) ∧
        (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
          B * ((N : ℝ) / R * Real.log N ^ 3) * Real.log N ^ 7 := by
  sorry

/-- For N at least 8 the power 4 times N to the two sevenths is at most N. -/
theorem four_rpow1622 (N : ℕ) (hN : 8 ≤ N) : 4 * (N : ℝ) ^ (2 / 7 : ℝ) ≤ N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h8R : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h5 : (4 : ℝ) ≤ (N : ℝ) ^ (5 / 7 : ℝ) := by
    have hpow : (4 : ℝ) ^ 7 ≤ (N : ℝ) ^ 5 := by
      have h1 : (8 : ℝ) ^ 5 ≤ (N : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) h8R 5
      norm_num at h1 ⊢
      linarith
    have hle := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ 7) hpow
      (by norm_num : (0 : ℝ) ≤ 1 / 7)
    have h4 : ((4 : ℝ) ^ ((7 : ℕ) : ℝ)) ^ (1 / 7 : ℝ) = 4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show (((7 : ℕ) : ℝ)) * (1 / 7 : ℝ) = 1 by norm_num, Real.rpow_one]
    have hN5 : ((N : ℝ) ^ ((5 : ℕ) : ℝ)) ^ (1 / 7 : ℝ) = (N : ℝ) ^ (5 / 7 : ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hNpos)]
      norm_num
    rwa [← Real.rpow_natCast (4 : ℝ) 7, ← Real.rpow_natCast (N : ℝ) 5, h4, hN5] at hle
  have he : (N : ℝ) ^ (5 / 7 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) = (N : ℝ) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hm : (4 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) ^ (5 / 7 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) :=
    mul_le_mul_of_nonneg_right h5 (Real.rpow_pos_of_pos hNpos _).le
  linarith

/-- If x is within b of u, then the square of x is at most twice the square of u
plus twice the square of b. -/
theorem norm_sq_le_of_near1622 {x u : ℂ} {b : ℝ} (h : ‖x - u‖ ≤ b) :
    ‖x‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * b ^ 2 := by
  have h1 : ‖x‖ ≤ ‖u‖ + ‖x - u‖ := by
    calc ‖x‖ = ‖u + (x - u)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have h0 := norm_nonneg (x - u)
  have h2 : ‖x‖ ≤ ‖u‖ + b := by linarith
  have h3 : ‖x‖ ^ 2 ≤ (‖u‖ + b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith [sq_nonneg (‖u‖ - b)]

/-- P0093 page 158 equation 4.8 at general R. CONDITIONAL on mellin_transfer1622
and lemma2_central1622. -/
theorem mellin_central_general1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ α in -(4 / (N : ℝ))..(4 / (N : ℝ)), ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / R * Real.log N ^ 6 := by
  obtain ⟨B0, hB0, B, hB, Nt, ht⟩ := mellin_transfer1622 hG
  obtain ⟨C, hC, Nc, hc⟩ := lemma2_central1622 B0 hB0
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

/-- P0093 page 158 equation 4.7 at general R. CONDITIONAL on mellin_transfer1622
and lemma2_outer1622. -/
theorem mellin_outer_general1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / R * Real.log N ^ 10 := by
  obtain ⟨B0, hB0, B, hB, Nt, ht⟩ := mellin_transfer1622 hG
  obtain ⟨C, hC, Nc, hc⟩ := lemma2_outer1622 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨2 * C + 2 * B ^ 2, by positivity, max 8 (max L (max Nt Nc)), ?_⟩
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
  have huv : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNr hRpos]
    have := four_rpow1622 N (by omega)
    nlinarith
  obtain ⟨M, hM, hA⟩ := ht N htN q hq hqt χ hχ
  obtain ⟨hIU, hU⟩ := hc N hcN R hR1 hR M hM
  have hcont : Continuous (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) :=
    (continuous_character_prime357 χ N (by omega)).norm.pow 2
  have hmono : (∫ α in (4 / (N : ℝ))..(1 / R), ‖characterPrime280 χ N α‖ ^ 2) ≤
      ∫ α in (4 / (N : ℝ))..(1 / R),
        (2 * ‖mellinU1622 N M α‖ ^ 2 + 2 * (B * Real.sqrt N) ^ 2) :=
    intervalIntegral.integral_mono_on huv (hcont.intervalIntegrable _ _)
      ((hIU.const_mul 2).add intervalIntegrable_const)
      (fun α _ => norm_sq_le_of_near1622 (hA α))
  have hsplit : (∫ α in (4 / (N : ℝ))..(1 / R),
      (2 * ‖mellinU1622 N M α‖ ^ 2 + 2 * (B * Real.sqrt N) ^ 2)) =
      2 * (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) +
        2 * (B * Real.sqrt N) ^ 2 * (1 / R - 4 / (N : ℝ)) := by
    rw [intervalIntegral.integral_add (hIU.const_mul 2) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hsq : (B * Real.sqrt N) ^ 2 = B ^ 2 * (N : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hNr.le]
  have hNR : 0 ≤ (N : ℝ) / R := by positivity
  have hlen : (N : ℝ) * (1 / R - 4 / (N : ℝ)) ≤ (N : ℝ) / R := by
    have : 0 ≤ 4 / (N : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left (show 1 / R - 4 / (N : ℝ) ≤ 1 / R by linarith) hNr.le
    calc _ ≤ (N : ℝ) * (1 / R) := h
      _ = _ := by ring
  have h10 : 1 ≤ Real.log N ^ 10 := one_le_pow₀ hlog
  have hU' : B * 0 + C * ((N : ℝ) / R * Real.log N ^ 3) * Real.log N ^ 7 =
      C * ((N : ℝ) / R) * Real.log N ^ 10 := by ring
  rw [hsplit, hsq] at hmono
  have hA2 : 2 * B ^ 2 * (N : ℝ) * (1 / R - 4 / (N : ℝ)) ≤
      2 * B ^ 2 * ((N : ℝ) / R) * Real.log N ^ 10 := by
    have hb : 0 ≤ 2 * B ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hlen hb
    have h2 : (N : ℝ) / R ≤ (N : ℝ) / R * Real.log N ^ 10 := le_mul_of_one_le_right hNR h10
    have h3 := mul_le_mul_of_nonneg_left h2 hb
    nlinarith
  have hend : (2 * C + 2 * B ^ 2) * (N : ℝ) / R * Real.log N ^ 10 =
      2 * (C * ((N : ℝ) / R) * Real.log N ^ 10) + 2 * B ^ 2 * ((N : ℝ) / R) * Real.log N ^ 10 := by
    ring
  rw [hend]
  have hU2 : (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
      C * ((N : ℝ) / R) * Real.log N ^ 10 := by
    refine hU.trans (le_of_eq ?_)
    ring
  linarith

/-- The negative outer interval by conjugate reflection. CONDITIONAL as
mellin_outer_general1622. P0093 page 158 last sentence. -/
theorem mellin_outer_negative1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ α in -(1 / R)..-(4 / (N : ℝ)), ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / R * Real.log N ^ 10 := by
  obtain ⟨B, hB, N0, hpos⟩ := mellin_outer_general1622 hG
  refine ⟨B, hB, N0, ?_⟩
  intro N hN q hq hqt χ hχ R hR1 hR
  have hstar : star χ ≠ 1 := by
    intro h
    apply hχ
    simpa only [star_star, star_one] using congrArg star h
  rw [← intervalIntegral.integral_comp_neg]
  simp_rw [character_norm_reflect357]
  exact hpos N hN q hq hqt (star χ) hstar R hR1 hR

/-- P0093 page 159 equation 5.2 at radius 1 over R. Page 155 lets tau be any
function of N in its range, and page 166 says the doubled arcs need only a trivial
modification. CONDITIONAL on the three leaves of this file. -/
theorem mellin_radius1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ α in -(1 / R)..(1 / R), ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / R * Real.log N ^ 13 := by
  obtain ⟨B0, hB0, N0, h0⟩ := mellin_central_general1622 hG
  obtain ⟨Bp, hBp, Np, hp⟩ := mellin_outer_general1622 hG
  obtain ⟨Bm, hBm, Nm, hm⟩ := mellin_outer_negative1622 hG
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨Bm + B0 + Bp, by positivity, max 1 (max L (max N0 (max Np Nm))), ?_⟩
  intro N hN q hq hqt χ hχ R hR1 hR
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
  have hRpos : (0 : ℝ) < R := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h6 : Real.log N ^ 6 ≤ Real.log N ^ 13 :=
    pow_le_pow_right₀ hlog (by norm_num)
  have h10 : Real.log N ^ 10 ≤ Real.log N ^ 13 :=
    pow_le_pow_right₀ hlog (by norm_num)
  have hcont : Continuous (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) :=
    (continuous_character_prime357 χ N (by omega)).norm.pow 2
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable (-(1 / R)) (-(4 / (N : ℝ))))
    (hcont.intervalIntegrable (-(4 / (N : ℝ))) (4 / (N : ℝ)))
  have hadd' := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable (-(1 / R)) (4 / (N : ℝ)))
    (hcont.intervalIntegrable (4 / (N : ℝ)) (1 / R))
  rw [← hadd', ← hadd]
  have b0 := (h0 N h0N q hq hqt χ hχ R hR1 hR).trans
    (mul_le_mul_of_nonneg_left h6 (by positivity))
  have bp := (hp N hpN q hq hqt χ hχ R hR1 hR).trans
    (mul_le_mul_of_nonneg_left h10 (by positivity))
  have bm := (hm N hmN q hq hqt χ hχ R hR1 hR).trans
    (mul_le_mul_of_nonneg_left h10 (by positivity))
  calc
    _ ≤ Bm * N / R * Real.log N ^ 13 + B0 * N / R * Real.log N ^ 13 +
        Bp * N / R * Real.log N ^ 13 := add_le_add (add_le_add bm b0) bp
    _ = _ := by ring

/-- q tau with q at most tau is at most N to the two sevenths, and at least 1. -/
theorem qtau_range1622 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hqt : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) :
    1 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ∧
      (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hτ : 1 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := Real.one_le_rpow hNr (by norm_num)
  constructor
  · nlinarith
  · have h2 : (N : ℝ) ^ (1 / 7 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) = (N : ℝ) ^ (2 / 7 : ℝ) := by
      rw [← Real.rpow_add hNp]
      norm_num
    nlinarith

/-- P0093 page 158 equation 4.8. Exact mellin_near357 statement.
CONDITIONAL on mellin_transfer1622 and lemma2_central1622. -/
theorem mellin_near_recut1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in -(4 / (N : ℝ))..(4 / (N : ℝ)),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
  obtain ⟨B, hB, N0, h⟩ := mellin_central_general1622 hG
  refine ⟨B, hB, max 1 N0, ?_⟩
  intro N hN q hq hqt χ hχ
  have h1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  obtain ⟨hR1, hR⟩ := qtau_range1622 N q h1 hq hqt
  exact h N (lt_of_le_of_lt (le_max_right _ _) hN) q hq hqt χ hχ _ hR1 hR

/-- P0093 page 158 equation 4.7 and the substitution for N_0. Exact
mellin_positive_far357 statement. CONDITIONAL on mellin_transfer1622 and
lemma2_outer1622. -/
theorem mellin_positive_far_recut1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 10 := by
  obtain ⟨B, hB, N0, h⟩ := mellin_outer_general1622 hG
  refine ⟨B, hB, max 1 N0, ?_⟩
  intro N hN q hq hqt χ hχ
  have h1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  obtain ⟨hR1, hR⟩ := qtau_range1622 N q h1 hq hqt
  exact h N (lt_of_le_of_lt (le_max_right _ _) hN) q hq hqt χ hχ _ hR1 hR

/-- P0093 page 159 equation 5.2. Exact MellinBound280. CONDITIONAL on the three
leaves of this file. -/
theorem mellin_bound_recut1622 (hG : LeanLab.DERZ1997.GRH) : MellinBound280 := by
  obtain ⟨B, hB, N0, h⟩ := mellin_radius1622 hG
  refine ⟨B, hB, max 1 N0, ?_⟩
  intro N hN q hq hqt χ hχ
  have h1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  obtain ⟨hR1, hR⟩ := qtau_range1622 N q h1 hq hqt
  exact h N (lt_of_le_of_lt (le_max_right _ _) hN) q hq hqt χ hχ _ hR1 hR

end LeanLab.Linnik1951
