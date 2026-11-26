/-
P0093 pages 156 through 159. Existing square estimates moved upstream.
All statements and proofs are preserved.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_lemma2_outer_square519

namespace LeanLab.Linnik1951.Task519
open MeasureTheory Filter Finset

/-- TWIN of lemma2_positive_square519 in Decomp519a, same statement, proof copied with the split calls.
P0093 page 158 equations 4.7 and 4.8. The full positive half interval
is assembled from the clean central part and the signed outer estimate.
CONDITIONAL ON lemma2_outer_square519_split. -/
theorem lemma2_positive_square519_w1121 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2) (Set.Icc 0 (1 / R)) ∧
          (∫ α in 0..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 13) := by
  obtain ⟨Cc, hCc, Nc, hc⟩ := central_square_mass519 B0 hB0
  obtain ⟨Co, hCo, No, ho⟩ := lemma2_outer_square519_split B0 hB0
  have hscale : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ (5 / 7 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 7)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  have hlogs : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨Ns, hs⟩ := eventually_atTop.mp hscale
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp hlogs
  refine ⟨Cc + Co, by positivity, max 3 (max Nc (max No (max Ns Nl))), ?_⟩
  intro N hN R hR hRN M hM
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hRp : 0 < R := by linarith
  have hlog : 1 ≤ Real.log N := hl N (by omega)
  have hlog0 : 0 ≤ Real.log N := by linarith
  have h4R : 4 * R ≤ N := by
    calc _ ≤ 4 * (N : ℝ) ^ (2 / 7 : ℝ) := mul_le_mul_of_nonneg_left hRN (by norm_num)
      _ ≤ (N : ℝ) ^ (5 / 7 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_right (hs N (by omega)) (by positivity)
      _ = N := by rw [← Real.rpow_add hNp]; norm_num
  have hδr : 4 / (N : ℝ) ≤ 1 / R :=
    (div_le_div_iff₀ hNp hRp).mpr (by simpa only [one_mul] using h4R)
  obtain ⟨hiC, hbC⟩ := hc N (by omega) M hM
  obtain ⟨hiO, hbO⟩ := ho N (by omega) R hR hRN M hM
  have hiCI := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by positivity : (0 : ℝ) ≤ 4 / (N : ℝ))).mpr hiC
  have hiOI := (intervalIntegrable_iff_integrableOn_Icc_of_le hδr).mpr hiO
  have hiP := hiCI.trans hiOI
  have hRleN : R ≤ N := by
    calc R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hRN
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have hNR : 1 ≤ (N : ℝ) / R := (le_div_iff₀ hRp).mpr (by simpa using hRleN)
  have hlogscale : Real.log N ^ 13 ≤ (N : ℝ) / R * Real.log N ^ 13 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hNR (pow_nonneg hlog0 13)
  have hcu : (∫ α in 0..(4 / (N : ℝ)), ‖mellinU519 N M α‖ ^ 2) ≤
      Cc * ((N : ℝ) / R * Real.log N ^ 13) :=
    hbC.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hlog (by omega : 6 ≤ 13)) hCc.le).trans
        (mul_le_mul_of_nonneg_left hlogscale hCc.le))
  have hou : (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
      Co * ((N : ℝ) / R * Real.log N ^ 13) := by
    apply hbO.trans
    gcongr
    norm_num
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le
    (by positivity : (0 : ℝ) ≤ 1 / R)).mp hiP, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hiCI hiOI]
  calc _ ≤ Cc * ((N : ℝ) / R * Real.log N ^ 13) +
      Co * ((N : ℝ) / R * Real.log N ^ 13) := add_le_add hcu hou
    _ = _ := by ring

/-- TWIN of lemma2_square519 in Decomp519a, same statement, proof copied with the split calls.
P0093 pages 156 through 158 Lemma 2 equations 4.1 through 4.8.
The diagonal square estimate is assembled from the clean central interval,
the signed outer estimate and the proved conjugate reflection.
CONDITIONAL ON lemma2_outer_square519_split. No GRH or prime occurs here. -/
theorem lemma2_square519_w1121 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2) (Set.Icc (-(1 / R)) (1 / R)) ∧
          (∫ α in -(1 / R)..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 13) := by
  obtain ⟨C, hC, Np, hp⟩ := lemma2_positive_square519_w1121 B0 hB0
  refine ⟨2 * C, by positivity, max 1 Np, ?_⟩
  intro N hN R hR hRN M hM
  have hN1 : 1 ≤ N := by omega
  have hr0 : (0 : ℝ) ≤ 1 / R := by positivity
  obtain ⟨hiP, hbP⟩ := hp N (by omega) R hR hRN M hM
  have hMref := reflected_line_bound519 N B0 M hM.1 hM.2
  obtain ⟨hiQ, hbQ⟩ := hp N (by omega) R hR hRN
    (fun t => (starRingEnd ℂ) (M (-t))) hMref
  have hiN : IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      (Set.Icc (-(1 / R)) 0) := by
    simpa only [Set.neg_Icc, neg_zero, mellin_reflection519 N hN1 M,
      Complex.norm_conj, neg_neg] using hiQ.comp_neg
  have hiPI := (intervalIntegrable_iff_integrableOn_Icc_of_le hr0).mpr hiP
  have hiNI := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (neg_nonpos.mpr hr0)).mpr hiN
  have hiFull := hiNI.trans hiPI
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le
    (show -(1 / R) ≤ 1 / R by linarith)).mp hiFull, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hiNI hiPI,
    mellin_negative_square519 N hN1 M (1 / R)]
  calc _ ≤ C * ((N : ℝ) / R * Real.log N ^ 13) +
      C * ((N : ℝ) / R * Real.log N ^ 13) := add_le_add hbQ hbP
    _ = _ := by ring

/-- TWIN of nonprincipal_mass519 in Decomp519a, same statement plus hT, proof copied with the twin calls.
P0093 page 159 equation 5.2. The corrected Mellin transfer and the
abstract square estimate imply the nonprincipal character square estimate.
CONDITIONAL ON the transfer hypothesis hT, the statement of grh_mellin_transfer519,
and on lemma2_square519_w1121. -/
theorem nonprincipal_mass519_b1122 (hG : LeanLab.DERZ1997.GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
            (∫ α in -(1 / R)..(1 / R), ‖characterPrime519 χ N α‖ ^ 2) ≤
              C * ((N : ℝ) / R * Real.log N ^ 13) := by
  obtain ⟨B0, hB0, B, hB, Nt, ht⟩ := hT
  obtain ⟨C, hC, Nm, hm⟩ := lemma2_square519_w1121 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨2 * C + 4 * B ^ 2, by positivity, max 1 (max L (max Nt Nm)), ?_⟩
  intro N hN q hq hqN χ hχ R hR hRN
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := by linarith
  have hNt : Nt < N := by omega
  have hNm : Nm < N := by omega
  have hLN : (L : ℝ) < N := by exact_mod_cast (show L < N by omega)
  have hlog : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hLN).le
  have hlog13 : 1 ≤ Real.log N ^ 13 := one_le_pow₀ hlog
  obtain ⟨M, hM, hrem⟩ := ht N hNt q hq hqN χ hχ
  obtain ⟨hiM, hmass⟩ := hm N hNm R hR hRN M hM
  have hc := (continuous_character_prime519 χ N hN1).norm.pow 2
  have hle : ∀ α : ℝ, ‖characterPrime519 χ N α‖ ^ 2 ≤
      2 * ‖mellinU519 N M α‖ ^ 2 + 2 * B ^ 2 * N := by
    intro α
    have htri : ‖characterPrime519 χ N α‖ ≤
        ‖mellinU519 N M α‖ + B * Real.sqrt N := by
      have := norm_add_le (mellinU519 N M α)
        (characterPrime519 χ N α - mellinU519 N M α)
      have he : mellinU519 N M α +
          (characterPrime519 χ N α - mellinU519 N M α) = characterPrime519 χ N α := by ring
      rw [he] at this
      exact this.trans (add_le_add le_rfl (hrem α))
    nlinarith [sq_nonneg (‖mellinU519 N M α‖ - B * Real.sqrt N),
      Real.sq_sqrt hNp.le, norm_nonneg (characterPrime519 χ N α),
      norm_nonneg (mellinU519 N M α), Real.sqrt_nonneg (N : ℝ)]
  have hiMi : IntervalIntegrable (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      volume (-(1 / R)) (1 / R) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [one_div_nonneg.mpr hRp.le] : -(1 / R) ≤ (1 / R))).mpr
    exact hiM
  have hh := intervalIntegral.integral_mono_on (by linarith [one_div_nonneg.mpr hRp.le] : -(1 / R) ≤ (1 / R))
    (hc.intervalIntegrable _ _)
    ((hiMi.const_mul 2).add (intervalIntegrable_const (a := -(1 / R)) (b := 1 / R)))
    (fun α _ => hle α)
  rw [intervalIntegral.integral_add (hiMi.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hh
  calc
    _ ≤ 2 * (∫ α in -(1 / R)..(1 / R), ‖mellinU519 N M α‖ ^ 2) +
        (1 / R - -(1 / R)) * (2 * B ^ 2 * N) := hh
    _ ≤ 2 * (C * ((N : ℝ) / R * Real.log N ^ 13)) +
        (1 / R - -(1 / R)) * (2 * B ^ 2 * N) := by gcongr
    _ ≤ (2 * C + 4 * B ^ 2) * ((N : ℝ) / R * Real.log N ^ 13) := by
      have he : (1 / R - -(1 / R)) * (2 * B ^ 2 * N) =
          4 * B ^ 2 * ((N : ℝ) / R) := by ring
      rw [he]
      have := mul_le_mul_of_nonneg_left hlog13
        (show 0 ≤ 4 * B ^ 2 * ((N : ℝ) / R) by positivity)
      nlinarith


end LeanLab.Linnik1951.Task519
