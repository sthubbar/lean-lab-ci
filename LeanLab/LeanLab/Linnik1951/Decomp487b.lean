/-
P0093 route supplies for Assembly376. Sealed contour data is imported before its tail proof.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Repair493ContourData
import LeanLab.Linnik1951.SPLIT_outer_tail_pointwise487

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. P0093 page 157 truncation before equation 4.4. The written exponentially small remainder is eventually at most one, uniformly over the outer alpha interval and line bounded coefficients. No frequency square estimate occurs. -/
theorem outer_tail_pointwise487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
            ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ≤ 1 := by
  exact outer_tail_pointwise487_split B0 hB0

/-- P0093 page 157 truncation before equation 4.4. The tail square mass is bounded by one after integrating the pointwise remainder. CONDITIONAL only on outer_tail_pointwise487. -/
theorem outer_tail_square487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          IntervalIntegrable (fun α : ℝ =>
            ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2)
              volume (4 / (N : ℝ)) (1 / R) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R),
            ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2) ≤ D := by
  obtain ⟨Nt, ht⟩ := outer_tail_pointwise487 B0 hB0
  refine ⟨1, by norm_num, max 8 Nt, ?_⟩
  intro N hN R hR1 hR M hM
  have h8 : 8 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := by linarith
  have hab : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNp hRp]
    have hfour := four_rpow1622 N h8
    nlinarith
  have hbound (α : ℝ) (hα : α ∈ Set.Icc (4 / (N : ℝ)) (1 / R)) :
      ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2 ≤ 1 := by
    have hh := ht N (lt_of_le_of_lt (le_max_right _ _) hN) R hR1 hR M hM α hα
    have hn := norm_nonneg (mellinU1622 N M α - truncatedMellin487 N R M α)
    nlinarith
  have hmeas : StronglyMeasurable (fun α : ℝ =>
      ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2) := by
    simpa only [Pi.pow_apply, Pi.sub_apply] using
      ((stronglyMeasurable_mellinU487 N (by omega) M hM.1).sub
        (continuous_truncatedMellin487 N (by omega) R M hM.1).stronglyMeasurable).norm.fun_pow 2
  have hInt : IntegrableOn (fun α : ℝ =>
      ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2)
      (Set.Icc (4 / (N : ℝ)) (1 / R)) := by
    change Integrable (fun α : ℝ =>
      ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2)
      (volume.restrict (Set.Icc (4 / (N : ℝ)) (1 / R)))
    refine (show IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Icc (4 / (N : ℝ)) (1 / R)) volume from continuous_const.integrableOn_Icc).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with α hα
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound α hα
  have hI := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hInt
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ _α in (4 / (N : ℝ))..(1 / R), (1 : ℝ) :=
      intervalIntegral.integral_mono_on hab hI intervalIntegrable_const hbound
    _ = 1 / R - 4 / (N : ℝ) := by simp
    _ ≤ 1 := by
      have hh : 1 / R ≤ 1 := (div_le_one hRp).mpr hR1
      have hn : 0 ≤ 4 / (N : ℝ) := by positivity
      linarith


/-- LEAF. P0093 pages 157 and 158 equations 4.4 through 4.7. The square mass of the finite signed contour is bounded by the difference and sum frequency kernels. Complex phases stay inside the t integral. This has no infinite contour or truncation error and no character or GRH. -/
theorem outer_finite_square487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          IntervalIntegrable (fun α : ℝ => ‖truncatedMellin487 N R M α‖ ^ 2)
            volume (4 / (N : ℝ)) (1 / R) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖truncatedMellin487 N R M α‖ ^ 2) ≤
            C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
  sorry

/-- P0093 pages 157 and 158 equations 4.3 through 4.7. Exact abstract_outer_kernels442 statement from the finite signed contour and its tail. CONDITIONAL only on outer_tail_square487 and outer_finite_square487. -/
theorem abstract_outer_kernels487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          IntervalIntegrable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2) volume
            (4 / (N : ℝ)) (1 / R) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
            A * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            A * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) + A := by
  obtain ⟨D, hD, Nt, ht⟩ := outer_tail_square487 B0 hB0
  obtain ⟨C, hC, Nc, hc⟩ := outer_finite_square487 B0 hB0
  obtain ⟨Ni, hi⟩ := outer_mellin_sq_integrable442 B0 hB0
  refine ⟨2 * C + 2 * D, by positivity, max 8 (max Nt (max Nc Ni)), ?_⟩
  intro N hN R hR1 hR M hM
  have h8 : 8 ≤ N := by omega
  have hNt : Nt < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNc : Nc < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNi : Ni < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := by linarith
  have hab : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNp hRp]
    have hfour := four_rpow1622 N h8
    nlinarith
  obtain ⟨hIt, htail⟩ := ht N hNt R hR1 hR M hM
  obtain ⟨hIc, hcore⟩ := hc N hNc R hR1 hR M hM
  have hI := hi N hNi R hR1 hR M hM
  refine ⟨hI, ?_⟩
  have hpoint (α : ℝ) : ‖mellinU1622 N M α‖ ^ 2 ≤
      2 * ‖truncatedMellin487 N R M α‖ ^ 2 +
      2 * ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2 :=
    norm_sq_le_of_near1622 (le_refl _)
  have hmono := intervalIntegral.integral_mono_on hab hI
    ((hIc.const_mul 2).add (hIt.const_mul 2)) (fun α _ => hpoint α)
  rw [intervalIntegral.integral_add (hIc.const_mul 2) (hIt.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  let T := (N : ℝ) / R * Real.log N ^ 3
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hd : 0 ≤ differenceKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => by positivity)
  have hs : 0 ≤ sumKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => (Real.exp_pos _).le)
  have hx : 0 ≤ Real.log N ^ 6 * differenceKernel376 T := mul_nonneg (by positivity) hd
  have hy : 0 ≤ Real.log N ^ 7 * sumKernel376 T := mul_nonneg (by positivity) hs
  change _ ≤ C * Real.log N ^ 6 * differenceKernel376 T +
    C * Real.log N ^ 7 * sumKernel376 T at hcore
  change _ ≤ (2 * C + 2 * D) * Real.log N ^ 6 * differenceKernel376 T +
    (2 * C + 2 * D) * Real.log N ^ 7 * sumKernel376 T + (2 * C + 2 * D)
  nlinarith [mul_nonneg hD.le hx, mul_nonneg hD.le hy]


/-- P0093 pages 158 and 159 equations 4.4 through 5.1. Exact outer_to_kernels376 statement. CONDITIONAL on the two signed outer leaves, mellin_transfer1622 and GRH. -/
theorem outer_to_kernels487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * Real.log N ^ 6 * differenceKernel376
                ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 3) +
              B * Real.log N ^ 7 * sumKernel376
                ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 3) + B := by
  obtain ⟨B0, hB0, D, hD, Nt, ht⟩ := mellin_transfer1622 hG
  obtain ⟨A, hA, Na, ha⟩ := abstract_outer_kernels487 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨2 * A + 2 * D ^ 2, by positivity, max 8 (max L (max Nt Na)), ?_⟩
  intro N hN q hq hqt χ hχ
  have h8 : 8 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNt : Nt < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNa : Na < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 1 ≤ Real.log N := by
    have hNrL : (L : ℝ) < N := by exact_mod_cast hLN
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hNrL).le
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set R := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hR
  obtain ⟨hR1, hR2⟩ := qtau_range1622 N q (by omega) hq hqt
  have hRp : 0 < R := by dsimp [R]; positivity
  have hRN : R ≤ N := by
    have := four_rpow1622 N (by omega)
    change R ≤ (N : ℝ) ^ (2 / 7 : ℝ) at hR2
    have : 0 ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by positivity
    linarith
  have huv : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNr hRp]
    have := four_rpow1622 N (by omega)
    change R ≤ (N : ℝ) ^ (2 / 7 : ℝ) at hR2
    linarith
  obtain ⟨M, hM, hm⟩ := ht N hNt q hq hqt χ hχ
  obtain ⟨hIU, hU⟩ := ha N hNa R hR1 hR2 M hM
  have hc := (continuous_character_prime357 χ N (by omega)).norm.pow 2
  have hmono : (∫ α in (4 / (N : ℝ))..(1 / R), ‖characterPrime280 χ N α‖ ^ 2) ≤
      ∫ α in (4 / (N : ℝ))..(1 / R),
        2 * ‖mellinU1622 N M α‖ ^ 2 + 2 * (D * Real.sqrt N) ^ 2 :=
    intervalIntegral.integral_mono_on huv (hc.intervalIntegrable _ _)
      ((hIU.const_mul 2).add intervalIntegrable_const)
      (fun α _ => norm_sq_le_of_near1622 (hm α))
  rw [intervalIntegral.integral_add (hIU.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  set T := (N : ℝ) / R * Real.log N ^ 3 with hT
  have hratio : 1 ≤ (N : ℝ) / R := (le_div_iff₀ hRp).mpr (by simpa using hRN)
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hratio (one_le_pow₀ hl)
  have hdiff := difference_kernel_lower442 T hT1
  have hdiff0 : 0 ≤ differenceKernel376 T := by linarith
  have hsum0 : 0 ≤ sumKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => (Real.exp_pos _).le)
  have hratioT : (N : ℝ) / R ≤ T := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hl)
  have herr : (1 / R - 4 / (N : ℝ)) * (2 * (D * Real.sqrt N) ^ 2) ≤
      2 * D ^ 2 * (Real.log N ^ 6 * differenceKernel376 T) := by
    have hsq : (D * Real.sqrt N) ^ 2 = D ^ 2 * (N : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hNr.le]
    rw [hsq]
    have hh : (1 / R - 4 / (N : ℝ)) * (N : ℝ) ≤ (N : ℝ) / R := by
      have : 0 ≤ 4 / (N : ℝ) := by positivity
      calc
        _ ≤ (1 / R) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hNr.le
        _ = _ := by ring
    have hc := (hratioT.trans hdiff).trans
      (le_mul_of_one_le_left hdiff0 (one_le_pow₀ hl (n := 6)))
    calc
      _ = 2 * D ^ 2 * ((1 / R - 4 / (N : ℝ)) * (N : ℝ)) := by ring
      _ ≤ 2 * D ^ 2 * ((N : ℝ) / R) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
  change _ ≤ A * Real.log N ^ 6 * differenceKernel376 T +
    A * Real.log N ^ 7 * sumKernel376 T + A at hU
  change _ ≤ (2 * A + 2 * D ^ 2) * Real.log N ^ 6 * differenceKernel376 T +
    (2 * A + 2 * D ^ 2) * Real.log N ^ 7 * sumKernel376 T + (2 * A + 2 * D ^ 2)
  have hsumterm : 0 ≤ D ^ 2 * (Real.log N ^ 7 * sumKernel376 T) :=
    mul_nonneg (sq_nonneg D)
      (mul_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log N) 7) hsum0)
  nlinarith [sq_nonneg D]

/-- P0093 page 158 equation 4.7. Exact abstract outer integral bound from the two real kernel estimates. CONDITIONAL only on the finite signed contour and its tail. -/
theorem lemma2_outer487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
        IntervalIntegrable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2) MeasureTheory.volume
          (4 / (N : ℝ)) (1 / R) ∧
        (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
          B * ((N : ℝ) / R * Real.log N ^ 3) * Real.log N ^ 7 := by
  obtain ⟨A, hA, N0, ha⟩ := abstract_outer_kernels487 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨57 * A, by positivity, max 3 (max N0 L), ?_⟩
  intro N hN R hR1 hR M hM
  have h3 : 3 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : N0 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hRp : 0 < R := by linarith
  have hl : 1 ≤ Real.log N := by
    have hLR : (L : ℝ) < N := by exact_mod_cast hLN
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hLR).le
  have hRN : R ≤ N := by
    calc R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hR
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  let V := (N : ℝ) / R
  let T := V * Real.log N ^ 3
  have hV1 : 1 ≤ V := (le_div_iff₀ hRp).mpr (by simpa using hRN)
  have hVN : V ≤ N := (div_le_iff₀ hRp).mpr (by nlinarith)
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hV1 (one_le_pow₀ hl)
  have hd := difference_kernel_le376 T hT1
  have hs := sum_kernel_le376 T hT1
  have hw := frequency_window_log376 N V (by exact_mod_cast h3.le) (by linarith) hVN
  obtain ⟨hI, hU⟩ := ha N hN0 R hR1 hR M hM
  refine ⟨hI, ?_⟩
  change _ ≤ A * Real.log N ^ 6 * differenceKernel376 T +
    A * Real.log N ^ 7 * sumKernel376 T + A at hU
  have hdiff : A * Real.log N ^ 6 * differenceKernel376 T ≤
      40 * A * V * Real.log N ^ 10 := by
    calc
      _ ≤ A * Real.log N ^ 6 * (8 * T * (5 * Real.log N)) :=
        mul_le_mul_of_nonneg_left
          (hd.trans (mul_le_mul_of_nonneg_left hw (by positivity))) (by positivity)
      _ = _ := by dsimp [T]; ring
  have hsum : A * Real.log N ^ 7 * sumKernel376 T ≤
      16 * A * V * Real.log N ^ 10 := by
    calc
      _ ≤ A * Real.log N ^ 7 * (16 * T) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by dsimp [T]; ring
  have hconst : A ≤ A * V * Real.log N ^ 10 := by
    have hh := one_le_mul_of_one_le_of_one_le hV1 (one_le_pow₀ hl (n := 10))
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hh hA.le
  have htotal : (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
      57 * A * V * Real.log N ^ 10 := by linarith
  refine htotal.trans (le_of_eq ?_)
  dsimp [V]
  ring

/-- P0093 page 158 equation 4.7. Exact positive outer integral supply from the two real kernel bounds. CONDITIONAL on the two signed outer leaves, mellin_transfer1622 and GRH. The refuted absolute mass child is not used. -/
theorem mellin_positive_far487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 10 := by
  obtain ⟨B, hB, N0, hb⟩ := outer_to_kernels487 hG
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨57 * B, by positivity, max 3 (max N0 L), ?_⟩
  intro N hN q hq hqt χ hχ
  have h3 : 3 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : N0 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 1 ≤ Real.log N := by
    have hLR : (L : ℝ) < N := by exact_mod_cast hLN
    have hh := Real.log_le_log (Real.exp_pos 1) (hL.trans hLR).le
    simpa only [Real.log_exp] using hh
  let D := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)
  let R := (N : ℝ) / D
  let T := R * Real.log N ^ 3
  have htau : 1 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le hqR htau
  have hDpos : 0 < D := by linarith
  have hDN : D ≤ N := by
    calc
      D ≤ (N : ℝ) ^ (1 / 7 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_right hqt (by positivity)
      _ = (N : ℝ) ^ (2 / 7 : ℝ) := by rw [← Real.rpow_add hNp]; congr 1; norm_num
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have hR1 : 1 ≤ R := (le_div_iff₀ hDpos).mpr (by simpa using hDN)
  have hRN : R ≤ N := (div_le_iff₀ hDpos).mpr (by
    simpa using mul_le_mul_of_nonneg_left hD1 hNp.le)
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hR1 (one_le_pow₀ hlog)
  have hdiff := difference_kernel_le376 T hT1
  have hsum := sum_kernel_le376 T hT1
  have hwindow := frequency_window_log376 N R (by exact_mod_cast h3.le) (by linarith) hRN
  have hsmall : 1 ≤ R * Real.log N ^ 10 := one_le_mul_of_one_le_of_one_le hR1 (one_le_pow₀ hlog)
  have h := hb N hN0 q hq hqt χ hχ
  change _ ≤ B * Real.log N ^ 6 * differenceKernel376 T +
    B * Real.log N ^ 7 * sumKernel376 T + B at h
  have hd : B * Real.log N ^ 6 * differenceKernel376 T ≤
      40 * B * R * Real.log N ^ 10 := by
    calc
      _ ≤ B * Real.log N ^ 6 * (8 * T * (5 * Real.log N)) :=
        mul_le_mul_of_nonneg_left
          (hdiff.trans (mul_le_mul_of_nonneg_left hwindow (by positivity))) (by positivity)
      _ = _ := by dsimp [T]; ring
  have hs : B * Real.log N ^ 7 * sumKernel376 T ≤
      16 * B * R * Real.log N ^ 10 := by
    calc
      _ ≤ B * Real.log N ^ 7 * (16 * T) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by dsimp [T]; ring
  have hconst : B ≤ B * R * Real.log N ^ 10 := by
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hsmall hB.le
  calc
    _ ≤ 57 * B * R * Real.log N ^ 10 := by linarith
    _ = _ := by dsimp [R, D]; ring

/-- P0093 page 158 equation 4.7 at a general radius. CONDITIONAL on the signed abstract outer kernels, the character transfer and GRH. -/
theorem mellin_outer_general487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / R * Real.log N ^ 10 := by
  obtain ⟨B0, hB0, B, hB, Nt, ht⟩ := mellin_transfer1622 hG
  obtain ⟨C, hC, Nc, hc⟩ := lemma2_outer487 B0 hB0
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

/-- P0093 page 158 final sentence at a general radius. Reflection gives the negative interval. CONDITIONAL on the signed abstract outer kernels, the character transfer and GRH. -/
theorem mellin_outer_negative487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ α in -(1 / R)..-(4 / (N : ℝ)), ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / R * Real.log N ^ 10 := by
  obtain ⟨B, hB, N0, hpos⟩ := mellin_outer_general487 hG
  refine ⟨B, hB, N0, ?_⟩
  intro N hN q hq hqt χ hχ R hR1 hR
  have hstar : star χ ≠ 1 := by
    intro h
    apply hχ
    simpa only [star_star, star_one] using congrArg star h
  rw [← intervalIntegral.integral_comp_neg]
  simp_rw [character_norm_reflect357]
  exact hpos N hN q hq hqt (star χ) hstar R hR1 hR

/-- P0093 page 159 equation 5.2 at a general radius. CONDITIONAL on mellin_transfer1622, the finite signed contour and its tail, and GRH. No absolute outer mass estimate is used. -/
theorem mellin_radius487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ α in -(1 / R)..(1 / R), ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / R * Real.log N ^ 13 := by
  obtain ⟨B0, hB0, N0, h0⟩ := mellin_central_general487 hG
  obtain ⟨Bp, hBp, Np, hp⟩ := mellin_outer_general487 hG
  obtain ⟨Bm, hBm, Nm, hm⟩ := mellin_outer_negative487 hG
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


end LeanLab.Linnik1951
