/-
P0093 pages 157 and 158. Abstract outer Mellin kernel estimate and transfer.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT1622_mellin
import LeanLab.Linnik1951.Decomp376f

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. P0093 page 158 equations 4.4 through 4.6. After truncating
the contour, the two frequency sign regions give the difference and
sum kernels. This retains only the abstract Mellin integral U.
There is no character, prime series or GRH. The constant term absorbs
the exponentially small contour remainder on page 157 equation 4.3. -/
theorem abstract_outer_kernels442 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          IntervalIntegrable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2) volume
            (4 / (N : ℝ)) (1 / R) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
            A * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            A * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) + A := by
  sorry

/-- LEAF. P0093 page 158 reciprocal difference kernel after equation
4.6. Its integral on the square box is at least T when T is at least
one. This lower bound absorbs the prime power transfer error only. -/
theorem difference_kernel_lower442 (T : ℝ) (hT : 1 ≤ T) :
    T ≤ differenceKernel376 T := by
  have hTp : 0 < T := by linarith
  have hc : Continuous (fun t : ℝ => ∫ u in -T..T, 1 / (1 + |t - u|)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_const.div
        (continuous_const.add ((continuous_fst.sub continuous_snd).abs))
        (fun x : ℝ × ℝ => ne_of_gt (show (0 : ℝ) < 1 + |x.1 - x.2| by positivity))) (-T) T
  have hinner (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      (2 * T) / (1 + 2 * T) ≤ ∫ u in -T..T, 1 / (1 + |t - u|) := by
    have hh : (∫ _u in -T..T, (1 : ℝ) / (1 + 2 * T)) ≤
        ∫ u in -T..T, 1 / (1 + |t - u|) := by
      apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        ((show Continuous (fun u : ℝ => 1 / (1 + |t - u|)) by
          exact continuous_const.div
            (continuous_const.add ((continuous_const.sub continuous_id).abs))
            (fun u => ne_of_gt (by positivity))).intervalIntegrable _ _)
      intro u hu
      have hab : |t - u| ≤ 2 * T := abs_le.mpr ⟨by linarith [ht.1, hu.2], by linarith [ht.2, hu.1]⟩
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have he : (∫ _u in -T..T, (1 : ℝ) / (1 + 2 * T)) =
        (2 * T) / (1 + 2 * T) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rwa [he] at hh
  have hout : (∫ _t in -T..T, (2 * T) / (1 + 2 * T)) ≤ differenceKernel376 T := by
    exact intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hc.intervalIntegrable _ _) hinner
  have hcalc : (∫ _t in -T..T, (2 * T) / (1 + 2 * T)) =
      4 * T ^ 2 / (1 + 2 * T) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hcalc] at hout
  apply le_trans _ hout
  apply (le_div_iff₀ (by positivity : 0 < 1 + 2 * T)).mpr
  nlinarith

/-- P0093 pages 158 and 159 equations 4.4 through 5.1. Exact
outer_to_kernels376 statement. CONDITIONAL on abstract_outer_kernels442
and the existing Mellin transfer. The transfer error is absorbed by
the proved lower bound for the nonnegative difference kernel. -/
theorem outer_to_kernels_decomposed442 (hG : LeanLab.DERZ1997.GRH) :
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
  obtain ⟨A, hA, Na, ha⟩ := abstract_outer_kernels442 B0 hB0
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

/-- P0093 page 158 equation 4.7. Exact lemma2_outer1622 statement
from the abstract contour leaf and the two proved real kernel bounds.
CONDITIONAL only on abstract_outer_kernels442. No prime transfer is used. -/
theorem lemma2_outer_decomposed442 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
        IntervalIntegrable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2) MeasureTheory.volume
          (4 / (N : ℝ)) (1 / R) ∧
        (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
          B * ((N : ℝ) / R * Real.log N ^ 3) * Real.log N ^ 7 := by
  obtain ⟨A, hA, N0, ha⟩ := abstract_outer_kernels442 B0 hB0
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

end LeanLab.Linnik1951
