/-
Split of the sealed amplitude step principal_integral_amplitude491 of
SPLIT_principal_convolution491. The statement stays exactly as it is; this file adds
four leaves and one assembly.

The argument. The amplitude of the principal square integral is compared with the
square integral of the model series S one, taken over the same short arc. That
comparison is the Cauchy Schwarz step of the convolution comparison and is already
proved, so the leaves carry only the size of the arc integral: the near constant phase,
where the residual is at most three, and then the three modulus ranges at a residual of
at least four, namely the unit modulus, the moduli from two up to the one twentieth
power of N, where the arc is still long, and the moduli from that power up, where the
arc is short and the reciprocal length is the smaller of the two error sizes. The
assembly splits on the residual, then on the modulus equal to one, then on the size of
the modulus, adds the four constants and folds the two error sizes into the single
printed one. No analytic input is invented here.
-/
import LeanLab.Linnik1951.SPLIT_principal_convolution491

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- LEAF. The size step at a near constant phase. For a residual at most three, which
is the range where the damped logarithmic convolution is the empty sum and only the
first frequency of the model series enters, the square integral of the model series over
the short arc is bounded by the two printed error sizes, with nothing subtracted. -/
theorem principal_integral_arc_size_small_residual491 (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ 3 →
        ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          logFourier520 N z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The unit modulus step at a residual of at least four. At modulus one the
reduced residue set is the single residue zero, the principal character series is the
full prime series and the arc is the longest one the parameter range allows; the
amplitude of the square integral, with no main term subtracted, is bounded by the two
printed error sizes. -/
theorem principal_integral_unit_modulus_large_residual491 (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, q = 1 → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The intermediate modulus step at a residual of at least four. For a modulus
from two up to the one twentieth power of N a reduced residue twist is present but the
arc is still long, so both printed error sizes are needed; the amplitude of the square
integral, with no main term subtracted, is bounded by their sum. -/
theorem principal_integral_intermediate_modulus_large_residual491 (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The large modulus step at a residual of at least four. For a modulus at least
the one twentieth power of N the arc is short and the reciprocal length term is the
smaller of the two printed error sizes, while the square root term and the thirteenth
power of the logarithm are the ones that survive; the amplitude of the square integral,
with no main term subtracted, is bounded by their sum. -/
theorem principal_integral_large_modulus_large_residual491 (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (N : ℝ) ^ (1 / 20 : ℝ) ≤ (q : ℝ) → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- Folding a constant into a larger one, at a fixed nonnegative error size. -/
private theorem fold_scale491 {c d N lg E : ℝ} (hcd : c ≤ d) (hN : 0 ≤ N) (hlg : 0 ≤ lg)
    (hE : 0 ≤ E) : c * N * lg * E ≤ d * N * lg * E := by
  have hX : 0 ≤ N * lg * E := mul_nonneg (mul_nonneg hN hlg) hE
  calc c * N * lg * E = c * (N * lg * E) := by ring
    _ ≤ d * (N * lg * E) := mul_le_mul_of_nonneg_right hcd hX
    _ = d * N * lg * E := by ring

/-- The amplitude of the principal square integral, assembled from the size step and the
three modulus ranges. The statement is the sealed one, unchanged. At a residual at most
three the comparison with the model series and the size step suffice; above three the
three modulus ranges cover every positive modulus up to the one tenth power of N, and the
constants are added. -/
theorem principal_integral_amplitude491_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
        ‖principalIntegral491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C0, hC0, N0a, h0⟩ := principal_arc_compare491 hG
  obtain ⟨C1, hC1, N1, h1⟩ := principal_integral_arc_size_small_residual491 hG hM
  obtain ⟨C2, hC2, N2, h2⟩ := principal_integral_unit_modulus_large_residual491 hG hM
  obtain ⟨C3, hC3, N3, h3⟩ := principal_integral_intermediate_modulus_large_residual491 hG hM
  obtain ⟨C4, hC4, N4, h4⟩ := principal_integral_large_modulus_large_residual491 hG hM
  refine ⟨C0 + C1 + C2 + C3 + C4, by positivity,
    max 129 (max N0a (max N1 (max N2 (max N3 N4)))), ?_⟩
  intro N hN q hq hqQ n hn
  have hN129 : 129 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hrest : max N0a (max N1 (max N2 (max N3 N4))) < N :=
    lt_of_le_of_lt (le_max_right _ _) hN
  have hN0a : N0a < N := lt_of_le_of_lt (le_max_left _ _) hrest
  have ht1 : max N1 (max N2 (max N3 N4)) < N := lt_of_le_of_lt (le_max_right _ _) hrest
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) ht1
  have ht2 : max N2 (max N3 N4) < N := lt_of_le_of_lt (le_max_right _ _) ht1
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_left _ _) ht2
  have ht3 : max N3 N4 < N := lt_of_le_of_lt (le_max_right _ _) ht2
  have hN3 : N3 < N := lt_of_le_of_lt (le_max_left _ _) ht3
  have hN4 : N4 < N := lt_of_le_of_lt (le_max_right _ _) ht3
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have htp : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hR : (0 : ℝ) < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := mul_pos hqpos htp
  have hS : (0 : ℝ) < Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := Real.sqrt_pos.mpr hR
  have hlg : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hlg13 : (0 : ℝ) ≤ Real.log N ^ 13 := pow_nonneg hlg 13
  have hA0 : (0 : ℝ) ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hB0 : (0 : ℝ) ≤ 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hE0 : (0 : ℝ) ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
      1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by linarith
  have hBE : 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
      1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
        1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by linarith
  rcases le_or_gt n 3 with hn3 | hn4
  · have hcmp := h0 N hN0a q hq hqQ n
    have hsz := h1 N hN1 q hq hqQ n hn3
    have htri : ‖principalIntegral491 N q n‖ ≤
        ‖principalIntegral491 N q n -
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ +
        ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ := by
      have heq : (principalIntegral491 N q n -
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) +
          (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
          principalIntegral491 N q n := by ring
      calc ‖principalIntegral491 N q n‖ =
          ‖(principalIntegral491 N q n -
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
                (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
              logFourier520 N z ^ 2 *
                Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) +
            (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
                (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
              logFourier520 N z ^ 2 *
                Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))‖ := by
            rw [heq]
        _ ≤ _ := norm_add_le _ _
    have hsum : ‖principalIntegral491 N q n‖ ≤
        C0 * (N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
          C1 * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
      htri.trans (add_le_add hcmp hsz)
    have hfold : C0 * (N : ℝ) * Real.log N ^ 13 /
            Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
          C1 * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
        (C0 + C1) * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
      have h0le : C0 * (N : ℝ) * Real.log N ^ 13 /
            Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
          C0 * (N : ℝ) * Real.log N ^ 13 *
            (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
        le_of_eq (by ring)
      have h0le' : C0 * (N : ℝ) * Real.log N ^ 13 /
            Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
          C0 * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
        h0le.trans (mul_le_mul_of_nonneg_left hBE
          (mul_nonneg (mul_nonneg hC0.le hNpos.le) hlg13))
      nlinarith [h0le']
    exact hsum.trans (hfold.trans (fold_scale491
      (by linarith : C0 + C1 ≤ C0 + C1 + C2 + C3 + C4) hNpos.le hlg13 hE0))
  · have hn4' : (4 : ℤ) ≤ n := by omega
    rcases eq_or_lt_of_le hq with hq1 | hq2
    · subst hq1
      have hb := h2 N hN2 1 rfl n hn4' hn
      exact hb.trans (fold_scale491 (by linarith : C2 ≤ C0 + C1 + C2 + C3 + C4)
        hNpos.le hlg13 hE0)
    · have hq2' : 2 ≤ q := hq2
      rcases le_or_gt (q : ℝ) ((N : ℝ) ^ (1 / 20 : ℝ)) with hs | hb
      · have hb' := h3 N hN3 q hq hqQ hq2' hs n hn4' hn
        exact hb'.trans (fold_scale491 (by linarith : C3 ≤ C0 + C1 + C2 + C3 + C4)
          hNpos.le hlg13 hE0)
      · have hb' := h4 N hN4 q hq hqQ hq2' hb.le n hn4' hn
        exact hb'.trans (fold_scale491 (by linarith : C4 ≤ C0 + C1 + C2 + C3 + C4)
          hNpos.le hlg13 hE0)

end LeanLab.Linnik1951
