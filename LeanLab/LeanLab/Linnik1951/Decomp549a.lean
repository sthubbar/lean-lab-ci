/-
P0093 pages 160 and 161 equations 6.1 through 6.3.
The error only amplitude and the unit modulus approximation cannot both hold.
This checks the split, not the paper. The original main term is retained.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp491b
import LeanLab.Linnik1951.LogConvPort111

namespace LeanLab.Linnik1951

/-- P0093 page 161 equation 6.3. The displayed error at modulus one, multiplied
by log squared N and divided by N, tends to zero. This uses the existing
logarithmic power absorption theorem. -/
theorem principal_error_small549 (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C * Real.log N ^ 15 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
          1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) ≤ ε := by
  obtain ⟨N0, hN0⟩ := polylog_small_split111 15
    (c := 1 / 14) (A := C) (ε := ε / 2) (by norm_num) (by positivity)
  refine ⟨max 1 N0, ?_⟩
  intro N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hb := hN0 N (by omega)
  have hsqrt : Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) = (N : ℝ) ^ (1 / 14 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le]
    norm_num
  have hp := Real.rpow_le_rpow_of_exponent_le hN1
    (by norm_num : (1 / 14 : ℝ) ≤ 1 / 7)
  have hpos : 0 < (N : ℝ) ^ (1 / 14 : ℝ) := Real.rpow_pos_of_pos hNp _
  have hinv := one_div_le_one_div_of_le hpos hp
  rw [hsqrt]
  calc
    _ ≤ C * Real.log N ^ 15 * (2 / (N : ℝ) ^ (1 / 14 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity [Real.log_nonneg hN1])
      convert add_le_add_right hinv (1 / (N : ℝ) ^ (1 / 14 : ℝ)) using 1 <;> ring
    _ ≤ (ε / 2 * (N : ℝ) ^ (1 / 14 : ℝ)) *
        (2 / (N : ℝ) ^ (1 / 14 : ℝ)) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = ε := by field_simp

/-- P0093 page 161 after equation 6.3. At residual N the damped convolution
exceeds every fixed multiple of the displayed unit modulus error for large N.
The lower bound is the existing clean logarithmic convolution theorem. -/
theorem principal_main_dominates_error549 (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
          1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) <
        Real.exp (-1) * logConvolution1622 N := by
  obtain ⟨N0, hN0⟩ := principal_error_small549 C (Real.exp (-1) / 2) hC (by positivity)
  refine ⟨max 4 N0, ?_⟩
  intro N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog2 : 0 < Real.log N ^ 2 := by positivity
  have hg := mul_le_mul_of_nonneg_right (hN0 N (by omega)) hNp.le
  have hl : (N : ℝ) / Real.log N ^ 2 ≤ logConvolution1622 N := by
    simpa only [logConvolution1622, logConvolution1622_lc111] using
      logConv_main_le1622_lc111 N (by omega)
  have hl' := mul_le_mul_of_nonneg_left ((div_le_iff₀ hlog2).mp hl)
    (Real.exp_pos (-1)).le
  apply (mul_lt_mul_iff_left₀ hlog2).mp
  nlinarith [Real.exp_pos (-1)]

/-- P0093 page 161 equation 6.3. QUESTION about the sealed split.
If the unit modulus approximation holds, the error only amplitude statement
is false. The witness is modulus one and residual N for large N.
No GRH, Mellin bound or admitted theorem is used in this implication. -/
theorem principal_amplitude_incompatible_with_unit549
    (hunit : ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 →
        ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
        ‖principalIntegral491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  rintro ⟨A, hA, NA, hAmp⟩
  obtain ⟨B, hB, NB, hUnit⟩ := hunit
  obtain ⟨NC, hDom⟩ := principal_main_dominates_error549 (A + B) (by positivity)
  let N := max 4 (max NA (max NB NC)) + 1
  have hNA : NA < N := by omega
  have hNB : NB < N := by omega
  have hNC : NC < N := by omega
  have hN4 : 4 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hq : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow hN1 (by norm_num)
  have ha := hAmp N hNA 1 (by omega) (by simpa using hq) (N : ℤ) (le_refl _)
  have hb := hUnit N hNB 1 (by omega) (by simpa using hq) rfl (N : ℤ)
    (by exact_mod_cast hN4) (le_refl _)
  have hd := hDom N hNC
  have hexp : -(N : ℝ) / N = -1 := by field_simp
  simp only [Nat.cast_one, one_mul, Int.toNat_natCast, hexp] at ha hb
  have hl : 0 ≤ logConvolution1622 N := by
    have h := logConv_main_le1622_lc111 N hN4
    have he : logConvolution1622 N = logConvolution1622_lc111 N := rfl
    rw [← he] at h
    exact (by positivity : 0 ≤ (N : ℝ) / Real.log N ^ 2).trans h
  have hn : ‖((Real.exp (-1) * logConvolution1622 N : ℝ) : ℂ)‖ =
      Real.exp (-1) * logConvolution1622 N := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ht := norm_le_norm_add_norm_sub (principalIntegral491 N 1 (N : ℤ))
    (((Real.exp (-1) * logConvolution1622 N : ℝ) : ℂ))
  rw [hn] at ht
  have hu := ht.trans (add_le_add ha hb)
  nlinarith

/-- P0093 pages 160 and 161 equations 6.1 through 6.3. QUESTION about the split.
The error only amplitude and unit modulus approximation are incompatible.
This is an unconditional negation of their conjunction, not a refutation of
an individual GRH implication. The witness is q equal to one and n equal to N. -/
theorem not_principal_amplitude_and_unit549 :
    ¬ ((∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
        ‖principalIntegral491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 →
        ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))))) := by
  rintro ⟨hAmp, hUnit⟩
  exact principal_amplitude_incompatible_with_unit549 hUnit hAmp

end LeanLab.Linnik1951
