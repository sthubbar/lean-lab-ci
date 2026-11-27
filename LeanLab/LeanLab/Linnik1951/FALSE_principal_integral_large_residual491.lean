/-
P0093 pages 160 and 161, equations 6.1 through 6.3. A record about the split
SPLIT_principal_integral_amplitude491: under the extended Riemann hypothesis and the
Mellin estimate, each of its three leaves at a residual of at least four is false.
The leaves are principal_integral_unit_modulus_large_residual491,
principal_integral_intermediate_modulus_large_residual491 and
principal_integral_large_modulus_large_residual491. Each bounds the principal square
integral alone, with no main term subtracted, by the two printed error sizes. At
residual N the integral is close to the damped logarithmic convolution by
principal_convolution491, and that convolution is at least N over log squared N, far
above the error sizes, which only shrink as the modulus grows. So none of the three
leaves can be proved except by refuting the hypotheses. The statements of the split
are not changed here. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp549a

namespace LeanLab.Linnik1951

/-- The two printed error sizes only shrink as the modulus grows from one. -/
theorem error_size_antitone_modulus491 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) :
    1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
        1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
      1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNp _
  have hle : (N : ℝ) ^ (1 / 7 : ℝ) ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by
    nlinarith
  have h1 := one_div_le_one_div_of_le hp hle
  have h2 := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hp) (Real.sqrt_le_sqrt hle)
  linarith

/-- The common refutation. Under GRH and the Mellin estimate, no bound of the
principal square integral alone by the two printed error sizes can hold at residual N
along any choice of admissible moduli q N, with q at least one and at most the one
tenth power of N, defined for all large N. -/
theorem principal_integral_alone_false_along491 (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) (qf : ℕ → ℕ) (N1 : ℕ)
    (hqf : ∀ N : ℕ, N1 < N → 1 ≤ qf N ∧ ((qf N : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → N1 < N →
        ‖principalIntegral491 N (qf N) (N : ℤ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((qf N : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((qf N : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  rintro ⟨A, hA, NA, hAmp⟩
  obtain ⟨B, hB, NB, hConv⟩ := principal_convolution491 hG hM
  obtain ⟨NC, hDom⟩ := principal_main_dominates_error549 (A + B) (by positivity)
  let N := max 4 (max NA (max NB (max NC N1))) + 1
  have hNA : NA < N := by omega
  have hNB : NB < N := by omega
  have hNC : NC < N := by omega
  have hN1 : N1 < N := by omega
  have hN4 : 4 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hq1, hqQ⟩ := hqf N hN1
  have ha := hAmp N hNA hN1
  have hb := hConv N hNB (qf N) hq1 hqQ (N : ℤ) (le_refl _)
  have hd := hDom N hNC
  have hexp : -(N : ℝ) / N = -1 := by field_simp
  simp only [Int.toNat_natCast, hexp] at hb
  have hl : 0 ≤ logConvolution1622 N := by
    have h := logConv_main_le1622_lc111 N hN4
    have he : logConvolution1622 N = logConvolution1622_lc111 N := rfl
    rw [← he] at h
    exact (by positivity : 0 ≤ (N : ℝ) / Real.log N ^ 2).trans h
  have hn : ‖((Real.exp (-1) * logConvolution1622 N : ℝ) : ℂ)‖ =
      Real.exp (-1) * logConvolution1622 N := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ht := norm_le_norm_add_norm_sub (principalIntegral491 N (qf N) (N : ℤ))
    (((Real.exp (-1) * logConvolution1622 N : ℝ) : ℂ))
  rw [hn] at ht
  have hE := error_size_antitone_modulus491 N (qf N) (by omega) hq1
  have hlg : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hF : (0 : ℝ) ≤ (N : ℝ) * Real.log N ^ 13 := by positivity
  have hsum := ht.trans (add_le_add ha hb)
  have hmono : (A + B) * ((N : ℝ) * Real.log N ^ 13) *
      (1 / ((qf N : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
        1 / Real.sqrt ((qf N : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      (A + B) * ((N : ℝ) * Real.log N ^ 13) *
      (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) :=
    mul_le_mul_of_nonneg_left hE (mul_nonneg (by positivity) hF)
  have hd' : (A + B) * ((N : ℝ) * Real.log N ^ 13) *
      (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) <
      Real.exp (-1) * logConvolution1622 N := by
    have := hd
    calc _ = (A + B) * (N : ℝ) * Real.log N ^ 13 *
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) := by ring
      _ < _ := this
  have hlin : A * (N : ℝ) * Real.log N ^ 13 *
        (1 / ((qf N : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
          1 / Real.sqrt ((qf N : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
      B * (N : ℝ) * Real.log N ^ 13 *
        (1 / ((qf N : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
          1 / Real.sqrt ((qf N : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) =
      (A + B) * ((N : ℝ) * Real.log N ^ 13) *
      (1 / ((qf N : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
        1 / Real.sqrt ((qf N : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring
  linarith

/-- P0093 pages 160 and 161. FALSE under its hypotheses: the conclusion of the leaf
principal_integral_unit_modulus_large_residual491 fails under GRH and the Mellin
estimate. Witness modulus one, residual N, all large N. -/
theorem principal_integral_unit_modulus_large_residual_false491
    (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, q = 1 → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  rintro ⟨C, hC, N0, h⟩
  refine principal_integral_alone_false_along491 hG hM (fun _ => 1) 4 ?_
    ⟨C, hC, N0, fun N hN hN4 => h N hN 1 rfl (N : ℤ) (by exact_mod_cast hN4.le) le_rfl⟩
  intro N hN
  refine ⟨le_rfl, ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  simpa using Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1 / 10)

/-- P0093 pages 160 and 161. FALSE under its hypotheses: the conclusion of the leaf
principal_integral_intermediate_modulus_large_residual491 fails under GRH and the
Mellin estimate. Witness modulus two, residual N, all N above two to the twentieth. -/
theorem principal_integral_intermediate_modulus_large_residual_false491
    (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  have key : ∀ N : ℕ, 2 ^ 20 < N →
      ((2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) ∧ ((2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    intro N hN
    have hNr : ((2 : ℝ) ^ (20 : ℝ)) ≤ (N : ℝ) := by
      have : ((2 ^ 20 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN.le
      have h2 : ((2 : ℝ) ^ (20 : ℝ)) = ((2 ^ 20 : ℕ) : ℝ) := by
        rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        push_cast
        ring
      rw [h2]
      exact this
    have h20 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hNr (by norm_num : (0 : ℝ) ≤ 1 / 20)
      rwa [← Real.rpow_mul (by norm_num), show (20 : ℝ) * (1 / 20) = 1 by norm_num,
        Real.rpow_one] at this
    have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hNr
    have hmono := Real.rpow_le_rpow_of_exponent_le hN1
      (by norm_num : (1 / 20 : ℝ) ≤ 1 / 10)
    exact ⟨by simpa using h20, by simpa using h20.trans hmono⟩
  rintro ⟨C, hC, N0, h⟩
  refine principal_integral_alone_false_along491 hG hM (fun _ => 2) (2 ^ 20) ?_
    ⟨C, hC, N0, fun N hN hN1 => h N hN 2 (by norm_num) (key N hN1).2 le_rfl (key N hN1).1
      (N : ℤ) (by exact_mod_cast (show 4 ≤ N by omega)) le_rfl⟩
  intro N hN
  exact ⟨by norm_num, (key N hN).2⟩

/-- P0093 pages 160 and 161. FALSE under its hypotheses: the conclusion of the leaf
principal_integral_large_modulus_large_residual491 fails under GRH and the Mellin
estimate. Witness the modulus the ceiling of the one twentieth power of N, residual N,
all N above two to the twentieth. -/
theorem principal_integral_large_modulus_large_residual_false491
    (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (N : ℝ) ^ (1 / 20 : ℝ) ≤ (q : ℝ) → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  have key : ∀ N : ℕ, 2 ^ 20 < N →
      2 ≤ ⌈(N : ℝ) ^ (1 / 20 : ℝ)⌉₊ ∧
      (N : ℝ) ^ (1 / 20 : ℝ) ≤ (⌈(N : ℝ) ^ (1 / 20 : ℝ)⌉₊ : ℝ) ∧
      (⌈(N : ℝ) ^ (1 / 20 : ℝ)⌉₊ : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    intro N hN
    have hNr : ((2 : ℝ) ^ (20 : ℝ)) ≤ (N : ℝ) := by
      have : ((2 ^ 20 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN.le
      have h2 : ((2 : ℝ) ^ (20 : ℝ)) = ((2 ^ 20 : ℕ) : ℝ) := by
        rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        push_cast
        ring
      rw [h2]
      exact this
    have hNp : (0 : ℝ) ≤ N := by positivity
    have h20 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hNr (by norm_num : (0 : ℝ) ≤ 1 / 20)
      rwa [← Real.rpow_mul (by norm_num), show (20 : ℝ) * (1 / 20) = 1 by norm_num,
        Real.rpow_one] at this
    have hsq : (N : ℝ) ^ (1 / 10 : ℝ) = (N : ℝ) ^ (1 / 20 : ℝ) * (N : ℝ) ^ (1 / 20 : ℝ) := by
      rw [← Real.rpow_add' hNp (by norm_num)]
      norm_num
    have hle := Nat.le_ceil ((N : ℝ) ^ (1 / 20 : ℝ))
    have hlt := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp (1 / 20 : ℝ))
    refine ⟨?_, hle, ?_⟩
    · have : (2 : ℝ) ≤ (⌈(N : ℝ) ^ (1 / 20 : ℝ)⌉₊ : ℝ) := h20.trans hle
      exact_mod_cast this
    · rw [hsq]
      nlinarith
  rintro ⟨C, hC, N0, h⟩
  refine principal_integral_alone_false_along491 hG hM
    (fun N => ⌈(N : ℝ) ^ (1 / 20 : ℝ)⌉₊) (2 ^ 20) ?_
    ⟨C, hC, N0, fun N hN hN1 => h N hN _ (by have := (key N hN1).1; omega)
      (key N hN1).2.2 (key N hN1).1 (key N hN1).2.1
      (N : ℤ) (by exact_mod_cast (show 4 ≤ N by omega)) le_rfl⟩
  intro N hN
  exact ⟨by have := (key N hN).1; omega, (key N hN).2.2⟩

end LeanLab.Linnik1951
