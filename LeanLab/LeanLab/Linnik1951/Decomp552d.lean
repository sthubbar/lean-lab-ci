/-
P0093 pages 160 and 161. Elementary radius and error scale comparisons.
These statements do not supply a principal contour approximation.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp552c
import LeanLab.Linnik1951.Asymptotics357
import LeanLab.Linnik1951.Decomp549b

namespace LeanLab.Linnik1951

/-- P0093 page 161 after equation 6.3. The exact prime square full
period coefficient vanishes for every signed residual at most three.
This statement does not replace the truncated local arc by that coefficient. -/
theorem prime_square_small_residual_full_period552 (N : ℕ) (hN : 1 ≤ N)
    (n : ℤ) (hn : n ≤ 3) :
    (∫ z in (0 : ℝ)..1, primeFourier111 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) = 0 := by
  simp_rw [prime_series_nat552]
  have hp (z : ℝ) :
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  simp_rw [hp]
  rw [fourier_square_integral520 _ (prime_coefficients_summable552 N hN) n]
  split_ifs with hn0
  · rw [prime_coefficient_convolution552, prime_pair_count_small552 _ (by omega)]
    simp
  · rfl


/-- P0093 page 160 before equation 6.2. With q at most N to one tenth
and tau equal to N to one seventh, q tau is at most N to seventeen seventieths. -/
theorem q_tau_le552 (N q : ℕ) (hN : 1 ≤ N)
    (hq : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (17 / 70 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by rw [← Real.rpow_add hNp]; norm_num

/-- P0093 page 160 before equation 6.2. The original radius parameter
has square at most square root of N on the major modulus range. -/
theorem q_tau_square_le_sqrt552 (N q : ℕ) (hN : 1 ≤ N)
    (hq : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ^ 2 ≤ Real.sqrt N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ ((N : ℝ) ^ (17 / 70 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (q_tau_le552 N q hN hq) 2
    _ = (N : ℝ) ^ (17 / 35 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      norm_num
    _ ≤ Real.sqrt N := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)

/-- P0093 page 160 before equation 6.2. If log N is at least one,
the square root cost fits within N log N to power thirteen over q tau. -/
theorem sqrt_absorption552 (N q : ℕ) (hN : 1 ≤ N) (hq1 : 1 ≤ q)
    (hq : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) (hlog : 1 ≤ Real.log N) :
    Real.sqrt N ≤ (N : ℝ) * Real.log N ^ 13 /
      ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN3 : 3 ≤ N := by
    by_contra hN3
    have hNle : (N : ℝ) ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
    have he : Real.exp 1 ≤ N := (Real.le_log_iff_exp_le hNp).mp hlog
    have ht : (2 : ℝ) < Real.exp 1 := by
      have hh := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      norm_num at hh
      exact hh
    linarith
  exact (principal_contour_extension_scale549 N q hN3 hq1 hq).2

/-- P0093 pages 160 and 161 equations 6.1 through 6.3. Auxiliary
interval comparison. At N above one the sealed core radius is strictly
smaller than the original arc radius on the stated modulus range. -/
theorem core_radius_lt552 (N q : ℕ) (hN : 2 ≤ N) (hq1 : 1 ≤ q)
    (hq : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    1 / (N : ℝ) < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply one_div_lt_one_div_of_lt (mul_pos hqp (Real.rpow_pos_of_pos hNp _))
  calc
    _ ≤ (N : ℝ) ^ (17 / 70 : ℝ) := q_tau_le552 N q (by omega) hq
    _ < (N : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt
      (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
    _ = N := Real.rpow_one _

/-- P0093 page 161 equation 6.4. Auxiliary negative result about a
candidate estimate. The requested unit modulus error scale is sublinear,
so a crude bound proportional to N does not supply it. -/
theorem unit_error_sublinear552 (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
          1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) ≤ ε * N := by
  obtain ⟨M, hM⟩ := power_saving_negligible357 (2 * C) (1 / 14) (by positivity)
    (by norm_num) 13 ε hε
  refine ⟨max 1 M, ?_⟩
  intro N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hroot : Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) = (N : ℝ) ^ (1 / 14 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have hpow : (N : ℝ) ^ (1 / 14 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hinv : 1 / (N : ℝ) ^ (1 / 7 : ℝ) ≤ 1 / (N : ℝ) ^ (1 / 14 : ℝ) :=
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hNp _) hpow
  rw [hroot]
  calc
    _ ≤ C * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 14 : ℝ) + 1 / (N : ℝ) ^ (1 / 14 : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hinv (le_refl (1 / (N : ℝ) ^ (1 / 14 : ℝ)))) (by positivity)
    _ = (2 * C) * (N : ℝ) ^ (1 - (1 / 14 : ℝ)) * Real.log N ^ 13 := by
      rw [Real.rpow_sub hNp, Real.rpow_one]
      ring
    _ ≤ ε * N := hM N (by have := le_max_right 1 M; omega)

/-- P0093 page 161 equation 6.4. Auxiliary strict separation between
the printed unit error scale and a linear candidate upper bound. -/
theorem linear_bound_insufficient552 (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
          1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) < N := by
  obtain ⟨M, hM⟩ := unit_error_sublinear552 C (1 / 2) hC (by norm_num)
  refine ⟨max 1 M, ?_⟩
  intro N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := hM N (by have := le_max_right 1 M; omega)
  linarith

end LeanLab.Linnik1951
