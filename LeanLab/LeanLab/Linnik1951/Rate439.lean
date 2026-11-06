/-
P0093 page 168 equation 10.5. Uniform divisor and cutoff arithmetic.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Smooth439

namespace LeanLab.Linnik1951

/-- P0093 page 168 equation 10.5. The logarithmic absolute tail factor
is at most ten times the reciprocal square root at every positive cutoff. -/
theorem logarithmic_tail_sqrt439 (Q : ℕ) (hQ : 1 ≤ Q) :
    (6 + 2 * Real.log Q) / (Q : ℝ) ≤ 10 / Real.sqrt Q := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hroot : 1 ≤ Real.sqrt Q := by
    simpa using Real.sqrt_le_sqrt hQR
  have hpos : (0 : ℝ) < Q := by linarith
  have hrpos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hpos
  have hlog := Real.log_le_rpow_div (x := (Q : ℝ)) (Nat.cast_nonneg Q)
    (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hnum : 6 + 2 * Real.log Q ≤ 10 * Real.sqrt Q := by linarith
  rw [div_le_div_iff₀ hpos hrpos]
  calc
    (6 + 2 * Real.log Q) * Real.sqrt Q ≤ (10 * Real.sqrt Q) * Real.sqrt Q :=
      mul_le_mul_of_nonneg_right hnum hrpos.le
    _ = 10 * (Q : ℝ) := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hpos.le]

/-- P0093 page 168 equation 10.5. The explicit absolute coefficient tail
has a uniform negative power rate when the residual is at most N. The
small power divisor bound is reused at exponent one hundredth. -/
theorem absolute_tail_uniform_scale439 :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ n : ℕ, 1 ≤ n → n ≤ N →
      4 * ((6 + 2 * Real.log ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊) *
        (n.divisors.card : ℝ) ^ 2 / (⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ : ℝ)) ≤
          C * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
  obtain ⟨D, hD, hd⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow 100 (by norm_num)
  refine ⟨80 * D ^ 2, by positivity, ?_⟩
  intro N hN n hn hnN
  let Q := ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hQ : 1 ≤ Q := Nat.floor_pos.mpr (Real.one_le_rpow hNR (by norm_num))
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hrootp : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQR
  have hdN : (n.divisors.card : ℝ) ≤ D * (N : ℝ) ^ (1 / 100 : ℝ) := by
    apply (hd n hn).trans
    norm_num
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnN) (by norm_num)) hD.le
  have hexp : ((N : ℝ) ^ (1 / 100 : ℝ)) ^ 2 * (N : ℝ) ^ (-(1 / 20 : ℝ)) =
      (N : ℝ) ^ (-(3 / 100 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← Real.rpow_add hNp]
    congr 1
    norm_num
  change 4 * ((6 + 2 * Real.log Q) * (n.divisors.card : ℝ) ^ 2 / (Q : ℝ)) ≤ _
  calc
    _ = 4 * (n.divisors.card : ℝ) ^ 2 * ((6 + 2 * Real.log Q) / (Q : ℝ)) := by ring
    _ ≤ 4 * (n.divisors.card : ℝ) ^ 2 * (10 / Real.sqrt Q) :=
      mul_le_mul_of_nonneg_left (logarithmic_tail_sqrt439 Q hQ) (by positivity)
    _ = 40 * (n.divisors.card : ℝ) ^ 2 * (1 / Real.sqrt Q) := by ring
    _ ≤ 40 * (n.divisors.card : ℝ) ^ 2 * (2 * (N : ℝ) ^ (-(1 / 20 : ℝ))) := by
      gcongr
      exact inverse_sqrt_floor376 N hN
    _ ≤ 40 * (D * (N : ℝ) ^ (1 / 100 : ℝ)) ^ 2 *
        (2 * (N : ℝ) ^ (-(1 / 20 : ℝ))) := by gcongr
    _ = (80 * D ^ 2) * (((N : ℝ) ^ (1 / 100 : ℝ)) ^ 2 *
        (N : ℝ) ^ (-(1 / 20 : ℝ))) := by ring
    _ = (80 * D ^ 2) * (N : ℝ) ^ (-(3 / 100 : ℝ)) := by rw [hexp]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)) (by positivity)

end LeanLab.Linnik1951
