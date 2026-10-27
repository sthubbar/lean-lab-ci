import LeanLab.Estermann1938.Ramanujan112
import LeanLab.HeathBrown1985.DivisorEps
import LeanLab.HeathBrown1985.Bound25

/-!
Estermann 1938, P0091, page 312, the second inequality in display 39.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Estermann1938.Decay112
open Real
open Ramanujan112

/-- The logarithmic factor in display 39 is bounded by nine times q to power one eighth. -/
theorem log_factor_le {q : ℕ} (hq : 1 ≤ q) :
    1 + Real.log q ≤ 9 * (q : ℝ) ^ ((1 : ℝ) / 8) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp : 1 ≤ (q : ℝ) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hqR (by norm_num)
  have hl := Real.log_le_rpow_div (Nat.cast_nonneg q) (by norm_num : (0 : ℝ) < 1 / 8)
  norm_num at hl
  linarith

/-- The elementary totient bound used to obtain the q decay in display 39. -/
theorem inv_totient_le {q : ℕ} (hq : 1 ≤ q) :
    (q.totient : ℝ)⁻¹ ≤
      (9 * Real.exp 1 * (1 + (Real.log 2)⁻¹)) * (q : ℝ) ^ ((1 : ℝ) / 8) / q := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL := Real.log_natCast_nonneg q
  have hpoly : 1 + Real.log q / Real.log 2 ≤
      (1 + (Real.log 2)⁻¹) * (1 + Real.log q) := by
    have hi : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr hl2.le
    rw [div_eq_mul_inv]
    nlinarith
  calc
    (q.totient : ℝ)⁻¹ ≤ Real.exp 1 * (1 + Real.log q / Real.log 2) / q :=
      LeanLab.HeathBrown1985.inv_totient_le q q hq le_rfl
    _ ≤ Real.exp 1 * ((1 + (Real.log 2)⁻¹) * (1 + Real.log q)) / q := by
      gcongr
    _ ≤ Real.exp 1 * ((1 + (Real.log 2)⁻¹) *
        (9 * (q : ℝ) ^ ((1 : ℝ) / 8))) / q := by
      gcongr
      exact log_factor_le hq
    _ = _ := by ring

/-- Display 39, page 312: one constant bounds the normalized g2 by n squared q to power negative three halves. -/
theorem display39 : ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (x : ℝ) (q : ℕ), 1 ≤ q →
    ‖g2 n x q / (q.totient : ℂ) ^ 2‖ ≤ A * (n : ℝ) ^ 2 * (q : ℝ) ^ (-(3 : ℝ) / 2) := by
  obtain ⟨D, hD, hdiv⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow 8 (by norm_num)
  let B : ℝ := 9 * Real.exp 1 * (1 + (Real.log 2)⁻¹)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨36 * D * B ^ 2, by positivity, ?_⟩
  intro n x q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hd : (q.divisors.card : ℝ) ≤ D * (q : ℝ) ^ ((1 : ℝ) / 8) := by
    simpa using hdiv q hq
  have hi : (q.totient : ℝ)⁻¹ ≤ B * (q : ℝ) ^ ((1 : ℝ) / 8) / q := inv_totient_le hq
  have hp : ((q : ℝ) ^ ((1 : ℝ) / 8)) ^ 4 / (q : ℝ) ^ 2 =
      (q : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
    norm_num
    rw [← Real.rpow_two, ← Real.rpow_sub hqR]
    norm_num
  calc
    ‖g2 n x q / (q.totient : ℂ) ^ 2‖ ≤
        4 * (n : ℝ) ^ 2 * (1 + Real.log q) * q.divisors.card / (q.totient : ℝ) ^ 2 :=
      display39_first n x hq
    _ = 4 * (n : ℝ) ^ 2 * (1 + Real.log q) * q.divisors.card * ((q.totient : ℝ)⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]
    _ ≤ 4 * (n : ℝ) ^ 2 * (9 * (q : ℝ) ^ ((1 : ℝ) / 8)) *
        (D * (q : ℝ) ^ ((1 : ℝ) / 8)) * (B * (q : ℝ) ^ ((1 : ℝ) / 8) / q) ^ 2 := by
      gcongr
      · exact log_factor_le hq
    _ = (36 * D * B ^ 2) * (n : ℝ) ^ 2 *
        (((q : ℝ) ^ ((1 : ℝ) / 8)) ^ 4 / (q : ℝ) ^ 2) := by ring
    _ = _ := by rw [hp]

#print axioms log_factor_le
#print axioms inv_totient_le
#print axioms display39

end LeanLab.Estermann1938.Decay112
