/-
P0093 page 166 equation 9.1. Elementary saving from a local system estimate.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp376c
import LeanLab.Perelli1996.Totient

namespace LeanLab.Linnik1951

open Filter
open scoped Topology

/-- P0093 page 166 after equation 9.3. The elementary square root
lower bound for the totient gives a reciprocal denominator bound.
Reuse the proved lab bound from P0083 page 484 equation 17. -/
theorem reciprocal_totient435 (q : ℕ) (hq : 1 ≤ q) :
    1 / (q.totient : ℝ) ≤ 2 / Real.sqrt q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hb : (q : ℝ) ≤ 2 * (q.totient : ℝ) ^ 2 := by
    exact_mod_cast LeanLab.Perelli1996.Totient.le_two_totient_sq q
  have hs : Real.sqrt q ≤ 2 * (q.totient : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  rw [div_le_div_iff₀ hφ (Real.sqrt_pos.mpr hqpos)]
  simpa using hs

/-- P0093 page 166 equation 9.1 and its use in 9.3. For q at least
N to one tenth the principal term is at most twice N to nineteen
twentieths, once log N is at least one. -/
theorem system_principal_bound435 (N q : ℕ) (hN : 1 ≤ N)
    (hlog : 1 ≤ Real.log N) (hq : (N : ℝ) ^ (1 / 10 : ℝ) ≤ q) :
    (N : ℝ) / q.totient / Real.log N ≤ 2 * (N : ℝ) ^ (19 / 20 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq1 : 1 ≤ q := by
    have h := (Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1 / 10)).trans hq
    exact_mod_cast h
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : (N : ℝ) ^ (1 / 20 : ℝ) ≤ Real.sqrt q := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = ((N : ℝ) ^ (1 / 10 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul hNp.le]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hq (by norm_num)
  have hi : 1 / (q.totient : ℝ) ≤ 2 / (N : ℝ) ^ (1 / 20 : ℝ) :=
    (reciprocal_totient435 q hq1).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) hs)
  calc
    _ ≤ (N : ℝ) / q.totient :=
      div_le_self (by positivity) hlog
    _ = (N : ℝ) * (1 / (q.totient : ℝ)) := by ring
    _ ≤ (N : ℝ) * (2 / (N : ℝ) ^ (1 / 20 : ℝ)) :=
      mul_le_mul_of_nonneg_left hi hNp.le
    _ = _ := by
      rw [show (N : ℝ) * (2 / (N : ℝ) ^ (1 / 20 : ℝ)) =
        2 * ((N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ (1 / 20 : ℝ)) by rw [Real.rpow_one]; ring,
        ← Real.rpow_sub hNp]
      norm_num

/-- P0093 page 166 equation 9.1. Dropping q from the square root
error denominator costs only a weaker power saving. Both reciprocal
terms are bounded by three times N to negative one fourteenth. -/
theorem system_reciprocal_bound435 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) :
    1 / (N : ℝ) ^ (1 / 7 : ℝ) +
      2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
        3 / (N : ℝ) ^ (1 / 14 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hτ : (N : ℝ) ^ (1 / 14 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hs : (N : ℝ) ^ (1 / 14 : ℝ) ≤
      Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    calc
      _ = Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le]
        norm_num
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [Real.rpow_pos_of_pos hNp (1 / 7 : ℝ)])
  have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : (0 : ℝ) < (N : ℝ) ^ (1 / 14 : ℝ)) hτ
  have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : (0 : ℝ) < (N : ℝ) ^ (1 / 14 : ℝ)) hs
  calc
    _ ≤ 1 / (N : ℝ) ^ (1 / 14 : ℝ) + 2 / (N : ℝ) ^ (1 / 14 : ℝ) := add_le_add h1 h2
    _ = _ := by ring

/-- P0093 page 166 equation 9.3. An arbitrary fixed logarithmic
power is eventually below any prescribed positive power of N.
This packages the real logarithmic absorption already used in the lab. -/
theorem log_power_small435 (k : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → Real.log N ^ k ≤ (N : ℝ) ^ a := by
  have he := (isLittleO_log_rpow_rpow_atTop (k : ℝ) ha).def (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually he)
  refine ⟨max 1 N0, ?_⟩
  intro N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have h := hN0 N (by have := le_max_right 1 N0; omega)
  simpa only [Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlog k), abs_of_pos (Real.rpow_pos_of_pos hNp a), one_mul] using h

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951

/-- P0093 page 166 equation 9.1 through 9.3. The explicit local
main term and error are bounded by five times N to nineteen twentieths
 times the thirteenth power of log N. The square root totient bound
suffices for this weaker saving. -/
theorem system_expression_bound435 (N q : ℕ) (hN : 1 ≤ N)
    (hlog : 1 ≤ Real.log N) (hq : (N : ℝ) ^ (1 / 10 : ℝ) ≤ q) :
    (N : ℝ) / q.totient / Real.log N +
      (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
          2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      5 * (N : ℝ) ^ (19 / 20 : ℝ) * Real.log N ^ 13 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq1 : 1 ≤ q := by
    exact_mod_cast (Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1 / 10)).trans hq
  have hlog13 : 1 ≤ Real.log N ^ 13 := one_le_pow₀ hlog
  have hprincipal := system_principal_bound435 N q hN hlog hq
  have hprincipal' : (N : ℝ) / q.totient / Real.log N ≤
      2 * (N : ℝ) ^ (19 / 20 : ℝ) * Real.log N ^ 13 :=
    hprincipal.trans (le_mul_of_one_le_right (by positivity) hlog13)
  have herror : (N : ℝ) * Real.log N ^ 13 *
      (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
        2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      3 * (N : ℝ) ^ (19 / 20 : ℝ) * Real.log N ^ 13 := by
    calc
      _ ≤ (N : ℝ) * Real.log N ^ 13 * (3 / (N : ℝ) ^ (1 / 14 : ℝ)) :=
        mul_le_mul_of_nonneg_left (system_reciprocal_bound435 N q hN hq1) (by positivity)
      _ = 3 * (N : ℝ) ^ (13 / 14 : ℝ) * Real.log N ^ 13 := by
        rw [show (N : ℝ) * Real.log N ^ 13 * (3 / (N : ℝ) ^ (1 / 14 : ℝ)) =
          3 * ((N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ (1 / 14 : ℝ)) * Real.log N ^ 13 by
            rw [Real.rpow_one]; ring, ← Real.rpow_sub hNp]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (13 / 14 : ℝ) ≤ 19 / 20))
          (by norm_num : (0 : ℝ) ≤ 3)) (by positivity)
  linarith

end LeanLab.Linnik1951
