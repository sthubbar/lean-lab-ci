/-
P0093 page 166. Separate the local rational system estimate from absorption.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Mass435

namespace LeanLab.Linnik1951

/-- LEAF. P0093 page 166 equation 9.1. Retain the principal totient
term and both explicit error denominators from the displayed formula.
The Mobius square is at most one. The fixed positive constant absorbs
its coefficient and the error constant. The derivation is the stated
modification of page 156 equation 3.4 through page 161 equation 6.4.
There is no uniform power saving in this leaf. -/
theorem doubled_system_expansion435 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        (∫ α in arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
          ‖primeFourier111 N α‖ ^ 2) ≤
          C * ((N : ℝ) / q.totient / Real.log N +
            (N : ℝ) * Real.log N ^ 13 *
              (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
                2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by
  sorry

/-- P0093 page 166 equation 9.1 used in 9.3. Exact
 doubled_system_mass376 statement. CONDITIONAL only on the explicit
local expansion. Totient saving and logarithmic absorption are proved. -/
theorem doubled_system_mass_decomposed435 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, (N : ℝ) ^ (1 / 10 : ℝ) ≤ (q : ℝ) →
        (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
          (∫ α in arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
            ‖primeFourier111 N α‖ ^ 2) ≤ C * (N : ℝ) ^ (98 / 100 : ℝ) := by
  obtain ⟨C, hC, Na, ha⟩ := doubled_system_expansion435 hG
  obtain ⟨Nl, hl⟩ := log_power_small435 13 (3 / 100) (by norm_num)
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨5 * C, by positivity, max 1 (max Na (max Nl L)), ?_⟩
  intro N hN q hq hqt
  have h1 : 1 ≤ N := by have := le_max_left 1 (max Na (max Nl L)); omega
  have hNa : Na < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNl : Nl < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hLN : L < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have hlog : 1 ≤ Real.log N := by
    have hNR : (L : ℝ) < N := by exact_mod_cast hLN
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hNR).le
  have hq1 : 1 ≤ q := by
    exact_mod_cast (Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1 / 10)).trans hq
  calc
    _ ≤ C * ((N : ℝ) / q.totient / Real.log N +
        (N : ℝ) * Real.log N ^ 13 *
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := ha N hNa q hq1 hqt
    _ ≤ C * (5 * (N : ℝ) ^ (19 / 20 : ℝ) * Real.log N ^ 13) :=
      mul_le_mul_of_nonneg_left (system_expression_bound435 N q h1 hlog hq) hC.le
    _ ≤ C * (5 * (N : ℝ) ^ (19 / 20 : ℝ) * (N : ℝ) ^ (3 / 100 : ℝ)) := by
      gcongr
      exact hl N hNl
    _ = _ := by
      rw [mul_assoc 5, ← Real.rpow_add hNp]
      norm_num
      ring

end LeanLab.Linnik1951
