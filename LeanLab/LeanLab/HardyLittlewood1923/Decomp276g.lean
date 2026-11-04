/-
AI wrote this Lean code for CODEX task276.
P0004 page 30 equation 3.511 and its preceding counting estimate.
Binary Goldbach is OPEN.
-/
import LeanLab.HardyLittlewood1923.TheoremC

namespace LeanLab.HardyLittlewood1923.Decomp276g

open Finset

/-- P0004 page 30 before equation 3.511. Fixing all but one coordinate determines the last prime. -/
theorem Nr_le_pow (s n : ℕ) : Nr (s + 1) n ≤ (n + 1) ^ s := by
  classical
  calc _ ≤ #((Fintype.piFinset fun _ : Fin (s + 1) => range (n + 1)).filter
      (fun u => ∑ i, u i = n)) := by
        apply card_le_card
        intro u hu
        obtain ⟨hu, _, hs⟩ := mem_filter.mp hu
        exact mem_filter.mpr ⟨hu, hs⟩
       _ ≤ _ := card_fixsum_le s n n

/-- P0004 page 30 before equation 3.511, an explicit strict power bound for the prime count. -/
theorem Nr_lt_power (s n : ℕ) (hn : 1 ≤ n) :
    (Nr (s + 1) n : ℝ) < 2 ^ (s + 1) * (n : ℝ) ^ s := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (Nr (s + 1) n : ℝ) ≤ ((n : ℝ) + 1) ^ s := by
    exact_mod_cast Nr_le_pow s n
  have hs : ((n : ℝ) + 1) ^ s ≤ 2 ^ s * (n : ℝ) ^ s := by
    rw [← mul_pow]
    gcongr
    linarith
  have hp : 0 < (2 : ℝ) ^ s * (n : ℝ) ^ s := by positivity
  calc _ ≤ ((n : ℝ) + 1) ^ s := hc
       _ ≤ 2 ^ s * (n : ℝ) ^ s := hs
       _ < _ := by rw [pow_succ]; nlinarith only [hp]

/-- P0004 page 30 equation 3.511, an explicit weighted count bound. -/
theorem nur_le_power_log (s n : ℕ) (hn : 1 ≤ n) :
    nur (s + 1) n ≤ 2 ^ s * (n : ℝ) ^ s * Real.log n ^ (s + 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (Nr (s + 1) n : ℝ) ≤ ((n : ℝ) + 1) ^ s := by
    exact_mod_cast Nr_le_pow s n
  have hs : ((n : ℝ) + 1) ^ s ≤ 2 ^ s * (n : ℝ) ^ s := by
    rw [← mul_pow]
    gcongr
    linarith
  exact (nur_le (s + 1) n).trans
    (mul_le_mul_of_nonneg_right (hc.trans hs) (pow_nonneg (Real.log_natCast_nonneg n) _))

#print axioms Nr_le_pow
#print axioms Nr_lt_power
#print axioms nur_le_power_log

end LeanLab.HardyLittlewood1923.Decomp276g
