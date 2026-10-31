/-
AI wrote this Lean code for CODEX task71.
P0037 Section 3, printed page 208, PDF page 5.
Only the finite arithmetic correction factor is formalized here.
The probabilistic coverage model remains heuristic.
Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.DtRS1998.Task71.Heuristic

/-- The local factor in the printed product. -/
def localCorrection (s : ℚ) : ℚ := 1 - 1 / (s - 1) ^ 2

/-- The odd primes at most r. -/
def oddPrimes (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)

/-- The arithmetic correction C of Section 3, as an exact rational. -/
def correction (r : ℕ) : ℚ := 2 * ∏ p ∈ oddPrimes r, localCorrection p

theorem local_factor_identity (s : ℚ) (hs : 3 ≤ s) :
    ((s - 2) / (s - 1)) / ((s - 1) / s) = localCorrection s := by
  have hs0 : s ≠ 0 := by linarith
  have hs1 : s - 1 ≠ 0 := by linarith
  unfold localCorrection
  field_simp [hs0, hs1]
  <;> ring

theorem local_factor_bounds (s : ℚ) (hs : 3 ≤ s) :
    0 < localCorrection s ∧ localCorrection s ≤ 1 := by
  have hpos : 0 < s - 1 := by linarith
  have hden : 0 < (s - 1) ^ 2 := sq_pos_of_pos hpos
  have hbig : 1 < (s - 1) ^ 2 := by nlinarith [sq_nonneg (s - 2)]
  have hinv : 1 / (s - 1) ^ 2 < 1 := (div_lt_one hden).2 hbig
  unfold localCorrection
  constructor
  · linarith
  · exact sub_le_self _ (div_nonneg zero_le_one (le_of_lt hden))

theorem correction_bounds (r : ℕ) : 0 < correction r ∧ correction r ≤ 2 := by
  have hparts : ∀ p ∈ oddPrimes r, 0 < localCorrection p ∧ localCorrection p ≤ 1 := by
    intro p hp
    have hp3 : 3 ≤ p := (Finset.mem_filter.mp hp).2.2
    exact local_factor_bounds p (by exact_mod_cast hp3)
  have hpos : 0 < ∏ p ∈ oddPrimes r, localCorrection p :=
    Finset.prod_pos (fun p hp => (hparts p hp).1)
  have hle : ∏ p ∈ oddPrimes r, localCorrection p ≤ 1 :=
    Finset.prod_le_one₀ (fun p hp => le_of_lt (hparts p hp).1)
      (fun p hp => (hparts p hp).2)
  unfold correction
  constructor <;> nlinarith

set_option maxRecDepth 100000 in
theorem correction3 : correction 3 = 3 / 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem correction97_bounds :
    (132 : ℚ) / 100 < correction 97 ∧ correction 97 < (133 : ℚ) / 100 := by
  decide +kernel

end LeanLab.DtRS1998.Task71.Heuristic
