import LeanLab.Ricci1937.Decomp338ae
import LeanLab.Ricci1937.Decomp338m

/-!
Ricci 1937, iteration of the distinct first two block profile.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary iteration from distinct first and second endpoints.
First memoir page 89 case four and second memoir pages 113 to 115, formulas 31.3 to 31.5. -/
lemma decomp338_profile_from_two (h Y t : ℕ) (hY : 4 ≤ Y) (hYt : Y ≤ t)
    (ε : ℝ) (α : ℕ → ℝ)
    (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε)
    (hfirst : (decomp338GreedyCutoff h Y t 0 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 1)))
    (hsecond : (decomp338GreedyCutoff h Y t 1 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 2)))
    (hrec : ∀ i, α (i + 3) = α (i + 2) * exp (-(decomp305HeadMass (i + 2) : ℝ) / 100 / 2 + ε))
    (i : ℕ) :
    (decomp338GreedyCutoff h Y t i : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) := by
  let c := decomp338GreedyCutoff h Y t
  have hlo := (decomp338_greedy_cutoff_bounds h Y t hYt).2.1
  have htail (k : ℕ) : (c (k + 1) : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (k + 2))) := by
    induction k with
    | zero => exact hsecond
    | succ i ih =>
      change (c (i + 2) : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 3)))
      by_cases hp : (t : ℝ) ^ (α (i + 2)) ≤ Y
      · have hci : (c (i + 1) : ℝ) ≤ Y := by simpa only [max_eq_left hp] using ih
        have hs : (c (i + 2) : ℝ) ≤ c (i + 1) := by
          exact_mod_cast decomp338_greedy_step_le h Y (c (i + 1)) (i + 2)
        exact hs.trans (hci.trans (le_max_left _ _))
      · have hci : (c (i + 1) : ℝ) ≤ (t : ℝ) ^ (α (i + 2)) := by
          simpa only [max_eq_right (le_of_lt (lt_of_not_ge hp))] using ih
        let r := exp (-(decomp305HeadMass (i + 2) : ℝ) / 100 / 2 + ε)
        have hstep := decomp338_greedy_step_power_max h Y (c (i + 1)) (i + 2) hY (hlo (i + 1)) ε hsmall
        change (c (i + 2) : ℝ) ≤ max (Y : ℝ) ((c (i + 1) : ℝ) ^ r) at hstep
        have hrpow : (c (i + 1) : ℝ) ^ r ≤ ((t : ℝ) ^ (α (i + 2))) ^ r :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hci (exp_pos _).le
        have heq : ((t : ℝ) ^ (α (i + 2))) ^ r = (t : ℝ) ^ (α (i + 3)) := by
          rw [← Real.rpow_mul (Nat.cast_nonneg _), hrec i]
        exact hstep.trans (max_le_max_left _ (hrpow.trans_eq heq))
  cases i with
  | zero => exact hfirst
  | succ i => exact htail i

/-- Auxiliary later recurrence for the distinct case four profile.
First memoir page 89 case four and second memoir page 115 after 31.3 and 31.4. -/
lemma decomp338_case_four_profile_recurrence (ε : ℝ) (α : ℕ → ℝ)
    (hα2 : α 2 = exp (-(1.46 + Real.log 4) / 2 + 2 * ε))
    (htail : ∀ i, α (i + 3) = exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ i) :
    ∀ i, α (i + 3) = α (i + 2) * exp (-(decomp305HeadMass (i + 2) : ℝ) / 100 / 2 + ε) := by
  intro i
  cases i with
  | zero =>
    have h3 := htail 0
    norm_num only [Nat.zero_add, pow_zero, mul_one] at h3 ⊢
    rw [h3, hα2, ← exp_add]
    congr 1
    norm_num [decomp305HeadMass] <;> ring
  | succ i =>
    change α (i + 4) = α (i + 3) * _
    rw [show i + 4 = (i + 1) + 3 by omega, htail (i + 1), htail i, pow_succ]
    norm_num [decomp305HeadMass] <;> ring

end
end LeanLab.Ricci1937
