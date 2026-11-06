import LeanLab.Ricci1937.Decomp338i

/-!
Ricci 1937, canonical cutoff support profile.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary profile recurrence for second memoir pages 113 and 114 formulas 31.3 to 31.5.
The printed cumulative powers are the products of the successive perturbed block powers. -/
lemma decomp338_support_profile_recurrence (ε : ℝ) (α : ℕ → ℝ)
    (hα1 : α 1 = exp (-0.90 / 2 + ε))
    (hα2 : α 2 = exp (-1.46 / 2 + 2 * ε))
    (htail : ∀ i, α (i + 3) = exp (-1.98 / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ i) :
    α 1 = exp (-(decomp305HeadMass 0 : ℝ) / 100 / 2 + ε) ∧
      ∀ i, α (i + 2) = α (i + 1) * exp (-(decomp305HeadMass (i + 1) : ℝ) / 100 / 2 + ε) := by
  constructor
  · rw [hα1]
    congr 1
    norm_num [decomp305HeadMass]
  · intro i
    rcases i with _ | i
    · norm_num only [Nat.zero_add, decomp305HeadMass, Nat.cast_ofNat]
      rw [hα2, hα1, ← exp_add]
      congr 1
      ring
    rcases i with _ | i
    · have h3 : α 3 = exp (-1.98 / 2 + 3 * ε) := by simpa using htail 0
      norm_num only [Nat.zero_add, decomp305HeadMass, Nat.cast_ofNat]
      rw [h3, hα2, ← exp_add]
      congr 1
      ring
    · change α (i + 4) = α (i + 3) * exp (-(decomp305HeadMass (i + 3) : ℝ) / 100 / 2 + ε)
      rw [show i + 4 = (i + 1) + 3 by omega, htail (i + 1), htail i, pow_succ]
      norm_num [decomp305HeadMass] <;> ring

/-- Auxiliary actual cutoff profile for second memoir pages 113 and 114 formulas 31.3 to 31.5.
The canonical greedy cutoffs obey the printed perturbed cumulative powers until the residual endpoint,
and the residual endpoint bounds every later cutoff. -/
lemma decomp338_greedy_profile_bound (h Y t : ℕ) (hY : 4 ≤ Y) (hYt : Y ≤ t)
    (ε : ℝ) (α : ℕ → ℝ)
    (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε)
    (hα1 : α 1 = exp (-(decomp305HeadMass 0 : ℝ) / 100 / 2 + ε))
    (hrec : ∀ i, α (i + 2) = α (i + 1) * exp (-(decomp305HeadMass (i + 1) : ℝ) / 100 / 2 + ε))
    (i : ℕ) :
    (decomp338GreedyCutoff h Y t i : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) := by
  let c := decomp338GreedyCutoff h Y t
  have hlo := (decomp338_greedy_cutoff_bounds h Y t hYt).2.1
  induction i with
  | zero =>
    change (decomp338GreedyStep h Y t 0 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 1))
    rw [hα1]
    exact decomp338_greedy_step_power_max h Y t 0 hY hYt ε hsmall
  | succ i ih =>
    change (c (i + 1) : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 2)))
    change (c i : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) at ih
    by_cases hp : (t : ℝ) ^ (α (i + 1)) ≤ Y
    · have hci : (c i : ℝ) ≤ Y := by simpa only [max_eq_left hp] using ih
      have hs : (c (i + 1) : ℝ) ≤ c i := by
        exact_mod_cast decomp338_greedy_step_le h Y (c i) (i + 1)
      exact hs.trans (hci.trans (le_max_left _ _))
    · have hci : (c i : ℝ) ≤ (t : ℝ) ^ (α (i + 1)) := by
        simpa only [max_eq_right (le_of_lt (lt_of_not_ge hp))] using ih
      let r := exp (-(decomp305HeadMass (i + 1) : ℝ) / 100 / 2 + ε)
      have hstep := decomp338_greedy_step_power_max h Y (c i) (i + 1) hY (hlo i) ε hsmall
      change (c (i + 1) : ℝ) ≤ max (Y : ℝ) ((c i : ℝ) ^ r) at hstep
      have hrpow : (c i : ℝ) ^ r ≤ ((t : ℝ) ^ (α (i + 1))) ^ r :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hci (exp_pos _).le
      have heq : ((t : ℝ) ^ (α (i + 1))) ^ r = (t : ℝ) ^ (α (i + 2)) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg _), hrec i]
      have hle : (c i : ℝ) ^ r ≤ (t : ℝ) ^ (α (i + 2)) := hrpow.trans_eq heq
      exact hstep.trans (max_le_max_left _ hle)

end
end LeanLab.Ricci1937
