import LeanLab.Ricci1937.Decomp338w
import LeanLab.Ricci1937.Decomp338m

/-!
Ricci 1937, shifted geometric support profiles.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary profile iteration from an improved first endpoint.
Second memoir pages 113 to 115, formulas 31.3 to 31.5 and their mixed variant. -/
lemma decomp338_profile_from_first (h Y t : ℕ) (hY : 4 ≤ Y) (hYt : Y ≤ t)
    (ε : ℝ) (α : ℕ → ℝ)
    (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε)
    (hfirst : (decomp338GreedyCutoff h Y t 0 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 1)))
    (hrec : ∀ i, α (i + 2) = α (i + 1) * exp (-(decomp305HeadMass (i + 1) : ℝ) / 100 / 2 + ε))
    (i : ℕ) :
    (decomp338GreedyCutoff h Y t i : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) := by
  let c := decomp338GreedyCutoff h Y t
  have hlo := (decomp338_greedy_cutoff_bounds h Y t hYt).2.1
  induction i with
  | zero => exact hfirst
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

/-- Auxiliary shifted geometric profile for first memoir page 89 cases two and three.
Second memoir pages 113 to 115, formulas 31.3 to 31.5 and their mixed variant.
Scaling every positive depth by exp of half log r preserves the later recurrence. -/
lemma decomp338_shifted_support_profile (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ ε : ℝ, ∃ α : ℕ → ℝ, 0 < ε ∧ ε < 1 / 4 ∧ α 0 = 1 ∧
      (∀ i, 0 < α i) ∧ (∀ i, α (i + 1) ≤ α i) ∧
      (∀ n, (∑ i ∈ range n, α (i + 1)) ≤ exp (Real.log r / 2) * ricciTau 2 + 0.001) ∧
      α 1 = exp (-(0.90 - Real.log r) / 2 + ε) ∧
      ∀ i, α (i + 2) = α (i + 1) * exp (-(decomp305HeadMass (i + 1) : ℝ) / 100 / 2 + ε) := by
  obtain ⟨ε, a, hε0, hε, ha0, hapos, hamono, hasum, ha1, ha2, hatail⟩ :=
    decompJ365_support_profile 0.001 (by norm_num)
  obtain ⟨_, harec⟩ := decomp338_support_profile_recurrence ε a ha1 ha2 hatail
  let s := exp (Real.log r / 2)
  have hs0 : 0 < s := exp_pos _
  have hs1 : s ≤ 1 := exp_le_one_iff.mpr (by linarith [Real.log_nonpos hr.le hr1])
  let α : ℕ → ℝ := fun i => if i = 0 then 1 else s * a i
  have hαpos (i : ℕ) : 0 < α i := by
    dsimp [α]
    split_ifs
    · norm_num
    · exact mul_pos hs0 (hapos i)
  have hαmono (i : ℕ) : α (i + 1) ≤ α i := by
    rcases i with _ | i
    · change s * a 1 ≤ 1
      have ha := hamono 0
      rw [ha0] at ha
      nlinarith [hapos 1]
    · simpa only [α, ite_eq_right (by omega : i + 1 + 1 ≠ 0),
        ite_eq_right (by omega : i + 1 ≠ 0)] using
        mul_le_mul_of_nonneg_left (hamono (i + 1)) hs0.le
  refine ⟨ε, α, hε0, hε, by simp [α], hαpos, hαmono, ?_, ?_, ?_⟩
  · intro n
    have hsum : (∑ i ∈ range n, α (i + 1)) = s * ∑ i ∈ range n, a (i + 1) := by
      simp only [α, Nat.add_one_ne_zero, ite_false, mul_sum]
    rw [hsum]
    have hh := mul_le_mul_of_nonneg_left (hasum n) hs0.le
    dsimp [s] at *
    nlinarith
  · change s * a 1 = _
    rw [ha1, ← exp_add]
    congr 1
    ring
  · intro i
    change s * a (i + 2) = (s * a (i + 1)) * _
    rw [harec i]
    ring

end
end LeanLab.Ricci1937
