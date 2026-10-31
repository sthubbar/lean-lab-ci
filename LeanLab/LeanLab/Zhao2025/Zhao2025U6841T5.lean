import Mathlib
import LeanLab.Zhao2025.Zhao2025U6825Lemma31

/-!
# Zhao 2025, the T input `t₅ ≤ 0.09063` of layout C at `Λ = 1.363`, `λ₀ = 0.857`

G. Zhao, "The exceptional set of Goldbach problem and Linnik's constant", arXiv 2511.05631v2,
a preprint.  Unit U-6841, CLOUD 20261021T0316Z-cloud57.  AI wrote the Lean code.
Binary Goldbach is open.

The (3.27) bound is a Stieltjes sum over the 200 step grid `Λₖ = 1.363 + k h`, `h = 3.837/200`,
with integer zero counts `nₖ` from Theorem I (3.26):
`T ≤ n₀ e^{-W Λ₀} + Σ_{k<200} (n_{k+1} - nₖ) e^{-W Λₖ} + 0.001`, `W = 10/3`,
the `0.001` from Corollary 3.2 beyond `5.2`.  Here `W h = 0.06395` and `W Λ₀ = 1363/300`.

Proved unconditionally: `t5_sum_le`, the sum with the lab counts `n₀ = 6` and jumps `jumps`
is at most `0.09063`; Python gives `0.0906167`.
Conditional, `t5_conditional`: if Zhao's (3.27) gives `t` at most that sum with these counts,
then `t ≤ 0.09063`.  The counts themselves are the floors of `1/Δ²` from (3.26) with the
optimal `x`, computed in floats by numerics/zhao_U6825_grid.py; their interval certification
from bounds on `G` of (3.22) is NOT done here and is the next action.  Vacuity: `t5_vacuity`.
-/

namespace LeanLab.Zhao2025.U6841

open LeanLab.Pintz2018 LeanLab.Zhao2025.U6825

/-- The jumps `n_{k+1} - nₖ`, `k = 0, …, 199`, of the integer Theorem I counts at
`Λ = 1.363`, `λ₀ = 0.857`; `n₀ = 6`, `n₂₀₀ = 782`. -/
def jumps : List ℕ := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 2, 3, 3, 2, 3, 3, 3, 4, 3, 3, 4, 4, 3, 4, 4, 5, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 7, 6, 7, 8, 7, 8, 8, 9, 8, 10, 9, 10, 11, 11, 11, 12, 12, 13, 14, 14, 14, 16, 16, 17, 18, 18, 20, 20, 22, 22, 24, 25, 26, 28, 29, 31, 32]

set_option maxRecDepth 100000 in
theorem jumps_length : jumps.length = 200 := by decide +kernel

set_option maxRecDepth 100000 in
theorem jumps_total : 6 + jumps.sum = 782 := by decide +kernel

/-- The polynomial `Σ_{k<200} jumpsₖ qᵏ`. -/
noncomputable def P (q : ℝ) : ℝ := ∑ k ∈ Finset.range 200, (jumps.getD k 0 : ℝ) * q ^ k

theorem P_mono {q u : ℝ} (h0 : 0 ≤ q) (h : q ≤ u) : P q ≤ P u := by
  unfold P
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h k) (by positivity)

/-- The same polynomial over `ℚ`, for a kernel evaluation. -/
def Pq (q : ℚ) : ℚ := ∑ k ∈ Finset.range 200, (jumps.getD k 0 : ℚ) * q ^ k

set_option maxRecDepth 100000 in
theorem Pq_at : Pq (93806 / 100000) ≤ 242482 / 100000 := by decide +kernel

theorem P_at : P 0.93806 ≤ 2.42482 := by
  have h : P 0.93806 = ((Pq (93806 / 100000) : ℚ) : ℝ) := by
    unfold P Pq; push_cast; norm_num
  rw [h]
  have h2 : ((Pq (93806 / 100000) : ℚ) : ℝ) ≤ ((242482 / 100000 : ℚ) : ℝ) := by
    exact_mod_cast Pq_at
  calc _ ≤ _ := h2
    _ = 2.42482 := by norm_num

theorem q_up : Real.exp (-(0.06395 : ℝ)) ≤ 0.93806 :=
  eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)

theorem e0_up : Real.exp (-(1363 / 300 : ℝ)) ≤ 0.010638 :=
  eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)

/-- The (3.27) sum at `Λ₀ = 1.363` with counts `6` and `jumps`. -/
noncomputable def T327sum : ℝ :=
  6 * Real.exp (-(10 / 3 * 1.363)) +
    (∑ k ∈ Finset.range 200, (jumps.getD k 0 : ℝ) *
      Real.exp (-(10 / 3 * (1.363 + k * (3.837 / 200))))) + 0.001

theorem T327sum_eq :
    T327sum = Real.exp (-(1363 / 300 : ℝ)) * (6 + P (Real.exp (-(0.06395 : ℝ)))) + 0.001 := by
  unfold T327sum P
  rw [mul_add, Finset.mul_sum]
  congr 2
  · norm_num; ring_nf
  · apply Finset.sum_congr rfl
    intro k _
    have : Real.exp (-(10 / 3 * (1.363 + (k : ℝ) * (3.837 / 200)))) =
        Real.exp (-(1363 / 300 : ℝ)) * Real.exp (-(0.06395 : ℝ)) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    rw [this]; ring

theorem T327sum_nonneg : 0 ≤ T327sum := by
  unfold T327sum
  have : 0 ≤ ∑ k ∈ Finset.range 200, (jumps.getD k 0 : ℝ) *
      Real.exp (-(10 / 3 * (1.363 + k * (3.837 / 200)))) :=
    Finset.sum_nonneg (fun k _ => by positivity)
  positivity

/-- PROVED unconditional: the (3.27) sum with the lab counts is at most `0.09063`. -/
theorem t5_sum_le : T327sum ≤ 0.09063 := by
  rw [T327sum_eq]
  have hq0 : 0 ≤ Real.exp (-(0.06395 : ℝ)) := (Real.exp_pos _).le
  have hP : P (Real.exp (-(0.06395 : ℝ))) ≤ 2.42482 := (P_mono hq0 q_up).trans P_at
  have hP0 : 0 ≤ P (Real.exp (-(0.06395 : ℝ))) := by
    unfold P; exact Finset.sum_nonneg (fun k _ => by positivity)
  have he := e0_up
  have he0 : 0 ≤ Real.exp (-(1363 / 300 : ℝ)) := (Real.exp_pos _).le
  nlinarith

/-- CONDITIONAL ON Zhao (3.27) evaluated with the Theorem I (3.26) integer counts `6`, `jumps`,
taken as the named hypothesis `h327`: the layout C input `t₅ ≤ 0.09063`. -/
theorem t5_conditional (t : ℝ) (h327 : t ≤ T327sum) : t ≤ 0.09063 :=
  h327.trans t5_sum_le

/-- Vacuity: the hypothesis is satisfiable. -/
theorem t5_vacuity : ∃ t : ℝ, t ≤ T327sum := ⟨0, T327sum_nonneg⟩

end LeanLab.Zhao2025.U6841

#print axioms LeanLab.Zhao2025.U6841.jumps_total
#print axioms LeanLab.Zhao2025.U6841.Pq_at
#print axioms LeanLab.Zhao2025.U6841.P_at
#print axioms LeanLab.Zhao2025.U6841.jumps_length
#print axioms LeanLab.Zhao2025.U6841.q_up
#print axioms LeanLab.Zhao2025.U6841.e0_up
#print axioms LeanLab.Zhao2025.U6841.T327sum_eq
#print axioms LeanLab.Zhao2025.U6841.t5_sum_le
#print axioms LeanLab.Zhao2025.U6841.t5_conditional
#print axioms LeanLab.Zhao2025.U6841.t5_vacuity
