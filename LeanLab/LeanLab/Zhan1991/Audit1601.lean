/-
Unit U-1601, statement audit of the two open leaves in Zhan1991/DecompJ822.
AI wrote this Lean code. Goldbach is open.
win_card110 is false even for nonnegative U, so the repair needs 1 ≤ U and not only 0 ≤ U.
minor_integral_bound110 is true once its bound is nonnegative.
-/
import LeanLab.Zhan1991.Decomp110

namespace LeanLab.Zhan1991.Audit1601

open LeanLab.Zhan1991

/-- win_card110 fails at N = 6 and U = 0, where the window is the single prime 2.
This is sharper than not_win_card_unrestricted226, which uses U = -1. Zhan page 270 has a
positive radius U, so this is a question about the lab statement and not about the paper. -/
theorem not_win_card_nonneg :
    ¬ ∀ (N : ℕ) (U : ℝ), 0 ≤ U → ((Win N U).card : ℝ) ≤ 3 * U := by
  intro h
  have hbad := h 6 0 le_rfl
  have hm : 2 ∈ Win ((6 : ℕ) : ℝ) 0 := by
    simp only [Win, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, Nat.prime_two⟩
    · apply Nat.ceil_le.mpr
      norm_num
    · apply Nat.le_floor
      norm_num
  have hc : 0 < (Win ((6 : ℕ) : ℝ) 0).card := Finset.card_pos.mpr ⟨2, hm⟩
  have hc' : (0 : ℝ) < ((Win ((6 : ℕ) : ℝ) 0).card : ℝ) := by exact_mod_cast hc
  linarith

/-- Repaired minor_integral_bound110: the sup bound is required to be nonnegative.
Zhan page 270, display 3.20 and 3.21. PROVED from the existing Decomp110 lemmas. -/
theorem minor_integral_bound_repaired (N : ℕ) (U d K : ℝ)
    (hM : 0 ≤ K * U * Real.log N ^ (-4 : ℝ))
    (h_sup : ∀ α ∈ minorArcs110 N U d,
      ‖primeSum110 N U α‖ ≤ K * U * Real.log N ^ (-4 : ℝ)) :
    |minorTerm110 N U d| ≤
      (K * U * Real.log N ^ (-4 : ℝ)) *
      (∫ α in (0 : ℝ)..1, ‖primeSum110 N U α‖ ^ 2) := by
  have e : (T N U : ℝ) - majorTerm110 N U d = minorTerm110 N U d := minor_identity226 N U d
  rw [primeSum_L2_110, ← e]
  exact minor_difference_bound226 N U d _ hM h_sup

/-- Vacuity instance for the repaired hypothesis: N = 9, U = K = 1 give a positive bound. -/
theorem minor_integral_bound_repaired_instance :
    0 < (1 : ℝ) * 1 * Real.log ((9 : ℕ) : ℝ) ^ (-4 : ℝ) := by
  have h : 0 < Real.log ((9 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  have := Real.rpow_pos_of_pos h (-4 : ℝ)
  linarith

end LeanLab.Zhan1991.Audit1601

#print axioms LeanLab.Zhan1991.Audit1601.not_win_card_nonneg
#print axioms LeanLab.Zhan1991.Audit1601.minor_integral_bound_repaired
#print axioms LeanLab.Zhan1991.Audit1601.minor_integral_bound_repaired_instance
