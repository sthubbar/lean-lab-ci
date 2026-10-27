/-
CODEX task47, unit U-8096. AI wrote this Lean code. Binary Goldbach is open.
An elementary negative result for the remaining cited exceptional-set estimates.
The general count bound f N at most N alone cannot give a sublinear power bound.
This concerns an abstract model, not the actual Goldbach exceptional set.
-/
import Mathlib

namespace LeanLab.ExceptionalSet.TrivialBoundBarrier
open Filter Real Topology

/-- The maximal count N satisfies the trivial count bound but no smaller power bound. -/
theorem no_sublinear_bound_self {θ : ℝ} (hθ : θ < 1) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ C * (N : ℝ) ^ θ := by
  rintro ⟨C, hC⟩
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - θ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN1, hgt⟩ := (eventually_ge_atTop 1 |>.and (ht.eventually_gt_atTop C)).exists
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : (N : ℝ) ^ (1 - θ) ≤ C := by
    rw [Real.rpow_sub hN0, Real.rpow_one]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hN0 θ)).mpr (hC N hN1)
  exact (not_lt_of_ge hp) hgt

/-- A concrete model for why the elementary cardinality bound does not imply Lu's exponent. -/
theorem no_lu_bound_for_maximal_count :
    (∀ N : ℕ, (N : ℝ) ≤ N) ∧
      ¬ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ C * (N : ℝ) ^ (0.879 : ℝ) :=
  ⟨fun _ => le_rfl, no_sublinear_bound_self (by norm_num)⟩

/-- A trivial maximal count cannot satisfy the printed exponential saving shape. -/
theorem no_exponential_saving_self {θ : ℝ} (hθ : 0 < θ) :
    ¬ ∃ c C : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 1 ≤ N →
      (N:ℝ) ≤ C * N * Real.exp (-c * Real.log N ^ θ) := by
  rintro ⟨c,C,hc,N0,h⟩
  have hp : Tendsto (fun N : ℕ => Real.log N ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hn : Tendsto (fun N : ℕ => -c * Real.log N ^ θ) atTop atBot := by
    simpa [Function.comp_def,neg_mul] using tendsto_neg_atTop_atBot.comp (hp.const_mul_atTop hc)
  have he : Tendsto (fun N : ℕ => C * Real.exp (-c * Real.log N ^ θ)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hn).const_mul C
  obtain ⟨N,hN0,hN1,hsmall⟩ := ((eventually_ge_atTop N0).and
    ((eventually_ge_atTop 1).and (he.eventually_lt_const (by norm_num : (0:ℝ)<1)))).exists
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hh := h N hN0 hN1
  have hh1 : (1:ℝ) ≤ C * Real.exp (-c * Real.log N ^ θ) := by
    apply (mul_le_mul_iff_right₀ hNr).mp
    simpa [mul_assoc,mul_comm,mul_left_comm] using hh
  exact (not_lt_of_ge hh1) hsmall

end LeanLab.ExceptionalSet.TrivialBoundBarrier

#print axioms LeanLab.ExceptionalSet.TrivialBoundBarrier.no_sublinear_bound_self
#print axioms LeanLab.ExceptionalSet.TrivialBoundBarrier.no_lu_bound_for_maximal_count
