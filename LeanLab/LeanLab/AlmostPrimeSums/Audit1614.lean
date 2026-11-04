/-
Unit U-1614, run 20261104T0803Z-26516. Refutations of the old leaves of `DecompJ1062`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.AlmostPrimeSums.DecompJ1062

namespace LeanLab.AlmostPrimeSums.Audit1614
open Filter Real TogashiUchiyamaScale

/-- The old `lower_sieve_constant`, false at `ε = 0`. -/
theorem old_lower_sieve_constant_false : ¬ ∀ T ε : ℝ, 26.4612 - ε / 2 < (26.4612 : ℝ) := by
  intro h
  have := h 0 0
  norm_num at this

/-- The old `lower_sieve_setup`, false at `T = -1`: `M (-1) N < 0` for every `N ≥ 2`. -/
theorem old_lower_sieve_setup_false : ¬ ∀ T ε : ℝ, ∀ᶠ N : ℕ in atTop, 0 ≤ M T N := by
  intro h
  obtain ⟨N, hN, h2⟩ := ((h (-1) 0).and (eventually_ge_atTop 2)).exists
  have hQ := (Q_bounds N).1
  have hA : Apaper (-1) N < 0 := by
    unfold Apaper Cpaper
    apply inv_lt_zero.mpr
    have : 0 < exp (2 * eulerMascheroniConstant) := exp_pos _
    nlinarith [mul_pos this hQ]
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have : M (-1) N < 0 := by
    unfold M
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hA hφ) (by positivity)
  linarith

end LeanLab.AlmostPrimeSums.Audit1614
#print axioms LeanLab.AlmostPrimeSums.Audit1614.old_lower_sieve_constant_false
#print axioms LeanLab.AlmostPrimeSums.Audit1614.old_lower_sieve_setup_false
