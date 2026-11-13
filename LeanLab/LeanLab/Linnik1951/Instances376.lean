/-
P0093 pages 154 and 165. Nonempty large value set for the entropy cover.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SecondMoment111

namespace LeanLab.Linnik1951

/-- P0093 page 154 definition of T. At phase zero the damped power
series has strictly positive norm for every positive N. -/
theorem power_zero_norm_pos376 (N : ℕ) (hN : 1 ≤ N) :
    0 < ‖powerFourier111 N 0‖ := by
  let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
  have ha : Summable a := (damping_summable111 N hN).comp_injective hi
  have hp : 0 < ∑' m, a m := ha.tsum_pos (fun m => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  have heq : powerFourier111 N 0 = ((∑' m, a m : ℝ) : ℂ) := by
    unfold powerFourier111
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    simp [a]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  exact hp

/-- P0093 page 165 Lemma 5. For positive eta and positive N, zero
belongs to the actual large T set. The interval cover cannot be justified
by treating its covered set as empty. -/
theorem large_value_zero376 (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (hη : 0 < η) :
    (0 : ℝ) ∈ {α : ℝ | α ∈ Set.Icc 0 1 ∧
      (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} := by
  refine ⟨by norm_num, ?_⟩
  nlinarith [mul_pos hη (power_zero_norm_pos376 N hN)]

end LeanLab.Linnik1951
