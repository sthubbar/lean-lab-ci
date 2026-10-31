/-
P0028, arXiv 1610.02017, Lemma 4.3 item 2, pages 9 and 10.
The phase condition with δ/30 gives the mean control used in the uniform estimate.
No existence or size bound for the averaging set is asserted.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSOrthogonality

namespace LeanLab.Ternary.MMS
open Finset

/-- Distance of a character value from one is bounded by 2π times the phase distance. -/
theorem norm_e_sub_one_le (x : ℝ) : ‖e x - 1‖ ≤ 2 * Real.pi * |x| := by
  have he : e x = Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) := by
    unfold e
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    show (2 * Real.pi * x) / 2 = Real.pi * x by ring]
  calc |2 * Real.sin (Real.pi * x)| = 2 * |Real.sin (Real.pi * x)| := by
        rw [abs_mul]
        norm_num
    _ ≤ 2 * |Real.pi * x| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = 2 * Real.pi * |x| := by rw [abs_mul, abs_of_pos Real.pi_pos]; ring

/-- Subtracting an integer does not change the character. -/
theorem e_sub_int (x : ℝ) (k : ℤ) : e (x - (k : ℝ)) = e x := by
  have he := e_add (x - (k : ℝ)) (k : ℝ)
  rw [sub_add_cancel, e_int, mul_one] at he
  exact he.symm

/-- Averaging does not increase a uniform bound on the distance of phases from one. -/
theorem bohrMean_sub_one_le (B : Finset ℤ) (hB : B.Nonempty) (γ r : ℝ)
    (hr : ∀ b ∈ B, ‖e ((b : ℝ) * γ) - 1‖ ≤ r) : ‖bohrMean B γ - 1‖ ≤ r := by
  have hc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hcc : (B.card : ℂ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have he : bohrMean B γ - 1 = (∑ b ∈ B, (e ((b : ℝ) * γ) - 1)) / (B.card : ℂ) := by
    unfold bohrMean bohrSum
    rw [sum_sub_distrib]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    field_simp <;> simp [mul_comm]
  have hs : ‖∑ b ∈ B, (e ((b : ℝ) * γ) - 1)‖ ≤ (B.card : ℝ) * r := by
    calc _ ≤ ∑ b ∈ B, ‖e ((b : ℝ) * γ) - 1‖ := norm_sum_le _ _
      _ ≤ ∑ b ∈ B, r := sum_le_sum hr
      _ = _ := by simp
  have hden : ‖(B.card : ℂ)‖ = (B.card : ℝ) := by simp
  rw [he, norm_div, hden]
  apply (div_le_iff₀ hc).mpr
  simpa only [mul_comm] using hs

/-- The paper's δ/30 phase condition implies the needed δ/4 bound for the mean. -/
theorem bohrMean_phase_control (B : Finset ℤ) (hB : B.Nonempty) (γ δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ b ∈ B, ∃ k : ℤ, |(b : ℝ) * γ - k| ≤ δ / 30) :
    ‖1 - bohrMean B γ‖ ≤ δ / 4 := by
  rw [norm_sub_rev]
  apply bohrMean_sub_one_le B hB γ (δ / 4)
  intro b hb
  obtain ⟨k, hk⟩ := hp b hb
  rw [← e_sub_int ((b : ℝ) * γ) k]
  calc ‖e ((b : ℝ) * γ - k) - 1‖ ≤ 2 * Real.pi * |(b : ℝ) * γ - k| :=
        norm_e_sub_one_le _
    _ ≤ 2 * Real.pi * (δ / 30) := mul_le_mul_of_nonneg_left hk (by positivity)
    _ ≤ δ / 4 := by
      have h := mul_le_mul_of_nonneg_right Real.pi_lt_d2.le hδ
      nlinarith

/-- Lemma 4.3 item 2 for any nonempty set satisfying the paper's large frequency phases. -/
theorem prop31Hyp_uniform_bound {N : ℕ} {η ε K q δ : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (hη : η ≤ 1) (hδ : 0 ≤ δ)
    (B : Finset ℤ) (hB : B.Nonempty)
    (hp : ∀ γ : ℝ, δ * N ≤ ‖fhat N f γ‖ →
      ∀ b ∈ B, ∃ k : ℤ, |(b : ℝ) * γ - k| ≤ δ / 30) :
    ∀ γ : ℝ, ‖intHat (intervalLift N f - intSmooth B (intervalLift N f)) γ‖ ≤ δ * N := by
  apply intSmooth_uniform_bound B hB (intervalLift N f) N δ
  · intro γ
    simpa only [intHat_intervalLift] using prop31Hyp_fhat_le hf hη γ
  · intro γ hγ
    apply bohrMean_phase_control B hB γ δ hδ
    exact hp γ (by simpa only [intHat_intervalLift] using hγ)

end LeanLab.Ternary.MMS
