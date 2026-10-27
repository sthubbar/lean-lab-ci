/-
P0028, arXiv 1610.02017, Lemma 4.3 proof on page 10.
The majorant condition at frequency zero controls the total mass.
This supplies the bound on the Fourier transform used in the uniformity argument.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSBohrSmoothing

namespace LeanLab.Ternary.MMS
open Finset

/-- At zero frequency the transform is the total mass. -/
theorem fhat_zero (N : ℕ) (f : ℕ → ℝ) :
    fhat N f 0 = ((∑ n ∈ Icc 1 N, f n : ℝ) : ℂ) := by
  simp [fhat]

/-- The norm of the transform is at most the mass of a nonnegative input. -/
theorem fhat_norm_le_mass (N : ℕ) (f : ℕ → ℝ)
    (hf : ∀ n ∈ Icc 1 N, 0 ≤ f n) (γ : ℝ) :
    ‖fhat N f γ‖ ≤ ∑ n ∈ Icc 1 N, f n := by
  unfold fhat
  apply (norm_sum_le _ _).trans
  apply le_of_eq
  apply sum_congr rfl
  intro n hn
  have he : Complex.exp (-(2 * Real.pi * Complex.I * (n * γ))) = e (-(n : ℝ) * γ) := by
    unfold e
    congr 1
    push_cast
    ring
  rw [norm_mul, he, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hf n hn)]

/-- The sparse majorant hypothesis bounds the mass by 1 + η times N. -/
theorem prop31Hyp_mass_le {N : ℕ} {η ε K q : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) :
    (∑ n ∈ Icc 1 N, f n) ≤ (1 + η) * N := by
  obtain ⟨ν, hν, hh⟩ := hf.2.2.1
  have h0 := hh 0
  rw [fhat_zero, fhat_zero] at h0
  have hone : (∑ n ∈ Icc 1 N, (1 : ℝ)) = N := by simp
  rw [hone, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h0
  have hsum : (∑ n ∈ Icc 1 N, f n) ≤ ∑ n ∈ Icc 1 N, ν n :=
    sum_le_sum hν
  have hup := (abs_le.mp h0).2
  linarith

/-- For η at most one the sparse hypotheses give a Fourier bound of 2N. -/
theorem prop31Hyp_fhat_le {N : ℕ} {η ε K q : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (hη : η ≤ 1) (γ : ℝ) :
    ‖fhat N f γ‖ ≤ 2 * N := by
  have hmass := prop31Hyp_mass_le hf
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlast : (1 + η) * N ≤ 2 * N := by nlinarith
  exact (fhat_norm_le_mass N f hf.1 γ).trans (hmass.trans hlast)

end LeanLab.Ternary.MMS
