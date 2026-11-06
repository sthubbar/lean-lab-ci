/-
P0079 page 11, display 41, elementary paired-product reduction.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp353c

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 11, display 41. Bounding all but the first two power
factors leaves the two paired prime-power norms and the kernel. -/
theorem integrand_paired_bound396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ)
    (γ η ε X α B : ℝ) (hs : 2 ≤ s) (hB : 0 ≤ B)
    (hG : ∀ i : Fin s, ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ ≤ B) :
    ‖integrand293 s l1 l2 μ γ η ε X α‖ ≤
      B ^ (s - 2) *
        ‖primeSum293 ε X (l1 * α) * powerSum293 (cutoff293 s μ ε X) (μ 0 * α)‖ *
        ‖primeSum293 ε X (l2 * α) * powerSum293 (cutoff293 s μ ε X) (μ 1 * α)‖ *
        kernel293 η α := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n + 2 := ⟨s - 2, by omega⟩
  have htail : (∏ i : Fin n,
      ‖powerSum293 (cutoff293 (n + 2) μ ε X) (μ (i + 2) * α)‖) ≤ B ^ n := by
    calc
      _ ≤ ∏ _ : Fin n, B := by
        apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i hi
        exact hG ⟨i + 2, by omega⟩
      _ = _ := by simp
  simp only [integrand293, norm_mul, character_norm293, mul_one, norm_prod,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg293 η α),
    Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, Nat.add_sub_cancel]
  have H := mul_le_mul_of_nonneg_left htail
    (by positivity : 0 ≤ ‖primeSum293 ε X (l1 * α)‖ * ‖primeSum293 ε X (l2 * α)‖ *
      ‖powerSum293 (cutoff293 (n + 2) μ ε X) (μ 0 * α)‖ *
      ‖powerSum293 (cutoff293 (n + 2) μ ε X) (μ 1 * α)‖)
  have H' := mul_le_mul_of_nonneg_right H (kernel_nonneg293 η α)
  simpa only [mul_assoc, mul_left_comm, mul_comm, Nat.reduceAdd, Nat.add_assoc] using H'

end LeanLab.LZPowersOfTwo
