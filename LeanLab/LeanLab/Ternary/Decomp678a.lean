/-
MMS https://arxiv.org/abs/1610.02017v2 pages 11 and 12.
Rectangular tests for the logarithmic prime measure in the triple quadrature.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp581b

namespace LeanLab.Ternary.MMS.Task678
open Finset Filter Topology

/-- The proved interval test also gives filter convergence.
Derived primitive quadrature step for MMS page 11 bottom display.
No short interval rough number estimate is used. -/
theorem prime_log_window_tendsto (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
        Real.log p / p) / Real.log x) atTop (𝓝 (b - a)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨X, hX⟩ := Task581.prime_log_power_window_limit a b ha hab (ε / 2) (by linarith)
  refine ⟨X, fun x hx => ?_⟩
  rw [Real.dist_eq]
  exact (hX x hx).trans_lt (by linarith)

/-- A product box test factors into its three one dimensional prime tests.
Derived finite algebra for MMS page 11 prime sum to integral passage.
The box has independent coordinates and has no order restriction. -/
theorem prime_log_box_factor (x a₁ b₁ a₂ b₂ a₃ b₃ : ℝ) :
    (∑ p ∈ (Ioc ⌊x ^ a₁⌋₊ ⌊x ^ b₁⌋₊).filter Nat.Prime,
      ∑ q ∈ (Ioc ⌊x ^ a₂⌋₊ ⌊x ^ b₂⌋₊).filter Nat.Prime,
        ∑ r ∈ (Ioc ⌊x ^ a₃⌋₊ ⌊x ^ b₃⌋₊).filter Nat.Prime,
          (Real.log p / p) * (Real.log q / q) * (Real.log r / r)) /
            Real.log x ^ 3 =
      ((∑ p ∈ (Ioc ⌊x ^ a₁⌋₊ ⌊x ^ b₁⌋₊).filter Nat.Prime,
        Real.log p / p) / Real.log x) *
      ((∑ q ∈ (Ioc ⌊x ^ a₂⌋₊ ⌊x ^ b₂⌋₊).filter Nat.Prime,
        Real.log q / q) / Real.log x) *
      ((∑ r ∈ (Ioc ⌊x ^ a₃⌋₊ ⌊x ^ b₃⌋₊).filter Nat.Prime,
        Real.log r / r) / Real.log x) := by
  simp only [← mul_sum, ← sum_mul]
  ring

/-- Logarithm weighted prime mass on a fixed product box tends to its volume.
Derived rectangular quadrature step for MMS page 11 bottom display.
This has no Buchstab kernel and no ordered region boundary. -/
theorem prime_log_box_tendsto (a₁ b₁ a₂ b₂ a₃ b₃ : ℝ)
    (ha₁ : 0 < a₁) (hab₁ : a₁ ≤ b₁)
    (ha₂ : 0 < a₂) (hab₂ : a₂ ≤ b₂)
    (ha₃ : 0 < a₃) (hab₃ : a₃ ≤ b₃) :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ (Ioc ⌊x ^ a₁⌋₊ ⌊x ^ b₁⌋₊).filter Nat.Prime,
        ∑ q ∈ (Ioc ⌊x ^ a₂⌋₊ ⌊x ^ b₂⌋₊).filter Nat.Prime,
          ∑ r ∈ (Ioc ⌊x ^ a₃⌋₊ ⌊x ^ b₃⌋₊).filter Nat.Prime,
            (Real.log p / p) * (Real.log q / q) * (Real.log r / r)) /
              Real.log x ^ 3) atTop (𝓝 ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃))) := by
  simp_rw [prime_log_box_factor]
  exact ((prime_log_window_tendsto a₁ b₁ ha₁ hab₁).mul
    (prime_log_window_tendsto a₂ b₂ ha₂ hab₂)).mul
      (prime_log_window_tendsto a₃ b₃ ha₃ hab₃)

/-- The frozen cofactor model is the kernel times three prime measure atoms.
Derived Jacobian identity for MMS page 11 bottom display.
The logarithmic prime weights give the extra three coordinate factors. -/
theorem cofactorModel_eq_kernel_mass {x : ℝ} (hx : 1 < x) {p : ℕ × ℕ × ℕ}
    (hp : p ∈ Task581.primeTriples x) :
    Task581.cofactorModel x p =
      Task571.extendedKernel Task571.buchstabModel
        (Real.log p.1 / Real.log x) (Real.log p.2.1 / Real.log x)
        (Real.log p.2.2 / Real.log x) *
      ((Real.log p.1 / p.1) / Real.log x) *
      ((Real.log p.2.1 / p.2.1) / Real.log x) *
      ((Real.log p.2.2 / p.2.2) / Real.log x) := by
  obtain ⟨ha, hab, hbc, hc⟩ := Task581.primeTriple_log_coordinates hx hp
  rw [Task571.extendedKernel_eq ha (hab.trans (hbc.trans hc)) hab (hbc.trans hc) hbc hc,
    Task581.cofactorModel_log_coordinates hx hp]
  have ht := (mem_filter.mp hp).2
  have hlx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hl₁ : Real.log (p.1 : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast ht.1.one_lt)).ne'
  have hl₂ : Real.log (p.2.1 : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast ht.2.1.one_lt)).ne'
  have hl₃ : Real.log (p.2.2 : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast ht.2.2.1.one_lt)).ne'
  have hp₁ : (p.1 : ℝ) ≠ 0 := by exact_mod_cast ht.1.ne_zero
  have hp₂ : (p.2.1 : ℝ) ≠ 0 := by exact_mod_cast ht.2.1.ne_zero
  have hp₃ : (p.2.2 : ℝ) ≠ 0 := by exact_mod_cast ht.2.2.1.ne_zero
  simp only [Task581.tripleProduct, Nat.cast_mul]
  field_simp

end LeanLab.Ternary.MMS.Task678
