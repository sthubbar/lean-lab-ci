/-
R-0014 salvage, T2, unit U-1108, PC run 20261019T2003Z-20508: the Fourier floor for fake primes.

On `ZMod M`, for any two functions `Φ, Ψ`, the convolutions at `n` differ by at most
`D · ‖Φ + Ψ‖₂`, where `D` bounds `|𝓕Φ − 𝓕Ψ|` at every frequency:
  `|Σ_j Φ_j Φ_{n−j} − Σ_j Ψ_j Ψ_{n−j}|² ≤ D² Σ_j |Φ_j + Ψ_j|²`.
So a fake set `F` that kills the Goldbach count `r(N)` of the primes `A` must move some
exponential sum by at least `r(N)/√(Σ|1_A + 1_F|²) ≥ r(N)/(2√max(#A, #F))`, about
`√N/(log N)^{3/2}` up to the singular series. The fakes of R0014FakePrimes reach about `√N`.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.MVSkeleton

open ZMod Finset

namespace LeanLab.Routes.R0014

open LeanLab.Routes.R0001 LeanLab.ExceptionalSet.MV

variable {M : ℕ} [NeZero M]

/-- The convolution of `Φ` with itself at `n`. -/
noncomputable def conv (Φ : ZMod M → ℂ) (n : ZMod M) : ℂ := ∑ j, Φ j * Φ (n - j)

/-- The difference of two convolutions through the DFT. -/
theorem conv_sub (Φ Ψ : ZMod M → ℂ) (n : ZMod M) :
    (M : ℂ) * (conv Φ n - conv Ψ n)
      = ∑ k, (𝓕 Φ k - 𝓕 Ψ k) * 𝓕 (Φ + Ψ) k * (stdAddChar (n * k) : ℂ) := by
  unfold conv
  rw [mul_sub, ← sum_dft_sq, ← sum_dft_sq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_add]
  simp only [Pi.add_apply]
  ring

/-- **The Fourier floor.** If `‖𝓕Φ k − 𝓕Ψ k‖ ≤ D` at every `k`, then
`‖conv Φ n − conv Ψ n‖² ≤ D² Σ_j ‖Φ j + Ψ j‖²`. -/
theorem conv_sub_sq_le (Φ Ψ : ZMod M → ℂ) (n : ZMod M) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ k, ‖𝓕 Φ k - 𝓕 Ψ k‖ ≤ D) :
    ‖conv Φ n - conv Ψ n‖ ^ 2 ≤ D ^ 2 * ∑ j, ‖Φ j + Ψ j‖ ^ 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  set g : ZMod M → ℂ := 𝓕 (Φ + Ψ) with hg
  -- ‖M · Δ‖ ≤ D Σ ‖g k‖
  have h1 : ‖(M : ℂ) * (conv Φ n - conv Ψ n)‖ ≤ D * ∑ k, ‖g k‖ := by
    rw [conv_sub, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul]
    have he : ‖(stdAddChar (n * k) : ℂ)‖ = 1 := by simp
    rw [he, mul_one]
    exact mul_le_mul_of_nonneg_right (hD k) (norm_nonneg _)
  have h1' : (M : ℝ) * ‖conv Φ n - conv Ψ n‖ ≤ D * ∑ k, ‖g k‖ := by
    rw [norm_mul] at h1; simpa using h1
  -- Cauchy-Schwarz and Parseval
  have hcs : (∑ k, ‖g k‖) ^ 2 ≤ (M : ℝ) * ∑ k, ‖g k‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ZMod M))) (f := fun k => ‖g k‖)
    simpa [ZMod.card] using this
  have hpar : ∑ k, ‖g k‖ ^ 2 = (M : ℝ) * ∑ j, ‖Φ j + Ψ j‖ ^ 2 := by
    rw [hg, dft_parseval_norm]; simp
  have hS0 : 0 ≤ ∑ k, ‖g k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hL0 : 0 ≤ (M : ℝ) * ‖conv Φ n - conv Ψ n‖ := by positivity
  have hsq : ((M : ℝ) * ‖conv Φ n - conv Ψ n‖) ^ 2 ≤ D ^ 2 * (M : ℝ) ^ 2 * ∑ j, ‖Φ j + Ψ j‖ ^ 2 := by
    calc ((M : ℝ) * ‖conv Φ n - conv Ψ n‖) ^ 2 ≤ (D * ∑ k, ‖g k‖) ^ 2 :=
          pow_le_pow_left₀ hL0 h1' 2
      _ = D ^ 2 * (∑ k, ‖g k‖) ^ 2 := by ring
      _ ≤ D ^ 2 * ((M : ℝ) * ∑ k, ‖g k‖ ^ 2) := by gcongr
      _ = D ^ 2 * (M : ℝ) ^ 2 * ∑ j, ‖Φ j + Ψ j‖ ^ 2 := by rw [hpar]; ring
  have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  have : (M : ℝ) ^ 2 * ‖conv Φ n - conv Ψ n‖ ^ 2 ≤ (M : ℝ) ^ 2 * (D ^ 2 * ∑ j, ‖Φ j + Ψ j‖ ^ 2) := by
    nlinarith [hsq]
  exact le_of_mul_le_mul_left this hM2

/-- The floor in the fake prime form: if `Ψ` has zero convolution at `n`, every bound `D` on
the change of the DFT satisfies `‖conv Φ n‖² ≤ D² Σ ‖Φ + Ψ‖²`. -/
theorem fake_floor (Φ Ψ : ZMod M → ℂ) (n : ZMod M) (hΨ : conv Ψ n = 0) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ k, ‖𝓕 Φ k - 𝓕 Ψ k‖ ≤ D) :
    ‖conv Φ n‖ ^ 2 ≤ D ^ 2 * ∑ j, ‖Φ j + Ψ j‖ ^ 2 := by
  have := conv_sub_sq_le Φ Ψ n hD0 hD
  rwa [hΨ, sub_zero] at this

/-- For `0/1` valued `Φ, Ψ`, `Σ ‖Φ + Ψ‖² ≤ 2 (#supp Φ + #supp Ψ)`, from `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem sum_norm_add_sq_le (Φ Ψ : ZMod M → ℂ) :
    ∑ j, ‖Φ j + Ψ j‖ ^ 2 ≤ 2 * ∑ j, ‖Φ j‖ ^ 2 + 2 * ∑ j, ‖Ψ j‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have := norm_add_le (Φ j) (Ψ j)
  nlinarith [norm_nonneg (Φ j), norm_nonneg (Ψ j), norm_nonneg (Φ j + Ψ j),
    sq_nonneg (‖Φ j‖ - ‖Ψ j‖)]

/-- The L¹ form of the floor: `M ‖conv Φ n − conv Ψ n‖ ≤ D Σ_k ‖𝓕(Φ + Ψ) k‖`; numerically about
1.5 times stronger than the L² form for primes, numerics/r0014_l1floor.out. -/
theorem conv_sub_le_l1 (Φ Ψ : ZMod M → ℂ) (n : ZMod M) {D : ℝ}
    (hD : ∀ k, ‖𝓕 Φ k - 𝓕 Ψ k‖ ≤ D) :
    (M : ℝ) * ‖conv Φ n - conv Ψ n‖ ≤ D * ∑ k, ‖𝓕 (Φ + Ψ) k‖ := by
  have h1 : ‖(M : ℂ) * (conv Φ n - conv Ψ n)‖ ≤ D * ∑ k, ‖𝓕 (Φ + Ψ) k‖ := by
    rw [conv_sub, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul]
    have he : ‖(stdAddChar (n * k) : ℂ)‖ = 1 := by simp
    rw [he, mul_one]
    exact mul_le_mul_of_nonneg_right (hD k) (norm_nonneg _)
  rw [norm_mul] at h1; simpa using h1

/-- Vacuity: on `ZMod 1` with `Φ = 1`, `Ψ = 0`, the hypotheses hold with `D = 1`. -/
example : conv (fun _ : ZMod 1 => (0 : ℂ)) 0 = 0 := by simp [conv]

end LeanLab.Routes.R0014
