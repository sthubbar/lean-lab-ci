import Mathlib

/-!
# R-5030, Selberg's identity `Λ₂ = Λ log + Λ * Λ`

Lab proof, unit U-5302, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
Selberg 1949. The smallest lemma of route R-5030: Bombieri's asymptotic sieve controls sums of the
generalized von Mangoldt function `Λ₂ = μ * log²` over a sequence with a level of distribution,
and Selberg's identity splits `Λ₂` into the prime part `Λ log` and the two-prime part `Λ * Λ`,
which no sieve can tell apart. Binary Goldbach is OPEN.

* `L f = f · log`, and `L_mul`: `L` is a derivation of the Dirichlet ring, `L(f * g) = Lf * g + f * Lg`;
* `selberg_identity`: `μ * log² = Λ log + Λ * Λ`;
* `vonMangoldt_conv_prime`, `lambda2_prime`: `(Λ * Λ)(p) = 0` and `Λ₂(p) = log² p` for a prime `p`,
  the vacuity test.
-/

namespace LeanLab.Routes.R5030

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta


/-- `L f = f · log`, pointwise. -/
noncomputable def L (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := pmul f log

/-- `Λ₂ = μ * log²`, the second generalized von Mangoldt function. -/
noncomputable def lambda2 : ArithmeticFunction ℝ := (μ : ArithmeticFunction ℝ) * pmul log log

lemma L_mul (f g : ArithmeticFunction ℝ) : L (f * g) = L f * g + f * L g := by
  ext n
  simp only [L, pmul_apply, ArithmeticFunction.add_apply, mul_apply, log_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  obtain ⟨h1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have ha : (x.1 : ℝ) ≠ 0 := by
    have : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at h1; exact hn h1.symm
    exact_mod_cast this
  have hb : (x.2 : ℝ) ≠ 0 := by
    have : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at h1; exact hn h1.symm
    exact_mod_cast this
  rw [← h1, Nat.cast_mul, Real.log_mul ha hb]
  ring

lemma L_zeta : L (ζ : ArithmeticFunction ℝ) = log := by
  unfold L
  exact zeta_pmul log

/-- Selberg's identity: `μ * log² = Λ log + Λ * Λ`. -/
theorem selberg_identity : lambda2 = pmul Λ log + Λ * Λ := by
  have hlog : pmul log log = L log := rfl
  have h1 : L (log : ArithmeticFunction ℝ) = L Λ * (ζ : ArithmeticFunction ℝ) + Λ * (Λ * ζ) := by
    rw [← vonMangoldt_mul_zeta, L_mul, L_zeta, vonMangoldt_mul_zeta]
  unfold lambda2
  rw [hlog, h1]
  have hμζ : (μ : ArithmeticFunction ℝ) * ζ = 1 := coe_moebius_mul_coe_zeta
  calc (μ : ArithmeticFunction ℝ) * (L Λ * ζ + Λ * (Λ * ζ))
      = (L Λ + Λ * Λ) * ((μ : ArithmeticFunction ℝ) * ζ) := by ring
    _ = pmul Λ log + Λ * Λ := by rw [hμζ, mul_one]; rfl

/-- `(Λ * Λ)(p) = 0` for a prime `p`. -/
lemma vonMangoldt_conv_prime {p : ℕ} (hp : p.Prime) : (Λ * Λ : ArithmeticFunction ℝ) p = 0 := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => Λ a * Λ b), Nat.Prime.divisors hp,
    Finset.sum_pair hp.one_lt.ne, Nat.div_self hp.pos, Nat.div_one]
  simp [vonMangoldt_apply_one]

/-- Vacuity test: `Λ₂(p) = log² p`, all of it in the prime part. -/
theorem lambda2_prime {p : ℕ} (hp : p.Prime) : lambda2 p = Real.log p * Real.log p := by
  rw [selberg_identity, ArithmeticFunction.add_apply, vonMangoldt_conv_prime hp, add_zero, pmul_apply,
    vonMangoldt_apply_prime hp, log_apply]

end LeanLab.Routes.R5030
