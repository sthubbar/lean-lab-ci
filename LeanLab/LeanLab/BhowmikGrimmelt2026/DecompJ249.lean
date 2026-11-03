/-
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- The Euler factor of the generalized singular series at a prime `p`. -/
noncomputable def eulerFactorGen {r₁ r₂ : ℕ} (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ) (p : ℕ) : ℂ :=
  ∑' k : ℕ, if h : p ^ k = 0 then 0 else @Aq r₁ r₂ χ₁ χ₂ N (p ^ k) ⟨h⟩

/-- The Euler factor of the ordinary singular series at a prime `p`. -/
noncomputable def eulerFactorSing (N : ℕ) (p : ℕ) : ℝ :=
  ∑' k : ℕ, (((ArithmeticFunction.moebius (p ^ k) : ℤ) : ℝ) ^ 2 / (Nat.totient (p ^ k) : ℝ) ^ 2) * (ramanujan (p ^ k) N).re

/-- The level `p ^ v_p(r)` of the `p` component of a character mod `r`. It is `1` when `p` is not
a prime factor of `r`, and also when `p` is not prime. -/
abbrev compLevel (r p : ℕ) : ℕ := p ^ r.factorization p

instance compLevel_neZero (r p : ℕ) : NeZero (compLevel r p) := by
  refine ⟨?_⟩
  by_cases hp : p.Prime
  · exact pow_ne_zero _ hp.ne_zero
  · simp [compLevel, Nat.factorization_eq_zero_of_not_prime r hp]

/-- `ψ` is the family of prime power components of `χ`: each `ψ p` is a primitive character mod
`p ^ v_p(r)` and `χ` is their product on the integers coprime to `r`. This is what the Euler
product needs, since `A_q(χ₁, χ₂)` factors through the components and not through `χ₁, χ₂`. -/
def IsPrimeComponents {r : ℕ} (χ : DirichletCharacter ℂ r)
    (ψ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r p)) : Prop :=
  (∀ p, (ψ p).IsPrimitive) ∧
    ∀ a : ℕ, a.Coprime r → χ (a : ZMod r) = ∏ p ∈ r.primeFactors, ψ p (a : ZMod (compLevel r p))

/-- LEAF. Standard fact behind Pintz's Main Lemma, used on page 23 of P0029: a primitive character
mod `r` is the product of primitive characters mod the prime powers exactly dividing `r`. -/
theorem exists_primeComponents {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) : ∃ ψ, IsPrimeComponents χ ψ := by
  sorry

/-- LEAF page 23. The ordinary singular series converges to the product of its Euler factors.
`1 ≤ N` is the range of (6.5) in `Bound65`; at `N = 0` the product diverges, see
`Audit1610.euler_sing_eq_old_false`. -/
theorem euler_sing_eq (N : ℕ) (hN : 1 ≤ N) :
    Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorSing N p) atTop (𝓝 (singular N)) := by
  sorry

/-- LEAF page 23. The generalized singular series of primitive `χ₁, χ₂` converges to the product
of the Euler factors of their prime power components. `1 ≤ N` alone does not repair the old form:
`eulerFactorGen χ₁ χ₂` vanishes at every prime `p` unless `r₁, r₂` are powers of `p`, see
`Audit1610.euler_gen_eq_old_forces_zero`. -/
theorem euler_gen_eq {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : IsPrimeComponents χ₁ ψ₁) (h₂ : IsPrimeComponents χ₂ ψ₂) (N : ℤ) (hN : 1 ≤ N) :
    Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorGen (ψ₁ p) (ψ₂ p) N p)
      atTop (𝓝 (genSing χ₁ χ₂ N)) := by
  sorry

/-- LEAF page 23. For primitive characters and any prime `p`, the norm of the generalized Euler
factor is at most the ordinary Euler factor. Primitivity is the hypothesis of (6.5). -/
theorem local_bound {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (N : ℕ) (hN : 1 ≤ N) (p : ℕ) (hp : p.Prime) :
    ‖eulerFactorGen χ₁ χ₂ N p‖ ≤ eulerFactorSing N p := by
  sorry

/-- LEAF page 23. If local factors satisfy the bound and the global series converge, then the limit norms satisfy the bound. -/
theorem prod_bound {F : ℕ → ℂ} {f : ℕ → ℝ} {L : ℂ} {l : ℝ}
    (hF : Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, F p) atTop (𝓝 L))
    (hf : Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, f p) atTop (𝓝 l))
    (h_bound : ∀ p, p.Prime → ‖F p‖ ≤ f p) : ‖L‖ ≤ l := by
  have H : ∀ X : ℕ, ‖∏ p ∈ (Finset.range X).filter Nat.Prime, F p‖ ≤ ∏ p ∈ (Finset.range X).filter Nat.Prime, f p := by
    intro X
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun p hp => h_bound p (Finset.mem_filter.mp hp).2)
  exact le_of_tendsto_of_tendsto' hF.norm hf H

/-- The assembly theorem for `bound65` (Pintz's Main Lemma on page 23). -/
theorem bound65_decomposed : Bound65 := by
  intro r₁ r₂ _ _ χ₁ χ₂ hχ₁ hχ₂ N hN
  obtain ⟨ψ₁, h₁⟩ := exists_primeComponents χ₁ hχ₁
  obtain ⟨ψ₂, h₂⟩ := exists_primeComponents χ₂ hχ₂
  exact prod_bound (euler_gen_eq χ₁ χ₂ hχ₁ hχ₂ ψ₁ ψ₂ h₁ h₂ N (by exact_mod_cast hN))
    (euler_sing_eq N hN)
    (fun p hp => local_bound (ψ₁ p) (ψ₂ p) (h₁.1 p) (h₂.1 p) N hN p hp)

end LeanLab.BhowmikGrimmelt2026
