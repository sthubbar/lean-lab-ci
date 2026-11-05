/-
Convergence of the component Euler product without a global coefficient identity.
Source: P0029 page 23 display 6.4 and Pintz Part I page 20 display 7.14.
The limit is not identified with genSing here.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.PrimeValues247
import LeanLab.BhowmikGrimmelt2026.EulerBounds247

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- The deviations of the component prime factors from one are absolutely summable.
Only finitely many primes divide the conductors or positive N.
Source: P0029 page 6 display 2.10 and Pintz Part I page 20 display 7.14. -/
theorem component_deviation_summable247 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun p : ℕ => ‖(if p.Prime then
      eulerFactorGen (ψ₁ p) (ψ₂ p) N p else 1) - 1‖) := by
  have hs : Summable (fun n : ℕ => 1 / (((n - 1 : ℕ) : ℝ) ^ 2)) := by
    rw [← summable_nat_add_iff 1]
    simpa only [Nat.add_sub_cancel] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ)))
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (r₁ + r₂ + N + 1)] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  by_cases hprime : p.Prime
  · have hp₁ : ¬ p ∣ r₁ := by
      intro hd
      have := Nat.le_of_dvd (NeZero.pos r₁) hd
      omega
    have hp₂ : ¬ p ∣ r₂ := by
      intro hd
      have := Nat.le_of_dvd (NeZero.pos r₂) hd
      omega
    have hpN : ¬ p ∣ N := by
      intro hd
      have := Nat.le_of_dvd (by omega : 0 < N) hd
      omega
    rw [if_pos hprime, unramified_factor_value247 r₁ r₂ p N hprime hp₁ hp₂,
      if_neg hpN]
    have he (a : ℂ) : 1 - 1 / a ^ 2 - 1 = -(1 / a ^ 2) := by ring
    rw [he]
    simp [norm_div, norm_pow, Nat.totient_prime hprime]
  · rw [if_neg hprime, sub_self, norm_zero]
    positivity

/-- The full sequence of finite component products converges to some complex number.
This theorem does not identify that number with the generalized singular series.
Source: Pintz Part I page 20 display 7.14, the convergent product step. -/
theorem component_product_converges247 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ z : ℂ, Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime,
      eulerFactorGen (ψ₁ p) (ψ₂ p) N p) atTop (𝓝 z) := by
  have hs := component_deviation_summable247 ψ₁ ψ₂ N hN
  have hm : Multipliable (fun p : ℕ => if p.Prime then
      eulerFactorGen (ψ₁ p) (ψ₂ p) N p else 1) := by
    convert multipliable_one_add_of_summable hs using 1
    funext p
    ring
  refine ⟨∏' p : ℕ, if p.Prime then eulerFactorGen (ψ₁ p) (ψ₂ p) N p else 1, ?_⟩
  simpa only [Finset.prod_filter] using hm.tendsto_prod_tprod_nat

/-- The same convergence holds in the exact positive integer frequency range of euler_gen_eq.
The global series identity is still a separate obligation.
Source: P0029 page 23 display 6.4. -/
theorem component_product_converges_int247 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (N : ℤ) (hN : 1 ≤ N) :
    ∃ z : ℂ, Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime,
      eulerFactorGen (ψ₁ p) (ψ₂ p) N p) atTop (𝓝 z) := by
  have hn : 1 ≤ N.toNat := by omega
  have hncast : (N.toNat : ℤ) = N := Int.toNat_of_nonneg (by omega)
  simpa only [hncast] using component_product_converges247 ψ₁ ψ₂ N.toNat hn

/-- For primitive components the limit of the full product has the desired norm bound.
It is not yet known here to equal genSing.
Source: P0029 page 23 display 6.5. -/
theorem component_product_limit_bound247 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : ∀ p, (ψ₁ p).IsPrimitive) (h₂ : ∀ p, (ψ₂ p).IsPrimitive)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ z : ℂ, Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime,
      eulerFactorGen (ψ₁ p) (ψ₂ p) N p) atTop (𝓝 z) ∧ ‖z‖ ≤ singular N := by
  obtain ⟨z, hz⟩ := component_product_converges247 ψ₁ ψ₂ N hN
  exact ⟨z, hz, prod_bound hz (euler_sing_eq N hN)
    (fun p hp => local_bound (ψ₁ p) (ψ₂ p) (h₁ p) (h₂ p) N hN p hp)⟩

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.component_deviation_summable247
#print axioms LeanLab.BhowmikGrimmelt2026.component_product_converges247
#print axioms LeanLab.BhowmikGrimmelt2026.component_product_converges_int247
#print axioms LeanLab.BhowmikGrimmelt2026.component_product_limit_bound247
