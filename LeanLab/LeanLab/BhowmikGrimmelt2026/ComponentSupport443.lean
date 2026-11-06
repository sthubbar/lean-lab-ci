/-
The missing conductor branch of the finite component coefficient identity.
Source: Pintz Part I page 19 display 7.9 and the support restrictions in 7.10.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.ComponentsLift443

namespace LeanLab.BhowmikGrimmelt2026

/-- A missing conductor power makes a factor of the finite component product zero.
Source: Pintz Part I page 19, before display 7.10.
Only the source level and modulus support enter this implication. -/
theorem component_product_zero443 {r₁ r₂ q : ℕ} [NeZero r₁] [NeZero r₂] [NeZero q]
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (N : ℤ) (X : ℕ) (hX : r₁ < X) (hbad : ¬r₁ ∣ q) :
    (∏ p ∈ (Finset.range X).filter Nat.Prime,
      aqZero247 (ψ₁ p) (ψ₂ p) N (p ^ q.factorization p)) = 0 := by
  classical
  have hn : ¬r₁.factorization ≤ q.factorization := fun h =>
    hbad ((Nat.factorization_le_iff_dvd (NeZero.ne r₁) (NeZero.ne q)).mp h)
  change ¬∀ p, r₁.factorization p ≤ q.factorization p at hn
  obtain ⟨p, hp⟩ := not_forall.mp hn
  have hlt : q.factorization p < r₁.factorization p := lt_of_not_ge hp
  have hprime : p.Prime := by
    by_contra h
    rw [Nat.factorization_eq_zero_of_not_prime r₁ h] at hlt
    omega
  have hd : p ∣ r₁ := Nat.dvd_of_factorization_pos (by omega)
  have hpX : p < X := lt_of_le_of_lt
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne r₁)) hd) hX
  have hlocal : ¬compLevel r₁ p ∣ p ^ q.factorization p := by
    rw [compLevel, Nat.pow_dvd_pow_iff_le_right hprime.one_lt]
    omega
  apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpX, hprime⟩)
  apply aqZero247_eq_zero_of_not_lcm_dvd
  intro hd
  exact hlocal ((Nat.dvd_lcm_left _ _).trans hd)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.component_product_zero443
