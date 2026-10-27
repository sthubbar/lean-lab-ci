/-
P0076 Lemma 5.4, pages 19 to 20. The complete local product bound at arbitrary nonzero modulus.
The local product definition is the prime by prime form of the sieve conditions in display 5.5.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.LocalSieveFourier

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The display 5.5 sieve sum, with the coprimality restrictions written prime by prime. -/
noncomputable def compositeSieveSum (q : ℕ) [NeZero q] (W V b : ℤ) (a : ℕ) : ℂ :=
  ∑ x : ZMod q,
    (∏ p : q.primeFactors, localSieveWeight p W V b (x.val : ZMod p)) *
      ZMod.stdAddChar ((a : ZMod q) * x)

/-- The complete divisor count bound for the sieve sum, without amenability assumptions. -/
theorem compositeSieveSum_norm_le_divisors (q : ℕ) [NeZero q]
    (W V b : ℤ) (a : ℕ) (ha : a.Coprime q) :
    ‖compositeSieveSum q W V b a‖ ≤ (q.divisors.card : ℝ) := by
  let P := q.primeFactors
  let K : P → ℕ := fun p => q.factorization p
  have hp (p : P) : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.property
  have hk (p : P) : 0 < K p :=
    (hp p).factorization_pos_of_dvd (NeZero.ne q) (Nat.dvd_of_mem_primeFactors p.property)
  letI : ∀ p : P, Fact (Nat.Prime (p : ℕ)) := fun p => ⟨hp p⟩
  letI : ∀ p : P, NeZero ((p : ℕ) ^ K p) := fun p => ⟨pow_ne_zero _ (hp p).ne_zero⟩
  let E : ZMod q ≃+* (∀ p : P, ZMod ((p : ℕ) ^ K p)) := ZMod.equivPi q (NeZero.ne q)
  let χ : AddChar (∀ p : P, ZMod ((p : ℕ) ^ K p)) ℂ :=
    (ZMod.stdAddChar.mulShift (a : ZMod q)).compAddMonoidHom E.symm.toAddMonoidHom
  let F : ∀ p : P, ZMod ((p : ℕ) ^ K p) → ℂ := fun p z =>
    localSieveWeight p W V b (ZMod.castHom (dvd_pow_self (p : ℕ) (hk p).ne') (ZMod p) z)
  let ψ : ∀ p : P, AddChar (ZMod ((p : ℕ) ^ K p)) ℂ := fun p =>
    { toFun := fun z => χ (Pi.single p z)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by intro z w; rw [Pi.single_add, AddChar.map_add_eq_mul] }
  have haunit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hψ (p : P) : Function.Injective (ψ p) := by
    intro z w he
    have h1 := ZMod.injective_stdAddChar he
    have h2 := haunit.mul_right_injective h1
    have h3 := E.symm.injective h2
    simpa using congrFun h3 p
  have hbound (p : P) : ‖∑ z : ZMod ((p : ℕ) ^ K p), F p z * χ (Pi.single p z)‖ ≤
      (K p : ℝ) + 1 :=
    localSieveWeight_prime_power_bound (hk p) W V b (ψ p) (hψ p)
  have hsum : compositeSieveSum q W V b a =
      ∑ y : ∀ p : P, ZMod ((p : ℕ) ^ K p), (∏ p : P, F p (y p)) * χ y := by
    unfold compositeSieveSum
    apply Fintype.sum_equiv E.toEquiv
    intro x
    have hweights : (∏ p : P, localSieveWeight p W V b (x.val : ZMod p)) =
        ∏ p : P, F p (E x p) := by
      apply prod_congr rfl
      intro p _
      congr 1
      let π : ZMod q →+* ZMod p := ZMod.castHom (Nat.dvd_of_mem_primeFactors p.property) (ZMod p)
      let ρ : ZMod ((p : ℕ) ^ K p) →+* ZMod p :=
        ZMod.castHom (dvd_pow_self (p : ℕ) (hk p).ne') (ZMod p)
      let ev := Pi.evalRingHom (fun p : P => ZMod ((p : ℕ) ^ K p)) p
      have hmaps : π = ρ.comp (ev.comp E.toRingHom) := Subsingleton.elim _ _
      have hx := DFunLike.congr_fun hmaps x
      change ZMod.cast x = ZMod.cast (E x p) at hx
      simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using hx
    rw [hweights]
    change (∏ p : P, F p (E x p)) * ZMod.stdAddChar ((a : ZMod q) * x) =
      (∏ p : P, F p (E x p)) * ZMod.stdAddChar ((a : ZMod q) * E.symm (E x))
    rw [E.symm_apply_apply]
  rw [hsum]
  calc
    _ ≤ ∏ p : P, ((K p : ℝ) + 1) := pi_weighted_character_bound χ F _ hbound
    _ = (q.divisors.card : ℝ) := by
      rw [Nat.card_divisors (NeZero.ne q)]
      push_cast
      exact Finset.prod_coe_sort q.primeFactors (fun p : ℕ => (q.factorization p : ℝ) + 1)

example : ‖compositeSieveSum 15 1 1 0 1‖ ≤ 4 := by
  have h := compositeSieveSum_norm_le_divisors 15 1 1 0 1 (by decide)
  have hc : (Nat.divisors 15).card = 4 := by decide
  simpa only [hc, Nat.cast_ofNat] using h

#print axioms compositeSieveSum_norm_le_divisors

end LeanLab.Teravainen2016
