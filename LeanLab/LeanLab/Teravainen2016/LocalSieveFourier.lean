/-
P0076 Lemma 5.4, pages 19 to 20. Local sieve bounds for transported primitive characters.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.ProductCharacter

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The one or two local exclusions of display 5.5 as a complex indicator. -/
noncomputable def localSieveWeight (p : ℕ) (W V b : ℤ) (y : ZMod p) : ℂ :=
  if (W : ZMod p) * V * y + b ≠ 0 ∧
      (p % 4 = 3 ∧ p ≠ 3 → (W : ZMod p) * V * y + b ≠ 1) then 1 else 0

/-- Any nontrivial prime field character obeys the affine forbidden residue bound. -/
theorem affine_addChar_bound {p : ℕ} [Fact p.Prime]
    (c b : ZMod p) (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 0) (F : Finset (ZMod p)) :
    ‖∑ x ∈ (univ : Finset (ZMod p)).filter (fun x => c * x + b ∉ F), ψ x‖ ≤ F.card := by
  by_cases hc : c = 0
  · subst c
    by_cases hb : b ∈ F
    · simp [hb]
    · simp only [zero_mul, zero_add, hb, not_false_eq_true, filter_true]
      have hs : ∑ x, ψ x = 0 := by simp [AddChar.sum_eq_ite, hψ]
      rw [hs, norm_zero]
      positivity
  · let T := (univ : Finset (ZMod p)).filter (fun x => c * x + b ∈ F)
    have he : (univ : Finset (ZMod p)).filter (fun x => c * x + b ∉ F) = Tᶜ := by
      ext x
      simp [T]
    rw [he]
    exact (addChar_complement_bound ψ hψ T).trans
      (by exact_mod_cast affine_forbidden_preimage_card c b hc F)

/-- The local prime sieve costs at most two for every nontrivial transported character. -/
theorem localSieveWeight_character_bound {p : ℕ} [Fact p.Prime]
    (W V b : ℤ) (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 0) :
    ‖∑ y : ZMod p, localSieveWeight p W V b y * ψ y‖ ≤ 2 := by
  by_cases hp : p % 4 = 3 ∧ p ≠ 3
  · have h := affine_addChar_bound ((W : ZMod p) * (V : ZMod p)) (b : ZMod p) ψ hψ ({0, 1} : Finset (ZMod p))
    have he : (∑ y : ZMod p, localSieveWeight p W V b y * ψ y) =
        ∑ y ∈ (univ : Finset (ZMod p)).filter
          (fun y => (W : ZMod p) * V * y + b ∉ ({0, 1} : Finset (ZMod p))), ψ y := by
      simp only [sum_filter]
      apply sum_congr rfl
      intro y _
      simp [localSieveWeight, hp]
    rw [he]
    exact h.trans (by exact_mod_cast (card_le_two : #({0, 1} : Finset (ZMod p)) ≤ 2))
  · have h := affine_addChar_bound ((W : ZMod p) * (V : ZMod p)) (b : ZMod p) ψ hψ ({0} : Finset (ZMod p))
    have he : (∑ y : ZMod p, localSieveWeight p W V b y * ψ y) =
        ∑ y ∈ (univ : Finset (ZMod p)).filter
          (fun y => (W : ZMod p) * V * y + b ∉ ({0} : Finset (ZMod p))), ψ y := by
      simp only [sum_filter]
      apply sum_congr rfl
      intro y _
      simp [localSieveWeight, hp]
    rw [he]
    exact h.trans (by simp)

/-- Higher powers vanish for every injective transported character. -/
theorem localSieveWeight_prime_power_zero {p k : ℕ} [Fact p.Prime] (hk : 2 ≤ k)
    (W V b : ℤ) (ψ : AddChar (ZMod (p ^ k)) ℂ) (hψ : Function.Injective ψ) :
    ∑ x : ZMod (p ^ k),
      localSieveWeight p W V b (ZMod.castHom (dvd_pow_self p (by omega : k ≠ 0)) (ZMod p) x) * ψ x = 0 := by
  apply lifted_weight_addChar_sum_eq_zero (Fact.out : p.Prime).pos _ _ ψ hψ
    (localSieveWeight p W V b)
  calc
    p = p ^ 1 := (pow_one p).symm
    _ < p ^ k := (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mpr (by omega)

/-- Every positive prime power factor costs at most its divisor count. -/
theorem localSieveWeight_prime_power_bound {p k : ℕ} [Fact p.Prime] (hk : 0 < k)
    (W V b : ℤ) (ψ : AddChar (ZMod (p ^ k)) ℂ) (hψ : Function.Injective ψ) :
    ‖∑ x : ZMod (p ^ k),
      localSieveWeight p W V b (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x) * ψ x‖ ≤ k + 1 := by
  by_cases hk1 : k = 1
  · subst k
    let E : ZMod (p ^ 1) ≃+* ZMod p := ZMod.ringEquivCongr (Nat.pow_one p)
    let ψp : AddChar (ZMod p) ℂ := ψ.compAddMonoidHom E.symm.toAddMonoidHom
    have hinj : Function.Injective ψp := hψ.comp E.symm.injective
    have hne : ψp ≠ 0 := by
      intro he
      have h10 : (1 : ZMod p) = 0 := hinj (a₁ := 1) (a₂ := 0) (by simp [he])
      exact one_ne_zero h10
    have hs : (∑ x : ZMod (p ^ 1),
        localSieveWeight p W V b (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x) * ψ x) =
        ∑ y : ZMod p, localSieveWeight p W V b y * ψp y := by
      apply Fintype.sum_equiv E.toEquiv
      intro x
      have hmaps : ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) = E.toRingHom :=
        Subsingleton.elim _ _
      rw [hmaps]
      change localSieveWeight p W V b (E x) * ψ x =
        localSieveWeight p W V b (E x) * ψ (E.symm (E x))
      rw [E.symm_apply_apply]
    rw [hs]
    convert localSieveWeight_character_bound W V b ψp hne using 1 <;> norm_num
  · rw [localSieveWeight_prime_power_zero (by omega) W V b ψ hψ, norm_zero]
    positivity

example : ‖∑ y : ZMod 7, localSieveWeight 7 1 1 0 y * ZMod.stdAddChar y‖ ≤ 2 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply localSieveWeight_character_bound
  intro he
  have hz : (1 : ZMod 7) = 0 := ZMod.injective_stdAddChar (by simp [he])
  exact one_ne_zero hz

#print axioms affine_addChar_bound
#print axioms localSieveWeight_character_bound
#print axioms localSieveWeight_prime_power_zero
#print axioms localSieveWeight_prime_power_bound

end LeanLab.Teravainen2016
