/-
P0095 Lu 2010, page 2379 equation 63, induced Gauss factors.
CODEX task47, unit U-8100. AI wrote this Lean code. Binary Goldbach is open.
Translation by a nonzero additive period forces a Gauss sum to vanish.
A nilpotent shift killed at the inducing level gives such a period.
-/
import Mathlib

namespace LeanLab.ExceptionalSet.Lu2010Induced
open Finset ZMod DirichletCharacter

variable {q r : ℕ} [NeZero q]

/-- A nonzero additive period of the character forces its primitive additive Gauss sum to zero. -/
theorem gauss_zero_of_period (χ : DirichletCharacter ℂ q) {d : ZMod q} (hd : d ≠ 0)
    (hperiod : ∀ a : ZMod q, χ (a + d) = χ a) :
    gaussSum χ stdAddChar = 0 := by
  have hs : (∑ a : ZMod q, χ (a + d) * stdAddChar (a + d)) =
      ∑ a : ZMod q, χ a * stdAddChar a :=
    Fintype.sum_equiv (Equiv.addRight d) _ _ (fun a => rfl)
  have hmul : gaussSum χ stdAddChar * stdAddChar d = gaussSum χ stdAddChar := by
    unfold gaussSum
    rw [sum_mul]
    calc (∑ a : ZMod q, χ a * stdAddChar a * stdAddChar d)
        = ∑ a : ZMod q, χ (a + d) * stdAddChar (a + d) := by
          apply sum_congr rfl
          intro a _
          rw [hperiod, AddChar.map_add_eq_mul]
          ring
      _ = _ := hs
  have hne : stdAddChar d ≠ 1 := by
    intro he
    apply hd
    apply injective_stdAddChar
    simpa using he
  have hz : gaussSum χ stdAddChar * (stdAddChar d - 1) = 0 := by
    linear_combination hmul
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hne)

omit [NeZero q] in
/-- Nilpotent shifts do not change unit status. -/
theorem isUnit_add_nilpotent (a : ZMod q) {d : ZMod q} (hd : IsNilpotent d) :
    IsUnit (a + d) ↔ IsUnit a := by
  constructor
  · intro ha
    have ht := hd.neg.isUnit_add_left_of_commute ha (Commute.all _ _)
    simpa using ht
  · intro ha
    exact hd.isUnit_add_left_of_commute ha (Commute.all _ _)

/-- A nilpotent shift that vanishes at the inducing level is a period of the induced character. -/
theorem induced_period (hrq : r ∣ q) (χ : DirichletCharacter ℂ r) {d : ZMod q}
    (hnil : IsNilpotent d) (hcast : ZMod.castHom hrq (ZMod r) d = 0) (a : ZMod q) :
    changeLevel hrq χ (a + d) = changeLevel hrq χ a := by
  by_cases ha : IsUnit a
  · have had : IsUnit (a + d) := (isUnit_add_nilpotent a hnil).mpr ha
    have h1 := changeLevel_eq_cast_of_dvd χ hrq ha.unit
    have h2 := changeLevel_eq_cast_of_dvd χ hrq had.unit
    rw [ha.unit_spec] at h1
    rw [had.unit_spec] at h2
    rw [h1, h2]
    change χ (ZMod.castHom hrq (ZMod r) (a + d)) = χ (ZMod.castHom hrq (ZMod r) a)
    rw [map_add, hcast, add_zero]
  · have had : ¬ IsUnit (a + d) := fun h => ha ((isUnit_add_nilpotent a hnil).mp h)
    rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ had]

/-- The induced Gauss sum vanishes in the presence of such a nonzero shift. -/
theorem induced_gauss_zero (hrq : r ∣ q) (χ : DirichletCharacter ℂ r) {d : ZMod q}
    (hd : d ≠ 0) (hnil : IsNilpotent d) (hcast : ZMod.castHom hrq (ZMod r) d = 0) :
    gaussSum (changeLevel hrq χ) stdAddChar = 0 :=
  gauss_zero_of_period _ hd (induced_period hrq χ hnil hcast)

/-- A shared prime of the inducing level and quotient gives a vanishing Gauss sum. -/
theorem induced_gauss_zero_of_shared_prime (hrq : r ∣ q) (χ : DirichletCharacter ℂ r)
    {p k : ℕ} (hp : 1 < p) (hpr : p ∣ r) (hk : 0 < k) (hq : q = r * p * k) :
    gaussSum (changeLevel hrq χ) stdAddChar = 0 := by
  have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hrq (NeZero.pos q)
  have hd0 : 0 < r * k := Nat.mul_pos hr0 hk
  have hdq : r * k < q := by rw [hq]; nlinarith
  have hne : ((r * k : ℕ) : ZMod q) ≠ 0 := by
    intro he
    have hdiv := (ZMod.natCast_eq_zero_iff (r * k) q).mp he
    have := Nat.le_of_dvd hd0 hdiv
    omega
  have hnil : IsNilpotent (((r * k : ℕ) : ZMod q)) := by
    refine ⟨2, ?_⟩
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    obtain ⟨t, ht⟩ := hpr
    refine ⟨t * k, ?_⟩
    rw [hq, ht]
    ring
  apply induced_gauss_zero hrq χ hne hnil
  rw [map_natCast, ZMod.natCast_eq_zero_iff]
  exact dvd_mul_right r k

/-- No coprimality between the conductor and quotient is needed for the vanishing direction. -/
theorem induced_gauss_zero_of_not_coprime (hrq : r ∣ q) (χ : DirichletCharacter ℂ r)
    (hcop : ¬ r.Coprime (q / r)) :
    gaussSum (changeLevel hrq χ) stdAddChar = 0 := by
  obtain ⟨p, hp, hpr, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  obtain ⟨k, hk⟩ := hpm
  have hq : q = r * p * k := by
    have hmul := Nat.mul_div_cancel' hrq
    rw [hk] at hmul
    nlinarith
  have hk0 : 0 < k := by
    by_contra h
    have hkz : k = 0 := by omega
    rw [hkz, mul_zero] at hq
    exact NeZero.ne q hq
  exact induced_gauss_zero_of_shared_prime hrq χ hp.one_lt hpr hk0 hq

/-- A nonzero nilpotent shift kills the principal Gauss sum. -/
theorem principal_gauss_zero_of_nilpotent {d : ZMod q} (hd : d ≠ 0) (hnil : IsNilpotent d) :
    gaussSum (1 : DirichletCharacter ℂ q) stdAddChar = 0 := by
  have h := induced_gauss_zero (r := 1) (Nat.one_dvd q) (1 : DirichletCharacter ℂ 1)
    hd hnil (by exact Subsingleton.elim _ _)
  simpa using h

/-- A repeated prime factor gives an explicit nonzero nilpotent shift. -/
theorem principal_gauss_zero_of_prime_square {p : ℕ} (hp : p.Prime) (hdiv : p * p ∣ q) :
    gaussSum (1 : DirichletCharacter ℂ q) stdAddChar = 0 := by
  obtain ⟨k, hk⟩ := hdiv
  have hk0 : 0 < k := by
    by_contra h
    have hkz : k = 0 := by omega
    rw [hkz, mul_zero] at hk
    exact NeZero.ne q hk
  have hd0 : 0 < p * k := Nat.mul_pos hp.pos hk0
  have hdq : p * k < q := by rw [hk]; nlinarith [hp.one_lt]
  have hne : ((p * k : ℕ) : ZMod q) ≠ 0 := by
    intro he
    have hdiv := (ZMod.natCast_eq_zero_iff (p * k) q).mp he
    have := Nat.le_of_dvd hd0 hdiv
    omega
  have hnil : IsNilpotent (((p * k : ℕ) : ZMod q)) := by
    refine ⟨2, ?_⟩
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    refine ⟨k, ?_⟩
    rw [hk]
    ring
  exact principal_gauss_zero_of_nilpotent hne hnil

/-- The principal Gauss sum vanishes at every nonsquarefree nonzero modulus. -/
theorem principal_gauss_zero_of_not_squarefree (hsq : ¬ Squarefree q) :
    gaussSum (1 : DirichletCharacter ℂ q) stdAddChar = 0 := by
  have h := mt Nat.squarefree_iff_prime_squarefree.mpr hsq
  push Not at h
  obtain ⟨p, hp, hdiv⟩ := h
  exact principal_gauss_zero_of_prime_square hp hdiv

/-- The shift 3 modulo 9 is nonzero and square zero, and the induced principal sum vanishes. -/
theorem instance_mod_nine :
    (3 : ZMod 9) ≠ 0 ∧ (3 : ZMod 9) ^ 2 = 0 ∧
      gaussSum (changeLevel (show 3 ∣ 9 by norm_num) (1 : DirichletCharacter ℂ 3)) stdAddChar = 0 := by
  refine ⟨by decide, by decide, ?_⟩
  exact induced_gauss_zero_of_shared_prime (by norm_num) _
    (p := 3) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end LeanLab.ExceptionalSet.Lu2010Induced

#print axioms LeanLab.ExceptionalSet.Lu2010Induced.gauss_zero_of_period
#print axioms LeanLab.ExceptionalSet.Lu2010Induced.isUnit_add_nilpotent
#print axioms LeanLab.ExceptionalSet.Lu2010Induced.induced_period
#print axioms LeanLab.ExceptionalSet.Lu2010Induced.induced_gauss_zero
#print axioms LeanLab.ExceptionalSet.Lu2010Induced.induced_gauss_zero_of_shared_prime
#print axioms LeanLab.ExceptionalSet.Lu2010Induced.induced_gauss_zero_of_not_coprime
#print axioms LeanLab.ExceptionalSet.Lu2010Induced.principal_gauss_zero_of_nilpotent
#print axioms LeanLab.ExceptionalSet.Lu2010Induced.principal_gauss_zero_of_prime_square
#print axioms LeanLab.ExceptionalSet.Lu2010Induced.principal_gauss_zero_of_not_squarefree
#print axioms LeanLab.ExceptionalSet.Lu2010Induced.instance_mod_nine
