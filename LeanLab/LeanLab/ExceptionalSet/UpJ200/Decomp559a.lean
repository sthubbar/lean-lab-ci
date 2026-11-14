import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
P0082 page 363 case ii c before display 22.
Local square roots and primitive real conductor descent.
Source: https://doi.org/10.5802/aif.1621
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp559a

/-- P0082 page 363 case ii c. A real character is trivial on unit squares. -/
theorem real_on_square (r : ℕ) (χ : DirichletCharacter ℂ r)
    (hreal : χ ^ 2 = 1) (x : (ZMod r)ˣ) : χ ((x : ZMod r) ^ 2) = 1 := by
  rw [map_pow, ← MulChar.pow_apply_coe, hreal, MulChar.one_apply_coe]

/-- P0082 page 363 case ii c. A square root of a unit is a unit. -/
theorem unit_square_of_ring_square (r : ℕ) (x : (ZMod r)ˣ)
    (h : IsSquare (x : ZMod r)) : IsSquare x := by
  obtain ⟨y, hy⟩ := h
  have hyunit : IsUnit y := isUnit_of_mul_isUnit_left (hy ▸ x.isUnit)
  refine ⟨hyunit.unit, ?_⟩
  apply Units.ext
  simpa only [Units.val_mul, hyunit.unit_spec] using hy

/-- P0082 page 363 case ii c. Square reduction kernels force character descent. -/
theorem real_factors_of_square_kernel (r d : ℕ) [NeZero r]
    (hd : d ∣ r) (χ : DirichletCharacter ℂ r) (hreal : χ ^ 2 = 1)
    (hsquare : ∀ x : (ZMod r)ˣ, ZMod.unitsMap hd x = 1 → IsSquare x) :
    χ.FactorsThrough d := by
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
  intro x hx
  obtain ⟨y, hy⟩ := hsquare x hx
  apply Units.ext
  change χ (x : ZMod r) = 1
  rw [hy, Units.val_mul, ← pow_two]
  exact real_on_square r χ hreal y

/-- P0082 page 363 case ii c. A primitive character cannot descend to a proper divisor. -/
theorem primitive_level_eq_of_factors (r d : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r) (hprimitive : χ.IsPrimitive)
    (hfactor : χ.FactorsThrough d) : r = d := by
  apply Nat.dvd_antisymm
  · have hc := χ.conductor_dvd_of_mem_conductorSet hfactor
    change χ.conductor = r at hprimitive
    rwa [hprimitive] at hc
  · exact hfactor.dvd

/-- P0082 page 363 case ii c. Kernel elements have an integral increment. -/
theorem kernel_integer_increment (r d : ℕ) [NeZero r] (hd : d ∣ r)
    (x : (ZMod r)ˣ) (hx : ZMod.unitsMap hd x = 1) :
    ∃ t : ℤ, (x : ZMod r) = 1 + (d : ZMod r) * t := by
  have hcast : ((x : ZMod r).val : ZMod d) = 1 := by
    have he := congrArg (fun z : (ZMod d)ˣ => (z : ZMod d)) hx
    rw [ZMod.unitsMap_val, ← ZMod.natCast_zmod_val (x : ZMod r), ZMod.cast_natCast hd] at he
    exact he
  have hdiv : (d : ℤ) ∣ 1 - ((x : ZMod r).val : ℤ) := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ 1 d).mp (by simpa using hcast)
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨-t, ?_⟩
  have he : ((x : ZMod r).val : ℤ) = 1 + (d : ℤ) * -t := by linarith
  have hc := congrArg (fun z : ℤ => (z : ZMod r)) he
  simpa using hc

/-- P0082 page 363 case ii c. Odd reduction kernels consist of squares. -/
theorem odd_kernel_square (r d p : ℕ) [NeZero r]
    (hr : r = p * d) (hp : Odd p) (hpd : p ∣ d)
    (x : (ZMod r)ˣ) (hx : ZMod.unitsMap (show d ∣ r by rw [hr]; exact dvd_mul_left d p) x = 1) :
    IsSquare x := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hpd
  obtain ⟨t, ht⟩ := kernel_integer_increment r d (by rw [hr]; exact dvd_mul_left d p) x hx
  apply unit_square_of_ring_square
  have hz : (p : ZMod r) * d = 0 := by rw [← Nat.cast_mul, ← hr]; exact ZMod.natCast_self r
  have hd2 : (d : ZMod r) ^ 2 = 0 := by
    calc
      _ = ((p : ZMod r) * d) * b := by rw [hb]; push_cast; ring
      _ = 0 := by rw [hz, zero_mul]
  have htwo : 2 * ((a : ZMod r) + 1) * d = d := by
    have hh : (p : ZMod r) = 2 * a + 1 := by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using congrArg (fun n : ℕ => (n : ZMod r)) ha
    rw [hh] at hz
    linear_combination hz
  refine ⟨1 + ((a : ZMod r) + 1) * d * t, ?_⟩
  rw [ht]
  linear_combination - (t : ZMod r) * htwo - (((a : ZMod r) + 1) * t) ^ 2 * hd2

/-- P0082 page 363 case ii c. The kernel above a multiple of eight consists of squares. -/
theorem two_kernel_square (r b : ℕ) [NeZero r] (hr : r = 16 * b)
    (x : (ZMod r)ˣ)
    (hx : ZMod.unitsMap (show 8 * b ∣ r by rw [hr]; exact ⟨2, by ring⟩) x = 1) :
    IsSquare x := by
  obtain ⟨t, ht⟩ := kernel_integer_increment r (8 * b) (by rw [hr]; exact ⟨2, by ring⟩) x hx
  apply unit_square_of_ring_square
  have hz : (16 : ZMod r) * b = 0 := by
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, ← hr]
    exact ZMod.natCast_self r
  refine ⟨1 + 4 * (b : ZMod r) * t, ?_⟩
  rw [ht]
  push_cast
  linear_combination - (b : ZMod r) * (t : ZMod r) ^ 2 * hz

/-- P0082 page 363 case ii c. An odd prime square cannot divide a primitive real conductor. -/
theorem primitive_odd_square_not_dvd (r : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r) (hprimitive : χ.IsPrimitive)
    (hreal : χ ^ 2 = 1) (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ¬ p * p ∣ r := by
  rintro ⟨b, hr⟩
  have hrd : r = p * (p * b) := by nlinarith [hr]
  have hd : p * b ∣ r := by rw [hr]; exact ⟨p, by ring⟩
  have hf := real_factors_of_square_kernel r (p * b) hd χ hreal
    (fun x hx => odd_kernel_square r (p * b) p hrd hodd (dvd_mul_right p b) x hx)
  have he := primitive_level_eq_of_factors r (p * b) χ hprimitive hf
  have hrpos : 0 < r := NeZero.pos r
  have hp2 := hp.two_le
  nlinarith

/-- P0082 page 363 case ii c. Sixteen cannot divide a primitive real conductor. -/
theorem primitive_sixteen_not_dvd (r : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r) (hprimitive : χ.IsPrimitive)
    (hreal : χ ^ 2 = 1) : ¬ 16 ∣ r := by
  rintro ⟨b, hr⟩
  have hd : 8 * b ∣ r := by rw [hr]; exact ⟨2, by ring⟩
  have hf := real_factors_of_square_kernel r (8 * b) hd χ hreal
    (fun x hx => two_kernel_square r b hr x hx)
  have he := primitive_level_eq_of_factors r (8 * b) χ hprimitive hf
  have hrpos : 0 < r := NeZero.pos r
  omega

/-- P0082 page 363 case ii c. The odd conductor part is squarefree. -/
theorem real_primitive_odd_part (r : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r) (hprimitive : χ.IsPrimitive)
    (hreal : χ ^ 2 = 1) (hnonprincipal : χ ≠ 1)
    (k u : ℕ) (hr : r = 2 ^ k * u) (hu : Odd u) :
    Squarefree u := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hpu
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    exact hu.not_two_dvd_nat (dvd_trans (dvd_mul_right 2 2) hpu)
  apply primitive_odd_square_not_dvd r χ hprimitive hreal p hp (hp.odd_of_ne_two hp2)
  exact dvd_trans hpu (by rw [hr]; exact dvd_mul_left u (2 ^ k))

/-- P0082 page 363 case ii c. The two conductor exponent is at most three. -/
theorem real_primitive_two_part (r : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r) (hprimitive : χ.IsPrimitive)
    (hreal : χ ^ 2 = 1) (hnonprincipal : χ ≠ 1)
    (k u : ℕ) (hr : r = 2 ^ k * u) (hu : Odd u) :
    k ≤ 3 := by
  by_contra hk
  have hp : (2 : ℕ) ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
  apply primitive_sixteen_not_dvd r χ hprimitive hreal
  have hd := dvd_trans hp (dvd_mul_right (2 ^ k) u)
  simpa only [show (2 : ℕ) ^ 4 = 16 by norm_num, hr] using hd

end LeanLab.ExceptionalSet.UpJ200.Decomp559a
