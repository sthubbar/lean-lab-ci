import Mathlib

/-!
P0045 preprint page 6 and journal page 775, the Davenport Chapter 5 classification.
This is a narrow port of the proved argument in
LeanLab/LanguascoPintzZaccagnini2007/Decomp481b.lean on main 126fcb0e92.
Importing that file also imports a historical LPZ2007 model with conflicting names.
Only the character factorization proof is reused here. No cited analytic input occurs.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Conductor637

open Finset Real

/-- P0045 page 6, the product of the distinct odd prime divisors. -/
noncomputable def oddPart (r : ℕ) : ℕ :=
  ∏ p ∈ r.primeFactors.filter (fun p => 2 < p), p

/-- Standard: if `x ^ 2 = 0` then `(1 + x) ^ n = 1 + n * x`. -/
private theorem one_add_pow {R : Type*} [CommRing R] {x : R} (hx : x ^ 2 = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + (n : R) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast; linear_combination (n : R) * hx

/-- Davenport Chapter 5, standard: a character factors through `d ∣ r` as soon as it is
trivial on every unit `1 + k d` of `ZMod r`. -/
private theorem factors {r d : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hd : d ∣ r)
    (h : ∀ k : ℕ, IsUnit ((1 : ZMod r) + (k : ZMod r) * (d : ZMod r)) →
      χ (1 + (k : ZMod r) * (d : ZMod r)) = 1) : χ.FactorsThrough d := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have hcast : (ZMod.castHom hd (ZMod d)) ((u : ZMod r) - 1) = 0 := by
    have := congrArg Units.val hu
    rw [ZMod.unitsMap_val] at this
    rw [map_sub, map_one, ZMod.castHom_apply, this, Units.val_one, sub_self]
  set x : ZMod r := (u : ZMod r) - 1 with hxdef
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hcast
  obtain ⟨k, hk⟩ := hcast
  have hu' : (u : ZMod r) = 1 + (k : ZMod r) * (d : ZMod r) := by
    have : x = ((d * k : ℕ) : ZMod r) := by rw [← hk, ZMod.natCast_zmod_val]
    rw [Nat.cast_mul] at this
    linear_combination this
  apply Units.ext
  rw [MulChar.coe_toUnitHom, Units.val_one, hu']
  exact h k (hu' ▸ u.isUnit)

/-- A real value of a character on a unit has `y ^ φ r = 1`. -/
private theorem pow_totient {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) {y : ZMod r}
    (hy : IsUnit y) : χ y ^ Nat.totient r = 1 := by
  obtain ⟨v, rfl⟩ := hy
  rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]

private theorem real {r : ℕ} {χ : DirichletCharacter ℂ r}
    (hreal : ∀ a, (χ a).im = 0) (a : ZMod r) : χ a = ((χ a).re : ℂ) :=
  Complex.ext (by simp) (by simp [hreal a])

/-- Case of an odd prime square: a real character factors through `r / p`. -/
private theorem odd_sq {p t : ℕ} (hp : p.Prime) (hodd : Odd p) (ht : 1 ≤ t)
    (χ : DirichletCharacter ℂ (p * p * t)) (hreal : ∀ a, (χ a).im = 0) :
    χ.FactorsThrough (p * t) := by
  have : NeZero (p * p * t) := ⟨by positivity [hp.pos]⟩
  refine factors χ ⟨p, by ring⟩ fun k hk => ?_
  set x : ZMod (p * p * t) := (k : ZMod (p * p * t)) * ((p * t : ℕ) : ZMod (p * p * t))
  have h0 : ((p * p * t : ℕ) : ZMod (p * p * t)) = 0 := ZMod.natCast_self _
  have hx2 : x ^ 2 = 0 := by
    have : x ^ 2 = (k : ZMod (p * p * t)) ^ 2 * (t : ZMod (p * p * t)) *
        ((p * p * t : ℕ) : ZMod (p * p * t)) := by simp only [x]; push_cast; ring
    rw [this, h0, mul_zero]
  have hpx : (p : ZMod (p * p * t)) * x = 0 := by
    have : (p : ZMod (p * p * t)) * x = (k : ZMod (p * p * t)) *
        ((p * p * t : ℕ) : ZMod (p * p * t)) := by simp only [x]; push_cast; ring
    rw [this, h0, mul_zero]
  have hpow : (1 + x) ^ p = 1 := by rw [one_add_pow hx2, hpx, add_zero]
  have hy : (χ (1 + x)) ^ p = 1 := by rw [← map_pow, hpow, map_one]
  rw [real hreal] at hy ⊢
  have hre : (χ (1 + x)).re ^ p = 1 := by exact_mod_cast hy
  have habs : |(χ (1 + x)).re| = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (abs_nonneg _) hp.ne_zero, pow_abs, hre, abs_one]
  rcases abs_eq (zero_le_one) |>.mp habs with h | h
  · rw [h]; simp
  · rw [h, hodd.neg_one_pow] at hre; norm_num at hre

/-- Case `16 ∣ r`: a real character factors through `r / 2`. -/
private theorem sixteen {t : ℕ} (ht : 1 ≤ t)
    (χ : DirichletCharacter ℂ (16 * t)) (hreal : ∀ a, (χ a).im = 0) :
    χ.FactorsThrough (8 * t) := by
  have : NeZero (16 * t) := ⟨by omega⟩
  refine factors χ ⟨2, by ring⟩ fun k hk => ?_
  have h0 : ((16 * t : ℕ) : ZMod (16 * t)) = 0 := ZMod.natCast_self _
  set w : ZMod (16 * t) := 1 + (k : ZMod (16 * t)) * ((4 * t : ℕ) : ZMod (16 * t))
  have hsq : (1 : ZMod (16 * t)) + (k : ZMod (16 * t)) * ((8 * t : ℕ) : ZMod (16 * t)) = w ^ 2 := by
    have : w ^ 2 = 1 + (k : ZMod (16 * t)) * ((8 * t : ℕ) : ZMod (16 * t)) +
        (k : ZMod (16 * t)) ^ 2 * (t : ZMod (16 * t)) * ((16 * t : ℕ) : ZMod (16 * t)) := by
      simp only [w]; push_cast; ring
    rw [this, h0, mul_zero, add_zero]
  have htot := pow_totient χ hk
  rw [hsq, map_pow, real hreal w] at htot ⊢
  have hn : Nat.totient (16 * t) ≠ 0 := by
    rw [Ne, Nat.totient_eq_zero]; omega
  have hre : ((χ w).re ^ 2) ^ Nat.totient (16 * t) = 1 := by exact_mod_cast htot
  rw [pow_eq_one_iff_of_nonneg (sq_nonneg _) hn] at hre
  rw [← Complex.ofReal_pow, hre, Complex.ofReal_one]

/-- Case `r = 2 m` with `m` odd: every character factors through `m`. -/
private theorem two_odd {m : ℕ} (hm : Odd m) (χ : DirichletCharacter ℂ (2 * m)) :
    χ.FactorsThrough m := by
  have : NeZero (2 * m) := ⟨by obtain ⟨j, rfl⟩ := hm; omega⟩
  refine factors χ ⟨2, by ring⟩ fun k hk => ?_
  have h2 : (2 : ℕ) ∣ 2 * m := ⟨m, rfl⟩
  have hk2 := hk.map (ZMod.castHom h2 (ZMod 2))
  rw [map_add, map_one, map_mul, map_natCast, map_natCast] at hk2
  have hm1 : ((m : ℕ) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, Nat.odd_iff.mp hm, Nat.cast_one]
  rw [hm1, mul_one] at hk2
  have hkz : ((k : ℕ) : ZMod 2) = 0 := by
    revert hk2; generalize ((k : ℕ) : ZMod 2) = z; revert z; decide
  rw [ZMod.natCast_eq_zero_iff] at hkz
  obtain ⟨j, rfl⟩ := hkz
  have : ((2 * j : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)) =
      (j : ZMod (2 * m)) * ((2 * m : ℕ) : ZMod (2 * m)) := by push_cast; ring
  rw [this, ZMod.natCast_self, mul_zero, add_zero, map_one]


private theorem two_odd' {r m : ℕ} (hm : Odd m) (hr : r = 2 * m)
    (χ : DirichletCharacter ℂ r) : χ.FactorsThrough m := by
  subst hr; exact two_odd hm χ

/-- P0045 page 6, first proof paragraph following display 10.
Davenport Chapter 5 supplies the classification of real primitive conductors.
Proved here from Mathlib's factor through criterion, by the three standard cases. -/
theorem classification :
    ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      χ.IsPrimitive → (∀ a, (χ a).im = 0) →
        r = oddPart r ∨ r = 4 * oddPart r ∨ r = 8 * oddPart r := by
  intro r hr χ hprim hreal
  have : NeZero r := ⟨by omega⟩
  have hr0 : r ≠ 0 := by omega
  have hle : ∀ d, χ.FactorsThrough d → r ≤ d := fun d hd => by
    have h := Nat.sInf_le (show d ∈ χ.conductorSet from hd)
    rwa [← DirichletCharacter.conductor, hprim] at h
  have hodd : ∀ p, p.Prime → 2 < p → ¬ p * p ∣ r := by
    rintro p hp h2 ⟨t, rfl⟩
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp at hr
      · exact h
    have := hle _ (odd_sq hp (hp.eq_two_or_odd'.resolve_left (by omega)) ht1 χ hreal)
    nlinarith [hp.two_le]
  have h16 : ¬ 16 ∣ r := by
    rintro ⟨t, rfl⟩
    have := hle _ (sixteen (by omega) χ hreal)
    omega
  have hoodd : ¬ 2 ∣ oddPart r := by
    intro h
    obtain ⟨p, hp, h2p⟩ := (Nat.prime_two.prime.dvd_finset_prod_iff _).mp h
    rw [Finset.mem_filter] at hp
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Nat.prime_of_mem_primeFactors hp.1)).mp h2p
    omega
  have hdecomp : r = 2 ^ r.factorization 2 * oddPart r := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hr0]
    rw [← Finset.prod_filter_mul_prod_filter_not r.primeFactors (fun p => 2 < p), mul_comm]
    congr 1
    · rw [Finset.prod_subset (s₁ := r.primeFactors.filter (fun p => ¬ 2 < p)) (s₂ := {2})]
      · simp
      · intro p hp
        rw [Finset.mem_filter] at hp
        have := (Nat.prime_of_mem_primeFactors hp.1).two_le
        simp only [Finset.mem_singleton]; omega
      · intro p hp hnot
        rw [Finset.mem_singleton] at hp
        subst hp
        have hn : (2 : ℕ) ∉ r.primeFactors := fun h => hnot (Finset.mem_filter.mpr ⟨h, by omega⟩)
        rw [← Nat.support_factorization] at hn
        rw [Finsupp.notMem_support_iff.mp hn, pow_zero]
    · unfold oddPart
      apply Finset.prod_congr rfl
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp.1
      have h1 : 1 ≤ r.factorization p :=
        (hpp.dvd_iff_one_le_factorization hr0).mp (Nat.dvd_of_mem_primeFactors hp.1)
      have h2 : r.factorization p < 2 := by
        by_contra hc
        push Not at hc
        exact hodd p hpp hp.2 (by rw [← pow_two]; exact (hpp.pow_dvd_iff_le_factorization hr0).mpr hc)
      rw [show r.factorization p = 1 by omega, pow_one]
  have hf3 : r.factorization 2 ≤ 3 := by
    by_contra hc
    push Not at hc
    exact h16 (by
      have := (Nat.prime_two.pow_dvd_iff_le_factorization hr0 (k := 4)).mpr hc
      simpa using this)
  have hf1 : r.factorization 2 ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hdecomp
    have := hle _ (two_odd' (Nat.odd_iff.mpr (by omega)) hdecomp χ)
    omega
  interval_cases h : r.factorization 2
  · left; simpa using hdecomp
  · exact absurd rfl hf1
  · right; left; simpa using hdecomp
  · right; right; simpa using hdecomp

#print axioms oddPart
#print axioms one_add_pow
#print axioms factors
#print axioms pow_totient
#print axioms real
#print axioms odd_sq
#print axioms sixteen
#print axioms two_odd
#print axioms two_odd'
#print axioms classification

end LeanLab.LPZ2007.Conductor637
