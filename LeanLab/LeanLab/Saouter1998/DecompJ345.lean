import Mathlib
import LeanLab.Saouter1998.Lemma1
import LeanLab.Saouter1998.Theorem2

namespace LeanLab.Saouter1998.BLS

/-- LEAF 864: The case F = 0 is excluded by N < 2F^3. Statement repaired 2026-10-31 by the
architect, run 20261031T2235Z-16111: without `hN_lt` it was false at every R, see
`LeanLab.Common.FalseLeafAudit20261031.leaf_F_zero_old_false`. -/
theorem leaf_F_zero (R : ℕ) (hN_lt : R * 0 + 1 < 2 * 0 ^ 3) :
    ((R * 0 + 1).Prime ↔
      R / (2 * 0) = 0 ∨ ¬ IsSquare (((R % (2 * 0) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * 0) : ℕ) : ℤ))) := by
  exfalso
  simp at hN_lt
/-- LEAF 864: Fermat and gcd conditions imply prime factors are 1 mod F -/
theorem leaf_pock (F R : ℕ) (a : ℤ) (hOdd : Odd (R * F + 1)) (hF : Even F) (hCoprime : Nat.Coprime R F)
    (hFermat : (a : ZMod (R * F + 1)) ^ (R * F) = 1)
    (hgcd : ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ (R * F / p) - 1) (R * F + 1) = 1) :
    ∀ p : ℕ, p.Prime → p ∣ R * F + 1 → ∃ k : ℕ, p = k * F + 1 := by
  intro p hp hpN
  have : Fact p.Prime := ⟨hp⟩
  set c : ZMod p := (a : ZMod p) ^ R with hc
  have hpow : c ^ F = 1 := by
    have h := congrArg (ZMod.castHom hpN (ZMod p)) hFermat
    simp only [map_pow, map_intCast, map_one] at h
    rw [hc, ← pow_mul]; exact h
  have hd : ∀ q : ℕ, q.Prime → q ∣ F → c ^ (F / q) ≠ 1 := by
    intro q hq hqF hcq
    have hdiv : R * (F / q) = R * F / q := (Nat.mul_div_assoc R hqF).symm
    have h1 : (a : ZMod p) ^ (R * F / q) = 1 := by
      rw [← hdiv, pow_mul, ← hc]; exact hcq
    have h2 : ((a ^ (R * F / q) - 1 : ℤ) : ZMod p) = 0 := by
      push_cast; rw [h1, sub_self]
    have hp_dvd_a : (p : ℤ) ∣ a ^ (R * F / q) - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h2
    have hp_dvd_N : (p : ℤ) ∣ (R * F + 1 : ℕ) := Int.natCast_dvd_natCast.mpr hpN
    have hp_dvd_gcd : (p : ℤ) ∣ (Int.gcd (a ^ (R * F / q) - 1) (R * F + 1) : ℤ) :=
      Int.dvd_coe_gcd hp_dvd_a hp_dvd_N
    have h_gcd_one := hgcd q hq hqF
    rw [h_gcd_one, Nat.cast_one] at hp_dvd_gcd
    have hp_dvd_one : p ∣ 1 := Int.natCast_dvd_natCast.mp hp_dvd_gcd
    exact Nat.Prime.not_dvd_one hp hp_dvd_one
  have hF0 : F ≠ 0 := by
    intro hF0; subst hF0
    have := hd 2 Nat.prime_two (dvd_zero 2)
    simp at this
  have hF_pos : 0 < F := Nat.pos_of_ne_zero hF0
  have hord : orderOf c = F := orderOf_eq_of_pow_and_pow_div_prime hF_pos hpow hd
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow hF0] at hpow
    exact zero_ne_one hpow
  have hF_dvd : F ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hc0
  have hp1 : 1 ≤ p := hp.one_le
  obtain ⟨k, hk⟩ := hF_dvd
  refine ⟨k, ?_⟩
  rw [mul_comm]
  omega

/-- LEAF 864: If N is prime, the condition holds -/
theorem leaf_prime_cond (F R : ℕ) (hF : 0 < F) (hN : (R * F + 1).Prime) :
    R / (2 * F) = 0 ∨ ¬ IsSquare (((R % (2 * F) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * F) : ℕ) : ℤ)) := by
  by_contra hcon
  rw [not_or, not_not] at hcon
  obtain ⟨hs0, t, ht⟩ := hcon
  obtain ⟨s, hs⟩ : ∃ s, s = R / (2 * F) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = R % (2 * F) := ⟨_, rfl⟩
  rw [← hs, ← hr] at ht
  rw [← hs] at hs0
  have hRsr : R = 2 * F * s + r := by rw [hs, hr]; exact (Nat.div_add_mod R (2 * F)).symm
  obtain ⟨u, hu⟩ : ∃ u, u = t.natAbs := ⟨_, rfl⟩
  have hut : ((u * u : ℕ) : ℤ) = t * t := by
    rw [hu]; push_cast; exact abs_mul_abs_self t
  have hru : r * r = u * u + 8 * s := by
    have : ((r * r : ℕ) : ℤ) = ((u * u + 8 * s : ℕ) : ℤ) := by
      push_cast at hut ⊢; rw [hut, ← ht]; ring
    exact_mod_cast this
  have hulr : u < r := by
    by_contra hge
    have hge' : r ≤ u := by omega
    have : r * r ≤ u * u := Nat.mul_le_mul hge' hge'
    omega
  have hpar : (r + u) % 2 = 0 := by
    have h1 : Even (r * r) ↔ Even (u * u) := by
      rw [hru, Nat.even_add]; simp [show Even (8 * s) from ⟨4 * s, by ring⟩]
    rw [Nat.even_mul, Nat.even_mul, or_self, or_self] at h1
    rcases Nat.even_or_odd r with h2 | h2
    · have := h1.mp h2
      obtain ⟨x, hx⟩ := h2; obtain ⟨y, hy⟩ := this; omega
    · have hu' : ¬ Even u := fun h => (Nat.not_even_iff_odd.mpr h2) (h1.mpr h)
      rw [Nat.not_even_iff_odd] at hu'
      obtain ⟨x, hx⟩ := h2; obtain ⟨y, hy⟩ := hu'; omega
  obtain ⟨a, ha⟩ : ∃ a, 2 * a = r + u := ⟨(r + u) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, 2 * b = r - u := ⟨(r - u) / 2, by omega⟩
  have hab : a * b = 2 * s := by
    have h4 : (2 * a) * (2 * b) = 8 * s := by
      rw [ha, hb]
      zify [hulr.le] at hru ⊢
      linear_combination hru
    have h4' : 4 * (a * b) = 4 * (2 * s) := by
      calc 4 * (a * b) = (2 * a) * (2 * b) := by ring
        _ = 8 * s := h4
        _ = 4 * (2 * s) := by ring
    omega
  have hsum : a + b = r := by omega
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, mul_zero] at hab; omega
    · exact h
  have ha1 : 1 ≤ a := by omega
  have hfac : R * F + 1 = (a * F + 1) * (b * F + 1) := by
    rw [hRsr, ← hsum]
    have : (a * F + 1) * (b * F + 1) =
        F * (F * (a * b)) + F * (a + b) + 1 := by ring
    rw [this, hab]; ring
  rw [hfac] at hN
  have h1 : a * F + 1 ≠ 1 := by have := Nat.mul_le_mul ha1 hF; omega
  have h2 : b * F + 1 ≠ 1 := by have := Nat.mul_le_mul hb1 hF; omega
  exact Nat.not_prime_mul h1 h2 hN

/-- LEAF 864: Composite N with factors 1 mod F and N < 2F^3 has exactly two such factors.
Statement repaired 2026-10-31 by the architect, run 20261031T2235Z-16111: `hR : 0 < R` added,
the old statement was false at R = 0, F = 1, where N = 1. -/
theorem leaf_comp_factors (F R : ℕ) (hF : 0 < F) (hR : 0 < R) (hN_lt : R * F + 1 < 2 * F ^ 3)
    (hpock : ∀ p : ℕ, p.Prime → p ∣ R * F + 1 → ∃ k : ℕ, p = k * F + 1)
    (hN : ¬ (R * F + 1).Prime) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ R * F + 1 = (a * F + 1) * (b * F + 1) := sorry

/-- LEAF 864: Factorization gives R in terms of a and b -/
theorem leaf_R_eq (F R a b : ℕ) (hF : 0 < F) (h : R * F + 1 = (a * F + 1) * (b * F + 1)) :
    R = a * b * F + a + b := by
  have h1 : R * F + 1 = (a * b * F + a + b) * F + 1 := by
    calc R * F + 1 = (a * F + 1) * (b * F + 1) := h
      _ = a * b * F * F + a * F + b * F + 1 := by ring
      _ = (a * b * F + a + b) * F + 1 := by ring
  exact Nat.eq_of_mul_eq_mul_right hF (Nat.add_right_cancel h1)

/-- LEAF 864: If N factors, the BLS condition fails. Statement repaired 2026-10-31 by the
architect, run 20261031T2235Z-16111: Lemma 1's hypotheses `Even F`, `Nat.Coprime R F` and
`N < 2F^3` added; the old statement was false at R = 5, F = 3, a = b = 1. -/
theorem leaf_comp_cond_from_factors (F R a b : ℕ) (hF : 0 < F)
    (hFe : Even F) (hCop : Nat.Coprime R F) (hN_lt : R * F + 1 < 2 * F ^ 3)
    (h_eq : R * F + 1 = (a * F + 1) * (b * F + 1)) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬ (R / (2 * F) = 0 ∨ ¬ IsSquare (((R % (2 * F) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * F) : ℕ) : ℤ))) := by
  sorry

/-- Assembly for Lemma 1, Brillhart, Lehmer and Selfridge 1975, Theorem 5 -/
theorem lemma1 : Lemma1 := by
  intro F R a hOdd hF hCoprime hFermat hgcd hN_lt
  rcases Nat.eq_zero_or_pos F with rfl | hF_pos
  · exact leaf_F_zero R hN_lt
  constructor
  · intro hN
    exact leaf_prime_cond F R hF_pos hN
  · intro hcond
    by_contra hN_comp
    have hpock := leaf_pock F R a hOdd hF hCoprime hFermat hgcd
    have hR : 0 < R := by
      rcases Nat.eq_zero_or_pos R with rfl | h
      · have h1 : F = 1 := Nat.coprime_zero_left F |>.mp hCoprime
        subst h1
        exact absurd hF (by decide)
      · exact h
    obtain ⟨a_fac, b_fac, ha, hb, heq⟩ := leaf_comp_factors F R hF_pos hR hN_lt hpock hN_comp
    have h_fail := leaf_comp_cond_from_factors F R a_fac b_fac hF_pos hF hCoprime hN_lt heq ha hb
    exact h_fail hcond

end LeanLab.Saouter1998.BLS
