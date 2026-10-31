/-
P0076 Theorem 1.3 proof, page 17, primitive representations and amenable residue classes.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Amenable

namespace LeanLab.Teravainen2016

/-- A primitive sum of two squares has no prime divisor congruent to three modulo four. -/
theorem primitive_sum_no_three_mod_four_prime {x y : ℤ} (hxy : Int.gcd x y = 1)
    {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 3) : ¬ (q : ℤ) ∣ x ^ 2 + y ^ 2 := by
  intro hd
  letI : Fact q.Prime := ⟨hq⟩
  have hc : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hxy
  have hs := ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime (n := x ^ 2 + y ^ 2) rfl hc
  have hs' := ZMod.isSquare_neg_one_of_dvd (Int.natCast_dvd.mp hd) hs
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hs') hq4

/-- A primitive sum of two squares is not divisible by four. -/
theorem primitive_sum_not_four_dvd {x y : ℤ} (hxy : Int.gcd x y = 1) :
    ¬ (4 : ℤ) ∣ x ^ 2 + y ^ 2 := by
  intro hd
  have hm := Int.emod_eq_zero_of_dvd hd
  rw [Int.add_emod, Int.sq_emod_four, Int.sq_emod_four] at hm
  have hx : x % 2 = 0 := by omega
  have hy : y % 2 = 0 := by omega
  have hdg := Int.dvd_gcd (Int.dvd_of_emod_eq_zero hx) (Int.dvd_of_emod_eq_zero hy)
  rw [hxy] at hdg
  norm_num at hdg

/-- For a prime in PStar, its predecessor has no forbidden odd prime divisor. -/
theorem inPStar_predecessor_no_three_mod_four_prime {p q : ℕ} (hp : InPStar p)
    (hq : q.Prime) (hq4 : q % 4 = 3) : ¬ (q : ℤ) ∣ (p : ℤ) - 1 := by
  obtain ⟨_, x, y, hxy, he⟩ := hp
  have hpred : (p : ℤ) - 1 = x ^ 2 + y ^ 2 := by linarith
  rw [hpred]
  exact primitive_sum_no_three_mod_four_prime hxy hq hq4

/-- An odd prime in PStar has predecessor equal to two modulo eight. -/
theorem inPStar_predecessor_mod_eight {p : ℕ} (hp : InPStar p) (hp2 : p ≠ 2) :
    (p : ℤ) - 1 ≡ 2 [ZMOD 8] := by
  obtain ⟨hprime, x, y, hxy, he⟩ := hp
  have hpred : (p : ℤ) - 1 = x ^ 2 + y ^ 2 := by linarith
  have hfour := primitive_sum_not_four_dvd hxy
  have hfour' : (x ^ 2 + y ^ 2) % 4 ≠ 0 := by
    simpa only [Int.dvd_iff_emod_eq_zero] using hfour
  have hmod : (x ^ 2 + y ^ 2) % 4 = (x % 2 + y % 2) % 4 := by
    rw [Int.add_emod, Int.sq_emod_four, Int.sq_emod_four]
  have hpodd : (p : ℤ) % 2 = 1 := Int.odd_iff.mp (hprime.odd_of_ne_two hp2).natCast
  have hx : Odd x := Int.odd_iff.mpr (by omega)
  have hy : Odd y := Int.odd_iff.mpr (by omega)
  apply Int.modEq_of_dvd
  have h8 := Int.dvd_add (Int.eight_dvd_sq_sub_one_of_odd hx)
    (Int.eight_dvd_sq_sub_one_of_odd hy)
  have he8 : 2 - ((p : ℤ) - 1) = -((x ^ 2 - 1) + (y ^ 2 - 1)) := by linarith
  rw [he8]
  exact Int.dvd_neg.mpr h8

/-- A sufficiently large prime in PStar gives an amenable linear polynomial at any permitted modulus. -/
theorem inPStar_amenable {p : ℕ} (hp : InPStar p) {K : ℤ} (hK : 1 ≤ K)
    (hK6 : (6 : ℤ) ^ 3 ∣ K) (hKp : K < p) : Amenable K p := by
  have hK0 : 0 < K := by omega
  have hK216 : (216 : ℤ) ∣ K := by norm_num at hK6; exact hK6
  have hKlarge : 216 ≤ K := Int.le_of_dvd hK0 hK216
  have hp2 : p ≠ 2 := by omega
  have hcop : IsCoprime (p : ℤ) K := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast]
    apply hp.1.coprime_iff_not_dvd.mpr
    intro hd
    have hd' : (p : ℤ) ∣ K := Int.natCast_dvd.mpr hd
    have hle := Int.le_of_dvd hK0 hd'
    omega
  refine ⟨hK, hK6, hcop, ?_, ?_⟩
  · intro q hq hq4 _ _
    exact inPStar_predecessor_no_three_mod_four_prime hp hq hq4
  · obtain ⟨u, hu⟩ := (inPStar_predecessor_mod_eight hp hp2).symm.dvd
    have he : (p : ℤ) - 1 = 2 ^ 1 * 3 ^ (2 * 0) * (4 * u + 1) := by
      norm_num at hu ⊢
      linarith
    refine ⟨1, 0, u, he, ?_, ?_⟩
    · intro h3
      apply inPStar_predecessor_no_three_mod_four_prime hp Nat.prime_three (by decide)
      rw [he]
      exact h3.mul_left _
    · norm_num
      exact (by norm_num : (24 : ℤ) ∣ 216).trans hK216

example : InPStar 11 := ⟨by decide, 1, 3, by norm_num, by norm_num⟩
example : ¬ (3 : ℤ) ∣ (11 : ℤ) - 1 := by norm_num
example : (11 : ℤ) - 1 ≡ 2 [ZMOD 8] := by decide

#print axioms primitive_sum_no_three_mod_four_prime
#print axioms primitive_sum_not_four_dvd
#print axioms inPStar_predecessor_no_three_mod_four_prime
#print axioms inPStar_predecessor_mod_eight
#print axioms inPStar_amenable

end LeanLab.Teravainen2016
