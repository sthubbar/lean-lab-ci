/-
Helfgott and Platt 2013, P0006, arXiv 1305.3062v2, unit U-1511, run 20261025T0416Z-19415.
Row by row check of the printed rows that U-0950's PaperNumbers.lean did not cover:
Section 4, "We set B to 29 so we had 10 potential candidates for a. As each one has about a
50% chance of success, we failed to find a suitable a in about 0.1% of cases";
Section 3, the parameter condition Δ > 2^n; footnote 1, Saouter's numbers 2^22 R + 1 with
N < 10^20, N ≡ 3 mod 10 and R odd.
AI-written Lean code, Claude, 2026-10-25. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN. Nothing here touches the
inputs of Theorem 4.1: a candidate with no usable a is merely skipped by the ladder.
-/
import Mathlib

namespace LeanLab.HelfgottPlatt.U1511

open ZMod

/-- Section 4: there are exactly 10 primes up to B = 29, the paper's "10 potential candidates". -/
theorem primes_le_29 :
    (Finset.range 30).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by decide

theorem card_primes_le_29 : ((Finset.range 30).filter Nat.Prime).card = 10 := by
  rw [primes_le_29]; rfl

/-- A Proth number with n ≥ 3 is 1 mod 8. -/
theorem proth_mod_eight (k m : ℕ) : (k * 2 ^ (m + 3) + 1) % 8 = 1 := by
  have : k * 2 ^ (m + 3) = 8 * (k * 2 ^ m) := by ring
  omega

/-- The candidate a = 2 never has Jacobi symbol -1 over a Proth number with n ≥ 3, so it never
meets the hypothesis of Theorem 2.3. With n = 52 only the 9 odd primes 3, ..., 29 can serve. -/
theorem jacobi_two_proth (k m : ℕ) : jacobiSym 2 (k * 2 ^ (m + 3) + 1) = 1 := by
  have h8 := proth_mod_eight k m
  have hodd : Odd (k * 2 ^ (m + 3) + 1) := by
    rw [Nat.odd_iff]; omega
  rw [jacobiSym.at_two hodd, χ₈_nat_eq_if_mod_eight]
  simp [h8, show (k * 2 ^ (m + 3) + 1) % 2 = 1 by omega]

theorem two_never_witness (k m : ℕ) : jacobiSym 2 (k * 2 ^ (m + 3) + 1) ≠ -1 := by
  rw [jacobi_two_proth]; decide

/-- For odd a, the Jacobi symbol of a over a Proth number N with n ≥ 2 equals that of N mod a
over a, by reciprocity, since N ≡ 1 mod 4. So whether a works depends only on N mod a. -/
theorem jacobi_proth_recip (k m a : ℕ) (ha : Odd a) :
    jacobiSym a (k * 2 ^ (m + 2) + 1) = jacobiSym ((k * 2 ^ (m + 2) + 1) % a : ℕ) a := by
  have h4 : (k * 2 ^ (m + 2) + 1) % 4 = 1 := by
    have : k * 2 ^ (m + 2) = 4 * (k * 2 ^ m) := by ring
    omega
  rw [jacobiSym.quadratic_reciprocity_one_mod_four' ha h4, jacobiSym.mod_left, Int.natCast_mod]

/-- The 50% in the paper: for each odd prime p up to 29 exactly (p - 1)/2 of the p - 1 nonzero
residues are squares. With reciprocity above and CRT over k, the exact density of sieved
candidates for which none of 3, ..., 29 works is 2^-9 = 1/512, about 0.195%, not 2^-10. -/
def sqCount (p : ℕ) : ℕ :=
  ((List.range p).filter (fun r => r ≠ 0 ∧ ∃ x ∈ List.range p, x * x % p = r)).length

theorem half_squares :
    sqCount 3 = 1 ∧ sqCount 5 = 2 ∧ sqCount 7 = 3 ∧ sqCount 11 = 5 ∧ sqCount 13 = 6 ∧
    sqCount 17 = 8 ∧ sqCount 19 = 9 ∧ sqCount 23 = 11 ∧ sqCount 29 = 14 := by
  decide +kernel

/-- The resulting density, a plain product: (1/2)^9 = 1/512 and 1/512 > 0.19%. -/
theorem density_value : ((1 : ℚ) / 2) ^ 9 = 1 / 512 ∧ (19 : ℚ) / 10000 < 1 / 512 := by
  norm_num

/-- Section 3: the algorithm needs Δ > 2^n; with Δ = 4e18 and n = 52 this holds. -/
theorem delta_gt : 2 ^ 52 < 4 * 10 ^ 18 := by norm_num

/-- Footnote 1: for N = 2^22 R + 1, R odd and N ≡ 3 mod 10 together say exactly R ≡ 3 mod 10. -/
theorem two_pow_22 : (2 : ℕ) ^ 22 = 4194304 := by norm_num

theorem saouter_key (R : ℕ) : (4194304 * R + 1) % 10 = (4 * (R % 10) + 1) % 10 := by
  rw [Nat.add_mod, Nat.mul_mod]; norm_num [Nat.add_mod, Nat.mul_mod]

theorem saouter_form (R : ℕ) : (R % 2 = 1 ∧ (4194304 * R + 1) % 10 = 3) ↔ R % 10 = 3 := by
  rw [saouter_key]
  have h10 := Nat.mod_lt R (show 10 > 0 by norm_num)
  have h2 : R % 2 = R % 10 % 2 := (Nat.mod_mod_of_dvd R (by norm_num)).symm
  rw [h2]
  interval_cases R % 10 <;> simp

/-- Footnote 1 reading note: a Proth number with n = 22 has R < 2^22, so is below 2^44 + 1;
Saouter's numbers up to 10^20 mostly have R ≥ 2^22 and lie outside Definition 2.1. -/
theorem saouter_outside_def (R : ℕ) (hN : 2 ^ 44 < 2 ^ 22 * R + 1) : 2 ^ 22 ≤ R := by
  by_contra h
  push Not at h
  have : 2 ^ 22 * R ≤ 2 ^ 22 * (2 ^ 22 - 1) := Nat.mul_le_mul_left _ (by omega)
  norm_num at this hN
  omega

/-- Vacuity: hypotheses can hold. 17 = 1 · 2^4 + 1, the Jacobi symbol of 2 over 17 is 1 and that
of 3 is -1; R = 3 meets footnote 1's conditions with N = 12582913 < 10^20. -/
theorem vac_17 : jacobiSym 2 17 = 1 ∧ jacobiSym 3 17 = -1 := by
  refine ⟨by simpa using jacobi_two_proth 1 1, ?_⟩
  have h := jacobi_proth_recip 1 2 3 (by decide)
  simp only [Nat.cast_ofNat] at h
  rw [show (17 : ℕ) = 1 * 2 ^ (2 + 2) + 1 by norm_num, h]
  have h2 : ((((1 * 2 ^ (2 + 2) + 1) % 3 : ℕ)) : ℤ) = 2 := by norm_num
  rw [h2, jacobiSym.at_two (by decide), χ₈_nat_eq_if_mod_eight]
  decide

theorem vac_saouter : (3 % 2 = 1 ∧ (4194304 * 3 + 1) % 10 = 3) ∧ 2 ^ 22 * 3 + 1 < 10 ^ 20 := by
  norm_num

#print axioms primes_le_29
#print axioms card_primes_le_29
#print axioms proth_mod_eight
#print axioms jacobi_two_proth
#print axioms two_never_witness
#print axioms jacobi_proth_recip
#print axioms half_squares
#print axioms density_value
#print axioms delta_gt
#print axioms two_pow_22
#print axioms saouter_key
#print axioms saouter_form
#print axioms saouter_outside_def
#print axioms vac_17
#print axioms vac_saouter

end LeanLab.HelfgottPlatt.U1511
