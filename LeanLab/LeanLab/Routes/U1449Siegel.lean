import Mathlib

/-!
# R-0047, T3 MOONSHOT: the Deuring-Heilbronn dichotomy for binary Goldbach, and the
# illusory obstruction at multiples of an exceptional modulus

Unit U-1449, PC run 20261021T2003Z-599. AI wrote this Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Route. Split on whether a Landau-Siegel zero exists. In the exceptional branch, with a real
primitive character χ mod q and a zero β close to 1, the primes in a range q^10 ≤ h ≤ q^c
behave as if χ(p) = -1, and Matomaki-Merikoski 2022, Theorem 1.4, give an asymptotic for the
Goldbach count with main term h S_h times a correction factor. For q prime, q ≡ 3 mod 4,
that factor is 1 + 1/(q - 2) when q ∤ h and exactly 0 when q ∣ h.

This file proves the arithmetic core of that zero, the smallest lemma the route needs:
if every element of a set is a quadratic non-residue mod a prime p ≡ 3 mod 4, then no two
elements sum to a multiple of p. So in the illusory world the exceptional branch is hostile
to Goldbach exactly at the multiples of q, and the dichotomy cannot close.

Plain math twins are in STATEMENTS.md under U-1449.
-/

namespace LeanLab.Routes.U1449

/-- For a prime `p ≡ 3 mod 4`, the Legendre symbol is odd: `(-a / p) = -(a / p)`.
This is `χ(-1) = -1` for the character of conductor `p`. -/
theorem neg_flip (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) (a : ℤ) :
    legendreSym p (-a) = - legendreSym p a := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp4
  rw [legendreSym.at_neg hp2, ZMod.χ₄_nat_three_mod_four hp4]
  ring

/-- The Legendre symbol depends only on the residue mod `p`. -/
theorem legendre_congr (p : ℕ) [Fact p.Prime] {a b : ℤ} (h : ((a : ℤ) : ZMod p) = ((b : ℤ) : ZMod p)) :
    legendreSym p a = legendreSym p b := by
  unfold legendreSym
  rw [h]

/-- The illusory obstruction: two quadratic non-residues mod a prime `p ≡ 3 mod 4`
never sum to a multiple of `p`. -/
theorem illusory_obstruction (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) {a b : ℤ}
    (ha : legendreSym p a = -1) (hb : legendreSym p b = -1) : ¬ ((p : ℤ) ∣ a + b) := by
  intro hdvd
  have h0 : (((a + b : ℤ)) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  have hba : ((b : ℤ) : ZMod p) = ((-a : ℤ) : ZMod p) := by
    push_cast at h0 ⊢
    linear_combination h0
  have := legendre_congr p hba
  rw [neg_flip p hp4, ha, hb] at this
  norm_num at this

/-- Goldbach form of the obstruction: if a set `S` of naturals consists of quadratic
non-residues mod a prime `p ≡ 3 mod 4`, the illusory primes of an exceptional modulus `p`,
then no multiple `N` of `p` is a sum of two elements of `S`. -/
theorem illusory_goldbach_fails (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) (S : Set ℕ)
    (hS : ∀ n ∈ S, legendreSym p (n : ℤ) = -1) {N : ℕ} (hN : p ∣ N) :
    ¬ ∃ a ∈ S, ∃ b ∈ S, a + b = N := by
  rintro ⟨a, ha, b, hb, rfl⟩
  apply illusory_obstruction p hp4 (hS a ha) (hS b hb)
  exact_mod_cast hN

/-- The density form: for a unit `a` mod `p ≡ 3 mod 4`, the illusory pair weight
`(1 - χ(a)) (1 - χ(-a))` vanishes. Summed over `a` it is the local factor of the
illusory Goldbach main term at `p ∣ N`, which is therefore `0`, matching the
Matomaki-Merikoski correction factor `1 + χ(-1) = 0`. -/
theorem pair_weight_zero (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) {a : ℤ}
    (ha : ((a : ℤ) : ZMod p) ≠ 0) :
    (1 - legendreSym p a) * (1 - legendreSym p (-a)) = 0 := by
  rw [neg_flip p hp4]
  rcases legendreSym.eq_one_or_neg_one p ha with h | h <;> rw [h] <;> norm_num

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The hypothesis `p ≡ 3 mod 4` cannot be dropped: mod `5`, `χ(-1) = +1`, and the two
non-residues `2` and `3` sum to `5`. This is the Matomaki-Merikoski case where the factor
is `1 + 1 = 2`, not `0`. -/
theorem flip_needed : legendreSym 5 2 = -1 ∧ legendreSym 5 3 = -1 ∧ (5 : ℤ) ∣ 2 + 3 := by
  refine ⟨?_, ?_, by norm_num⟩
  · rw [legendreSym.eq_neg_one_iff]; decide
  · rw [legendreSym.eq_neg_one_iff]; decide

/-- Vacuity: the hypotheses of `illusory_goldbach_fails` hold for a nonempty set,
`p = 7`, `S = {3, 5, 13}`, all non-residues mod `7`. -/
example : ∀ n ∈ ({3, 5, 13} : Set ℕ), legendreSym 7 (n : ℤ) = -1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl <;> rw [legendreSym.eq_neg_one_iff] <;> decide

/-- Vacuity: `7 % 4 = 3`, and `14 = 7 + 7` shows that dropping the non-residue hypothesis
on `S` lets a multiple of `7` be a sum, `7` being a ramified prime with symbol `0`. -/
example : 7 % 4 = 3 ∧ legendreSym 7 7 = 0 := by
  refine ⟨by norm_num, ?_⟩
  rw [legendreSym.eq_zero_iff]; decide

end LeanLab.Routes.U1449
