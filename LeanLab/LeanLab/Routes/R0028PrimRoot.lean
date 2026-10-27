import Mathlib

/-!
# R-0028, binary Goldbach for primitive roots in `𝔽_p`: an exact quadratic parity obstruction

Lab proof, unit U-1237, PC 20261020T1503Z-30533. AI wrote the Lean code. Known mathematics:
the finite field analogue of binary Goldbach replaces the primes by the primitive roots of
`𝔽_p`; Vinogradov's character expansion of the primitive root indicator with Weil and Gauss
square root bounds solves the binary problem for large `p`, see Cohen, Oliveira e Silva and
Trudgian, arXiv 1402.2724, for the explicit linear combination version. Binary Goldbach is
OPEN; this is a T3 route, never progress on Goldbach.

* `pow_half_eq_neg_one`: a primitive root `g` of `𝔽_p`, `p` odd, has `g ^ ((p-1)/2) = -1`.
* `neg_not_primitive`: for `p ≡ 3 mod 4` the negative of a primitive root is never one.
* `zero_not_sum_two`: so for `p ≡ 3 mod 4` the class `0` is never a sum of two primitive roots,
  the exact analogue of an odd `N` against two odd primes: the quadratic character, the order 2
  part of the character expansion, kills the main term, as the 2-adic factor of the singular
  series kills odd `N`.
* `vacuity_7`, `vacuity_13`: the hypotheses hold, `3` is a primitive root mod 7, and for
  `p = 13 ≡ 1 mod 4` the class `0` is `2 + 11` with both primitive, so the obstruction is
  specific to `p ≡ 3 mod 4`.
-/

namespace LeanLab.Routes.R0028

/-- A primitive root of `𝔽_p` for an odd prime `p` satisfies `g ^ ((p-1)/2) = -1`. -/
theorem pow_half_eq_neg_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {g : ZMod p}
    (hg : orderOf g = p - 1) : g ^ ((p - 1) / 2) = -1 := by
  have hodd : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hp.out with h2 | h2
    · exact absurd h2 hp2
    · exact h2
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le; omega
  have hsq : g ^ ((p - 1) / 2) * g ^ ((p - 1) / 2) = 1 := by
    rw [← pow_add]
    have : (p - 1) / 2 + (p - 1) / 2 = p - 1 := by omega
    rw [this, ← hg]; exact pow_orderOf_eq_one g
  have hne : g ^ ((p - 1) / 2) ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · omega
    · rw [hg]; omega
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h hne
  · exact h

/-- For `p ≡ 3 mod 4`, the negative of a primitive root of `𝔽_p` is not a primitive root. -/
theorem neg_not_primitive {p : ℕ} [hp : Fact p.Prime] (hp4 : p % 4 = 3) {g : ZMod p}
    (hg : orderOf g = p - 1) : orderOf (-g) ≠ p - 1 := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hhalf : g ^ ((p - 1) / 2) = -1 := pow_half_eq_neg_one hp2 hg
  have hoddhalf : Odd ((p - 1) / 2) := ⟨(p - 3) / 4, by omega⟩
  have hpow : (-g) ^ ((p - 1) / 2) = 1 := by
    rw [neg_pow, hhalf, hoddhalf.neg_one_pow]; ring
  intro h
  have hdvd : orderOf (-g) ∣ (p - 1) / 2 := orderOf_dvd_of_pow_eq_one hpow
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

/-- For `p ≡ 3 mod 4`, the class `0` of `𝔽_p` is not a sum of two primitive roots. -/
theorem zero_not_sum_two {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ¬ ∃ g h : ZMod p, orderOf g = p - 1 ∧ orderOf h = p - 1 ∧ g + h = 0 := by
  rintro ⟨g, h, hg, hh, hsum⟩
  have : h = -g := by linear_combination hsum
  subst this
  exact neg_not_primitive hp4 hg hh

/-- Vacuity: `3` is a primitive root mod `7`, and `7 ≡ 3 mod 4`. -/
theorem vacuity_7 : orderOf (3 : ZMod 7) = 7 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  decide

/-- Vacuity for the other class: mod `13 ≡ 1 mod 4`, `0 = 2 + 11` with both primitive roots. -/
theorem vacuity_13 : ∃ g h : ZMod 13, orderOf g = 13 - 1 ∧ orderOf h = 13 - 1 ∧ g + h = 0 := by
  refine ⟨2, 11, ?_, ?_, by decide⟩
  · rw [orderOf_eq_iff (by norm_num)]; exact ⟨by decide, by decide⟩
  · rw [orderOf_eq_iff (by norm_num)]; exact ⟨by decide, by decide⟩

end LeanLab.Routes.R0028
