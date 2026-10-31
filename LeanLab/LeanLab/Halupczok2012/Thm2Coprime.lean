/-
Halupczok 2012, Theorem 2 needs gcd(a, q) = 1. P0077 K. Halupczok, arXiv 1212.4406.
Theorem 2 is printed "for any fixed integer a with a ≤ n − X1 − Y1". For q = 3 and a = 3 the
inner prime sum is empty once X1 > 3, since the only prime ≡ 0 mod 3 is 3, while the
singular series T(n, 3, 3) is about 0.767 by numerics, so that single term already gives
about 0.767 Y1 Y2, not ≪ Y1 Y2 L^{-A}. The Lean below proves the empty-sum half.
The value of T is numerics only, see FINDINGS F-0008.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.
-/
import Mathlib

namespace LeanLab.Halupczok2012

/-- A prime in the class of `0` mod a prime `ℓ` is `ℓ` itself. -/
theorem prime_mod_eq_zero {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (h : p % ℓ = 0) : p = ℓ := by
  have hd : ℓ ∣ p := Nat.dvd_of_mod_eq_zero h
  exact ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp hd).symm

/-- **The p₁ sum of Theorem 2 is empty for `q = ℓ` prime and `a ≡ 0 mod ℓ`, once `X₁ > ℓ`**:
no prime `p₁ ≥ X₁` has `p₁ ≡ a mod ℓ`. -/
theorem no_prime_in_class {ℓ a X₁ : ℕ} (hℓ : ℓ.Prime) (ha : a % ℓ = 0) (hX : ℓ < X₁) :
    ∀ p : ℕ, p.Prime → X₁ ≤ p → p % ℓ ≠ a % ℓ := by
  intro p hp hXp h
  rw [ha] at h
  have := prime_mod_eq_zero hℓ hp h
  omega

/-- The case of the finding: `q = 3`, `a = 3`. -/
theorem no_prime_three_mod_three {X₁ : ℕ} (hX : 3 < X₁) :
    ∀ p : ℕ, p.Prime → X₁ ≤ p → ¬ p ≡ 3 [MOD 3] := by
  intro p hp hXp h
  exact no_prime_in_class Nat.prime_three (a := 3) (by norm_num) hX p hp hXp h

end LeanLab.Halupczok2012
