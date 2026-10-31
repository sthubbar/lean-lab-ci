import Mathlib

/-!
# Why P0039 restricts to m ≡ 4 mod 6: the class 2 mod 6 obstruction

T2 FRONTIER, unit U-1047, PC run 20261019T0803Z-3015. AI wrote this Lean code.
If `p, q > 3` are primes with `p + q ≡ 2 mod 6`, both are `1 mod 3`, so `3 ∣ p + 2` and
`3 ∣ q + 2`: each Chen condition `Ω(p + 2) ≤ 2` then forces `p + 2 = 3 r` with `r` prime,
a much thinner set. Numerics in gen/chen_exc.py: up to 10^7, 27 even m ≡ 2 mod 6 are not sums
of two Chen primes, the largest 35912, and none in the classes 0 and 4 mod 6. KNOWN mathematics.
-/

namespace LeanLab.ExceptionalSet.ChenClass2

theorem three_dvd_add_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq3 : 3 < q)
    (h : (p + q) % 6 = 2) : 3 ∣ p + 2 ∧ 3 ∣ q + 2 := by
  have hp' : p % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.dvd_prime hp).1 h3 with h1 | h1 <;> omega
  have hq' : q % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.dvd_prime hq).1 h3 with h1 | h1 <;> omega
  constructor <;> omega

/-- Vacuity test: `7 + 13 = 20 ≡ 2 mod 6`, and `3 ∣ 9`, `3 ∣ 15`. -/
example : 3 ∣ 7 + 2 ∧ 3 ∣ 13 + 2 :=
  three_dvd_add_two (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end LeanLab.ExceptionalSet.ChenClass2
