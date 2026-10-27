/-
Kai's scaffolding, I-0004, the mod 6 clusters of A020481, the least prime p with n - p prime.
PC run 20261020T0503Z-11094, unit U-1173. AI-written Lean code, Claude. Binary Goldbach is OPEN.

The residue rule behind the clusters:
* `excluded_same_class`: if `3 ∤ n`, a prime `p > 3` with `p ≡ n mod 3` and `n - p > 3` never has
  `n - p` prime, so half of the candidate primes are ruled out for every `n` with `3 ∤ n`;
* `none_excluded_mod3`: if `3 ∣ n`, no prime `p > 3` has `3 ∣ n - p`;
* `allowed_first`: for `n ≡ 1 mod 3` the allowed primes above 3 start 5, 11, 17; for `n ≡ 2 mod 3`
  they start 7, 13, 19, which is why the class 4 mod 6 sits between the classes 0 and 2 mod 6.
Numerics gen/mod6.py, gen/mod6_out.txt: mean least prime on n in [10⁶, 10⁷] is 17.55, 32.10, 26.72
for n ≡ 0, 2, 4 mod 6, ratios 1.83 and 1.52, blended 1.67 as Kai found.
KNOWN in spirit, the local factor of the singular series.
-/
import Mathlib

namespace LeanLab.KaiScaffolding.Mod6

theorem excluded_same_class {n p : ℕ} (hn : n % 3 ≠ 0) (hpn : p % 3 = n % 3) (hp : p ≤ n)
    (hgt : 3 < n - p) : ¬ (n - p).Prime := by
  intro h
  have h3 : 3 ∣ n - p := by omega
  rcases h.eq_one_or_self_of_dvd 3 h3 with h' | h' <;> omega

theorem none_excluded_mod3 {n p : ℕ} (hn : 3 ∣ n) (hp : p.Prime) (hp3 : 3 < p) (hpn : p ≤ n) :
    ¬ 3 ∣ n - p := by
  intro h
  have : 3 ∣ p := by omega
  rcases hp.eq_one_or_self_of_dvd 3 this with h' | h' <;> omega

theorem allowed_first :
    (5 % 3 ≠ 1 ∧ 11 % 3 ≠ 1 ∧ 17 % 3 ≠ 1) ∧ (7 % 3 ≠ 2 ∧ 13 % 3 ≠ 2 ∧ 19 % 3 ≠ 2) := by decide

/-- Vacuity: `n = 100`, `p = 7`, both `≡ 1 mod 3`, `n - p = 93 = 3 · 31`. -/
theorem vacuity : ¬ (100 - 7).Prime :=
  excluded_same_class (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end LeanLab.KaiScaffolding.Mod6
