/-
EvenGoldbachUpTo 10^9, zero sorry: every even n with 4 ≤ n ≤ 10^9 is a sum of two primes,
checked by the Lean kernel with no cited input.
Chain: small_1e6 in SmallGB.lean, from check_1e6 in BitUpTo1e6.lean; then BitUChain1 to BitUChain4, 327 windows of
990000 from 10^6 to 324730000 in BitUG1 to BitUG33; then BitVChain1 to BitVChain7, 684 windows of
990000 from 323740000 to 1000900000 in BitVG1 to BitVG69. Ten windows per file, each one bignum
equality checked by decide +kernel, sound by small_extend2 in SmallGB.lean, whose sieve uses the
primes below 31700 proved complete in P32.lean. The U windows recheck the range of the older
BitW1 to BitW163 files in the faster grouped layout, so one workspace builds the whole chain.
Each step keeps the prime q ≤ 1811, which bounds minGB for P0042. Far below the 4e18 of P0005; the point is that nothing here is cited.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.SmallGB
import LeanLab.Verifications.Top50.BitUChain1
import LeanLab.Verifications.Top50.BitUChain2
import LeanLab.Verifications.Top50.BitUChain3
import LeanLab.Verifications.Top50.BitUChain4
import LeanLab.Verifications.Top50.BitVChain1
import LeanLab.Verifications.Top50.BitVChain2
import LeanLab.Verifications.Top50.BitVChain3
import LeanLab.Verifications.Top50.BitVChain4
import LeanLab.Verifications.Top50.BitVChain5
import LeanLab.Verifications.Top50.BitVChain6
import LeanLab.Verifications.Top50.BitVChain7

namespace LeanLab.Verifications.Top50.Bits

/-- Every even n with 4 ≤ n ≤ 1000900000 is q + p with q, p prime and q ≤ 1811, kernel checked. -/
theorem smallGBUpTo_1000900000 : SmallGBUpTo 1811 1000900000 :=
  small_v684 <| small_v600 <| small_v500 <| small_v400 <| small_v300 <| small_v200 <| small_v100 <|
    small_mono (small_u327 <| small_u300 <| small_u200 <| small_u100 small_1e6) (by norm_num)

/-- Every even n with 4 ≤ n ≤ 10^9 is a sum of two primes, kernel checked, no cited input. -/
theorem evenGoldbachUpTo_1e9 : EvenGoldbachUpTo (10 ^ 9) :=
  upTo_of_small (small_mono smallGBUpTo_1000900000 (by norm_num))

/-- P0042 Table 3 on the range to 10^9: the least prime of a Goldbach partition of an even n with
4 ≤ n ≤ 10^9 is at most 1811, so at most the 2029 Granville, van de Lune and te Riele report
for their range to 2e10. The range from 10^9 to 2e10 stays their computation. -/
theorem minGB_le_1811_upTo_1e9 : ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 10 ^ 9 →
    LeanLab.Verifications.minGB n ≤ 1811 :=
  fun _ hn h4 hnB => minGB_le_of_small smallGBUpTo_1000900000 hn h4 (le_trans hnB (by norm_num))

theorem gvltr_max_upTo_1e9 : ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 10 ^ 9 →
    LeanLab.Verifications.minGB n ≤ 2029 :=
  fun n hn h4 hnB => le_trans (minGB_le_1811_upTo_1e9 n hn h4 hnB) (by norm_num)

/-- Ternary corollary: every odd n with 7 ≤ n ≤ 10^9 + 3 is a sum of three primes, as 3 plus
an even Goldbach sum. Trivial next to Helfgott-Platt, kept because it is cited-input free. -/
theorem ternaryGoldbachUpTo_1e9 : TernaryGoldbachUpTo (10 ^ 9 + 3) := by
  intro n hn h7 hnN
  obtain ⟨p, q, hp, hq, hpq⟩ := evenGoldbachUpTo_1e9 (n - 3)
    (by obtain ⟨k, rfl⟩ := hn; exact ⟨k - 1, by omega⟩) (by omega) (by omega)
  exact ⟨p, q, 3, hp, hq, Nat.prime_three, by omega⟩

end LeanLab.Verifications.Top50.Bits
