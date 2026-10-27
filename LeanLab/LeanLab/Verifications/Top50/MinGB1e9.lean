/-
U-0352, P0005 and P0042: the exact maximum of minGB on the even numbers from 4 to 10^9.
minGB n, the least prime p with n - p prime, is at most 1789 for every even n with 4 ≤ n ≤ 10^9,
and minGB 721013438 = 1789, so 1789 is the maximum and no smaller bound holds on that range.
Chain: msmall_1e6 in MinGBBase.lean, then BitMUChain1 to BitMUChain4 and BitMVChain1 to BitMVChain7,
the same 1011 windows of 990000 as BitUpTo1e9.lean but with q among the first 278 primes.
The attained value is Records2.minGB_1789, row 34 of the A025018 record table, checked by Pratt
certificates. Kernel checked, no cited input. The 4e18 range of P0005 stays cited.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.MinGBBase
import LeanLab.Verifications.Top50.BitMUChain1
import LeanLab.Verifications.Top50.BitMUChain2
import LeanLab.Verifications.Top50.BitMUChain3
import LeanLab.Verifications.Top50.BitMUChain4
import LeanLab.Verifications.Top50.BitMVChain1
import LeanLab.Verifications.Top50.BitMVChain2
import LeanLab.Verifications.Top50.BitMVChain3
import LeanLab.Verifications.Top50.BitMVChain4
import LeanLab.Verifications.Top50.BitMVChain5
import LeanLab.Verifications.Top50.BitMVChain6
import LeanLab.Verifications.Top50.BitMVChain7
import LeanLab.Verifications.Top50.Records2

namespace LeanLab.Verifications.Top50.Bits

/-- Every even n with 4 ≤ n ≤ 1000900000 is q + p with q, p prime and q ≤ 1789, kernel checked. -/
theorem msmallGBUpTo_1000900000 : SmallGBUpTo 1789 1000900000 :=
  msmall_v684 <| msmall_v600 <| msmall_v500 <| msmall_v400 <| msmall_v300 <| msmall_v200 <| msmall_v100 <|
    small_mono (msmall_u327 <| msmall_u300 <| msmall_u200 <| msmall_u100 msmall_1e6) (by norm_num)

/-- The least prime of a Goldbach partition of an even n with 4 ≤ n ≤ 10^9 is at most 1789. -/
theorem minGB_le_1789_upTo_1e9 : ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 10 ^ 9 →
    LeanLab.Verifications.minGB n ≤ 1789 :=
  fun _ hn h4 hnB => minGB_le_of_small msmallGBUpTo_1000900000 hn h4 (le_trans hnB (by norm_num))

/-- 1789 is the exact maximum of minGB on the even numbers from 4 to 10^9, attained at 721013438. -/
theorem minGB_max_upTo_1e9 :
    (∀ n : ℕ, Even n → 4 ≤ n → n ≤ 10 ^ 9 → LeanLab.Verifications.minGB n ≤ 1789) ∧
    LeanLab.Verifications.minGB 721013438 = 1789 :=
  ⟨minGB_le_1789_upTo_1e9, Records2.minGB_1789⟩

/-- No smaller bound on the small prime holds to 10^9. -/
theorem not_smallGB_lt_1789 {N : ℕ} (hN : N < 1789) : ¬ SmallGBUpTo N (10 ^ 9) := by
  intro h
  have := minGB_le_of_small h (n := 721013438) ⟨360506719, by norm_num⟩ (by norm_num) (by norm_num)
  rw [Records2.minGB_1789] at this
  omega

end LeanLab.Verifications.Top50.Bits

#print axioms LeanLab.Verifications.Top50.Bits.minGB_max_upTo_1e9
#print axioms LeanLab.Verifications.Top50.Bits.not_smallGB_lt_1789
