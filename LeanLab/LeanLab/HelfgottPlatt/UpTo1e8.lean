/-
Ternary Goldbach up to 10^8, checked by the Lean kernel with no cited input, unit U-0341,
run 20261017T1803Z-21479. Helfgott and Platt's ladder method, P0006, in miniature: binary
Goldbach to 10^5 from the lab's kernel check, evenGoldbachUpTo_1e5, plus a ladder of 1001
primes from 3 to 99982709 with gaps at most 99996, each prime by trial division over P10k, the last few by norm_num.
AI-written Lean code, Claude, 2026-10-17. Ternary Goldbach is Helfgott's theorem; the point
here is a kernel-checked range with no cited input. Binary Goldbach is OPEN.
-/
import LeanLab.HelfgottPlatt.Ladder
import LeanLab.HelfgottPlatt.LadderData
import LeanLab.HelfgottPlatt.LadderC1
import LeanLab.HelfgottPlatt.LadderC2
import LeanLab.HelfgottPlatt.LadderC3
import LeanLab.HelfgottPlatt.LadderC4
import LeanLab.HelfgottPlatt.LadderC5
import LeanLab.HelfgottPlatt.LadderC6
import LeanLab.Verifications.Top50.FastUpTo

namespace LeanLab.HelfgottPlatt

theorem ladder_prime : ∀ p ∈ ladder, p.Prime := by
  have h15 : ∀ p ∈ t1 ++ t2 ++ t3 ++ t4 ++ t5, p.Prime := by
    apply all_prime_of
    simp only [List.all_append, c1, c2, c3, c4, c5, Bool.and_self]
  intro p hp
  rw [ladder, List.mem_append] at hp
  rcases hp with hp | hp
  · exact h15 p hp
  · exact t6_prime p hp

theorem ladder_chain : (3 :: ladder).IsChain (LadderStep (10 ^ 5)) :=
  chainB_sound _ _ (by decide +kernel)

theorem ladder_last : ladder.getLastD 3 = 99982709 := by decide +kernel

/-- Every odd n with 7 ≤ n ≤ 10^8 is a sum of three primes, kernel checked, no cited input. -/
theorem ternaryGoldbachUpTo_1e8 : TernaryGoldbachUpTo (10 ^ 8) :=
  ternary_of_ladder LeanLab.Verifications.Top50.Fast.evenGoldbachUpTo_1e5 ladder ladder_prime
    ladder_chain (by rw [ladder_last]; norm_num)

end LeanLab.HelfgottPlatt
