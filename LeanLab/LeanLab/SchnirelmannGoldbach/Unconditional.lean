/-
Schnirelmann's theorem, 1930: every integer n ≥ 2 is a sum of at most H primes, for some
absolute H. Unconditional, zero sorry. The bound H is not explicit.
AI-written Lean code, Claude, 2026-10-16. Uses a port of the PNT+ Selberg sieve by
Arend Mellendijk, Apache 2.0.
-/
import LeanLab.SchnirelmannGoldbach.Main
import LeanLab.SchnirelmannGoldbach.S1.Final

namespace LeanLab.SchnirelmannGoldbach

theorem schnirelmann_bounded_primes :
    ∃ H : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H, SumOfPrimes k n :=
  schnirelmann_goldbach_of_S1u S1u_holds

end LeanLab.SchnirelmannGoldbach
