/-
P0017 Richstein 2001, unit U-1459, run 20261022T0003Z-15508: the kernel check behind
U1459GapExact.lean, core Lean only, reusing the trial division of GapCheck.lean. For every m from
2 to 89688: if m passes trial division and m + 64 passes trial division, then some number in
[m + 1, m + 63] passes too. So no two consecutive primes below 89689 differ by exactly 64.
Soundness is proved in U1459GapExact.lean.
AI-written Lean code, Claude, 2026-10-22. Binary Goldbach is OPEN.
-/
import LeanLab.Richstein2001.GapCheck

namespace LeanLab.Richstein2001.Core

/-- The condition at m: m is not prime, or m + 64 is not prime, or a prime lies strictly between. -/
def okExact (m : Nat) : Bool := !primeC m || !primeC (m + 64) || nextWithin m

def chkE (a b : Nat) : Bool := (List.range (b - a)).all (fun i => okExact (a + i))

set_option Elab.async false

theorem chkE_1 : chkE 2 15000 = true := by decide +kernel

end LeanLab.Richstein2001.Core
