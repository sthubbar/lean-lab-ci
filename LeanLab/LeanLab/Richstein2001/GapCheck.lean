/-
P0017 Richstein 2001: the kernel check behind Gap.lean, core Lean only, no Mathlib, so the
check fits in memory. For every m from 2 to 31396, if m passes trial division then some number
in [m + 1, m + 63] does too. Soundness is proved in Gap.lean.
AI-written Lean code, Claude, 2026-10-18, run 20261018T1103Z-12430. Binary Goldbach is OPEN.
-/

namespace LeanLab.Richstein2001.Core

/-- Trial division from d, the same recursion as LeanLab.noDivFrom. -/
def noDivFrom (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, d => if n < d * d then true else if n % d = 0 then false else noDivFrom n fuel (d + 1)

def primeC (n : Nat) : Bool := 2 ≤ n && noDivFrom n n 2

def nextWithin (p : Nat) : Bool := (List.range 63).any (fun i => primeC (p + 1 + i))

def chk (a b : Nat) : Bool :=
  (List.range (b - a)).all (fun i => !primeC (a + i) || nextWithin (a + i))

set_option Elab.async false

theorem chk_1 : chk 2 8000 = true := by decide +kernel
theorem chk_2 : chk 8000 16000 = true := by decide +kernel
theorem chk_3 : chk 16000 24000 = true := by decide +kernel
theorem chk_4 : chk 24000 31397 = true := by decide +kernel

end LeanLab.Richstein2001.Core
