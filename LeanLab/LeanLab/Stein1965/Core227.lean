/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Core-only certificate checker for the seed 3 run on pages 428 and 429.
CoreBridge227 proves agreement with the full window replay.
-/
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Decide

namespace LeanLab.Stein1965.Core227

abbrev State := List Nat × List Nat × Nat × Nat

def trial (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, d => if n < d * d then true else if n % d = 0 then false else trial n fuel (d + 1)

def prime (n : Nat) : Bool :=
  decide (3 ≤ n) && (n == 1 || (n != 2 && (2 ≤ n && trial n n 2)))

def seek (bits m : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, lo =>
    if m < lo then none
    else if bits.testBit lo && prime (m - lo) then some (m - lo)
    else seek bits m fuel (lo + 1)

def slice (x lo width : Nat) : Nat := (x >>> lo) % 2 ^ width

def add (s : State) (a lo cap : Nat) : State :=
  (s.1 ++ [a], s.2.1, s.2.2.1 ||| (1 <<< a),
    s.2.2.2 ||| slice (s.2.2.1 <<< a) lo (cap + 1 - lo) |||
      slice (1 <<< (a + a)) lo (cap + 1 - lo))

def advance (s : State) (delta width : Nat) : State :=
  (s.1, s.2.1, s.2.2.1, slice s.2.2.2 delta width)

def step (s : State) (m cap : Nat) : State :=
  if s.2.2.2.testBit 0 then s
  else match seek s.2.2.1 m (m + 1) 3 with
    | some a => add s a m cap
    | none => (s.1, s.2.1 ++ [m], s.2.2.1, s.2.2.2)

def gap (s : State) (d : Nat) : Bool :=
  let mask := (4 ^ d - 1) / 3
  (s.2.2.2 &&& mask) == mask

def length (gaps : List Nat) : Nat := (gaps.map (· + 1)).sum

def replay : List Nat → Nat → Nat → State → Option State
  | [], _, _, s => some s
  | d :: ds, lo, cap, s =>
    if gap s d then
      let m := lo + 2 * d
      let atEvent := advance s (2 * d) (cap + 1 - m)
      let stepped := step atEvent m cap
      let next := advance stepped 2 (cap + 1 - (m + 2))
      replay ds (m + 2) cap next
    else none

theorem replay_append (xs ys : List Nat) (lo cap : Nat) (s : State) :
    replay (xs ++ ys) lo cap s =
      (replay xs lo cap s).bind (fun t => replay ys (lo + 2 * length xs) cap t) := by
  induction xs generalizing lo s with
  | nil => simp [replay, length]
  | cons d ds ih =>
    simp only [List.cons_append, replay]
    by_cases hg : gap s d = true
    · simp only [hg, ↓reduceIte]
      rw [ih]
      congr 1
      funext t
      congr 1
      simp [length]
      omega
    · simp [hg]

theorem replay_join (xs ys : List Nat) (lo next cap : Nat) (s t u : State)
    (hn : lo + 2 * length xs = next)
    (hx : replay xs lo cap s = some t) (hy : replay ys next cap t = some u) :
    replay (xs ++ ys) lo cap s = some u := by
  rw [replay_append, hn, hx]
  exact hy

end LeanLab.Stein1965.Core227
#print axioms LeanLab.Stein1965.Core227.replay_append
#print axioms LeanLab.Stein1965.Core227.replay_join
