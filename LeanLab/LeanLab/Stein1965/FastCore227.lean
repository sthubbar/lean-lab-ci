/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Skip even trial divisors without changing the original primality predicate.
-/
import LeanLab.Stein1965.CoreCheck227

namespace LeanLab.Stein1965.FastCore227
open Core227

/-- Pair consecutive trial steps and skip the even divisor. -/
def oddTrial (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, d =>
    if n < d * d then true else if n % d = 0 then false
    else if n < (d + 1) * (d + 1) then true else oddTrial n fuel (d + 2)

theorem oddTrial_eq (n fuel d : Nat) (hn : n % 2 = 1) (hd : d % 2 = 1) :
    oddTrial n fuel d = trial n (2 * fuel) d := by
  induction fuel generalizing d with
  | zero => rfl
  | succ fuel ih =>
    rw [show 2 * (fuel + 1) = (2 * fuel + 1) + 1 by omega, trial]
    simp only [oddTrial]
    by_cases hs : n < d * d
    · simp [hs]
    · simp only [hs, ↓reduceIte]
      by_cases hm : n % d = 0
      · simp [hm]
      · simp only [hm, ↓reduceIte]
        rw [trial]
        have he : n % (d + 1) ≠ 0 := by
          intro hz
          have h2d : 2 ∣ d + 1 := Nat.dvd_of_mod_eq_zero (by omega)
          have hdn : d + 1 ∣ n := Nat.dvd_of_mod_eq_zero hz
          have h2n : 2 ∣ n := Nat.dvd_trans h2d hdn
          have hzero := Nat.mod_eq_zero_of_dvd h2n
          omega
        by_cases hs' : n < (d + 1) * (d + 1)
        · simp [hs']
        · simp only [hs', he, ↓reduceIte]
          simpa only [show d + 1 + 1 = d + 2 by omega] using ih (d + 2) (by omega)

def fastPrime (n : Nat) : Bool :=
  if 3 ≤ n then
    if n % 2 = 1 then oddTrial n ((n - 1) / 2) 3 else false
  else false

theorem fastPrime_eq (n : Nat) : fastPrime n = prime n := by
  by_cases h3 : 3 ≤ n
  · by_cases ho : n % 2 = 1
    · by_cases hn3 : n = 3
      · subst n
        decide +kernel
      · have h4 : ¬ n < 2 * 2 := by omega
        have hn0 : n ≠ 0 := by omega
        have hf : n = (n - 1) + 1 := by omega
        have he : 2 * ((n - 1) / 2) = n - 1 := by omega
        rw [fastPrime, ite_eq_left h3, ite_eq_left ho, oddTrial_eq n _ 3 ho (by decide), he]
        simp only [prime, h3, decide_true, Bool.true_and]
        have h1 : (n == 1) = false := by simp [show n ≠ 1 by omega]
        have h2 : (n != 2) = true := by simp [show n ≠ 2 by omega]
        rw [h1, h2]
        simp only [Bool.false_or, Bool.true_and]
        change trial n (n - 1) 3 = (decide (2 ≤ n) && trial n n 2)
        rw [show decide (2 ≤ n) = true from decide_eq_true (by omega), Bool.true_and]
        have ht : trial n n 2 = trial n (n - 1) 3 := by
          calc
            trial n n 2 = trial n (n - 1 + 1) 2 := congrArg (fun f => trial n f 2) hf
            _ = trial n (n - 1) 3 := by
              rw [trial]
              simp [h4, show n % 2 ≠ 0 by omega]
        exact ht.symm
    · have h0 : n % 2 = 0 := by omega
      have h4 : ¬ n < 2 * 2 := by omega
      simp only [fastPrime, h3, ho, ↓reduceIte, prime, decide_true, Bool.true_and]
      have hf : n = (n - 1) + 1 := by omega
      have ht : trial n n 2 = false := by
        calc
          trial n n 2 = trial n (n - 1 + 1) 2 := congrArg (fun f => trial n f 2) hf
          _ = false := by rw [trial]; simp [h4, h0]
      simp [ht, show n ≠ 1 by omega]
  · simp [fastPrime, prime, h3]


def fastSeek (bits m : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, lo =>
    if m < lo then none
    else if bits.testBit lo && fastPrime (m - lo) then some (m - lo)
    else fastSeek bits m fuel (lo + 1)

theorem fastSeek_eq (bits m fuel lo : Nat) : fastSeek bits m fuel lo = seek bits m fuel lo := by
  induction fuel generalizing lo with
  | zero => rfl
  | succ fuel ih => simp only [fastSeek, seek, fastPrime_eq, ih]

def fastStep (s : State) (m cap : Nat) : State :=
  if s.2.2.2.testBit 0 then s
  else match fastSeek s.2.2.1 m (m + 1) 3 with
    | some a => add s a m cap
    | none => (s.1, s.2.1 ++ [m], s.2.2.1, s.2.2.2)

theorem fastStep_eq (s : State) (m cap : Nat) : fastStep s m cap = step s m cap := by
  simp only [fastStep, step, fastSeek_eq]
  rfl

def fastReplay : List Nat → Nat → Nat → State → Option State
  | [], _, _, s => some s
  | d :: ds, lo, cap, s =>
    if gap s d then
      let m := lo + 2 * d
      let atEvent := advance s (2 * d) (cap + 1 - m)
      let stepped := fastStep atEvent m cap
      let next := advance stepped 2 (cap + 1 - (m + 2))
      fastReplay ds (m + 2) cap next
    else none

theorem fastReplay_eq (gaps : List Nat) (lo cap : Nat) (s : State) :
    fastReplay gaps lo cap s = replay gaps lo cap s := by
  induction gaps generalizing lo s with
  | nil => rfl
  | cons d ds ih => simp only [fastReplay, replay, fastStep_eq, ih]

def fastCheck (gaps : List Nat) (lo cap : Nat) (s t : State) : Bool :=
  match fastReplay gaps lo cap s with
  | none => false
  | some u => CoreCheck227.same u t

theorem fastCheck_sound (gaps : List Nat) (lo cap : Nat) (s t : State)
    (h : fastCheck gaps lo cap s t = true) : replay gaps lo cap s = some t := by
  apply CoreCheck227.check_sound gaps lo cap s t
  unfold CoreCheck227.check
  unfold fastCheck at h
  rw [fastReplay_eq] at h
  exact h

end LeanLab.Stein1965.FastCore227
#print axioms LeanLab.Stein1965.FastCore227.oddTrial_eq
#print axioms LeanLab.Stein1965.FastCore227.fastPrime_eq

#print axioms LeanLab.Stein1965.FastCore227.fastSeek_eq
#print axioms LeanLab.Stein1965.FastCore227.fastStep_eq
#print axioms LeanLab.Stein1965.FastCore227.fastReplay_eq
#print axioms LeanLab.Stein1965.FastCore227.fastCheck_sound
