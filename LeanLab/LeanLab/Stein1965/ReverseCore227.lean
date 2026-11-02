/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Prepend to a reversed basis during certificate evaluation.
The public certificate statements keep the original basis order.
-/
import LeanLab.Stein1965.FastCore227

namespace LeanLab.Stein1965.ReverseCore227
open Core227 FastCore227

def reverseState (s : State) : State := (s.1.reverse, s.2.1, s.2.2.1, s.2.2.2)

theorem reverseState_injective : Function.Injective reverseState := by
  intro s t h
  have hb := congrArg (fun u : State => u.1) h
  have hf := congrArg (fun u : State => u.2) h
  exact Prod.ext (List.reverse_inj.mp hb) hf

def reverseAdd (s : State) (a lo cap : Nat) : State :=
  (a :: s.1, s.2.1, s.2.2.1 ||| (1 <<< a),
    s.2.2.2 ||| slice (s.2.2.1 <<< a) lo (cap + 1 - lo) |||
      slice (1 <<< (a + a)) lo (cap + 1 - lo))

theorem reverseAdd_eq (s : State) (a lo cap : Nat) :
    reverseAdd (reverseState s) a lo cap = reverseState (add s a lo cap) := by
  simp only [reverseAdd, reverseState, add, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append]

theorem reverseAdvance_eq (s : State) (delta width : Nat) :
    advance (reverseState s) delta width = reverseState (advance s delta width) := rfl

def reverseStep (s : State) (m cap : Nat) : State :=
  if s.2.2.2.testBit 0 then s
  else match fastSeek s.2.2.1 m (m + 1) 3 with
    | some a => reverseAdd s a m cap
    | none => (s.1, s.2.1 ++ [m], s.2.2.1, s.2.2.2)

theorem reverseStep_eq (s : State) (m cap : Nat) :
    reverseStep (reverseState s) m cap = reverseState (fastStep s m cap) := by
  by_cases hs : s.2.2.2.testBit 0 = true
  · simp [reverseStep, fastStep, reverseState, hs]
  · simp only [reverseStep, fastStep, reverseState, hs, ↓reduceIte]
    cases ho : fastSeek s.2.2.1 m (m + 1) 3 with
    | none => rfl
    | some a => exact reverseAdd_eq s a m cap

def reverseReplay : List Nat → Nat → Nat → State → Option State
  | [], _, _, s => some s
  | d :: ds, lo, cap, s =>
    if gap s d then
      let m := lo + 2 * d
      let atEvent := advance s (2 * d) (cap + 1 - m)
      let stepped := reverseStep atEvent m cap
      let next := advance stepped 2 (cap + 1 - (m + 2))
      reverseReplay ds (m + 2) cap next
    else none

theorem reverseReplay_eq (gaps : List Nat) (lo cap : Nat) (s : State) :
    reverseReplay gaps lo cap (reverseState s) =
      (fastReplay gaps lo cap s).map reverseState := by
  induction gaps generalizing lo s with
  | nil => rfl
  | cons d ds ih =>
    have hg : gap (reverseState s) d = gap s d := rfl
    simp only [reverseReplay, fastReplay, hg]
    by_cases h : gap s d = true
    · simp only [h, ↓reduceIte, reverseAdvance_eq, reverseStep_eq, ih]
    · simp [h]

def reverseCheck (gaps : List Nat) (lo cap : Nat) (s t : State) : Bool :=
  match reverseReplay gaps lo cap (reverseState s) with
  | none => false
  | some u => CoreCheck227.same u (reverseState t)

theorem reverseCheck_sound (gaps : List Nat) (lo cap : Nat) (s t : State)
    (h : reverseCheck gaps lo cap s t = true) : replay gaps lo cap s = some t := by
  have hr := reverseReplay_eq gaps lo cap s
  rw [fastReplay_eq] at hr
  cases he : replay gaps lo cap s with
  | none =>
    rw [he] at hr
    simp only [Option.map_none] at hr
    simp only [reverseCheck, hr] at h
    contradiction
  | some u =>
    rw [he] at hr
    simp only [Option.map_some] at hr
    have hu := CoreCheck227.same_sound _ _ (by simpa only [reverseCheck, hr] using h)
    exact congrArg some (reverseState_injective hu)

end LeanLab.Stein1965.ReverseCore227
#print axioms LeanLab.Stein1965.ReverseCore227.reverseState_injective
#print axioms LeanLab.Stein1965.ReverseCore227.reverseAdd_eq
#print axioms LeanLab.Stein1965.ReverseCore227.reverseAdvance_eq
#print axioms LeanLab.Stein1965.ReverseCore227.reverseStep_eq
#print axioms LeanLab.Stein1965.ReverseCore227.reverseReplay_eq
#print axioms LeanLab.Stein1965.ReverseCore227.reverseCheck_sound
