/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Project the original replay to the bounded count and failure list.
-/
import LeanLab.Stein1965.TableSeek227

namespace LeanLab.Stein1965.CountCore227
open Core227 FastCore227 SeekBlock227 TableSeek227

abbrev SmallState := Nat × List Nat × Nat × Nat

def project (s : State) (cap : Nat) : SmallState :=
  ((s.1.filter (fun a => decide (a ≤ cap))).length, s.2.1, s.2.2.1, s.2.2.2)

def smallAdd (s : SmallState) (a lo cap : Nat) : SmallState :=
  (if a ≤ cap then s.1 + 1 else s.1, s.2.1, s.2.2.1 ||| (1 <<< a),
    s.2.2.2 ||| slice (s.2.2.1 <<< a) lo (cap + 1 - lo) |||
      slice (1 <<< (a + a)) lo (cap + 1 - lo))

theorem smallAdd_project (s : State) (a lo cap : Nat) :
    smallAdd (project s cap) a lo cap = project (add s a lo cap) cap := by
  by_cases ha : a ≤ cap <;> simp [smallAdd, project, add, ha]

def smallAdvance (s : SmallState) (delta width : Nat) : SmallState :=
  (s.1, s.2.1, s.2.2.1, slice s.2.2.2 delta width)

theorem smallAdvance_project (s : State) (delta width cap : Nat) :
    smallAdvance (project s cap) delta width = project (advance s delta width) cap := rfl

def smallStep (s : SmallState) (m cap : Nat) : SmallState :=
  if s.2.2.2.testBit 0 then s
  else match tableBlock s.2.2.1 m (m + 1) 3 with
    | some a => smallAdd s a m cap
    | none => (s.1, s.2.1 ++ [m], s.2.2.1, s.2.2.2)

theorem smallStep_project (s : State) (m cap : Nat) :
    smallStep (project s cap) m cap = project (fastStep s m cap) cap := by
  by_cases hs : s.2.2.2.testBit 0 = true
  · simp [smallStep, fastStep, project, hs]
  · simp only [smallStep, fastStep, project, tableBlock_eq, hs, ↓reduceIte]
    cases ho : fastSeek s.2.2.1 m (m + 1) 3 with
    | none => rfl
    | some a => exact smallAdd_project s a m cap

def smallGap (s : SmallState) (d : Nat) : Bool :=
  let mask := (4 ^ d - 1) / 3
  (s.2.2.2 &&& mask) == mask

def smallReplay : List Nat → Nat → Nat → SmallState → Option SmallState
  | [], _, _, s => some s
  | d :: ds, lo, cap, s =>
    if smallGap s d then
      let m := lo + 2 * d
      let atEvent := smallAdvance s (2 * d) (cap + 1 - m)
      let stepped := smallStep atEvent m cap
      let next := smallAdvance stepped 2 (cap + 1 - (m + 2))
      smallReplay ds (m + 2) cap next
    else none

theorem smallReplay_project (gaps : List Nat) (lo cap : Nat) (s : State) :
    smallReplay gaps lo cap (project s cap) = (replay gaps lo cap s).map (fun t => project t cap) := by
  have hr : smallReplay gaps lo cap (project s cap) =
      (fastReplay gaps lo cap s).map (fun t => project t cap) := by
    induction gaps generalizing lo s with
    | nil => rfl
    | cons d ds ih =>
      have hg : smallGap (project s cap) d = gap s d := rfl
      simp only [smallReplay, fastReplay, hg]
      by_cases h : gap s d = true
      · simp only [h, ↓reduceIte, smallAdvance_project, smallStep_project, ih]
      · simp [h]
  simpa only [fastReplay_eq] using hr

def same (s t : SmallState) : Bool :=
  (s.1 == t.1) && (s.2.1 == t.2.1) && (s.2.2.1 == t.2.2.1) && (s.2.2.2 == t.2.2.2)

theorem same_sound (s t : SmallState) (h : same s t = true) : s = t := by
  simp only [same, Bool.and_eq_true, beq_iff_eq] at h
  exact Prod.ext h.1.1.1 (Prod.ext h.1.1.2 (Prod.ext h.1.2 h.2))

def smallCheck (gaps : List Nat) (lo cap : Nat) (s t : SmallState) : Bool :=
  match smallReplay gaps lo cap s with
  | none => false
  | some u => same u t

theorem smallCheck_sound (gaps : List Nat) (lo cap : Nat) (s t : SmallState)
    (h : smallCheck gaps lo cap s t = true) : smallReplay gaps lo cap s = some t := by
  cases he : smallReplay gaps lo cap s with
  | none => simp [smallCheck, he] at h
  | some u => exact congrArg some (same_sound u t (by simpa only [smallCheck, he] using h))

theorem smallReplay_append (xs ys : List Nat) (lo cap : Nat) (s : SmallState) :
    smallReplay (xs ++ ys) lo cap s =
      (smallReplay xs lo cap s).bind (fun t => smallReplay ys (lo + 2 * length xs) cap t) := by
  induction xs generalizing lo s with
  | nil => simp [smallReplay, length]
  | cons d ds ih =>
    simp only [List.cons_append, smallReplay]
    by_cases hg : smallGap s d = true
    · simp only [hg, ↓reduceIte]
      rw [ih]
      congr 1
      funext t
      congr 1
      simp [length]
      omega
    · simp [hg]

theorem smallReplay_join (xs ys : List Nat) (lo next cap : Nat) (s t u : SmallState)
    (hn : lo + 2 * length xs = next)
    (hx : smallReplay xs lo cap s = some t) (hy : smallReplay ys next cap t = some u) :
    smallReplay (xs ++ ys) lo cap s = some u := by
  rw [smallReplay_append, hn, hx]
  exact hy

end LeanLab.Stein1965.CountCore227
#print axioms LeanLab.Stein1965.CountCore227.smallAdd_project
#print axioms LeanLab.Stein1965.CountCore227.smallAdvance_project
#print axioms LeanLab.Stein1965.CountCore227.smallStep_project
#print axioms LeanLab.Stein1965.CountCore227.smallReplay_project
#print axioms LeanLab.Stein1965.CountCore227.same_sound
#print axioms LeanLab.Stein1965.CountCore227.smallCheck_sound
#print axioms LeanLab.Stein1965.CountCore227.smallReplay_append
#print axioms LeanLab.Stein1965.CountCore227.smallReplay_join
