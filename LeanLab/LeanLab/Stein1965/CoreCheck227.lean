/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Boolean boundary comparison avoids constructing recursive list equality decisions.
-/
import LeanLab.Stein1965.Core227

namespace LeanLab.Stein1965.CoreCheck227
open Core227

def same (s t : State) : Bool :=
  (s.1 == t.1) && (s.2.1 == t.2.1) && (s.2.2.1 == t.2.2.1) && (s.2.2.2 == t.2.2.2)

theorem same_sound (s t : State) (h : same s t = true) : s = t := by
  simp only [same, Bool.and_eq_true, beq_iff_eq] at h
  exact Prod.ext h.1.1.1 (Prod.ext h.1.1.2 (Prod.ext h.1.2 h.2))

def check (gaps : List Nat) (lo cap : Nat) (s t : State) : Bool :=
  match replay gaps lo cap s with
  | none => false
  | some u => same u t

theorem check_sound (gaps : List Nat) (lo cap : Nat) (s t : State)
    (h : check gaps lo cap s t = true) : replay gaps lo cap s = some t := by
  cases he : replay gaps lo cap s with
  | none => simp [check, he] at h
  | some u =>
    have hu : u = t := same_sound u t (by simpa only [check, he] using h)
    exact congrArg some hu

theorem length_append (xs ys : List Nat) : length (xs ++ ys) = length xs + length ys := by
  induction xs with
  | nil => simp [length]
  | cons d ds ih =>
    simp only [List.cons_append, length, List.map_cons, List.sum_cons] at ih ⊢
    omega

end LeanLab.Stein1965.CoreCheck227
#print axioms LeanLab.Stein1965.CoreCheck227.same_sound
#print axioms LeanLab.Stein1965.CoreCheck227.check_sound
#print axioms LeanLab.Stein1965.CoreCheck227.length_append
