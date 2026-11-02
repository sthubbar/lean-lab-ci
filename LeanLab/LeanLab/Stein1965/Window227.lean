/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
A moving sum window for equations 2.2 and 2.3 on page 427.
-/
import LeanLab.Stein1965.Replay3
import LeanLab.Stein1965.Mask227

namespace LeanLab.Stein1965.Window227
open LeanLab.SteinStein1965
open LeanLab.Stein1965.Replay3
open LeanLab.Stein1965.Mask227

/-- Retain width bits starting at lo and store their indices relative to lo. -/
def slice (x lo width : ℕ) : ℕ := (x >>> lo) % 2 ^ width

theorem slice_testBit (x lo width k : ℕ) :
    (slice x lo width).testBit k = (decide (k < width) && x.testBit (lo + k)) := by
  simp [slice, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem slice_or (x y lo width : ℕ) :
    slice (x ||| y) lo width = slice x lo width ||| slice y lo width := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [slice_testBit, Nat.testBit_or]
  cases decide (k < width) <;> simp

theorem slice_slice (x lo width delta width' : ℕ) (h : delta + width' ≤ width) :
    slice (slice x lo width) delta width' = slice x (lo + delta) width' := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [slice_testBit]
  by_cases hk : k < width'
  · have hb : delta + k < width := by omega
    simp [hk, hb, Nat.add_assoc]
  · simp [hk]

/-- Keep the original basis and basis bits but only future sum bits through cap. -/
def window (s : BitState) (lo cap : ℕ) : BitState :=
  { s with sums := slice s.sums lo (cap + 1 - lo) }

/-- Insert a basis element while storing only its new sums in the current window. -/
def windowAdd (s : BitState) (a lo cap : ℕ) : BitState :=
  ⟨s.basis ++ [a], s.failures, s.bits ||| (1 <<< a),
    s.sums ||| slice (s.bits <<< a) lo (cap + 1 - lo) |||
      slice (1 <<< (a + a)) lo (cap + 1 - lo)⟩

theorem windowAdd_eq (s : BitState) (a lo cap : ℕ) :
    windowAdd (window s lo cap) a lo cap = window (bitAdd s a) lo cap := by
  simp only [windowAdd, window, bitAdd, slice_or]

def advance (s : BitState) (delta width : ℕ) : BitState :=
  { s with sums := slice s.sums delta width }

theorem advance_window (s : BitState) (lo next cap : ℕ)
    (hlo : lo ≤ next) :
    advance (window s lo cap) (next - lo) (cap + 1 - next) = window s next cap := by
  by_cases hn : next ≤ cap + 1
  · have hd : next - lo + (cap + 1 - next) ≤ cap + 1 - lo := by omega
    simp only [advance, window, slice_slice _ _ _ _ _ hd, Nat.add_sub_of_le hlo]
  · have hz : cap + 1 - next = 0 := by omega
    simp only [advance, window, hz, slice, pow_zero, Nat.mod_one]

/-- A step at the low end of a moving sum window. -/
def windowStep (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (s : BitState) (m cap : ℕ) : BitState :=
  if s.sums.testBit 0 then s
  else match choose m (fastCand isA s.basis m) with
    | some a => windowAdd s a m cap
    | none => { s with failures := s.failures ++ [m] }

theorem windowStep_eq (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (s : BitState) (m cap : ℕ) (hm : m ≤ cap) :
    windowStep isA choose (window s m cap) m cap =
      window (bitStep isA choose s m) m cap := by
  have ht : (window s m cap).sums.testBit 0 = s.sums.testBit m := by
    simp only [window, slice_testBit, Nat.add_zero,
      show decide (0 < cap + 1 - m) = true from decide_eq_true (by omega), Bool.true_and]
  simp only [windowStep, bitStep, ht]
  split
  · rfl
  · change (match choose m (fastCand isA s.basis m) with
        | some a => windowAdd (window s m cap) a m cap
        | none => { window s m cap with failures := s.failures ++ [m] }) = _
    cases ho : choose m (fastCand isA s.basis m) with
    | none => rfl
    | some a => exact windowAdd_eq s a m cap

end LeanLab.Stein1965.Window227
#print axioms LeanLab.Stein1965.Window227.slice_testBit
#print axioms LeanLab.Stein1965.Window227.slice_or
#print axioms LeanLab.Stein1965.Window227.slice_slice
#print axioms LeanLab.Stein1965.Window227.windowAdd_eq
#print axioms LeanLab.Stein1965.Window227.advance_window
#print axioms LeanLab.Stein1965.Window227.windowStep_eq
