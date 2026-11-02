/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Search a small low-bit block before falling back to the original search.
-/
import LeanLab.Stein1965.FastCore227

namespace LeanLab.Stein1965.SeekBlock227
open Core227 FastCore227

theorem seek_none_of_lt (bits m fuel lo : Nat) (h : m < lo) :
    fastSeek bits m fuel lo = none := by
  cases fuel <;> simp [fastSeek, h]

theorem seek_split (bits m f g lo : Nat) :
    fastSeek bits m (f + g) lo =
      match fastSeek bits m f lo with
      | some a => some a
      | none => fastSeek bits m g (lo + f) := by
  induction f generalizing lo with
  | zero => simp [fastSeek]
  | succ f ih =>
    rw [Nat.succ_add]
    by_cases hm : m < lo
    · simp [fastSeek, hm, seek_none_of_lt bits m g (lo + (f + 1)) (by omega)]
    · by_cases hb : bits.testBit lo = true ∧ fastPrime (m - lo) = true
      · simp [fastSeek, hm, hb]
      · simp only [fastSeek, Bool.and_eq_true, hm, hb, ↓reduceIte]
        rw [ih]
        rw [show lo + 1 + f = lo + (f + 1) by omega]

theorem seek_clip (bits m fuel lo width : Nat) (h : lo + fuel ≤ width) :
    fastSeek (bits % 2 ^ width) m fuel lo = fastSeek bits m fuel lo := by
  induction fuel generalizing lo with
  | zero => rfl
  | succ fuel ih =>
    have hl : lo < width := by omega
    have ht : (bits % 2 ^ width).testBit lo = bits.testBit lo := by
      rw [Nat.testBit_mod_two_pow]
      simp [hl]
    simp only [fastSeek, ht]
    by_cases hm : m < lo
    · simp [hm]
    · simp only [hm, ↓reduceIte]
      by_cases hb : bits.testBit lo = true ∧ fastPrime (m - lo) = true
      · simp [hb]
      · simp only [Bool.and_eq_true, hb, ↓reduceIte]
        exact ih (lo + 1) (by omega)

def blockSeek (bits m fuel lo : Nat) : Option Nat :=
  let first := min fuel (4096 - lo)
  match fastSeek (bits % 2 ^ 4096) m first lo with
  | some a => some a
  | none => fastSeek bits m (fuel - first) (lo + first)

theorem blockSeek_eq (bits m fuel lo : Nat) :
    blockSeek bits m fuel lo = fastSeek bits m fuel lo := by
  let first := min fuel (4096 - lo)
  have hf : first ≤ fuel := Nat.min_le_left _ _
  have hb : first ≤ 4096 - lo := Nat.min_le_right _ _
  change (match fastSeek (bits % 2 ^ 4096) m first lo with
    | some a => some a
    | none => fastSeek bits m (fuel - first) (lo + first)) = fastSeek bits m fuel lo
  by_cases hz : first = 0
  · simp [hz, fastSeek]
  · have hw : lo + first ≤ 4096 := by omega
    have hc := seek_clip bits m first lo 4096 hw
    have hs := seek_split bits m first (fuel - first) lo
    rw [Nat.add_sub_of_le hf] at hs
    rw [hc]
    exact hs.symm

end LeanLab.Stein1965.SeekBlock227
#print axioms LeanLab.Stein1965.SeekBlock227.seek_none_of_lt
#print axioms LeanLab.Stein1965.SeekBlock227.seek_split
#print axioms LeanLab.Stein1965.SeekBlock227.seek_clip
#print axioms LeanLab.Stein1965.SeekBlock227.blockSeek_eq
