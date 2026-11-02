/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Equivalence of the core checker and the moving BitState window.
Equations 2.2 and 2.3 on page 427.
-/
import LeanLab.Stein1965.Core227
import LeanLab.Stein1965.WindowReplay227

namespace LeanLab.Stein1965.CoreBridge227
open LeanLab.SteinStein1965
open LeanLab.Stein1965.WindowReplay227

/-- The same four fields, using a core tuple instead of BitState. -/
def pack (s : BitState) : Core227.State := (s.basis, s.failures, s.bits, s.sums)

theorem trial_eq (n fuel d : ℕ) : Core227.trial n fuel d = LeanLab.noDivFrom n fuel d := by
  induction fuel generalizing d with
  | zero => rfl
  | succ fuel ih => simp only [Core227.trial, LeanLab.noDivFrom, ih]

theorem prime_eq (n : ℕ) : Core227.prime n = primeA 3 n := by
  simp only [Core227.prime, primeA, LeanLab.primeB, trial_eq]

theorem seek_eq (bits m fuel lo : ℕ) :
    Core227.seek bits m fuel lo = seekAux (primeA 3) bits m fuel lo := by
  induction fuel generalizing lo with
  | zero => rfl
  | succ fuel ih => simp only [Core227.seek, seekAux, prime_eq, ih]

theorem advance_pack (s : BitState) (delta width : ℕ) :
    Core227.advance (pack s) delta width = pack (Window227.advance s delta width) := rfl

theorem add_pack (s : BitState) (a lo cap : ℕ) :
    Core227.add (pack s) a lo cap = pack (Window227.windowAdd s a lo cap) := rfl

theorem step_pack (s : BitState) (m cap : ℕ) :
    Core227.step (pack s) m cap = pack (windowSeekStep (fun _ a => a) s m cap) := by
  simp only [Core227.step, windowSeekStep, pack, seek_eq]
  split
  · rfl
  · cases seekAux (primeA 3) s.bits m (m + 1) 3 <;> rfl

theorem gap_pack (s : BitState) (d : ℕ) :
    Core227.gap (pack s) d = Mask227.gapCheckClosed s 0 d := rfl

theorem replay_pack (gaps : List ℕ) (lo cap : ℕ) (s : BitState) :
    Core227.replay gaps lo cap (pack s) =
      (windowReplay (fun _ a => a) gaps lo cap s).map pack := by
  induction gaps generalizing lo s with
  | nil => rfl
  | cons d ds ih =>
    simp only [Core227.replay, windowReplay, gap_pack]
    by_cases hg : Mask227.gapCheckClosed s 0 d = true
    · simp only [hg, ↓reduceIte, advance_pack, step_pack, ih]
    · simp [hg]

end LeanLab.Stein1965.CoreBridge227
#print axioms LeanLab.Stein1965.CoreBridge227.trial_eq
#print axioms LeanLab.Stein1965.CoreBridge227.prime_eq
#print axioms LeanLab.Stein1965.CoreBridge227.seek_eq
#print axioms LeanLab.Stein1965.CoreBridge227.advance_pack
#print axioms LeanLab.Stein1965.CoreBridge227.add_pack
#print axioms LeanLab.Stein1965.CoreBridge227.step_pack
#print axioms LeanLab.Stein1965.CoreBridge227.gap_pack
#print axioms LeanLab.Stein1965.CoreBridge227.replay_pack
