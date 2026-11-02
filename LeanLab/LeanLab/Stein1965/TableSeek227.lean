/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Use the proved divisor-table predicate in the clipped candidate search.
-/
import LeanLab.Stein1965.TableProof227
import LeanLab.Stein1965.SeekBlock227
namespace LeanLab.Stein1965.TableSeek227
open Core227 FastCore227 TablePrime227 TableProof227 SeekBlock227

def tableSeek (bits m : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, lo =>
    if m < lo then none
    else if bits.testBit lo && tablePrime (m - lo) then some (m - lo)
    else tableSeek bits m fuel (lo + 1)

theorem tableSeek_eq (bits m fuel lo : Nat) :
    tableSeek bits m fuel lo = fastSeek bits m fuel lo := by
  induction fuel generalizing lo with
  | zero => rfl
  | succ fuel ih => simp only [tableSeek, fastSeek, tablePrime_eq, fastPrime_eq, ih]

def tableBlock (bits m fuel lo : Nat) : Option Nat :=
  let first := min fuel (4096 - lo)
  match tableSeek (bits % 2 ^ 4096) m first lo with
  | some a => some a
  | none => fastSeek bits m (fuel - first) (lo + first)

theorem tableBlock_eq (bits m fuel lo : Nat) : tableBlock bits m fuel lo = fastSeek bits m fuel lo := by
  simp only [tableBlock, tableSeek_eq]
  exact blockSeek_eq bits m fuel lo

end LeanLab.Stein1965.TableSeek227
#print axioms LeanLab.Stein1965.TableSeek227.tableSeek_eq
#print axioms LeanLab.Stein1965.TableSeek227.tableBlock_eq
