/-
Saouter 1998, Lemma 1, page 864, citing Brillhart, Lehmer and Selfridge 1975,
Theorem 5. This is a proposition stating the cited criterion, with no proof claim.
Known factorization of F concerns certificate construction and is not an extra
mathematical restriction on a natural number F.
AI wrote this Lean code for CODEX task73. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Saouter1998.BLS

/-- Saouter's cited Lemma 1. This proposition has no proof in this module. -/
def Lemma1 : Prop :=
  ∀ F R : ℕ, ∀ a : ℤ,
    Odd (R * F + 1) → Even F → Nat.Coprime R F →
    (a : ZMod (R * F + 1)) ^ (R * F) = 1 →
    (∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ (R * F / p) - 1) (R * F + 1) = 1) →
    R * F + 1 < 2 * F ^ 3 →
    ((R * F + 1).Prime ↔
      R / (2 * F) = 0 ∨
        ¬ IsSquare (((R % (2 * F) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * F) : ℕ) : ℤ)))

end LeanLab.Saouter1998.BLS
