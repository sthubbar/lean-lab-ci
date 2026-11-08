import LeanLab.ExceptionalSet.BG2026Prop81MPR

/-!
P0029 page 32, the even multiples count in the proof of Theorem 8.2.
Source: https://arxiv.org/abs/2607.27282
For A greater than five halves the count grows faster than X to power three fifths.
The counting and power comparison helpers already exist in the lab.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp450h

open Real
open LeanLab.ExceptionalSet.BG2026 (evenMult)

/-- P0029 page 32, exact elementary count leaf of SPLIT_theorem82.
No major arc formula, zero hypothesis or prime distribution input is used. -/
theorem even_multiples_dominate_supplied :
    ∀ A : ℝ, 5 / 2 < A → ∃ r0 : ℕ, ∀ (r : ℕ) [NeZero r], r0 ≤ r →
      2 * (((r : ℝ) ^ A) ^ (3 / 5 : ℝ)) < ((evenMult r ((r : ℝ) ^ A)).card : ℝ) := by
  intro A hA
  have hAs : A * (3 / 5) < A - 1 := by linarith
  have hA1 : 0 < A - 1 := by linarith
  obtain ⟨x1, hx11, hx1⟩ := LeanLab.ExceptionalSet.BG2026.eventually_le_rpow
    (K := 16) hAs (by norm_num)
  obtain ⟨x2, _, hx2⟩ := LeanLab.ExceptionalSet.BG2026.eventually_le_rpow
    (a := 0) (K := 16) hA1 (by norm_num)
  refine ⟨⌈max x1 x2⌉₊, fun r _ hr => ?_⟩
  have hrx : max x1 x2 ≤ (r : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hr)
  have hrx1 : x1 ≤ (r : ℝ) := (le_max_left _ _).trans hrx
  have hrx2 : x2 ≤ (r : ℝ) := (le_max_right _ _).trans hrx
  have hr1 : (1 : ℝ) ≤ r := hx11.trans hrx1
  have hrpos : (0 : ℝ) < r := by linarith
  have hcount := LeanLab.ExceptionalSet.BG2026.evenMult_card_ge r
    (X := (r : ℝ) ^ A) (by positivity)
  have he : (r : ℝ) ^ A / (4 * r) = (r : ℝ) ^ (A - 1) / 4 := by
    rw [Real.rpow_sub_one hrpos.ne']
    field_simp
  rw [he] at hcount
  rw [← Real.rpow_mul hrpos.le]
  have hlarge := hx1 r hrx1
  have hconstant := hx2 r hrx2
  rw [Real.rpow_zero] at hconstant
  linarith

end LeanLab.ExceptionalSet.Decomp450h
