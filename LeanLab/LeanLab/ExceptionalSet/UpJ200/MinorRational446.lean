import LeanLab.ExceptionalSet.UpJ200.Decomp428c
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.MinorRational446`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
Real Dirichlet approximation on the literal minor arc complement.
Source: P0082 page 357, major arc definition, and page 366 after display 27.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.MinorRational446

open Real
open LeanLab.ExceptionalSet.U1539 (majorArcs)

/-- P0082 page 366 after display 27. Dirichlet approximation on the
minor arcs has reduced denominator above P and at most X divided by P.
This is an auxiliary real frequency version of the approximation step. -/
theorem minor_rational (P X β : ℝ) (hP : 0 < P) (hX : 0 < X) (hPX : P ≤ X)
    (hminor : β ∉ majorArcs P X) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ P < q ∧ (q : ℝ) ≤ X / P ∧
      Int.gcd a q = 1 ∧ |β - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
  let Q := X / P
  have hQ1 : 1 ≤ Q := (le_div_iff₀ hP).mpr (by simpa using hPX)
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hfloor : 0 < ⌊Q⌋₊ := Nat.floor_pos.mpr hQ1
  obtain ⟨r, hr, hrq⟩ := Real.exists_rat_abs_sub_le_and_den_le β hfloor
  let q := r.den
  have hq1 : 1 ≤ q := r.den_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast r.den_pos
  have hqQ : (q : ℝ) ≤ Q := by
    have hqfloor : (q : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast hrq
    exact hqfloor.trans (Nat.floor_le hQ.le)
  have hrval : (r : ℝ) = (r.num : ℝ) / (q : ℝ) := by
    exact_mod_cast (Rat.num_div_den r).symm
  have hap : |β - r.num / q| ≤ 1 / ((q : ℝ) * Q) := by
    rw [hrval] at hr
    refine hr.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have hQfloor := (Nat.lt_floor_add_one Q).le
    nlinarith
  have hqP : P < (q : ℝ) := by
    by_contra hn
    have hqp : (q : ℝ) ≤ P := le_of_not_gt hn
    apply hminor
    refine ⟨q, r.num, hq1, hqp, r.reduced, ?_⟩
    have he : (q : ℝ) * β - r.num = (q : ℝ) * (β - r.num / q) := by
      field_simp
    rw [he, abs_mul, abs_of_pos hq0]
    calc
      _ ≤ (q : ℝ) * (1 / ((q : ℝ) * Q)) := mul_le_mul_of_nonneg_left hap hq0.le
      _ = P / X := by dsimp [Q]; field_simp
  refine ⟨r.num, q, hq1, hqP, hqQ, r.reduced, hap.trans ?_⟩
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

end LeanLab.ExceptionalSet.UpJ200.MinorRational446
