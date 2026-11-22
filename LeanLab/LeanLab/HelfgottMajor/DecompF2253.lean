import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_short

/-!
# Split of the short-height conductor bounded estimate

This file refines the estimate on short heights when the conductor is at most the height.
The assumptions imply `2 ≤ q ≤ 20`, so the conductor range is finite.  The four leaves
below isolate four consecutive conductor blocks.  The assembly has the target statement
and has no gap of its own.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Conductor two block.  On this block the primitive character has level two and
the height is at most twenty, so only the zeros of that one function in a fixed strip
enter the count.  The estimate keeps the main term and the full error budget. -/
theorem book_zero_count_large_height_upper_short_conductor_le_height_F2253_q_two
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) (hq : q = 2) {T : ℝ}
    (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20) (hqT : (q : ℝ) ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Conductors three through eight.  The assumptions put both the conductor and
the height below twenty, so this block asks for the estimate only for the finitely many
primitive functions of levels three through eight.  The main term and error budget have
the same form as in the target. -/
theorem book_zero_count_large_height_upper_short_conductor_le_height_F2253_q_three_to_eight
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q)
    (hqlo : 3 ≤ q) (hqhi : q ≤ 8) {T : ℝ}
    (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20) (hqT : (q : ℝ) ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Conductors nine through fourteen.  The conductor and height are both below
twenty, so only a finite collection of primitive functions occurs.  The estimate retains
the main term and the full error budget on this middle conductor block. -/
theorem book_zero_count_large_height_upper_short_conductor_le_height_F2253_q_nine_to_fourteen
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q)
    (hqlo : 9 ≤ q) (hqhi : q ≤ 14) {T : ℝ}
    (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20) (hqT : (q : ℝ) ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Conductors fifteen through twenty.  These are the largest conductors allowed
when the conductor is at most the height and the height is at most twenty.  The estimate
keeps the main term and the full error budget for this last finite conductor block. -/
theorem book_zero_count_large_height_upper_short_conductor_le_height_F2253_q_fifteen_to_twenty
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q)
    (hqlo : 15 ≤ q) (hqhi : q ≤ 20) {T : ℝ}
    (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20) (hqT : (q : ℝ) ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly of the split.  The conductor is at most the height and the height is at
most twenty, hence the conductor is one of the integers from two through twenty.  The
four conductor blocks are exhaustive and disjoint. -/
theorem book_zero_count_large_height_upper_short_conductor_le_height_F2253
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) {T : ℝ}
    (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20) (hqT : (q : ℝ) ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  have hqT' : q ≤ T := by
    exact_mod_cast hqT
  have hq20 : q ≤ 20 := by omega
  interval_cases q <;>
    first
    | exact book_zero_count_large_height_upper_short_conductor_le_height_F2253_q_two χ hχ
        (by omega) (by omega) hT hT2 hT20 hqT hmain
    | exact book_zero_count_large_height_upper_short_conductor_le_height_F2253_q_three_to_eight
        χ hχ (by omega) (by omega) (by omega) hT hT2 hT20 hqT hmain
    | exact book_zero_count_large_height_upper_short_conductor_le_height_F2253_q_nine_to_fourteen
        χ hχ (by omega) (by omega) (by omega) hT hT2 hT20 hqT hmain
    | exact book_zero_count_large_height_upper_short_conductor_le_height_F2253_q_fifteen_to_twenty
        χ hχ (by omega) (by omega) (by omega) hT hT2 hT20 hqT hmain

#print axioms book_zero_count_large_height_upper_short_conductor_le_height_F2253

end LeanLab.HelfgottMajor.ZeroCount1623
