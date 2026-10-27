/-
AI wrote this Lean code. Codex task69, 2026-10-25.
Elementary translation of the arc estimates from a shifted period to zero through one.
Source: page 343 for the shifted period and pages 352 to 357 for the arc integrals.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.ModelPeriod
import LeanLab.Zinoviev1997.ArcInputs

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology LeanLab.CircleOrth MeasureTheory

theorem SZ_add_integer (N : ℕ) (α : ℝ) (k : ℤ) : SZ N (α + k) = SZ N α := by
  unfold SZ
  apply tsum_congr
  intro n
  rw [mul_add, ee_add]
  have he : ee ((n : ℝ) * k) = 1 := by
    have h := ee_integer ((n : ℤ) * k)
    simpa only [Int.cast_mul, Int.cast_natCast] using h
  rw [he, mul_one]

theorem SZ_periodic (N : ℕ) : Function.Periodic (SZ N) 1 := by
  intro α
  simpa using SZ_add_integer N α 1

/-- Integer translation preserves membership in the periodic major arcs. -/
theorem majorArcs_add_integer_iff (N : ℕ) (α : ℝ) (k : ℤ) :
    α + k ∈ majorArcs N ↔ α ∈ majorArcs N := by
  simp only [majorArcs, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, hq, a, ha, hac, j, hj⟩
    refine ⟨q, hq, a, ha, hac, j - k, ?_⟩
    have he : α + (a : ℝ) / q - ((j - k : ℤ) : ℝ) =
        (α + k) + (a : ℝ) / q - j := by push_cast; ring
    simpa only [he] using hj
  · rintro ⟨q, hq, a, ha, hac, j, hj⟩
    refine ⟨q, hq, a, ha, hac, j + k, ?_⟩
    have he : (α + k) + (a : ℝ) / q - ((j + k : ℤ) : ℝ) =
        α + (a : ℝ) / q - j := by push_cast; ring
    simpa only [he] using hj

/-- A minor arc bound on any closed full period gives the bound everywhere off the major arcs. -/
theorem minor_bound_of_window (N : ℕ) (t C : ℝ)
    (h : ∀ α ∈ Set.Icc t (t + 1) \ majorArcs N, ‖SZ N α‖ ≤ C)
    (α : ℝ) (hα : α ∉ majorArcs N) : ‖SZ N α‖ ≤ C := by
  let k : ℤ := ⌊α - t⌋
  have hk₁ : (k : ℝ) ≤ α - t := Int.floor_le (α - t)
  have hk₂ : α - t < (k : ℝ) + 1 := Int.lt_floor_add_one (α - t)
  have hb : α - k ∈ Set.Icc t (t + 1) := by
    constructor <;> linarith
  have he : α - k ∉ majorArcs N := by
    intro hh
    have hm := (majorArcs_add_integer_iff N (α - k) k).mpr hh
    exact hα (by simpa only [sub_add_cancel] using hm)
  have hh := h (α - k) ⟨hb, he⟩
  have hs := SZ_add_integer N (α - k) k
  simp only [sub_add_cancel] at hs
  simpa only [hs.symm] using hh

/-- Lemma 2.1 stated on another period supplies the fixed Lemma21Input.
This remains CONDITIONAL ON the minor arc estimate on that period. -/
theorem lemma21_of_window (N : ℕ) (t : ℝ)
    (h : ∀ α ∈ Set.Icc t (t + 1) \ majorArcs N,
      ‖SZ N α‖ ≤ 0.18 * N / Real.log N) : Lemma21Input N := by
  intro α hα
  exact minor_bound_of_window N t _ h α hα.2

end LeanLab.Zinoviev1997
