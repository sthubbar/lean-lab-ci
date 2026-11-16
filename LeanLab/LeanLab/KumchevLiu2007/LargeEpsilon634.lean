/-
Support reductions for the unwritten large epsilon residue of display 53.
The paper uses small epsilon. These are derived support statements for the
sealed lab encoding, not additional claims from the paper.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp129

namespace LeanLab.KumchevLiu2007.Task634

open Real Complex Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 2 display 5: the square window forces every represented
integer to be at least Y over four. -/
theorem windowPairs_empty_below (X Y : ℝ) (hY : 0 ≤ Y) (n : ℕ)
    (hn : (n : ℝ) < Y / 4) : Task129.windowPairs X Y n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨_, _, _, hl, _, he⟩ := Finset.mem_filter.mp hv
  have hs := Real.sq_sqrt hY
  have hr := Real.sqrt_nonneg Y
  have hm := Nat.cast_nonneg (α := ℝ) v.2
  have hv1 := Nat.cast_nonneg (α := ℝ) v.1
  have he' : (v.1 : ℝ) + (v.2 : ℝ) ^ 2 = (n : ℝ) := by exact_mod_cast he
  have hsq : (Real.sqrt Y / 2) ^ 2 ≤ (v.2 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) hm).mpr hl
  nlinarith

/-- P0088 page 16 display 53: below the support both the rough count and
the singular integral vanish, so the display 53 error is zero. -/
theorem err53_vanish_below (X ε B : ℝ) (n : ℕ) (hY : 0 ≤ Task129.windowY X ε)
    (hn : (n : ℝ) < Task129.windowY X ε / 4) : Task129.err53 X ε B n = 0 := by
  simp [Task129.err53, Task129.roughCount, Task129.singInt,
    windowPairs_empty_below X _ hY n hn]

/-- The page 16 choice of Y eventually exceeds eight times X when epsilon
exceeds five sixths. This is a support consequence for the lab's large range. -/
theorem eventually_large_window (ε : ℝ) (hε : 5 / 6 < ε) :
    ∀ᶠ X : ℝ in atTop, 2 ≤ X ∧ 2 * X < Task129.windowY X ε / 4 := by
  have hd : 0 < ε / 2 - 5 / 12 := by linarith
  have hp : ∀ᶠ X : ℝ in atTop, 12 ≤ X ^ (ε / 2 - 5 / 12) :=
    (tendsto_rpow_atTop hd).eventually (eventually_ge_atTop 12)
  filter_upwards [hp, eventually_ge_atTop (2 : ℝ)] with X hp hX
  refine ⟨hX, ?_⟩
  have hX0 : 0 < X := by linarith
  have he : Task129.windowY X ε = X * X ^ (ε / 2 - 5 / 12) := by
    unfold Task129.windowY
    rw [show (7 / 12 + ε / 2 : ℝ) = 1 + (ε / 2 - 5 / 12) by ring,
      Real.rpow_add hX0, Real.rpow_one]
  rw [he]
  nlinarith

/-- P0088 page 16 display 53, derived support reduction: for epsilon above
five sixths there are eventually no error exceptions anywhere with H at most X. -/
theorem eq53_very_large_eps (A B ε : ℝ) (hε : 5 / 6 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ H : ℝ, 0 ≤ H → H ≤ X →
      cntIoc (fun n => InH2 n ∧
        Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
          Task129.err53 X ε B n) X H = 0 := by
  filter_upwards [eventually_large_window ε hε] with X hX
  intro H hH hHX
  unfold cntIoc
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨hr, _, _, herr⟩ := hn
  have hnf : n ≤ ⌊X + H⌋₊ := Nat.lt_succ_iff.mp hr
  have hnr : (n : ℝ) ≤ X + H :=
    (Nat.cast_le.mpr hnf).trans (Nat.floor_le (by linarith [hX.1]))
  have hY : 0 ≤ Task129.windowY X ε := Real.rpow_nonneg (by linarith [hX.1]) _
  rw [err53_vanish_below X ε B n hY (by linarith [hX.2])] at herr
  exact (not_lt_of_ge (mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (Real.log_nonneg (by linarith [hX.1])) _))) herr

end LeanLab.KumchevLiu2007.Task634

#print axioms LeanLab.KumchevLiu2007.Task634.windowPairs_empty_below
#print axioms LeanLab.KumchevLiu2007.Task634.err53_vanish_below
#print axioms LeanLab.KumchevLiu2007.Task634.eventually_large_window
#print axioms LeanLab.KumchevLiu2007.Task634.eq53_very_large_eps
