import LeanLab.Pintz2021.VaughanBoundTask08

/-!
The variable major arc level minor remainder for P0054 page 9 display 3.1.
The proved task08 Lemma 1 and the existing finite Bessel bound are reused.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.MinorArc168

open Finset MinorArcs Lemma1U1369

/-- The minor remainder mean square at every admissible level P. -/
theorem minor_arc_remainder :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ X1 X P : ℝ, 2 ≤ X1 → X1 ≤ X → 3 ≤ X →
      1 ≤ P → P ≤ X → ∀ mi : Set ℝ, MeasurableSet mi →
        mi ⊆ (majorArcs P (X / P))ᶜ → ∀ M : ℕ,
          ∑ m ∈ range M, ‖R2 (S X1 X) mi m‖ ^ 2 ≤
            2 * A ^ 2 * (X / Real.sqrt P + X ^ (4 / 5 : ℝ)) ^ 2 *
              X * Real.log X ^ 10 := by
  obtain ⟨A, hA, hL⟩ := VaughanBoundTask08.lemma1On_proved
  refine ⟨A, hA, fun X1 X P hX1 hX1X hX3 hP1 hPX mi hmi hsub M => ?_⟩
  have h1 := hL X1 X P hX1 hX1X hX3 hP1 hPX mi hsub
  let B := A * (X / Real.sqrt P + X ^ (4 / 5 : ℝ)) * Real.log X ^ 4
  have hpoint : ∀ β ∈ mi, ‖S X1 X β‖ ≤ B := h1
  have hmain := sum_R2_sq_le (aS X1 X) (⌊X⌋₊ + 1) mi hmi hpoint M
  have hs := sum_aS_sq_le X1 (by linarith : 1 ≤ X)
  calc
    _ ≤ B ^ 2 * ∑ n ∈ range (⌊X⌋₊ + 1), ‖aS X1 X n‖ ^ 2 := hmain
    _ ≤ B ^ 2 * (2 * X * Real.log X ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg B)
    _ = _ := by dsimp [B]; ring

/-- In the usual range the four fifths term is bounded by X over square root P. -/
theorem four_fifths_le {X P : ℝ} (hX : 1 ≤ X) (hP : 0 < P)
    (hPX : P ≤ X ^ (2 / 5 : ℝ)) : X ^ (4 / 5 : ℝ) ≤ X / Real.sqrt P := by
  have hX0 : 0 < X := by linarith
  have hs : Real.sqrt P ≤ X ^ (1 / 5 : ℝ) := by
    calc
      _ ≤ Real.sqrt (X ^ (2 / 5 : ℝ)) := Real.sqrt_le_sqrt hPX
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
        norm_num
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hP)).mpr
  calc
    _ ≤ X ^ (4 / 5 : ℝ) * X ^ (1 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hX0.le _)
    _ = X := by rw [← Real.rpow_add hX0]; norm_num

/-- The standard X cubed over P remainder with the actual logarithmic loss. -/
theorem minor_arc_standard :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ X1 X P : ℝ, 2 ≤ X1 → X1 ≤ X → 3 ≤ X →
      1 ≤ P → P ≤ X ^ (2 / 5 : ℝ) → ∀ mi : Set ℝ, MeasurableSet mi →
        mi ⊆ (majorArcs P (X / P))ᶜ → ∀ M : ℕ,
          ∑ m ∈ range M, ‖R2 (S X1 X) mi m‖ ^ 2 ≤
            8 * A ^ 2 * X ^ 3 * Real.log X ^ 10 / P := by
  obtain ⟨A, hA, hmain⟩ := minor_arc_remainder
  refine ⟨A, hA, fun X1 X P hX1 hX1X hX3 hP1 hP2 mi hmi hsub M => ?_⟩
  have hX : 1 ≤ X := by linarith
  have hP : 0 < P := by linarith
  have hPX : P ≤ X := hP2.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (2 / 5 : ℝ) ≤ 1))
  have hb := hmain X1 X P hX1 hX1X hX3 hP1 hPX mi hmi hsub M
  have ht : X / Real.sqrt P + X ^ (4 / 5 : ℝ) ≤ 2 * (X / Real.sqrt P) := by
    linarith [four_fifths_le hX hP hP2]
  have hnorm := pow_le_pow_left₀ (by positivity : 0 ≤ X / Real.sqrt P + X ^ (4 / 5 : ℝ)) ht 2
  have hf : (2 * (X / Real.sqrt P)) ^ 2 = 4 * X ^ 2 / P := by
    rw [mul_pow, div_pow, Real.sq_sqrt hP.le]
    ring
  calc
    _ ≤ 2 * A ^ 2 * (X / Real.sqrt P + X ^ (4 / 5 : ℝ)) ^ 2 * X * Real.log X ^ 10 := hb
    _ ≤ 2 * A ^ 2 * (2 * (X / Real.sqrt P)) ^ 2 * X * Real.log X ^ 10 := by
      gcongr
    _ = _ := by rw [hf]; ring

end LeanLab.Pintz2021.MinorArc168

#print axioms LeanLab.Pintz2021.MinorArc168.minor_arc_remainder
#print axioms LeanLab.Pintz2021.MinorArc168.four_fifths_le
#print axioms LeanLab.Pintz2021.MinorArc168.minor_arc_standard
