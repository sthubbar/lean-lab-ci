import LeanLab.ExceptionalSet.Decomp428a

/-!
The power saving frame now needs only its fixed major arc count.
Source: P0015 page 356 display 3.2 and page 367 display 8.3.
These are auxiliary statements on the existing discrete circle model.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.PowerSaving428

open Real Finset ArithmeticFunction ZMod
open LeanLab.ExceptionalSet.MV

/-- CONDITIONAL ON the explicit fixed major arc count. The fourth moment
is supplied by Decomp428a, so no minor arc input remains.
Source: P0015 page 356 display 3.2 and page 367 display 8.3. -/
theorem powerSaving_of_major_count
    (hmajor : ∃ (θ C : ℝ) (X0 : ℕ), 0 < θ ∧ θ < 1 ∧ 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
              ‖majorPart (logPrimes x) (minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10)))
                (n : ZMod (Mx x))‖ ≤ (Mx x : ℝ) * x / 4)).card : ℕ) : ℝ)
          ≤ C * (x : ℝ) ^ θ) : PowerSaving := by
  obtain ⟨θ₁, C₁, X₁, hθ₁0, hθ₁1, hC₁, hX₁, h1⟩ := hmajor
  obtain ⟨θ₂, C₂, X₂, hθ₂0, hθ₂1, hC₂, hX₂, h2⟩ := Decomp428a.minor_arc_l4_power_supplied
  have hθ0 : 0 < max θ₁ θ₂ := lt_of_lt_of_le hθ₁0 (le_max_left _ _)
  have hθ1 : max θ₁ θ₂ < 1 := max_lt hθ₁1 hθ₂1
  refine ⟨1 - max θ₁ θ₂, by linarith, ?_⟩
  rw [sub_sub_cancel]
  refine powerBound_of_window (θ := max θ₁ θ₂) (C := C₁ + C₂) (X0 := max X₁ X₂) hθ0 ?_
  intro x hx
  have hb1 := h1 x (le_trans (le_max_left _ _) hx)
  have hb2 := h2 x (le_trans (le_max_right _ _) hx)
  have hx1 : 1 ≤ x := le_trans (le_trans hX₁ (le_max_left _ _)) hx
  have hxM : 2 * x < Mx x := by unfold Mx; omega
  have hMpos : (0 : ℝ) < (Mx x : ℝ) := by
    have : 0 < Mx x := by unfold Mx; omega
    exact_mod_cast this
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  have hT : (0 : ℝ) < (Mx x : ℝ) * x / 4 := by
    have := mul_pos hMpos hxpos
    linarith
  have hΦ : PrimeSupported (logPrimes x) x := by
    intro j hj
    by_contra hcon
    exact hj (by simp [logPrimes, hcon])
  have hsk := bad_le_skeleton (M := Mx x) (Φ := logPrimes x) (x := x) (a := x / 2 + 1) hΦ hxM
    (minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10))) hT
  have hsum : (badWindow x : ℝ) ≤ C₁ * (x : ℝ) ^ θ₁ + C₂ * (x : ℝ) ^ θ₂ := by
    unfold badWindow
    linarith
  have hx1r : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hp1 : (x : ℝ) ^ θ₁ ≤ (x : ℝ) ^ max θ₁ θ₂ :=
    Real.rpow_le_rpow_of_exponent_le hx1r (le_max_left _ _)
  have hp2 : (x : ℝ) ^ θ₂ ≤ (x : ℝ) ^ max θ₁ θ₂ :=
    Real.rpow_le_rpow_of_exponent_le hx1r (le_max_right _ _)
  have hm1 : C₁ * (x : ℝ) ^ θ₁ ≤ C₁ * (x : ℝ) ^ max θ₁ θ₂ :=
    mul_le_mul_of_nonneg_left hp1 hC₁
  have hm2 : C₂ * (x : ℝ) ^ θ₂ ≤ C₂ * (x : ℝ) ^ max θ₁ θ₂ :=
    mul_le_mul_of_nonneg_left hp2 hC₂
  have hfin : C₁ * (x : ℝ) ^ max θ₁ θ₂ + C₂ * (x : ℝ) ^ max θ₁ θ₂
      = (C₁ + C₂) * (x : ℝ) ^ max θ₁ θ₂ := by ring
  linarith


/-- The exact existing Theorem 5.1 type with the proved minor input.
CONDITIONAL ON BG2026.major_arc_count_power, which remains cited.
Source: P0015 page 367 display 8.3 and the existing dyadic frame. -/
theorem theorem51_supplied : PowerSaving :=
  powerSaving_of_major_count BG2026.major_arc_count_power

end LeanLab.ExceptionalSet.PowerSaving428
