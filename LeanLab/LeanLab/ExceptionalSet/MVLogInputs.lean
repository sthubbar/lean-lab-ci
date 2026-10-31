/-
The Estermann form from the circle method inputs, CONDITIONAL, unit U-1020, run
20261019T0202Z-9877, T2, P0015 skeleton and P0091 Estermann 1938.
`MVLogInputs A C₁ C₂ X0` is `MVInputs` with `x / (log x)^A` in place of `x^θ`; `MVSupInputs`
replaces the minor arc L4 mass by a sup bound `U` on the minor arcs, the form Vinogradov's
estimate gives, through `minor_L4_le_sup`. Either, at every log power, gives `LogPowerSaving`.
The inputs are NOT proved here: the major arc window count and Vinogradov's minor arc bound are
the analytic content of Estermann 1938. KNOWN mathematics. AI wrote this Lean code. Binary
Goldbach is open.
-/
import LeanLab.ExceptionalSet.MVLogWindow
import LeanLab.ExceptionalSet.MVMinorL4

open ZMod Finset Real

namespace LeanLab.ExceptionalSet.MV

attribute [local instance] Classical.propDecidable

/-- The two circle method inputs at log power `A`, for every `x ≥ X0`. -/
def MVLogInputs (A C₁ C₂ : ℝ) (X0 : ℕ) : Prop :=
  ∀ x : ℕ, X0 ≤ x → ∃ (M : ℕ) (hM0 : 0 < M), 2 * x < M ∧
    ∃ (Φ : ZMod M → ℂ) (m : Finset (ZMod M)) (T : ℝ),
      haveI : NeZero M := ⟨hM0.ne'⟩
      PrimeSupported Φ x ∧ 0 < T ∧
      ((((Finset.Icc (x / 2 + 1) x).filter
          (fun n : ℕ => Even n ∧ ‖majorPart Φ m (n : ZMod M)‖ ≤ T)).card : ℕ) : ℝ)
        ≤ C₁ * x / log x ^ A ∧
      (M : ℝ) * (∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4) / T ^ 2 ≤ C₂ * x / log x ^ A

/-- The same with a minor arc sup bound `U` in place of the L4 mass. -/
def MVSupInputs (A C₁ C₂ : ℝ) (X0 : ℕ) : Prop :=
  ∀ x : ℕ, X0 ≤ x → ∃ (M : ℕ) (hM0 : 0 < M), 2 * x < M ∧
    ∃ (Φ : ZMod M → ℂ) (m : Finset (ZMod M)) (T U : ℝ),
      haveI : NeZero M := ⟨hM0.ne'⟩
      PrimeSupported Φ x ∧ 0 < T ∧ (∀ k ∈ m, ‖𝓕 Φ k‖ ≤ U) ∧
      ((((Finset.Icc (x / 2 + 1) x).filter
          (fun n : ℕ => Even n ∧ ‖majorPart Φ m (n : ZMod M)‖ ≤ T)).card : ℕ) : ℝ)
        ≤ C₁ * x / log x ^ A ∧
      (M : ℝ) * (U ^ 2 * ((M : ℝ) * ∑ j, ‖Φ j‖ ^ 2)) / T ^ 2 ≤ C₂ * x / log x ^ A

/-- The sup form implies the L4 form. -/
theorem logInputs_of_sup {A C₁ C₂ : ℝ} {X0 : ℕ} (h : MVSupInputs A C₁ C₂ X0) :
    MVLogInputs A C₁ C₂ X0 := by
  intro x hx
  obtain ⟨M, hM0, hM, Φ, m, T, U, hΦ, hT, hU, hA, hB⟩ := h x hx
  have : NeZero M := ⟨hM0.ne'⟩
  exact ⟨M, hM0, hM, Φ, m, T, hΦ, hT, hA, (minorTerm_le_sup Φ m hU).trans hB⟩

/-- The window bound at log power `A` from the inputs, through `bad_le_skeleton`. -/
theorem windowLog_of_inputs {A C₁ C₂ : ℝ} {X0 : ℕ} (h : MVLogInputs A C₁ C₂ X0) :
    ∀ x : ℕ, X0 ≤ x → (badWindow x : ℝ) ≤ (C₁ + C₂) * x / log x ^ A := by
  intro x hx
  obtain ⟨M, hM0, hM, Φ, m, T, hΦ, hT, hA, hB⟩ := h x hx
  have : NeZero M := ⟨hM0.ne'⟩
  have := bad_le_skeleton hΦ hM m hT (x / 2 + 1)
  unfold badWindow
  have e : (C₁ + C₂) * x / log x ^ A = C₁ * x / log x ^ A + C₂ * x / log x ^ A := by ring
  rw [e]; linarith

/-- **Estermann 1938, CONDITIONAL ON `MVLogInputs` at every log power**: `LogPowerSaving`. -/
theorem logPowerSaving_of_inputs
    (h : ∀ A : ℝ, 0 < A → ∃ (C₁ C₂ : ℝ) (X0 : ℕ), MVLogInputs A C₁ C₂ X0) : LogPowerSaving :=
  logPowerSaving_of_windows fun A hA => by
    obtain ⟨C₁, C₂, X0, hI⟩ := h A hA
    exact ⟨C₁ + C₂, X0, windowLog_of_inputs hI⟩

/-- **CONDITIONAL ON `MVSupInputs` at every log power**, the Vinogradov sup form. -/
theorem logPowerSaving_of_supInputs
    (h : ∀ A : ℝ, 0 < A → ∃ (C₁ C₂ : ℝ) (X0 : ℕ), MVSupInputs A C₁ C₂ X0) : LogPowerSaving :=
  logPowerSaving_of_inputs fun A hA => by
    obtain ⟨C₁, C₂, X0, hI⟩ := h A hA
    exact ⟨C₁, C₂, X0, logInputs_of_sup hI⟩

#print axioms logInputs_of_sup
#print axioms windowLog_of_inputs
#print axioms logPowerSaving_of_inputs
#print axioms logPowerSaving_of_supInputs

end LeanLab.ExceptionalSet.MV
