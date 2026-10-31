/-
From the circle method frame to a power saving for E, CONDITIONAL on the two analytic inputs.
Unit U-0995, run 20261019T0103Z-31797, T2, P0015 Montgomery-Vaughan 1975 skeleton.
AI wrote this Lean code. Binary Goldbach is open. The inputs are NOT proved here.
-/
import LeanLab.ExceptionalSet.MVSkeleton

open ZMod Finset

namespace LeanLab.ExceptionalSet.MV

attribute [local instance] Classical.propDecidable

/-- The bad even numbers in the window `(x/2, x]`. -/
noncomputable def badWindow (x : ℕ) : ℕ :=
  ((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card

/-- Window bound: for `x ≥ X0`, at most `C x^θ` bad even numbers in `(x/2, x]`. -/
def WindowBound (θ C : ℝ) (X0 : ℕ) : Prop := ∀ x : ℕ, X0 ≤ x → (badWindow x : ℝ) ≤ C * (x : ℝ) ^ θ

/-- Dyadic summation: a window bound with `0 < θ` gives `PowerBound θ`. -/
theorem powerBound_of_window {θ C : ℝ} {X0 : ℕ} (hθ : 0 < θ)
    (h : WindowBound θ C X0) : PowerBound θ := by
  have h2 : (0 : ℝ) < 1 - (2 : ℝ) ^ (-θ) := by
    have : (2 : ℝ) ^ (-θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  set K : ℝ := max (X0 : ℝ) (C / (1 - (2 : ℝ) ^ (-θ))) with hK
  refine ⟨K, ?_⟩
  intro X
  induction X using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have hxθ : (1 : ℝ) ≤ (x : ℝ) ^ θ := Real.one_le_rpow hx1 hθ.le
    by_cases hX0 : x < X0
    · calc (E x : ℝ) ≤ x := by exact_mod_cast E_le x
        _ ≤ X0 := by exact_mod_cast hX0.le
        _ ≤ K := le_max_left _ _
        _ ≤ K * (x : ℝ) ^ θ := le_mul_of_one_le_right (le_trans (by positivity) (le_max_left _ _)) hxθ
    · replace hX0 := not_lt.mp hX0
      have hsplit := E_le_split (x / 2) x
      have hw := h x hX0
      have hKC : C ≤ K * (1 - (2 : ℝ) ^ (-θ)) := by
        have := le_max_right (X0 : ℝ) (C / (1 - (2 : ℝ) ^ (-θ)))
        rw [← hK] at this
        rwa [div_le_iff₀ h2] at this
      have hK0 : 0 ≤ K := le_trans (Nat.cast_nonneg _) (le_max_left _ _)
      -- bound E (x/2)
      have hhalf : (E (x / 2) : ℝ) ≤ K * ((x : ℝ) / 2) ^ θ := by
        rcases Nat.eq_zero_or_pos (x / 2) with h0 | hpos
        · rw [h0]; have : E 0 = 0 := by
            unfold E; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro n hn; simp at hn
          rw [this]; simp; positivity
        · have := ih (x / 2) (by omega) hpos
          refine this.trans (mul_le_mul_of_nonneg_left ?_ hK0)
          apply Real.rpow_le_rpow (by positivity) _ hθ.le
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
          exact_mod_cast Nat.div_mul_le_self x 2
      have hpow : ((x : ℝ) / 2) ^ θ = (2 : ℝ) ^ (-θ) * (x : ℝ) ^ θ := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num)]; ring
      have hsplit' : (E x : ℝ) ≤ E (x / 2) + badWindow x := by exact_mod_cast hsplit
      calc (E x : ℝ) ≤ E (x / 2) + badWindow x := hsplit'
        _ ≤ K * ((2 : ℝ) ^ (-θ) * (x : ℝ) ^ θ) + C * (x : ℝ) ^ θ := by rw [← hpow]; linarith
        _ ≤ K * ((2 : ℝ) ^ (-θ) * (x : ℝ) ^ θ) + K * (1 - (2 : ℝ) ^ (-θ)) * (x : ℝ) ^ θ := by
            gcongr
        _ = K * (x : ℝ) ^ θ := by ring

/-- The two analytic inputs, in the form `bad_le_skeleton` takes, for every `x ≥ X0`:
a modulus `M > 2x`, a prime-supported `Φ`, minor arcs `m` and a level `T > 0` such that the
major arc part is at most `T` for at most `C₁ x^θ` even `n` in the window, the major arc input,
and `M · (minor arc L4 mass) / T² ≤ C₂ x^θ`, the minor arc input. -/
def MVInputs (θ C₁ C₂ : ℝ) (X0 : ℕ) : Prop :=
  ∀ x : ℕ, X0 ≤ x → ∃ (M : ℕ) (hM0 : 0 < M), 2 * x < M ∧
    ∃ (Φ : ZMod M → ℂ) (m : Finset (ZMod M)) (T : ℝ),
      haveI : NeZero M := ⟨hM0.ne'⟩
      PrimeSupported Φ x ∧ 0 < T ∧
      ((((Finset.Icc (x / 2 + 1) x).filter
          (fun n : ℕ => Even n ∧ ‖majorPart Φ m (n : ZMod M)‖ ≤ T)).card : ℕ) : ℝ) ≤ C₁ * (x : ℝ) ^ θ ∧
      (M : ℝ) * (∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4) / T ^ 2 ≤ C₂ * (x : ℝ) ^ θ

theorem windowBound_of_inputs {θ C₁ C₂ : ℝ} {X0 : ℕ} (h : MVInputs θ C₁ C₂ X0) :
    WindowBound θ (C₁ + C₂) X0 := by
  intro x hx
  obtain ⟨M, hM0, hM, Φ, m, T, hΦ, hT, hA, hB⟩ := h x hx
  have : NeZero M := ⟨hM0.ne'⟩
  have := bad_le_skeleton hΦ hM m hT (x / 2 + 1)
  unfold badWindow
  linarith

/-- **CONDITIONAL ON `MVInputs`**: the circle method inputs with exponent `θ < 1` give a power
saving for the exceptional set, the form of Montgomery-Vaughan 1975, P0015. -/
theorem powerSaving_of_inputs {θ C₁ C₂ : ℝ} {X0 : ℕ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (h : MVInputs θ C₁ C₂ X0) : PowerSaving :=
  ⟨1 - θ, by linarith, by
    rw [sub_sub_cancel]; exact powerBound_of_window hθ0 (windowBound_of_inputs h)⟩

end LeanLab.ExceptionalSet.MV
