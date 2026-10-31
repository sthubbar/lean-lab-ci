import LeanLab.ChenDoubleSieve.Section3

/-!
# The finite form of Wu 2004 Lemma 3.2

Source: https://arxiv.org/pdf/0705.1652, page 10, equations 3.3 and 3.4.
Finiteness of the correction and positivity of the normalizer are explicit inputs.
These are algebraic implications. No analytic sieve estimate is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Set
namespace LeanLab.ChenDoubleSieve.Wu04

/-- Equation 3.3 follows from the supremum whenever its value is finite and Theta is positive.
CONDITIONAL ON finiteness of Hkn and positivity of the weighted normalizer. -/
theorem upper_at_sup {F : ℝ → ℝ} {δ s c : ℝ} {k N₀ N i : ℕ} {V : Fin i → ℝ} {Δ : ℝ}
    (hN₀ : N₀ ≤ N) (hN : 2 ≤ N) (hEven : Even N) (hU : UkData δ k N i V Δ)
    (hθ : 0 < Theta δ N i V Δ) (hfinite : Hkn F δ k N₀ s = (c : EReal)) :
    Phi δ N i V Δ s ≤ (normalized F s - c) * Theta δ N i V Δ := by
  let r := normalized F s - Phi δ N i V Δ s / Theta δ N i V Δ
  have hbound : Hkn F δ k N₀ s ≤ (r : EReal) := by
    apply sSup_le
    rintro _ ⟨d, hd, rfl⟩
    have hp := hd N hN₀ hN hEven i V Δ hU
    have hr : d ≤ r := by
      dsimp [r]
      have hdiv : Phi δ N i V Δ s / Theta δ N i V Δ ≤ normalized F s - d :=
        (div_le_iff₀ hθ).mpr hp
      linarith
    change (d : EReal) ≤ (r : EReal)
    exact_mod_cast hr
  rw [hfinite] at hbound
  have hcr : c ≤ r := by exact_mod_cast hbound
  have hdiv : Phi δ N i V Δ s / Theta δ N i V Δ ≤ normalized F s - c := by
    dsimp [r] at hcr
    linarith
  exact (div_le_iff₀ hθ).mp hdiv

/-- Equation 3.4 follows from the supremum under the corresponding finite inputs.
CONDITIONAL ON finiteness of hkn and positivity of the weighted normalizer. -/
theorem lower_at_sup {f : ℝ → ℝ} {δ s c : ℝ} {k N₀ N i : ℕ} {V : Fin i → ℝ} {Δ : ℝ}
    (hN₀ : N₀ ≤ N) (hN : 2 ≤ N) (hEven : Even N) (hU : UkData δ k N i V Δ)
    (hθ : 0 < Theta δ N i V Δ) (hfinite : hkn f δ k N₀ s = (c : EReal)) :
    (normalized f s + c) * Theta δ N i V Δ ≤ Phi δ N i V Δ s := by
  let r := Phi δ N i V Δ s / Theta δ N i V Δ - normalized f s
  have hbound : hkn f δ k N₀ s ≤ (r : EReal) := by
    apply sSup_le
    rintro _ ⟨d, hd, rfl⟩
    have hp := hd N hN₀ hN hEven i V Δ hU
    have hr : d ≤ r := by
      dsimp [r]
      have hdiv : normalized f s + d ≤ Phi δ N i V Δ s / Theta δ N i V Δ :=
        (le_div_iff₀ hθ).mpr hp
      linarith
    change (d : EReal) ≤ (r : EReal)
    exact_mod_cast hr
  rw [hfinite] at hbound
  have hcr : c ≤ r := by exact_mod_cast hbound
  have hdiv : normalized f s + c ≤ Phi δ N i V Δ s / Theta δ N i V Δ := by
    dsimp [r] at hcr
    linarith
  exact (le_div_iff₀ hθ).mp hdiv

/-- Zero is a genuine lower candidate for the zero lower sieve function. -/
theorem zero_lower_candidate (δ : ℝ) (k N₀ : ℕ) (s : ℝ) :
    LowerCandidate (fun _ => 0) δ k N₀ s 0 := by
  intro N hN₀ hN hEven i V Δ hU
  simp only [normalized, mul_zero, zero_div, zero_add, zero_mul]
  exact Finset.sum_nonneg fun t ht => Nat.cast_nonneg _

end LeanLab.ChenDoubleSieve.Wu04

#print axioms LeanLab.ChenDoubleSieve.Wu04.upper_at_sup
#print axioms LeanLab.ChenDoubleSieve.Wu04.lower_at_sup
#print axioms LeanLab.ChenDoubleSieve.Wu04.zero_lower_candidate
