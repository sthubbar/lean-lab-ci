import LeanLab.ExceptionalSet.UpJ200.Decomp450e
import LeanLab.ExceptionalSet.UpJ200.Decomp450e
import LeanLab.ExceptionalSet.PhaseInterval446

/-!
Parameter leaves for the distant phase input at P0082 page 366.
The analytic exponential sum is reused through the existing Karacuba route.
The two new leaves contain only real powers and exponential rescaling.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE expSumF)
open LeanLab.ExceptionalSet.Decomp404e (phaseSum)

/-- LEAF. P0082 page 366, frequency range in the application of Theorem 2.
A small exponent margin covers the integer floor of N divided by 2.
This statement has no exponential sum or cancellation conclusion. -/
theorem leaf_frequency_range (γ δ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hδsmall : δ < min ((γ - 1) / 24) (1 / 12)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ,
      F γ N ^ (3 * δ - 1) < |t| → |t| ≤ 2 * F γ N ^ (6 * δ) →
        F γ (2 * (N / 2 : ℕ)) ^ (-(1 - 2 * δ)) ≤ |t| ∧
          |t| ≤ F γ (N / 2 : ℕ) ^ (12 * δ) := by
  exact UpJ200.Decomp450e.frequency_range_supplied γ δ h1 h2 hδ hδsmall

/-- LEAF. P0082 page 366, common kappa rescaling after Theorem 2.
A positive dyadic exponential saving absorbs the two endpoint terms.
The kappa cap is explicit and this statement has no phase sum. -/
theorem leaf_decay_rescale (γ η B : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hη : 0 < η) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ κ : ℝ, 0 < κ → κ ≤ η / 6 →
      ∀ N : ℕ, N₀ ≤ N →
        B * (N / 2 : ℕ) * Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) + 2 ≤
          C * N * calE γ κ N ^ (-(3 / 2 : ℝ)) := by
  exact UpJ200.Decomp450c.decay_rescale_supplied γ η B h1 h2 hη hB

/-- Assembly. P0082 page 366, exact existing Decomp428d.leaf_far_phase.
The two scalar leaves and the existing Theorem 2 proof through the cited
Karacuba input are the only admitted ingredients in this phase supply. -/
theorem far_phase_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ t : ℝ, F γ N ^ (3 * δ - 1) < |t| → |t| ≤ 2 * F γ N ^ (6 * δ) →
            ‖phaseSum γ N t‖ ≤ C * N * calE γ κ N ^ (-(3 / 2 : ℝ)) := by
  refine ⟨min ((γ - 1) / 24) (1 / 12), lt_min (by linarith) (by norm_num), fun δ hδ hδsmall => ?_⟩
  have hδγ : δ < (γ - 1) / 24 := hδsmall.trans_le (min_le_left _ _)
  have hδ12 : δ < 1 / 12 := hδsmall.trans_le (min_le_right _ _)
  obtain ⟨η, B, hη, hs⟩ := LeanLab.ExceptionalSet.U1539.theorem2_via_karacuba
    γ h1 h2 (1 - 2 * δ) (12 * δ) (by linarith) (by linarith) (by positivity) (by linarith)
  obtain ⟨Nr, hr⟩ := leaf_frequency_range γ δ h1 h2 hδ hδsmall
  obtain ⟨C, hC, Nd, hd⟩ := leaf_decay_rescale γ η (|B| + 1) h1 h2 hη (by positivity)
  refine ⟨η / 6, by positivity, fun κ hκ hκsmall =>
    ⟨C, hC, max 2 (max Nr Nd), fun N hN t htlow hthigh => ?_⟩⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNr : Nr ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNd : Nd ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hm : 1 ≤ N / 2 := by omega
  obtain ⟨hl, hu⟩ := hr N hNr t htlow hthigh
  have hsum := hs (N / 2) hm t hl hu
  have hsum' : ‖expSumF γ t (N / 2)‖ ≤
      (|B| + 1) * (N / 2 : ℕ) * Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) := by
    refine hsum.trans ?_
    gcongr
    exact (le_abs_self B).trans (by linarith)
  calc
    _ ≤ ‖expSumF γ t (N / 2)‖ + 2 := PhaseInterval446.phase_interval_norm_le γ t N
    _ ≤ (|B| + 1) * (N / 2 : ℕ) * Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) + 2 :=
      by linarith [hsum']
    _ ≤ _ := hd κ hκ hκsmall N hNd

end LeanLab.ExceptionalSet.Decomp446c
