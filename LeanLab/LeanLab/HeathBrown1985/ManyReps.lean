/-
P0096 Heath-Brown 1985, a quantitative form of Corollary 1 from Theorem 1: for every C > 0,
all but O(x (log x)^{−C}) even m in (2x, 3x] have N₂(x, m) ≥ e⁻⁶ x, that is many weighted
representations, not just one. Hence, from Siegel-Walfisz alone, zero sorry.
Proof: such an m has abs(N₂ − x𝔖(m)) > e⁻⁶ x since 𝔖(m) ≥ 2e⁻⁶, and Theorem 1 bounds the sum
of these deviations by K x² (log x)^{−C}. Standard; KNOWN mathematics.
AI-written Lean code, Claude, run 20261017T0903Z-2557. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.HeathBrown1985.Corollary3

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset Real

attribute [local instance] Classical.propDecidable

/-- The even `m ∈ (2x, 3x]` with fewer than `e⁻⁶ x` weighted representations. -/
def fewReps (x : ℝ) : Finset ℕ :=
  ((range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ))).filter
    (fun m => Even m ∧ N2 x m < Real.exp (-6) * x)

theorem fewReps_card_of_theorem1 (h1 : Theorem1) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ((fewReps x).card : ℝ) ≤ K * x * Real.log x ^ (-C) := by
  obtain ⟨K1, hK1⟩ := h1 C hC
  refine ⟨K1 * Real.exp 6, fun x hx => ?_⟩
  set T := (range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ))
  have hx0 : 0 < x := by linarith
  have he : 0 < Real.exp (-6) := Real.exp_pos _
  have hterm : ∀ m ∈ fewReps x, Real.exp (-6) * x ≤ |N2 x m - x * singular m| := by
    intro m hm
    obtain ⟨-, hev, hlt⟩ := mem_filter.mp hm
    have hs := singular_ge hev
    have : Real.exp (-6) * x ≤ x * singular m - N2 x m := by nlinarith
    exact this.trans ((le_abs_self _).trans (abs_sub_comm _ _).le)
  have hsub : fewReps x ⊆ T := filter_subset _ _
  have hA : ((fewReps x).card : ℝ) * (Real.exp (-6) * x) ≤ ∑ m ∈ T, |N2 x m - x * singular m| := by
    calc ((fewReps x).card : ℝ) * (Real.exp (-6) * x) = ∑ m ∈ fewReps x, Real.exp (-6) * x := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ fewReps x, |N2 x m - x * singular m| := sum_le_sum hterm
      _ ≤ ∑ m ∈ T, |N2 x m - x * singular m| :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
  have hB := hA.trans (hK1 x hx)
  have hexp : Real.exp (-6) * Real.exp 6 = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-6) * x := by positivity
  rw [← le_div_iff₀ hpos] at hB
  calc ((fewReps x).card : ℝ) ≤ K1 * x ^ 2 * Real.log x ^ (-C) / (Real.exp (-6) * x) := hB
    _ = K1 * Real.exp 6 * x * Real.log x ^ (-C) := by
        rw [show Real.exp 6 = 1 / Real.exp (-6) by rw [Real.exp_neg]; field_simp]
        field_simp

/-- **From Siegel-Walfisz alone**, zero sorry: all but `O(x (log x)^{−C})` even `m ∈ (2x, 3x]`
have `N₂(x, m) ≥ e⁻⁶ x`. -/
theorem fewReps_card_of_siegelWalfisz (hSW : SiegelWalfisz) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ((fewReps x).card : ℝ) ≤ K * x * Real.log x ^ (-C) :=
  fewReps_card_of_theorem1 (theorem1_of_siegelWalfisz hSW) C hC

end LeanLab.HeathBrown1985
