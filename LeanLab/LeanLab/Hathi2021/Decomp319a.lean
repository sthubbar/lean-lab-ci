/-
P0101 Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4.
Supply split of Decomp115.analytic_lower_bound, pages 192 to 199.
The three analytic inputs stay open. The sealed original file is unchanged.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp570a
import LeanLab.Hathi2021.Decomp570b
import LeanLab.Hathi2021.Decomp570c

open Finset Real MeasureTheory Filter Topology LeanLab.Hathi2021.Decomp115

namespace LeanLab.Hathi2021.Decomp319a

/-- LEAF. Page 194, the R1 display in Lemma 2.2 at k equal to 82.
The major arc coefficient is kept separate from both minor arc estimates. -/
theorem major_arc_lower (C δ : ℝ) (hC : 1 < C) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      (556388 / 100000 * Real.pi ^ 2 / 16 - δ) * scale n₁ n₂ ≤ R1 n₁ n₂ :=
  Decomp570a.major_arc_lower C δ hC hδ

/-- LEAF. Pages 194 to 196, the R2 display in Lemma 2.4 with k equal to 82.
The absolute real exceptional contribution has order N1 N2 L to power 81.
The three elementary limit steps are proved separately. -/
theorem exceptional_arc_order_bound (C : ℝ) (hC : 1 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      |R2 n₁ n₂| ≤ K * ((n₁ : ℝ) * n₂ * L n₁ ^ 81) :=
  Decomp570b.exceptional_arc_order_bound C hC

/-- Pages 194 to 196, Lemma 2.4 at k equal to 82.
The exceptional contribution divided by N1 N2 L to power 82 tends to zero. -/
theorem exceptional_arc_small (C δ : ℝ) (hC : 1 < C) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      |R2 n₁ n₂| ≤ δ * scale n₁ n₂ := by
  obtain ⟨K, _, hbound⟩ := exceptional_arc_order_bound C hC
  exact exceptional_arc_small_of_order_bound C δ K hδ hbound

/-- LEAF. Pages 196 to 199, the R3 display in Lemma 2.5 at k equal to 82.
The constant 10823.8 and its unresolved rounding questions are inherited
from the sealed target. This is an open input, not a certified constant. -/
theorem remaining_arc_upper (C δ : ℝ) (hC : 1 < C) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      |R3 n₁ n₂| ≤ ((108238 / 10) * (PairLinnik.lam : ℝ) ^ (82 - 16) + δ) *
        scale n₁ n₂ :=
  Decomp570c.remaining_arc_upper C δ hC hδ

/-- Page 199. The exact sealed leaf statement assembled from three analytic leaves.
CONDITIONAL ON the three separate analytic arc estimates. -/
theorem analytic_lower_bound (C ε : ℝ) (hC : 1 < C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      (PairLinnik.margin101 (108238 / 10) 82 - ε) *
        ((n₁ : ℝ) * n₂ * logScale n₁ ^ 82) ≤ weightedCount n₁ n₂ := by
  obtain ⟨N₁, h₁⟩ := major_arc_lower C (ε / 3) hC (by positivity)
  obtain ⟨N₂, h₂⟩ := exceptional_arc_small C (ε / 3) hC (by positivity)
  obtain ⟨N₃, h₃⟩ := remaining_arc_upper C (ε / 3) hC (by positivity)
  refine ⟨max 16 (max N₁ (max N₂ N₃)), ?_⟩
  intro n₁ n₂ ho₁ ho₂ hn hlt hratio
  have h16 : 16 ≤ n₂ := (le_max_left _ _).trans hn
  have hN₁ : N₁ ≤ n₂ := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hN₂ : N₂ ≤ n₂ :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hn
  have hN₃ : N₃ ≤ n₂ :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hn
  have hm := h₁ n₁ n₂ ho₁ ho₂ hN₁ hlt hratio
  have he := h₂ n₁ n₂ ho₁ ho₂ hN₂ hlt hratio
  have hr := h₃ n₁ n₂ ho₁ ho₂ hN₃ hlt hratio
  have hdecomp := restrictedCount_eq_arcs n₁ n₂ h16 hlt
  have hcount := restrictedCount_le n₁ n₂
  have helo := neg_abs_le (R2 n₁ n₂)
  have hrlo := neg_abs_le (R3 n₁ n₂)
  change (PairLinnik.margin101 (108238 / 10) 82 - ε) * scale n₁ n₂ ≤ _
  unfold PairLinnik.margin101
  nlinarith

end LeanLab.Hathi2021.Decomp319a
