import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a

/-!
Split of `jutila_density481` of `Decomp481a`, the uniform bound on the sum of zero multiplicities
in the exceptional box, the density estimate that follows display 8.

The target bounds the multiplicity sum, taken over an arbitrary finite subset of the box, by
`C₀ * exp (4 * H)`, uniformly in the scale `X`, in the admissible parameter `P`, and in the subset.
This file cuts the box, and with it the index set of the sum, into three cells: the part whose real
part is at least `1 - H / (2 log X)` together with imaginary part at most `T / 2`, the part whose
real part is at least `1 - H / (2 log X)` together with imaginary part above `T / 2`, and the part
whose real part is below `1 - H / (2 log X)`. Each leaf repeats the full quantifier chain of the
target with its cell condition written into the filter of the sum, so each leaf bounds the same sum,
with the same uniformity, over a subset of the finite set the target covers: every leaf is a strict
weakening of the target and none of them can be the target itself.

`jutila_density481_split` below rewrites the sum over the finite set as the two-way split of a sum
over a filter and then splits the near-line part once more, and adds the three constants. Its proof
uses no `sorry` and does not use `jutila_density481`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-- LEAF. The near-line cell at low height. The sum of the analytic multiplicities, over the part
of the finite set whose real part is at least `1 - H / (2 log X)` and whose imaginary part is at
most `T / 2`, is at most the constant times `exp (4 * H)`; the bound is uniform in the scale `X`,
in the admissible parameter `P` and in the finite subset, exactly as in the target. This is one cell
of the box, so it asks for the target's bound on a strictly smaller index set. -/
theorem leaf_density_near_line_low481 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
        T ≤ P → P ≤ Real.sqrt X →
        ∀ F : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          (∀ z ∈ F, z ∈ zeroBox481 X H T P) →
          (∑ z ∈ F.filter (fun z => 1 - H / (2 * Real.log X) ≤ z.2.2.re ∧
              |z.2.2.im| ≤ T / 2),
            (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) ≤ C * Real.exp (4 * H) := by
  sorry

/-- LEAF. The near-line cell at large height. The sum of the analytic multiplicities, over the part
of the finite set whose real part is at least `1 - H / (2 log X)` and whose imaginary part is larger
than `T / 2`, is at most the constant times `exp (4 * H)`, with the same uniformity in the scale
`X`, in the admissible parameter `P` and in the finite subset as the target. This is the other
height cell of the near-line part, again a strictly smaller index set than the whole box. -/
theorem leaf_density_near_line_high481 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
        T ≤ P → P ≤ Real.sqrt X →
        ∀ F : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          (∀ z ∈ F, z ∈ zeroBox481 X H T P) →
          (∑ z ∈ F.filter (fun z => 1 - H / (2 * Real.log X) ≤ z.2.2.re ∧
              ¬ (|z.2.2.im| ≤ T / 2)),
            (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) ≤ C * Real.exp (4 * H) := by
  sorry

/-- LEAF. The deep cell. The sum of the analytic multiplicities, over the part of the finite set
whose real part is below `1 - H / (2 log X)`, that is over the half of the exceptional strip away
from the edge at one, is at most the constant times `exp (4 * H)`, uniformly in the scale `X`, in
the admissible parameter `P` and in the finite subset. This is the remaining cell of the box, and so
again the target's bound on a strictly smaller index set. -/
theorem leaf_density_deep481 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
        T ≤ P → P ≤ Real.sqrt X →
        ∀ F : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          (∀ z ∈ F, z ∈ zeroBox481 X H T P) →
          (∑ z ∈ F.filter (fun z => ¬ (1 - H / (2 * Real.log X) ≤ z.2.2.re)),
            (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) ≤ C * Real.exp (4 * H) := by
  sorry

/-- The split target: the statement of `jutila_density481`, proved from the three cell leaves by
splitting the finite sum over the filter of the near-line condition and then over the filter of the
low height condition inside it, and adding the three constants. -/
theorem jutila_density481_split : JutilaStatement481 := by
  obtain ⟨c₁, hc₁, h₁⟩ := leaf_density_near_line_low481
  obtain ⟨c₂, hc₂, h₂⟩ := leaf_density_near_line_high481
  obtain ⟨c₃, hc₃, h₃⟩ := leaf_density_deep481
  refine ⟨c₁ + c₂ + c₃, by linarith, ?_⟩
  intro H T hH hT
  obtain ⟨X₁, hX₁⟩ := h₁ H T hH hT
  obtain ⟨X₂, hX₂⟩ := h₂ H T hH hT
  obtain ⟨X₃, hX₃⟩ := h₃ H T hH hT
  refine ⟨max (max X₁ X₂) X₃, ?_⟩
  intro X hX P hTP hPX F hF
  have h1 : X₁ ≤ X :=
    le_trans (le_trans (le_max_left X₁ X₂) (le_max_left (max X₁ X₂) X₃)) hX
  have h2 : X₂ ≤ X :=
    le_trans (le_trans (le_max_right X₁ X₂) (le_max_left (max X₁ X₂) X₃)) hX
  have h3 : X₃ ≤ X := le_trans (le_max_right (max X₁ X₂) X₃) hX
  have b₁ := hX₁ X h1 P hTP hPX F (fun z hz => hF z hz)
  have b₂ := hX₂ X h2 P hTP hPX F (fun z hz => hF z hz)
  have b₃ := hX₃ X h3 P hTP hPX F (fun z hz => hF z hz)
  have hsplit :
      (∑ z ∈ F, (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) =
        (∑ z ∈ F.filter (fun z => 1 - H / (2 * Real.log X) ≤ z.2.2.re ∧
            |z.2.2.im| ≤ T / 2),
          (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) +
        (∑ z ∈ F.filter (fun z => 1 - H / (2 * Real.log X) ≤ z.2.2.re ∧
            ¬ (|z.2.2.im| ≤ T / 2)),
          (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) +
        (∑ z ∈ F.filter (fun z => ¬ (1 - H / (2 * Real.log X) ≤ z.2.2.re)),
          (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not F
      (fun z => 1 - H / (2 * Real.log X) ≤ z.2.2.re)
      (fun z => (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ))]
    rw [← Finset.sum_filter_add_sum_filter_not
      (F.filter (fun z => 1 - H / (2 * Real.log X) ≤ z.2.2.re))
      (fun z => |z.2.2.im| ≤ T / 2)
      (fun z => (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ))]
    rw [Finset.filter_filter, Finset.filter_filter]
  rw [hsplit]
  have hsum :
      (∑ z ∈ F.filter (fun z => 1 - H / (2 * Real.log X) ≤ z.2.2.re ∧
          |z.2.2.im| ≤ T / 2),
        (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) +
      (∑ z ∈ F.filter (fun z => 1 - H / (2 * Real.log X) ≤ z.2.2.re ∧
          ¬ (|z.2.2.im| ≤ T / 2)),
        (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) +
      (∑ z ∈ F.filter (fun z => ¬ (1 - H / (2 * Real.log X) ≤ z.2.2.re)),
        (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) ≤
        c₁ * Real.exp (4 * H) + c₂ * Real.exp (4 * H) + c₃ * Real.exp (4 * H) :=
    add_le_add (add_le_add b₁ b₂) b₃
  have hexp : (c₁ + c₂ + c₃) * Real.exp (4 * H) =
      c₁ * Real.exp (4 * H) + c₂ * Real.exp (4 * H) + c₃ * Real.exp (4 * H) := by
    ring
  linarith [hsum, hexp]

end

end LeanLab.LPZ2007


