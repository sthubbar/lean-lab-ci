/-
Ordered and unordered conventions for Brun's page 127 ratio consequence.
The unordered count includes the pair with equal primes once.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.SchnirelmannGoldbach.BrunRatio

open Finset Filter
open scoped Classical Topology

namespace LeanLab.SchnirelmannGoldbach

/-- Count Goldbach pairs with their smaller prime first. -/
def unorderedCount (n : ℕ) : ℕ :=
  #{p ∈ range n | p.Prime ∧ (n - p).Prime ∧ p ≤ n - p}

/-- The two usual counting conventions differ by at most a factor of two. -/
theorem unordered_count_bounds (n : ℕ) :
    unorderedCount n ≤ r n ∧ r n ≤ 2 * unorderedCount n := by
  let A := {p ∈ range n | p.Prime ∧ (n - p).Prime}
  let U := {p ∈ range n | p.Prime ∧ (n - p).Prime ∧ p ≤ n - p}
  have hUA : U ⊆ A := by
    intro p hp
    obtain ⟨hpn, hp, hq, _⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hpn, hp, hq⟩
  have hAU : A ⊆ U ∪ U.image (fun p => n - p) := by
    intro p hp
    obtain ⟨hpn, hp, hq⟩ := mem_filter.mp hp
    have hpn' := mem_range.mp hpn
    by_cases h : p ≤ n - p
    · exact mem_union_left _ (mem_filter.mpr ⟨hpn, hp, hq, h⟩)
    · apply mem_union_right
      apply mem_image.mpr
      have heq : n - (n - p) = p := by omega
      refine ⟨n - p, mem_filter.mpr ⟨mem_range.mpr ?_, hq, ?_, ?_⟩, heq⟩
      · have := hp.two_le
        omega
      · simpa only [heq] using hp
      · omega
  have h1 := card_le_card hUA
  have h2 := card_le_card hAU
  have h3 := card_union_le U (U.image (fun p => n - p))
  have h4 := card_image_le (s := U) (f := fun p => n - p)
  change U.card ≤ A.card ∧ A.card ≤ 2 * U.card
  exact ⟨h1, by omega⟩

example : unorderedCount 10 = 2 := by decide
example : r 10 = 3 := by decide

/-- Brun's ratio limit holds for unordered pairs as well. -/
theorem unordered_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (unorderedCount n : ℝ) / Nat.primeCounting n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) ?_ goldbach_ratio_tendsto_zero
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (unordered_count_bounds n).1

end LeanLab.SchnirelmannGoldbach

#print axioms LeanLab.SchnirelmannGoldbach.unordered_count_bounds

#print axioms LeanLab.SchnirelmannGoldbach.unordered_ratio_tendsto_zero
