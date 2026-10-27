/-
R-5260, CLOUD 20261020T1914Z-cloud49, unit U-6720, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

Regularity and removal for the Goldbach tripartite graph: vertex classes A, A
and targets N, a triangle for each a + b = N.  Every regularity, counting or
removal conclusion is stable under deleting a small proportion of A, and
binary Goldbach at one N is not.
* `killSet A N` = {a ∈ A : 2a ≤ N, N - a ∈ A}, its size is the unordered
  count h(N).
* `kill_target`: deleting `killSet A N` leaves no a + b = N inside A.
* `kill_min`: every deletion that kills N removes at least h(N) elements,
  since the pairs {a, N - a} form a matching; so h(N) is the exact cost.
* `not_robust_implies_rep`: a property closed under deleting h(N) elements
  never implies a representation of N.
* `sum_rep_eq_sq`: Σ_N r_A(N) = |A|², the only quantity a triangle count sees
  without weights at each target.
-/
import Mathlib

namespace LeanLab.Routes.R5260

open Finset

/-- Ordered representation count r_A(N) = #{(a, b) ∈ A × A : a + b = N}. -/
def rep (A : Finset ℕ) (N : ℕ) : ℕ :=
  ((A ×ˢ A).filter (fun x => x.1 + x.2 = N)).card

/-- The kill set: the smaller member of each representation of N. -/
def killSet (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  A.filter (fun a => 2 * a ≤ N ∧ N - a ∈ A)

/-- Deleting the kill set leaves no representation of N. -/
theorem kill_target (A : Finset ℕ) (N : ℕ) :
    ∀ a ∈ A \ killSet A N, ∀ b ∈ A \ killSet A N, a + b ≠ N := by
  intro a ha b hb hab
  simp only [killSet, mem_sdiff, mem_filter, not_and] at ha hb
  rcases le_total a b with h | h
  · have h1 : 2 * a ≤ N := by omega
    have h2 : N - a = b := by omega
    exact ha.2 ha.1 h1 (h2 ▸ hb.1)
  · have h1 : 2 * b ≤ N := by omega
    have h2 : N - b = a := by omega
    exact hb.2 hb.1 h1 (h2 ▸ ha.1)

/-- The kill set is the exact minimum: any B ⊆ A with no representation of N
has |A \ B| ≥ |killSet A N|. -/
theorem kill_min (A B : Finset ℕ) (N : ℕ) (hB : B ⊆ A)
    (hno : ∀ a ∈ B, ∀ b ∈ B, a + b ≠ N) :
    (killSet A N).card ≤ (A \ B).card := by
  classical
  let f : ℕ → ℕ := fun a => if a ∈ B then N - a else a
  apply Finset.card_le_card_of_injOn f
  · intro a ha
    simp only [killSet, coe_filter, Set.mem_setOf_eq] at ha
    obtain ⟨haA, h2, hNa⟩ := ha
    simp only [coe_sdiff, Set.mem_diff, mem_coe]
    by_cases haB : a ∈ B
    · simp only [f, haB, ite_true]
      refine ⟨hNa, fun h => hno a haB (N - a) h ?_⟩
      omega
    · simp only [f, haB, ite_false, not_false_eq_true, and_true]
      exact haA
  · intro a ha a' ha' hf
    simp only [killSet, coe_filter, Set.mem_setOf_eq] at ha ha'
    by_cases h1 : a ∈ B <;> by_cases h2 : a' ∈ B <;>
      simp only [f, h1, h2, ite_true, ite_false] at hf <;> omega

/-- Robustness: a property of finite sets that survives deleting the kill set
cannot force a representation of N in every set that has it. -/
theorem not_robust_implies_rep (Φ : Finset ℕ → Prop) (A : Finset ℕ) (N : ℕ)
    (hclosed : Φ (A \ killSet A N)) :
    ¬ (∀ B, Φ B → ∃ a ∈ B, ∃ b ∈ B, a + b = N) := by
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := h _ hclosed
  exact kill_target A N a ha b hb hab

/-- The averaged triangle count: Σ_{N ≤ 2M} r_A(N) = |A|² for A ⊆ [0, M]. -/
theorem sum_rep_eq_sq (A : Finset ℕ) (M : ℕ) (hA : A ⊆ range (M + 1)) :
    ∑ N ∈ range (2 * M + 1), rep A N = A.card ^ 2 := by
  classical
  have hmaps : ∀ x ∈ A ×ˢ A, (fun x : ℕ × ℕ => x.1 + x.2) x ∈ range (2 * M + 1) := by
    intro x hx
    rw [mem_product] at hx
    have h1 := mem_range.mp (hA hx.1)
    have h2 := mem_range.mp (hA hx.2)
    simp only [mem_range]
    omega
  rw [sq, ← card_product, card_eq_sum_card_fiberwise hmaps]
  rfl

/-- Vacuity check: A = primes below 10, N = 10, kill set {3, 5}, |killSet| = 2,
and r_A(10) = 3 ordered pairs, (3, 7), (7, 3), (5, 5). -/
example : killSet {2, 3, 5, 7} 10 = {3, 5} := by decide
example : rep {2, 3, 5, 7} 10 = 3 := by decide
example : ∀ a ∈ ({2, 7} : Finset ℕ), ∀ b ∈ ({2, 7} : Finset ℕ), a + b ≠ 10 := by decide

end LeanLab.Routes.R5260

#print axioms LeanLab.Routes.R5260.kill_target
#print axioms LeanLab.Routes.R5260.kill_min
#print axioms LeanLab.Routes.R5260.not_robust_implies_rep
#print axioms LeanLab.Routes.R5260.sum_rep_eq_sq
