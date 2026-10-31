import Mathlib
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-! Equation 2.1 on page 2045, with its literal tuple counting definition.
Positive q encodes the paper's shift negative q.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

/-- Tuple starts from one through x, with every shifted entry prime. -/
def tupleCount (s : Finset ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter fun n => ∀ q ∈ s, (n - q).Prime).card

/-- Even integers from four through x whose minimal partition starts with p. -/
def minimalCount (p x : ℕ) : ℕ :=
  ((Finset.Icc 4 x).filter fun n => Even n ∧ p.Prime ∧ (n - p).Prime ∧
    ∀ q ∈ Finset.Icc 2 (p - 1), ¬ (q.Prime ∧ (n - q).Prime)).card

/-- The right hand side of equation 2.1 for a supplied set of positive shifts. -/
def paperInclusionExclusion (s : Finset ℕ) (p x : ℕ) : ℤ :=
  - ∑ t ∈ s.powerset.filter (p ∈ ·), (-1 : ℤ)^t.card * tupleCount t x

/-- A boundary question for the literal definition: the singleton tuple also counts five. -/
theorem equation21_boundary_question :
    minimalCount 3 6 = 1 ∧ tupleCount {3} 6 = 2 ∧
      paperInclusionExclusion {3} 3 6 = 2 := by
  decide +kernel

/-- For odd shifts, the only prime tuple start outside the even starts is p plus two. -/
theorem singleton_tuple_boundary {p n : ℕ} (hp : Odd p) :
    (n - p).Prime ↔ (Even n ∧ (n - p).Prime) ∨ n = p + 2 := by
  constructor
  · intro hq
    rcases hq.eq_two_or_odd' with h2 | ho
    · right
      have hn := hq.two_le
      omega
    · left
      refine ⟨?_, hq⟩
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := ho
      have hn := hq.two_le
      exact ⟨a + b + 1, by omega⟩
  · rintro (⟨_, hq⟩ | rfl)
    · exact hq
    · simpa using Nat.prime_two

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.equation21_boundary_question

#print axioms LeanLab.OeSHP2014.Task74.singleton_tuple_boundary
