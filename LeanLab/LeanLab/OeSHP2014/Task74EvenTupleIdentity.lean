import LeanLab.OeSHP2014.Task74FiniteExclusion
import LeanLab.OeSHP2014.Task74InclusionExclusion

/-! Equation 2.1 on page 2045 with an explicit restriction to even starts.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

/-- All smaller prime shifts considered by the minimal partition test. -/
def smallerPrimeShifts (p : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (p - 1)).filter Nat.Prime

/-- Prime tuple counts with even starts from four through x. -/
def evenTupleCount (s : Finset ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 4 x).filter fun n => Even n ∧ ∀ q ∈ s, (n - q).Prime).card

/-- The exact finite identity with the even start convention stated explicitly. -/
theorem minimalCount_even_inclusion_exclusion (p x : ℕ) (hp : p.Prime) :
    (minimalCount p x : ℤ) =
      ∑ t ∈ (smallerPrimeShifts p).powerset, (-1 : ℤ)^t.card *
        (evenTupleCount (insert p t) x : ℤ) := by
  classical
  let U := (Finset.Icc 4 x).filter fun n => Even n ∧ (n - p).Prime
  have h := finite_exclusion U (smallerPrimeShifts p) (fun q n => (n - q).Prime)
  have hl : (U.filter (fun n => ∀ q ∈ smallerPrimeShifts p, ¬ (n - q).Prime)).card =
      minimalCount p x := by
    unfold minimalCount
    congr 1
    ext n
    simp [U, smallerPrimeShifts, hp, and_assoc]
  have hr (t : Finset ℕ) : (U.filter (fun n => ∀ q ∈ t, (n - q).Prime)).card =
      evenTupleCount (insert p t) x := by
    unfold evenTupleCount
    congr 1
    ext n
    simp [U, and_assoc]
  simpa only [hl, hr] using h

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.minimalCount_even_inclusion_exclusion
