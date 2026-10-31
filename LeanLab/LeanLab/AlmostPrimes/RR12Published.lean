import LeanLab.AlmostPrimes.AP12Theta

/-!
# The full modulus twelve rows of Ramaré and Rumely

AI wrote the Lean code. Goldbach is open.
Source: Ramaré and Rumely 1996, Theorem 1 page 398, Table 1 page 419,
Table 2 page 422, https://doi.org/10.1090/S0025-5718-96-00669-2.
The four epsilons and thresholds were read from the printed Table 1 image.
These Props record cited statements. They do not assert the analytic estimates.
-/

noncomputable section
namespace LeanLab.AlmostPrimes.RR12Published

open Real AP12Theta

/-- The complete row for modulus twelve in Table 1. -/
def analyticRows : List (ℝ × ℝ) :=
  [(10 ^ 10, 0.002781), (10 ^ 13, 0.002241),
    (10 ^ 30, 0.002099), (10 ^ 100, 0.001610)]

/-- Cited Table 1, specialized to modulus twelve. Theorem 1 is stronger since
it also bounds the maximum over all y between one and x. -/
def Table1 : Prop :=
  ∀ a : ℕ, Nat.Coprime a 12 → ∀ row ∈ analyticRows, ∀ x : ℝ, row.1 ≤ x →
    |theta12 a x - x / 4| ≤ row.2 * x / 4

/-- Cited Table 2, theta column for modulus twelve, over its printed positive range.
The introductory Theorem 2 starts at one. Section 5.2 and the table include smaller x. -/
def Table2 : Prop :=
  ∀ a : ℕ, Nat.Coprime a 12 → ∀ x : ℝ, 0 < x → x ≤ 10 ^ 10 →
    |theta12 a x - x / 4| ≤ 1.735502 * sqrt x

/-- The Table 2 bound restricted to the range of the introductory Theorem 2. -/
def PrintedTable2 : Prop :=
  ∀ a : ℕ, Nat.Coprime a 12 → ∀ x : ℝ, 1 ≤ x → x ≤ 10 ^ 10 →
    |theta12 a x - x / 4| ≤ 1.735502 * sqrt x

/-- Extending the printed small range to positive x below one is elementary.
CONDITIONAL ON PrintedTable2 only. -/
theorem table2_of_printed (h : PrintedTable2) : Table2 := by
  intro a ha x hx h10
  by_cases h1 : 1 ≤ x
  · exact h a ha x h1 h10
  · have hx1 : x < 1 := lt_of_not_ge h1
    have hf : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
    have ht : theta12 a x = 0 := by simp [theta12, hf]
    have hs := sqrt_nonneg x
    have hsq := sq_sqrt hx.le
    have hs1 : sqrt x ≤ 1 := by nlinarith
    rw [ht, zero_sub, abs_neg, abs_of_nonneg (by positivity : 0 ≤ x / 4)]
    nlinarith

/-- The two cited table rows as one named input. -/
def Published : Prop := Table1 ∧ Table2

/-- The printed table inputs imply the packaged input, including its elementary extension.
CONDITIONAL ON Table1 and PrintedTable2 only. -/
theorem published_of_printed (h1 : Table1) (h2 : PrintedTable2) : Published :=
  ⟨h1, table2_of_printed h2⟩

/-- The published absolute error bounds imply the lower input.
CONDITIONAL ON Published. -/
theorem lower_of_published (h : Published) : RR12ThetaLower := by
  constructor
  · intro a ha x hx h10
    have hb := (abs_le.mp (h.2 a ha x (by linarith) h10)).1
    linarith
  · intro a ha x hx
    have hm : ((10 ^ 10, 0.002781) : ℝ × ℝ) ∈ analyticRows := by simp [analyticRows]
    have hb := (abs_le.mp (h.1 a ha (10 ^ 10, 0.002781) hm x hx)).1
    dsimp at hb
    linarith

/-- The prime count bound from the published table rows by Abel summation.
CONDITIONAL ON Published only. -/
theorem count12_lower_of_published (h : Published) (a : ℕ) (ha : Nat.Coprime a 12)
    {x : ℝ} (hx : 10 ^ 9 ≤ x) : 0.21 * x / log x < count12 a x :=
  count12_lower_from_1e9 (lower_of_published h) a ha hx

/-- A concrete Table 2 instance at x equal to one. -/
theorem table2_at_one : |theta12 1 1 - (1 : ℝ) / 4| ≤ 1.735502 * sqrt 1 := by
  have ht : theta12 1 1 = 0 := by norm_num [theta12, Finset.sum_Icc_succ_top]
  rw [ht]
  norm_num

end LeanLab.AlmostPrimes.RR12Published

#print axioms LeanLab.AlmostPrimes.RR12Published.lower_of_published
#print axioms LeanLab.AlmostPrimes.RR12Published.count12_lower_of_published
#print axioms LeanLab.AlmostPrimes.RR12Published.table2_at_one
#print axioms LeanLab.AlmostPrimes.RR12Published.table2_of_printed
#print axioms LeanLab.AlmostPrimes.RR12Published.published_of_printed
