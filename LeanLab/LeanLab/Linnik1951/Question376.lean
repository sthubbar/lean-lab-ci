/-
P0093 page 168 after equation 10.6. Audit of the claimed uniform upper bound.
The paper issue stays a QUESTION pending Claude review.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.TailBridge376
import LeanLab.MissingDigit.UnboundedSeries

namespace LeanLab.Linnik1951

/-- Audit counterstatement for P0093 page 168 after equation 10.6.
The exact product used in this folder exceeds every real constant on
positive even residuals. Reuse the proved ordinary series result from
MissingDigit through its proved Euler product equality. -/
theorem exists_even_singular_gt376 (C : ℝ) :
    ∃ n : ℕ, 2 ≤ n ∧ Even n ∧ C < singularSeries111 n := by
  obtain ⟨n, hn, he, hgt⟩ := LeanLab.MissingDigit.KimSeries.exists_even_series_gt C
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := he
    omega
  refine ⟨n, hn2, he, ?_⟩
  rw [singular_eq_heath_brown376 n hn2 he]
  rw [LeanLab.MissingDigit.KimSeries.series_eq_euler hn] at hgt
  exact hgt

/-- Audit counterstatement for P0093 page 168 after equation 10.6.
There is no constant upper bound for the exact singular product on all
positive even residuals. This is a negative bound result. The paper
interpretation remains a QUESTION rather than a finding. -/
theorem not_uniform_singular_upper376 :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → Even n → singularSeries111 n ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn, he, hgt⟩ := exists_even_singular_gt376 C
  exact (not_lt_of_ge (hC n hn he)) hgt

end LeanLab.Linnik1951
