/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
Elementary content of the definition of a Goldbach number in Chirre and Hagen,
arXiv 2512.23534, printed page 1. No assertion of the binary conjecture is made.
-/
import LeanLab.ChirreHagen2025.Statements

namespace LeanLab.Routes.Task59

open LeanLab.ChirreHagen2025

/-- A sum of two odd primes is even and is at least 6. -/
theorem goldbach_number_even_and_six_le {n : ℕ} (hn : IsGoldbachNumber n) :
    Even n ∧ 6 ≤ n := by
  obtain ⟨p, q, hp, hq, ⟨a, ha⟩, ⟨b, hb⟩, rfl⟩ := hn
  constructor
  · exact ⟨a + b + 1, by omega⟩
  · have := hp.two_le
    have := hq.two_le
    omega

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.goldbach_number_even_and_six_le
