/-
AI wrote the Lean code. CODEX task638.
Source: Song 2020, pages 4 and 5, the S1 and S2 displays.
These four definitions move from Decomp139 with identical declaration text.
This removes the import cycle between Decomp139 and Prep1121FourierS2.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Characteristic139

namespace LeanLab.Song2020.Decomp139

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Pages 4 and 5. The truncated Fourier polynomial of Lemma 1. -/
def fourier (a : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) : ℂ :=
  ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), a H h * eC (h * x)

/-- Pages 4 and 5. S1 with negative Fourier frequencies as in the defined sawtooth. -/
def truncatedSum (a : ℕ → ℤ → ℂ) (H : ℕ) (γ : ℝ) (n : ℕ) (y α : ℝ) : ℂ :=
  ∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
    (fourier a H (-((p : ℝ) + 1) ^ γ) - fourier a H (-(p : ℝ) ^ γ))

/-- Pages 4 and 5. The displayed S2 bound. -/
def tailBudget (γ n y H : ℝ) : ℝ :=
  H ^ ((1 : ℝ) / 2) * n ^ (1 - γ / 2) + H⁻¹ * y * n ^ (1 - γ)

/-- Page 5. The truncated subwindow of the prime window: the integers x with
x minus n over 3 less than y in absolute value and x at most t. Partial summation over the
window produces sums over these initial segments. -/
def subWindow (n : ℕ) (y t : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t)

end
end LeanLab.Song2020.Decomp139
