/-
Split of grh_mellin_transfer519 into three leaves. The transfer of a
nonprincipal character prime sum to a Mellin integral is cut into three
independent steps: the uniform bound for the logarithm of the L-function on the
vertical line under the zero hypothesis, the exact prime power expansion of the
difference between the character prime series and that Mellin integral, and the
size of the part of the expansion carrying exponents at least two. The assembly
at the end has no sorry and does not use grh_mellin_transfer519.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp519a

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

/-- LEAF. Line bound step. Under the hypothesis on the zeros of the Riemann zeta
function and of the Dirichlet L-functions, the function sending a real t to the
logarithm of the L-function of a nonprincipal character, taken at the point
1/2 + 1/ln N + i t of the vertical line, is continuous in t and is bounded by a
constant that does not depend on the character or on N, times the cube of the
logarithm of N times the absolute value of t plus two. This is the only step
that uses the zero hypothesis. It carries no difference of two sums, no Mellin
integral and no prime power. -/
theorem line_bound_lnL519 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          Continuous (fun t : ℝ =>
            Complex.log (DirichletCharacter.LFunction χ (mellinLine519 N t))) ∧
          ∀ t : ℝ, ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine519 N t))‖ ≤
            B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  sorry

/-- LEAF. Prime power expansion step. The difference between the damped character
prime series and the Mellin integral, along the vertical line, of the logarithm
of the L-function of the same character is exactly minus the double sum over all
primes and all exponents at least two, each term carrying the value of the
character at the prime power, the exponential damping at that power and the
oscillating exponential at that power. This is an identity for every real alpha;
the zero hypothesis only serves to keep the logarithm on one branch and to move
the line past the zeros. -/
theorem mellin_log_expansion519 (hG : LeanLab.DERZ1997.GRH) :
    ∀ N : ℕ, 2 ≤ N → ∀ (q : ℕ) [NeZero q], 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ,
        characterPrime519 χ N α -
            mellinU519 N
              (fun t : ℝ => Complex.log
                (DirichletCharacter.LFunction χ (mellinLine519 N t))) α
          = -∑' p : Nat.Primes, ∑' k : ℕ,
              (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
                (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
                  Complex.exp
                    ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)) := by
  sorry

/-- LEAF. Prime power tail step. The part of the prime power double sum with
exponents at least two, summed over all primes and all such exponents, is at
most a constant independent of N, of the character and of alpha, times the
square root of N. The exponential damping at the prime powers is what makes the
double sum absolutely convergent. No zero hypothesis, no Mellin integral and no
estimate on the character occur here. -/
theorem prime_power_tail519 :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ α : ℝ,
        ‖∑' p : Nat.Primes, ∑' k : ℕ,
            (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
          ≤ B * Real.sqrt N := by
  sorry

/-- The three leaves together give the transfer of the nonprincipal character
prime series to a Mellin integral whose coefficient is the logarithm of the
L-function on the line, with the prime power part paid for by a square root of N
error. -/
theorem grh_mellin_transfer519_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖characterPrime519 χ N α - mellinU519 N M α‖ ≤ B * Real.sqrt N := by
  obtain ⟨B0, hB0, N1, h1⟩ := line_bound_lnL519 hG
  obtain ⟨B, hB, N3, h3⟩ := prime_power_tail519
  refine ⟨B0, hB0, B, hB, max N1 (max N3 2), ?_⟩
  intro N hN q hq hqt χ hχ
  have h2 : 2 ≤ N := by omega
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨hcont, hbd⟩ := h1 N (by omega) q hq hqt χ hχ
  refine ⟨fun t : ℝ => Complex.log
      (DirichletCharacter.LFunction χ (mellinLine519 N t)), ⟨hcont, hbd⟩, ?_⟩
  intro α
  rw [mellin_log_expansion519 hG N h2 q hq χ hχ α]
  simpa only [norm_neg] using h3 N (by omega) q hq χ α

end LeanLab.Linnik1951.Task519
