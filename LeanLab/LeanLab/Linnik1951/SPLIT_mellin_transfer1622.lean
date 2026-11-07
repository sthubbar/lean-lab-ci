/-
Split of mellin_transfer1622 into three leaves. The transfer of the character
prime sum to a Mellin integral is cut into three independent steps: the line
bound of the coefficient under the zero hypothesis, the prime power expansion of
the logarithm, and the size of the part of that expansion carrying powers of
exponent at least two. The assembly at the end has no sorry and does not use
mellin_transfer1622.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT1622_mellin

namespace LeanLab.Linnik1951

/-- LEAF. Line bound step. Under the hypothesis on the zeros, the logarithm of the
L-function of a nonprincipal character, taken on the line 1/2 + 1/ln N + i t, is
continuous in t and bounded by a constant independent of N times ln cubed of N
times (|t| + 2). This is the only step that uses the zero hypothesis. It carries
no estimate on the difference of the two sums and no Mellin integral. -/
theorem lineBound_lnL1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          LineBound1622 N B0
            (fun t : ℝ => Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))) := by
  sorry

/-- LEAF. Prime power expansion step. The difference between the character prime
sum and the Mellin integral of the logarithm of the L-function is exactly minus
the sum over all primes and all exponents at least two, each term carrying the
value of the character at the prime power and the exponential damping at that
power. This is an identity for every real alpha, with the zero hypothesis only
used to keep the logarithm on one branch and to move the line past the zeros. -/
theorem mellin_lnL_expansion1622 (hG : LeanLab.DERZ1997.GRH) :
    ∀ N : ℕ, 2 ≤ N → ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ,
      characterPrime280 χ N α -
          mellinU1622 N
            (fun t : ℝ => Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))) α
        = -∑' p : Nat.Primes, ∑' k : ℕ,
            (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)) := by
  sorry

/-- LEAF. Prime power tail step. The part of the prime power sum with exponents at
least two, summed over all primes and all such exponents, is at most a constant
times the square root of N. The exponential damping at the powers is what makes
the sum absolutely convergent. No zero hypothesis, no character estimate and no
Mellin integral occur here. -/
theorem prime_power_tail1622 :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ α : ℝ,
        ‖∑' p : Nat.Primes, ∑' k : ℕ,
            (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
          ≤ B * Real.sqrt N := by
  sorry

/-- The three leaves together give the transfer of the character prime sum to a
Mellin integral on the line, with the coefficient the logarithm of the
L-function. -/
theorem mellin_transfer1622_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, LineBound1622 N B0 M ∧ ∀ α : ℝ,
            ‖characterPrime280 χ N α - mellinU1622 N M α‖ ≤ B * Real.sqrt N := by
  obtain ⟨B0, hB0, N1, h1⟩ := lineBound_lnL1622 hG
  obtain ⟨B, hB, N3, h3⟩ := prime_power_tail1622
  refine ⟨B0, hB0, B, hB, max N1 (max N3 2), ?_⟩
  intro N hN q hq hqt χ hχ
  haveI : NeZero q := ⟨by omega⟩
  have h2 : 2 ≤ N := by omega
  refine ⟨fun t : ℝ => Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t)),
    h1 N (by omega) q hq hqt χ hχ, ?_⟩
  intro α
  rw [mellin_lnL_expansion1622 hG N h2 q χ hχ α]
  simpa only [norm_neg] using h3 N (by omega) q hq χ α

end LeanLab.Linnik1951
