import LeanLab.ChenDoubleSieve.Decomp347a
import LeanLab.ChenDoubleSieve.Decomp347f
import LeanLab.ChenDoubleSieve.Decomp347g

/-!
The first half with the exact sealed modulus correction retained.
Source: https://arxiv.org/pdf/0705.1652, pages 36 and 37 equation 9.7.
This does not close the original first_half leaf.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task347
open Task275 Task315
open Wu41 (S PS)

/-- The exact finite first half transport with the crossing defect retained.
Source: page 36 substitutions and page 37 equation 9.7. The positive S4 reserve
is kept in baseline. No claim that the defect is a power error is made. -/
theorem first_half_transport_with_defect (N : ℕ) (hN : 1 ≤ N) :
    2 * sieveTerms N 0 - sieveTerms N 1 - sieveTerms N 3 +
      sieveTerms N 4 + sieveTerms N 5 - 2 * sieveTerms N 7 -
      sieveTerms N 9 + deltaOne N ≤ baseline N + crossingDefect N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let K := (N : ℝ) ^ kappa1
  let V := (N : ℝ) ^ kappa2
  let T := (N : ℝ) ^ sigma2
  have hKV : K ≤ V :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [kappa1, kappa2])
  have hVT : V ≤ T :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [kappa2, sigma2])
  have hTN : T ≤ (N : ℝ) := by
    dsimp only [T]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN1 (show sigma2 ≤ 1 by norm_num [sigma2])
  have hfirst := first_buchstab_printed N hN
  have hS1 : (Wu08.S₁ (primeSequence N) N V T : ℝ) =
      sieveTerms N 3 - (∑ p ∈ PS N K V, S (primeSequence N) p N K : ℕ) -
      ((∑ q ∈ lowerCrossingPairs N, S (primeSequence N) (q.1 * q.2) N q.1) : ℝ) := by
    change (Wu08.S₁ (primeSequence N) N V T : ℝ) =
      ((∑ p ∈ PS N K T, S (primeSequence N) p N K : ℕ) : ℝ) -
      (∑ p ∈ PS N K V, S (primeSequence N) p N K : ℕ) -
      ((∑ q ∈ lowerCrossingPairs N, S (primeSequence N) (q.1 * q.2) N q.1) : ℝ)
    simpa only [lowerCrossingPairs, Nat.cast_sum] using
      S1_buchstab_expansion (primeSequence N) N hKV hVT hTN
  have hS2 : (Wu08.S₂ (primeSequence N) N T : ℝ) = sieveTerms N 7 := by
    unfold Wu08.S₂
    rw [pairs_eq_upper]
    rfl
  have hS3 := S3_raising_with_defect N hN
  have hcross := small_pair_compensation N hN
  have hS4 : (0 : ℝ) ≤ (Wu08.S₄ (primeSequence N) N V T : ℝ) := Nat.cast_nonneg _
  dsimp only [baseline, deltaOne]
  rw [← hS2]
  nlinarith only [hfirst, hS1, hS3, hcross, hS4]

/-- A clean first half estimate with its unabsorbed crossing defect stated explicitly.
Source: page 37 equation 9.7 and the corrected finite transport. This is weaker
than the sealed first_half statement and is not used to label that leaf closed. -/
theorem first_half_with_defect : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      2 * sieveTerms N 0 - sieveTerms N 1 - sieveTerms N 3 +
        sieveTerms N 4 + sieveTerms N 5 - 2 * sieveTerms N 7 -
        sieveTerms N 9 + deltaOne N ≤
      2 * (D12 N : ℝ) + crossingDefect N + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  obtain ⟨M, hM⟩ := baseline_bound
  refine ⟨11, by norm_num, max M 1, ?_⟩
  intro N hEven hN
  have hfinite := first_half_transport_with_defect N (by omega)
  have hbase := hM N hEven (by omega)
  linarith only [hfinite, hbase]

end LeanLab.ChenDoubleSieve.Task347
