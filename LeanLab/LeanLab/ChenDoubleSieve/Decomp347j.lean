import LeanLab.ChenDoubleSieve.Decomp347h

/-!
The remaining compensation obligation for the exact sealed first half.
Source: https://arxiv.org/pdf/0705.1652, pages 36 and 37 equation 9.7.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task347
open Task275 Task315
open Wu41 (S PS)

/-- Three nonnegative reserves from the written Buchstab substitutions.
Source: page 36 and page 37 equation 9.7. The first reserve pays for Upsilon 5,
the second is the corrected S3 raising surplus, and the third is S4. -/
def transportReserve (N : ℕ) : ℝ :=
  ((∑ q ∈ lowerCrossingPairs N, S (primeSequence N) (q.1 * q.2) N q.1) : ℝ) +
    tripleTerms N 1 - sieveTerms N 5 +
    (exemptUpsilon10 N + tripleTerms N 2 -
      (Wu08.S₃ (primeSequence N) N ((N : ℝ) ^ kappa2) ((N : ℝ) ^ sigma2) : ℝ)) +
    (Wu08.S₄ (primeSequence N) N ((N : ℝ) ^ kappa2) ((N : ℝ) ^ sigma2) : ℝ)

/-- Every reserve is nonnegative before any averaged compensation is asserted.
Source: page 36 substitutions and the nonnegative S4 in page 35 equation 9.5. -/
theorem transportReserve_nonneg (N : ℕ) (hN : 1 ≤ N) : 0 ≤ transportReserve N := by
  have h1 := small_pair_compensation N hN
  have h2 := S3_raising_le N hN
  have h3 : (0 : ℝ) ≤
      (Wu08.S₄ (primeSequence N) N ((N : ℝ) ^ kappa2) ((N : ℝ) ^ sigma2) : ℝ) := Nat.cast_nonneg _
  unfold transportReserve
  linarith only [h1, h2, h3]

/-- The finite transport separates the crossing defect from its explicit reserves.
Source: page 36 substitutions and page 37 equation 9.7. -/
theorem first_half_transport_identity (N : ℕ) (hN : 1 ≤ N) :
    2 * sieveTerms N 0 - sieveTerms N 1 - sieveTerms N 3 +
      sieveTerms N 4 + sieveTerms N 5 - 2 * sieveTerms N 7 -
      sieveTerms N 9 + deltaOne N = baseline N + crossingDefect N - transportReserve N := by
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
  dsimp only [baseline, deltaOne, transportReserve]
  rw [← hS2, exemptUpsilon10_eq]
  nlinarith only [hfirst, hS1]

/-- LEAF. Wu 2004 pages 36 and 37, positive reserves in the proof of equation 9.7.
Only the remaining averaged comparison for the exact sealed Upsilon 10 convention
is asserted. This has no D12 and none of the initial prime or base sieve terms.
Its validity at the literal convention remains the recorded QUESTION. -/
theorem crossing_compensation : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      crossingDefect N ≤ transportReserve N + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  sorry

/-- The previous transport header is preserved and follows from the smaller compensation leaf.
Source: pages 36 and 37 equation 9.7. OPEN through crossing_compensation. -/
theorem first_half_transport : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      2 * sieveTerms N 0 - sieveTerms N 1 - sieveTerms N 3 +
        sieveTerms N 4 + sieveTerms N 5 - 2 * sieveTerms N 7 -
        sieveTerms N 9 + deltaOne N ≤
      baseline N + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  obtain ⟨C, hC, M, hM⟩ := crossing_compensation
  refine ⟨C, hC, max M 1, ?_⟩
  intro N hEven hN
  have hid := first_half_transport_identity N (by omega)
  have hc := hM N hEven (by omega)
  linarith only [hid, hc]

/-- Exact supply of the sealed first_half conclusion from the smaller transport leaf.
Source: page 37 equation 9.7. This assembly remains OPEN through transport. -/
theorem first_half_supplied : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      2 * sieveTerms N 0 - sieveTerms N 1 - sieveTerms N 3 +
        sieveTerms N 4 + sieveTerms N 5 - 2 * sieveTerms N 7 -
        sieveTerms N 9 + deltaOne N ≤
      2 * (D12 N : ℝ) + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  obtain ⟨C, hC, M, hM⟩ := first_half_transport
  obtain ⟨B, hB⟩ := baseline_bound
  refine ⟨C + 11, by linarith, max M B, ?_⟩
  intro N hEven hN
  have ht := hM N hEven (by omega)
  have hb := hB N hEven (by omega)
  nlinarith only [ht, hb]


end LeanLab.ChenDoubleSieve.Task347
