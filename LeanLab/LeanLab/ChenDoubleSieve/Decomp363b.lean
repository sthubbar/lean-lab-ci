import LeanLab.ChenDoubleSieve.Decomp363c

/-!
The two analytic inputs in the written proof of Wu 2004 equation 10.2.
The linear sieve retains the arithmetic progression discrepancy.
The mean value input contains neither a sifted count nor the lower function.
Source: https://arxiv.org/pdf/0705.1652, page 6 and page 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task363
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The finite level Q used before equation 10.2. -/
def sieveLevel (B : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B

/-- Squarefree moduli up to Q that are coprime to N.
One is present when Q is at least one. The moduli need not have all prime
factors below the sifting level. -/
def remainderModuli (B : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊sieveLevel B N⌋₊).filter (fun q => Squarefree q ∧ q.Coprime N)

/-- The absolute discrepancy sum dominated by Lemma 2.3 on page 38.
Only the fixed endpoint N and residue N are needed here. -/
def rawRemainder (B : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ remainderModuli B N,
    |(#((primeSequence N).filter (fun a => q ∣ a)) : ℝ) -
      Wu04.li N / (q.totient : ℝ)|

/-- The discrepancy is nonnegative for every finite parameter choice. -/
theorem rawRemainder_nonneg (B : ℝ) (N : ℕ) : 0 ≤ rawRemainder B N := by
  exact Finset.sum_nonneg (fun q _ => abs_nonneg _)

/-- LEAF. Wu 2004 page 6 Lemma 2.2 equation 2.5, specialized on page 38.
Retain the li main term, the relative sieve error and the discrepancy sum
with its fixed sieve constant.
This estimate has not used the mean value theorem of Lemma 2.3. -/
theorem linear_sieve_with_remainder (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        liMain0 f B N - δ * (Wu04.li N * lowerDensity N) -
          C * rawRemainder B N ≤ sieveTerms N 0 := by
  sorry

/-- LEAF. Wu 2004 page 6 Lemma 2.3 and page 38 remainder display.
Specialize to the single multiplier one, the endpoint N and residue N.
The estimate has no linear sieve function and no sifted count. -/
theorem remainder_log_cubic : ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      rawRemainder B N ≤ D * (N : ℝ) / log N ^ 3 := by
  sorry

/-- The exact sealed main0_lower statement follows from the two analytic pieces.
OPEN through linear_sieve_with_remainder and remainder_log_cubic.
This proof has no sorry of its own and calls neither original OPEN target. -/
theorem main0_lower_supplied (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        main0 f B N - η * Θ N ≤ sieveTerms N 0 := by
  intro η hη
  obtain ⟨K, hK, M, hM⟩ := li_density_scale_bounded
  obtain ⟨C, hC, hs⟩ := linear_sieve_with_remainder F f h
    (η / (3 * K)) (by positivity)
  obtain ⟨B, hB, D, hD, L, hL⟩ := remainder_log_cubic
  obtain ⟨J, hJ⟩ := hs B hB
  obtain ⟨T, hT⟩ := log_cubic_absorbed (C * D) (η / 3)
    (mul_nonneg hC hD) (by positivity)
  obtain ⟨U, hU⟩ := liMain0_error_absorbed F f h B (η / 3) (by positivity)
  refine ⟨B, hB, max M (max L (max J (max T U))), ?_⟩
  intro N hEven hN
  have hscale := hM N hEven (by omega)
  have hraw := mul_le_mul_of_nonneg_left (hL N hEven (by omega)) hC
  have hsmall := hT N (by omega)
  have hbudget : η / (3 * K) * (Wu04.li N * lowerDensity N) ≤
      η / 3 * Θ N := by
    calc
      _ ≤ η / (3 * K) * (K * Θ N) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by field_simp
  have hremainder : C * rawRemainder B N ≤ η / 3 * Θ N := by
    calc
      _ ≤ C * (D * (N : ℝ) / log N ^ 3) := hraw
      _ = (C * D) * (N : ℝ) / log N ^ 3 := by ring
      _ ≤ _ := hsmall
  have hbound := hJ N hEven (by omega)
  have hli := le_trans (le_abs_self (main0 f B N - liMain0 f B N))
    (hU N hEven (by omega))
  linarith

end LeanLab.ChenDoubleSieve.Task363
