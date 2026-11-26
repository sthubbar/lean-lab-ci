import LeanLab.HelfgottMajor.SPLIT_stieltjes_positive_zero_sum
import LeanLab.HelfgottMajor.SPLIT_zero_count_error_bound

/-!
Wiring of `positive_mass_norm_sum_integral_endpoint_of_leaves` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral_stieltjes`, burst-20261124 S3.

That assembly rests on three leaves of the proof of book Lemma 16.9, P0014 Part IV pages 431 and
432, as applied in Lemma 16.10 on pages 433 and 434. In this burst `error_integral_le` was proved
in place, `stieltjes_positive_zero_sum` was proved as the twin
`StieltjesSplit.stieltjes_positive_zero_sum_of_leaves`, and `zero_count_error_bound` was reduced by
the proved bridge `ZeroCountErrorBound.count_of_book` to the book count of display 3.95.

The result below repeats the assembly with those proved pieces, so the endpoint bound holds
CONDITIONAL ON exactly one input: the book zero count of display 3.95, display 16.21 page 431,
taken here as the hypothesis `hbook`, the statement of the cited leaf
`ZeroCount1623.book_zero_count`. It is complete and its axioms are the standard three.
The endpoint term at height `T` stays, as the module doc of the Stieltjes file explains.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a.EndpointWire
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- The bound of `positive_mass_norm_sum_integral_endpoint_of_leaves`, book Lemma 16.9 applied as
in Lemma 16.10, pages 431 to 434, CONDITIONAL ON the book zero count of display 3.95 for `χ` at
every height at least one, the hypothesis `hbook`. -/
theorem positive_mass_norm_sum_integral_endpoint_of_book (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hbook : ∀ U : ℝ, 1 ≤ U →
      |ZeroCount1623.bookCount χ U - ZeroCount1623.bookMain q U| ≤ ZeroCount1623.bookError q U) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ *
        (0.15 * log ((q : ℝ) * T) + 3.389) := by
  obtain ⟨c, hc⟩ := ZeroCountErrorBound.count_of_book χ hbook
  rw [StieltjesSplit.stieltjes_positive_zero_sum_of_leaves q χ δ T c hT hzeros]
  have hE := error_integral_le q χ δ T c hT (fun t ht => hc t ht.1)
  have hTb := abs_le.mp (hc T hT)
  have h1b := abs_le.mp (hc 1 le_rfl)
  have hGT : 0 ≤ ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ := norm_nonneg _
  have hG1eq : ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ =
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ := by
    simp only [Complex.ofReal_one, one_mul]
  have hG1 : 0 ≤ ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ := norm_nonneg _
  rw [hG1eq]
  simp only [mul_one] at h1b ⊢
  nlinarith [mul_le_mul_of_nonneg_left hTb.2 hGT, mul_le_mul_of_nonneg_left h1b.1 hG1]

end LeanLab.HelfgottMajor.Decomp431a.EndpointWire

#print axioms LeanLab.HelfgottMajor.Decomp431a.EndpointWire.positive_mass_norm_sum_integral_endpoint_of_book
