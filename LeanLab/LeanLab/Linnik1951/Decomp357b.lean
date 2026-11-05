/-
P0093 pages 165 and 168. Separate local major arc analysis from the arithmetic tail.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357a
import LeanLab.Linnik1951.Decomp357l

namespace LeanLab.Linnik1951

/-- LEAF. P0093 page 165 equation 8.1, page 166 equation 8.2 and page 168
equation 10.7. Local arc expansion and its logarithmic relative error give
the finite singular series main term. This leaf does not replace its tail
by the infinite Euler product. -/
theorem major_to_truncated357 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        ε * scale111 k N := by
  sorry

/-- LEAF. P0093 page 168 equations 10.5 and 10.6. Summing the singular
series tail over the exponent tuples gives a negligible error. This is
arithmetic and has no GRH or Mellin hypothesis. -/
theorem truncated_to_main357 (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |truncatedMain357 k N - mainTerm111 k N| ≤ ε * scale111 k N := by
  exact truncated_to_main_from_tail357 k hk ε hε

/-- P0093 page 168 equations 10.6 and 10.7. Exact major_error280 statement.
CONDITIONAL on the local major arc and arithmetic tail leaves. -/
theorem major_error_decomposed357 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - mainTerm111 k N| ≤
        ε * scale111 k N := by
  obtain ⟨Na, ha⟩ := major_to_truncated357 hG hM k hk (ε / 2) (by positivity)
  obtain ⟨Nt, ht⟩ := truncated_to_main357 k hk (ε / 2) (by positivity)
  refine ⟨max Na Nt, ?_⟩
  intro N hev hN
  have hA := ha N hev (lt_of_le_of_lt (le_max_left _ _) hN)
  have hT := ht N hev (lt_of_le_of_lt (le_max_right _ _) hN)
  calc
    _ ≤ |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| +
        |truncatedMain357 k N - mainTerm111 k N| := abs_sub_le _ _ _
    _ ≤ ε / 2 * scale111 k N + ε / 2 * scale111 k N := add_le_add hA hT
    _ = _ := by ring

end LeanLab.Linnik1951
