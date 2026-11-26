/-
P0093 Sections 3 to 10. Existing analytic conclusions after their data.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Base280b
import LeanLab.Linnik1951.Decomp111

namespace LeanLab.Linnik1951

/-- LEAF. P0093 page 159 equation 5.2, from the Mellin contour shift under
GRH and Lemma 2 on pages 156 to 158. Only the diagonal case is needed here. -/
theorem mellin_bound280 (hG : LeanLab.DERZ1997.GRH) : MellinBound280 := by
  exact mellin_bound696 hG

/-- LEAF. P0093 page 165 equations 8.1 and 8.2, and page 168 equations 10.5
to 10.7. The major arc error is arbitrarily small relative to scale for fixed k.
The Mellin input feeds the local prime square estimate of Section 6. -/
theorem major_error280 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - mainTerm111 k N| ≤
        ε * scale111 k N := by
  exact major_error_split111 hG k hk ε hε

/-- LEAF. P0093 pages 162 to 166 Lemmas 4 to 7, equations 7.6 and 9.2.
Choose one absolute eta so the exceptional minor contribution is arbitrarily
small relative to scale for each fixed k under GRH via equation 9.1.
Enlarging to a measurable cover
bounds the actual large T set used in this statement. -/
theorem exceptional_error280 (hG : LeanLab.DERZ1997.GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ k : ℕ, 3 ≤ k →
      ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |arcContribution280 k N (exceptionalArcs280 N η)| ≤ ε * scale111 k N := by
  exact exceptional_error_split111 hG

/-- LEAF. P0093 page 167 immediately before equation 10.1.
Outside the exceptional set the power series is at most its chosen threshold. -/
theorem good_minor_power_bound280 (N : ℕ) (η α : ℝ)
    (hα : α ∈ goodMinorArcs280 N η) :
    ‖powerFourier111 N α‖ ≤ (1 - η) * ‖powerFourier111 N 0‖ := by
  exact le_of_not_gt (fun h => hα.2 (Or.inr ⟨hα.1, fun hm => hα.2 (Or.inl hm), h⟩))

/-- LEAF. P0093 page 167 equation 10.1 with the factor e from equation 2.2
absorbed in an absolute constant. Lemma 3 and the bound on T outside its
exceptional set give geometric decay in k minus two. -/
theorem minor_error280 (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hT : ∀ N : ℕ, ∀ α : ℝ, α ∈ goodMinorArcs280 N η →
      ‖powerFourier111 N α‖ ≤ (1 - η) * ‖powerFourier111 N 0‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 < N →
        |arcContribution280 k N (goodMinorArcs280 N η)| ≤
          C * scale111 k N * (1 - η) ^ (k - 2) := by
  exact minor_error_proved357_up111 η hη hη1 hT

/-- LEAF. P0093 page 154 equation 2.2 and page 167 equation 10.2.
Fourier orthogonality counts the representations and the disjoint measurable
partition of the unit interval splits its integral into three pieces. -/
theorem circle_partition280 (k N : ℕ) (hN : 1 ≤ N) (η : ℝ) :
    (representationCount111 k N : ℝ) =
      arcContribution280 k N (majorArcs280 N) +
      arcContribution280 k N (exceptionalArcs280 N η) +
      arcContribution280 k N (goodMinorArcs280 N η) := by
  exact circle_partition_proved435_up111 k N hN η

/-- P0093 page 168 after equation 10.7. The exact error_bound111 statement
follows from the six smaller leaves. CONDITIONAL on those leaves. -/
theorem error_bound_decomposed280 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 ∧
      ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |(representationCount111 k N : ℝ) - mainTerm111 k N| ≤
          5 * C * scale111 k N * (1 - η) ^ (k - 2) := by
  obtain ⟨η, hη, hη1, hE⟩ := exceptional_error280 hG
  obtain ⟨C, hC, hR⟩ := minor_error280 η hη hη1 (fun N α hα => good_minor_power_bound280 N η α hα)
  refine ⟨C, η, hC, hη, hη1, ?_⟩
  intro k hk
  have hr : 0 < (1 - η) ^ (k - 2) := pow_pos (by linarith) _
  have hε : 0 < C * (1 - η) ^ (k - 2) := mul_pos hC hr
  obtain ⟨NM, hM⟩ := major_error280 hG (mellin_bound280 hG) k hk _ hε
  obtain ⟨NE, hE⟩ := hE k hk _ hε
  obtain ⟨NR, hR⟩ := hR k hk
  refine ⟨max 1 (max NM (max NE NR)), ?_⟩
  intro N hev hN
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hm : NM < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have he : NE < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hg : NR < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hmajor := hM N hev hm
  have hexc := hE N hev he
  have hminor := hR N hev hg
  have hs := (scale_pos111 k N h1).le
  have hid := circle_partition280 k N (by omega) η
  have htri := abs_add_le
    (arcContribution280 k N (majorArcs280 N) - mainTerm111 k N)
    (arcContribution280 k N (exceptionalArcs280 N η))
  have htri' := abs_add_le
    ((arcContribution280 k N (majorArcs280 N) - mainTerm111 k N) +
      arcContribution280 k N (exceptionalArcs280 N η))
    (arcContribution280 k N (goodMinorArcs280 N η))
  have heq : (representationCount111 k N : ℝ) - mainTerm111 k N =
    ((arcContribution280 k N (majorArcs280 N) - mainTerm111 k N) +
      arcContribution280 k N (exceptionalArcs280 N η)) +
      arcContribution280 k N (goodMinorArcs280 N η) := by rw [hid]; ring
  rw [heq]
  nlinarith [mul_nonneg (mul_nonneg hC.le hs) hr.le]

end LeanLab.Linnik1951
