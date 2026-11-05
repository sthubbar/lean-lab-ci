/-
P0093 pages 168 and 169. Assembly through the refined supply leaves.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357j

namespace LeanLab.Linnik1951

/-- P0093 page 168 after equation 10.7. Exact error_bound111 statement.
CONDITIONAL on six independent analytic and counting supply leaves. -/
theorem error_bound_refined357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 ∧
      ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |(representationCount111 k N : ℝ) - mainTerm111 k N| ≤
          5 * C * scale111 k N * (1 - η) ^ (k - 2) := by
  obtain ⟨η, hη, hη1, hE⟩ := exceptional_error_decomposed357 hG
  obtain ⟨C, hC, hR⟩ := minor_error_proved357 η hη hη1 (fun N α hα => good_minor_power_bound280 N η α hα)
  refine ⟨C, η, hC, hη, hη1, ?_⟩
  intro k hk
  have hr : 0 < (1 - η) ^ (k - 2) := pow_pos (by linarith) _
  have hε : 0 < C * (1 - η) ^ (k - 2) := mul_pos hC hr
  obtain ⟨NM, hM⟩ := major_error_decomposed357 hG (mellin_bound_decomposed357 hG) k hk _ hε
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
  have hid := circle_partition_decomposed357 k N (by omega) η
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

open LeanLab.Linnik LeanLab.DERZ1997

/-- P0093 pages 168 and 169. Exact original GRH existence conclusion.
CONDITIONAL on the six supply leaves in error_bound_refined357. -/
theorem linnik1951_refined357 : GRH → ∃ K, AllLargeEven (LinnikAtMost K) := by
  intro hG
  obtain ⟨C, η, hC, hη, hη1, he⟩ := error_bound_refined357 hG
  obtain ⟨c, hc, hm⟩ := main_lower111
  obtain ⟨k, hk, hkc⟩ := choose_exponent111 hC hc hη hη1
  obtain ⟨Ne, he⟩ := he k hk
  obtain ⟨Nm, hm⟩ := hm k hk
  refine ⟨k, max 1 (max Ne Nm), ?_⟩
  intro N hev hN
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNe : Ne < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNm : Nm < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have he' := he N hev hNe
  have hpos : 0 < (representationCount111 k N : ℝ) :=
    positive_of_error111 (scale_pos111 k N h1) hkc (hm N hev hNm) (by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using he')
  exact atMost_of_exact (representation_of_count_pos111 (by exact_mod_cast hpos))

end LeanLab.Linnik1951
