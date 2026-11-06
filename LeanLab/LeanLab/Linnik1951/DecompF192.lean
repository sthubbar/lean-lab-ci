/-
P0093 page 168 after equation 10.7. Split of error_bound111 into leaf estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp111

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997
open Finset

/-- Major arc contribution as a real number, from the circle method. -/
noncomputable def majorContribF192 (k N : ℕ) : ℝ := 0

/-- Exceptional minor arc contribution as a real number. -/
noncomputable def exceptionalContribF192 (k N : ℕ) (η : ℝ) : ℝ := 0

/-- Remaining minor arc contribution as a real number. -/
noncomputable def minorContribF192 (k N : ℕ) (η : ℝ) : ℝ := 0

/-- LEAF. Step one of the error bound argument: choose a positive geometric
parameter eta strictly below one. This is the eta that controls the
geometric decay in the minor arc estimate. -/
theorem leaf_eta_exists_F192 (hG : GRH) : ∃ η : ℝ, 0 < η ∧ η < 1 := by
  sorry

/-- LEAF. Step two of the error bound argument: the circle method expresses
the representation count as the sum of a major arc contribution, an
exceptional minor contribution and a remaining minor contribution.
This is the partition identity of page 154 equation 2.2 and page 167
equation 10.2. -/
theorem leaf_circle_partition_F192 (k N : ℕ) (hN : 1 ≤ N) (η : ℝ) :
    (representationCount111 k N : ℝ) =
      (majorContribF192 k N : ℝ) + (exceptionalContribF192 k N η : ℝ) +
      (minorContribF192 k N η : ℝ) := by
  sorry

/-- LEAF. Step three of the error bound argument: under GRH the major arc
contribution differs from the main term by at most epsilon times scale
for each fixed k at least 3 and all sufficiently large even N.
This is page 168 equations 10.5 to 10.7. -/
theorem leaf_major_bound_F192 (hG : GRH) (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |(majorContribF192 k N : ℝ) - mainTerm111 k N| ≤ ε * scale111 k N := by
  sorry

/-- LEAF. Step four of the error bound argument: under GRH there exists
eta strictly between zero and one such that the exceptional minor
contribution is at most epsilon times scale for each fixed k at least 3
and all sufficiently large even N. This is page 166 equations 9.1 to 9.3. -/
theorem leaf_exceptional_bound_F192 (hG : GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |(exceptionalContribF192 k N η : ℝ)| ≤ ε * scale111 k N := by
  sorry

/-- LEAF. Step five of the error bound argument: for any fixed eta strictly
between zero and one, the remaining minor contribution is bounded by
C times scale times the k minus 2 power of 1 minus eta, for some positive
absolute C and each fixed k at least 3. This is page 167 equation 10.1. -/
theorem leaf_minor_bound_F192 (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |(minorContribF192 k N η : ℝ)| ≤ C * scale111 k N * (1 - η) ^ (k - 2) := by
  sorry

/-- P0093 page 168 after equation 10.7. Assembly of the exact error_bound111
statement from the five leaf estimates. CONDITIONAL on those leaves. -/
theorem error_bound111_F192 (hG : GRH) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 ∧
      ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |(representationCount111 k N : ℝ) - mainTerm111 k N| ≤
          5 * C * scale111 k N * (1 - η) ^ (k - 2) := by
  obtain ⟨η, hη, hη1, hE⟩ := leaf_exceptional_bound_F192 hG
  obtain ⟨C, hC, hR⟩ := leaf_minor_bound_F192 η hη hη1
  refine ⟨C, η, hC, hη, hη1, ?_⟩
  intro k hk
  have hr : 0 < (1 - η) ^ (k - 2) := pow_pos (by linarith) _
  have hε : 0 < C * (1 - η) ^ (k - 2) := mul_pos hC hr
  obtain ⟨NM, hM⟩ := leaf_major_bound_F192 hG k hk _ hε
  obtain ⟨NE, hE'⟩ := hE k hk _ hε
  obtain ⟨NR, hR'⟩ := hR k hk
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
  have hexc := hE' N hev he
  have hminor := hR' N hev hg
  have hs := (scale_pos111 k N h1).le
  have hid := leaf_circle_partition_F192 k N (by omega) η
  have heq : (representationCount111 k N : ℝ) - mainTerm111 k N =
    ((majorContribF192 k N : ℝ) - mainTerm111 k N) +
      (exceptionalContribF192 k N η : ℝ) + (minorContribF192 k N η : ℝ) := by
    rw [hid]
    ring
  rw [heq]
  have htri := abs_add_le
    ((majorContribF192 k N : ℝ) - mainTerm111 k N)
    ((exceptionalContribF192 k N η : ℝ) + (minorContribF192 k N η : ℝ))
  have htri2 := abs_add_le
    (exceptionalContribF192 k N η : ℝ) (minorContribF192 k N η : ℝ)
  nlinarith [mul_nonneg (mul_nonneg hC.le hs) hr.le]

end LeanLab.Linnik1951
