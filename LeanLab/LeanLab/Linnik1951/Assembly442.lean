/-
P0093 pages 168 and 169. Assemble the proved arithmetic relative correction.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Relative442
import LeanLab.Linnik1951.Assembly435

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997

/-- P0093 page 168 equation 10.7. Exact finite major arc target with
its arithmetic correction proved. CONDITIONAL on the existing local
major expansion, GRH and the explicit Mellin input. -/
theorem major_to_truncated442 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        ε * scale111 k N := by
  obtain ⟨A, hA, Na, ha⟩ := major_expansion_remainder376 hG hM k hk
  obtain ⟨Nr, hr⟩ := major_relative_negligible_proved442 k hk (ε / (2 * A)) (by positivity)
  obtain ⟨Np, hp⟩ := power_saving_negligible357 A (1 / 1000) hA
    (by norm_num) (k + 13) (ε / 2) (by positivity)
  refine ⟨max 2 (max Na (max Nr Np)), ?_⟩
  intro N hev hN
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNa : Na < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNr : Nr < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNp : Np < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hscale : (N : ℝ) ≤ scale111 k N := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast h2.le)
    have hr : 1 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hl)
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hr)
  have hrel : A * majorRelative376 k N ≤ (ε / 2) * scale111 k N := by
    calc
      _ ≤ A * (ε / (2 * A) * scale111 k N) :=
        mul_le_mul_of_nonneg_left (hr N hev hNr) hA.le
      _ = _ := by field_simp [hA.ne']
  have hpower : A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) ≤
      (ε / 2) * scale111 k N :=
    (hp N hNp).trans (mul_le_mul_of_nonneg_left hscale (by positivity))
  calc
    _ ≤ A * majorRelative376 k N +
        A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := ha N hev hNa
    _ ≤ (ε / 2) * scale111 k N + (ε / 2) * scale111 k N := add_le_add hrel hpower
    _ = _ := by ring

/-- P0093 page 168 equations 10.6 and 10.7. Exact major_error280
statement with the arithmetic coefficient replacement and relative
correction proved. CONDITIONAL on the remaining local major expansion,
GRH and the explicit Mellin input. -/
theorem major_error442 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - mainTerm111 k N| ≤
        ε * scale111 k N := by
  obtain ⟨Na, ha⟩ := major_to_truncated442 hG hM k hk (ε / 2) (by positivity)
  obtain ⟨Nt, ht⟩ := truncated_to_main_proved376 k hk (ε / 2) (by positivity)
  refine ⟨max Na Nt, ?_⟩
  intro N hev hN
  have hA := ha N hev (lt_of_le_of_lt (le_max_left _ _) hN)
  have hT := ht N hev (lt_of_le_of_lt (le_max_right _ _) hN)
  calc
    _ ≤ |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| +
        |truncatedMain357 k N - mainTerm111 k N| := abs_sub_le _ _ _
    _ ≤ ε / 2 * scale111 k N + ε / 2 * scale111 k N := add_le_add hA hT
    _ = _ := by ring

/-- P0093 page 168 after equation 10.7. Exact error_bound111
statement using the proved arithmetic relative correction. CONDITIONAL
on the unchanged central and outer Mellin bounds, major expansion and
doubled system expansion. No arithmetic relative bound is cited. -/
theorem error_bound442 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 ∧
      ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |(representationCount111 k N : ℝ) - mainTerm111 k N| ≤
          5 * C * scale111 k N * (1 - η) ^ (k - 2) := by
  obtain ⟨η, hη, hη1, hE⟩ := exceptional_error435 hG
  obtain ⟨C, hC, hR⟩ := minor_error_proved357 η hη hη1 (fun N α hα => good_minor_power_bound280 N η α hα)
  refine ⟨C, η, hC, hη, hη1, ?_⟩
  intro k hk
  have hr : 0 < (1 - η) ^ (k - 2) := pow_pos (by linarith) _
  have hε : 0 < C * (1 - η) ^ (k - 2) := mul_pos hC hr
  obtain ⟨NM, hM⟩ := major_error442 hG (mellin_bound_refined376 hG) k hk _ hε
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
  have hid := circle_partition_proved435 k N (by omega) η
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

/-- P0093 pages 154, 168 and 169. Exact linnik1951_decomposed111
statement from the refined error assembly. CONDITIONAL on the four
remaining analytic inputs listed above. -/
theorem linnik1951_decomposed442 : GRH → ∃ K, AllLargeEven (LinnikAtMost K) := by
  intro hG
  obtain ⟨C, η, hC, hη, hη1, he⟩ := error_bound442 hG
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
