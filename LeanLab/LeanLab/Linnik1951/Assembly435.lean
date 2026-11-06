/-
P0093 pages 166 to 169. Assemble the refined binary entropy supply.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Assembly376
import LeanLab.Linnik1951.Cover435
import LeanLab.Linnik1951.Circle435

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997

/-- P0093 Page 166 equation 9.2. Exact exceptional_error280 statement through the refined interval cover and doubled system mass. CONDITIONAL on these analytic and geometric inputs. -/
theorem exceptional_error435 (hG : LeanLab.DERZ1997.GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ k : ℕ, 3 ≤ k →
      ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |arcContribution280 k N (exceptionalArcs280 N η)| ≤ ε * scale111 k N := by
  obtain ⟨η, hη, hη1, C, hC, Nc, hc⟩ := exceptional_prime_mass435 hG
  obtain ⟨A, hA, Na, ha⟩ := power_uniform_log357
  refine ⟨η, hη, hη1, ?_⟩
  intro k hk ε hε
  obtain ⟨Ne, he⟩ := power_saving_negligible357 (Real.exp 1 * A ^ k * C)
    (1 / 100) (by positivity) (by norm_num) k ε hε
  refine ⟨max 2 (max Nc (max Na Ne)), ?_⟩
  intro N hev hN
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hcN : Nc < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have haN : Na < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have heN : Ne < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hscale : (N : ℝ) ≤ scale111 k N := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast h2.le)
    have hr : 1 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hl)
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hr)
  have hbound := arc_abs_le_prime_mass357 k N (by omega) (exceptionalArcs280 N η)
    (fun α hα => hα.1) (measurable_exceptional357 N (by omega) η)
    (A * Real.log N) (mul_nonneg hA.le hlog) (fun α _ => ha N haN α)
  calc
    _ ≤ Real.exp 1 * (A * Real.log N) ^ k *
        (C * (N : ℝ) ^ (1 - (1 / 100 : ℝ))) :=
      hbound.trans (mul_le_mul_of_nonneg_left (hc N hcN) (by positivity))
    _ = (Real.exp 1 * A ^ k * C) * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) * Real.log N ^ k := by
      rw [mul_pow]; ring
    _ ≤ ε * N := he N heN
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale hε.le

/-- P0093 Page 168 after equation 10.7. Exact error_bound111 statement assembled through the task435 entropy supply and existing analytic leaves. The singular tail and remaining minor estimate are proved. CONDITIONAL on the remaining explicit inputs. -/
theorem error_bound435 (hG : LeanLab.DERZ1997.GRH) :
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
  obtain ⟨NM, hM⟩ := major_error_refined376 hG (mellin_bound_refined376 hG) k hk _ hε
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

/-- P0093 Pages 168 and 169. Exact original GRH existence conclusion through the refined error bound. This remains CONDITIONAL on the remaining explicit inputs. -/
theorem linnik1951_decomposed435 : GRH → ∃ K, AllLargeEven (LinnikAtMost K) := by
  intro hG
  obtain ⟨C, η, hC, hη, hη1, he⟩ := error_bound435 hG
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
