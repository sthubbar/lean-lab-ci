/-
P0093 page 168 equation 10.6. Close the arithmetic main term replacement.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp376a

namespace LeanLab.Linnik1951

/-- P0093 page 168 equation 10.6. Exact truncated_to_main357 statement,
now using the proved pointwise singular tail rather than a cited input. -/
theorem truncated_to_main_proved376 (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |truncatedMain357 k N - mainTerm111 k N| ≤ ε * scale111 k N := by
  obtain ⟨C, hC, Nt, ht⟩ := singular_tail_decomposed376
  let A := 1 / Real.log 2 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨Ne, he⟩ := power_saving_negligible357 (A ^ k * C / Real.log 2 ^ 2)
    (1 / 100) (by positivity) (by norm_num) k ε hε
  obtain ⟨Nl, hl⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨max 2 (max Nt (max Ne Nl)), ?_⟩
  intro N hev hN
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have htN : Nt < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have heN : Ne < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hlN : Nl < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hlR : (Nl : ℝ) < (N : ℝ) := by exact_mod_cast hlN
  have hlog : 1 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos _) (hl.trans hlR).le
    simpa only [Real.log_exp] using h
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
    have hp : (2 : ℝ) ^ Nat.log 2 N ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    have hh := Real.log_le_log (pow_pos (by norm_num) _) hp
    rw [Real.log_pow] at hh
    exact (le_div_iff₀ hl2).mpr hh
  have hbox : ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ k ≤ (A * Real.log N) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    dsimp [A]
    rw [add_mul, one_div_mul_eq_div]
    linarith
  have hscale : (N : ℝ) ≤ scale111 k N := by
    have hr : 1 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hl2).mpr
      (by simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ N by exact_mod_cast h2.le))
    exact le_mul_of_one_le_right hpos.le (one_le_pow₀ hr)
  have hb := truncated_error_card357 k N (C * (N : ℝ) ^ (-(1 / 100 : ℝ))) (by positivity) (ht N htN)
  have hp : (N : ℝ) ^ (-(1 / 100 : ℝ)) * N = (N : ℝ) ^ (1 - (1 / 100 : ℝ)) := by
    calc
      _ = (N : ℝ) ^ (-(1 / 100 : ℝ)) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ (-(1 / 100 : ℝ) + 1) := (Real.rpow_add hpos _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ (A * Real.log N) ^ k * (C * (N : ℝ) ^ (-(1 / 100 : ℝ))) *
        ((N : ℝ) / Real.log 2 ^ 2) := hb.trans (by gcongr)
    _ = (A ^ k * C / Real.log 2 ^ 2) * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) * Real.log N ^ k := by
      rw [mul_pow, ← hp]
      ring
    _ ≤ ε * N := he N heN
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale hε.le

end LeanLab.Linnik1951
