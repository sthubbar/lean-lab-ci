/-
Unit task393, far range of the pointwise bound for `Dpt`.

For `y ≥ δ^-6` the prime power increment `Dpt δ y` is at most `4 δ √y`. The squares are
counted with the Brun-Titchmarsh bound `primesBetween_le` at level `y^(1/6)`; the cubes and
higher powers are counted trivially, one prime per integer. This is a helper for the open leaf
`leaf_dpt_W_le` in `DqtWeight.lean`, which stays open; binary Goldbach is open as well.
AI wrote the Lean code, Claude. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ChirreHagen2025.ThetaPsi
import LeanLab.PNTSieve.BrunTitchmarsh

namespace LeanLab.Task393
open Real Chebyshev Finset
open LeanLab.ChirreHagen2025

/-- `θ c - θ a` is at most `log c` times the number of primes in `(⌊a⌋, ⌊c⌋]`. -/
theorem far_theta_sub_le_card {a c : ℝ} (hac : a ≤ c) (hc : 1 ≤ c) (ha : 0 ≤ a) :
    θ c - θ a ≤ Real.log c *
      (((Finset.Ico (⌊a⌋₊ + 1) (⌊c⌋₊ + 1)).filter Nat.Prime).card : ℝ) := by
  have e : ∀ n : ℕ, Finset.Icc 0 n = Finset.Ico 0 (n + 1) := by
    intro n; ext p; simp
  have hmn : ⌊a⌋₊ + 1 ≤ ⌊c⌋₊ + 1 := Nat.succ_le_succ (Nat.floor_le_floor hac)
  rw [theta_eq_sum_Icc c, theta_eq_sum_Icc a, Finset.sum_filter, Finset.sum_filter, e, e,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (⌊a⌋₊ + 1)) hmn, add_sub_cancel_left,
    ← Finset.sum_filter]
  have hle : ∀ p ∈ (Finset.Ico (⌊a⌋₊ + 1) (⌊c⌋₊ + 1)).filter Nat.Prime,
      Real.log (p : ℝ) ≤ Real.log c := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have hpn : (p : ℝ) ≤ (⌊c⌋₊ : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hp.1.2
    exact Real.log_le_log hp0 (hpn.trans (Nat.floor_le (by linarith)))
  have := Finset.sum_le_card_nsmul _ _ _ hle
  rw [nsmul_eq_mul] at this
  linarith

/-- `θ c - θ a ≤ log c * primesBetween a c`. -/
theorem far_theta_sub_le_primesBetween {a c : ℝ} (hac : a ≤ c) (hc : 1 ≤ c) (ha : 0 ≤ a) :
    θ c - θ a ≤ Real.log c * (LeanLab.PNTSieve.BrunTitchmarsh.primesBetween a c : ℝ) := by
  refine (far_theta_sub_le_card hac hc ha).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg hc)
  unfold LeanLab.PNTSieve.BrunTitchmarsh.primesBetween
  have hsub : (Finset.Ico (⌊a⌋₊ + 1) (⌊c⌋₊ + 1)).filter Nat.Prime ⊆
      (Finset.Icc ⌈a⌉₊ ⌊c⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨(Nat.ceil_le_floor_add_one a).trans hp.1.1, Nat.lt_succ_iff.mp hp.1.2⟩, hp.2⟩
  exact_mod_cast Finset.card_le_card hsub

/-- `θ c - θ a ≤ (c - a + 1) log c`, one prime per integer. -/
theorem far_theta_sub_le_count {a c : ℝ} (hac : a ≤ c) (hc : 1 ≤ c) (ha : 0 ≤ a) :
    θ c - θ a ≤ (c - a + 1) * Real.log c := by
  refine (far_theta_sub_le_card hac hc ha).trans ?_
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hc)
  have h1 : ((Finset.Ico (⌊a⌋₊ + 1) (⌊c⌋₊ + 1)).filter Nat.Prime).card ≤ ⌊c⌋₊ - ⌊a⌋₊ := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Ico]; omega
  have hmn : ⌊a⌋₊ ≤ ⌊c⌋₊ := Nat.floor_le_floor hac
  have h2 : (((Finset.Ico (⌊a⌋₊ + 1) (⌊c⌋₊ + 1)).filter Nat.Prime).card : ℝ)
      ≤ (⌊c⌋₊ : ℝ) - (⌊a⌋₊ : ℝ) := by
    rw [← Nat.cast_sub hmn]; exact_mod_cast h1
  have h3 : (⌊c⌋₊ : ℝ) ≤ c := Nat.floor_le (by linarith)
  have h4 : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  linarith

/-- The absorption inequality in the variable `w = y^(1/48)`. -/
theorem far_absorb {δ w : ℝ} (hδ : 0 < δ) (hw : 40 ≤ w) (hD : 1 ≤ δ * w ^ 8) :
    3.001 * (δ * w ^ 24) + 73728 * w ^ 12 + 96 * w * ((δ * w ^ 16 + 1) * (48 * w))
      ≤ 4 * (δ * w ^ 24) := by
  have hw0 : (0 : ℝ) ≤ w := by linarith
  have w4 : (2560000 : ℝ) ≤ w ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 40) hw 4
    norm_num at this; linarith
  have w6 : (4096000000 : ℝ) ≤ w ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 40) hw 6
    norm_num at this; linarith
  have h1 : 73728 * w ^ 12 ≤ 0.03 * (δ * w ^ 24) := by
    have a : w ^ 12 ≤ δ * w ^ 8 * w ^ 12 := le_mul_of_one_le_left (by positivity) hD
    have b : (73728 : ℝ) ≤ 0.03 * w ^ 4 := by linarith
    calc 73728 * w ^ 12 ≤ (0.03 * w ^ 4) * (δ * w ^ 8 * w ^ 12) :=
          mul_le_mul b a (by positivity) (by positivity)
      _ = 0.03 * (δ * w ^ 24) := by ring
  have h2 : 4608 * (δ * w ^ 18) ≤ 0.01 * (δ * w ^ 24) := by
    have a : (4608 : ℝ) ≤ 0.01 * w ^ 6 := by linarith
    calc 4608 * (δ * w ^ 18) ≤ (0.01 * w ^ 6) * (δ * w ^ 18) :=
          mul_le_mul_of_nonneg_right a (by positivity)
      _ = 0.01 * (δ * w ^ 24) := by ring
  have h3 : 4608 * w ^ 2 ≤ 4608 * (δ * w ^ 18) := by
    have a : w ^ 2 ≤ δ * w ^ 8 * w ^ 2 := le_mul_of_one_le_left (by positivity) hD
    have b : w ^ 10 ≤ w ^ 18 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have c : δ * w ^ 10 ≤ δ * w ^ 18 := mul_le_mul_of_nonneg_left b hδ.le
    have d : δ * w ^ 8 * w ^ 2 = δ * w ^ 10 := by ring
    linarith
  have e : 96 * w * ((δ * w ^ 16 + 1) * (48 * w)) = 4608 * (δ * w ^ 18) + 4608 * w ^ 2 := by
    ring
  have hX : 0 ≤ δ * w ^ 24 := by positivity
  rw [e]
  linarith

/-- Far range: for `y ≥ δ^-6`, `Dpt δ y ≤ 4 δ √y`. -/
theorem Dpt_le_far {δ y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hy6 : 1 / δ ^ 6 ≤ y) :
    Dpt δ y ≤ 4 * (δ * √y) := by
  have hδle : δ ≤ 1 / 10 ^ 14 * 10 := by norm_num at hδ1 ⊢; linarith
  have hδ6 : 0 < δ ^ 6 := by positivity
  have hy0' : 0 < y := lt_of_lt_of_le (by positivity) hy6
  have hy0 : 0 ≤ y := hy0'.le
  have hyδ : 1 ≤ y * δ ^ 6 := by rwa [div_le_iff₀ hδ6] at hy6
  have hy78 : (10 : ℝ) ^ 78 ≤ y := by
    have h1 : δ ^ 6 ≤ (1 / 10 ^ 13) ^ 6 := pow_le_pow_left₀ hδ.le hδ1 6
    have h2 : y * δ ^ 6 ≤ y * (1 / 10 ^ 13) ^ 6 := mul_le_mul_of_nonneg_left h1 hy0
    have h3 : (1 : ℝ) ≤ y * (1 / 10 ^ 13) ^ 6 := hyδ.trans h2
    have h4 : y * (1 / 10 ^ 13) ^ 6 = y / 10 ^ 78 := by ring
    rw [h4, le_div_iff₀ (by positivity)] at h3
    linarith
  have hy1 : 1 ≤ y := le_trans (one_le_pow₀ (by norm_num)) hy78
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = y ^ ((1 : ℝ) / 48) := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by rw [hw]; exact Real.rpow_nonneg hy0 _
  have hw48 : w ^ 48 = y := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
  have hw40 : 40 ≤ w := by
    by_contra h
    push Not at h
    have h1 := pow_lt_pow_left₀ h hw0 (by norm_num : 48 ≠ 0)
    rw [hw48] at h1
    have h2 : (40 : ℝ) ^ 48 ≤ 10 ^ 78 := by norm_num
    linarith
  have hwpos : 0 < w := by linarith
  have hw16 : y ^ ((1 : ℝ) / 3) = w ^ 16 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
  have hs : √y = w ^ 24 := by
    have e : (w ^ 24) ^ 2 = y := by rw [← hw48]; ring
    rw [← e]; exact Real.sqrt_sq (by positivity)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log w := ⟨_, rfl⟩
  have hℓ1 : 1 ≤ ℓ := by
    have := Real.exp_one_lt_d9
    rw [hℓ]; exact (Real.le_log_iff_exp_le hwpos).mpr (by linarith)
  have hℓw : ℓ ≤ w - 1 := by rw [hℓ]; exact Real.log_le_sub_one_of_pos hwpos
  have hLy : Real.log y = 48 * ℓ := by rw [← hw48, Real.log_pow, hℓ]; norm_num
  have hD : 1 ≤ δ * w ^ 8 := by
    by_contra h
    push Not at h
    have h1 : (δ * w ^ 8) ^ 6 < 1 := pow_lt_one₀ (by positivity) h (by norm_num)
    have h2 : (δ * w ^ 8) ^ 6 = y * δ ^ 6 := by rw [← hw48]; ring
    linarith
  set b := (1 + δ) * y with hb
  have hyb' : y < b := by nlinarith
  have hyb : y ≤ b := hyb'.le
  have hb1 : 1 ≤ b := by linarith
  have hLb : Real.log b ≤ 48 * ℓ + δ := by
    rw [hb, Real.log_mul (by linarith) (by linarith), hLy]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + δ by linarith)
    linarith
  have hLb0 : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hδ1' : δ ≤ 1 := by norm_num at hδle; linarith
  have hLbw : Real.log b ≤ 48 * w := by linarith
  set N := ⌊Real.log b / Real.log 2⌋₊ with hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNy : ⌊Real.log y / Real.log 2⌋₊ ≤ N :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hyb) hl2.le)
  unfold Dpt
  rw [← hb, fpt_eq_sum hb1 le_rfl, fpt_eq_sum hy1 hNy, ← Finset.sum_sub_distrib]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 3.001 * (δ * w ^ 24) + 73728 * w ^ 12 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (δ * w ^ 16 + 1) * (48 * w) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have e2 : ∀ t : ℝ, t ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) = √t := fun t => by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hterm : ∀ k ∈ Icc 2 N, θ (b ^ ((1 : ℝ) / k)) - θ (y ^ ((1 : ℝ) / k))
      ≤ (if k = 2 then A else 0) + B := by
    intro k hk
    rcases eq_or_ne k 2 with rfl | hk2ne
    · rw [if_pos (rfl : (2:ℕ) = 2), e2, e2]
      have hlt : √y < √b := Real.sqrt_lt_sqrt hy0 hyb'
      have hsy0 : 0 < √y := Real.sqrt_pos.mpr hy0'
      have hsb : √b ≤ (1 + δ / 2) * √y := by
        rw [hb, Real.sqrt_mul (by linarith)]
        apply mul_le_mul_of_nonneg_right _ hsy0.le
        exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
      have hh0 : 0 < √b - √y := by linarith
      have hh : √b - √y ≤ δ * w ^ 24 / 2 := by rw [← hs]; linarith
      have hz : 1 < w ^ 8 := by
        have := one_lt_pow₀ (show 1 < w by linarith) (by norm_num : 8 ≠ 0)
        exact this
      have hPB := LeanLab.PNTSieve.BrunTitchmarsh.primesBetween_le (√y) (√b - √y) (w ^ 8)
        hsy0 hh0 hz
      rw [show √y + (√b - √y) = √b by ring, Real.log_pow, ← hℓ] at hPB
      push_cast at hPB
      have hsb1 : 1 ≤ √b := by
        have : (1 : ℝ) ≤ w ^ 24 := one_le_pow₀ (by linarith)
        rw [hs] at hlt; linarith
      have hT := far_theta_sub_le_primesBetween hlt.le hsb1 hsy0.le
      rw [Real.log_sqrt (by linarith)] at hT
      have s1 : Real.log b / 2 * (2 * (√b - √y) / (8 * ℓ)) ≤ 3.001 * (δ * w ^ 24) := by
        have e : Real.log b / 2 * (2 * (√b - √y) / (8 * ℓ))
            = Real.log b * (√b - √y) / (8 * ℓ) := by ring
        rw [e, div_le_iff₀ (by linarith)]
        have a1 : Real.log b * (√b - √y) ≤ (48 * ℓ + δ) * (δ * w ^ 24 / 2) :=
          mul_le_mul hLb hh hh0.le (by linarith)
        have a2 : δ * (δ * w ^ 24) ≤ (0.016 * ℓ) * (δ * w ^ 24) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        nlinarith
      have s2 : Real.log b / 2 * (6 * w ^ 8 * (1 + 8 * ℓ) ^ 3) ≤ 73728 * w ^ 12 := by
        have a1 : (1 + 8 * ℓ) ^ 3 ≤ (8 * w) ^ 3 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 3
        calc Real.log b / 2 * (6 * w ^ 8 * (1 + 8 * ℓ) ^ 3)
            ≤ (48 * w / 2) * (6 * w ^ 8 * (8 * w) ^ 3) :=
              mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left a1 (by positivity))
                (by positivity) (by positivity)
          _ = 73728 * w ^ 12 := by ring
      have s3 : Real.log b / 2 *
          (LeanLab.PNTSieve.BrunTitchmarsh.primesBetween (√y) (√b) : ℝ)
          ≤ Real.log b / 2 * (2 * (√b - √y) / (8 * ℓ) + 6 * w ^ 8 * (1 + 8 * ℓ) ^ 3) :=
        mul_le_mul_of_nonneg_left hPB (by linarith)
      rw [hA]
      linarith
    · have hk3 : 3 ≤ k := by
        have := (Finset.mem_Icc.mp hk).1; omega
      rw [if_neg hk2ne, zero_add]
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hr0 : (0 : ℝ) ≤ 1 / k := by positivity
      have hr1 : (1 : ℝ) / k ≤ 1 / 3 := by
        rw [div_le_div_iff₀ hk0 (by norm_num)]; norm_num; exact_mod_cast hk3
      have hy0k : 0 ≤ y ^ ((1 : ℝ) / k) := by positivity
      have hybk : y ^ ((1 : ℝ) / k) ≤ b ^ ((1 : ℝ) / k) := Real.rpow_le_rpow hy0 hyb hr0
      have hbk : b ^ ((1 : ℝ) / k) = (1 + δ) ^ ((1 : ℝ) / k) * y ^ ((1 : ℝ) / k) :=
        Real.mul_rpow (by linarith) hy0
      have hδk : (1 + δ) ^ ((1 : ℝ) / k) ≤ 1 + δ := by
        calc (1 + δ) ^ ((1 : ℝ) / k) ≤ (1 + δ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = 1 + δ := Real.rpow_one _
      have hy3 : y ^ ((1 : ℝ) / k) ≤ w ^ 16 := by
        rw [← hw16]; exact Real.rpow_le_rpow_of_exponent_le hy1 hr1
      have hdiff : b ^ ((1 : ℝ) / k) - y ^ ((1 : ℝ) / k) + 1 ≤ δ * w ^ 16 + 1 := by
        have a1 : ((1 + δ) ^ ((1 : ℝ) / k) - 1) * y ^ ((1 : ℝ) / k) ≤ δ * w ^ 16 :=
          mul_le_mul (by linarith) hy3 hy0k hδ.le
        rw [hbk]; linarith
      have hb1k : 1 ≤ b ^ ((1 : ℝ) / k) := Real.one_le_rpow hb1 hr0
      have hlog : Real.log (b ^ ((1 : ℝ) / k)) ≤ 48 * w := by
        rw [Real.log_rpow (by linarith)]
        have : 1 / (k : ℝ) * Real.log b ≤ 1 * Real.log b :=
          mul_le_mul_of_nonneg_right
            (by rw [div_le_one hk0]; exact_mod_cast (by omega : 1 ≤ k)) hLb0
        linarith
      refine (far_theta_sub_le_count hybk hb1k hy0k).trans ?_
      rw [hB]
      exact mul_le_mul hdiff hlog (Real.log_nonneg hb1k) (by positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hite : (∑ k ∈ Icc 2 N, (if k = 2 then A else 0)) ≤ A := by
    simp only [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hA0
  have hNle : ((N + 1 - 2 : ℕ) : ℝ) ≤ 96 * w := by
    have h1 : ((N + 1 - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N + 1 - 2 ≤ N)
    have h2 : (N : ℝ) ≤ Real.log b / Real.log 2 := Nat.floor_le (div_nonneg hLb0 hl2.le)
    have h3 : Real.log b / Real.log 2 ≤ 96 * w := by
      rw [div_le_iff₀ hl2]
      have := Real.log_two_gt_d9
      have h4 : w * (1 / 2) ≤ w * Real.log 2 := mul_le_mul_of_nonneg_left (by linarith) hw0
      linarith
    linarith
  have hNB : ((N + 1 - 2 : ℕ) : ℝ) * B ≤ 96 * w * B := mul_le_mul_of_nonneg_right hNle hB0
  have hfin := far_absorb hδ hw40 hD
  rw [hs]
  subst hA hB
  linarith

end LeanLab.Task393
