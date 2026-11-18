/-
Unit task393. Pointwise bounds for the prime power increment `Dpt δ y`, the helper lemmas
`Dpt_le_small` and `Dpt_le_mid` toward the open leaf `leaf_dpt_W_le` in `DqtWeight.lean`.
`Dpt δ y` is the sum over `k ≥ 2` of `θ(((1+δ)y)^{1/k}) - θ(y^{1/k})`; each term is bounded by a
count of integers times `log ((1+δ)y) / k`, and the sum of `1/k` is a logarithm.
Binary Goldbach is open; nothing here changes that.
AI wrote the Lean code, Claude. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ChirreHagen2025.ThetaPsi

namespace LeanLab.Task393
open Real Chebyshev Finset
open LeanLab.ChirreHagen2025

/-- `θ n - θ m ≤ (n - m) log C` for naturals `m ≤ n ≤ C`. -/
theorem theta_nat_sub_le (m : ℕ) (C : ℝ) : ∀ n : ℕ, m ≤ n → (n : ℝ) ≤ C →
    θ (n : ℝ) - θ (m : ℝ) ≤ ((n : ℝ) - m) * Real.log C := by
  intro n hmn
  induction n, hmn using Nat.le_induction with
  | base => intro _; simp
  | succ n hmn ih =>
    intro hC
    have hC' : (n : ℝ) + 1 ≤ C := by push_cast at hC; exact hC
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have ih' := ih (by linarith)
    have hstep : θ ((n + 1 : ℕ) : ℝ) - θ (n : ℝ) ≤ Real.log C := by
      rw [theta_eq_sum_Icc, theta_eq_sum_Icc, Nat.floor_natCast, Nat.floor_natCast,
        Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega)]
      simp only [add_sub_cancel_left]
      split_ifs with hp
      · exact Real.log_le_log (by positivity) hC
      · exact Real.log_nonneg (by linarith)
    have e : (((n + 1 : ℕ) : ℝ) - m) * Real.log C
        = ((n : ℝ) - m) * Real.log C + Real.log C := by push_cast; ring
    rw [e]
    linarith

/-- Count lemma: `θ c - θ a ≤ (c - a + 1) log c`. -/
theorem theta_sub_le_count {a c : ℝ} (_ha : 0 ≤ a) (hac : a ≤ c) (hc : 1 ≤ c) :
    θ c - θ a ≤ (c - a + 1) * Real.log c := by
  rw [theta_eq_theta_coe_floor c, theta_eq_theta_coe_floor a]
  have hmn : ⌊a⌋₊ ≤ ⌊c⌋₊ := Nat.floor_le_floor hac
  have hn : (⌊c⌋₊ : ℝ) ≤ c := Nat.floor_le (by linarith)
  have hm : a < ⌊a⌋₊ + 1 := Nat.lt_floor_add_one a
  have h := theta_nat_sub_le ⌊a⌋₊ c ⌊c⌋₊ hmn hn
  have hl : 0 ≤ Real.log c := Real.log_nonneg hc
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hl

/-- The `k`-th root interval: its ends, its length and the logarithm of its top end. -/
theorem root_facts {δ y : ℝ} (hδ : 0 < δ) (hy : 1 ≤ y) {k : ℕ} (hk2 : 2 ≤ k) :
    0 ≤ y ^ ((1 : ℝ) / k) ∧ y ^ ((1 : ℝ) / k) ≤ ((1 + δ) * y) ^ ((1 : ℝ) / k) ∧
    ((1 + δ) * y) ^ ((1 : ℝ) / k) ≤ y ^ ((1 : ℝ) / k) + δ * √y ∧
    1 ≤ ((1 + δ) * y) ^ ((1 : ℝ) / k) ∧
    Real.log (((1 + δ) * y) ^ ((1 : ℝ) / k)) = 1 / (k : ℝ) * Real.log ((1 + δ) * y) := by
  have hb1 : 1 ≤ (1 + δ) * y := by nlinarith
  have hyb : y ≤ (1 + δ) * y := by nlinarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hr0 : (0 : ℝ) ≤ 1 / k := by positivity
  have hr1 : (1 : ℝ) / k ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hk0 (by norm_num)]; norm_num; exact_mod_cast hk2
  have hy0 : 0 ≤ y ^ ((1 : ℝ) / k) := Real.rpow_nonneg (by linarith) _
  have hyb' : y ^ ((1 : ℝ) / k) ≤ ((1 + δ) * y) ^ ((1 : ℝ) / k) :=
    Real.rpow_le_rpow (by linarith) hyb hr0
  have hbk : ((1 + δ) * y) ^ ((1 : ℝ) / k) = (1 + δ) ^ ((1 : ℝ) / k) * y ^ ((1 : ℝ) / k) :=
    Real.mul_rpow (by linarith) (by linarith)
  have hδk : (1 + δ) ^ ((1 : ℝ) / k) ≤ 1 + δ := by
    calc (1 + δ) ^ ((1 : ℝ) / k) ≤ (1 + δ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 + δ := Real.rpow_one _
  have hysq : y ^ ((1 : ℝ) / k) ≤ √y := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hy hr1
  refine ⟨hy0, hyb', ?_, Real.one_le_rpow hb1 hr0, ?_⟩
  · rw [hbk]
    have h : ((1 + δ) ^ ((1 : ℝ) / k) - 1) * y ^ ((1 : ℝ) / k) ≤ δ * √y :=
      mul_le_mul (by linarith) hysq hy0 hδ.le
    have e : (1 + δ) ^ ((1 : ℝ) / k) * y ^ ((1 : ℝ) / k)
        = ((1 + δ) ^ ((1 : ℝ) / k) - 1) * y ^ ((1 : ℝ) / k) + y ^ ((1 : ℝ) / k) := by ring
    rw [e]
    linarith
  · rw [Real.log_rpow (by linarith)]

/-- A term of the sum, in general. -/
theorem term_le_big {δ y : ℝ} (hδ : 0 < δ) (hy : 1 ≤ y) {k : ℕ} (hk2 : 2 ≤ k) :
    θ (((1 + δ) * y) ^ ((1 : ℝ) / k)) - θ (y ^ ((1 : ℝ) / k))
      ≤ (δ * √y + 1) * (1 / (k : ℝ) * Real.log ((1 + δ) * y)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := root_facts hδ hy hk2
  have h := theta_sub_le_count h0 h1 h3
  have hl : 0 ≤ Real.log (((1 + δ) * y) ^ ((1 : ℝ) / k)) := Real.log_nonneg h3
  rw [h4] at h hl
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hl)

/-- A term of the sum when the root interval is shorter than 1. -/
theorem term_le_small {δ y : ℝ} (hδ : 0 < δ) (hy : 1 ≤ y) (hs : δ * √y < 1) {k : ℕ}
    (hk2 : 2 ≤ k) :
    θ (((1 + δ) * y) ^ ((1 : ℝ) / k)) - θ (y ^ ((1 : ℝ) / k))
      ≤ 1 / (k : ℝ) * Real.log ((1 + δ) * y) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := root_facts hδ hy hk2
  have h := theta_sub_le_log h0 h1 (by linarith) h3
  rw [h4] at h
  exact h

/-- `∑_{2 ≤ k ≤ N} 1/k ≤ log N`. -/
theorem sum_inv_le_log : ∀ N : ℕ, 1 ≤ N → ∑ k ∈ Icc 2 N, (1 / (k : ℝ)) ≤ Real.log N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have h := Real.log_le_sub_one_of_pos (div_pos hn0 hn1)
    rw [Real.log_div hn0.ne' hn1.ne'] at h
    have e : (n : ℝ) / (n + 1) = 1 - 1 / (n + 1) := by
      rw [eq_sub_iff_add_eq, ← add_div, div_self hn1.ne']
    push_cast
    linarith

/-- The sum over `k`, given a bound `c log b / k` on each term. -/
theorem Dpt_le_core {δ y c : ℝ} (hδ : 0 < δ) (hy : 2 ≤ y) (hc : 0 ≤ c)
    (hterm : ∀ k : ℕ, 2 ≤ k → θ (((1 + δ) * y) ^ ((1 : ℝ) / k)) - θ (y ^ ((1 : ℝ) / k))
      ≤ c * (1 / (k : ℝ) * Real.log ((1 + δ) * y))) :
    Dpt δ y ≤ c * Real.log ((1 + δ) * y) * Real.log (Real.log ((1 + δ) * y) / Real.log 2) := by
  set b := (1 + δ) * y with hb
  have hyb : y ≤ b := by nlinarith
  have hb2 : 2 ≤ b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hq1 : 1 ≤ Real.log b / Real.log 2 := by
    rw [le_div_iff₀ hl2, one_mul]; exact Real.log_le_log (by norm_num) hb2
  have hN1 : 1 ≤ ⌊Real.log b / Real.log 2⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; exact hq1)
  have hNy : ⌊Real.log y / Real.log 2⌋₊ ≤ ⌊Real.log b / Real.log 2⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hyb) hl2.le)
  have hNle : (⌊Real.log b / Real.log 2⌋₊ : ℝ) ≤ Real.log b / Real.log 2 :=
    Nat.floor_le (by linarith)
  unfold Dpt
  rw [← hb, fpt_eq_sum hb1 le_rfl, fpt_eq_sum (by linarith : (1 : ℝ) ≤ y) hNy,
    ← Finset.sum_sub_distrib]
  have h1 : ∑ k ∈ Icc 2 ⌊Real.log b / Real.log 2⌋₊,
        (θ (b ^ ((1 : ℝ) / k)) - θ (y ^ ((1 : ℝ) / k)))
      ≤ ∑ k ∈ Icc 2 ⌊Real.log b / Real.log 2⌋₊, c * Real.log b * (1 / (k : ℝ)) := by
    apply Finset.sum_le_sum
    intro k hk
    have h := hterm k (Finset.mem_Icc.mp hk).1
    have e : c * (1 / (k : ℝ) * Real.log b) = c * Real.log b * (1 / (k : ℝ)) := by ring
    rw [← e]; exact h
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  have h2 := sum_inv_le_log _ hN1
  have h3 : Real.log (⌊Real.log b / Real.log 2⌋₊ : ℝ) ≤ Real.log (Real.log b / Real.log 2) :=
    Real.log_le_log (by exact_mod_cast hN1) hNle
  exact mul_le_mul_of_nonneg_left (h2.trans h3) (mul_nonneg hc hlb)

theorem exp30_le : Real.exp 30 ≤ 2.0001 * 10 ^ 13 := by
  have h : Real.exp 1 ^ 30 ≤ (2.7182818286 : ℝ) ^ 30 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 30
  have e : Real.exp 30 = Real.exp 1 ^ 30 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  refine h.trans ?_
  norm_num

/-- `L = log (2.0001 / δ) ≥ 30` for `δ ≤ 10^-13`. -/
theorem L_ge_30 {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) :
    30 ≤ Real.log (2.0001 / δ) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  refine exp30_le.trans ?_
  rw [le_div_iff₀ hδ]
  have h : δ * 10 ^ 13 ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hδ1; exact hδ1
  nlinarith

theorem log_mul_le {c L : ℝ} (hc : 0 < c) (hL : 30 ≤ L) :
    Real.log (c * L) ≤ Real.log (30 * c) + L / 30 - 1 := by
  have hL0 : 0 < L := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < L / 30 by positivity)
  have e : c * L = (30 * c) * (L / 30) := by ring
  rw [e, Real.log_mul (by positivity) (by positivity)]
  linarith

theorem log90_le : Real.log 90 ≤ 5 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : (2.7 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 :=
    pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) Real.exp_one_gt_d9.le) 5
  have e : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  refine le_trans ?_ h
  norm_num

theorem log270_le : Real.log 270 ≤ 6 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : (2.7 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 :=
    pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) Real.exp_one_gt_d9.le) 6
  have e : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  refine le_trans ?_ h
  norm_num

/-- Small range `2 < y ≤ 1/(4δ²)`: every root interval is shorter than 1. -/
theorem Dpt_le_small {δ y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hy : 2 < y)
    (hyT : y ≤ 1 / (4 * δ ^ 2)) :
    Dpt δ y ≤ Real.log (2.0001 / δ) / 6 * Real.log ((1 + δ) * y) := by
  have hL30 : 30 ≤ Real.log (2.0001 / δ) := L_ge_30 hδ hδ1
  have hδ' : δ ≤ 1 := by
    have : (1 : ℝ) / 10 ^ 13 ≤ 1 := by norm_num
    linarith
  have hy0 : 0 < y := by linarith
  have hyb : y ≤ (1 + δ) * y := by nlinarith
  have hB0 : 0 < (1 + δ) * y := mul_pos (by linarith) hy0
  have hyT' : 4 * δ ^ 2 * y ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hyT; linarith
  have hsq : δ * √y ≤ 1 / 2 := by
    by_contra h
    rw [not_le] at h
    have h2 := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)
    rw [mul_pow, Real.sq_sqrt hy0.le] at h2
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl23 : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlb : 0 ≤ Real.log ((1 + δ) * y) := Real.log_nonneg (by linarith)
  have hcore := Dpt_le_core (c := 1) hδ hy.le zero_le_one (fun k hk => by
    rw [one_mul]; exact term_le_small hδ (by linarith) (by linarith) hk)
  have hbd : (1 + δ) * y ≤ (2.0001 / δ) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have h := mul_le_mul_of_nonneg_left hyT' (by linarith : (0 : ℝ) ≤ 1 + δ)
    have e : (1 + δ) * y * δ ^ 2 = (1 + δ) * (4 * δ ^ 2 * y) / 4 := by ring
    rw [e]
    norm_num
    linarith
  have e2 : Real.log ((2.0001 / δ) ^ 2) = 2 * Real.log (2.0001 / δ) := by
    rw [Real.log_pow]; norm_num
  have hlogb : Real.log ((1 + δ) * y) ≤ 2 * Real.log (2.0001 / δ) := by
    rw [← e2]; exact Real.log_le_log hB0 hbd
  have hq1 : 1 ≤ Real.log ((1 + δ) * y) / Real.log 2 := by
    rw [le_div_iff₀ hl2, one_mul]; exact Real.log_le_log (by norm_num) (by linarith)
  have hq : Real.log ((1 + δ) * y) / Real.log 2 ≤ 3 * Real.log (2.0001 / δ) := by
    rw [div_le_iff₀ hl2]
    have h := mul_le_mul_of_nonneg_left hl23
      (by linarith : (0 : ℝ) ≤ 3 * Real.log (2.0001 / δ))
    linarith
  have hll : Real.log (Real.log ((1 + δ) * y) / Real.log 2) ≤ Real.log (2.0001 / δ) / 6 := by
    have h1 := Real.log_le_log (by linarith) hq
    have h2 := log_mul_le (c := 3) (by norm_num) hL30
    have e90 : (30 : ℝ) * 3 = 90 := by norm_num
    rw [e90] at h2
    have h3 := log90_le
    linarith
  have hfin := mul_le_mul_of_nonneg_left hll hlb
  calc Dpt δ y ≤ 1 * Real.log ((1 + δ) * y)
        * Real.log (Real.log ((1 + δ) * y) / Real.log 2) := hcore
    _ = Real.log ((1 + δ) * y) * Real.log (Real.log ((1 + δ) * y) / Real.log 2) := by ring
    _ ≤ Real.log ((1 + δ) * y) * (Real.log (2.0001 / δ) / 6) := hfin
    _ = Real.log (2.0001 / δ) / 6 * Real.log ((1 + δ) * y) := by ring

/-- Mid range `1/(4δ²) < y ≤ δ^-6`: each root interval holds at most `δ √y + 1` primes. -/
theorem Dpt_le_mid {δ y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13)
    (hyT : 1 / (4 * δ ^ 2) < y) (hy6 : y ≤ 1 / δ ^ 6) :
    Dpt δ y ≤ 9 / 2 * Real.log (2.0001 / δ) ^ 2 * (δ * √y) := by
  have hL30 : 30 ≤ Real.log (2.0001 / δ) := L_ge_30 hδ hδ1
  have hδ' : δ ≤ 1 / 10 := by
    have : (1 : ℝ) / 10 ^ 13 ≤ 1 / 10 := by norm_num
    linarith
  have hy0 : 0 < y := lt_trans (by positivity) hyT
  have hyT' : 1 < 4 * δ ^ 2 * y := by
    rw [div_lt_iff₀ (by positivity)] at hyT; linarith
  have hy6' : y * δ ^ 6 ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hy6; exact hy6
  have hδ2 : δ ^ 2 ≤ 1 / 100 := by nlinarith
  have hy2 : 2 ≤ y := by
    by_contra h
    rw [not_le] at h
    have := mul_le_mul hδ2 h.le hy0.le (by norm_num : (0 : ℝ) ≤ 1 / 100)
    linarith
  have hyb : y ≤ (1 + δ) * y := by nlinarith
  have hB0 : 0 < (1 + δ) * y := mul_pos (by linarith) hy0
  have hs0 : 0 ≤ δ * √y := by positivity
  have hsq : 1 ≤ 2 * (δ * √y) := by
    by_contra h
    rw [not_le] at h
    have h2 := pow_lt_pow_left₀ h (by positivity) (by norm_num : (2 : ℕ) ≠ 0)
    rw [mul_pow, mul_pow, Real.sq_sqrt hy0.le] at h2
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl23 : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlb : 0 ≤ Real.log ((1 + δ) * y) := Real.log_nonneg (by linarith)
  have hcore := Dpt_le_core (c := δ * √y + 1) hδ hy2 (by linarith) (fun k hk =>
    term_le_big hδ (by linarith) hk)
  have hbd : (1 + δ) * y ≤ (2.0001 / δ) ^ 6 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have h := mul_le_mul_of_nonneg_left hy6' (by linarith : (0 : ℝ) ≤ 1 + δ)
    have e : (1 + δ) * y * δ ^ 6 = (1 + δ) * (y * δ ^ 6) := by ring
    rw [e]
    norm_num
    linarith
  have e6 : Real.log ((2.0001 / δ) ^ 6) = 6 * Real.log (2.0001 / δ) := by
    rw [Real.log_pow]; norm_num
  have hlogb : Real.log ((1 + δ) * y) ≤ 6 * Real.log (2.0001 / δ) := by
    rw [← e6]; exact Real.log_le_log hB0 hbd
  have hq1 : 1 ≤ Real.log ((1 + δ) * y) / Real.log 2 := by
    rw [le_div_iff₀ hl2, one_mul]; exact Real.log_le_log (by norm_num) (by linarith)
  have hq : Real.log ((1 + δ) * y) / Real.log 2 ≤ 9 * Real.log (2.0001 / δ) := by
    rw [div_le_iff₀ hl2]
    have h := mul_le_mul_of_nonneg_left hl23
      (by linarith : (0 : ℝ) ≤ 9 * Real.log (2.0001 / δ))
    linarith
  have hll0 : 0 ≤ Real.log (Real.log ((1 + δ) * y) / Real.log 2) := Real.log_nonneg hq1
  have hll : Real.log (Real.log ((1 + δ) * y) / Real.log 2) ≤ Real.log (2.0001 / δ) / 4 := by
    have h1 := Real.log_le_log (by linarith) hq
    have h2 := log_mul_le (c := 9) (by norm_num) hL30
    have e270 : (30 : ℝ) * 9 = 270 := by norm_num
    rw [e270] at h2
    have h3 := log270_le
    linarith
  have a1 : (δ * √y + 1) * Real.log ((1 + δ) * y)
        * Real.log (Real.log ((1 + δ) * y) / Real.log 2)
      ≤ (3 * (δ * √y)) * (6 * Real.log (2.0001 / δ)) * (Real.log (2.0001 / δ) / 4) :=
    mul_le_mul (mul_le_mul (by linarith) hlogb hlb (by linarith)) hll hll0
      (mul_nonneg (by linarith) (by linarith))
  calc Dpt δ y ≤ (δ * √y + 1) * Real.log ((1 + δ) * y)
        * Real.log (Real.log ((1 + δ) * y) / Real.log 2) := hcore
    _ ≤ (3 * (δ * √y)) * (6 * Real.log (2.0001 / δ)) * (Real.log (2.0001 / δ) / 4) := a1
    _ = 9 / 2 * Real.log (2.0001 / δ) ^ 2 * (δ * √y) := by ring

end LeanLab.Task393
