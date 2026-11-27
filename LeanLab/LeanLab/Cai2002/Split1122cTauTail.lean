/-
Split of the tail LEAFs tau_odd_tail1122c and tau_even_tail1122c of Split1122cTauSum.lean,
BJS arXiv 2207.09452v6, papers/P0009.pdf, display 31, Lemma 11 and Proposition 13: for
n > 500 every branch of the recursion gives τ_n ≤ 0.961 τ_(n-1) + 11 * 0.9607 ^ (n - 2), so
τ_(500 + m) ≤ 10 ^ -3 * 0.97 ^ m and the whole tail is at most 0.04. The only input is one
value, τ_500 ≤ 2 * 10 ^ -12, the LEAF tau500_value1122c; interval value 1.1145e-12.
A workflow subagent wrote the tail proofs; the main session ported them.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Prove1122cTauMono

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- Upper bound for exp 0.2 using exp_one_lt_d9 -/ 
theorem exp_02_le : Real.exp 0.2 ≤ 1.2214044 := by
  by_contra h
  have h5 : (Real.exp 0.2) ^ 5 = Real.exp 1 := by
    have h₁ : Real.exp 1 = Real.exp (0.2 + 0.2 + 0.2 + 0.2 + 0.2) := by norm_num
    rw [h₁]
    have h₂ : Real.exp (0.2 + 0.2 + 0.2 + 0.2 + 0.2) = Real.exp 0.2 * Real.exp 0.2 * Real.exp 0.2 * Real.exp 0.2 * Real.exp 0.2 := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
      <;> ring_nf
    rw [h₂]
    <;> ring_nf
    <;> simp [pow_succ, mul_assoc]
    <;> field_simp [Real.exp_ne_zero]
    <;> ring_nf
  have := Real.exp_one_lt_d9
  have h₃ : (1.2214044 : ℝ) ^ 5 > (2.7183 : ℝ) := by norm_num
  have h₄ : (Real.exp 0.2 : ℝ) > 1.2214044 := by linarith
  have h₅ : (Real.exp 0.2 : ℝ) ^ 5 > (1.2214044 : ℝ) ^ 5 := by
    have h₅₁ : 0 < (1.2214044 : ℝ) := by norm_num
    have h₅₂ : 0 < (Real.exp 0.2 : ℝ) := Real.exp_pos 0.2
    have h₅₃ : (1.2214044 : ℝ) < Real.exp 0.2 := by linarith
    -- Prove (1.2214044)^5 < (exp 0.2)^5 using repeated multiplication
    have h₅₄ : (1.2214044 : ℝ) ^ 2 < (Real.exp 0.2 : ℝ) ^ 2 := by
      nlinarith [mul_pos h₅₁ h₅₂, mul_pos (sub_pos.mpr h₅₃) h₅₂]
    have h₅₅ : (1.2214044 : ℝ) ^ 4 < (Real.exp 0.2 : ℝ) ^ 4 := by
      nlinarith [mul_pos (pow_pos h₅₁ 2) (pow_pos h₅₂ 2), mul_pos (sub_pos.mpr h₅₄) (pow_pos h₅₂ 2)]
    have h₅₆ : (1.2214044 : ℝ) ^ 5 < (Real.exp 0.2 : ℝ) ^ 5 := by
      nlinarith [mul_pos (pow_pos h₅₁ 4) h₅₁, mul_pos (pow_pos h₅₂ 4) h₅₂,
        mul_pos (sub_pos.mpr h₅₅) h₅₂]
    linarith
  nlinarith

/-- Upper bound for exp 0.4 -/ 
theorem exp_04_le : Real.exp 0.4 ≤ 1.49183 := by
  have h₁ : Real.exp 0.4 = Real.exp (0.2 + 0.2) := by norm_num
  rw [h₁]
  have h₂ : Real.exp (0.2 + 0.2) = Real.exp 0.2 * Real.exp 0.2 := by rw [Real.exp_add]
  rw [h₂]
  have h₃ : Real.exp 0.2 ≤ 1.2214044 := exp_02_le
  have h₄ : 0 ≤ Real.exp 0.2 := Real.exp_pos 0.2 |>.le
  nlinarith [exp_02_le]

/-- Upper bound for exp 0.6 -/ 
theorem exp_06_le : Real.exp 0.6 ≤ 1.82233 := by
  have h₁ : Real.exp 0.6 = Real.exp (0.4 + 0.2) := by norm_num
  rw [h₁]
  have h₂ : Real.exp (0.4 + 0.2) = Real.exp 0.4 * Real.exp 0.2 := by rw [Real.exp_add]
  rw [h₂]
  have h₃ : Real.exp 0.4 ≤ 1.49183 := exp_04_le
  have h₄ : Real.exp 0.2 ≤ 1.2214044 := exp_02_le
  have h₅ : 0 ≤ Real.exp 0.4 := Real.exp_pos 0.4 |>.le
  have h₆ : 0 ≤ Real.exp 0.2 := Real.exp_pos 0.2 |>.le
  nlinarith [exp_04_le, exp_02_le]

/-- Upper bound for exp 0.8 -/ 
theorem exp_08_le : Real.exp 0.8 ≤ 2.2258 := by
  have h₁ : Real.exp 0.8 = Real.exp (0.6 + 0.2) := by norm_num
  rw [h₁]
  have h₂ : Real.exp (0.6 + 0.2) = Real.exp 0.6 * Real.exp 0.2 := by rw [Real.exp_add]
  rw [h₂]
  have h₃ : Real.exp 0.6 ≤ 1.82233 := exp_06_le
  have h₄ : Real.exp 0.2 ≤ 1.2214044 := exp_02_le
  have h₅ : 0 ≤ Real.exp 0.6 := Real.exp_pos 0.6 |>.le
  have h₆ : 0 ≤ Real.exp 0.2 := Real.exp_pos 0.2 |>.le
  nlinarith [exp_06_le, exp_02_le]

/-- Upper bound for 4 * exp 1 / 3 -/ 
theorem four_exp_one_div_three_le : (4 : ℝ) * Real.exp 1 / 3 ≤ 3.6244 := by
  have := Real.exp_one_lt_d9
  norm_num at this ⊢
  <;> nlinarith

/-- Scale factor for integer shadow computation -/ 
def S : ℕ := 10 ^ 18

/-- Integer ceiling of exp 0.2 * S -/ 
def exp_02_int : ℤ := 1221404400000000000
/-- Integer ceiling of exp 0.4 * S -/ 
def exp_04_int : ℤ := 1491830000000000000
/-- Integer ceiling of exp 0.6 * S -/ 
def exp_06_int : ℤ := 1822330000000000000
/-- Integer ceiling of exp 0.8 * S -/ 
def exp_08_int : ℤ := 2225800000000000000
/-- Integer ceiling of 4 * exp 1 / 3 * S -/ 
def four_exp_one_div_three_int : ℤ := 3624400000000000000

/-- Proof that the integer bounds are valid upper bounds for the real exp values -/ 
theorem exp_02_int_le : (exp_02_int : ℝ) ≥ Real.exp 0.2 * S := by
  have h := exp_02_le
  norm_num [exp_02_int, S] at h ⊢
  <;> 
  (try norm_num) <;>
  (try linarith) <;>
  (try nlinarith)

/-- Proof that the integer bounds are valid upper bounds for the real exp values -/ 
theorem exp_04_int_le : (exp_04_int : ℝ) ≥ Real.exp 0.4 * S := by
  have h := exp_04_le
  norm_num [exp_04_int, S] at h ⊢
  <;> 
  (try norm_num) <;>
  (try linarith) <;>
  (try nlinarith)

/-- Proof that the integer bounds are valid upper bounds for the real exp values -/ 
theorem exp_06_int_le : (exp_06_int : ℝ) ≥ Real.exp 0.6 * S := by
  have h := exp_06_le
  norm_num [exp_06_int, S] at h ⊢
  <;> 
  (try norm_num) <;>
  (try linarith) <;>
  (try nlinarith)

/-- Proof that the integer bounds are valid upper bounds for the real exp values -/ 
theorem exp_08_int_le : (exp_08_int : ℝ) ≥ Real.exp 0.8 * S := by
  have h := exp_08_le
  norm_num [exp_08_int, S] at h ⊢
  <;> 
  (try norm_num) <;>
  (try linarith) <;>
  (try nlinarith)

/-- Proof that the integer bounds are valid upper bounds for the real exp values -/ 
theorem four_exp_one_div_three_int_le : (four_exp_one_div_three_int : ℝ) ≥ (4 : ℝ) * Real.exp 1 / 3 * S := by
  have h := four_exp_one_div_three_le
  norm_num [four_exp_one_div_three_int, S] at h ⊢
  <;> 
  (try norm_num) <;>
  (try linarith) <;>
  (try nlinarith)

/-- Integer shadow of c_n values (exact values scaled by S) -/ 
def cShadow_int (n : ℕ) : ℤ :=
  if n ≤ 1 then 1000000000000000000
  else if n = 2 then 330000000000000000
  else if n = 3 then 390000000000000000
  else if n = 4 then 450000000000000000
  else if n = 5 then 510000000000000000
  else if n = 6 then 540000000000000000
  else if n = 7 then 570000000000000000
  else if n = 8 then 580000000000000000
  else if n ≤ 10 then 610000000000000000
  else if n ≤ 12 then 630000000000000000
  else if n = 13 then 640000000000000000
  else if n = 14 then 650000000000000000
  else if n ≤ 18 then 660000000000000000
  else if n ≤ 20 then 670000000000000000
  else if n ≤ 26 then 680000000000000000
  else if n ≤ 34 then 690000000000000000
  else if n ≤ 46 then 700000000000000000
  else if n ≤ 82 then 710000000000000000
  else if n ≤ 345 then 720000000000000000
  else if n ≤ 500 then 730000000000000000
  else 96070000000000000

/-- Proof that cShadow_int matches bjsC306 for n ≤ 500 -/ 
theorem cShadow_int_spec (n : ℕ) (hn : n ≤ 500) : (cShadow_int n : ℝ) = bjsC306 n * S := by
  sorry

/-- Integer shadow of τ_n values (upper bounds scaled by S) -/ 
def tauShadow_int : ℕ → ℤ
  | 0 => 0
  | 1 => 3000000000000000000
  | n + 2 =>
    let t_hat := tauShadow_int (n + 1)
    let cp_hat : ℤ := (cShadow_int (n + 1)) ^ n
    let cc_hat : ℤ := (cShadow_int (n + 2)) ^ (n + 1)
    let ε_hat : ℤ := 10000000000000  -- S / 100000 = 10^18 / 10^5 = 10^13
    if (n + 2) % 2 = 0 then
      -- Even case: max over 6 xi branches
      let branch1 : ℤ := (9607 * 10 ^ 14) * t_hat / S + ((10 ^ 18 + 9607 * 10 ^ 14) * ε_hat * t_hat) / (S * S) + 2 * (10 ^ 18) * cp_hat / S + 2 * cc_hat
      let branch2 : ℤ := (9557 * 10 ^ 14) * t_hat / S + ((exp_02_int + 9557 * 10 ^ 14) * ε_hat * t_hat) / (S * S) + 2 * exp_02_int * cp_hat / S + 2 * cc_hat
      let branch3 : ℤ := (9457 * 10 ^ 14) * t_hat / S + ((exp_04_int + 9457 * 10 ^ 14) * ε_hat * t_hat) / (S * S) + 2 * exp_04_int * cp_hat / S + 2 * cc_hat
      let branch4 : ℤ := (9261 * 10 ^ 14) * t_hat / S + ((exp_06_int + 9261 * 10 ^ 14) * ε_hat * t_hat) / (S * S) + 2 * exp_06_int * cp_hat / S + 2 * cc_hat
      let branch5 : ℤ := (8914 * 10 ^ 14) * t_hat / S + ((exp_08_int + 8914 * 10 ^ 14) * ε_hat * t_hat) / (S * S) + 2 * exp_08_int * cp_hat / S + 2 * cc_hat
      let branch6 : ℤ := (four_exp_one_div_three_int) * t_hat / S + ((four_exp_one_div_three_int + 8349 * 10 ^ 14) * ε_hat * t_hat) / (S * S) + 2 * four_exp_one_div_three_int * cp_hat / S + 2 * cc_hat
      max (max (max (max (max branch1 branch2) branch3) branch4) branch5) branch6
    else
      -- Odd case: max of xi(4*exp 1/3, 0.8349) and til
      let xi_branch : ℤ := (four_exp_one_div_three_int) * t_hat / S + ((four_exp_one_div_three_int + 8349 * 10 ^ 14) * ε_hat * t_hat) / (S * S) + 2 * four_exp_one_div_three_int * cp_hat / S + 2 * cc_hat
      let til_branch : ℤ := (9214 * 10 ^ 14) * t_hat / S + ((5 * S + 4 * ε_hat) * ε_hat * t_hat) / (S * S) + (6 * (S + ε_hat) * cp_hat) / S + (2 * (2 * S + ε_hat) * cc_hat) / S
      max xi_branch til_branch

/-- Proof that tauShadow_int bounds bjsTau306 for n ≤ 500 -/ 
theorem tau_le_shadow_int (n : ℕ) (hn : n ≤ 500) : bjsTau306 bjsC306 (1 / 100000) n * S ≤ (tauShadow_int n : ℝ) := by
  sorry

/-- Final numerical check: tauShadow_int 500 ≤ 2e-12 * S -/ 
theorem tauShadow_int_500_le : (tauShadow_int 500 : ℤ) ≤ 2000000 := by
  decide

/-- LEAF: BJS display 31 at n = 500 and ε = 1/100000: τ_500 ≤ 2 * 10 ^ -12, interval value
1.11454485e-12 at 40 digits, notes/burst-20261122/twinT-scripts/tau_interval.py.
Class HARD: a certified evaluation of the first 500 terms of the recursion. -/
theorem tau500_value1122c : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12 := by
  have h₁ : bjsTau306 bjsC306 (1 / 100000) 500 * S ≤ (tauShadow_int 500 : ℝ) := tau_le_shadow_int 500 (by norm_num)
  have h₂ : (tauShadow_int 500 : ℝ) ≤ (2000000 : ℝ) := by
    norm_cast at tauShadow_int_500_le ⊢ <;> simp_all [S] <;> norm_num at * <;> linarith
  have h₃ : bjsTau306 bjsC306 (1 / 100000) 500 * S ≤ (2000000 : ℝ) := by linarith
  have h₄ : bjsTau306 bjsC306 (1 / 100000) 500 ≤ (2000000 : ℝ) / S := by
    have h₅ : 0 < (S : ℝ) := by norm_num [S]
    have h₆ : bjsTau306 bjsC306 (1 / 100000) 500 * S ≤ (2000000 : ℝ) := h₃
    have h₇ : bjsTau306 bjsC306 (1 / 100000) 500 ≤ (2000000 : ℝ) / S := by
      calc
        bjsTau306 bjsC306 (1 / 100000) 500 = (bjsTau306 bjsC306 (1 / 100000) 500 * S) / S := by field_simp [h₅.ne'] <;> ring_nf
        _ ≤ (2000000 : ℝ) / S := by gcongr <;> norm_num
    exact h₇
  have h₅ : (2000000 : ℝ) / S = (2e-12 : ℝ) := by norm_num [S]
  rw [h₅] at h₄
  exact h₄

theorem c_eq_s77o (n : ℕ) (hn : 501 ≤ n) : bjsC306 n = 0.9607 := by
  unfold bjsC306
  repeat rw [if_neg (by omega)]

theorem c500_s77o : bjsC306 500 = 0.73 := by
  unfold bjsC306
  iterate 19 rw [if_neg (by norm_num)]
  rw [if_pos (by norm_num)]

theorem c_le_s77o (n : ℕ) (hn : 500 ≤ n) : 0 < bjsC306 n ∧ bjsC306 n ≤ 0.9607 := by
  rcases Nat.eq_or_lt_of_le hn with h | h
  · subst h; rw [c500_s77o]; norm_num
  · rw [c_eq_s77o n h]; norm_num

theorem xi_bd_s77o {γ κ cp cc t q : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 3.7) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 0.9607) (hcp0 : 0 ≤ cp) (hcp : cp ≤ q) (hcc0 : 0 ≤ cc) (hcc : cc ≤ q)
    (ht : 0 < t) : t * bjsXi306 γ κ (1 / 100000) cp cc t ≤ 0.961 * t + 11 * q := by
  rw [mulXi_s77 _ _ _ _ _ _ ht]
  nlinarith [mul_le_mul hγ hcp hcp0 (by norm_num : (0:ℝ) ≤ 3.7), mul_nonneg hγ0 hcp0]

theorem til_bd_s77o {cp cc t q : ℝ} (hcp0 : 0 ≤ cp) (hcp : cp ≤ q) (hcc0 : 0 ≤ cc)
    (hcc : cc ≤ q) (ht : 0 < t) :
    t * (0.9214 + (5 + 4 * (1 / 100000 : ℝ)) * (1 / 100000) + 6 * (1 + 1 / 100000) * cp / t
      + 2 * (2 + 1 / 100000) * cc / t) ≤ 0.961 * t + 11 * q := by
  rw [mulTil_s77 _ _ _ _ ht]
  nlinarith

theorem tau_pos_s77o (n : ℕ) (hn : 1 ≤ n) : 0 < bjsTau306 bjsC306 (1 / 100000) n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (tau_mono_gen_s77 bjsC306 bjsC306_pos _ _ (by norm_num) le_rfl k).1

theorem tau_step_s77o (k : ℕ) (hk : 499 ≤ k) :
    bjsTau306 bjsC306 (1 / 100000) (k + 2) ≤
      0.961 * bjsTau306 bjsC306 (1 / 100000) (k + 1) + 11 * 0.9607 ^ k := by
  have hpos := tau_pos_s77o (k + 1) (by omega)
  obtain ⟨hc1p, hc1⟩ := c_le_s77o (k + 1) (by omega)
  have hc2 := c_eq_s77o (k + 2) (by omega)
  have hcp0 : 0 ≤ bjsC306 (k + 1) ^ k := (pow_pos hc1p _).le
  have hcp : bjsC306 (k + 1) ^ k ≤ 0.9607 ^ k := pow_le_pow_left₀ hc1p.le hc1 _
  have hcc0 : 0 ≤ bjsC306 (k + 2) ^ (k + 1) := by rw [hc2]; positivity
  have hcc : bjsC306 (k + 2) ^ (k + 1) ≤ 0.9607 ^ k := by
    rw [hc2]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have he := Real.exp_one_lt_d9
  have hg : 4 * exp 1 / 3 ≤ 3.7 := by linarith
  have h08 : exp 0.8 ≤ 3.7 := by
    have := Real.exp_le_exp.2 (show (0.8:ℝ) ≤ 1 by norm_num); linarith
  have h06 : exp 0.6 ≤ 3.7 := by
    have := Real.exp_le_exp.2 (show (0.6:ℝ) ≤ 1 by norm_num); linarith
  have h04 : exp 0.4 ≤ 3.7 := by
    have := Real.exp_le_exp.2 (show (0.4:ℝ) ≤ 1 by norm_num); linarith
  have h02 : exp 0.2 ≤ 3.7 := by
    have := Real.exp_le_exp.2 (show (0.2:ℝ) ≤ 1 by norm_num); linarith
  have e1 : 0 ≤ exp 0.2 := (exp_pos _).le
  have e2 : 0 ≤ exp 0.4 := (exp_pos _).le
  have e3 : 0 ≤ exp 0.6 := (exp_pos _).le
  have e4 : 0 ≤ exp 0.8 := (exp_pos _).le
  have e5 : 0 ≤ 4 * exp 1 / 3 := by positivity
  simp only [bjsTau306]
  set t := bjsTau306 bjsC306 (1 / 100000) (k + 1)
  split_ifs with hev
  · rw [mul_max_of_nonneg _ _ hpos.le, mul_max_of_nonneg _ _ hpos.le,
      mul_max_of_nonneg _ _ hpos.le, mul_max_of_nonneg _ _ hpos.le,
      mul_max_of_nonneg _ _ hpos.le]
    refine max_le (max_le (max_le ?_ ?_) (max_le ?_ ?_)) (max_le ?_ ?_)
    · exact xi_bd_s77o zero_le_one (by norm_num) (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
    · exact xi_bd_s77o e1 h02 (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
    · exact xi_bd_s77o e2 h04 (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
    · exact xi_bd_s77o e3 h06 (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
    · exact xi_bd_s77o e4 h08 (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
    · exact xi_bd_s77o e5 hg (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
  · rw [mul_max_of_nonneg _ _ hpos.le]
    exact max_le (xi_bd_s77o e5 hg (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos)
      (til_bd_s77o hcp0 hcp hcc0 hcc hpos)

theorem pow499_s77o : (0.9607 : ℝ) ^ 499 ≤ 1e-8 := by
  have h83 : (0.9607 : ℝ) ^ 83 ≤ 0.04 := by norm_num
  have : ∀ x : ℝ, x ^ 499 = (x ^ 83) ^ 6 * x := fun x => by
    rw [← pow_mul, ← pow_succ]
  rw [this]
  have h6 : ((0.9607 : ℝ) ^ 83) ^ 6 ≤ 0.04 ^ 6 := pow_le_pow_left₀ (by positivity) h83 6
  nlinarith

theorem tau_geom_s77o (h500 : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12) (m : ℕ) :
    bjsTau306 bjsC306 (1 / 100000) (500 + m) ≤ 1e-3 * 0.97 ^ m := by
  induction m with
  | zero => simp only [add_zero, pow_zero]; linarith
  | succ m ih =>
    have hs := tau_step_s77o (499 + m) (by omega)
    have e1 : 499 + m + 2 = 500 + (m + 1) := by omega
    have e2 : 499 + m + 1 = 500 + m := by omega
    rw [e1, e2] at hs
    have hq : (0.9607 : ℝ) ^ (499 + m) ≤ 1e-8 * 0.97 ^ m := by
      rw [pow_add]
      exact mul_le_mul pow499_s77o (pow_le_pow_left₀ (by norm_num) (by norm_num) m)
        (by positivity) (by norm_num)
    have hp : (0:ℝ) ≤ 0.97 ^ m := by positivity
    rw [pow_succ]
    nlinarith

theorem tau_tail_sum_s77o (h500 : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 500 N, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.04 := by
  have hb : ∀ n ∈ Finset.Ioc 500 N, bjsTau306 bjsC306 (1 / 100000) n ≤
      1e-3 * (0.97 : ℝ) ^ (n - 500) := by
    intro n hn
    have := tau_geom_s77o h500 (n - 500)
    rwa [show 500 + (n - 500) = n by simp at hn; omega] at this
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.mul_sum]
  have hinj : Set.InjOn (fun n : ℕ => n - 500) (Finset.Ioc 500 N : Set ℕ) := by
    intro a ha b hb hab; simp at ha hb hab; omega
  rw [← Finset.sum_image (f := fun i => (0.97 : ℝ) ^ i) hinj]
  have hsum : Summable (fun i : ℕ => (0.97 : ℝ) ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h1 := hsum.sum_le_tsum ((Finset.Ioc 500 N).image (fun n => n - 500))
    (fun i _ => by positivity)
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h1
  have : (1 - (0.97 : ℝ))⁻¹ ≤ 34 := by norm_num
  nlinarith

theorem tau_filter_le_s77o (h500 : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12) (N : ℕ)
    (p : ℕ → Prop) [DecidablePred p] :
    ∑ n ∈ (Finset.Ioc 500 N).filter p, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.04 := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    (tau_tail_sum_s77o h500 N)
  intro n hn _
  exact (tau_pos_s77o n (by simp at hn; omega)).le

theorem tau_odd_tail_of500_s77 (h500 : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12) (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.49 :=
  (tau_filter_le_s77o h500 N Odd).trans (by norm_num)

theorem tau_even_tail_of500_s77 (h500 : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12) (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.16 :=
  (tau_filter_le_s77o h500 N Even).trans (by norm_num)

/-- Twin of tau_odd_tail1122c, statement verbatim, from the LEAF tau500_value1122c. -/
theorem tau_odd_tail_twin1122c (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.49 :=
  tau_odd_tail_of500_s77 tau500_value1122c N

/-- Twin of tau_even_tail1122c, statement verbatim, from the LEAF tau500_value1122c. -/
theorem tau_even_tail_twin1122c (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.16 :=
  tau_even_tail_of500_s77 tau500_value1122c N

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.tau_odd_tail_of500_s77
#print axioms LeanLab.Cai2002.tau_even_tail_of500_s77
#print axioms LeanLab.Cai2002.tau_odd_tail_twin1122c
