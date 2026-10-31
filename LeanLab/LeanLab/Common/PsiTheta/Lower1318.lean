/-
# The lower half of the cited Schoenfeld bound

Unit U-1318, PC run 20261021T0103Z-19411, track T1, ladder rung 5b shared input.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel. Known mathematics.

`Discharge1315.lean` showed the cited `Dudek2014.Section22.Schoenfeld` is exactly as strong as
`SchoenfeldLower`: `0.98 √y < ψ(y) - θ(y)` for `y ≥ 121`. Here:
* `lowChk_table`: one `decide +kernel` table, `8^(n+1) ≤ E(n) · lcm(1..n) · 3^(n+1)` for
  `11 ≤ n < 10^4`, where `E(n) = lcm(1..c(n))`, `c(n) ∈ {4, 5, 7, 9}`, `c(n)^3 ≤ n^2`;
* `psi_sub_theta_gt_small`: hence, by Costa Pereira `ψ(y) - θ(y) ≥ ψ(√y) + ψ(y^{1/3})`, the
  lower half on `121 ≤ y < 10^8`, unconditional;
* `RSThetaLower`: the cited input, `θ(t) ≥ 0.98 t` for `t ≥ 7481`, Rosser and Schoenfeld 1962;
* `schoenfeld_lower_of_rs`, `schoenfeld_of_rs`: `SchoenfeldLower` and `Schoenfeld` CONDITIONAL
  ON `RSThetaLower` only;
* `rs_theta_lower_at_10000`: the vacuity instance, `θ(10^4) ≥ 9800`, proved.
Goldbach is open.
-/
import LeanLab.Common.PsiTheta.Discharge1315

namespace LeanLab.Common.PsiTheta

open Real Chebyshev
open LeanLab.Dudek2014.Section22

/-! ### The kernel table -/

/-- The cube root floor used at row `n`: `c(n)^3 ≤ n^2` for `n ≥ 11`. -/
def cRoot (n : ℕ) : ℕ := if n < 12 then 4 else if n < 19 then 5 else if n < 27 then 7 else 9

/-- `E(n) = lcm(1..c(n))`, as a literal. -/
def lowE (n : ℕ) : ℕ := if n < 12 then 12 else if n < 19 then 60 else if n < 27 then 420 else 2520

lemma lowE_eq (n : ℕ) : lowE n = Nat.lcmUpto (cRoot n) := by
  unfold lowE cRoot
  split_ifs <;> decide +kernel

lemma cRoot_cube {n : ℕ} (hn : 11 ≤ n) : cRoot n ^ 3 ≤ n ^ 2 := by
  unfold cRoot
  split_ifs with h1 h2 h3
  · calc 4 ^ 3 ≤ 11 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  · calc 5 ^ 3 ≤ 12 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
  · calc 7 ^ 3 ≤ 19 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
  · calc 9 ^ 3 ≤ 27 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2

/-- Row `n` state: `L = lcm(1..n)`, `A = 3^(n+1)`, `B = 8^(n+1)`; checks `k` rows. -/
def lowChk : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _ => true
  | k + 1, n, L, A, B =>
    Nat.ble B (lowE n * L * A) && lowChk k (n + 1) (Nat.lcm L (n + 1)) (3 * A) (8 * B)

lemma lowChk_sound : ∀ (k n : ℕ),
    lowChk k n (Nat.lcmUpto n) (3 ^ (n + 1)) (8 ^ (n + 1)) = true →
    ∀ m, n ≤ m → m < n + k → 8 ^ (m + 1) ≤ lowE m * Nat.lcmUpto m * 3 ^ (m + 1) := by
  intro k
  induction k with
  | zero => intro n _ m h1 h2; omega
  | succ k ih =>
    intro n h m h1 h2
    simp only [lowChk, Bool.and_eq_true, Nat.ble_eq] at h
    rw [← lcmUpto_succ, show 3 * 3 ^ (n + 1) = 3 ^ (n + 1 + 1) by ring,
      show 8 * 8 ^ (n + 1) = 8 ^ (n + 1 + 1) by ring] at h
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · subst e; exact h.1
    · exact ih (n + 1) h.2 m e (by omega)

/-- `lcm(1..11) = 27720` in the table's start state. -/
lemma lowChk_table : lowChk 9989 11 27720 531441 68719476736 = true := by decide +kernel

/-- **`8^(n+1) ≤ E(n) lcm(1..n) 3^(n+1)` for `11 ≤ n < 10^4`.** -/
theorem lcm_lower_table {n : ℕ} (h1 : 11 ≤ n) (h2 : n < 10000) :
    8 ^ (n + 1) ≤ lowE n * Nat.lcmUpto n * 3 ^ (n + 1) := by
  have h := lowChk_table
  rw [← lcmUpto_11, show (531441 : ℕ) = 3 ^ (11 + 1) by norm_num,
    show (68719476736 : ℕ) = 8 ^ (11 + 1) by norm_num] at h
  exact lowChk_sound 9989 11 h n h1 (by omega)

/-! ### Real analysis -/

/-- `0.98 < log 8 - log 3`, from `exp 0.98 ≤ e / 1.02 < 8/3`. -/
lemma log83_gt : (0.98 : ℝ) < log 8 - log 3 := by
  rw [← Real.log_div (by norm_num) (by norm_num), Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 : (1.02 : ℝ) ≤ exp 0.02 := by
    have := Real.add_one_le_exp (0.02 : ℝ); linarith
  have : exp (1 : ℝ) = exp 0.98 * exp 0.02 := by rw [← Real.exp_add]; norm_num
  have hp := Real.exp_pos 0.98
  nlinarith

/-- If `c^3 ≤ y` then `log lcm(1..c) = ψ(c) ≤ ψ(y^{1/3})`. -/
lemma log_lcm_le_psi_cbrt {c : ℕ} {y : ℝ} (_hy : 0 ≤ y) (h : (c : ℝ) ^ 3 ≤ y) :
    log (Nat.lcmUpto c : ℝ) ≤ ψ (y ^ (3 : ℝ)⁻¹) := by
  rw [← psi_eq_log_lcmUpto]
  apply psi_mono
  have hc : (c : ℝ) = ((c : ℝ) ^ (3 : ℕ)) ^ (3 : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  rw [hc]
  exact Real.rpow_le_rpow (by positivity) h (by norm_num)

/-- **Lower half of the cited Schoenfeld bound on `121 ≤ y < 10^8`, unconditional.** -/
theorem psi_sub_theta_gt_small {y : ℝ} (hy : 121 ≤ y) (hy8 : y < 10 ^ 8) :
    0.98 * √y < ψ y - θ y := by
  have hy0 : 0 ≤ y := by linarith
  have hCP := psi_sub_theta_ge_psi_add_psi_add_psi hy0
  have e2 : y ^ (2 : ℝ)⁻¹ = √y := by rw [Real.sqrt_eq_rpow]; norm_num
  rw [e2] at hCP
  have h7 := psi_nonneg (y ^ (7 : ℝ)⁻¹)
  set t := √y with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg y
  have ht2 : t ^ 2 = y := Real.sq_sqrt hy0
  set n := ⌊t⌋₊ with hn
  have hnt : (n : ℝ) ≤ t := Nat.floor_le ht0
  have hnt' : t < n + 1 := Nat.lt_floor_add_one t
  have ht11 : 11 ≤ t := by nlinarith
  have ht4 : t < 10000 := by nlinarith
  have hn11 : 11 ≤ n := by
    have : (10 : ℝ) < n := by linarith
    have : 10 < n := by exact_mod_cast this
    omega
  have hn4 : n < 10000 := by
    have : (n : ℝ) < 10000 := by linarith
    exact_mod_cast this
  -- the table row
  have hT := lcm_lower_table hn11 hn4
  rw [lowE_eq] at hT
  have hT' : ((8 : ℝ)) ^ (n + 1) ≤ (Nat.lcmUpto (cRoot n) : ℝ) * Nat.lcmUpto n * 3 ^ (n + 1) := by
    exact_mod_cast hT
  have hE0 : (0 : ℝ) < Nat.lcmUpto (cRoot n) := by exact_mod_cast Nat.lcmUpto_pos _
  have hL0 : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos _
  have hlog := Real.log_le_log (by positivity) hT'
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hlog
  -- ψ(t) = log lcm(1..n)
  have hpsi : ψ t = log (Nat.lcmUpto n) := by rw [psi_eq_psi_coe_floor, psi_eq_log_lcmUpto]
  -- ψ(y^{1/3}) ≥ log lcm(1..c(n))
  have hc3 : ((cRoot n : ℕ) : ℝ) ^ 3 ≤ y := by
    have := cRoot_cube hn11
    have h' : ((cRoot n : ℕ) : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 := by exact_mod_cast this
    nlinarith
  have hcb := log_lcm_le_psi_cbrt hy0 hc3
  have h83 := log83_gt
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  push_cast at hlog
  nlinarith

/-! ### The cited θ bound and the conditional result -/

/-- **Rosser and Schoenfeld 1962, cited.** `θ(t) ≥ 0.98 t` for every `t ≥ 7481`.
Source: J. B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers,
Illinois J. Math. 6 (1962) 64-94, the entry `θ(x) > (1 - 0.02) x` for `x ≥ 7481`, as tabulated
in Broadbent, Kadiri, Lumley, Ng, Wilk, Sharper bounds for the Chebyshev function θ(x),
arXiv 2002.11068, Table 1, row Rosser and Schoenfeld 1962. The paper's bound is strict; the
Prop uses `≤`, which is weaker. -/
def RSThetaLower : Prop :=
  ∀ t : ℝ, 7481 ≤ t → 0.98 * t ≤ θ t

/-- The lower half for `y ≥ 10^8`. CONDITIONAL ON `RSThetaLower`. -/
theorem psi_sub_theta_gt_large (hRS : RSThetaLower) {y : ℝ} (hy : 10 ^ 8 ≤ y) :
    0.98 * √y < ψ y - θ y := by
  have hy0 : 0 ≤ y := by linarith
  have hCP := psi_sub_theta_ge_psi_add_psi_add_psi hy0
  have e2 : y ^ (2 : ℝ)⁻¹ = √y := by rw [Real.sqrt_eq_rpow]; norm_num
  rw [e2] at hCP
  have h7 := psi_nonneg (y ^ (7 : ℝ)⁻¹)
  have ht0 : 0 ≤ √y := Real.sqrt_nonneg y
  have ht4 : 7481 ≤ √y := by
    rw [Real.le_sqrt (by norm_num) hy0]; linarith
  have hth := hRS _ ht4
  have htp := theta_le_psi √y
  have h2 : (2 : ℝ) ^ 3 ≤ y := by linarith
  have hcb := log_lcm_le_psi_cbrt (c := 2) hy0 (by exact_mod_cast h2)
  have hl2 : (0 : ℝ) < log (Nat.lcmUpto 2 : ℝ) := by
    rw [show Nat.lcmUpto 2 = 2 by decide +kernel]; push_cast
    exact Real.log_pos (by norm_num)
  linarith

/-- **`SchoenfeldLower` from one classical θ bound.** CONDITIONAL ON `RSThetaLower`. -/
theorem schoenfeld_lower_of_rs (hRS : RSThetaLower) : SchoenfeldLower := by
  intro y hy
  rw [psiF_eq_psi, thetaF_eq_theta]
  rcases lt_or_ge y (10 ^ 8) with h | h
  · exact psi_sub_theta_gt_small hy h
  · exact psi_sub_theta_gt_large hRS h

/-- **The cited `Dudek2014.Section22.Schoenfeld` from Rosser and Schoenfeld 1962 alone.**
CONDITIONAL ON `RSThetaLower`. -/
theorem schoenfeld_of_rs (hRS : RSThetaLower) : Schoenfeld :=
  schoenfeld_of_lower (schoenfeld_lower_of_rs hRS)

/-! ### Vacuity: `RSThetaLower`'s inequality at `t = 10^4` -/

/-- Iterated lcm: `lcmFin k n (lcm(1..n)) = lcm(1..n+k)`. -/
def lcmFin : ℕ → ℕ → ℕ → ℕ
  | 0, _, L => L
  | k + 1, n, L => lcmFin k (n + 1) (Nat.lcm L (n + 1))

lemma lcmFin_eq : ∀ k n, lcmFin k n (Nat.lcmUpto n) = Nat.lcmUpto (n + k) := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    simp only [lcmFin]
    rw [← lcmUpto_succ, ih (n + 1)]
    congr 1; omega

lemma lcm10000_chk : Nat.ble (8 ^ 10164) (lcmFin 10000 0 1 * 3 ^ 10164) = true := by
  decide +kernel

/-- **Vacuity instance: `0.98 · 10^4 ≤ θ(10^4)`.** Via `ψ(10^4) ≥ 10164 log(8/3)` from the
lcm, and `ψ - θ ≤ log 3 · (100 + 22 + 22)` by Costa Pereira. -/
theorem rs_theta_lower_at_10000 : 0.98 * (10000 : ℝ) ≤ θ 10000 := by
  have hchk := lcm10000_chk
  have hF := lcmFin_eq 10000 0
  rw [lcmUpto_zero, zero_add] at hF
  rw [Nat.ble_eq, hF] at hchk
  have hR : ((8 : ℝ)) ^ 10164 ≤ (Nat.lcmUpto 10000 : ℝ) * 3 ^ 10164 := by exact_mod_cast hchk
  have hL0 : (0 : ℝ) < Nat.lcmUpto 10000 := by exact_mod_cast Nat.lcmUpto_pos _
  have hlog := Real.log_le_log (by positivity) hR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  clear hR hchk hF
  have hpsi : ψ (10000 : ℝ) = log (Nat.lcmUpto 10000) := by
    have := psi_eq_log_lcmUpto 10000; push_cast at this; exact this
  have hCP := psi_sub_theta_le_psi_add_psi_add_psi (10000 : ℝ)
  have e2 : (10000 : ℝ) ^ (2 : ℝ)⁻¹ = 100 := by
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e3 : (10000 : ℝ) ^ (3 : ℝ)⁻¹ < 22 := by
    have h22 : (22 : ℝ) = ((22 : ℝ) ^ (3 : ℝ)) ^ (3 : ℝ)⁻¹ := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    rw [h22]
    apply Real.rpow_lt_rpow (by norm_num) _ (by norm_num)
    norm_num
  have e5 : (10000 : ℝ) ^ (5 : ℝ)⁻¹ ≤ (10000 : ℝ) ^ (3 : ℝ)⁻¹ :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have p2 := psi_le_log3_mul (t := 100) (by norm_num) (by norm_num)
  have p3 := psi_le_log3_mul (t := (10000 : ℝ) ^ (3 : ℝ)⁻¹) (by positivity) (by linarith)
  have p5 := psi_le_log3_mul (t := (10000 : ℝ) ^ (5 : ℝ)⁻¹) (by positivity) (by linarith)
  rw [e2] at hCP
  have hl := log_three_lt
  have hl0 : 0 ≤ log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have h83 := log83_gt
  push_cast at hlog
  have hm : (10164 : ℝ) * 0.98 < 10164 * (log 8 - log 3) :=
    mul_lt_mul_of_pos_left h83 (by norm_num)
  set u := (10000 : ℝ) ^ (3 : ℝ)⁻¹ with hu
  set v := (10000 : ℝ) ^ (5 : ℝ)⁻¹ with hv
  have hv0 : 0 ≤ v := by positivity
  have q2 : log 3 * 100 ≤ 1.11 * 100 := by nlinarith
  have q3 : log 3 * u ≤ 1.11 * 22 := by nlinarith
  have q5 : log 3 * v ≤ 1.11 * 22 := by nlinarith
  have htp := theta_le_psi (10000 : ℝ)
  linarith

end LeanLab.Common.PsiTheta
