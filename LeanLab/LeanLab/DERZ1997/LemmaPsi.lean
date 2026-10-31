/-
P0011, the intermediate lemma from the ψ form of Schoenfeld's bound, unit U-5466,
cloud session 20261019T1116Z-cloud23.

P0011 page 101 quotes Schoenfeld (6.1) for Θ:
`|Θ(n) - n| < √n (log n - 2) log n / (8π)` for `n ≥ 2.3 · 10^9`. Lee and Nosal,
arXiv 2312.05628 display (1.1), give this shape for ψ. The Schoenfeld paper could not be
read from the cloud, NEEDS_COPY INPUT Schoenfeld1976. This file proves the printed lemma from
the ψ form, so the printed constant `1.615 · 10^12` stands whichever reading is right:
* `psi_diff_le`: if no prime lies in `(p, n]` beyond those that `θ` sees, the prime powers
  add at most `θ(√n) - θ(√p) + 4.2 · 10^8` to `ψ(n) - ψ(p)`, from
  `ψ = θ + Σ_{k=2}^{67} θ(x^{1/k})` and `θ(t) ≤ t log 4`;
* `derz_lemma_of_schoenfeldPsi`, the gap is at most `1.61485 · 10^12 < 1.615 · 10^12`.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.DERZ1997.Lemma

namespace LeanLab.DERZ1997
open Real Chebyshev

/-- Schoenfeld's bound in the ψ form, `|ψ(x) - x| < √x (log x - 2) log x / (8π)` for
`x ≥ 2.3 · 10^9`, as Lee and Nosal attribute it. CITED, not proved here. -/
def SchoenfeldPsi61 : Prop :=
  ∀ x : ℝ, 23 * 10 ^ 8 ≤ x → |ψ x - x| < √x * (Real.log x - 2) * Real.log x / (8 * π)

theorem floor_log_le_67 {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 10 ^ 20) :
    ⌊Real.log x / Real.log 2⌋₊ ≤ 67 := by
  have hl := Real.log_le_log (by linarith) h2
  have hl2 := log_1e20_lt
  have h2l := Real.log_two_gt_d9
  apply Nat.floor_le_of_le
  rw [div_le_iff₀ (by linarith)]
  have hlx : Real.log x ≤ 46.0522 := hl.trans hl2.le
  push_cast; nlinarith

theorem log_four_lt : Real.log 4 < 1.3863 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have := Real.log_two_lt_d9; push_cast; linarith

/-- `x^{1/k} ≤ 4.65 · 10^6` for `3 ≤ k` and `1 ≤ x ≤ 10^20`. -/
theorem root_le {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 10 ^ 20) {k : ℕ} (hk : 3 ≤ k) :
    x ^ ((1 : ℝ) / k) ≤ 4.65e6 := by
  have hx0 : 0 < x := by linarith
  have e : x ^ ((1 : ℝ) / k) ≤ x ^ ((1 : ℝ) / 3) := by
    apply Real.rpow_le_rpow_of_exponent_le h1
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine e.trans ?_
  by_contra h
  push_neg at h
  have h3 : (4.65e6 : ℝ) ^ 3 < (x ^ ((1 : ℝ) / 3)) ^ 3 :=
    pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [← Real.rpow_natCast (x ^ _), ← Real.rpow_mul hx0.le] at h3
  norm_num at h3
  linarith

/-- `ψ(x) - θ(x) ≤ θ(√x) + 4.2 · 10^8` for `2 ≤ x ≤ 10^20`. -/
theorem psi_sub_theta_upper {x : ℝ} (h1 : 2 ≤ x) (h2 : x ≤ 10 ^ 20) :
    ψ x - θ x ≤ θ (√x) + 4.2e8 := by
  rw [psi_eq_theta_add_sum_theta' h1 (floor_log_le_67 (by linarith) h2)]
  have hsplit : (Finset.Icc 2 67 : Finset ℕ) = insert 2 (Finset.Icc 3 67) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hrest : ∑ n ∈ (Finset.Icc 3 67 : Finset ℕ), θ (x ^ ((1 : ℝ) / (n : ℝ))) ≤ 65 * (1.3863 * 4.65e6) := by
    have hb : ∀ n ∈ (Finset.Icc 3 67 : Finset ℕ), θ (x ^ ((1 : ℝ) / (n : ℝ))) ≤ 1.3863 * 4.65e6 := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hr := root_le (by linarith) h2 hn.1
      have hr0 : 0 ≤ x ^ ((1 : ℝ) / n) := Real.rpow_nonneg (by linarith) _
      have := theta_le_log4_mul_x hr0
      have := log_four_lt
      nlinarith
    calc ∑ n ∈ (Finset.Icc 3 67 : Finset ℕ), θ (x ^ ((1 : ℝ) / (n : ℝ)))
        ≤ ∑ n ∈ (Finset.Icc 3 67 : Finset ℕ), (1.3863 * 4.65e6 : ℝ) := Finset.sum_le_sum hb
      _ = 65 * (1.3863 * 4.65e6) := by simp
  have hsq : x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) = √x := by
    rw [Real.sqrt_eq_rpow]; norm_num
  rw [hsq]
  norm_num at hrest ⊢
  linarith

/-- `ψ(x) - θ(x) ≥ θ(√x)` for `x ≥ 4`. -/
theorem psi_sub_theta_lower {x : ℝ} (h1 : 4 ≤ x) (h2 : x ≤ 10 ^ 20) :
    θ (√x) ≤ ψ x - θ x := by
  rw [psi_eq_theta_add_sum_theta' (by linarith) (floor_log_le_67 (by linarith) h2)]
  have hsplit : (Finset.Icc 2 67 : Finset ℕ) = insert 2 (Finset.Icc 3 67) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hsq : x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) = √x := by
    rw [Real.sqrt_eq_rpow]; norm_num
  rw [hsq]
  have : 0 ≤ ∑ n ∈ (Finset.Icc 3 67 : Finset ℕ), θ (x ^ ((1 : ℝ) / (n : ℝ))) :=
    Finset.sum_nonneg fun _ _ => theta_nonneg _
  linarith

/-- `θ(√y) - θ(√p) ≤ (√y - √p + 1) log √y` for `1 ≤ p ≤ y`. -/
theorem theta_sqrt_diff {p y : ℝ} (hp : 1 ≤ p) (hpy : p ≤ y) :
    θ (√y) - θ (√p) ≤ (√y - √p + 1) * Real.log (√y) := by
  have hsp : 1 ≤ √p := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hsy : √p ≤ √y := Real.sqrt_le_sqrt hpy
  set a := ⌊√p⌋₊ with ha
  set b := ⌊√y⌋₊ with hb
  have hab : a ≤ b := Nat.floor_le_floor hsy
  rw [theta_eq_theta_coe_floor (√y), theta_eq_theta_coe_floor (√p), ← ha, ← hb,
    theta_nat_add hab]
  have hbR : (b : ℝ) ≤ √y := Nat.floor_le (by linarith)
  have haR : √p - 1 < (a : ℝ) := Nat.sub_one_lt_floor _
  have hlogb : ∀ k ∈ Finset.Ioc a b, (if k.Prime then Real.log k else 0) ≤ Real.log (√y) := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    split_ifs with hkp
    · have : (k : ℝ) ≤ b := by exact_mod_cast hk.2
      exact Real.log_le_log (by exact_mod_cast hkp.pos) (by linarith)
    · exact Real.log_nonneg (by linarith)
  have hsum := Finset.sum_le_sum hlogb
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul] at hsum
  have hcard : ((b - a : ℕ) : ℝ) ≤ √y - √p + 1 := by
    rw [Nat.cast_sub hab]; linarith
  have hl0 : 0 ≤ Real.log (√y) := Real.log_nonneg (by linarith)
  have := mul_le_mul_of_nonneg_right hcard hl0
  linarith

/-- **The P0011 intermediate lemma from the ψ form of Schoenfeld's bound**, with the
printed constant `1.615 · 10^12`. CONDITIONAL ON `SchoenfeldPsi61`. -/
theorem derz_lemma_of_schoenfeldPsi (h : SchoenfeldPsi61) :
    ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9 := by
  intro n h6 hn
  rcases Nat.lt_or_ge n (1615 * 10 ^ 9 + 4) with hsmall | hbig
  · rcases Nat.lt_or_ge n 7 with h7 | h7
    · exact ⟨2, Nat.prime_two, by omega, by omega⟩
    · exact ⟨3, Nat.prime_three, by omega, by omega⟩
  set m := n - 4 with hm
  obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (m / 2) (by omega)
  have hqm : q ≤ m := by omega
  set p := Nat.findGreatest Nat.Prime m with hpdef
  have hqp : q ≤ p := Nat.le_findGreatest hqm hq
  have hp : p.Prime := Nat.findGreatest_spec hqm hq
  have hpm : p ≤ m := Nat.findGreatest_le m
  have hnp : ∀ k, p < k → k ≤ m → ¬ k.Prime := fun k h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  have hp11 : 5 * 10 ^ 11 ≤ p := by omega
  refine ⟨p, hp, by omega, ?_⟩
  have hθg := theta_gap hpm (by omega) hnp
  rw [show m + 4 = n by omega] at hθg
  have hpR : (5 * 10 ^ 11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp11
  have hnR : (n : ℝ) ≤ 10 ^ 20 := by exact_mod_cast hn
  have hpn : (p : ℝ) ≤ n := by exact_mod_cast (by omega : p ≤ n)
  -- Schoenfeld at n and p, uniformly
  have hu : ∀ x : ℝ, 10 ^ 11 ≤ x → x ≤ 10 ^ 20 → |ψ x - x| ≤ 807195 * 10 ^ 6 := by
    intro x h1 h2
    refine (h x (by linarith)).le.trans ?_
    have hL := Real.log_le_log (by linarith) h2
    have hL2 := log_1e20_lt
    have hg := log_ge_two (x := x) (by linarith)
    have hs := sqrt_le_1e10 h2
    have hpi := Real.pi_gt_d6
    rw [div_le_iff₀ (by positivity)]
    have hlx : Real.log x ≤ 46.0522 := hL.trans hL2.le
    have a : (Real.log x - 2) * Real.log x ≤ (46.0522 - 2) * 46.0522 :=
      mul_le_mul (by linarith) hlx (by linarith) (by norm_num)
    have hprod : √x * (Real.log x - 2) * Real.log x ≤ 10 ^ 10 * ((46.0522 - 2) * 46.0522) := by
      rw [mul_assoc]; exact mul_le_mul hs a (by nlinarith) (by norm_num)
    nlinarith
  have h1 := hu n (by linarith) hnR
  have h2 := hu p (by linarith) (by linarith)
  -- ψ(n) - ψ(p) ≤ 2 log n + 4.2e8 + (√n - √p + 1) log √n
  have hd1 := psi_sub_theta_upper (x := n) (by linarith) hnR
  have hd2 := psi_sub_theta_lower (x := p) (by linarith) (by linarith)
  have hd3 := theta_sqrt_diff (p := p) (y := n) (by linarith) hpn
  have hlogn : Real.log n ≤ 46.0522 := (Real.log_le_log (by linarith) hnR).trans log_1e20_lt.le
  have hlogsq : Real.log (√(n : ℝ)) ≤ 23.03 := by
    rw [Real.log_sqrt (by linarith)]; linarith
  have hlogsq0 : 0 ≤ Real.log (√(n : ℝ)) := Real.log_nonneg (by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith)
  -- √n - √p ≤ (n - p) / (2 √p) ≤ (n - p) / 1.4e6
  have hsp : (7 * 10 ^ 5 : ℝ) ≤ √(p : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hsn : √(p : ℝ) ≤ √(n : ℝ) := Real.sqrt_le_sqrt hpn
  have hroot : (√(n : ℝ) - √(p : ℝ)) * (2 * (7 * 10 ^ 5)) ≤ (n : ℝ) - p := by
    have e : (√(n : ℝ) - √(p : ℝ)) * (√(n : ℝ) + √(p : ℝ)) = (n : ℝ) - p := by
      have a := Real.sq_sqrt (show (0 : ℝ) ≤ n by linarith)
      have b := Real.sq_sqrt (show (0 : ℝ) ≤ p by linarith)
      nlinarith
    have : (2 * (7 * 10 ^ 5) : ℝ) ≤ √(n : ℝ) + √(p : ℝ) := by linarith
    nlinarith
  have hD : (√(n : ℝ) - √(p : ℝ) + 1) * Real.log (√(n : ℝ))
      ≤ ((n : ℝ) - p) / (14 * 10 ^ 5) * 23.03 + 23.03 := by
    have hd0 : 0 ≤ √(n : ℝ) - √(p : ℝ) := by linarith
    have : √(n : ℝ) - √(p : ℝ) ≤ ((n : ℝ) - p) / (14 * 10 ^ 5) := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith
  have hreal : (n : ℝ) - p < 1615 * 10 ^ 9 := by
    have a1 := (abs_le.mp h1).1
    have a2 := (abs_le.mp h2).2
    have hθ0 := theta_nonneg (√(p : ℝ))
    nlinarith
  have : ((n - p : ℕ) : ℝ) < 1615 * 10 ^ 9 := by
    rw [Nat.cast_sub (by omega)]; exact hreal
  exact_mod_cast this.le

/-- The main theorem from Zinoviev, the `10^13` even check and the ψ form of Schoenfeld. -/
theorem derz_main_of_psi
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hS : GRH → SchoenfeldPsi61) (hD : EvenGoldbachUpTo (10 ^ 13)) :
    GRH → TernaryGoldbach :=
  derz_main_of_gap (1615 * 10 ^ 9) (by norm_num) hZ
    (fun hG => derz_lemma_of_schoenfeldPsi (hS hG)) hD

end LeanLab.DERZ1997
