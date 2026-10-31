/-
P0022, Kaniecki 1995, the input `Const4` of Lemma5Kernel.lean, PROVED here.
PC run 20261021T1203Z-6472, unit U-1416, T1.

`Const4`: `K² ≤ 4`, `K = Σ_p log p/(√p (p - 1))`, p. 370; true value `K² ≈ 2.96346`.
Proof. `K ≤ 2`. Head `n ≤ 50`: the 15 prime terms bounded by certified rationals, with
`log p ≤ k log 2/128` when `p^128 ≤ 2^k` and `√p ≥ q` when `q² ≤ p`; head at most 1.4525002.
Tail `n ≥ 51`: `log p/(√p (p-1)) ≤ (51/50) Λ(n) w(n)`, `w(x) = 1/(x √x)`; summation by parts,
the lab's `sbp`, in two phases, `ψ(n) ≤ n log 3` for `n ≤ 299` and `ψ(n) ≤ 1.9 n` beyond, against
`w(x+1) ≤ F(x) - F(x+1)`, `F(x) = 2/√x`, with `ψ(50) ≥ 71 log 2` from `2^71 ≤ lcm(1..50)`.
Tail at most 0.4661 · 51/50. Total at most 1.93.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5LamSq
import LeanLab.Kaniecki1995.Lemma5KernelG

set_option exponentiation.threshold 2000

namespace LeanLab.Kaniecki1995.L5U1416

open Real Chebyshev Set
open scoped ArithmeticFunction.vonMangoldt

/-- the summand of `K451` -/
noncomputable def kt (n : ℕ) : ℝ := ‖L5.primeTerm (1 / 2 : ℂ) n‖

noncomputable def S (k : ℕ) : ℝ := ∑ n ∈ Finset.range k, kt n

theorem S_succ (k : ℕ) : S (k + 1) = S k + kt k := Finset.sum_range_succ _ _

theorem kt_nonneg (n : ℕ) : 0 ≤ kt n := norm_nonneg _

theorem hzero {n : ℕ} (h : ¬ n.Prime) : kt n ≤ 0 := by simp [kt, L5.primeTerm, h]

theorem hterm {p k : ℕ} {q b : ℝ} (hp : p.Prime) (hk : p ^ 128 ≤ 2 ^ k) (hq0 : 0 < q)
    (hq : q ^ 2 ≤ p) (hb : (k : ℝ) * 0.6931471808 / 128 ≤ b * (q * ((p : ℝ) - 1))) :
    kt p ≤ b := by
  unfold kt; rw [L5.norm_primeTerm_half hp]
  have hx2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs : q ≤ √(p : ℝ) := Real.le_sqrt_of_sq_le hq
  have hl := L5Lam.log_le_pow p k hk
  have hqp : 0 < q * ((p : ℝ) - 1) := mul_pos hq0 (by linarith)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) * 0.6931471808 / 128 := by positivity
  have hb0 : 0 ≤ b := by
    by_contra h; push_neg at h
    have := mul_neg_of_neg_of_pos h hqp; linarith
  rw [div_le_iff₀ (mul_pos (by linarith) (by linarith))]
  have : b * (q * ((p : ℝ) - 1)) ≤ b * (√(p : ℝ) * ((p : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (by linarith)) hb0
  linarith

theorem u0 : kt 0 ≤ 0 := hzero (by norm_num)

theorem u1 : kt 1 ≤ 0 := hzero (by norm_num)

theorem u2 : kt 2 ≤ 2450669 / 5000000 :=
  hterm (p := 2) (k := 128) (q := 7071 / 5000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u3 : kt 3 ≤ 634693 / 2000000 :=
  hterm (p := 3) (k := 203) (q := 433 / 250) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u4 : kt 4 ≤ 0 := hzero (by norm_num)

theorem u5 : kt 5 ≤ 225533 / 1250000 :=
  hterm (p := 5) (k := 298) (q := 559 / 250) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u6 : kt 6 ≤ 0 := hzero (by norm_num)

theorem u7 : kt 7 ≤ 1228079 / 10000000 :=
  hterm (p := 7) (k := 360) (q := 26457 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u8 : kt 8 ≤ 0 := hzero (by norm_num)

theorem u9 : kt 9 ≤ 0 := hzero (by norm_num)

theorem u10 : kt 10 ≤ 0 := hzero (by norm_num)

theorem u11 : kt 11 ≤ 723313 / 10000000 :=
  hterm (p := 11) (k := 443) (q := 16583 / 5000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u12 : kt 12 ≤ 0 := hzero (by norm_num)

theorem u13 : kt 13 ≤ 593263 / 10000000 :=
  hterm (p := 13) (k := 474) (q := 7211 / 2000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u14 : kt 14 ≤ 0 := hzero (by norm_num)

theorem u15 : kt 15 ≤ 0 := hzero (by norm_num)

theorem u16 : kt 16 ≤ 0 := hzero (by norm_num)

theorem u17 : kt 17 ≤ 215067 / 5000000 :=
  hterm (p := 17) (k := 524) (q := 41231 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u18 : kt 18 ≤ 0 := hzero (by norm_num)

theorem u19 : kt 19 ≤ 37547 / 1000000 :=
  hterm (p := 19) (k := 544) (q := 10897 / 2500) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u20 : kt 20 ≤ 0 := hzero (by norm_num)

theorem u21 : kt 21 ≤ 0 := hzero (by norm_num)

theorem u22 : kt 22 ≤ 0 := hzero (by norm_num)

theorem u23 : kt 23 ≤ 297687 / 10000000 :=
  hterm (p := 23) (k := 580) (q := 23979 / 5000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u24 : kt 24 ≤ 0 := hzero (by norm_num)

theorem u25 : kt 25 ≤ 0 := hzero (by norm_num)

theorem u26 : kt 26 ≤ 0 := hzero (by norm_num)

theorem u27 : kt 27 ≤ 0 := hzero (by norm_num)

theorem u28 : kt 28 ≤ 0 := hzero (by norm_num)

theorem u29 : kt 29 ≤ 111693 / 5000000 :=
  hterm (p := 29) (k := 622) (q := 53851 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u30 : kt 30 ≤ 0 := hzero (by norm_num)

theorem u31 : kt 31 ≤ 20587 / 1000000 :=
  hterm (p := 31) (k := 635) (q := 55677 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u32 : kt 32 ≤ 0 := hzero (by norm_num)

theorem u33 : kt 33 ≤ 0 := hzero (by norm_num)

theorem u34 : kt 34 ≤ 0 := hzero (by norm_num)

theorem u35 : kt 35 ≤ 0 := hzero (by norm_num)

theorem u36 : kt 36 ≤ 0 := hzero (by norm_num)

theorem u37 : kt 37 ≤ 164947 / 10000000 :=
  hterm (p := 37) (k := 667) (q := 60827 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u38 : kt 38 ≤ 0 := hzero (by norm_num)

theorem u39 : kt 39 ≤ 0 := hzero (by norm_num)

theorem u40 : kt 40 ≤ 0 := hzero (by norm_num)

theorem u41 : kt 41 ≤ 145041 / 10000000 :=
  hterm (p := 41) (k := 686) (q := 64031 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u42 : kt 42 ≤ 0 := hzero (by norm_num)

theorem u43 : kt 43 ≤ 68327 / 5000000 :=
  hterm (p := 43) (k := 695) (q := 32787 / 5000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u44 : kt 44 ≤ 0 := hzero (by norm_num)

theorem u45 : kt 45 ≤ 0 := hzero (by norm_num)

theorem u46 : kt 46 ≤ 0 := hzero (by norm_num)

theorem u47 : kt 47 ≤ 122091 / 10000000 :=
  hterm (p := 47) (k := 711) (q := 17139 / 2500) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem u48 : kt 48 ≤ 0 := hzero (by norm_num)

theorem u49 : kt 49 ≤ 0 := hzero (by norm_num)

theorem u50 : kt 50 ≤ 0 := hzero (by norm_num)

theorem s0 : S 0 ≤ 0 := by simp [S]

theorem s1 : S 1 ≤ 0 / 1 := by
  have h := S_succ 0
  linarith [s0, u0]

theorem s2 : S 2 ≤ 0 / 1 := by
  have h := S_succ 1
  linarith [s1, u1]

theorem s3 : S 3 ≤ 2450669 / 5000000 := by
  have h := S_succ 2
  linarith [s2, u2]

theorem s4 : S 4 ≤ 8074803 / 10000000 := by
  have h := S_succ 3
  linarith [s3, u3]

theorem s5 : S 5 ≤ 8074803 / 10000000 := by
  have h := S_succ 4
  linarith [s4, u4]

theorem s6 : S 6 ≤ 9879067 / 10000000 := by
  have h := S_succ 5
  linarith [s5, u5]

theorem s7 : S 7 ≤ 9879067 / 10000000 := by
  have h := S_succ 6
  linarith [s6, u6]

theorem s8 : S 8 ≤ 5553573 / 5000000 := by
  have h := S_succ 7
  linarith [s7, u7]

theorem s9 : S 9 ≤ 5553573 / 5000000 := by
  have h := S_succ 8
  linarith [s8, u8]

theorem s10 : S 10 ≤ 5553573 / 5000000 := by
  have h := S_succ 9
  linarith [s9, u9]

theorem s11 : S 11 ≤ 5553573 / 5000000 := by
  have h := S_succ 10
  linarith [s10, u10]

theorem s12 : S 12 ≤ 11830459 / 10000000 := by
  have h := S_succ 11
  linarith [s11, u11]

theorem s13 : S 13 ≤ 11830459 / 10000000 := by
  have h := S_succ 12
  linarith [s12, u12]

theorem s14 : S 14 ≤ 6211861 / 5000000 := by
  have h := S_succ 13
  linarith [s13, u13]

theorem s15 : S 15 ≤ 6211861 / 5000000 := by
  have h := S_succ 14
  linarith [s14, u14]

theorem s16 : S 16 ≤ 6211861 / 5000000 := by
  have h := S_succ 15
  linarith [s15, u15]

theorem s17 : S 17 ≤ 6211861 / 5000000 := by
  have h := S_succ 16
  linarith [s16, u16]

theorem s18 : S 18 ≤ 401683 / 312500 := by
  have h := S_succ 17
  linarith [s17, u17]

theorem s19 : S 19 ≤ 401683 / 312500 := by
  have h := S_succ 18
  linarith [s18, u18]

theorem s20 : S 20 ≤ 6614663 / 5000000 := by
  have h := S_succ 19
  linarith [s19, u19]

theorem s21 : S 21 ≤ 6614663 / 5000000 := by
  have h := S_succ 20
  linarith [s20, u20]

theorem s22 : S 22 ≤ 6614663 / 5000000 := by
  have h := S_succ 21
  linarith [s21, u21]

theorem s23 : S 23 ≤ 6614663 / 5000000 := by
  have h := S_succ 22
  linarith [s22, u22]

theorem s24 : S 24 ≤ 13527013 / 10000000 := by
  have h := S_succ 23
  linarith [s23, u23]

theorem s25 : S 25 ≤ 13527013 / 10000000 := by
  have h := S_succ 24
  linarith [s24, u24]

theorem s26 : S 26 ≤ 13527013 / 10000000 := by
  have h := S_succ 25
  linarith [s25, u25]

theorem s27 : S 27 ≤ 13527013 / 10000000 := by
  have h := S_succ 26
  linarith [s26, u26]

theorem s28 : S 28 ≤ 13527013 / 10000000 := by
  have h := S_succ 27
  linarith [s27, u27]

theorem s29 : S 29 ≤ 13527013 / 10000000 := by
  have h := S_succ 28
  linarith [s28, u28]

theorem s30 : S 30 ≤ 13750399 / 10000000 := by
  have h := S_succ 29
  linarith [s29, u29]

theorem s31 : S 31 ≤ 13750399 / 10000000 := by
  have h := S_succ 30
  linarith [s30, u30]

theorem s32 : S 32 ≤ 13956269 / 10000000 := by
  have h := S_succ 31
  linarith [s31, u31]

theorem s33 : S 33 ≤ 13956269 / 10000000 := by
  have h := S_succ 32
  linarith [s32, u32]

theorem s34 : S 34 ≤ 13956269 / 10000000 := by
  have h := S_succ 33
  linarith [s33, u33]

theorem s35 : S 35 ≤ 13956269 / 10000000 := by
  have h := S_succ 34
  linarith [s34, u34]

theorem s36 : S 36 ≤ 13956269 / 10000000 := by
  have h := S_succ 35
  linarith [s35, u35]

theorem s37 : S 37 ≤ 13956269 / 10000000 := by
  have h := S_succ 36
  linarith [s36, u36]

theorem s38 : S 38 ≤ 110322 / 78125 := by
  have h := S_succ 37
  linarith [s37, u37]

theorem s39 : S 39 ≤ 110322 / 78125 := by
  have h := S_succ 38
  linarith [s38, u38]

theorem s40 : S 40 ≤ 110322 / 78125 := by
  have h := S_succ 39
  linarith [s39, u39]

theorem s41 : S 41 ≤ 110322 / 78125 := by
  have h := S_succ 40
  linarith [s40, u40]

theorem s42 : S 42 ≤ 14266257 / 10000000 := by
  have h := S_succ 41
  linarith [s41, u41]

theorem s43 : S 43 ≤ 14266257 / 10000000 := by
  have h := S_succ 42
  linarith [s42, u42]

theorem s44 : S 44 ≤ 14402911 / 10000000 := by
  have h := S_succ 43
  linarith [s43, u43]

theorem s45 : S 45 ≤ 14402911 / 10000000 := by
  have h := S_succ 44
  linarith [s44, u44]

theorem s46 : S 46 ≤ 14402911 / 10000000 := by
  have h := S_succ 45
  linarith [s45, u45]

theorem s47 : S 47 ≤ 14402911 / 10000000 := by
  have h := S_succ 46
  linarith [s46, u46]

theorem s48 : S 48 ≤ 7262501 / 5000000 := by
  have h := S_succ 47
  linarith [s47, u47]

theorem s49 : S 49 ≤ 7262501 / 5000000 := by
  have h := S_succ 48
  linarith [s48, u48]

theorem s50 : S 50 ≤ 7262501 / 5000000 := by
  have h := S_succ 49
  linarith [s49, u49]

theorem s51 : S 51 ≤ 7262501 / 5000000 := by
  have h := S_succ 50
  linarith [s50, u50]

/-! ### The tail -/

/-- `w(x) = x^{-3/2}` -/
noncomputable def w (x : ℝ) : ℝ := 1 / (x * √x)

/-- `F(x) = 2/√x` -/
noncomputable def F (x : ℝ) : ℝ := 2 / √x

theorem w_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ w x := by unfold w; positivity

theorem w_anti {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : w y ≤ w x := by
  unfold w
  exact one_div_le_one_div_of_le (mul_pos hx (Real.sqrt_pos.2 hx))
    (mul_le_mul h (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _) (by linarith))

theorem w_tel {x : ℝ} (hx : 1 ≤ x) : w (x + 1) ≤ F x - F (x + 1) := by
  have hx0 : 0 < x := by linarith
  unfold w F
  have ha : 0 < √x := Real.sqrt_pos.2 hx0
  have hb : 0 < √(x + 1) := Real.sqrt_pos.2 (by linarith)
  have ha2 : √x ^ 2 = x := Real.sq_sqrt hx0.le
  have hb2 : √(x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hab : √x ≤ √(x + 1) := Real.sqrt_le_sqrt (by linarith)
  set a := √x
  set b := √(x + 1)
  have e1 : (x + 1) * b = b ^ 3 := by rw [← hb2]; ring
  have e2 : 2 / a - 2 / b = 1 / b ^ 3 + (2 * b ^ 3 - 2 * a * b ^ 2 - a) / (a * b ^ 3) := by
    field_simp; ring
  have e3 : 2 * b ^ 3 - 2 * a * b ^ 2 - a = (b - a) * (2 * b ^ 2 - a * b - a ^ 2) := by
    linear_combination a * (hb2 - ha2)
  have hn : 0 ≤ 2 * b ^ 3 - 2 * a * b ^ 2 - a := by
    rw [e3]; exact mul_nonneg (by linarith) (by nlinarith)
  rw [e1, e2]
  exact le_add_of_nonneg_right (div_nonneg hn (by positivity))

theorem tel_w (a : ℕ) (ha : 1 ≤ a) :
    ∀ N : ℕ, a ≤ N → ∑ n ∈ Finset.Ico (a + 1) (N + 1), w n ≤ F a - F N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans ha hN)
    have := w_tel h1
    push_cast
    linarith

theorem F_nonneg (x : ℝ) : 0 ≤ F x := by unfold F; positivity

/-- `lcm(1..n)` by recursion, for a kernel check -/
def lc : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lc n) (n + 1)

theorem lc_eq (n : ℕ) : lc n = Nat.lcmUpto n := by
  induction n with
  | zero => simp [lc, L5LamSq.lcmUpto_zero']
  | succ n ih => rw [L5LamSq.lcmUpto_succ, ← ih]; rfl

theorem lc50 : 2 ^ 71 ≤ lc 50 := by decide +kernel

/-- `ψ(50) ≥ 71 log 2` -/
theorem psi50_ge : 71 * Real.log 2 ≤ ψ ((50 : ℕ) : ℝ) := by
  rw [psi_eq_log_lcmUpto, ← lc_eq]
  have h : ((2 : ℝ) ^ 71) ≤ ((lc 50 : ℕ) : ℝ) := by exact_mod_cast lc50
  have := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at this
  push_cast at this ⊢
  linarith

theorem tail_sum (M : ℕ) (hM : 299 ≤ M) :
    ∑ n ∈ Finset.Ico 51 (M + 1), Λ n * w n ≤
      (Real.log 3 * 50 - ψ ((50 : ℕ) : ℝ)) * w 50 + Real.log 3 * (F 50 - F 299) +
        (1.9 - Real.log 3) * (299 * w 299) + 1.9 * F 299 := by
  have hanti : ∀ m : ℕ, 50 ≤ m → w ((m + 1 : ℕ) : ℝ) ≤ w (m : ℝ) := by
    intro m hm
    have h : (50 : ℝ) ≤ m := by exact_mod_cast hm
    exact w_anti (by linarith) (by push_cast; linarith)
  have hl3 := L5LamSq.log3_bounds
  have hl3' : Real.log 3 ≤ 1.9 := by linarith [hl3.2]
  have P1 := L5LamSq.sbp w (Real.log 3) 50 hanti 299 (by norm_num)
    (fun m _ h2 => L5LamSq.psi_le_log3 m (by omega))
  have T1 := tel_w 50 (by norm_num) 299 (by norm_num)
  have P2 := L5LamSq.sbp w 1.9 299 (fun m hm => hanti m (by omega)) M hM
    (fun m h1 _ => L5LamSq.psi_le_19' m h1 hl3')
  have T2 := tel_w 299 (by norm_num) M hM
  have hM' : (299 : ℝ) ≤ M := by exact_mod_cast hM
  have n1 : 0 ≤ (1.9 * (M : ℝ) - ψ (M : ℝ)) * w M :=
    mul_nonneg (by linarith [L5LamSq.psi_le_19' M hM hl3']) (w_nonneg (by linarith))
  have n2 := F_nonneg (M : ℝ)
  have hsplit : ∑ n ∈ Finset.Ico 51 (M + 1), Λ n * w n =
      ∑ n ∈ Finset.Ico 51 300, Λ n * w n + ∑ n ∈ Finset.Ico 300 (M + 1), Λ n * w n :=
    (Finset.sum_Ico_consecutive _ (by norm_num) (by omega)).symm
  have m1 := mul_le_mul_of_nonneg_left T1 (by linarith [hl3.1] : (0 : ℝ) ≤ Real.log 3)
  have m2 := mul_le_mul_of_nonneg_left T2 (by norm_num : (0 : ℝ) ≤ 1.9)
  simp only [show (50 + 1 : ℕ) = 51 by rfl, show (299 + 1 : ℕ) = 300 by rfl] at P1 T1 P2 T2 m1 m2
  rw [hsplit]
  push_cast at *
  nlinarith

theorem tail_num :
    (Real.log 3 * 50 - ψ ((50 : ℕ) : ℝ)) * w 50 + Real.log 3 * (F 50 - F 299) +
      (1.9 - Real.log 3) * (299 * w 299) + 1.9 * F 299 ≤ 0.4662 := by
  have hl3 := L5LamSq.log3_bounds
  have hp := psi50_ge
  have l2 := Real.log_two_gt_d9
  have s5a : (7.071 : ℝ) ≤ √50 := Real.le_sqrt_of_sq_le (by norm_num)
  have s2a : (17.29 : ℝ) ≤ √299 := Real.le_sqrt_of_sq_le (by norm_num)
  have s2b : √299 ≤ (17.3 : ℝ) := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hw50 : w 50 ≤ 1 / (50 * 7.071) := by
    unfold w; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hw50' : 0 ≤ w 50 := w_nonneg (by norm_num)
  have hX : Real.log 3 * 50 - ψ ((50 : ℕ) : ℝ) ≤ 5.72 := by
    have := hl3.2
    have hp' := hp
    norm_num at hp' ⊢
    linarith
  have hA : (Real.log 3 * 50 - ψ ((50 : ℕ) : ℝ)) * w 50 ≤ 5.72 * (1 / (50 * 7.071)) :=
    (mul_le_mul_of_nonneg_right hX hw50').trans
      (mul_le_mul_of_nonneg_left hw50 (by norm_num))
  have hF50 : F 50 ≤ 2 / 7.071 := by
    unfold F; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) s5a
  have hF299 : 2 / 17.3 ≤ F 299 := by
    unfold F; exact div_le_div_of_nonneg_left (by norm_num) (by positivity) s2b
  have hF299' : F 299 ≤ 2 / 17.29 := by
    unfold F; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) s2a
  have hs0 : 0 < √(299 : ℝ) := by positivity
  have h299 : 299 * w 299 = 1 / √299 := by unfold w; field_simp
  have h299' : 1 / √(299 : ℝ) ≤ 1 / 17.29 := one_div_le_one_div_of_le (by norm_num) s2a
  have hFd : 0 ≤ F 50 - F 299 := by
    unfold F
    exact sub_nonneg.2 (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (Real.sqrt_le_sqrt (by norm_num)))
  have hB : Real.log 3 * (F 50 - F 299) ≤ 1.09864 * (2 / 7.071 - 2 / 17.3) :=
    mul_le_mul hl3.2 (by linarith) hFd (by norm_num)
  have hC : (1.9 - Real.log 3) * (299 * w 299) ≤ 0.80206 * (1 / 17.29) := by
    rw [h299]
    exact mul_le_mul (by linarith [hl3.1]) h299' (by positivity) (by norm_num)
  have hD : 1.9 * F 299 ≤ 1.9 * (2 / 17.29) := by linarith
  norm_num at hA hB hC hD ⊢
  linarith

theorem kt_le_tail {n : ℕ} (hn : 51 ≤ n) : kt n ≤ 51 / 50 * (Λ n * w n) := by
  have hn' : (51 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hp : n.Prime
  · unfold kt w
    rw [L5.norm_primeTerm_half hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    rw [div_le_iff₀ (mul_pos hs (by linarith))]
    have e : 51 / 50 * (Real.log n * (1 / (n * √(n : ℝ)))) * (√(n : ℝ) * ((n : ℝ) - 1)) =
        Real.log n * (51 * ((n : ℝ) - 1) / (50 * n)) := by
      field_simp
    rw [e]
    refine le_mul_of_one_le_right hl ?_
    rw [le_div_iff₀ (by linarith)]; linarith
  · have := hzero hp
    have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have h1 := w_nonneg (x := (n : ℝ)) (by linarith)
    have : 0 ≤ 51 / 50 * (Λ n * w n) := by positivity
    linarith

/-- `K ≤ 2` -/
theorem K451_le_two : L5.K451 ≤ 2 := by
  show ∑' n : ℕ, kt n ≤ 2
  refine Real.tsum_le_of_sum_range_le kt_nonneg fun N => ?_
  change S N ≤ 2
  set M := max N 299
  have hM : 299 ≤ M := le_max_right _ _
  have h1 : S N ≤ S (M + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun i _ _ => kt_nonneg i)
  have hsplit : S (M + 1) = S 51 + ∑ n ∈ Finset.Ico 51 (M + 1), kt n :=
    (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  have h2 : ∑ n ∈ Finset.Ico 51 (M + 1), kt n ≤
      ∑ n ∈ Finset.Ico 51 (M + 1), 51 / 50 * (Λ n * w n) :=
    Finset.sum_le_sum fun n hn => kt_le_tail (by simp at hn; omega)
  rw [← Finset.mul_sum] at h2
  have h3 := tail_sum M hM
  have h4 := tail_num
  have h5 := s51
  linarith

theorem K451_nonneg : 0 ≤ L5.K451 := tsum_nonneg fun _ => norm_nonneg _

/-- **`Const4`**, PROVED: `K² ≤ 4`, p. 370, the paper states `K² < 4.51`. -/
theorem const4 : L5.Const4 := by
  unfold L5.Const4
  nlinarith [K451_le_two, K451_nonneg]

/-- **`Const451`**, p. 370, PROVED. -/
theorem const451 : L5.Const451 := L5.const451_of_const4 const4

/-- **(22), p. 370**, PROVED, no named input. -/
theorem bound22 : L5.Bound22 := L5.bound22_of_K4 const4

/-- **Lemma 5, p. 368**, CONDITIONAL ON Lemma 4 and `Parseval1920` only. -/
theorem lemma5_of_U1416 (h4 : Lemma4) (hP : L5.Parseval1920) : Lemma5 :=
  L5LamSq.lemma5_of_lamSq2 h4 hP const4

/-- **Lemma 5, guarded**, CONDITIONAL ON `Lemma4G` and `Parseval1920` only. -/
theorem lemma5G_of_U1416 (h4 : L5.Lemma4G) (hP : L5.Parseval1920) : L5.Lemma5G :=
  L5.lemma5G_of_K4 h4 hP L5LamSq.bound21 const4

/-- **The Remark, p. 373**, CONDITIONAL ON `Lemma4G` and `Parseval1920` only. -/
theorem remark_of_U1416 (h4 : L5.Lemma4G) (hP : L5.Parseval1920) : RemarkStatement :=
  L5.remark_of_lemma4G_K4 h4 hP L5LamSq.bound21 const4

/-- Vacuity: `K > 0`, the `p = 2` term is positive, so `Const4` is not about a zero sum. -/
theorem K451_pos : 0 < L5.K451 := by
  have h2 : 0 < kt 2 := by
    unfold kt; rw [L5.norm_primeTerm_half Nat.prime_two]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have : (0 : ℝ) < √((2 : ℕ) : ℝ) := Real.sqrt_pos.2 (by norm_num)
    push_cast at *
    apply div_pos (by assumption); nlinarith
  have hs : Summable kt := L5.summable_norm_primeTerm (s := (1 / 2 : ℂ)) (by norm_num)
  exact lt_of_lt_of_le h2 (hs.le_tsum 2 fun j _ => kt_nonneg j)

end LeanLab.Kaniecki1995.L5U1416

#print axioms LeanLab.Kaniecki1995.L5U1416.hzero
#print axioms LeanLab.Kaniecki1995.L5U1416.hterm
#print axioms LeanLab.Kaniecki1995.L5U1416.s51
#print axioms LeanLab.Kaniecki1995.L5U1416.w_anti
#print axioms LeanLab.Kaniecki1995.L5U1416.w_tel
#print axioms LeanLab.Kaniecki1995.L5U1416.tel_w
#print axioms LeanLab.Kaniecki1995.L5U1416.lc50
#print axioms LeanLab.Kaniecki1995.L5U1416.psi50_ge
#print axioms LeanLab.Kaniecki1995.L5U1416.tail_sum
#print axioms LeanLab.Kaniecki1995.L5U1416.tail_num
#print axioms LeanLab.Kaniecki1995.L5U1416.kt_le_tail
#print axioms LeanLab.Kaniecki1995.L5U1416.K451_le_two
#print axioms LeanLab.Kaniecki1995.L5U1416.K451_nonneg
#print axioms LeanLab.Kaniecki1995.L5U1416.const4
#print axioms LeanLab.Kaniecki1995.L5U1416.const451
#print axioms LeanLab.Kaniecki1995.L5U1416.bound22
#print axioms LeanLab.Kaniecki1995.L5U1416.lemma5_of_U1416
#print axioms LeanLab.Kaniecki1995.L5U1416.lemma5G_of_U1416
#print axioms LeanLab.Kaniecki1995.L5U1416.remark_of_U1416
#print axioms LeanLab.Kaniecki1995.L5U1416.K451_pos
