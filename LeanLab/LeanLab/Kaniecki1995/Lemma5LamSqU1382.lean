/-
P0022, Kaniecki 1995, the input `LamSq2` of Lemma5Near21.lean, PROVED here.
PC run 20261021T0903Z-24128, unit U-1382, T1.

`LamSq2`: for `1 < s ≤ 2`, `Σ Λ(n)² n^{-s} ≤ 2/(s-1)²`. Write `u = s - 1 ∈ (0, 1]`.
Head `n ≤ 300`: `Λ(n)² n^{-1-u} ≤ n a_n 2^{-ju}` for `2^j ≤ n`, with the certified `f n ≤ a_n`
of Lemma5Lam.lean, so the head is at most `P(2^{-u})`, `P` a polynomial of degree 8 with
coefficients the block sums of `n a_n`.
Tail `n > 300`: `Λ(n)² ≤ Λ(n) log n`, summation by parts against `g_u(x) = log x · x^{-1-u}`,
with `ψ(N) ≤ 1.9 N` for `N ≥ 300` from Lemma5Lam.lean and `G_u(x) = x^{-u}(log x/u + 1/u²)`,
`G_u' = -g_u`, so by the mean value theorem `g_u(x+1) ≤ G_u(x) - G_u(x+1)`; the tail is at most
`1.9 (300 g_u(300) + G_u(300))`, and `u²` times this is `1.9 φ(u)`,
`φ(u) = 300^{-u}(1 + u log 300 + u² log 300)`, antitone in `u ≥ 0` with `φ(0) = 1`.
So `u² Σ ≤ u² P(2^{-u}) + 1.9 φ(u)`, and this is at most 2 on each of ten pieces of `(0, 1]`,
with rational bounds `2^{-a} ≤ r`, `300^{-a} ≤ ρ` checked as `r^m 2^k ≥ 1`, `ρ^m 300^k ≥ 1` for
`a = k/m`. Grid and numbers: numerics/U1382_grid.py, U1382_lamsq_gen.py and their .out files.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5Lam

set_option exponentiation.threshold 2000

namespace LeanLab.Kaniecki1995.L5LamSqU1382

open Real Chebyshev
open scoped ArithmeticFunction.vonMangoldt

/-! ### Real analysis helpers -/

noncomputable def q (u : ℝ) : ℝ := (2 : ℝ) ^ (-u)

theorem pow_q {u : ℝ} (j : ℕ) : ((2 : ℝ) ^ j) ^ (-u) = q u ^ j := by
  unfold q
  rw [← Real.rpow_natCast 2 j, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast _ j,
    ← Real.rpow_mul (by norm_num), mul_comm]

theorem root_le {b r a : ℝ} (k m : ℕ) (hb : 1 ≤ b) (hm : 0 < m) (hak : a * m = k)
    (hr : 0 ≤ r) (h : 1 ≤ r ^ m * b ^ k) : b ^ (-a) ≤ r := by
  have hb0 : 0 < b := by linarith
  have hx : (b ^ (-a)) ^ m = (b ^ k)⁻¹ := by
    rw [← Real.rpow_natCast _ m, ← Real.rpow_mul hb0.le, neg_mul, hak, Real.rpow_neg hb0.le,
      Real.rpow_natCast]
  by_contra hlt
  push Not at hlt
  have := pow_lt_pow_left₀ hlt hr hm.ne'
  rw [hx] at this
  have hbk : 0 < b ^ k := by positivity
  have := mul_lt_mul_of_pos_right this hbk
  rw [inv_mul_cancel₀ hbk.ne'] at this
  linarith

/-- `g_u(x) = log x · x^{-(1+u)}` -/
noncomputable def g (u x : ℝ) : ℝ := Real.log x * x ^ (-(1 + u))

/-- `G_u(x) = x^{-u} (log x / u + 1/u²)`, an antiderivative of `-g_u` -/
noncomputable def G (u x : ℝ) : ℝ := x ^ (-u) * (Real.log x / u + 1 / u ^ 2)

theorem g_eq {u x : ℝ} (hx : 0 < x) : g u x = (Real.log x / x) * x ^ (-u) := by
  unfold g
  rw [neg_add, Real.rpow_add hx, Real.rpow_neg_one]; ring

theorem g_anti {u x y : ℝ} (hu : 0 ≤ u) (hx : 3 ≤ x) (hxy : x ≤ y) : g u y ≤ g u x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  rw [g_eq hx0, g_eq hy0]
  have he : Real.exp 1 ≤ x := by have := Real.exp_one_lt_d9; linarith
  have h1 : Real.log y / y ≤ Real.log x / x :=
    Real.log_div_self_antitoneOn he (he.trans hxy) hxy
  have h2 : y ^ (-u) ≤ x ^ (-u) := Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have h3 : 0 ≤ Real.log y / y := div_nonneg (Real.log_nonneg (by linarith)) hy0.le
  have h4 : 0 ≤ x ^ (-u) := by positivity
  exact mul_le_mul h1 h2 (by positivity) (h3.trans h1)

theorem hasDerivAt_G {u y : ℝ} (hu : 0 < u) (hy : 0 < y) : HasDerivAt (G u) (-g u y) y := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (-u)) (-u * y ^ (-u - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  have h2 : HasDerivAt (fun x : ℝ => Real.log x / u + 1 / u ^ 2) (y⁻¹ / u) y :=
    ((Real.hasDerivAt_log hy.ne').div_const u).add_const _
  have h := h1.mul h2
  unfold G
  convert h using 1
  unfold g
  rw [Real.rpow_sub hy, Real.rpow_one, neg_add, Real.rpow_add hy, Real.rpow_neg_one]
  field_simp
  ring

theorem g_tel {u x : ℝ} (hu : 0 < u) (hx : 3 ≤ x) : g u (x + 1) ≤ G u x - G u (x + 1) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (G u) (fun y => -g u y)
    (show x < x + 1 by linarith)
    (fun y hy => (hasDerivAt_G hu (by linarith [hy.1])).continuousAt.continuousWithinAt)
    (fun y hy => hasDerivAt_G hu (by linarith [hy.1]))
  have : G u x - G u (x + 1) = g u c := by
    have e : x + 1 - x = 1 := by ring
    rw [e, div_one] at hcd; linarith
  rw [this]
  exact g_anti hu.le (by linarith [hc.1]) hc.2.le

theorem G_nonneg {u x : ℝ} (hu : 0 < u) (hx : 1 ≤ x) : 0 ≤ G u x := by
  unfold G; have := Real.log_nonneg hx; positivity

theorem g_nonneg {u x : ℝ} (hx : 1 ≤ x) : 0 ≤ g u x := by
  unfold g; have := Real.log_nonneg hx; have : 0 ≤ x := by linarith
  positivity

/-- `φ(u) = 300^{-u} (1 + u log 300 + u² log 300)` -/
noncomputable def phi (u : ℝ) : ℝ :=
  (300 : ℝ) ^ (-u) * (1 + u * Real.log 300 + u ^ 2 * Real.log 300)

theorem two_le_log300 : 2 ≤ Real.log 300 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e]; nlinarith [Real.exp_pos 1]

theorem phi_anti : AntitoneOn phi (Set.Ici 0) := by
  set L := Real.log 300 with hLdef
  have hL := two_le_log300
  have hform : phi = fun u => Real.exp (-(u * L)) * (1 + u * L + u ^ 2 * L) := by
    funext u; unfold phi
    rw [Real.rpow_def_of_pos (by norm_num), hLdef]; ring_nf
  have hd : ∀ u : ℝ, HasDerivAt phi (Real.exp (-(u * L)) * (u * L * (2 - L - u * L))) u := by
    intro u
    rw [hform]
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-(u * L))) (Real.exp (-(u * L)) * (-(1 * L))) u :=
      (((hasDerivAt_id u).mul_const L).neg).exp
    have h2 : HasDerivAt (fun u : ℝ => 1 + u * L + u ^ 2 * L) (1 * L + (2 * u) * L) u := by
      have := (((hasDerivAt_id u).mul_const L).const_add 1).add ((hasDerivAt_pow 2 u).mul_const L)
      convert this using 1
      · funext x; simp
      · push_cast; ring
    convert h1.mul h2 using 1; ring
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · exact fun u _ => (hd u).continuousAt.continuousWithinAt
  · exact fun u _ => (hd u).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    rw [(hd u).deriv]
    have hu0 : 0 < u := hu
    have : u * L * (2 - L - u * L) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith)
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le this

theorem tail_identity {u : ℝ} (hu : 0 < u) :
    u ^ 2 * (1.9 * (300 * g u 300 + G u 300)) = 1.9 * phi u := by
  unfold g G phi
  rw [neg_add, Real.rpow_add (by norm_num), Real.rpow_neg_one]
  field_simp
  ring


/-! ### The head `n ≤ 300` -/

/-- the summand of `LamSq2` at `s = 1 + u` -/
noncomputable def F (u : ℝ) (n : ℕ) : ℝ := Λ n ^ 2 * (n : ℝ) ^ (-(1 + u))

/-- the head partial sums -/
noncomputable def HS (u : ℝ) (k : ℕ) : ℝ := ∑ n ∈ Finset.range k, F u n

theorem HS_zero (u : ℝ) : HS u 0 = 0 := by simp [HS]

theorem HS_succ (u : ℝ) (k : ℕ) : HS u (k + 1) = HS u k + F u k := Finset.sum_range_succ _ _

theorem F_nonneg (u : ℝ) (n : ℕ) : 0 ≤ F u n := by unfold F; positivity

theorem q_nonneg (u : ℝ) : 0 ≤ q u := by unfold q; positivity

theorem hterm {u a : ℝ} {n j : ℕ} (hu : 0 ≤ u) (hn : 2 ^ j ≤ n) (hf : L5Lam.f n ≤ a) :
    F u n ≤ n * a * q u ^ j := by
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.pow_pos (n := j) two_pos) hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hfeq : F u n = (n : ℝ) * L5Lam.f n * (n : ℝ) ^ (-u) := by
    unfold F L5Lam.f
    have e : (n : ℝ) ^ (-(1 + u)) = (n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) * (n : ℝ) ^ (-u) := by
      rw [mul_assoc, ← Real.rpow_add hn']
      conv_rhs => arg 1; rw [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hn']; congr 1; ring
    rw [e]; ring
  have hq : (n : ℝ) ^ (-u) ≤ q u ^ j := by
    have h2 : ((2 : ℝ) ^ j) ≤ n := by exact_mod_cast hn
    calc (n : ℝ) ^ (-u) ≤ ((2 : ℝ) ^ j) ^ (-u) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
      _ = q u ^ j := pow_q j
  have hf0 : 0 ≤ L5Lam.f n := L5Lam.f_nonneg n
  rw [hfeq]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hf hn'.le) hq (by positivity)
    (mul_nonneg hn'.le (hf0.trans hf))

theorem e0 {u : ℝ} (_hu : 0 ≤ u) : F u 0 ≤ 0 := by simp [F]

theorem e1 {u : ℝ} (_hu : 0 ≤ u) : F u 1 ≤ 0 := by simp [F]

theorem e2 {u : ℝ} (hu : 0 ≤ u) : F u 2 ≤ 2 * (1201133 / 10000000) * q u ^ 1 :=
  hterm hu (by norm_num) L5Lam.t2

theorem e3 {u : ℝ} (hu : 0 ≤ u) : F u 3 ≤ 3 * (1342705 / 10000000) * q u ^ 1 :=
  hterm hu (by norm_num) L5Lam.t3

theorem e4 {u : ℝ} (hu : 0 ≤ u) : F u 4 ≤ 4 * (300284 / 10000000) * q u ^ 2 :=
  hterm hu (by norm_num) L5Lam.t4

theorem e5 {u : ℝ} (hu : 0 ≤ u) : F u 5 ≤ 5 * (1041655 / 10000000) * q u ^ 2 :=
  hterm hu (by norm_num) L5Lam.t5

theorem e6 {u : ℝ} (hu : 0 ≤ u) : F u 6 ≤ 6 * (0 / 10000000) * q u ^ 2 :=
  hterm hu (by norm_num) L5Lam.t6

theorem e7 {u : ℝ} (hu : 0 ≤ u) : F u 7 ≤ 7 * (775604 / 10000000) * q u ^ 2 :=
  hterm hu (by norm_num) L5Lam.t7

theorem e8 {u : ℝ} (hu : 0 ≤ u) : F u 8 ≤ 8 * (75071 / 10000000) * q u ^ 3 :=
  hterm hu (by norm_num) L5Lam.t8

theorem e9 {u : ℝ} (hu : 0 ≤ u) : F u 9 ≤ 9 * (149190 / 10000000) * q u ^ 3 :=
  hterm hu (by norm_num) L5Lam.t9

theorem e10 {u : ℝ} (hu : 0 ≤ u) : F u 10 ≤ 10 * (0 / 10000000) * q u ^ 3 :=
  hterm hu (by norm_num) L5Lam.t10

theorem e11 {u : ℝ} (hu : 0 ≤ u) : F u 11 ≤ 11 * (475613 / 10000000) * q u ^ 3 :=
  hterm hu (by norm_num) L5Lam.t11

theorem e12 {u : ℝ} (hu : 0 ≤ u) : F u 12 ≤ 12 * (0 / 10000000) * q u ^ 3 :=
  hterm hu (by norm_num) L5Lam.t12

theorem e13 {u : ℝ} (hu : 0 ≤ u) : F u 13 ≤ 13 * (389854 / 10000000) * q u ^ 3 :=
  hterm hu (by norm_num) L5Lam.t13

theorem e14 {u : ℝ} (hu : 0 ≤ u) : F u 14 ≤ 14 * (0 / 10000000) * q u ^ 3 :=
  hterm hu (by norm_num) L5Lam.t14

theorem e15 {u : ℝ} (hu : 0 ≤ u) : F u 15 ≤ 15 * (0 / 10000000) * q u ^ 3 :=
  hterm hu (by norm_num) L5Lam.t15

theorem e16 {u : ℝ} (hu : 0 ≤ u) : F u 16 ≤ 16 * (18768 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t16

theorem e17 {u : ℝ} (hu : 0 ≤ u) : F u 17 ≤ 17 * (278610 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t17

theorem e18 {u : ℝ} (hu : 0 ≤ u) : F u 18 ≤ 18 * (0 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t18

theorem e19 {u : ℝ} (hu : 0 ≤ u) : F u 19 ≤ 19 * (240393 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t19

theorem e20 {u : ℝ} (hu : 0 ≤ u) : F u 20 ≤ 20 * (0 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t20

theorem e21 {u : ℝ} (hu : 0 ≤ u) : F u 21 ≤ 21 * (0 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t21

theorem e22 {u : ℝ} (hu : 0 ≤ u) : F u 22 ≤ 22 * (0 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t22

theorem e23 {u : ℝ} (hu : 0 ≤ u) : F u 23 ≤ 23 * (186480 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t23

theorem e24 {u : ℝ} (hu : 0 ≤ u) : F u 24 ≤ 24 * (0 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t24

theorem e25 {u : ℝ} (hu : 0 ≤ u) : F u 25 ≤ 25 * (41667 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t25

theorem e26 {u : ℝ} (hu : 0 ≤ u) : F u 26 ≤ 26 * (0 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t26

theorem e27 {u : ℝ} (hu : 0 ≤ u) : F u 27 ≤ 27 * (16577 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t27

theorem e28 {u : ℝ} (hu : 0 ≤ u) : F u 28 ≤ 28 * (0 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t28

theorem e29 {u : ℝ} (hu : 0 ≤ u) : F u 29 ≤ 29 * (134902 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t29

theorem e30 {u : ℝ} (hu : 0 ≤ u) : F u 30 ≤ 30 * (0 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t30

theorem e31 {u : ℝ} (hu : 0 ≤ u) : F u 31 ≤ 31 * (123043 / 10000000) * q u ^ 4 :=
  hterm hu (by norm_num) L5Lam.t31

theorem e32 {u : ℝ} (hu : 0 ≤ u) : F u 32 ≤ 32 * (4692 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t32

theorem e33 {u : ℝ} (hu : 0 ≤ u) : F u 33 ≤ 33 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t33

theorem e34 {u : ℝ} (hu : 0 ≤ u) : F u 34 ≤ 34 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t34

theorem e35 {u : ℝ} (hu : 0 ≤ u) : F u 35 ≤ 35 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t35

theorem e36 {u : ℝ} (hu : 0 ≤ u) : F u 36 ≤ 36 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t36

theorem e37 {u : ℝ} (hu : 0 ≤ u) : F u 37 ≤ 37 * (95297 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t37

theorem e38 {u : ℝ} (hu : 0 ≤ u) : F u 38 ≤ 38 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t38

theorem e39 {u : ℝ} (hu : 0 ≤ u) : F u 39 ≤ 39 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t39

theorem e40 {u : ℝ} (hu : 0 ≤ u) : F u 40 ≤ 40 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t40

theorem e41 {u : ℝ} (hu : 0 ≤ u) : F u 41 ≤ 41 * (82095 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t41

theorem e42 {u : ℝ} (hu : 0 ≤ u) : F u 42 ≤ 42 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t42

theorem e43 {u : ℝ} (hu : 0 ≤ u) : F u 43 ≤ 43 * (76607 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t43

theorem e44 {u : ℝ} (hu : 0 ≤ u) : F u 44 ≤ 44 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t44

theorem e45 {u : ℝ} (hu : 0 ≤ u) : F u 45 ≤ 45 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t45

theorem e46 {u : ℝ} (hu : 0 ≤ u) : F u 46 ≤ 46 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t46

theorem e47 {u : ℝ} (hu : 0 ≤ u) : F u 47 ≤ 47 * (67109 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t47

theorem e48 {u : ℝ} (hu : 0 ≤ u) : F u 48 ≤ 48 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t48

theorem e49 {u : ℝ} (hu : 0 ≤ u) : F u 49 ≤ 49 * (15829 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t49

theorem e50 {u : ℝ} (hu : 0 ≤ u) : F u 50 ≤ 50 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t50

theorem e51 {u : ℝ} (hu : 0 ≤ u) : F u 51 ≤ 51 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t51

theorem e52 {u : ℝ} (hu : 0 ≤ u) : F u 52 ≤ 52 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t52

theorem e53 {u : ℝ} (hu : 0 ≤ u) : F u 53 ≤ 53 * (56244 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t53

theorem e54 {u : ℝ} (hu : 0 ≤ u) : F u 54 ≤ 54 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t54

theorem e55 {u : ℝ} (hu : 0 ≤ u) : F u 55 ≤ 55 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t55

theorem e56 {u : ℝ} (hu : 0 ≤ u) : F u 56 ≤ 56 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t56

theorem e57 {u : ℝ} (hu : 0 ≤ u) : F u 57 ≤ 57 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t57

theorem e58 {u : ℝ} (hu : 0 ≤ u) : F u 58 ≤ 58 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t58

theorem e59 {u : ℝ} (hu : 0 ≤ u) : F u 59 ≤ 59 * (47766 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t59

theorem e60 {u : ℝ} (hu : 0 ≤ u) : F u 60 ≤ 60 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t60

theorem e61 {u : ℝ} (hu : 0 ≤ u) : F u 61 ≤ 61 * (45520 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t61

theorem e62 {u : ℝ} (hu : 0 ≤ u) : F u 62 ≤ 62 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t62

theorem e63 {u : ℝ} (hu : 0 ≤ u) : F u 63 ≤ 63 * (0 / 10000000) * q u ^ 5 :=
  hterm hu (by norm_num) L5Lam.t63

theorem e64 {u : ℝ} (hu : 0 ≤ u) : F u 64 ≤ 64 * (1173 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t64

theorem e65 {u : ℝ} (hu : 0 ≤ u) : F u 65 ≤ 65 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t65

theorem e66 {u : ℝ} (hu : 0 ≤ u) : F u 66 ≤ 66 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t66

theorem e67 {u : ℝ} (hu : 0 ≤ u) : F u 67 ≤ 67 * (39439 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t67

theorem e68 {u : ℝ} (hu : 0 ≤ u) : F u 68 ≤ 68 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t68

theorem e69 {u : ℝ} (hu : 0 ≤ u) : F u 69 ≤ 69 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t69

theorem e70 {u : ℝ} (hu : 0 ≤ u) : F u 70 ≤ 70 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t70

theorem e71 {u : ℝ} (hu : 0 ≤ u) : F u 71 ≤ 71 * (36122 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t71

theorem e72 {u : ℝ} (hu : 0 ≤ u) : F u 72 ≤ 72 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t72

theorem e73 {u : ℝ} (hu : 0 ≤ u) : F u 73 ≤ 73 * (34605 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t73

theorem e74 {u : ℝ} (hu : 0 ≤ u) : F u 74 ≤ 74 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t74

theorem e75 {u : ℝ} (hu : 0 ≤ u) : F u 75 ≤ 75 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t75

theorem e76 {u : ℝ} (hu : 0 ≤ u) : F u 76 ≤ 76 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t76

theorem e77 {u : ℝ} (hu : 0 ≤ u) : F u 77 ≤ 77 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t77

theorem e78 {u : ℝ} (hu : 0 ≤ u) : F u 78 ≤ 78 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t78

theorem e79 {u : ℝ} (hu : 0 ≤ u) : F u 79 ≤ 79 * (30601 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t79

theorem e80 {u : ℝ} (hu : 0 ≤ u) : F u 80 ≤ 80 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t80

theorem e81 {u : ℝ} (hu : 0 ≤ u) : F u 81 ≤ 81 * (1842 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t81

theorem e82 {u : ℝ} (hu : 0 ≤ u) : F u 82 ≤ 82 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t82

theorem e83 {u : ℝ} (hu : 0 ≤ u) : F u 83 ≤ 83 * (28414 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t83

theorem e84 {u : ℝ} (hu : 0 ≤ u) : F u 84 ≤ 84 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t84

theorem e85 {u : ℝ} (hu : 0 ≤ u) : F u 85 ≤ 85 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t85

theorem e86 {u : ℝ} (hu : 0 ≤ u) : F u 86 ≤ 86 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t86

theorem e87 {u : ℝ} (hu : 0 ≤ u) : F u 87 ≤ 87 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t87

theorem e88 {u : ℝ} (hu : 0 ≤ u) : F u 88 ≤ 88 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t88

theorem e89 {u : ℝ} (hu : 0 ≤ u) : F u 89 ≤ 89 * (25443 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t89

theorem e90 {u : ℝ} (hu : 0 ≤ u) : F u 90 ≤ 90 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t90

theorem e91 {u : ℝ} (hu : 0 ≤ u) : F u 91 ≤ 91 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t91

theorem e92 {u : ℝ} (hu : 0 ≤ u) : F u 92 ≤ 92 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t92

theorem e93 {u : ℝ} (hu : 0 ≤ u) : F u 93 ≤ 93 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t93

theorem e94 {u : ℝ} (hu : 0 ≤ u) : F u 94 ≤ 94 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t94

theorem e95 {u : ℝ} (hu : 0 ≤ u) : F u 95 ≤ 95 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t95

theorem e96 {u : ℝ} (hu : 0 ≤ u) : F u 96 ≤ 96 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t96

theorem e97 {u : ℝ} (hu : 0 ≤ u) : F u 97 ≤ 97 * (22254 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t97

theorem e98 {u : ℝ} (hu : 0 ≤ u) : F u 98 ≤ 98 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t98

theorem e99 {u : ℝ} (hu : 0 ≤ u) : F u 99 ≤ 99 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t99

theorem e100 {u : ℝ} (hu : 0 ≤ u) : F u 100 ≤ 100 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t100

theorem e101 {u : ℝ} (hu : 0 ≤ u) : F u 101 ≤ 101 * (20917 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t101

theorem e102 {u : ℝ} (hu : 0 ≤ u) : F u 102 ≤ 102 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t102

theorem e103 {u : ℝ} (hu : 0 ≤ u) : F u 103 ≤ 103 * (20254 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t103

theorem e104 {u : ℝ} (hu : 0 ≤ u) : F u 104 ≤ 104 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t104

theorem e105 {u : ℝ} (hu : 0 ≤ u) : F u 105 ≤ 105 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t105

theorem e106 {u : ℝ} (hu : 0 ≤ u) : F u 106 ≤ 106 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t106

theorem e107 {u : ℝ} (hu : 0 ≤ u) : F u 107 ≤ 107 * (19076 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t107

theorem e108 {u : ℝ} (hu : 0 ≤ u) : F u 108 ≤ 108 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t108

theorem e109 {u : ℝ} (hu : 0 ≤ u) : F u 109 ≤ 109 * (18554 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t109

theorem e110 {u : ℝ} (hu : 0 ≤ u) : F u 110 ≤ 110 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t110

theorem e111 {u : ℝ} (hu : 0 ≤ u) : F u 111 ≤ 111 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t111

theorem e112 {u : ℝ} (hu : 0 ≤ u) : F u 112 ≤ 112 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t112

theorem e113 {u : ℝ} (hu : 0 ≤ u) : F u 113 ≤ 113 * (17503 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t113

theorem e114 {u : ℝ} (hu : 0 ≤ u) : F u 114 ≤ 114 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t114

theorem e115 {u : ℝ} (hu : 0 ≤ u) : F u 115 ≤ 115 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t115

theorem e116 {u : ℝ} (hu : 0 ≤ u) : F u 116 ≤ 116 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t116

theorem e117 {u : ℝ} (hu : 0 ≤ u) : F u 117 ≤ 117 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t117

theorem e118 {u : ℝ} (hu : 0 ≤ u) : F u 118 ≤ 118 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t118

theorem e119 {u : ℝ} (hu : 0 ≤ u) : F u 119 ≤ 119 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t119

theorem e120 {u : ℝ} (hu : 0 ≤ u) : F u 120 ≤ 120 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t120

theorem e121 {u : ℝ} (hu : 0 ≤ u) : F u 121 ≤ 121 * (3931 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t121

theorem e122 {u : ℝ} (hu : 0 ≤ u) : F u 122 ≤ 122 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t122

theorem e123 {u : ℝ} (hu : 0 ≤ u) : F u 123 ≤ 123 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t123

theorem e124 {u : ℝ} (hu : 0 ≤ u) : F u 124 ≤ 124 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t124

theorem e125 {u : ℝ} (hu : 0 ≤ u) : F u 125 ≤ 125 * (1667 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t125

theorem e126 {u : ℝ} (hu : 0 ≤ u) : F u 126 ≤ 126 * (0 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t126

theorem e127 {u : ℝ} (hu : 0 ≤ u) : F u 127 ≤ 127 * (14564 / 10000000) * q u ^ 6 :=
  hterm hu (by norm_num) L5Lam.t127

theorem e128 {u : ℝ} (hu : 0 ≤ u) : F u 128 ≤ 128 * (294 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t128

theorem e129 {u : ℝ} (hu : 0 ≤ u) : F u 129 ≤ 129 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t129

theorem e130 {u : ℝ} (hu : 0 ≤ u) : F u 130 ≤ 130 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t130

theorem e131 {u : ℝ} (hu : 0 ≤ u) : F u 131 ≤ 131 * (13872 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t131

theorem e132 {u : ℝ} (hu : 0 ≤ u) : F u 132 ≤ 132 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t132

theorem e133 {u : ℝ} (hu : 0 ≤ u) : F u 133 ≤ 133 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t133

theorem e134 {u : ℝ} (hu : 0 ≤ u) : F u 134 ≤ 134 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t134

theorem e135 {u : ℝ} (hu : 0 ≤ u) : F u 135 ≤ 135 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t135

theorem e136 {u : ℝ} (hu : 0 ≤ u) : F u 136 ≤ 136 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t136

theorem e137 {u : ℝ} (hu : 0 ≤ u) : F u 137 ≤ 137 * (12910 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t137

theorem e138 {u : ℝ} (hu : 0 ≤ u) : F u 138 ≤ 138 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t138

theorem e139 {u : ℝ} (hu : 0 ≤ u) : F u 139 ≤ 139 * (12624 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t139

theorem e140 {u : ℝ} (hu : 0 ≤ u) : F u 140 ≤ 140 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t140

theorem e141 {u : ℝ} (hu : 0 ≤ u) : F u 141 ≤ 141 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t141

theorem e142 {u : ℝ} (hu : 0 ≤ u) : F u 142 ≤ 142 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t142

theorem e143 {u : ℝ} (hu : 0 ≤ u) : F u 143 ≤ 143 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t143

theorem e144 {u : ℝ} (hu : 0 ≤ u) : F u 144 ≤ 144 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t144

theorem e145 {u : ℝ} (hu : 0 ≤ u) : F u 145 ≤ 145 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t145

theorem e146 {u : ℝ} (hu : 0 ≤ u) : F u 146 ≤ 146 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t146

theorem e147 {u : ℝ} (hu : 0 ≤ u) : F u 147 ≤ 147 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t147

theorem e148 {u : ℝ} (hu : 0 ≤ u) : F u 148 ≤ 148 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t148

theorem e149 {u : ℝ} (hu : 0 ≤ u) : F u 149 ≤ 149 * (11302 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t149

theorem e150 {u : ℝ} (hu : 0 ≤ u) : F u 150 ≤ 150 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t150

theorem e151 {u : ℝ} (hu : 0 ≤ u) : F u 151 ≤ 151 * (11052 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t151

theorem e152 {u : ℝ} (hu : 0 ≤ u) : F u 152 ≤ 152 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t152

theorem e153 {u : ℝ} (hu : 0 ≤ u) : F u 153 ≤ 153 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t153

theorem e154 {u : ℝ} (hu : 0 ≤ u) : F u 154 ≤ 154 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t154

theorem e155 {u : ℝ} (hu : 0 ≤ u) : F u 155 ≤ 155 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t155

theorem e156 {u : ℝ} (hu : 0 ≤ u) : F u 156 ≤ 156 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t156

theorem e157 {u : ℝ} (hu : 0 ≤ u) : F u 157 ≤ 157 * (10379 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t157

theorem e158 {u : ℝ} (hu : 0 ≤ u) : F u 158 ≤ 158 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t158

theorem e159 {u : ℝ} (hu : 0 ≤ u) : F u 159 ≤ 159 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t159

theorem e160 {u : ℝ} (hu : 0 ≤ u) : F u 160 ≤ 160 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t160

theorem e161 {u : ℝ} (hu : 0 ≤ u) : F u 161 ≤ 161 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t161

theorem e162 {u : ℝ} (hu : 0 ≤ u) : F u 162 ≤ 162 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t162

theorem e163 {u : ℝ} (hu : 0 ≤ u) : F u 163 ≤ 163 * (9774 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t163

theorem e164 {u : ℝ} (hu : 0 ≤ u) : F u 164 ≤ 164 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t164

theorem e165 {u : ℝ} (hu : 0 ≤ u) : F u 165 ≤ 165 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t165

theorem e166 {u : ℝ} (hu : 0 ≤ u) : F u 166 ≤ 166 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t166

theorem e167 {u : ℝ} (hu : 0 ≤ u) : F u 167 ≤ 167 * (9410 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t167

theorem e168 {u : ℝ} (hu : 0 ≤ u) : F u 168 ≤ 168 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t168

theorem e169 {u : ℝ} (hu : 0 ≤ u) : F u 169 ≤ 169 * (2307 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t169

theorem e170 {u : ℝ} (hu : 0 ≤ u) : F u 170 ≤ 170 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t170

theorem e171 {u : ℝ} (hu : 0 ≤ u) : F u 171 ≤ 171 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t171

theorem e172 {u : ℝ} (hu : 0 ≤ u) : F u 172 ≤ 172 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t172

theorem e173 {u : ℝ} (hu : 0 ≤ u) : F u 173 ≤ 173 * (8880 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t173

theorem e174 {u : ℝ} (hu : 0 ≤ u) : F u 174 ≤ 174 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t174

theorem e175 {u : ℝ} (hu : 0 ≤ u) : F u 175 ≤ 175 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t175

theorem e176 {u : ℝ} (hu : 0 ≤ u) : F u 176 ≤ 176 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t176

theorem e177 {u : ℝ} (hu : 0 ≤ u) : F u 177 ≤ 177 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t177

theorem e178 {u : ℝ} (hu : 0 ≤ u) : F u 178 ≤ 178 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t178

theorem e179 {u : ℝ} (hu : 0 ≤ u) : F u 179 ≤ 179 * (8400 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t179

theorem e180 {u : ℝ} (hu : 0 ≤ u) : F u 180 ≤ 180 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t180

theorem e181 {u : ℝ} (hu : 0 ≤ u) : F u 181 ≤ 181 * (8250 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t181

theorem e182 {u : ℝ} (hu : 0 ≤ u) : F u 182 ≤ 182 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t182

theorem e183 {u : ℝ} (hu : 0 ≤ u) : F u 183 ≤ 183 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t183

theorem e184 {u : ℝ} (hu : 0 ≤ u) : F u 184 ≤ 184 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t184

theorem e185 {u : ℝ} (hu : 0 ≤ u) : F u 185 ≤ 185 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t185

theorem e186 {u : ℝ} (hu : 0 ≤ u) : F u 186 ≤ 186 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t186

theorem e187 {u : ℝ} (hu : 0 ≤ u) : F u 187 ≤ 187 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t187

theorem e188 {u : ℝ} (hu : 0 ≤ u) : F u 188 ≤ 188 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t188

theorem e189 {u : ℝ} (hu : 0 ≤ u) : F u 189 ≤ 189 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t189

theorem e190 {u : ℝ} (hu : 0 ≤ u) : F u 190 ≤ 190 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t190

theorem e191 {u : ℝ} (hu : 0 ≤ u) : F u 191 ≤ 191 * (7564 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t191

theorem e192 {u : ℝ} (hu : 0 ≤ u) : F u 192 ≤ 192 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t192

theorem e193 {u : ℝ} (hu : 0 ≤ u) : F u 193 ≤ 193 * (7438 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t193

theorem e194 {u : ℝ} (hu : 0 ≤ u) : F u 194 ≤ 194 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t194

theorem e195 {u : ℝ} (hu : 0 ≤ u) : F u 195 ≤ 195 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t195

theorem e196 {u : ℝ} (hu : 0 ≤ u) : F u 196 ≤ 196 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t196

theorem e197 {u : ℝ} (hu : 0 ≤ u) : F u 197 ≤ 197 * (7198 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t197

theorem e198 {u : ℝ} (hu : 0 ≤ u) : F u 198 ≤ 198 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t198

theorem e199 {u : ℝ} (hu : 0 ≤ u) : F u 199 ≤ 199 * (7083 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t199

theorem e200 {u : ℝ} (hu : 0 ≤ u) : F u 200 ≤ 200 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t200

theorem e201 {u : ℝ} (hu : 0 ≤ u) : F u 201 ≤ 201 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t201

theorem e202 {u : ℝ} (hu : 0 ≤ u) : F u 202 ≤ 202 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t202

theorem e203 {u : ℝ} (hu : 0 ≤ u) : F u 203 ≤ 203 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t203

theorem e204 {u : ℝ} (hu : 0 ≤ u) : F u 204 ≤ 204 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t204

theorem e205 {u : ℝ} (hu : 0 ≤ u) : F u 205 ≤ 205 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t205

theorem e206 {u : ℝ} (hu : 0 ≤ u) : F u 206 ≤ 206 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t206

theorem e207 {u : ℝ} (hu : 0 ≤ u) : F u 207 ≤ 207 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t207

theorem e208 {u : ℝ} (hu : 0 ≤ u) : F u 208 ≤ 208 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t208

theorem e209 {u : ℝ} (hu : 0 ≤ u) : F u 209 ≤ 209 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t209

theorem e210 {u : ℝ} (hu : 0 ≤ u) : F u 210 ≤ 210 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t210

theorem e211 {u : ℝ} (hu : 0 ≤ u) : F u 211 ≤ 211 * (6443 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t211

theorem e212 {u : ℝ} (hu : 0 ≤ u) : F u 212 ≤ 212 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t212

theorem e213 {u : ℝ} (hu : 0 ≤ u) : F u 213 ≤ 213 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t213

theorem e214 {u : ℝ} (hu : 0 ≤ u) : F u 214 ≤ 214 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t214

theorem e215 {u : ℝ} (hu : 0 ≤ u) : F u 215 ≤ 215 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t215

theorem e216 {u : ℝ} (hu : 0 ≤ u) : F u 216 ≤ 216 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t216

theorem e217 {u : ℝ} (hu : 0 ≤ u) : F u 217 ≤ 217 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t217

theorem e218 {u : ℝ} (hu : 0 ≤ u) : F u 218 ≤ 218 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t218

theorem e219 {u : ℝ} (hu : 0 ≤ u) : F u 219 ≤ 219 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t219

theorem e220 {u : ℝ} (hu : 0 ≤ u) : F u 220 ≤ 220 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t220

theorem e221 {u : ℝ} (hu : 0 ≤ u) : F u 221 ≤ 221 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t221

theorem e222 {u : ℝ} (hu : 0 ≤ u) : F u 222 ≤ 222 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t222

theorem e223 {u : ℝ} (hu : 0 ≤ u) : F u 223 ≤ 223 * (5886 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t223

theorem e224 {u : ℝ} (hu : 0 ≤ u) : F u 224 ≤ 224 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t224

theorem e225 {u : ℝ} (hu : 0 ≤ u) : F u 225 ≤ 225 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t225

theorem e226 {u : ℝ} (hu : 0 ≤ u) : F u 226 ≤ 226 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t226

theorem e227 {u : ℝ} (hu : 0 ≤ u) : F u 227 ≤ 227 * (5714 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t227

theorem e228 {u : ℝ} (hu : 0 ≤ u) : F u 228 ≤ 228 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t228

theorem e229 {u : ℝ} (hu : 0 ≤ u) : F u 229 ≤ 229 * (5637 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t229

theorem e230 {u : ℝ} (hu : 0 ≤ u) : F u 230 ≤ 230 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t230

theorem e231 {u : ℝ} (hu : 0 ≤ u) : F u 231 ≤ 231 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t231

theorem e232 {u : ℝ} (hu : 0 ≤ u) : F u 232 ≤ 232 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t232

theorem e233 {u : ℝ} (hu : 0 ≤ u) : F u 233 ≤ 233 * (5478 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t233

theorem e234 {u : ℝ} (hu : 0 ≤ u) : F u 234 ≤ 234 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t234

theorem e235 {u : ℝ} (hu : 0 ≤ u) : F u 235 ≤ 235 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t235

theorem e236 {u : ℝ} (hu : 0 ≤ u) : F u 236 ≤ 236 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t236

theorem e237 {u : ℝ} (hu : 0 ≤ u) : F u 237 ≤ 237 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t237

theorem e238 {u : ℝ} (hu : 0 ≤ u) : F u 238 ≤ 238 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t238

theorem e239 {u : ℝ} (hu : 0 ≤ u) : F u 239 ≤ 239 * (5258 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t239

theorem e240 {u : ℝ} (hu : 0 ≤ u) : F u 240 ≤ 240 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t240

theorem e241 {u : ℝ} (hu : 0 ≤ u) : F u 241 ≤ 241 * (5182 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t241

theorem e242 {u : ℝ} (hu : 0 ≤ u) : F u 242 ≤ 242 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t242

theorem e243 {u : ℝ} (hu : 0 ≤ u) : F u 243 ≤ 243 * (205 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t243

theorem e244 {u : ℝ} (hu : 0 ≤ u) : F u 244 ≤ 244 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t244

theorem e245 {u : ℝ} (hu : 0 ≤ u) : F u 245 ≤ 245 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t245

theorem e246 {u : ℝ} (hu : 0 ≤ u) : F u 246 ≤ 246 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t246

theorem e247 {u : ℝ} (hu : 0 ≤ u) : F u 247 ≤ 247 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t247

theorem e248 {u : ℝ} (hu : 0 ≤ u) : F u 248 ≤ 248 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t248

theorem e249 {u : ℝ} (hu : 0 ≤ u) : F u 249 ≤ 249 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t249

theorem e250 {u : ℝ} (hu : 0 ≤ u) : F u 250 ≤ 250 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t250

theorem e251 {u : ℝ} (hu : 0 ≤ u) : F u 251 ≤ 251 * (4853 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t251

theorem e252 {u : ℝ} (hu : 0 ≤ u) : F u 252 ≤ 252 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t252

theorem e253 {u : ℝ} (hu : 0 ≤ u) : F u 253 ≤ 253 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t253

theorem e254 {u : ℝ} (hu : 0 ≤ u) : F u 254 ≤ 254 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t254

theorem e255 {u : ℝ} (hu : 0 ≤ u) : F u 255 ≤ 255 * (0 / 10000000) * q u ^ 7 :=
  hterm hu (by norm_num) L5Lam.t255

theorem e256 {u : ℝ} (hu : 0 ≤ u) : F u 256 ≤ 256 * (74 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t256

theorem e257 {u : ℝ} (hu : 0 ≤ u) : F u 257 ≤ 257 * (4665 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t257

theorem e258 {u : ℝ} (hu : 0 ≤ u) : F u 258 ≤ 258 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t258

theorem e259 {u : ℝ} (hu : 0 ≤ u) : F u 259 ≤ 259 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t259

theorem e260 {u : ℝ} (hu : 0 ≤ u) : F u 260 ≤ 260 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t260

theorem e261 {u : ℝ} (hu : 0 ≤ u) : F u 261 ≤ 261 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t261

theorem e262 {u : ℝ} (hu : 0 ≤ u) : F u 262 ≤ 262 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t262

theorem e263 {u : ℝ} (hu : 0 ≤ u) : F u 263 ≤ 263 * (4490 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t263

theorem e264 {u : ℝ} (hu : 0 ≤ u) : F u 264 ≤ 264 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t264

theorem e265 {u : ℝ} (hu : 0 ≤ u) : F u 265 ≤ 265 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t265

theorem e266 {u : ℝ} (hu : 0 ≤ u) : F u 266 ≤ 266 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t266

theorem e267 {u : ℝ} (hu : 0 ≤ u) : F u 267 ≤ 267 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t267

theorem e268 {u : ℝ} (hu : 0 ≤ u) : F u 268 ≤ 268 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t268

theorem e269 {u : ℝ} (hu : 0 ≤ u) : F u 269 ≤ 269 * (4333 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t269

theorem e270 {u : ℝ} (hu : 0 ≤ u) : F u 270 ≤ 270 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t270

theorem e271 {u : ℝ} (hu : 0 ≤ u) : F u 271 ≤ 271 * (4278 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t271

theorem e272 {u : ℝ} (hu : 0 ≤ u) : F u 272 ≤ 272 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t272

theorem e273 {u : ℝ} (hu : 0 ≤ u) : F u 273 ≤ 273 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t273

theorem e274 {u : ℝ} (hu : 0 ≤ u) : F u 274 ≤ 274 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t274

theorem e275 {u : ℝ} (hu : 0 ≤ u) : F u 275 ≤ 275 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t275

theorem e276 {u : ℝ} (hu : 0 ≤ u) : F u 276 ≤ 276 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t276

theorem e277 {u : ℝ} (hu : 0 ≤ u) : F u 277 ≤ 277 * (4126 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t277

theorem e278 {u : ℝ} (hu : 0 ≤ u) : F u 278 ≤ 278 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t278

theorem e279 {u : ℝ} (hu : 0 ≤ u) : F u 279 ≤ 279 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t279

theorem e280 {u : ℝ} (hu : 0 ≤ u) : F u 280 ≤ 280 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t280

theorem e281 {u : ℝ} (hu : 0 ≤ u) : F u 281 ≤ 281 * (4033 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t281

theorem e282 {u : ℝ} (hu : 0 ≤ u) : F u 282 ≤ 282 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t282

theorem e283 {u : ℝ} (hu : 0 ≤ u) : F u 283 ≤ 283 * (3984 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t283

theorem e284 {u : ℝ} (hu : 0 ≤ u) : F u 284 ≤ 284 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t284

theorem e285 {u : ℝ} (hu : 0 ≤ u) : F u 285 ≤ 285 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t285

theorem e286 {u : ℝ} (hu : 0 ≤ u) : F u 286 ≤ 286 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t286

theorem e287 {u : ℝ} (hu : 0 ≤ u) : F u 287 ≤ 287 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t287

theorem e288 {u : ℝ} (hu : 0 ≤ u) : F u 288 ≤ 288 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t288

theorem e289 {u : ℝ} (hu : 0 ≤ u) : F u 289 ≤ 289 * (965 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t289

theorem e290 {u : ℝ} (hu : 0 ≤ u) : F u 290 ≤ 290 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t290

theorem e291 {u : ℝ} (hu : 0 ≤ u) : F u 291 ≤ 291 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t291

theorem e292 {u : ℝ} (hu : 0 ≤ u) : F u 292 ≤ 292 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t292

theorem e293 {u : ℝ} (hu : 0 ≤ u) : F u 293 ≤ 293 * (3759 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t293

theorem e294 {u : ℝ} (hu : 0 ≤ u) : F u 294 ≤ 294 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t294

theorem e295 {u : ℝ} (hu : 0 ≤ u) : F u 295 ≤ 295 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t295

theorem e296 {u : ℝ} (hu : 0 ≤ u) : F u 296 ≤ 296 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t296

theorem e297 {u : ℝ} (hu : 0 ≤ u) : F u 297 ≤ 297 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t297

theorem e298 {u : ℝ} (hu : 0 ≤ u) : F u 298 ≤ 298 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t298

theorem e299 {u : ℝ} (hu : 0 ≤ u) : F u 299 ≤ 299 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t299

theorem e300 {u : ℝ} (hu : 0 ≤ u) : F u 300 ≤ 300 * (0 / 10000000) * q u ^ 8 :=
  hterm hu (by norm_num) L5Lam.t300

theorem hs1 {u : ℝ} (hu : 0 ≤ u) : HS u 1 ≤ 0 := by
  have h := HS_succ u 0
  linarith [HS_zero u, e0 hu]

theorem hs2 {u : ℝ} (hu : 0 ≤ u) : HS u 2 ≤ 0 := by
  have h := HS_succ u 1
  linarith [hs1 hu, e1 hu]

theorem hs3 {u : ℝ} (hu : 0 ≤ u) : HS u 3 ≤ 2402266 / 10000000 * q u ^ 1 := by
  have h := HS_succ u 2
  linarith [hs2 hu, e2 hu]

theorem hs4 {u : ℝ} (hu : 0 ≤ u) : HS u 4 ≤ 6430381 / 10000000 * q u ^ 1 := by
  have h := HS_succ u 3
  linarith [hs3 hu, e3 hu]

theorem hs5 {u : ℝ} (hu : 0 ≤ u) : HS u 5 ≤ 6430381 / 10000000 * q u ^ 1 + 1201136 / 10000000 * q u ^ 2 := by
  have h := HS_succ u 4
  linarith [hs4 hu, e4 hu]

theorem hs6 {u : ℝ} (hu : 0 ≤ u) : HS u 6 ≤ 6430381 / 10000000 * q u ^ 1 + 6409411 / 10000000 * q u ^ 2 := by
  have h := HS_succ u 5
  linarith [hs5 hu, e5 hu]

theorem hs7 {u : ℝ} (hu : 0 ≤ u) : HS u 7 ≤ 6430381 / 10000000 * q u ^ 1 + 6409411 / 10000000 * q u ^ 2 := by
  have h := HS_succ u 6
  linarith [hs6 hu, e6 hu]

theorem hs8 {u : ℝ} (hu : 0 ≤ u) : HS u 8 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 := by
  have h := HS_succ u 7
  linarith [hs7 hu, e7 hu]

theorem hs9 {u : ℝ} (hu : 0 ≤ u) : HS u 9 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 600568 / 10000000 * q u ^ 3 := by
  have h := HS_succ u 8
  linarith [hs8 hu, e8 hu]

theorem hs10 {u : ℝ} (hu : 0 ≤ u) : HS u 10 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 1943278 / 10000000 * q u ^ 3 := by
  have h := HS_succ u 9
  linarith [hs9 hu, e9 hu]

theorem hs11 {u : ℝ} (hu : 0 ≤ u) : HS u 11 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 1943278 / 10000000 * q u ^ 3 := by
  have h := HS_succ u 10
  linarith [hs10 hu, e10 hu]

theorem hs12 {u : ℝ} (hu : 0 ≤ u) : HS u 12 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 7175021 / 10000000 * q u ^ 3 := by
  have h := HS_succ u 11
  linarith [hs11 hu, e11 hu]

theorem hs13 {u : ℝ} (hu : 0 ≤ u) : HS u 13 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 7175021 / 10000000 * q u ^ 3 := by
  have h := HS_succ u 12
  linarith [hs12 hu, e12 hu]

theorem hs14 {u : ℝ} (hu : 0 ≤ u) : HS u 14 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 := by
  have h := HS_succ u 13
  linarith [hs13 hu, e13 hu]

theorem hs15 {u : ℝ} (hu : 0 ≤ u) : HS u 15 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 := by
  have h := HS_succ u 14
  linarith [hs14 hu, e14 hu]

theorem hs16 {u : ℝ} (hu : 0 ≤ u) : HS u 16 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 := by
  have h := HS_succ u 15
  linarith [hs15 hu, e15 hu]

theorem hs17 {u : ℝ} (hu : 0 ≤ u) : HS u 17 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 300288 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 16
  linarith [hs16 hu, e16 hu]

theorem hs18 {u : ℝ} (hu : 0 ≤ u) : HS u 18 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 5036658 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 17
  linarith [hs17 hu, e17 hu]

theorem hs19 {u : ℝ} (hu : 0 ≤ u) : HS u 19 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 5036658 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 18
  linarith [hs18 hu, e18 hu]

theorem hs20 {u : ℝ} (hu : 0 ≤ u) : HS u 20 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 9604125 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 19
  linarith [hs19 hu, e19 hu]

theorem hs21 {u : ℝ} (hu : 0 ≤ u) : HS u 21 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 9604125 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 20
  linarith [hs20 hu, e20 hu]

theorem hs22 {u : ℝ} (hu : 0 ≤ u) : HS u 22 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 9604125 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 21
  linarith [hs21 hu, e21 hu]

theorem hs23 {u : ℝ} (hu : 0 ≤ u) : HS u 23 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 9604125 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 22
  linarith [hs22 hu, e22 hu]

theorem hs24 {u : ℝ} (hu : 0 ≤ u) : HS u 24 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 13893165 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 23
  linarith [hs23 hu, e23 hu]

theorem hs25 {u : ℝ} (hu : 0 ≤ u) : HS u 25 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 13893165 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 24
  linarith [hs24 hu, e24 hu]

theorem hs26 {u : ℝ} (hu : 0 ≤ u) : HS u 26 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 14934840 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 25
  linarith [hs25 hu, e25 hu]

theorem hs27 {u : ℝ} (hu : 0 ≤ u) : HS u 27 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 14934840 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 26
  linarith [hs26 hu, e26 hu]

theorem hs28 {u : ℝ} (hu : 0 ≤ u) : HS u 28 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 15382419 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 27
  linarith [hs27 hu, e27 hu]

theorem hs29 {u : ℝ} (hu : 0 ≤ u) : HS u 29 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 15382419 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 28
  linarith [hs28 hu, e28 hu]

theorem hs30 {u : ℝ} (hu : 0 ≤ u) : HS u 30 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 19294577 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 29
  linarith [hs29 hu, e29 hu]

theorem hs31 {u : ℝ} (hu : 0 ≤ u) : HS u 31 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 19294577 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 30
  linarith [hs30 hu, e30 hu]

theorem hs32 {u : ℝ} (hu : 0 ≤ u) : HS u 32 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 := by
  have h := HS_succ u 31
  linarith [hs31 hu, e31 hu]

theorem hs33 {u : ℝ} (hu : 0 ≤ u) : HS u 33 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 150144 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 32
  linarith [hs32 hu, e32 hu]

theorem hs34 {u : ℝ} (hu : 0 ≤ u) : HS u 34 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 150144 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 33
  linarith [hs33 hu, e33 hu]

theorem hs35 {u : ℝ} (hu : 0 ≤ u) : HS u 35 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 150144 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 34
  linarith [hs34 hu, e34 hu]

theorem hs36 {u : ℝ} (hu : 0 ≤ u) : HS u 36 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 150144 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 35
  linarith [hs35 hu, e35 hu]

theorem hs37 {u : ℝ} (hu : 0 ≤ u) : HS u 37 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 150144 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 36
  linarith [hs36 hu, e36 hu]

theorem hs38 {u : ℝ} (hu : 0 ≤ u) : HS u 38 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 3676133 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 37
  linarith [hs37 hu, e37 hu]

theorem hs39 {u : ℝ} (hu : 0 ≤ u) : HS u 39 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 3676133 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 38
  linarith [hs38 hu, e38 hu]

theorem hs40 {u : ℝ} (hu : 0 ≤ u) : HS u 40 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 3676133 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 39
  linarith [hs39 hu, e39 hu]

theorem hs41 {u : ℝ} (hu : 0 ≤ u) : HS u 41 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 3676133 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 40
  linarith [hs40 hu, e40 hu]

theorem hs42 {u : ℝ} (hu : 0 ≤ u) : HS u 42 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 7042028 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 41
  linarith [hs41 hu, e41 hu]

theorem hs43 {u : ℝ} (hu : 0 ≤ u) : HS u 43 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 7042028 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 42
  linarith [hs42 hu, e42 hu]

theorem hs44 {u : ℝ} (hu : 0 ≤ u) : HS u 44 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 10336129 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 43
  linarith [hs43 hu, e43 hu]

theorem hs45 {u : ℝ} (hu : 0 ≤ u) : HS u 45 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 10336129 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 44
  linarith [hs44 hu, e44 hu]

theorem hs46 {u : ℝ} (hu : 0 ≤ u) : HS u 46 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 10336129 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 45
  linarith [hs45 hu, e45 hu]

theorem hs47 {u : ℝ} (hu : 0 ≤ u) : HS u 47 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 10336129 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 46
  linarith [hs46 hu, e46 hu]

theorem hs48 {u : ℝ} (hu : 0 ≤ u) : HS u 48 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 13490252 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 47
  linarith [hs47 hu, e47 hu]

theorem hs49 {u : ℝ} (hu : 0 ≤ u) : HS u 49 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 13490252 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 48
  linarith [hs48 hu, e48 hu]

theorem hs50 {u : ℝ} (hu : 0 ≤ u) : HS u 50 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 14265873 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 49
  linarith [hs49 hu, e49 hu]

theorem hs51 {u : ℝ} (hu : 0 ≤ u) : HS u 51 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 14265873 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 50
  linarith [hs50 hu, e50 hu]

theorem hs52 {u : ℝ} (hu : 0 ≤ u) : HS u 52 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 14265873 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 51
  linarith [hs51 hu, e51 hu]

theorem hs53 {u : ℝ} (hu : 0 ≤ u) : HS u 53 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 14265873 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 52
  linarith [hs52 hu, e52 hu]

theorem hs54 {u : ℝ} (hu : 0 ≤ u) : HS u 54 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 17246805 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 53
  linarith [hs53 hu, e53 hu]

theorem hs55 {u : ℝ} (hu : 0 ≤ u) : HS u 55 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 17246805 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 54
  linarith [hs54 hu, e54 hu]

theorem hs56 {u : ℝ} (hu : 0 ≤ u) : HS u 56 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 17246805 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 55
  linarith [hs55 hu, e55 hu]

theorem hs57 {u : ℝ} (hu : 0 ≤ u) : HS u 57 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 17246805 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 56
  linarith [hs56 hu, e56 hu]

theorem hs58 {u : ℝ} (hu : 0 ≤ u) : HS u 58 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 17246805 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 57
  linarith [hs57 hu, e57 hu]

theorem hs59 {u : ℝ} (hu : 0 ≤ u) : HS u 59 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 17246805 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 58
  linarith [hs58 hu, e58 hu]

theorem hs60 {u : ℝ} (hu : 0 ≤ u) : HS u 60 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 20064999 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 59
  linarith [hs59 hu, e59 hu]

theorem hs61 {u : ℝ} (hu : 0 ≤ u) : HS u 61 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 20064999 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 60
  linarith [hs60 hu, e60 hu]

theorem hs62 {u : ℝ} (hu : 0 ≤ u) : HS u 62 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 61
  linarith [hs61 hu, e61 hu]

theorem hs63 {u : ℝ} (hu : 0 ≤ u) : HS u 63 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 62
  linarith [hs62 hu, e62 hu]

theorem hs64 {u : ℝ} (hu : 0 ≤ u) : HS u 64 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 := by
  have h := HS_succ u 63
  linarith [hs63 hu, e63 hu]

theorem hs65 {u : ℝ} (hu : 0 ≤ u) : HS u 65 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 75072 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 64
  linarith [hs64 hu, e64 hu]

theorem hs66 {u : ℝ} (hu : 0 ≤ u) : HS u 66 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 75072 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 65
  linarith [hs65 hu, e65 hu]

theorem hs67 {u : ℝ} (hu : 0 ≤ u) : HS u 67 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 75072 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 66
  linarith [hs66 hu, e66 hu]

theorem hs68 {u : ℝ} (hu : 0 ≤ u) : HS u 68 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 2717485 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 67
  linarith [hs67 hu, e67 hu]

theorem hs69 {u : ℝ} (hu : 0 ≤ u) : HS u 69 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 2717485 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 68
  linarith [hs68 hu, e68 hu]

theorem hs70 {u : ℝ} (hu : 0 ≤ u) : HS u 70 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 2717485 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 69
  linarith [hs69 hu, e69 hu]

theorem hs71 {u : ℝ} (hu : 0 ≤ u) : HS u 71 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 2717485 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 70
  linarith [hs70 hu, e70 hu]

theorem hs72 {u : ℝ} (hu : 0 ≤ u) : HS u 72 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 5282147 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 71
  linarith [hs71 hu, e71 hu]

theorem hs73 {u : ℝ} (hu : 0 ≤ u) : HS u 73 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 5282147 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 72
  linarith [hs72 hu, e72 hu]

theorem hs74 {u : ℝ} (hu : 0 ≤ u) : HS u 74 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 7808312 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 73
  linarith [hs73 hu, e73 hu]

theorem hs75 {u : ℝ} (hu : 0 ≤ u) : HS u 75 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 7808312 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 74
  linarith [hs74 hu, e74 hu]

theorem hs76 {u : ℝ} (hu : 0 ≤ u) : HS u 76 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 7808312 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 75
  linarith [hs75 hu, e75 hu]

theorem hs77 {u : ℝ} (hu : 0 ≤ u) : HS u 77 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 7808312 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 76
  linarith [hs76 hu, e76 hu]

theorem hs78 {u : ℝ} (hu : 0 ≤ u) : HS u 78 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 7808312 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 77
  linarith [hs77 hu, e77 hu]

theorem hs79 {u : ℝ} (hu : 0 ≤ u) : HS u 79 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 7808312 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 78
  linarith [hs78 hu, e78 hu]

theorem hs80 {u : ℝ} (hu : 0 ≤ u) : HS u 80 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 10225791 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 79
  linarith [hs79 hu, e79 hu]

theorem hs81 {u : ℝ} (hu : 0 ≤ u) : HS u 81 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 10225791 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 80
  linarith [hs80 hu, e80 hu]

theorem hs82 {u : ℝ} (hu : 0 ≤ u) : HS u 82 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 10374993 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 81
  linarith [hs81 hu, e81 hu]

theorem hs83 {u : ℝ} (hu : 0 ≤ u) : HS u 83 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 10374993 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 82
  linarith [hs82 hu, e82 hu]

theorem hs84 {u : ℝ} (hu : 0 ≤ u) : HS u 84 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 12733355 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 83
  linarith [hs83 hu, e83 hu]

theorem hs85 {u : ℝ} (hu : 0 ≤ u) : HS u 85 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 12733355 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 84
  linarith [hs84 hu, e84 hu]

theorem hs86 {u : ℝ} (hu : 0 ≤ u) : HS u 86 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 12733355 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 85
  linarith [hs85 hu, e85 hu]

theorem hs87 {u : ℝ} (hu : 0 ≤ u) : HS u 87 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 12733355 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 86
  linarith [hs86 hu, e86 hu]

theorem hs88 {u : ℝ} (hu : 0 ≤ u) : HS u 88 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 12733355 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 87
  linarith [hs87 hu, e87 hu]

theorem hs89 {u : ℝ} (hu : 0 ≤ u) : HS u 89 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 12733355 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 88
  linarith [hs88 hu, e88 hu]

theorem hs90 {u : ℝ} (hu : 0 ≤ u) : HS u 90 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 14997782 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 89
  linarith [hs89 hu, e89 hu]

theorem hs91 {u : ℝ} (hu : 0 ≤ u) : HS u 91 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 14997782 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 90
  linarith [hs90 hu, e90 hu]

theorem hs92 {u : ℝ} (hu : 0 ≤ u) : HS u 92 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 14997782 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 91
  linarith [hs91 hu, e91 hu]

theorem hs93 {u : ℝ} (hu : 0 ≤ u) : HS u 93 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 14997782 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 92
  linarith [hs92 hu, e92 hu]

theorem hs94 {u : ℝ} (hu : 0 ≤ u) : HS u 94 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 14997782 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 93
  linarith [hs93 hu, e93 hu]

theorem hs95 {u : ℝ} (hu : 0 ≤ u) : HS u 95 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 14997782 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 94
  linarith [hs94 hu, e94 hu]

theorem hs96 {u : ℝ} (hu : 0 ≤ u) : HS u 96 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 14997782 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 95
  linarith [hs95 hu, e95 hu]

theorem hs97 {u : ℝ} (hu : 0 ≤ u) : HS u 97 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 14997782 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 96
  linarith [hs96 hu, e96 hu]

theorem hs98 {u : ℝ} (hu : 0 ≤ u) : HS u 98 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 17156420 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 97
  linarith [hs97 hu, e97 hu]

theorem hs99 {u : ℝ} (hu : 0 ≤ u) : HS u 99 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 17156420 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 98
  linarith [hs98 hu, e98 hu]

theorem hs100 {u : ℝ} (hu : 0 ≤ u) : HS u 100 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 17156420 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 99
  linarith [hs99 hu, e99 hu]

theorem hs101 {u : ℝ} (hu : 0 ≤ u) : HS u 101 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 17156420 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 100
  linarith [hs100 hu, e100 hu]

theorem hs102 {u : ℝ} (hu : 0 ≤ u) : HS u 102 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 19269037 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 101
  linarith [hs101 hu, e101 hu]

theorem hs103 {u : ℝ} (hu : 0 ≤ u) : HS u 103 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 19269037 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 102
  linarith [hs102 hu, e102 hu]

theorem hs104 {u : ℝ} (hu : 0 ≤ u) : HS u 104 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 21355199 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 103
  linarith [hs103 hu, e103 hu]

theorem hs105 {u : ℝ} (hu : 0 ≤ u) : HS u 105 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 21355199 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 104
  linarith [hs104 hu, e104 hu]

theorem hs106 {u : ℝ} (hu : 0 ≤ u) : HS u 106 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 21355199 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 105
  linarith [hs105 hu, e105 hu]

theorem hs107 {u : ℝ} (hu : 0 ≤ u) : HS u 107 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 21355199 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 106
  linarith [hs106 hu, e106 hu]

theorem hs108 {u : ℝ} (hu : 0 ≤ u) : HS u 108 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 23396331 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 107
  linarith [hs107 hu, e107 hu]

theorem hs109 {u : ℝ} (hu : 0 ≤ u) : HS u 109 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 23396331 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 108
  linarith [hs108 hu, e108 hu]

theorem hs110 {u : ℝ} (hu : 0 ≤ u) : HS u 110 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 25418717 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 109
  linarith [hs109 hu, e109 hu]

theorem hs111 {u : ℝ} (hu : 0 ≤ u) : HS u 111 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 25418717 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 110
  linarith [hs110 hu, e110 hu]

theorem hs112 {u : ℝ} (hu : 0 ≤ u) : HS u 112 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 25418717 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 111
  linarith [hs111 hu, e111 hu]

theorem hs113 {u : ℝ} (hu : 0 ≤ u) : HS u 113 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 25418717 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 112
  linarith [hs112 hu, e112 hu]

theorem hs114 {u : ℝ} (hu : 0 ≤ u) : HS u 114 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27396556 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 113
  linarith [hs113 hu, e113 hu]

theorem hs115 {u : ℝ} (hu : 0 ≤ u) : HS u 115 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27396556 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 114
  linarith [hs114 hu, e114 hu]

theorem hs116 {u : ℝ} (hu : 0 ≤ u) : HS u 116 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27396556 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 115
  linarith [hs115 hu, e115 hu]

theorem hs117 {u : ℝ} (hu : 0 ≤ u) : HS u 117 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27396556 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 116
  linarith [hs116 hu, e116 hu]

theorem hs118 {u : ℝ} (hu : 0 ≤ u) : HS u 118 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27396556 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 117
  linarith [hs117 hu, e117 hu]

theorem hs119 {u : ℝ} (hu : 0 ≤ u) : HS u 119 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27396556 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 118
  linarith [hs118 hu, e118 hu]

theorem hs120 {u : ℝ} (hu : 0 ≤ u) : HS u 120 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27396556 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 119
  linarith [hs119 hu, e119 hu]

theorem hs121 {u : ℝ} (hu : 0 ≤ u) : HS u 121 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27396556 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 120
  linarith [hs120 hu, e120 hu]

theorem hs122 {u : ℝ} (hu : 0 ≤ u) : HS u 122 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27872207 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 121
  linarith [hs121 hu, e121 hu]

theorem hs123 {u : ℝ} (hu : 0 ≤ u) : HS u 123 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27872207 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 122
  linarith [hs122 hu, e122 hu]

theorem hs124 {u : ℝ} (hu : 0 ≤ u) : HS u 124 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27872207 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 123
  linarith [hs123 hu, e123 hu]

theorem hs125 {u : ℝ} (hu : 0 ≤ u) : HS u 125 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 27872207 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 124
  linarith [hs124 hu, e124 hu]

theorem hs126 {u : ℝ} (hu : 0 ≤ u) : HS u 126 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 28080582 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 125
  linarith [hs125 hu, e125 hu]

theorem hs127 {u : ℝ} (hu : 0 ≤ u) : HS u 127 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 28080582 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 126
  linarith [hs126 hu, e126 hu]

theorem hs128 {u : ℝ} (hu : 0 ≤ u) : HS u 128 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 := by
  have h := HS_succ u 127
  linarith [hs127 hu, e127 hu]

theorem hs129 {u : ℝ} (hu : 0 ≤ u) : HS u 129 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 37632 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 128
  linarith [hs128 hu, e128 hu]

theorem hs130 {u : ℝ} (hu : 0 ≤ u) : HS u 130 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 37632 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 129
  linarith [hs129 hu, e129 hu]

theorem hs131 {u : ℝ} (hu : 0 ≤ u) : HS u 131 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 37632 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 130
  linarith [hs130 hu, e130 hu]

theorem hs132 {u : ℝ} (hu : 0 ≤ u) : HS u 132 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 1854864 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 131
  linarith [hs131 hu, e131 hu]

theorem hs133 {u : ℝ} (hu : 0 ≤ u) : HS u 133 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 1854864 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 132
  linarith [hs132 hu, e132 hu]

theorem hs134 {u : ℝ} (hu : 0 ≤ u) : HS u 134 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 1854864 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 133
  linarith [hs133 hu, e133 hu]

theorem hs135 {u : ℝ} (hu : 0 ≤ u) : HS u 135 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 1854864 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 134
  linarith [hs134 hu, e134 hu]

theorem hs136 {u : ℝ} (hu : 0 ≤ u) : HS u 136 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 1854864 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 135
  linarith [hs135 hu, e135 hu]

theorem hs137 {u : ℝ} (hu : 0 ≤ u) : HS u 137 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 1854864 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 136
  linarith [hs136 hu, e136 hu]

theorem hs138 {u : ℝ} (hu : 0 ≤ u) : HS u 138 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 3623534 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 137
  linarith [hs137 hu, e137 hu]

theorem hs139 {u : ℝ} (hu : 0 ≤ u) : HS u 139 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 3623534 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 138
  linarith [hs138 hu, e138 hu]

theorem hs140 {u : ℝ} (hu : 0 ≤ u) : HS u 140 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 5378270 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 139
  linarith [hs139 hu, e139 hu]

theorem hs141 {u : ℝ} (hu : 0 ≤ u) : HS u 141 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 5378270 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 140
  linarith [hs140 hu, e140 hu]

theorem hs142 {u : ℝ} (hu : 0 ≤ u) : HS u 142 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 5378270 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 141
  linarith [hs141 hu, e141 hu]

theorem hs143 {u : ℝ} (hu : 0 ≤ u) : HS u 143 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 5378270 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 142
  linarith [hs142 hu, e142 hu]

theorem hs144 {u : ℝ} (hu : 0 ≤ u) : HS u 144 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 5378270 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 143
  linarith [hs143 hu, e143 hu]

theorem hs145 {u : ℝ} (hu : 0 ≤ u) : HS u 145 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 5378270 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 144
  linarith [hs144 hu, e144 hu]

theorem hs146 {u : ℝ} (hu : 0 ≤ u) : HS u 146 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 5378270 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 145
  linarith [hs145 hu, e145 hu]

theorem hs147 {u : ℝ} (hu : 0 ≤ u) : HS u 147 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 5378270 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 146
  linarith [hs146 hu, e146 hu]

theorem hs148 {u : ℝ} (hu : 0 ≤ u) : HS u 148 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 5378270 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 147
  linarith [hs147 hu, e147 hu]

theorem hs149 {u : ℝ} (hu : 0 ≤ u) : HS u 149 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 5378270 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 148
  linarith [hs148 hu, e148 hu]

theorem hs150 {u : ℝ} (hu : 0 ≤ u) : HS u 150 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 7062268 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 149
  linarith [hs149 hu, e149 hu]

theorem hs151 {u : ℝ} (hu : 0 ≤ u) : HS u 151 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 7062268 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 150
  linarith [hs150 hu, e150 hu]

theorem hs152 {u : ℝ} (hu : 0 ≤ u) : HS u 152 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 8731120 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 151
  linarith [hs151 hu, e151 hu]

theorem hs153 {u : ℝ} (hu : 0 ≤ u) : HS u 153 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 8731120 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 152
  linarith [hs152 hu, e152 hu]

theorem hs154 {u : ℝ} (hu : 0 ≤ u) : HS u 154 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 8731120 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 153
  linarith [hs153 hu, e153 hu]

theorem hs155 {u : ℝ} (hu : 0 ≤ u) : HS u 155 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 8731120 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 154
  linarith [hs154 hu, e154 hu]

theorem hs156 {u : ℝ} (hu : 0 ≤ u) : HS u 156 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 8731120 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 155
  linarith [hs155 hu, e155 hu]

theorem hs157 {u : ℝ} (hu : 0 ≤ u) : HS u 157 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 8731120 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 156
  linarith [hs156 hu, e156 hu]

theorem hs158 {u : ℝ} (hu : 0 ≤ u) : HS u 158 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 10360623 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 157
  linarith [hs157 hu, e157 hu]

theorem hs159 {u : ℝ} (hu : 0 ≤ u) : HS u 159 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 10360623 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 158
  linarith [hs158 hu, e158 hu]

theorem hs160 {u : ℝ} (hu : 0 ≤ u) : HS u 160 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 10360623 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 159
  linarith [hs159 hu, e159 hu]

theorem hs161 {u : ℝ} (hu : 0 ≤ u) : HS u 161 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 10360623 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 160
  linarith [hs160 hu, e160 hu]

theorem hs162 {u : ℝ} (hu : 0 ≤ u) : HS u 162 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 10360623 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 161
  linarith [hs161 hu, e161 hu]

theorem hs163 {u : ℝ} (hu : 0 ≤ u) : HS u 163 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 10360623 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 162
  linarith [hs162 hu, e162 hu]

theorem hs164 {u : ℝ} (hu : 0 ≤ u) : HS u 164 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 11953785 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 163
  linarith [hs163 hu, e163 hu]

theorem hs165 {u : ℝ} (hu : 0 ≤ u) : HS u 165 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 11953785 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 164
  linarith [hs164 hu, e164 hu]

theorem hs166 {u : ℝ} (hu : 0 ≤ u) : HS u 166 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 11953785 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 165
  linarith [hs165 hu, e165 hu]

theorem hs167 {u : ℝ} (hu : 0 ≤ u) : HS u 167 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 11953785 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 166
  linarith [hs166 hu, e166 hu]

theorem hs168 {u : ℝ} (hu : 0 ≤ u) : HS u 168 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 13525255 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 167
  linarith [hs167 hu, e167 hu]

theorem hs169 {u : ℝ} (hu : 0 ≤ u) : HS u 169 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 13525255 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 168
  linarith [hs168 hu, e168 hu]

theorem hs170 {u : ℝ} (hu : 0 ≤ u) : HS u 170 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 13915138 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 169
  linarith [hs169 hu, e169 hu]

theorem hs171 {u : ℝ} (hu : 0 ≤ u) : HS u 171 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 13915138 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 170
  linarith [hs170 hu, e170 hu]

theorem hs172 {u : ℝ} (hu : 0 ≤ u) : HS u 172 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 13915138 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 171
  linarith [hs171 hu, e171 hu]

theorem hs173 {u : ℝ} (hu : 0 ≤ u) : HS u 173 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 13915138 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 172
  linarith [hs172 hu, e172 hu]

theorem hs174 {u : ℝ} (hu : 0 ≤ u) : HS u 174 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 15451378 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 173
  linarith [hs173 hu, e173 hu]

theorem hs175 {u : ℝ} (hu : 0 ≤ u) : HS u 175 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 15451378 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 174
  linarith [hs174 hu, e174 hu]

theorem hs176 {u : ℝ} (hu : 0 ≤ u) : HS u 176 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 15451378 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 175
  linarith [hs175 hu, e175 hu]

theorem hs177 {u : ℝ} (hu : 0 ≤ u) : HS u 177 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 15451378 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 176
  linarith [hs176 hu, e176 hu]

theorem hs178 {u : ℝ} (hu : 0 ≤ u) : HS u 178 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 15451378 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 177
  linarith [hs177 hu, e177 hu]

theorem hs179 {u : ℝ} (hu : 0 ≤ u) : HS u 179 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 15451378 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 178
  linarith [hs178 hu, e178 hu]

theorem hs180 {u : ℝ} (hu : 0 ≤ u) : HS u 180 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 16954978 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 179
  linarith [hs179 hu, e179 hu]

theorem hs181 {u : ℝ} (hu : 0 ≤ u) : HS u 181 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 16954978 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 180
  linarith [hs180 hu, e180 hu]

theorem hs182 {u : ℝ} (hu : 0 ≤ u) : HS u 182 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 18448228 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 181
  linarith [hs181 hu, e181 hu]

theorem hs183 {u : ℝ} (hu : 0 ≤ u) : HS u 183 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 18448228 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 182
  linarith [hs182 hu, e182 hu]

theorem hs184 {u : ℝ} (hu : 0 ≤ u) : HS u 184 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 18448228 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 183
  linarith [hs183 hu, e183 hu]

theorem hs185 {u : ℝ} (hu : 0 ≤ u) : HS u 185 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 18448228 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 184
  linarith [hs184 hu, e184 hu]

theorem hs186 {u : ℝ} (hu : 0 ≤ u) : HS u 186 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 18448228 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 185
  linarith [hs185 hu, e185 hu]

theorem hs187 {u : ℝ} (hu : 0 ≤ u) : HS u 187 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 18448228 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 186
  linarith [hs186 hu, e186 hu]

theorem hs188 {u : ℝ} (hu : 0 ≤ u) : HS u 188 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 18448228 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 187
  linarith [hs187 hu, e187 hu]

theorem hs189 {u : ℝ} (hu : 0 ≤ u) : HS u 189 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 18448228 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 188
  linarith [hs188 hu, e188 hu]

theorem hs190 {u : ℝ} (hu : 0 ≤ u) : HS u 190 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 18448228 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 189
  linarith [hs189 hu, e189 hu]

theorem hs191 {u : ℝ} (hu : 0 ≤ u) : HS u 191 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 18448228 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 190
  linarith [hs190 hu, e190 hu]

theorem hs192 {u : ℝ} (hu : 0 ≤ u) : HS u 192 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 19892952 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 191
  linarith [hs191 hu, e191 hu]

theorem hs193 {u : ℝ} (hu : 0 ≤ u) : HS u 193 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 19892952 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 192
  linarith [hs192 hu, e192 hu]

theorem hs194 {u : ℝ} (hu : 0 ≤ u) : HS u 194 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 21328486 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 193
  linarith [hs193 hu, e193 hu]

theorem hs195 {u : ℝ} (hu : 0 ≤ u) : HS u 195 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 21328486 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 194
  linarith [hs194 hu, e194 hu]

theorem hs196 {u : ℝ} (hu : 0 ≤ u) : HS u 196 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 21328486 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 195
  linarith [hs195 hu, e195 hu]

theorem hs197 {u : ℝ} (hu : 0 ≤ u) : HS u 197 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 21328486 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 196
  linarith [hs196 hu, e196 hu]

theorem hs198 {u : ℝ} (hu : 0 ≤ u) : HS u 198 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 22746492 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 197
  linarith [hs197 hu, e197 hu]

theorem hs199 {u : ℝ} (hu : 0 ≤ u) : HS u 199 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 22746492 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 198
  linarith [hs198 hu, e198 hu]

theorem hs200 {u : ℝ} (hu : 0 ≤ u) : HS u 200 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 199
  linarith [hs199 hu, e199 hu]

theorem hs201 {u : ℝ} (hu : 0 ≤ u) : HS u 201 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 200
  linarith [hs200 hu, e200 hu]

theorem hs202 {u : ℝ} (hu : 0 ≤ u) : HS u 202 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 201
  linarith [hs201 hu, e201 hu]

theorem hs203 {u : ℝ} (hu : 0 ≤ u) : HS u 203 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 202
  linarith [hs202 hu, e202 hu]

theorem hs204 {u : ℝ} (hu : 0 ≤ u) : HS u 204 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 203
  linarith [hs203 hu, e203 hu]

theorem hs205 {u : ℝ} (hu : 0 ≤ u) : HS u 205 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 204
  linarith [hs204 hu, e204 hu]

theorem hs206 {u : ℝ} (hu : 0 ≤ u) : HS u 206 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 205
  linarith [hs205 hu, e205 hu]

theorem hs207 {u : ℝ} (hu : 0 ≤ u) : HS u 207 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 206
  linarith [hs206 hu, e206 hu]

theorem hs208 {u : ℝ} (hu : 0 ≤ u) : HS u 208 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 207
  linarith [hs207 hu, e207 hu]

theorem hs209 {u : ℝ} (hu : 0 ≤ u) : HS u 209 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 208
  linarith [hs208 hu, e208 hu]

theorem hs210 {u : ℝ} (hu : 0 ≤ u) : HS u 210 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 209
  linarith [hs209 hu, e209 hu]

theorem hs211 {u : ℝ} (hu : 0 ≤ u) : HS u 211 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 24156009 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 210
  linarith [hs210 hu, e210 hu]

theorem hs212 {u : ℝ} (hu : 0 ≤ u) : HS u 212 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 211
  linarith [hs211 hu, e211 hu]

theorem hs213 {u : ℝ} (hu : 0 ≤ u) : HS u 213 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 212
  linarith [hs212 hu, e212 hu]

theorem hs214 {u : ℝ} (hu : 0 ≤ u) : HS u 214 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 213
  linarith [hs213 hu, e213 hu]

theorem hs215 {u : ℝ} (hu : 0 ≤ u) : HS u 215 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 214
  linarith [hs214 hu, e214 hu]

theorem hs216 {u : ℝ} (hu : 0 ≤ u) : HS u 216 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 215
  linarith [hs215 hu, e215 hu]

theorem hs217 {u : ℝ} (hu : 0 ≤ u) : HS u 217 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 216
  linarith [hs216 hu, e216 hu]

theorem hs218 {u : ℝ} (hu : 0 ≤ u) : HS u 218 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 217
  linarith [hs217 hu, e217 hu]

theorem hs219 {u : ℝ} (hu : 0 ≤ u) : HS u 219 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 218
  linarith [hs218 hu, e218 hu]

theorem hs220 {u : ℝ} (hu : 0 ≤ u) : HS u 220 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 219
  linarith [hs219 hu, e219 hu]

theorem hs221 {u : ℝ} (hu : 0 ≤ u) : HS u 221 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 220
  linarith [hs220 hu, e220 hu]

theorem hs222 {u : ℝ} (hu : 0 ≤ u) : HS u 222 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 221
  linarith [hs221 hu, e221 hu]

theorem hs223 {u : ℝ} (hu : 0 ≤ u) : HS u 223 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 25515482 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 222
  linarith [hs222 hu, e222 hu]

theorem hs224 {u : ℝ} (hu : 0 ≤ u) : HS u 224 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 26828060 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 223
  linarith [hs223 hu, e223 hu]

theorem hs225 {u : ℝ} (hu : 0 ≤ u) : HS u 225 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 26828060 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 224
  linarith [hs224 hu, e224 hu]

theorem hs226 {u : ℝ} (hu : 0 ≤ u) : HS u 226 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 26828060 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 225
  linarith [hs225 hu, e225 hu]

theorem hs227 {u : ℝ} (hu : 0 ≤ u) : HS u 227 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 26828060 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 226
  linarith [hs226 hu, e226 hu]

theorem hs228 {u : ℝ} (hu : 0 ≤ u) : HS u 228 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 28125138 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 227
  linarith [hs227 hu, e227 hu]

theorem hs229 {u : ℝ} (hu : 0 ≤ u) : HS u 229 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 28125138 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 228
  linarith [hs228 hu, e228 hu]

theorem hs230 {u : ℝ} (hu : 0 ≤ u) : HS u 230 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 29416011 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 229
  linarith [hs229 hu, e229 hu]

theorem hs231 {u : ℝ} (hu : 0 ≤ u) : HS u 231 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 29416011 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 230
  linarith [hs230 hu, e230 hu]

theorem hs232 {u : ℝ} (hu : 0 ≤ u) : HS u 232 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 29416011 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 231
  linarith [hs231 hu, e231 hu]

theorem hs233 {u : ℝ} (hu : 0 ≤ u) : HS u 233 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 29416011 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 232
  linarith [hs232 hu, e232 hu]

theorem hs234 {u : ℝ} (hu : 0 ≤ u) : HS u 234 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 30692385 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 233
  linarith [hs233 hu, e233 hu]

theorem hs235 {u : ℝ} (hu : 0 ≤ u) : HS u 235 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 30692385 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 234
  linarith [hs234 hu, e234 hu]

theorem hs236 {u : ℝ} (hu : 0 ≤ u) : HS u 236 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 30692385 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 235
  linarith [hs235 hu, e235 hu]

theorem hs237 {u : ℝ} (hu : 0 ≤ u) : HS u 237 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 30692385 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 236
  linarith [hs236 hu, e236 hu]

theorem hs238 {u : ℝ} (hu : 0 ≤ u) : HS u 238 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 30692385 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 237
  linarith [hs237 hu, e237 hu]

theorem hs239 {u : ℝ} (hu : 0 ≤ u) : HS u 239 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 30692385 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 238
  linarith [hs238 hu, e238 hu]

theorem hs240 {u : ℝ} (hu : 0 ≤ u) : HS u 240 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 31949047 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 239
  linarith [hs239 hu, e239 hu]

theorem hs241 {u : ℝ} (hu : 0 ≤ u) : HS u 241 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 31949047 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 240
  linarith [hs240 hu, e240 hu]

theorem hs242 {u : ℝ} (hu : 0 ≤ u) : HS u 242 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 33197909 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 241
  linarith [hs241 hu, e241 hu]

theorem hs243 {u : ℝ} (hu : 0 ≤ u) : HS u 243 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 33197909 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 242
  linarith [hs242 hu, e242 hu]

theorem hs244 {u : ℝ} (hu : 0 ≤ u) : HS u 244 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 33247724 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 243
  linarith [hs243 hu, e243 hu]

theorem hs245 {u : ℝ} (hu : 0 ≤ u) : HS u 245 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 33247724 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 244
  linarith [hs244 hu, e244 hu]

theorem hs246 {u : ℝ} (hu : 0 ≤ u) : HS u 246 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 33247724 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 245
  linarith [hs245 hu, e245 hu]

theorem hs247 {u : ℝ} (hu : 0 ≤ u) : HS u 247 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 33247724 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 246
  linarith [hs246 hu, e246 hu]

theorem hs248 {u : ℝ} (hu : 0 ≤ u) : HS u 248 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 33247724 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 247
  linarith [hs247 hu, e247 hu]

theorem hs249 {u : ℝ} (hu : 0 ≤ u) : HS u 249 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 33247724 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 248
  linarith [hs248 hu, e248 hu]

theorem hs250 {u : ℝ} (hu : 0 ≤ u) : HS u 250 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 33247724 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 249
  linarith [hs249 hu, e249 hu]

theorem hs251 {u : ℝ} (hu : 0 ≤ u) : HS u 251 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 33247724 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 250
  linarith [hs250 hu, e250 hu]

theorem hs252 {u : ℝ} (hu : 0 ≤ u) : HS u 252 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 251
  linarith [hs251 hu, e251 hu]

theorem hs253 {u : ℝ} (hu : 0 ≤ u) : HS u 253 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 252
  linarith [hs252 hu, e252 hu]

theorem hs254 {u : ℝ} (hu : 0 ≤ u) : HS u 254 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 253
  linarith [hs253 hu, e253 hu]

theorem hs255 {u : ℝ} (hu : 0 ≤ u) : HS u 255 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 254
  linarith [hs254 hu, e254 hu]

theorem hs256 {u : ℝ} (hu : 0 ≤ u) : HS u 256 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 := by
  have h := HS_succ u 255
  linarith [hs255 hu, e255 hu]

theorem hs257 {u : ℝ} (hu : 0 ≤ u) : HS u 257 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 18944 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 256
  linarith [hs256 hu, e256 hu]

theorem hs258 {u : ℝ} (hu : 0 ≤ u) : HS u 258 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 1217849 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 257
  linarith [hs257 hu, e257 hu]

theorem hs259 {u : ℝ} (hu : 0 ≤ u) : HS u 259 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 1217849 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 258
  linarith [hs258 hu, e258 hu]

theorem hs260 {u : ℝ} (hu : 0 ≤ u) : HS u 260 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 1217849 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 259
  linarith [hs259 hu, e259 hu]

theorem hs261 {u : ℝ} (hu : 0 ≤ u) : HS u 261 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 1217849 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 260
  linarith [hs260 hu, e260 hu]

theorem hs262 {u : ℝ} (hu : 0 ≤ u) : HS u 262 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 1217849 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 261
  linarith [hs261 hu, e261 hu]

theorem hs263 {u : ℝ} (hu : 0 ≤ u) : HS u 263 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 1217849 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 262
  linarith [hs262 hu, e262 hu]

theorem hs264 {u : ℝ} (hu : 0 ≤ u) : HS u 264 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 2398719 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 263
  linarith [hs263 hu, e263 hu]

theorem hs265 {u : ℝ} (hu : 0 ≤ u) : HS u 265 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 2398719 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 264
  linarith [hs264 hu, e264 hu]

theorem hs266 {u : ℝ} (hu : 0 ≤ u) : HS u 266 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 2398719 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 265
  linarith [hs265 hu, e265 hu]

theorem hs267 {u : ℝ} (hu : 0 ≤ u) : HS u 267 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 2398719 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 266
  linarith [hs266 hu, e266 hu]

theorem hs268 {u : ℝ} (hu : 0 ≤ u) : HS u 268 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 2398719 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 267
  linarith [hs267 hu, e267 hu]

theorem hs269 {u : ℝ} (hu : 0 ≤ u) : HS u 269 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 2398719 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 268
  linarith [hs268 hu, e268 hu]

theorem hs270 {u : ℝ} (hu : 0 ≤ u) : HS u 270 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 3564296 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 269
  linarith [hs269 hu, e269 hu]

theorem hs271 {u : ℝ} (hu : 0 ≤ u) : HS u 271 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 3564296 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 270
  linarith [hs270 hu, e270 hu]

theorem hs272 {u : ℝ} (hu : 0 ≤ u) : HS u 272 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 4723634 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 271
  linarith [hs271 hu, e271 hu]

theorem hs273 {u : ℝ} (hu : 0 ≤ u) : HS u 273 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 4723634 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 272
  linarith [hs272 hu, e272 hu]

theorem hs274 {u : ℝ} (hu : 0 ≤ u) : HS u 274 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 4723634 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 273
  linarith [hs273 hu, e273 hu]

theorem hs275 {u : ℝ} (hu : 0 ≤ u) : HS u 275 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 4723634 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 274
  linarith [hs274 hu, e274 hu]

theorem hs276 {u : ℝ} (hu : 0 ≤ u) : HS u 276 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 4723634 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 275
  linarith [hs275 hu, e275 hu]

theorem hs277 {u : ℝ} (hu : 0 ≤ u) : HS u 277 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 4723634 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 276
  linarith [hs276 hu, e276 hu]

theorem hs278 {u : ℝ} (hu : 0 ≤ u) : HS u 278 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 5866536 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 277
  linarith [hs277 hu, e277 hu]

theorem hs279 {u : ℝ} (hu : 0 ≤ u) : HS u 279 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 5866536 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 278
  linarith [hs278 hu, e278 hu]

theorem hs280 {u : ℝ} (hu : 0 ≤ u) : HS u 280 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 5866536 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 279
  linarith [hs279 hu, e279 hu]

theorem hs281 {u : ℝ} (hu : 0 ≤ u) : HS u 281 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 5866536 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 280
  linarith [hs280 hu, e280 hu]

theorem hs282 {u : ℝ} (hu : 0 ≤ u) : HS u 282 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 6999809 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 281
  linarith [hs281 hu, e281 hu]

theorem hs283 {u : ℝ} (hu : 0 ≤ u) : HS u 283 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 6999809 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 282
  linarith [hs282 hu, e282 hu]

theorem hs284 {u : ℝ} (hu : 0 ≤ u) : HS u 284 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 8127281 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 283
  linarith [hs283 hu, e283 hu]

theorem hs285 {u : ℝ} (hu : 0 ≤ u) : HS u 285 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 8127281 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 284
  linarith [hs284 hu, e284 hu]

theorem hs286 {u : ℝ} (hu : 0 ≤ u) : HS u 286 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 8127281 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 285
  linarith [hs285 hu, e285 hu]

theorem hs287 {u : ℝ} (hu : 0 ≤ u) : HS u 287 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 8127281 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 286
  linarith [hs286 hu, e286 hu]

theorem hs288 {u : ℝ} (hu : 0 ≤ u) : HS u 288 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 8127281 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 287
  linarith [hs287 hu, e287 hu]

theorem hs289 {u : ℝ} (hu : 0 ≤ u) : HS u 289 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 8127281 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 288
  linarith [hs288 hu, e288 hu]

theorem hs290 {u : ℝ} (hu : 0 ≤ u) : HS u 290 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 8406166 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 289
  linarith [hs289 hu, e289 hu]

theorem hs291 {u : ℝ} (hu : 0 ≤ u) : HS u 291 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 8406166 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 290
  linarith [hs290 hu, e290 hu]

theorem hs292 {u : ℝ} (hu : 0 ≤ u) : HS u 292 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 8406166 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 291
  linarith [hs291 hu, e291 hu]

theorem hs293 {u : ℝ} (hu : 0 ≤ u) : HS u 293 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 8406166 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 292
  linarith [hs292 hu, e292 hu]

theorem hs294 {u : ℝ} (hu : 0 ≤ u) : HS u 294 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 9507553 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 293
  linarith [hs293 hu, e293 hu]

theorem hs295 {u : ℝ} (hu : 0 ≤ u) : HS u 295 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 9507553 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 294
  linarith [hs294 hu, e294 hu]

theorem hs296 {u : ℝ} (hu : 0 ≤ u) : HS u 296 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 9507553 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 295
  linarith [hs295 hu, e295 hu]

theorem hs297 {u : ℝ} (hu : 0 ≤ u) : HS u 297 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 9507553 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 296
  linarith [hs296 hu, e296 hu]

theorem hs298 {u : ℝ} (hu : 0 ≤ u) : HS u 298 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 9507553 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 297
  linarith [hs297 hu, e297 hu]

theorem hs299 {u : ℝ} (hu : 0 ≤ u) : HS u 299 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 9507553 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 298
  linarith [hs298 hu, e298 hu]

theorem hs300 {u : ℝ} (hu : 0 ≤ u) : HS u 300 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 9507553 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 299
  linarith [hs299 hu, e299 hu]

theorem hs301 {u : ℝ} (hu : 0 ≤ u) : HS u 301 ≤ 6430381 / 10000000 * q u ^ 1 + 11838639 / 10000000 * q u ^ 2 + 12243123 / 10000000 * q u ^ 3 + 23108910 / 10000000 * q u ^ 4 + 22841719 / 10000000 * q u ^ 5 + 29930210 / 10000000 * q u ^ 6 + 34465827 / 10000000 * q u ^ 7 + 9507553 / 10000000 * q u ^ 8 := by
  have h := HS_succ u 300
  linarith [hs300 hu, e300 hu]

/-- the head bound as a polynomial in `2^{-u}` -/
noncomputable def P (x : ℝ) : ℝ :=
  6430381 / 10000000 * x ^ 1 + 11838639 / 10000000 * x ^ 2 + 12243123 / 10000000 * x ^ 3 + 23108910 / 10000000 * x ^ 4 + 22841719 / 10000000 * x ^ 5 + 29930210 / 10000000 * x ^ 6 + 34465827 / 10000000 * x ^ 7 + 9507553 / 10000000 * x ^ 8

theorem head_le {u : ℝ} (hu : 0 ≤ u) : HS u 301 ≤ P (q u) := by
  have := hs301 hu; unfold P; linarith

theorem P_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ P x := by unfold P; positivity

theorem P_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : P x ≤ P y := by
  unfold P; gcongr

/-! ### The one variable inequality, on ten pieces of `(0, 1]` -/

theorem piece {u a b r ρ : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ u) (hb : u ≤ b)
    (hr : (2 : ℝ) ^ (-a) ≤ r) (hρ : (300 : ℝ) ^ (-a) ≤ ρ)
    (hnum : b ^ 2 * P r + 1.9 * (ρ * (1 + a * (1054 * 0.6931471808 / 128) +
      a ^ 2 * (1054 * 0.6931471808 / 128))) ≤ 2) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 := by
  have hu0 : 0 ≤ u := ha0.trans ha
  have hq : q u ≤ r :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg ha)).trans hr
  have hP := P_mono (q_nonneg u) hq
  have hP0 := P_nonneg (q_nonneg u)
  have hu2 : u ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hu0 hb 2
  have h1 : u ^ 2 * P (q u) ≤ b ^ 2 * P r := mul_le_mul hu2 hP hP0 (by positivity)
  have hphi : phi u ≤ phi a := phi_anti (Set.mem_Ici.2 ha0) (Set.mem_Ici.2 hu0) ha
  have hL := L5Lam.log_le_pow 300 1054 (by norm_num)
  push_cast at hL
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have hL0 : 0 ≤ Real.log 300 := Real.log_nonneg (by norm_num)
  have hphia : phi a ≤ ρ * (1 + a * (1054 * 0.6931471808 / 128) +
      a ^ 2 * (1054 * 0.6931471808 / 128)) := by
    unfold phi
    refine mul_le_mul hρ ?_ (by positivity) hρ0
    have := mul_le_mul_of_nonneg_left hL ha0
    have := mul_le_mul_of_nonneg_left hL (sq_nonneg a)
    linarith
  linarith

theorem pc0 {u : ℝ} (ha : (0 / 1 : ℝ) ≤ u) (hb : u ≤ (1 / 13 : ℝ)) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 :=
  piece (by norm_num) ha hb
    (root_le (r := (1 / 1 : ℝ)) 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (root_le (r := (1 / 1 : ℝ)) 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by unfold P; norm_num)

theorem pc1 {u : ℝ} (ha : (1 / 13 : ℝ) ≤ u) (hb : u ≤ (1 / 8 : ℝ)) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 :=
  piece (by norm_num) ha hb
    (root_le (r := (9481 / 10000 : ℝ)) 1 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (root_le (r := (6449 / 10000 : ℝ)) 1 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by unfold P; norm_num)

theorem pc2 {u : ℝ} (ha : (1 / 8 : ℝ) ≤ u) (hb : u ≤ (3 / 17 : ℝ)) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 :=
  piece (by norm_num) ha hb
    (root_le (r := (9171 / 10000 : ℝ)) 1 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (root_le (r := (2451 / 5000 : ℝ)) 1 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by unfold P; norm_num)

theorem pc3 {u : ℝ} (ha : (3 / 17 : ℝ) ≤ u) (hb : u ≤ (4 / 17 : ℝ)) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 :=
  piece (by norm_num) ha hb
    (root_le (r := (8849 / 10000 : ℝ)) 3 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (root_le (r := (731 / 2000 : ℝ)) 3 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by unfold P; norm_num)

theorem pc4 {u : ℝ} (ha : (4 / 17 : ℝ) ≤ u) (hb : u ≤ (5 / 16 : ℝ)) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 :=
  piece (by norm_num) ha hb
    (root_le (r := (531 / 625 : ℝ)) 4 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (root_le (r := (1307 / 5000 : ℝ)) 4 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by unfold P; norm_num)

theorem pc5 {u : ℝ} (ha : (5 / 16 : ℝ) ≤ u) (hb : u ≤ (7 / 17 : ℝ)) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 :=
  piece (by norm_num) ha hb
    (root_le (r := (8053 / 10000 : ℝ)) 5 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (root_le (r := (1683 / 10000 : ℝ)) 5 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by unfold P; norm_num)

theorem pc6 {u : ℝ} (ha : (7 / 17 : ℝ) ≤ u) (hb : u ≤ (6 / 11 : ℝ)) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 :=
  piece (by norm_num) ha hb
    (root_le (r := (3759 / 5000 : ℝ)) 7 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (root_le (r := (239 / 2500 : ℝ)) 7 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by unfold P; norm_num)

theorem pc7 {u : ℝ} (ha : (6 / 11 : ℝ) ≤ u) (hb : u ≤ (8 / 11 : ℝ)) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 :=
  piece (by norm_num) ha hb
    (root_le (r := (1713 / 2500 : ℝ)) 6 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (root_le (r := (223 / 5000 : ℝ)) 6 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by unfold P; norm_num)

theorem pc8 {u : ℝ} (ha : (8 / 11 : ℝ) ≤ u) (hb : u ≤ (19 / 20 : ℝ)) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 :=
  piece (by norm_num) ha hb
    (root_le (r := (6041 / 10000 : ℝ)) 8 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (root_le (r := (79 / 5000 : ℝ)) 8 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by unfold P; norm_num)

theorem pc9 {u : ℝ} (ha : (19 / 20 : ℝ) ≤ u) (hb : u ≤ (1 / 1 : ℝ)) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 :=
  piece (by norm_num) ha hb
    (root_le (r := (5177 / 10000 : ℝ)) 19 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (root_le (r := (9 / 2000 : ℝ)) 19 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by unfold P; norm_num)

theorem main_ineq {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    u ^ 2 * P (q u) + 1.9 * phi u ≤ 2 := by
  rcases le_total u (1 / 13) with c0 | c0
  · exact pc0 (by linarith) c0
  rcases le_total u (1 / 8) with c1 | c1
  · exact pc1 (by linarith) c1
  rcases le_total u (3 / 17) with c2 | c2
  · exact pc2 (by linarith) c2
  rcases le_total u (4 / 17) with c3 | c3
  · exact pc3 (by linarith) c3
  rcases le_total u (5 / 16) with c4 | c4
  · exact pc4 (by linarith) c4
  rcases le_total u (7 / 17) with c5 | c5
  · exact pc5 (by linarith) c5
  rcases le_total u (6 / 11) with c6 | c6
  · exact pc6 (by linarith) c6
  rcases le_total u (8 / 11) with c7 | c7
  · exact pc7 (by linarith) c7
  rcases le_total u (19 / 20) with c8 | c8
  · exact pc8 (by linarith) c8
  exact pc9 c8 (by linarith)

/-! ### The tail `n > 300` by summation by parts -/

/-- the weighted tail -/
noncomputable def Tl (u : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Ico 301 (N + 1), Λ n * g u n

theorem tail_ind {u : ℝ} (hu : 0 < u) (N : ℕ) (hN : 300 ≤ N) :
    Tl u N + (1.9 * N - ψ (N : ℝ)) * g u N ≤ 1.9 * (300 * g u 300 + G u 300 - G u N) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have : Tl u 300 = 0 := by simp [Tl]
    rw [this]
    have := psi_nonneg ((300 : ℕ) : ℝ)
    have := g_nonneg (u := u) (show (1 : ℝ) ≤ 300 by norm_num)
    push_cast at *
    nlinarith
  | succ N hN ih =>
    have hT : Tl u (N + 1) = Tl u N + Λ (N + 1) * g u ((N + 1 : ℕ) : ℝ) := by
      unfold Tl; rw [Finset.sum_Ico_succ_top (by omega)]
    have hN' : (300 : ℝ) ≤ N := by exact_mod_cast hN
    have hpsi := L5Lam.psi_succ N
    have hb := L5Lam.psi_le_19 N hN
    have ha := g_anti (u := u) (x := (N : ℝ)) (y := (N : ℝ) + 1) hu.le (by linarith) (by linarith)
    have ht := g_tel (u := u) (x := (N : ℝ)) hu (by linarith)
    rw [hT, hpsi]
    push_cast at *
    nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem tail_le {u : ℝ} (hu : 0 < u) (N : ℕ) (hN : 300 ≤ N) :
    Tl u N ≤ 1.9 * (300 * g u 300 + G u 300) := by
  have h := tail_ind hu N hN
  have hN' : (300 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 0 ≤ (1.9 * N - ψ (N : ℝ)) * g u N :=
    mul_nonneg (by linarith [L5Lam.psi_le_19 N hN]) (g_nonneg (by linarith))
  have h2 := G_nonneg hu (show (1 : ℝ) ≤ N by linarith)
  linarith

theorem F_le_lam_g {u : ℝ} {n : ℕ} (hn : 0 < n) : F u n ≤ Λ n * g u n := by
  have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  unfold F g
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)

theorem tsum_F_le {u : ℝ} (hu : 0 < u) :
    ∑' n : ℕ, F u n ≤ HS u 301 + 1.9 * (300 * g u 300 + G u 300) := by
  have hT0 : 0 ≤ 1.9 * (300 * g u 300 + G u 300) := by
    have := g_nonneg (u := u) (show (1 : ℝ) ≤ 300 by norm_num)
    have := G_nonneg hu (show (1 : ℝ) ≤ 300 by norm_num)
    positivity
  refine Real.tsum_le_of_sum_range_le (F_nonneg u) fun N => ?_
  change HS u N ≤ _
  rcases le_or_gt N 301 with hN | hN
  · have : HS u N ≤ HS u 301 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hN)
        (fun i _ _ => F_nonneg u i)
    linarith
  · obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
    have hK : 300 ≤ K := by omega
    have hsplit : HS u (K + 1) = HS u 301 + ∑ n ∈ Finset.Ico 301 (K + 1), F u n :=
      (Finset.sum_range_add_sum_Ico _ (by omega)).symm
    have htl : ∑ n ∈ Finset.Ico 301 (K + 1), F u n ≤ Tl u K :=
      Finset.sum_le_sum fun n hn => F_le_lam_g (by simp at hn; omega)
    have := tail_le hu K hK
    linarith

/-! ### `LamSq2` -/

theorem lamSq2_u {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) : ∑' n : ℕ, F u n ≤ 2 / u ^ 2 := by
  have ht := tsum_F_le h0
  have hh := head_le h0.le
  have hid := tail_identity h0
  have hm := main_ineq h0 h1
  rw [le_div_iff₀ (by positivity)]
  calc (∑' n : ℕ, F u n) * u ^ 2
      ≤ (P (q u) + 1.9 * (300 * g u 300 + G u 300)) * u ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg u)
    _ = u ^ 2 * P (q u) + u ^ 2 * (1.9 * (300 * g u 300 + G u 300)) := by ring
    _ ≤ 2 := by rw [hid]; exact hm

/-- **`LamSq2`**, PROVED: for `1 < s ≤ 2`, `Σ Λ(n)² n^{-s} ≤ 2/(s-1)²`. -/
theorem lamSq2 : L5.LamSq2 := by
  intro s hs1 hs2
  have hu : 0 < s - 1 := by linarith
  have e : ∀ n : ℕ, Λ n ^ 2 * (n : ℝ) ^ (-s) = F (s - 1) n := fun n => by
    unfold F; congr 2; ring
  rw [tsum_congr e]
  exact lamSq2_u hu (by linarith)

/-- **(21), p. 370**, PROVED, no cited input: `DiagLam2` and `LamSq2` are both discharged. -/
theorem bound21 : L5.Bound21 := L5Lam.bound21_of_lamSq lamSq2

/-- **Lemma 5, p. 368**, CONDITIONAL ON Lemma 4, `Parseval1920`, `Const4`. -/
theorem lemma5_of_L4_P_C4 (h4 : Lemma4) (hP : L5.Parseval1920) (hC : L5.Const4) : Lemma5 :=
  L5Lam.lemma5_of_lamSq h4 hP lamSq2 hC

/-- Vacuity: the range of `LamSq2` is met at `s = 3/2` and the sum there is positive, so the
bound is not about an empty or zero sum. -/
theorem lamSq2_nonvacuous :
    ∃ s : ℝ, 1 < s ∧ s ≤ 2 ∧ 0 < ∑' n : ℕ, Λ n ^ 2 * (n : ℝ) ^ (-s) := by
  refine ⟨3 / 2, by norm_num, by norm_num, ?_⟩
  refine (L5.summable_lamSq (by norm_num)).tsum_pos (fun n => by positivity) 2 ?_
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity

/-- Vacuity of the one variable inequality: at `u = 1/2` both sides are finite reals and the
pieces hypotheses hold. -/
theorem main_ineq_nonvacuous : (1 / 2 : ℝ) ^ 2 * P (q (1 / 2)) + 1.9 * phi (1 / 2) ≤ 2 :=
  main_ineq (by norm_num) (by norm_num)

end LeanLab.Kaniecki1995.L5LamSqU1382

#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.pow_q
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.root_le
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.g_anti
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.hasDerivAt_G
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.g_tel
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.G_nonneg
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.g_nonneg
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.two_le_log300
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.phi_anti
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.tail_identity
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.hterm
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.head_le
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.P_mono
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.piece
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.main_ineq
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.tail_ind
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.tail_le
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.F_le_lam_g
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.tsum_F_le
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.lamSq2_u
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.lamSq2
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.bound21
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.lemma5_of_L4_P_C4
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.lamSq2_nonvacuous
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.main_ineq_nonvacuous
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.hs301
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.pc0
#print axioms LeanLab.Kaniecki1995.L5LamSqU1382.pc9
