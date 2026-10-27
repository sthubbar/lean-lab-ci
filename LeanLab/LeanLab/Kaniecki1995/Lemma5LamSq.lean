/-
P0022, Kaniecki 1995, the input `LamSq2` of Lemma5Near21.lean, PROVED here.
PC run 20261021T1203Z-6472, unit U-1382, T1.

`LamSq2`: `Σ Λ(n)² n^{-s} ≤ 2/(s-1)²` for `1 < s ≤ 2`.
Proof. `Λ(n)² ≤ Λ(n) log n`. With `h(x) = log x · x^{-s}`, decreasing on `[3, ∞)`, and
`H(x) = x^{1-s} (log x/(s-1) + 1/(s-1)²)`, so `H' = -h` and `h(n+1) ≤ H(n) - H(n+1)` for `n ≥ 3`,
summation by parts gives, for `Σ_{n ≥ 4} Λ(n) h(n)`, the bound
`(3c - ψ(3)) h(3) + c H(3) + (1.9 - c)(H(299) + 299 h(299))`, `c = log 3`, using
`ψ(n) ≤ n log 3` for `n ≤ 299`, from `lcm(1, …, n) ≤ 3^n` checked by a kernel computation, and
`ψ(n) ≤ 1.9 n` for `n ≥ 300`, the lab's `psi_le_19`. The terms `n = 2, 3` are kept exactly.
Multiplied by `(s-1)²` the total is at most 1.987 on each of five intervals of `s - 1`,
`[0, 0.12], [0.12, 0.25], [0.25, 0.45], [0.45, 0.74], [0.74, 1]`, via `e^{-x} ≤ 1/(1+x+x²/2+x³/6)`.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5Lam

set_option exponentiation.threshold 9000

namespace LeanLab.Kaniecki1995.L5LamSq

open Real Chebyshev Set
open scoped ArithmeticFunction.vonMangoldt

/-! ### `ψ(n) ≤ n log 3` for `n ≤ 299` -/

theorem lcmUpto_succ (n : ℕ) : Nat.lcmUpto (n + 1) = Nat.lcm (Nat.lcmUpto n) (n + 1) := by
  unfold Nat.lcmUpto
  rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega, Finset.lcm_insert]
  rw [lcm_eq_nat_lcm, Nat.lcm_comm]; rfl

/-- the checker: `l = lcm(1..m)`, `p = 3^m` -/
def chk : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | k + 1, m, l, p => decide (Nat.lcm l (m + 1) ≤ 3 * p) && chk k (m + 1) (Nat.lcm l (m + 1)) (3 * p)

theorem chk_spec : ∀ k m : ℕ, Nat.lcmUpto m ≤ 3 ^ m → chk k m (Nat.lcmUpto m) (3 ^ m) = true →
    ∀ j, j ≤ k → Nat.lcmUpto (m + j) ≤ 3 ^ (m + j) := by
  intro k
  induction k with
  | zero => intro m hm _ j hj; obtain rfl : j = 0 := by omega
            simpa using hm
  | succ k ih =>
    intro m hm hc j hj
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [← lcmUpto_succ, show 3 * 3 ^ m = 3 ^ (m + 1) by ring] at hc
    rcases j with _ | j
    · simpa using hm
    · have := ih (m + 1) hc.1 hc.2 j (by omega)
      rwa [show m + 1 + j = m + (j + 1) by omega] at this

theorem chk_run : chk 299 0 1 1 = true := by decide +kernel

theorem lcmUpto_zero' : Nat.lcmUpto 0 = 1 := by simp [Nat.lcmUpto]

theorem lcmUpto_le (n : ℕ) (hn : n ≤ 299) : Nat.lcmUpto n ≤ 3 ^ n := by
  have h := chk_spec 299 0 (by simp [lcmUpto_zero']) (by rw [lcmUpto_zero']; exact chk_run) n hn
  simpa using h

theorem psi_le_log3 (n : ℕ) (hn : n ≤ 299) : ψ (n : ℝ) ≤ Real.log 3 * n := by
  rw [psi_eq_log_lcmUpto]
  have h1 : ((Nat.lcmUpto n : ℕ) : ℝ) ≤ ((3 ^ n : ℕ) : ℝ) := by exact_mod_cast lcmUpto_le n hn
  have h0 : (0 : ℝ) < (Nat.lcmUpto n : ℕ) := by exact_mod_cast Nat.lcmUpto_pos n
  calc Real.log (Nat.lcmUpto n) ≤ Real.log ((3 ^ n : ℕ) : ℝ) := Real.log_le_log h0 h1
    _ = Real.log 3 * n := by push_cast; rw [Real.log_pow]; ring

theorem psi_le_19' (n : ℕ) (hn : 299 ≤ n) (ha : Real.log 3 ≤ 1.9) : ψ (n : ℝ) ≤ 1.9 * n := by
  rcases eq_or_lt_of_le hn with rfl | h
  · have := psi_le_log3 299 le_rfl
    push_cast at this ⊢
    linarith
  · exact L5Lam.psi_le_19 n h

theorem psi_three : ψ ((3 : ℕ) : ℝ) = Real.log 2 + Real.log 3 := by
  have e1 := L5Lam.psi_succ 0
  have e2 := L5Lam.psi_succ 1
  have e3 := L5Lam.psi_succ 2
  simp only [Nat.cast_zero, psi_zero, zero_add] at e1
  rw [ArithmeticFunction.vonMangoldt_apply_one] at e1
  rw [show (1 + 1 : ℕ) = 2 by rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at e2
  rw [show (2 + 1 : ℕ) = 3 by rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three] at e3
  push_cast at e1 e2 e3 ⊢
  rw [e3, e2, e1]; ring

/-! ### The weights `h` and `H` -/

/-- `h(x) = log x · x^{-s}` -/
noncomputable def hh (s x : ℝ) : ℝ := Real.log x * x ^ (-s)

/-- `H(x) = x^{-(s-1)} (log x/(s-1) + 1/(s-1)²)`, so `H' = -h` -/
noncomputable def HH (s x : ℝ) : ℝ := x ^ (-(s - 1)) * (Real.log x / (s - 1) + 1 / (s - 1) ^ 2)

theorem one_lt_log3 : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]; have := Real.exp_one_lt_d9; linarith

theorem hasDerivAt_hh (s : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (hh s) (x ^ (-s) / x * (1 - s * Real.log x)) x := by
  have h := (Real.hasDerivAt_log hx.ne').mul (Real.hasDerivAt_rpow_const (p := -s) (Or.inl hx.ne'))
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one hx.ne']
  field_simp
  ring

theorem hh_anti {s : ℝ} (hs : 1 < s) : AntitoneOn (hh s) (Ici 3) := by
  have hd : ∀ x ∈ Ici (3 : ℝ), HasDerivAt (hh s) (x ^ (-s) / x * (1 - s * Real.log x)) x :=
    fun x hx => hasDerivAt_hh s (by simp at hx; linarith)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 3)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ici]; exact fun x hx => (hd x (Ioi_subset_Ici_self hx)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx
    simp only [mem_Ioi] at hx
    rw [(hd x (le_of_lt hx)).deriv]
    have hx0 : 0 < x := by linarith
    have hl : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx.le
    have := one_lt_log3
    have h1 : 1 - s * Real.log x ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h1

theorem hasDerivAt_HH {s : ℝ} (hs : 1 < s) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (HH s) (-hh s x) x := by
  have h := (Real.hasDerivAt_rpow_const (p := -(s - 1)) (Or.inl hx.ne')).mul
    (((Real.hasDerivAt_log hx.ne').div_const (s - 1)).add_const (1 / (s - 1) ^ 2))
  refine h.congr_deriv ?_
  have hs1 : s - 1 ≠ 0 := by linarith
  have e1 : x ^ (-(s - 1) - 1) = x ^ (-s) := by congr 1; ring
  have e2 : x ^ (-(s - 1)) = x ^ (-s) * x := by
    rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add_one hx.ne']
  rw [e1, e2]; unfold hh
  field_simp
  ring

theorem hh_tel {s : ℝ} (hs : 1 < s) {x : ℝ} (hx : 3 ≤ x) : hh s (x + 1) ≤ HH s x - HH s (x + 1) := by
  set φ : ℝ → ℝ := fun y => HH s y + y * hh s (x + 1)
  have hd : ∀ y ∈ Icc x (x + 1), HasDerivAt φ (-hh s y + hh s (x + 1)) y := by
    intro y hy
    have hy0 : 0 < y := by simp at hy; linarith
    have := (hasDerivAt_HH hs hy0).add ((hasDerivAt_id' y).mul_const (hh s (x + 1)))
    convert this using 1; ring
  have hanti : AntitoneOn φ (Icc x (x + 1)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc x (x + 1))
    · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
    · rw [interior_Icc]; exact fun y hy => (hd y (Ioo_subset_Icc_self hy)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      rw [(hd y (Ioo_subset_Icc_self hy)).deriv]
      have := hh_anti hs (show y ∈ Ici 3 by simp at hy ⊢; linarith)
        (show x + 1 ∈ Ici 3 by simp; linarith) (by simp at hy; linarith)
      linarith
  have := hanti (show x ∈ Icc x (x + 1) by simp) (show x + 1 ∈ Icc x (x + 1) by simp) (by linarith)
  simp only [φ] at this
  linarith

theorem hh_nonneg (s : ℝ) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ hh s x := by
  unfold hh; have := Real.log_nonneg hx; have : 0 < x := by linarith
  positivity

theorem HH_nonneg {s : ℝ} (hs : 1 < s) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ HH s x := by
  unfold HH; have := Real.log_nonneg hx; have : 0 < x := by linarith
  have : 0 < s - 1 := by linarith
  positivity

/-! ### Summation by parts -/

theorem sbp (f : ℝ → ℝ) (c : ℝ) (a : ℕ)
    (hanti : ∀ m : ℕ, a ≤ m → f ((m + 1 : ℕ) : ℝ) ≤ f (m : ℝ)) :
    ∀ N : ℕ, a ≤ N → (∀ m : ℕ, a ≤ m → m < N → ψ (m : ℝ) ≤ c * m) →
      ∑ n ∈ Finset.Ico (a + 1) (N + 1), Λ n * f n + (c * N - ψ (N : ℝ)) * f N ≤
        (c * a - ψ (a : ℝ)) * f a + c * ∑ n ∈ Finset.Ico (a + 1) (N + 1), f n := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => intro _; simp
  | succ N hN ih =>
    intro hψ
    have ih' := ih (fun m h1 h2 => hψ m h1 (by omega))
    have hb := hψ N hN (by omega)
    have ha := hanti N hN
    have e1 : ∑ n ∈ Finset.Ico (a + 1) (N + 1 + 1), Λ n * f n =
        ∑ n ∈ Finset.Ico (a + 1) (N + 1), Λ n * f n + Λ (N + 1) * f ((N + 1 : ℕ) : ℝ) :=
      Finset.sum_Ico_succ_top (by omega) _
    have e2 : ∑ n ∈ Finset.Ico (a + 1) (N + 1 + 1), f n =
        ∑ n ∈ Finset.Ico (a + 1) (N + 1), f n + f ((N + 1 : ℕ) : ℝ) :=
      Finset.sum_Ico_succ_top (by omega) _
    rw [e1, e2, L5Lam.psi_succ]
    have hm : (c * N - ψ (N : ℝ)) * f ((N + 1 : ℕ) : ℝ) ≤ (c * N - ψ (N : ℝ)) * f N :=
      mul_le_mul_of_nonneg_left ha (by linarith)
    push_cast at *
    nlinarith

theorem tel_sum {s : ℝ} (hs : 1 < s) (a : ℕ) (ha : 3 ≤ a) :
    ∀ N : ℕ, a ≤ N → ∑ n ∈ Finset.Ico (a + 1) (N + 1), hh s n ≤ HH s a - HH s N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast (le_trans ha hN)
    have := hh_tel hs h3
    push_cast
    linarith

/-! ### The tail `Σ_{4 ≤ n ≤ M} Λ(n) h(n)` -/

theorem tail_bound {s : ℝ} (hs : 1 < s) (M : ℕ) (hM : 299 ≤ M) :
    ∑ n ∈ Finset.Ico 4 (M + 1), Λ n * hh s n ≤
      (3 * Real.log 3 - (Real.log 2 + Real.log 3)) * hh s 3 + Real.log 3 * HH s 3 +
        (1.9 - Real.log 3) * (HH s 299 + 299 * hh s 299) := by
  have hanti : ∀ m : ℕ, 3 ≤ m → hh s ((m + 1 : ℕ) : ℝ) ≤ hh s (m : ℝ) := by
    intro m hm
    have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    exact hh_anti hs (show (m : ℝ) ∈ Ici 3 from h3) (show ((m + 1 : ℕ) : ℝ) ∈ Ici 3 by
      simp only [mem_Ici]; push_cast; linarith) (by push_cast; linarith)
  have hl3 := one_lt_log3
  have hl3' : Real.log 3 ≤ 1.9 := by
    have := L5Lam.log_le_pow 3 203 (by norm_num); push_cast at this
    have := Real.log_two_lt_d9; nlinarith
  have P1 := sbp (hh s) (Real.log 3) 3 hanti 299 (by norm_num)
    (fun m _ h2 => psi_le_log3 m (by omega))
  have T1 := tel_sum hs 3 le_rfl 299 (by norm_num)
  have P2 := sbp (hh s) 1.9 299 (fun m hm => hanti m (by omega)) M hM
    (fun m h1 _ => psi_le_19' m h1 hl3')
  have T2 := tel_sum hs 299 (by norm_num) M hM
  have hM' : (299 : ℝ) ≤ M := by exact_mod_cast hM
  have n1 : 0 ≤ (1.9 * (M : ℝ) - ψ (M : ℝ)) * hh s M :=
    mul_nonneg (by linarith [psi_le_19' M hM hl3']) (hh_nonneg s (by linarith))
  have n2 := HH_nonneg hs (show (1 : ℝ) ≤ M by linarith)
  have hsplit : ∑ n ∈ Finset.Ico 4 (M + 1), Λ n * hh s n =
      ∑ n ∈ Finset.Ico 4 300, Λ n * hh s n + ∑ n ∈ Finset.Ico 300 (M + 1), Λ n * hh s n :=
    (Finset.sum_Ico_consecutive _ (by norm_num) (by omega)).symm
  have m1 := mul_le_mul_of_nonneg_left T1 (by linarith : (0 : ℝ) ≤ Real.log 3)
  have m2 := mul_le_mul_of_nonneg_left T2 (by norm_num : (0 : ℝ) ≤ 1.9)
  rw [psi_three] at P1
  simp only [show (3 + 1 : ℕ) = 4 by rfl, show (299 + 1 : ℕ) = 300 by rfl] at P1 T1 P2 T2 m1 m2
  rw [hsplit]
  push_cast at *
  nlinarith

/-! ### Numerical facts -/

theorem log_ge_pow (p k E : ℕ) (hp : 0 < p) (h : 2 ^ k ≤ p ^ E) :
    (k : ℝ) * Real.log 2 ≤ E * Real.log p := by
  have h' : ((2 : ℝ)) ^ k ≤ (p : ℝ) ^ E := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rwa [Real.log_pow, Real.log_pow] at this

theorem log_le_pow' (p k E : ℕ) (hp : 0 < p) (h : p ^ E ≤ 2 ^ k) :
    (E : ℝ) * Real.log p ≤ k * Real.log 2 := by
  have h' : (p : ℝ) ^ E ≤ (2 : ℝ) ^ k := by exact_mod_cast h
  have := Real.log_le_log (by have : (0 : ℝ) < p := by exact_mod_cast hp
                              positivity) h'
  rwa [Real.log_pow, Real.log_pow] at this

theorem log3_bounds : 1.09794 ≤ Real.log 3 ∧ Real.log 3 ≤ 1.09864 := by
  have h1 := log_ge_pow 3 1584 1000 (by norm_num) (by norm_num)
  have h2 := log_le_pow' 3 1585 1000 (by norm_num) (by norm_num)
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  push_cast at h1 h2
  constructor <;> nlinarith

theorem log299_bounds : 5.70044 ≤ Real.log 299 ∧ Real.log 299 ≤ 5.70114 := by
  have h1 := log_ge_pow 299 8224 1000 (by norm_num) (by norm_num)
  have h2 := log_le_pow' 299 8225 1000 (by norm_num) (by norm_num)
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  push_cast at h1 h2
  constructor <;> nlinarith

theorem expneg_le {x x0 : ℝ} (h0 : 0 ≤ x0) (h : x0 ≤ x) :
    Real.exp (-x) ≤ 1 / (1 + x0 + x0 ^ 2 / 2 + x0 ^ 3 / 6) := by
  have hc := Real.sum_le_exp_of_nonneg h0 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hc
  norm_num at hc
  have hp : 0 < 1 + x0 + x0 ^ 2 / 2 + x0 ^ 3 / 6 := by positivity
  rw [le_div_iff₀ hp]
  have e1 : Real.exp (-x) ≤ Real.exp (-x0) := Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (-x0) * Real.exp x0 = 1 := by rw [← Real.exp_add]; simp
  have e3 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have e4 : 0 ≤ Real.exp (-x0) := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left (show 1 + x0 + x0 ^ 2 / 2 + x0 ^ 3 / 6 ≤ Real.exp x0 by
    linarith) e4]

theorem phi_le {x x0 : ℝ} (h0 : 0 ≤ x0) (h : x0 ≤ x) :
    Real.exp (-x) * (x + 1) ≤ (1 + x0) / (1 + x0 + x0 ^ 2 / 2 + x0 ^ 3 / 6) := by
  have e0 : Real.exp (-x) * (x + 1) ≤ Real.exp (-x0) * (1 + x0) := by
    have hd := Real.add_one_le_exp (x - x0)
    have he : Real.exp (-x0) = Real.exp (-x) * Real.exp (x - x0) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he]
    have hp : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
    have : x + 1 ≤ Real.exp (x - x0) * (1 + x0) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hp]
  have e1 := expneg_le h0 le_rfl
  have : Real.exp (-x0) * (1 + x0) ≤ 1 / (1 + x0 + x0 ^ 2 / 2 + x0 ^ 3 / 6) * (1 + x0) :=
    mul_le_mul_of_nonneg_right e1 (by linarith)
  rw [div_mul_eq_mul_div, one_mul] at this
  linarith

/-- the left side of the final inequality, `(s-1)²` times the bound, `u = s - 1` -/
noncomputable def Fin (u l2 a L : ℝ) : ℝ :=
  u ^ 2 * (l2 ^ 2 * Real.exp (-(u * l2)) / 2 + (3 * a ^ 2 - l2 * a) * Real.exp (-(u * a)) / 3) +
    a * (Real.exp (-(u * a)) * (u * a + 1)) +
    (1.9 - a) * (Real.exp (-(u * L)) * (u * L + 1) + u ^ 2 * L * Real.exp (-(u * L)))

theorem combine {u β l2 a L e2 e3 p3 e9 p9 : ℝ} (hu0 : 0 ≤ u) (huβ : u ≤ β)
    (hl2 : 0 ≤ l2) (hl2' : l2 ≤ 0.6931471808) (ha : 1.09794 ≤ a) (ha' : a ≤ 1.09864)
    (hL0 : 0 ≤ L) (hL' : L ≤ 5.70114) (hK : 3 * a ^ 2 - l2 * a ≤ 2.86)
    (h2 : Real.exp (-(u * l2)) ≤ e2) (h3 : Real.exp (-(u * a)) ≤ e3)
    (hp3 : Real.exp (-(u * a)) * (u * a + 1) ≤ p3)
    (h9 : Real.exp (-(u * L)) ≤ e9) (hp9 : Real.exp (-(u * L)) * (u * L + 1) ≤ p9) :
    Fin u l2 a L ≤ β ^ 2 * (0.6931471808 ^ 2 * e2 / 2 + 2.86 * e3 / 3) + 1.09864 * p3 +
      (1.9 - 1.09794) * (p9 + β ^ 2 * 5.70114 * e9) := by
  unfold Fin
  set E2 := Real.exp (-(u * l2)); set E3 := Real.exp (-(u * a)); set E9 := Real.exp (-(u * L))
  have hE2 : 0 ≤ E2 := (Real.exp_pos _).le
  have hE3 : 0 ≤ E3 := (Real.exp_pos _).le
  have hE9 : 0 ≤ E9 := (Real.exp_pos _).le
  have hK0 : 0 ≤ 3 * a ^ 2 - l2 * a := by nlinarith
  have u2 : u ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hu0 huβ 2
  have A1 : l2 ^ 2 * E2 ≤ 0.6931471808 ^ 2 * e2 :=
    mul_le_mul (pow_le_pow_left₀ hl2 hl2' 2) h2 hE2 (by positivity)
  have A2 : (3 * a ^ 2 - l2 * a) * E3 ≤ 2.86 * e3 := mul_le_mul hK h3 hE3 (by norm_num)
  have A0 : 0 ≤ l2 ^ 2 * E2 / 2 + (3 * a ^ 2 - l2 * a) * E3 / 3 := by positivity
  have T1 := mul_le_mul u2 (show l2 ^ 2 * E2 / 2 + (3 * a ^ 2 - l2 * a) * E3 / 3 ≤
    0.6931471808 ^ 2 * e2 / 2 + 2.86 * e3 / 3 by linarith) A0 (sq_nonneg β)
  have P0 : 0 ≤ E3 * (u * a + 1) := mul_nonneg hE3 (by nlinarith)
  have T2 : a * (E3 * (u * a + 1)) ≤ 1.09864 * p3 := mul_le_mul ha' hp3 P0 (by norm_num)
  have B1 : u ^ 2 * L * E9 ≤ β ^ 2 * 5.70114 * e9 :=
    mul_le_mul (mul_le_mul u2 hL' hL0 (sq_nonneg β)) h9 hE9 (by positivity)
  have B0 : 0 ≤ E9 * (u * L + 1) + u ^ 2 * L * E9 := by
    have : 0 ≤ u * L + 1 := by nlinarith
    positivity
  have T3 : (1.9 - a) * (E9 * (u * L + 1) + u ^ 2 * L * E9) ≤
      (1.9 - 1.09794) * (p9 + β ^ 2 * 5.70114 * e9) :=
    mul_le_mul (by linarith) (by linarith) B0 (by norm_num)
  linarith

theorem piece {u l2 a L : ℝ} (α β : ℝ) (hα : 0 ≤ α) (huα : α ≤ u) (huβ : u ≤ β)
    (hl2 : 0.6931471803 ≤ l2) (hl2' : l2 ≤ 0.6931471808) (ha : 1.09794 ≤ a) (ha' : a ≤ 1.09864)
    (hL : 5.70044 ≤ L) (hL' : L ≤ 5.70114) (hK : 3 * a ^ 2 - l2 * a ≤ 2.86)
    (hnum : β ^ 2 * (0.6931471808 ^ 2 *
        (1 / (1 + α * 0.6931471803 + (α * 0.6931471803) ^ 2 / 2 + (α * 0.6931471803) ^ 3 / 6)) / 2
        + 2.86 * (1 / (1 + α * 1.09794 + (α * 1.09794) ^ 2 / 2 + (α * 1.09794) ^ 3 / 6)) / 3) +
      1.09864 * ((1 + α * 1.09794) / (1 + α * 1.09794 + (α * 1.09794) ^ 2 / 2 + (α * 1.09794) ^ 3 / 6)) +
      (1.9 - 1.09794) * ((1 + α * 5.70044) /
          (1 + α * 5.70044 + (α * 5.70044) ^ 2 / 2 + (α * 5.70044) ^ 3 / 6) +
        β ^ 2 * 5.70114 *
          (1 / (1 + α * 5.70044 + (α * 5.70044) ^ 2 / 2 + (α * 5.70044) ^ 3 / 6))) ≤ 2) :
    Fin u l2 a L ≤ 2 := by
  have hu0 : 0 ≤ u := le_trans hα huα
  have x2 : α * 0.6931471803 ≤ u * l2 := mul_le_mul huα hl2 (by norm_num) hu0
  have x3 : α * 1.09794 ≤ u * a := mul_le_mul huα ha (by norm_num) hu0
  have x9 : α * 5.70044 ≤ u * L := mul_le_mul huα hL (by norm_num) hu0
  refine le_trans (combine hu0 huβ (by linarith) hl2' ha ha' (by linarith) hL' hK
    (expneg_le (by positivity) x2) (expneg_le (by positivity) x3) (phi_le (by positivity) x3)
    (expneg_le (by positivity) x9) (phi_le (by positivity) x9)) hnum

theorem fin_le {u l2 a L : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hl2 : 0.6931471803 ≤ l2) (hl2' : l2 ≤ 0.6931471808) (ha : 1.09794 ≤ a) (ha' : a ≤ 1.09864)
    (hL : 5.70044 ≤ L) (hL' : L ≤ 5.70114) : Fin u l2 a L ≤ 2 := by
  have hK : 3 * a ^ 2 - l2 * a ≤ 2.86 := by nlinarith
  rcases le_total u 0.12 with h1 | h1
  · exact piece 0 0.12 le_rfl hu0.le h1 hl2 hl2' ha ha' hL hL' hK (by norm_num)
  rcases le_total u 0.25 with h2 | h2
  · exact piece 0.12 0.25 (by norm_num) h1 h2 hl2 hl2' ha ha' hL hL' hK (by norm_num)
  rcases le_total u 0.45 with h3 | h3
  · exact piece 0.25 0.45 (by norm_num) h2 h3 hl2 hl2' ha ha' hL hL' hK (by norm_num)
  rcases le_total u 0.74 with h4 | h4
  · exact piece 0.45 0.74 (by norm_num) h3 h4 hl2 hl2' ha ha' hL hL' hK (by norm_num)
  · exact piece 0.74 1 (by norm_num) h4 hu1 hl2 hl2' ha ha' hL hL' hK (by norm_num)

/-! ### Assembly -/

theorem rpow_neg_s {s x : ℝ} (hx : 0 < x) :
    x ^ (-s) = Real.exp (-((s - 1) * Real.log x)) / x := by
  rw [Real.rpow_def_of_pos hx, show Real.log x * -s = -((s - 1) * Real.log x) + -Real.log x by ring,
    Real.exp_add, Real.exp_neg (Real.log x), Real.exp_log hx, div_eq_mul_inv]

theorem rpow_neg_u {s x : ℝ} (hx : 0 < x) :
    x ^ (-(s - 1)) = Real.exp (-((s - 1) * Real.log x)) := by
  rw [Real.rpow_def_of_pos hx]; congr 1; ring

theorem lam_le (s : ℝ) (n : ℕ) : Λ n ^ 2 * (n : ℝ) ^ (-s) ≤ Λ n * hh s n := by
  have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have h2 : 0 ≤ (n : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  unfold hh
  have : Λ n ^ 2 ≤ Λ n * Real.log n := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this h2]

/-- the bound `B(s)` for every partial sum -/
noncomputable def Bnd (s : ℝ) : ℝ :=
  Real.log 2 ^ 2 * (2 : ℝ) ^ (-s) + Real.log 3 ^ 2 * (3 : ℝ) ^ (-s) +
    ((3 * Real.log 3 - (Real.log 2 + Real.log 3)) * hh s 3 + Real.log 3 * HH s 3 +
      (1.9 - Real.log 3) * (HH s 299 + 299 * hh s 299))

theorem partial_le {s : ℝ} (hs : 1 < s) (N : ℕ) :
    ∑ n ∈ Finset.range N, Λ n ^ 2 * (n : ℝ) ^ (-s) ≤ Bnd s := by
  set F : ℕ → ℝ := fun n => Λ n ^ 2 * (n : ℝ) ^ (-s)
  have hF : ∀ n, 0 ≤ F n := fun n => by
    simp only [F]; have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) n) (-s); positivity
  have h1 : ∑ n ∈ Finset.range N, F n ≤ ∑ n ∈ Finset.range ((N + 299) + 1), F n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun i _ _ => hF i)
  refine h1.trans ?_
  set M := N + 299
  have hsplit := (Finset.sum_range_add_sum_Ico F (show 4 ≤ M + 1 by omega)).symm
  rw [hsplit]
  have h4 : ∑ n ∈ Finset.range 4, F n = Real.log 2 ^ 2 * (2 : ℝ) ^ (-s) +
      Real.log 3 ^ 2 * (3 : ℝ) ^ (-s) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, F]
    rw [ArithmeticFunction.vonMangoldt_apply_one,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
    simp
  have ht : ∑ n ∈ Finset.Ico 4 (M + 1), F n ≤ ∑ n ∈ Finset.Ico 4 (M + 1), Λ n * hh s n :=
    Finset.sum_le_sum fun n _ => lam_le s n
  have hb := tail_bound hs M (by omega)
  unfold Bnd
  linarith

theorem bnd_le {s : ℝ} (hs : 1 < s) (hs2 : s ≤ 2) : Bnd s ≤ 2 / (s - 1) ^ 2 := by
  set u := s - 1 with hu
  have hu0 : 0 < u := by linarith
  obtain ⟨a1, a2⟩ := log3_bounds
  obtain ⟨L1, L2⟩ := log299_bounds
  have hf := fin_le hu0 (by linarith) Real.log_two_gt_d9.le Real.log_two_lt_d9.le a1 a2 L1 L2
  have key : u ^ 2 * Bnd s = Fin u (Real.log 2) (Real.log 3) (Real.log 299) := by
    unfold Bnd Fin hh HH
    rw [rpow_neg_u (by norm_num : (0 : ℝ) < 3), rpow_neg_u (by norm_num : (0 : ℝ) < 299),
      rpow_neg_s (by norm_num : (0 : ℝ) < 2), rpow_neg_s (by norm_num : (0 : ℝ) < 3),
      rpow_neg_s (by norm_num : (0 : ℝ) < 299), ← hu]
    field_simp
    ring
  rw [le_div_iff₀ (by positivity), mul_comm]
  linarith

/-- **`LamSq2`**, PROVED: `Σ Λ(n)² n^{-s} ≤ 2/(s-1)²` for `1 < s ≤ 2`. -/
theorem lamSq2 : L5.LamSq2 := by
  intro s hs1 hs2
  refine Real.tsum_le_of_sum_range_le (fun n => ?_) (fun N => (partial_le hs1 N).trans (bnd_le hs1 hs2))
  have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) n) (-s); positivity

/-- **(21), p. 370**, PROVED, no named input. -/
theorem bound21 : L5.Bound21 := L5Lam.bound21_of_lamSq lamSq2

/-- **Lemma 5, p. 368**, CONDITIONAL ON Lemma 4, `Parseval1920`, `Const4`. -/
theorem lemma5_of_lamSq2 (h4 : Lemma4) (hP : L5.Parseval1920) (hC : L5.Const4) : Lemma5 :=
  L5Lam.lemma5_of_lamSq h4 hP lamSq2 hC

/-- Vacuity: the `n = 2` term of the sum in `LamSq2` at `s = 1.5` is positive, and `s = 1.5` meets
the range, so the bound is not about an empty or zero sum. -/
theorem lamSq2_nonvacuous :
    (1 : ℝ) < 1.5 ∧ (1.5 : ℝ) ≤ 2 ∧ 0 < Λ 2 ^ 2 * ((2 : ℕ) : ℝ) ^ (-(1.5 : ℝ)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

end LeanLab.Kaniecki1995.L5LamSq

#print axioms LeanLab.Kaniecki1995.L5LamSq.lcmUpto_le
#print axioms LeanLab.Kaniecki1995.L5LamSq.psi_le_log3
#print axioms LeanLab.Kaniecki1995.L5LamSq.hh_anti
#print axioms LeanLab.Kaniecki1995.L5LamSq.hh_tel
#print axioms LeanLab.Kaniecki1995.L5LamSq.sbp
#print axioms LeanLab.Kaniecki1995.L5LamSq.tail_bound
#print axioms LeanLab.Kaniecki1995.L5LamSq.fin_le
#print axioms LeanLab.Kaniecki1995.L5LamSq.partial_le
#print axioms LeanLab.Kaniecki1995.L5LamSq.bnd_le
#print axioms LeanLab.Kaniecki1995.L5LamSq.lamSq2
#print axioms LeanLab.Kaniecki1995.L5LamSq.bound21
#print axioms LeanLab.Kaniecki1995.L5LamSq.lemma5_of_lamSq2
#print axioms LeanLab.Kaniecki1995.L5LamSq.lamSq2_nonvacuous
#print axioms LeanLab.Kaniecki1995.L5LamSq.lcmUpto_succ
#print axioms LeanLab.Kaniecki1995.L5LamSq.chk_spec
#print axioms LeanLab.Kaniecki1995.L5LamSq.chk_run
#print axioms LeanLab.Kaniecki1995.L5LamSq.lcmUpto_zero'
#print axioms LeanLab.Kaniecki1995.L5LamSq.psi_le_19'
#print axioms LeanLab.Kaniecki1995.L5LamSq.psi_three
#print axioms LeanLab.Kaniecki1995.L5LamSq.one_lt_log3
#print axioms LeanLab.Kaniecki1995.L5LamSq.hasDerivAt_hh
#print axioms LeanLab.Kaniecki1995.L5LamSq.hasDerivAt_HH
#print axioms LeanLab.Kaniecki1995.L5LamSq.hh_nonneg
#print axioms LeanLab.Kaniecki1995.L5LamSq.HH_nonneg
#print axioms LeanLab.Kaniecki1995.L5LamSq.tel_sum
#print axioms LeanLab.Kaniecki1995.L5LamSq.log_ge_pow
#print axioms LeanLab.Kaniecki1995.L5LamSq.log_le_pow'
#print axioms LeanLab.Kaniecki1995.L5LamSq.log3_bounds
#print axioms LeanLab.Kaniecki1995.L5LamSq.log299_bounds
#print axioms LeanLab.Kaniecki1995.L5LamSq.expneg_le
#print axioms LeanLab.Kaniecki1995.L5LamSq.phi_le
#print axioms LeanLab.Kaniecki1995.L5LamSq.combine
#print axioms LeanLab.Kaniecki1995.L5LamSq.piece
#print axioms LeanLab.Kaniecki1995.L5LamSq.rpow_neg_s
#print axioms LeanLab.Kaniecki1995.L5LamSq.rpow_neg_u
#print axioms LeanLab.Kaniecki1995.L5LamSq.lam_le
