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

  /-! ### A certified evaluation of τ_500

  BJS display 31 is affine in τ at each step: a branch is
  `κ τ + (γ+κ) ε τ + 2 γ cp + 2 cc` with `cp = c_(n-1)^(n-2)` and `cc = c_n^(n-1)`, so once the
  two c-powers are bounded by powers of 0.73 each step contracts by 0.960719607 (even n) or
  0.9214501 (odd n) and gains a geometric correction. Two steps contract by 0.8853 and gain at
  most 20.5 * 0.73 ^ n, and iterating that from the certified value at n = 20 gives τ_500 at most
  1.2 * 10 ^ -12. The helper lemmas are the parent file's, with the additive constant of the
  pair step kept geometric instead of constant, so that it decays to nothing by n = 500. -/

  /-- The Table 2 values c_m are nonnegative (from the positivity of bjsC306). -/
  private lemma bjsC306_nonneg_s77c (n : ℕ) : 0 ≤ bjsC306 n := (bjsC306_pos n).le

/-- Clearing the denominator in one branch of display 31. -/
private lemma mul_xi_s77c (γ κ ε cp cc t : ℝ) (ht : t ≠ 0) :
    t * bjsXi306 γ κ ε cp cc t = t * κ + t * (γ + κ) * ε + 2 * γ * cp + 2 * cc := by
  unfold bjsXi306
  field_simp

/-- Pushing a nonnegative factor into a two-term maximum, under a bound. -/
private lemma mul_max2_leR_s77c {t C a b : ℝ} (ht : 0 ≤ t)
    (h1 : t * a ≤ C) (h2 : t * b ≤ C) : t * max a b ≤ C := by
  rw [mul_max_of_nonneg _ _ ht]
  exact max_le h1 h2

/-- The τ_n are positive from n = 1 on. -/
private lemma tau_pos_s77c (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ n, 1 ≤ n → 0 < bjsTau306 bjsC306 ε n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · intro h; omega
    · intro _; simp [bjsTau306]
    · intro _
      have ht : 0 < bjsTau306 bjsC306 ε (m + 1) := ih (m + 1) (by omega) (by omega)
      have ht0 : 0 ≤ bjsTau306 bjsC306 ε (m + 1) := le_of_lt ht
      have hcp : 0 ≤ bjsC306 (m + 1) ^ m := pow_nonneg (bjsC306_nonneg_s77c _) _
      have hcc : 0 ≤ bjsC306 (m + 2) ^ (m + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
      simp only [bjsTau306]
      by_cases hpar : Even (m + 2)
      · rw [if_pos hpar]
        refine mul_pos ht ?_
        have hx : (0.9607 : ℝ) ≤
            bjsXi306 1 0.9607 ε (bjsC306 (m + 1) ^ m) (bjsC306 (m + 2) ^ (m + 1))
              (bjsTau306 bjsC306 ε (m + 1)) := by
          unfold bjsXi306
          have h1 : 0 ≤ 2 * 1 * bjsC306 (m + 1) ^ m / bjsTau306 bjsC306 ε (m + 1) :=
            div_nonneg (by positivity) ht0
          have h2 : 0 ≤ 2 * (bjsC306 (m + 2) ^ (m + 1)) /
              bjsTau306 bjsC306 ε (m + 1) := div_nonneg (by positivity) ht0
          have h3 : 0 ≤ (1 + 0.9607) * ε := mul_nonneg (by norm_num) hε
          linarith
        exact lt_of_lt_of_le (by norm_num)
          (le_trans hx (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))))
      · rw [if_neg hpar]
        refine mul_pos ht ?_
        have hx : (0.9214 : ℝ) ≤ 0.9214 + (5 + 4 * ε) * ε +
            6 * (1 + ε) * (bjsC306 (m + 1) ^ m) / bjsTau306 bjsC306 ε (m + 1) +
            2 * (2 + ε) * (bjsC306 (m + 2) ^ (m + 1)) / bjsTau306 bjsC306 ε (m + 1) := by
          have h1 : 0 ≤ (5 + 4 * ε) * ε := mul_nonneg (by linarith) hε
          have h2 : 0 ≤ 6 * (1 + ε) * (bjsC306 (m + 1) ^ m) /
              bjsTau306 bjsC306 ε (m + 1) :=
            div_nonneg (mul_nonneg (by linarith) hcp) ht0
          have h3 : 0 ≤ 2 * (2 + ε) * (bjsC306 (m + 2) ^ (m + 1)) /
              bjsTau306 bjsC306 ε (m + 1) :=
            div_nonneg (mul_nonneg (by linarith) hcc) ht0
          linarith
        exact lt_of_lt_of_le (by norm_num) (le_trans hx (le_max_right _ _))

/-- τ_n is nonnegative. -/
private lemma tau_nonneg_s77c (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ bjsTau306 bjsC306 ε n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [bjsTau306]
  · exact le_of_lt (tau_pos_s77c ε hε n h)

/-- exp(1/5) ≤ 1.2214028. -/
private lemma exp_02_le_s77c : Real.exp 0.2 ≤ 1.2214028 := by
  have h : (0.2 : ℝ) = 1 / 5 := by norm_num
  rw [h]
  refine le_of_pow_le_pow_left₀ (by norm_num : (5:ℕ) ≠ 0) (by norm_num) ?_
  have h5 : (Real.exp (1 / 5)) ^ 5 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h5]
  calc Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
    _ ≤ (1.2214028 : ℝ) ^ 5 := by norm_num

/-- exp(2/5) ≤ 1.4918247999. -/
private lemma exp_04_le_s77c : Real.exp 0.4 ≤ 1.4918247999 := by
  rw [show (0.4 : ℝ) = 0.2 + 0.2 from by norm_num, Real.exp_add]
  calc Real.exp 0.2 * Real.exp 0.2 ≤ 1.2214028 * 1.2214028 :=
        mul_le_mul exp_02_le_s77c exp_02_le_s77c (Real.exp_pos _).le (by norm_num)
    _ ≤ 1.4918247999 := by norm_num

/-- exp(3/5) ≤ 1.8221189877. -/
private lemma exp_06_le_s77c : Real.exp 0.6 ≤ 1.8221189878 := by
  rw [show (0.6 : ℝ) = 0.2 + 0.4 from by norm_num, Real.exp_add]
  calc Real.exp 0.2 * Real.exp 0.4 ≤ 1.2214028 * 1.4918247999 :=
        mul_le_mul exp_02_le_s77c exp_04_le_s77c (Real.exp_pos _).le (by norm_num)
    _ ≤ 1.8221189878 := by norm_num

/-- exp(4/5) ≤ 2.2255412335. -/
private lemma exp_08_le_s77c : Real.exp 0.8 ≤ 2.2255412336 := by
  rw [show (0.8 : ℝ) = 0.4 + 0.4 from by norm_num, Real.exp_add]
  calc Real.exp 0.4 * Real.exp 0.4 ≤ 1.4918247999 * 1.4918247999 :=
        mul_le_mul exp_04_le_s77c exp_04_le_s77c (Real.exp_pos _).le (by norm_num)
    _ ≤ 2.2255412336 := by norm_num

/-- 4 exp 1 / 3 ≤ 3.6243757720, the γ₃ of Lemma 9. -/
private lemma four_exp_one_le_s77c : 4 * Real.exp 1 / 3 ≤ 3.6243757720 := by
  nlinarith [Real.exp_one_lt_d9]

/-- A cleared branch of display 31, bounded by its value at the upper endpoints. -/
private lemma xi_le_of_s77c {γ γu κ ε cp cc t C A qcp qcc : ℝ}
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ γu) (hκ : 0 ≤ κ) (hε0 : 0 ≤ ε)
    (hcp0 : 0 ≤ cp) (hcc0 : 0 ≤ cc) (ht0 : 0 ≤ t)
    (ht : t ≤ A) (hcp : cp ≤ qcp) (hcc : cc ≤ qcc)
    (key : A * κ + A * (γu + κ) * ε + 2 * γu * qcp + 2 * qcc ≤ C) :
    t * bjsXi306 γ κ ε cp cc t ≤ C := by
  rcases eq_or_lt_of_le ht0 with h | h
  · have hA : (0:ℝ) ≤ A := h ▸ ht
    have hC : (0:ℝ) ≤ C := by
      have h0 : (0:ℝ) ≤ A * κ + A * (γu + κ) * ε + 2 * γu * qcp + 2 * qcc := by
        have h1 : (0:ℝ) ≤ A * κ := mul_nonneg hA hκ
        have h2 : (0:ℝ) ≤ A * (γu + κ) * ε := by
          have hgk : (0:ℝ) ≤ γu + κ := by linarith
          exact mul_nonneg (mul_nonneg hA hgk) hε0
        have h3 : (0:ℝ) ≤ 2 * γu * qcp := by
          have h2' : (0:ℝ) ≤ 2 * γu := by linarith
          have hq : (0:ℝ) ≤ qcp := le_trans hcp0 hcp
          exact mul_nonneg h2' hq
        have h4 : (0:ℝ) ≤ 2 * qcc := mul_nonneg (by norm_num) (le_trans hcc0 hcc)
        linarith
      linarith
    rw [← h]
    simp only [zero_mul]
    exact hC
  · rw [mul_xi_s77c γ κ ε cp cc t h.ne']
    have h1 : t * κ ≤ A * κ := mul_le_mul_of_nonneg_right ht hκ
    have h2 : t * (γ + κ) * ε ≤ A * (γu + κ) * ε := by
      have hgk : γ + κ ≤ γu + κ := by linarith
      have hgk0 : (0:ℝ) ≤ γ + κ := by linarith
      have hs : t * (γ + κ) ≤ A * (γu + κ) := mul_le_mul ht hgk hgk0 (le_trans ht0 ht)
      have hb0 : (0:ℝ) ≤ A * (γu + κ) :=
        mul_nonneg (le_trans ht0 ht) (by linarith)
      exact mul_le_mul hs le_rfl hε0 hb0
    have h3 : 2 * γ * cp ≤ 2 * γu * qcp := by
      have hm : γ * cp ≤ γu * qcp := mul_le_mul hγ hcp hcp0 (by linarith)
      linarith
    have h4 : 2 * cc ≤ 2 * qcc := by linarith
    linarith

/-- The second odd branch of display 31, bounded by its value at the upper endpoints. -/
private lemma odd2_le_of_s77c {ε cp cc t C A qcp qcc : ℝ}
    (hε0 : 0 ≤ ε) (hcp0 : 0 ≤ cp) (hcc0 : 0 ≤ cc) (ht0 : 0 ≤ t)
    (ht : t ≤ A) (hcp : cp ≤ qcp) (hcc : cc ≤ qcc)
    (key : A * (0.9214 + (5 + 4 * ε) * ε) + 6 * (1 + ε) * qcp + 2 * (2 + ε) * qcc ≤ C) :
    t * (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t + 2 * (2 + ε) * cc / t) ≤ C := by
  rcases eq_or_lt_of_le ht0 with h | h
  · have hA : (0:ℝ) ≤ A := h ▸ ht
    have hC : (0:ℝ) ≤ C := by
      have h0 : (0:ℝ) ≤ A * (0.9214 + (5 + 4 * ε) * ε) + 6 * (1 + ε) * qcp
          + 2 * (2 + ε) * qcc := by
        have h1 : (0:ℝ) ≤ A * (0.9214 + (5 + 4 * ε) * ε) :=
          mul_nonneg hA (by nlinarith)
        have h2 : (0:ℝ) ≤ 6 * (1 + ε) * qcp := by
          have h2' : (0:ℝ) ≤ 6 * (1 + ε) := mul_nonneg (by norm_num) (by linarith)
          exact mul_nonneg h2' (le_trans hcp0 hcp)
        have h3 : (0:ℝ) ≤ 2 * (2 + ε) * qcc := by
          have h3' : (0:ℝ) ≤ 2 * (2 + ε) := mul_nonneg (by norm_num) (by linarith)
          exact mul_nonneg h3' (le_trans hcc0 hcc)
        linarith
      linarith
    rw [← h]
    simp only [zero_mul]
    exact hC
  · have e1 : t * (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t +
        2 * (2 + ε) * cc / t) =
        t * (0.9214 + (5 + 4 * ε) * ε) + 6 * (1 + ε) * cp + 2 * (2 + ε) * cc := by
      field_simp
    rw [e1]
    have hc1 : (0:ℝ) ≤ 0.9214 + (5 + 4 * ε) * ε := by nlinarith
    have h1 : t * (0.9214 + (5 + 4 * ε) * ε) ≤ A * (0.9214 + (5 + 4 * ε) * ε) :=
      mul_le_mul_of_nonneg_right ht hc1
    have h2 : 6 * (1 + ε) * cp ≤ 6 * (1 + ε) * qcp :=
      mul_le_mul_of_nonneg_left hcp (by linarith)
    have h3 : 2 * (2 + ε) * cc ≤ 2 * (2 + ε) * qcc :=
      mul_le_mul_of_nonneg_left hcc (by linarith)
    linarith

/-- Certificate step to n = 2: τ_2 ≤ 10.413585322274. -/
private lemma tauA_2_s77c :
    bjsTau306 bjsC306 (1 / 100000) 2 ≤ 10.413585322274 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((0:ℕ) + 1) ≤ 3 := by norm_num [bjsTau306]
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((0:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((0:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((0:ℕ) + 1) ^ 0 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((0:ℕ) + 2) ^ (0 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((0:ℕ) + 1) ^ 0 ≤ 1 := by norm_num [bjsC306]
  have hcc : bjsC306 ((0:ℕ) + 2) ^ (0 + 1) ≤ 0.33 := by norm_num [bjsC306]
  rw [show (2:ℕ) = (0:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((0:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · exact xi_le_of_s77c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 3: τ_3 ≤ 12.184021041375. -/
private lemma tauA_3_s77c :
    bjsTau306 bjsC306 (1 / 100000) 3 ≤ 12.184021041375 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((1:ℕ) + 1) ≤ 10.413585322274 := tauA_2_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((1:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((1:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((1:ℕ) + 1) ^ 1 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((1:ℕ) + 2) ^ (1 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((1:ℕ) + 1) ^ 1 ≤ 0.33 := by norm_num [bjsC306]
  have hcc : bjsC306 ((1:ℕ) + 2) ^ (1 + 1) ≤ 0.1521 := by norm_num [bjsC306]
  rw [show (3:ℕ) = (1:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((1:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of_s77c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 4: τ_4 ≤ 12.198334899666. -/
private lemma tauA_4_s77c :
    bjsTau306 bjsC306 (1 / 100000) 4 ≤ 12.198334899666 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((2:ℕ) + 1) ≤ 12.184021041375 := tauA_3_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((2:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((2:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((2:ℕ) + 1) ^ 2 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((2:ℕ) + 2) ^ (2 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((2:ℕ) + 1) ^ 2 ≤ 0.1521 := by norm_num [bjsC306]
  have hcc : bjsC306 ((2:ℕ) + 2) ^ (2 + 1) ≤ 0.091125 := by norm_num [bjsC306]
  rw [show (4:ℕ) = (2:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((2:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · exact xi_le_of_s77c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 5: τ_5 ≤ 12.057520918719. -/
private lemma tauA_5_s77c :
    bjsTau306 bjsC306 (1 / 100000) 5 ≤ 12.057520918719 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((3:ℕ) + 1) ≤ 12.198334899666 := tauA_4_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((3:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((3:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((3:ℕ) + 1) ^ 3 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((3:ℕ) + 2) ^ (3 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((3:ℕ) + 1) ^ 3 ≤ 0.091125 := by norm_num [bjsC306]
  have hcc : bjsC306 ((3:ℕ) + 2) ^ (3 + 1) ≤ 0.0676521 := by norm_num [bjsC306]
  rw [show (5:ℕ) = (3:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((3:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of_s77c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 6: τ_6 ≤ 11.811034158426. -/
private lemma tauA_6_s77c :
    bjsTau306 bjsC306 (1 / 100000) 6 ≤ 11.811034158426 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((4:ℕ) + 1) ≤ 12.057520918719 := tauA_5_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((4:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((4:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((4:ℕ) + 1) ^ 4 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((4:ℕ) + 2) ^ (4 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((4:ℕ) + 1) ^ 4 ≤ 0.0676521 := by norm_num [bjsC306]
  have hcc : bjsC306 ((4:ℕ) + 2) ^ (4 + 1) ≤ 0.0459166 := by norm_num [bjsC306]
  rw [show (6:ℕ) = (4:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((4:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · exact xi_le_of_s77c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 7: τ_7 ≤ 11.295966470933. -/
private lemma tauA_7_s77c :
    bjsTau306 bjsC306 (1 / 100000) 7 ≤ 11.295966470933 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((5:ℕ) + 1) ≤ 11.811034158426 := tauA_6_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((5:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((5:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((5:ℕ) + 1) ^ 5 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((5:ℕ) + 2) ^ (5 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((5:ℕ) + 1) ^ 5 ≤ 0.0459166 := by norm_num [bjsC306]
  have hcc : bjsC306 ((5:ℕ) + 2) ^ (5 + 1) ≤ 0.0342965 := by norm_num [bjsC306]
  rw [show (7:ℕ) = (5:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((5:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of_s77c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 8: τ_8 ≤ 10.96500926864. -/
private lemma tauA_8_s77c :
    bjsTau306 bjsC306 (1 / 100000) 8 ≤ 10.96500926864 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((6:ℕ) + 1) ≤ 11.295966470933 := tauA_7_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((6:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((6:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((6:ℕ) + 1) ^ 6 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((6:ℕ) + 2) ^ (6 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((6:ℕ) + 1) ^ 6 ≤ 0.0342965 := by norm_num [bjsC306]
  have hcc : bjsC306 ((6:ℕ) + 2) ^ (6 + 1) ≤ 0.0220799 := by norm_num [bjsC306]
  rw [show (8:ℕ) = (6:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((6:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · exact xi_le_of_s77c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 9: τ_9 ≤ 10.312872103185. -/
private lemma tauA_9_s77c :
    bjsTau306 bjsC306 (1 / 100000) 9 ≤ 10.312872103185 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((7:ℕ) + 1) ≤ 10.96500926864 := tauA_8_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((7:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((7:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((7:ℕ) + 1) ^ 7 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((7:ℕ) + 2) ^ (7 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((7:ℕ) + 1) ^ 7 ≤ 0.0220799 := by norm_num [bjsC306]
  have hcc : bjsC306 ((7:ℕ) + 2) ^ (7 + 1) ≤ 0.0191708 := by norm_num [bjsC306]
  rw [show (9:ℕ) = (7:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((7:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of_s77c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 10: τ_10 ≤ 9.969508434014. -/
private lemma tauA_10_s77c :
    bjsTau306 bjsC306 (1 / 100000) 10 ≤ 9.969508434014 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((8:ℕ) + 1) ≤ 10.312872103185 := tauA_9_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((8:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((8:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((8:ℕ) + 1) ^ 8 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((8:ℕ) + 2) ^ (8 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((8:ℕ) + 1) ^ 8 ≤ 0.0191708 := by norm_num [bjsC306]
  have hcc : bjsC306 ((8:ℕ) + 2) ^ (8 + 1) ≤ 0.0116942 := by norm_num [bjsC306]
  rw [show (10:ℕ) = (8:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((8:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · exact xi_le_of_s77c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 11: τ_11 ≤ 9.295966889149. -/
private lemma tauA_11_s77c :
    bjsTau306 bjsC306 (1 / 100000) 11 ≤ 9.295966889149 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((9:ℕ) + 1) ≤ 9.969508434014 := tauA_10_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((9:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((9:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((9:ℕ) + 1) ^ 9 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((9:ℕ) + 2) ^ (9 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((9:ℕ) + 1) ^ 9 ≤ 0.0116942 := by norm_num [bjsC306]
  have hcc : bjsC306 ((9:ℕ) + 2) ^ (9 + 1) ≤ 0.00984931 := by norm_num [bjsC306]
  rw [show (11:ℕ) = (9:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((9:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of_s77c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 12: τ_12 ≤ 8.962926416429. -/
private lemma tauA_12_s77c :
    bjsTau306 bjsC306 (1 / 100000) 12 ≤ 8.962926416429 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((10:ℕ) + 1) ≤ 9.295966889149 := tauA_11_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((10:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((10:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((10:ℕ) + 1) ^ 10 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((10:ℕ) + 2) ^ (10 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((10:ℕ) + 1) ^ 10 ≤ 0.00984931 := by norm_num [bjsC306]
  have hcc : bjsC306 ((10:ℕ) + 2) ^ (10 + 1) ≤ 0.00620507 := by norm_num [bjsC306]
  rw [show (12:ℕ) = (10:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((10:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · exact xi_le_of_s77c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 13: τ_13 ≤ 8.315008916756. -/
private lemma tauA_13_s77c :
    bjsTau306 bjsC306 (1 / 100000) 13 ≤ 8.315008916756 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((11:ℕ) + 1) ≤ 8.962926416429 := tauA_12_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((11:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((11:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((11:ℕ) + 1) ^ 11 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((11:ℕ) + 2) ^ (11 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((11:ℕ) + 1) ^ 11 ≤ 0.00620507 := by norm_num [bjsC306]
  have hcc : bjsC306 ((11:ℕ) + 2) ^ (11 + 1) ≤ 0.00472237 := by norm_num [bjsC306]
  rw [show (13:ℕ) = (11:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((11:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of_s77c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 14: τ_14 ≤ 8.005231258708. -/
private lemma tauA_14_s77c :
    bjsTau306 bjsC306 (1 / 100000) 14 ≤ 8.005231258708 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((12:ℕ) + 1) ≤ 8.315008916756 := tauA_13_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((12:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((12:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((12:ℕ) + 1) ^ 12 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((12:ℕ) + 2) ^ (12 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((12:ℕ) + 1) ^ 12 ≤ 0.00472237 := by norm_num [bjsC306]
  have hcc : bjsC306 ((12:ℕ) + 2) ^ (12 + 1) ≤ 0.00369721 := by norm_num [bjsC306]
  rw [show (14:ℕ) = (12:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((12:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · exact xi_le_of_s77c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 15: τ_15 ≤ 7.410507407889. -/
private lemma tauA_15_s77c :
    bjsTau306 bjsC306 (1 / 100000) 15 ≤ 7.410507407889 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((13:ℕ) + 1) ≤ 8.005231258708 := tauA_14_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((13:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((13:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((13:ℕ) + 1) ^ 13 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((13:ℕ) + 2) ^ (13 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((13:ℕ) + 1) ^ 13 ≤ 0.00369721 := by norm_num [bjsC306]
  have hcc : bjsC306 ((13:ℕ) + 2) ^ (13 + 1) ≤ 0.00297588 := by norm_num [bjsC306]
  rw [show (15:ℕ) = (13:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((13:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of_s77c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 16: τ_16 ≤ 7.129299684578. -/
private lemma tauA_16_s77c :
    bjsTau306 bjsC306 (1 / 100000) 16 ≤ 7.129299684578 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((14:ℕ) + 1) ≤ 7.410507407889 := tauA_15_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((14:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((14:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((14:ℕ) + 1) ^ 14 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((14:ℕ) + 2) ^ (14 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((14:ℕ) + 1) ^ 14 ≤ 0.00297588 := by norm_num [bjsC306]
  have hcc : bjsC306 ((14:ℕ) + 2) ^ (14 + 1) ≤ 0.00196408 := by norm_num [bjsC306]
  rw [show (16:ℕ) = (14:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((14:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · exact xi_le_of_s77c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 17: τ_17 ≤ 6.586263020977. -/
private lemma tauA_17_s77c :
    bjsTau306 bjsC306 (1 / 100000) 17 ≤ 6.586263020977 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((15:ℕ) + 1) ≤ 7.129299684578 := tauA_16_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((15:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((15:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((15:ℕ) + 1) ^ 15 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((15:ℕ) + 2) ^ (15 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((15:ℕ) + 1) ^ 15 ≤ 0.00196408 := by norm_num [bjsC306]
  have hcc : bjsC306 ((15:ℕ) + 2) ^ (15 + 1) ≤ 0.0012963 := by norm_num [bjsC306]
  rw [show (17:ℕ) = (15:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((15:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of_s77c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 18: τ_18 ≤ 6.331855727112. -/
private lemma tauA_18_s77c :
    bjsTau306 bjsC306 (1 / 100000) 18 ≤ 6.331855727112 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((16:ℕ) + 1) ≤ 6.586263020977 := tauA_17_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((16:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((16:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((16:ℕ) + 1) ^ 16 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((16:ℕ) + 2) ^ (16 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((16:ℕ) + 1) ^ 16 ≤ 0.0012963 := by norm_num [bjsC306]
  have hcc : bjsC306 ((16:ℕ) + 2) ^ (16 + 1) ≤ 0.000855553 := by norm_num [bjsC306]
  rw [show (18:ℕ) = (16:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((16:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · exact xi_le_of_s77c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 19: τ_19 ≤ 5.842582630418. -/
private lemma tauA_19_s77c :
    bjsTau306 bjsC306 (1 / 100000) 19 ≤ 5.842582630418 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((17:ℕ) + 1) ≤ 6.331855727112 := tauA_18_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((17:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((17:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((17:ℕ) + 1) ^ 17 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((17:ℕ) + 2) ^ (17 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((17:ℕ) + 1) ^ 17 ≤ 0.000855553 := by norm_num [bjsC306]
  have hcc : bjsC306 ((17:ℕ) + 2) ^ (17 + 1) ≤ 0.000740196 := by norm_num [bjsC306]
  rw [show (19:ℕ) = (17:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((17:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of_s77c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 20: τ_20 ≤ 5.615555942561. -/
private lemma tauA_20_s77c :
    bjsTau306 bjsC306 (1 / 100000) 20 ≤ 5.615555942561 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((18:ℕ) + 1) ≤ 5.842582630418 := tauA_19_s77c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((18:ℕ) + 1) :=
    tau_nonneg_s77c _ (by norm_num) ((18:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((18:ℕ) + 1) ^ 18 := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((18:ℕ) + 2) ^ (18 + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 ((18:ℕ) + 1) ^ 18 ≤ 0.000740196 := by norm_num [bjsC306]
  have hcc : bjsC306 ((18:ℕ) + 2) ^ (18 + 1) ≤ 0.000495931 := by norm_num [bjsC306]
  rw [show (20:ℕ) = (18:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((18:ℕ) + 2))]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of_s77c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · exact xi_le_of_s77c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- The c_n of BJS Table 2 are at most 0.73 up to n = 500. -/
private lemma bjsC306_le73_s77o (m : ℕ) (hm2 : 2 ≤ m) (hm500 : m ≤ 500) :
    bjsC306 m ≤ 0.73 := by
  unfold bjsC306
  rw [if_neg (by omega : ¬ m ≤ 1)]
  by_cases h2 : m = 2
  · rw [if_pos h2]; norm_num
  rw [if_neg h2]
  by_cases h3 : m = 3
  · rw [if_pos h3]; norm_num
  rw [if_neg h3]
  by_cases h4 : m = 4
  · rw [if_pos h4]; norm_num
  rw [if_neg h4]
  by_cases h5 : m = 5
  · rw [if_pos h5]; norm_num
  rw [if_neg h5]
  by_cases h6 : m = 6
  · rw [if_pos h6]; norm_num
  rw [if_neg h6]
  by_cases h7 : m = 7
  · rw [if_pos h7]; norm_num
  rw [if_neg h7]
  by_cases h8 : m = 8
  · rw [if_pos h8]; norm_num
  rw [if_neg h8]
  by_cases h10 : m ≤ 10
  · rw [if_pos h10]; norm_num
  rw [if_neg h10]
  by_cases h12 : m ≤ 12
  · rw [if_pos h12]; norm_num
  rw [if_neg h12]
  by_cases h13 : m = 13
  · rw [if_pos h13]; norm_num
  rw [if_neg h13]
  by_cases h14 : m = 14
  · rw [if_pos h14]; norm_num
  rw [if_neg h14]
  by_cases h18 : m ≤ 18
  · rw [if_pos h18]; norm_num
  rw [if_neg h18]
  by_cases h20 : m ≤ 20
  · rw [if_pos h20]; norm_num
  rw [if_neg h20]
  by_cases h26 : m ≤ 26
  · rw [if_pos h26]; norm_num
  rw [if_neg h26]
  by_cases h34 : m ≤ 34
  · rw [if_pos h34]; norm_num
  rw [if_neg h34]
  by_cases h46 : m ≤ 46
  · rw [if_pos h46]; norm_num
  rw [if_neg h46]
  by_cases h82 : m ≤ 82
  · rw [if_pos h82]; norm_num
  rw [if_neg h82]
  by_cases h345 : m ≤ 345
  · rw [if_pos h345]; norm_num
  rw [if_neg h345]
  rw [if_pos hm500]

/-- One step of display 31 at even n = k + 2: the ratio is at most 0.960719607, the gain at
most 8.709 * 0.73 ^ k. -/
private lemma step_even_s77c (k : ℕ) (hk : 2 ≤ k) (hk2 : k + 2 ≤ 500) (hpar : Even (k + 2)) :
    bjsTau306 bjsC306 (1 / 100000) (k + 2) ≤
      0.960719607 * bjsTau306 bjsC306 (1 / 100000) (k + 1) + 8.709 * 0.73 ^ k := by
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) (k + 1) :=
    tau_nonneg_s77c _ (by norm_num) (k + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 (k + 1) ^ k := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 (k + 2) ^ (k + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 (k + 1) ^ k ≤ 0.73 ^ k :=
    pow_le_pow_left₀ (bjsC306_nonneg_s77c _)
      (bjsC306_le73_s77o (k + 1) (by omega) (by omega)) k
  have hcc : bjsC306 (k + 2) ^ (k + 1) ≤ 0.73 ^ (k + 1) :=
    pow_le_pow_left₀ (bjsC306_nonneg_s77c _)
      (bjsC306_le73_s77o (k + 2) (by omega) (by omega)) (k + 1)
  have h73 : (0:ℝ) < (0.73:ℝ) ^ k := pow_pos (by norm_num) k
  have hsum : 2 * 3.6243757720 * (0.73:ℝ) ^ k + 2 * (0.73:ℝ) ^ (k + 1)
      ≤ 8.709 * (0.73:ℝ) ^ k := by
    rw [pow_succ]; nlinarith [h73]
  simp only [bjsTau306]
  try dsimp only
  rw [if_pos hpar]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
      · exact xi_le_of_s77c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
    · refine mul_max2_leR_s77c ht0 ?_ ?_
      · exact xi_le_of_s77c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
      · exact xi_le_of_s77c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
  · refine mul_max2_leR_s77c ht0 ?_ ?_
    · exact xi_le_of_s77c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
    · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)

/-- One step of display 31 at odd n = k + 2: the ratio is at most 0.9214501, the gain at most
8.93 * 0.73 ^ k. -/
private lemma step_odd_s77c (k : ℕ) (hk : 2 ≤ k) (hk2 : k + 2 ≤ 500) (hpar : ¬ Even (k + 2)) :
    bjsTau306 bjsC306 (1 / 100000) (k + 2) ≤
      0.9214501 * bjsTau306 bjsC306 (1 / 100000) (k + 1) + 8.93 * 0.73 ^ k := by
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) (k + 1) :=
    tau_nonneg_s77c _ (by norm_num) (k + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 (k + 1) ^ k := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 (k + 2) ^ (k + 1) := pow_nonneg (bjsC306_nonneg_s77c _) _
  have hcp : bjsC306 (k + 1) ^ k ≤ 0.73 ^ k :=
    pow_le_pow_left₀ (bjsC306_nonneg_s77c _)
      (bjsC306_le73_s77o (k + 1) (by omega) (by omega)) k
  have hcc : bjsC306 (k + 2) ^ (k + 1) ≤ 0.73 ^ (k + 1) :=
    pow_le_pow_left₀ (bjsC306_nonneg_s77c _)
      (bjsC306_le73_s77o (k + 2) (by omega) (by omega)) (k + 1)
  have h73 : (0:ℝ) < (0.73:ℝ) ^ k := pow_pos (by norm_num) k
  have hsum : 6 * (1 + 1 / 100000) * (0.73:ℝ) ^ k + 2 * (2 + 1 / 100000) * (0.73:ℝ) ^ (k + 1)
      ≤ 8.93 * (0.73:ℝ) ^ k := by
    rw [pow_succ]; nlinarith [h73]
  have hsum2 : 2 * 3.6243757720 * (0.73:ℝ) ^ k + 2 * (0.73:ℝ) ^ (k + 1)
      ≤ 8.93 * (0.73:ℝ) ^ k := by
    rw [pow_succ]; nlinarith [h73]
  simp only [bjsTau306]
  try dsimp only
  rw [if_neg hpar]
  refine mul_max2_leR_s77c ht0 ?_ ?_
  · exact xi_le_of_s77c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le_s77c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
  · exact odd2_le_of_s77c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)

/-- Two steps of display 31 at even n = k + 2: the ratio is at most 0.8853, the gain at most
20.5 * 0.73 ^ (k + 2). -/
private lemma pair_step_s77c (k : ℕ) (hk : 18 ≤ k) (hk2 : k + 4 ≤ 500) (hpar : Even k) :
    bjsTau306 bjsC306 (1 / 100000) (k + 4) ≤
      0.8853 * bjsTau306 bjsC306 (1 / 100000) (k + 2) + 20.5 * 0.73 ^ (k + 2) := by
  have hpar4 : Even (k + 4) := by obtain ⟨r, hr⟩ := hpar; exact ⟨r + 2, by omega⟩
  have hodd3 : ¬ Even (k + 3) := by
    obtain ⟨q, hq⟩ := hpar
    rintro ⟨r, hr⟩
    omega
  have hA := step_even_s77c (k + 2) (by omega) (by omega) hpar4
  have hB := step_odd_s77c (k + 1) (by omega) (by omega) hodd3
  have hAB : 0.960719607 * 0.9214501 ≤ (0.8853:ℝ) := by norm_num
  have hsplit : (0.73:ℝ) ^ (k + 1) = (1 / 0.73) * 0.73 ^ (k + 2) := by
    have h2 : (0.73:ℝ) ^ (k + 2) = (0.73:ℝ) ^ (k + 1) * 0.73 := pow_succ _ _
    rw [h2]; field_simp
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) (k + 2) := tau_nonneg_s77c _ (by norm_num) _
  have h73 : (0:ℝ) < (0.73:ℝ) ^ (k + 2) := pow_pos (by norm_num) _
  have hmul : 0.960719607 * bjsTau306 bjsC306 (1 / 100000) (k + 3) ≤
      0.960719607 * (0.9214501 * bjsTau306 bjsC306 (1 / 100000) (k + 2)
        + 8.93 * 0.73 ^ (k + 1)) :=
    mul_le_mul_of_nonneg_left hB (by norm_num)
  nlinarith [hA, hmul, hAB, hsplit, ht0, h73]

/-- The pairs from n = 20 on: τ_(20 + 2 j) is at most 0.8853 ^ j τ_20 plus a correction that
never exceeds 0.12 * 0.8853 ^ j. -/
private lemma tau_chain_s77c (j : ℕ) (hj : j ≤ 240) :
    bjsTau306 bjsC306 (1 / 100000) (20 + 2 * j) ≤
      (0.8853:ℝ) ^ j * 5.615555942561 + 0.12 * ((0.8853:ℝ) ^ j - ((0.73:ℝ) ^ 2) ^ j) := by
  induction j with
  | zero => simpa using tauA_20_s77c
  | succ j ih =>
    have hpar : Even (18 + 2 * j) := ⟨9 + j, by ring⟩
    have hpair := pair_step_s77c (18 + 2 * j) (by omega) (by omega) hpar
    have e1 : 18 + 2 * j + 4 = 20 + 2 * (j + 1) := by ring
    have e2 : 18 + 2 * j + 2 = 20 + 2 * j := by ring
    rw [e1, e2] at hpair
    have hq : (0.8853:ℝ) ^ (j + 1) = 0.8853 ^ j * 0.8853 := pow_succ _ _
    have hs : ((0.73:ℝ) ^ 2) ^ (j + 1) = ((0.73:ℝ) ^ 2) ^ j * (0.73:ℝ) ^ 2 := pow_succ _ _
    have h73 : (0.73:ℝ) ^ (20 + 2 * j) = (0.73:ℝ) ^ 20 * ((0.73:ℝ) ^ 2) ^ j := by
      rw [pow_add, ← pow_mul]
    have hkey : 20.5 * (0.73:ℝ) ^ 20 ≤ 0.12 * (0.8853 - (0.73:ℝ) ^ 2) := by norm_num
    have hq0 : (0:ℝ) ≤ (0.8853:ℝ) ^ j := by positivity
    have hs0 : (0:ℝ) ≤ ((0.73:ℝ) ^ 2) ^ j := by positivity
    have ihj := ih (by omega)
    nlinarith [hpair, ihj, hq, hs, h73, hkey, hq0, hs0]

/-- BJS display 31 at n = 500 and ε = 1/100000: τ_500 ≤ 2 * 10 ^ -12, by the certified
value at n = 20 and the geometric pair contraction of display 31 from there. -/
theorem tau500_value1122c : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12 := by
  have h := tau_chain_s77c 240 (by norm_num)
  have h500 : 20 + 2 * 240 = 500 := by norm_num
  rw [h500] at h
  have hP30 : (0.8853:ℝ) ^ 30 ≤ 0.02587 := by norm_num
  have hP240 : (0.8853:ℝ) ^ 240 = ((0.8853:ℝ) ^ 30) ^ 8 := by
    rw [show (240:ℕ) = 30 * 8 from by norm_num, pow_mul]
  have hP8 : ((0.8853:ℝ) ^ 30) ^ 8 ≤ (0.02587:ℝ) ^ 8 := pow_le_pow_left₀ (by positivity) hP30 8
  have hnum : (0.02587:ℝ) ^ 8 ≤ 21 / 100000000000000 := by norm_num
  have hs : (0:ℝ) ≤ ((0.73:ℝ) ^ 2) ^ 240 := by positivity
  rw [hP240] at h
  nlinarith [h, hP8, hnum, hs]

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
