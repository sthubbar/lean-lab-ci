/-
Split of the two numerical LEAFs tau_odd_sum_le132_1122c and tau_even_sum_le135_1122c of
Split1122cTwinT.lean: the partial sums of the bounds τ_n of BJS display 31, Bordignon,
Johnston and Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, Lemma 11 and
Proposition 13, pages 11 to 14, with c_n of Table 2, at 0 < ε ≤ 1/100000.
The computation behind Table 1 has three parts, each a LEAF here:
* τ_n is increasing in ε, since t ξ = t κ + t (γ + κ) ε + 2 γ c_(n-1) ^ (n-2) + 2 c_n ^ (n-1)
  is increasing in t and in ε, so ε = 1/100000 is the worst case;
* the finite sums up to n = 500 at ε = 1/100000, interval values 131.5073810 over odd n and
  134.8362246 over even n;
* the tail beyond n = 500, where c_n = 0.9607 and τ_n decays geometrically, interval value
  about 3.1e-6 in total.
The two old LEAFs are proved here from these, as twins.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122cTwinT

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- From m = 2 on, every Table 2 value, and 0.9607 of Lemma 8, lies in [0, 0.9607]. -/
private lemma bjsC306_range1122c (m : ℕ) (hm : 2 ≤ m) :
    0 ≤ bjsC306 m ∧ bjsC306 m ≤ 0.9607 := by
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
  by_cases h500 : m ≤ 500
  · rw [if_pos h500]; norm_num
  rw [if_neg h500]
  norm_num

/-- The Table 2 values c_m of display 31 are nonnegative. -/
private lemma bjsC306_nonneg1122c (n : ℕ) : 0 ≤ bjsC306 n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> norm_num [bjsC306]
  · exact (bjsC306_range1122c n h).1

/-- Any exponential of an argument at most 1 is at most 4. -/
private lemma exp_le_four1122c {x : ℝ} (hx : x ≤ 1) : Real.exp x ≤ 4 :=
  le_of_lt (lt_of_le_of_lt (Real.exp_le_exp.mpr hx) (by linarith [Real.exp_one_lt_three]))

/-- Clearing the denominator in one branch of display 31. -/
private lemma mul_xi1122c (γ κ ε cp cc t : ℝ) (ht : t ≠ 0) :
    t * bjsXi306 γ κ ε cp cc t = t * κ + t * (γ + κ) * ε + 2 * γ * cp + 2 * cc := by
  unfold bjsXi306
  field_simp

/-- Pushing a nonnegative factor into a two-term maximum, under a bound. -/
private lemma mul_max2_leR1122c {t C a b : ℝ} (ht : 0 ≤ t)
    (h1 : t * a ≤ C) (h2 : t * b ≤ C) : t * max a b ≤ C := by
  rw [mul_max_of_nonneg _ _ ht]
  exact max_le h1 h2

/-- Pushing a nonnegative factor into a two-term maximum, on both sides. -/
private lemma mul_max2_le1122c {t t0 a b c d : ℝ} (ht : 0 ≤ t) (ht0 : 0 ≤ t0)
    (h1 : t * a ≤ t0 * c) (h2 : t * b ≤ t0 * d) : t * max a b ≤ t0 * max c d := by
  rw [mul_max_of_nonneg _ _ ht, mul_max_of_nonneg _ _ ht0]
  exact max_le_max h1 h2

/-- Every branch of display 31, cleared, is at most 0.9608 t + 11 q. -/
private lemma branch_le1122c {γ κ ε cp cc q t : ℝ}
    (hγ0 : 0 ≤ γ) (hγ4 : γ ≤ 4) (hκ : κ ≤ 0.9607)
    (hε0 : 0 ≤ ε) (hε5 : ε ≤ 1 / 100000)
    (hcp0 : 0 ≤ cp) (hcc0 : 0 ≤ cc) (hcq : cp ≤ q) (hcq2 : cc ≤ q) (hq : 0 ≤ q)
    (ht : 0 ≤ t) :
    t * bjsXi306 γ κ ε cp cc t ≤ 0.9608 * t + 11 * q := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h]
    simpa using (show (0:ℝ) ≤ 11 * q by linarith)
  · rw [mul_xi1122c γ κ ε cp cc t h.ne']
    have h1 : t * κ ≤ 0.9607 * t := by
      calc t * κ = κ * t := by ring
        _ ≤ 0.9607 * t := mul_le_mul_of_nonneg_right hκ (le_of_lt h)
    have h2 : t * (γ + κ) * ε ≤ t * (1 / 20000) := by
      have hgk : γ + κ ≤ 5 := by linarith
      have hmul : (γ + κ) * ε ≤ 5 * (1 / 100000) :=
        mul_le_mul hgk hε5 hε0 (by norm_num)
      have hmul' : (γ + κ) * ε ≤ 1 / 20000 := by linarith
      calc t * (γ + κ) * ε = t * ((γ + κ) * ε) := by ring
        _ ≤ t * (1 / 20000) := mul_le_mul_of_nonneg_left hmul' (le_of_lt h)
    have h3 : 2 * γ * cp ≤ 8 * q := by nlinarith
    have h4 : 2 * cc ≤ 2 * q := by nlinarith
    nlinarith

/-- The second odd branch of display 31, cleared, is at most 0.9608 t + 11 q. -/
private lemma branch2_le1122c {ε cp cc q t : ℝ} (hε0 : 0 ≤ ε) (hε5 : ε ≤ 1 / 100000)
    (hcp0 : 0 ≤ cp) (hcc0 : 0 ≤ cc) (hcq : cp ≤ q) (hcq2 : cc ≤ q) (hq : 0 ≤ q)
    (ht : 0 ≤ t) :
    t * (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t + 2 * (2 + ε) * cc / t) ≤
      0.9608 * t + 11 * q := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h]
    simpa using (show (0:ℝ) ≤ 11 * q by linarith)
  · have e1 : t * (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t +
        2 * (2 + ε) * cc / t) =
        t * (0.9214 + (5 + 4 * ε) * ε) + 6 * (1 + ε) * cp + 2 * (2 + ε) * cc := by
      field_simp
    rw [e1]
    have h1 : t * (0.9214 + (5 + 4 * ε) * ε) ≤ t * 0.9215 := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt h)
      nlinarith
    have h2 : 6 * (1 + ε) * cp ≤ 6.1 * q := by nlinarith
    have h3 : 2 * (2 + ε) * cc ≤ 4.1 * q := by nlinarith
    nlinarith

/-- The τ_n are positive from n = 1 on. -/
private lemma tau_pos1122c (ε : ℝ) (hε : 0 ≤ ε) :
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
      have hcp : 0 ≤ bjsC306 (m + 1) ^ m := pow_nonneg (bjsC306_nonneg1122c _) _
      have hcc : 0 ≤ bjsC306 (m + 2) ^ (m + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
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
private lemma tau_nonneg1122c (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ bjsTau306 bjsC306 ε n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [bjsTau306]
  · exact le_of_lt (tau_pos1122c ε hε n h)

/-- The cleared branches of display 31 are increasing in both τ_(n-1) and ε. -/
private lemma mul_xi_mono1122c {γ κ ε ε0 cp cc t t0 : ℝ} (hγ : 0 ≤ γ) (hκ : 0 < κ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ ε0) (ht : 0 < t) (htt : t ≤ t0) :
    t * bjsXi306 γ κ ε cp cc t ≤ t0 * bjsXi306 γ κ ε0 cp cc t0 := by
  have ht' : t ≠ 0 := ht.ne'
  have ht0' : t0 ≠ 0 := (lt_of_lt_of_le ht htt).ne'
  rw [mul_xi1122c γ κ ε cp cc t ht', mul_xi1122c γ κ ε0 cp cc t0 ht0']
  have hA : t * (κ + (γ + κ) * ε) ≤ t0 * (κ + (γ + κ) * ε0) := by
    refine mul_le_mul htt ?_ ?_ ?_
    · nlinarith
    · have h1 : 0 ≤ (γ + κ) * ε := mul_nonneg (by linarith) hε0
      linarith
    · linarith
  nlinarith [hA]

/-- The second odd branch of display 31, cleared, is increasing in both τ_(n-1) and ε. -/
private lemma mul_odd2_mono1122c {ε ε0 cp cc t t0 : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ ε0)
    (hcp : 0 ≤ cp) (hcc : 0 ≤ cc) (ht : 0 < t) (htt : t ≤ t0) :
    t * (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t + 2 * (2 + ε) * cc / t) ≤
      t0 * (0.9214 + (5 + 4 * ε0) * ε0 + 6 * (1 + ε0) * cp / t0 +
        2 * (2 + ε0) * cc / t0) := by
  have ht' : t ≠ 0 := ht.ne'
  have ht0' : t0 ≠ 0 := (lt_of_lt_of_le ht htt).ne'
  have e1 : t * (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t +
      2 * (2 + ε) * cc / t) =
      t * (0.9214 + (5 + 4 * ε) * ε) + 6 * (1 + ε) * cp + 2 * (2 + ε) * cc := by
    field_simp
  have e2 : t0 * (0.9214 + (5 + 4 * ε0) * ε0 + 6 * (1 + ε0) * cp / t0 +
      2 * (2 + ε0) * cc / t0) =
      t0 * (0.9214 + (5 + 4 * ε0) * ε0) + 6 * (1 + ε0) * cp + 2 * (2 + ε0) * cc := by
    field_simp
  rw [e1, e2]
  have hA : t * (0.9214 + (5 + 4 * ε) * ε) ≤ t0 * (0.9214 + (5 + 4 * ε0) * ε0) := by
    refine mul_le_mul htt ?_ ?_ ?_
    · nlinarith
    · nlinarith
    · linarith
  have hB : 6 * (1 + ε) * cp ≤ 6 * (1 + ε0) * cp := by nlinarith
  have hC : 2 * (2 + ε) * cc ≤ 2 * (2 + ε0) * cc := by nlinarith
  linarith

/-- The affine step of display 31: each τ step multiplies by at most 0.9608. -/
private lemma tau_step1122c (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hε5 : ε ≤ 1 / 100000) :
    bjsTau306 bjsC306 ε (n + 2) ≤
      (0.9608 : ℝ) * bjsTau306 bjsC306 ε (n + 1) + 11 * (0.9607 : ℝ) ^ n := by
  have hq : (0:ℝ) ≤ (0.9607 : ℝ) ^ n := pow_nonneg (by norm_num) n
  have hcp0 : (0:ℝ) ≤ bjsC306 (n + 1) ^ n := pow_nonneg (bjsC306_nonneg1122c _) n
  have hcc0 : (0:ℝ) ≤ bjsC306 (n + 2) ^ (n + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 (n + 1) ^ n ≤ (0.9607:ℝ) ^ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · exact pow_le_pow_left₀ (bjsC306_nonneg1122c _)
        ((bjsC306_range1122c (n + 1) (by omega)).2) n
  have hcc : bjsC306 (n + 2) ^ (n + 1) ≤ (0.9607:ℝ) ^ n := by
    have h1 : bjsC306 (n + 2) ^ (n + 1) ≤ (0.9607:ℝ) ^ (n + 1) :=
      pow_le_pow_left₀ (bjsC306_nonneg1122c _)
        ((bjsC306_range1122c (n + 2) (by omega)).2) (n + 1)
    refine le_trans h1 ?_
    rw [pow_succ]
    exact mul_le_of_le_one_right hq (by norm_num)
  have ht : (0:ℝ) ≤ bjsTau306 bjsC306 ε (n + 1) := tau_nonneg1122c ε hε (n + 1)
  simp only [bjsTau306]
  by_cases hpar : Even (n + 2)
  · rw [if_pos hpar]
    refine mul_max2_leR1122c ht ?_ ?_
    · refine mul_max2_leR1122c ht ?_ ?_
      · refine mul_max2_leR1122c ht ?_ ?_
        · exact branch_le1122c (by norm_num) (by norm_num) (by norm_num) hε hε5 hcp0 hcc0 hcp hcc hq ht
        · exact branch_le1122c (exp_pos 0.2).le (exp_le_four1122c (by norm_num)) (by norm_num) hε hε5 hcp0 hcc0 hcp hcc hq ht
      · refine mul_max2_leR1122c ht ?_ ?_
        · exact branch_le1122c (exp_pos 0.4).le (exp_le_four1122c (by norm_num)) (by norm_num) hε hε5 hcp0 hcc0 hcp hcc hq ht
        · exact branch_le1122c (exp_pos 0.6).le (exp_le_four1122c (by norm_num)) (by norm_num) hε hε5 hcp0 hcc0 hcp hcc hq ht
    · refine mul_max2_leR1122c ht ?_ ?_
      · exact branch_le1122c (exp_pos 0.8).le (exp_le_four1122c (by norm_num)) (by norm_num) hε hε5 hcp0 hcc0 hcp hcc hq ht
      · exact branch_le1122c (by positivity) (by nlinarith [Real.exp_one_lt_three]) (by norm_num) hε hε5 hcp0 hcc0 hcp hcc hq ht
  · rw [if_neg hpar]
    exact mul_max2_leR1122c ht
      (branch_le1122c (by positivity) (by nlinarith [Real.exp_one_lt_three]) (by norm_num) hε hε5 hcp0 hcc0 hcp hcc hq ht)
      (branch2_le1122c hε hε5 hcp0 hcc0 hcp hcc hq ht)

/-- Geometric bound on partial sums of 0 ≤ r < 1. -/
private lemma geom_range_le1122c (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    ∑ k ∈ Finset.range m, r ^ k ≤ 1 / (1 - r) := by
  have hden : 0 < 1 - r := by linarith
  rw [geom_sum_eq (ne_of_lt hr1)]
  have hEq : (r ^ m - 1) / (r - 1) = (1 - r ^ m) / (1 - r) := by
    have h1 : r - 1 ≠ 0 := by linarith
    have h2 : (1:ℝ) - r ≠ 0 := by linarith
    field_simp
    ring
  rw [hEq, div_le_div_iff₀ hden hden]
  have hp : 0 ≤ r ^ m := pow_nonneg hr0 m
  nlinarith

/-- Uniform geometric bound on the τ_n: τ_n ≤ 3000 · 0.965^n. -/
private lemma tau_geometric1122c (ε : ℝ) (hε : 0 ≤ ε) (hε5 : ε ≤ 1 / 100000) :
    ∀ n, bjsTau306 bjsC306 ε n ≤ 3000 * (0.965 : ℝ) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · norm_num [bjsTau306]
    · norm_num [bjsTau306]
    · have h1 := tau_step1122c m ε hε hε5
      have h2 : bjsTau306 bjsC306 ε (m + 1) ≤ 3000 * (0.965:ℝ) ^ (m + 1) :=
        ih (m + 1) (by omega)
      have hq1 : (0.9607:ℝ) ^ m ≤ (0.965:ℝ) ^ m :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) m
      have hp : (0:ℝ) < (0.965:ℝ) ^ m := pow_pos (by norm_num) m
      have e1 : (0.965:ℝ) ^ (m + 1) = (0.965:ℝ) ^ m * 0.965 := by rw [pow_succ]
      have esq : (0.965:ℝ) ^ 2 = 0.931225 := by norm_num
      have e2 : (0.965:ℝ) ^ (m + 2) = (0.965:ℝ) ^ m * 0.931225 := by
        rw [pow_add, esq]
      rw [e1] at h2
      rw [e2]
      nlinarith [h1, h2, hq1, hp]


/-- LEAF: BJS Lemma 11, display 31, monotonicity of the recursion in ε: for
0 < ε ≤ 1/100000, τ_n(ε) ≤ τ_n(1/100000) for every n, since each ξ in the recursion is
κ + (γ + κ) ε + 2 γ cp / t + 2 cc / t and t ξ is increasing in t and ε.
Class MEDIUM: induction on n through the maxima. -/
theorem tau_mono_eps1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (n : ℕ) :
    bjsTau306 bjsC306 ε n ≤ bjsTau306 bjsC306 (1 / 100000) n := by
  have hε0 : 0 ≤ ε := le_of_lt hε
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · norm_num [bjsTau306]
    · norm_num [bjsTau306]
    · have ht : 0 < bjsTau306 bjsC306 ε (m + 1) := tau_pos1122c ε hε0 (m + 1) (by omega)
      have htt : bjsTau306 bjsC306 ε (m + 1) ≤ bjsTau306 bjsC306 (1 / 100000) (m + 1) :=
        ih (m + 1) (by omega)
      have ht0 : 0 ≤ bjsTau306 bjsC306 (1 / 100000) (m + 1) :=
        le_of_lt (lt_of_lt_of_le ht htt)
      simp only [bjsTau306]
      split_ifs with hpar
      · refine mul_max2_le1122c (le_of_lt ht) ht0 ?_ ?_
        · refine mul_max2_le1122c (le_of_lt ht) ht0 ?_ ?_
          · refine mul_max2_le1122c (le_of_lt ht) ht0 ?_ ?_
            · exact mul_xi_mono1122c (by norm_num) (by norm_num) hε0 hε5 ht htt
            · exact mul_xi_mono1122c (exp_pos 0.2).le (by norm_num) hε0 hε5 ht htt
          · refine mul_max2_le1122c (le_of_lt ht) ht0 ?_ ?_
            · exact mul_xi_mono1122c (exp_pos 0.4).le (by norm_num) hε0 hε5 ht htt
            · exact mul_xi_mono1122c (exp_pos 0.6).le (by norm_num) hε0 hε5 ht htt
        · refine mul_max2_le1122c (le_of_lt ht) ht0 ?_ ?_
          · exact mul_xi_mono1122c (exp_pos 0.8).le (by norm_num) hε0 hε5 ht htt
          · exact mul_xi_mono1122c (by positivity) (by norm_num) hε0 hε5 ht htt
      · refine mul_max2_le1122c (le_of_lt ht) ht0 ?_ ?_
        · exact mul_xi_mono1122c (by positivity) (by norm_num) hε0 hε5 ht htt
        · exact mul_odd2_mono1122c hε0 hε5 (pow_nonneg (bjsC306_nonneg1122c _) _)
            (pow_nonneg (bjsC306_nonneg1122c _) _) ht htt

/-- exp(1/5) ≤ 1.2214028. -/
private lemma exp_02_le1122c : Real.exp 0.2 ≤ 1.2214028 := by
  have h : (0.2 : ℝ) = 1 / 5 := by norm_num
  rw [h]
  refine le_of_pow_le_pow_left₀ (by norm_num : (5:ℕ) ≠ 0) (by norm_num) ?_
  have h5 : (Real.exp (1 / 5)) ^ 5 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h5]
  calc Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
    _ ≤ (1.2214028 : ℝ) ^ 5 := by norm_num

/-- exp(2/5) ≤ 1.4918247999. -/
private lemma exp_04_le1122c : Real.exp 0.4 ≤ 1.4918247999 := by
  rw [show (0.4 : ℝ) = 0.2 + 0.2 from by norm_num, Real.exp_add]
  calc Real.exp 0.2 * Real.exp 0.2 ≤ 1.2214028 * 1.2214028 :=
        mul_le_mul exp_02_le1122c exp_02_le1122c (Real.exp_pos _).le (by norm_num)
    _ ≤ 1.4918247999 := by norm_num

/-- exp(3/5) ≤ 1.8221189877. -/
private lemma exp_06_le1122c : Real.exp 0.6 ≤ 1.8221189878 := by
  rw [show (0.6 : ℝ) = 0.2 + 0.4 from by norm_num, Real.exp_add]
  calc Real.exp 0.2 * Real.exp 0.4 ≤ 1.2214028 * 1.4918247999 :=
        mul_le_mul exp_02_le1122c exp_04_le1122c (Real.exp_pos _).le (by norm_num)
    _ ≤ 1.8221189878 := by norm_num

/-- exp(4/5) ≤ 2.2255412335. -/
private lemma exp_08_le1122c : Real.exp 0.8 ≤ 2.2255412336 := by
  rw [show (0.8 : ℝ) = 0.4 + 0.4 from by norm_num, Real.exp_add]
  calc Real.exp 0.4 * Real.exp 0.4 ≤ 1.4918247999 * 1.4918247999 :=
        mul_le_mul exp_04_le1122c exp_04_le1122c (Real.exp_pos _).le (by norm_num)
    _ ≤ 2.2255412336 := by norm_num

/-- 4 exp 1 / 3 ≤ 3.6243757720, the γ₃ of Lemma 9. -/
private lemma four_exp_one_le1122c : 4 * Real.exp 1 / 3 ≤ 3.6243757720 := by
  nlinarith [Real.exp_one_lt_d9]

/-- A cleared branch of display 31, bounded by its value at the upper endpoints. -/
private lemma xi_le_of1122c {γ γu κ ε cp cc t C A qcp qcc : ℝ}
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
  · rw [mul_xi1122c γ κ ε cp cc t h.ne']
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
private lemma odd2_le_of1122c {ε cp cc t C A qcp qcc : ℝ}
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
private lemma tauA_2_1122c :
    bjsTau306 bjsC306 (1 / 100000) 2 ≤ 10.413585322274 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((0:ℕ) + 1) ≤ 3 := by norm_num [bjsTau306]
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((0:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((0:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((0:ℕ) + 1) ^ 0 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((0:ℕ) + 2) ^ (0 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((0:ℕ) + 1) ^ 0 ≤ 1 := by norm_num [bjsC306]
  have hcc : bjsC306 ((0:ℕ) + 2) ^ (0 + 1) ≤ 0.33 := by norm_num [bjsC306]
  rw [show (2:ℕ) = (0:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((0:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 3: τ_3 ≤ 12.184021041375. -/
private lemma tauA_3_1122c :
    bjsTau306 bjsC306 (1 / 100000) 3 ≤ 12.184021041375 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((1:ℕ) + 1) ≤ 10.413585322274 := tauA_2_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((1:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((1:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((1:ℕ) + 1) ^ 1 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((1:ℕ) + 2) ^ (1 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((1:ℕ) + 1) ^ 1 ≤ 0.33 := by norm_num [bjsC306]
  have hcc : bjsC306 ((1:ℕ) + 2) ^ (1 + 1) ≤ 0.1521 := by norm_num [bjsC306]
  rw [show (3:ℕ) = (1:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((1:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 4: τ_4 ≤ 12.198334899666. -/
private lemma tauA_4_1122c :
    bjsTau306 bjsC306 (1 / 100000) 4 ≤ 12.198334899666 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((2:ℕ) + 1) ≤ 12.184021041375 := tauA_3_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((2:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((2:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((2:ℕ) + 1) ^ 2 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((2:ℕ) + 2) ^ (2 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((2:ℕ) + 1) ^ 2 ≤ 0.1521 := by norm_num [bjsC306]
  have hcc : bjsC306 ((2:ℕ) + 2) ^ (2 + 1) ≤ 0.091125 := by norm_num [bjsC306]
  rw [show (4:ℕ) = (2:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((2:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 5: τ_5 ≤ 12.057520918719. -/
private lemma tauA_5_1122c :
    bjsTau306 bjsC306 (1 / 100000) 5 ≤ 12.057520918719 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((3:ℕ) + 1) ≤ 12.198334899666 := tauA_4_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((3:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((3:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((3:ℕ) + 1) ^ 3 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((3:ℕ) + 2) ^ (3 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((3:ℕ) + 1) ^ 3 ≤ 0.091125 := by norm_num [bjsC306]
  have hcc : bjsC306 ((3:ℕ) + 2) ^ (3 + 1) ≤ 0.0676521 := by norm_num [bjsC306]
  rw [show (5:ℕ) = (3:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((3:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 6: τ_6 ≤ 11.811034158426. -/
private lemma tauA_6_1122c :
    bjsTau306 bjsC306 (1 / 100000) 6 ≤ 11.811034158426 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((4:ℕ) + 1) ≤ 12.057520918719 := tauA_5_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((4:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((4:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((4:ℕ) + 1) ^ 4 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((4:ℕ) + 2) ^ (4 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((4:ℕ) + 1) ^ 4 ≤ 0.0676521 := by norm_num [bjsC306]
  have hcc : bjsC306 ((4:ℕ) + 2) ^ (4 + 1) ≤ 0.0459166 := by norm_num [bjsC306]
  rw [show (6:ℕ) = (4:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((4:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 7: τ_7 ≤ 11.295966470933. -/
private lemma tauA_7_1122c :
    bjsTau306 bjsC306 (1 / 100000) 7 ≤ 11.295966470933 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((5:ℕ) + 1) ≤ 11.811034158426 := tauA_6_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((5:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((5:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((5:ℕ) + 1) ^ 5 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((5:ℕ) + 2) ^ (5 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((5:ℕ) + 1) ^ 5 ≤ 0.0459166 := by norm_num [bjsC306]
  have hcc : bjsC306 ((5:ℕ) + 2) ^ (5 + 1) ≤ 0.0342965 := by norm_num [bjsC306]
  rw [show (7:ℕ) = (5:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((5:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 8: τ_8 ≤ 10.96500926864. -/
private lemma tauA_8_1122c :
    bjsTau306 bjsC306 (1 / 100000) 8 ≤ 10.96500926864 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((6:ℕ) + 1) ≤ 11.295966470933 := tauA_7_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((6:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((6:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((6:ℕ) + 1) ^ 6 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((6:ℕ) + 2) ^ (6 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((6:ℕ) + 1) ^ 6 ≤ 0.0342965 := by norm_num [bjsC306]
  have hcc : bjsC306 ((6:ℕ) + 2) ^ (6 + 1) ≤ 0.0220799 := by norm_num [bjsC306]
  rw [show (8:ℕ) = (6:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((6:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 9: τ_9 ≤ 10.312872103185. -/
private lemma tauA_9_1122c :
    bjsTau306 bjsC306 (1 / 100000) 9 ≤ 10.312872103185 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((7:ℕ) + 1) ≤ 10.96500926864 := tauA_8_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((7:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((7:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((7:ℕ) + 1) ^ 7 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((7:ℕ) + 2) ^ (7 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((7:ℕ) + 1) ^ 7 ≤ 0.0220799 := by norm_num [bjsC306]
  have hcc : bjsC306 ((7:ℕ) + 2) ^ (7 + 1) ≤ 0.0191708 := by norm_num [bjsC306]
  rw [show (9:ℕ) = (7:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((7:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 10: τ_10 ≤ 9.969508434014. -/
private lemma tauA_10_1122c :
    bjsTau306 bjsC306 (1 / 100000) 10 ≤ 9.969508434014 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((8:ℕ) + 1) ≤ 10.312872103185 := tauA_9_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((8:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((8:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((8:ℕ) + 1) ^ 8 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((8:ℕ) + 2) ^ (8 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((8:ℕ) + 1) ^ 8 ≤ 0.0191708 := by norm_num [bjsC306]
  have hcc : bjsC306 ((8:ℕ) + 2) ^ (8 + 1) ≤ 0.0116942 := by norm_num [bjsC306]
  rw [show (10:ℕ) = (8:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((8:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 11: τ_11 ≤ 9.295966889149. -/
private lemma tauA_11_1122c :
    bjsTau306 bjsC306 (1 / 100000) 11 ≤ 9.295966889149 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((9:ℕ) + 1) ≤ 9.969508434014 := tauA_10_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((9:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((9:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((9:ℕ) + 1) ^ 9 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((9:ℕ) + 2) ^ (9 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((9:ℕ) + 1) ^ 9 ≤ 0.0116942 := by norm_num [bjsC306]
  have hcc : bjsC306 ((9:ℕ) + 2) ^ (9 + 1) ≤ 0.00984931 := by norm_num [bjsC306]
  rw [show (11:ℕ) = (9:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((9:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 12: τ_12 ≤ 8.962926416429. -/
private lemma tauA_12_1122c :
    bjsTau306 bjsC306 (1 / 100000) 12 ≤ 8.962926416429 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((10:ℕ) + 1) ≤ 9.295966889149 := tauA_11_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((10:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((10:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((10:ℕ) + 1) ^ 10 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((10:ℕ) + 2) ^ (10 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((10:ℕ) + 1) ^ 10 ≤ 0.00984931 := by norm_num [bjsC306]
  have hcc : bjsC306 ((10:ℕ) + 2) ^ (10 + 1) ≤ 0.00620507 := by norm_num [bjsC306]
  rw [show (12:ℕ) = (10:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((10:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 13: τ_13 ≤ 8.315008916756. -/
private lemma tauA_13_1122c :
    bjsTau306 bjsC306 (1 / 100000) 13 ≤ 8.315008916756 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((11:ℕ) + 1) ≤ 8.962926416429 := tauA_12_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((11:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((11:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((11:ℕ) + 1) ^ 11 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((11:ℕ) + 2) ^ (11 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((11:ℕ) + 1) ^ 11 ≤ 0.00620507 := by norm_num [bjsC306]
  have hcc : bjsC306 ((11:ℕ) + 2) ^ (11 + 1) ≤ 0.00472237 := by norm_num [bjsC306]
  rw [show (13:ℕ) = (11:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((11:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 14: τ_14 ≤ 8.005231258708. -/
private lemma tauA_14_1122c :
    bjsTau306 bjsC306 (1 / 100000) 14 ≤ 8.005231258708 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((12:ℕ) + 1) ≤ 8.315008916756 := tauA_13_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((12:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((12:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((12:ℕ) + 1) ^ 12 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((12:ℕ) + 2) ^ (12 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((12:ℕ) + 1) ^ 12 ≤ 0.00472237 := by norm_num [bjsC306]
  have hcc : bjsC306 ((12:ℕ) + 2) ^ (12 + 1) ≤ 0.00369721 := by norm_num [bjsC306]
  rw [show (14:ℕ) = (12:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((12:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 15: τ_15 ≤ 7.410507407889. -/
private lemma tauA_15_1122c :
    bjsTau306 bjsC306 (1 / 100000) 15 ≤ 7.410507407889 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((13:ℕ) + 1) ≤ 8.005231258708 := tauA_14_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((13:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((13:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((13:ℕ) + 1) ^ 13 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((13:ℕ) + 2) ^ (13 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((13:ℕ) + 1) ^ 13 ≤ 0.00369721 := by norm_num [bjsC306]
  have hcc : bjsC306 ((13:ℕ) + 2) ^ (13 + 1) ≤ 0.00297588 := by norm_num [bjsC306]
  rw [show (15:ℕ) = (13:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((13:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 16: τ_16 ≤ 7.129299684578. -/
private lemma tauA_16_1122c :
    bjsTau306 bjsC306 (1 / 100000) 16 ≤ 7.129299684578 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((14:ℕ) + 1) ≤ 7.410507407889 := tauA_15_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((14:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((14:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((14:ℕ) + 1) ^ 14 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((14:ℕ) + 2) ^ (14 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((14:ℕ) + 1) ^ 14 ≤ 0.00297588 := by norm_num [bjsC306]
  have hcc : bjsC306 ((14:ℕ) + 2) ^ (14 + 1) ≤ 0.00196408 := by norm_num [bjsC306]
  rw [show (16:ℕ) = (14:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((14:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 17: τ_17 ≤ 6.586263020977. -/
private lemma tauA_17_1122c :
    bjsTau306 bjsC306 (1 / 100000) 17 ≤ 6.586263020977 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((15:ℕ) + 1) ≤ 7.129299684578 := tauA_16_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((15:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((15:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((15:ℕ) + 1) ^ 15 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((15:ℕ) + 2) ^ (15 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((15:ℕ) + 1) ^ 15 ≤ 0.00196408 := by norm_num [bjsC306]
  have hcc : bjsC306 ((15:ℕ) + 2) ^ (15 + 1) ≤ 0.0012963 := by norm_num [bjsC306]
  rw [show (17:ℕ) = (15:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((15:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 18: τ_18 ≤ 6.331855727112. -/
private lemma tauA_18_1122c :
    bjsTau306 bjsC306 (1 / 100000) 18 ≤ 6.331855727112 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((16:ℕ) + 1) ≤ 6.586263020977 := tauA_17_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((16:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((16:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((16:ℕ) + 1) ^ 16 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((16:ℕ) + 2) ^ (16 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((16:ℕ) + 1) ^ 16 ≤ 0.0012963 := by norm_num [bjsC306]
  have hcc : bjsC306 ((16:ℕ) + 2) ^ (16 + 1) ≤ 0.000855553 := by norm_num [bjsC306]
  rw [show (18:ℕ) = (16:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((16:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 19: τ_19 ≤ 5.842582630418. -/
private lemma tauA_19_1122c :
    bjsTau306 bjsC306 (1 / 100000) 19 ≤ 5.842582630418 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((17:ℕ) + 1) ≤ 6.331855727112 := tauA_18_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((17:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((17:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((17:ℕ) + 1) ^ 17 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((17:ℕ) + 2) ^ (17 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((17:ℕ) + 1) ^ 17 ≤ 0.000855553 := by norm_num [bjsC306]
  have hcc : bjsC306 ((17:ℕ) + 2) ^ (17 + 1) ≤ 0.000740196 := by norm_num [bjsC306]
  rw [show (19:ℕ) = (17:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((17:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 20: τ_20 ≤ 5.615555942561. -/
private lemma tauA_20_1122c :
    bjsTau306 bjsC306 (1 / 100000) 20 ≤ 5.615555942561 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((18:ℕ) + 1) ≤ 5.842582630418 := tauA_19_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((18:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((18:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((18:ℕ) + 1) ^ 18 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((18:ℕ) + 2) ^ (18 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((18:ℕ) + 1) ^ 18 ≤ 0.000740196 := by norm_num [bjsC306]
  have hcc : bjsC306 ((18:ℕ) + 2) ^ (18 + 1) ≤ 0.000495931 := by norm_num [bjsC306]
  rw [show (20:ℕ) = (18:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((18:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 21: τ_21 ≤ 5.179217118213. -/
private lemma tauA_21_1122c :
    bjsTau306 bjsC306 (1 / 100000) 21 ≤ 5.179217118213 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((19:ℕ) + 1) ≤ 5.615555942561 := tauA_20_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((19:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((19:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((19:ℕ) + 1) ^ 19 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((19:ℕ) + 2) ^ (19 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((19:ℕ) + 1) ^ 19 ≤ 0.000495931 := by norm_num [bjsC306]
  have hcc : bjsC306 ((19:ℕ) + 2) ^ (19 + 1) ≤ 0.000446867 := by norm_num [bjsC306]
  rw [show (21:ℕ) = (19:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((19:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 22: τ_22 ≤ 4.977276908378. -/
private lemma tauA_22_1122c :
    bjsTau306 bjsC306 (1 / 100000) 22 ≤ 4.977276908378 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((20:ℕ) + 1) ≤ 5.179217118213 := tauA_21_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((20:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((20:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((20:ℕ) + 1) ^ 20 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((20:ℕ) + 2) ^ (20 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((20:ℕ) + 1) ^ 20 ≤ 0.000446867 := by norm_num [bjsC306]
  have hcc : bjsC306 ((20:ℕ) + 2) ^ (20 + 1) ≤ 0.00030387 := by norm_num [bjsC306]
  rw [show (22:ℕ) = (20:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((20:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 23: τ_23 ≤ 4.588961579581. -/
private lemma tauA_23_1122c :
    bjsTau306 bjsC306 (1 / 100000) 23 ≤ 4.588961579581 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((21:ℕ) + 1) ≤ 4.977276908378 := tauA_22_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((21:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((21:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((21:ℕ) + 1) ^ 21 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((21:ℕ) + 2) ^ (21 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((21:ℕ) + 1) ^ 21 ≤ 0.00030387 := by norm_num [bjsC306]
  have hcc : bjsC306 ((21:ℕ) + 2) ^ (21 + 1) ≤ 0.000206632 := by norm_num [bjsC306]
  rw [show (23:ℕ) = (21:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((21:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 24: τ_24 ≤ 4.409399649274. -/
private lemma tauA_24_1122c :
    bjsTau306 bjsC306 (1 / 100000) 24 ≤ 4.409399649274 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((22:ℕ) + 1) ≤ 4.588961579581 := tauA_23_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((22:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((22:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((22:ℕ) + 1) ^ 22 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((22:ℕ) + 2) ^ (22 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((22:ℕ) + 1) ^ 22 ≤ 0.000206632 := by norm_num [bjsC306]
  have hcc : bjsC306 ((22:ℕ) + 2) ^ (22 + 1) ≤ 0.00014051 := by norm_num [bjsC306]
  rw [show (24:ℕ) = (22:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((22:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 25: τ_25 ≤ 4.064266564529. -/
private lemma tauA_25_1122c :
    bjsTau306 bjsC306 (1 / 100000) 25 ≤ 4.064266564529 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((23:ℕ) + 1) ≤ 4.409399649274 := tauA_24_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((23:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((23:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((23:ℕ) + 1) ^ 23 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((23:ℕ) + 2) ^ (23 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((23:ℕ) + 1) ^ 23 ≤ 0.00014051 := by norm_num [bjsC306]
  have hcc : bjsC306 ((23:ℕ) + 2) ^ (23 + 1) ≤ 0.0000955464 := by norm_num [bjsC306]
  rw [show (25:ℕ) = (23:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((23:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 26: τ_26 ≤ 3.904941612418. -/
private lemma tauA_26_1122c :
    bjsTau306 bjsC306 (1 / 100000) 26 ≤ 3.904941612418 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((24:ℕ) + 1) ≤ 4.064266564529 := tauA_25_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((24:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((24:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((24:ℕ) + 1) ^ 24 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((24:ℕ) + 2) ^ (24 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((24:ℕ) + 1) ^ 24 ≤ 0.0000955464 := by norm_num [bjsC306]
  have hcc : bjsC306 ((24:ℕ) + 2) ^ (24 + 1) ≤ 0.0000649715 := by norm_num [bjsC306]
  rw [show (26:ℕ) = (24:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((24:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 27: τ_27 ≤ 3.598856591715. -/
private lemma tauA_27_1122c :
    bjsTau306 bjsC306 (1 / 100000) 27 ≤ 3.598856591715 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((25:ℕ) + 1) ≤ 3.904941612418 := tauA_26_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((25:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((25:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((25:ℕ) + 1) ^ 25 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((25:ℕ) + 2) ^ (25 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((25:ℕ) + 1) ^ 25 ≤ 0.0000649715 := by norm_num [bjsC306]
  have hcc : bjsC306 ((25:ℕ) + 2) ^ (25 + 1) ≤ 0.0000645768 := by norm_num [bjsC306]
  rw [show (27:ℕ) = (25:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((25:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 28: τ_28 ≤ 3.457710360042. -/
private lemma tauA_28_1122c :
    bjsTau306 bjsC306 (1 / 100000) 28 ≤ 3.457710360042 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((26:ℕ) + 1) ≤ 3.598856591715 := tauA_27_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((26:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((26:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((26:ℕ) + 1) ^ 26 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((26:ℕ) + 2) ^ (26 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((26:ℕ) + 1) ^ 26 ≤ 0.0000645768 := by norm_num [bjsC306]
  have hcc : bjsC306 ((26:ℕ) + 2) ^ (26 + 1) ≤ 0.000044558 := by norm_num [bjsC306]
  rw [show (28:ℕ) = (26:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((26:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 29: τ_29 ≤ 3.186497544333. -/
private lemma tauA_29_1122c :
    bjsTau306 bjsC306 (1 / 100000) 29 ≤ 3.186497544333 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((27:ℕ) + 1) ≤ 3.457710360042 := tauA_28_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((27:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((27:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((27:ℕ) + 1) ^ 27 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((27:ℕ) + 2) ^ (27 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((27:ℕ) + 1) ^ 27 ≤ 0.000044558 := by norm_num [bjsC306]
  have hcc : bjsC306 ((27:ℕ) + 2) ^ (27 + 1) ≤ 0.0000307451 := by norm_num [bjsC306]
  rw [show (29:ℕ) = (27:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((27:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 30: τ_30 ≤ 3.061434586899. -/
private lemma tauA_30_1122c :
    bjsTau306 bjsC306 (1 / 100000) 30 ≤ 3.061434586899 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((28:ℕ) + 1) ≤ 3.186497544333 := tauA_29_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((28:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((28:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((28:ℕ) + 1) ^ 28 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((28:ℕ) + 2) ^ (28 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((28:ℕ) + 1) ^ 28 ≤ 0.0000307451 := by norm_num [bjsC306]
  have hcc : bjsC306 ((28:ℕ) + 2) ^ (28 + 1) ≤ 0.0000212141 := by norm_num [bjsC306]
  rw [show (30:ℕ) = (28:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((28:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 31: τ_31 ≤ 2.821144738289. -/
private lemma tauA_31_1122c :
    bjsTau306 bjsC306 (1 / 100000) 31 ≤ 2.821144738289 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((29:ℕ) + 1) ≤ 3.061434586899 := tauA_30_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((29:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((29:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((29:ℕ) + 1) ^ 29 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((29:ℕ) + 2) ^ (29 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((29:ℕ) + 1) ^ 29 ≤ 0.0000212141 := by norm_num [bjsC306]
  have hcc : bjsC306 ((29:ℕ) + 2) ^ (29 + 1) ≤ 0.0000146377 := by norm_num [bjsC306]
  rw [show (31:ℕ) = (29:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((29:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 32: τ_32 ≤ 2.71037853986. -/
private lemma tauA_32_1122c :
    bjsTau306 bjsC306 (1 / 100000) 32 ≤ 2.71037853986 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((30:ℕ) + 1) ≤ 2.821144738289 := tauA_31_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((30:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((30:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((30:ℕ) + 1) ^ 30 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((30:ℕ) + 2) ^ (30 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((30:ℕ) + 1) ^ 30 ≤ 0.0000146377 := by norm_num [bjsC306]
  have hcc : bjsC306 ((30:ℕ) + 2) ^ (30 + 1) ≤ 0.0000101001 := by norm_num [bjsC306]
  rw [show (32:ℕ) = (30:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((30:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 33: τ_33 ≤ 2.497566784024. -/
private lemma tauA_33_1122c :
    bjsTau306 bjsC306 (1 / 100000) 33 ≤ 2.497566784024 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((31:ℕ) + 1) ≤ 2.71037853986 := tauA_32_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((31:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((31:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((31:ℕ) + 1) ^ 31 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((31:ℕ) + 2) ^ (31 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((31:ℕ) + 1) ^ 31 ≤ 0.0000101001 := by norm_num [bjsC306]
  have hcc : bjsC306 ((31:ℕ) + 2) ^ (31 + 1) ≤ 0.00000696901 := by norm_num [bjsC306]
  rw [show (33:ℕ) = (31:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((31:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 34: τ_34 ≤ 2.399484934464. -/
private lemma tauA_34_1122c :
    bjsTau306 bjsC306 (1 / 100000) 34 ≤ 2.399484934464 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((32:ℕ) + 1) ≤ 2.497566784024 := tauA_33_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((32:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((32:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((32:ℕ) + 1) ^ 32 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((32:ℕ) + 2) ^ (32 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((32:ℕ) + 1) ^ 32 ≤ 0.00000696901 := by norm_num [bjsC306]
  have hcc : bjsC306 ((32:ℕ) + 2) ^ (32 + 1) ≤ 0.00000480862 := by norm_num [bjsC306]
  rw [show (34:ℕ) = (32:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((32:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 35: τ_35 ≤ 2.211055892739. -/
private lemma tauA_35_1122c :
    bjsTau306 bjsC306 (1 / 100000) 35 ≤ 2.211055892739 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((33:ℕ) + 1) ≤ 2.399484934464 := tauA_34_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((33:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((33:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((33:ℕ) + 1) ^ 33 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((33:ℕ) + 2) ^ (33 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((33:ℕ) + 1) ^ 33 ≤ 0.00000480862 := by norm_num [bjsC306]
  have hcc : bjsC306 ((33:ℕ) + 2) ^ (33 + 1) ≤ 0.0000054117 := by norm_num [bjsC306]
  rw [show (35:ℕ) = (33:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((33:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 36: τ_36 ≤ 2.124223148108. -/
private lemma tauA_36_1122c :
    bjsTau306 bjsC306 (1 / 100000) 36 ≤ 2.124223148108 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((34:ℕ) + 1) ≤ 2.211055892739 := tauA_35_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((34:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((34:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((34:ℕ) + 1) ^ 34 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((34:ℕ) + 2) ^ (34 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((34:ℕ) + 1) ^ 34 ≤ 0.0000054117 := by norm_num [bjsC306]
  have hcc : bjsC306 ((34:ℕ) + 2) ^ (34 + 1) ≤ 0.00000378819 := by norm_num [bjsC306]
  rw [show (36:ℕ) = (34:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((34:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 37: τ_37 ≤ 1.957398757055. -/
private lemma tauA_37_1122c :
    bjsTau306 bjsC306 (1 / 100000) 37 ≤ 1.957398757055 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((35:ℕ) + 1) ≤ 2.124223148108 := tauA_36_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((35:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((35:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((35:ℕ) + 1) ^ 35 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((35:ℕ) + 2) ^ (35 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((35:ℕ) + 1) ^ 35 ≤ 0.00000378819 := by norm_num [bjsC306]
  have hcc : bjsC306 ((35:ℕ) + 2) ^ (35 + 1) ≤ 0.00000265174 := by norm_num [bjsC306]
  rw [show (37:ℕ) = (35:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((35:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 38: τ_38 ≤ 1.880520380541. -/
private lemma tauA_38_1122c :
    bjsTau306 bjsC306 (1 / 100000) 38 ≤ 1.880520380541 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((36:ℕ) + 1) ≤ 1.957398757055 := tauA_37_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((36:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((36:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((36:ℕ) + 1) ^ 36 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((36:ℕ) + 2) ^ (36 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((36:ℕ) + 1) ^ 36 ≤ 0.00000265174 := by norm_num [bjsC306]
  have hcc : bjsC306 ((36:ℕ) + 2) ^ (36 + 1) ≤ 0.00000185622 := by norm_num [bjsC306]
  rw [show (38:ℕ) = (36:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((36:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 39: τ_39 ≤ 1.73282184026. -/
private lemma tauA_39_1122c :
    bjsTau306 bjsC306 (1 / 100000) 39 ≤ 1.73282184026 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((37:ℕ) + 1) ≤ 1.880520380541 := tauA_38_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((37:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((37:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((37:ℕ) + 1) ^ 37 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((37:ℕ) + 2) ^ (37 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((37:ℕ) + 1) ^ 37 ≤ 0.00000185622 := by norm_num [bjsC306]
  have hcc : bjsC306 ((37:ℕ) + 2) ^ (37 + 1) ≤ 0.00000129935 := by norm_num [bjsC306]
  rw [show (39:ℕ) = (37:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((37:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 40: τ_40 ≤ 1.664760335164. -/
private lemma tauA_40_1122c :
    bjsTau306 bjsC306 (1 / 100000) 40 ≤ 1.664760335164 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((38:ℕ) + 1) ≤ 1.73282184026 := tauA_39_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((38:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((38:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((38:ℕ) + 1) ^ 38 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((38:ℕ) + 2) ^ (38 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((38:ℕ) + 1) ^ 38 ≤ 0.00000129935 := by norm_num [bjsC306]
  have hcc : bjsC306 ((38:ℕ) + 2) ^ (38 + 1) ≤ 0.000000909544 := by norm_num [bjsC306]
  rw [show (40:ℕ) = (38:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((38:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 41: τ_41 ≤ 1.534001415559. -/
private lemma tauA_41_1122c :
    bjsTau306 bjsC306 (1 / 100000) 41 ≤ 1.534001415559 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((39:ℕ) + 1) ≤ 1.664760335164 := tauA_40_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((39:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((39:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((39:ℕ) + 1) ^ 39 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((39:ℕ) + 2) ^ (39 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((39:ℕ) + 1) ^ 39 ≤ 0.000000909544 := by norm_num [bjsC306]
  have hcc : bjsC306 ((39:ℕ) + 2) ^ (39 + 1) ≤ 0.000000636681 := by norm_num [bjsC306]
  rw [show (41:ℕ) = (39:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((39:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 42: τ_42 ≤ 1.47374740181. -/
private lemma tauA_42_1122c :
    bjsTau306 bjsC306 (1 / 100000) 42 ≤ 1.47374740181 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((40:ℕ) + 1) ≤ 1.534001415559 := tauA_41_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((40:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((40:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((40:ℕ) + 1) ^ 40 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((40:ℕ) + 2) ^ (40 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((40:ℕ) + 1) ^ 40 ≤ 0.000000636681 := by norm_num [bjsC306]
  have hcc : bjsC306 ((40:ℕ) + 2) ^ (40 + 1) ≤ 0.000000445677 := by norm_num [bjsC306]
  rw [show (42:ℕ) = (40:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((40:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 43: τ_43 ≤ 1.357988465979. -/
private lemma tauA_43_1122c :
    bjsTau306 bjsC306 (1 / 100000) 43 ≤ 1.357988465979 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((41:ℕ) + 1) ≤ 1.47374740181 := tauA_42_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((41:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((41:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((41:ℕ) + 1) ^ 41 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((41:ℕ) + 2) ^ (41 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((41:ℕ) + 1) ^ 41 ≤ 0.000000445677 := by norm_num [bjsC306]
  have hcc : bjsC306 ((41:ℕ) + 2) ^ (41 + 1) ≤ 0.000000311974 := by norm_num [bjsC306]
  rw [show (43:ℕ) = (41:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((41:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 44: τ_44 ≤ 1.304647206058. -/
private lemma tauA_44_1122c :
    bjsTau306 bjsC306 (1 / 100000) 44 ≤ 1.304647206058 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((42:ℕ) + 1) ≤ 1.357988465979 := tauA_43_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((42:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((42:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((42:ℕ) + 1) ^ 42 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((42:ℕ) + 2) ^ (42 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((42:ℕ) + 1) ^ 42 ≤ 0.000000311974 := by norm_num [bjsC306]
  have hcc : bjsC306 ((42:ℕ) + 2) ^ (42 + 1) ≤ 0.000000218382 := by norm_num [bjsC306]
  rw [show (44:ℕ) = (42:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((42:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 45: τ_45 ≤ 1.202169090325. -/
private lemma tauA_45_1122c :
    bjsTau306 bjsC306 (1 / 100000) 45 ≤ 1.202169090325 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((43:ℕ) + 1) ≤ 1.304647206058 := tauA_44_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((43:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((43:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((43:ℕ) + 1) ^ 43 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((43:ℕ) + 2) ^ (43 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((43:ℕ) + 1) ^ 43 ≤ 0.000000218382 := by norm_num [bjsC306]
  have hcc : bjsC306 ((43:ℕ) + 2) ^ (43 + 1) ≤ 0.000000152868 := by norm_num [bjsC306]
  rw [show (45:ℕ) = (43:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((43:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 46: τ_46 ≤ 1.154947935755. -/
private lemma tauA_46_1122c :
    bjsTau306 bjsC306 (1 / 100000) 46 ≤ 1.154947935755 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((44:ℕ) + 1) ≤ 1.202169090325 := tauA_45_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((44:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((44:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((44:ℕ) + 1) ^ 44 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((44:ℕ) + 2) ^ (44 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((44:ℕ) + 1) ^ 44 ≤ 0.000000152868 := by norm_num [bjsC306]
  have hcc : bjsC306 ((44:ℕ) + 2) ^ (44 + 1) ≤ 0.000000107007 := by norm_num [bjsC306]
  rw [show (46:ℕ) = (44:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((44:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 47: τ_47 ≤ 1.064227993283. -/
private lemma tauA_47_1122c :
    bjsTau306 bjsC306 (1 / 100000) 47 ≤ 1.064227993283 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((45:ℕ) + 1) ≤ 1.154947935755 := tauA_46_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((45:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((45:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((45:ℕ) + 1) ^ 45 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((45:ℕ) + 2) ^ (45 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((45:ℕ) + 1) ^ 45 ≤ 0.000000107007 := by norm_num [bjsC306]
  have hcc : bjsC306 ((45:ℕ) + 2) ^ (45 + 1) ≤ 0.000000143842 := by norm_num [bjsC306]
  rw [show (47:ℕ) = (45:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((45:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 48: τ_48 ≤ 1.022425191406. -/
private lemma tauA_48_1122c :
    bjsTau306 bjsC306 (1 / 100000) 48 ≤ 1.022425191406 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((46:ℕ) + 1) ≤ 1.064227993283 := tauA_47_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((46:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((46:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((46:ℕ) + 1) ^ 46 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((46:ℕ) + 2) ^ (46 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((46:ℕ) + 1) ^ 46 ≤ 0.000000143842 := by norm_num [bjsC306]
  have hcc : bjsC306 ((46:ℕ) + 2) ^ (46 + 1) ≤ 0.000000102128 := by norm_num [bjsC306]
  rw [show (48:ℕ) = (46:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((46:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 49: τ_49 ≤ 0.942114595848. -/
private lemma tauA_49_1122c :
    bjsTau306 bjsC306 (1 / 100000) 49 ≤ 0.942114595848 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((47:ℕ) + 1) ≤ 1.022425191406 := tauA_48_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((47:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((47:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((47:ℕ) + 1) ^ 47 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((47:ℕ) + 2) ^ (47 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((47:ℕ) + 1) ^ 47 ≤ 0.000000102128 := by norm_num [bjsC306]
  have hcc : bjsC306 ((47:ℕ) + 2) ^ (47 + 1) ≤ 0.0000000725105 := by norm_num [bjsC306]
  rw [show (49:ℕ) = (47:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((47:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 50: τ_50 ≤ 0.905108212259. -/
private lemma tauA_50_1122c :
    bjsTau306 bjsC306 (1 / 100000) 50 ≤ 0.905108212259 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((48:ℕ) + 1) ≤ 0.942114595848 := tauA_49_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((48:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((48:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((48:ℕ) + 1) ^ 48 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((48:ℕ) + 2) ^ (48 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((48:ℕ) + 1) ^ 48 ≤ 0.0000000725105 := by norm_num [bjsC306]
  have hcc : bjsC306 ((48:ℕ) + 2) ^ (48 + 1) ≤ 0.0000000514825 := by norm_num [bjsC306]
  rw [show (50:ℕ) = (48:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((48:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 51: τ_51 ≤ 0.834012417658. -/
private lemma tauA_51_1122c :
    bjsTau306 bjsC306 (1 / 100000) 51 ≤ 0.834012417658 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((49:ℕ) + 1) ≤ 0.905108212259 := tauA_50_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((49:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((49:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((49:ℕ) + 1) ^ 49 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((49:ℕ) + 2) ^ (49 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((49:ℕ) + 1) ^ 49 ≤ 0.0000000514825 := by norm_num [bjsC306]
  have hcc : bjsC306 ((49:ℕ) + 2) ^ (49 + 1) ≤ 0.0000000365526 := by norm_num [bjsC306]
  rw [show (51:ℕ) = (49:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((49:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 52: τ_52 ≤ 0.801252207136. -/
private lemma tauA_52_1122c :
    bjsTau306 bjsC306 (1 / 100000) 52 ≤ 0.801252207136 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((50:ℕ) + 1) ≤ 0.834012417658 := tauA_51_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((50:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((50:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((50:ℕ) + 1) ^ 50 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((50:ℕ) + 2) ^ (50 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((50:ℕ) + 1) ^ 50 ≤ 0.0000000365526 := by norm_num [bjsC306]
  have hcc : bjsC306 ((50:ℕ) + 2) ^ (50 + 1) ≤ 0.0000000259523 := by norm_num [bjsC306]
  rw [show (52:ℕ) = (50:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((50:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 53: τ_53 ≤ 0.738314076007. -/
private lemma tauA_53_1122c :
    bjsTau306 bjsC306 (1 / 100000) 53 ≤ 0.738314076007 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((51:ℕ) + 1) ≤ 0.801252207136 := tauA_52_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((51:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((51:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((51:ℕ) + 1) ^ 51 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((51:ℕ) + 2) ^ (51 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((51:ℕ) + 1) ^ 51 ≤ 0.0000000259523 := by norm_num [bjsC306]
  have hcc : bjsC306 ((51:ℕ) + 2) ^ (51 + 1) ≤ 0.0000000184262 := by norm_num [bjsC306]
  rw [show (53:ℕ) = (51:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((51:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 54: τ_54 ≤ 0.709312871962. -/
private lemma tauA_54_1122c :
    bjsTau306 bjsC306 (1 / 100000) 54 ≤ 0.709312871962 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((52:ℕ) + 1) ≤ 0.738314076007 := tauA_53_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((52:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((52:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((52:ℕ) + 1) ^ 52 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((52:ℕ) + 2) ^ (52 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((52:ℕ) + 1) ^ 52 ≤ 0.0000000184262 := by norm_num [bjsC306]
  have hcc : bjsC306 ((52:ℕ) + 2) ^ (52 + 1) ≤ 0.0000000130826 := by norm_num [bjsC306]
  rw [show (54:ℕ) = (52:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((52:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 55: τ_55 ≤ 0.653596461805. -/
private lemma tauA_55_1122c :
    bjsTau306 bjsC306 (1 / 100000) 55 ≤ 0.653596461805 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((53:ℕ) + 1) ≤ 0.709312871962 := tauA_54_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((53:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((53:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((53:ℕ) + 1) ^ 53 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((53:ℕ) + 2) ^ (53 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((53:ℕ) + 1) ^ 53 ≤ 0.0000000130826 := by norm_num [bjsC306]
  have hcc : bjsC306 ((53:ℕ) + 2) ^ (53 + 1) ≤ 0.00000000928862 := by norm_num [bjsC306]
  rw [show (55:ℕ) = (53:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((53:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 56: τ_56 ≤ 0.627922967689. -/
private lemma tauA_56_1122c :
    bjsTau306 bjsC306 (1 / 100000) 56 ≤ 0.627922967689 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((54:ℕ) + 1) ≤ 0.653596461805 := tauA_55_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((54:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((54:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((54:ℕ) + 1) ^ 54 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((54:ℕ) + 2) ^ (54 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((54:ℕ) + 1) ^ 54 ≤ 0.00000000928862 := by norm_num [bjsC306]
  have hcc : bjsC306 ((54:ℕ) + 2) ^ (54 + 1) ≤ 0.00000000659492 := by norm_num [bjsC306]
  rw [show (56:ℕ) = (54:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((54:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 57: τ_57 ≤ 0.578599677128. -/
private lemma tauA_57_1122c :
    bjsTau306 bjsC306 (1 / 100000) 57 ≤ 0.578599677128 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((55:ℕ) + 1) ≤ 0.627922967689 := tauA_56_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((55:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((55:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((55:ℕ) + 1) ^ 55 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((55:ℕ) + 2) ^ (55 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((55:ℕ) + 1) ^ 55 ≤ 0.00000000659492 := by norm_num [bjsC306]
  have hcc : bjsC306 ((55:ℕ) + 2) ^ (55 + 1) ≤ 0.00000000468239 := by norm_num [bjsC306]
  rw [show (57:ℕ) = (55:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((55:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 58: τ_58 ≤ 0.555872070435. -/
private lemma tauA_58_1122c :
    bjsTau306 bjsC306 (1 / 100000) 58 ≤ 0.555872070435 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((56:ℕ) + 1) ≤ 0.578599677128 := tauA_57_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((56:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((56:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((56:ℕ) + 1) ^ 56 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((56:ℕ) + 2) ^ (56 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((56:ℕ) + 1) ^ 56 ≤ 0.00000000468239 := by norm_num [bjsC306]
  have hcc : bjsC306 ((56:ℕ) + 2) ^ (56 + 1) ≤ 0.0000000033245 := by norm_num [bjsC306]
  rw [show (58:ℕ) = (56:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((56:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 59: τ_59 ≤ 0.512208348914. -/
private lemma tauA_59_1122c :
    bjsTau306 bjsC306 (1 / 100000) 59 ≤ 0.512208348914 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((57:ℕ) + 1) ≤ 0.555872070435 := tauA_58_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((57:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((57:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((57:ℕ) + 1) ^ 57 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((57:ℕ) + 2) ^ (57 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((57:ℕ) + 1) ^ 57 ≤ 0.0000000033245 := by norm_num [bjsC306]
  have hcc : bjsC306 ((57:ℕ) + 2) ^ (57 + 1) ≤ 0.0000000023604 := by norm_num [bjsC306]
  rw [show (59:ℕ) = (57:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((57:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 60: τ_60 ≤ 0.492088611744. -/
private lemma tauA_60_1122c :
    bjsTau306 bjsC306 (1 / 100000) 60 ≤ 0.492088611744 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((58:ℕ) + 1) ≤ 0.512208348914 := tauA_59_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((58:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((58:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((58:ℕ) + 1) ^ 58 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((58:ℕ) + 2) ^ (58 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((58:ℕ) + 1) ^ 58 ≤ 0.0000000023604 := by norm_num [bjsC306]
  have hcc : bjsC306 ((58:ℕ) + 2) ^ (58 + 1) ≤ 0.00000000167588 := by norm_num [bjsC306]
  rw [show (60:ℕ) = (58:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((58:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 61: τ_61 ≤ 0.453435066304. -/
private lemma tauA_61_1122c :
    bjsTau306 bjsC306 (1 / 100000) 61 ≤ 0.453435066304 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((59:ℕ) + 1) ≤ 0.492088611744 := tauA_60_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((59:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((59:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((59:ℕ) + 1) ^ 59 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((59:ℕ) + 2) ^ (59 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((59:ℕ) + 1) ^ 59 ≤ 0.00000000167588 := by norm_num [bjsC306]
  have hcc : bjsC306 ((59:ℕ) + 2) ^ (59 + 1) ≤ 0.00000000118988 := by norm_num [bjsC306]
  rw [show (61:ℕ) = (59:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((59:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 62: τ_62 ≤ 0.435623962769. -/
private lemma tauA_62_1122c :
    bjsTau306 bjsC306 (1 / 100000) 62 ≤ 0.435623962769 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((60:ℕ) + 1) ≤ 0.453435066304 := tauA_61_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((60:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((60:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((60:ℕ) + 1) ^ 60 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((60:ℕ) + 2) ^ (60 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((60:ℕ) + 1) ^ 60 ≤ 0.00000000118988 := by norm_num [bjsC306]
  have hcc : bjsC306 ((60:ℕ) + 2) ^ (60 + 1) ≤ 0.000000000844811 := by norm_num [bjsC306]
  rw [show (62:ℕ) = (60:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((60:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 63: τ_63 ≤ 0.401405708136. -/
private lemma tauA_63_1122c :
    bjsTau306 bjsC306 (1 / 100000) 63 ≤ 0.401405708136 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((61:ℕ) + 1) ≤ 0.435623962769 := tauA_62_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((61:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((61:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((61:ℕ) + 1) ^ 61 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((61:ℕ) + 2) ^ (61 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((61:ℕ) + 1) ^ 61 ≤ 0.000000000844811 := by norm_num [bjsC306]
  have hcc : bjsC306 ((61:ℕ) + 2) ^ (61 + 1) ≤ 0.000000000599816 := by norm_num [bjsC306]
  rw [show (63:ℕ) = (61:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((61:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 64: τ_64 ≤ 0.38563833622. -/
private lemma tauA_64_1122c :
    bjsTau306 bjsC306 (1 / 100000) 64 ≤ 0.38563833622 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((62:ℕ) + 1) ≤ 0.401405708136 := tauA_63_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((62:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((62:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((62:ℕ) + 1) ^ 62 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((62:ℕ) + 2) ^ (62 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((62:ℕ) + 1) ^ 62 ≤ 0.000000000599816 := by norm_num [bjsC306]
  have hcc : bjsC306 ((62:ℕ) + 2) ^ (62 + 1) ≤ 0.000000000425869 := by norm_num [bjsC306]
  rw [show (64:ℕ) = (62:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((62:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 65: τ_65 ≤ 0.355346448829. -/
private lemma tauA_65_1122c :
    bjsTau306 bjsC306 (1 / 100000) 65 ≤ 0.355346448829 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((63:ℕ) + 1) ≤ 0.38563833622 := tauA_64_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((63:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((63:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((63:ℕ) + 1) ^ 63 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((63:ℕ) + 2) ^ (63 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((63:ℕ) + 1) ^ 63 ≤ 0.000000000425869 := by norm_num [bjsC306]
  have hcc : bjsC306 ((63:ℕ) + 2) ^ (63 + 1) ≤ 0.000000000302367 := by norm_num [bjsC306]
  rw [show (65:ℕ) = (63:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((63:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 66: τ_66 ≤ 0.341388301702. -/
private lemma tauA_66_1122c :
    bjsTau306 bjsC306 (1 / 100000) 66 ≤ 0.341388301702 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((64:ℕ) + 1) ≤ 0.355346448829 := tauA_65_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((64:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((64:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((64:ℕ) + 1) ^ 64 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((64:ℕ) + 2) ^ (64 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((64:ℕ) + 1) ^ 64 ≤ 0.000000000302367 := by norm_num [bjsC306]
  have hcc : bjsC306 ((64:ℕ) + 2) ^ (64 + 1) ≤ 0.000000000214681 := by norm_num [bjsC306]
  rw [show (66:ℕ) = (64:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((64:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 67: τ_67 ≤ 0.314572252638. -/
private lemma tauA_67_1122c :
    bjsTau306 bjsC306 (1 / 100000) 67 ≤ 0.314572252638 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((65:ℕ) + 1) ≤ 0.341388301702 := tauA_66_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((65:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((65:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((65:ℕ) + 1) ^ 65 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((65:ℕ) + 2) ^ (65 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((65:ℕ) + 1) ^ 65 ≤ 0.000000000214681 := by norm_num [bjsC306]
  have hcc : bjsC306 ((65:ℕ) + 2) ^ (65 + 1) ≤ 0.000000000152424 := by norm_num [bjsC306]
  rw [show (67:ℕ) = (65:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((65:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 68: τ_68 ≤ 0.302215731449. -/
private lemma tauA_68_1122c :
    bjsTau306 bjsC306 (1 / 100000) 68 ≤ 0.302215731449 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((66:ℕ) + 1) ≤ 0.314572252638 := tauA_67_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((66:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((66:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((66:ℕ) + 1) ^ 66 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((66:ℕ) + 2) ^ (66 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((66:ℕ) + 1) ^ 66 ≤ 0.000000000152424 := by norm_num [bjsC306]
  have hcc : bjsC306 ((66:ℕ) + 2) ^ (66 + 1) ≤ 0.000000000108221 := by norm_num [bjsC306]
  rw [show (68:ℕ) = (66:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((66:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 69: τ_69 ≤ 0.278476686822. -/
private lemma tauA_69_1122c :
    bjsTau306 bjsC306 (1 / 100000) 69 ≤ 0.278476686822 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((67:ℕ) + 1) ≤ 0.302215731449 := tauA_68_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((67:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((67:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((67:ℕ) + 1) ^ 67 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((67:ℕ) + 2) ^ (67 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((67:ℕ) + 1) ^ 67 ≤ 0.000000000108221 := by norm_num [bjsC306]
  have hcc : bjsC306 ((67:ℕ) + 2) ^ (67 + 1) ≤ 0.0000000000768366 := by norm_num [bjsC306]
  rw [show (69:ℕ) = (67:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((67:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 70: τ_70 ≤ 0.267538013386. -/
private lemma tauA_70_1122c :
    bjsTau306 bjsC306 (1 / 100000) 70 ≤ 0.267538013386 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((68:ℕ) + 1) ≤ 0.278476686822 := tauA_69_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((68:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((68:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((68:ℕ) + 1) ^ 68 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((68:ℕ) + 2) ^ (68 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((68:ℕ) + 1) ^ 68 ≤ 0.0000000000768366 := by norm_num [bjsC306]
  have hcc : bjsC306 ((68:ℕ) + 2) ^ (68 + 1) ≤ 0.000000000054554 := by norm_num [bjsC306]
  rw [show (70:ℕ) = (68:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_pos (by norm_num : Even ((68:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- Certificate step to n = 71: τ_71 ≤ 0.246522903024. -/
private lemma tauA_71_1122c :
    bjsTau306 bjsC306 (1 / 100000) 71 ≤ 0.246522903024 := by
  have hprev : bjsTau306 bjsC306 (1 / 100000) ((69:ℕ) + 1) ≤ 0.267538013386 := tauA_70_1122c
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) ((69:ℕ) + 1) :=
    tau_nonneg1122c _ (by norm_num) ((69:ℕ) + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 ((69:ℕ) + 1) ^ 69 := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 ((69:ℕ) + 2) ^ (69 + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp : bjsC306 ((69:ℕ) + 1) ^ 69 ≤ 0.000000000054554 := by norm_num [bjsC306]
  have hcc : bjsC306 ((69:ℕ) + 2) ^ (69 + 1) ≤ 0.0000000000387333 := by norm_num [bjsC306]
  rw [show (71:ℕ) = (69:ℕ) + 2 from rfl, bjsTau306]
  try dsimp only
  rw [if_neg (by norm_num : ¬ Even ((69:ℕ) + 2))]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := hprev) (hcp := hcp) (hcc := hcc) (key := by norm_num)

/-- From m = 2 to m = 500 every value of BJS Table 2 is at most 0.73. -/
private lemma bjsC306_le73_1122c (m : ℕ) (hm2 : 2 ≤ m) (hm500 : m ≤ 500) :
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

/-- Powers of 0.73 from 71 on are below 2e-10. -/
private lemma pow73_le1122c (n : ℕ) (h : 70 ≤ n) : (0.73 : ℝ) ^ n ≤ 3 / 10000000000 := by
  have h70 : (0.73 : ℝ) ^ 70 ≤ 3 / 10000000000 := by norm_num
  calc (0.73 : ℝ) ^ n ≤ (0.73 : ℝ) ^ 70 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    _ ≤ 3 / 10000000000 := h70

/-- Beyond 71 both c-powers of display 31 are below 2e-10. -/
private lemma cpow_le1122c (n : ℕ) (hn : 70 ≤ n) (hn2 : n + 2 ≤ 500) :
    bjsC306 (n + 1) ^ n ≤ 3 / 10000000000 := by
  have hc : bjsC306 (n + 1) ≤ 0.73 := bjsC306_le73_1122c (n + 1) (by omega) (by omega)
  exact le_trans (pow_le_pow_left₀ (bjsC306_nonneg1122c _) hc n) (pow73_le1122c n hn)

/-- The same for the second c-power. -/
private lemma cpow2_le1122c (n : ℕ) (hn : 70 ≤ n) (hn2 : n + 2 ≤ 500) :
    bjsC306 (n + 2) ^ (n + 1) ≤ 3 / 10000000000 := by
  have hc : bjsC306 (n + 2) ≤ 0.73 := bjsC306_le73_1122c (n + 2) (by omega) (by omega)
  exact le_trans (pow_le_pow_left₀ (bjsC306_nonneg1122c _) hc (n + 1))
    (pow73_le1122c (n + 1) (by omega))

/-- One step of display 31 beyond n = 71, at ε = 1/100000: the ratio is at most 0.960719607. -/
private lemma tail_step_even1122c (n : ℕ) (hn : 70 ≤ n) (hn2 : n + 2 ≤ 500) (hpar : Even (n + 2)) :
    bjsTau306 bjsC306 (1 / 100000) (n + 2) ≤ 0.960719607 * bjsTau306 bjsC306 (1 / 100000) (n + 1) + 0.00000001 := by
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) (n + 1) := tau_nonneg1122c _ (by norm_num) (n + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 (n + 1) ^ n := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 (n + 2) ^ (n + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp := cpow_le1122c n hn hn2
  have hcc := cpow2_le1122c n hn hn2
  simp only [bjsTau306]
  try dsimp only
  rw [if_pos hpar]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1) (hγ0 := by norm_num) (hγ := by norm_num) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
      · exact xi_le_of1122c (γu := 1.2214028) (hγ0 := (Real.exp_pos 0.2).le) (hγ := exp_02_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
    · refine mul_max2_leR1122c ht0 ?_ ?_
      · exact xi_le_of1122c (γu := 1.4918247999) (hγ0 := (Real.exp_pos 0.4).le) (hγ := exp_04_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
      · exact xi_le_of1122c (γu := 1.8221189878) (hγ0 := (Real.exp_pos 0.6).le) (hγ := exp_06_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
  · refine mul_max2_leR1122c ht0 ?_ ?_
    · exact xi_le_of1122c (γu := 2.2255412336) (hγ0 := (Real.exp_pos 0.8).le) (hγ := exp_08_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
    · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)

/-- One step of display 31 beyond n = 71, at ε = 1/100000: the ratio is at most 0.9214501. -/
private lemma tail_step_odd1122c (n : ℕ) (hn : 70 ≤ n) (hn2 : n + 2 ≤ 500) (hpar : ¬ Even (n + 2)) :
    bjsTau306 bjsC306 (1 / 100000) (n + 2) ≤ 0.9214501 * bjsTau306 bjsC306 (1 / 100000) (n + 1) + 0.00000001 := by
  have ht0 : (0:ℝ) ≤ bjsTau306 bjsC306 (1 / 100000) (n + 1) := tau_nonneg1122c _ (by norm_num) (n + 1)
  have hcp0 : (0:ℝ) ≤ bjsC306 (n + 1) ^ n := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcc0 : (0:ℝ) ≤ bjsC306 (n + 2) ^ (n + 1) := pow_nonneg (bjsC306_nonneg1122c _) _
  have hcp := cpow_le1122c n hn hn2
  have hcc := cpow2_le1122c n hn hn2
  simp only [bjsTau306]
  try dsimp only
  rw [if_neg hpar]
  refine mul_max2_leR1122c ht0 ?_ ?_
  · exact xi_le_of1122c (γu := 3.6243757720) (hγ0 := by positivity) (hγ := four_exp_one_le1122c) (hκ := by norm_num) (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)
  · exact odd2_le_of1122c (hε0 := by norm_num) (hcp0 := hcp0) (hcc0 := hcc0) (ht0 := ht0) (ht := le_rfl) (hcp := hcp) (hcc := hcc) (key := by linarith)

/-- The additive constant of one pair of display 31 steps is below C. -/
private lemma pairC1122c :
    (0.9214501 : ℝ) * 0.00000001 + 0.00000001 + 0.8852551779421107 * 0.0000002 ≤ 0.0000002 := by
  norm_num

/-- The paired step beyond 71: two steps of display 31 multiply τ by at most P and add at most 3.4e-8. -/
private lemma tail_pair1122c (k : ℕ) (hk : k ≤ 214) :
    bjsTau306 bjsC306 (1 / 100000) (71 + 2 * k) ≤
      0.8852551779421107 ^ k * 0.246522903024 + 0.0000002 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      refine le_trans tauA_71_1122c ?_
      norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hp : bjsTau306 bjsC306 (1 / 100000) (71 + 2 * m) ≤
          0.8852551779421107 ^ m * 0.246522903024 + 0.0000002 :=
        ih m (by omega) (by omega)
      have stepe := tail_step_even1122c (70 + 2 * m) (by omega) (by omega)
        (show Even ((70 + 2 * m) + 2) from ⟨36 + m, by ring⟩)
      have e1 : (70 + 2 * m) + 2 = 71 + 2 * m + 1 := by omega
      have e2 : (70 + 2 * m) + 1 = 71 + 2 * m := by omega
      rw [e1, e2] at stepe
      have stepo := tail_step_odd1122c (71 + 2 * m) (by omega) (by omega)
        (show ¬ Even ((71 + 2 * m) + 2) from by rintro ⟨r, hr⟩; omega)
      have estep : 71 + 2 * (m + 1) = (71 + 2 * m) + 2 := by omega
      rw [estep]
      have hmul : 0.8852551779421107 * bjsTau306 bjsC306 (1 / 100000) (71 + 2 * m) ≤
          0.8852551779421107 * (0.8852551779421107 ^ m * 0.246522903024 + 0.0000002) :=
        mul_le_mul_of_nonneg_left hp (by norm_num)
      have hC := pairC1122c
      calc bjsTau306 bjsC306 (1 / 100000) ((71 + 2 * m) + 2)
          ≤ 0.9214501 * bjsTau306 bjsC306 (1 / 100000) ((71 + 2 * m) + 1) + 0.00000001 := stepo
        _ ≤ 0.9214501 * (0.960719607 * bjsTau306 bjsC306 (1 / 100000) (71 + 2 * m)
              + 0.00000001) + 0.00000001 := by linarith [stepe]
        _ = 0.8852551779421107 * bjsTau306 bjsC306 (1 / 100000) (71 + 2 * m)
              + (0.9214501 * 0.00000001 + 0.00000001) := by ring
        _ ≤ 0.8852551779421107 * (0.8852551779421107 ^ m * 0.246522903024 + 0.0000002)
              + (0.9214501 * 0.00000001 + 0.00000001) := by linarith [hmul]
        _ ≤ 0.8852551779421107 ^ (m + 1) * 0.246522903024 + 0.0000002 := by
            rw [pow_succ]
            nlinarith [hC, mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 0.8852551779421107) m)
              (by norm_num : (0:ℝ) ≤ 0.246522903024)]

/-- Splitting a filtered sum over Icc 1 500 at 71. -/
private lemma sum_split71_1122c (p : ℕ → Prop) [DecidablePred p] (u : ℕ → ℝ) :
    ∑ n ∈ (Finset.Icc 1 500).filter p, u n =
      ∑ n ∈ (Finset.Icc 1 71).filter p, u n + ∑ n ∈ (Finset.Ioc 71 500).filter p, u n := by
  have h1 : ∀ M : ℕ, Finset.Icc 1 M = Finset.Ioc 0 M := fun M => by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1, h1, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_Ioc_consecutive _ (Nat.zero_le 71) (by norm_num : 71 ≤ 500)]

/-- The odd indices up to 71 are 1, 3, ..., 71. -/
private lemma icc_odd1122c : (Finset.Icc 1 71).filter Odd = (Finset.range 36).image (fun k => 1 + 2 * k) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨j, hj⟩⟩
    exact ⟨j, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨k, by omega⟩⟩

/-- The odd indices from 71 to 500 are 73, 75, ..., 499. -/
private lemma ioc_odd1122c :
    (Finset.Ioc 71 500).filter Odd = (Finset.range 214).image (fun k => 73 + 2 * k) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨j, hj⟩⟩
    exact ⟨j - 36, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨k + 36, by omega⟩⟩

/-- The even indices up to 71 are 2, 4, ..., 70. -/
private lemma icc_even1122c :
    (Finset.Icc 1 71).filter Even = (Finset.range 35).image (fun k => 2 + 2 * k) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨j, hj⟩⟩
    exact ⟨j - 1, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨k + 1, by omega⟩⟩

/-- The even indices from 71 to 500 are 72, 74, ..., 500. -/
private lemma ioc_even1122c :
    (Finset.Ioc 71 500).filter Even = (Finset.range 215).image (fun k => 72 + 2 * k) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨j, hj⟩⟩
    exact ⟨j - 36, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨k + 36, by omega⟩⟩

/-- The certificate values up to 71: the sum over the odd indices. -/
private lemma prefix_odd1122c :
    ∑ k ∈ Finset.range 36, bjsTau306 bjsC306 (1 / 100000) (1 + 2 * k) ≤ 129.605489 := by
  have h0 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 0) ≤ 3 := by norm_num [bjsTau306]
  have h1 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 1) ≤ 12.184021041375 := tauA_3_1122c
  have h2 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 2) ≤ 12.057520918719 := tauA_5_1122c
  have h3 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 3) ≤ 11.295966470933 := tauA_7_1122c
  have h4 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 4) ≤ 10.312872103185 := tauA_9_1122c
  have h5 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 5) ≤ 9.295966889149 := tauA_11_1122c
  have h6 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 6) ≤ 8.315008916756 := tauA_13_1122c
  have h7 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 7) ≤ 7.410507407889 := tauA_15_1122c
  have h8 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 8) ≤ 6.586263020977 := tauA_17_1122c
  have h9 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 9) ≤ 5.842582630418 := tauA_19_1122c
  have h10 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 10) ≤ 5.179217118213 := tauA_21_1122c
  have h11 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 11) ≤ 4.588961579581 := tauA_23_1122c
  have h12 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 12) ≤ 4.064266564529 := tauA_25_1122c
  have h13 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 13) ≤ 3.598856591715 := tauA_27_1122c
  have h14 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 14) ≤ 3.186497544333 := tauA_29_1122c
  have h15 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 15) ≤ 2.821144738289 := tauA_31_1122c
  have h16 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 16) ≤ 2.497566784024 := tauA_33_1122c
  have h17 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 17) ≤ 2.211055892739 := tauA_35_1122c
  have h18 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 18) ≤ 1.957398757055 := tauA_37_1122c
  have h19 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 19) ≤ 1.73282184026 := tauA_39_1122c
  have h20 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 20) ≤ 1.534001415559 := tauA_41_1122c
  have h21 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 21) ≤ 1.357988465979 := tauA_43_1122c
  have h22 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 22) ≤ 1.202169090325 := tauA_45_1122c
  have h23 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 23) ≤ 1.064227993283 := tauA_47_1122c
  have h24 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 24) ≤ 0.942114595848 := tauA_49_1122c
  have h25 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 25) ≤ 0.834012417658 := tauA_51_1122c
  have h26 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 26) ≤ 0.738314076007 := tauA_53_1122c
  have h27 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 27) ≤ 0.653596461805 := tauA_55_1122c
  have h28 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 28) ≤ 0.578599677128 := tauA_57_1122c
  have h29 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 29) ≤ 0.512208348914 := tauA_59_1122c
  have h30 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 30) ≤ 0.453435066304 := tauA_61_1122c
  have h31 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 31) ≤ 0.401405708136 := tauA_63_1122c
  have h32 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 32) ≤ 0.355346448829 := tauA_65_1122c
  have h33 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 33) ≤ 0.314572252638 := tauA_67_1122c
  have h34 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 34) ≤ 0.278476686822 := tauA_69_1122c
  have h35 : bjsTau306 bjsC306 (1 / 100000) (1 + 2 * 35) ≤ 0.246522903024 := tauA_71_1122c
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  linarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]

/-- The certificate values up to 71: the sum over the even indices. -/
private lemma prefix_even1122c :
    ∑ k ∈ Finset.range 35, bjsTau306 bjsC306 (1 / 100000) (2 + 2 * k) ≤ 132.772201 := by
  have h0 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 0) ≤ 10.413585322274 := tauA_2_1122c
  have h1 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 1) ≤ 12.198334899666 := tauA_4_1122c
  have h2 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 2) ≤ 11.811034158426 := tauA_6_1122c
  have h3 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 3) ≤ 10.96500926864 := tauA_8_1122c
  have h4 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 4) ≤ 9.969508434014 := tauA_10_1122c
  have h5 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 5) ≤ 8.962926416429 := tauA_12_1122c
  have h6 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 6) ≤ 8.005231258708 := tauA_14_1122c
  have h7 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 7) ≤ 7.129299684578 := tauA_16_1122c
  have h8 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 8) ≤ 6.331855727112 := tauA_18_1122c
  have h9 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 9) ≤ 5.615555942561 := tauA_20_1122c
  have h10 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 10) ≤ 4.977276908378 := tauA_22_1122c
  have h11 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 11) ≤ 4.409399649274 := tauA_24_1122c
  have h12 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 12) ≤ 3.904941612418 := tauA_26_1122c
  have h13 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 13) ≤ 3.457710360042 := tauA_28_1122c
  have h14 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 14) ≤ 3.061434586899 := tauA_30_1122c
  have h15 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 15) ≤ 2.71037853986 := tauA_32_1122c
  have h16 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 16) ≤ 2.399484934464 := tauA_34_1122c
  have h17 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 17) ≤ 2.124223148108 := tauA_36_1122c
  have h18 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 18) ≤ 1.880520380541 := tauA_38_1122c
  have h19 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 19) ≤ 1.664760335164 := tauA_40_1122c
  have h20 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 20) ≤ 1.47374740181 := tauA_42_1122c
  have h21 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 21) ≤ 1.304647206058 := tauA_44_1122c
  have h22 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 22) ≤ 1.154947935755 := tauA_46_1122c
  have h23 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 23) ≤ 1.022425191406 := tauA_48_1122c
  have h24 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 24) ≤ 0.905108212259 := tauA_50_1122c
  have h25 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 25) ≤ 0.801252207136 := tauA_52_1122c
  have h26 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 26) ≤ 0.709312871962 := tauA_54_1122c
  have h27 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 27) ≤ 0.627922967689 := tauA_56_1122c
  have h28 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 28) ≤ 0.555872070435 := tauA_58_1122c
  have h29 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 29) ≤ 0.492088611744 := tauA_60_1122c
  have h30 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 30) ≤ 0.435623962769 := tauA_62_1122c
  have h31 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 31) ≤ 0.38563833622 := tauA_64_1122c
  have h32 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 32) ≤ 0.341388301702 := tauA_66_1122c
  have h33 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 33) ≤ 0.302215731449 := tauA_68_1122c
  have h34 : bjsTau306 bjsC306 (1 / 100000) (2 + 2 * 34) ≤ 0.267538013386 := tauA_70_1122c
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  linarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]

/-- The tail beyond 71 over the odd indices. -/
private lemma tail_odd_sum1122c :
    ∑ k ∈ Finset.range 214, bjsTau306 bjsC306 (1 / 100000) (73 + 2 * k) ≤ 1.901965 := by
  have hb : ∀ k ∈ Finset.range 214, bjsTau306 bjsC306 (1 / 100000) (73 + 2 * k) ≤ (0.8852551779421107 : ℝ) ^ (k + 1) * 0.246522903024 + 0.0000002 := by
    intro k hk
    have hk' : k + 1 ≤ 214 := by
      simp only [Finset.mem_range] at hk
      omega
    have hp := tail_pair1122c (k + 1) hk'
    have e : 71 + 2 * (k + 1) = 73 + 2 * k := by omega
    rw [e] at hp
    exact hp
  refine le_trans (Finset.sum_le_sum hb) ?_
  have hshift : ∀ m : ℕ, ∑ k ∈ Finset.range m, (0.8852551779421107 : ℝ) ^ (k + 1)
      = 0.8852551779421107 * ∑ k ∈ Finset.range m, (0.8852551779421107 : ℝ) ^ k := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ]
      ring
  have hsum : ∑ k ∈ Finset.range 214,
      ((0.8852551779421107 : ℝ) ^ (k + 1) * 0.246522903024 + 0.0000002)
      = (∑ k ∈ Finset.range 214, (0.8852551779421107 : ℝ) ^ (k + 1)) * 0.246522903024
        + 214 * 0.0000002 := by
    rw [Finset.sum_add_distrib, Finset.sum_mul]
    simp
  have hg : ∑ k ∈ Finset.range 214, (0.8852551779421107 : ℝ) ^ k
      ≤ 1 / (1 - 0.8852551779421107) :=
    geom_range_le1122c _ (by norm_num) (by norm_num) 214
  rw [hsum, hshift 214]
  nlinarith [hg]

/-- The tail beyond 71 over the even indices. -/
private lemma tail_even_sum1122c :
    ∑ k ∈ Finset.range 215, bjsTau306 bjsC306 (1 / 100000) (72 + 2 * k) ≤ 2.064097 := by
  have hb : ∀ k ∈ Finset.range 215, bjsTau306 bjsC306 (1 / 100000) (72 + 2 * k) ≤ 0.960719607 * ((0.8852551779421107 : ℝ) ^ k * 0.246522903024 + 0.0000002) + 0.00000001 := by
    intro k hk
    have hk' : k ≤ 214 := by
      simp only [Finset.mem_range] at hk
      omega
    have hpair := tail_pair1122c k hk'
    have estepe := tail_step_even1122c (70 + 2 * k) (by omega) (by omega)
      (show Even ((70 + 2 * k) + 2) from ⟨36 + k, by ring⟩)
    have e : (70 + 2 * k) + 2 = 72 + 2 * k := by omega
    have e2 : (70 + 2 * k) + 1 = 71 + 2 * k := by omega
    rw [e, e2] at estepe
    have hmul := mul_le_mul_of_nonneg_left hpair (by norm_num : (0:ℝ) ≤ 0.960719607)
    linarith [estepe, hmul]
  refine le_trans (Finset.sum_le_sum hb) ?_
  have hsplit : ∑ k ∈ Finset.range 215,
      (0.960719607 * ((0.8852551779421107 : ℝ) ^ k * 0.246522903024 + 0.0000002)
        + 0.00000001)
      = 0.960719607 * (∑ k ∈ Finset.range 215,
          ((0.8852551779421107 : ℝ) ^ k * 0.246522903024 + 0.0000002))
        + 215 * 0.00000001 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hinner : ∑ k ∈ Finset.range 215,
      ((0.8852551779421107 : ℝ) ^ k * 0.246522903024 + 0.0000002)
      = (∑ k ∈ Finset.range 215, (0.8852551779421107 : ℝ) ^ k) * 0.246522903024
        + 215 * 0.0000002 := by
    rw [Finset.sum_add_distrib, Finset.sum_mul]
    simp
  rw [hsplit, hinner]
  have hg : ∑ k ∈ Finset.range 215, (0.8852551779421107 : ℝ) ^ k
      ≤ 1 / (1 - 0.8852551779421107) :=
    geom_range_le1122c _ (by norm_num) (by norm_num) 215
  nlinarith [mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 0.246522903024)]

/-- LEAF: BJS Proposition 13, the finite part of the Table 1 computation at ε = 1/100000:
the partial sums of τ_n over odd n up to N ≤ 500 are at most 131.508; interval value of the
full sum to 500 is 131.5073810. Class HARD: certified evaluation of 500 recursive terms
with exp and max. -/
theorem tau_odd_le500_1122c (N : ℕ) (hN : N ≤ 500) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 131.508 := by
  have hε0 : (0:ℝ) ≤ 1 / 100000 := by norm_num
  have hsp := sum_split71_1122c (p := Odd) (u := fun n => bjsTau306 bjsC306 (1 / 100000) n)
  have hmono : ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n
      ≤ ∑ n ∈ (Finset.Icc 1 500).filter Odd, bjsTau306 bjsC306 (1 / 100000) n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      obtain ⟨hx3, hx4⟩ := Finset.mem_Icc.1 hx1
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hx3, by omega⟩, hx2⟩
    · intro i _ _; exact tau_nonneg1122c _ hε0 i
  refine hmono.trans ?_
  rw [hsp]
  have h1 : ∑ n ∈ (Finset.Icc 1 71).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 129.605489 := by
    rw [icc_odd1122c, Finset.sum_image (by intro x _ y _ h; simp only [] at h; omega)]
    exact prefix_odd1122c
  have h2 : ∑ n ∈ (Finset.Ioc 71 500).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 1.901965 := by
    rw [ioc_odd1122c, Finset.sum_image (by intro x _ y _ h; simp only [] at h; omega)]
    exact tail_odd_sum1122c
  linarith

/-- LEAF: as tau_odd_le500_1122c over even n, bound 134.837; interval value 134.8362246.
Class HARD. -/
theorem tau_even_le500_1122c (N : ℕ) (hN : N ≤ 500) :
    ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 134.837 := by
  have hε0 : (0:ℝ) ≤ 1 / 100000 := by norm_num
  have hsp := sum_split71_1122c (p := Even) (u := fun n => bjsTau306 bjsC306 (1 / 100000) n)
  have hmono : ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n
      ≤ ∑ n ∈ (Finset.Icc 1 500).filter Even, bjsTau306 bjsC306 (1 / 100000) n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      obtain ⟨hx3, hx4⟩ := Finset.mem_Icc.1 hx1
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hx3, by omega⟩, hx2⟩
    · intro i _ _; exact tau_nonneg1122c _ hε0 i
  refine hmono.trans ?_
  rw [hsp]
  have h1 : ∑ n ∈ (Finset.Icc 1 71).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 132.772201 := by
    rw [icc_even1122c, Finset.sum_image (by intro x _ y _ h; simp only [] at h; omega)]
    exact prefix_even1122c
  have h2 : ∑ n ∈ (Finset.Ioc 71 500).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 2.064097 := by
    rw [ioc_even1122c, Finset.sum_image (by intro x _ y _ h; simp only [] at h; omega)]
    exact tail_even_sum1122c
  linarith

/-- LEAF: the tail of the Table 1 computation at ε = 1/100000: for n > 500, c_n = 0.9607
and τ_n = κ' τ_(n-1) + O(0.9607 ^ n) with κ' < 1, so the sum of τ_n over odd n from 501 to
N is at most 0.49; interval value of the whole tail about 3.1e-6. Class MEDIUM: a
geometric bound from the recursion, after one certified value at n = 500. -/
theorem tau_odd_tail1122c (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.49 := by
  have hε0 : (0 : ℝ) ≤ 1 / 100000 := by norm_num
  have hb : ∀ n, bjsTau306 bjsC306 (1 / 100000) n ≤ 3000 * (0.965 : ℝ) ^ n :=
    tau_geometric1122c (1 / 100000) hε0 (le_refl _)
  have h1 : ∑ n ∈ (Finset.Ioc 500 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n
      ≤ ∑ n ∈ Finset.Ioc 500 N, bjsTau306 bjsC306 (1 / 100000) n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro i _ _; exact tau_nonneg1122c _ hε0 i
  have h2 : ∑ n ∈ Finset.Ioc 500 N, bjsTau306 bjsC306 (1 / 100000) n
      ≤ ∑ n ∈ Finset.Ioc 500 N, 3000 * (0.965 : ℝ) ^ n :=
    Finset.sum_le_sum (fun i _ => hb i)
  have hgeo : ∑ n ∈ Finset.Ioc 500 N, (0.965 : ℝ) ^ n ≤ (0.965 : ℝ) ^ 501 / (1 - 0.965) := by
    rw [show Finset.Ioc 500 N = Finset.Ico 501 (N + 1) from by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega]
    rw [Finset.sum_Ico_eq_sum_range]
    have hrw : ∀ k : ℕ, (0.965 : ℝ) ^ (501 + k) = (0.965 : ℝ) ^ 501 * (0.965 : ℝ) ^ k :=
      fun k => by rw [pow_add]
    simp only [hrw]
    rw [← Finset.mul_sum]
    have hg : ∑ k ∈ Finset.range (N + 1 - 501), (0.965 : ℝ) ^ k ≤ 1 / (1 - 0.965) :=
      geom_range_le1122c _ (by norm_num) (by norm_num) _
    calc (0.965 : ℝ) ^ 501 * ∑ k ∈ Finset.range (N + 1 - 501), (0.965 : ℝ) ^ k
        ≤ (0.965 : ℝ) ^ 501 * (1 / (1 - 0.965)) :=
          mul_le_mul_of_nonneg_left hg (pow_nonneg (by norm_num) 501)
      _ = (0.965 : ℝ) ^ 501 / (1 - 0.965) := by ring
  have hsmall : (0.965 : ℝ) ^ 501 ≤ 1 / 10000000 := by
    have h20 : (0.965 : ℝ) ^ 20 ≤ 1 / 2 := by norm_num
    have h500 : (0.965 : ℝ) ^ 500 = ((0.965 : ℝ) ^ 20) ^ 25 := by rw [← pow_mul]
    have h500' : (0.965 : ℝ) ^ 500 ≤ ((1 : ℝ) / 2) ^ 25 := by
      rw [h500]; exact pow_le_pow_left₀ (by norm_num) h20 25
    have hp500 : (0 : ℝ) ≤ (0.965 : ℝ) ^ 500 := pow_nonneg (by norm_num) 500
    have h501 : (0.965 : ℝ) ^ 501 ≤ ((1 : ℝ) / 2) ^ 25 := by
      rw [pow_succ]
      have hstep : (0.965 : ℝ) ^ 500 * 0.965 ≤ (0.965 : ℝ) ^ 500 * 1 :=
        mul_le_mul_of_nonneg_left (by norm_num) hp500
      linarith
    have h25 : ((1 : ℝ) / 2) ^ 25 = 1 / 33554432 := by norm_num
    rw [h25] at h501
    calc (0.965 : ℝ) ^ 501 ≤ 1 / 33554432 := h501
      _ ≤ 1 / 10000000 := by norm_num
  have hden : (0 : ℝ) < 1 - 0.965 := by norm_num
  refine le_trans h1 (le_trans h2 ?_)
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left hgeo (by norm_num)) ?_
  have hstep : (0.965 : ℝ) ^ 501 / (1 - 0.965) ≤ (1 / 10000000) / (1 - 0.965) := by
    rw [div_le_div_iff₀ hden hden]
    exact mul_le_mul_of_nonneg_right hsmall (le_of_lt hden)
  calc 3000 * ((0.965 : ℝ) ^ 501 / (1 - 0.965))
      ≤ 3000 * ((1 / 10000000) / (1 - 0.965)) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ ≤ 0.49 := by norm_num

/-- LEAF: as tau_odd_tail1122c over even n, bound 0.16. Class MEDIUM. -/
theorem tau_even_tail1122c (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.16 := by
  have hε0 : (0 : ℝ) ≤ 1 / 100000 := by norm_num
  have hb : ∀ n, bjsTau306 bjsC306 (1 / 100000) n ≤ 3000 * (0.965 : ℝ) ^ n :=
    tau_geometric1122c (1 / 100000) hε0 (le_refl _)
  have h1 : ∑ n ∈ (Finset.Ioc 500 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n
      ≤ ∑ n ∈ Finset.Ioc 500 N, bjsTau306 bjsC306 (1 / 100000) n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro i _ _; exact tau_nonneg1122c _ hε0 i
  have h2 : ∑ n ∈ Finset.Ioc 500 N, bjsTau306 bjsC306 (1 / 100000) n
      ≤ ∑ n ∈ Finset.Ioc 500 N, 3000 * (0.965 : ℝ) ^ n :=
    Finset.sum_le_sum (fun i _ => hb i)
  have hgeo : ∑ n ∈ Finset.Ioc 500 N, (0.965 : ℝ) ^ n ≤ (0.965 : ℝ) ^ 501 / (1 - 0.965) := by
    rw [show Finset.Ioc 500 N = Finset.Ico 501 (N + 1) from by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega]
    rw [Finset.sum_Ico_eq_sum_range]
    have hrw : ∀ k : ℕ, (0.965 : ℝ) ^ (501 + k) = (0.965 : ℝ) ^ 501 * (0.965 : ℝ) ^ k :=
      fun k => by rw [pow_add]
    simp only [hrw]
    rw [← Finset.mul_sum]
    have hg : ∑ k ∈ Finset.range (N + 1 - 501), (0.965 : ℝ) ^ k ≤ 1 / (1 - 0.965) :=
      geom_range_le1122c _ (by norm_num) (by norm_num) _
    calc (0.965 : ℝ) ^ 501 * ∑ k ∈ Finset.range (N + 1 - 501), (0.965 : ℝ) ^ k
        ≤ (0.965 : ℝ) ^ 501 * (1 / (1 - 0.965)) :=
          mul_le_mul_of_nonneg_left hg (pow_nonneg (by norm_num) 501)
      _ = (0.965 : ℝ) ^ 501 / (1 - 0.965) := by ring
  have hsmall : (0.965 : ℝ) ^ 501 ≤ 1 / 10000000 := by
    have h20 : (0.965 : ℝ) ^ 20 ≤ 1 / 2 := by norm_num
    have h500 : (0.965 : ℝ) ^ 500 = ((0.965 : ℝ) ^ 20) ^ 25 := by rw [← pow_mul]
    have h500' : (0.965 : ℝ) ^ 500 ≤ ((1 : ℝ) / 2) ^ 25 := by
      rw [h500]; exact pow_le_pow_left₀ (by norm_num) h20 25
    have hp500 : (0 : ℝ) ≤ (0.965 : ℝ) ^ 500 := pow_nonneg (by norm_num) 500
    have h501 : (0.965 : ℝ) ^ 501 ≤ ((1 : ℝ) / 2) ^ 25 := by
      rw [pow_succ]
      have hstep : (0.965 : ℝ) ^ 500 * 0.965 ≤ (0.965 : ℝ) ^ 500 * 1 :=
        mul_le_mul_of_nonneg_left (by norm_num) hp500
      linarith
    have h25 : ((1 : ℝ) / 2) ^ 25 = 1 / 33554432 := by norm_num
    rw [h25] at h501
    calc (0.965 : ℝ) ^ 501 ≤ 1 / 33554432 := h501
      _ ≤ 1 / 10000000 := by norm_num
  have hden : (0 : ℝ) < 1 - 0.965 := by norm_num
  refine le_trans h1 (le_trans h2 ?_)
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left hgeo (by norm_num)) ?_
  have hstep : (0.965 : ℝ) ^ 501 / (1 - 0.965) ≤ (1 / 10000000) / (1 - 0.965) := by
    rw [div_le_div_iff₀ hden hden]
    exact mul_le_mul_of_nonneg_right hsmall (le_of_lt hden)
  calc 3000 * ((0.965 : ℝ) ^ 501 / (1 - 0.965))
      ≤ 3000 * ((1 / 10000000) / (1 - 0.965)) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ ≤ 0.16 := by norm_num

/-- Splitting a filtered sum over Icc 1 N at 500. -/
theorem sum_split500_1122c (p : ℕ → Prop) [DecidablePred p] (u : ℕ → ℝ) (N : ℕ)
    (hN : 500 ≤ N) :
    ∑ n ∈ (Finset.Icc 1 N).filter p, u n =
      ∑ n ∈ (Finset.Icc 1 500).filter p, u n + ∑ n ∈ (Finset.Ioc 500 N).filter p, u n := by
  have h1 : ∀ M : ℕ, Finset.Icc 1 M = Finset.Ioc 0 M := fun M => by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1, h1, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_Ioc_consecutive _ (Nat.zero_le 500) hN]

/-- Twin of tau_odd_sum_le132_1122c, statement verbatim, from the LEAFs above. -/
theorem tau_odd_sum_le132_twin1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤ 132 := by
  have hm : ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤
      ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n :=
    Finset.sum_le_sum fun n _ => tau_mono_eps1122c ε hε hε5 n
  refine hm.trans ?_
  rcases le_or_gt N 500 with h | h
  · linarith [tau_odd_le500_1122c N h]
  · rw [sum_split500_1122c Odd _ N h.le]
    linarith [tau_odd_le500_1122c 500 le_rfl, tau_odd_tail1122c N]

/-- Twin of tau_even_sum_le135_1122c, statement verbatim, from the LEAFs above. -/
theorem tau_even_sum_le135_twin1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 ε n ≤ 135 := by
  have hm : ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 ε n ≤
      ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n :=
    Finset.sum_le_sum fun n _ => tau_mono_eps1122c ε hε hε5 n
  refine hm.trans ?_
  rcases le_or_gt N 500 with h | h
  · linarith [tau_even_le500_1122c N h]
  · rw [sum_split500_1122c Even _ N h.le]
    linarith [tau_even_le500_1122c 500 le_rfl, tau_even_tail1122c N]

end LeanLab.Cai2002
