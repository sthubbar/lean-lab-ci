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

/-- LEAF: BJS Proposition 13, the finite part of the Table 1 computation at ε = 1/100000:
the partial sums of τ_n over odd n up to N ≤ 500 are at most 131.508; interval value of the
full sum to 500 is 131.5073810. Class HARD: certified evaluation of 500 recursive terms
with exp and max. -/
theorem tau_odd_le500_1122c (N : ℕ) (hN : N ≤ 500) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 131.508 := by
  sorry

/-- LEAF: as tau_odd_le500_1122c over even n, bound 134.837; interval value 134.8362246.
Class HARD. -/
theorem tau_even_le500_1122c (N : ℕ) (hN : N ≤ 500) :
    ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 134.837 := by
  sorry

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

#print axioms LeanLab.Cai2002.sum_split500_1122c
#print axioms LeanLab.Cai2002.tau_odd_sum_le132_twin1122c
#print axioms LeanLab.Cai2002.tau_even_sum_le135_twin1122c
