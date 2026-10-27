/-
P0038 Shao 2012, Proposition 3.2, the real-variable part: three non-increasing sequences of
length 8 in [0, 1], the sorted values of f₁, f₂, f₃ on the units mod 15. If no admissible
index triple, j₁j₂ + j₂j₃ + j₃j₁ > 5(j₁ + j₂ + j₃) with all three values positive, has values
summing past 3/2, then T(F₁, F₂, F₃) = F₁F₂ + F₂F₃ + F₃F₁ - 5(F₁ + F₂ + F₃) ≤ 0.
One lemma per sorted support pattern, 34 of them as in the paper; the linear programming
bounds 15, 15.5 and 16 are proved by `linarith only` from the dual support that a solver
found, so the kernel checks each certificate.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0125.
-/
import Mathlib

open Finset

namespace LeanLab.DensityGoldbach.P32

/-- In `[0, 1]` and non-increasing on `0, …, 7`. -/
def Good (x : ℕ → ℝ) : Prop :=
  (∀ j < 8, 0 ≤ x j ∧ x j ≤ 1) ∧ ∀ i j, i ≤ j → j < 8 → x j ≤ x i

/-- Exactly the first `n` of the eight values are positive. -/
def Supp (x : ℕ → ℝ) (n : ℕ) : Prop := ∀ j < 8, (0 < x j ↔ j < n)

/-- No admissible index triple with positive values sums past `3/2`; indices are 0-based. -/
def Bad (x y z : ℕ → ℝ) : Prop := ∀ j₁ j₂ j₃ : ℕ, j₁ < 8 → j₂ < 8 → j₃ < 8 →
  5 * ((j₁ + 1) + (j₂ + 1) + (j₃ + 1)) < (j₁ + 1) * (j₂ + 1) + (j₂ + 1) * (j₃ + 1)
    + (j₃ + 1) * (j₁ + 1) →
  0 < x j₁ → 0 < y j₂ → 0 < z j₃ → x j₁ + y j₂ + z j₃ ≤ 3 / 2

/-- `T(a, b, c) = ab + bc + ca - 5(a + b + c)`. -/
def Tf (a b c : ℝ) : ℝ := a * b + b * c + c * a - 5 * (a + b + c)

def sum8 (x : ℕ → ℝ) : ℝ := x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7

lemma z_of {x : ℕ → ℝ} {n : ℕ} (hg : Good x) (hs : Supp x n) (j : ℕ) (hj : j < 8)
    (hn : n ≤ j) : x j = 0 :=
  le_antisymm (not_lt.1 fun h => absurd ((hs j hj).1 h) (by omega)) (hg.1 j hj).1

lemma p_of {x : ℕ → ℝ} {n : ℕ} (_hg : Good x) (hs : Supp x n) (j : ℕ) (hj : j < 8)
    (hn : j < n) : 0 < x j := (hs j hj).2 hn

lemma m_of {x : ℕ → ℝ} (hg : Good x) (j k : ℕ) (hk : k = j + 1) (hk8 : k < 8) :
    x k ≤ x j := hg.2 j k (by omega) hk8

lemma o_of {x : ℕ → ℝ} (hg : Good x) (j : ℕ) (hj : j < 8) : x j ≤ 1 := (hg.1 j hj).2

lemma n_of {x : ℕ → ℝ} (hg : Good x) (j : ℕ) (hj : j < 8) : 0 ≤ x j := (hg.1 j hj).1

lemma sum8_eq (x : ℕ → ℝ) : sum8 x = ∑ j ∈ range 8, x j := by
  simp [sum8, sum_range_succ]

lemma sum8_nonneg {x : ℕ → ℝ} (hg : Good x) : 0 ≤ sum8 x := by
  unfold sum8
  linarith [n_of hg 0 (by norm_num), n_of hg 1 (by norm_num), n_of hg 2 (by norm_num),
    n_of hg 3 (by norm_num), n_of hg 4 (by norm_num), n_of hg 5 (by norm_num),
    n_of hg 6 (by norm_num), n_of hg 7 (by norm_num)]

lemma sum8_le {x : ℕ → ℝ} {n : ℕ} (hg : Good x) (hs : Supp x n) (hn : n ≤ 8) :
    sum8 x ≤ n := by
  rw [sum8_eq]
  calc ∑ j ∈ range 8, x j ≤ ∑ j ∈ range 8, (if j < n then (1 : ℝ) else 0) := by
        apply sum_le_sum
        intro j hj
        have hj8 := mem_range.1 hj
        split_ifs with h
        · exact o_of hg j hj8
        · exact (z_of hg hs j hj8 (not_lt.1 h)).le
    _ = n := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]
        congr 1
        have : (range 8).filter (fun j => j < n) = range n := by
          ext j; simp only [mem_filter, mem_range]; omega
        rw [this, card_range]

lemma T15 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c ≤ 15) :
    Tf a b c ≤ 0 := by
  unfold Tf
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sub_nonneg.2 h)]

/-- `a ≤ 2`, `a + t ≤ 16` with `t = b + c`: `T ≤ a t + t²/4 - 5a - 5t ≤ 0`. -/
lemma T16 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h1 : a ≤ 2)
    (h : a + b + c ≤ 16) : Tf a b c ≤ 0 := by
  unfold Tf
  have hbc : b * c ≤ (b + c) ^ 2 / 4 := by nlinarith [sq_nonneg (b - c)]
  have ht : (b + c) * (b + c) ≤ (16 - a) * (b + c) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith [mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg (add_nonneg hb hc) (sub_nonneg.2 h1)]

/-- `a ≤ 3`, `a + t ≤ 15.5`. -/
lemma T155 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h1 : a ≤ 3)
    (h : a + b + c ≤ 31 / 2) : Tf a b c ≤ 0 := by
  unfold Tf
  have hbc : b * c ≤ (b + c) ^ 2 / 4 := by nlinarith [sq_nonneg (b - c)]
  have ht : (b + c) * (b + c) ≤ (31 / 2 - a) * (b + c) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith [mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg (add_nonneg hb hc) (sub_nonneg.2 h1)]

/-- `a + b ≤ 8`, `a + b + c ≤ 15.5`. -/
lemma T458 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h1 : a + b ≤ 8)
    (h : a + b + c ≤ 31 / 2) : Tf a b c ≤ 0 := by
  unfold Tf
  have hab : a * b ≤ (a + b) ^ 2 / 4 := by nlinarith [sq_nonneg (a - b)]
  by_cases hp : a + b ≤ 5
  · nlinarith [mul_nonneg hc (sub_nonneg.2 hp), add_nonneg ha hb]
  · push Not at hp
    have hc' : (a + b - 5) * c ≤ (a + b - 5) * (31 / 2 - (a + b)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hp.le)]

theorem pat_2_7_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 2) (hsy : Supp y 7) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (31 / 2 : ℝ) := by
    unfold sum8
    linarith only [hB 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgy 4 (by norm_num),
      o_of hgy 5 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      o_of hgz 5 (by norm_num),
      o_of hgz 6 (by norm_num),
      z_of hgx hsx 2 (by norm_num) (by norm_num),
      z_of hgx hsx 3 (by norm_num) (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num)]
  exact T16 _ _ _ nx ny nz (sum8_le hgx hsx (by norm_num)) (by linarith)

theorem pat_2_8_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 2) (hsy : Supp y 8) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (16 : ℝ) := by
    unfold sum8
    linarith only [hB 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 1 7 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 7 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgy 4 (by norm_num),
      o_of hgy 5 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      o_of hgz 5 (by norm_num),
      n_of hgx 1 (by norm_num),
      z_of hgx hsx 2 (by norm_num) (by norm_num),
      z_of hgx hsx 3 (by norm_num) (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num)]
  exact T16 _ _ _ nx ny nz (sum8_le hgx hsx (by norm_num)) (by linarith)

theorem pat_3_6_7 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 3) (hsy : Supp y 6) (hsz : Supp z 7) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (29 / 2 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgy 4 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      o_of hgz 5 (by norm_num),
      z_of hgx hsx 3 (by norm_num) (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_3_6_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 3) (hsy : Supp y 6) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (31 / 2 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgy 4 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      o_of hgz 5 (by norm_num),
      o_of hgz 6 (by norm_num),
      z_of hgx hsx 3 (by norm_num) (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num)]
  exact T155 _ _ _ nx ny nz (sum8_le hgx hsx (by norm_num)) (by linarith)

theorem pat_3_7_7 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 3) (hsy : Supp y 7) (hsz : Supp z 7) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (15 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgy 4 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      n_of hgx 2 (by norm_num),
      z_of hgx hsx 3 (by norm_num) (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_3_7_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 3) (hsy : Supp y 7) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (15 : ℝ) := by
    unfold sum8
    linarith only [hB 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgy 4 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      o_of hgz 5 (by norm_num),
      z_of hgx hsx 3 (by norm_num) (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_3_8_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 3) (hsy : Supp y 8) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (31 / 2 : ℝ) := by
    unfold sum8
    linarith only [hB 1 7 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 7 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgy 4 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      n_of hgx 2 (by norm_num),
      z_of hgx hsx 3 (by norm_num) (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num)]
  exact T155 _ _ _ nx ny nz (sum8_le hgx hsx (by norm_num)) (by linarith)

theorem pat_4_5_7 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 4) (hsy : Supp y 5) (hsz : Supp z 7) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (29 / 2 : ℝ) := by
    unfold sum8
    linarith only [hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      o_of hgz 5 (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 5 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_4_5_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 4) (hsy : Supp y 5) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  by_cases hext' : 8 ≤ sum8 x + sum8 y
  · have hext : -(sum8 x + sum8 y) ≤ -8 := by linarith
    unfold sum8 at hext
    have hS : sum8 x + sum8 y + sum8 z ≤ (15 : ℝ) := by
      unfold sum8
      linarith only [m_of hgz 6 7 rfl (by norm_num),
        hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
        hext,
        o_of hgx 0 (by norm_num),
        o_of hgx 1 (by norm_num),
        o_of hgx 2 (by norm_num),
        o_of hgy 0 (by norm_num),
        o_of hgy 1 (by norm_num),
        o_of hgy 2 (by norm_num),
        o_of hgy 3 (by norm_num),
        o_of hgz 0 (by norm_num),
        o_of hgz 1 (by norm_num),
        o_of hgz 2 (by norm_num),
        o_of hgz 3 (by norm_num),
        o_of hgz 4 (by norm_num),
        o_of hgz 5 (by norm_num),
        z_of hgx hsx 4 (by norm_num) (by norm_num),
        z_of hgx hsx 5 (by norm_num) (by norm_num),
        z_of hgx hsx 6 (by norm_num) (by norm_num),
        z_of hgx hsx 7 (by norm_num) (by norm_num),
        z_of hgy hsy 5 (by norm_num) (by norm_num),
        z_of hgy hsy 6 (by norm_num) (by norm_num),
        z_of hgy hsy 7 (by norm_num) (by norm_num)]
    exact T15 _ _ _ nx ny nz (by linarith)
  · push Not at hext'
    have hS : sum8 x + sum8 y + sum8 z ≤ (31 / 2 : ℝ) := by
      unfold sum8
      linarith only [hB 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
        o_of hgx 0 (by norm_num),
        o_of hgx 1 (by norm_num),
        o_of hgx 2 (by norm_num),
        o_of hgy 0 (by norm_num),
        o_of hgy 1 (by norm_num),
        o_of hgy 2 (by norm_num),
        o_of hgy 3 (by norm_num),
        o_of hgz 0 (by norm_num),
        o_of hgz 1 (by norm_num),
        o_of hgz 2 (by norm_num),
        o_of hgz 3 (by norm_num),
        o_of hgz 4 (by norm_num),
        o_of hgz 5 (by norm_num),
        o_of hgz 6 (by norm_num),
        z_of hgx hsx 4 (by norm_num) (by norm_num),
        z_of hgx hsx 5 (by norm_num) (by norm_num),
        z_of hgx hsx 6 (by norm_num) (by norm_num),
        z_of hgx hsx 7 (by norm_num) (by norm_num),
        z_of hgy hsy 5 (by norm_num) (by norm_num),
        z_of hgy hsy 6 (by norm_num) (by norm_num),
        z_of hgy hsy 7 (by norm_num) (by norm_num)]
    exact T458 _ _ _ nx ny nz hext'.le hS

theorem pat_4_6_6 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 4) (hsy : Supp y 6) (hsz : Supp z 6) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (29 / 2 : ℝ) := by
    unfold sum8
    linarith only [hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgy 4 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 6 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_4_6_7 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 4) (hsy : Supp y 6) (hsz : Supp z 7) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (59 / 4 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgy 4 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      o_of hgz 5 (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_4_6_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 4) (hsy : Supp y 6) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (15 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      o_of hgz 5 (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_4_7_7 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 4) (hsy : Supp y 7) (hsz : Supp z 7) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (59 / 4 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgy 4 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      n_of hgx 3 (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_4_7_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 4) (hsy : Supp y 7) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (15 : ℝ) := by
    unfold sum8
    linarith only [hB 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      n_of hgx 3 (by norm_num),
      z_of hgx hsx 4 (by norm_num) (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_4_8_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 4) (hsy : Supp y 8) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  by_cases hext' : 3 ≤ sum8 x
  · have hext : -(sum8 x) ≤ -3 := by linarith
    unfold sum8 at hext
    have hS : sum8 x + sum8 y + sum8 z ≤ (15 : ℝ) := by
      unfold sum8
      linarith only [hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
        hB 2 7 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 7 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
        hB 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
        hB 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
        hext,
        o_of hgx 0 (by norm_num),
        o_of hgx 1 (by norm_num),
        o_of hgy 0 (by norm_num),
        o_of hgy 1 (by norm_num),
        o_of hgy 2 (by norm_num),
        o_of hgy 3 (by norm_num),
        o_of hgz 0 (by norm_num),
        o_of hgz 1 (by norm_num),
        o_of hgz 2 (by norm_num),
        o_of hgz 3 (by norm_num),
        z_of hgx hsx 4 (by norm_num) (by norm_num),
        z_of hgx hsx 5 (by norm_num) (by norm_num),
        z_of hgx hsx 6 (by norm_num) (by norm_num),
        z_of hgx hsx 7 (by norm_num) (by norm_num)]
    exact T15 _ _ _ nx ny nz (by linarith)
  · push Not at hext'
    have hS : sum8 x + sum8 y + sum8 z ≤ (61 / 4 : ℝ) := by
      unfold sum8
      linarith only [m_of hgz 6 7 rfl (by norm_num),
        hB 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
        hB 1 7 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 7 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
        hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
        hB 2 7 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 7 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
        hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
        hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
        hB 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
        o_of hgx 0 (by norm_num),
        o_of hgy 0 (by norm_num),
        o_of hgy 1 (by norm_num),
        o_of hgy 2 (by norm_num),
        o_of hgy 3 (by norm_num),
        o_of hgy 4 (by norm_num),
        o_of hgz 0 (by norm_num),
        o_of hgz 1 (by norm_num),
        o_of hgz 2 (by norm_num),
        o_of hgz 3 (by norm_num),
        o_of hgz 4 (by norm_num),
        n_of hgx 3 (by norm_num),
        z_of hgx hsx 4 (by norm_num) (by norm_num),
        z_of hgx hsx 5 (by norm_num) (by norm_num),
        z_of hgx hsx 6 (by norm_num) (by norm_num),
        z_of hgx hsx 7 (by norm_num) (by norm_num)]
    exact T155 _ _ _ nx ny nz hext'.le (by linarith)

theorem pat_5_5_6 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 5) (hsy : Supp y 5) (hsz : Supp z 6) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (29 / 2 : ℝ) := by
    unfold sum8
    linarith only [hB 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgx 3 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 5 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 6 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_5_5_7 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 5) (hsy : Supp y 5) (hsz : Supp z 7) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (59 / 4 : ℝ) := by
    unfold sum8
    linarith only [hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgx 3 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      o_of hgz 5 (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 5 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_5_5_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 5) (hsy : Supp y 5) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (15 : ℝ) := by
    unfold sum8
    linarith only [hB 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      o_of hgz 5 (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 5 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_5_6_6 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 5) (hsy : Supp y 6) (hsz : Supp z 6) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (59 / 4 : ℝ) := by
    unfold sum8
    linarith only [hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgx 3 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgy 4 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 6 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_5_6_7 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 5) (hsy : Supp y 6) (hsz : Supp z 7) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (117 / 8 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_5_6_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 5) (hsy : Supp y 6) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (15 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      o_of hgz 5 (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_5_7_7 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 5) (hsy : Supp y 7) (hsz : Supp z 7) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (29 / 2 : ℝ) := by
    unfold sum8
    linarith only [hB 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_5_7_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 5) (hsy : Supp y 7) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (149 / 10 : ℝ) := by
    unfold sum8
    linarith only [hB 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_5_8_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 5) (hsy : Supp y 8) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (15 : ℝ) := by
    unfold sum8
    linarith only [hB 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 7 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 7 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      z_of hgx hsx 5 (by norm_num) (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_6_6_6 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 6) (hsy : Supp y 6) (hsz : Supp z 6) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (117 / 8 : ℝ) := by
    unfold sum8
    linarith only [hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 5 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 5 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 3 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgx 3 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 6 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_6_6_7 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 6) (hsy : Supp y 6) (hsz : Supp z 7) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (29 / 2 : ℝ) := by
    unfold sum8
    linarith only [hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 5 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_6_6_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 6) (hsy : Supp y 6) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (149 / 10 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 4 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 5 2 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 2 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      o_of hgz 4 (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 6 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_6_7_7 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 6) (hsy : Supp y 7) (hsz : Supp z 7) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (73 / 5 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 4 6 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 3 (by norm_num) (by norm_num)),
      hB 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 5 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 5 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 3 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_6_7_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 6) (hsy : Supp y 7) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (207 / 14 : ℝ) := by
    unfold sum8
    linarith only [hB 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 5 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 2 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 5 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 5 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 3 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_6_8_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 6) (hsy : Supp y 8) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (15 : ℝ) := by
    unfold sum8
    linarith only [hB 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 1 7 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 7 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 4 7 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 7 (by norm_num) (by norm_num)) (p_of hgz hsz 3 (by norm_num) (by norm_num)),
      hB 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 5 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgy 3 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      z_of hgx hsx 6 (by norm_num) (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_7_7_7 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 7) (hsy : Supp y 7) (hsz : Supp z 7) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (102 / 7 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 5 2 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 2 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 5 6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 2 (by norm_num) (by norm_num)),
      hB 6 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 6 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 3 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num),
      z_of hgz hsz 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_7_7_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 7) (hsy : Supp y 7) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (59 / 4 : ℝ) := by
    unfold sum8
    linarith only [hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 4 6 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 3 (by norm_num) (by norm_num)),
      hB 5 2 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 2 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 5 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 6 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 6 (by norm_num) (by norm_num)) (p_of hgy hsy 2 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 6 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 6 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgx 2 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      o_of hgz 3 (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num),
      z_of hgy hsy 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_7_8_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 7) (hsy : Supp y 8) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (239 / 16 : ℝ) := by
    unfold sum8
    linarith only [hB 1 7 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 1 (by norm_num) (by norm_num)) (p_of hgy hsy 7 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 4 7 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 7 (by norm_num) (by norm_num)) (p_of hgz hsz 3 (by norm_num) (by norm_num)),
      hB 5 2 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 2 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 5 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 3 (by norm_num) (by norm_num)),
      hB 5 6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 2 (by norm_num) (by norm_num)),
      hB 6 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 6 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 6 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 6 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 2 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgy 2 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num),
      o_of hgz 2 (by norm_num),
      z_of hgx hsx 7 (by norm_num) (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

theorem pat_8_8_8 (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hsx : Supp x 8) (hsy : Supp y 8) (hsz : Supp z 8) (hB : Bad x y z) :
    Tf (sum8 x) (sum8 y) (sum8 z) ≤ 0 := by
  have nx := sum8_nonneg hgx
  have ny := sum8_nonneg hgy
  have nz := sum8_nonneg hgz
  have hS : sum8 x + sum8 y + sum8 z ≤ (15 : ℝ) := by
    unfold sum8
    linarith only [hB 2 7 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 2 (by norm_num) (by norm_num)) (p_of hgy hsy 7 (by norm_num) (by norm_num)) (p_of hgz hsz 5 (by norm_num) (by norm_num)),
      hB 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 3 (by norm_num) (by norm_num)) (p_of hgy hsy 6 (by norm_num) (by norm_num)) (p_of hgz hsz 4 (by norm_num) (by norm_num)),
      hB 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 4 (by norm_num) (by norm_num)) (p_of hgy hsy 3 (by norm_num) (by norm_num)) (p_of hgz hsz 6 (by norm_num) (by norm_num)),
      hB 5 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 5 (by norm_num) (by norm_num)) (p_of hgy hsy 2 (by norm_num) (by norm_num)) (p_of hgz hsz 7 (by norm_num) (by norm_num)),
      hB 6 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 6 (by norm_num) (by norm_num)) (p_of hgy hsy 4 (by norm_num) (by norm_num)) (p_of hgz hsz 3 (by norm_num) (by norm_num)),
      hB 7 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (p_of hgx hsx 7 (by norm_num) (by norm_num)) (p_of hgy hsy 5 (by norm_num) (by norm_num)) (p_of hgz hsz 2 (by norm_num) (by norm_num)),
      o_of hgx 0 (by norm_num),
      o_of hgx 1 (by norm_num),
      o_of hgy 0 (by norm_num),
      o_of hgy 1 (by norm_num),
      o_of hgz 0 (by norm_num),
      o_of hgz 1 (by norm_num)]
  exact T15 _ _ _ nx ny nz (by linarith)

lemma T_pair (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : 0 < Tf a b c) :
    5 < a + b := by
  unfold Tf at h
  by_contra hle
  push Not at hle
  nlinarith [mul_nonneg hc (sub_nonneg.2 hle), sq_nonneg (a - b)]

/-- `T` only grows coordinatewise from a point where it is positive. -/
lemma Tmono (a b c A B C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : a ≤ A)
    (hB : b ≤ B) (hC : c ≤ C) (h : 0 < Tf a b c) : 0 < Tf A B C := by
  have hab := T_pair a b c ha hb hc h
  have hbc := T_pair b c a hb hc ha (by unfold Tf at h ⊢; linarith)
  have hca := T_pair c a b hc ha hb (by unfold Tf at h ⊢; linarith)
  have s1 : Tf a b c ≤ Tf A b c := by unfold Tf; nlinarith
  have s2 : Tf A b c ≤ Tf A B c := by unfold Tf; nlinarith
  have s3 : Tf A B c ≤ Tf A B C := by unfold Tf; nlinarith
  linarith

/-- **The real part of Prop 3.2**, sorted supports `n₁ ≤ n₂ ≤ n₃`. -/
theorem real_main (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hB : Bad x y z) (n₁ n₂ n₃ : ℕ) (hsx : Supp x n₁) (hsy : Supp y n₂) (hsz : Supp z n₃)
    (h12 : n₁ ≤ n₂) (h23 : n₂ ≤ n₃) (h3 : n₃ ≤ 8)
    (hT : 0 < Tf (sum8 x) (sum8 y) (sum8 z)) : False := by
  have hN : 0 < Tf n₁ n₂ n₃ :=
    Tmono _ _ _ _ _ _ (sum8_nonneg hgx) (sum8_nonneg hgy) (sum8_nonneg hgz)
      (sum8_le hgx hsx (by omega)) (sum8_le hgy hsy (by omega)) (sum8_le hgz hsz h3) hT
  interval_cases n₃ <;> interval_cases n₂ <;> interval_cases n₁
  all_goals first
    | (norm_num [Tf] at hN; done)
    | exact absurd hT (not_lt.2 (pat_2_7_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_2_8_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_3_6_7 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_3_6_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_3_7_7 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_3_7_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_3_8_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_4_5_7 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_4_5_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_4_6_6 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_4_6_7 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_4_6_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_4_7_7 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_4_7_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_4_8_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_5_5_6 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_5_5_7 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_5_5_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_5_6_6 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_5_6_7 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_5_6_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_5_7_7 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_5_7_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_5_8_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_6_6_6 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_6_6_7 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_6_6_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_6_7_7 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_6_7_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_6_8_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_7_7_7 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_7_7_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_7_8_8 x y z hgx hgy hgz hsx hsy hsz hB))
    | exact absurd hT (not_lt.2 (pat_8_8_8 x y z hgx hgy hgz hsx hsy hsz hB))

end LeanLab.DensityGoldbach.P32
