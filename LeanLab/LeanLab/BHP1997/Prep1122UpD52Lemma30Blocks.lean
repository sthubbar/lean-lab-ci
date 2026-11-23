/-
P0069 Baker Harman Pintz 1997, page 49, proof of Lemma 34, first line: "Here f_m satisfies
5.1 and 5.2 by Lemma 30". Burst burst-20261122, leaf `upD52_leaf_f_lemma30` of
`Prep1122UpD52Split`.

Lemma 30 on page 44 is stated for one dyadic block n ~ N with N at most
Y^(1/2 + theta2/4 - eps), the range 5.5. The sum f_m runs over all n at most
Y^(1/2 + theta2/4 - 2 eps), so f is a sum of O(L) dyadic blocks. Here: the cut of f into the
blocks 2^j <= n < 2^(j+1), j at most log_2 of Y^(1/2 + theta2/4 - 2 eps), is PROVED exactly,
with the coefficients a_n cut off above Y^(1/2 + theta2/4 - 2 eps), which keeps 3.1; the
count of blocks is at most log x and each block lies in the range 5.5, PROVED; the passage
from the blocks to f is `upD52_combine_blocks`, PROVED. The one LEAF is Lemma 30 for one block.
No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122UpD52Combine

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF: P0069 page 44, Lemma 30, the conclusion 5.2 of page 43 for the principal character,
for one dyadic block: b_m = sum over n ~ N, nl = m of a_n psi(l, w), with (a_n) satisfying 3.1,
w = exp(log^(9/10) x) of page 25, and N at most Y^(1/2 + theta2/4 - eps), the range 5.5. Here
n ~ N is read as N <= n < 2N, and the constant is uniform in N, as the paper uses it in
Lemma 34. CONDITIONAL on the cited Theorem 4 and Lemma 9. Class HARD. -/
theorem upD52_leaf_lemma30_block (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℕ → ℝ)
    (hc : ∀ x N k, c x N k = ∑ n ∈ k.divisors.filter (fun n : ℕ => N ≤ n ∧ n < 2 * N),
        a x n * upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε) →
      ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x N m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x N m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  sorry

/-- The dyadic cut of a divisor sum with n at most Z into the blocks 2^j <= n < 2^(j+1),
j <= log_2 floor(Z), with the coefficient cut off above Z. PROVED. -/
theorem upD52L30_dyadic (Z : ℝ) (a g : ℕ → ℝ) (k : ℕ) :
    ∑ n ∈ k.divisors.filter (fun n : ℕ => (n : ℝ) ≤ Z), a n * g n =
      ∑ j ∈ Finset.range (Nat.log 2 ⌊Z⌋₊ + 1),
        ∑ n ∈ k.divisors.filter (fun n : ℕ => 2 ^ j ≤ n ∧ n < 2 * 2 ^ j),
          (if (n : ℝ) ≤ Z then a n else 0) * g n := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hn)
  have hiff : ∀ j : ℕ, (2 ^ j ≤ n ∧ n < 2 * 2 ^ j) ↔ Nat.log 2 n = j := by
    intro j
    rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, hn0⟩), pow_succ, mul_comm (2 ^ j) 2]
  simp only [hiff]
  rw [Finset.sum_ite_eq]
  by_cases hZ : (n : ℝ) ≤ Z
  · have hmem : Nat.log 2 n ∈ Finset.range (Nat.log 2 ⌊Z⌋₊ + 1) := by
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.log_mono_right (Nat.le_floor hZ)
    simp [hmem, hZ]
  · simp [hZ]

/-- The coefficients cut off above Z keep 3.1 with the same constant. PROVED. -/
theorem upD52L30_cut_31 (a : ℝ → ℕ → ℝ) {B : ℝ} (Z : ℝ → ℝ)
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ C : ℝ, ∀ x n, |(fun x (n : ℕ) => if (n : ℝ) ≤ Z x then a x n else 0) x n| ≤
      C * ((n.divisors.card : ℕ) : ℝ) ^ B := by
  obtain ⟨C, hC⟩ := ha
  have hC0 : 0 ≤ C := by
    have h := hC 0 1
    simp at h
    exact le_trans (abs_nonneg _) h
  refine ⟨C, fun x n => ?_⟩
  simp only
  split_ifs
  · exact hC x n
  · simp only [abs_zero]
    positivity

/-- For x >= e^4 the number of dyadic blocks, log_2 floor(Y^(1/2 + theta2/4 - 2 eps)) + 1, is
at most log x. PROVED. -/
theorem upD52L30_J_le {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (x : ℝ)
    (hx : Real.exp 4 ≤ x) :
    ((Nat.log 2 ⌊(x ^ (11 / 20 + ε)) ^
        (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 4 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at this
  have hx1 : 1 ≤ x := by
    have := Real.add_one_le_exp (4 : ℝ)
    linarith
  set F := ⌊(x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)⌋₊ with hF
  set L := Nat.log 2 F with hLdef
  push_cast
  by_cases hF0 : F = 0
  · have : L = 0 := by rw [hLdef, hF0]; simp
    rw [this]; push_cast; linarith
  have hZ : (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) ≤
      x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul hx0.le]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    nlinarith
  have hZ0 : 0 ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) := by
    positivity
  have h2L : ((2 : ℝ) ^ L) ≤ x ^ (1 / 2 : ℝ) := by
    have h1 : 2 ^ L ≤ F := Nat.pow_log_le_self 2 hF0
    have h2 : ((2 ^ L : ℕ) : ℝ) ≤ (F : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact le_trans h2 (le_trans (Nat.floor_le hZ0) hZ)
  have hlog := Real.log_le_log (by positivity) h2L
  rw [Real.log_pow, Real.log_rpow hx0] at hlog
  have hl2 := Real.log_two_gt_d9
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  nlinarith

/-- For x >= 1 and j below the block count, the block 2^j <= n < 2^(j+1) has 1 <= 2^j and
2^j at most Y^(1/2 + theta2/4 - eps), the range 5.5 of Lemma 30. PROVED. -/
theorem upD52L30_block_range {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (x : ℝ)
    (hx : 1 ≤ x) (j : ℕ)
    (hj : j < Nat.log 2 ⌊(x ^ (11 / 20 + ε)) ^
        (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)⌋₊ + 1) :
    1 ≤ 2 ^ j ∧ (((2 ^ j : ℕ)) : ℝ) ≤
      (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε) := by
  refine ⟨Nat.one_le_two_pow, ?_⟩
  have hY : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx (by linarith)
  have hZ1 : 1 ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) :=
    Real.one_le_rpow hY (by nlinarith)
  set F := ⌊(x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)⌋₊ with hF
  have hF1 : 1 ≤ F := Nat.le_floor (by exact_mod_cast hZ1)
  have h1 : 2 ^ j ≤ F :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp hj))
      (Nat.pow_log_le_self 2 (by omega))
  have h2 : (((2 ^ j : ℕ)) : ℝ) ≤ (F : ℝ) := by exact_mod_cast h1
  refine le_trans h2 (le_trans (Nat.floor_le (by linarith)) ?_)
  exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)

/-- P0069 page 49, proof of Lemma 34: f_m satisfies 5.2 by Lemma 30, with the exact statement
of `upD52_leaf_f_lemma30`. PROVED from the one-block LEAF `upD52_leaf_lemma30_block` by the
dyadic cut `upD52L30_dyadic`, the block count `upD52L30_J_le`, the range check
`upD52L30_block_range` and `upD52_combine_blocks`. CONDITIONAL on the cited Theorem 4 and
Lemma 9. -/
theorem upD52_f_lemma30_of_blocks (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  have ha' := upD52L30_cut_31 a (fun x =>
    (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)) ha
  refine upD52_combine_blocks c
    (fun x j k => ∑ n ∈ k.divisors.filter (fun n : ℕ => 2 ^ j ≤ n ∧ n < 2 * 2 ^ j),
      (fun x (n : ℕ) => if (n : ℝ) ≤
          (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)
        then a x n else 0) x n *
        upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
    (fun x => Nat.log 2 ⌊(x ^ (11 / 20 + ε)) ^
        (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)⌋₊ + 1) ?_ ?_
  · refine ⟨Real.exp 4, fun x hx => ⟨upD52L30_J_le hε hε8 x hx, fun k _ => ?_⟩⟩
    rw [hc x k]
    exact upD52L30_dyadic _ (a x) (fun n => upperRough (k / n)
      (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) k
  · intro A hA
    obtain ⟨C, hC⟩ := upD52_leaf_lemma30_block h4 h9 hε hε8 _ ha'
      (fun x N k => ∑ n ∈ k.divisors.filter (fun n : ℕ => N ≤ n ∧ n < 2 * N),
        (fun x (n : ℕ) => if (n : ℝ) ≤
            (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)
          then a x n else 0) x n *
          upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
      (fun _ _ _ => rfl) A hA
    refine ⟨max C 1, fun x hx j hj q hq1 hqQ => ?_⟩
    obtain ⟨h1, h2⟩ := upD52L30_block_range hε hε8 x (le_trans (le_max_right _ _) hx) j hj
    refine le_trans (hC x (le_trans (le_max_left _ _) hx) (2 ^ j) h1 h2 q hq1 hqQ) ?_
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hY0 : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
    have hRL : 0 ≤ (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
        Real.log x ^ (-A) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hRL

end LeanLab.BHP1997.DecompC165d
