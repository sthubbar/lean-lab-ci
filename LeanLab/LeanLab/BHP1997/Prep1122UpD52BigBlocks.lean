/-
P0069 Baker Harman Pintz 1997, pages 49 and 50, proof of Lemma 34, the part of g_m with
p1 >= Y^eps, cut into dyadic blocks in p1. Burst burst-20261122, wave on the leaf
`upD52_leaf_g_big_lemma33` of `Prep1122UpD52Split`.

The page says: "Let h_m be the contribution to g_m from n ~ N, p1 ~ P. With N(s, chi) the sum
over p1 ~ P of chi(p1) p1^(-s) we know from Lemma 5 that 3.2 holds, and of course if
P >= Y^eps we may obtain 5.1 and 5.2 from Lemma 33." Here only p1 is cut, into the blocks
P <= p1 < 2P with P = 2^j; the n range stays whole, since Lemma 33 treats the n factor as a
coefficient sequence satisfying 3.1.

`upD52_g_big_of_blocks` has the exact statement of `upD52_leaf_g_big_lemma33`. It is PROVED
from the one LEAF `upD52_leaf_lemma33_block` by the fiberwise split of the p1 sum along
Nat.log 2 p1, the count of blocks J x = Nat.log 2 (floor Y^c1) + 1 <= log x for large x, and
the PROVED rule `upD52_combine_blocks`. The LEAF takes P <= Y^c1, not P < Y^c1: a block with
P = 2^j at most floor Y^c1 satisfies the weak form directly, and the block condition
P <= p1 < Y^c1 inside the sum keeps the LEAF equally faithful.
No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122UpD52Combine

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF: P0069 pages 49 and 50, proof of Lemma 34, the block h_m of g_m with p1 ~ P, here
P <= p1 < 2P, P a power of 2 below Y^c1, restricted to Y^eps <= p1: 5.2 of page 43 for the
principal character follows from Lemma 33 case 5.13, with N(s, chi) the sum over p1 ~ P of
chi(p1) p1^(-s) satisfying 3.2 by Lemma 5. The constant is uniform in P. Stated for every
P with 1 <= P <= Y^c1. CONDITIONAL on the cited Theorem 4 and Lemma 9. Class HARD. The lowest
nonempty block may straddle Y^eps, the boundary of the strict inequality eps < beta2 of case
5.13, as in the paper's own P >= Y^eps; the paper also treats h_m as a product although
psi(n1, p1) couples n1 to p1. -/
theorem upD52_leaf_lemma33_block (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℕ → ℝ)
    (hc : ∀ x P k, c x P k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
          upperRough (k / n / p) (p : ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ P : ℕ, 1 ≤ P →
      (P : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x P m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x P m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  sorry

/-- The dyadic split of a sum over nonzero p along Nat.log 2 p: if every p in s is nonzero
with Nat.log 2 p < J, the sum over s is the sum over j < J of the sums over the blocks
2^j <= p < 2 * 2^j. PROVED. -/
theorem upBB_dyadic_split (s : Finset ℕ) (f : ℕ → ℝ) (J : ℕ)
    (hs : ∀ p ∈ s, p ≠ 0 ∧ Nat.log 2 p < J) :
    ∑ p ∈ s, f p = ∑ j ∈ Finset.range J,
      ∑ p ∈ s.filter (fun p : ℕ => 2 ^ j ≤ p ∧ p < 2 * 2 ^ j), f p := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Nat.log 2) (t := Finset.range J)
    (fun p hp => Finset.mem_range.mpr (hs p hp).2) f]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr (Finset.filter_congr (fun p hp => ?_)) (fun _ _ => rfl)
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, (hs p hp).1⟩), pow_succ']

/-- The number of dyadic blocks: for x >= exp 2, Nat.log 2 (floor Y^c1) + 1 <= log x, with
Y = x^(11/20 + eps). PROVED. -/
theorem upBB_J_le {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (x : ℝ)
    (hx : Real.exp 2 ≤ x) :
    ((Nat.log 2 (Nat.floor ((x ^ (11 / 20 + ε)) ^ upperC1 ε)) + 1 : ℕ) : ℝ) ≤ Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL2 : 2 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at this
  set N := Nat.floor ((x ^ (11 / 20 + ε)) ^ upperC1 ε) with hN
  set L := Nat.log 2 N with hLdef
  push_cast
  by_cases hN0 : N = 0
  · have : L = 0 := by rw [hLdef, hN0]; simp
    rw [this]; push_cast; linarith
  have hY0 : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hpow : (2 : ℝ) ^ L ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε := by
    have h1 : 2 ^ L ≤ N := Nat.pow_log_le_self 2 hN0
    have h2 : ((2 ^ L : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
    have h3 : (N : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε :=
      Nat.floor_le (Real.rpow_nonneg hY0.le _)
    push_cast at h2
    linarith
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_rpow hY0, Real.log_rpow hx0] at hlog
  have hl2 := Real.log_two_gt_d9
  have hc1 : upperC1 ε ≤ 13 / 100 := by unfold upperC1; norm_num; linarith
  have hc1' : 0 ≤ upperC1 ε := by unfold upperC1; norm_num; linarith
  have hLx : 0 ≤ Real.log x := by linarith
  have hk : upperC1 ε * ((11 / 20 + ε) * Real.log x) ≤ (13 / 100) * (6 / 10) * Real.log x := by
    have : (11 / 20 + ε) * Real.log x ≤ 6 / 10 * Real.log x := by nlinarith
    calc upperC1 ε * ((11 / 20 + ε) * Real.log x) ≤ 13 / 100 * ((11 / 20 + ε) * Real.log x) :=
          mul_le_mul_of_nonneg_right hc1 (by positivity)
      _ ≤ 13 / 100 * (6 / 10 * Real.log x) := by linarith
      _ = _ := by ring
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  nlinarith

/-- P0069 pages 49 and 50, proof of Lemma 34, the part of g_m with p1 >= Y^eps, with the exact
statement of `upD52_leaf_g_big_lemma33`. PROVED from the LEAF `upD52_leaf_lemma33_block`, one
block P <= p1 < 2P for each P = 2^j <= Y^c1, by the dyadic split `upBB_dyadic_split`, the block
count `upBB_J_le` and the PROVED rule `upD52_combine_blocks`. CONDITIONAL on the cited
Theorem 4 and Lemma 9. -/
theorem upD52_g_big_of_blocks (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (p : ℝ)) :
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
  obtain ⟨cb, hcb⟩ : ∃ cb : ℝ → ℕ → ℕ → ℝ, ∀ x P k, cb x P k = ∑ n ∈ k.divisors.filter
        (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
          upperRough (k / n / p) (p : ℝ) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hleaf := upD52_leaf_lemma33_block h4 h9 hε hε8 a ha cb hcb
  refine upD52_combine_blocks c (fun x j k => cb x (2 ^ j) k)
    (fun x => Nat.log 2 (Nat.floor ((x ^ (11 / 20 + ε)) ^ upperC1 ε)) + 1) ?_ ?_
  · refine ⟨Real.exp 2, fun x hx => ⟨upBB_J_le hε hε8 x hx, fun k _ => ?_⟩⟩
    rw [hc x k]
    simp only [hcb x _ k]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← Finset.mul_sum]
    congr 1
    refine (upBB_dyadic_split _ _ _ (fun p hp => ?_)).trans
      (Finset.sum_congr rfl (fun j _ => by rw [Finset.filter_filter]))
    rw [Finset.mem_filter] at hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    refine ⟨hpr.ne_zero, Nat.lt_succ_of_le (Nat.log_mono_right ?_)⟩
    exact Nat.le_floor hp.2.1.2.le
  · intro A hA
    obtain ⟨C, hC⟩ := hleaf A hA
    refine ⟨max C 1, fun x hx j hj q hq1 hqQ => ?_⟩
    have hCx : C ≤ x := le_trans (le_max_left _ _) hx
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hY1 : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 (by positivity)
    have hc1 : 0 ≤ upperC1 ε := by unfold upperC1; norm_num; linarith
    have hYc1 : 1 ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε := Real.one_le_rpow hY1 hc1
    have hN1 : 1 ≤ Nat.floor ((x ^ (11 / 20 + ε)) ^ upperC1 ε) :=
      Nat.le_floor (by exact_mod_cast hYc1)
    have hjle : 2 ^ j ≤ Nat.floor ((x ^ (11 / 20 + ε)) ^ upperC1 ε) :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp hj))
        (Nat.pow_log_le_self 2 (by omega))
    have hPle : ((2 ^ j : ℕ) : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε :=
      le_trans (by exact_mod_cast hjle) (Nat.floor_le (by linarith))
    refine le_trans (hC x hCx (2 ^ j) Nat.one_le_two_pow hPle q hq1 hqQ) ?_
    have hx0 : 0 ≤ x := by linarith
    have hR : 0 ≤ x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 := by
      have : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0 _
      positivity
    have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hR) hL

end LeanLab.BHP1997.DecompC165d
