/-
P0069 Baker Harman Pintz 1997, page 49, proof of Lemma 34, conclusion 5.1 of page 43. Burst
burst-20261122, session S113, step l34s51-s113, on the leaves `l34s_f_lemma30` and
`l34s_g_big_lemma33` of `Prep1122Lemma34Split51`, cut as session S50 cut the parallel 5.2
leaves in `Prep1122UpD52Lemma30Blocks` and `Prep1122UpD52BigBlocks`.

1. `l34s_f_lemma30_s113` has the exact statement of `l34s_f_lemma30` and is PROVED from the one
   LEAF `l34s51_leaf_lemma30_block`, Lemma 30 of page 44 for one dyadic block n ~ N in the
   range 5.5, by the dyadic cut `upD52L30_dyadic` with the coefficients cut above
   Y^(1/2 + theta2/4 - 2 eps), `upD52L30_cut_31`, the block count `upD52L30_J_le`, the range
   check `upD52L30_block_range` and the PROVED rule `s113_combine_blocks`.
2. `l34s_g_big_lemma33_s113` has the exact statement of `l34s_g_big_lemma33` and is PROVED from
   the one LEAF `l34s51_leaf_lemma33_block`, the block h_m with p1 ~ P, by the dyadic split
   `upBB_dyadic_split` of the p1 sum, the block count `upBB_J_le` and `s113_combine_blocks`.
No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.S113L34Combine51
import LeanLab.BHP1997.Prep1122UpD52Lemma30Blocks
import LeanLab.BHP1997.Prep1122UpD52BigBlocks

namespace LeanLab.BHP1997.S113L34Blocks51
open Classical Complex Decomp132 DecompC165b LeanLab.BHP1997.DecompC165d
open LeanLab.BHP1997.S113L34Combine51

/-- LEAF: P0069 page 44, Lemma 30, the conclusion 5.1 of page 43 with the page 19 set E and its
size, for one dyadic block: b_m = sum over n ~ N, nl = m of a_n psi(l, w), with (a_n)
satisfying 3.1, w = exp(log^(9/10) x) of page 25, and N at most Y^(1/2 + theta2/4 - eps), the
range 5.5. Here n ~ N is read as N <= n < 2N, the constant is uniform in N as the paper uses it
in Lemma 34, and the set E may depend on N, which only weakens the statement. CONDITIONAL on the
cited Theorem 4 and Lemma 9. Class HARD. -/
theorem l34s51_leaf_lemma30_block (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℕ → ℝ)
    (hc : ∀ x N k, c x N k = ∑ n ∈ k.divisors.filter (fun n : ℕ => N ≤ n ∧ n < 2 * N),
        a x n * upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) :
    ∃ E : ℝ → ℝ → ℕ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ N : ℕ, 1 ≤ N →
        (N : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε) →
        ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
        ((E A x N q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x N q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (c x N m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- P0069 page 49, proof of Lemma 34, "Here f_m satisfies (5.1) and (5.2) by Lemma 30", the
part for 5.1. The exact statement of the leaf `l34s_f_lemma30` of `Prep1122Lemma34Split51`,
twin for the lab gate. PROVED from the one-block LEAF `l34s51_leaf_lemma30_block`. CONDITIONAL
on the cited Theorem 4 and Lemma 9. -/
theorem l34s_f_lemma30_s113 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                ((∑ n ∈ m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
                  a x n * upperRough (m / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  have ha' := upD52L30_cut_31 a (fun x =>
    (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)) ha
  obtain ⟨E, hE⟩ := l34s51_leaf_lemma30_block h4 h9 hε hε8 _ ha'
    (fun x N k => ∑ n ∈ k.divisors.filter (fun n : ℕ => N ≤ n ∧ n < 2 * N),
      (fun x (n : ℕ) => if (n : ℝ) ≤
          (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)
        then a x n else 0) x n *
        upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
    (fun _ _ _ => rfl)
  refine s113_combine_blocks (fun x k => ∑ n ∈ k.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
      a x n * upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
    (fun x j k => ∑ n ∈ k.divisors.filter (fun n : ℕ => 2 ^ j ≤ n ∧ n < 2 * 2 ^ j),
      (fun x (n : ℕ) => if (n : ℝ) ≤
          (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)
        then a x n else 0) x n *
        upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
    (fun x => Nat.log 2 ⌊(x ^ (11 / 20 + ε)) ^
        (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)⌋₊ + 1) ?_ ?_
  · refine ⟨Real.exp 4, fun x hx => ⟨upD52L30_J_le hε hε8 x hx, fun k _ => ?_⟩⟩
    exact upD52L30_dyadic _ (a x) (fun n => upperRough (k / n)
      (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) k
  · refine ⟨fun A x j q => E A x (2 ^ j) q, fun A hA A' hA' => ?_⟩
    obtain ⟨C, hC⟩ := hE A hA A' hA'
    refine ⟨max C 1, fun x hx j hj q hq1 hqQ => ?_⟩
    obtain ⟨h1, h2⟩ := upD52L30_block_range hε hε8 x (le_trans (le_max_right _ _) hx) j hj
    obtain ⟨hc1, hc2⟩ := hC x (le_trans (le_max_left _ _) hx) (2 ^ j) h1 h2 q hq1 hqQ
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hY0 : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
    have hRL : 0 ≤ (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
        Real.log x ^ (-A') :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
    have hKL : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Real.log_nonneg hx1) _)
    refine ⟨le_trans hc1 ?_, le_trans hc2 ?_⟩
    · rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hKL
    · rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hRL

/-- LEAF: P0069 pages 49 and 50, proof of Lemma 34, the block h_m of g_m with p1 ~ P, here
P <= p1 < 2P, P a power of 2 at most Y^c1, restricted to Y^eps <= p1 < Y^c1: 5.1 of page 43 with
the page 19 set E and its size follows from Lemma 33 case 5.13 on page 48, with N(s, chi) the
sum over p1 ~ P of chi(p1) p1^(-s) satisfying 3.2 by Lemma 5. The constant is uniform in P and
the set E may depend on P. Stated for every P with 1 <= P <= Y^c1. CONDITIONAL on the cited
Theorem 4 and Lemma 9. Class HARD. The lowest nonempty block may straddle Y^eps, as in the
paper's own P >= Y^eps; the paper treats h_m as a product although psi(n1, p1) couples n1
to p1. -/
theorem l34s51_leaf_lemma33_block (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℕ → ℝ)
    (hc : ∀ x P k, c x P k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            ((x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
              (P ≤ p ∧ p < 2 * P)),
          upperRough (k / n / p : ℕ) (p : ℝ)) :
    ∃ E : ℝ → ℝ → ℕ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ P : ℕ, 1 ≤ P →
        (P : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε →
        ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
        ((E A x P q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x P q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (c x P m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- P0069 pages 49 and 50, proof of Lemma 34, the part of g_m with P >= Y^eps, for 5.1. The
exact statement of the leaf `l34s_g_big_lemma33` of `Prep1122Lemma34Split51`, twin for the lab
gate. PROVED from the LEAF `l34s51_leaf_lemma33_block`. CONDITIONAL on the cited Theorem 4 and
Lemma 9. -/
theorem l34s_g_big_lemma33_s113 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                ((∑ n ∈ m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
                  a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
                      (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε),
                    upperRough (m / n / p : ℕ) (p : ℝ) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  obtain ⟨cb, hcb⟩ : ∃ cb : ℝ → ℕ → ℕ → ℝ, ∀ x P k, cb x P k = ∑ n ∈ k.divisors.filter
        (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            ((x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
              (P ≤ p ∧ p < 2 * P)),
          upperRough (k / n / p : ℕ) (p : ℝ) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨E, hE⟩ := l34s51_leaf_lemma33_block h4 h9 hε hε8 a ha cb hcb
  refine s113_combine_blocks (fun x k => ∑ n ∈ k.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
      a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
          (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε),
        upperRough (k / n / p : ℕ) (p : ℝ))
    (fun x j k => cb x (2 ^ j) k)
    (fun x => Nat.log 2 (Nat.floor ((x ^ (11 / 20 + ε)) ^ upperC1 ε)) + 1) ?_ ?_
  · refine ⟨Real.exp 2, fun x hx => ⟨upBB_J_le hε hε8 x hx, fun k _ => ?_⟩⟩
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
    exact Nat.le_floor hp.2.2.le
  · refine ⟨fun A x j q => E A x (2 ^ j) q, fun A hA A' hA' => ?_⟩
    obtain ⟨C, hC⟩ := hE A hA A' hA'
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
    obtain ⟨hc1', hc2'⟩ := hC x hCx (2 ^ j) Nat.one_le_two_pow hPle q hq1 hqQ
    have hY0 : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
    have hRL : 0 ≤ (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
        Real.log x ^ (-A') :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
    have hKL : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Real.log_nonneg hx1) _)
    refine ⟨le_trans hc1' ?_, le_trans hc2' ?_⟩
    · rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hKL
    · rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hRL

end LeanLab.BHP1997.S113L34Blocks51
