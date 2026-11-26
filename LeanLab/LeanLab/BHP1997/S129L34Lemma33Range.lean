/-
P0069 Baker Harman Pintz 1997, pages 49 and 50, proof of Lemma 34, the block h_m of g_m with
p1 ~ P. Burst burst-20261122, session S129, step l34s51-s113-p2, on the LEAF
`l34s51_leaf_lemma33_block` of S113L34Blocks51.

`l34s51_leaf_lemma33_block_split` has the exact statement of that LEAF and is PROVED from the
one LEAF `l34s51_leaf_lemma33_block_live`, the same statement for the blocks that meet the
range Y^eps <= p1 of page 49, that is Y^eps < 2P. For 2P <= Y^eps the coefficient c of the block
is zero, since every p1 in it is below Y^eps, so 5.1 holds with E empty.
No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.S113L34Blocks51

namespace LeanLab.BHP1997.S129L34Lemma33Range
open Classical Complex Decomp132 DecompC165b LeanLab.BHP1997.DecompC165d

/-- LEAF: P0069 pages 49 and 50, proof of Lemma 34, the block h_m of g_m with p1 ~ P that meets
the range p1 >= Y^eps of page 49, so Y^eps < 2P: 5.1 of page 43 with the page 19 set E and its
size follows from Lemma 33 case 5.13 on page 48, with N(s, chi) the sum over p1 ~ P of
chi(p1) p1^(-s) satisfying 3.2 by Lemma 5. Constant uniform in P, E may depend on P.
CONDITIONAL on the cited Theorem 4 and Lemma 9. Class HARD. -/
theorem l34s51_leaf_lemma33_block_live (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
        (x ^ (11 / 20 + ε)) ^ ε < 2 * (P : ℝ) →
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

/-- P0069 pages 49 and 50, proof of Lemma 34, the block h_m with p1 ~ P. The exact statement of
the LEAF `l34s51_leaf_lemma33_block` of S113L34Blocks51. PROVED from the LEAF
`l34s51_leaf_lemma33_block_live`; blocks with 2P <= Y^eps are empty. CONDITIONAL on the cited
Theorem 4 and Lemma 9. -/
theorem l34s51_leaf_lemma33_block_split (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
  obtain ⟨E, hE⟩ := l34s51_leaf_lemma33_block_live h4 h9 hε hε8 a ha c hc
  refine ⟨fun A x P q => if (x ^ (11 / 20 + ε)) ^ ε < 2 * (P : ℝ) then E A x P q else ∅,
    fun A hA A' hA' => ?_⟩
  obtain ⟨C, hC⟩ := hE A hA A' hA'
  refine ⟨max C 1, fun x hx P hP1 hPc q hq1 hqQ => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  have hRL : 0 ≤ (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
      Real.log x ^ (-A') :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have hKL : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have hC0 : 0 ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
  by_cases hbig : (x ^ (11 / 20 + ε)) ^ ε < 2 * (P : ℝ)
  · simp only [if_pos hbig]
    obtain ⟨hc1, hc2⟩ := hC x (le_trans (le_max_left _ _) hx) P hP1 hPc hbig q hq1 hqQ
    refine ⟨le_trans hc1 ?_, le_trans hc2 ?_⟩
    · rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hKL
    · rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hRL
  · simp only [if_neg hbig]
    have hzero : ∀ m, c x P m = 0 := by
      intro m
      rw [hc]
      refine Finset.sum_eq_zero (fun n _ => ?_)
      rw [Finset.sum_eq_zero (fun p hp => ?_), mul_zero]
      exfalso
      rw [Finset.mem_filter] at hp
      obtain ⟨_, ⟨hlo, _⟩, _, hhi⟩ := hp
      have : (p : ℝ) < 2 * (P : ℝ) := by exact_mod_cast hhi
      exact hbig (lt_of_le_of_lt hlo this)
    refine ⟨?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      rw [mul_assoc]; exact mul_nonneg hC0 hKL
    · simp only [hzero, Complex.ofReal_zero, zero_mul, zero_div, Finset.sum_const_zero,
        norm_zero]
      norm_num
      rw [mul_assoc]; exact mul_nonneg hC0 hRL

end LeanLab.BHP1997.S129L34Lemma33Range

#print axioms LeanLab.BHP1997.S129L34Lemma33Range.l34s51_leaf_lemma33_block_split
