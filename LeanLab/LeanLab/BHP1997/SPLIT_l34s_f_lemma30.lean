/-
Burst burst-20261122, session S129, wave 13, second pass. P0069 Baker Harman Pintz 1997, proof of
Lemma 34 on page 49, "Here f_m satisfies (5.1) and (5.2) by Lemma 30".
`l34s_f_lemma30_split` proves exactly the statement of the LEAF `l34s_f_lemma30` of
Prep1122Lemma34Split51 from the cited LEAF `leaf_l34s_lemma30_gen` of SPLIT_l34s_gs_lemma30, Lemma 30
of page 44 with 5.5, applied to a_n cut at n <= Y^(1/2 + theta2/4 - 2 eps). For x >= 1 this cut
lies inside 5.5, so the two coefficients agree, and `l34s_add` with the PROVED `l34s_zero51`, 5.1
for the zero coefficient, transfers 5.1.
No new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_l34s_gs_lemma30

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- P0069 page 43: 5.1 with the page 19 set E and its size holds for the zero coefficient, with E
empty. PROVED. -/
theorem l34s_zero51 (ε : ℝ) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (((fun (_ : ℝ) (_ : ℕ) => (0 : ℝ)) x m : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  refine ⟨fun _ _ _ => ∅, fun A _ A' _ => ⟨3, fun x hx q _ _ => ⟨?_, ?_⟩⟩⟩
  · have hl : 0 < Real.log x := Real.log_pos (by linarith)
    simp only [Finset.card_empty, Nat.cast_zero]
    have := Real.rpow_pos_of_pos hl (-2 * A)
    have := Real.rpow_nonneg (Nat.cast_nonneg q) (1 / 2 : ℝ)
    positivity
  · have hl : 0 < Real.log x := Real.log_pos (by linarith)
    have h1 := Real.rpow_pos_of_pos hl (-A')
    have h2 := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < x) (11 / 20 + ε)
    simp only [Complex.ofReal_zero, zero_mul, zero_div, Finset.sum_const_zero, norm_zero]
    norm_num
    positivity

/-- P0069 page 49, proof of Lemma 34, f_m by Lemma 30. Exactly the statement of `l34s_f_lemma30`
of Prep1122Lemma34Split51. PROVED from `leaf_l34s_lemma30_gen`, `l34s_add` and `l34s_zero51`.
CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem l34s_f_lemma30_split (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
  obtain ⟨C, hC⟩ := ha
  have key := leaf_l34s_lemma30_gen h4 h9 hε hε8
    (fun x n => if (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) ∧
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε)
      then a x n else 0) (B := B)
    ⟨|C|, fun x n => by
      split_ifs
      · exact (hC x n).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
          (Real.rpow_nonneg (Nat.cast_nonneg _) B))
      · rw [abs_zero]; exact mul_nonneg (abs_nonneg C) (Real.rpow_nonneg (Nat.cast_nonneg _) B)⟩
    (fun x _ n hn => by
      rw [ite_eq_right_iff]; intro h; exact absurd h.2 (not_le.mpr hn))
  refine l34s_add _ _ _ ⟨1, fun x hx m _ => ?_⟩ key (l34s_zero51 ε)
  have hY : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx (by linarith)
  have hc : (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) ≤
      (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε) :=
    Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  simp only [add_zero]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h : (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)
  · rw [if_pos h, if_pos ⟨h, h.trans hc⟩]
  · rw [if_neg h, if_neg (fun h' => h h'.1), zero_mul]

end LeanLab.BHP1997.DecompC165d
