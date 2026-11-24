/-
Burst burst-20261122, session S83, OMOS FEED. P0069 Baker Harman Pintz 1997, proof of Lemma 34 on
page 50, the part of g_m with w <= p1 < Y^eps.
This file splits `DecompC165d.l34s_g_small_iterate` of Prep1122Lemma34Split51 along the first step
of the iteration on page 50, read from the page images of papers/P0069-original.pdf: Buchstab's
identity psi(n1, p1) = psi(n1, w) - sum over w <= p2 < p1, p2 | n1, of psi(n1/p2, p2) gives
g_small = u - v_big - v_small, where
* u is the sum over n p1 n1 = m of a_n psi(n1, w): since n <= Y^(1/2 + theta2/4 - 2 eps) and
  p1 < Y^eps, here n p1 < Y^(1/2 + theta2/4 - eps), which is 5.5, so Lemma 30 applies as it did to f_m;
* v_big is the sum over n p1 p2 n2 = m with w <= p2 < p1 and p1 p2 >= Y^eps of a_n psi(n2, p2):
  here Y^eps <= p1 p2 <= Y^(2 eps), and Lemma 5 for the polynomial of p1 p2 and Lemma 33 give 5.1;
* v_small is the same sum with p1 p2 < Y^eps, which "need only decompose again", the rest of the
  iteration that ends after O(L^(1/10)) steps.

LEAFs, all HARD and CONDITIONAL on the cited Theorem 4 and Lemma 9:
* `leaf_l34s_gs_lemma30`, u by Lemma 30;
* `leaf_l34s_gs_lemma33`, v_big by Lemma 5 and Lemma 33;
* `leaf_l34s_gs_iterate`, v_small by the further iteration.
PROVED here: `l34s_gs_inner`, `l34s_gs_identity`, the Buchstab step with the p1 p2 range split at
Y^eps, and `l34s_g_small_iterate_split` with exactly the statement of `l34s_g_small_iterate`, from
the three LEAFs and the PROVED `l34s_add` and `l34s_neg`.
No new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122Lemma34Split51

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- LEAF: P0069 page 50, proof of Lemma 34, first step of the iteration for w <= P <= Y^eps, the
first Buchstab term n p1 psi(n1, w): "a further decomposition is possible" since
n p1 < Y^(1/2 + theta2/4 - eps), which is 5.5, so "(5.1) and (5.2) by Lemma 30" as for f_m on
page 49, for 5.1 on page 43 with the page 19 set E and its size from page 3. Here n <=
Y^(1/2 + theta2/4 - 2 eps), w <= p1 < Y^eps, w = exp(log^(9/10) x) from page 25. Lemma 30 is on
page 44. CONDITIONAL on the cited Theorem 4 and Lemma 9. HARD. -/
theorem leaf_l34s_gs_lemma30 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                    upperRough (m / n / p : ℕ) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- LEAF: P0069 page 50, proof of Lemma 34, after the first step of the iteration, the terms
n p1 p2 n2 with w <= p2 < p1 < Y^eps and p1 p2 >= Y^eps, which need no further decomposition:
with N(s, chi) the polynomial of p1 p2, Lemma 5 gives 3.2, and since Y^eps <= p1 p2 <= Y^(2 eps)
Lemma 33 gives 5.1 and 5.2, as in case 5.13 on page 48, for 5.1 on page 43 with the page 19 set E
and its size from page 3. CONDITIONAL on the cited Theorem 4 and Lemma 9. HARD. -/
theorem leaf_l34s_gs_lemma33 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                    ∑ p2 ∈ (m / n / p).primeFactors.filter (fun p2 : ℕ =>
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ) ∧
                        (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) * (p2 : ℝ)),
                      upperRough (m / n / p / p2 : ℕ) (p2 : ℝ) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- LEAF: P0069 page 50, proof of Lemma 34, the rest of the iteration: the terms n p1 p2 n2 with
w <= p2 < p1 and p1 p2 < Y^eps "need only decompose again if p1 ... pj < Y^eps ... The process
terminates after O(L^(1/10)) steps", in the same fashion as case ii of Lemma 13 on page 26, for
5.1 on page 43 with the page 19 set E and its size from page 3. CONDITIONAL on the cited Theorem 4
and Lemma 9. HARD. -/
theorem leaf_l34s_gs_iterate (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                    ∑ p2 ∈ (m / n / p).primeFactors.filter (fun p2 : ℕ =>
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ) ∧
                        (p : ℝ) * (p2 : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                      upperRough (m / n / p / p2 : ℕ) (p2 : ℝ) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- P0069 page 50, the Buchstab step of the iteration for one `l = m / n`: for `w <= p1 < Z`,
`psi(l/p1, p1) = psi(l/p1, w) - sum over w <= p2 < p1 of psi(l/p1/p2, p2)`, with the `p2` sum split
at `p1 p2 = Z`. PROVED from `upper_rough_buchstab_step`. -/
theorem l34s_gs_inner (l : ℕ) (w Z : ℝ) :
    (∑ p ∈ l.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < Z),
        upperRough (l / p : ℕ) (p : ℝ)) =
      (∑ p ∈ l.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < Z),
        upperRough (l / p : ℕ) w) +
      -((∑ p ∈ l.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < Z),
          ∑ p2 ∈ (l / p).primeFactors.filter (fun p2 : ℕ =>
            w ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ) ∧ Z ≤ (p : ℝ) * (p2 : ℝ)),
            upperRough (l / p / p2 : ℕ) (p2 : ℝ)) +
        (∑ p ∈ l.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < Z),
          ∑ p2 ∈ (l / p).primeFactors.filter (fun p2 : ℕ =>
            w ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ) ∧ (p : ℝ) * (p2 : ℝ) < Z),
            upperRough (l / p / p2 : ℕ) (p2 : ℝ))) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hwp : w ≤ (p : ℝ) := (Finset.mem_filter.mp hp).2.1
  rw [upper_rough_buchstab_step (l / p) hwp]
  have hs : (∑ p2 ∈ (l / p).primeFactors.filter (fun p2 : ℕ => w ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ)),
        upperRough (l / p / p2 : ℕ) (p2 : ℝ)) =
      (∑ p2 ∈ (l / p).primeFactors.filter (fun p2 : ℕ =>
          w ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ) ∧ Z ≤ (p : ℝ) * (p2 : ℝ)),
        upperRough (l / p / p2 : ℕ) (p2 : ℝ)) +
      (∑ p2 ∈ (l / p).primeFactors.filter (fun p2 : ℕ =>
          w ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ) ∧ (p : ℝ) * (p2 : ℝ) < Z),
        upperRough (l / p / p2 : ℕ) (p2 : ℝ)) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p2 _ => ?_)
    by_cases h1 : w ≤ (p2 : ℝ) <;> by_cases h2 : (p2 : ℝ) < (p : ℝ) <;>
      rcases le_or_gt Z ((p : ℝ) * (p2 : ℝ)) with h3 | h3 <;>
      first
        | simp [h1, h2, h3, not_lt.mpr h3]
        | simp [h1, h2, h3, not_le.mpr h3]
  rw [hs]; ring

/-- P0069 page 50, the identity g_small = u - v_big - v_small for every x and m. PROVED from
`l34s_gs_inner`. -/
theorem l34s_gs_identity (ε : ℝ) (a : ℝ → ℕ → ℝ) (x : ℝ) (m : ℕ) :
    (∑ n ∈ m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
                  a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                    upperRough (m / n / p : ℕ) (p : ℝ) : ℝ) =
      (∑ n ∈ m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
                  a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                    upperRough (m / n / p : ℕ) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) : ℝ) +
      -((∑ n ∈ m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
                  a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                    ∑ p2 ∈ (m / n / p).primeFactors.filter (fun p2 : ℕ =>
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ) ∧
                        (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) * (p2 : ℝ)),
                      upperRough (m / n / p / p2 : ℕ) (p2 : ℝ) : ℝ) +
        (∑ n ∈ m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
                  a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                    ∑ p2 ∈ (m / n / p).primeFactors.filter (fun p2 : ℕ =>
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ) ∧
                        (p : ℝ) * (p2 : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                      upperRough (m / n / p / p2 : ℕ) (p2 : ℝ) : ℝ)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [l34s_gs_inner (m / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) ((x ^ (11 / 20 + ε)) ^ ε)]
  ring

/-- P0069 page 50, proof of Lemma 34, the part of g_m with w <= p1 < Y^eps. Exactly the statement
of `l34s_g_small_iterate`. PROVED from the three LEAFs above by the Buchstab step
`l34s_gs_identity`, `l34s_add` and `l34s_neg`. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem l34s_g_small_iterate_split (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                    upperRough (m / n / p : ℕ) (p : ℝ) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  refine l34s_add _ _ _ ⟨0, fun x _ m _ => l34s_gs_identity ε a x m⟩
    (leaf_l34s_gs_lemma30 h4 h9 hε hε8 a ha)
    (l34s_neg _ (l34s_add _ _ _ ⟨0, fun _ _ _ _ => rfl⟩
      (leaf_l34s_gs_lemma33 h4 h9 hε hε8 a ha) (leaf_l34s_gs_iterate h4 h9 hε hε8 a ha)))

end LeanLab.BHP1997.DecompC165d
