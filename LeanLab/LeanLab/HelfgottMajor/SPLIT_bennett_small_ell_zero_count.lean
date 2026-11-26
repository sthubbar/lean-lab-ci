import LeanLab.HelfgottMajor.SPLIT_bennett_two_sided_zero_count

/-!
# Split of `bennett_small_ell_zero_count`

Bennett, Martin, O'Bryant and Rechnitzer, Math. Comp. 90 2021, Lemma 6.1 (c), page 1478, states
the computed range `1.567 ≤ ℓ ≤ 6`, `1 < q < 935`, `T ≥ 0` with the sharper error
`ℓ / log (2 + ℓ)`. This file makes that display the LEAF and proves that it implies the Theorem
1.1 error `0.22737 ℓ + 2 log (1 + ℓ) - 0.5` on `1.567 < ℓ ≤ 6`, by five intervals of `ℓ` and the
elementary bound `log y ≥ k log 2 + 1 - 2^k / y`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

/-- `log y ≥ k log 2 + 1 - 2^k / y` for `y > 0`, from `log x ≤ x - 1` at `x = 2^k / y`. No
input. -/
lemma log_ge_pow_two_bound (k : ℕ) {y : ℝ} (hy : 0 < y) :
    (k : ℝ) * Real.log 2 + 1 - 2 ^ k / y ≤ Real.log y := by
  have hpos : 0 < (2 : ℝ) ^ k / y := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (by positivity) hy.ne', Real.log_pow] at h
  linarith

/-- On one interval `lo ≤ ℓ ≤ hi`, the comparison follows from a lower bound `a` for
`log (2 + ℓ)`, a lower bound `c` for `log (1 + ℓ)` and the numerical check
`hi ≤ a (0.22737 lo + 2 c - 0.5)`. No input. -/
lemma ell_over_log_le_of_bounds {ℓ lo hi a c : ℝ} (hlo : lo ≤ ℓ) (hhi : ℓ ≤ hi) (ha : 0 < a)
    (hA : a ≤ Real.log (2 + ℓ)) (hC : c ≤ Real.log (1 + ℓ))
    (hnum : hi ≤ a * (0.22737 * lo + 2 * c - 0.5)) (hpos : 0 ≤ 0.22737 * lo + 2 * c - 0.5) :
    ℓ / Real.log (2 + ℓ) ≤ 0.22737 * ℓ + 2 * Real.log (1 + ℓ) - 0.5 := by
  have hL : 0 < Real.log (2 + ℓ) := lt_of_lt_of_le ha hA
  rw [div_le_iff₀ hL]
  have hR : 0.22737 * lo + 2 * c - 0.5 ≤ 0.22737 * ℓ + 2 * Real.log (1 + ℓ) - 0.5 := by
    linarith
  have h1 : a * (0.22737 * lo + 2 * c - 0.5) ≤
      Real.log (2 + ℓ) * (0.22737 * ℓ + 2 * Real.log (1 + ℓ) - 0.5) :=
    mul_le_mul hA hR hpos hL.le
  linarith

/-- The Lemma 6.1 (c) error is at most the Theorem 1.1 error on `1.567 ≤ ℓ ≤ 6`. Proved by five
intervals, no input. -/
lemma ell_over_log_le_bennett_error {ℓ : ℝ} (h1 : 1.567 ≤ ℓ) (h6 : ℓ ≤ 6) :
    ℓ / Real.log (2 + ℓ) ≤ 0.22737 * ℓ + 2 * Real.log (1 + ℓ) - 0.5 := by
  have hl2 := Real.log_two_gt_d9
  have mono : ∀ {x y : ℝ}, 0 < x → x ≤ y → Real.log x ≤ Real.log y :=
    fun hx hxy => Real.log_le_log hx hxy
  rcases le_or_gt ℓ 2 with hA | hA
  · -- `1.567 ≤ ℓ ≤ 2`
    have e1 := log_ge_pow_two_bound 2 (show (0 : ℝ) < 3.567 by norm_num)
    have e2 := log_ge_pow_two_bound 1 (show (0 : ℝ) < 2.567 by norm_num)
    have m1 := mono (show (0 : ℝ) < 3.567 by norm_num) (show (3.567 : ℝ) ≤ 2 + ℓ by linarith)
    have m2 := mono (show (0 : ℝ) < 2.567 by norm_num) (show (2.567 : ℝ) ≤ 1 + ℓ by linarith)
    norm_num at e1 e2
    exact ell_over_log_le_of_bounds h1 hA (a := 1.25) (c := 0.91) (by norm_num)
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt ℓ 2.5 with hB | hB
  · -- `2 ≤ ℓ ≤ 2.5`
    have e1 := log_ge_pow_two_bound 2 (show (0 : ℝ) < 4 by norm_num)
    have e2 := log_ge_pow_two_bound 2 (show (0 : ℝ) < 3 by norm_num)
    have m1 := mono (show (0 : ℝ) < 4 by norm_num) (show (4 : ℝ) ≤ 2 + ℓ by linarith)
    have m2 := mono (show (0 : ℝ) < 3 by norm_num) (show (3 : ℝ) ≤ 1 + ℓ by linarith)
    norm_num at e1 e2
    exact ell_over_log_le_of_bounds hA.le hB (lo := 2) (a := 1.38) (c := 1.05) (by norm_num)
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt ℓ 3 with hC | hC
  · -- `2.5 ≤ ℓ ≤ 3`
    have e1 := log_ge_pow_two_bound 2 (show (0 : ℝ) < 4.5 by norm_num)
    have e2 := log_ge_pow_two_bound 2 (show (0 : ℝ) < 3.5 by norm_num)
    have m1 := mono (show (0 : ℝ) < 4.5 by norm_num) (show (4.5 : ℝ) ≤ 2 + ℓ by linarith)
    have m2 := mono (show (0 : ℝ) < 3.5 by norm_num) (show (3.5 : ℝ) ≤ 1 + ℓ by linarith)
    norm_num at e1 e2
    exact ell_over_log_le_of_bounds hB.le hC (lo := 2.5) (a := 1.49) (c := 1.24) (by norm_num)
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt ℓ 4.5 with hD | hD
  · -- `3 ≤ ℓ ≤ 4.5`
    have e1 := log_ge_pow_two_bound 2 (show (0 : ℝ) < 5 by norm_num)
    have e2 := log_ge_pow_two_bound 2 (show (0 : ℝ) < 4 by norm_num)
    have m1 := mono (show (0 : ℝ) < 5 by norm_num) (show (5 : ℝ) ≤ 2 + ℓ by linarith)
    have m2 := mono (show (0 : ℝ) < 4 by norm_num) (show (4 : ℝ) ≤ 1 + ℓ by linarith)
    norm_num at e1 e2
    exact ell_over_log_le_of_bounds hC.le hD (lo := 3) (a := 1.58) (c := 1.38) (by norm_num)
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  · -- `4.5 ≤ ℓ ≤ 6`
    have e1 := log_ge_pow_two_bound 3 (show (0 : ℝ) < 6.5 by norm_num)
    have e2 := log_ge_pow_two_bound 2 (show (0 : ℝ) < 5.5 by norm_num)
    have m1 := mono (show (0 : ℝ) < 6.5 by norm_num) (show (6.5 : ℝ) ≤ 2 + ℓ by linarith)
    have m2 := mono (show (0 : ℝ) < 5.5 by norm_num) (show (5.5 : ℝ) ≤ 1 + ℓ by linarith)
    norm_num at e1 e2
    exact ell_over_log_le_of_bounds hD.le h6 (lo := 4.5) (a := 1.84) (c := 1.65) (by norm_num)
      (by linarith) (by linarith) (by norm_num) (by norm_num)

variable {q : ℕ} [NeZero q]

/-- LEAF: Bennett et al. 2021, Lemma 6.1 (c), page 1478, section 6.3. HARD, CITED, a rigorous
computation in Arb of all zeros of the primitive `L`-functions with `1 < q < 935` and `ℓ ≤ 6`: for
`χ` primitive of conductor `1 < q < 935`, `T ≥ 0` and `1.567 ≤ ℓ ≤ 6`, with
`ℓ = log (q (T + 2)/(2π))`, `|N(T, χ) - (T/π log (qT/(2πe)) - χ(-1)/4)| ≤ ℓ / log (2 + ℓ)`. Here
`N(T, χ)` is the multiplicity sum over the lab set `stripZeros χ T`. -/
theorem bennett_lemma_6_1_c (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1 < q) (hq935 : q < 935) {T : ℝ} (hT : 0 ≤ T)
    (hℓ1 : 1.567 ≤ Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)))
    (hℓ6 : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 6) :
    |∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) -
        (T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) -
          (χ (-1)).re / 4)| ≤
      Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) /
        Real.log (2 + Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi))) := by
  sorry

/-- Split of `bennett_small_ell_zero_count`, same statement, from the Lemma 6.1 (c) leaf and the
proved comparison of the two error terms. -/
theorem bennett_small_ell_zero_count_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1 < q) (hq935 : q < 935) {T : ℝ} (hT : 5 / 7 ≤ T)
    (hℓ1 : 1.567 < Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)))
    (hℓ6 : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 6) :
    |∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) -
        (T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) -
          (χ (-1)).re / 4)| ≤
      0.22737 * Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) +
        2 * Real.log (1 + Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi))) - 0.5 :=
  (bennett_lemma_6_1_c χ hχ hq hq935 (by linarith) hℓ1.le hℓ6).trans
    (ell_over_log_le_bennett_error hℓ1.le hℓ6)

end LeanLab.HelfgottMajor.ZeroCount1623
