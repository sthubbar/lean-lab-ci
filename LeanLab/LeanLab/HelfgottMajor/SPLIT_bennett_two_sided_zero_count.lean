import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_short_conductor_le_height

/-!
# Split of `bennett_two_sided_zero_count`

Bennett, Martin, O'Bryant and Rechnitzer, Counting zeros of Dirichlet L-functions, Math. Comp. 90
2021, prove Theorem 1.1, page 1456, by cutting the range of `ℓ = log (q (T + 2) / (2π))` into
three pieces, section 6, pages 1475 to 1479:

* section 6.1, `ℓ ≥ 27.02`, the analytic bound with the parameters `η, c, r` of page 1475;
* section 6.2, `5.98 ≤ ℓ ≤ 28`, the same argument with the other `c, r` of page 1477;
* section 6.3, `ℓ ≤ 6`, the rigorous zero computation for `1 < q < 935`, Lemma 6.1 (b) and (c),
  page 1478, and the sentence of page 1456 that the computed zeros verify Theorem 1.1 there.

Each piece is a LEAF here. The assembly is proved: for `ℓ ≤ 6` and `T ≥ 5/7` the conductor is at
most `2π e^6 · 7/19 < 934`, so the computation range `q < 935` is automatic, as the paper notes.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF: Bennett et al. 2021, Lemma 6.1 (b), page 1478, section 6.3. HARD, CITED, a rigorous
computation of the low zeros of the 40 primitive characters with `q ≤ 15`: for `χ` primitive of
conductor `1 < q < 935` and `T ≥ 0`, if `ℓ = log (q (T + 2) / (2π)) ≤ 1.567` then
`N(T, χ) = 0`. Here `N(T, χ)` is the multiplicity sum over the lab set `stripZeros χ T`. -/
theorem bennett_lemma_6_1_b (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1 < q) (hq935 : q < 935) {T : ℝ} (hT : 0 ≤ T)
    (hℓ : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 1.567) :
    ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) = 0 := by
  sorry

/-- LEAF: Bennett et al. 2021, section 6.3 with Lemma 6.1 (c), page 1478, and page 1456, line
`we computed all 806,544 zeros ... with ℓ ≤ 6 and 1 < q < 935, to sufficient precision to verify
the bounds in Theorem 1.1 in this range`. HARD, CITED, a rigorous zero computation in Arb: for
`χ` primitive of conductor `1 < q < 935`, `T ≥ 5/7` and `1.567 < ℓ ≤ 6`, the Theorem 1.1 bound
holds. Lemma 6.1 (c) states the sharper error `ℓ / log (2 + ℓ)`; the Theorem 1.1 form is the one
the paper says the computation verifies. -/
theorem bennett_small_ell_zero_count (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1 < q) (hq935 : q < 935) {T : ℝ} (hT : 5 / 7 ≤ T)
    (hℓ1 : 1.567 < Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)))
    (hℓ6 : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 6) :
    |∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) -
        (T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) -
          (χ (-1)).re / 4)| ≤
      0.22737 * Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) +
        2 * Real.log (1 + Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi))) - 0.5 := by
  sorry

/-- LEAF: Bennett et al. 2021, section 6.2, Middle values of `ℓ`, pages 1477 and 1478. HARD,
CITED: with `c = 1 + 505/(111 ℓ + 430)` and `r = 149/140 + 747/(36 ℓ + 283)`, the argument of
sections 2 to 5 gives the Theorem 1.1 bound for `χ` primitive of conductor `q > 1`, `T ≥ 5/7`
and `5.98 ≤ ℓ ≤ 28`. -/
theorem bennett_middle_ell_zero_count (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1 < q) {T : ℝ} (hT : 5 / 7 ≤ T)
    (hℓ1 : 5.98 ≤ Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)))
    (hℓ2 : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 28) :
    |∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) -
        (T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) -
          (χ (-1)).re / 4)| ≤
      0.22737 * Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) +
        2 * Real.log (1 + Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi))) - 0.5 := by
  sorry

/-- LEAF: Bennett et al. 2021, section 6.1, Large values of `ℓ`, pages 1475 to 1477, ending
`This establishes Theorem 1.1 for ℓ ≥ 27.02`. HARD, CITED: with `η = 18/(10 ℓ + 9)` and the `c, r`
of page 1475, inequality 2.6 with Propositions 5.2 and 5.4 gives the Theorem 1.1 bound for `χ`
primitive of conductor `q > 1`, `T ≥ 5/7` and `ℓ ≥ 27.02`. -/
theorem bennett_large_ell_zero_count (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1 < q) {T : ℝ} (hT : 5 / 7 ≤ T)
    (hℓ : 27.02 ≤ Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi))) :
    |∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) -
        (T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) -
          (χ (-1)).re / 4)| ≤
      0.22737 * Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) +
        2 * Real.log (1 + Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi))) - 0.5 := by
  sorry

/-- For `ℓ ≤ 6` and `T ≥ 5/7` the conductor is below `935`: `q ≤ 2π e^6 · 7/19 < 934`. This is
the remark that makes the computation range of section 6.3 cover all of `ℓ ≤ 6`. Proved. -/
lemma conductor_lt_935_of_ell_le_six {T : ℝ} (hT : 5 / 7 ≤ T)
    (hℓ6 : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 6) : q < 935 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpi0 := Real.pi_pos
  have hpos : 0 < (q : ℝ) * (T + 2) / (2 * Real.pi) := by
    apply div_pos _ (by positivity)
    exact mul_pos (by linarith) (by linarith)
  have hx := (Real.log_le_iff_le_exp hpos).mp hℓ6
  have he6 : Real.exp 6 < 403.43 := by
    have h1 : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 6 < (2.7182818286 : ℝ) ^ 6 :=
      pow_lt_pow_left₀ h2 (Real.exp_pos 1).le (by norm_num)
    rw [h1]
    calc Real.exp 1 ^ 6 < (2.7182818286 : ℝ) ^ 6 := h3
      _ < 403.43 := by norm_num
  have hpi := Real.pi_lt_d4
  rw [div_le_iff₀ (by positivity)] at hx
  have hqT : (q : ℝ) * (19 / 7) ≤ (q : ℝ) * (T + 2) := by nlinarith
  have hfin : (q : ℝ) < 935 := by nlinarith
  exact_mod_cast hfin

/-- Split of `bennett_two_sided_zero_count`, same statement, assembled from the four range
leaves of Bennett et al. section 6. -/
theorem bennett_two_sided_zero_count_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1 < q) {T : ℝ} (hT : 5 / 7 ≤ T) :
    (Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 1.567 →
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) = 0) ∧
    (1.567 < Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) →
      |∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) -
          (T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) -
            (χ (-1)).re / 4)| ≤
        0.22737 * Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) +
          2 * Real.log (1 + Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi))) - 0.5) := by
  constructor
  · intro hℓ
    exact bennett_lemma_6_1_b χ hχ hq
      (conductor_lt_935_of_ell_le_six hT (by linarith)) (by linarith) hℓ
  · intro hℓ
    by_cases h6 : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 6
    · exact bennett_small_ell_zero_count χ hχ hq (conductor_lt_935_of_ell_le_six hT h6) hT hℓ h6
    · by_cases h28 : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 28
      · exact bennett_middle_ell_zero_count χ hχ hq hT (by linarith) h28
      · exact bennett_large_ell_zero_count χ hχ hq hT (by linarith)

end LeanLab.HelfgottMajor.ZeroCount1623
