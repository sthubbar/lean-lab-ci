import LeanLab.HelfgottMajor.SPLIT_bennett_two_sided_zero_count

/-!
# Split of `bennett_lemma_6_1_b`

Bennett, Martin, O'Bryant and Rechnitzer, Counting zeros of Dirichlet L-functions, Math. Comp. 90
2021, Lemma 6.1 (b), page 1478: for `χ` primitive of conductor `1 < q < 935`, `T ≥ 0` and
`ℓ = log (q (T + 2) / (2π)) ≤ 1.567`, `N(T, χ) = 0`. The proof, page 1479, has two steps:

* `The conditions in Lemma 6.1(b) imply that q ≤ 15.` Proved here: `T ≥ 0` gives
  `q ≤ π e^{1.567} < 16`.
* `The 40 primitive characters with q ≤ 15 are covered in our dataset, and for each, the
  lowest-height zero is excluded by log q(T+2)/(2π) ≤ 1.567.` One LEAF, stated per character and
  with no `T`: every zero in the critical strip has `log (q (|γ| + 2) / (2π)) > 1.567`.

The assembly is proved: a counted zero would have `|γ| ≤ T`, so its own `ℓ` is at most the `ℓ` of
`T`, contradicting the leaf; the strip set is empty and the sum is `0`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set

variable {q : ℕ} [NeZero q]

/-- LEAF: Bennett et al. 2021, proof of Lemma 6.1 (b), page 1479, the rigorous zero data of the
40 primitive characters with `q ≤ 15`. MEDIUM, CITED, one finite computation per character: for
`χ` primitive of conductor `1 < q ≤ 15`, every zero `ρ = β + iγ` of `L(s, χ)` with `0 < β < 1`
has `log (q (|γ| + 2) / (2π)) > 1.567`, that is its lowest zero lies above height
`2π e^{1.567} / q - 2`. -/
theorem bennett_lowest_zero_q_le_15 (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1 < q) (hq15 : q ≤ 15) {ρ : ℂ} (hz : DirichletCharacter.LFunction χ ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    1.567 < Real.log ((q : ℝ) * (|ρ.im| + 2) / (2 * Real.pi)) := by
  sorry

/-- `e^{0.567} < 1.8432`, from `e^x ≤ 1/(1 - x)` at `x = 0.14175`, raised to the fourth power.
Proved. -/
lemma exp_0567_lt : Real.exp 0.567 < 1.8432 := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 0.14175) (by norm_num) (by norm_num)
  have h4 : Real.exp 0.567 = Real.exp 0.14175 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h4]
  calc Real.exp 0.14175 ^ 4 < (1 / (1 - 0.14175)) ^ 4 :=
        pow_lt_pow_left₀ h (Real.exp_pos _).le (by norm_num)
    _ < 1.8432 := by norm_num

/-- `e^{1.567} < 5.0104`. Proved. -/
lemma exp_1567_lt : Real.exp 1.567 < 5.0104 := by
  have h1 : Real.exp 1.567 = Real.exp 1 * Real.exp 0.567 := by
    rw [← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have h2 := exp_0567_lt
  rw [h1]
  calc Real.exp 1 * Real.exp 0.567 < 2.7182818286 * 1.8432 := by
        apply mul_lt_mul he h2.le (Real.exp_pos _) (by norm_num)
    _ < 5.0104 := by norm_num

/-- Bennett et al. 2021, page 1479, `The conditions in Lemma 6.1(b) imply that q ≤ 15`: from
`T ≥ 0` and `ℓ ≤ 1.567`, `q ≤ π e^{1.567} < 15.75`. Proved. -/
lemma conductor_le_15_of_ell_le_1567 {T : ℝ} (hT : 0 ≤ T)
    (hℓ : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 1.567) : q ≤ 15 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpi0 := Real.pi_pos
  have hpos : 0 < (q : ℝ) * (T + 2) / (2 * Real.pi) := by
    apply div_pos _ (by positivity)
    exact mul_pos (by linarith) (by linarith)
  have hx := (Real.log_le_iff_le_exp hpos).mp hℓ
  have he := exp_1567_lt
  have hpi := Real.pi_lt_d2
  rw [div_le_iff₀ (by positivity)] at hx
  have hq2 : (q : ℝ) * 2 ≤ (q : ℝ) * (T + 2) := by nlinarith
  have hfin : (q : ℝ) < 16 := by nlinarith
  have : q < 16 := by exact_mod_cast hfin
  omega

/-- Split of `bennett_lemma_6_1_b`, same statement, from the proved bound `q ≤ 15` and the
per character LEAF `bennett_lowest_zero_q_le_15`. -/
theorem bennett_lemma_6_1_b_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1 < q) (hq935 : q < 935) {T : ℝ} (hT : 0 ≤ T)
    (hℓ : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 1.567) :
    ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) = 0 := by
  have hq15 := conductor_le_15_of_ell_le_1567 hT hℓ
  apply Finset.sum_eq_zero
  intro ρ hρ
  exfalso
  rw [Set.Finite.mem_toFinset] at hρ
  obtain ⟨hz, h0, h1, hT'⟩ := hρ
  have hlow := bennett_lowest_zero_q_le_15 χ hχ hq hq15 hz h0 h1
  have hq1 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hpi0 := Real.pi_pos
  have hpos : 0 < (q : ℝ) * (|ρ.im| + 2) / (2 * Real.pi) := by
    apply div_pos _ (by positivity)
    exact mul_pos hq1 (by positivity)
  have hmono : Real.log ((q : ℝ) * (|ρ.im| + 2) / (2 * Real.pi)) ≤
      Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) := by
    apply Real.log_le_log hpos
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hq1.le
  linarith

end LeanLab.HelfgottMajor.ZeroCount1623

#print axioms LeanLab.HelfgottMajor.ZeroCount1623.exp_0567_lt
#print axioms LeanLab.HelfgottMajor.ZeroCount1623.exp_1567_lt
#print axioms LeanLab.HelfgottMajor.ZeroCount1623.conductor_le_15_of_ell_le_1567
#print axioms LeanLab.HelfgottMajor.ZeroCount1623.bennett_lemma_6_1_b_split
