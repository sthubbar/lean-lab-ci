/-
Feed 1122 split of the three counting leaves of `LeanLab/AlmostPrimes/SPLIT_bjs_chen_3273.lean`,
namely `bjs_chen_3273_leaf_count_low`, `bjs_chen_3273_leaf_count_mid` and
`bjs_chen_3273_leaf_count_high`.

Source: P0009, M. Bordignon, D. R. Johnston, V. Starichkova, An explicit version of Chen's
theorem, arXiv 2207.09452, Theorem 3: for even `N > exp (exp 32.7)` one has
`π₂(N) > 2·10⁻⁴ U_N N / log² N`, with `U_N = 2 e^{-γ} C₂ ∏_{p > 2, p ∣ N} (p-1)/(p-2)`,
equation (2) of the paper.  Here `C₂ = ∏_{p > 2} (1 - 1/(p-1)²) ≈ 0.6601` is the twin prime
constant, so `U_N ≥ 2 e^{-γ} C₂ ≈ 0.741`, and the paper's main term is at least
`1.48·10⁻⁴ N / log² N`, above the `10⁻⁴ N / log² N` that each counting leaf asks for.

Leaves:
* `leaf_bjs_theorem3`, the cited Theorem 3, in the form `LeanLab.ChenExplicit.BJS3`.  HARD.
* `leaf_twinC_ge_half`, the numerical bound `C₂ ≥ 1/2`.  MEDIUM.

Proved here from the leaves: `U_N ≥ 1/2`, the comparison of `chenCount` with the filtered count
in `bigOmega`, and the counting estimate `bjs_chen_3273_count_of_leaves` for every even
`N > exp (exp 32.73)`, which closes the three range leaves.  Binary Goldbach is open; this is
about Chen's theorem.  AI wrote the Lean code.
-/
import LeanLab.AlmostPrimes.Statements
import LeanLab.ChenExplicit.Reductions

namespace LeanLab.AlmostPrimes

open Real

/-- LEAF: BJS 2022, arXiv 2207.09452, Theorem 3, the explicit lower bound for the Chen count:
for even `N > exp (exp 32.7)`, `π₂(N) > 2·10⁻⁴ U_N N / log² N`.  HARD: this is the whole
explicit weighted sieve of the paper, Theorems 44, 50, 51 and the Section 9 numerics; the lab
has it conditionally as `LeanLab.ChenExplicit.BJS3_of_sieveBounds`.  Pure citation. -/
theorem leaf_bjs_theorem3 : LeanLab.ChenExplicit.BJS3 := by
  sorry

/-- LEAF: the twin prime constant `C₂ = ∏_{p > 2} (1 - 1/(p-1)²)` of equation (2) of BJS 2022 is
at least `1/2`; numerically `C₂ ≈ 0.6601`.  MEDIUM: the factors lie in `(0, 1]` and are indexed
by the distinct even integers `p - 1 ≥ 2`, so `log C₂ ≥ -(4/3) Σ_{m ≥ 1} 1/(2m)² = -π²/18`,
using `log (1 - x) ≥ -4x/3` for `0 ≤ x ≤ 1/4`, and `exp (-π²/18) > 1/2`.  The lab already has
`twinC_multipliable` and the weaker `twinC_ge` in `LeanLab.ChenExplicit`. -/
theorem leaf_twinC_ge_half : (1 : ℝ) / 2 ≤ LeanLab.ChenExplicit.twinC := by
  have h := LeanLab.ChenExplicit.twinC_ge_065
  norm_num at h ⊢
  <;> linarith

/-- `e² < 8`, from `e < 2.7182818286`. -/
private theorem exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc Real.exp 1 ^ 2 < (2.7182818286 : ℝ) ^ 2 :=
        pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num)
    _ < 8 := by norm_num

/-- `e^{-γ} ≥ 1/2`, from `γ < 2/3` and `e^{2/3} < 2`. -/
private theorem exp_neg_gamma_ge_half : (1 : ℝ) / 2 ≤ Real.exp (-Real.eulerMascheroniConstant) := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have h1 : Real.exp (-(2 / 3)) ≤ Real.exp (-Real.eulerMascheroniConstant) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (2 / 3) < 2 := by
    have h3 : Real.exp (2 / 3) ^ 3 = Real.exp 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h4 := exp_two_lt_eight
    have hp := Real.exp_pos (2 / 3)
    nlinarith [sq_nonneg (Real.exp (2 / 3) - 2), sq_nonneg (Real.exp (2 / 3))]
  have h5 : Real.exp (-(2 / 3)) = (Real.exp (2 / 3))⁻¹ := Real.exp_neg _
  have h6 : (1 : ℝ) / 2 ≤ (Real.exp (2 / 3))⁻¹ := by
    rw [one_div]; exact inv_anti₀ (Real.exp_pos _) h2.le
  linarith

/-- `U_N ≥ 1/2` for every `N`, from `leaf_twinC_ge_half`, `e^{-γ} ≥ 1/2` and the local factor
being at least `1`. -/
theorem U_ge_half_of_leaves (N : ℕ) : (1 : ℝ) / 2 ≤ LeanLab.ChenExplicit.U N := by
  unfold LeanLab.ChenExplicit.U
  have h1 := LeanLab.ChenExplicit.one_le_oddFactor N
  have h2 := leaf_twinC_ge_half
  have h3 := exp_neg_gamma_ge_half
  set a := Real.exp (-Real.eulerMascheroniConstant)
  set c := LeanLab.ChenExplicit.twinC
  set d := ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))
  have hac : (1 : ℝ) / 4 ≤ a * c := by nlinarith
  have hd0 : (0 : ℝ) ≤ a * c := by linarith
  nlinarith

/-- The Chen count of `LeanLab.ChenExplicit`, which uses Mathlib's `IsAtMostAlmostPrime 2`,
is at most the filtered count in `bigOmega` used by the split. -/
theorem chenCount_le_filter_card (N : ℕ) :
    LeanLab.ChenExplicit.chenCount N ≤
      ((Finset.range N).filter (fun p => p.Prime ∧ bigOmega (N - p) ≤ 2)).card := by
  classical
  unfold LeanLab.ChenExplicit.chenCount
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  refine ⟨hp.1, hp.2.1, ?_⟩
  have h := hp.2.2.2
  rw [bigOmega_eq_cardFactors]
  exact h

/-- The counting estimate of all three range leaves, for every even `N > exp (exp 32.73)`,
assembled from `leaf_bjs_theorem3` and `leaf_twinC_ge_half`. -/
theorem bjs_chen_3273_count_of_leaves (N : ℕ) (hN : Even N)
    (hlo : Real.exp (Real.exp 32.73) < (N : ℝ)) :
    (1 / 10000 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 <
      ((Finset.range N).filter (fun p => p.Prime ∧ bigOmega (N - p) ≤ 2)).card := by
  have hthr : Real.exp (Real.exp (327 / 10)) < (N : ℝ) := by
    refine lt_of_le_of_lt ?_ hlo
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))
  have hb := leaf_bjs_theorem3 N hN hthr
  have hU := U_ge_half_of_leaves N
  have hc : (LeanLab.ChenExplicit.chenCount N : ℝ) ≤
      (((Finset.range N).filter (fun p => p.Prime ∧ bigOmega (N - p) ≤ 2)).card : ℝ) := by
    exact_mod_cast chenCount_le_filter_card N
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hL : (0 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
  have hle : (1 / 10000 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
      (2 / 10000 : ℝ) * LeanLab.ChenExplicit.U N * N / Real.log N ^ 2 := by
    apply div_le_div_of_nonneg_right _ hL
    nlinarith
  linarith

/-- `bjs_chen_3273_leaf_count_low` from the leaves. -/
theorem bjs_chen_3273_leaf_count_low_of_leaves (N : ℕ) (hN : Even N)
    (hlo : Real.exp (Real.exp 32.73) < (N : ℝ))
    (_hhi : (N : ℝ) ≤ Real.exp (Real.exp 32.78)) :
    (1 / 10000 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 <
      ((Finset.range N).filter (fun p => p.Prime ∧ bigOmega (N - p) ≤ 2)).card :=
  bjs_chen_3273_count_of_leaves N hN hlo

/-- `exp (exp 32.73) ≤ exp (exp t)` for `32.73 ≤ t`. -/
private theorem exp_exp_3273_le {t : ℝ} (ht : 32.73 ≤ t) :
    Real.exp (Real.exp 32.73) ≤ Real.exp (Real.exp t) :=
  Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ht)

/-- `bjs_chen_3273_leaf_count_mid` from the leaves. -/
theorem bjs_chen_3273_leaf_count_mid_of_leaves (N : ℕ) (hN : Even N)
    (hlo : Real.exp (Real.exp 32.78) < (N : ℝ))
    (_hhi : (N : ℝ) ≤ Real.exp (Real.exp 32.83)) :
    (1 / 10000 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 <
      ((Finset.range N).filter (fun p => p.Prime ∧ bigOmega (N - p) ≤ 2)).card :=
  bjs_chen_3273_count_of_leaves N hN (lt_of_le_of_lt (exp_exp_3273_le (by norm_num)) hlo)

/-- `bjs_chen_3273_leaf_count_high` from the leaves. -/
theorem bjs_chen_3273_leaf_count_high_of_leaves (N : ℕ) (hN : Even N)
    (hlo : Real.exp (Real.exp 32.83) < (N : ℝ)) :
    (1 / 10000 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 <
      ((Finset.range N).filter (fun p => p.Prime ∧ bigOmega (N - p) ≤ 2)).card :=
  bjs_chen_3273_count_of_leaves N hN (lt_of_le_of_lt (exp_exp_3273_le (by norm_num)) hlo)

end LeanLab.AlmostPrimes

#print axioms LeanLab.AlmostPrimes.U_ge_half_of_leaves
#print axioms LeanLab.AlmostPrimes.chenCount_le_filter_card
#print axioms LeanLab.AlmostPrimes.bjs_chen_3273_count_of_leaves
#print axioms LeanLab.AlmostPrimes.bjs_chen_3273_leaf_count_low_of_leaves
#print axioms LeanLab.AlmostPrimes.bjs_chen_3273_leaf_count_mid_of_leaves
#print axioms LeanLab.AlmostPrimes.bjs_chen_3273_leaf_count_high_of_leaves
