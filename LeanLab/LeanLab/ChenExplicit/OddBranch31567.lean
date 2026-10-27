/-
AI wrote this Lean code. CODEX task44.
CITED input: Bordignon arXiv 1809.05226 v2, Theorem 1.3, page 2, eq 4.
This is the odd character input used in the BJS exceptional zero branch.
BJS arXiv 2207.09452 v6 calls the nu formulas eqs 81 and 91.
The resulting zero bound stays CONDITIONAL ON BordignonOdd800.
-/
import LeanLab.ChenExplicit.U1490NuX1
import LeanLab.ChenExplicit.U1498MX3

open Real DirichletCharacter

noncomputable section
namespace LeanLab.ChenExplicit.OddBranch31567

open LeanLab.ChenExplicit.U1483 LeanLab.ChenExplicit.U1490

/-- The primitive odd real non-principal characters. -/
def OddRealPrim {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  χ.Odd ∧ χ.IsPrimitive ∧ χ ≠ 1 ∧ χ ^ 2 = 1

/-- CITED: Bordignon Theorem 1.3, odd branch, eq 4. -/
def BordignonOdd800 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), OddRealPrim χ → (4e5 : ℝ) < q →
    ∀ β : ℝ, RealZero χ β → 1 - 1 / (9.6459 * log q) ≤ β →
      β ≤ 1 - 800 / (sqrt q * log q ^ 2)

/-- A scalar bound used to recognize the exceptional zero region. -/
lemma exp125_le : exp (12.5 : ℝ) ≤ 4e5 := by
  have he : exp (12.5 : ℝ) = exp 1 ^ 12 * exp 0.5 := by
    rw [exp_one_pow, ← exp_add]; norm_num
  have h1 : exp 1 ^ 12 ≤ (2.7182818286 : ℝ) ^ 12 :=
    pow_le_pow_left₀ (exp_pos _).le exp_one_lt_d9.le 12
  have h2 : exp (0.5 : ℝ) ≤ 2 := by
    rw [← exp_log (by norm_num : (0 : ℝ) < 2), exp_le_exp]
    have := log_two_gt_d9; linarith
  rw [he]
  calc exp 1 ^ 12 * exp 0.5 ≤ (2.7182818286 : ℝ) ^ 12 * 2 :=
    mul_le_mul h1 h2 (exp_pos _).le (by positivity)
    _ ≤ 4e5 := by norm_num

lemma odd_gap_le_region {q : ℝ} (hq : 4e5 < q) :
    800 / (sqrt q * log q ^ 2) ≤ 1 / (9.6459 * log q) := by
  have hq0 : 0 < q := by linarith
  have hl : 12.5 ≤ log q := by
    rw [le_log_iff_exp_le hq0]; exact exp125_le.trans hq.le
  have hs : (632 : ℝ) ≤ sqrt q := by
    rw [show (632 : ℝ) = sqrt (632 ^ 2 : ℝ) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by linarith)
  have hp : 800 * 9.6459 ≤ sqrt q * log q := by
    have := mul_le_mul hs hl (by norm_num : (0 : ℝ) ≤ 12.5) (by positivity)
    norm_num at this ⊢; linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_right hp (show 0 ≤ log q by linarith)
  nlinarith

/-- CONDITIONAL ON BordignonOdd800: other real zeroes already satisfy its upper bound. -/
theorem odd_zero_bound (hOdd : BordignonOdd800) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : OddRealPrim χ) (hq : (4e5 : ℝ) < q)
    (β : ℝ) (hβ : RealZero χ β) : β ≤ 1 - 800 / (sqrt q * log q ^ 2) := by
  by_cases hregion : 1 - 1 / (9.6459 * log (q : ℝ)) ≤ β
  · exact hOdd q χ hχ hq β hβ hregion
  · have hgap := odd_gap_le_region hq
    push_neg at hregion
    linarith

lemma odd_gap_ge_plus_gap {q K : ℝ} (hq : 4e5 < q) (hqK : q ≤ K)
    (hK : log K ≤ 200) : 4 / (sqrt K * log K) ≤ 800 / (sqrt q * log q ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hlq : 0 < log q := log_pos (by linarith)
  have hlK : log q ≤ log K := log_le_log hq0 hqK
  have hc : cP q ≤ 800 := by unfold cP; exact max_le (by norm_num) (by linarith)
  exact (gapP_ge_K hq hqK).trans (div_le_div_of_nonneg_right hc (by positivity))

/-- CONDITIONAL ON BordignonOdd800: the plus gap applies to odd characters up to K. -/
theorem odd_upto_K (hOdd : BordignonOdd800) {K : ℝ} (hK : log K ≤ 200)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : OddRealPrim χ)
    (hq : (4e5 : ℝ) < q) (hqK : (q : ℝ) ≤ K) (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - 4 / (sqrt K * log K) := by
  have hz := odd_zero_bound hOdd q χ hχ hq β hβ
  have hg := odd_gap_ge_plus_gap hq hqK hK
  linarith

lemma logK1_le200 : log U1490NuX1.K1 ≤ 200 := by
  have hu := U1490NuX1.logLx_le
  unfold U1490NuX1.K1
  rw [log_rpow U1490NuX1.Lx_pos]
  unfold U1490NuX1.δ
  nlinarith

lemma logK3_le200 : log U1498MX3.K ≤ 200 := by
  have hu := U1498MX3.logℓ_bounds.2
  unfold U1498MX3.K
  rw [log_rpow U1498MX3.ℓ_pos]
  nlinarith

/-- CONDITIONAL ON BordignonOdd800: odd branch at x1 of X2. -/
theorem nuP1_odd (hOdd : BordignonOdd800) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : OddRealPrim χ) (hq : (4e5 : ℝ) < q)
    (hqK : (q : ℝ) ≤ U1490NuX1.K1) (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - U1490NuX1.nuP := by
  have hz := odd_upto_K hOdd logK1_le200 q χ hχ hq hqK β hβ
  have hg : U1490NuX1.nuP ≤ 4 / (sqrt U1490NuX1.K1 * log U1490NuX1.K1) := min_le_left _ _
  linarith

/-- CONDITIONAL ON BordignonOdd800: odd branch at x2 of X3. -/
theorem nuP3_odd (hOdd : BordignonOdd800) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : OddRealPrim χ) (hq : (4e5 : ℝ) < q)
    (hqK : (q : ℝ) ≤ U1498MX3.K) (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - U1498MX3.νP := by
  have hz := odd_upto_K hOdd logK3_le200 q χ hχ hq hqK β hβ
  have hg : U1498MX3.νP ≤ 4 / (sqrt U1498MX3.K * log U1498MX3.K) := min_le_left _ _
  linarith

/-- Concrete domain instance for the elementary gap comparison. -/
example : 4 / (sqrt (10 ^ 6 : ℝ) * log (10 ^ 6)) ≤
    800 / (sqrt (10 ^ 6 : ℝ) * log (10 ^ 6) ^ 2) := by
  apply odd_gap_ge_plus_gap (by norm_num) le_rfl
  rw [log_pow]
  have h10 : log (10 : ℝ) ≤ 3 := by
    rw [log_le_iff_le_exp (by norm_num)]
    have := sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢
    linarith
  norm_num; linarith

#print axioms exp125_le
#print axioms odd_gap_le_region
#print axioms odd_zero_bound
#print axioms odd_gap_ge_plus_gap
#print axioms odd_upto_K
#print axioms logK1_le200
#print axioms logK3_le200
#print axioms nuP1_odd
#print axioms nuP3_odd

end LeanLab.ChenExplicit.OddBranch31567
