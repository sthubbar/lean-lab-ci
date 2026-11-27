/-
Split of the OPEN leaf `leaf_err_rearrange` of SPLIT_Decomp409b, the first inequality of
display (4.13), P0069 page 27, with remainder x^0.96.

The paper swaps the sums in the sum of c double prime over I1 = (x - y1, x]: for fixed m, n
and d in the dagger range, the k = mnl in I1 with d | l are the multiples of mnd in I1, at
most y1/(mnd) + 2 of them. This gives three pieces:
* `leaf_err_count`, the swap and the interval count, deterministic, MEDIUM;
* `leaf_err_main`, the y1/(mnd) part, bounded by y1 L^K times the reciprocal sum over d
  through the divisor moment sum over m ~ M of tau(m)^B / m, HARD;
* `leaf_err_remainder`, the + 2 part, bounded by x^0.96 under (4.8) or (4.9), HARD.
`leaf_err_rearrange_split` restates `leaf_err_rearrange` verbatim.
AI wrote the Lean code. Goldbach is open.
-
- Helper lemma: divisor moment sum with 1/k factor
- By `divisor_moment` in Decomp409a, ∑_{k≤N} τ(k)^B ≤ C N (log N)^D
- Then ∑_{k≤N} τ(k)^B / k ≤ C (log N)^(D+1) by partial summation
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_Decomp409b

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409b
open Finset Filter Topology Decomp1518
attribute [local instance] Classical.propDecidable

/-- LEAF: display (4.13), the swap of sums and the interval count. MEDIUM.
For k = mnl in (x - y, x], psiErr l counts the d | P(w), gamma at most d below gamma w,
with d | l, that is mnd | k. The multiples of mnd in the window number at most
(y + 1)/(mnd) + 1, at most y/(mnd) + 2 as mnd is at least 1. Needs 0 at most y at most x.
Non-vacuity: a = b = 0 gives 0 at most 0; for a = b = 1 both sides are positive. -/
theorem leaf_err_count (a b : ℕ → ℂ) (M N w γ x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) :
    ∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, conv2E a b M N w γ k ≤
      ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        ∑ d ∈ (siftingProduct w).divisors.filter (fun d => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w),
          ‖a m‖ * ‖b n‖ * (y / ((m : ℝ) * n * d) + 2) := by
  sorry

/-- LEAF: display (4.13), the main part. HARD.
The y1/(mnd) terms factor as y1 times the sum over m ~ M of |a_m|/m, the same over n, and
the reciprocal sum over d. Under (4.8) or (4.9), M, N are at most x, so by (3.1) each
factor is at most the sum over m up to 2x of tau(m)^|B| / m, at most C L^K.
Non-vacuity: a = b = 0 makes the left side zero. -/
theorem leaf_err_main :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∃ C K X0 : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ x : ℝ, X0 ≤ x →
        ∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
          ∑ d ∈ (siftingProduct (wof x)).divisors.filter
              (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x),
            ‖a x m‖ * ‖b x n‖ * (y1 x / ((m : ℝ) * n * d)) ≤
          C * (y1 x * L x ^ K *
            ∑ d ∈ (siftingProduct (wof x)).divisors.filter
              (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ))) := by
  sorry

/-- LEAF: display (4.13), the remainder. HARD.
The + 2 terms total at most 2 (M + 1)(N + 1) gamma w max tau^|B| squared. Here gamma is
x^(ε/12), w = exp(L^(9/10)) and tau(m) are x^o(1), and MN is at most x^0.775 under (4.8)
or x^(0.92 + ε/4) under (4.9), so the total is below C x^0.96 once ε is small.
Non-vacuity: a = b = 0 makes the left side zero. -/
theorem leaf_err_remainder :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∃ C X0 : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X0 ≤ x →
        ∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
          ∑ d ∈ (siftingProduct (wof x)).divisors.filter
              (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x),
            ‖a x m‖ * ‖b x n‖ * 2 ≤ C * x ^ (0.96 : ℝ) := by
  sorry

/-- Proved glue: y1 x is at most x for x at least 1. -/
theorem y1_le_self {x : ℝ} (hx : 1 ≤ x) : y1 x ≤ x := by
  unfold y1
  have h0 : 0 ≤ Real.log x ^ (1 / 3 : ℝ) := Real.rpow_nonneg (Real.log_nonneg hx) _
  have h1 : Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  nlinarith

/-- `leaf_err_rearrange`, verbatim, CONDITIONAL ON `leaf_err_count`, `leaf_err_main` and
`leaf_err_remainder`. -/
theorem leaf_err_rearrange_split :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∃ C K X0 : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ x : ℝ, X0 ≤ x →
        ∑ k ∈ Finset.Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊,
          conv2E (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k ≤
            C * (y1 x * L x ^ K *
              ∑ d ∈ (siftingProduct (wof x)).divisors.filter
                (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ))
              + x ^ (0.96 : ℝ)) := by
  obtain ⟨ε2, hε2, h2⟩ := leaf_err_main
  obtain ⟨ε3, hε3, h3⟩ := leaf_err_remainder
  refine ⟨min ε2 ε3, lt_min hε2 hε3, ?_⟩
  intro ε hε hεs B a b M N ha hb hr
  obtain ⟨C2, K, X2, hC2, hK, h2'⟩ :=
    h2 ε hε (hεs.trans_le (min_le_left _ _)) B a b M N ha hb hr
  obtain ⟨C3, X3, hC3, h3'⟩ :=
    h3 ε hε (hεs.trans_le (min_le_right _ _)) B a b M N ha hb hr
  refine ⟨C2 + C3, K, max (max X2 X3) 1, add_nonneg hC2 hC3, hK, ?_⟩
  intro x hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : X3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hy : 0 < y1 x := y1_pos (by linarith)
  have hyx : y1 x ≤ x := y1_le_self hx1
  set S := ∑ d ∈ (siftingProduct (wof x)).divisors.filter
    (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ)) with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    refine Finset.sum_nonneg fun i hi => ?_
    have hi2 := (Finset.mem_filter.1 hi).2.1
    have : (0 : ℝ) ≤ i := le_trans (by norm_num) (le_trans (le_max_left 2 _) hi2)
    positivity
  have hL : 0 ≤ L x := Real.log_nonneg hx1
  have hmain0 : 0 ≤ y1 x * L x ^ K * S :=
    mul_nonneg (mul_nonneg hy.le (Real.rpow_nonneg hL _)) hS0
  have hp0 : 0 ≤ x ^ (0.96 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc _ ≤ _ := leaf_err_count (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) x (y1 x) hy.le hyx
    _ = (∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
          ∑ d ∈ (siftingProduct (wof x)).divisors.filter
              (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x),
            ‖a x m‖ * ‖b x n‖ * (y1 x / ((m : ℝ) * n * d))) +
        ∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
          ∑ d ∈ (siftingProduct (wof x)).divisors.filter
              (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x),
            ‖a x m‖ * ‖b x n‖ * 2 := by
        simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ C2 * (y1 x * L x ^ K * S) + C3 * x ^ (0.96 : ℝ) := add_le_add (h2' x hx2) (h3' x hx3)
    _ ≤ (C2 + C3) * (y1 x * L x ^ K * S + x ^ (0.96 : ℝ)) := by nlinarith

#print axioms y1_le_self
#print axioms leaf_err_rearrange_split

end LeanLab.BakerHarmanPintz1997.Decomp409b
