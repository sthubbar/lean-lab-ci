/-
Split of the OPEN leaf `leaf_err_rearrange` of SPLIT_Decomp409b.lean, P0069 page 27,
display (4.13), first inequality. The statement is restated verbatim in
`leaf_err_rearrange_of_leaves`.

The split follows the proof described in the leaf's doc comment.
Leaf 1, the sum swap and interval count: the sum of c double prime over I1 is a sum over m, n
and d of |a_m b_n| times the number of k in I1 divisible by mnd, at most y1/(mnd) + 2.
Leaf 2, the harmonic weight sums: the sums over m ~ M of |a_m|/m and over n ~ N of |b_n|/n
have product at most L^K, from the bound of tau(m)^B/m summed over m up to 2M.
Leaf 3, the remainder size: the plain weight sums times the number of d below gamma w
are O(x^0.96) under (4.8) or (4.9) once epsilon is small.
The assembly is proved. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp409b

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409b
open Finset Filter Topology Decomp1518
attribute [local instance] Classical.propDecidable

/-- LEAF: display (4.13), first step, the sum swap. MEDIUM.
Summing c double prime over k in I1 and swapping, the pairs m, n with mn | k and the d with
d | k/(mn) give, for each m, n and each d | P(w) with gamma at most d below gamma w, the
number of k in I1 divisible by mnd, at most (y1 + 1)/(mnd) + 1 at most y1/(mnd) + 2. The d
counted number at most gamma w + 1, since they are positive integers below gamma w.
Non-vacuity: every x at least 1 and every a, b, M, N; equality-free for a = b = 0. -/
theorem leaf_err_swap (x M N w γ : ℝ) (a b : ℕ → ℂ) (hx : 1 ≤ x) (hγ : 1 ≤ γ) (hw : 1 ≤ w) :
    ∑ k ∈ Finset.Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, conv2E a b M N w γ k ≤
      y1 x * ((∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ‖a m‖ / (m : ℝ)) *
          (∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊, ‖b n‖ / (n : ℝ))) *
        ∑ d ∈ (siftingProduct w).divisors.filter
          (fun d => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w), (1 / (d : ℝ)) +
      2 * ((∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ‖a m‖) * (∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊, ‖b n‖)) *
        (γ * w + 1) := by
  sorry

/-- LEAF: display (4.13), "using sum over m ~ M of tau(m)^B/m at most L^K". HARD, CITED.
The harmonic sums of tau to the B over m up to 2M with 2M at most x are O(L^K), K depending
on B, the classical mean value of the divisor function; the ranges (4.8) or (4.9) give
M and N at most x. Non-vacuity: a = b = 0 gives the product zero. -/
theorem leaf_err_harmonic (ε : ℝ) (hε : 0 < ε) (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ)
    (ha : ∀ x k, ‖a x k‖ ≤ tau k ^ B) (hb : ∀ x k, ‖b x k‖ ≤ tau k ^ B)
    (hr : ∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) :
    ∃ C K X0 : ℝ, 0 ≤ K ∧ ∀ x : ℝ, X0 ≤ x →
      (∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖ / (m : ℝ)) *
          (∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖ / (n : ℝ)) ≤ C * L x ^ K := by
  sorry

/-- LEAF: display (4.13), the remainder "at most M N gamma w times x^o(1), below x^0.96
under (4.8) or (4.9) once epsilon is small". MEDIUM.
The plain sums are at most (M + 1) and (N + 1) times x^o(1) by the divisor bound, MN is at
most x^0.775 under (4.8) and x^(0.92 + ε/4) under (4.9), and gamma w is x^(ε/12 + o(1)).
Non-vacuity: a = b = 0 makes the left side zero. -/
theorem leaf_err_remainder :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
        2 * ((∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖) * (∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖)) *
          (cutoff ε x * wof x + 1) ≤ C * x ^ (0.96 : ℝ) := by
  sorry

/-- `leaf_err_rearrange` of SPLIT_Decomp409b, verbatim. CONDITIONAL ON `leaf_err_swap`,
`leaf_err_harmonic` and `leaf_err_remainder`. -/
theorem leaf_err_rearrange_of_leaves :
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
  obtain ⟨ε0, hε0, hrem⟩ := leaf_err_remainder
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hεs B a b M N ha hb hr
  obtain ⟨C1, K, X1, hK, h1⟩ := leaf_err_harmonic ε hε B a b M N ha hb hr
  obtain ⟨C2, X2, h2⟩ := hrem ε hε hεs B a b M N ha hb hr
  refine ⟨max (max C1 C2) 0, K, max (max X1 X2) 1, le_max_right _ _, hK, ?_⟩
  intro x hx
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hγ : (1 : ℝ) ≤ cutoff ε x := le_trans (by norm_num) (le_max_left _ _)
  have hw : (1 : ℝ) ≤ wof x := by
    unfold wof
    exact Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg hx3) _)
  have hy : 0 ≤ y1 x := (y1_pos (by linarith)).le
  have hL : 0 ≤ L x ^ K := Real.rpow_nonneg (Real.log_nonneg hx3) _
  set S := ∑ d ∈ (siftingProduct (wof x)).divisors.filter
    (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ)) with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    refine Finset.sum_nonneg fun d hd => ?_
    have h1 : cutoff ε x ≤ d := (Finset.mem_filter.mp hd).2.1
    exact one_div_nonneg.mpr (by linarith)
  have hsw := leaf_err_swap x (M x) (N x) (wof x) (cutoff ε x) (a x) (b x) hx3 hγ hw
  have hh := h1 x hx1
  have hrr := h2 x hx2
  have hxp : 0 ≤ x ^ (0.96 : ℝ) := Real.rpow_nonneg (by linarith) _
  set C := max (max C1 C2) 0
  have hC1 : C1 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hmain : y1 x * ((∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖ / (m : ℝ)) *
          (∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖ / (n : ℝ))) * S ≤
        C * (y1 x * L x ^ K * S) := by
    have hyS : 0 ≤ y1 x * S := mul_nonneg hy hS0
    calc _ = (y1 x * S) * ((∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖ / (m : ℝ)) *
          (∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖ / (n : ℝ))) := by ring
      _ ≤ (y1 x * S) * (C1 * L x ^ K) := mul_le_mul_of_nonneg_left hh hyS
      _ ≤ (y1 x * S) * (C * L x ^ K) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC1 hL) hyS
      _ = C * (y1 x * L x ^ K * S) := by ring
  have hrem' : 2 * ((∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖) *
      (∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖)) * (cutoff ε x * wof x + 1) ≤
        C * x ^ (0.96 : ℝ) := hrr.trans (mul_le_mul_of_nonneg_right hC2 hxp)
  calc _ ≤ _ := hsw
    _ ≤ C * (y1 x * L x ^ K * S) + C * x ^ (0.96 : ℝ) := add_le_add hmain hrem'
    _ = _ := by ring

#print axioms leaf_err_rearrange_of_leaves

end LeanLab.BakerHarmanPintz1997.Decomp409b
