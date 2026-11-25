/-
BURST 2026-11-22, session S111, burst-20261122. SPLIT of the edge LEAFs
SecondDyadicCases1122.case1_edge, SecondDyadicCases1122.case2_edge and
SecondDyadicCase3Split1122.case3_edge, Lemma 3.4 Cases 1 to 3 of Kumchev and Liu
2007, P0088, arXiv 0801.0130, pages 11 to 12, on the stretch t in [Y - 2H, Y] of
the second sum of display 52, page 15, in window form.

AUDIT of the S81 obstruction. The obstruction is not real. S81 bounded the
short sum by its number of terms times the maximum coefficient, which loses the
maximum of tau. The l1 route works: for t in [Y - 2H, Y] every m in the short
sum lies in the window, so sqrt of Y - 2H < m < sqrt Y, an interval of length at
most 2H Y^(-1/2). The coefficient of m has modulus at most the number of block
primes p dividing m, at most 2 since p > Y^(1/6) and m < Y^(1/2), times tau of
m / p, at most tau of m. With tau of m at most twice the number of divisors up to
the square root, the sum of tau over an interval of length l ending below N is
at most 2 l times 1 + log N plus 2 sqrt N. Here N is about Y^(1/2) and
l is about H Y^(-1/2), so the squared short sum is at most a constant times
H^2 Y^(-1) log^2 X plus Y^(1/2). Since H is at most Y L^(-4B), the first is at
most H L^(-4B) log^2 X; since Y = X^(7/12 + eps/2) and H is at least
X^(7/18 + eps) L^(-4B) with 7/18 > 7/24, the second is at most H L^(-A) for large
X. So each edge holds for B0 about A/4 + 1, uniformly in M, D and alpha; no Shiu
type input is needed, and the window filter, which is a formalization artifact
of the window form, is harmless on the edge. Not treated in the paper, whose
short sums on page 10 carry no window filter.

This file PROVES each of the three edge LEAFs, checked by type_of%, from one
new LEAF edge_pointwise, the pointwise bound of the squared short sum on the
edge stretch described above, class MEDIUM, elementary, by the hyperbola bound
for tau over a short interval; and the integral reduction edge_integral_le,
PROVED.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SecondDyadicCases1122
import LeanLab.KumchevLiu2007.SecondDyadicCase3Split1122

namespace LeanLab.KumchevLiu2007.SecondDyadicEdges1123

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- PROVED. The integral of the squared short sum over [Y - 2H, Y] is at most
2H times a pointwise bound K on that stretch. -/
theorem edge_integral_le (S : Finset ℕ) (c : ℕ → ℂ) (Y H K : ℝ) (hH : 0 ≤ H)
    (h : ∀ t : ℝ, Y - 2 * H ≤ t → t ≤ Y →
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2 ≤ K) :
    (∫ t in Y - 2 * H..Y,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2) ≤
      2 * H * K := by
  have hab : Y - 2 * H ≤ Y := by linarith
  calc (∫ t in Y - 2 * H..Y,
        ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2)
      ≤ ∫ _t in Y - 2 * H..Y, K :=
        intervalIntegral.integral_mono_on hab
          (short_sum_sq_intervalIntegrable _ _ _ _ _) intervalIntegrable_const
          (fun t ht => h t ht.1 ht.2)
    _ = 2 * H * K := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- LEAF: P0088 pages 11 to 12, Lemma 3.4 Cases 1 to 3, the edge stretch
t in [Y - 2H, Y] of the second sum of display 52 in window form. Class MEDIUM.
The pointwise bound of the squared short sum, uniform in alpha, M and D: the
coefficient of m has modulus at most 2 tau of m, the m lie in an interval of
length at most 2H Y^(-1/2) below Y^(1/2), and the elementary hyperbola bound
for the sum of tau over a short interval gives at most a constant times
H^2 Y^(-1) log^2 X plus Y^(1/2), which is at most C H L^(-A) by the H range of
Theorem 1. Not a display of the paper: the paper has no window filter here; the
window filter comes from the window form of display 52. Elementary, no cited
input. -/
theorem edge_pointwise (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α M D : ℝ, ∀ t : ℝ, windowY X ε - 2 * H ≤ t → t ≤ windowY X ε →
        ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 ≤
            C * H / Real.log X ^ A := by
  sorry

/-- PROVED. H is nonnegative in the H range of Theorem 1. -/
theorem H_nonneg (X H B ε : ℝ) (hX : 2 ≤ X)
    (hlo : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H) : 0 ≤ H := by
  have hL : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have h1 : 0 ≤ X ^ (7 / 18 + ε) := Real.rpow_nonneg (by linarith) _
  have h2 : 0 ≤ (Real.log X ^ B) ^ (-4 : ℤ) := zpow_nonneg (Real.rpow_nonneg hL _) _
  exact (mul_nonneg h1 h2).trans hlo

/-- PROVED from edge_pointwise and edge_integral_le. Generic edge bound, for any
real M and D. -/
theorem edge_all (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α M D : ℝ,
        (∫ t in windowY X ε - 2 * H..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := edge_pointwise A hA
  refine ⟨B0, hB0, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε hε'
  refine ⟨2 * C, X0, by linarith, hX0, ?_⟩
  intro X H hX hlo hhi α M D
  have hH : 0 ≤ H := H_nonneg X H B ε (hX0.trans hX) hlo
  refine (edge_integral_le _ _ _ H _ hH
    (fun t ht1 ht2 => k X H hX hlo hhi α M D t ht1 ht2)).trans (le_of_eq ?_)
  ring

/-- PROVED from edge_pointwise. Exact statement of SecondDyadicCases1122.case1_edge. -/
theorem case1_edge : type_of% @SecondDyadicCases1122.case1_edge := fun A hA => by
  obtain ⟨B0, hB0, h⟩ := edge_all A hA
  refine ⟨B0, hB0, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε hε'
  exact ⟨C, X0, hC, hX0, fun X H hX hlo hhi α _ _ _ _ _ _ M _ _ _ D _ _ =>
    k X H hX hlo hhi α M D⟩

/-- PROVED from edge_pointwise. Exact statement of SecondDyadicCases1122.case2_edge. -/
theorem case2_edge : type_of% @SecondDyadicCases1122.case2_edge := fun A hA => by
  obtain ⟨B0, hB0, h⟩ := edge_all A hA
  refine ⟨B0, hB0, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε hε'
  exact ⟨C, X0, hC, hX0, fun X H hX hlo hhi α _ _ _ _ _ _ M _ _ _ D _ _ =>
    k X H hX hlo hhi α M D⟩

/-- PROVED from edge_pointwise. Exact statement of SecondDyadicCase3Split1122.case3_edge. -/
theorem case3_edge : type_of% @SecondDyadicCase3Split1122.case3_edge := fun A hA => by
  obtain ⟨B0, hB0, h⟩ := edge_all A hA
  refine ⟨B0, hB0, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε hε'
  exact ⟨C, X0, hC, hX0, fun X H hX hlo hhi α _ _ _ _ _ _ M _ _ _ D _ =>
    k X H hX hlo hhi α M D⟩

example : type_of% @SecondDyadicCases1122.case1_edge := case1_edge
example : type_of% @SecondDyadicCases1122.case2_edge := case2_edge
example : type_of% @SecondDyadicCase3Split1122.case3_edge := case3_edge

end LeanLab.KumchevLiu2007.SecondDyadicEdges1123

#print axioms LeanLab.KumchevLiu2007.SecondDyadicEdges1123.edge_integral_le
#print axioms LeanLab.KumchevLiu2007.SecondDyadicEdges1123.H_nonneg
#print axioms LeanLab.KumchevLiu2007.SecondDyadicEdges1123.edge_all
#print axioms LeanLab.KumchevLiu2007.SecondDyadicEdges1123.case1_edge
#print axioms LeanLab.KumchevLiu2007.SecondDyadicEdges1123.case2_edge
#print axioms LeanLab.KumchevLiu2007.SecondDyadicEdges1123.case3_edge
