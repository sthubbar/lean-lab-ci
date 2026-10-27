/-
P0023 Liu, Wang 2002, Acta Arith. 105, 133-175: the reduction of Theorem 1, p. 134, to the
named analytic inputs of the final chain, p. 174.
* `Icount N` is the weighted count (3.9) p. 145: the sum of `log p1 · log p2 · log p3` over
  primes `p1 + p2 + p3 = N` with `0.001 N ≤ pj ≤ N`.
* `isTernarySum_of_Icount_pos`: `Icount N > 0` gives a representation. PROVED.
* `liuWang_of_inputs`: if for every odd `N ≥ e^3100` the five inputs of `final_chain` hold
  with `I = Icount N`, then `TernaryAbove (e^3100)`, the lab's `Ternary.liuWang`.
  CONDITIONAL ON those inputs: Lemma 4.3, Lemmas 5.1 5.2 and Proposition 6.1, Parseval,
  Rosser-Schoenfeld 1975, and (3.10). Nothing analytic is proved here.
AI-written Lean code, Claude, 2026-10-21, session 20261021T0117Z-cloud55, unit U-6812.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Ternary.Statements
import LeanLab.LiuWang2002.Constants

namespace LeanLab.LiuWang2002.Reduction

open Real LeanLab.Ternary

/-- The triple `(a, b, N - a - b)` is counted in (3.9). -/
def Admissible (N a b : ℕ) : Prop :=
  a + b ≤ N ∧ a.Prime ∧ b.Prime ∧ (N - a - b).Prime ∧
    (0.001 : ℝ) * N ≤ a ∧ (0.001 : ℝ) * N ≤ b ∧ (0.001 : ℝ) * N ≤ ((N - a - b : ℕ) : ℝ)

open Classical in
/-- (3.9) p. 145: `I(N)`, the sum of `log p1 log p2 log p3` over admissible prime triples. -/
noncomputable def Icount (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
    if Admissible N a b then log a * log b * log ((N - a - b : ℕ) : ℝ) else 0

/-- A positive `I(N)` gives a representation of `N` as a sum of three primes. PROVED. -/
theorem isTernarySum_of_Icount_pos (N : ℕ) (h : 0 < Icount N) : IsTernarySum N := by
  by_contra hno
  have hz : Icount N = 0 := by
    unfold Icount
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    rintro ⟨hab, ha, hb, hc, -⟩
    exact hno ⟨a, b, N - a - b, ha, hb, hc, by omega⟩
  linarith

/-- Theorem 1 of Liu-Wang, p. 134, CONDITIONAL ON the named inputs of the final chain for
every odd `N ≥ e^3100`, with `L = log N`. The arithmetic and the counting are PROVED. -/
theorem liuWang_of_inputs
    (hin : ∀ N : ℕ, Odd N → exp 3100 ≤ (N : ℝ) →
      ∃ I1 J E M psiN : ℝ,
        I1 - J - E ≤ Icount N ∧
        E ≤ 3 * exp (3 / 2 * log N) * log N ^ 3 ∧
        0.5437 * (N : ℝ) ^ 2 ≤ I1 ∧
        J ≤ 0.5033 * N / log N * M ∧
        M ≤ log N * psiN ∧
        psiN ≤ 1.0012 * N) :
    TernaryAbove (exp 3100) := by
  intro N hodd hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (exp_pos _) hN
  have hL : (3100 : ℝ) ≤ log N := (le_log_iff_exp_le hNpos).mpr hN
  obtain ⟨I1, J, E, M, psiN, h1, h2, h3, h4, h5, h6⟩ := hin N hodd hN
  have he : exp (log N) = (N : ℝ) := exp_log hNpos
  refine isTernarySum_of_Icount_pos N ?_
  refine (Constants.final_chain (log N) (Icount N) I1 J E M psiN hL h1 h2 ?_ ?_ h5 ?_).2
  · rw [he]; exact h3
  · rw [he]; exact h4
  · rw [he]; exact h6

/-- Vacuity test: the hypothesis of `liuWang_of_inputs` is not contradictory on its face;
for a single `N` with `Icount N ≥ 0.5437 N^2` the inputs hold with `J = E = M = psiN = 0`.
PROVED. -/
theorem inputs_consistent (N : ℕ) (hN1 : 1 ≤ N) (hI : 0.5437 * (N : ℝ) ^ 2 ≤ Icount N) :
    ∃ I1 J E M psiN : ℝ,
      I1 - J - E ≤ Icount N ∧ E ≤ 3 * exp (3 / 2 * log N) * log N ^ 3 ∧
      0.5437 * (N : ℝ) ^ 2 ≤ I1 ∧ J ≤ 0.5033 * N / log N * M ∧ M ≤ log N * psiN ∧
      psiN ≤ 1.0012 * N := by
  have hl : 0 ≤ log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  refine ⟨Icount N, 0, 0, 0, 0, by simp, by positivity, hI, by simp, by simp, by positivity⟩

end LeanLab.LiuWang2002.Reduction

#print axioms LeanLab.LiuWang2002.Reduction.isTernarySum_of_Icount_pos
#print axioms LeanLab.LiuWang2002.Reduction.liuWang_of_inputs
#print axioms LeanLab.LiuWang2002.Reduction.inputs_consistent
