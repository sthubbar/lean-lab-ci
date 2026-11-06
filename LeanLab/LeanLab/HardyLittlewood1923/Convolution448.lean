import LeanLab.HardyLittlewood1923.TheoremBRec
import LeanLab.HardyLittlewood1923.Decomp276b
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
AI wrote this Lean code for CODEX task448.
P0004 page 7 equations 1.46 and 1.47.
Goldbach is OPEN.
-/
namespace LeanLab.HardyLittlewood1923.Convolution448
open Finset Finset.HasAntidiagonal
/-- P0004 page 7 equations 1.46 and 1.47. The empty tuple contributes one at zero and zero at every other sum. -/
theorem count_zero (n : ℕ) : nur 0 n = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n; simp [nur]
  · simp [nur, hn, Ne.symm hn]


/-- P0004 page 7 equations 1.46 and 1.47. The damped prime coefficient used in the Cauchy product. -/
noncomputable def primeTerm (z : ℂ) (m : ℕ) : ℂ :=
  if m.Prime then (Real.log m : ℂ) * Complex.exp (-(m : ℂ) * z) else 0
/-- P0004 page 7 equations 1.46 and 1.47. The damped weighted ordered tuple coefficient. -/
noncomputable def countTerm (r : ℕ) (z : ℂ) (m : ℕ) : ℂ :=
  (nur r m : ℂ) * Complex.exp (-(m : ℂ) * z)

/-- P0004 page 7 equations 1.46 and 1.47. The existing tuple recurrence identifies each finite Cauchy product coefficient. -/
theorem count_convolution (r m : ℕ) (z : ℂ) :
    (∑ kl ∈ antidiagonal m, primeTerm z kl.1 * countTerm r z kl.2) =
      countTerm (r + 1) z m := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => primeTerm z a * countTerm r z b) m]
  unfold countTerm
  rw [nur_succ, sum_filter, Complex.ofReal_sum, sum_mul]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by have := mem_range.mp hk; omega
  by_cases hp : k.Prime
  · simp only [primeTerm, if_pos hp, Complex.ofReal_mul]
    rw [show (Real.log k : ℂ) * Complex.exp (-(k : ℂ) * z) *
          ((nur r (m - k) : ℂ) * Complex.exp (-((m - k : ℕ) : ℂ) * z)) =
        ((Real.log k : ℂ) * (nur r (m - k) : ℂ)) *
          (Complex.exp (-(k : ℂ) * z) * Complex.exp (-((m - k : ℕ) : ℂ) * z)) by ring,
      ← Complex.exp_add]
    congr 2
    rw [Nat.cast_sub hkm]
    ring
  · simp [primeTerm, hp]

/-- P0004 page 7 equations 1.46 and 1.47. Absolute convergence and the finite recurrence prove the power series identity. -/
theorem count_series_power (z : ℂ) (hs : Summable (fun m => ‖primeTerm z m‖)) (r : ℕ) :
    Summable (fun m => ‖countTerm r z m‖) ∧
      (∑' m, primeTerm z m) ^ r = ∑' m, countTerm r z m := by
  induction r with
  | zero =>
    have hf : countTerm 0 z = fun m : ℕ => if m = 0 then (1 : ℂ) else 0 := by
      funext m
      by_cases hm : m = 0 <;> simp [countTerm, count_zero, hm]
    rw [hf]
    exact ⟨(hasSum_ite_eq 0 (1 : ℂ)).summable.norm, by
      simpa using (hasSum_ite_eq 0 (1 : ℂ)).tsum_eq.symm⟩
  | succ r ih =>
    obtain ⟨hi, he⟩ := ih
    have hconv := summable_norm_sum_mul_antidiagonal_of_summable_norm hs hi
    have hcauchy := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hi
    refine ⟨?_, ?_⟩
    · simpa only [count_convolution] using hconv
    · rw [pow_succ', he]
      exact hcauchy.trans (tsum_congr fun m => count_convolution r m z)
/-- P0004 page 7 equation 1.47. The actual prime series power counts ordered prime tuples. -/
theorem primeSeries_power {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    Decomp276b.primeSeries z ^ r =
      ∑' m : ℕ, (nur r m : ℂ) * Complex.exp (-(m : ℂ) * z) := by
  have hs : Summable (fun m => ‖primeTerm z m‖) := by
    simpa only [primeTerm] using (Decomp276b.primeSeries_summable hz).norm
  simpa only [Decomp276b.primeSeries, primeTerm, countTerm] using
    (count_series_power z hs r).2

/-- P0004 page 7 equation 1.47. The ordered tuple series is absolutely convergent inside the circle. -/
theorem nur_series_summable {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    Summable (fun m : ℕ => ‖(nur r m : ℂ) * Complex.exp (-(m : ℂ) * z)‖) := by
  have hs : Summable (fun m => ‖primeTerm z m‖) := by
    simpa only [primeTerm] using (Decomp276b.primeSeries_summable hz).norm
  simpa only [countTerm] using (count_series_power z hs r).1

#print axioms count_zero
#print axioms count_convolution
#print axioms count_series_power
#print axioms primeSeries_power
#print axioms nur_series_summable
end LeanLab.HardyLittlewood1923.Convolution448
