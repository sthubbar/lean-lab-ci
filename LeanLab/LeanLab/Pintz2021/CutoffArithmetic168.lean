import LeanLab.Pintz2021.Truncation168
import LeanLab.Pintz2021.QuasiTask53

/-!
The actual character cutoff implies the quasi divisibility of P0054 page 7 display 2.14.
This connects the real maximum to the proved task53 integer ratio lemmas.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.CutoffArithmetic168

open State1581 DecompJ281

/-- A real reduced denominator bound gives the common factorial multiple. -/
theorem real_ratio_quasidivisor {r m : ℕ} (hr : 0 < r) {U : ℝ}
    (h : (r : ℝ) / (Nat.gcd m r : ℝ) ≤ U) : r ∣ (⌈U⌉₊).factorial * m := by
  have hg : Nat.gcd r m ≠ 0 := (Nat.gcd_pos_of_pos_left m hr).ne'
  have heq : ((r / Nat.gcd r m : ℕ) : ℝ) = (r : ℝ) / (Nat.gcd m r : ℝ) := by
    rw [Nat.cast_div (Nat.gcd_dvd_left r m) (by exact_mod_cast hg), Nat.gcd_comm]
  apply QuasiTask53.quasi_divisor_of_ratio_le hr
  exact_mod_cast (heq.trans_le (h.trans (Nat.le_ceil U)))

/-- Bounded actual character cutoff gives both quasi divisors and bounded conductor. -/
theorem cutoff_quasidivisors (z w : ExcPair) (m : ℕ) {U : ℝ}
    (h : UCutoff z w m ≤ U) :
    z.r ∣ (⌈U⌉₊).factorial * m ∧ w.r ∣ (⌈U⌉₊).factorial * m ∧
      (lift z (Nat.lcm z.r w.r) * (lift w (Nat.lcm z.r w.r))⁻¹).conductor ≤ ⌈U⌉₊ := by
  simp only [UCutoff, max_le_iff] at h
  have hz : 0 < z.r := by
    have := z.hr
    exact Nat.pos_of_ne_zero (NeZero.ne z.r)
  have hw : 0 < w.r := by
    have := w.hr
    exact Nat.pos_of_ne_zero (NeZero.ne w.r)
  exact ⟨real_ratio_quasidivisor hz h.2.1.1,
    real_ratio_quasidivisor hw h.2.1.2, by exact_mod_cast h.2.2.trans (Nat.le_ceil U)⟩

/-- The pair lcm is a quasi divisor with the same factorial multiplier. -/
theorem cutoff_lcm_divides (z w : ExcPair) (m : ℕ) {U : ℝ}
    (h : UCutoff z w m ≤ U) : Nat.lcm z.r w.r ∣ (⌈U⌉₊).factorial * m := by
  obtain ⟨hz, hw, _⟩ := cutoff_quasidivisors z w m h
  exact Nat.lcm_dvd hz hw

/-- Every retained pair satisfies the common quasi divisibility condition. -/
theorem retained_lcm_divides {E : Finset ExcPair} {P U : ℝ} {m : ℕ}
    {z w : ExcPair} (h : (z, w) ∈ Truncation168.retainedPairs E P U m) :
    Nat.lcm z.r w.r ∣ (⌈U⌉₊).factorial * m :=
  cutoff_lcm_divides z w m (Truncation168.mem_retainedPairs.mp h).2.2.2.2.2

end LeanLab.Pintz2021.CutoffArithmetic168

#print axioms LeanLab.Pintz2021.CutoffArithmetic168.real_ratio_quasidivisor
#print axioms LeanLab.Pintz2021.CutoffArithmetic168.cutoff_quasidivisors
#print axioms LeanLab.Pintz2021.CutoffArithmetic168.cutoff_lcm_divides
#print axioms LeanLab.Pintz2021.CutoffArithmetic168.retained_lcm_divides
