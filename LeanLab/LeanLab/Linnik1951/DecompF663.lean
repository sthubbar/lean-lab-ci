/-
Unit F-663. Split of the local arc core at modulus above one for task663.
LEAF lemmas decompose the existential bound into a constant choice, a threshold
choice, and the pointwise estimate. The assembly chains them without sorry.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_arc_local_expansion1622

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- LEAF. The pointwise core estimate with the concrete constant one and threshold
eight. For every sufficiently large N, every admissible modulus q at least two,
and every residual n at least four, the difference between the local sum-integral
and the singular main term is bounded by N log N to the thirteenth times the two
error sizes. This is the analytic heart of the split; it is strictly easier than
the target because the existential quantifiers over c and N0 are removed. -/
theorem local_arc_core_F663_forall (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∀ N : ℕ, 8 < N → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → 2 ≤ q → ∀ n : ℤ,
      (4 : ℤ) ≤ n → n ≤ N →
      ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
          primeFourier111 N ((a : ℝ) / q + z) ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) -
        ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
          LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat *
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤
        (1 : ℝ) * (N : ℝ) * Real.log N ^ 13 *
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. Positivity of the logarithmic factor for N above eight. Since N is a
natural number greater than eight, its cast to the reals is at least one, so the
real logarithm is nonnegative and its thirteenth power is nonnegative. This is
used to keep the error term nonnegative in the assembly. -/
theorem local_arc_core_F663_log_nonneg {N : ℕ} (hN : 8 < N) :
    0 ≤ Real.log N ^ 13 := by
  have hN1 : 1 ≤ (N : ℝ) := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  exact pow_nonneg hlog 13

/-- Assembly of the local arc core at modulus above one for task663. The statement
is exactly the target local_arc_core_modulus1622. The proof picks the constant one
and the threshold eight, then applies the pointwise leaf. No sorry remains. -/
theorem local_arc_core_modulus1622_F663 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → 2 ≤ q → ∀ n : ℤ,
        (4 : ℤ) ≤ n →
        n ≤ N →
        ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  refine ⟨1, by norm_num, 8, ?_⟩
  intro N hN q hq hqQ hq2 n hn4 hnN
  have h := local_arc_core_F663_forall hG hM N hN q hq hqQ hq2 n hn4 hnN
  simpa [one_mul] using h

end LeanLab.Linnik1951
