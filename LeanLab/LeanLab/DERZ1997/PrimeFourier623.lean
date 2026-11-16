import LeanLab.DERZ1997.Decomp136b
import LeanLab.Common.CircleOrth

/-!
The finite prime Fourier coefficient behind P0011 page 100.
This identifies the prime count exactly before estimating the prime-power error.
The positive-frequency convention reverses both exponential signs together.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.DERZ1997.PrimeFourier623
open Complex Finset
open Decomp136b LeanLab.CircleOrth

/-- The coefficient of N in the cube of the finite prime exponential sum is J of N.
P0011 page 100, the definition of J and the orthogonality display.
Every prime in a retained triple is at most N, so the finite prime support is exact.
No assertion about the von Mangoldt error term is made here.
-/
theorem weightedJ_fourier623 (N : ℕ) :
    (∫ α in (0 : ℝ)..1,
      LeanLab.CircleOrth.S
        (((range (N + 1)).filter Nat.Prime).map Nat.castEmbedding)
        (fun p : ℤ => (Real.log p.toNat : ℂ)) α ^ 3 * ee (-(N : ℝ) * α)) =
      (weightedJ N : ℂ) := by
  classical
  have hi := ternary_orth
    (((range (N + 1)).filter Nat.Prime).map Nat.castEmbedding)
    (fun p : ℤ => (Real.log p.toNat : ℂ)) (N : ℤ)
  simp only [Int.cast_natCast] at hi
  simp_rw [neg_mul]
  rw [hi]
  unfold weightedJ primeTriples
  push_cast
  simp only [Finset.sum_map, Nat.castEmbedding_apply, Int.toNat_natCast,
    Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  refine Finset.sum_congr rfl fun p hp => ?_
  by_cases hpp : p.Prime
  · simp only [hpp, ↓reduceIte]
    refine Finset.sum_congr rfl fun q hq => ?_
    by_cases hqp : q.Prime
    · simp only [hqp, ↓reduceIte]
      refine Finset.sum_congr rfl fun r hr => ?_
      by_cases hrp : r.Prime
      · have heq : ((p : ℤ) + (q : ℤ) + (r : ℤ) = (N : ℤ)) ↔ p + q + r = N := by omega
        simp [hrp, heq]
      · simp [hrp]
    · simp [hqp]
  · simp [hpp]

/-- A nonzero instance in the paper's working range. -/
example : (weightedJ 9 : ℂ) ≠ 0 := by
  have hpos : 0 < weightedJ 9 := by
    apply (weightedJ_pos_iff_nonempty 9).mpr
    refine ⟨(3, 3, 3), ?_⟩
    rw [mem_primeTriples]
    norm_num
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

end LeanLab.DERZ1997.PrimeFourier623
