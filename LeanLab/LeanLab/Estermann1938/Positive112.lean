import LeanLab.Estermann1938.Series112
import LeanLab.ExceptionalSet.MVMajorSing

/-!
Estermann 1938, P0091, page 313, display 49.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Estermann1938.Positive112
open scoped BigOperators
open Filter Topology Series112 Ramanujan112

/-- The singular series has a convergent real sum at every positive frequency, display 44. -/
theorem singular_real_summable (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun q : ℕ => factor q * (c q m).re) := by
  have h := (Complex.hasSum_re (singular_summable m hm).hasSum).summable
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

/-- The terms of display 44 agree with the lab's proved binary singular series factors. -/
theorem term_eq_f2 {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    factor q * (c q m).re = LeanLab.ExceptionalSet.MVMajor.f2 m q := by
  rw [c_eq_ramanujan hq, LeanLab.ExceptionalSet.MVMajor.f2_apply hq]
  simp only [Complex.ofReal_re]
  unfold factor
  ring

/-- The finite truncations used in the lab converge to the exact S in display 44. -/
theorem partial_tendsto (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun P : ℕ => ∑ q ∈ Finset.Icc 1 P, LeanLab.ExceptionalSet.MVMajor.f2 m q)
      atTop (𝓝 (S m)) := by
  have ht := (singular_real_summable m hm).hasSum.tendsto_sum_nat
  have he (P : ℕ) :
      (∑ q ∈ Finset.Icc 1 P, LeanLab.ExceptionalSet.MVMajor.f2 m q) =
      ∑ q ∈ Finset.range (P + 1), factor q * (c q m).re := by
    have hset : Finset.range (P + 1) = insert 0 (Finset.Icc 1 P) := by
      ext q
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    simp only [factor, Nat.totient_zero, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
      div_zero, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro q hq
    exact (term_eq_f2 (Finset.mem_Icc.mp hq).1 m).symm
  have hcomp := ht.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun P : ℕ => ∑ q ∈ Finset.range (P + 1), factor q * (c q m).re)
    atTop (𝓝 (S m)) at hcomp
  apply hcomp.congr'
  exact Eventually.of_forall (fun P => (he P).symm)

/-- Display 49, page 313: the singular series of every positive even integer is at least one. -/
theorem display49 (m : ℕ) (hm : Even m) (hm0 : m ≠ 0) : 1 ≤ S m := by
  have hsqrt : Tendsto (fun P : ℕ => Real.sqrt (P : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun P : ℕ =>
      Real.exp 8 * LeanLab.ExceptionalSet.MVMajor.G m / Real.sqrt (P : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  have hlo : Tendsto (fun P : ℕ =>
      1 - Real.exp 8 * LeanLab.ExceptionalSet.MVMajor.G m / Real.sqrt (P : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hz
  apply le_of_tendsto_of_tendsto hlo (partial_tendsto m (by omega))
  filter_upwards [eventually_ge_atTop 2] with P hP
  exact LeanLab.ExceptionalSet.MVMajor.sing2_ge hm hm0 hP

#print axioms singular_real_summable
#print axioms term_eq_f2
#print axioms partial_tendsto
#print axioms display49

end LeanLab.Estermann1938.Positive112
