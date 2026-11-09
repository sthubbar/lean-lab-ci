import LeanLab.ExceptionalSet.OddKernel467
import LeanLab.ExceptionalSet.Fejer467
import LeanLab.ExceptionalSet.BG2026MinorCont
import LeanLab.ExceptionalSet.Decomp404a

/-!
P0082 page366 display28 and page367 final identity.
Only odd primes occur once P is at least two.
Their square has no odd Fourier coefficient.
This gives the exact major and minor coefficient relation used in section6.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.OddCoefficient467
open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.U1539 (Sp eC R1 majorArcs hcheck)

/-- P0082 page366 display28. R2 is the Fourier coefficient of the minor
arc indicator times the square of the prime sum on one period. -/
noncomputable def minorCoefficient (P X : ℝ) (m : ℤ) : ℂ :=
  hcheck ((majorArcs P X)ᶜ.indicator (fun α => Sp P X α ^ 2)) m

/-- P0082 page366 before display28. The full prime square has zero
Fourier coefficient at an odd integer when the prime range excludes two. -/
theorem prime_square_odd_coefficient (P X : ℝ) (hP : 2 ≤ P) (m : ℤ) (hm : Odd m) :
    hcheck (fun α => Sp P X α ^ 2) m = 0 := by
  classical
  let s := (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  have he (α : ℝ) : Sp P X α ^ 2 * eC (-(α * m)) =
      ∑ p ∈ s, ∑ q ∈ s, ((Real.log p : ℂ) * (Real.log q : ℂ)) *
        BG2026.eC ((((p : ℤ) + q - m : ℤ) : ℝ) * α) := by
    rw [PrimeKernel264.Sp_sq, Finset.product_eq_sprod, sum_product, sum_mul]
    apply sum_congr rfl
    intro p hp
    rw [sum_mul]
    apply sum_congr rfl
    intro q hq
    change ((Real.log p : ℂ) * (Real.log q : ℂ)) *
      eC (α * ((p + q : ℕ) : ℝ)) * eC (-(α * m)) =
        ((Real.log p : ℂ) * (Real.log q : ℂ)) * eC ((((p : ℤ) + q - m : ℤ) : ℝ) * α)
    rw [mul_assoc, ← Fejer467.phase_add]
    congr 2
    push_cast
    ring
  unfold hcheck
  simp_rw [he]
  rw [BG2026.integral_double_sum]
  apply sum_eq_zero
  intro p hp
  apply sum_eq_zero
  intro q hq
  have hp' := (mem_filter.mp hp).2
  have hq' := (mem_filter.mp hq).2
  have hpf := (mem_Ioc.mp (mem_filter.mp hp).1).1
  have hqf := (mem_Ioc.mp (mem_filter.mp hq).1).1
  have hfloor : 2 ≤ ⌊P⌋₊ := Nat.le_floor hP
  have hpodd : Odd p := Nat.odd_iff.mpr (hp'.eq_two_or_odd.resolve_left (by omega))
  have hqodd : Odd q := Nat.odd_iff.mpr (hq'.eq_two_or_odd.resolve_left (by omega))
  have hne : (p : ℤ) + q - m ≠ 0 := by
    intro hf
    have hsum : Even (((p + q : ℕ) : ℤ)) :=
      (Int.even_coe_nat _).mpr (hpodd.add_odd hqodd)
    have hmeq : m = ((p + q : ℕ) : ℤ) := by push_cast; omega
    apply (Int.not_even_iff_odd.mpr hm)
    rwa [hmeq]
  simp only [hne, ite_false, mul_zero]

/-- P0082 page366 display28. The minor arc indicator times the prime
square is integrable on one period. -/
theorem minor_intervalIntegrable (P X : ℝ) :
    IntervalIntegrable ((majorArcs P X)ᶜ.indicator (fun α => Sp P X α ^ 2)) volume 0 1 := by
  have hc : Continuous (fun α : ℝ => Sp P X α ^ 2) := by unfold Sp eC; fun_prop
  exact ⟨(hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
    (PrimeKernel264.measurableSet_majorArcs P X).compl, by simp⟩

/-- P0082 page366 display28. Major and minor coefficients add to the
full coefficient because the two indicators partition one period. -/
theorem major_add_minor_coefficient (P X : ℝ) (m : ℤ) :
    R1 P X m + minorCoefficient P X m = hcheck (fun α => Sp P X α ^ 2) m := by
  classical
  rw [← Decomp404a.major_hcheck]
  unfold minorCoefficient hcheck
  have hc : Continuous (fun α : ℝ => eC (-(α * m))) := by unfold eC; fun_prop
  rw [← intervalIntegral.integral_add
    ((Decomp404a.major_intervalIntegrable P X).mul_continuousOn hc.continuousOn)
    ((minor_intervalIntegrable P X).mul_continuousOn hc.continuousOn)]
  apply intervalIntegral.integral_congr
  intro α hα
  by_cases ha : α ∈ majorArcs P X <;> simp [ha]

/-- P0082 page366 display28. At an odd integer, the minor coefficient
is the negative of the major coefficient. -/
theorem odd_minor_eq_neg_major (P X : ℝ) (hP : 2 ≤ P) (m : ℤ) (hm : Odd m) :
    minorCoefficient P X m = -R1 P X m := by
  have hh := major_add_minor_coefficient P X m
  rw [prime_square_odd_coefficient P X hP m hm] at hh
  linear_combination hh

/-- P0082 page367 final display. The shifted kernel isolates the upper
adjacent minor coefficient with the printed trapezoid weight. -/
theorem weighted_minor_identity (P X Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α in (majorArcs P X)ᶜ,
      Sp P X α ^ 2 * OddKernel467.evenKernel Δ α * eC (-(α * v))) =
        (KernelTransform264.weight Δ (2 * Int.fract v - 1) : ℂ) *
          minorCoefficient P X (⌊v⌋ + 1) := by
  classical
  let h : ℝ → ℂ := (majorArcs P X)ᶜ.indicator (fun α => Sp P X α ^ 2)
  have hper : Function.Periodic h 1 := by
    intro α
    have hm : α + 1 ∈ majorArcs P X ↔ α ∈ majorArcs P X :=
      Iff.of_eq (Decomp371a.majorArcs_periodic P X α)
    simp only [h, Set.indicator_apply, Set.mem_compl_iff, hm, Decomp371a.Sp_periodic P X α]
  have hh := OddKernel467.weighted_adjacent_identity h hper (minor_intervalIntegrable P X)
    Δ v hΔ hΔ1
  have he : (fun α : ℝ => h α * OddKernel467.evenKernel Δ α * eC (-(α * v))) =
      (majorArcs P X)ᶜ.indicator (fun α =>
        Sp P X α ^ 2 * OddKernel467.evenKernel Δ α * eC (-(α * v))) := by
    ext α
    by_cases ha : α ∈ majorArcs P X <;> simp [h, ha]
  rw [he, integral_indicator (PrimeKernel264.measurableSet_majorArcs P X).compl] at hh
  exact hh

/-- P0082 page367 final display and page368 boundary paragraph. Away
from the fractional boundary, an odd upper neighbor gives minus its major coefficient. -/
theorem plateau_odd_major_identity (P X Δ v : ℝ) (hP : 2 ≤ P)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hm : Odd (⌊v⌋ + 1))
    (hleft : Δ / 2 ≤ Int.fract v) (hright : Int.fract v ≤ 1 - Δ / 2) :
    (∫ α in (majorArcs P X)ᶜ,
      Sp P X α ^ 2 * OddKernel467.evenKernel Δ α * eC (-(α * v))) =
        -R1 P X (⌊v⌋ + 1) := by
  rw [weighted_minor_identity P X Δ v hΔ hΔ1]
  have hp : |2 * Int.fract v - 1| ≤ 1 - Δ := by rw [abs_le]; constructor <;> linarith
  rw [KernelTransform264.weight_one hΔ hΔ1 hp]
  simp only [Complex.ofReal_one, one_mul]
  exact odd_minor_eq_neg_major P X hP _ hm

end LeanLab.ExceptionalSet.OddCoefficient467
