import Mathlib
import LeanLab.ExceptionalSet.BG2026MinorCont
import LeanLab.ExceptionalSet.PrimeKernel264

/-!
Upstream supply of display (28) of P0082 for `DecompJ200.leaf_major_odd_moment`.
Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, https://doi.org/10.5802/aif.1621, page 366.

Page 366, start of section 6: for odd `m`, `∫_0^1 S(α)² e(-αm) dα = 0`, since every prime
counted exceeds `P ≥ 2` and is odd, so `R₁(m) = -R₂(m)` with
`R₂(m) = ∫_{𝔫 ∩ [0,1]} S(α)² e(-αm) dα`, display (28).

`R2` is defined here. `odd_full_period_zero` and `odd_major_eq_neg_minor` are copies of the
proved theorems of the same names in `Parity385`, which imports `DecompJ200` transitively, so
`DecompJ200` cannot import it. The proofs are unchanged.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.OddSupplyJ200

open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp eC R1 majorArcs)

/-- `R₂(m) = ∫_{𝔫 ∩ [0,1]} S(α)² e(-αm) dα`, the minor arc part of the unit period,
P0082 page 366, display (28), with `𝔫` the complement of the major arcs `𝔑` of page 357. -/
noncomputable def R2 (P X : ℝ) (m : ℤ) : ℂ :=
  ∫ α in (majorArcs P X)ᶜ ∩ Icc (0 : ℝ) 1, Sp P X α ^ 2 * eC (-(α * m))

/-- The full period prime square coefficient vanishes at every odd integer.
Source: P0082 page 366, the equality immediately before display (28).
Copy of `Parity385.odd_full_period_zero`. -/
theorem odd_full_period_zero (P X : ℝ) (hP : 2 ≤ P) (m : ℤ) (hm : Odd m) :
    (∫ α in (0 : ℝ)..1, Sp P X α ^ 2 * eC (-(α * m))) = 0 := by
  let s := (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  have he (a b : ℝ) : eC a * eC b = BG2026.eC (a + b) := by
    unfold eC BG2026.eC
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hx (α : ℝ) : Sp P X α ^ 2 * eC (-(α * m)) =
      ∑ p ∈ s, ∑ q ∈ s, ((Real.log p : ℂ) * Real.log q) *
        BG2026.eC ((((p : ℤ) + q - m : ℤ) : ℝ) * α) := by
    rw [PrimeKernel264.Sp_sq, Finset.product_eq_sprod, Finset.sum_product]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    calc
      _ = ((Real.log p : ℂ) * Real.log q) *
          (eC (α * ((p + q : ℕ) : ℝ)) * eC (-(α * m))) := by ring
      _ = _ := by rw [he]; congr 2; push_cast; ring
  simp_rw [hx]
  rw [BG2026.integral_double_sum]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  have hfloor : 2 ≤ ⌊P⌋₊ := Nat.le_floor (by norm_num; exact hP)
  have hp2 : p ≠ 2 := by
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    omega
  have hq2 : q ≠ 2 := by
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
    omega
  have hpo : Odd p := Nat.odd_iff.mpr ((Finset.mem_filter.mp hp).2.eq_two_or_odd.resolve_left hp2)
  have hqo : Odd q := Nat.odd_iff.mpr ((Finset.mem_filter.mp hq).2.eq_two_or_odd.resolve_left hq2)
  have hev : Even ((p : ℤ) + q) := by exact_mod_cast hpo.add_odd hqo
  have hne : (p : ℤ) + q - m ≠ 0 := by
    intro hh
    have heq : (p : ℤ) + q = m := by linarith
    rw [heq] at hev
    exact (Int.not_even_iff_odd.mpr hm) hev
  simp only [hne, ite_false, mul_zero]

/-- At odd frequency the major coefficient is the negative minor coefficient.
Source: P0082 page 366 display (28), with both integrals over the unit interval.
Copy of `Parity385.odd_major_eq_neg_minor`. -/
theorem odd_major_eq_neg_minor (P X : ℝ) (hP : 2 ≤ P) (m : ℤ) (hm : Odd m) :
    R1 P X m = -(∫ α in (majorArcs P X)ᶜ ∩ Icc (0 : ℝ) 1,
      Sp P X α ^ 2 * eC (-(α * m))) := by
  have hc : Continuous (fun α : ℝ => Sp P X α ^ 2 * eC (-(α * m))) := by
    unfold Sp eC
    fun_prop
  have hfull : (∫ α in Icc (0 : ℝ) 1, Sp P X α ^ 2 * eC (-(α * m))) = 0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact odd_full_period_zero P X hP m hm
  have hf : IntegrableOn (fun α : ℝ => Sp P X α ^ 2 * eC (-(α * m))) (Icc (0 : ℝ) 1) :=
    hc.integrableOn_Icc
  have hi := integral_inter_add_sdiff (s := Icc (0 : ℝ) 1) (t := majorArcs P X)
    (PrimeKernel264.measurableSet_majorArcs P X) hf
  have hsd : Icc (0 : ℝ) 1 \ majorArcs P X = (majorArcs P X)ᶜ ∩ Icc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  rw [Set.inter_comm (Icc (0 : ℝ) 1) (majorArcs P X), hsd, hfull] at hi
  exact eq_neg_of_add_eq_zero_left hi

/-- Display (28), P0082 page 366, in the form used for the odd moment: for odd `m` and
`P ≥ 2`, `R₁(m) = -R₂(m)`. -/
theorem R1_eq_neg_R2 (P X : ℝ) (hP : 2 ≤ P) (m : ℤ) (hm : Odd m) :
    R1 P X m = -R2 P X m :=
  odd_major_eq_neg_minor P X hP m hm

/-- Hence `|R₁(m)|² = |R₂(m)|²` for odd `m`, P0082 page 366. -/
theorem norm_sq_R1_eq (P X : ℝ) (hP : 2 ≤ P) (m : ℤ) (hm : Odd m) :
    ‖R1 P X m‖ ^ 2 = ‖R2 P X m‖ ^ 2 := by
  rw [R1_eq_neg_R2 P X hP m hm, norm_neg]

end LeanLab.ExceptionalSet.OddSupplyJ200
