import Mathlib
import LeanLab.HelfgottMajor.PVCases1122

/-!
# Polya finite Fourier expansion of an initial segment sum

Frolenkov, arXiv 1107.0381, display 12 with display 13: for χ primitive modulo q,
`τ(χ⁻¹) · ∑_{m<K} χ(m) = ∑_h χ⁻¹(h) · ∑_{m<K} e(m h / q)`, the inner sum a finite geometric sum.
This is an exact finite identity, obtained from `PV420Split1122.gauss_twist` applied to χ⁻¹ by
swapping finite sums.

The identity alone does not make the LEAF `PVCases1122.even_truncated` strictly smaller: the
remaining step, the truncation of the h sum at Pomerance's H with his explicit error, Frolenkov
displays 15, 16, 14 and 17, is the whole content of that LEAF. So no assembly and no new LEAF is
added here, only the PROVED identity. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVEvenPolya1122

open Finset

/-- The inverse of a primitive Dirichlet character is primitive. PROVED. -/
theorem isPrimitive_inv {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    (χ⁻¹).IsPrimitive := by
  rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
  exact hχ

/-- Frolenkov display 12 with display 13, summed over an initial segment: for χ primitive mod q,
`τ(χ⁻¹) ∑_{m<K} χ(m) = ∑_h χ⁻¹(h) ∑_{m<K} e(m h/q)`. PROVED. -/
theorem polya_initial_segment {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (K : ℕ) :
    gaussSum χ⁻¹ ZMod.stdAddChar * ∑ m ∈ range K, χ (m : ZMod q) =
      ∑ h : ZMod q, χ⁻¹ h * ∑ m ∈ range K, ZMod.stdAddChar ((m : ZMod q) * h) := by
  have hχ' := isPrimitive_inv hχ
  calc gaussSum χ⁻¹ ZMod.stdAddChar * ∑ m ∈ range K, χ (m : ZMod q)
      = ∑ m ∈ range K, χ⁻¹⁻¹ (m : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by
        rw [mul_comm, sum_mul, inv_inv]
    _ = ∑ m ∈ range K, ∑ x : ZMod q, χ⁻¹ x * ZMod.stdAddChar ((m : ZMod q) * x) :=
        sum_congr rfl fun m _ => LeanLab.HelfgottMajor.PV420Split1122.gauss_twist hχ' _
    _ = ∑ h : ZMod q, χ⁻¹ h * ∑ m ∈ range K, ZMod.stdAddChar ((m : ZMod q) * h) := by
        rw [sum_comm]
        simp_rw [mul_sum]

/-- The inner sum is geometric: `e(m h/q) = e(h/q)^m`. PROVED. -/
theorem inner_geometric {q : ℕ} [NeZero q] (h : ZMod q) (K : ℕ) :
    ∑ m ∈ range K, ZMod.stdAddChar ((m : ZMod q) * h) =
      ∑ m ∈ range K, ZMod.stdAddChar h ^ m := by
  refine sum_congr rfl fun m _ => ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

end LeanLab.HelfgottMajor.PVEvenPolya1122

#print axioms LeanLab.HelfgottMajor.PVEvenPolya1122.isPrimitive_inv
#print axioms LeanLab.HelfgottMajor.PVEvenPolya1122.polya_initial_segment
#print axioms LeanLab.HelfgottMajor.PVEvenPolya1122.inner_geometric
