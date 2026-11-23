import Mathlib
import LeanLab.HelfgottMajor.PVEvenPolya1122

/-!
Route burst S68, burst-20261122, tag odd-truncated, second file.
An ingredient of the LEAF `PVOddTrunc1122.odd_cot_bound`: the cotangent form of the geometric
denominator in the finite Polya identity, Frolenkov arXiv 1107.0381 display 12 with display 13,
1/(e^(iθ) - 1) = -1/2 - (i/2) cot(θ/2), used at θ = 2π h/q, and the geometric sum over an
interval written with it. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVOddCot1122

open Complex
open scoped Real

/-- The cotangent form of 1/(e^(iθ) - 1), for sin(θ/2) ≠ 0. PROVED. -/
theorem inv_exp_sub_one (θ : ℝ) (hs : Real.sin (θ / 2) ≠ 0) :
    1 / (exp (θ * I) - 1) = -1 / 2 - I / 2 * (Real.cot (θ / 2) : ℂ) := by
  set c := Real.cos (θ / 2)
  set s := Real.sin (θ / 2)
  have hcs : c ^ 2 + s ^ 2 = 1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq _
  have hw : exp (θ * I) = ((c : ℂ) + s * I) ^ 2 := by
    have : (θ : ℂ) * I = ((θ / 2 : ℝ) : ℂ) * I + ((θ / 2 : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this, exp_add, ← sq, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hcot : (Real.cot (θ / 2) : ℂ) = c / s := by
    simp only [c, s, Real.cot_eq_cos_div_sin, ofReal_div]
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hden : ((c : ℂ) + s * I) ^ 2 - 1 = 2 * s * I * (c + s * I) := by
    have hcs' : (c : ℂ) ^ 2 = 1 - s ^ 2 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hcs; push_cast at this; linear_combination this
    linear_combination hcs' - (s : ℂ) ^ 2 * I_sq
  have hne : (c : ℂ) + s * I ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact hs this
  rw [hw, hden, hcot]
  have hcs' : (c : ℂ) ^ 2 + s ^ 2 = 1 := by exact_mod_cast hcs
  have hk : (c : ℂ) / s * s = c := div_mul_cancel₀ _ hsc
  rw [eq_comm, eq_div_iff (by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hsc) I_ne_zero) hne)]
  linear_combination hcs' + (-I * c * s - s ^ 2 - c ^ 2) * I_sq + (-I ^ 2 * (c + s * I)) * hk

/-- The geometric sum over an interval, for z ≠ 1:
`∑_{m=M}^{N} z^m = (z^(N+1) - z^M)/(z - 1)` when M ≤ N + 1. PROVED. -/
theorem geom_interval {z : ℂ} (hz : z ≠ 1) {M N : ℕ} (h : M ≤ N + 1) :
    ∑ m ∈ Finset.Icc M N, z ^ m = (z ^ (N + 1) - z ^ M) / (z - 1) := by
  have hI : Finset.Icc M N = Finset.Ico M (N + 1) := by ext x; simp
  rw [hI, geom_sum_Ico hz h]

/-- The cotangent form at e(h/q) for h ≠ 0 in ZMod q:
1/(e(h/q) - 1) = -1/2 - (i/2) cot(π h/q), with h read as its least residue. PROVED. -/
theorem inv_stdAddChar_sub_one {q : ℕ} [NeZero q] {h : ZMod q} (hh : h ≠ 0) :
    1 / (ZMod.stdAddChar h - 1) = -1 / 2 - I / 2 * (Real.cot (π * h.val / q) : ℂ) := by
  have hv : 0 < h.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero h).mpr hh)
  have hvq : h.val < q := ZMod.val_lt h
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q from Nat.pos_of_ne_zero (NeZero.ne q))
  have hvr : (0 : ℝ) < h.val := by exact_mod_cast hv
  have hvqr : (h.val : ℝ) < q := by exact_mod_cast hvq
  have hs : Real.sin (2 * π * h.val / q / 2) ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [show 2 * π * (h.val : ℝ) / q / 2 = π * (h.val / q) by ring]
      have : (h.val : ℝ) / q < 1 := (div_lt_one hq).mpr hvqr
      nlinarith [Real.pi_pos]
  have e1 : ZMod.stdAddChar h = exp (((2 * π * h.val / q : ℝ) : ℂ) * I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]; congr 1; push_cast; ring
  rw [e1, inv_exp_sub_one _ hs]
  congr 3; ring_nf

/-- The finite Polya identity for an interval sum in cotangent form, Frolenkov arXiv 1107.0381
display 12 with display 13 and 1/(e(h/q) - 1) = -1/2 - (i/2) cot(π h/q): for χ primitive mod q,
q ≠ 1 and M ≤ N + 1,
τ(χ⁻¹) ∑_{M ≤ m ≤ N} χ(m) = -(1/2) τ(χ⁻¹) (χ(N+1) - χ(M))
  - (i/2) ∑_h χ⁻¹(h) cot(π h/q) (e(h/q)^(N+1) - e(h/q)^M). PROVED. -/
theorem polya_interval_cot {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) {M N : ℕ} (hMN : M ≤ N + 1) :
    gaussSum χ⁻¹ ZMod.stdAddChar * ∑ m ∈ Finset.Icc M N, χ (m : ZMod q) =
      -(1 / 2) * gaussSum χ⁻¹ ZMod.stdAddChar * (χ ((N + 1 : ℕ) : ZMod q) - χ (M : ZMod q)) -
      I / 2 * ∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M) := by
  have hχ' := LeanLab.HelfgottMajor.PVEvenPolya1122.isPrimitive_inv hχ
  have tw : ∀ n : ℕ, χ (n : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar =
      ∑ h : ZMod q, χ⁻¹ h * ZMod.stdAddChar h ^ n := by
    intro n
    have := LeanLab.HelfgottMajor.PV420Split1122.gauss_twist hχ' (n : ZMod q)
    rw [inv_inv] at this
    rw [this]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have lhs : gaussSum χ⁻¹ ZMod.stdAddChar * ∑ m ∈ Finset.Icc M N, χ (m : ZMod q) =
      ∑ h : ZMod q, χ⁻¹ h * ∑ m ∈ Finset.Icc M N, ZMod.stdAddChar h ^ m := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm, tw m]
  have term : ∀ h : ZMod q, χ⁻¹ h * ∑ m ∈ Finset.Icc M N, ZMod.stdAddChar h ^ m =
      -(1 / 2) * (χ⁻¹ h * ZMod.stdAddChar h ^ (N + 1) - χ⁻¹ h * ZMod.stdAddChar h ^ M) -
      I / 2 * (χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)) := by
    intro h
    by_cases hh : h = 0
    · subst hh
      rw [DirichletCharacter.map_zero' _ hq]; ring
    · have hne : ZMod.stdAddChar h ≠ 1 := by
        intro h1
        exact hh (ZMod.injective_stdAddChar (h1.trans (AddChar.map_zero_eq_one _).symm))
      have hsub : ZMod.stdAddChar h - 1 ≠ 0 := sub_ne_zero.mpr hne
      rw [LeanLab.HelfgottMajor.PVOddCot1122.geom_interval hne hMN]
      have hc := inv_stdAddChar_sub_one (q := q) hh
      rw [div_eq_mul_one_div, hc]; ring
  rw [lhs, Finset.sum_congr rfl fun h _ => term h, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_sub_distrib, ← tw, ← tw]
  ring

end LeanLab.HelfgottMajor.PVOddCot1122

#print axioms LeanLab.HelfgottMajor.PVOddCot1122.inv_exp_sub_one
#print axioms LeanLab.HelfgottMajor.PVOddCot1122.geom_interval
#print axioms LeanLab.HelfgottMajor.PVOddCot1122.inv_stdAddChar_sub_one
#print axioms LeanLab.HelfgottMajor.PVOddCot1122.polya_interval_cot
