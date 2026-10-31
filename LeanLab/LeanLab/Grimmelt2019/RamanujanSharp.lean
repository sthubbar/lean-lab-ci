/-
AI wrote this Lean code for CODEX task03.
P0074, page 13, the finite character error in the Ramanujan computation.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.UnitMass

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Enumerating units by their least nonnegative representatives gives the reduced residues. -/
theorem sum_units_val {q : ℕ} [NeZero q] (f : ℕ → ℝ) :
    ∑ u : (ZMod q)ˣ, f (u : ZMod q).val =
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), f r := by
  classical
  refine Finset.sum_bij (fun u _ => (u : ZMod q).val) ?_ ?_ ?_ ?_
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _),
      ZMod.val_coe_unit_coprime u⟩
  · intro u hu v hv hval
    apply Units.ext
    exact ZMod.val_injective q hval
  · intro r hr
    obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hr
    let u := ZMod.unitOfCoprime r hc
    refine ⟨u, Finset.mem_univ _, ?_⟩
    change (r : ZMod q).val = r
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
  · intro u hu
    rfl

/-- The reduced-residue Ramanujan convolution identity written as a sum over units. -/
theorem sum_units_ram {q : ℕ} [NeZero q] (n : ℤ) :
    ∑ u : (ZMod q)ˣ, ram q (n - (u : ZMod q).val) =
      (ArithmeticFunction.moebius q : ℝ) * ram q n := by
  rw [sum_units_val (fun r : ℕ => ram q (n - (r : ℤ)))]
  exact sum_ram_sub_nat (Nat.pos_of_ne_zero (NeZero.ne q)) n

/-- Rough support lets the unit residue masses recover the full Ramanujan window sum. -/
theorem unitMass_ram_sum {q : ℕ} [NeZero q] (W : Finset ℤ) (ω : ℤ → ℝ) (n : ℤ)
    (hrough : ∀ m ∈ W, Int.gcd m q ≠ 1 → ω m = 0) :
    ∑ u : (ZMod q)ˣ, unitMass W ω u * (ram q (n - (u : ZMod q).val) : ℂ) =
      ((∑ m ∈ W, ω m * ram q (n - m) : ℝ) : ℂ) := by
  classical
  simp_rw [unitMass, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hu : IsUnit (m : ZMod q)
  · let u : (ZMod q)ˣ := hu.unit
    have huc : (u : ZMod q) = (m : ZMod q) := hu.unit_spec
    have heq : ∀ v : (ZMod q)ˣ, ((m : ZMod q) = (v : ZMod q)) ↔ v = u := by
      intro v
      rw [← huc, Units.val_inj]
      exact eq_comm
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, huc,
      Complex.ofReal_mul]
    rw [ZMod.val_intCast, ← ram_emod q n m]
  · have heq : ∀ u : (ZMod q)ˣ, (m : ZMod q) ≠ (u : ZMod q) := by
      intro u heq
      exact hu (heq.symm ▸ u.isUnit)
    have hg : Int.gcd m q ≠ 1 := by
      intro hg
      apply hu
      rw [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm,
        Int.isCoprime_iff_gcd_eq_one]
      exact hg
    simp only [heq, ite_false, Finset.sum_const_zero, hrough m hm hg,
      Complex.ofReal_zero, zero_mul]

#print axioms sum_units_val
#print axioms sum_units_ram
#print axioms unitMass_ram_sum
end LeanLab.Grimmelt2019.MainTerm
