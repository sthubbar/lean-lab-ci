/-
Elementary rational arc separation for PP1993 pages 45 and 46.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
AI wrote the Lean code. Goldbach is open.
This file supplies geometry only. It asserts no analytic estimate.
-/
import LeanLab.Languasco2004.Decomp279b

namespace LeanLab.Languasco2004.ArcGeometry413
open Finset Real
noncomputable section

/-- Page 46 before display 14: distinct rational centres are separated
by the reciprocal product of their positive denominators. -/
theorem rational_separation (a q b r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hne : (a : ℝ) / q ≠ (b : ℝ) / r) :
    1 / ((q : ℝ) * r) ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  let d : ℤ := (a : ℤ) * r - (b : ℤ) * q
  have hd : d ≠ 0 := by
    intro hd
    apply hne
    apply (div_eq_div_iff hqp.ne' hrp.ne').mpr
    have hreal := congrArg (fun z : ℤ => (z : ℝ)) hd
    dsimp [d] at hreal
    push_cast at hreal
    linarith
  have hdone : (1 : ℝ) ≤ |(d : ℝ)| := by
    have hint : (1 : ℤ) ≤ |d| := by
      have hpos := abs_pos.mpr hd
      omega
    exact_mod_cast hint
  have hformula : (a : ℝ) / q - (b : ℝ) / r = (d : ℝ) / ((q : ℝ) * r) := by
    dsimp [d]
    push_cast
    field_simp
    <;> ring
  rw [hformula, abs_div, abs_of_pos (mul_pos hqp hrp)]
  exact div_le_div_of_nonneg_right hdone (mul_pos hqp hrp).le

/-- Page 45 display 7: reduced fractions with positive denominators
identify their numerator and denominator uniquely. -/
theorem reduced_centre_unique (a q b r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (haq : Nat.Coprime a q) (hbr : Nat.Coprime b r)
    (heq : (a : ℝ) / q = (b : ℝ) / r) : a = b ∧ q = r := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hx : a * r = b * q := by
    have hx := (div_eq_div_iff hqp.ne' hrp.ne').mp heq
    exact_mod_cast hx
  have hqr : q ∣ r := by
    apply haq.symm.dvd_mul_left.mp
    rw [hx]
    exact dvd_mul_left q b
  have hrq : r ∣ q := by
    apply hbr.symm.dvd_mul_left.mp
    rw [← hx]
    exact dvd_mul_left r a
  have hden : q = r := Nat.dvd_antisymm hqr hrq
  subst r
  exact ⟨mul_right_cancel₀ (Nat.ne_of_gt hq) hx, rfl⟩

/-- Page 46 before display 14: denominators at most Q give the
usual Farey separation by one over Q squared. -/
theorem bounded_denominator_separation (a q b r : ℕ) (Q : ℝ)
    (hq : 0 < q) (hr : 0 < r) (hqQ : (q : ℝ) ≤ Q) (hrQ : (r : ℝ) ≤ Q)
    (hne : (a : ℝ) / q ≠ (b : ℝ) / r) :
    1 / Q ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hQ : 0 < Q := hqp.trans_le hqQ
  have hprod : (q : ℝ) * r ≤ Q ^ 2 := by nlinarith [mul_le_mul hqQ hrQ hrp.le hQ.le]
  exact (one_div_le_one_div_of_le (mul_pos hqp hrp) hprod).trans
    (rational_separation a q b r hq hr hne)

/-- Page 45 display 7: rational arcs of a common radius are disjoint
when twice the radius is at most the Farey separation. -/
theorem common_radius_disjoint (a q b r : ℕ) (Q R : ℝ)
    (hq : 0 < q) (hr : 0 < r) (hqQ : (q : ℝ) ≤ Q) (hrQ : (r : ℝ) ≤ Q)
    (hne : (a : ℝ) / q ≠ (b : ℝ) / r) (hR : 2 * R ≤ 1 / Q ^ 2) :
    Disjoint {x : ℝ | |x - (a : ℝ) / q| < R}
      {x : ℝ | |x - (b : ℝ) / r| < R} := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hsep := bounded_denominator_separation a q b r Q hq hr hqQ hrQ hne
  have htri := abs_sub_le ((a : ℝ) / q) x ((b : ℝ) / r)
  rw [abs_sub_comm ((a : ℝ) / q) x] at htri
  change |x - (a : ℝ) / q| < R at hx
  change |x - (b : ℝ) / r| < R at hy
  linarith

#print axioms rational_separation
#print axioms reduced_centre_unique
#print axioms bounded_denominator_separation
#print axioms common_radius_disjoint
end
end LeanLab.Languasco2004.ArcGeometry413
