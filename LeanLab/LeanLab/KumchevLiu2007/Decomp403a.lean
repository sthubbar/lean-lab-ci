/-
Three-square orthogonality from page 13 display 45 and property v.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp342h

namespace LeanLab.KumchevLiu2007.Task403a

open Real Complex U1534 Task129b Task129c
open scoped BigOperators

/-- Page 13 display 45. A3 is periodic in n with period q. -/
theorem A3_periodic (q : ℕ) : Function.Periodic (fun n : ℕ => Task129c.A3 n q) q := by
  intro n
  by_cases hq : q = 0
  · subst q
    rfl
  letI : NeZero q := ⟨hq⟩
  simp only [Task342h.A3_zmod_formula, Nat.cast_add, ZMod.natCast_self, add_zero]

/-- Page 13 property v. Three-square coefficients at distinct moduli are orthogonal.
The zero based full period equals the printed period by periodicity. -/
theorem A3_orthogonal (q r : ℕ) (hqr : q ≠ r) :
    ∑ n ∈ Finset.range (q * r), Task129c.A3 n q * Task129c.A3 n r = 0 := by
  by_cases hq : q = 0
  · subst q; simp
  by_cases hr : r = 0
  · subst r; simp
  have hN : q * r ≠ 0 := Nat.mul_ne_zero hq hr
  have : NeZero (q * r) := ⟨hN⟩
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have sum_range (f : ZMod (q * r) → ℂ) :
      ∑ n ∈ Finset.range (q * r), f (n : ZMod (q * r)) = ∑ n : ZMod (q * r), f n := by
    apply Finset.sum_bij (s := Finset.range (q*r))
      (t := (Finset.univ : Finset (ZMod (q*r)))) (fun a _ => (a : ZMod (q*r)))
    · intro a ha; exact Finset.mem_univ _
    · intro a ha b hb hab
      have h := congrArg ZMod.val hab
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
    · intro a ha
      exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro a ha; rfl
  have cross (a b : ℕ) (ha : a.Coprime q) (hb : b.Coprime r) :
      ∑ n ∈ Finset.range (q*r), ee (-((a*n : ℕ) : ℝ)/q) * ee (-((b*n : ℕ) : ℝ)/r) = 0 := by
    have hfreq : (-((a*r+b*q : ℕ) : ZMod (q*r))) ≠ 0 := by
      intro h
      have hd := (ZMod.natCast_eq_zero_iff (a*r+b*q) (q*r)).mp (neg_eq_zero.mp h)
      have hqd : q ∣ a*r+b*q := dvd_trans (dvd_mul_right q r) hd
      have hrd : r ∣ a*r+b*q := dvd_trans (dvd_mul_left r q) hd
      have hqd' : q ∣ a*r := (Nat.dvd_add_iff_left (dvd_mul_left q b)).mpr hqd
      have hrd' : r ∣ b*q := (Nat.dvd_add_iff_right (dvd_mul_left r a)).mpr hrd
      exact hqr (Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left hqd')
        (hb.symm.dvd_of_dvd_mul_left hrd'))
    have heq (n : ℕ) : ee (-((a*n : ℕ) : ℝ)/q) * ee (-((b*n : ℕ) : ℝ)/r) =
        ZMod.stdAddChar ((n : ZMod (q*r)) * (-((a*r+b*q : ℕ) : ZMod (q*r)))) := by
      have hcast : (n : ZMod (q*r)) * (-((a*r+b*q : ℕ) : ZMod (q*r))) =
          (((-((n*(a*r+b*q) : ℕ) : ℤ)) : ℤ) : ZMod (q*r)) := by push_cast; ring
      rw [hcast, ZMod.stdAddChar_coe]
      unfold ee
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    simp_rw [heq]
    rw [sum_range (fun n => ZMod.stdAddChar (n * (-((a*r+b*q : ℕ) : ZMod (q*r)))))]
    have hs := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := q*r))
      (-((a*r+b*q : ℕ) : ZMod (q*r))) (ZMod.isPrimitive_stdAddChar (q*r))
    simpa only [ite_eq_right hfreq, Nat.cast_zero] using hs
  unfold Task129c.A3
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a ha
  have hca := (Finset.mem_filter.mp ha).2
  have hcb := (Finset.mem_filter.mp hb).2
  have hs := cross a b hca hcb
  have heq (n : ℕ) :
      (1 / (Nat.totient q : ℂ)^3 *
        (gaussS q a ^ 3 * ee (-((a*n : ℕ) : ℝ)/q))) *
      (1 / (Nat.totient r : ℂ)^3 *
        (gaussS r b ^ 3 * ee (-((b*n : ℕ) : ℝ)/r))) =
      ((1 / (Nat.totient q : ℂ)^3 * gaussS q a ^ 3) *
        (1 / (Nat.totient r : ℂ)^3 * gaussS r b ^ 3)) *
        (ee (-((a*n : ℕ) : ℝ)/q) * ee (-((b*n : ℕ) : ℝ)/r)) := by ring
  simp_rw [heq]
  rw [← Finset.mul_sum, hs, mul_zero]


/-- Page 13 property v with the printed indexing from one through q times r. -/
theorem A3_orthogonal_Icc (q r : ℕ) (hqr : q ≠ r) :
    ∑ n ∈ Finset.Icc 1 (q * r), A3 n q * A3 n r = 0 := by
  have hq : A3 (q * r) q = A3 0 q := by
    simpa [Nat.mul_comm] using (A3_periodic q).nat_mul r 0
  have hr : A3 (q * r) r = A3 0 r := by
    simpa using (A3_periodic r).nat_mul q 0
  have hi : Finset.Icc 1 (q * r) = Finset.Ico 1 (q * r + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hi, Finset.sum_Ico_eq_sub _ (by omega), Finset.sum_range_succ,
    Finset.sum_range_one, A3_orthogonal q r hqr, hq, hr]
  ring

end LeanLab.KumchevLiu2007.Task403a
