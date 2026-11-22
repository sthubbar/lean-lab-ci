/-
MMS https://arxiv.org/abs/1610.02017v2 page 11 bottom display.
Uniform error control for approximation of the ordered Buchstab kernel.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp678a

namespace LeanLab.Ternary.MMS.Task678
open Finset

/-- The logarithmic prime atom mass on the ordered region is at most one.
Derived uniform budget for kernel approximation on MMS page 11.
The reciprocal modulus mass bound is reused with all coordinates at most one quarter. -/
theorem prime_log_triple_mass_le_one {x : ℝ} (hx : Real.exp 100 ≤ x) :
    (∑ p ∈ Task581.primeTriples x,
      ((Real.log p.1 / p.1) / Real.log x) *
      ((Real.log p.2.1 / p.2.1) / Real.log x) *
      ((Real.log p.2.2 / p.2.2) / Real.log x)) ≤ 1 := by
  have hx1 : 1 < x := by
    have := Real.add_one_le_exp (100 : ℝ)
    linarith
  have hmass : Task581.tripleMass x ≤ 64 := by
    apply (Task581.tripleMass_le_cube x).trans
    have hm := Task581.prime_window_mass_le hx
    have h0 : 0 ≤ ∑ p ∈
        (Ioc ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime,
          (1 : ℝ) / p := sum_nonneg fun p hp => by positivity
    have hh := pow_le_pow_left₀ h0 hm 3
    norm_num at hh ⊢
    exact hh
  calc
    _ ≤ ∑ p ∈ Task581.primeTriples x, (1 / 64 : ℝ) / Task581.tripleProduct p := by
      apply sum_le_sum
      intro p hp
      obtain ⟨ha, hab, hbc, hc⟩ := Task581.primeTriple_log_coordinates hx1 hp
      have ha0 : 0 ≤ Real.log p.1 / Real.log x := by linarith
      have hb0 : 0 ≤ Real.log p.2.1 / Real.log x := ha0.trans hab
      have hc0 : 0 ≤ Real.log p.2.2 / Real.log x := hb0.trans hbc
      have hprod : (Real.log p.1 / Real.log x) * (Real.log p.2.1 / Real.log x) *
          (Real.log p.2.2 / Real.log x) ≤ (1 / 4 : ℝ) * (1 / 4) * (1 / 4) :=
        mul_le_mul (mul_le_mul (hab.trans (hbc.trans hc)) (hbc.trans hc)
          hb0 (by norm_num)) hc hc0 (by norm_num)
      have he : ((Real.log p.1 / p.1) / Real.log x) *
          ((Real.log p.2.1 / p.2.1) / Real.log x) *
          ((Real.log p.2.2 / p.2.2) / Real.log x) =
          ((Real.log p.1 / Real.log x) * (Real.log p.2.1 / Real.log x) *
            (Real.log p.2.2 / Real.log x)) / Task581.tripleProduct p := by
        simp only [Task581.tripleProduct, Nat.cast_mul]
        ring
      rw [he]
      apply div_le_div_of_nonneg_right _ (by positivity)
      norm_num at hprod ⊢
      exact hprod
    _ = (1 / 64 : ℝ) * Task581.tripleMass x := by
      simp [Task581.tripleMass, div_eq_mul_inv, mul_sum]
    _ ≤ (1 / 64 : ℝ) * 64 := mul_le_mul_of_nonneg_left hmass (by norm_num)
    _ = 1 := by norm_num

/-- A uniform kernel error gives the same error after ordered prime quadrature.
Derived approximation step for MMS page 11 bottom display.
The supplied finite pointwise bound is explicit and contains no cited input. -/
theorem cofactorModel_step_error {x ε : ℝ} (hx : Real.exp 100 ≤ x) (hε : 0 ≤ ε)
    (G : ℕ × ℕ × ℕ → ℝ)
    (hG : ∀ p ∈ Task581.primeTriples x,
      |Task571.extendedKernel Task571.buchstabModel
        (Real.log p.1 / Real.log x) (Real.log p.2.1 / Real.log x)
        (Real.log p.2.2 / Real.log x) - G p| ≤ ε) :
    |(∑ p ∈ Task581.primeTriples x, Task581.cofactorModel x p) -
      ∑ p ∈ Task581.primeTriples x, G p *
        ((Real.log p.1 / p.1) / Real.log x) *
        ((Real.log p.2.1 / p.2.1) / Real.log x) *
        ((Real.log p.2.2 / p.2.2) / Real.log x)| ≤ ε := by
  have hx1 : 1 < x := by
    have := Real.add_one_le_exp (100 : ℝ)
    linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  let W : ℕ × ℕ × ℕ → ℝ := fun p =>
    ((Real.log p.1 / p.1) / Real.log x) *
    ((Real.log p.2.1 / p.2.1) / Real.log x) *
    ((Real.log p.2.2 / p.2.2) / Real.log x)
  have hw : ∀ p ∈ Task581.primeTriples x, 0 ≤ W p := by
    intro p hp
    have ht := (mem_filter.mp hp).2
    have hl₁ := Real.log_nonneg (show (1 : ℝ) ≤ p.1 by exact_mod_cast ht.1.one_lt.le)
    have hl₂ := Real.log_nonneg (show (1 : ℝ) ≤ p.2.1 by exact_mod_cast ht.2.1.one_lt.le)
    have hl₃ := Real.log_nonneg (show (1 : ℝ) ≤ p.2.2 by exact_mod_cast ht.2.2.1.one_lt.le)
    dsimp [W]
    positivity
  have he : ∀ p ∈ Task581.primeTriples x,
      |Task581.cofactorModel x p - G p *
        ((Real.log p.1 / p.1) / Real.log x) *
        ((Real.log p.2.1 / p.2.1) / Real.log x) *
        ((Real.log p.2.2 / p.2.2) / Real.log x)| ≤ ε * W p := by
    intro p hp
    rw [cofactorModel_eq_kernel_mass hx1 hp]
    have hid : Task571.extendedKernel Task571.buchstabModel
        (Real.log p.1 / Real.log x) (Real.log p.2.1 / Real.log x)
        (Real.log p.2.2 / Real.log x) *
        ((Real.log p.1 / p.1) / Real.log x) *
        ((Real.log p.2.1 / p.2.1) / Real.log x) *
        ((Real.log p.2.2 / p.2.2) / Real.log x) - G p *
        ((Real.log p.1 / p.1) / Real.log x) *
        ((Real.log p.2.1 / p.2.1) / Real.log x) *
        ((Real.log p.2.2 / p.2.2) / Real.log x) =
      (Task571.extendedKernel Task571.buchstabModel
        (Real.log p.1 / Real.log x) (Real.log p.2.1 / Real.log x)
        (Real.log p.2.2 / Real.log x) - G p) * W p := by dsimp [W]; ring
    rw [hid, abs_mul, abs_of_nonneg (hw p hp)]
    exact mul_le_mul_of_nonneg_right (hG p hp) (hw p hp)
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ Task581.primeTriples x, |Task581.cofactorModel x p - G p *
        ((Real.log p.1 / p.1) / Real.log x) *
        ((Real.log p.2.1 / p.2.1) / Real.log x) *
        ((Real.log p.2.2 / p.2.2) / Real.log x)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Task581.primeTriples x, ε * W p := sum_le_sum he
    _ = ε * ∑ p ∈ Task581.primeTriples x, W p := (mul_sum _ _ _).symm
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (prime_log_triple_mass_le_one hx) hε
    _ = ε := mul_one _

end LeanLab.Ternary.MMS.Task678
