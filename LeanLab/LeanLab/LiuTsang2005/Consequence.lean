/-
P0081 J. Liu, K.-M. Tsang 2005, the consequence of Theorem 1.1 (i) that the paper draws:
the prime solutions satisfy `pⱼ ≪ abs n + A^{15/2} log^{26} A`, from
`abs aⱼ pⱼ ≪ abs n + A abs(a₁a₂a₃)^{5/2} log^{26} A` and `abs(a₁a₂a₃) ≤ abs aⱼ A²`.

* `rpow_key`: for `0 ≤ x ≤ A`, `0 ≤ q ≤ A²`: `A (x q)^{5/2} ≤ x A^{15/2}`.
* `Bnd_le_mul`: `Bnd a₁ a₂ a₃ ≤ abs aⱼ · A^{15/2} log^{26} A` for each `j`.
* `theorem11i_simple`: Theorem 1.1 (i) implies the `A^{15/2}` form, CONDITIONAL ON (i) only.

AI-written Lean code, Claude, PC run 20261020T0403Z-27388, unit U-1155. Checked only by the
Lean kernel. Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.LiuTsang2005.Statements

namespace LeanLab.LiuTsang2005
open Real

/-- `A (x q)^{5/2} ≤ x A^{15/2}` for `0 ≤ x ≤ A` and `0 ≤ q ≤ A²`. -/
theorem rpow_key {A x q : ℝ} (hx : 0 ≤ x) (hxA : x ≤ A) (hq : 0 ≤ q) (hqA : q ≤ A ^ 2) :
    A * (x * q) ^ (5 / 2 : ℝ) ≤ x * A ^ (15 / 2 : ℝ) := by
  have hA : 0 ≤ A := le_trans hx hxA
  rcases eq_or_lt_of_le hx with h0 | hxpos
  · subst h0; simp [zero_rpow (by norm_num : (5 / 2 : ℝ) ≠ 0)]
  have hApos : 0 < A := lt_of_lt_of_le hxpos hxA
  rw [mul_rpow hx hq]
  have h1 : x ^ (5 / 2 : ℝ) = x * x ^ (3 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, rpow_add hxpos, rpow_one]
  have h2 : x ^ (3 / 2 : ℝ) ≤ A ^ (3 / 2 : ℝ) := rpow_le_rpow hx hxA (by norm_num)
  have h3 : q ^ (5 / 2 : ℝ) ≤ A ^ (5 : ℝ) := by
    calc q ^ (5 / 2 : ℝ) ≤ (A ^ 2) ^ (5 / 2 : ℝ) := rpow_le_rpow hq hqA (by norm_num)
      _ = A ^ (5 : ℝ) := by
          rw [← rpow_natCast, ← rpow_mul hA]; norm_num
  have h4 : A ^ (15 / 2 : ℝ) = A * (A ^ (3 / 2 : ℝ) * A ^ (5 : ℝ)) := by
    rw [← rpow_add hApos, show (15 / 2 : ℝ) = 1 + (3 / 2 + 5) by norm_num,
      rpow_add hApos, rpow_one]
  rw [h1, h4]
  have hx32 : 0 ≤ x ^ (3 / 2 : ℝ) := rpow_nonneg hx _
  have hq52 : 0 ≤ q ^ (5 / 2 : ℝ) := rpow_nonneg hq _
  have hA32 : 0 ≤ A ^ (3 / 2 : ℝ) := rpow_nonneg hA _
  have := mul_le_mul h2 h3 hq52 hA32
  have := mul_le_mul_of_nonneg_left this (mul_nonneg hA hx)
  nlinarith [this]

theorem log_pow_nonneg_Abig (a₁ a₂ a₃ : ℤ) : 0 ≤ Real.log (Abig a₁ a₂ a₃) ^ 26 := by
  have := Real.log_nonneg (by linarith [two_le_Abig a₁ a₂ a₃] : (1 : ℝ) ≤ Abig a₁ a₂ a₃)
  positivity

/-- The bound, with the product split as `aⱼ` times the other two. -/
theorem Bnd_le_of_split (a₁ a₂ a₃ : ℤ) {x q : ℝ} (hx : 0 ≤ x) (hxA : x ≤ Abig a₁ a₂ a₃)
    (hq : 0 ≤ q) (hqA : q ≤ Abig a₁ a₂ a₃ ^ 2) (hsplit : |((a₁ * a₂ * a₃ : ℤ) : ℝ)| = x * q) :
    Bnd a₁ a₂ a₃ ≤ x * (Abig a₁ a₂ a₃ ^ (15 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26) := by
  unfold Bnd
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (rpow_key hx hxA hq hqA) (log_pow_nonneg_Abig a₁ a₂ a₃)

theorem Bnd_le_mul₁ (a₁ a₂ a₃ : ℤ) :
    Bnd a₁ a₂ a₃ ≤ |(a₁ : ℝ)| * (Abig a₁ a₂ a₃ ^ (15 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26) := by
  have hA0 : 0 ≤ Abig a₁ a₂ a₃ := by linarith [two_le_Abig a₁ a₂ a₃]
  refine Bnd_le_of_split a₁ a₂ a₃ (abs_nonneg _) (abs_le_Abig₁ _ _ _)
    (q := |(a₂ : ℝ)| * |(a₃ : ℝ)|) (by positivity) ?_ ?_
  · rw [pow_two]
    exact mul_le_mul (abs_le_Abig₂ _ _ _) (abs_le_Abig₃ _ _ _) (abs_nonneg _) hA0
  · push_cast; rw [abs_mul, abs_mul]; ring

theorem Bnd_le_mul₂ (a₁ a₂ a₃ : ℤ) :
    Bnd a₁ a₂ a₃ ≤ |(a₂ : ℝ)| * (Abig a₁ a₂ a₃ ^ (15 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26) := by
  have hA0 : 0 ≤ Abig a₁ a₂ a₃ := by linarith [two_le_Abig a₁ a₂ a₃]
  refine Bnd_le_of_split a₁ a₂ a₃ (abs_nonneg _) (abs_le_Abig₂ _ _ _)
    (q := |(a₁ : ℝ)| * |(a₃ : ℝ)|) (by positivity) ?_ ?_
  · rw [pow_two]
    exact mul_le_mul (abs_le_Abig₁ _ _ _) (abs_le_Abig₃ _ _ _) (abs_nonneg _) hA0
  · push_cast; rw [abs_mul, abs_mul]; ring

theorem Bnd_le_mul₃ (a₁ a₂ a₃ : ℤ) :
    Bnd a₁ a₂ a₃ ≤ |(a₃ : ℝ)| * (Abig a₁ a₂ a₃ ^ (15 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26) := by
  have hA0 : 0 ≤ Abig a₁ a₂ a₃ := by linarith [two_le_Abig a₁ a₂ a₃]
  refine Bnd_le_of_split a₁ a₂ a₃ (abs_nonneg _) (abs_le_Abig₃ _ _ _)
    (q := |(a₁ : ℝ)| * |(a₂ : ℝ)|) (by positivity) ?_ ?_
  · rw [pow_two]
    exact mul_le_mul (abs_le_Abig₁ _ _ _) (abs_le_Abig₂ _ _ _) (abs_nonneg _) hA0
  · push_cast; rw [abs_mul, abs_mul]; ring

/-- From `abs a · p ≤ C (abs n + abs a · M)` with `a` a nonzero integer: `p ≤ C (abs n + M)`. -/
theorem p_le_of {a : ℤ} (ha : a ≠ 0) {C p n M : ℝ} (hC : 0 < C) (hn : 0 ≤ n) (hM : 0 ≤ M)
    (h : |(a : ℝ)| * p ≤ C * (n + |(a : ℝ)| * M)) : p ≤ C * (n + M) := by
  have ha1 : (1 : ℝ) ≤ |(a : ℝ)| := by
    have : (1 : ℤ) ≤ |a| := Int.one_le_abs ha
    exact_mod_cast this
  have hpos : 0 < |(a : ℝ)| := by linarith
  have key : |(a : ℝ)| * p ≤ |(a : ℝ)| * (C * (n + M)) := by
    have : C * (n + |(a : ℝ)| * M) ≤ |(a : ℝ)| * (C * (n + M)) := by
      nlinarith [mul_nonneg (sub_nonneg.2 ha1) (mul_nonneg hC.le hn)]
    linarith
  exact le_of_mul_le_mul_left key hpos

/-- **The consequence of Theorem 1.1 (i)**: prime solutions with
`pⱼ ≤ C (abs n + A^{15/2} log^{26} A)`. CONDITIONAL ON Liu-Tsang Theorem 1.1 (i). -/
theorem theorem11i_simple (h : Theorem11i) :
    ∃ C : ℝ, 0 < C ∧ ∀ a₁ a₂ a₃ n : ℤ, Cond a₁ a₂ a₃ n → ¬ SameSign a₁ a₂ a₃ →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ a₁ * p₁ + a₂ * p₂ + a₃ * p₃ = n ∧
        (p₁ : ℝ) ≤ C * (|(n : ℝ)| +
          Abig a₁ a₂ a₃ ^ (15 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26) ∧
        (p₂ : ℝ) ≤ C * (|(n : ℝ)| +
          Abig a₁ a₂ a₃ ^ (15 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26) ∧
        (p₃ : ℝ) ≤ C * (|(n : ℝ)| +
          Abig a₁ a₂ a₃ ^ (15 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26) := by
  obtain ⟨C, hC, hT⟩ := h
  refine ⟨C, hC, fun a₁ a₂ a₃ n hc hs => ?_⟩
  obtain ⟨p₁, p₂, p₃, h1, h2, h3, he, b1, b2, b3⟩ := hT a₁ a₂ a₃ n hc hs
  have hA0 : 0 ≤ Abig a₁ a₂ a₃ := by linarith [two_le_Abig a₁ a₂ a₃]
  have hM : 0 ≤ Abig a₁ a₂ a₃ ^ (15 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26 :=
    mul_nonneg (rpow_nonneg hA0 _) (log_pow_nonneg_Abig a₁ a₂ a₃)
  refine ⟨p₁, p₂, p₃, h1, h2, h3, he, ?_, ?_, ?_⟩
  · refine p_le_of hc.1 hC (abs_nonneg _) hM (le_trans b1 ?_)
    exact mul_le_mul_of_nonneg_left (by linarith [Bnd_le_mul₁ a₁ a₂ a₃]) hC.le
  · refine p_le_of hc.2.1 hC (abs_nonneg _) hM (le_trans b2 ?_)
    exact mul_le_mul_of_nonneg_left (by linarith [Bnd_le_mul₂ a₁ a₂ a₃]) hC.le
  · refine p_le_of hc.2.2.1 hC (abs_nonneg _) hM (le_trans b3 ?_)
    exact mul_le_mul_of_nonneg_left (by linarith [Bnd_le_mul₃ a₁ a₂ a₃]) hC.le

/-- Vacuity of `rpow_key`'s hypotheses: `x = 2`, `q = 3`, `A = 2` meet them. -/
example : (0 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 ∧ (0 : ℝ) ≤ 3 ∧ (3 : ℝ) ≤ 2 ^ 2 := by norm_num

#print axioms rpow_key
#print axioms Bnd_le_mul₁
#print axioms Bnd_le_mul₂
#print axioms Bnd_le_mul₃
#print axioms p_le_of
#print axioms theorem11i_simple

end LeanLab.LiuTsang2005
