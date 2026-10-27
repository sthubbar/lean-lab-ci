/-
P0081 Liu and Tsang 2005, Theorem 1.1 (i): the A^{15/2} form of the prime sizes.
From `abs aⱼ pⱼ ≤ C (abs n + A abs(a₁a₂a₃)^{5/2} log^{26} A)` and
`abs(a₁a₂a₃) ≤ abs aⱼ A²` we get `A abs(a₁a₂a₃)^{5/2} ≤ abs aⱼ A^{15/2}`, so
`abs aⱼ pⱼ ≤ C abs aⱼ (abs n + A^{15/2} log^{26} A)` and `pⱼ ≤ C (abs n + A^{15/2} log^{26} A)`.
CONDITIONAL ON the cited `Theorem11i`; the step itself is proved.

AI-written Lean code, Claude, 2026-10-18, cloud session 20261018T1650Z-cloud4;
built, one fix in key_rpow, by cloud session 20261018T1720Z-cloud5, log build/20261018T1720Z-cloud5.log.
Checked only by the Lean kernel. Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.LiuTsang2005.Statements

namespace LeanLab.LiuTsang2005
open Real

/-- The real inequality behind the step: if `0 ≤ x ≤ A`, `0 < A` and `0 ≤ P ≤ x A²`,
then `A P^{5/2} ≤ x A^{15/2}`. -/
theorem key_rpow {x A P : ℝ} (hx : 0 ≤ x) (hxA : x ≤ A) (hA : 0 < A) (hP : 0 ≤ P)
    (hPA : P ≤ x * A ^ 2) : A * P ^ (5 / 2 : ℝ) ≤ x * A ^ (15 / 2 : ℝ) := by
  have h1 : P ^ (5 / 2 : ℝ) ≤ (x * A ^ 2) ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow hP hPA (by norm_num)
  have h2 : (x * A ^ 2) ^ (5 / 2 : ℝ) = x ^ (5 / 2 : ℝ) * A ^ (5 : ℝ) := by
    rw [Real.mul_rpow hx (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hA.le]
    norm_num
  have h3 : x ^ (5 / 2 : ℝ) = x * x ^ (3 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num]
    rcases hx.eq_or_lt with h | h
    · subst h; rw [Real.zero_rpow (by norm_num), zero_mul]
    · rw [Real.rpow_add h, Real.rpow_one]
  have h4 : x ^ (3 / 2 : ℝ) ≤ A ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hx hxA (by norm_num)
  have h5 : A * (x * A ^ (3 / 2 : ℝ) * A ^ (5 : ℝ)) = x * A ^ (15 / 2 : ℝ) := by
    have : A ^ (15 / 2 : ℝ) = A ^ (1 : ℝ) * A ^ (3 / 2 : ℝ) * A ^ (5 : ℝ) := by
      rw [← Real.rpow_add hA, ← Real.rpow_add hA]; norm_num
    rw [this, Real.rpow_one]; ring
  calc A * P ^ (5 / 2 : ℝ) ≤ A * (x ^ (5 / 2 : ℝ) * A ^ (5 : ℝ)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hA.le
    _ = A * (x * x ^ (3 / 2 : ℝ) * A ^ (5 : ℝ)) := by rw [h3]
    _ ≤ A * (x * A ^ (3 / 2 : ℝ) * A ^ (5 : ℝ)) := by gcongr
    _ = x * A ^ (15 / 2 : ℝ) := h5

/-- `abs(a₁a₂a₃) ≤ abs aⱼ · A²` for `j = 1`; the other two follow by symmetry of the product. -/
theorem prod_le₁ (a₁ a₂ a₃ : ℤ) :
    |((a₁ * a₂ * a₃ : ℤ) : ℝ)| ≤ |(a₁ : ℝ)| * Abig a₁ a₂ a₃ ^ 2 := by
  have hA : 0 ≤ Abig a₁ a₂ a₃ := by linarith [two_le_Abig a₁ a₂ a₃]
  push_cast
  rw [abs_mul, abs_mul, pow_two, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (abs_le_Abig₂ _ _ _) (abs_le_Abig₃ _ _ _)
    (abs_nonneg _) hA) (abs_nonneg _)

theorem prod_le₂ (a₁ a₂ a₃ : ℤ) :
    |((a₁ * a₂ * a₃ : ℤ) : ℝ)| ≤ |(a₂ : ℝ)| * Abig a₁ a₂ a₃ ^ 2 := by
  have hA : 0 ≤ Abig a₁ a₂ a₃ := by linarith [two_le_Abig a₁ a₂ a₃]
  push_cast
  rw [abs_mul, abs_mul, pow_two]
  calc |(a₁ : ℝ)| * |(a₂ : ℝ)| * |(a₃ : ℝ)| = |(a₂ : ℝ)| * (|(a₁ : ℝ)| * |(a₃ : ℝ)|) := by ring
    _ ≤ |(a₂ : ℝ)| * (Abig a₁ a₂ a₃ * Abig a₁ a₂ a₃) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (abs_le_Abig₁ _ _ _) (abs_le_Abig₃ _ _ _)
        (abs_nonneg _) hA) (abs_nonneg _)

theorem prod_le₃ (a₁ a₂ a₃ : ℤ) :
    |((a₁ * a₂ * a₃ : ℤ) : ℝ)| ≤ |(a₃ : ℝ)| * Abig a₁ a₂ a₃ ^ 2 := by
  have hA : 0 ≤ Abig a₁ a₂ a₃ := by linarith [two_le_Abig a₁ a₂ a₃]
  push_cast
  rw [abs_mul, abs_mul, pow_two]
  calc |(a₁ : ℝ)| * |(a₂ : ℝ)| * |(a₃ : ℝ)| = |(a₃ : ℝ)| * (|(a₁ : ℝ)| * |(a₂ : ℝ)|) := by ring
    _ ≤ |(a₃ : ℝ)| * (Abig a₁ a₂ a₃ * Abig a₁ a₂ a₃) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (abs_le_Abig₁ _ _ _) (abs_le_Abig₂ _ _ _)
        (abs_nonneg _) hA) (abs_nonneg _)

/-- The bound term divided by `abs aⱼ`: `Bnd ≤ abs aⱼ · A^{15/2} log^{26} A`, any `j`. -/
theorem Bnd_le_of {a₁ a₂ a₃ : ℤ} {x : ℝ} (hx : 0 ≤ x) (hxA : x ≤ Abig a₁ a₂ a₃)
    (hP : |((a₁ * a₂ * a₃ : ℤ) : ℝ)| ≤ x * Abig a₁ a₂ a₃ ^ 2) :
    Bnd a₁ a₂ a₃ ≤ x * (Abig a₁ a₂ a₃ ^ (15 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26) := by
  set A := Abig a₁ a₂ a₃
  have hA : 2 ≤ A := two_le_Abig a₁ a₂ a₃
  have hlog : 0 ≤ Real.log A ^ 26 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ A); positivity
  have := key_rpow hx hxA (by linarith) (abs_nonneg _) hP
  unfold Bnd
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right this hlog

/-- From `abs a · p ≤ C (abs n + B)`, `B ≤ abs a · M`, `1 ≤ abs a`: `p ≤ C (abs n + M)`. -/
theorem div_step {a p C N B M : ℝ} (ha : 1 ≤ a) (hC : 0 < C) (hN : 0 ≤ N)
    (h : a * p ≤ C * (N + B)) (hB : B ≤ a * M) : p ≤ C * (N + M) := by
  have ha0 : 0 < a := by linarith
  have h1 : a * p ≤ a * (C * (N + M)) := by
    calc a * p ≤ C * (N + B) := h
      _ ≤ C * (N + a * M) := by gcongr
      _ ≤ C * (a * N + a * M) := by gcongr; nlinarith
      _ = a * (C * (N + M)) := by ring
  exact le_of_mul_le_mul_left h1 ha0

theorem one_le_abs_of_ne {a : ℤ} (h : a ≠ 0) : (1 : ℝ) ≤ |(a : ℝ)| := by
  have : (1 : ℤ) ≤ |a| := Int.one_le_abs h
  exact_mod_cast (show ((1 : ℤ) : ℝ) ≤ ((|a| : ℤ) : ℝ) by exact_mod_cast this)

/-- Theorem 1.1 (i) in the `A^{15/2}` form: each prime satisfies
`pⱼ ≤ C (abs n + A^{15/2} log^{26} A)`. CONDITIONAL ON `Theorem11i` as a hypothesis. -/
theorem theorem11i_primes (h : Theorem11i) :
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
  obtain ⟨n1, n2, n3, -⟩ := hc
  refine ⟨p₁, p₂, p₃, h1, h2, h3, he, ?_, ?_, ?_⟩
  · exact div_step (one_le_abs_of_ne n1) hC (abs_nonneg _) b1
      (Bnd_le_of (abs_nonneg _) (abs_le_Abig₁ _ _ _) (prod_le₁ _ _ _))
  · exact div_step (one_le_abs_of_ne n2) hC (abs_nonneg _) b2
      (Bnd_le_of (abs_nonneg _) (abs_le_Abig₂ _ _ _) (prod_le₂ _ _ _))
  · exact div_step (one_le_abs_of_ne n3) hC (abs_nonneg _) b3
      (Bnd_le_of (abs_nonneg _) (abs_le_Abig₃ _ _ _) (prod_le₃ _ _ _))

end LeanLab.LiuTsang2005
