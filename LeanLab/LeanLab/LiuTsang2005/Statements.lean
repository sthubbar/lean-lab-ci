/-
P0081 J. Liu, K.-M. Tsang, Small prime solutions of ternary linear equations,
Acta Arith. 118 (2005) 79-100, CC-BY, read through a text extraction of the impan PDF.
Theorem 1.1, under the parity condition 1.2 and the coprimality condition 1.3, with
A = max(2, abs a₁, abs a₂, abs a₃):
(i) if a₁, a₂, a₃ are not all of the same sign, a₁p₁ + a₂p₂ + a₃p₃ = n has prime solutions
    with abs aⱼ pⱼ ≪ abs n + A abs(a₁a₂a₃)^{5/2} log^{26} A;
(ii) if all aⱼ are positive, it is soluble whenever n ≫ A (a₁a₂a₃)^{5/2} log^{26} A.
The comparison signs are lost in the extraction; we encode both with an absolute constant C,
which is implied by the ≤ and ≥ readings too. CITED as Prop defs, not asserted.
PROVED, zero sorry: (ii) gives the paper's A^{17/2} log^{26} A form, and with
a₁ = a₂ = a₃ = 1 it gives Vinogradov's three primes theorem.

AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Ternary.Statements

namespace LeanLab.LiuTsang2005
open Real

/-- Conditions 1.2 and 1.3. -/
def Cond (a₁ a₂ a₃ n : ℤ) : Prop :=
  a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₃ ≠ 0 ∧ Even (a₁ + a₂ + a₃ - n) ∧
  Int.gcd a₁ a₂ = 1 ∧ Int.gcd a₁ a₃ = 1 ∧ Int.gcd a₂ a₃ = 1 ∧
  Int.gcd a₁ n = 1 ∧ Int.gcd a₂ n = 1 ∧ Int.gcd a₃ n = 1

/-- `A = max(2, abs a₁, abs a₂, abs a₃)`. -/
noncomputable def Abig (a₁ a₂ a₃ : ℤ) : ℝ := max 2 (max |(a₁ : ℝ)| (max |(a₂ : ℝ)| |(a₃ : ℝ)|))

/-- `A abs(a₁a₂a₃)^{5/2} log^{26} A`. -/
noncomputable def Bnd (a₁ a₂ a₃ : ℤ) : ℝ :=
  Abig a₁ a₂ a₃ * |((a₁ * a₂ * a₃ : ℤ) : ℝ)| ^ (5 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26

def SameSign (a₁ a₂ a₃ : ℤ) : Prop := (0 < a₁ ∧ 0 < a₂ ∧ 0 < a₃) ∨ (a₁ < 0 ∧ a₂ < 0 ∧ a₃ < 0)

/-- Theorem 1.1 (i). -/
def Theorem11i : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a₁ a₂ a₃ n : ℤ, Cond a₁ a₂ a₃ n → ¬ SameSign a₁ a₂ a₃ →
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ a₁ * p₁ + a₂ * p₂ + a₃ * p₃ = n ∧
      |(a₁ : ℝ)| * p₁ ≤ C * (|(n : ℝ)| + Bnd a₁ a₂ a₃) ∧
      |(a₂ : ℝ)| * p₂ ≤ C * (|(n : ℝ)| + Bnd a₁ a₂ a₃) ∧
      |(a₃ : ℝ)| * p₃ ≤ C * (|(n : ℝ)| + Bnd a₁ a₂ a₃)

/-- Theorem 1.1 (ii). -/
def Theorem11ii : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a₁ a₂ a₃ n : ℤ, Cond a₁ a₂ a₃ n → 0 < a₁ → 0 < a₂ → 0 < a₃ →
    C * Bnd a₁ a₂ a₃ ≤ n →
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ a₁ * p₁ + a₂ * p₂ + a₃ * p₃ = n

/-! ### Links, zero sorry -/

theorem cond_one_one_one {n : ℤ} (hn : Odd n) : Cond 1 1 1 n := by
  refine ⟨one_ne_zero, one_ne_zero, one_ne_zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := hn; exact ⟨1 - k, by ring⟩
  all_goals simp [Int.gcd]

/-- Theorem 1.1 (ii) with `a₁ = a₂ = a₃ = 1` gives Vinogradov's three primes theorem. -/
theorem vinogradov_of_theorem11ii (h : Theorem11ii) : ∃ N0 : ℝ, Ternary.TernaryAbove N0 := by
  obtain ⟨C, hC, hT⟩ := h
  refine ⟨C * Bnd 1 1 1, fun n hn hle => ?_⟩
  obtain ⟨p₁, p₂, p₃, h1, h2, h3, he⟩ :=
    hT 1 1 1 n (cond_one_one_one (by exact_mod_cast hn.natCast)) one_pos one_pos one_pos
      (by exact_mod_cast hle)
  refine ⟨p₁, p₂, p₃, h1, h2, h3, ?_⟩
  have : ((p₁ + p₂ + p₃ : ℕ) : ℤ) = (n : ℤ) := by push_cast; linarith
  exact_mod_cast this

theorem abs_le_Abig₁ (a₁ a₂ a₃ : ℤ) : |(a₁ : ℝ)| ≤ Abig a₁ a₂ a₃ :=
  le_trans (le_max_left _ _) (le_max_right _ _)
theorem abs_le_Abig₂ (a₁ a₂ a₃ : ℤ) : |(a₂ : ℝ)| ≤ Abig a₁ a₂ a₃ :=
  le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
theorem abs_le_Abig₃ (a₁ a₂ a₃ : ℤ) : |(a₃ : ℝ)| ≤ Abig a₁ a₂ a₃ :=
  le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
theorem two_le_Abig (a₁ a₂ a₃ : ℤ) : 2 ≤ Abig a₁ a₂ a₃ := le_max_left _ _

/-- `A abs(a₁a₂a₃)^{5/2} ≤ A^{17/2}`, the paper's simplification. -/
theorem Bnd_le (a₁ a₂ a₃ : ℤ) :
    Bnd a₁ a₂ a₃ ≤ Abig a₁ a₂ a₃ ^ (17 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26 := by
  set A := Abig a₁ a₂ a₃
  have hA : 2 ≤ A := two_le_Abig a₁ a₂ a₃
  have hA0 : 0 < A := by linarith
  have hprod : |((a₁ * a₂ * a₃ : ℤ) : ℝ)| ≤ A ^ 3 := by
    push_cast
    rw [abs_mul, abs_mul, pow_succ, pow_two]
    apply mul_le_mul (mul_le_mul (abs_le_Abig₁ _ _ _) (abs_le_Abig₂ _ _ _) (abs_nonneg _)
      hA0.le) (abs_le_Abig₃ _ _ _) (abs_nonneg _) (by positivity)
  have hpow : |((a₁ * a₂ * a₃ : ℤ) : ℝ)| ^ (5 / 2 : ℝ) ≤ A ^ (15 / 2 : ℝ) := by
    calc |((a₁ * a₂ * a₃ : ℤ) : ℝ)| ^ (5 / 2 : ℝ) ≤ (A ^ 3) ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow (abs_nonneg _) hprod (by norm_num)
      _ = A ^ (15 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
  have hlog : 0 ≤ Real.log A ^ 26 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ A); positivity
  unfold Bnd
  calc A * |((a₁ * a₂ * a₃ : ℤ) : ℝ)| ^ (5 / 2 : ℝ) * Real.log A ^ 26
      ≤ A * A ^ (15 / 2 : ℝ) * Real.log A ^ 26 := by gcongr
    _ = A ^ (17 / 2 : ℝ) * Real.log A ^ 26 := by
        congr 1
        rw [show (17 / 2 : ℝ) = 1 + 15 / 2 by norm_num, Real.rpow_add hA0, Real.rpow_one]

/-- The paper's consequence of (ii): soluble whenever `n ≫ A^{17/2} log^{26} A`. -/
theorem theorem11ii_simple (h : Theorem11ii) :
    ∃ C : ℝ, 0 < C ∧ ∀ a₁ a₂ a₃ n : ℤ, Cond a₁ a₂ a₃ n → 0 < a₁ → 0 < a₂ → 0 < a₃ →
      C * (Abig a₁ a₂ a₃ ^ (17 / 2 : ℝ) * Real.log (Abig a₁ a₂ a₃) ^ 26) ≤ n →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ a₁ * p₁ + a₂ * p₂ + a₃ * p₃ = n := by
  obtain ⟨C, hC, hT⟩ := h
  refine ⟨C, hC, fun a₁ a₂ a₃ n hc h1 h2 h3 hn => hT a₁ a₂ a₃ n hc h1 h2 h3 ?_⟩
  exact le_trans (mul_le_mul_of_nonneg_left (Bnd_le a₁ a₂ a₃) hC.le) hn

end LeanLab.LiuTsang2005
