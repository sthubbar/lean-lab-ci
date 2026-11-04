/-
Display 47 and the diagonal term on pages 14 and 15 of arXiv 0801.0130.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp271b

namespace LeanLab.KumchevLiu2007.Task292a

open Real Complex Task129b
open scoped BigOperators

/-- Page 14 display 47. Explicit product from the proved prime bound. -/
noncomputable def localMajorant (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))

/-- LEAF. Page 13 property i, cited from Schwarz Sections 2 and 3.
The Chinese remainder theorem factors A2 at coprime moduli. This is the
algebraic input to display 47, without any estimate or summation. -/
theorem A2_coprime_mul (n a b : ℕ) (hab : a.Coprime b) :
    U1534.A2 n (a * b) = U1534.A2 n a * U1534.A2 n b := by
  sorry

/-- Page 14 displays 46 and 47. Reuse the proved prime coefficient bound. -/
theorem prime_coefficient_bound (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ‖U1534.A2 n p‖ ≤ 1 / (p : ℝ) + 6 / (p : ℝ) ^ 2 := by
  exact A2_prime_norm_le_inv_add p n

/-- Page 13 property i. Mathlib gives the squarefree product step.
CONDITIONAL on A2_coprime_mul. -/
theorem squarefree_factorization (n q : ℕ) (hq : Squarefree q) :
    U1534.A2 n q = ∏ p ∈ q.primeFactors, U1534.A2 n p := by
  let f : ArithmeticFunction ℂ := ⟨U1534.A2 n, by simp [U1534.A2]⟩
  have hf : f.IsMultiplicative :=
    ⟨U1534.A2_one n, fun {a b} hab => A2_coprime_mul n a b hab⟩
  exact (hf.prod_primeFactors hq).symm

/-- Page 14 display 47. Multiply the prime bounds using squarefree
support. CONDITIONAL on A2_coprime_mul. -/
theorem coefficient_product_bound (n q : ℕ) (hq : 0 < q) :
    ‖U1534.A2 n q‖ ≤ localMajorant q / (q : ℝ) := by
  classical
  by_cases hs : Squarefree q
  · rw [squarefree_factorization n q hs, norm_prod]
    calc
      _ ≤ ∏ p ∈ q.primeFactors, ((1 + 6 / (p : ℝ)) / (p : ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro p hp; exact norm_nonneg _
        · intro p hp
          haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
          have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
          convert prime_coefficient_bound p n using 1 <;> field_simp [hp0] <;> ring
      _ = localMajorant q / (q : ℝ) := by
        rw [Finset.prod_div_distrib]
        have he : (∏ p ∈ q.primeFactors, (p : ℝ)) = q := by
          rw [← Nat.cast_prod]
          exact_mod_cast Nat.prod_primeFactors_of_squarefree hs
        rw [he]
        rfl
  · rw [A2_eq_zero_of_not_squarefree n q hs, norm_zero]
    exact div_nonneg (Finset.prod_nonneg (fun p _ => by positivity)) (Nat.cast_nonneg q)

/-- LEAF. Page 14 display 47 and page 15 first display. The square of the
local product is bounded by C log x for q at most x to the one third.
This leaf has no A2 coefficient and no interval sum. -/
theorem localMajorant_log_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ (x : ℝ) (q : ℕ),
      x0 ≤ x → 0 < q → (q : ℝ) ≤ x ^ (1 / 3 : ℝ) →
      localMajorant q ^ 2 ≤ C * Real.log x := by
  sorry

/-- LEAF. Page 15 first display. Real cutoff reciprocal square tail.
The already proved sum_inv_sq_Ioc_le handles positive natural cutoffs. -/
theorem reciprocal_square_tail (P : ℝ) (b : ℕ) (hP : 0 < P) :
    (∑ q ∈ Finset.Ioc ⌊P⌋₊ b, 1 / (q : ℝ) ^ 2) ≤ 2 / P := by
  sorry

/-- Page 15 first display. Exact statement of Task271b.diagonal_bound.
CONDITIONAL on the three OPEN leaves in this file. -/
theorem diagonal_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → 1 ≤ y → y ≤ x → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ^ 2) ≤
        C * (y / P * Real.log x) := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := localMajorant_log_bound
  refine ⟨4 * C, x0, by positivity, hx0, ?_⟩
  intro x y P Q hx hy hyx hP
  have hx2 : 2 ≤ x := hx0.trans hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hpoint (n q : ℕ) (hq : q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊) :
      ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ^ 2 ≤
        C * Real.log x * (1 / (q : ℝ) ^ 2) := by
    have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
    have hqy : (q : ℝ) ≤ y ^ (1 / 3 : ℝ) :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hq).2).trans (Nat.floor_le (by positivity))
    have hqx : (q : ℝ) ≤ x ^ (1 / 3 : ℝ) := hqy.trans
      (Real.rpow_le_rpow (by linarith) hyx (by norm_num))
    have hcoef := coefficient_product_bound n q hqn
    have hprod := hb x q hx hqn hqx
    have hw : ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ≤ ‖U1534.A2 n q‖ := by
      rw [norm_mul, norm_neg]
      exact mul_le_of_le_one_left (norm_nonneg _) (Task271b.smoothWeight_norm_le_one q Q)
    calc
      _ ≤ (localMajorant q / (q : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hw.trans hcoef) 2
      _ = localMajorant q ^ 2 * (1 / (q : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod (by positivity)
  calc
    _ ≤ ∑ _n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          C * Real.log x * (1 / (q : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun q hq => hpoint n q hq
    _ = ((intervalNumbers x y).card : ℝ) * (C * Real.log x *
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊, 1 / (q : ℝ) ^ 2) := by
      simp [Finset.mul_sum]
    _ ≤ (2 * y) * (C * Real.log x * (2 / P)) := by
      apply mul_le_mul
      · exact Task271a.interval_card_le (by linarith) hy
      · exact mul_le_mul_of_nonneg_left (reciprocal_square_tail P _ hP) (by positivity)
      · positivity
      · positivity
    _ = (4 * C) * (y / P * Real.log x) := by ring

end LeanLab.KumchevLiu2007.Task292a
