/-
Single modulus and numerical supplies for the three-square diagonal.
Source page 15 first display. The numerical leaf is proved. The period coefficient estimate remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438a
import LeanLab.KumchevLiu2007.Decomp438l

namespace LeanLab.KumchevLiu2007.Task438b

open Real Complex Task129b Task129c Task292a
open scoped BigOperators

/-- LEAF. Page 15 first display, from the coefficient definition on page 13
and Schwarz page 83 display 2.11. Only one modulus occurs. Averaging its
squared coefficient retains the local root count cancellation.
The condition q cubed at most y supplies enough complete periods. -/
theorem coefficient_interval_square :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, ∀ q : ℕ,
      0 ≤ x → 1 ≤ y → 0 < q → (q : ℝ) ^ 3 ≤ y →
      (∑ n ∈ intervalNumbers x y, ‖A3 n q‖ ^ 2) ≤
        K * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by
  exact Task438l.coefficient_interval_square

/-- LEAF. Page 15 first display, numerical reciprocal square tail.
No A3 coefficient, smooth weight or n variable occurs here.
The local product has only factors 1 plus 6 divided by p. -/
theorem majorant_square_tail :
    ∃ K x0 : ℝ, 0 < K ∧ 2 ≤ x0 ∧ ∀ x P : ℝ,
      x0 ≤ x → 0 < P →
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊x ^ (1 / 3 : ℝ)⌋₊,
        localMajorant q ^ 6 / (q : ℝ) ^ 2) ≤
          K * (Real.log x / P) := by
  exact Task438k.majorant_square_tail

/-- Page 15 first display. Exact Task403c diagonal target.
CONDITIONAL only on Task438l.complete_period_square. -/
theorem diagonal_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → 1 ≤ y → y ≤ x → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * A3 n q‖ ^ 2) ≤
        C * (y / P * Real.log x) := by
  obtain ⟨K, hK, hk⟩ := coefficient_interval_square
  obtain ⟨L, x0, hL, hx0, hl⟩ := majorant_square_tail
  refine ⟨K * L, x0, by positivity, hx0, ?_⟩
  intro x y P Q hx hy hyx hP
  have hx2 : 2 ≤ x := hx0.trans hx
  have hxy : y ^ (1 / 3 : ℝ) ≤ x ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hyx (by norm_num)
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        K * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hqy : (q : ℝ) ≤ y ^ (1 / 3 : ℝ) :=
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hq).2).trans (Nat.floor_le (by positivity))
      have hcube : (q : ℝ) ^ 3 ≤ y := by
        calc
          _ ≤ (y ^ (1 / 3 : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hqy 3
          _ = y := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ y)]
            norm_num
      calc
        _ ≤ ∑ n ∈ intervalNumbers x y, ‖A3 n q‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          apply pow_le_pow_left₀ (norm_nonneg _)
          rw [norm_mul, norm_neg]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (Task271b.smoothWeight_norm_le_one q Q)
        _ ≤ _ := hk x y q (by linarith) hy hqn hcube
    _ = K * y * ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        localMajorant q ^ 6 / (q : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ K * y * ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊x ^ (1 / 3 : ℝ)⌋₊,
        localMajorant q ^ 6 / (q : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hxy)
      · intro q hq hnot
        positivity
    _ ≤ K * y * (L * (Real.log x / P)) :=
      mul_le_mul_of_nonneg_left (hl x P hx hP) (by positivity)
    _ = K * L * (y / P * Real.log x) := by ring

end LeanLab.KumchevLiu2007.Task438b
