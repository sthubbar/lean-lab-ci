/-
Exact supplies for the original three-square mean square inputs.
Source https://arxiv.org/abs/0801.0130 pages 14 and 15.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp447a
import LeanLab.KumchevLiu2007.Decomp447b
import LeanLab.KumchevLiu2007.Decomp438h

namespace LeanLab.KumchevLiu2007.Supply447
open Real Complex Task129b Task129c Task292a Task292c Task403c
open scoped BigOperators

/-- Page 15 first display. Exact Task438b single modulus interval supply.
The complete period input has a clean Task447a proof. -/
theorem coefficient_interval_square :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, ∀ q : ℕ,
      0 ≤ x → 1 ≤ y → 0 < q → (q : ℝ) ^ 3 ≤ y →
      (∑ n ∈ intervalNumbers x y, ‖A3 n q‖ ^ 2) ≤
        K * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by
  obtain ⟨K, hK, hb⟩ := Task447a.complete_period_square
  refine ⟨6 * K, by positivity, ?_⟩
  intro x y q hx hy hq hqy
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqle : (q : ℝ) ≤ y := by
    have hpos : 0 ≤ (q : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) + 1) := by positivity
    nlinarith
  have hper : Function.Periodic (fun n => ‖A3 n q‖ ^ 2) q := by
    intro n
    change ‖A3 (n + q) q‖ ^ 2 = ‖A3 n q‖ ^ 2
    have he : A3 (n + q) q = A3 n q := Task403a.A3_periodic q n
    rw [he]
  calc
    _ ≤ 6 * y / (q : ℝ) * (∑ n ∈ Finset.range q, ‖A3 n q‖ ^ 2) :=
      Task438l.nonnegative_periodic_interval _ q hq hper (fun n => sq_nonneg _) x y hx hy hqle
    _ ≤ 6 * y / (q : ℝ) * (K * (localMajorant q ^ 6 / (q : ℝ))) :=
      mul_le_mul_of_nonneg_left (hb q hq) (by positivity)
    _ = (6 * K) * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by ring


/-- Page 15 first display. Exact Task403c diagonal target.
The complete period and numerical tail inputs have clean proofs. -/
theorem diagonal_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → 1 ≤ y → y ≤ x → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * A3 n q‖ ^ 2) ≤
        C * (y / P * Real.log x) := by
  obtain ⟨K, hK, hk⟩ := coefficient_interval_square
  obtain ⟨L, x0, hL, hx0, hl⟩ := Task438k.majorant_square_tail
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


/-- Page 15 second and third displays. Exact clean distinct modulus supply already proved in Task438h. -/
theorem off_diagonal_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x y P Q : ℝ,
      0 ≤ x → 1 ≤ y → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * A3 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re) ≤
        C * y ^ (3 / 4 : ℝ) := by
  exact Task438h.off_diagonal_power_bound

/-- Page 14 below display 50. Exact Task438a pointwise tail statement.
The Task447b numerical input has a clean proof. -/
theorem smooth_tail_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) → ∀ n : ℕ,
      ‖∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q : ℂ) * A3 n q‖ ^ 2 ≤
          C / Real.log x ^ A := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := Task447b.smooth_reciprocal_tail A ε hA hε
  refine ⟨C ^ 2, x0, by positivity, hx0, ?_⟩
  intro x y Q hx hy hyx hQpos hQ n
  have hx2 : 2 ≤ x := hx0.trans hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    _ ≤ (C / Real.log x ^ (A / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        ((Task438j.smooth_tail_norm n _ Q).trans (hb x y Q hx hy hyx hQpos hQ)) 2
    _ = C ^ 2 / Real.log x ^ A := by
      have hp : (Real.log x ^ (A / 2)) ^ (2 : ℕ) = Real.log x ^ A := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
        congr 1
        push_cast
        ring
      rw [div_pow, hp]


/-- Page 14 display 50. Exact Task403c target from the two smaller leaves.
The Task447b smooth fractional moment and parameter inputs have clean proofs. -/
theorem truncation_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ‖(series3 n P - product3 n Q) - tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
          C * (y / Real.log x ^ A) := by
  obtain ⟨C, xs, hC, hxs, hs⟩ := smooth_tail_pointwise A ε hA hε
  obtain ⟨xt, hxt, ht⟩ := Task342d.cutoff_order ε hε
  refine ⟨2 * C, max xs xt, by positivity, hxs.trans (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hxs' : xs ≤ x := (le_max_left _ _).trans hx
  have hxt' : xt ≤ x := (le_max_right _ _).trans hx
  have hx2 : 2 ≤ x := hxs.trans hxs'
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  have hQT := ht x y Q hxt' hy hQ
  calc
    _ ≤ ∑ _n ∈ intervalNumbers x y, C / Real.log x ^ A := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Task438i.smooth_remainder_identity n P Q _ hP hPQ hQT, norm_neg]
      exact hs x y Q hxs' hy hyx (hP.trans_le hPQ) hQ n
    _ = ((intervalNumbers x y).card : ℝ) * (C / Real.log x ^ A) := by simp
    _ ≤ (2 * y) * (C / Real.log x ^ A) :=
      mul_le_mul_of_nonneg_right (Task271a.interval_card_le (by linarith) hy1)
        (by positivity)
    _ = (2 * C) * (y / Real.log x ^ A) := by ring


#print axioms coefficient_interval_square
#print axioms diagonal_bound
#print axioms off_diagonal_power_bound
#print axioms smooth_tail_pointwise
#print axioms truncation_input

end LeanLab.KumchevLiu2007.Supply447
