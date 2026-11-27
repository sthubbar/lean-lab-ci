/-
Split of `prime_minor_multi_451` from SPLIT_minor_bare_multi_denominator451, P0029 page 27,
proof of Lemma 7.3, display 7.8, the minor arc part: "On m(R) ... S_phi satisfies the same
Vinogradov-Vaughan minor-arc estimate as S, giving the minor arc fourth moment bound
(X^3/R + X^(13/5)) (log X)^5".

The paper's route for the prime restricted family is: a pointwise minor arc bound for the
unsmoothed partial sums, transferred to the smoothed sum by summation by parts, then the
family second moment with the supremum pulled out. Here:

* the pointwise bound for the full von Mangoldt partial sums at logarithm power two is the
  existing open leaf `split_leaf_ssum_minor_log2` of SPLIT_minor_bare_family328, reused, not
  restated; it is the QUESTION 2 input of the folder, since display 4.8 only prints power four;
* `leaf_nonprime_partial_feed1122`: removing the higher prime powers from a partial sum costs
  at most a power saving, MEDIUM;
* `leaf_prime_parts_feed1122`: summation by parts for the prime restricted smoothed sum, the
  analogue of the proved `Sphi_of_partial_bound261`, PROVED here;
* `leaf_prime_family_feed1122`: the family second moment with the supremum pulled out, the
  analogue of the proved `supported_family_sharp261` for the prime restricted sum, MEDIUM.

The assembly `prime_minor_multi_451_from_leaves` has exactly the parent statement.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp451a
import LeanLab.BhowmikGrimmelt2026.SPLIT_minor_bare_family328

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction NNReal

attribute [local instance] Classical.propDecidable

/-- LEAF: P0029 page 27, proof of Lemma 7.3, display 7.8, minor arc part, the step from the
von Mangoldt sum S of display 4.8 to its prime part. Class MEDIUM. For every X at least two,
every partial length m at most X and every real alpha, the partial sum of S up to m minus its
prime restricted part, which is the sum of Lambda of n times e of alpha n over the higher
prime powers n at most m, has modulus at most two times X to four fifths times the square of
log X. Proof sketch: the modulus is at most the sum of Lambda over higher prime powers up to
X, which is at most log X times the number of perfect powers up to X, at most the square root
of X times log X over log two. -/
theorem leaf_nonprime_partial_feed1122 {X m : ℕ} (hX : 2 ≤ X) (hm : m ≤ X) (α : ℝ) :
    ‖Ssum m α - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n)‖ ≤
      2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 := by
  have h_main : ‖Ssum m α - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime), (vonMangoldt n : ℂ) * ee (α * n)‖ ≤ ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ) := by
    have h₁ : Ssum m α = ∑ n ∈ Finset.Icc 1 m, (vonMangoldt n : ℂ) * ee (α * n) := by
      rfl
    rw [h₁]
    have h₂ : (∑ n ∈ Finset.Icc 1 m, (vonMangoldt n : ℂ) * ee (α * n)) - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime), (vonMangoldt n : ℂ) * ee (α * n) = ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℂ) * ee (α * n) := by
      have h₃ : (Finset.Icc 1 m).filter (fun n => n.Prime) ∪ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime) = Finset.Icc 1 m := by
        apply Finset.ext
        intro x
        simp [Finset.mem_union, Finset.mem_filter]
        <;> by_cases hx : x.Prime <;> simp_all
        <;> aesop
      have h₄ : Disjoint ((Finset.Icc 1 m).filter (fun n => n.Prime)) ((Finset.Icc 1 m).filter (fun n => ¬ n.Prime)) := by
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        simp [Finset.mem_filter] at hx₁ hx₂
        tauto
      calc
        (∑ n ∈ Finset.Icc 1 m, (vonMangoldt n : ℂ) * ee (α * n)) - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime), (vonMangoldt n : ℂ) * ee (α * n) =
            ∑ n ∈ Finset.Icc 1 m, (vonMangoldt n : ℂ) * ee (α * n) - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime), (vonMangoldt n : ℂ) * ee (α * n) := by rfl
        _ = ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℂ) * ee (α * n) := by
          have h₅ : ∑ n ∈ Finset.Icc 1 m, (vonMangoldt n : ℂ) * ee (α * n) = ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime), (vonMangoldt n : ℂ) * ee (α * n) + ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℂ) * ee (α * n) := by
            rw [← Finset.sum_union h₄]
            rw [h₃]
          rw [h₅]
          ring
          <;> simp [sub_eq_add_neg]
          <;> abel
    rw [h₂]
    have h₃ : ‖(∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℂ) * ee (α * n))‖ ≤ ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ) := by
      calc
        _ = ‖∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℂ) * ee (α * n)‖ := by rfl
        _ ≤ ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), ‖(vonMangoldt n : ℂ) * ee (α * n)‖ := norm_sum_le _ _
        _ = ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), ‖(vonMangoldt n : ℂ)‖ * ‖ee (α * n)‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [norm_mul]
        _ = ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), ‖(vonMangoldt n : ℂ)‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          have h₄ : ‖ee (α * n)‖ = 1 := by
            simp [ee, Complex.norm_eq_abs, Complex.abs_exp, Real.exp_zero]
            <;> ring_nf
            <;> simp [Complex.abs, Complex.normSq, Real.sqrt_eq_iff_sq_eq]
            <;> ring_nf
            <;> field_simp [Real.exp_ne_zero]
            <;> ring_nf
          rw [h₄]
          <;> simp [mul_one]
        _ = ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [Complex.norm_eq_abs, Complex.abs_ofReal, Real.norm_eq_abs, abs_of_nonneg, vonMangoldt_nonneg]
          <;> norm_cast
    exact h₃
  have h_sum_le : (∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ)) ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 := by
    have h₁ : (∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ)) ≤ ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ) := by
      have h₁₁ : (Finset.Icc 1 m).filter (fun n => ¬ n.Prime) ⊆ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime) := by
        apply Finset.filter_subset_filter
        apply Finset.Icc_subset_Icc
        <;> omega
      have h₁₂ : ∀ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), 0 ≤ (vonMangoldt n : ℝ) := by
        intro n hn
        exact by
          norm_cast
          <;> exact ArithmeticFunction.vonMangoldt_nonneg
      exact Finset.sum_le_sum_of_subset_of_nonneg h₁₁ h₁₂
    have h₂ : ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ) ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 := by
      have h₂₁ : ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ) ≤ Real.sqrt X * Real.log X ^ 2 / Real.log 2 := by
        have h₂₁₁ : ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ) = ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), (vonMangoldt n : ℝ) := by
          have h₂₁₁₁ : ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ) = ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), (vonMangoldt n : ℝ) + ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n = 0), (vonMangoldt n : ℝ) := by
            have h₂₁₁₂ : (Finset.Icc 1 X).filter (fun n => ¬ n.Prime) = (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0) ∪ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n = 0) := by
              apply Finset.ext
              intro x
              simp [Finset.mem_union, Finset.mem_filter]
              <;> by_cases hx : ArithmeticFunction.vonMangoldt x = 0 <;> simp_all
              <;> aesop
            have h₂₁₁₃ : Disjoint ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)) ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n = 0)) := by
              rw [Finset.disjoint_left]
              intro x hx₁ hx₂
              simp [Finset.mem_filter] at hx₁ hx₂
              <;> aesop
            calc
              ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ) = ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0) ∪ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n = 0), (vonMangoldt n : ℝ) := by rw [h₂₁₁₂]
              _ = ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), (vonMangoldt n : ℝ) + ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n = 0), (vonMangoldt n : ℝ) := by
                rw [Finset.sum_union h₂₁₁₃]
          have h₂₁₁₄ : ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n = 0), (vonMangoldt n : ℝ) = 0 := by
            apply Finset.sum_eq_zero
            intro x hx
            simp [Finset.mem_filter] at hx
            have h₂₁₁₅ : (ArithmeticFunction.vonMangoldt x : ℝ) = 0 := by
              norm_cast at hx.2.2 ⊢
              <;> simp_all
            rw [h₂₁₁₅]
          linarith
        have h₂₁₂ : ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), (vonMangoldt n : ℝ) ≤ Real.sqrt X * Real.log X ^ 2 / Real.log 2 := by
          have h₂₁₃ : ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), (vonMangoldt n : ℝ) ≤ (∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), (Real.log X : ℝ)) := by
            apply Finset.sum_le_sum
            intro n hn
            have h₂₁₃₁ : (vonMangoldt n : ℝ) ≤ Real.log X := by
              have h₂₁₃₂ : (vonMangoldt n : ℝ) ≤ Real.log n := by
                exact_mod_cast ArithmeticFunction.vonMangoldt_le_log
              have h₂₁₃₃ : (n : ℝ) ≤ X := by
                simp [Finset.mem_filter, Finset.mem_Icc] at hn
                exact_mod_cast hn.2.1
              have h₂₁₃₄ : Real.log n ≤ Real.log X := Real.log_le_log (by
                simp [Finset.mem_filter, Finset.mem_Icc] at hn
                norm_cast at hn.1.1 ⊢ <;> omega) h₂₁₃₃
              linarith
            exact h₂₁₃₁
          have h₂₁₄ : (∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), (Real.log X : ℝ)) = ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)).card * Real.log X := by
            simp [Finset.sum_const, nsmul_eq_mul]
            <;> ring_nf
            <;> field_simp
            <;> ring_nf
          have h₂₁₅ : ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)).card ≤ ⌊Real.sqrt X⌋₊ * (Nat.log 2 X) := by
            have h₂₁₅₁ : ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)) ⊆ Finset.Icc 1 X := by
              apply Finset.filter_subset
            have h₂₁₅₂ : ∀ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), n.Prime = false := by
              intro n hn
              simp [Finset.mem_filter] at hn
              tauto
            have h₂₁₅₃ : ∀ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), Nat.Prime (Nat.minFac n) := by
              intro n hn
              simp [Finset.mem_filter] at hn
              have h₂₁₅₄ : ArithmeticFunction.vonMangoldt n ≠ 0 := hn.2.2
              have h₂₁₅₅ : Nat.Prime (Nat.minFac n) := Nat.minFac_prime (by
                have h₂₁₅₆ : n ≠ 1 := by
                  by_contra h
                  rw [h] at h₂₁₅₄
                  norm_num [ArithmeticFunction.vonMangoldt_apply] at h₂₁₅₄
                exact h₂₁₅₆)
              exact h₂₁₅₅
            have h₂₁₅₇ : ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)).card ≤ ⌊Real.sqrt X⌋₊ * (Nat.log 2 X) := by
              classical
              -- Use the fact that each n in the filter is a prime power p^k with k ≥ 2
              -- Map each n to (minFac n, k) where k is the exponent
              -- The number of such pairs is bounded by ⌊√X⌋₊ * log_2 X
              have h₂₁₅₈ : ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)).card ≤ (Finset.Icc 1 ⌊Real.sqrt X⌋₊).card * (Nat.log 2 X) := by
                classical
                -- Define the injection from the filtered set to the product
                let S := (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)
                let T := Finset.Icc 1 ⌊Real.sqrt X⌋₊ ×ˢ Finset.Icc 1 (Nat.log 2 X)
                -- Define the function f : S → T by f(n) = (minFac n, k) where k is the exponent in the prime factorization
                have h₂₁₅₈₁ : S.card ≤ T.card := by
                  -- Use the fact that we can inject S into T
                  have h₂₁₅₈₂ : ∀ n ∈ S, (Nat.minFac n) ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊ := by
                    intro n hn
                    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
                    have h₂₁₅₈₃ : 1 ≤ n := hn.1.1
                    have h₂₁₅₈₄ : n ≤ X := hn.1.2
                    have h₂₁₅₈₅ : ¬n.Prime := hn.2.1
                    have h₂₁₅₈₆ : ArithmeticFunction.vonMangoldt n ≠ 0 := hn.2.2
                    have h₂₁₅₈₇ : Nat.Prime (Nat.minFac n) := Nat.minFac_prime (by
                      by_contra h
                      have h₂₁₅₈₈ : n = 1 := by simpa using h
                      rw [h₂₁₅₈₈] at h₂₁₅₈₆
                      norm_num [ArithmeticFunction.vonMangoldt_apply] at h₂₁₅₈₆
                    )
                    have h₂₁₅₈₉ : (Nat.minFac n : ℕ) ≤ ⌊Real.sqrt X⌋₊ := by
                      have h₂₁₅₉₀ : (Nat.minFac n : ℕ) ^ 2 ≤ n := by
                        have h₂₁₅₉₁ : Nat.Prime (Nat.minFac n) := h₂₁₅₈₇
                        have h₂₁₅₉₂ : (Nat.minFac n : ℕ) ∣ n := Nat.minFac_dvd n
                        have h₂₁₅₉₃ : (Nat.minFac n : ℕ) ≠ n := by
                          intro h₂₁₅₉₄
                          have h₂₁₅₉₅ : n.Prime := by
                            apply Nat.prime_of_minFac_eq_self
                            <;> omega
                          contradiction
                        have h₂₁₅₉₆ : (Nat.minFac n : ℕ) < n := by
                          have h₂₁₅₉₇ : (Nat.minFac n : ℕ) ∣ n := Nat.minFac_dvd n
                          have h₂₁₅₉₈ : (Nat.minFac n : ℕ) ≤ n := Nat.le_of_dvd (by omega) h₂₁₅₉₇
                          omega
                        nlinarith [Nat.Prime.one_lt h₂₁₅₈₇]
                      have h₂₁₅₉₄ : (n : ℝ) ≤ X := by exact_mod_cast h₂₁₅₈₄
                      have h₂₁₅₉₅ : (Nat.minFac n : ℝ) ^ 2 ≤ X := by
                        have h₂₁₅₉₆ : (Nat.minFac n : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast h₂₁₅₉₀
                        linarith
                      have h₂₁₅₉₆ : (Nat.minFac n : ℝ) ≤ Real.sqrt X := Real.le_sqrt_of_sq_le h₂₁₅₉₅
                      have h₂₁₅₉₇ : (Nat.minFac n : ℕ) ≤ ⌊Real.sqrt X⌋₊ := by
                        rw [Nat.le_floor] <;> norm_cast at h₂₁₅₉₆ ⊢ <;> simp_all [Nat.floor_le, Nat.lt_floor_add_one]
                        <;> nlinarith
                      exact h₂₁₅₉₇
                    have h₂₁₅₈₁₀ : 1 ≤ Nat.minFac n := Nat.Prime.one_lt h₂₁₅₈₇ |>.le
                    exact ⟨by omega, by omega⟩
                  have h₂₁₅₈₁₁ : ∀ n ∈ S, ∃ k ∈ Finset.Icc 1 (Nat.log 2 X), n = (Nat.minFac n) ^ k := by
                    intro n hn
                    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
                    have h₂₁₅₈₁₂ : 1 ≤ n := hn.1.1
                    have h₂₁₅₈₁₃ : n ≤ X := hn.1.2
                    have h₂₁₅₈₁₄ : ¬n.Prime := hn.2.1
                    have h₂₁₅₈₁₅ : ArithmeticFunction.vonMangoldt n ≠ 0 := hn.2.2
                    have h₂₁₅₈₁₆ : Nat.Prime (Nat.minFac n) := Nat.minFac_prime (by
                      by_contra h
                      have h₂₁₅₈₁₇ : n = 1 := by simpa using h
                      rw [h₂₁₅₈₁₇] at h₂₁₅₈₁₅
                      norm_num [ArithmeticFunction.vonMangoldt_apply] at h₂₁₅₈₁₅
                    )
                    have h₂₁₅₈₁₈ : (Nat.factorization n) (Nat.minFac n) ≥ 2 := by
                      have h₂₁₅₈₁₉ : n ≠ 1 := by
                        by_contra h
                        rw [h] at h₂₁₅₈₁₅
                        norm_num [ArithmeticFunction.vonMangoldt_apply] at h₂₁₅₈₁₅
                      have h₂₁₅₈₂₀ : (Nat.factorization n) (Nat.minFac n) ≥ 1 := by
                        have h₂₁₅₈₂₁ : (Nat.minFac n) ∣ n := Nat.minFac_dvd n
                        have h₂₁₅₈₂₂ : (Nat.factorization n) (Nat.minFac n) ≥ 1 := by
                          apply Nat.succ_le_of_lt
                          apply Nat.factorization_pos_of_dvd
                          <;> simp_all [Nat.Prime.ne_zero]
                          <;> omega
                        exact h₂₁₅₈₂₂
                      by_contra h₂₁₅₈₂₃
                      have h₂₁₅₈₂₄ : (Nat.factorization n) (Nat.minFac n) ≤ 1 := by linarith
                      have h₂₁₅₈₂₅ : (Nat.factorization n) (Nat.minFac n) = 1 := by
                        omega
                      have h₂₁₅₈₂₆ : n = Nat.minFac n := by
                        have h₂₁₅₈₂₇ : Nat.factorization n = { (Nat.minFac n) := 1 } := by
                          apply Finsupp.ext
                          intro p
                          by_cases hp : p = Nat.minFac n
                          · simp [hp, h₂₁₅₈₂₅]
                          · have h₂₁₅₈₂₈ : (Nat.factorization n) p = 0 := by
                              have h₂₁₅₈₂₉ : p ∉ (Nat.factorization n).support := by
                                intro h₂₁₅₈₃₀
                                have h₂₁₅₈₃₁ : p ∈ (Nat.factorization n).support := h₂₁₅₈₃₀
                                have h₂₁₅₈₃₂ : (Nat.factorization n).support = {Nat.minFac n} := by
                                  have h₂₁₅₈₃₃ : n ≠ 1 := by
                                    by_contra h
                                    rw [h] at h₂₁₅₈₁₅
                                    norm_num [ArithmeticFunction.vonMangoldt_apply] at h₂₁₅₈₁₅
                                  have h₂₁₅₈₃₄ : (Nat.factorization n).support = {Nat.minFac n} := by
                                    rw [Nat.factorization_eq_prime_pow_iff (by
                                      have h₂₁₅₈₃₅ : n ≠ 1 := by
                                        by_contra h
                                        rw [h] at h₂₁₅₈₁₅
                                        norm_num [ArithmeticFunction.vonMangoldt_apply] at h₂₁₅₈₁₅
                                      omega)
                                    <;> aesop
                                  exact h₂₁₅₈₃₄
                                simp_all [Set.mem_singleton_iff]
                                <;> aesop
                              simp_all [Finsupp.mem_support_iff]
                            simp [h₂₁₅₈₂₈]
                          <;> aesop
                        have h₂₁₅₈₃₀ : n = Nat.minFac n := by
                          rw [← Nat.prod_factorization n]
                          rw [h₂₁₅₈₂₇]
                          simp [Finsupp.prod_const]
                          <;> norm_cast
                          <;> simp [h₂₁₅₈₇.ne_zero]
                        exact h₂₁₅₈₃₀
                      have h₂₁₅₈₃₁ : n.Prime := by
                        have h₂₁₅₈₃₂ : n = Nat.minFac n := h₂₁₅₈₂₆
                        rw [h₂₁₅₈₃₂]
                        exact h₂₁₅₈₇
                      contradiction
                    -- Now we know the exponent is at least 2
                    have h₂₁₅₈₃₂ : ∃ k : ℕ, n = (Nat.minFac n) ^ k ∧ k ≥ 2 := by
                      use (Nat.factorization n) (Nat.minFac n)
                      constructor
                      · have h₂₁₅₈₃₃ : n = (Nat.minFac n) ^ (Nat.factorization n) (Nat.minFac n) := by
                          have h₂₁₅₈₃₄ : n ≠ 1 := by
                            by_contra h
                            rw [h] at h₂₁₅₈₁₅
                            norm_num [ArithmeticFunction.vonMangoldt_apply] at h₂₁₅₈₁₅
                          have h₂₁₅₈₃₅ : Nat.factorization n = { (Nat.minFac n) := (Nat.factorization n) (Nat.minFac n) } := by
                            apply Finsupp.ext
                            intro p
                            by_cases hp : p = Nat.minFac n
                            · simp [hp]
                            · have h₂₁₅₈₃₆ : (Nat.factorization n) p = 0 := by
                                have h₂₁₅₈₃₇ : p ∉ (Nat.factorization n).support := by
                                  intro h₂₁₅₈₃₈
                                  have h₂₁₅₈₃₉ : p ∈ (Nat.factorization n).support := h₂₁₅₈₃₈
                                  have h₂₁₅₈₄₀ : (Nat.factorization n).support = {Nat.minFac n} := by
                                    have h₂₁₅₈₄₁ : n ≠ 1 := by
                                      by_contra h
                                      rw [h] at h₂₁₅₈₁₅
                                      norm_num [ArithmeticFunction.vonMangoldt_apply] at h₂₁₅₈₁₅
                                    have h₂₁₅₈₄₂ : (Nat.factorization n).support = {Nat.minFac n} := by
                                      rw [Nat.factorization_eq_prime_pow_iff (by
                                        have h₂₁₅₈₄₃ : n ≠ 1 := by
                                          by_contra h
                                          rw [h] at h₂₁₅₈₁₅
                                          norm_num [ArithmeticFunction.vonMangoldt_apply] at h₂₁₅₈₁₅
                                        omega)
                                      <;> aesop
                                    exact h₂₁₅₈₄₂
                                  simp_all [Set.mem_singleton_iff]
                                  <;> aesop
                                simp_all [Finsupp.mem_support_iff]
                              simp [h₂₁₅₈₃₆]
                            <;> aesop
                          rw [← Nat.prod_factorization n]
                          rw [h₂₁₅₈₃₅]
                          simp [Finsupp.prod_const]
                          <;> norm_cast
                          <;> simp [h₂₁₅₈₇.ne_zero]
                      exact h₂₁₅₈₃₃
                      · omega
                    obtain ⟨k, hk, hk2⟩ := h₂₁₅₈₃₂
                    have h₂₁₅₈₃₃ : k ≤ Nat.log 2 X := by
                      have h₂₁₅₈₃₄ : 2 ^ k ≤ n := by
                        have h₂₁₅₈₃₅ : 2 ≤ Nat.minFac n := Nat.Prime.one_lt h₂₁₅₈₁₆ |>.le
                        calc
                          2 ^ k ≤ (Nat.minFac n) ^ k := by exact Nat.pow_le_pow_of_le_left (by omega) k
                          _ = n := by rw [hk]
                      have h₂₁₅₈₃₆ : (2 : ℕ) ^ k ≤ X := by
                        calc
                          (2 : ℕ) ^ k ≤ n := h₂₁₅₈₃₄
                          _ ≤ X := by exact_mod_cast hn.1.2
                      have h₂₁₅₈₃₇ : k ≤ Nat.log 2 X := by
                        by_contra h₂₁₅₈₃₈
                        have h₂₁₅₈₃₉ : Nat.log 2 X < k := by omega
                        have h₂₁₅₈₄₀ : 2 ^ k > X := by
                          have h₂₁₅₈₄₁ : 2 ^ (Nat.log 2 X + 1) > X := by
                            have h₂₁₅₈₄₂ : 2 ^ (Nat.log 2 X + 1) > X := by
                              calc
                                2 ^ (Nat.log 2 X + 1) = 2 ^ Nat.log 2 X * 2 := by ring_nf
                                _ > X := by
                                  have h₂₁₅₈₄₃ : 2 ^ Nat.log 2 X > X / 2 := by
                                    have h₂₁₅₈₄₄ : 2 ^ Nat.log 2 X > X / 2 := by
                                      have h₂₁₅₈₄₅ : 2 ^ Nat.log 2 X > X / 2 := by
                                        calc
                                          2 ^ Nat.log 2 X ≥ X / 2 + 1 := by
                                            have h₂₁₅₈₄₆ := Nat.log2_le_iff (by omega : 0 < X)
                                            have h₂₁₅₈₄₇ : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log2_le_self X
                                            have h₂₁₅₈₄₈ : X < 2 ^ (Nat.log 2 X + 1) := by
                                              calc
                                                X < 2 ^ (Nat.log 2 X + 1) := by
                                                  have h₂₁₅₈₄₉ := Nat.lt_pow_succ_log2 (by omega : 0 < X)
                                                  exact h₂₁₅₈₄₉
                                                _ = 2 ^ (Nat.log 2 X + 1) := by ring_nf
                                            omega
                                          _ > X / 2 := by omega
                                      exact h₂₁₅₈₄₅
                                    exact h₂₁₅₈₄₄
                                  have h₂₁₅₈₄₅ : (2 : ℕ) ^ Nat.log 2 X * 2 > X := by
                                    have h₂₁₅₈₄₆ : (2 : ℕ) ^ Nat.log 2 X > X / 2 := h₂₁₅₈₄₃
                                    have h₂₁₅₈₄₇ : (2 : ℕ) ^ Nat.log 2 X * 2 > X := by
                                      omega
                                    exact h₂₁₅₈₄₇
                                  omega
                            omega
                          have h₂₁₅₈₄₈ : 2 ^ k ≥ 2 ^ (Nat.log 2 X + 1) := by
                            exact Nat.pow_le_pow_of_le_right (by norm_num) (by omega)
                          linarith
                        linarith
                      exact h₂₁₅₈₃₇
                    refine' ⟨k, ⟨by omega, by omega⟩, _⟩
                    <;> simp_all [pow_succ]
                    <;> ring_nf at *
                    <;> nlinarith
                  -- Now we have the injection
                  have h₂₁₅₈₁₂ : S.card ≤ T.card := by
                    classical
                    -- Use the injection to bound the cardinality
                    have h₂₁₅₈₁₃ : ∀ n ∈ S, (Nat.minFac n, (Nat.factorization n) (Nat.minFac n)) ∈ T := by
                      intro n hn
                      simp only [S, T, Finset.mem_filter, Finset.mem_Icc, Finset.mem_product, Finset.mem_range] at hn ⊢
                      have h₂₁₅₈₁₄ : (Nat.minFac n) ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊ := h₂₁₅₈₂ n hn
                      have h₂₁₅₈₁₅ : ∃ k ∈ Finset.Icc 1 (Nat.log 2 X), n = (Nat.minFac n) ^ k := h₂₁₅₈₁₁ n hn
                      have h₂₁₅₈₁₆ : (Nat.factorization n) (Nat.minFac n) ∈ Finset.Icc 1 (Nat.log 2 X) := by
                        have h₂₁₅₈₁₇ : n ≠ 1 := by
                          by_contra h
                          simp_all [ArithmeticFunction.vonMangoldt_apply]
                        have h₂₁₅₈₁₈ : (Nat.factorization n) (Nat.minFac n) ≥ 2 := by
                          by_contra h₂₁₅₈₁₉
                          have h₂₁₅₈₂₀ : (Nat.factorization n) (Nat.minFac n) ≤ 1 := by omega
                          have h₂₁₅₈₂₁ : (Nat.factorization n) (Nat.minFac n) = 1 := by
                            have h₂₁₅₈₂₂ : (Nat.factorization n) (Nat.minFac n) ≥ 1 := by
                              have h₂₁₅₈₂₃ : (Nat.minFac n) ∣ n := Nat.minFac_dvd n
                              have h₂₁₅₈₂₄ : (Nat.factorization n) (Nat.minFac n) ≥ 1 := by
                                apply Nat.succ_le_of_lt
                                apply Nat.factorization_pos_of_dvd
                                <;> simp_all [Nat.Prime.ne_zero]
                                <;> omega
                              exact h₂₁₅₈₂₄
                            omega
                          have h₂₁₅₈₂₅ : n = Nat.minFac n := by
                            have h₂₁₅₈₂₆ : Nat.factorization n = { (Nat.minFac n) := 1 } := by
                              apply Finsupp.ext
                              intro p
                              by_cases hp : p = Nat.minFac n
                              · simp [hp, h₂₁₅₈₂₁]
                              · have h₂₁₅₈₂₇ : (Nat.factorization n) p = 0 := by
                                  have h₂₁₅₈₂₈ : p ∉ (Nat.factorization n).support := by
                                    intro h₂₁₅₈₂₉
                                    have h₂₁₅₈₃₀ : p ∈ (Nat.factorization n).support := h₂₁₅₈₂₉
                                    have h₂₁₅₈₃₁ : (Nat.factorization n).support = {Nat.minFac n} := by
                                      have h₂₁₅₈₃₂ : n ≠ 1 := by
                                        by_contra h
                                        simp_all [ArithmeticFunction.vonMangoldt_apply]
                                      have h₂₁₅₈₃₃ : (Nat.factorization n).support = {Nat.minFac n} := by
                                        rw [Nat.factorization_eq_prime_pow_iff (by
                                          have h₂₁₅₈₃₄ : n ≠ 1 := by
                                            by_contra h
                                            simp_all [ArithmeticFunction.vonMangoldt_apply]
                                          omega)
                                        <;> aesop
                                      exact h₂₁₅₈₃₃
                                    simp_all [Set.mem_singleton_iff]
                                    <;> aesop
                                  simp_all [Finsupp.mem_support_iff]
                                simp [h₂₁₅₈₂₇]
                              <;> aesop
                            have h₂₁₅₈₂₈ : n = Nat.minFac n := by
                              rw [← Nat.prod_factorization n]
                              rw [h₂₁₅₈₂₆]
                              simp [Finsupp.prod_const]
                              <;> norm_cast
                              <;> simp [Nat.Prime.ne_zero h₂₁₅₈₁₆]
                            exact h₂₁₅₈₂₈
                          have h₂₁₅₈₂₉ : n.Prime := by
                            have h₂₁₅₈₃₀ : n = Nat.minFac n := h₂₁₅₈₂₅
                            rw [h₂₁₅₈₃₀]
                            exact h₂₁₅₈₁₆
                          simp_all
                        have h₂₁₅₈₃₀ : (Nat.factorization n) (Nat.minFac n) ≤ Nat.log 2 X := by
                          have h₂₁₅₈₃₁ : 2 ^ (Nat.factorization n) (Nat.minFac n) ≤ n := by
                            have h₂₁₅₈₃₂ : 2 ≤ Nat.minFac n := Nat.Prime.one_lt h₂₁₅₈₁₆ |>.le
                            calc
                              2 ^ (Nat.factorization n) (Nat.minFac n) ≤ (Nat.minFac n) ^ (Nat.factorization n) (Nat.minFac n) := by
                                exact Nat.pow_le_pow_of_le_left (by omega) _
                              _ = n := by
                                have h₂₁₅₈₃₃ : n = (Nat.minFac n) ^ (Nat.factorization n) (Nat.minFac n) := by
                                  have h₂₁₅₈₃₄ : n ≠ 1 := by
                                    by_contra h
                                    simp_all [ArithmeticFunction.vonMangoldt_apply]
                                  have h₂₁₅₈₃₅ : Nat.factorization n = { (Nat.minFac n) := (Nat.factorization n) (Nat.minFac n) } := by
                                    apply Finsupp.ext
                                    intro p
                                    by_cases hp : p = Nat.minFac n
                                    · simp [hp]
                                    · have h₂₁₅₈₃₆ : (Nat.factorization n) p = 0 := by
                                        have h₂₁₅₈₃₇ : p ∉ (Nat.factorization n).support := by
                                          intro h₂₁₅₈₃₈
                                          have h₂₁₅₈₃₉ : p ∈ (Nat.factorization n).support := h₂₁₅₈₃₈
                                          have h₂₁₅₈₄₀ : (Nat.factorization n).support = {Nat.minFac n} := by
                                            have h₂₁₅₈₄₁ : n ≠ 1 := by
                                              by_contra h
                                              simp_all [ArithmeticFunction.vonMangoldt_apply]
                                            have h₂₁₅₈₄₂ : (Nat.factorization n).support = {Nat.minFac n} := by
                                              rw [Nat.factorization_eq_prime_pow_iff (by
                                                have h₂₁₅₈₄₃ : n ≠ 1 := by
                                                  by_contra h
                                                  simp_all [ArithmeticFunction.vonMangoldt_apply]
                                                omega)
                                              <;> aesop
                                            exact h₂₁₅₈₄₂
                                          simp_all [Set.mem_singleton_iff]
                                          <;> aesop
                                        simp_all [Finsupp.mem_support_iff]
                                      simp [h₂₁₅₈₃₆]
                                    <;> aesop
                                  rw [← Nat.prod_factorization n]
                                  rw [h₂₁₅₈₃₅]
                                  simp [Finsupp.prod_const]
                                  <;> norm_cast
                                  <;> simp [Nat.Prime.ne_zero h₂₁₅₈₁₆]
                                rw [h₂₁₅₈₃₃]
                          have h₂₁₅₈₃₄ : (2 : ℕ) ^ (Nat.factorization n) (Nat.minFac n) ≤ X := by
                            calc
                              (2 : ℕ) ^ (Nat.factorization n) (Nat.minFac n) ≤ n := h₂₁₅₈₃₁
                              _ ≤ X := by
                                simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
                                exact_mod_cast hn.1.2
                          have h₂₁₅₈₃₅ : (Nat.factorization n) (Nat.minFac n) ≤ Nat.log 2 X := by
                            by_contra h₂₁₅₈₃₆
                            have h₂₁₅₈₃₇ : Nat.log 2 X < (Nat.factorization n) (Nat.minFac n) := by omega
                            have h₂₁₅₈₃₈ : 2 ^ (Nat.factorization n) (Nat.minFac n) > X := by
                              have h₂₁₅₈₃₉ : 2 ^ (Nat.log 2 X + 1) > X := by
                                have h₂₁₅₈₄₀ : 2 ^ (Nat.log 2 X + 1) > X := by
                                  calc
                                    2 ^ (Nat.log 2 X + 1) = 2 ^ Nat.log 2 X * 2 := by ring_nf
                                    _ > X := by
                                      have h₂₁₅₈₄₁ : 2 ^ Nat.log 2 X > X / 2 := by
                                        have h₂₁₅₈₄₂ : 2 ^ Nat.log 2 X > X / 2 := by
                                          have h₂₁₅₈₄₃ : 2 ^ Nat.log 2 X > X / 2 := by
                                            calc
                                              2 ^ Nat.log 2 X ≥ X / 2 + 1 := by
                                                have h₂₁₅₈₄₄ := Nat.log2_le_iff (by
                                                  simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
                                                  omega)
                                                have h₂₁₅₈₄₅ : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log2_le_self X
                                                have h₂₁₅₈₄₆ : X < 2 ^ (Nat.log 2 X + 1) := by
                                                  calc
                                                    X < 2 ^ (Nat.log 2 X + 1) := by
                                                      have h₂₁₅₈₄₇ := Nat.lt_pow_succ_log2 (by
                                                        simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
                                                        omega)
                                                      exact h₂₁₅₈₄₇
                                                    _ = 2 ^ (Nat.log 2 X + 1) := by ring_nf
                                                omega
                                          _ > X / 2 := by omega
                                        exact h₂₁₅₈₄₃
                                      exact h₂₁₅₈₄₂
                                    have h₂₁₅₈₄₃ : (2 : ℕ) ^ Nat.log 2 X * 2 > X := by
                                      have h₂₁₅₈₄₄ : (2 : ℕ) ^ Nat.log 2 X > X / 2 := h₂₁₅₈₄₁
                                      have h₂₁₅₈₄₅ : (2 : ℕ) ^ Nat.log 2 X * 2 > X := by
                                        omega
                                      exact h₂₁₅₈₄₅
                                    omega
                              have h₂₁₅₈₄₀ : 2 ^ (Nat.factorization n) (Nat.minFac n) ≥ 2 ^ (Nat.log 2 X + 1) := by
                                exact Nat.pow_le_pow_of_le_right (by norm_num) (by omega)
                              linarith
                            linarith
                          exact h₂₁₅₈₃₅
                        exact ⟨by omega, by omega⟩
                      exact ⟨h₂₁₅₈₁₄, h₂₁₅₈₁₆⟩
                    -- Use the injection to bound the cardinality
                    have h₂₁₅₈₁₄ : S.card ≤ T.card := by
                      classical
                      -- Define the function from S to T
                      let f : ℕ → ℕ × ℕ := fun n => (Nat.minFac n, (Nat.factorization n) (Nat.minFac n))
                      have h₂₁₅₈₁₅ : ∀ n ∈ S, f n ∈ T := by
                        intro n hn
                        exact h₂₁₅₈₁₃ n hn
                      have h₂₁₅₈₁₆ : Set.Injective (fun n : ℕ => (Nat.minFac n, (Nat.factorization n) (Nat.minFac n))) := by
                        intro n m h
                        simp_all [Prod.ext_iff]
                        <;> aesop
                      -- Use the fact that the function is injective to bound the cardinality
                      have h₂₁₅₈₁₇ : S.card ≤ T.card := by
                        calc
                          S.card = (S.image f).card := by
                            rw [Finset.card_image_of_injective h₂₁₅₈₁₆]
                          _ ≤ T.card := by
                            apply Finset.card_le_of_subset
                            intro x hx
                            simp only [Finset.mem_image, f] at hx
                            obtain ⟨n, hn, rfl⟩ := hx
                            exact h₂₁₅₈₁₅ n hn
                      exact h₂₁₅₈₁₇
                    exact h₂₁₅₈₁₄
                  exact h₂₁₅₈₁₂
                calc
                  ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)).card ≤ (Finset.Icc 1 ⌊Real.sqrt X⌋₊).card * (Nat.log 2 X) := by
                    have h₂₁₅₈₁₈ : T.card = (Finset.Icc 1 ⌊Real.sqrt X⌋₊).card * (Nat.log 2 X) := by
                      simp [T, Finset.card_product, Finset.Icc_eq_empty, Nat.cast_le]
                      <;> cases' le_or_lt ⌊Real.sqrt X⌋₊ 1 with h h <;> simp_all [Finset.Icc_eq_empty]
                      <;> cases' le_or_lt (Nat.log 2 X) 1 with h h <;> simp_all [Finset.Icc_eq_empty]
                      <;> ring_nf
                      <;> norm_num
                      <;> omega
                    have h₂₁₅₈₁₉ : S.card ≤ T.card := h₂₁₅₈₁
                    linarith
                  _ = (Finset.Icc 1 ⌊Real.sqrt X⌋₊).card * (Nat.log 2 X) := by rfl
              have h₂₁₅₉ : (Finset.Icc 1 ⌊Real.sqrt X⌋₊).card = ⌊Real.sqrt X⌋₊ := by
                simp [Finset.Icc_eq_empty, Nat.cast_le]
                <;> cases' le_or_lt ⌊Real.sqrt X⌋₊ 1 with h h <;> simp_all [Finset.Icc_eq_empty]
                <;> norm_num
                <;> linarith [Nat.floor_le (Real.sqrt X)]
              have h₂₁₅₁₀ : (Finset.Icc 1 ⌊Real.sqrt X⌋₊).card * (Nat.log 2 X) = ⌊Real.sqrt X⌋₊ * (Nat.log 2 X) := by
                rw [h₂₁₅₉]
                <;> ring
              calc
                ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)).card ≤ (Finset.Icc 1 ⌊Real.sqrt X⌋₊).card * (Nat.log 2 X) := h₂₁₅₈
                _ = ⌊Real.sqrt X⌋₊ * (Nat.log 2 X) := by rw [h₂₁₅₁₀]
            exact h₂₁₅₇
          have h₂₁₆ : (⌊Real.sqrt X⌋₊ : ℝ) ≤ Real.sqrt X := by
            exact_mod_cast Nat.floor_le (Real.sqrt X)
          have h₂₁₇ : (Nat.log 2 X : ℝ) ≤ Real.log X / Real.log 2 := by
            have h₂₁₇₁ : (2 : ℝ) ^ (Nat.log 2 X : ℕ) ≤ X := by
              exact_mod_cast Nat.pow_log2_le_self X
            have h₂₁₇₂ : Real.log ((2 : ℝ) ^ (Nat.log 2 X : ℕ)) ≤ Real.log X := Real.log_le_log (by positivity) h₂₁₇₁
            have h₂₁₇₃ : Real.log ((2 : ℝ) ^ (Nat.log 2 X : ℕ)) = (Nat.log 2 X : ℝ) * Real.log 2 := by
              rw [Real.log_pow]
              <;> norm_cast
              <;> field_simp [Real.log_mul, Real.log_rpow]
              <;> ring_nf
              <;> norm_num
            rw [h₂₁₇₃] at h₂₁₇₂
            have h₂₁₇₄ : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
            have h₂₁₇₅ : (Nat.log 2 X : ℝ) * Real.log 2 ≤ Real.log X := by linarith
            have h₂₁₇₆ : (Nat.log 2 X : ℝ) ≤ Real.log X / Real.log 2 := by
              rw [le_div_iff h₂₁₇₄]
              nlinarith
            exact h₂₁₇₆
          have h₂₁₈ : ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)).card * Real.log X ≤ Real.sqrt X * Real.log X ^ 2 / Real.log 2 := by
            have h₂₁₈₁ : ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)).card ≤ ⌊Real.sqrt X⌋₊ * (Nat.log 2 X) := h₂₁₅
            have h₂₁₈₂ : (⌊Real.sqrt X⌋₊ : ℝ) ≤ Real.sqrt X := h₂₁₆
            have h₂₁₈₃ : (Nat.log 2 X : ℝ) ≤ Real.log X / Real.log 2 := h₂₁₇
            have h₂₁₈₄ : 0 ≤ Real.log X := Real.log_nonneg (by norm_cast <;> omega)
            have h₂₁₈₅ : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
            have h₂₁₈₆ : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have h₂₁₈₇ : 0 ≤ (⌊Real.sqrt X⌋₊ : ℝ) := by positivity
            have h₂₁₈₈ : 0 ≤ (Nat.log 2 X : ℝ) := by positivity
            calc
              (((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)).card : ℝ) * Real.log X ≤ (⌊Real.sqrt X⌋₊ * (Nat.log 2 X) : ℝ) * Real.log X := by
                exact_mod_cast h₂₁₈₁ |>.mul_le_mul_of_nonneg_right h₂₁₈₄
              _ = (⌊Real.sqrt X⌋₊ : ℝ) * (Nat.log 2 X : ℝ) * Real.log X := by norm_cast <;> ring_nf
              _ ≤ (Real.sqrt X : ℝ) * (Real.log X / Real.log 2) * Real.log X := by
                gcongr <;> norm_num <;> nlinarith
              _ = Real.sqrt X * Real.log X ^ 2 / Real.log 2 := by
                field_simp [h₂₁₈₆.ne']
                <;> ring_nf
                <;> field_simp [h₂₁₈₆.ne']
                <;> ring_nf
          calc
            ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), (vonMangoldt n : ℝ) ≤ ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), (Real.log X : ℝ) := h₂₁₃
            _ = ((Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0)).card * Real.log X := by rw [h₂₁₄]
            _ ≤ Real.sqrt X * Real.log X ^ 2 / Real.log 2 := h₂₁₈
        calc
          ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ) = ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0), (vonMangoldt n : ℝ) := h₂₁₁
          _ ≤ Real.sqrt X * Real.log X ^ 2 / Real.log 2 := h₂₁₂
      have h₂₂ : (Real.sqrt X : ℝ) * Real.log X ^ 2 / Real.log 2 ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 := by
        have h₂₂₁ : (X : ℝ) ≥ 2 := by exact_mod_cast hX
        have h₂₂₂ : Real.log X ≥ 0 := Real.log_nonneg (by linarith)
        have h₂₂₃ : Real.log X ^ 2 ≥ 0 := by positivity
        have h₂₂₄ : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h₂₂₅ : 0 < (X : ℝ) := by linarith
        have h₂₂₆ : 0 < Real.sqrt X := Real.sqrt_pos.mpr (by positivity)
        by_cases h₂₂₇ : Real.log X = 0
        · have h₂₂₈ : X = 1 := by
            have h₂₂₉ : Real.log X = 0 := h₂₂₇
            have h₂₃₀ : X ≤ 1 := by
              by_contra h
              have h₂₃₁ : X ≥ 2 := by omega
              have h₂₃₂ : Real.log X ≥ Real.log 2 := Real.log_le_log (by positivity) (by exact_mod_cast h₂₃₁)
              have h₂₃₃ : Real.log 2 > 0 := Real.log_pos (by norm_num)
              linarith
            have h₂₃₄ : X ≥ 2 := by exact_mod_cast hX
            linarith
          · have h₂₂₈ : 0 < Real.log X := by
              contrapose! h₂₂₇
              linarith
            have h₂₂₉ : 0 < Real.log X ^ 2 := by positivity
            have h₂₃₀ : (Real.sqrt X : ℝ) / Real.log 2 ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) := by
              have h₂₃₁ : Real.sqrt X = (X : ℝ) ^ (1 / 2 : ℝ) := by
                rw [Real.sqrt_eq_rpow]
                <;> norm_num
              rw [h₂₃₁]
              have h₂₃₂ : (X : ℝ) ^ (1 / 2 : ℝ) / Real.log 2 ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) := by
                have h₂₃₃ : (X : ℝ) ^ (1 / 2 : ℝ) / Real.log 2 ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) := by
                  -- Use the fact that X ≥ 2 to bound the ratio
                  have h₂₃₄ : (X : ℝ) ^ (3 / 10 : ℝ) ≥ 1 := by
                    apply Real.one_le_rpow
                    <;> norm_num
                    <;> linarith
                  have h₂₃₅ : (2 : ℝ) * (X : ℝ) ^ (3 / 10 : ℝ) ≥ 2 := by
                    have h₂₃₆ : (X : ℝ) ^ (3 / 10 : ℝ) ≥ 1 := h₂₃₄
                    nlinarith
                  have h₂₃₆ : (1 : ℝ) / Real.log 2 < 2 := by
                    have h₂₃₇ : Real.log 2 > 0 := Real.log_pos (by norm_num)
                    have h₂₃₈ : (1 : ℝ) / Real.log 2 < 2 := by
                      rw [div_lt_iff h₂₃₇]
                      have := Real.log_two_gt_d9
                      norm_num at this ⊢
                      <;> nlinarith
                    exact h₂₃₈
                  have h₂₃₇ : (X : ℝ) ^ (1 / 2 : ℝ) / Real.log 2 = (1 / Real.log 2) * (X : ℝ) ^ (1 / 2 : ℝ) := by ring
                  have h₂₃₈ : 2 * (X : ℝ) ^ (4 / 5 : ℝ) = 2 * (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (3 / 10 : ℝ) := by
                    have h₂₃₉ : (X : ℝ) ^ (4 / 5 : ℝ) = (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (3 / 10 : ℝ) := by
                      have h₂₄₀ : (4 / 5 : ℝ) = (1 / 2 : ℝ) + (3 / 10 : ℝ) := by norm_num
                      rw [h₂₄₀]
                      rw [Real.rpow_add (by positivity)]
                      <;> ring_nf
                    rw [h₂₃₉]
                    <;> ring
                  rw [h₂₃₇, h₂₃₈]
                  have h₂₃₉ : (1 / Real.log 2 : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (3 / 10 : ℝ) := by
                    have h₂₄₀ : 0 < (X : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
                    have h₂₄₁ : (1 / Real.log 2 : ℝ) ≤ 2 * (X : ℝ) ^ (3 / 10 : ℝ) := by
                      have h₂₄₂ : (1 / Real.log 2 : ℝ) < 2 := by
                        have h₂₄₃ : Real.log 2 > 0 := Real.log_pos (by norm_num)
                        have h₂₄₄ : (1 : ℝ) / Real.log 2 < 2 := by
                          rw [div_lt_iff h₂₄₃]
                          have := Real.log_two_gt_d9
                          norm_num at this ⊢
                          <;> nlinarith
                        exact h₂₄₄
                      have h₂₄₃ : (2 : ℝ) ≤ 2 * (X : ℝ) ^ (3 / 10 : ℝ) := by
                        have h₂₄₄ : (1 : ℝ) ≤ (X : ℝ) ^ (3 / 10 : ℝ) := h₂₃₄
                        nlinarith
                      linarith
                    nlinarith
                  nlinarith
                exact h₂₃₃
              exact h₂₃₂
            have h₂₃₁ : (Real.sqrt X : ℝ) * Real.log X ^ 2 / Real.log 2 ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 := by
              have h₂₃₂ : (Real.sqrt X : ℝ) / Real.log 2 ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) := h₂₃₀
              have h₂₃₃ : 0 ≤ Real.log X ^ 2 := by positivity
              have h₂₃₄ : (Real.sqrt X : ℝ) * Real.log X ^ 2 / Real.log 2 = ((Real.sqrt X : ℝ) / Real.log 2) * Real.log X ^ 2 := by
                ring
              rw [h₂₃₄]
              have h₂₃₅ : 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 = (2 * (X : ℝ) ^ (4 / 5 : ℝ)) * Real.log X ^ 2 := by ring
              rw [h₂₃₅]
              nlinarith
            exact h₂₃₁
      linarith
    linarith
  calc
    ‖Ssum m α - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime), (vonMangoldt n : ℂ) * ee (α * n)‖ ≤ ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), (vonMangoldt n : ℝ) := h_main
    _ ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 := h_sum_le

/-- PROVED in this file, no sorry. P0029 page 27, proof of Lemma 7.3, display 7.8, minor arc
part, the transfer of the minor arc estimate from S to the smoothed sum S_phi by summation by
parts, for the prime restricted smoothed sum. For admissible phi with Lipschitz constant L, every
cutoff N at most X, and a nonnegative B bounding every prime restricted partial sum up to
m at most N, the prime restricted smoothed sum of length X at cutoff N has modulus at most
L times B. This is the prime analogue of the proved `Sphi_of_partial_bound261`; phi of n
over N vanishes for n at least N, so the length X plays no role. -/
theorem leaf_prime_parts_feed1122 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {X N : ℕ} (hNX : N ≤ X) {α B : ℝ}
    (hB : 0 ≤ B)
    (hpartial : ∀ m ≤ N, ‖∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n)‖ ≤ B) :
    ‖∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
        ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)‖ ≤ (L : ℝ) * B := by
  classical
  set a : ℕ → ℂ := fun n => if n.Prime then (vonMangoldt n : ℂ) * ee (α * n) else 0 with ha
  have hpart' : ∀ m ≤ N, ‖∑ k ∈ Finset.range (m + 1), a k‖ ≤ B := by
    intro m hm
    have hc : (∑ k ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt k : ℂ) * ee (α * k)) = ∑ k ∈ Finset.range (m + 1), a k := by
      rw [Finset.sum_filter]
      apply Finset.sum_subset
      · intro x hx
        simp only [Finset.mem_Icc] at hx
        simp only [Finset.mem_range]
        omega
      · intro x _ hx
        have hx0 : x = 0 := by
          by_contra h0
          apply hx
          simp only [Finset.mem_Icc]
          constructor
          · omega
          · simp only [Finset.mem_range] at *
            omega
        subst hx0
        simp [ha, Nat.not_prime_zero]
    rw [← hc]
    exact hpartial m hm
  have hmain : (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
        ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) =
      ∑ n ∈ Finset.range (X + 1), ϕ ((n : ℝ) / N) • a n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime
    · simp only [hp, ite_true, ha, Complex.real_smul]
      push_cast
      ring
    · simp [hp, ha]
  rw [hmain]
  by_cases hN : N = 0
  · subst N
    have h0 : ϕ 0 = 0 := by
      by_contra h
      have hs := hϕ.supp (subset_tsupport ϕ h)
      linarith [hs.1]
    simp [h0]
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hcut : (∑ n ∈ Finset.range (X + 1), ϕ ((n : ℝ) / N) • a n) =
      ∑ n ∈ Finset.range (N + 1), ϕ ((n : ℝ) / N) • a n := by
    symm
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at *
      omega
    · intro x _ hx
      simp only [Finset.mem_range, not_lt] at hx
      have h1 : (1 : ℝ) ≤ (x : ℝ) / N := by
        rw [le_div_iff₀ hNpos]
        have : (N : ℝ) + 1 ≤ x := by exact_mod_cast hx
        linarith
      rw [phi_zero_ge_one261 hϕ h1, zero_smul]
  rw [hcut]
  have hphi1 : ϕ ((N : ℝ) / N) = 0 := by
    rw [div_self hNpos.ne']
    exact phi_zero_ge_one261 hϕ le_rfl
  have hparts := Finset.sum_range_by_parts (fun n : ℕ => ϕ ((n : ℝ) / N)) a (N + 1)
  have hrepr : (∑ n ∈ Finset.range (N + 1), ϕ ((n : ℝ) / N) • a n) =
      -(∑ n ∈ Finset.range N, (ϕ (((n + 1 : ℕ) : ℝ) / N) - ϕ ((n : ℝ) / N)) •
        ∑ k ∈ Finset.range (n + 1), a k) := by
    simpa only [Nat.add_sub_cancel, hphi1, zero_smul, zero_sub] using hparts
  have hstep (n : ℕ) :
      |ϕ (((n + 1 : ℕ) : ℝ) / N) - ϕ ((n : ℝ) / N)| ≤ (L : ℝ) / N := by
    have h := hL.norm_sub_le (((n + 1 : ℕ) : ℝ) / N) ((n : ℝ) / N)
    simp only [Real.norm_eq_abs] at h
    have heq : ((n + 1 : ℕ) : ℝ) / N - (n : ℝ) / N = 1 / N := by push_cast; ring
    rw [heq, abs_of_pos (one_div_pos.mpr hNpos)] at h
    simpa only [div_eq_mul_inv, one_mul] using h
  rw [hrepr, norm_neg]
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        ‖(ϕ (((n + 1 : ℕ) : ℝ) / N) - ϕ ((n : ℝ) / N)) •
          ∑ k ∈ Finset.range (n + 1), a k‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, ((L : ℝ) / N) * B := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hstep n) (hpart' n (by simp only [Finset.mem_range] at hn; omega))
        (norm_nonneg _) (by positivity)
    _ = (L : ℝ) * B := by simp; field_simp

/-- LEAF: P0029 page 27, proof of Lemma 7.3, display 7.8, the family second moment over the
cutoff N with the minor arc supremum pulled out, for the prime restricted smoothed sum.
Class MEDIUM. For admissible phi there is a nonnegative K such that for every X at least two,
every measurable multiplier W bounded by B, and every U bounding the prime restricted smoothed
sum of length X at every cutoff n at most X wherever W is nonzero, the sum over N from one to
X of the squared modulus of the integral over the unit interval of the square of the prime
restricted smoothed sum at cutoff N times W times e of minus N alpha is at most K times B
squared times U squared times X times log X. This is the prime analogue of the proved
`supported_family_sharp261`, whose constant is 96 times L squared. -/
theorem leaf_prime_family_feed1122 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X : ℕ), 2 ≤ X → ∀ (W : ℝ → ℂ), Measurable W →
      ∀ (B U : ℝ), 0 ≤ B → 0 ≤ U → (∀ α, ‖W α‖ ≤ B) →
      (∀ n ≤ X, ∀ α, W α ≠ 0 →
        ‖∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
          ((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ ≤ U) →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
            ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) ^ 2 * W α *
            ee (-(N * α))‖ ^ 2 ≤
        K * B ^ 2 * U ^ 2 * X * Real.log X := by
  have h_main : ∃ (K : ℝ), 0 ≤ K ∧ ∀ (X : ℕ), 2 ≤ X → ∀ (W : ℝ → ℂ), Measurable W →
      ∀ (B U : ℝ), 0 ≤ B → 0 ≤ U → (∀ α, ‖W α‖ ≤ B) →
      (∀ n ≤ X, ∀ α, W α ≠ 0 →
        ‖∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
          ((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ ≤ U) →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
            ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) ^ 2 * W α *
            ee (-(N * α))‖ ^ 2 ≤
        K * B ^ 2 * U ^ 2 * X * Real.log X := by
    -- Use the same proof structure as supported_family_sharp261
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
    obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
    have hM' : ∀ x, |ϕ x| ≤ M := by
      intro x
      exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x)
    -- The proof follows supported_family_sharp261 with the prime-restricted sum
    have h₁ : ∃ (K : ℝ), 0 ≤ K ∧ ∀ (X : ℕ), 2 ≤ X → ∀ (W : ℝ → ℂ), Measurable W →
        ∀ (B U : ℝ), 0 ≤ B → 0 ≤ U → (∀ α, ‖W α‖ ≤ B) →
        (∀ n ≤ X, ∀ α, W α ≠ 0 →
          ‖∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
            ((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ ≤ U) →
        ∑ N ∈ Finset.Icc 1 X,
          ‖∫ α in (0 : ℝ)..1,
            (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
              ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) ^ 2 * W α *
              ee (-(N * α))‖ ^ 2 ≤
          K * B ^ 2 * U ^ 2 * X * Real.log X := by
      classical
      -- Get the Lipschitz constant and bound for ϕ
      obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
      obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
      have hb : ∀ x, |ϕ x| ≤ max M 0 := by
        intro x
        exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans (le_max_left M 0)
      -- Define the prime-restricted smoothed sum for a given cutoff n
      let Sphi_prime (n : ℕ) (α : ℝ) : ℂ := ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime), ((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)
      -- Uniform bound for the prime-restricted sum: same as Sphi_uniform261
      have h_uniform : ∀ (n : ℕ) (α : ℝ), ‖Sphi_prime n α‖ ≤ 6 * (max M 0 : ℝ) * n := by
        intro n α
        have h₁ : ‖Sphi_prime n α‖ ≤ ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime), ‖((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ := by
          calc
            _ = ‖∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime), ((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ := rfl
            _ ≤ ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime), ‖((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ := norm_sum_le _ _
        have h₂ : ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime), ‖((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ ≤ ∑ k ∈ Finset.range (n + 1), (vonMangoldt k : ℝ) * (max M 0 : ℝ) := by
          have h₃ : ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime), ‖((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ ≤ ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime), (vonMangoldt k : ℝ) * (max M 0 : ℝ) := by
            apply Finset.sum_le_sum
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_range] at hk
            have h₄ : ‖((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ = (vonMangoldt k : ℝ) * |ϕ (k / n)| := by
              simp [norm_mul, Complex.norm_eq_abs, Complex.abs_ofReal, Real.norm_eq_abs, abs_mul, abs_of_nonneg vonMangoldt_nonneg, ee_eq_library84, LeanLab.PNTPort.LargeSieve.norm_e]
              <;> ring_nf
              <;> simp [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
              <;> norm_cast
            rw [h₄]
            have h₅ : |ϕ (k / n)| ≤ max M 0 := by
              have h₆ : |ϕ (k / n)| ≤ M := by
                exact hb (k / n)
              have h₇ : (M : ℝ) ≤ max M 0 := by apply le_max_left
              linarith
            have h₆ : (vonMangoldt k : ℝ) ≥ 0 := by exact_mod_cast vonMangoldt_nonneg
            have h₇ : (vonMangoldt k : ℝ) * |ϕ (k / n)| ≤ (vonMangoldt k : ℝ) * (max M 0 : ℝ) := by
              exact mul_le_mul_of_nonneg_left h₅ h₆
            linarith
          have h₄ : ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime), (vonMangoldt k : ℝ) * (max M 0 : ℝ) ≤ ∑ k ∈ Finset.range (n + 1), (vonMangoldt k : ℝ) * (max M 0 : ℝ) := by
            have h₅ : (Finset.range (X + 1)).filter (fun k => k.Prime) ⊆ Finset.range (n + 1) := by
              apply Finset.filter_subset
              apply Finset.range_subset.2
              have h₆ : X + 1 ≤ n + 1 := by
                have h₇ : X ≤ n := by
                  by_contra h
                  have h₈ : n < X := by omega
                  have h₉ : n ≤ X := by omega
                  -- This case shouldn't happen in our usage, but we handle it
                  simp_all [Finset.mem_range]
                  <;> omega
                omega
              exact h₆
            have h₆ : ∀ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime), 0 ≤ (vonMangoldt k : ℝ) * (max M 0 : ℝ) := by
              intro k hk
              have h₇ : 0 ≤ (vonMangoldt k : ℝ) := by exact_mod_cast vonMangoldt_nonneg
              have h₈ : 0 ≤ (max M 0 : ℝ) := by positivity
              positivity
            exact Finset.sum_le_sum_of_subset_of_nonneg h₅ h₆
          linarith
        have h₃ : ∑ k ∈ Finset.range (n + 1), (vonMangoldt k : ℝ) * (max M 0 : ℝ) = (max M 0 : ℝ) * ∑ k ∈ Finset.range (n + 1), (vonMangoldt k : ℝ) := by
          rw [Finset.mul_sum]
          <;> ring
        have h₄ : ∑ k ∈ Finset.range (n + 1), (vonMangoldt k : ℝ) ≤ 6 * n := by
          have h₅ : ∑ k ∈ Finset.range (n + 1), vonMangoldt k ≤ 6 * n := by
            have h₆ : ∑ k ∈ Finset.range (n + 1), vonMangoldt k ≤ 6 * n := by
              -- Use the mangoldt_mass261 lemma
              have h₇ : ∑ k ∈ Finset.range (n + 1), vonMangoldt k ≤ 6 * n := by
                exact_mod_cast LeanLab.BhowmikGrimmelt2026.mangoldt_mass261 n
              exact h₇
            exact h₆
          calc
            _ = (max M 0 : ℝ) * ∑ k ∈ Finset.range (n + 1), (vonMangoldt k : ℝ) := by rw [h₃]
            _ ≤ (max M 0 : ℝ) * (6 * n : ℝ) := by
              gcongr
            _ = 6 * (max M 0 : ℝ) * n := by ring
        calc
          ‖Sphi_prime n α‖ ≤ ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime), ‖((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ := h₁
          _ ≤ ∑ k ∈ Finset.range (n + 1), (vonMangoldt k : ℝ) * (max M 0 : ℝ) := h₂
          _ = (max M 0 : ℝ) * ∑ k ∈ Finset.range (n + 1), (vonMangoldt k : ℝ) := by rw [h₃]
          _ ≤ 6 * (max M 0 : ℝ) * n := by
            linarith
      -- Define F j α = (Sphi_prime j α)^2 * W α
      let F (j : ℕ) (α : ℝ) : ℂ := (Sphi_prime j α) ^ 2 * W α
      -- Prove F j ∈ L^p using the uniform bound
      have hLp (j : ℕ) : MemLp (F j) 2 (volume.restrict (Set.Ioc 0 1)) := by
        apply MemLp.of_bound (((continuous_Sphi_prime j).pow 2).measurable.mul hW).aestronglyMeasurable ((6 * (max M 0 : ℝ) * j : ℝ) ^ 2 * B)
        apply Filter.Eventually.of_forall
        intro α
        change ‖F j α‖ ≤ _
        simp only [F]
        rw [norm_mul, norm_pow]
        exact mul_le_mul
          (pow_le_pow_left₀ (norm_nonneg _) (h_uniform j α) 2)
          (hWB α) (norm_nonneg _) (sq_nonneg _)
      -- The rest follows supported_family_sharp261
      have hS0 : F 0 = 0 := by
        funext α
        simp [F, Sphi_prime]
        <;> norm_num
        <;> simp [Finset.sum_range_zero]
      have hS1 : F 1 = 0 := by
        funext α
        simp [F, Sphi_prime]
        <;> norm_num [Finset.sum_range_succ]
        <;> simp_all [Nat.Prime]
        <;> aesop
      have hzero : F 0 = 0 := hS0
      have hint (j : ℕ) : IntervalIntegrable (F j) volume 0 1 := by
        apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
        exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (hLp j)
      have hinc (j : ℕ) (_hj : j ∈ Finset.Icc 1 X) :
          MemLp (fun α => F j α - F (j - 1) α) 2 (volume.restrict (Set.Ioc 0 1)) := by
        have h₁ : MemLp (F j) 2 (volume.restrict (Set.Ioc 0 1)) := hLp j
        have h₂ : MemLp (F (j - 1)) 2 (volume.restrict (Set.Ioc 0 1)) := hLp (j - 1)
        exact h₁.sub h₂
      have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
      -- Energy increment bound (analogue of supported_increment261)
      have hE (j : ℕ) (hj : j ∈ Finset.Icc 1 X) :
          (∫ α in (0 : ℝ)..1, ‖F j α - F (j - 1) α‖ ^ 2) ≤ 24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * Real.log X / j := by
        sorry
      -- Use family_inverse_energy261 to get the final bound
      have h₂ : ∑ N ∈ Finset.Icc 1 X, ‖∫ α in (0 : ℝ)..1, F N α * ee (-(N * α))‖ ^ 2 ≤ 96 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X := by
        sorry
      -- Convert back to the original statement
      refine' ⟨96 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2, by positivity, _⟩
      intro X hX W hW B U hB hU hWB hsup
      have h₃ := h₂
      simp only [F, Sphi_prime] at h₃ ⊢
      <;> simp_all [mul_assoc]
      <;> norm_num
      <;> linarith
    exact h₁
  exact h₁
  obtain ⟨K, hK, h₂⟩ := h_main
  refine' ⟨K, hK, _⟩
  intro X hX W hW B U hB hU hWB hsup
  exact h₂ X hX W hW B U hB hU hWB hsup
  obtain ⟨K, hK, h₂⟩ := h_main
  refine' ⟨K, hK, _⟩
  intro X hX W hW B U hB hU hWB hsup
  exact h₂ X hX W hW B U hB hU hWB hsup

/-- Assembly: `prime_minor_multi_451` with exactly its statement, from the reused leaf
`split_leaf_ssum_minor_log2` and the three leaves above. -/
theorem prime_minor_multi_451_from_leaves {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
              ee (-(N * α))‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  classical
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  obtain ⟨C₀, hC₀, h₀⟩ := split_leaf_ssum_minor_log2
  obtain ⟨K, hK, hfamK⟩ := leaf_prime_family_feed1122 hϕ
  refine ⟨2 * K * ((L : ℝ) * (C₀ + 2)) ^ 2, by positivity, ?_⟩
  intro X hX _hR2
  set R : ℝ := (X : ℝ) ^ ϑ with hRdef
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < R := by linarith
  have hRX : R ≤ X := by
    calc
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = _ := Real.rpow_one _
  set A : ℝ := (X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hlog2 : 0 ≤ Real.log X ^ 2 := by positivity
  have hX45 : (X : ℝ) ^ (4 / 5 : ℝ) ≤ A := by
    have : 0 ≤ (X : ℝ) / Real.sqrt R := by positivity
    linarith
  let W : ℝ → ℂ := fun α => if MajorArc X R α then 0 else 1
  have hW : Measurable W :=
    measurable_const.ite (measurableSet_majorArc84 X R) measurable_const
  have hWB (α : ℝ) : ‖W α‖ ≤ (1 : ℝ) := by
    by_cases hm : MajorArc X R α <;> simp [W, hm]
  set U : ℝ := (L : ℝ) * ((C₀ + 2) * A * Real.log X ^ 2) with hUdef
  have hU0 : 0 ≤ U := by positivity
  have hsup : ∀ n ≤ X, ∀ α, W α ≠ 0 →
      ‖∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
        ((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ ≤ U := by
    intro n hn α hne
    have hm : ¬ MajorArc X R α := by
      intro hh
      exact hne (by simp [W, hh])
    have hBn : 0 ≤ (C₀ + 2) * A * Real.log X ^ 2 := by positivity
    apply leaf_prime_parts_feed1122 hϕ hL hn hBn
    intro m hmn
    have hmX : m ≤ X := hmn.trans hn
    have hS := h₀ X hX R hR1 hRX m hmX α hm
    have hD := leaf_nonprime_partial_feed1122 hX hmX α
    have htri : ‖∑ k ∈ (Finset.Icc 1 m).filter (fun k => k.Prime),
        (vonMangoldt k : ℂ) * ee (α * k)‖ ≤
        ‖Ssum m α‖ + ‖Ssum m α - ∑ k ∈ (Finset.Icc 1 m).filter (fun k => k.Prime),
          (vonMangoldt k : ℂ) * ee (α * k)‖ := by
      have := norm_sub_le (Ssum m α) (Ssum m α -
        ∑ k ∈ (Finset.Icc 1 m).filter (fun k => k.Prime), (vonMangoldt k : ℂ) * ee (α * k))
      simpa using this
    have hD' : 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 ≤ 2 * A * Real.log X ^ 2 := by
      gcongr
    have hexp : (C₀ + 2) * A * Real.log X ^ 2 =
        C₀ * A * Real.log X ^ 2 + 2 * A * Real.log X ^ 2 := by ring
    linarith
  have hfam := hfamK X hX W hW 1 U (by norm_num) hU0 hWB hsup
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1,
          (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
            ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) ^ 2 * W α *
            ee (-(N * α))) =
      ∫ α in (0 : ℝ)..1,
          if MajorArc X R α then 0 else
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
              ee (-(N * α)) := by
    apply intervalIntegral.integral_congr
    intro α _
    by_cases hm : MajorArc X R α <;> simp [W, hm]
  simp_rw [heq] at hfam
  have hA2 : ((X : ℝ) / Real.sqrt R) ^ 2 = (X : ℝ) ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hRp.le]
  have hD2 : ((X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 = (X : ℝ) ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
    norm_num
  have hsq : A ^ 2 ≤ 2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) := by
    rw [← hA2, ← hD2, hAdef]
    nlinarith only [sq_nonneg ((X : ℝ) / Real.sqrt R - (X : ℝ) ^ (4 / 5 : ℝ))]
  have hlogX : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  have hpi := split_leaf_power_identity X hX ϑ
  calc
    _ ≤ K * 1 ^ 2 * U ^ 2 * X * Real.log X := hfam
    _ = K * ((L : ℝ) * (C₀ + 2)) ^ 2 * A ^ 2 * X * Real.log X ^ 5 := by
      rw [hUdef]; ring
    _ ≤ K * ((L : ℝ) * (C₀ + 2)) ^ 2 *
        (2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ))) * X * Real.log X ^ 5 := by
      gcongr
    _ = 2 * K * ((L : ℝ) * (C₀ + 2)) ^ 2 *
        (((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) * (X : ℝ)) *
          Real.log X ^ 5 := by
      rw [hRdef]; ring
    _ = _ := by
      rw [hpi, hRdef]; ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_nonprime_partial_feed1122
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_prime_parts_feed1122
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_prime_family_feed1122
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_multi_451_from_leaves
