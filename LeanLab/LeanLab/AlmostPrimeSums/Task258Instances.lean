import LeanLab.AlmostPrimeSums.RosserAnalytic
import LeanLab.AlmostPrimeSums.RosserFirst

/-!
AI wrote these concrete instances for CODEX task258. Goldbach is open.
Sources and plain math twins are in STATEMENTS.md. None of these examples
uses either new analytic leaf or the fundamental lemma proof placeholder.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real BoundingSieve

example : rosserDefect 2 true 2 = 1 := by
  norm_num [rosserDefect, rosserWeight, decPrimes, Nat.prime_two.primeFactors,
    Nat.prime_two.squarefree, ArithmeticFunction.moebius_apply_prime Nat.prime_two]

example : rosserDefect 2 false 6 = 1 := by
  have hd : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
  have hf : (6 : ℕ).primeFactors = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
  have hs : Squarefree 6 := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.squarefree_mul_iff]
    exact ⟨by decide, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  have hsort : ({2, 3} : Finset ℕ).sort (· ≥ ·) = [3, 2] := by
    have he : ({2, 3} : Finset ℕ) = insert 3 {2} := by ext n; simp [or_comm]
    rw [he, Finset.sort_insert (· ≥ ·) (by simp) (by simp)]
    simp
  norm_num [rosserDefect, hd, rosserWeight, decPrimes, hf, hs, hsort,
    Nat.prime_two.primeFactors, Nat.prime_three.primeFactors,
    Nat.prime_two.squarefree, Nat.prime_three.squarefree,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  exact ⟨1, by norm_num, by norm_num, by norm_num⟩

example : 0 ≤ rosserDefect 2 true 2 ∧ 0 ≤ rosserDefect 2 false 6 :=
  ⟨rosserDefect_nonneg _ _ _, rosserDefect_nonneg _ _ _⟩

example : rosserDefect 100 true 2 = 0 ∧ rosserDefect 100 false 2 = 0 := by
  have hp : ∀ p ∈ (2 : ℕ).primeFactors, (p : ℝ) ≤ 3 := by
    simp [Nat.prime_two.primeFactors]
  exact ⟨rosserDefect_eq_zero_of_small 100 3 (by norm_num) true hp (by norm_num),
    rosserDefect_eq_zero_of_small 100 3 (by norm_num) false hp (by norm_num)⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ s.selbergTerms 2 = 1 ∧
    (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) = 1 / 2 ∧
    s.mainSum (fun _ => 1) = 3 / 2 := by
  obtain ⟨s, hP, _, hnu, _⟩ := single_prime_density_instance
  have h1 : s.nu 1 = 1 := s.nu_mult.map_one
  have hd : (2 : ℕ).divisors = {1, 2} := by decide
  refine ⟨s, hP, ?_, ?_, ?_⟩
  · norm_num [s.selbergTerms_apply, hnu, Nat.prime_two.primeFactors]
  · norm_num [hP, hnu, Nat.prime_two.primeFactors]
  · norm_num [BoundingSieve.mainSum, hP, hd, h1, hnu]

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    (∑ n ∈ s.prodPrimes.divisors, if 2 ∣ n then s.selbergTerms n else 0) =
      s.selbergTerms s.prodPrimes * s.nu 2 / s.nu s.prodPrimes := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  exact ⟨s, hP, sum_selbergTerms_multiples s (by rw [hP])⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    s.selbergTerms s.prodPrimes * (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) =
      s.nu s.prodPrimes := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  exact ⟨s, hP, selbergTerms_mul_eulerProduct s⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
      (∑ n ∈ s.prodPrimes.divisors, if 2 ∣ n then s.selbergTerms n else 0) = s.nu 2 := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  exact ⟨s, hP, eulerProduct_mul_selbergTerms_multiples s (by rw [hP])⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    s.mainSum (fun _ => 1) =
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        ∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * ∑ _d ∈ n.divisors, (1 : ℝ) := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  exact ⟨s, hP, mainSum_eq_selberg_average s (fun _ => 1)⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * (if n = 1 then 1 else 0)) = 1 := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  exact ⟨s, hP, selberg_average_indicator_one s⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    s.mainSum (fun _ => 0) ≤ s.mainSum (fun _ => 1) := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  refine ⟨s, hP, mainSum_mono_of_divisor_sum s (fun _ => 0) (fun _ => 1) ?_⟩
  intro n _
  simp

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    s.mainSum (fun _ => 1) - (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) =
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        ∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n *
          ((∑ _d ∈ n.divisors, (1 : ℝ)) - (if n = 1 then 1 else 0)) := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  exact ⟨s, hP, mainSum_sub_eulerProduct_eq s (fun _ => 1)⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) ≤ s.mainSum (rosserWeight 2 true) ∧
    s.mainSum (rosserWeight 2 false) ≤ ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  exact ⟨s, hP, mainSum_eulerProduct_signs s _ _
    (fun n _ => rosser_upper_isUpperMoebius 2 n) (fun n _ => rosser_lower_le 2 n)⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ ∀ upper : Bool,
    |s.mainSum (rosserWeight 2 upper) - (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p))| =
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        ∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect 2 upper n := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  exact ⟨s, hP, rosser_mainSum_error_eq s 2⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    ((s.mainSum (rosserWeight 2 true) ≤
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) * 2) ↔
      (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect 2 true n) ≤ 1) ∧
    (((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) * 1 ≤
      s.mainSum (rosserWeight 2 false)) ↔
      (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect 2 false n) ≤ 0) := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  refine ⟨s, hP, ?_, ?_⟩
  · convert rosser_upper_mainSum_iff_defect s 2 2 using 1; norm_num
  · simpa using rosser_lower_mainSum_iff_defect s 2 1

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ ∀ upper : Bool,
    s.mainSum (rosserWeight (3 ^ 10) upper) =
      ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  refine ⟨s, hP, ?_⟩
  intro upper
  apply rosser_mainSum_exact_of_card_le_seven s (3 ^ 10) 3 (by norm_num) le_rfl
  · intro p hp
    have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
    subst p; norm_num
  · simp [hP, Nat.prime_two.primeFactors]

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (2 : ℝ) ≤ p ∧ (p : ℝ) < 3),
      (1 - s.nu p)⁻¹) ≤ log 3 / log 2 * (1 + 1) := by
  obtain ⟨s, hP, _, _, hden, _⟩ := single_prime_density_instance
  refine ⟨s, hP, linearDensity_uniform_above s (log 2) 1 2 hden (by norm_num)
    (by norm_num) (by simp) 2 3 le_rfl (by norm_num)⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ rosserFirstBoundary s 2 = 1 / 2 ∧
    rosserFirstBoundary s 3 = 0 := by
  obtain ⟨s, hP, _, hnu, _⟩ := single_prime_density_instance
  refine ⟨s, hP, ?_, ?_⟩ <;>
    norm_num [rosserFirstBoundary, hP, hnu, Nat.prime_two.primeFactors, Finset.filter_singleton]

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ 0 ≤ rosserFirstBoundary s 2 ∧
    rosserFirstBoundary s 2 ≤ (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
      (log 3 / log 2 * (1 + log 2 / log 2) - 1) := by
  obtain ⟨s, hP, _, _, hden, _⟩ := single_prime_density_instance
  refine ⟨s, hP, rosserFirstBoundary_nonneg s 2,
    rosserFirstBoundary_le_density s (log 2) 2 3 hden (by norm_num) (by norm_num) ?_⟩
  intro p hp
  have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
  subst p; norm_num

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    rosserFirstBoundary s 3 = 0 := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  refine ⟨s, hP, rosserFirstBoundary_eq_zero s 3 ?_⟩
  intro p hp
  have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
  subst p; norm_num

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    rosserFirstBoundary s 2 =
      (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < 2), (1 - s.nu p)) -
        ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  exact ⟨s, hP, rosserFirstBoundary_eq_product_sub s 2⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    rosserFirstBoundary s 2 =
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        ((∏ p ∈ s.prodPrimes.primeFactors.filter
          (fun p : ℕ => (2 : ℝ) ≤ p ∧ (p : ℝ) < 3), (1 - s.nu p)⁻¹) - 1) := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  refine ⟨s, hP, rosserFirstBoundary_eq_relative s 2 3 ?_⟩
  intro p hp
  have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
  subst p; norm_num

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ ∀ upper : Bool,
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect 2 upper n) =
      ∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => (2 : ℝ) ≤ (n : ℝ) * 3 ^ 2),
        s.selbergTerms n * rosserDefect 2 upper n := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  refine ⟨s, hP, fun upper => rosser_defect_moment_eq_tail s 2 3 (by norm_num) ?_ upper⟩
  intro p hp
  have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
  subst p; norm_num

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ ∀ upper : Bool,
    s.mainSum (rosserWeight 100 upper) = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  refine ⟨s, hP, fun upper => rosser_mainSum_exact_of_prod_bound s 100 3 (by norm_num) ?_ ?_ upper⟩
  · intro p hp
    have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
    subst p; norm_num
  · rw [hP]; norm_num

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    (let Q := s.prodPrimes.primeFactors.filter (fun p : ℕ => (2 : ℝ) ≤ p ∧ (p : ℝ) < 3)
     let M := log (log 3 / log 2) + log 2 / log 2
     let R := log 3 / log 2 * (1 + log 2 / log 2)
     LeanLab.PNTSieve.Bonferroni.rho s.nu (Q, 4, 5) ≤
       max (M ^ 5 / (5 : ℕ).factorial) (M ^ 6 / (6 : ℕ).factorial) * R) := by
  obtain ⟨s, hP, _, _, hden, _⟩ := single_prime_density_instance
  exact ⟨s, hP, linearDensity_interval_block_rho s (log 2)
    (log_pos (by norm_num)).le hden 2 3 (by norm_num) (by norm_num) 4⟩

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ ∀ upper : Bool,
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect 2 upper n) ≤
      2 ^ s.prodPrimes.primeFactors.card * (log (3 + 1) / log 2 * (1 + log 2 / log 2)) := by
  obtain ⟨s, hP, _, _, hden, _⟩ := single_prime_density_instance
  refine ⟨s, hP, fun upper => rosser_defect_moment_le_coarse s (log 2) 2 3
    (log_pos (by norm_num)).le (by norm_num) ?_ hden upper⟩
  intro p hp
  have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
  subst p; norm_num

example : ∃ C : ℝ, 0 < C ∧ ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ ∀ upper : Bool,
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect (3 ^ 10) upper n) ≤
      C * exp (-(log (3 ^ 10) / log 3)) := by
  obtain ⟨C, hC, hbound⟩ := rosser_defect_moment_exp_bounded (log 2) 3
    (log_pos (by norm_num)).le (by norm_num)
  obtain ⟨s, hP, _, _, hden, _⟩ := single_prime_density_instance
  refine ⟨C, hC, s, hP, fun upper => hbound s 3 (3 ^ 10) (by norm_num) le_rfl le_rfl ?_ hden upper⟩
  intro p hp
  have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
  subst p; norm_num

example : let z := max 3 (exp (log 2 + 2))
    ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ 0 < log 2 ∧ LinearDensity s (log 2) ∧
      2 ≤ z ∧ max 2 (exp (log 2 + 2)) ≤ z ∧
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) ∧ ∀ upper : Bool,
        (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect (z ^ 10) upper n) = 0 := by
  let z : ℝ := max 3 (exp (log 2 + 2))
  change ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ 0 < log 2 ∧ LinearDensity s (log 2) ∧
    2 ≤ z ∧ max 2 (exp (log 2 + 2)) ≤ z ∧
    (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) ∧ ∀ upper : Bool,
      (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect (z ^ 10) upper n) = 0
  obtain ⟨s, hP, _, hnu, hden, _⟩ := single_prime_density_instance
  have hz3 : (3 : ℝ) ≤ z := le_max_left _ _
  have hz2 : (2 : ℝ) ≤ z := le_trans (by norm_num) hz3
  have hprime : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z := by
    intro p hp
    have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
    subst p
    norm_num only [Nat.cast_ofNat]
    linarith
  refine ⟨s, hP, log_pos (by norm_num), hden, hz2,
    max_le hz2 (le_max_right _ _), hprime, ?_⟩
  intro upper
  have he := rosser_mainSum_error_eq s (z ^ 10) upper
  rw [rosser_mainSum_exact_of_card_le_seven s (z ^ 10) z hz2 le_rfl hprime
    (by simp [hP, Nat.prime_two.primeFactors]) upper, sub_self, abs_zero] at he
  have hV : (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) = 1 / 2 := by
    norm_num [hP, hnu, Nat.prime_two.primeFactors]
  rw [hV] at he
  linarith

example : (exp (log 27 / 3)) ^ 3 = (27 : ℝ) :=
  rosser_first_threshold_cube 27 (by norm_num)

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    rosserFirstBoundary s (exp (log 27 / 3)) = 0 := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  refine ⟨s, hP, rosserFirstBoundary_zero_of_cube_le s 3 27 (by norm_num) (by norm_num) ?_⟩
  intro p hp
  have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
  subst p; norm_num

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    rosserFirstBoundary s (exp (log 8 / 3)) ≤
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (3 / (log 8 / log 3) * (1 + 3 * log 2 / log 8) - 1) := by
  obtain ⟨s, hP, _, _, hden, _⟩ := single_prime_density_instance
  have he : exp (log 8 / 3) = (2 : ℝ) := by
    have hl : log (8 : ℝ) / 3 = log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
      ring
    rw [hl, exp_log (by norm_num)]
  refine ⟨s, hP, rosserFirstBoundary_le_three_div s (log 2) 3 8 hden (by norm_num)
    (by norm_num) (by rw [he]) (by rw [he]; norm_num) ?_⟩
  intro p hp
  have hp2 : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
  subst p; norm_num

example : ∀ upper : Bool, rosserDefect (4 ^ 10) upper 6 = 0 := by
  intro upper
  have hf : (6 : ℕ).primeFactors = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
  apply rosserDefect_zero_of_card_le_eight (4 ^ 10) 4 (by norm_num) le_rfl upper
  · rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.squarefree_mul_iff]
    exact ⟨by decide, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  · intro p hp
    simp only [hf, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  · simp [hf]

example : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ ∀ upper : Bool,
    ((∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect (3 ^ 10) upper n) =
      ∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => 9 ≤ n.primeFactors.card),
        s.selbergTerms n * rosserDefect (3 ^ 10) upper n) ∧
    ((∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect (3 ^ 10) upper n) =
      ∑ n ∈ s.prodPrimes.divisors.filter
          (fun n : ℕ => (3 : ℝ) ^ 10 ≤ (n : ℝ) * 3 ^ 2 ∧ 9 ≤ n.primeFactors.card),
        s.selbergTerms n * rosserDefect (3 ^ 10) upper n) := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  have hp : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < 3 := by
    intro p hp
    have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
    subst p; norm_num
  exact ⟨s, hP, fun upper =>
    ⟨rosser_defect_moment_eq_many_primes s (3 ^ 10) 3 (by norm_num) le_rfl hp upper,
      rosser_defect_moment_eq_tail_many_primes s (3 ^ 10) 3 (by norm_num) le_rfl hp upper⟩⟩

example : ∃ C : ℝ, 0 < C ∧ ∃ s : BoundingSieve, s.prodPrimes = 2 ∧
    ∃ lp lm : ℕ → ℝ,
      (∀ d, |lp d| ≤ 1 ∧ |lm d| ≤ 1) ∧ lp 1 = 1 ∧ lm 1 = 1 ∧
      |s.mainSum lp - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
        C * exp (-(log (3 ^ 10) / log 3)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) ∧
      |s.mainSum lm - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
        C * exp (-(log (3 ^ 10) / log 3)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  obtain ⟨C, hC, hweight⟩ := fundamental_lemma_bounded (log 2) 3
    (log_pos (by norm_num)).le (by norm_num)
  obtain ⟨s, hP, _, _, hden, _⟩ := single_prime_density_instance
  have hp : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < 3 := by
    intro p hp
    have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
    subst p; norm_num
  obtain ⟨lp, lm, hb, hp1, hm1, _, _, _, _, he1, he2⟩ :=
    hweight s 3 (3 ^ 10) (by norm_num) le_rfl le_rfl hp hden
  exact ⟨C, hC, s, hP, lp, lm, hb, hp1, hm1, he1, he2⟩

end LeanLab.AlmostPrimeSums.Decomp1527b
