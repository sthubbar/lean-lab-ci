/-
The refined explicit Schnirelmann constant from the new S1 coefficient.
This is a lab refinement of the existing Chapter 7 formal proof, not a printed book constant.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.SchnirelmannGoldbach.Task63Constants

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannGoldbach.Task63

open LeanLab.SchnirelmannExplicit LeanLab.SchnirelmannExplicit.Sharper
open LeanLab.SchnirelmannExplicit.Sharper3 LeanLab.SchnirelmannExplicit.Sharper4
open LeanLab.SchnirelmannExplicit.Sharper5 LeanLab.SchnirelmannExplicit.Sharper6
open LeanLab.SchnirelmannExplicit.DysonBasis

/-- S3 with the rational lower density 1/14959, from N = 100003. -/
theorem density_mid_14959 : ∀ N ≥ 10 ^ 5 + 3,
    (1 / 14959 : ℝ) * N ≤ #{n ∈ Icc 1 N | n ∈ G} := by
  intro N hN
  have hαpos : (0 : ℝ) < 1 / 14959 := by norm_num
  rcases Nat.lt_or_ge N N₂ with hlt | hge
  · set s := N - 2 with hs
    have h1 : (Nat.primeCounting s : ℝ) ≤ #{n ∈ Icc 1 N | n ∈ G} := by
      exact_mod_cast card_ge_pi_G s N (by omega)
    have hpi := pi_lower_092 s (by omega)
    have hsR : (10 ^ 5 + 1 : ℝ) ≤ s := by
      have : 10 ^ 5 + 1 ≤ s := by omega
      exact_mod_cast this
    have hsn : (s : ℝ) = N - 2 := by
      rw [hs]
      push_cast [show 2 ≤ N by omega]
      ring
    have hlogs : 0 < Real.log s := Real.log_pos (by linarith)
    have hlogsN : Real.log s ≤ 12000 := log_le_of_lt_12000 s (by omega) (by omega)
    have h2 : (92 / 100 : ℝ) * s / 12000 ≤ (92 / 100 : ℝ) * s / Real.log s :=
      div_le_div_of_nonneg_left (by positivity) hlogs hlogsN
    have hα : (1 / 14959 : ℝ) * 12000 ≤ 0.91 := by norm_num
    have hNR : (10 ^ 5 + 3 : ℝ) ≤ N := by exact_mod_cast hN
    have h3 : (1 / 14959 : ℝ) * N ≤ (92 / 100 : ℝ) * s / 12000 := by
      rw [le_div_iff₀ (by norm_num), hsn]
      have := mul_le_mul_of_nonneg_right hα (by linarith : (0 : ℝ) ≤ N)
      nlinarith
    linarith
  · have h := S3_gen6 32.54 (by norm_num) N₂ N₂_ge10 S1u_3254 N hge
    have hrat : (1 / 14959 : ℝ) ≤
        (499 / 1000 : ℝ) ^ 2 * (92 / 100) ^ 4 / ((32.54 : ℝ) ^ 2 * 2.52) := by norm_num
    exact (mul_le_mul_of_nonneg_right hrat (Nat.cast_nonneg N)).trans h

/-- S4 with the same rational lower bound 1/14959. -/
theorem density_ge_14959 : (1 / 14959 : ℝ) ≤ schnirelmannDensity ({0, 1} ∪ G : Set ℕ) := by
  apply S4_floor2 (1 / 14959 : ℝ) (by norm_num) (10 ^ 5 + 3) 12 density_mid_14959
  · intro n hn h1
    have hpos : (0 : ℝ) < n := by exact_mod_cast h1
    have hle : (n : ℝ) ≤ 10 ^ 5 + 3 := by exact_mod_cast hn.le
    calc Real.log n ≤ Real.log (10 ^ 5 + 3) := Real.log_le_log hpos hle
      _ ≤ 12 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have := Real.add_one_le_exp (12 : ℝ)
        have h12 : (2.7182818283 : ℝ) ^ 12 ≤ Real.exp 12 := by
          have e := Real.exp_nat_mul 1 12
          rw [mul_one] at e
          rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, e]
          exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 12
        linarith [show (10 ^ 5 + 3 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 by norm_num]
  · norm_num
  · norm_num

/-- S5 has the explicit basis order 14959. -/
theorem basis_order_14959 : (14959 : ℕ) • ({0, 1} ∪ G : Set ℕ) = Set.univ := by
  exact nsmul_eq_univ_dyson ({0, 1} ∪ G : Set ℕ) (Or.inl (Or.inl rfl)) (1 / 14959 : ℝ)
    (by convert density_ge_14959) 14959 (by norm_num)

/-- Every integer above 1 is a sum of at most 29920 primes. -/
theorem schnirelmann_bounded_primes_29920 :
    ∀ n : ℕ, 2 ≤ n → ∃ k ≤ 29920, SumOfPrimes k n := by
  have hh := basis_order_14959
  intro n hn
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · exact ⟨1, by norm_num, [2], rfl, by simp [Nat.prime_two], rfl⟩
  · exact ⟨1, by norm_num, [3], rfl, by simp [Nat.prime_three], rfl⟩
  · have hmem : n - 2 ∈ (14959 : ℕ) • ({0, 1} ∪ G : Set ℕ) := by rw [hh]; trivial
    obtain ⟨l, hl, hlA, hls⟩ := exists_list_of_mem_nsmul _ 14959 (n - 2) hmem
    obtain ⟨k, hk, hs⟩ := list_step l hlA 2 le_rfl
    rw [hls, show n - 2 + 2 = n by omega] at hs
    exact ⟨k, by omega, hs⟩

end LeanLab.SchnirelmannGoldbach.Task63

#print axioms LeanLab.SchnirelmannGoldbach.Task63.density_mid_14959

#print axioms LeanLab.SchnirelmannGoldbach.Task63.density_ge_14959

#print axioms LeanLab.SchnirelmannGoldbach.Task63.schnirelmann_bounded_primes_29920

#print axioms LeanLab.SchnirelmannGoldbach.Task63.basis_order_14959
