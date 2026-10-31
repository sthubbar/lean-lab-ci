import LeanLab.PNTPort.Vinogradov.TernaryLower
import LeanLab.Ternary.Statements

/-!
# Vinogradov's three primes theorem by the circle method

Lab proof, unit U-5261. AI wrote this file. Known mathematics, no cited input.

`vinogradov_circle : ∃ C, Ternary.TernaryAbove C`: every large odd `n` is a sum of three primes,
from `r3_lower` after removing the triples with a prime power that is not a prime, which weigh
at most `3 (ψ(n) - θ(n)) · 6 n log n ≤ 36 n^{3/2} log² n`. This is Vinogradov's own route,
the circle method, independent of the lab's earlier proof through Heath-Brown's Theorem 1; both
rest on the lab's Siegel-Walfisz theorem and are ineffective. Ternary Goldbach for all odd
`n > 5` is Helfgott's theorem; binary Goldbach is OPEN.
-/

namespace LeanLab.PNTPort.Vinogradov

open Finset Real

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- The pair sum with one entry fixed, uniformly bounded. -/
lemma pair_le (N n x : ℕ) :
    ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N, (if x + y + z = n then Λ y * Λ z else 0) ≤
      6 * N * Real.log N := by
  have hlN := Real.log_natCast_nonneg N
  have hψ := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by positivity)
  rw [Chebyshev.psi, Nat.floor_natCast] at hψ
  have hI : Ioc 0 N = Icc 1 N := by ext m; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI] at hψ
  have h4 : Real.log 4 + 4 ≤ 6 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hy : ∀ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N, (if x + y + z = n then Λ y * Λ z else 0) ≤
      Λ y * Real.log N := by
    intro y _
    rw [← sum_filter]
    have hsub : (Icc 1 N).filter (fun z => x + y + z = n) ⊆ {n - x - y} := by
      intro z hz; rw [mem_filter] at hz; rw [mem_singleton]; omega
    calc ∑ z ∈ (Icc 1 N).filter (fun z => x + y + z = n), Λ y * Λ z
        ≤ ∑ z ∈ (Icc 1 N).filter (fun z => x + y + z = n), Λ y * Real.log N := by
          refine sum_le_sum fun z hz => ?_
          rw [mem_filter, mem_Icc] at hz
          apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
          exact ArithmeticFunction.vonMangoldt_le_log.trans
            (Real.log_le_log (by exact_mod_cast hz.1.1) (by exact_mod_cast hz.1.2))
      _ = ((Icc 1 N).filter (fun z => x + y + z = n)).card * (Λ y * Real.log N) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 1 * (Λ y * Real.log N) := by
          apply mul_le_mul_of_nonneg_right _
            (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hlN)
          exact_mod_cast (card_le_card hsub).trans (card_singleton _).le
      _ = Λ y * Real.log N := one_mul _
  calc _ ≤ ∑ y ∈ Icc 1 N, Λ y * Real.log N := sum_le_sum hy
    _ = (∑ y ∈ Icc 1 N, Λ y) * Real.log N := by rw [sum_mul]
    _ ≤ ((Real.log 4 + 4) * N) * Real.log N := mul_le_mul_of_nonneg_right hψ hlN
    _ ≤ (6 * N) * Real.log N := by gcongr
    _ = 6 * N * Real.log N := by ring

lemma bad_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ (Icc 1 N).filter (fun a => ¬ a.Prime), Λ a ≤ 2 * Real.sqrt N * Real.log N := by
  have h := Chebyshev.psi_sub_theta_le (x := (N : ℝ)) (by exact_mod_cast hN)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast] at h
  have hI : Ioc 0 N = Icc 1 N := by ext m; simp only [mem_Ioc, mem_Icc]; omega
  rwa [hI] at h

/-- Triples whose first entry is not a prime. -/
lemma tri_bound (N n : ℕ) (hN : 1 ≤ N) :
    ∑ x ∈ Icc 1 N, (if ¬ x.Prime then Λ x *
      ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N, (if x + y + z = n then Λ y * Λ z else 0) else 0) ≤
      2 * Real.sqrt N * Real.log N * (6 * N * Real.log N) := by
  rw [← sum_filter]
  calc ∑ x ∈ (Icc 1 N).filter (fun x => ¬ x.Prime), Λ x *
        ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N, (if x + y + z = n then Λ y * Λ z else 0)
      ≤ ∑ x ∈ (Icc 1 N).filter (fun x => ¬ x.Prime), Λ x * (6 * N * Real.log N) :=
        sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (pair_le N n x) ArithmeticFunction.vonMangoldt_nonneg
    _ = (∑ x ∈ (Icc 1 N).filter (fun x => ¬ x.Prime), Λ x) * (6 * N * Real.log N) := by
        rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (bad_le N hN) (by
        have := Real.log_natCast_nonneg N; positivity)

/-- Pulling the first variable out of a triple sum. -/
lemma pull (N n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N,
      (if P x then (if x + y + z = n then Λ x * Λ y * Λ z else 0) else 0) =
    ∑ x ∈ Icc 1 N, (if P x then Λ x *
      ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N, (if x + y + z = n then Λ y * Λ z else 0) else 0) := by
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : P x
  · simp only [if_pos hx, mul_sum]
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    split_ifs <;> ring
  · simp [hx]

/-- If no prime triple sums to `n`, then `r₃(n)` is carried by prime powers. -/
lemma r3_le_bad (N n : ℕ) (hN : 1 ≤ N) (hno : ¬ LeanLab.IsTernarySum n) :
    r3 N n ≤ 3 * (2 * Real.sqrt N * Real.log N * (6 * N * Real.log N)) := by
  set B := 2 * Real.sqrt N * Real.log N * (6 * N * Real.log N) with hB
  set T : ℕ → ℕ → ℕ → ℝ := fun a b c => if a + b + c = n then Λ a * Λ b * Λ c else 0 with hT
  have hT0 : ∀ a b c, 0 ≤ T a b c := fun a b c => by
    simp only [hT]; split_ifs
    · exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        ArithmeticFunction.vonMangoldt_nonneg) ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl
  have hpt : ∀ a b c : ℕ, T a b c ≤ (if ¬ a.Prime then T a b c else 0) +
      (if ¬ b.Prime then T a b c else 0) + (if ¬ c.Prime then T a b c else 0) := by
    intro a b c
    have h0 := hT0 a b c
    by_cases h : a + b + c = n
    · have hnp : ¬ a.Prime ∨ ¬ b.Prime ∨ ¬ c.Prime := by
        by_contra hc; push_neg at hc; exact hno ⟨a, b, c, hc.1, hc.2.1, hc.2.2, h⟩
      have u1 : 0 ≤ (if ¬ a.Prime then T a b c else 0) := by split_ifs <;> linarith
      have u2 : 0 ≤ (if ¬ b.Prime then T a b c else 0) := by split_ifs <;> linarith
      have u3 : 0 ≤ (if ¬ c.Prime then T a b c else 0) := by split_ifs <;> linarith
      rcases hnp with h1 | h1 | h1
      · rw [if_pos h1] at u1 ⊢; linarith
      · rw [if_pos h1] at u2 ⊢; linarith
      · rw [if_pos h1] at u3 ⊢; linarith
    · have : T a b c = 0 := by simp only [hT]; rw [if_neg h]
      rw [this]; simp
  have hsum : r3 N n ≤ ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
      ((if ¬ a.Prime then T a b c else 0) + (if ¬ b.Prime then T a b c else 0) +
        (if ¬ c.Prime then T a b c else 0)) := by
    unfold r3
    exact sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun c _ => hpt a b c
  simp only [sum_add_distrib] at hsum
  -- first variable
  have s1 : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N, (if ¬ a.Prime then T a b c else 0) ≤ B := by
    simp only [hT]; rw [pull]; exact tri_bound N n hN
  -- second variable
  have s2 : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N, (if ¬ b.Prime then T a b c else 0) ≤ B := by
    rw [sum_comm]
    have : ∑ b ∈ Icc 1 N, ∑ a ∈ Icc 1 N, ∑ c ∈ Icc 1 N, (if ¬ b.Prime then T a b c else 0) =
        ∑ b ∈ Icc 1 N, ∑ a ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
          (if ¬ b.Prime then (if b + a + c = n then Λ b * Λ a * Λ c else 0) else 0) := by
      refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => sum_congr rfl fun c _ => ?_
      simp only [hT]; rw [show a + b + c = b + a + c by ring]; split_ifs <;> ring
    rw [this, pull]; exact tri_bound N n hN
  -- third variable
  have s3 : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N, (if ¬ c.Prime then T a b c else 0) ≤ B := by
    have rev : ∀ F : ℕ → ℕ → ℕ → ℝ, ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N, F a b c =
        ∑ c ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ a ∈ Icc 1 N, F a b c := by
      intro F
      calc ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N, F a b c
          = ∑ b ∈ Icc 1 N, ∑ a ∈ Icc 1 N, ∑ c ∈ Icc 1 N, F a b c := sum_comm
        _ = ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N, ∑ a ∈ Icc 1 N, F a b c :=
            sum_congr rfl fun b _ => sum_comm
        _ = ∑ c ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ a ∈ Icc 1 N, F a b c := sum_comm
    rw [rev (fun a b c => if ¬ c.Prime then T a b c else 0)]
    have : ∑ c ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ a ∈ Icc 1 N, (if ¬ c.Prime then T a b c else 0) =
        ∑ c ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ a ∈ Icc 1 N,
          (if ¬ c.Prime then (if c + b + a = n then Λ c * Λ b * Λ a else 0) else 0) := by
      refine sum_congr rfl fun c _ => sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
      simp only [hT]; rw [show a + b + c = c + b + a by ring]; split_ifs <;> ring
    rw [this, pull]; exact tri_bound N n hN
  linarith

/-- **Vinogradov's three primes theorem by the circle method**, unconditional, ineffective. -/
theorem vinogradov_circle : ∃ C : ℝ, LeanLab.Ternary.TernaryAbove C := by
  obtain ⟨N₀, h⟩ := r3_lower
  obtain ⟨K, hK, hlog⟩ := BV.log_rpow_le_rpow 2 (1 / 4) (by norm_num)
  refine ⟨max N₀ (max 2 ((1440 * K + 1) ^ 4)), ?_⟩
  intro n hodd hn
  by_contra hno
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : (2 : ℝ) ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnK : (1440 * K + 1) ^ 4 ≤ (n : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hlow := h n hn0 hodd
  have hup := r3_le_bad n n hn1 hno
  have hl := hlog n hn2
  have hlN := Real.log_natCast_nonneg n
  have hnr : (0 : ℝ) < n := by linarith
  -- n^{1/4} > 1440 K
  set t := (n : ℝ) ^ ((1 : ℝ) / 4) with ht
  have ht4 : t ^ 4 = n := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hnr.le]; norm_num
  have ht0 : 0 < t := Real.rpow_pos_of_pos hnr _
  have htK : 1440 * K + 1 ≤ t := by
    by_contra hlt; push_neg at hlt
    have : t ^ 4 < (1440 * K + 1) ^ 4 := pow_lt_pow_left₀ hlt ht0.le (by norm_num)
    linarith
  have hsq : Real.sqrt n = t ^ 2 := by
    rw [← ht4, show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hl2 : Real.log n * Real.log n ≤ K * t := by
    have : Real.log n ^ (2 : ℝ) = Real.log n * Real.log n := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [← this]; exact hl
  -- 36 n^{3/2} log² n ≤ 36 K t^7 < t^8 / 40 = n²/40
  have hupper : 3 * (2 * Real.sqrt n * Real.log n * (6 * n * Real.log n)) ≤ 36 * K * t ^ 7 := by
    have e6 : Real.sqrt n * n = t ^ 6 := by rw [hsq, ← ht4]; ring
    have : 3 * (2 * Real.sqrt n * Real.log n * (6 * n * Real.log n)) =
        36 * (Real.sqrt n * n) * (Real.log n * Real.log n) := by ring
    rw [this, e6]
    have : 36 * t ^ 6 * (Real.log n * Real.log n) ≤ 36 * t ^ 6 * (K * t) :=
      mul_le_mul_of_nonneg_left hl2 (by positivity)
    linarith
  have hlast : 36 * K * t ^ 7 < (n : ℝ) ^ 2 / 40 := by
    rw [← ht4]
    have : (t ^ 4) ^ 2 / 40 = t ^ 7 * (t / 40) := by ring
    rw [this]
    have h7 : 0 < t ^ 7 := by positivity
    have : 36 * K < t / 40 := by linarith
    nlinarith
  linarith

end LeanLab.PNTPort.Vinogradov
