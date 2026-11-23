/-
P0076, Section 4, page 15, the second inequality of the display after display 4.3.
Split of leaf_euler_product_ge_log_ratio in NormalizationSplit.lean into one cited LEAF,
the bounded bias between primes 1 and 3 mod 4 in sums of 1/p, and a proved assembly that
uses the lab's explicit Mertens second theorem mertens2_block.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.NormalizationSplit

open Finset Real
open scoped Classical

namespace LeanLab.Teravainen2016

/-- LEAF: page 15, second inequality of the display after display 4.3, the class 3 mod 4 half
of the Mertens estimate behind it. Class HARD.
The sums of 1/p over primes y < p at most x in the class 1 mod 4 and in the class 3 mod 4
differ by a bounded amount, uniformly in 2 at most y at most x. This is the convergence of the
sum of chi_4 p / p over primes, which follows from L 1 chi_4 = pi / 4 being nonzero and the
Mertens theorem for arithmetic progressions; the paper uses it implicitly to get the
exponent 3/2 of the sieve dimension from omega p = 1 or 2. -/
theorem leaf_mertens_mod4_bias :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y x : ℝ, 2 ≤ y → y ≤ x →
      ∑ p ∈ ((Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime).filter (fun p => p % 4 = 1), (1 : ℝ) / p -
        ∑ p ∈ ((Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime).filter (fun p => p % 4 = 3), (1 : ℝ) / p ≤ B := by
  sorry

/-- Each local factor of the Euler product is at least the exponential of omega p / p,
since 1 - x is at most exp of -x. -/
theorem exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ (1 - x)⁻¹ := by
  have h1 : 0 < 1 - x := by linarith
  have h2 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  rw [le_inv_comm₀ (Real.exp_pos x) h1, ← Real.exp_neg]
  exact h2

/-- The statement of leaf_euler_product_ge_log_ratio, CONDITIONAL ON leaf_mertens_mod4_bias.
Page 15: the product is at least exp of the sum of omega p / p, which is the sum of 1/p plus the
sum over p = 3 mod 4 of 1/p, then mertens2_block and the bias leaf. -/
theorem leaf_euler_product_ge_log_ratio_of_leaves :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) ≤
        C * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
  obtain ⟨B, hB0, HB⟩ := leaf_mertens_mod4_bias
  refine ⟨Real.exp (6 + B / 2), Real.exp_pos _, ?_⟩
  intro w hw z hz1
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw10 : (10 : ℝ) ≤ w := hwBig1.trans hw
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogw1 : 1 ≤ Real.log w := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set F := (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z) with hF
  -- facts about primes in F
  have hFp : ∀ p ∈ F, p.Prime ∧ w < p ∧ (10 : ℝ) < p := by
    intro p hp
    have h := (mem_filter.mp hp).2
    exact ⟨h.1, h.2.1, lt_of_le_of_lt hw10 (by exact_mod_cast h.2.1)⟩
  have hx : ∀ p ∈ F, (envelopingOmega w p : ℝ) / p < 1 := by
    intro p hp
    obtain ⟨-, -, h10⟩ := hFp p hp
    have hω : (envelopingOmega w p : ℝ) ≤ 2 := by
      unfold envelopingOmega; split_ifs <;> norm_num
    rw [div_lt_one (by linarith)]; linarith
  have hfac1 : ∀ p ∈ F, 1 ≤ (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
    intro p hp
    have h0 : 0 ≤ (envelopingOmega w p : ℝ) / p := by positivity
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp ((envelopingOmega w p : ℝ) / p) := Real.exp_le_exp.mpr h0
      _ ≤ _ := exp_le_inv_one_sub (hx p hp)
  have hP1 : 1 ≤ ∏ p ∈ F, (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := one_le_prod₀ hfac1
  have hexpP : Real.exp (∑ p ∈ F, (envelopingOmega w p : ℝ) / p) ≤
      ∏ p ∈ F, (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
    rw [Real.exp_sum]
    exact prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) (fun p hp => exp_le_inv_one_sub (hx p hp))
  by_cases hzw : z < w
  · -- below w the ratio is below one and the product is at least one
    have hlz : 0 ≤ Real.log z := Real.log_nonneg hz1
    have hratio : Real.log z / Real.log w ≤ 1 := by
      rw [div_le_one hlogw]
      exact Real.log_le_log (by linarith) hzw.le
    have hr : (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one (div_nonneg hlz hlogw.le) hratio (by norm_num)
    have hC1 : 1 ≤ Real.exp (6 + B / 2) := Real.one_le_exp (by positivity)
    calc _ ≤ 1 := hr
      _ ≤ Real.exp (6 + B / 2) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hP1 (Real.exp_pos _).le
  · push_neg at hzw
    have hz10 : (10 : ℝ) ≤ z := hw10.trans hzw
    have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
    -- F is the block of primes in mertens2_block
    have hFeq : F = (Ioc ⌊(w : ℝ)⌋₊ ⌊z⌋₊).filter Nat.Prime := by
      rw [Nat.floor_natCast]
      ext p
      simp only [hF, mem_filter, mem_range, mem_Ioc]
      constructor
      · rintro ⟨-, hp, hwp, hpz⟩
        exact ⟨⟨hwp, Nat.le_floor hpz⟩, hp⟩
      · rintro ⟨⟨hwp, hpz⟩, hp⟩
        refine ⟨by omega, hp, hwp, ?_⟩
        exact (Nat.le_floor_iff (by linarith)).mp hpz
    have hM := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block (y := (w : ℝ)) (x := z) (le_trans (by norm_num) hw10) hzw
    rw [← hFeq] at hM
    have hS1 : Real.log (Real.log z) - Real.log (Real.log w) - 4 / Real.log w ≤
        ∑ p ∈ F, (1 : ℝ) / p := by
      have := (abs_le.mp hM).1; linarith
    have hbias := HB w z (le_trans (by norm_num) hw10) hzw
    rw [← hFeq] at hbias
    -- split the sum of 1/p by residue mod 4
    have hodd : ∀ p ∈ F, p % 4 = 1 ∨ p % 4 = 3 := by
      intro p hp
      obtain ⟨hpp, -, h10⟩ := hFp p hp
      have hne : p ≠ 2 := by
        intro h; rw [h] at h10; norm_num at h10
      have := hpp.eq_one_or_self_of_dvd 2
      rcases Nat.even_or_odd p with he | ho
      · exact absurd (this (even_iff_two_dvd.mp he)) (by omega)
      · have := Nat.odd_iff.mp ho; omega
    have hsplit : ∑ p ∈ F, (1 : ℝ) / p =
        ∑ p ∈ F.filter (fun p => p % 4 = 1), (1 : ℝ) / p +
          ∑ p ∈ F.filter (fun p => p % 4 = 3), (1 : ℝ) / p := by
      rw [← sum_filter_add_sum_filter_not F (fun p => p % 4 = 1)]
      congr 1
      apply sum_congr _ (fun _ _ => rfl)
      ext p
      simp only [mem_filter]
      constructor
      · rintro ⟨hp, h⟩; exact ⟨hp, by rcases hodd p hp with h' | h' <;> omega⟩
      · rintro ⟨hp, h⟩; exact ⟨hp, by omega⟩
    have hω : ∑ p ∈ F, (envelopingOmega w p : ℝ) / p =
        ∑ p ∈ F, (1 : ℝ) / p + ∑ p ∈ F.filter (fun p => p % 4 = 3), (1 : ℝ) / p := by
      rw [Finset.sum_filter (s := F) (fun p => p % 4 = 3), ← sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      obtain ⟨-, hwp, -⟩ := hFp p hp
      unfold envelopingOmega
      rw [if_neg (by omega)]
      rcases hodd p hp with h | h
      · rw [if_pos h, if_neg (by omega)]; push_cast; ring
      · rw [if_neg (by omega), if_pos h]; push_cast; ring
    have hsum : (3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w)) - (6 + B / 2) ≤
        ∑ p ∈ F, (envelopingOmega w p : ℝ) / p := by
      have h4 : 4 / Real.log w ≤ 4 := by
        rw [div_le_iff₀ hlogw]; linarith
      rw [hω]; linarith
    have hratio : (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) =
        Real.exp ((3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w))) := by
      rw [Real.rpow_def_of_pos (div_pos hlogz hlogw), Real.log_div hlogz.ne' hlogw.ne']
      ring_nf
    rw [hratio]
    calc Real.exp ((3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w)))
        = Real.exp (6 + B / 2) *
            Real.exp ((3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w)) - (6 + B / 2)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (6 + B / 2) * Real.exp (∑ p ∈ F, (envelopingOmega w p : ℝ) / p) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hexpP (Real.exp_pos _).le

end LeanLab.Teravainen2016
