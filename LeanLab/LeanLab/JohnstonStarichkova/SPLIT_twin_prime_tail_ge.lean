/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3, page 3, the twin prime constant
C_2 = prod_{p>2} (1 - 1/(p-1)^2), tail over primes p > 50.
SPLIT of the LEAF twin_prime_tail_ge from SPLIT_twin_prime_const_gt.lean into two numerical
LEAF lemmas and a fully proved glue:
  (1) finite part over primes 50 < p ≤ N, N = 10^5, at least c1 = 996047/1000000;
  (2) prime tail: every finite sum of 1/(p-1)^2 over primes p > N is at most c2 = 1/400000;
  (3) glue, proved: Weierstrass product inequality prod (1 - a_i) ≥ 1 - sum a_i, factors in
      [0, 1] so partial products only shrink when primes are added, every finite partial
      product is at least c1 * (1 - c2), hence so is the tprod; if the product were not
      multipliable the tprod is 1 by convention, which also exceeds the bound.
AI wrote this Lean code.

Numerics, Python with 40 digit Decimal arithmetic and a sieve to 10^7:
  finite product over primes 50 < p ≤ 10^5 of (1 - 1/(p-1)^2) = 0.99604706500050810...
    so c1 = 0.996047 has margin 6.5e-8;
  sum over primes 10^5 < p ≤ 10^7 of 1/(p-1)^2 plus the estimate 1/(10^7 ln 10^7) for the
    rest = 8.026e-7, so c2 = 2.5e-6 has room by a factor above 3. An explicit bound from
    Rosser and Schoenfeld 1962, pi(x) < 1.25506 x / ln x, gives about 1.09e-6 by partial
    summation, and p_n > n ln n gives about 1.24e-6, both below c2;
  c1 * (1 - c2) = 0.99604450988 ≥ 0.996044, margin 5.1e-7;
  true tail product 0.99604627, so the target 0.996044 has margin 2.3e-6.
-/
import Mathlib

namespace LeanLab.JohnstonStarichkova

/-- LEAF: P0019 v3 page 3, tail of C_2, finite part: the product over primes 50 < p ≤ 10^5
of (1 - 1/(p-1)^2) is at least 0.996047, its value being 0.9960470650005; a certified finite
computation over the 9577 primes in that range, exact rational or interval arithmetic.
Class MEDIUM. -/
theorem twin_prime_tail_finite_ge :
    (996047 / 1000000 : ℝ) ≤ ∏ p ∈ (Finset.Ioc 50 100000).filter Nat.Prime,
      (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  sorry

/-- LEAF: P0019 v3 page 3, tail of C_2, prime tail: every finite sum of 1/(p-1)^2 over
primes p > 10^5 is at most 1/400000; its full value is about 8.03e-7, and the bound follows by
partial summation from the explicit Chebyshev bound pi(x) < 1.25506 x / ln x of Rosser and
Schoenfeld 1962, Illinois J. Math. 6, Corollary 1, or from p_n > n ln n, Theorem 3 there.
Class HARD. -/
theorem twin_prime_tail_sum_le (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime ∧ 100000 < p) :
    ∑ p ∈ t, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 400000 := by
  sorry

/-- Weierstrass product inequality: for a_i in [0, 1], prod (1 - a_i) ≥ 1 - sum a_i. -/
theorem one_sub_sum_le_prod_one_sub_split {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ t, 0 ≤ a i) (h1 : ∀ i ∈ t, a i ≤ 1) :
    1 - ∑ i ∈ t, a i ≤ ∏ i ∈ t, (1 - a i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hS : 0 ≤ ∑ i ∈ t, a i :=
      Finset.sum_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have ha0 := h0 j (Finset.mem_insert_self j t)
    have ha1 := h1 j (Finset.mem_insert_self j t)
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr ha1)]

theorem twin_factor_bounds_split (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ 1 / ((n : ℝ) - 1) ^ 2 ∧ 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 := by
  have h : (2 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  nlinarith

/-- Every finite product over primes p > 50 is at least c1 * (1 - c2). -/
theorem twin_prime_tail_finset_ge_split (u : Finset ℕ) (hu : ∀ n ∈ u, n.Prime ∧ 50 < n) :
    (996047 / 1000000 : ℝ) * (1 - 1 / 400000) ≤ ∏ n ∈ u, (1 - 1 / ((n : ℝ) - 1) ^ 2) := by
  classical
  set F := (Finset.Ioc 50 100000).filter Nat.Prime with hF
  set h : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) - 1) ^ 2 with hh
  have hfac : ∀ n, 3 ≤ n → 0 ≤ h n ∧ h n ≤ 1 := by
    intro n hn
    obtain ⟨a, b⟩ := twin_factor_bounds_split n hn
    exact ⟨by simp only [hh]; linarith, by simp only [hh]; linarith⟩
  have hUF : ∀ n ∈ u ∪ F, 3 ≤ n := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · have := (hu n hn).2; omega
    · have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1; omega
  -- step 1: adding the primes of F only lowers the product
  have h1 : ∏ n ∈ u ∪ F, h n ≤ ∏ n ∈ u, h n := by
    rw [← Finset.prod_sdiff (Finset.subset_union_left (s₂ := F))]
    have hle : ∏ n ∈ (u ∪ F) \ u, h n ≤ 1 :=
      Finset.prod_le_one₀ (fun n hn => (hfac n (hUF n (Finset.mem_sdiff.mp hn).1)).1)
        (fun n hn => (hfac n (hUF n (Finset.mem_sdiff.mp hn).1)).2)
    have hpos : 0 ≤ ∏ n ∈ u, h n :=
      Finset.prod_nonneg (fun n hn => (hfac n (hUF n (Finset.mem_union_left _ hn))).1)
    nlinarith
  -- step 2: split off F
  have h2 : ∏ n ∈ u ∪ F, h n = (∏ n ∈ (u ∪ F) \ F, h n) * ∏ n ∈ F, h n :=
    (Finset.prod_sdiff (Finset.subset_union_right (s₁ := u))).symm
  -- step 3: the rest consists of primes above 10^5
  have hrest : ∀ n ∈ (u ∪ F) \ F, n.Prime ∧ 100000 < n := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_sdiff.mp hn
    rcases Finset.mem_union.mp hn1 with hn1 | hn1
    · obtain ⟨hp, h50⟩ := hu n hn1
      refine ⟨hp, ?_⟩
      by_contra hc
      exact hn2 (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h50, by omega⟩, hp⟩)
    · exact absurd hn1 hn2
  have hW := one_sub_sum_le_prod_one_sub_split ((u ∪ F) \ F) (fun n => 1 / ((n : ℝ) - 1) ^ 2)
    (fun n hn => (twin_factor_bounds_split n
      (hUF n (Finset.mem_sdiff.mp hn).1)).1)
    (fun n hn => (twin_factor_bounds_split n
      (hUF n (Finset.mem_sdiff.mp hn).1)).2)
  have hT := twin_prime_tail_sum_le ((u ∪ F) \ F) hrest
  have hfin := twin_prime_tail_finite_ge
  have hR : (1 - 1 / 400000 : ℝ) ≤ ∏ n ∈ (u ∪ F) \ F, h n := by
    simp only [hh]; linarith
  have hFpos : (0 : ℝ) ≤ ∏ n ∈ F, h n := le_trans (by norm_num) hfin
  calc (996047 / 1000000 : ℝ) * (1 - 1 / 400000)
      = (1 - 1 / 400000) * (996047 / 1000000) := by ring
    _ ≤ (∏ n ∈ (u ∪ F) \ F, h n) * ∏ n ∈ F, h n :=
        mul_le_mul hR hfin (by norm_num) (le_trans (by norm_num) hR)
    _ = ∏ n ∈ u ∪ F, h n := h2.symm
    _ ≤ ∏ n ∈ u, h n := h1

theorem twin_prime_tail_ge_split :
    (0.996044 : ℝ) ≤ ∏' x : ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
        Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
        Set {p : ℕ // p.Prime ∧ 2 < p}),
      (1 - 1 / ((((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) : ℝ) - 1) ^ 2) := by
  set f := fun x : ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
        Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
        Set {p : ℕ // p.Prime ∧ 2 < p}) =>
      (1 - 1 / ((((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) : ℝ) - 1) ^ 2) with hf
  by_cases hm : Multipliable f
  · have hlow : ∀ s, (996047 / 1000000 : ℝ) * (1 - 1 / 400000) ≤ ∏ x ∈ s, f x := by
      intro s
      let e : ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
          Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
          Set {p : ℕ // p.Prime ∧ 2 < p}) ↪ ℕ :=
        ⟨fun x => x.1.1, fun a b hab => Subtype.ext (Subtype.ext hab)⟩
      have hmap : ∏ x ∈ s, f x = ∏ n ∈ s.map e, (1 - 1 / ((n : ℝ) - 1) ^ 2) := by
        rw [Finset.prod_map]; rfl
      rw [hmap]
      apply twin_prime_tail_finset_ge_split
      intro n hn
      obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hn
      have hx := x.2
      simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_subtype,
        Finset.mem_range] at hx
      exact ⟨x.1.2.1, by show 50 < x.1.1; omega⟩
    have := ge_of_tendsto' hm.hasProd hlow
    linarith [show (0.996044 : ℝ) ≤ 996047 / 1000000 * (1 - 1 / 400000) by norm_num]
  · rw [tprod_eq_one_of_not_multipliable hm]
    norm_num

end LeanLab.JohnstonStarichkova
