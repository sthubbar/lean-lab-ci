/-
Split of the LEAF `premise_of_range` of SPLIT_lifted_bound_of_allLevels into one leaf, the explicit
Mertens bound on all primes of a range, with an assembly that has the leaf's statement verbatim
and uses no sorry.

The assembly does the reductions of step 7 of the hand proof of `fixedKappa_of_allLevels`: levels u
below y₀ are raised to y₀, a level w ≤ y₀ gives the empty product, each factor (1 - g' n p)⁻¹ is
at most (1 - (1 + η)/p)⁻¹, and the primes of P' outside Q' in [u, w) are a subset of all primes in
[max u y₀, w). What is left is Mertens on all primes of a range, the leaf `mertens_range_product`.

This file adds no definition, changes no existing file, and leaves the sealed statements untouched.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SPLIT_lifted_bound_of_allLevels

namespace LeanLab.BS2022GRH.SieveAllLevels1611
open Real Finset Classical

/-- LEAF: step 7 of the hand proof of `fixedKappa_of_allLevels`, the analytic core: for all primes p
of a range [u, w) with u ≥ Y and log w ≤ K log u, ∏ (1 - (1 + η)/p)⁻¹ ≤ (1 + ε) log w / log u once
η is small and Y large. By Mertens' second theorem with explicit error, Rosser and Schoenfeld 1962
Theorem 5, ∑_{u ≤ p < w} 1/p ≤ log (log w / log u) + O(1/log² u), the product is at most
(log w / log u)^{1+η} (1 + O(1/u) + O(1/log² u)) ≤ K^η (1 + o(1)) log w / log u.
HARD: explicit Mertens is not in Mathlib. Strictly easier than the parent: no sieve system, no
density function, no excluded set. Non-vacuity: for K ≤ 1 the range condition forces w ≤ u, and
for K > 1 it is the classical Mertens statement. -/
theorem mertens_range_product {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ Y : ℝ, 2 ≤ Y ∧ ∀ u w : ℝ, Y ≤ u → u < w → log w ≤ K * log u →
      ∏ p ∈ (range ⌈w⌉₊).filter (fun p : ℕ => p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < w),
        (1 - (1 + η) / (p : ℝ))⁻¹ ≤ (1 + ε) * (log w / log u) := by
  sorry

/-- **Assembly**, CONDITIONAL ON `mertens_range_product`: the statement of `premise_of_range`
verbatim. -/
theorem premise_of_range_split {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∃ Y : ℝ, ∀ (P' : Set ℕ) (Q' : Finset ℕ) (g' : ℕ → ℕ → ℝ) (z' y₀ : ℝ),
      (∀ p ∈ P', p.Prime) → (∀ n, ∀ p ∈ P', 0 ≤ g' n p ∧ g' n p < 1) →
      Y ≤ y₀ → log z' ≤ K * log y₀ →
      (∀ p ∈ P', p ∉ Q' → y₀ ≤ (p : ℝ)) →
      (∀ n, ∀ p ∈ P', p ∉ Q' → g' n p ≤ (1 + η) / (p : ℝ)) →
      AllLevelsPremise P' Q' g' ε z' := by
  obtain ⟨η, hη0, hη1, Y, hY2, hM⟩ := mertens_range_product hε K
  refine ⟨η, hη0, Y, ?_⟩
  intro P' Q' g' z' y₀ hP hg hY hK hlarge hgη n u w hu huw hwz
  have hy₀2 : (2 : ℝ) ≤ y₀ := le_trans hY2 hY
  have hlogu : 0 < log u := log_pos hu
  have hlogw : log u < log w := log_lt_log (by linarith) huw
  have hratio : 1 < log w / log u := (one_lt_div hlogu).2 hlogw
  set u₁ := max u y₀ with hu₁
  have hFsub : ∀ p ∈ (range ⌈w⌉₊).filter (fun p => p ∈ P' ∧ p ∉ Q' ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < w),
      p.Prime ∧ u₁ ≤ (p : ℝ) ∧ (p : ℝ) < w ∧ p ∈ P' ∧ p ∉ Q' := by
    intro p hp
    simp only [mem_filter] at hp
    obtain ⟨_, hpP, hpQ, hup, hpw⟩ := hp
    exact ⟨hP p hpP, max_le hup (hlarge p hpP hpQ), hpw, hpP, hpQ⟩
  -- each factor
  have hfac : ∀ p ∈ (range ⌈w⌉₊).filter (fun p => p ∈ P' ∧ p ∉ Q' ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < w),
      0 ≤ (1 - g' n p)⁻¹ ∧ (1 - g' n p)⁻¹ ≤ (1 - (1 + η) / (p : ℝ))⁻¹ := by
    intro p hp
    obtain ⟨_, hpu, _, hpP, hpQ⟩ := hFsub p hp
    have hp2 : (2 : ℝ) ≤ p := le_trans hy₀2 (le_trans (le_max_right u y₀) hpu)
    have hlt : (1 + η) / (p : ℝ) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    have hg1 := hg n p hpP
    have hgle := hgη n p hpP hpQ
    refine ⟨inv_nonneg.2 (by linarith [hg1.2]), ?_⟩
    exact inv_anti₀ (by linarith) (by linarith)
  by_cases hcase : w ≤ u₁
  · have hempty : (range ⌈w⌉₊).filter (fun p => p ∈ P' ∧ p ∉ Q' ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < w)
        = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      obtain ⟨_, hpu, hpw, _⟩ := hFsub p hp
      linarith
    rw [hempty, prod_empty]
    nlinarith
  · replace hcase := not_le.1 hcase
    have hYu₁ : Y ≤ u₁ := le_trans hY (le_max_right u y₀)
    have hlogy₀ : 0 < log y₀ := log_pos (by linarith)
    have hlogwz : log w ≤ log z' := log_le_log (by linarith) hwz
    have hKpos : 0 < K := by
      by_contra hn
      replace hn := not_lt.1 hn
      have : K * log y₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn hlogy₀.le
      linarith
    have hlogu₁ : log y₀ ≤ log u₁ := log_le_log (by linarith) (le_max_right u y₀)
    have hrange : log w ≤ K * log u₁ := by
      have := mul_le_mul_of_nonneg_left hlogu₁ hKpos.le
      linarith
    have hMer := hM u₁ w hYu₁ hcase hrange
    have hsub : (range ⌈w⌉₊).filter (fun p => p ∈ P' ∧ p ∉ Q' ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < w) ⊆
        (range ⌈w⌉₊).filter (fun p : ℕ => p.Prime ∧ u₁ ≤ (p : ℝ) ∧ (p : ℝ) < w) := by
      intro p hp
      have h1 := hFsub p hp
      simp only [mem_filter] at hp ⊢
      exact ⟨hp.1, h1.1, h1.2.1, h1.2.2.1⟩
    have hone : ∀ p ∈ (range ⌈w⌉₊).filter (fun p : ℕ => p.Prime ∧ u₁ ≤ (p : ℝ) ∧ (p : ℝ) < w),
        1 ≤ (1 - (1 + η) / (p : ℝ))⁻¹ := by
      intro p hp
      simp only [mem_filter] at hp
      have hp2 : (2 : ℝ) ≤ p := le_trans hy₀2 (le_trans (le_max_right u y₀) hp.2.2.1)
      have hpos : 0 < (1 + η) / (p : ℝ) := div_pos (by linarith) (by linarith)
      have hlt : (1 + η) / (p : ℝ) < 1 := by
        rw [div_lt_one (by linarith)]; linarith
      exact one_le_inv₀ (by linarith) |>.2 (by linarith)
    calc ∏ p ∈ (range ⌈w⌉₊).filter (fun p => p ∈ P' ∧ p ∉ Q' ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < w),
          (1 - g' n p)⁻¹
        ≤ ∏ p ∈ (range ⌈w⌉₊).filter (fun p => p ∈ P' ∧ p ∉ Q' ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < w),
          (1 - (1 + η) / (p : ℝ))⁻¹ :=
          prod_le_prod₀ (fun p hp => (hfac p hp).1) (fun p hp => (hfac p hp).2)
      _ ≤ ∏ p ∈ (range ⌈w⌉₊).filter (fun p : ℕ => p.Prime ∧ u₁ ≤ (p : ℝ) ∧ (p : ℝ) < w),
          (1 - (1 + η) / (p : ℝ))⁻¹ :=
          prod_le_prod_of_subset_of_one_le₀ hsub
            (fun p hp => le_trans zero_le_one (hone p (hsub hp)))
            (fun p hp _ => hone p hp)
      _ ≤ (1 + ε) * (log w / log u₁) := hMer
      _ ≤ (1 + ε) * (log w / log u) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact div_le_div_of_nonneg_left (by linarith) hlogu
            (log_le_log (by linarith) (le_max_left u y₀))

end LeanLab.BS2022GRH.SieveAllLevels1611

#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.mertens_range_product
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.premise_of_range_split
