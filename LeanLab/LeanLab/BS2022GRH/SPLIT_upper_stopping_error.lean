/-
Split of the OPEN target `upper_stopping_error` of Decomp327b, the signed upper stopping error
of BJS arXiv 2207.09452v6, Lemma 11 display 33 summed over odd n as in Proposition 13 p. 14,
with the constant C1 of Lemma 14 read from journal Table 1 p. 1218.

The target sums, over odd n, the stopping term T_n of display 28 minus V times the delay term f_n.
The paper proof bounds each term by V times epsilon tau_n e^2 h of s, display 32, and sums the
tau_n over odd n into C1 of epsilon, which Table 1 bounds by 112.

The n equal to one term is ALREADY PROVED in Decomp327a as `first_stopping_bound`, with tau_1
equal to 3, BJS p. 11. This file uses it, so the open content is the odd n at least 3 tail with
coefficient 112 minus 3, that is 109, which is exactly the sum of tau_{2n-1} over n at least 2.
That tail is split by the range of s into the piece where h is the constant e^{-2}, s at most 2,
and the piece where h of s is e^{-s}, s from 2 to 3, the two branches of BJS display 7.

This file adds no definition, changes no existing file, and leaves the sealed statement untouched.
The assembly declares neither the target nor any leaf as a hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.Decomp327b

namespace LeanLab.BS2022GRH.Decomp327b
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d Decomp327a
noncomputable section

/-- LEAF: BJS Lemma 11 for odd n at least 3, case n odd and 1 at most s at most 3 via display 39,
summed as in Proposition 13 over odd n from 3, with the tail of C1 from Lemma 14 and journal
Table 1 p. 1218, restricted to s at most 2 where h of s equals e^{-2}. Class HARD, a real
analytic induction step for Codex: displays 34 to 39 and the numerical bound on the sum of tau_n
over odd n at least 3 by 109. Strictly easier than the target: the n equal to one term is absent
and s is confined to the interval from 1 to 2. Non-vacuity: z equal to D equal to 2 gives s equal
to 1, and P empty satisfies every hypothesis. -/
theorem upper_stopping_odd_tail_low (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ≤ D) (hs : log D / log z ≤ 2) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if 3 ≤ n ∧ n % 2 = 1 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 109 * exp 2 * hS (log D / log z)) := by
  have h_main : (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3), if 3 ≤ n ∧ n % 2 = 1 then stoppingTerm (siftingPrimes P z \ Q) D g n - (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z) else 0) ≤ (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * ((1 / 8349 : ℝ) * 109 * exp 2 * hS (log D / log z)) := by
    classical
    -- Set up notation
    let S := siftingPrimes P z \ Q
    let V := ∏ p ∈ S, (1 - g p)
    let s := log D / log z
    -- The τ_n constants from BJS Lemma 14 (defined recursively in the paper for ε = 1/8349)
    -- τ_1 = 3, τ_n ≥ 0 for all n, and ∑_{odd n≥3} τ_n = 109.
    -- We use a placeholder definition here; the actual values come from the paper's recursive definition.
    let tau : ℕ → ℝ := fun n => 0
    have h_tau_sum : ∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), tau n ≤ 109 := by sorry
    have h_tau_nonneg : ∀ n, 0 ≤ tau n := by sorry
    have hzpos : 0 < z := by linarith
    have hlz : 0 < log z := Real.log_pos (by linarith)
    have hD : 1 < D := by linarith
    have hlD : 0 < log D := Real.log_pos hD
    have hs1 : 1 ≤ s := by
      rw [show s = log D / log z by rfl]
      apply (le_div_iff₀ hlz).2
      exact Real.log_le_log (by linarith) hzD
    have hs2 : s ≤ 2 := by
      rw [show s = log D / log z by rfl]
      exact hs
    have hVpos : 0 ≤ V := by
      apply Finset.prod_nonneg
      intro p hp
      have h₁ : 0 ≤ g p := (hg p (by
        simp only [S, Finset.mem_sdiff, Finset.mem_filter] at hp ⊢
        norm_cast at hp ⊢
        <;> aesop)).1
      have h₂ : g p < 1 := (hg p (by
        simp only [S, Finset.mem_sdiff, Finset.mem_filter] at hp ⊢
        norm_cast at hp ⊢
        <;> aesop)).2
      linarith
    -- Convert the sum to a filtered sum over odd n ≥ 3
    have h_sum_filter : (∑ n ∈ Finset.range (S.card + 3), (if 3 ≤ n ∧ n % 2 = 1 then stoppingTerm S D g n - V * delayTerm n s else 0 : ℝ)) = ∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), (stoppingTerm S D g n - V * delayTerm n s : ℝ) := by
      calc
        (∑ n ∈ Finset.range (S.card + 3), (if 3 ≤ n ∧ n % 2 = 1 then stoppingTerm S D g n - V * delayTerm n s else 0 : ℝ)) = ∑ n in Finset.range (S.card + 3), (if 3 ≤ n ∧ n % 2 = 1 then (stoppingTerm S D g n - V * delayTerm n s : ℝ) else 0) := by simp [sub_eq_add_neg]
        _ = ∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), (stoppingTerm S D g n - V * delayTerm n s : ℝ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n hn
          split_ifs <;> simp_all
          <;> aesop
    rw [h_sum_filter]
    -- Per-term bound (BJS Lemma 11, display 33/39): for each odd n ≥ 3,
    -- stoppingTerm S D g n - V * delayTerm n s ≤ V * (1/8349) * τ_n * exp 2 * hS s
    -- where τ_n are the constants from BJS Lemma 14, with τ_1 = 3 and ∑_{odd n≥3} τ_n = 109.
    -- The actual τ_n are defined recursively in the paper (Lemma 14) and depend on ε = 1/8349.
    have h_per_term : ∀ n ∈ (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), (stoppingTerm S D g n - V * delayTerm n s : ℝ) ≤ V * ((1 / 8349 : ℝ) * tau n * Real.exp 2 * hS s) := by
      sorry
    -- Sum the per-term bounds
    have h_sum_bound : ∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), (stoppingTerm S D g n - V * delayTerm n s : ℝ) ≤ ∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), (V * ((1 / 8349 : ℝ) * tau n * Real.exp 2 * hS s) : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact h_per_term n hn
    -- Factor out constants
    have h_sum_const : ∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), (V * ((1 / 8349 : ℝ) * tau n * Real.exp 2 * hS s) : ℝ) = (∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), tau n) * (V * ((1 / 8349 : ℝ) * Real.exp 2 * hS s)) := by
      calc
        ∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), (V * ((1 / 8349 : ℝ) * tau n * Real.exp 2 * hS s) : ℝ) = ∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), (tau n * (V * ((1 / 8349 : ℝ) * Real.exp 2 * hS s))) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = (∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), tau n) * (V * ((1 / 8349 : ℝ) * Real.exp 2 * hS s)) := by
          rw [Finset.sum_mul]
          <;> simp [mul_assoc, mul_comm, mul_left_comm]
    rw [h_sum_const] at h_sum_bound
    -- Bound the sum of τ_n by 109 (BJS Lemma 14 / Table 1: ∑_{odd n≥3} τ_n = 109)
    have h_tau_sum_bound : (∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), tau n) ≤ 109 := by
      sorry
    -- hS s is positive
    have h_hS_pos : 0 < hS s := by
      rw [show s = log D / log z by rfl]
      have h₁ : 1 ≤ (log D / log z : ℝ) := hs1
      exact hS_pos h₁
    have h_exp_pos : 0 < Real.exp 2 := Real.exp_pos 2
    have h_coeff_pos : 0 < (1 / 8349 : ℝ) * Real.exp 2 * hS s := by positivity
    have h_V_pos : 0 ≤ V := hVpos
    have h_tau_nonneg_sum : 0 ≤ ∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), tau n := by
      apply Finset.sum_nonneg
      intro n hn
      exact h_tau_nonneg n
    -- Combine the bounds
    have h_final : (∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), tau n) * (V * ((1 / 8349 : ℝ) * Real.exp 2 * hS s)) ≤ V * ((1 / 8349 : ℝ) * 109 * Real.exp 2 * hS s) := by
      have h₁ : (∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), tau n) ≤ 109 := h_tau_sum_bound
      have h₂ : 0 ≤ V := hVpos
      have h₃ : 0 ≤ (1 / 8349 : ℝ) * Real.exp 2 * hS s := by positivity
      have h₄ : 0 ≤ V * ((1 / 8349 : ℝ) * Real.exp 2 * hS s) := by positivity
      calc
        (∑ n in (Finset.range (S.card + 3)).filter (fun n => 3 ≤ n ∧ n % 2 = 1), tau n) * (V * ((1 / 8349 : ℝ) * Real.exp 2 * hS s)) ≤ 109 * (V * ((1 / 8349 : ℝ) * Real.exp 2 * hS s)) := by
          gcongr
        _ = V * (109 * ((1 / 8349 : ℝ) * Real.exp 2 * hS s)) := by ring
        _ = V * ((1 / 8349 : ℝ) * 109 * Real.exp 2 * hS s) := by ring
    linarith
  simpa using h_main

/-- LEAF: BJS Lemma 11 for odd n at least 3 via display 39, summed as in Proposition 13 over odd
n from 3, with the tail of C1 from Lemma 14 and journal Table 1 p. 1218, restricted to s from 2 to
3 where h of s equals e^{-s}. Class HARD, a real analytic induction step for Codex: displays 34 to
39, Lemma 10 for the integral of h, and the bound 109 on the sum of tau_n over odd n at least 3.
Strictly easier than the target: the n equal to one term is absent and s is confined to the
interval from 2 to 3. Non-vacuity: z equal to 2 and D equal to 4 gives s equal to 2, and P empty
satisfies every hypothesis. -/
theorem upper_stopping_odd_tail_high (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hs2 : 2 ≤ log D / log z) (hs : log D / log z ≤ 3) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if 3 ≤ n ∧ n % 2 = 1 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 109 * exp 2 * hS (log D / log z)) := by
  sorry

/-- The target statement verbatim, from `first_stopping_bound` of Decomp327a, proved, and the
two LEAF tails. CONDITIONAL ON upper_stopping_odd_tail_low and upper_stopping_odd_tail_high. -/
theorem upper_stopping_error_split (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ≤ D) (hs : log D / log z ≤ 3) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if n % 2 = 1 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 112 * exp 2 * hS (log D / log z)) := by
  set S := siftingPrimes P z \ Q
  set V := ∏ p ∈ S, (1 - g p)
  set s := log D / log z with hsdef
  have hlz : 0 < log z := log_pos (by linarith)
  have hs1 : 1 ≤ s := by
    rw [hsdef, le_div_iff₀ hlz, one_mul]
    exact log_le_log (by linarith) hzD
  have hspos : 0 < s := by linarith
  rw [odd_sum_split _ (by omega)]
  have h1 : stoppingTerm S D g 1 ≤ V * (3 / s - 1 + (1 / 8349 : ℝ) * 3 * exp 2 * hS s) :=
    first_stopping_bound P Q g z D hP hg hz hprod hzD hs
  have hd1 : delayTerm 1 s = 3 / s - 1 := by
    simp only [delayTerm]
    rw [max_eq_left (by linarith)]
    field_simp
  have htail : (∑ n ∈ range (S.card + 3),
      if 3 ≤ n ∧ n % 2 = 1 then stoppingTerm S D g n - V * delayTerm n s else 0) ≤
      V * ((1 / 8349 : ℝ) * 109 * exp 2 * hS s) := by
    rcases le_total s 2 with h2 | h2
    · exact upper_stopping_odd_tail_low P Q g z D hP hg hz hprod hzD h2
    · exact upper_stopping_odd_tail_high P Q g z D hP hg hz hprod h2 hs
  rw [hd1]
  have e1 : V * (3 / s - 1 + (1 / 8349 : ℝ) * 3 * exp 2 * hS s) =
      V * (3 / s - 1) + V * ((1 / 8349 : ℝ) * 3 * exp 2 * hS s) := by ring
  have e2 : V * ((1 / 8349 : ℝ) * 112 * exp 2 * hS s) =
      V * ((1 / 8349 : ℝ) * 3 * exp 2 * hS s) + V * ((1 / 8349 : ℝ) * 109 * exp 2 * hS s) := by
    ring
  linarith [h1, htail, e1, e2]

end

end LeanLab.BS2022GRH.Decomp327b

#print axioms LeanLab.BS2022GRH.Decomp327b.upper_stopping_odd_tail_low
#print axioms LeanLab.BS2022GRH.Decomp327b.upper_stopping_odd_tail_high
#print axioms LeanLab.BS2022GRH.Decomp327b.upper_stopping_error_split
