/-
Twin proof of the LEAF `leafB8_J3` of `Split1122bBoundary8.lean`.

Source: Bordignon, Johnston, Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, page 6,
displays 15 to 17, quoting Nathanson Theorem 9.4. Write A = 3 (1 + O(3)).

* Displays 15 and 17: for 0 < t ≤ 3, t O(t) = A - t, termwise from the definition.
* Display 16 summed, the PROVED twin leaf8_deriv_even_twin: (t E(t))' = - O(t - 1) for
  t > 2, which on (2, 3) equals 1 - A / (t - 1). With E continuous on [2, ∞) by the
  Weierstrass test and E(2) = 1, the mean value theorem gives
  t E(t) = t - A log (t - 1) on [2, 3].
* Hence P(t) = 2 + O(t) - E(t) = A (1 + log (t - 1)) / t on [2, 3], and
  J(3) = 3 q(3) P(3) + the integral over [2, 3] of P(t) q(t + 1) = A K(q), by linearity of
  the interval integral, which needs no integrability.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bBoundary8
import LeanLab.Cai2002.Prove1122bDerivOdd8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- Displays 15 and 17: for 0 < t ≤ 3, t O(t) = 3 - t + 3 O(3). Copied from tO_low_q8. -/
theorem tO_low_j3 (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 3) :
    t * oSumB8 t = 3 - t + 3 * oSumB8 3 := by
  have htp : t ≠ 0 := ne_of_gt ht0
  have hterm : ∀ n : ℕ, t * (if Odd n then bjsF306 n t else 0) =
      (if n = 1 then 3 - t else 0) + 3 * (if Odd n then bjsF306 n 3 else 0) := by
    intro n
    match n with
    | 0 => simp [bjsF306]
    | 1 =>
      simp only [bjsF306, if_pos odd_one, if_pos ht, if_true, le_refl]
      field_simp; ring
    | m + 2 =>
      have hn : m + 2 ≠ 1 := by omega
      by_cases ho : Odd (m + 2)
      · simp only [bjsF306, if_pos ho, if_neg hn, if_pos (And.intro ho ht),
          if_pos (And.intro ho (le_refl (3 : ℝ)))]
        field_simp; ring
      · simp [ho]
  have hs1 : Summable (fun n : ℕ => if n = 1 then 3 - t else 0) := by
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn; simp only [Finset.mem_singleton] at hn; simp [hn]
  have hs2 : Summable (fun n : ℕ => 3 * (if Odd n then bjsF306 n 3 else 0)) :=
    (parity_summableB8 Odd 3 (fun n h => Or.inl ⟨h, by norm_num⟩) (by norm_num)).mul_left 3
  unfold oSumB8
  rw [← tsum_mul_left]
  simp_rw [hterm]
  rw [hs1.tsum_add hs2, tsum_ite_eq, tsum_mul_left]

/-- Display 18 with Lemma 8, uniform in x. Copied from term_bound_j8. -/
theorem term_bound_j3 (P : ℕ → Prop) [DecidablePred P] (x : ℝ)
    (hP : ∀ n, P n → (Odd n ∧ 1 ≤ x) ∨ (Even n ∧ 2 ≤ x)) (n : ℕ) :
    ‖(if P n then bjsF306 n x else 0)‖ ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by
  have hu : 0 ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by positivity
  split_ifs with h
  · rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      rw [show bjsF306 0 x = 0 from rfl, norm_zero]
      exact hu
    · rw [Real.norm_eq_abs]
      have h1 := abs_fn_le_d8 n hn x (hP n h)
      have h2 := hSieve_le_d8 x
      have h3 : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
      have h4 : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) := by positivity
      have h5 : (0.9607 : ℝ) ^ (n - 1) ≤ (0.9607 : ℝ) ^ (n - 2) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      calc |bjsF306 n x|
          ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * LeanLab.ChenExplicit.hSieve x := h1
        _ ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2) := mul_le_mul_of_nonneg_left h2 h4
        _ = 2 * (0.9607 : ℝ) ^ (n - 1) * (exp 2 * exp (-2)) := by ring
        _ ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by rw [h3, mul_one]; linarith
  · simpa using hu

/-- E is continuous on [2, ∞). Copied from eSum_cont_j8. -/
theorem eSum_cont_j3 : ContinuousOn eSumB8 (Set.Ici 2) := by
  have : ContinuousOn (fun x => ∑' n : ℕ, if Even n then bjsF306 n x else 0) (Set.Ici 2) := by
    refine continuousOn_tsum (fun n => ?_) bound_summable_d8 (fun n x hx => ?_)
    · by_cases h : Even n
      · simp only [if_pos h]
        exact fn_even_contIci_o8 n h
      · simp only [if_neg h]; exact continuousOn_const
    · have : (2 : ℝ) ≤ x := hx
      exact term_bound_j3 Even x (fun n h => Or.inr ⟨h, this⟩) n
  exact this

/-- Display 16 summed on [2, 3] with E(2) = 1: t E(t) = t - A log (t - 1),
A = 3 (1 + O(3)). -/
theorem tE_low_j3 (he : eSumB8 2 = 1) (t : ℝ) (ht2 : 2 ≤ t) (ht3 : t ≤ 3) :
    t * eSumB8 t = t - 3 * (1 + oSumB8 3) * log (t - 1) := by
  set A := 3 * (1 + oSumB8 3) with hA
  set f : ℝ → ℝ := fun x => x * eSumB8 x - x + A * log (x - 1) with hf
  have hf2 : f 2 = 0 := by
    simp only [hf, he]; norm_num
  suffices h : f t = 0 by simp only [hf] at h; linarith
  rcases eq_or_lt_of_le ht2 with h | h
  · rw [← h]; exact hf2
  have hcont : ContinuousOn f (Set.Icc 2 t) := by
    have hE : ContinuousOn eSumB8 (Set.Icc 2 t) := eSum_cont_j3.mono Set.Icc_subset_Ici_self
    have hL : ContinuousOn (fun x : ℝ => log (x - 1)) (Set.Icc 2 t) :=
      (continuousOn_id.sub continuousOn_const).log (fun x hx => by
        have : (2 : ℝ) ≤ x := hx.1
        show x - 1 ≠ 0; linarith)
    exact ((continuousOn_id.mul hE).sub continuousOn_id).add (continuousOn_const.mul hL)
  have hderiv : ∀ x ∈ Set.Ioo 2 t,
      HasDerivAt f (-oSumB8 (x - 1) - 1 + A * (1 / (x - 1))) x := by
    intro x hx
    have hx2 : (2 : ℝ) < x := hx.1
    have h1 : HasDerivAt (fun y : ℝ => y * eSumB8 y) (-oSumB8 (x - 1)) x :=
      leaf8_deriv_even_twin x hx2
    have hne : x - 1 ≠ 0 := by linarith
    have h2 : HasDerivAt (fun y : ℝ => log (y - 1)) (1 / (x - 1)) x := by
      have := ((hasDerivAt_id x).sub_const 1).log hne
      simpa using this
    exact (h1.sub (hasDerivAt_id x)).add (h2.const_mul A)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f _ h hcont hderiv
  have hc1 : 1 < c - 1 := by linarith [hc.1]
  have hc3 : c - 1 ≤ 3 := by linarith [hc.2]
  have hO := tO_low_j3 (c - 1) (by linarith) hc3
  have hzero : -oSumB8 (c - 1) - 1 + A * (1 / (c - 1)) = 0 := by
    have hne : c - 1 ≠ 0 := by linarith
    field_simp
    rw [hA]
    linarith
  rw [hzero, hf2, eq_comm, div_eq_zero_iff] at hslope
  rcases hslope with h' | h'
  · linarith
  · exact absurd h' (by linarith)

/-- P(t) = A (1 + log (t - 1)) / t on [2, 3]. -/
theorem pSum_low_j3 (he : eSumB8 2 = 1) (t : ℝ) (ht2 : 2 ≤ t) (ht3 : t ≤ 3) :
    pSumB8 t = 3 * (1 + oSumB8 3) * (1 + log (t - 1)) / t := by
  have hne : t ≠ 0 := by linarith
  have h1 := tO_low_j3 t (by linarith) ht3
  have h2 := tE_low_j3 he t ht2 ht3
  rw [eq_div_iff hne]
  unfold pSumB8
  linear_combination h1 - h2

/-- Twin of leafB8_J3 of Split1122bBoundary8.lean, statement copied verbatim. -/
theorem leafB8_J3_twin (q : ℝ → ℝ) (hq : IsAdjB8 q) (he : eSumB8 2 = 1) :
    jInvB8 q 3 = 3 * (1 + oSumB8 3) * kConstB8 q := by
  unfold jInvB8 kConstB8
  rw [show (3 : ℝ) - 1 = 2 by norm_num]
  rw [intervalIntegral.integral_congr (g := fun t =>
      3 * (1 + oSumB8 3) * ((1 + log (t - 1)) * q (t + 1) / t)) (fun t ht => by
    rw [Set.uIcc_of_le (by norm_num)] at ht
    simp only
    rw [pSum_low_j3 he t ht.1 ht.2]
    ring)]
  rw [intervalIntegral.integral_const_mul, pSum_low_j3 he 3 (by norm_num) le_rfl,
    show (3 : ℝ) - 1 = 2 by norm_num]
  ring

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_J3_twin
