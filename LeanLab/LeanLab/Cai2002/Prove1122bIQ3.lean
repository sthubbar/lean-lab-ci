/-
Twin proof of the LEAF `leafB8_IQ3` of `Split1122bBoundary8.lean`.

Source: Bordignon, Johnston, Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, page 6,
displays 15 to 17, quoting Nathanson Theorem 9.4. With O and E the odd and even sums and
A = 3 (1 + O(3)):
* on (0, 3], t O(t) = A - t, displays 15 and 17, copied from tO_low_q8 of the park file
  Prove1122bQInv8.lean;
* on [2, 3], s E(s) = 2 E(2) - A log (s - 1) + s - 2: the function
  s E(s) + A log (s - 1) - s has derivative - O(s - 1) + A / (s - 1) - 1 = 0 on (2, 3) by
  leaf8_deriv_even_twin, and is continuous on [2, 3], E being continuous on [2, ∞) by the
  Weierstrass test, copied from eSum_cont_j8 of the park file Prove1122bJInv8.lean;
* the integral of t Q(t) over [2, 3] is then computed with the antiderivative
  (A + c) t - A ((t - 1) log (t - 1) - (t - 1)), c = 2 E(2) - 2, and the A terms cancel in
  I(3) = 6 Q(3) - that integral.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bBoundary8
import LeanLab.Cai2002.Prove1122bDerivOdd8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- Displays 15 and 17: for 0 < t ≤ 3, t O(t) = 3 - t + 3 O(3). Copy of tO_low_q8. -/
theorem tO_low_iq3 (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 3) :
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

/-- Display 18 with Lemma 8, uniform in x. Copy of term_bound_j8. -/
theorem term_bound_iq3 (P : ℕ → Prop) [DecidablePred P] (x : ℝ)
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

/-- E is continuous on [2, ∞). Copy of eSum_cont_j8. -/
theorem eSum_cont_iq3 : ContinuousOn eSumB8 (Set.Ici 2) := by
  have : ContinuousOn (fun x => ∑' n : ℕ, if Even n then bjsF306 n x else 0) (Set.Ici 2) := by
    refine continuousOn_tsum (fun n => ?_) bound_summable_d8 (fun n x hx => ?_)
    · by_cases h : Even n
      · simp only [if_pos h]
        exact fn_even_contIci_o8 n h
      · simp only [if_neg h]; exact continuousOn_const
    · have : (2 : ℝ) ≤ x := hx
      exact term_bound_iq3 Even x (fun n h => Or.inr ⟨h, this⟩) n
  exact this

/-- Display 16 summed on [2, 3]: s E(s) = 2 E(2) - A log (s - 1) + s - 2. -/
theorem sE_low_iq3 (s : ℝ) (h2 : 2 ≤ s) (h3 : s ≤ 3) :
    s * eSumB8 s = 2 * eSumB8 2 - (3 + 3 * oSumB8 3) * log (s - 1) + s - 2 := by
  set A := 3 + 3 * oSumB8 3 with hA
  rcases eq_or_lt_of_le h2 with h | h
  · subst h; norm_num
  · set φ : ℝ → ℝ := fun t => t * eSumB8 t + A * log (t - 1) - t with hφ
    have hcont : ContinuousOn φ (Set.Icc 2 s) := by
      have hE : ContinuousOn (fun t => t * eSumB8 t) (Set.Icc 2 s) :=
        continuousOn_id.mul (eSum_cont_iq3.mono Set.Icc_subset_Ici_self)
      have hL : ContinuousOn (fun t : ℝ => log (t - 1)) (Set.Icc 2 s) := by
        apply ContinuousOn.log (by fun_prop)
        intro x hx; have := hx.1; linarith
      exact (hE.add (hL.const_smul A)).sub continuousOn_id
    have hder : ∀ x ∈ Set.Ioo 2 s, HasDerivAt φ 0 x := by
      intro x hx
      have hx2 : 2 < x := hx.1
      have hx3 : x < 3 := lt_of_lt_of_le hx.2 h3
      have hE : HasDerivAt (fun t => t * eSumB8 t) (-oSumB8 (x - 1)) x :=
        leaf8_deriv_even_twin x hx2
      have hx1 : x - 1 ≠ 0 := by linarith
      have hL : HasDerivAt (fun t : ℝ => log (t - 1)) (1 / (x - 1)) x := by
        have := ((hasDerivAt_id x).sub_const 1).log hx1
        simpa using this
      have hall := (hE.add (hL.const_mul A)).sub (hasDerivAt_id x)
      have hO : (x - 1) * oSumB8 (x - 1) = 3 - (x - 1) + 3 * oSumB8 3 :=
        tO_low_iq3 (x - 1) (by linarith) (by linarith)
      have : oSumB8 (x - 1) = (A - (x - 1)) / (x - 1) := by
        rw [eq_div_iff hx1, hA]; linarith
      have hv : -oSumB8 (x - 1) + A * (1 / (x - 1)) - 1 = 0 := by
        rw [this]; field_simp; ring
      exact hall.congr_deriv hv
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope φ (fun _ => 0) h hcont hder
    have hs0 : s - 2 ≠ 0 := by linarith
    have heq : φ s = φ 2 := by
      have := hc'; rw [eq_div_iff hs0] at this; linarith
    simp only [hφ] at heq
    norm_num at heq
    linarith

/-- The integral of t Q(t) over [2, 3]. -/
theorem integral_tQ_iq3 :
    ∫ t in (2 : ℝ)..3, t * (oSumB8 t + eSumB8 t) =
      2 * (3 + 3 * oSumB8 3) + (2 * eSumB8 2 - 2) - 2 * (3 + 3 * oSumB8 3) * log 2 := by
  set A := 3 + 3 * oSumB8 3 with hA
  set c := 2 * eSumB8 2 - 2 with hc
  have hcongr : ∫ t in (2 : ℝ)..3, t * (oSumB8 t + eSumB8 t) =
      ∫ t in (2 : ℝ)..3, (A + c - A * log (t - 1)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have h1 := tO_low_iq3 t (by linarith [ht.1]) ht.2
    have h2 := sE_low_iq3 t ht.1 ht.2
    simp only
    rw [mul_add, h1, h2, hA, hc]; ring
  rw [hcongr]
  set F : ℝ → ℝ := fun t => (A + c) * t - A * ((t - 1) * log (t - 1) - (t - 1)) with hF
  have hderF : ∀ x ∈ Set.uIcc (2 : ℝ) 3, HasDerivAt F (A + c - A * log (x - 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have hsub : HasDerivAt (fun t : ℝ => t - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have hlog : HasDerivAt (fun t : ℝ => log (t - 1)) (1 / (x - 1)) x := by
      simpa using hsub.log hx1
    have hall := ((hasDerivAt_id x).const_mul (A + c)).sub
      (((hsub.mul hlog).sub hsub).const_mul A)
    have hv : (A + c) * 1 - A * (1 * log (x - 1) + (x - 1) * (1 / (x - 1)) - 1) =
        A + c - A * log (x - 1) := by
      rw [mul_one_div_cancel hx1]; ring
    exact hall.congr_deriv hv
  have hint : IntervalIntegrable (fun t : ℝ => A + c - A * log (t - 1)) MeasureTheory.volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderF hint]
  simp only [hF]
  norm_num
  ring

/-- Twin of the LEAF `leafB8_IQ3` of `Split1122bBoundary8.lean`, statement copied verbatim. -/
theorem leafB8_IQ3_twin : qInvB8 3 = 2 * eSumB8 2 - 2 := by
  have hI := integral_tQ_iq3
  have h3 := sE_low_iq3 3 (by norm_num) le_rfl
  have hO := tO_low_iq3 3 (by norm_num) le_rfl
  unfold qInvB8
  rw [show (3 : ℝ) - 1 = 2 by norm_num, hI]
  norm_num at h3
  linear_combination 2 * h3

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_IQ3_twin
