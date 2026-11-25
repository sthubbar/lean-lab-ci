/-
Split of the three HARD leaves delay_odd_at_three_bound, delay_even_bound_two_three and
delay_even_bound_three_four of SPLIT_delay_odd_summable and SPLIT_delay_even_summable, all
instances of BJS arXiv 2207.09452v6 display 18 with c_n equal to 0.9607, Lemma 8, cited by BJS
from Nathanson Lemma 9.7.

BJS Remark 1 after Lemma 10 says Lemma 8 is Nathanson's induction driven by the bound
H of s at most alpha s h of s, where H of s is the integral of h of t minus 1 over t above s,
display 24, and h is display 7, the existing definition hS. This file proves that induction in
Lean: the case n equal to 1 from display 15, and the step from displays 16 and 17 with
integral monotonicity. The two remaining LEAFs are the pure real bounds of BJS Lemma 10,
display 25 at s0 equal to 2 and display 26; they mention no delay term.

This file adds no definition and changes no existing file.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SPLIT_delay_even_summable

namespace LeanLab.BS2022GRH.Decomp327a
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d MeasureTheory Set
noncomputable section

/-- LEAF: BJS Lemma 10 display 25 at s0 equal to 2 with kappa_2 equal to 0.9607, where H of s
is the integral of h of t minus 1 over t above s, display 24, and h is display 7. Class HARD:
the paper reduces it to display 27 and a monotonicity claim plus the exponential integral
E1 of 3 to five digits; the maximum of H of s over s h of s is alpha equal to 0.96068 at s
equal to 2, so the margin is about 2e-5. Checked numerically in this session on s from 2 to 12. -/
theorem bjs_lemma10_H_le (s : ℝ) (hs : 2 ≤ s) :
    ∫ t in Ioi s, hS (t - 1) ≤ 0.9607 * s * hS s := by
  sorry

/-- LEAF: BJS Lemma 10 display 26 with kappa tilde equal to 0.9214: H of 3 is at most
kappa tilde s h of s for s from 1 to 3. Class MEDIUM: the paper uses H of 3 equal to
H of 2 minus e^-2 and the decrease of s e^-s, with 2 alpha minus 1 at most 0.9214, which
again needs E1 of 3 to about four digits. Checked numerically in this session. -/
theorem bjs_lemma10_H3_le (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    ∫ t in Ioi (3 : ℝ), hS (t - 1) ≤ 0.9214 * s * hS s := by
  sorry

/-- Proved: h of u is at most e^-u for u at least 1, display 7. -/
theorem hS_le_exp_neg (u : ℝ) (hu : 1 ≤ u) : hS u ≤ exp (-u) := by
  unfold hS
  split_ifs with h2 h3
  · exact exp_le_exp.mpr (by linarith)
  · exact le_rfl
  · have hu0 : 0 < u := by linarith
    have : 3 / u ≤ 1 := by rw [div_le_one hu0]; linarith
    have he := (exp_pos (-u)).le
    nlinarith

/-- Proved: h of display 7 is measurable. -/
theorem hS_measurable : Measurable hS := by
  unfold hS
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop))

/-- Proved: t maps to h of t minus 1 is integrable above any L at least 2, so H of display 24
is a genuine integral. -/
theorem hS_shift_integrableOn (L : ℝ) (hL : 2 ≤ L) :
    IntegrableOn (fun t => hS (t - 1)) (Ioi L) := by
  have hb : IntegrableOn (fun t : ℝ => exp 1 * exp (-t)) (Ioi L) :=
    (integrableOn_exp_neg_Ioi L).const_mul _
  refine hb.mono' ((hS_measurable.comp (measurable_id.sub_const 1)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  have ht' : L < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (LeanLab.BS2022GRH.Envelope327.hS_pos (by linarith)).le]
  calc hS (t - 1) ≤ exp (-(t - 1)) := hS_le_exp_neg _ (by linarith)
    _ = exp 1 * exp (-t) := by rw [← exp_add]; ring_nf

/-- Proved: a nonnegative integrand bounded by C h of t minus 1 above L has integral at most
C H of L, the integral step of Nathanson's induction. -/
theorem shifted_integral_le (f : ℝ → ℝ) (C L : ℝ) (hL : 2 ≤ L)
    (h0 : ∀ t, L < t → 0 ≤ f (t - 1)) (hle : ∀ t, L < t → f (t - 1) ≤ C * hS (t - 1)) :
    ∫ t in Ioi L, f (t - 1) ≤ C * ∫ t in Ioi L, hS (t - 1) := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg ?_ ((hS_shift_integrableOn L hL).const_mul C) ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => h0 t ht)
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => hle t ht)

/-- Display 18 with c_n equal to 0.9607 for every n at least 1, on the domain of display 18,
by Nathanson's induction. CONDITIONAL ON bjs_lemma10_H_le and bjs_lemma10_H3_le. -/
theorem bound18 (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : if n % 2 = 1 then 1 ≤ s else 2 ≤ s) :
    delayTerm n s ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * hS s := by
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
  · have hs1 : 1 ≤ s := by simpa using hs
    have hs0 : 0 < s := by linarith
    simp only [delayTerm, Nat.sub_self, pow_zero, mul_one]
    rw [div_le_iff₀ hs0]
    have hm : max (3 - s) 0 = 0 ∨ (max (3 - s) 0 = 3 - s ∧ s ≤ 3) := by
      rcases le_total (3 - s) 0 with h | h
      · left; exact max_eq_right h
      · right; exact ⟨max_eq_left h, by linarith⟩
    unfold hS
    split_ifs with ha hb
    · have hk : 2 * exp 2 * exp (-2) = 2 := by rw [mul_assoc, ← exp_add]; simp
      rw [hk]; rcases hm with h | ⟨h, _⟩ <;> rw [h] <;> linarith
    · have hk : 2 * exp 2 * exp (-s) = 2 * exp (2 - s) := by
        rw [mul_assoc, ← exp_add]; ring_nf
      rw [hk]
      have ha' : 2 < s := not_le.mp ha
      have he : exp (-1) ≤ exp (2 - s) := exp_le_exp.mpr (by linarith)
      have he1 : (1 : ℝ) / 4 ≤ exp (-1) := by
        rw [exp_neg, one_div]
        apply inv_anti₀ (exp_pos 1)
        linarith [exp_one_lt_d9]
      rcases hm with h | ⟨h, _⟩ <;> rw [h] <;> nlinarith
    · have : max (3 - s) 0 = 0 := max_eq_right (by linarith)
      rw [this]; positivity
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have IH : ∀ u : ℝ, (if (m + 1) % 2 = 1 then 1 ≤ u else 2 ≤ u) →
        delayTerm (m + 1) u ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * hS u := by
      intro u hu
      have := ih (m + 1) (by omega) (by omega) u hu
      rwa [show m + 1 - 1 = m by omega] at this
    have hs0 : 0 < s := by
      split_ifs at hs <;> linarith
    have hC : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m := by positivity
    rw [delayTerm, div_le_iff₀ hs0]
    by_cases ho : (m + 2) % 2 = 1
    · rw [if_pos ho] at hs ⊢
      have hm1 : ¬ (m + 1) % 2 = 1 := by omega
      have hL : 2 ≤ max s 3 := le_trans (by norm_num) (le_max_right s 3)
      have key := shifted_integral_le (delayTerm (m + 1)) (2 * exp 2 * (0.9607 : ℝ) ^ m)
        (max s 3) hL
        (fun t ht => delayTerm_nonneg (m + 1) (t - 1)
          (by rw [if_neg hm1]; linarith [le_max_right s 3]))
        (fun t ht => IH (t - 1) (by rw [if_neg hm1]; linarith [le_max_right s 3]))
      have hH : ∫ t in Ioi (max s 3), hS (t - 1) ≤ 0.9607 * s * hS s := by
        have hhs := (LeanLab.BS2022GRH.Envelope327.hS_pos hs).le
        rcases le_total s 3 with h3 | h3
        · rw [max_eq_right h3]
          have := bjs_lemma10_H3_le s hs h3
          nlinarith [mul_nonneg hs0.le hhs]
        · rw [max_eq_left h3]; exact bjs_lemma10_H_le s (by linarith)
      calc ∫ t in Ioi (max s 3), delayTerm (m + 1) (t - 1)
          ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * ∫ t in Ioi (max s 3), hS (t - 1) := key
        _ ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * (0.9607 * s * hS s) :=
            mul_le_mul_of_nonneg_left hH hC
        _ = 2 * exp 2 * (0.9607 : ℝ) ^ (m + 2 - 1) * hS s * s := by
            rw [show m + 2 - 1 = m + 1 by omega, pow_succ]; ring
    · rw [if_neg ho] at hs ⊢
      have hm1 : (m + 1) % 2 = 1 := by omega
      have key := shifted_integral_le (delayTerm (m + 1)) (2 * exp 2 * (0.9607 : ℝ) ^ m)
        s hs
        (fun t ht => delayTerm_nonneg (m + 1) (t - 1)
          (by rw [if_pos hm1]; linarith [show s < t from ht]))
        (fun t ht => IH (t - 1) (by rw [if_pos hm1]; linarith [show s < t from ht]))
      have hH := bjs_lemma10_H_le s hs
      calc ∫ t in Ioi s, delayTerm (m + 1) (t - 1)
          ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * ∫ t in Ioi s, hS (t - 1) := key
        _ ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * (0.9607 * s * hS s) :=
            mul_le_mul_of_nonneg_left hH hC
        _ = 2 * exp 2 * (0.9607 : ℝ) ^ (m + 2 - 1) * hS s * s := by
            rw [show m + 2 - 1 = m + 1 by omega, pow_succ]; ring

/-- The leaf delay_odd_at_three_bound verbatim. CONDITIONAL ON the two Lemma 10 LEAFs. -/
theorem delay_odd_at_three_bound_split (n : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    delayTerm n 3 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-3) := by
  have h := bound18 n (by omega) 3 (by rw [if_pos hodd]; norm_num)
  have h3 : hS 3 = exp (-3) := by norm_num [hS]
  rwa [h3] at h

/-- The leaf delay_even_bound_two_three verbatim. CONDITIONAL ON the two Lemma 10 LEAFs. -/
theorem delay_even_bound_two_three_split (n : ℕ) (hn : 2 ≤ n) (heven : n % 2 = 0) (s : ℝ)
    (hs2 : 2 ≤ s) (hs3 : s ≤ 3) :
    delayTerm n s ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-s) := by
  have h := bound18 n (by omega) s (by rw [if_neg (by omega)]; exact hs2)
  have hh : hS s = exp (-s) := by
    unfold hS
    split_ifs <;> first | rfl | (rw [show s = 2 by linarith]) | (exfalso; linarith)
  rwa [hh] at h

/-- The leaf delay_even_bound_three_four verbatim. CONDITIONAL ON the two Lemma 10 LEAFs. -/
theorem delay_even_bound_three_four_split (n : ℕ) (hn : 2 ≤ n) (heven : n % 2 = 0) (s : ℝ)
    (hs3 : 3 ≤ s) (hs4 : s ≤ 4) :
    delayTerm n s ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * (3 / s * exp (-s)) := by
  have h := bound18 n (by omega) s (by rw [if_neg (by omega)]; linarith)
  have hh : hS s = 3 / s * exp (-s) := by
    unfold hS
    split_ifs <;> first | rfl | (exfalso; linarith) | (rw [show s = 3 by linarith]; norm_num)
  rwa [hh] at h

end

end LeanLab.BS2022GRH.Decomp327a

#print axioms LeanLab.BS2022GRH.Decomp327a.bjs_lemma10_H_le
#print axioms LeanLab.BS2022GRH.Decomp327a.bjs_lemma10_H3_le
#print axioms LeanLab.BS2022GRH.Decomp327a.hS_le_exp_neg
#print axioms LeanLab.BS2022GRH.Decomp327a.hS_measurable
#print axioms LeanLab.BS2022GRH.Decomp327a.hS_shift_integrableOn
#print axioms LeanLab.BS2022GRH.Decomp327a.shifted_integral_le
#print axioms LeanLab.BS2022GRH.Decomp327a.bound18
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_odd_at_three_bound_split
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_even_bound_two_three_split
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_even_bound_three_four_split
