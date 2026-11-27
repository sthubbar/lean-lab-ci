/- AI wrote this Lean code for CODEX task700. Goldbach is open.
Geometric convergence of the iterated delay integrals.
BJS arXiv 2207.09452v6 p. 6 displays 15 to 18 and p. 7 Lemma 8.
https://arxiv.org/abs/2207.09452v6 -/
import LeanLab.BS2022GRH.Decomp327a
import LeanLab.BS2022GRH.Delay700

namespace LeanLab.BS2022GRH.DelayTerms700
open Real MeasureTheory Set Decomp327a Delay700
noncomputable section

/-- The first delay term fits the geometric majorant at index one. -/
theorem first_majorant (s : ℝ) (hs : 1 ≤ s) :
    delayTerm 1 s ≤ 4 * exp 3 * (99/100 : ℝ) * weight s := by
  have hwpos := (weight_pos s).le
  by_cases h3 : 3 ≤ s
  · rw [delayTerm_eq_zero_of_endpoint 1 s (by norm_num; exact h3)]
    positivity
  · have hs0 : 0 < s := by linarith
    have hf : delayTerm 1 s ≤ 2 := by
      change max (3-s) 0 / s ≤ 2
      apply (div_le_iff₀ hs0).2
      apply max_le <;> linarith
    have hw : exp (-3) ≤ weight s := by
      unfold weight
      split_ifs with h2 h4
      · exact exp_le_exp.mpr (by norm_num)
      · exact exp_le_exp.mpr (by linarith)
      · linarith
    have hm := mul_le_mul_of_nonneg_left hw
      (show 0 ≤ 4 * exp 3 * (99/100 : ℝ) by positivity)
    have he : exp 3 * exp (-3) = 1 := by rw [← exp_add]; norm_num
    nlinarith

/-- Every delay term has a geometric upper bound on its parity domain. -/
theorem delayTerm_geometric (n : ℕ) (s : ℝ)
    (hs : if n % 2 = 1 then 1 ≤ s else 2 ≤ s) :
    delayTerm n s ≤ 4 * exp 3 * (99/100 : ℝ)^n * weight s := by
  have hwpos := (weight_pos s).le
  induction n using Nat.twoStepInduction generalizing s with
  | zero => simp only [delayTerm]; positivity
  | one =>
      norm_num only at hs ⊢
      exact first_majorant s hs
  | more n ih0 ih1 =>
      let a := if (n+2) % 2 = 1 then max s 3 else s
      have hs0 : 0 < s := by split_ifs at hs <;> linarith
      have ha : 2 ≤ a := by
        dsimp [a]
        split_ifs with h
        · exact le_trans (by norm_num) (le_max_right s 3)
        · rw [ite_eq_right h] at hs; exact hs
      have hprev (t : ℝ) (ht : t ∈ Ioi a) :
          if (n+1)%2=1 then 1 ≤ t-1 else 2 ≤ t-1 := by
        have ht' := Set.mem_Ioi.mp ht
        dsimp [a] at ht'
        by_cases h : (n+2)%2=1
        · rw [ite_eq_left h] at ht'
          have hp : (n+1)%2 ≠ 1 := by omega
          rw [ite_eq_right hp]
          linarith [le_max_right s 3]
        · rw [ite_eq_right h] at ht'
          have hp : (n+1)%2=1 := by omega
          rw [ite_eq_left hp]
          rw [ite_eq_right h] at hs
          linarith
      have hi : (∫ t : ℝ in Ioi a, delayTerm (n+1) (t-1)) ≤
          (4 * exp 3 * (99/100 : ℝ)^(n+1)) *
            ∫ t : ℝ in Ioi a, weight (t-1) := by
        rw [← integral_const_mul]
        apply setIntegral_mono_of_nonneg
        · intro t ht
          exact delayTerm_nonneg (n+1) (t-1) (hprev t ht)
        · intro t ht
          exact ih1 (t-1) (hprev t ht) (weight_pos _).le
        · exact (weight_shift_integrable a ha).const_mul _
      have hc : (∫ t : ℝ in Ioi a, weight (t-1)) ≤
          (99/100 : ℝ) * s * weight s := by
        dsimp [a]
        split_ifs with h
        · exact weight_contraction_odd s (by rw [ite_eq_left h] at hs; exact hs)
        · exact weight_contraction s (by rw [ite_eq_right h] at hs; exact hs)
      have hh := mul_le_mul_of_nonneg_left hc
        (show 0 ≤ 4 * exp 3 * (99/100 : ℝ)^(n+1) by positivity)
      rw [delayTerm]
      change (∫ t : ℝ in Ioi a, delayTerm (n+1) (t-1)) / s ≤ _
      apply (div_le_iff₀ hs0).2
      calc
        _ ≤ (4 * exp 3 * (99/100 : ℝ)^(n+1)) * ((99/100 : ℝ)*s*weight s) := hi.trans hh
        _ = (4 * exp 3 * (99/100 : ℝ)^(n+2) * weight s)*s := by
          rw [show n+2 = (n+1)+1 by omega, pow_succ]
          ring

/-- Geometric comparison proves convergence of the odd series on its full domain. -/
theorem odd_summable (s : ℝ) (hs : 1 ≤ s) :
    Summable (fun n : ℕ => if n%2=1 then delayTerm n s else 0) := by
  have hwpos := (weight_pos s).le
  apply Summable.of_nonneg_of_le (f := fun n : ℕ =>
    (4 * exp 3 * weight s) * (99/100 : ℝ)^n)
  · intro n
    split_ifs with h
    · exact delayTerm_nonneg n s (by simpa [h] using hs)
    · rfl
  · intro n
    split_ifs with h
    · have hh := delayTerm_geometric n s (by simpa [h] using hs)
      nlinarith only [hh]
    · positivity
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 99/100)
      (by norm_num)).mul_left _

/-- Geometric comparison proves convergence of the even series on its full domain. -/
theorem even_summable (s : ℝ) (hs : 2 ≤ s) :
    Summable (fun n : ℕ => if 0<n ∧ n%2=0 then delayTerm n s else 0) := by
  have hwpos := (weight_pos s).le
  apply Summable.of_nonneg_of_le (f := fun n : ℕ =>
    (4 * exp 3 * weight s) * (99/100 : ℝ)^n)
  · intro n
    split_ifs with h
    · exact delayTerm_nonneg n s (by rw [ite_eq_right (by omega)]; exact hs)
    · rfl
  · intro n
    split_ifs with h
    · have hh := delayTerm_geometric n s (by rw [ite_eq_right (by omega)]; exact hs)
      nlinarith only [hh]
    · positivity
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 99/100)
      (by norm_num)).mul_left _

/-- The coarse odd sum budget obtained from the geometric estimate. -/
theorem odd_tsum_coarse (s : ℝ) (hs : 1 ≤ s) :
    (∑' n : ℕ, if n%2=1 then delayTerm n s else 0) ≤ 400 * exp 3 * weight s := by
  have hwpos := (weight_pos s).le
  have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 99/100)
    (by norm_num)).mul_left (4 * exp 3 * weight s)
  have hle := (odd_summable s hs).tsum_le_tsum (fun n => ?_) hg
  · convert hle using 1
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 99/100)
      (by norm_num)]
    norm_num
    ring
  · split_ifs with h
    · have hh := delayTerm_geometric n s (by simpa [h] using hs)
      nlinarith only [hh]
    · positivity

/-- The coarse even sum budget obtained from the geometric estimate. -/
theorem even_tsum_coarse (s : ℝ) (hs : 2 ≤ s) :
    (∑' n : ℕ, if 0<n ∧ n%2=0 then delayTerm n s else 0) ≤ 400 * exp 3 * weight s := by
  have hwpos := (weight_pos s).le
  have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 99/100)
    (by norm_num)).mul_left (4 * exp 3 * weight s)
  have hle := (even_summable s hs).tsum_le_tsum (fun n => ?_) hg
  · convert hle using 1
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 99/100)
      (by norm_num)]
    norm_num
    ring
  · split_ifs with h
    · have hh := delayTerm_geometric n s (by rw [ite_eq_right (by omega)]; exact hs)
      nlinarith only [hh]
    · positivity

/-- The coarse budget is strictly larger than the sharp odd target at two. -/
theorem geometric_budget_two_too_large :
    2 * exp eulerMascheroniConstant / 2 - 1 < 400 * exp 3 * weight 2 := by
  have hg : eulerMascheroniConstant < 1 :=
    eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  have he := exp_lt_exp.mpr hg
  have hm : exp 3 * exp (-2) = exp 1 := by rw [← exp_add]; norm_num
  simp only [weight, show (2 : ℝ) ≤ 2 by norm_num, ↓reduceIte]
  nlinarith [exp_pos (1 : ℝ)]

/-- The odd terms have the affine scaling used in Nathanson Lemma 9.9. -/
theorem odd_term_scaling (n : ℕ) (s : ℝ) (hs : 1 ≤ s) (h3 : s ≤ 3) :
    s * (if n%2=1 then delayTerm n s else 0) =
      3 * (if n%2=1 then delayTerm n 3 else 0) + if n=1 then 3-s else 0 := by
  have hs0 : s ≠ 0 := by linarith
  by_cases ho : n%2=1
  · rw [ite_eq_left ho, ite_eq_left ho]
    rcases n with _ | (_ | n)
    · norm_num at ho
    · norm_num only
      change s*(max (3-s) 0 / s) = 3*(max (3-3) 0 / 3) + (3-s)
      rw [max_eq_left (by linarith : 0 ≤ 3-s), mul_div_cancel₀ _ hs0]
      norm_num
    · have hne : n+1+1 ≠ 1 := by omega
      rw [ite_eq_right hne, add_zero]
      change s * delayTerm (n+2) s = 3 * delayTerm (n+2) 3
      rw [delayTerm, delayTerm]
      have hp : (n+2)%2=1 := by omega
      rw [ite_eq_left hp, ite_eq_left hp, max_eq_right h3, max_self,
        mul_div_cancel₀ _ hs0, mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
  · have hn : n ≠ 1 := by omega
    simp [ho, hn]

/-- The full odd sum has the exact initial scaling, without claiming its normalization. -/
theorem odd_tsum_scaling (s : ℝ) (hs : 1 ≤ s) (h3 : s ≤ 3) :
    s * (1 + ∑' n : ℕ, if n%2=1 then delayTerm n s else 0) =
      3 * (1 + ∑' n : ℕ, if n%2=1 then delayTerm n 3 else 0) := by
  have hsum : (∑' n : ℕ, s * (if n%2=1 then delayTerm n s else 0)) =
      ∑' n : ℕ, (3 * (if n%2=1 then delayTerm n 3 else 0) + if n=1 then 3-s else 0) :=
    tsum_congr (fun n => odd_term_scaling n s hs h3)
  have hsingle : Summable (fun n : ℕ => if n=1 then 3-s else 0) :=
    (hasSum_ite_eq 1 (3-s)).summable
  rw [tsum_mul_left,
    ((odd_summable 3 (by norm_num)).mul_left 3).tsum_add hsingle,
    tsum_mul_left, tsum_ite_eq] at hsum
  linarith

end
end LeanLab.BS2022GRH.DelayTerms700

#print axioms LeanLab.BS2022GRH.DelayTerms700.first_majorant
#print axioms LeanLab.BS2022GRH.DelayTerms700.delayTerm_geometric
#print axioms LeanLab.BS2022GRH.DelayTerms700.odd_summable
#print axioms LeanLab.BS2022GRH.DelayTerms700.even_summable

#print axioms LeanLab.BS2022GRH.DelayTerms700.odd_tsum_coarse
#print axioms LeanLab.BS2022GRH.DelayTerms700.even_tsum_coarse
#print axioms LeanLab.BS2022GRH.DelayTerms700.geometric_budget_two_too_large

#print axioms LeanLab.BS2022GRH.DelayTerms700.odd_term_scaling
#print axioms LeanLab.BS2022GRH.DelayTerms700.odd_tsum_scaling
