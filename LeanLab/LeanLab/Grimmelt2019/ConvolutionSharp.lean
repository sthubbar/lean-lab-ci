/-
AI wrote this Lean code for CODEX task03.
P0074, pages 13 and 14, the main term and its character error.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.RamanujanError
import LeanLab.Grimmelt2019.PaperCharacter

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Uniform character estimates give convolution error at most cnu times Q sqrt Q times E. -/
theorem conv_Tnu_approx_characters {X Y cν cω E : ℝ} {Q : ℕ} {ω : ℤ → ℝ} {n : ℤ}
    (hcν : 0 ≤ cν) (hE : 0 ≤ E)
    (hχ : ∀ q ∈ Finset.Icc 1 Q, CharacterEquidist (Wn X Y n) q ω (cω * Y) E)
    (hrough : ∀ q ∈ Finset.Icc 1 Q, ∀ m ∈ Wn X Y n, Int.gcd m q ≠ 1 → ω m = 0) :
    |Prop21.conv (Prop21.supp X) ω (Tnu cν Y Q) n - cν * cω * Y * SQ Q n| ≤
      cν * (Q : ℝ) * Real.sqrt Q * E := by
  let R : ℕ → ℝ := fun q => (ArithmeticFunction.moebius q : ℝ) / q.totient *
      (∑ m ∈ Wn X Y n, ω m * ram q (n - m)) -
    cω * Y * ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * ram q n)
  have hdiff : Prop21.conv (Prop21.supp X) ω (Tnu cν Y Q) n - cν * cω * Y * SQ Q n =
      cν * ∑ q ∈ Finset.Icc 1 Q, R q := by
    rw [conv_Tnu, SQ_eq_paper]
    dsimp only [R]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hRq : ∀ q ∈ Finset.Icc 1 Q, |R q| ≤ Real.sqrt Q * E := by
    intro q hq
    have hq' := Finset.mem_Icc.mp hq
    letI : NeZero q := ⟨by omega⟩
    have hr := ram_term_error hE (hχ q hq) n (hrough q hq)
    exact hr.trans (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (by exact_mod_cast hq'.2)) hE)
  have hsum : |∑ q ∈ Finset.Icc 1 Q, R q| ≤ (Q : ℝ) * Real.sqrt Q * E := by
    calc
      _ ≤ ∑ q ∈ Finset.Icc 1 Q, |R q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ Finset.Icc 1 Q, Real.sqrt Q * E := Finset.sum_le_sum hRq
      _ = _ := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp only [Nat.add_sub_cancel]
        ring
  rw [hdiff, abs_mul, abs_of_nonneg hcν]
  exact (mul_le_mul_of_nonneg_left hsum hcν).trans_eq (by ring)

/-- The literal condition 29 and roughness give the sharp paper main term estimate. -/
theorem conv_Tnu_approx_paperCondition29 {X Y H cν cω E : ℝ} {Q : ℕ} {ω : ℤ → ℝ}
    (hY : 0 ≤ Y) (hX : 1 ≤ X - 3 * Y) (hH : H < Y) (hE : 0 ≤ E) (hcν : 0 ≤ cν)
    (h29 : ∀ q ∈ Finset.Icc 1 Q, PaperCondition29 X Y q ω cω E)
    (hrough : ∀ m ∈ omegaRange X Y, ω m ≠ 0 → QRough Q m)
    (n : ℤ) (hn : n ∈ Prop21.win X H) :
    |Prop21.conv (Prop21.supp X) ω (Tnu cν Y Q) n - cν * cω * Y * SQ Q n| ≤
      cν * (Q : ℝ) * Real.sqrt Q * (2 * E + |cω|) := by
  have hn' : X - H ≤ (n : ℝ) ∧ (n : ℝ) ≤ X := by
    simpa only [Prop21.win, Finset.mem_Icc, Int.ceil_le, Int.le_floor] using hn
  have hleft : 1 ≤ (n : ℝ) - 2 * Y := by linarith
  have hright : (n : ℝ) - Y ≤ X := by linarith
  have hW := Wn_subset_omegaRange hH hn
  apply conv_Tnu_approx_characters hcν (by positivity)
  · intro q hq
    exact character_window_of_prefix (omegaRange X Y) hY hleft hright
      (omegaRange_subset_supp hY hX) hW (prefix_of_paperCondition29 hY (h29 q hq))
  · intro q hq m hm hbad
    by_contra hne
    have hqr := Finset.mem_Icc.mp hq
    exact hbad ((hrough m (hW hm) hne).gcd_eq_one (by omega) hqr.2)

#print axioms conv_Tnu_approx_characters
#print axioms conv_Tnu_approx_paperCondition29
end LeanLab.Grimmelt2019.MainTerm
