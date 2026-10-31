import LeanLab.RieselVaughan1983.Lemma2LogMoments

/-! Convergence of the prime sums defining A0 and A2 on page 46.
AI wrote the Lean code. Binary Goldbach is OPEN. -/
namespace LeanLab.RieselVaughan1983.Lemma2
open Real
noncomputable section

def a0Term (p : ℕ) : ℝ :=
  if p.Prime then Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) else 0

def a2Term (p : ℕ) : ℝ := if p.Prime then
  (8 * (p : ℝ) ^ 2 - 10 * p + 4) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2) *
    Real.log p ^ 2 else 0

lemma root_div_sq (p : ℕ) (hp : 0 < p) :
    (p : ℝ) ^ (1 / 3 : ℝ) / (p : ℝ) ^ 2 = (p : ℝ) ^ (-(5 / 3 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [← Real.rpow_natCast, ← Real.rpow_sub hp0]
  norm_num

lemma a0Term_nonneg (p : ℕ) : 0 ≤ a0Term p := by
  unfold a0Term
  split_ifs with hp
  · apply div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  · exact le_rfl

lemma a0Term_le (p : ℕ) : a0Term p ≤ 6 * (p : ℝ) ^ (-(5 / 3 : ℝ)) := by
  by_cases hp : p.Prime
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hr := Real.rpow_nonneg hp0.le (1 / 3 : ℝ)
    have hl := log_le_root p hp.pos
    have he := root_div_sq p hp.pos
    rw [a0Term, if_pos hp, ← he]
    apply (div_le_iff₀ (mul_pos hp0 (by linarith))).mpr
    field_simp
    nlinarith
  · simp [a0Term, hp, Real.rpow_nonneg]

lemma a2Term_nonneg (p : ℕ) : 0 ≤ a2Term p := by
  unfold a2Term
  split_ifs with hp
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    apply mul_nonneg
    · apply div_nonneg
      · nlinarith
      · positivity
    · positivity
  · exact le_rfl

lemma a2Term_le (p : ℕ) : a2Term p ≤ 576 * (p : ℝ) ^ (-(5 / 3 : ℝ)) := by
  by_cases hp : p.Prime
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp1 : (0 : ℝ) < p - 1 := by linarith
    have hc : (8 * (p : ℝ) ^ 2 - 10 * p + 4) /
        ((p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2) ≤ 32 / (p : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg ((p : ℝ) - 2)]
    have hl := log_sq_le_root p hp.pos
    have hr := Real.rpow_nonneg hp0.le (1 / 3 : ℝ)
    rw [a2Term, if_pos hp, ← root_div_sq p hp.pos]
    calc _ ≤ (32 / (p : ℝ) ^ 2) * Real.log p ^ 2 :=
          mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ ≤ (32 / (p : ℝ) ^ 2) * (18 * (p : ℝ) ^ (1 / 3 : ℝ)) := by gcongr
      _ = _ := by ring
  · simp [a2Term, hp, Real.rpow_nonneg]

lemma a0Term_summable : Summable a0Term :=
  (Real.summable_nat_rpow.mpr (by norm_num : -(5 / 3 : ℝ) < -1)).mul_left 6
    |>.of_nonneg_of_le a0Term_nonneg a0Term_le

lemma a2Term_summable : Summable a2Term :=
  (Real.summable_nat_rpow.mpr (by norm_num : -(5 / 3 : ℝ) < -1)).mul_left 576
    |>.of_nonneg_of_le a2Term_nonneg a2Term_le

lemma A0_hasSum : HasSum a0Term A0 := a0Term_summable.hasSum
lemma A2_hasSum : HasSum a2Term A2 := a2Term_summable.hasSum
lemma A0_nonneg : 0 ≤ A0 := tsum_nonneg a0Term_nonneg
lemma A2_nonneg : 0 ≤ A2 := tsum_nonneg a2Term_nonneg
lemma A1_pos : 0 < A1 := by
  unfold A1
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith [A0_nonneg]

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.root_div_sq
#print axioms LeanLab.RieselVaughan1983.Lemma2.a0Term_nonneg
#print axioms LeanLab.RieselVaughan1983.Lemma2.a0Term_le
#print axioms LeanLab.RieselVaughan1983.Lemma2.a2Term_nonneg
#print axioms LeanLab.RieselVaughan1983.Lemma2.a2Term_le
#print axioms LeanLab.RieselVaughan1983.Lemma2.a0Term_summable
#print axioms LeanLab.RieselVaughan1983.Lemma2.a2Term_summable
#print axioms LeanLab.RieselVaughan1983.Lemma2.A0_hasSum
#print axioms LeanLab.RieselVaughan1983.Lemma2.A2_hasSum
#print axioms LeanLab.RieselVaughan1983.Lemma2.A0_nonneg
#print axioms LeanLab.RieselVaughan1983.Lemma2.A2_nonneg
#print axioms LeanLab.RieselVaughan1983.Lemma2.A1_pos
