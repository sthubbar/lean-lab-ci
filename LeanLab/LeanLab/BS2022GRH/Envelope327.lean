/- AI wrote this Lean code for CODEX task327. Goldbach is open.
Source audit and auxiliary bounds for the Rosser model leaves.
BJS arXiv 2207.09452v6, p. 8 Lemma 9 displays 22 and 23.
https://arxiv.org/abs/2207.09452v6 -/
import LeanLab.BS2022GRH.Thm6Factor

namespace LeanLab.BS2022GRH.Envelope327
open Real
noncomputable section

/-- The sieve error envelope is positive on its source domain, p. 5 display 7. -/
theorem hS_pos {s : ℝ} (hs : 1 ≤ s) : 0 < hS s := by
  unfold hS
  split_ifs <;> positivity

/-- On the first transition interval the shifted envelope is constant.
BJS p. 8 display 22, using the definition on p. 5 display 7. -/
theorem hS_shift_eq {s : ℝ} (hs : 2 ≤ s) (ht : s ≤ 3) :
    hS (s - 1) = exp (s - 2) * hS s := by
  have hleft : hS (s - 1) = exp (-2) := by
    rw [hS, if_pos (by linarith)]
  rw [hleft]
  by_cases h2 : s ≤ 2
  · have he : s = 2 := by linarith
    subst s
    simp [hS]
  · rw [hS, if_neg h2, if_pos ht, ← exp_add]
    congr 1
    ring

/-- The printed first branch of BJS Lemma 9 fails at s0 equal to two
and s equal to eleven fifths. This is a source QUESTION, not a leaf refutation.
Current arXiv 2207.09452 p. 8 display 22. -/
theorem bjs_lemma9_counterexample :
    exp ((2 : ℝ) - 2) * hS (11 / 5) < hS (11 / 5 - 1) := by
  norm_num [hS]

/-- The universal printed first branch is false on its stated domain.
The witness is s0 equal to two and s equal to eleven fifths, p. 8 display 22. -/
theorem not_bjs_lemma9_first_branch :
    ¬ ∀ s0 s : ℝ, 2 ≤ s0 → s0 ≤ 2.8 → 2 ≤ s → s ≤ s0 + 0.2 →
      hS (s - 1) ≤ exp (s0 - 2) * hS s := by
  intro h
  exact (not_le.mpr bjs_lemma9_counterexample)
    (h 2 (11 / 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- A conservative corrected first branch uses the right interval endpoint.
Auxiliary repair of BJS p. 8 display 22, from the exact shift identity. -/
theorem hS_shift_le_endpoint {s0 s : ℝ} (hs0 : 2 ≤ s0) (ht0 : s0 ≤ 2.8)
    (hs : 2 ≤ s) (ht : s ≤ s0 + 0.2) :
    hS (s - 1) ≤ exp (s0 + 0.2 - 2) * hS s := by
  rw [hS_shift_eq hs (by linarith)]
  exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith)) (hS_pos (by linarith)).le

/-- The source low-range inequality holds without an approximation.
BJS p. 8 display 23. -/
theorem three_div_mul_hS_two_le {s : ℝ} (hs : 1 ≤ s) (ht : s ≤ 3) :
    3 / s * hS 2 ≤ 3 * hS s := by
  have hspos : 0 < s := by linarith
  by_cases h2 : s ≤ 2
  · simp only [hS, if_pos h2, show (2 : ℝ) ≤ 2 by norm_num, ↓reduceIte]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hspos).mpr (by linarith)) (exp_pos _).le
  · simp only [hS, if_neg h2, if_pos ht, show (2 : ℝ) ≤ 2 by norm_num, ↓reduceIte]
    have he : exp (s - 2) ≤ s := by
      have hc := convexOn_exp.2 (show (0 : ℝ) ∈ Set.univ by trivial)
        (show (1 : ℝ) ∈ Set.univ by trivial)
        (show 0 ≤ 3 - s by linarith) (show 0 ≤ s - 2 by linarith)
        (show 3 - s + (s - 2) = 1 by ring)
      norm_num at hc
      have he1 : exp (1 : ℝ) ≤ 3 := by
        have := exp_one_lt_d9
        norm_num at this
        linarith
      nlinarith
    have heq : exp (-2 : ℝ) = exp (s - 2) * exp (-s) := by rw [← exp_add]; congr 1 <;> ring
    rw [heq]
    have := mul_le_mul_of_nonneg_right he (exp_pos (-s)).le
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hspos).2
    nlinarith

/-- The global shift bound used in the older proof remains valid.
BJS v2 p. 7 before Lemma 9 and current p. 8 Lemma 9 display 22. -/
theorem hS_shift_le_global {s : ℝ} (hs : 2 ≤ s) :
    hS (s - 1) ≤ (4 * exp 1 / 3) * hS s := by
  by_cases h3 : s ≤ 3
  · rw [hS_shift_eq hs h3]
    have he : exp (s - 2) ≤ 4 * exp 1 / 3 := by
      have hh : exp (s - 2) ≤ exp 1 := exp_le_exp.mpr (by linarith)
      nlinarith [exp_pos (1 : ℝ)]
    exact mul_le_mul_of_nonneg_right he (hS_pos (by linarith)).le
  · have hs0 : 0 < s := by linarith
    have hs1 : 0 < s - 1 := by linarith
    have hss : hS s = 3 / s * exp (-s) := by
      rw [hS, if_neg (by linarith), if_neg h3]
    have heq : exp (-(s - 1)) = exp 1 * exp (-s) := by
      rw [← exp_add]
      congr 1
      ring
    rw [hss]
    by_cases h4 : s ≤ 4
    · have hh : hS (s - 1) = exp (-(s - 1)) := by
        rw [hS, if_neg (by linarith), if_pos (by linarith)]
      rw [hh, heq]
      have hc : (1 : ℝ) ≤ 4 / s := (le_div_iff₀ hs0).2 (by linarith)
      calc
        _ = 1 * (exp 1 * exp (-s)) := by ring
        _ ≤ (4 / s) * (exp 1 * exp (-s)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by ring
    · have hh : hS (s - 1) = 3 / (s - 1) * exp (-(s - 1)) := by
        rw [hS, if_neg (by linarith), if_neg (by linarith)]
      rw [hh, heq]
      have hc : 3 / (s - 1) ≤ 4 / s :=
        (div_le_div_iff₀ hs1 hs0).2 (by linarith)
      calc
        _ = (3 / (s - 1)) * (exp 1 * exp (-s)) := by ring
        _ ≤ (4 / s) * (exp 1 * exp (-s)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by ring

#print axioms hS_shift_le_global
#print axioms hS_pos
#print axioms hS_shift_eq
#print axioms bjs_lemma9_counterexample
#print axioms not_bjs_lemma9_first_branch
#print axioms hS_shift_le_endpoint
#print axioms three_div_mul_hS_two_le

end
end LeanLab.BS2022GRH.Envelope327
