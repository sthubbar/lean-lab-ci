/- AI wrote the Lean code for CODEX task164.
Journal Lemma 3, pp. 1215 and 1216. Goldbach is open. -/
import LeanLab.BS2022GRH.ChenThresholdGRH
namespace LeanLab.BS2022GRH.DecompC164a
open Real Finset Classical ChenThresholdGRH
noncomputable section
/-- The grouped logarithmic numerator in qG, p. 1216. -/
def firstGroup (t : ℝ) : ℝ := (1.314 * t + 0.092 * log t + 60.883) / exp (t / 4)
/-- The mixed logarithmic term in qG, p. 1216. -/
def secondGroup (t : ℝ) : ℝ := 8.250 * log t / (exp (t / 4) * t)
/-- Pair the negative term with the last positive term, p. 1216. -/
def thirdGroup (t : ℝ) : ℝ :=
  939.260 / (exp (t / 4) * t) - 237.934 / (exp (t / 2) * t)
/-- LEAF. The grouped logarithmic numerator decreases for t at least 2.
Journal p. 1216, coefficient domination in Lemma 3. -/
theorem firstGroup_antitone : AntitoneOn firstGroup (Set.Ici 2) := by
  have hd (t : ℝ) (ht : 2 ≤ t) : HasDerivAt firstGroup
      (((1.314 + 0.092 / t) * exp (t / 4) -
        (1.314 * t + 0.092 * log t + 60.883) * (exp (t / 4) / 4)) /
          exp (t / 4) ^ 2) t := by
    unfold firstGroup
    convert (((((hasDerivAt_id t).const_mul 1.314).add
      ((hasDerivAt_log (by linarith : t ≠ 0)).const_mul 0.092)).add_const 60.883).div
      (((hasDerivAt_id t).div_const 4).exp) (exp_ne_zero _)) using 1
    · ext x <;> dsimp <;> ring
    · dsimp; ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (by
      have h : 2 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
      exact h.le)).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht2 : 2 ≤ t := by
    have h : 2 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    exact h.le
  rw [(hd t ht2).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hlog : 0 ≤ log t := log_nonneg (by linarith)
  have hdiv : 0.092 / t ≤ (0.046 : ℝ) := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hneg : 1.314 + 0.092 / t - (1.314 * t + 0.092 * log t + 60.883) / 4 ≤ 0 := by
    nlinarith
  have hmul := mul_nonpos_of_nonpos_of_nonneg hneg (exp_pos (t / 4)).le
  nlinarith
/-- LEAF. The mixed logarithmic term decreases for t at least 2.
Journal p. 1216, coefficient domination in Lemma 3. -/
theorem secondGroup_antitone : AntitoneOn secondGroup (Set.Ici 2) := by
  have hd (t : ℝ) (ht : 2 ≤ t) : HasDerivAt secondGroup
      ((8.250 / t * (exp (t / 4) * t) - 8.250 * log t *
        (exp (t / 4) / 4 * t + exp (t / 4))) / (exp (t / 4) * t) ^ 2) t := by
    unfold secondGroup
    convert (((hasDerivAt_log (by linarith : t ≠ 0)).const_mul 8.250).div
      ((((hasDerivAt_id t).div_const 4).exp).mul (hasDerivAt_id t))
      (by change exp (t / 4) * t ≠ 0; exact mul_ne_zero (exp_ne_zero _) (by linarith))) using 1
    · ext x <;> dsimp <;> ring
    · dsimp; ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (by
      have h : 2 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
      exact h.le)).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht2 : 2 ≤ t := by
    have h : 2 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    exact h.le
  rw [(hd t ht2).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hlog : (2 / 3 : ℝ) ≤ log t := by
    have := log_le_log (by norm_num : (0 : ℝ) < 2) ht2
    linarith [log_two_gt_d9]
  have hprod : 1 ≤ log t * (t / 4 + 1) := by nlinarith
  have hmul := mul_nonpos_of_nonpos_of_nonneg (by linarith : 1 - log t * (t / 4 + 1) ≤ 0)
    (exp_pos (t / 4)).le
  have hc : 8.250 / t * (exp (t / 4) * t) = 8.250 * exp (t / 4) := by
    field_simp
  rw [hc]
  nlinarith
/-- LEAF. The paired final terms decrease for t at least 2.
Journal p. 1216, coefficient domination in Lemma 3.
Keep the negative summand paired with the larger positive summand. -/
theorem thirdGroup_antitone : AntitoneOn thirdGroup (Set.Ici 2) := by
  have hd (t : ℝ) (ht : 2 ≤ t) : HasDerivAt thirdGroup
      ((-939.260 * (t / 4 + 1) * exp (t / 4) + 237.934 * (t / 2 + 1)) /
        (exp (t / 4) ^ 2 * t ^ 2)) t := by
    have he : exp (t / 2) = exp (t / 4) ^ 2 := by
      rw [pow_two, ← exp_add]; congr 1; ring
    have ht0 : t ≠ 0 := by linarith
    have he0 := exp_ne_zero (t / 4)
    unfold thirdGroup
    convert (((hasDerivAt_const t (939.260 : ℝ)).div
      ((((hasDerivAt_id t).div_const 4).exp).mul (hasDerivAt_id t)) (by change exp (t / 4) * t ≠ 0; exact mul_ne_zero (exp_ne_zero _) ht0)).sub
      ((hasDerivAt_const t (237.934 : ℝ)).div
      ((((hasDerivAt_id t).div_const 2).exp).mul (hasDerivAt_id t)) (by change exp (t / 2) * t ≠ 0; exact mul_ne_zero (exp_ne_zero _) ht0))) using 1
    · rfl
    · dsimp
      rw [he]
      field_simp
      <;> ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (by
      have h : 2 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
      exact h.le)).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht2 : 2 ≤ t := by
    have h : 2 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    exact h.le
  rw [(hd t ht2).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have he : 1 ≤ exp (t / 4) := one_le_exp (by linarith)
  have hm := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ t / 4 + 1)
  nlinarith
/-- Exponential coordinates for the printed coefficient, p. 1216. -/
theorem qG_groups (X : ℝ) (hX : 0 < X) :
    qG X = 0.165 + 12.683 / log X + 254.980 / log X ^ 2 +
      2607.854 / log X ^ 3 + 11605.056 / log X ^ 4 +
      firstGroup (log X) + secondGroup (log X) + thirdGroup (log X) := by
  have h4 : X ^ (1 / 4 : ℝ) = exp (log X / 4) := by
    rw [rpow_def_of_pos hX]; congr 1; ring
  have h2 : √X = exp (log X / 2) := by
    rw [sqrt_eq_rpow, rpow_def_of_pos hX]; congr 1; ring
  unfold qG firstGroup secondGroup thirdGroup
  rw [h4, h2]
  ring
/-- Exact domination of qG used by the endpoint specialization. -/
theorem qG_antitone (X N : ℝ) (hX : 9 ≤ X) (hXN : X ≤ N) : qG N ≤ qG X := by
  have hX0 : 0 < X := by linarith
  have hN0 : 0 < N := by linarith
  have hlog9 : (2 : ℝ) ≤ log 9 := by
    rw [le_log_iff_exp_le (by norm_num)]
    have h : exp (2 : ℝ) = exp 1 * exp 1 := by rw [← exp_add]; norm_num
    rw [h]
    nlinarith [exp_one_lt_d9, exp_pos (1 : ℝ)]
  have hx : 2 ≤ log X := hlog9.trans (log_le_log (by norm_num) hX)
  have hn : 2 ≤ log N := hx.trans (log_le_log hX0 hXN)
  have hlog := log_le_log hX0 hXN
  rw [qG_groups X hX0, qG_groups N hN0]
  have h1 : 12.683 / log N ≤ 12.683 / log X := by gcongr
  have h2 : 254.980 / log N ^ 2 ≤ 254.980 / log X ^ 2 := by gcongr
  have h3 : 2607.854 / log N ^ 3 ≤ 2607.854 / log X ^ 3 := by gcongr
  have h4 : 11605.056 / log N ^ 4 ≤ 11605.056 / log X ^ 4 := by gcongr
  linarith [firstGroup_antitone hx hn hlog, secondGroup_antitone hx hn hlog,
    thirdGroup_antitone hx hn hlog]
/-- LEAF. Lemma 3 p. 1216, explicit progression estimate at the running endpoint.
CITED source is Ernvall-Hytonen and Palojarvi 2022 Theorem 1.
The source specialization and the sealed small endpoint range both remain OPEN. -/
theorem progression_at_endpoint (hG : GRH) (d a : ℕ) (N : ℝ)
    (hd : 3 ≤ d) (hdN : (d : ℝ) ≤ √N) (ha : Nat.Coprime a d) :
    |((((range (⌊N⌋₊ + 1)).filter (fun p => p.Prime ∧ p % d = a % d)).card : ℕ) : ℝ)
        - liPV N / (d.totient : ℝ)| ≤ qG N * √N * log N := by
  sorry

/-- Exact sealed Lemma3J. The endpoint input remains CITED and OPEN. -/
theorem lemma3J : Lemma3J := by
  intro hG d a X₂ N hd hdX hXN ha
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hspos : 0 < √X₂ := by linarith
  have hX0 : 0 ≤ X₂ := (sqrt_pos.mp hspos).le
  have hX9 : 9 ≤ X₂ := by nlinarith [sq_sqrt hX0]
  have hraw := progression_at_endpoint hG d a N hd
    (hdX.trans (sqrt_le_sqrt hXN)) ha
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (qG_antitone X₂ N hX9 hXN) (sqrt_nonneg N))
    (log_nonneg (by linarith)))
end
end LeanLab.BS2022GRH.DecompC164a
#print axioms LeanLab.BS2022GRH.DecompC164a.firstGroup_antitone
#print axioms LeanLab.BS2022GRH.DecompC164a.secondGroup_antitone
#print axioms LeanLab.BS2022GRH.DecompC164a.thirdGroup_antitone
#print axioms LeanLab.BS2022GRH.DecompC164a.qG_groups
#print axioms LeanLab.BS2022GRH.DecompC164a.qG_antitone
#print axioms LeanLab.BS2022GRH.DecompC164a.lemma3J
