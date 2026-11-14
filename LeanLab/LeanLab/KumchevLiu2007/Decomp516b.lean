/-
A downstream clean supply for the singular series lower bound.
Kumchev and Liu, arXiv 0801.0130, page 14 displays 48 and 49.
The mean square proof imports Decomp129, so this supply cannot be imported
by Decomp129 or Decomp516a without a cycle.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Supply129r

namespace LeanLab.KumchevLiu2007.Task516b

open Real Complex LeanLab.KumchevLiu2007 Task129
open scoped BigOperators Topology

/-- Page 14 displays 48 and 49. The exact singular series lower bound leaf,
proved from the clean two variable mean square supply by Chebyshev counting. -/
theorem eq48_49_series_lower (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ c C X0 : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          ‖series2 n (Real.log X ^ B)‖ < c / Real.log (Real.log X ^ B)) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨c, Q0, hc, hQ0, hp⟩ := Task129a.P2_lower_explicit
  refine ⟨A + 3, by linarith, ?_⟩
  intro B hB ε hε
  have hBpos : 0 < B := by linarith
  obtain ⟨C, x0, hC, hx0, hm⟩ := Supply129r.lemma38_two_local_supply
    (max 2 (A + 2)) (1 / 4) (le_max_left _ _) (by norm_num)
  obtain ⟨M, hM1, hMP⟩ := pow_le_sieveLevel B (1 / 2) hBpos (by norm_num)
  refine ⟨c / 2, 8 * C / c ^ 2,
    max x0 (Real.exp (max M (max 2 Q0))), by positivity, by positivity,
    hx0.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX
  have hxx0 : x0 ≤ X := (le_max_left _ _).trans hX
  have hX2 : 2 ≤ X := hx0.trans hxx0
  have hXpos : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hLM : max M (max 2 Q0) ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hX)
    rwa [Real.log_exp] at h
  set L := Real.log X with hL
  have hL2 : 2 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLM)
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hB1 : 1 ≤ B := by linarith
  set P := L ^ B with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos hLpos B
  have hLP : L ≤ P := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1 hB1
    simpa using h
  have hPQ0 : Q0 ≤ P := ((le_max_right _ _).trans ((le_max_right _ _).trans hLM)).trans hLP
  have hP2 : 2 ≤ P := hL2.trans hLP
  have hlogPpos : 0 < Real.log P := Real.log_pos (by linarith)
  have hcut : P ≤ Real.exp (L ^ (1 - (1 / 4 : ℝ))) := by
    exact (hMP X ((le_max_left _ _).trans hLM)).trans
      (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
  have hlogPL : Real.log P ≤ L := by
    have h := Real.log_le_log hPpos (hMP X ((le_max_left _ _).trans hLM))
    rw [log_sieveLevel] at h
    exact h.trans (by
      have h := Real.rpow_le_rpow_of_exponent_le hL1
        (show (1 : ℝ) - 1 / 2 / 2 ≤ 1 by norm_num)
      simpa using h)
  have hHpos : 0 < H := (Real.rpow_pos_of_pos hXpos _).trans_le hH
  have hlow : X ^ (1 / 4 : ℝ) ≤ H :=
    (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)).trans hH
  have hsum := hm X H P P hxx0 hlow hHX hPpos le_rfl hcut
  have hprod := hp P hPQ0
  have key : ∀ n : ℕ, X < (n : ℝ) →
      (InH2 n ∧ ‖series2 n P‖ < (c / 2) / Real.log P) →
      (c / 2 * L⁻¹) ^ 2 < ‖series2 n P - partialProduct2 n P‖ ^ 2 := by
    rintro n _ ⟨hn, hs⟩
    have hpn := hprod n hn
    have htri := norm_sub_norm_le (partialProduct2 n P) (series2 n P)
    have hd : c / 2 / Real.log P < ‖series2 n P - partialProduct2 n P‖ := by
      rw [norm_sub_rev]
      change c / Real.log P ≤ ‖partialProduct2 n P‖ at hpn
      have heq : c / Real.log P = 2 * (c / 2 / Real.log P) := by ring
      rw [heq] at hpn
      linarith only [hpn, htri, hs]
    have ht : c / 2 * L⁻¹ ≤ c / 2 / Real.log P := by
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by positivity) hlogPpos hlogPL
    exact (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mpr (ht.trans_lt hd)
  have hcheb := cnt_mul_le_sum (S := fun n => InH2 n ∧
      ‖series2 n P‖ < (c / 2) / Real.log P) (H := H)
    (fun n => ‖series2 n P - partialProduct2 n P‖ ^ 2) hXpos.le
    (fun n => by positivity) key
  have hcnt := hcheb.trans hsum
  have ht : 0 < (c / 2 * L⁻¹) ^ 2 := by positivity
  have hinv : ((c / 2 * L⁻¹) ^ 2)⁻¹ = 4 / c ^ 2 * L ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    field_simp
    norm_num
  have b1 : H / P * L * L ^ (2 : ℝ) ≤ H * L ^ (-A) := by
    have heq : H / P * L * L ^ (2 : ℝ) = H * L ^ (-B + 1 + 2) := by
      rw [Real.rpow_add hLpos, Real.rpow_add hLpos, Real.rpow_neg hLpos.le, Real.rpow_one]
      dsimp [P]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hHpos.le
  have b2 : H / L ^ (max 2 (A + 2)) * L ^ (2 : ℝ) ≤ H * L ^ (-A) := by
    have heq : H / L ^ (max 2 (A + 2)) * L ^ (2 : ℝ) =
        H * L ^ (-max 2 (A + 2) + 2) := by
      rw [Real.rpow_add hLpos, Real.rpow_neg hLpos.le]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [le_max_right 2 (A + 2)])) hHpos.le
  have hfin : (cntIoc (fun n => InH2 n ∧ ‖series2 n P‖ < (c / 2) / Real.log P) X H : ℝ) ≤
      C * (H / P * L + H / L ^ (max 2 (A + 2))) * (4 / c ^ 2 * L ^ (2 : ℝ)) := by
    rw [← hinv, ← div_eq_mul_inv, le_div_iff₀ ht]
    exact hcnt
  calc _ ≤ C * (H / P * L + H / L ^ (max 2 (A + 2))) * (4 / c ^ 2 * L ^ (2 : ℝ)) := hfin
    _ = 4 * C / c ^ 2 * (H / P * L * L ^ (2 : ℝ) +
        H / L ^ (max 2 (A + 2)) * L ^ (2 : ℝ)) := by ring
    _ ≤ 4 * C / c ^ 2 * (H * L ^ (-A) + H * L ^ (-A)) :=
      mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by positivity)
    _ = 8 * C / c ^ 2 * H / L ^ A := by rw [Real.rpow_neg hLpos.le]; ring

/-- Page 16 display 55 with the exact sealed circle_input statement.
CONDITIONAL ON the weighted Proposition 1 estimate and the explicitly
unwritten epsilon residue. The singular series estimate is supplied by the
clean theorem above, without importing it into the upstream leaf file. -/
theorem circle_input (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ *
            (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) <
          ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
            main2 X (windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  exact Task129.circle_input_of_estimates A hA (fun X _ => X)
    (by intro X ε hX hε; exact le_rfl)
    (Task129.eq53_full_range (A + 5) (by linarith)) (eq48_49_series_lower A hA)

/-- Page 16 displays 53 to 55 on the printed H range.
CONDITIONAL ON the weighted Proposition 1 input only. The clean singular
series lower bound supplies displays 48 and 49. The unwritten epsilon leaf
is not used by this written range statement. -/
theorem circle_input_written (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ *
            (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) <
          ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
            main2 X (windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  exact Task129.circle_input_of_estimates A hA (fun X ε => X ^ (1 - ε))
    (by
      intro X ε hX hε
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X)
          (by linarith : 1 - ε ≤ 1))
    (Task129.eq53_prop1 (A + 5) (by linarith)) (eq48_49_series_lower A hA)

end LeanLab.KumchevLiu2007.Task516b
