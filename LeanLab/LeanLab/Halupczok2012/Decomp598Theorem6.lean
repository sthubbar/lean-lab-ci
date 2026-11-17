import LeanLab.Halupczok2012.Decomp532a
import LeanLab.Halupczok2012.Decomp598Pointwise
import LeanLab.Halupczok2012.Decomp598Lemma21
import LeanLab.Halupczok2012.U1439Thm2Reduction

/-!
Halupczok journal pages 338 to 340, display 2.4 and Theorem 3.1.
https://doi.org/10.5802/jtnb.839
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp598Theorem6

open Finset
open scoped Classical

/-- LEAF: Journal page 338, Theorem 2.2, display 2.4.
This is Halupczok's adapted first moment, with unrestricted p3.
Kawada 1993 Theorem 2 alone covers only the equal endpoint case. -/
theorem kawada_thm22_display24 :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ C Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
        |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y| ≤
          C * Y ^ 2 * Real.log Y ^ (-A) := by
  sorry

/-- The nonnegative weighted Cauchy Schwarz step on journal page 340.
A pointwise bound converts the second moment to the first moment. -/
theorem filtered_first_moment_cauchy {ι κ : Type*} (W : Finset ι) (U : Finset κ)
    (p : κ → ι → Prop) [∀ q n, Decidable (p q n)] (w : ι → ℝ) (D M : ℝ)
    (hw : ∀ n ∈ W, 0 ≤ w n) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hpoint : ∀ n ∈ W, w n ≤ D)
    (hmoment : ∑ n ∈ W, ((U.filter (fun q => p q n)).card : ℝ) ^ 2 ≤ M) :
    (∑ q ∈ U, ∑ n ∈ W.filter (p q), w n) ^ 2 ≤
      D * M * ∑ n ∈ W, w n := by
  have hexchange : ∑ q ∈ U, ∑ n ∈ W.filter (p q), w n =
      ∑ n ∈ W, w n * ((U.filter (fun q => p q n)).card : ℝ) := by
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    rw [card_filter]
    push_cast
    rw [mul_sum]
    apply sum_congr rfl
    intro q _
    split_ifs <;> simp
  rw [hexchange]
  have hsecond : ∑ n ∈ W, w n ^ 2 ≤ D * ∑ n ∈ W, w n := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    simpa [sq] using mul_le_mul_of_nonneg_right (hpoint n hn) (hw n hn)
  have hsum0 : 0 ≤ ∑ n ∈ W, w n := sum_nonneg hw
  calc
    _ ≤ (∑ n ∈ W, w n ^ 2) *
        ∑ n ∈ W, ((U.filter (fun q => p q n)).card : ℝ) ^ 2 :=
      sum_mul_sq_le_sq_mul_sq W _ _
    _ ≤ (D * ∑ n ∈ W, w n) * M :=
      mul_le_mul hsecond hmoment (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- The square of the sealed Theorem 6 left side after the page 340 Cauchy Schwarz step.
The first moment and the overlap moment remain explicit inputs. -/
theorem thm6_squared_of_moments (X1 X2 Y Q1 Q2 D M E : ℝ) (a1 a2 : ℤ)
    (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hpoint : ∀ k ∈ kRange X1 Y,
      (∑ q2 ∈ Icc 1 ⌊Q2⌋₊,
        |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y|) ≤ D)
    (hmoment : ∑ k ∈ kRange X1 Y,
      (((Icc 1 ⌊Q1⌋₊).filter (fun q : ℕ => ((2 * k : ℕ) : ℤ) ≡ a1 [ZMOD q])).card : ℝ) ^ 2 ≤ M)
    (hfirst : ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
      |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y| ≤ E) :
    thm6LHS X1 X2 Y Q1 Q2 a1 a2 ^ 2 ≤ D * M * E := by
  have h := filtered_first_moment_cauchy (kRange X1 Y) (Icc 1 ⌊Q1⌋₊)
    (fun q k : ℕ => ((2 * k : ℕ) : ℤ) ≡ a1 [ZMOD q])
    (fun k => ∑ q2 ∈ Icc 1 ⌊Q2⌋₊,
      |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y|)
    D M (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hD hM hpoint hmoment
  have hf : (∑ k ∈ kRange X1 Y, ∑ q2 ∈ Icc 1 ⌊Q2⌋₊,
      |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y|) ≤ E := by
    rw [sum_comm]
    exact hfirst
  exact h.trans (mul_le_mul_of_nonneg_left hf (mul_nonneg hD hM))

/-- Journal page 340, the pointwise step with an elementary log fourth power loss.
The larger logarithmic loss is absorbed by display 2.4 at exponent 2A plus 9. -/
theorem inner_error_pointwise :
    ∀ ε : ℝ, 0 < ε → ∃ BP : ℝ, 0 < BP ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 →
    ∀ a2 : ℤ, ∃ D Y0 : ℝ, 0 < D ∧
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-BP) →
      ∀ k ∈ kRange X1 Y,
        (∑ q2 ∈ Icc 1 ⌊Q2⌋₊,
          |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y|) ≤
          D * Y * Real.log Y ^ 4 := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro c1 c3 hc1 hc3 a2
  let K := (1 / c1) ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨D, hD, hb⟩ := Decomp598Pointwise.inner_error_polylog K c3 hK hc3
  refine ⟨D, Real.exp 1, hD, ?_⟩
  intro X1 X2 Y Q2 hY hlow hYX1 hYX2 hX2 hQ21 hQ2 k hk
  have hY1 : 1 ≤ Y := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hY
  have hY0 : 0 ≤ Y := by linarith
  have hX20 : 0 ≤ X2 := hY0.trans hYX2
  have hL1 : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hY
  have hXp : X2 ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (hY1.trans hYX2) (by norm_num)
  have hLp : Real.log Y ^ (-(1 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hQY : (⌊Q2⌋₊ : ℝ) ≤ c3 * Y := by
    calc
      _ ≤ Q2 := Nat.floor_le (by linarith)
      _ ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-1 : ℝ) := hQ2
      _ ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) :=
        mul_le_of_le_one_right (by positivity) hLp
      _ ≤ c3 * Y := mul_le_of_le_one_right (by positivity) hXp
  have hXsq : X1 ≤ K * Y ^ 2 := by
    have hh := le_sq_of_rpow hc1 (hY1.trans hYX1)
      (by linarith : (1 / 2 : ℝ) ≤ 2 / 3 + ε) hlow
    convert hh using 1 <;> dsimp [K] <;> ring
  have hN : 1 ≤ ⌊Q2⌋₊ := Nat.le_floor (by simpa using hQ21)
  exact hb X1 X2 Y ⌊Q2⌋₊ a2 hY hYX1 hXsq hN hQY k hk

/-- The logarithmic cancellation in the final line of the page 340 proof.
The first moment is used at exponent 2A plus 9. -/
theorem log_cancel {L A : ℝ} (hL : 0 < L) :
    L ^ 4 * L ^ 5 * L ^ (-(2 * A + 9)) = (L ^ (-A)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hL,
    ← Real.rpow_add hL, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  congr 1
  ring

/-- The sealed Theorem6 conclusion from the three explicit page 340 inputs.
This finite implication adds no analytic assumption to those inputs. -/
theorem thm6_of_three_bounds (A X1 X2 Y Q1 Q2 D M E : ℝ) (a1 a2 : ℤ)
    (hY : 0 ≤ Y) (hL : 0 < Real.log Y) (hD : 0 ≤ D) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hpoint : ∀ k ∈ kRange X1 Y,
      (∑ q2 ∈ Icc 1 ⌊Q2⌋₊,
        |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y|) ≤
          D * Y * Real.log Y ^ 4)
    (hmoment : ∑ k ∈ kRange X1 Y,
      (((Icc 1 ⌊Q1⌋₊).filter (fun q : ℕ => ((2 * k : ℕ) : ℤ) ≡ a1 [ZMOD q])).card : ℝ) ^ 2 ≤
        M * Y * Real.log Y ^ 5)
    (hfirst : ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
      |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y| ≤
        E * Y ^ 2 * Real.log Y ^ (-(2 * A + 9))) :
    thm6LHS X1 X2 Y Q1 Q2 a1 a2 ≤
      Real.sqrt (D * M * E) * Y ^ 2 * Real.log Y ^ (-A) := by
  have hb := thm6_squared_of_moments X1 X2 Y Q1 Q2
    (D * Y * Real.log Y ^ 4) (M * Y * Real.log Y ^ 5)
    (E * Y ^ 2 * Real.log Y ^ (-(2 * A + 9))) a1 a2
    (by positivity) (by positivity) hpoint hmoment hfirst
  have heq : (D * Y * Real.log Y ^ 4) * (M * Y * Real.log Y ^ 5) *
      (E * Y ^ 2 * Real.log Y ^ (-(2 * A + 9))) =
      (Real.sqrt (D * M * E) * Y ^ 2 * Real.log Y ^ (-A)) ^ 2 := by
    calc
      _ = (D * M * E) * (Y ^ 2) ^ 2 *
          (Real.log Y ^ 4 * Real.log Y ^ 5 * Real.log Y ^ (-(2 * A + 9))) := by ring
      _ = _ := by
        rw [log_cancel hL, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  rw [heq] at hb
  exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (by positivity) hb

/-- The exact sealed Theorem6 statement from the two page 340 error inputs
and the full even overlap form derived directly from lemma21_eventual.
This implication is CONDITIONAL ON the three explicitly supplied bounds. -/
theorem theorem6_of_inputs
    (h24 :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ C Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
        |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y| ≤
          C * Y ^ 2 * Real.log Y ^ (-A))
    (hpoint :
    ∀ ε : ℝ, 0 < ε → ∃ BP : ℝ, 0 < BP ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 →
    ∀ a2 : ℤ, ∃ D Y0 : ℝ, 0 < D ∧
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-BP) →
      ∀ k ∈ kRange X1 Y,
        (∑ q2 ∈ Icc 1 ⌊Q2⌋₊,
          |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y|) ≤
          D * Y * Real.log Y ^ 4)
    (hmoment : ∀ c K : ℝ, 0 < c → 0 < K → ∀ a : ℤ,
    ∃ C Y0 : ℝ, 0 < C ∧ ∀ X Y Q : ℝ,
      Y0 ≤ Y → 1 ≤ Y → Y ≤ X → X ≤ K * Y ^ 2 → (a : ℝ) ≤ X →
      1 ≤ Q → Q ≤ c * Y ^ (3 / 2 : ℝ) * X ^ (-(1 / 2) : ℝ) →
      ∑ k ∈ kRange X Y,
        (((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => ((2 * k : ℕ) : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 ≤
          C * Y * Real.log Y ^ 5) : Theorem6 := by
  intro A ε hA hε
  obtain ⟨B24, hB24, h24b⟩ := h24 (2 * A + 9) ε (by linarith) hε
  obtain ⟨BP, hBP, hpointb⟩ := hpoint ε hε
  let B := max B24 BP
  refine ⟨B, lt_of_lt_of_le hB24 (le_max_left _ _), ?_⟩
  intro c1 c2 c3 hc1 hc2 hc3 a1 a2
  let K := (1 / c1) ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨CM, YM, hCM, hMom⟩ := hmoment c2 K hc2 hK a1
  obtain ⟨D, YD, hD, hPt⟩ := hpointb c1 c3 hc1 hc3 a2
  obtain ⟨E, YE, hFirst⟩ := h24b c1 c3 hc1 hc3 a2
  refine ⟨Real.sqrt (D * CM * max E 0),
    max (Real.exp 1) (max YM (max YD YE)), ?_⟩
  intro X1 X2 Y Q1 Q2 hY hlow hYX1 hYX2 hX2 hQ11 hQ1 hQ21 hQ2 ha1
  have hYe : Real.exp 1 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hYe
  have hY0 : 0 ≤ Y := by linarith
  have hX20 : 0 ≤ X2 := hY0.trans hYX2
  have hL1 : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hYe
  have hL : 0 < Real.log Y := by linarith
  have hYM : YM ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYD : YD ≤ Y := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYE : YE ≤ Y := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hlevel (b : ℝ) (hb : b ≤ B) :
      Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-b) := by
    apply hQ2.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg hb)
  have hXsq : X1 ≤ K * Y ^ 2 := by
    have hh := le_sq_of_rpow hc1 (hY1.trans hYX1)
      (by linarith : (1 / 2 : ℝ) ≤ 2 / 3 + ε) hlow
    convert hh using 1 <;> dsimp [K] <;> ring
  have hM := hMom X1 Y Q1 hYM hY1 hYX1 hXsq ha1 hQ11 hQ1
  have hP := hPt X1 X2 Y Q2 hYD hlow hYX1 hYX2 hX2 hQ21
    (hlevel BP (le_max_right _ _))
  have hF := hFirst X1 X2 Y Q2 hYE hlow hYX1 hYX2 hX2 hQ21
    (hlevel B24 (le_max_left _ _))
  have hF' : ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
      |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y| ≤
        max E 0 * Y ^ 2 * Real.log Y ^ (-(2 * A + 9)) := by
    apply hF.trans
    gcongr
    exact le_max_left _ _
  exact thm6_of_three_bounds A X1 X2 Y Q1 Q2 D CM (max E 0) a1 a2
    hY0 hL hD.le hCM.le (le_max_right _ _) hP hM hF'

/-- Journal Theorem 3.1, with exactly the sealed Theorem6 conclusion.
This assembly is CONDITIONAL ON display 2.4 and the existing summatory Voronoi
leaf through lemma21_eventual and its dyadic extension. The pointwise input is elementary. -/
theorem theorem6 : Theorem6 :=
  theorem6_of_inputs kawada_thm22_display24 inner_error_pointwise
    Decomp598Lemma21.fixed_even_moment_via_lemma21

end LeanLab.Halupczok2012.Decomp598Theorem6
