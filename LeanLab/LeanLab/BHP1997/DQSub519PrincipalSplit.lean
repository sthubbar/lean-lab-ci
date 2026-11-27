/-
Burst 2026-11-24, session S4, burst-20261124, unit S4-21. SPLIT of the LEAF
`DQLowerExceptionalMeanSquare.Sub519.leaf_char_principal_z0` of `DQSub519Split.lean`.
Source: P0069 Baker Harman Pintz 1997, page 52, display 5.19, "the same argument yields (5.19)",
the argument being the proof of Lemma 29 on pages 43 and 44 for the principal character, with
`T2` replaced by `T0^2` and `z' = z0 = 1/T0^2`.

The cut follows the paper and the lab split `DQLeaf518SplitFeed1122` of the companion leaf
`leaf_char_nonprincipal`:
* `leaf_perron_window_z0`, HARD, CITED [30] Lemma 3.19, Titchmarsh 1986 book p. 70: the window
  sum is the Perron integral at height `Y` up to `O(Y^(1/100))`; the part `|t| ≤ T0` is the
  subtracted main term, so what is left is the Perron integral over `T0 ≤ |t| ≤ Y`;
* `leaf_harman_mean_z0`, HARD, CITED variant of [8] Lemma 2, Harman 1982 p. 339, with the kernel
  bound `|((1+z0)^s - 1)/s|^2 ≪ 1/(T0^4 + t^2)`: the mean square of that Perron integral;
* `leaf_window_integrable_z0`, MEDIUM, tacit in the paper: both integrands are interval
  integrable in `y`.
`perronT0_le_window` is PROVED, and `leaf_char_principal_z0_of_leaves` has exactly the type of
`leaf_char_principal_z0`, checked by the `example` at the end, and is PROVED from the three
leaves with `DQLeaf518SplitFeed1122.sq_norm_integral_le`.

No new definition. AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.DQSub519Split
import LeanLab.BHP1997.DQLeaf518SplitFeed1122Lemma29

namespace LeanLab.BHP1997.DQSub519Principal
open Classical Complex Decomp132 DecompC165b DecompC165d LowerShortC165 LowerShortMeanSquare
open LeanLab.BHP1997.DQLowerExceptionalMeanSquare
open scoped BigOperators
open MeasureTheory

/-- LEAF: page 43, first step of the proof of Lemma 29, rerun on page 52 for `χ0` at
`z0 = 1/T0^2`. Class HARD, CITED [30] Lemma 3.19, Titchmarsh 1986 book p. 70. P0069 Baker
Harman Pintz 1997: the window sum `Σ_{m ∈ J_y} b(m) χ0(m)` equals
`(1/2πi) ∫_{1/2-iY}^{1/2+iY} G(s, χ0) ((y+yz0)^s - y^s)/s ds + O(Y^ε)`, here with `ε = 1/100`.
Splitting `[-Y, Y]` at `±T0`, the window sum minus the `|t| ≤ T0` part minus the Perron
integral over `T0 ≤ |t| ≤ Y` is `O(Y^(1/100))`, so its mean square over `y ∈ [Y/2, 3Y]` is at
most a constant times `Y^(1+1/50)`. -/
theorem leaf_perron_window_z0 (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖((∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
          (b x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) -
          ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ∫ t in (-perronT0 x)..(perronT0 x),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) -
          ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ((∫ t in (-x ^ (11 / 20 + ε))..(-perronT0 x),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) +
             (∫ t in (perronT0 x)..(x ^ (11 / 20 + ε)),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)))‖ ^ 2 ≤
        K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
  sorry

/-- LEAF: page 44, the display after 5.4, rerun on page 52 for `χ0` at `z0 = 1/T0^2` with `T2`
replaced by `T0^2`. Class HARD, CITED variant of [8] Lemma 2, Harman 1982 p. 339, with the
kernel bound `|((1+z0)^(1/2+it) - 1)/(1/2+it)|^2 ≪ 1/(T0^4 + t^2)`, which holds since
`z0 = 1/T0^2`. P0069 Baker Harman Pintz 1997: the mean square over `y ∈ [Y/2, 3Y]` of the Perron
integral over `T0 ≤ |t| ≤ Y` is `≪ Y^2 ∫_{T0 ≤ |t| ≤ Y} |G(1/2+it, χ0)|^2 / (T0^4 + t^2) dt`;
the form without the factor `L` follows by Plancherel after `y = e^v`, see NOTE U-1744 in
`DQSub519Split`. -/
theorem leaf_harman_mean_z0 (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ((∫ t in (-x ^ (11 / 20 + ε))..(-perronT0 x),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) +
             (∫ t in (perronT0 x)..(x ^ (11 / 20 + ε)),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)))‖ ^ 2 ≤
        K * (x ^ (11 / 20 + ε)) ^ 2 *
          ((∫ t in (-x ^ (11 / 20 + ε))..(-perronT0 x),
              ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((perronT0 x ^ 2) ^ 2 + t ^ 2)) +
            (∫ t in (perronT0 x)..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((perronT0 x ^ 2) ^ 2 + t ^ 2))) := by
  sorry

/-- LEAF: pages 43 to 44 and 52, tacit in the paper, class MEDIUM. P0069 Baker Harman Pintz
1997: the squared Perron error and the squared Perron integral over `T0 ≤ |t| ≤ Y` are interval
integrable in `y` on `[Y/2, 3Y]`; the window sum is piecewise constant in `y` and the Perron
integrals are continuous in `y > 0`. -/
theorem leaf_window_integrable_z0 (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      IntervalIntegrable (fun y : ℝ =>
        ‖((∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
          (b x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) -
          ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ∫ t in (-perronT0 x)..(perronT0 x),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) -
          ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ((∫ t in (-x ^ (11 / 20 + ε))..(-perronT0 x),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) +
             (∫ t in (perronT0 x)..(x ^ (11 / 20 + ε)),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)))‖ ^ 2)
        MeasureTheory.volume (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
      IntervalIntegrable (fun y : ℝ =>
        ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ((∫ t in (-x ^ (11 / 20 + ε))..(-perronT0 x),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) +
             (∫ t in (perronT0 x)..(x ^ (11 / 20 + ε)),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)))‖ ^ 2)
        MeasureTheory.volume (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) := by
  sorry

/-- PROVED. `T0 ≤ Y` once `log x ≥ 729`: `T0 ≤ T0^4 ≤ x^(1/20) ≤ x^(11/20+ε)`. -/
theorem perronT0_le_window {ε x : ℝ} (hε : 0 < ε) (hx : Real.exp 729 ≤ x) :
    perronT0 x ≤ x ^ (11 / 20 + ε) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hL : 729 ≤ Real.log x := by
    rw [← Real.log_exp 729]; exact Real.log_le_log (Real.exp_pos _) hx
  have hT1 : 1 ≤ perronT0 x := Sub519.one_le_perronT0 hx1
  have hT4 := Sub519.perronT0_pow4_le hxpos hL
  have hTT : perronT0 x ≤ perronT0 x ^ 4 := by
    calc perronT0 x = perronT0 x ^ 1 := (pow_one _).symm
      _ ≤ perronT0 x ^ 4 := pow_le_pow_right₀ hT1 (by norm_num)
  have hxY : x ^ (1 / 20 : ℝ) ≤ x ^ (11 / 20 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  linarith

/-- PROVED from the three LEAFs above, CONDITIONAL ON them: exactly the statement of
`Sub519.leaf_char_principal_z0`. The Perron error and the Perron integral over
`T0 ≤ |t| ≤ Y` are combined by `∫ ‖f‖^2 ≤ 2 ∫ ‖f - g‖^2 + 2 ∫ ‖g‖^2`. -/
theorem leaf_char_principal_z0_of_leaves (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖(∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
          (b x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) -
          ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ∫ t in (-perronT0 x)..(perronT0 x),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        K * (x ^ (11 / 20 + ε)) ^ 2 *
          ((∫ t in (-x ^ (11 / 20 + ε))..(-perronT0 x),
              ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((perronT0 x ^ 2) ^ 2 + t ^ 2)) +
            (∫ t in (perronT0 x)..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((perronT0 x ^ 2) ^ 2 + t ^ 2))) +
        K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
  obtain ⟨K1, hK1, C1, hC1⟩ := leaf_perron_window_z0 b hε hb
  obtain ⟨K2, hK2, C2, hC2⟩ := leaf_harman_mean_z0 b hε hb
  obtain ⟨C3, hC3⟩ := leaf_window_integrable_z0 b hε hb
  refine ⟨2 * (K1 + K2), by positivity, max (max C1 C2) (max C3 (Real.exp 729)), ?_⟩
  intro x hx q hq1 hqQ
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : Real.exp 729 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx4
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hxpos _
  have hTY := perronT0_le_window hε hx4
  have hT0 : 0 ≤ perronT0 x := (Real.exp_pos _).le
  have hab : x ^ (11 / 20 + ε) / 2 ≤ 3 * x ^ (11 / 20 + ε) := by linarith
  obtain ⟨hi1, hi2⟩ := hC3 x hx3 q hq1 hqQ
  have e1 := hC1 x hx1 q hq1 hqQ
  have e2 := hC2 x hx2 q hq1 hqQ
  refine (DQLeaf518SplitFeed1122.sq_norm_integral_le hab hi1 hi2).trans ?_
  have hG1 : 0 ≤ ∫ t in (-x ^ (11 / 20 + ε))..(-perronT0 x),
      ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
          (1 : DirichletCharacter ℂ q) (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        ((perronT0 x ^ 2) ^ 2 + t ^ 2) :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
  have hG2 : 0 ≤ ∫ t in (perronT0 x)..(x ^ (11 / 20 + ε)),
      ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
          (1 : DirichletCharacter ℂ q) (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        ((perronT0 x ^ 2) ^ 2 + t ^ 2) :=
    intervalIntegral.integral_nonneg hTY (fun t _ => by positivity)
  have hE : 0 ≤ x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by positivity
  have hYG : 0 ≤ (x ^ (11 / 20 + ε)) ^ 2 * ((∫ t in (-x ^ (11 / 20 + ε))..(-perronT0 x),
      ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
          (1 : DirichletCharacter ℂ q) (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        ((perronT0 x ^ 2) ^ 2 + t ^ 2)) +
      (∫ t in (perronT0 x)..(x ^ (11 / 20 + ε)),
      ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
          (1 : DirichletCharacter ℂ q) (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        ((perronT0 x ^ 2) ^ 2 + t ^ 2))) := by positivity
  nlinarith [mul_nonneg hK1 hYG, mul_nonneg hK2 hE]

/-- PROVED. The assembly has the exact type of the LEAF `Sub519.leaf_char_principal_z0`. -/
example : type_of% @Sub519.leaf_char_principal_z0 := @leaf_char_principal_z0_of_leaves

end LeanLab.BHP1997.DQSub519Principal

#print axioms LeanLab.BHP1997.DQSub519Principal.perronT0_le_window
#print axioms LeanLab.BHP1997.DQSub519Principal.leaf_char_principal_z0_of_leaves
