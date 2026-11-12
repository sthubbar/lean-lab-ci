/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 52. The elementary skeleton of display 1.9
for the lower short weight b0.

Page 52 ends with "Now (1.9) follows from (5.18), (5.23) and (5.22)". Written out, for every
character `χ` and every `y`,

  `S - δχ M = (S - δχ W(y, z)) + δχ (W(y, z) - z H(y)) + δχ (z H(y) - M)`,

where `S` is the window sum of `b0(m) χ(m)` and `M` the main term. Then
`|a + b + c|^2 ≤ 3 (|a|^2 + |b|^2 + |c|^2)`, integrate over `y` in `[Y/2, 3Y]` and sum over the
characters outside `E_q`. The first term is 5.18, the second 5.23 and the third 5.22; the last
two carry the factor `δχ`, so only the principal character contributes to them.

This file proves that step, with the functions `W` and `H` of Section 4 left as arbitrary
parameters, since the lab has not defined them. It adds no sorry. The OPEN leaf
`LowerShortC165.lower_exceptional_mean_square` is not replaced: the three hypotheses of
`lower_exceptional_mean_square_of_518_522_523` are 5.18, 5.22 and 5.23 for some `W` and `H`,
and stating them as leaves with `W` and `H` existentially quantified would be a restatement of
the leaf, not a split. See the burst notes, QUESTION 3, on the truncation of the window to J.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.LowerShortC165

namespace LeanLab.BHP1997.LowerShortMeanSquare
open Classical Complex Decomp132 DecompC165b DecompC165d LowerShortC165
open scoped BigOperators
open MeasureTheory

/-- P0069 Baker Harman Pintz 1997, page 52, the last line, "(1.9) follows from (5.18), (5.23)
and (5.22)": the norm of a sum of three terms, squared, is at most three times the sum of the
squares. -/
theorem norm_add3_sq_le (a b c : ℂ) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h := norm_add₃_le (a := a) (b := b) (c := c)
  have h0 := norm_nonneg (a + b + c)
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hc := norm_nonneg c
  have hsq : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := by
    rw [sq, sq]; exact mul_le_mul h h h0 (by positivity)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]

/-- P0069 Baker Harman Pintz 1997, page 52, the decomposition behind "(1.9) follows from
(5.18), (5.23) and (5.22)", pointwise in `y`: with `S` the window sum of `b0 χ`, `W = W(y, z)`,
`Hz = z H(y)` and `M` the main term of 1.9,
`|S - δ M|^2 ≤ 3 (|S - δ W|^2 + |δ|^2 |W - z H|^2 + |δ|^2 |z H - M|^2)`. -/
theorem pointwise_split (S W Hz M δ : ℂ) :
    ‖S - δ * M‖ ^ 2 ≤
      3 * (‖S - δ * W‖ ^ 2 + ‖δ‖ ^ 2 * ‖W - Hz‖ ^ 2 + ‖δ‖ ^ 2 * ‖Hz - M‖ ^ 2) := by
  have hdec : S - δ * M = (S - δ * W) + δ * (W - Hz) + δ * (Hz - M) := by ring
  have h := norm_add3_sq_le (S - δ * W) (δ * (W - Hz)) (δ * (Hz - M))
  rw [norm_mul, norm_mul, mul_pow, mul_pow] at h
  rw [hdec]; exact h

/-- P0069 Baker Harman Pintz 1997, page 3, the definition of `δχ`, and page 52, 5.22 and 5.23:
the terms carrying `δχ` count only for the principal character, so their sum over any set of
characters is at most the principal term. -/
theorem sum_delta_sq_le {q : ℕ} (T : Finset (DirichletCharacter ℂ q)) {g : ℝ} (hg : 0 ≤ g) :
    ∑ χ ∈ T, ‖Thm2.delta χ‖ ^ 2 * g ≤ g := by
  have hterm : ∀ χ : DirichletCharacter ℂ q,
      ‖Thm2.delta χ‖ ^ 2 * g = if χ = 1 then g else 0 := by
    intro χ
    unfold Thm2.delta
    split_ifs <;> simp
  simp only [hterm]
  rw [Finset.sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact hg

/-- P0069 Baker Harman Pintz 1997, page 52, "(1.9) follows from (5.18), (5.23) and (5.22)",
integrated over `y` in `[a, b]` and summed over a set `T` of characters, the complement of the
exceptional set `E_q` in the application. The 5.18 term keeps the sum over `T`; the 5.22 and
5.23 terms, which carry `δχ`, are bounded by their principal term. The left side need not be
integrable: if it is not, its integral is zero. -/
theorem mean_square_three {q : ℕ} (T : Finset (DirichletCharacter ℂ q)) {a b : ℝ}
    (hab : a ≤ b) (S : DirichletCharacter ℂ q → ℝ → ℂ) (W Hz M : ℝ → ℂ)
    (hS : ∀ χ ∈ T, IntervalIntegrable (fun y => ‖S χ y - Thm2.delta χ * W y‖ ^ 2) volume a b)
    (hW : IntervalIntegrable (fun y => ‖W y - Hz y‖ ^ 2) volume a b)
    (hH : IntervalIntegrable (fun y => ‖Hz y - M y‖ ^ 2) volume a b) :
    ∑ χ ∈ T, ∫ y in a..b, ‖S χ y - Thm2.delta χ * M y‖ ^ 2 ≤
      3 * (∑ χ ∈ T, ∫ y in a..b, ‖S χ y - Thm2.delta χ * W y‖ ^ 2) +
        3 * (∫ y in a..b, ‖W y - Hz y‖ ^ 2) + 3 * (∫ y in a..b, ‖Hz y - M y‖ ^ 2) := by
  set IW := ∫ y in a..b, ‖W y - Hz y‖ ^ 2 with hIW
  set IH := ∫ y in a..b, ‖Hz y - M y‖ ^ 2 with hIH
  have hIW0 : 0 ≤ IW := intervalIntegral.integral_nonneg hab fun _ _ => by positivity
  have hIH0 : 0 ≤ IH := intervalIntegral.integral_nonneg hab fun _ _ => by positivity
  have key : ∀ χ ∈ T, ∫ y in a..b, ‖S χ y - Thm2.delta χ * M y‖ ^ 2 ≤
      3 * (∫ y in a..b, ‖S χ y - Thm2.delta χ * W y‖ ^ 2) +
        3 * (‖Thm2.delta χ‖ ^ 2 * IW) + 3 * (‖Thm2.delta χ‖ ^ 2 * IH) := by
    intro χ hχ
    set d := ‖Thm2.delta χ‖ ^ 2
    have hR : IntervalIntegrable (fun y => 3 * (‖S χ y - Thm2.delta χ * W y‖ ^ 2 +
        d * ‖W y - Hz y‖ ^ 2 + d * ‖Hz y - M y‖ ^ 2)) volume a b :=
      (((hS χ hχ).add (hW.const_mul d)).add (hH.const_mul d)).const_mul 3
    have hRint : ∫ y in a..b, 3 * (‖S χ y - Thm2.delta χ * W y‖ ^ 2 +
        d * ‖W y - Hz y‖ ^ 2 + d * ‖Hz y - M y‖ ^ 2) =
        3 * (∫ y in a..b, ‖S χ y - Thm2.delta χ * W y‖ ^ 2) + 3 * (d * IW) +
          3 * (d * IH) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((hS χ hχ).add (hW.const_mul d)) (hH.const_mul d),
        intervalIntegral.integral_add (hS χ hχ) (hW.const_mul d),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    rw [← hRint]
    by_cases hL : IntervalIntegrable (fun y => ‖S χ y - Thm2.delta χ * M y‖ ^ 2) volume a b
    · exact intervalIntegral.integral_mono_on hab hL hR fun y _ =>
        pointwise_split (S χ y) (W y) (Hz y) (M y) (Thm2.delta χ)
    · rw [intervalIntegral.integral_undef hL]
      exact intervalIntegral.integral_nonneg hab fun _ _ => by positivity
  calc _ ≤ ∑ χ ∈ T, (3 * (∫ y in a..b, ‖S χ y - Thm2.delta χ * W y‖ ^ 2) +
        3 * (‖Thm2.delta χ‖ ^ 2 * IW) + 3 * (‖Thm2.delta χ‖ ^ 2 * IH)) :=
        Finset.sum_le_sum key
    _ = 3 * (∑ χ ∈ T, ∫ y in a..b, ‖S χ y - Thm2.delta χ * W y‖ ^ 2) +
        3 * (∑ χ ∈ T, ‖Thm2.delta χ‖ ^ 2 * IW) + 3 * (∑ χ ∈ T, ‖Thm2.delta χ‖ ^ 2 * IH) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
    _ ≤ _ := by
        have h1 := sum_delta_sq_le T hIW0
        have h2 := sum_delta_sq_le T hIH0
        linarith

/-- P0069 Baker Harman Pintz 1997, page 3, display 1.9: the summand of 1.9 is the window sum of
`b0 χ` minus `δχ` times the window sum of the constant `v0 / L'`. -/
theorem window_sum_sub (ω : ℝ → ℝ) (ε x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : Finset ℕ) :
    ∑ m ∈ s, ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
        Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε))) =
      (∑ m ∈ s, (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q)) -
        Thm2.delta χ * ∑ m ∈ s, ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ) := by
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

/-- P0069 Baker Harman Pintz 1997, Section 5, page 52, "Now (1.9) follows from (5.18), (5.23)
and (5.22)", for b0 in the lab's form of 1.9, display 1.9 on page 3 with the window restricted
to J. CONDITIONAL on three hypotheses, for some functions `W(x, q, y, z)` and `H(x, q, y)`,
the `W` and `H` of pages 43 and 52 which the lab has not defined:
* `h518`, display 5.18, the conclusion of Lemma 29 for b0, with its exceptional set `E_q`;
* `h523`, display 5.23, from 5.21, the proof of 4.4;
* `h522`, display 5.22, from 5.20 and 5.21, here with the window main term restricted to J,
  see QUESTION 3 of the burst notes.
Each hypothesis includes that its integrand is interval integrable on `[Y/2, 3Y]`. -/
theorem lower_exceptional_mean_square_of_518_522_523 (ω : ℝ → ℝ) {ε : ℝ}
    (W : ℝ → ℕ → ℝ → ℝ → ℂ) (H : ℝ → ℕ → ℝ → ℂ)
    (h518 : ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          (∀ χ : DirichletCharacter ℂ q, IntervalIntegrable (fun y =>
            ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q)) -
              Thm2.delta χ * W x q y z‖ ^ 2) volume
            (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε))) ∧
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖(∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q)) -
                Thm2.delta χ * W x q y z‖ ^ 2 ≤
                  C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (h523 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          IntervalIntegrable (fun y => ‖W x q y z - z * H x q y‖ ^ 2) volume
            (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖W x q y z - z * H x q y‖ ^ 2 ≤
            C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (h522 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          IntervalIntegrable (fun y => ‖z * H x q y -
              ∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)‖ ^ 2) volume
            (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖z * H x q y -
                ∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                  ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)‖ ^ 2 ≤
            C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  obtain ⟨E, hE⟩ := h518
  refine ⟨E, fun A hA => ?_⟩
  obtain ⟨C1, hC1⟩ := hE A hA
  obtain ⟨C2, hC2⟩ := h523 A hA
  obtain ⟨C3, hC3⟩ := h522 A hA
  set K := max (max (max C1 C2) C3) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hC1K : C1 ≤ K := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hC2K : C2 ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hC3K : C3 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨9 * K, fun x hx q hq hqQ => ?_⟩
  have hxK : K ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hcard, hms⟩ := hC1 x (by linarith) q hq hqQ
  simp only [window_sum_sub]
  set Y := x ^ (11 / 20 + ε) with hY
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (by linarith) _
  have hR0 : 0 ≤ ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A) := by
    have := Real.rpow_nonneg (Real.log_nonneg hx1) (-A)
    positivity
  have hq0 : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := by
    have := Real.rpow_nonneg (Real.log_nonneg hx1) (-2 * A)
    have := Real.rpow_nonneg (Nat.cast_nonneg q) (1 / 2 : ℝ)
    positivity
  refine ⟨?_, fun z hz1 hz2 => ?_⟩
  · calc ((E A x q).card : ℝ) ≤ C1 * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := hcard
      _ ≤ 9 * K * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith) hq0
  obtain ⟨hint1, hb1⟩ := hms z hz1 hz2
  obtain ⟨hint2, hb2⟩ := hC2 x (by linarith) q hq hqQ z hz1 hz2
  obtain ⟨hint3, hb3⟩ := hC3 x (by linarith) q hq hqQ z hz1 hz2
  have hab : Y / 2 ≤ 3 * Y := by linarith
  have hmain := mean_square_three ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q)
    hab
    (fun χ y => ∑ m ∈ (rightInterval ε x).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
      (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q))
    (fun y => W x q y z) (fun y => z * H x q y)
    (fun y => ∑ m ∈ (rightInterval ε x).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
      ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ))
    (fun χ _ => hint1 χ) hint2 hint3
  have hK9 : 3 * (C1 * ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A)) +
      3 * (C2 * ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A)) +
      3 * (C3 * ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A)) ≤
      9 * K * ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A) := by
    have e : ∀ c : ℝ, c * ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A) =
        c * (((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A)) := fun c => by ring
    rw [e, e, e, e]
    have h1 := mul_le_mul_of_nonneg_right hC1K hR0
    have h2 := mul_le_mul_of_nonneg_right hC2K hR0
    have h3 := mul_le_mul_of_nonneg_right hC3K hR0
    nlinarith
  linarith

/-! ### The steps 5.19 to 5.23 on page 52, with `W` and `H` as parameters -/

/-- P0069 Baker Harman Pintz 1997, page 52, "Combining (5.19), (5.17)" to get 5.20, and
"Combining (5.20) with (5.21)": the norm of a sum of two terms, squared, is at most twice the
sum of the squares. -/
theorem norm_add_sq_le_two (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := norm_add_le a b
  have h0 := norm_nonneg (a + b)
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    rw [sq, sq]; exact mul_le_mul h h h0 (by positivity)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- P0069 Baker Harman Pintz 1997, page 52, "Another consequence of (5.21) is (5.23)": a
pointwise bound `|f(y)| ≤ B y` on `[a, b]`, with `0 ≤ a ≤ b`, gives the mean square bound
`∫ |f|^2 ≤ B^2 b^2 (b - a)`. With `f(y) = W(y, z) - z H(y)`, `B = C z L^(-A)` from 5.21,
`a = Y/2` and `b = 3Y`, this is `≪ z^2 Y^3 L^(-2A)`, which is 5.23. -/
theorem mean_square_of_pointwise {a b B : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (f : ℝ → ℂ) (hf : ∀ y ∈ Set.Icc a b, ‖f y‖ ≤ B * y) :
    ∫ y in a..b, ‖f y‖ ^ 2 ≤ B ^ 2 * b ^ 2 * (b - a) := by
  have hR : 0 ≤ B ^ 2 * b ^ 2 * (b - a) := by
    have : 0 ≤ b - a := by linarith
    positivity
  by_cases hL : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume a b
  · have h := intervalIntegral.integral_mono_on hab hL
      (intervalIntegrable_const (c := B ^ 2 * b ^ 2)) fun y hy => by
        have h1 := hf y hy
        have h0 := norm_nonneg (f y)
        have hy0 : 0 ≤ y := le_trans ha hy.1
        have h2 : B * y ≤ B * b := mul_le_mul_of_nonneg_left hy.2 hB
        have h3 : ‖f y‖ ≤ B * b := h1.trans h2
        calc ‖f y‖ ^ 2 ≤ (B * b) ^ 2 := pow_le_pow_left₀ h0 h3 2
          _ = B ^ 2 * b ^ 2 := by ring
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  · rw [intervalIntegral.integral_undef hL]
    exact hR

/-- P0069 Baker Harman Pintz 1997, page 52, "and consequently (5.22)": the quantity
`z H(y) - v0 y z / L'` is `z / z0` times the same quantity at `z0`, so its mean square scales
by `(z / z0)^2`, and the bound `≪ z0^2 Y^3 L^(-A)` at `z0` becomes `≪ z^2 Y^3 L^(-A)` at `z`.
Here `c` stands for `v0 / L'`. -/
theorem mean_square_scale_z (H : ℝ → ℂ) (c : ℂ) {z z0 : ℝ} (hz0 : z0 ≠ 0) (a b : ℝ) :
    ∫ y in a..b, ‖(z : ℂ) * H y - c * y * z‖ ^ 2 =
      (z / z0) ^ 2 * ∫ y in a..b, ‖(z0 : ℂ) * H y - c * y * z0‖ ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y _ => ?_
  have hz0' : (z0 : ℂ) ≠ 0 := by exact_mod_cast hz0
  have hid : (z : ℂ) * H y - c * y * z = ((z / z0 : ℝ) : ℂ) * ((z0 : ℂ) * H y - c * y * z0) := by
    push_cast
    field_simp
  simp only [hid, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- P0069 Baker Harman Pintz 1997, page 52, "and consequently (5.22)", as a bound: if the
mean square at `z0` is at most `K z0^2`, the mean square at `z` is at most `K z^2`. -/
theorem mean_square_scale_z_le (H : ℝ → ℂ) (c : ℂ) {z z0 K : ℝ} (hz0 : z0 ≠ 0) (a b : ℝ)
    (h0 : ∫ y in a..b, ‖(z0 : ℂ) * H y - c * y * z0‖ ^ 2 ≤ K * z0 ^ 2) :
    ∫ y in a..b, ‖(z : ℂ) * H y - c * y * z‖ ^ 2 ≤ K * z ^ 2 := by
  rw [mean_square_scale_z H c hz0 a b]
  have hs : 0 ≤ (z / z0) ^ 2 := sq_nonneg _
  calc (z / z0) ^ 2 * ∫ y in a..b, ‖(z0 : ℂ) * H y - c * y * z0‖ ^ 2
      ≤ (z / z0) ^ 2 * (K * z0 ^ 2) := mul_le_mul_of_nonneg_left h0 hs
    _ = K * z ^ 2 := by field_simp

end LeanLab.BHP1997.LowerShortMeanSquare
