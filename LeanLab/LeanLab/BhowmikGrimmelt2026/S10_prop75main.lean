/-
S10-05, burst-20261124, CLOUD S10. Target: `leaf_main_and_single_zero` of SPLIT_prop75.lean,
P0029 Bhowmik and Grimmelt 2026, Proposition 7.5, display 7.17, page 28.

Verdict: the leaf is NOT a faithful piece of the paper proof and is not split here.
The paper derives, from two uses of Lemma 7.4, display 7.12, that the smoothed major arc
integral `I` equals `N 𝔖(N) + 𝓜 + 𝒵` up to an error small in mean square; the double zero
sum `𝒵` of display 7.16 is a MAIN term next to `𝓜` of display 7.15. The leaf asks for
`I - N 𝔖(N) - 𝓜` to be small, so it silently asserts that `𝒵` is small.

What is proved here, without sorry and without cited inputs used as axioms:
* `sq_transfer_S10`: an abstract mean square transfer, if `f - g` is small in mean square then
  `f` is small iff `g` is small.
* `leaf_rphi_major_of_lemma73_S10`: step one of the paper, display 7.8 at
  `η = R ^ (-1/4)`, as an implication from the hypothesis `Lemma73`.
* `merged_of_prop75_S10`: `Prop75` together with Lemma 7.3 gives the merged estimate, the
  mean square of `I - N 𝔖(N) - 𝓜 - 𝒵`; this is the step the paper actually proves.
* `leaf_main_iff_zero_pair_S10`: under the merged estimate, the body of
  `leaf_main_and_single_zero` holds iff the body of `leaf_zero_pair` holds.
* `leaf_main_iff_zero_pair_of_paper_S10`: under the paper's own `Prop75` and `Lemma73`, the two
  leaves are equivalent. So the leaf stands or falls with the double zero sum being small in
  mean square, which a real zero of a real primitive character of conductor at most `R` close
  to `1` would contradict, see the note.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import LeanLab.BhowmikGrimmelt2026.Feed1122_SPLIT_prop75_leaf_rphi_major

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- `‖a‖ ^ 2 ≤ 2 ‖a - b‖ ^ 2 + 2 ‖b‖ ^ 2` in `ℂ`. PROVED. -/
theorem norm_sq_le_two_S10 (a b : ℂ) : ‖a‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    simpa using norm_add_le (a - b) b
  have h0 : 0 ≤ ‖a‖ := norm_nonneg _
  have hsq : ‖a‖ ^ 2 ≤ (‖a - b‖ + ‖b‖) ^ 2 := by
    rw [pow_two, pow_two]; exact mul_le_mul h h h0 (by positivity)
  nlinarith [sq_nonneg (‖a - b‖ - ‖b‖)]

/-- Abstract mean square transfer. If `f - g` has mean square at most `C₀ B X`, then a bound
`C B X` for the mean square of `g` gives one for `f`. PROVED. -/
theorem sq_transfer_S10 (f g : ℕ → ℕ → ℂ) (B : ℕ → ℝ) (C₀ : ℝ)
    (hfg : ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖f X N - g X N‖ ^ 2 ≤ C₀ * B X)
    (hg : ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖g X N‖ ^ 2 ≤ C * B X) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖f X N‖ ^ 2 ≤ C * B X := by
  obtain ⟨C, hC⟩ := hg
  refine ⟨2 * C₀ + 2 * C, fun X hX => ?_⟩
  calc ∑ N ∈ Finset.Icc 1 X, ‖f X N‖ ^ 2
      ≤ ∑ N ∈ Finset.Icc 1 X, (2 * ‖f X N - g X N‖ ^ 2 + 2 * ‖g X N‖ ^ 2) :=
        Finset.sum_le_sum fun N _ => norm_sq_le_two_S10 _ _
    _ = 2 * ∑ N ∈ Finset.Icc 1 X, ‖f X N - g X N‖ ^ 2 +
          2 * ∑ N ∈ Finset.Icc 1 X, ‖g X N‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (C₀ * B X) + 2 * (C * B X) := by linarith [hfg X hX, hC X hX]
    _ = (2 * C₀ + 2 * C) * B X := by ring

/-- The symmetric form of the transfer: under the same hypothesis, `f` small iff `g` small.
PROVED. -/
theorem sq_transfer_iff_S10 (f g : ℕ → ℕ → ℂ) (B : ℕ → ℝ) (C₀ : ℝ)
    (hfg : ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖f X N - g X N‖ ^ 2 ≤ C₀ * B X) :
    (∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖f X N‖ ^ 2 ≤ C * B X) ↔
      (∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖g X N‖ ^ 2 ≤ C * B X) := by
  constructor
  · intro hf
    refine sq_transfer_S10 g f B C₀ (fun X hX => ?_) hf
    calc ∑ N ∈ Finset.Icc 1 X, ‖g X N - f X N‖ ^ 2
        = ∑ N ∈ Finset.Icc 1 X, ‖f X N - g X N‖ ^ 2 := by
          refine Finset.sum_congr rfl fun N _ => ?_
          rw [norm_sub_rev]
      _ ≤ C₀ * B X := hfg X hX
  · exact sq_transfer_S10 f g B C₀ hfg

/-- Step one of Proposition 7.5, Lemma 7.3 display 7.8 page 26 at `η = R ^ (-1/4)` and
`T_q = η X q / R`, taken from the hypothesis `Lemma73` instead of the cited `lemma73`.
The proof is that of `leaf_rphi_major_of_leaves` with the hypothesis in place of the cited
theorem. PROVED as an implication. -/
theorem leaf_rphi_major_of_lemma73_S10 (h73 : Lemma73) (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(rphi ϕ N : ℂ) -
          ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  obtain ⟨C₇, h₇⟩ := h73 ϕ G hϕ hG ϑ hϑ0 (by linarith)
  obtain ⟨X₀, hX₀⟩ := leaf_eta_admissible ϑ hϑ0 hϑ
  set F : ℕ → ℝ := fun X => ∑ N ∈ Finset.Icc 1 X,
        ‖(rphi ϕ N : ℂ) -
          ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))‖ ^ 2 with hF
  set g : ℕ → ℝ := fun X => ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5
    with hgdef
  have hgpos : ∀ X : ℕ, 2 ≤ X → 0 < g X := by
    intro X hX
    have hx : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hl : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
    simp only [g]; positivity
  obtain ⟨Cs, hCs0, hCs⟩ := small_X_absorb F g X₀ hgpos
  refine ⟨Cs + 2 * max C₇ 0, ?_⟩
  intro X hX
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hx : (0 : ℝ) < X := by linarith
  have hgX := hgpos X hX
  suffices key : F X ≤ (Cs + 2 * max C₇ 0) * g X by rw [mul_assoc]; exact key
  by_cases hsmall : X < X₀
  · have := hCs X hX hsmall
    nlinarith [le_max_right C₇ 0]
  · replace hsmall := not_lt.mp hsmall
    have hr1 : (1 : ℝ) ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hx1 hϑ0.le
    have hr : (0 : ℝ) < (X : ℝ) ^ ϑ := by linarith
    set r := (X : ℝ) ^ ϑ with hrdef
    set η := r ^ (-(1 / 4) : ℝ) with hηdef
    have hη0 : 0 < η := Real.rpow_pos_of_pos hr _
    have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr1 (by norm_num)
    have h := h₇ X hX η hη0 hη1 (hX₀ X hsmall)
    have hη4 : η ^ 4 = r⁻¹ := by
      rw [hηdef, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      norm_num [Real.rpow_neg_one]
    have he1 : r⁻¹ * (X : ℝ) ^ 3 = (X : ℝ) ^ (3 - ϑ) := by
      rw [Real.rpow_sub hx, hrdef]
      norm_num [div_eq_inv_mul]
    have he2 : (X : ℝ) ^ (-(2 / 5) : ℝ) * (X : ℝ) ^ 3 = (X : ℝ) ^ (13 / 5 : ℝ) := by
      rw [show (13 / 5 : ℝ) = -(2 / 5) + (3 : ℕ) by norm_num, Real.rpow_add hx,
        Real.rpow_natCast]
    have hrhs : C₇ * (r⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ) + η ^ 4) * (X : ℝ) ^ 3 *
        Real.log X ^ 5 =
        C₇ * (2 * (X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
      rw [hη4, ← he1, ← he2]; ring
    have hl : 0 ≤ Real.log X := Real.log_nonneg hx1
    have hp1 : 0 ≤ (X : ℝ) ^ (3 - ϑ) := (Real.rpow_pos_of_pos hx _).le
    have hp2 : 0 ≤ (X : ℝ) ^ (13 / 5 : ℝ) := (Real.rpow_pos_of_pos hx _).le
    have hL5 : 0 ≤ Real.log X ^ 5 := pow_nonneg hl 5
    have hstep : C₇ * (2 * (X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 ≤
        2 * max C₇ 0 * g X := by
      simp only [g]
      have hA : 0 ≤ (2 * (X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
        positivity
      have hm := le_max_left C₇ 0
      have hm0 := le_max_right C₇ 0
      nlinarith [mul_le_mul_of_nonneg_right hm hA, mul_nonneg hm0 (mul_nonneg hp2 hL5)]
    have hFX : F X ≤ C₇ * (r⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ) + η ^ 4) * (X : ℝ) ^ 3 *
        Real.log X ^ 5 := by
      simp only [F]; exact h
    nlinarith [mul_nonneg hCs0 hgX.le]

/-- The merged estimate, the step the paper proves from two uses of Lemma 7.4: the mean square
over `N ≤ X` of `I - N 𝔖(N) - 𝓜 - 𝒵`, with `I` the smoothed major arc integral, is at most the
target shape. It follows from `Prop75`, display 7.17 page 28, and step one, display 7.8.
PROVED as an implication. -/
theorem merged_of_prop75_S10 (h75 : Prop75) (h73 : Lemma73) (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) - N * singular N -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  obtain ⟨C₁, h₁⟩ := leaf_rphi_major_of_lemma73_S10 h73 ϕ G hϕ hG ϑ hϑ0 hϑ
  obtain ⟨C₅, h₅⟩ := h75 ϕ G hϕ hG ϑ hϑ0 hϑ
  have key := sq_transfer_S10
    (fun X N => (∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) - N * singular N -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ))
    (fun X N => (rphi ϕ N : ℂ) - N * singular N -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ))
    (fun X : ℕ => ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5) C₁
    (fun X hX => by
      calc _ = ∑ N ∈ Finset.Icc 1 X,
              ‖(rphi ϕ N : ℂ) -
                ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                  bRhat G ((X : ℝ) ^ ϑ)
                    (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                  ee (-(N * α))‖ ^ 2 := by
            refine Finset.sum_congr rfl fun N _ => ?_
            rw [← norm_neg]; congr 2; ring
        _ ≤ _ := by rw [← mul_assoc]; exact h₁ X hX)
    ⟨C₅, fun X hX => by rw [← mul_assoc]; exact h₅ X hX⟩
  obtain ⟨C, hC⟩ := key
  exact ⟨C, fun X hX => by rw [mul_assoc]; exact hC X hX⟩

/-- Under the merged estimate, the body of `leaf_main_and_single_zero` holds iff the body of
`leaf_zero_pair` holds. PROVED. -/
theorem leaf_main_iff_zero_pair_S10 (ϕ G : ℝ → ℝ) (ϑ : ℝ)
    (hmerged : ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) - N * singular N -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5) :
    (∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) - N * singular N -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5) ↔
    (∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5) := by
  obtain ⟨C₀, h₀⟩ := hmerged
  have hiff := sq_transfer_iff_S10
    (fun X N => (∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) - N * singular N -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ))
    (fun X N => Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ))
    (fun X : ℕ => ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5) C₀
    (fun X hX => by rw [← mul_assoc]; exact h₀ X hX)
  simp only [← mul_assoc] at hiff
  exact hiff

/-- Under the paper's own Proposition 7.5 and Lemma 7.3, the leaf `leaf_main_and_single_zero`
and the leaf `leaf_zero_pair` of SPLIT_prop75.lean are equivalent, for every admissible `ϕ`,
`G` and `ϑ`. So the first leaf is exactly as strong as the claim that the double zero sum
`𝒵` of display 7.16 is small in mean square, which the paper does not prove. PROVED as an
implication. -/
theorem leaf_main_iff_zero_pair_of_paper_S10 (h75 : Prop75) (h73 : Lemma73) (ϕ G : ℝ → ℝ)
    (hϕ : IsPhi ϕ) (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    (∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) - N * singular N -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5) ↔
    (∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5) :=
  leaf_main_iff_zero_pair_S10 ϕ G ϑ (merged_of_prop75_S10 h75 h73 ϕ G hϕ hG ϑ hϑ0 hϑ)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.sq_transfer_iff_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_rphi_major_of_lemma73_S10
#print axioms LeanLab.BhowmikGrimmelt2026.merged_of_prop75_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_main_iff_zero_pair_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_main_iff_zero_pair_of_paper_S10
