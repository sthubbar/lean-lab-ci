import LeanLab.ChirreHagen2025.Decomp377a
import LeanLab.ChirreHagen2025.DecompJ611
import LeanLab.ChirreHagen2025.PrimePowers272
import LeanLab.ChirreHagen2025.FinitePrimePowers272
import LeanLab.ChirreHagen2025.Decomp377c

/-!
P0075 page 5 display 2.9. The cited mean value proof is Proposition 2.11
on pages 102 and 103 of Dona, Helfgott and Zuniga Alterman.
https://doi.org/10.5802/jtnb.1194
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp429c
open MeasureTheory ArithmeticFunction Decomp377a

/-- P0075 page 5, the two finite coefficient moments after the mean value step. -/
noncomputable def coefficientMoment (T : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊T⌋₊, (vonMangoldt n * selbergWeight T n) ^ 2 / (n : ℝ) ^ k

/-- P0075 page 4, the smoothing weight lies between zero and one. -/
theorem selberg_weight_bounds (T : ℝ) (n : ℕ) (hn : 1 ≤ n) (hnT : (n : ℝ) ≤ T) :
    0 ≤ selbergWeight T n ∧ selbergWeight T n ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hT0 : 0 < T := hn0.trans_le hnT
  unfold selbergWeight
  split_ifs with h
  · norm_num
  · have hlog0 : 0 ≤ Real.log (T / (n : ℝ)) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ hn0).mpr (by simpa using hnT)
    have hnlt : T / Real.exp (2 * 1.278) < (n : ℝ) := lt_of_not_ge h
    have hr : T / (n : ℝ) ≤ Real.exp (2 * 1.278) := by
      apply (div_le_iff₀ hn0).mpr
      have hh := (div_lt_iff₀ (Real.exp_pos (2 * 1.278))).mp hnlt
      linarith
    constructor
    · positivity
    · apply (div_le_one (by norm_num : (0 : ℝ) < 2 * 1.278)).mpr
      exact (Real.log_le_iff_le_exp (by positivity)).mpr hr

/-- P0075 page 5, discarding the weight bounds either finite coefficient moment. -/
theorem coefficientMoment_le (T : ℝ) (k : ℕ) (hT : 0 ≤ T) :
    coefficientMoment T k ≤
      ∑ n ∈ Finset.Icc 1 ⌊T⌋₊, vonMangoldt n ^ 2 / (n : ℝ) ^ k := by
  unfold coefficientMoment
  apply Finset.sum_le_sum
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have hnT : (n : ℝ) ≤ T := (by exact_mod_cast hn'.2 : (n : ℝ) ≤ ⌊T⌋₊).trans (Nat.floor_le hT)
  have hw := selberg_weight_bounds T n hn'.1 hnT
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hw2 := pow_le_pow_left₀ hw.1 hw.2 2
  rw [mul_pow]
  nlinarith [sq_nonneg (vonMangoldt n)]

/-- P0075 page 5, the first coefficient moment uses only the stated Appendix bound.
CONDITIONAL ON the supplied Lemma A.2 input. -/
theorem first_moment_of (hA2 : Additional122.lemmaA2) (hRH : RiemannHypothesis)
    (T : ℝ) (hT : 4 * 10 ^ 13 ≤ T) :
    coefficientMoment T 1 ≤ Real.log T ^ 2 / 2 + 6 := by
  have h := coefficientMoment_le T 1 (by linarith)
  simp only [pow_one] at h
  exact h.trans ((hA2 hRH T (by linarith)).trans (by linarith))

/-- P0075 page 5, the second coefficient moment is a finite part of Appendix A.1.
CONDITIONAL ON the supplied numerical bound in Lemma A.1 part 2. -/
theorem second_moment_of (hA1 : Additional122.lemmaA1_part2) (T : ℝ) (hT : 0 ≤ T) :
    coefficientMoment T 2 ≤ 0.8053 := by
  let f : ℕ → ℝ := fun n => vonMangoldt n ^ 2 / (n : ℝ) ^ 2
  have hf : Summable f := by
    apply (summable_nat_add_iff 1).mp
    simpa [f, Nat.cast_add, Nat.cast_one] using hA1.1
  have hsum : (∑' n : ℕ, f n) < 0.8053 := by
    rw [hf.tsum_eq_zero_add]
    simpa [f, Nat.cast_add, Nat.cast_one] using hA1.2
  exact (coefficientMoment_le T 2 hT).trans
    ((hf.sum_le_tsum (Finset.Icc 1 ⌊T⌋₊) (fun n hn => by dsimp [f]; positivity)).trans hsum.le)

/-- LEAF. P0075 page 5, mean value display before display 2.9.
Dona, Helfgott and Zuniga Alterman Proposition 2.11 on pages 102 and 103
bounds the finite polynomial by its two coefficient moments. Its proof
uses the improved Hilbert inequality of Preissmann. This leaf has no
Appendix numerical coefficient estimate and no zeta remainder. -/
theorem polynomial_mean_value (T : ℝ) (hT : 10000 ≤ T) :
    (∫ t in (10 ^ 4 : ℝ)..T, ‖polynomial T t‖ ^ 2) ≤
      (T - 10000 + 4.133) * coefficientMoment T 2 + 8.265 * coefficientMoment T 1 := by
  sorry

/-- P0075 page 5 display 2.9 from the mean value input and the two Appendix inputs.
CONDITIONAL ON all three supplied inputs. -/
theorem polynomial_mean_square_of (hA1 : Additional122.lemmaA1_part2)
    (hA2 : Additional122.lemmaA2) (hRH : RiemannHypothesis) (T : ℝ)
    (hT : 4 * 10 ^ 13 ≤ T) :
    (∫ t in (10 ^ 4 : ℝ)..T, ‖polynomial T t‖ ^ 2) ≤
      0.8053 * T + 4.1325 * Real.log T ^ 2 - 8000 := by
  exact (polynomial_mean_value T (by linarith)).trans
    (mean_value_budget T _ _ (by linarith) (second_moment_of hA1 T (by linarith))
      (first_moment_of hA2 hRH T hT))

/-- Exact existing Decomp377a.polynomial_mean_square statement.
CONDITIONAL ON polynomial_mean_value and the inherited Appendix numerical
and prime-sum inputs. Proved finite identities replace their old sorry leaves.
The inherited Appendix arithmetic questions remain. -/
theorem polynomial_mean_square (hRH : RiemannHypothesis) (T : ℝ)
    (hT : 4 * 10 ^ 13 ≤ T) :
    (∫ t in (10 ^ 4 : ℝ)..T, ‖polynomial T t‖ ^ 2) ≤
      0.8053 * T + 4.1325 * Real.log T ^ 2 - 8000 := by
  have hA1 : Additional122.lemmaA1_part2 := by
    refine ⟨Additional122.mangoldt_sq_summable, ?_⟩
    exact DecompJ207.mangoldt_sum_bound PrimePowers272.mangoldt_sum_eq_prime_sum
      Summability272.prime_sum_le_part3 DecompJ207.lemmaA1_part3_assumed.2
  have hA2 : Additional122.lemmaA2 := by
    intro hRH' x hx
    have hsplit := Decomp377c.leaf_sum_split x hx
    have hpowers := FinitePrimePowers272.leaf_sum_prime_powers x hx
    have htheta := DecompJ611.leaf_theta_integral x hx hRH'
    have hnum := DecompJ207.lemmaA1_part3_assumed.2
    linarith
  exact polynomial_mean_square_of hA1 hA2 hRH T hT

end LeanLab.ChirreHagen2025.Decomp429c
