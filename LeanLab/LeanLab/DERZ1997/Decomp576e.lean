import Mathlib

/-!
Uniform centre bounds for the real-part power Jensen argument.
Trudgian arXiv:1206.1844v4 page 7, display 4.4.
The lower bound here is weaker than the printed Euler-product ratio.
It is enough to isolate a conductor-independent centre logarithm budget.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.DERZ1997.Decomp576e
open Complex MeasureTheory Set
open scoped LSeries.notation ArithmeticFunction.Moebius

/-- Bounded coefficients give a uniform vertical-line L-series norm majorant.
Trudgian page 7, the absolute-series upper bound in display 4.4.
-/
theorem norm_LSeries_vertical576 {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖LSeries f ((σ : ℂ) + I * t)‖ ≤
      ∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖ := by
  let s : ℂ := (σ : ℂ) + I * t
  have hb : ∀ n, ‖LSeries.term f s n‖ ≤ ‖LSeries.term 1 (σ : ℂ) n‖ := fun n =>
    (LSeries.norm_term_le s (g := 1) (by simpa using hf n)).trans
      (LSeries.norm_term_le_of_re_le_re _ (by simp [s]) n)
  have hsum : Summable (fun n : ℕ => ‖LSeries.term 1 (σ : ℂ) n‖) :=
    (LSeriesSummable_one_iff.mpr (by simpa using hσ)).norm
  have hs : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb hsum)

/-- The Mobius inverse bounds the centre norm from below, uniformly in the modulus.
Trudgian page 7, display 4.4, with the weaker lower bound reciprocal zeta of sigma.
The centre sigma is arbitrary above one and includes five quarters.
-/
theorem LFunction_centre_lower576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖DirichletCharacter.LFunction χ ((σ : ℂ) + I * t)‖ *
      ∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖ := by
  have hs : 1 < ((σ : ℂ) + I * t).re := by simpa using hσ
  have hinv := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hb : ‖LSeries (↗χ * ↗μ) ((σ : ℂ) + I * t)‖ ≤
      ∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖ := by
    apply norm_LSeries_vertical576 (σ := σ) (t := t) ?_ hσ
    intro n
    simp only [Pi.mul_apply, norm_mul]
    have hχ := χ.norm_le_one n
    have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    nlinarith [norm_nonneg (χ n), norm_nonneg ((μ n : ℤ) : ℂ)]
  have hprod : ‖DirichletCharacter.LFunction χ ((σ : ℂ) + I * t)‖ *
      ‖LSeries (↗χ * ↗μ) ((σ : ℂ) + I * t)‖ = 1 := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs, ← norm_mul, hinv, norm_one]
  calc
    1 = _ := hprod.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)

/-- The absolute Dirichlet-series majorant at five quarters is at most five.
Trudgian page 7, display 4.4, using the elementary integral-test majorant.
-/
theorem quarter_series_budget576 :
    (∑' n : ℕ, ‖LSeries.term 1 (5 / 4 : ℂ) n‖) ≤ 5 := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-5 / 4 : ℝ)) (Ici 1) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) hxy (by norm_num)
  have hint : IntegrableOn (fun x : ℝ => x ^ (-5 / 4 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have ht := AntitoneOn.tsum_comp_add_le_integral
    (f := fun x : ℝ => x ^ (-5 / 4 : ℝ)) 1
    (by simpa only [Nat.cast_one] using hanti)
    (by simpa only [Nat.cast_one] using hint)
    (by
      intro x hx
      have hx' : (1 : ℝ) < x := by simpa only [Nat.cast_one, mem_Ioi] using hx
      exact Real.rpow_nonneg (by linarith) _)
  norm_num only [Nat.cast_one] at ht
  rw [integral_Ioi_rpow_of_lt (a := -(5 / 4 : ℝ)) (c := 1) (by norm_num) (by norm_num)] at ht
  norm_num at ht
  have hsum : Summable (fun n : ℕ => ‖LSeries.term 1 (5 / 4 : ℂ) n‖) :=
    (LSeriesSummable_one_iff.mpr (by norm_num)).norm
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hfirst : ∑ n ∈ Finset.range 2, ‖LSeries.term 1 (5 / 4 : ℂ) n‖ = 1 := by
    simp [Finset.sum_range_succ, LSeries.term]
  rw [hfirst] at hsplit
  have heq (n : ℕ) : ‖LSeries.term 1 (5 / 4 : ℂ) (n + 2)‖ =
      ((n + 2 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
    rw [LSeries.norm_term_eq, if_neg (by omega : n + 2 ≠ 0)]
    rw [show (5 / 4 : ℂ).re = (5 / 4 : ℝ) by norm_num]
    simp only [Pi.one_apply, norm_one]
    rw [show (-5 / 4 : ℝ) = -(5 / 4 : ℝ) by ring, Real.rpow_neg, one_div] <;> positivity
  have htail : (∑' n : ℕ, ‖LSeries.term 1 (5 / 4 : ℂ) (n + 2)‖) ≤ 4 := by
    simpa only [heq, Nat.cast_add, Nat.cast_ofNat, add_assoc, one_add_one_eq_two,
      show (-5 / 4 : ℝ) = -(5 / 4 : ℝ) by ring] using ht
  linarith

/-- The Jensen centre has norm at least one fifth for every character.
Trudgian page 7, display 4.4, with a derived loose numerical lower bound.
-/
theorem LFunction_quarter_lower576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 5 : ℝ) ≤ ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + I * t)‖ := by
  have hlow := LFunction_centre_lower576 χ (by norm_num : (1 : ℝ) < 5 / 4) t
  have hmajor := mul_le_mul_of_nonneg_left quarter_series_budget576
    (norm_nonneg (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + I * t)))
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hlow
  linarith

end LeanLab.DERZ1997.Decomp576e
