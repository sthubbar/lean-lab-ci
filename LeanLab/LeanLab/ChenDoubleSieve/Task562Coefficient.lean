import LeanLab.ChenDoubleSieve.Task562Polynomial
import LeanLab.ChenDoubleSieve.Task562Moments

/-!
Finite coefficient integration for Wu 2004 Lemma 5.2 page 26, D2,16.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task562
open Wu04Functional

/-- Exact rational integration of a four variable polynomial in shifted coordinates.
Wu 2004 page 26, derived finite moment functional. -/
def polyMomentQ (p : MvPolynomial (Fin 4) ℚ) (a b : ℚ) : ℚ :=
  ∑ e ∈ p.support, p.coeff e *
    ((b - a) ^ ((∑ j : Fin 4, e j) + 4) / momentDenom 4 (fun j => e j))

/-- The finite coefficient functional equals the actual ordered polynomial integral.
Wu 2004 page 26, derived exact quadrature identity. -/
theorem integral_eval_shifted (p : MvPolynomial (Fin 4) ℚ) {a b : ℚ} (hab : a ≤ b) :
    (∫ x in domain (fun _ : Fin 4 => (a : ℝ)) (fun _ => (b : ℝ)),
      p.eval₂ (algebraMap ℚ ℝ) (fun j => x j - (a : ℝ))) = (polyMomentQ p a b : ℝ) := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hi (e : Fin 4 →₀ ℕ) : IntegrableOn (fun x : Fin 4 → ℝ =>
      (algebraMap ℚ ℝ) (p.coeff e) * ∏ j, (x j - (a : ℝ)) ^ e j)
      (domain (fun _ => (a : ℝ)) (fun _ => (b : ℝ))) volume := by
    apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
    fun_prop
  simp_rw [MvPolynomial.eval₂_eq']
  rw [integral_finsetSum _ (fun e _ => hi e)]
  unfold polyMomentQ
  push_cast
  apply sum_congr rfl
  intro e he
  rw [MeasureTheory.integral_const_mul, ordered_shifted_monomial 4 (fun j => e j) hab']
  rfl

/-- The normalized coordinate polynomial in shifted variables.
Wu 2004 page 26, derived rational certificate data. -/
def zPoly (j : Fin 4) : MvPolynomial (Fin 4) ℚ :=
  (MvPolynomial.X j - MvPolynomial.C (41 / 1455)) * MvPolynomial.C (1455 / 541)

/-- The normalized sum polynomial in shifted variables.
Wu 2004 page 26, derived rational certificate data. -/
def tPoly : MvPolynomial (Fin 4) ℚ :=
  ((∑ j : Fin 4, MvPolynomial.X j) - MvPolynomial.C (164 / 1455)) *
    MvPolynomial.C (1455 / 746)

/-- The explicit finite polynomial over the rationals whose real evaluation is r3Poly.
Wu 2004 page 26, derived exact certificate data. -/
def upperMvPoly : MvPolynomial (Fin 4) ℚ :=
  MvPolynomial.C (1 / ((541 / 1455 : ℚ) ^ 4 * (746 / 1455 : ℚ))) *
    (∏ j : Fin 4, (1 - zPoly j + zPoly j ^ 2 - zPoly j ^ 3 +
      MvPolynomial.C (2825761 / 79170210500))) *
    (1 + tPoly + tPoly ^ 2 + tPoly ^ 3 + tPoly ^ 4 + tPoly ^ 5 +
      MvPolynomial.C (304006671424 / 2101053678330063))

/-- Evaluation of each normalized coordinate polynomial gives the intended real coordinate.
Wu 2004 page 26, derived certificate translation. -/
theorem zPoly_eval (x : Fin 4 → ℝ) (j : Fin 4) :
    (zPoly j).eval₂ (algebraMap ℚ ℝ) (fun j => x j - (100 / 291 : ℝ)) =
      (x j - 541 / 1455) / (541 / 1455 : ℝ) := by
  simp [zPoly]
  ring

/-- Evaluation of the normalized sum polynomial gives the intended real sum.
Wu 2004 page 26, derived certificate translation. -/
theorem tPoly_eval (x : Fin 4 → ℝ) :
    tPoly.eval₂ (algebraMap ℚ ℝ) (fun j => x j - (100 / 291 : ℝ)) =
      ((∑ j, x j) - 4 * (541 / 1455 : ℝ)) / (746 / 1455 : ℝ) := by
  simp [tPoly, Fin.sum_univ_succ]
  ring

/-- The rational polynomial data evaluate to the already proved pointwise majorant.
Wu 2004 page 26, derived certificate translation. -/
theorem upperMvPoly_eval (x : Fin 4 → ℝ) :
    upperMvPoly.eval₂ (algebraMap ℚ ℝ) (fun j => x j - (100 / 291 : ℝ)) = r3Poly x := by
  simp [upperMvPoly, r3Poly, g3, p5, zPoly_eval, tPoly_eval]

/-- Exact integration of the polynomial majorant reduces to a finite rational expression.
Wu 2004 page 26, derived coefficient certificate identity. -/
theorem r3Poly_integral_eq :
    (∫ x in domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)), r3Poly x) =
      (polyMomentQ upperMvPoly (100 / 291) (2 / 5) : ℝ) := by
  have h := integral_eval_shifted upperMvPoly (by norm_num : (100 / 291 : ℚ) ≤ 2 / 5)
  simpa only [Rat.cast_div, Rat.cast_ofNat, upperMvPoly_eval] using h

end LeanLab.ChenDoubleSieve.Task562
