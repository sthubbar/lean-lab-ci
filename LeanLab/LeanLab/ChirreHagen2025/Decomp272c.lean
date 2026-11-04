import LeanLab.ChirreHagen2025.Decomp122b

/-!
P0075 page 3, equation 2.1 and its four termwise bounds.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp272c

open MeasureTheory ArithmeticFunction Decomp122b

/-- LEAF. P0075 page 3, equation 2.1, by Dirichlet series and integration by parts.
At an integer N the sum through N minus one is exactly psi at the left limit.
Integrability is included before using the improper integral. -/
theorem backlund_identity (σ t : ℝ) (hσ : 1 < σ) (hσtop : σ < 2)
    (ht : 100 ≤ |t|) (N : ℕ) (hN : 74 ≤ N) :
    IntegrableOn
      (fun y : ℝ => ((Chebyshev.psi y - y : ℝ) : ℂ) /
        (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1)) (Set.Ioi (N : ℝ)) ∧
    -(deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)) =
      (∑ n ∈ Finset.Icc 1 (N - 1),
        (vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * Complex.I)) -
      (((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n) - (N : ℝ) : ℝ) : ℂ) /
        (N : ℂ) ^ ((σ : ℂ) + t * Complex.I) +
      (N : ℂ) ^ (1 - ((σ : ℂ) + t * Complex.I)) /
        ((σ : ℂ) + t * Complex.I - 1) +
      ((σ : ℂ) + t * Complex.I) *
        ∫ y in Set.Ioi (N : ℝ), ((Chebyshev.psi y - y : ℝ) : ℂ) /
          (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1) := by
  sorry

/-- LEAF. P0075 page 3, first display after equation 2.1.
Triangle inequality and reference 11, Lemma 10 bound the finite Mangoldt sum. -/
theorem finite_mangoldt_bound (σ t : ℝ) (hσ : 1 < σ) (hσtop : σ < 2)
    (ht : 100 ≤ |t|) (N : ℕ) (hN : 74 ≤ N) :
    ‖∑ n ∈ Finset.Icc 1 (N - 1),
      (vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * Complex.I)‖ ≤
      Real.log ((N : ℝ) - 1) - Real.eulerMascheroniConstant +
        1.3 / Real.log ((N : ℝ) - 1) ^ 2 := by
  sorry

/-- LEAF. P0075 page 3, second term bound after equation 2.1.
Use reference 19, Theorem 10. At prime powers take its left limit,
which exists since the finite sum through N minus one is psi at N minus. -/
theorem psi_boundary_bound (hRH : RiemannHypothesis) (σ t : ℝ)
    (hσ : 1 < σ) (hσtop : σ < 2) (ht : 100 ≤ |t|) (N : ℕ) (hN : 74 ≤ N) :
    ‖(((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n) - (N : ℝ) : ℝ) : ℂ) /
      (N : ℂ) ^ ((σ : ℂ) + t * Complex.I)‖ ≤
        Real.log (N : ℝ) ^ 2 / (8 * Real.pi * Real.sqrt (N : ℝ)) := by
  sorry

/-- LEAF. P0075 page 3, the trivial bound stated after the finite sum bound.
The numerator has norm at most one and the denominator has norm at least abs t. -/
theorem pole_term_bound (σ t : ℝ) (hσ : 1 < σ) (hσtop : σ < 2)
    (ht : 100 ≤ |t|) (N : ℕ) (hN : 74 ≤ N) :
    ‖(N : ℂ) ^ (1 - ((σ : ℂ) + t * Complex.I)) /
      ((σ : ℂ) + t * Complex.I - 1)‖ ≤ 1 / |t| := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have ht0 : (0 : ℝ) < |t| := by linarith
  have hnum : ‖(N : ℂ) ^ (1 - ((σ : ℂ) + t * Complex.I))‖ ≤ 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
    simpa using Real.rpow_le_one_of_one_le_of_nonpos hN1 (show 1 - σ ≤ 0 by linarith)
  have hden : |t| ≤ ‖(σ : ℂ) + t * Complex.I - 1‖ := by
    simpa using Complex.abs_im_le_norm ((σ : ℂ) + t * Complex.I - 1)
  rw [norm_div]
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (one_div_le_one_div_of_le ht0 hden)

/-- LEAF. P0075 page 3, the two displays bounding the last term of equation 2.1.
Use the Schoenfeld psi bound and integrate its majorant. The factor 1.001
bounds the ratio of the norm of sigma plus it to abs t. -/
theorem psi_tail_bound (hRH : RiemannHypothesis) (σ t : ℝ)
    (hσ : 1 < σ) (hσtop : σ < 2) (ht : 100 ≤ |t|) (N : ℕ) (hN : 74 ≤ N) :
    ‖((σ : ℂ) + t * Complex.I) *
      ∫ y in Set.Ioi (N : ℝ), ((Chebyshev.psi y - y : ℝ) : ℂ) /
        (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1)‖ ≤
      1.001 * |t| * (Real.log (N : ℝ) ^ 2 + 4 * Real.log (N : ℝ) + 8) /
        (4 * Real.pi * Real.sqrt (N : ℝ)) := by
  sorry

/-- P0075 page 3. The exact statement of Decomp122b.backlund_reduction.
CONDITIONAL ON the five preceding leaves, including the cited quantitative inputs. -/
theorem backlund_reduction (hRH : RiemannHypothesis) (σ t : ℝ)
    (hσ : 1 < σ) (hσtop : σ < 2) (ht : 100 ≤ |t|)
    (N : ℕ) (hN : 74 ≤ N) :
    ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      backlundRhs |t| N := by
  have hid := (backlund_identity σ t hσ hσtop ht N hN).2
  have hsum := finite_mangoldt_bound σ t hσ hσtop ht N hN
  have hboundary := psi_boundary_bound hRH σ t hσ hσtop ht N hN
  have hpole := pole_term_bound σ t hσ hσtop ht N hN
  have htail := psi_tail_bound hRH σ t hσ hσtop ht N hN
  have hnorm := norm_add_le
    ((∑ n ∈ Finset.Icc 1 (N - 1),
      (vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * Complex.I)) -
      (((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n) - (N : ℝ) : ℝ) : ℂ) /
        (N : ℂ) ^ ((σ : ℂ) + t * Complex.I) +
      (N : ℂ) ^ (1 - ((σ : ℂ) + t * Complex.I)) /
        ((σ : ℂ) + t * Complex.I - 1))
    (((σ : ℂ) + t * Complex.I) *
      ∫ y in Set.Ioi (N : ℝ), ((Chebyshev.psi y - y : ℝ) : ℂ) /
        (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1))
  rw [← hid, norm_neg] at hnorm
  have htriangle := norm_add_le
    ((∑ n ∈ Finset.Icc 1 (N - 1),
      (vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * Complex.I)) -
      (((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n) - (N : ℝ) : ℝ) : ℂ) /
        (N : ℂ) ^ ((σ : ℂ) + t * Complex.I))
    ((N : ℂ) ^ (1 - ((σ : ℂ) + t * Complex.I)) /
      ((σ : ℂ) + t * Complex.I - 1))
  have hsub := norm_sub_le
    (∑ n ∈ Finset.Icc 1 (N - 1),
      (vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * Complex.I))
    ((((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n) - (N : ℝ) : ℝ) : ℂ) /
      (N : ℂ) ^ ((σ : ℂ) + t * Complex.I))
  unfold Decomp122b.backlundRhs
  linarith

end LeanLab.ChirreHagen2025.Decomp272c
