import LeanLab.ChirreHagen2025.Decomp377b
import LeanLab.ChirreHagen2025.Decomp358c
import LeanLab.ChirreHagen2025.Decomp358d

/-!
P0075 pages 2 and 3, Lemma 2.1 with the proved Backlund identity.
Only the cited finite Mangoldt and Schoenfeld range inputs remain.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Backlund377
open MeasureTheory ArithmeticFunction Decomp122b

/-- P0075 page 3, the exact four-term reduction with the proved identity.
CONDITIONAL ON the two finite Mangoldt and two Schoenfeld range leaves. -/
theorem backlund_reduction (hRH : RiemannHypothesis) (σ t : ℝ)
    (hσ : 1 < σ) (hσtop : σ < 2) (ht : 100 ≤ |t|)
    (N : ℕ) (hN : 74 ≤ N) :
    ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      backlundRhs |t| N := by
  have hid := (Decomp377b.backlund_identity σ t hσ hσtop ht N hN).2
  have hsum := Decomp358d.finite_mangoldt_bound σ t hσ hσtop ht N hN
  have hboundary := Decomp358b.psi_boundary_bound hRH σ t hσ hσtop ht N hN
  have hpole := Decomp272c.pole_term_bound σ t hσ hσtop ht N hN
  have htail := Decomp358c.psi_tail_bound hRH σ t hσ hσtop ht N hN
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


/-- P0075 pages 2 and 3, Lemma 2.1 from the reduced analytic inputs.
CONDITIONAL ON the same four quantitative range leaves. -/
theorem lemma2_1_assembled : lemma2_1 := by
  intro hRH σ t hσ hσtop ht
  apply boundary_extension t ht (4 * Real.log |t|) ?_ σ hσ hσtop
  intro s hs hstop
  obtain ⟨hN, hnum⟩ := backlund_numeric |t| ht
  exact (backlund_reduction hRH s t hs hstop ht _ hN).trans hnum


end LeanLab.ChirreHagen2025.Backlund377
