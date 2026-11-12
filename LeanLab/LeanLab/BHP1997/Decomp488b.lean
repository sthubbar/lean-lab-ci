/-
P0069, page 22, Perron formula before display 3.36.
The L-series and interval integral interchange uses dominated convergence.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp488a
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace LeanLab.BHP1997.DecompC165a.Contour230
open Classical Complex MeanValue132 MeasureTheory Set
open scoped Topology

/-- LEAF. Page 22, Perron formula before display 3.36.
On a right line of absolute convergence, integration commutes with the L-series.
The finite interval and the regular kernel give a summable constant majorant. -/
theorem LSeries_integral_interchange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a b c H t : ℝ) (hc : 1 / 2 < c) :
    (∫ u in (-H)..H, integrand a b χ t ((c : ℂ) + u * I)) =
      ∑' n : ℕ, ∫ u in (-H)..H,
        LSeries.term (χ ·) (Thm4.half t + ((c : ℂ) + u * I)) n *
          kernel a b ((c : ℂ) + u * I) := by
  let K : ℝ → ℂ := fun u => kernel a b ((c : ℂ) + u * I)
  let s : ℝ → ℂ := fun u => Thm4.half t + ((c : ℂ) + u * I)
  have hK : Continuous K := (kernel_entire a b).continuous.comp (by fun_prop)
  have hs : Continuous s := by dsimp [s, Thm4.half]; fun_prop
  have hre (u : ℝ) : (s u).re = 1 / 2 + c := by simp [s, Thm4.half]
  have hsr (u : ℝ) : 1 < (s u).re := by rw [hre]; linarith
  obtain ⟨M, hM⟩ := (isCompact_uIcc.image hK.norm).bddAbove
  let B : ℝ := max M 0
  have hB : 0 ≤ B := le_max_right _ _
  have hKB (u : ℝ) (hu : u ∈ uIcc (-H) H) : ‖K u‖ ≤ B :=
    (hM ⟨u, hu, rfl⟩).trans (le_max_left _ _)
  have hpow : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 + c))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hterm (n : ℕ) (u : ℝ) :
      ‖LSeries.term (χ ·) (s u) n‖ ≤ (n : ℝ) ^ (-(1 / 2 + c)) := by
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [ite_true, Nat.cast_zero]
      exact Real.rpow_nonneg (by norm_num) _
    · simp only [Nat.ne_of_gt hn, ite_false, hre]
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ n)]
      simpa only [one_div] using
        div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity : 0 ≤ (n : ℝ) ^ (1 / 2 + c))
  have hcont (n : ℕ) : Continuous (fun u => LSeries.term (χ ·) (s u) n * K u) := by
    have htd : Differentiable ℂ (fun z : ℂ => LSeries.term (χ ·) z n) :=
      fun z => (LSeries.hasDerivAt_term (χ ·) n z).differentiableAt
    have htc := htd.continuous
    exact (htc.comp hs).mul hK
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := -H) (b := H) (μ := volume)
    (F := fun n u => LSeries.term (χ ·) (s u) n * K u)
    (f := fun u => integrand a b χ t ((c : ℂ) + u * I))
    (fun n _ => (n : ℝ) ^ (-(1 / 2 + c)) * B)
    (fun n => (hcont n).aestronglyMeasurable.restrict)
    (fun n => Filter.Eventually.of_forall (fun u hu => by
      rw [norm_mul]
      exact mul_le_mul (hterm n u) (hKB u (uIoc_subset_uIcc hu))
        (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)))
    (Filter.Eventually.of_forall (fun _ _ => hpow.mul_right B))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun u _ => by
      have hh := (χ.LSeriesSummable_of_one_lt_re (hsr u)).hasSum.mul_right (K u)
      change HasSum _ (LSeries (χ ·) (s u) * K u) at hh
      rw [← χ.LFunction_eq_LSeries (hsr u)] at hh
      exact hh))
  exact hsum.tsum_eq.symm

/-- Page 22, the interchange at the chosen abscissa and safe height. -/
theorem rightIntegral_eq_perronSeries {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 2 ≤ x) (N T t : ℝ) :
    rightIntegral x N T χ t = perronSeries x N T χ t := by
  unfold rightIntegral perronSeries
  congr 1
  apply LSeries_integral_interchange
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  linarith [one_div_pos.mpr hl]

end LeanLab.BHP1997.DecompC165a.Contour230
