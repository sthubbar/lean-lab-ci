/-
P0069 Baker Harman Pintz 1997, page 22, the right edge of the strip
in the horizontal contour estimate. Absolute convergence gives a bound
independent of the character and its modulus.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.Repair499Euler
open MeasureTheory Set

/-- Page 22, the elementary zeta majorant at a real argument above one. -/
theorem pseries_le (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ha : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Ici 1) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one ha) hab (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun t : ℝ => t ^ (-σ)) 1
    (by simpa using ha)
    (integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) (by norm_num : (0 : ℝ) < (1 : ℕ)))
    (fun t ht => Real.rpow_nonneg
      (le_trans (by norm_num : (0 : ℝ) ≤ (1 : ℕ)) ht.le) (-σ))
  norm_num only [Nat.cast_one] at htail
  rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) zero_lt_one,
    Real.one_rpow] at htail
  have htail' : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-σ)) ≤ 1 / (σ - 1) := by
    have he : -1 / (-σ + 1) = 1 / (σ - 1) := by
      field_simp [show σ - 1 ≠ 0 by linarith, show -σ + 1 ≠ 0 by linarith]
      ring
    simpa only [Nat.add_assoc, Nat.reduceAdd, he] using htail
  have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) :=
    (summable_nat_add_iff 1).mpr hs
  rw [hs.tsum_eq_zero_add, hshift.tsum_eq_zero_add]
  simp only [Nat.cast_zero, Nat.cast_one, Real.one_rpow,
    Real.zero_rpow (by linarith : -σ ≠ 0), zero_add, Nat.add_assoc]
  linarith

/-- Page 22, the right-edge majorant: bounded character coefficients
are dominated by the convergent real p-series. -/
theorem LFunction_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : ‖χ.LFunction s‖ ≤ 1 + 1 / (s.re - 1) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hb : ∀ n : ℕ, ‖LSeries.term (fun k => χ (k : ZMod q)) s n‖ ≤
      (n : ℝ) ^ (-s.re) := by
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst n
      simp [Real.zero_rpow (by linarith : -s.re ≠ 0)]
    · rw [ite_eq_right hn, Real.rpow_neg (Nat.cast_nonneg n)]
      simpa only [one_div] using
        div_le_div_of_nonneg_right (χ.norm_le_one (n : ZMod q))
          (Real.rpow_nonneg (Nat.cast_nonneg n) s.re)
  have hnorm : Summable (fun n => ‖LSeries.term (fun k => χ (k : ZMod q)) s n‖) :=
    hsum.of_nonneg_of_le (fun n => norm_nonneg _) hb
  rw [χ.LFunction_eq_LSeries hs]
  exact (norm_tsum_le_tsum_norm hnorm).trans
    ((hnorm.tsum_le_tsum hb hsum).trans (pseries_le s.re hs))

end LeanLab.BHP1997.Repair499Euler

namespace LeanLab.BHP1997.Repair499Euler

/-- Page 22, at the right edge sigma equals one plus the reciprocal
of log x. The absolute-convergence bound is at most a constant times log x. -/
theorem right_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ (q : ℕ) [NeZero q],
      ∀ χ : DirichletCharacter ℂ q, ∀ u : ℝ,
        ‖χ.LFunction (((1 + 1 / Real.log x : ℝ) : ℂ) + u * Complex.I)‖ ≤
          C * Real.log x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + 1 / Real.log 2, by positivity, ?_⟩
  intro x hx q _ χ u
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hh := LFunction_norm_le χ
    (s := (((1 + 1 / Real.log x : ℝ) : ℂ) + u * Complex.I)) (by simp; positivity)
  have hb : ‖χ.LFunction (((1 + 1 / Real.log x : ℝ) : ℂ) + u * Complex.I)‖ ≤
      1 + Real.log x := by
    simpa using hh
  have hlo : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h1 : 1 ≤ Real.log x / Real.log 2 := (le_div_iff₀ hlog2).mpr (by simpa using hlo)
  calc _ ≤ 1 + Real.log x := hb
    _ ≤ Real.log x / Real.log 2 + Real.log x := by linarith only [h1]
    _ = (1 + 1 / Real.log 2) * Real.log x := by ring

end LeanLab.BHP1997.Repair499Euler
