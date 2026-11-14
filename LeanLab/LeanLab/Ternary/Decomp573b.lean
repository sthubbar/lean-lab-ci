/-
Helfgott https://arxiv.org/abs/1312.7748v2 page 51.
Parseval for the absolutely convergent remainder series.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp573a
import LeanLab.Ternary.MMSBohrSmoothing

namespace LeanLab.Ternary.Task573
open MeasureTheory
open scoped ComplexConjugate
open LeanLab.Ternary.MMS

/-- Parseval for the absolutely summable natural index character series.
Helfgott page 51 last display for the remainder coefficients. -/
theorem charSeries_parseval (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) :
    (∫ α in Set.Ioc (0 : ℝ) 1, ‖Task420.charSeries a α‖ ^ 2) = ∑' n, ‖a n‖ ^ 2 := by
  have hpair : Summable fun i : ℕ × ℕ => ‖a i.1 * conj (a i.2)‖ := by
    simpa only [norm_mul, Complex.norm_conj] using ha.mul_norm ha
  have hexp (α : ℝ) :
      ((‖Task420.charSeries a α‖ ^ 2 : ℝ) : ℂ) =
        ∑' i : ℕ × ℕ, (a i.1 * conj (a i.2)) * e ((((i.1 : ℤ) - i.2 : ℤ) : ℝ) * α) := by
    have ha' : Summable fun n => ‖a n * e ((n : ℝ) * α)‖ := by
      simpa only [norm_mul, norm_e, mul_one] using ha
    have hb' : Summable fun n => ‖conj (a n * e ((n : ℝ) * α))‖ := by
      simpa only [Complex.norm_conj] using ha'
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    unfold Task420.charSeries
    rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm ha' hb']
    apply tsum_congr
    intro i
    rw [map_mul, conj_e]
    have he : e ((i.1 : ℝ) * α) * e (-((i.2 : ℝ) * α)) =
        e ((((i.1 : ℤ) - i.2 : ℤ) : ℝ) * α) := by
      rw [← e_add]
      congr 1
      push_cast
      ring
    calc
      _ = (a i.1 * conj (a i.2)) *
          (e ((i.1 : ℝ) * α) * e (-((i.2 : ℝ) * α))) := by ring
      _ = _ := by rw [he]
  have h := Task420.integral_l1_characters
    (fun i : ℕ × ℕ => a i.1 * conj (a i.2))
    (fun i : ℕ × ℕ => (i.1 : ℤ) - i.2) hpair
  have hd : Summable fun i : ℕ × ℕ =>
      if (i.1 : ℤ) - i.2 = 0 then a i.1 * conj (a i.2) else 0 := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => by split_ifs <;> simp <;> positivity) hpair
  have hdiag : (∑' i : ℕ × ℕ, if (i.1 : ℤ) - i.2 = 0 then
      a i.1 * conj (a i.2) else 0) = ∑' n, a n * conj (a n) := by
    rw [hd.tsum_prod]
    apply tsum_congr
    intro n
    rw [tsum_eq_single n]
    · simp
    · intro m hm
      have hne : (n : ℤ) - m ≠ 0 := by omega
      simp [hne]
  have hdiag' : (∑' i : ℕ × ℕ, if (i.1 : ℤ) - i.2 = 0 then
      a i.1 * conj (a i.2) else 0) = ((∑' n, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [hdiag, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hdiag'] at h
  have hnorm : (fun α => ((‖Task420.charSeries a α‖ ^ 2 : ℝ) : ℂ)) =
      (fun α => ∑' i : ℕ × ℕ, (a i.1 * conj (a i.2)) *
        e ((((i.1 : ℤ) - i.2 : ℤ) : ℝ) * α)) := funext hexp
  rw [← hnorm, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

end LeanLab.Ternary.Task573
