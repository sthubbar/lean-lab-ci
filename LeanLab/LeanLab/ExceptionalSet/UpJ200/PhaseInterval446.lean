import LeanLab.ExceptionalSet.UpJ200.Decomp428d

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.PhaseInterval446`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
Endpoint correction for the dyadic phase interval on P0082 page 366.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.PhaseInterval446

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (eC norm_eC expSumF)
open LeanLab.ExceptionalSet.UpJ200.Decomp404e (phaseSum)

/-- P0082 pages 354 and 366, application of Theorem 2.
Changing its closed interval to the half open dyadic phase interval
costs at most two unit modulus endpoint terms. -/
theorem phase_interval_norm_le (γ t : ℝ) (N : ℕ) :
    ‖phaseSum γ N t‖ ≤ ‖expSumF γ t (N / 2)‖ + 2 := by
  let m := N / 2
  let f : ℕ → ℂ := fun n => eC (t * F γ n)
  have hm : m ≤ 2 * m := by omega
  have he : (∑ n ∈ Ioc m (2 * m), f n) = expSumF γ t m - f m := by
    have hh := Finset.add_sum_Ioc_eq_sum_Icc (f := f) hm
    change f m + (∑ n ∈ Ioc m (2 * m), f n) = expSumF γ t m at hh
    linear_combination hh
  have hb : ‖∑ n ∈ Ioc m (2 * m), f n‖ ≤ ‖expSumF γ t m‖ + 1 := by
    rw [he]
    simpa only [f, norm_eC] using norm_sub_le (expSumF γ t m) (f m)
  have hN : N = 2 * m ∨ N = 2 * m + 1 := by dsimp [m]; omega
  change ‖∑ n ∈ Ioc m N, f n‖ ≤ ‖expSumF γ t m‖ + 2
  rcases hN with hN | hN
  · rw [hN]
    linarith
  · rw [hN, Finset.sum_Ioc_succ_top hm f]
    have hh := norm_add_le (∑ n ∈ Ioc m (2 * m), f n) (f (2 * m + 1))
    simp only [f, norm_eC] at hh
    linarith

end LeanLab.ExceptionalSet.UpJ200.PhaseInterval446
