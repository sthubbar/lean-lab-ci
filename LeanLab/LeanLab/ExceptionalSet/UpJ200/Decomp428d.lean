import LeanLab.ExceptionalSet.UpJ200.Decomp428c

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.Decomp428d`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
Distant frequency supply for P0082 page 366 display 26.
The two smaller leaves isolate cancellation and integral localization.
The weighted prime energy is shared with the nearby frequency supply.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp428d

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp Kfun calE eC norm_eC)
open LeanLab.ExceptionalSet.UpJ200.Decomp404e

/-- Page 366 display 27. The full index phase sum is at most N.
This is the trivial bound used on the nearby strip. -/
theorem phaseSum_norm_le (γ : ℝ) (N : ℕ) (t : ℝ) : ‖phaseSum γ N t‖ ≤ N := by
  unfold phaseSum
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (N / 2) N, ‖eC (t * F γ n)‖ := norm_sum_le _ _
    _ = ((N - N / 2 : ℕ) : ℝ) := by simp only [norm_eC, sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc]
    _ ≤ N := by exact_mod_cast Nat.sub_le N (N / 2)

end LeanLab.ExceptionalSet.UpJ200.Decomp428d
