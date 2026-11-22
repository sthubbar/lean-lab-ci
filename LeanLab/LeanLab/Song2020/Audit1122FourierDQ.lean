/-
AI wrote the Lean code. CLAUDE S47 burst-20261122, unit P1122-0154, 2026-11-22.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, printed pages 3 to 5, Lemma 1 and the S2 bound.
Audit of `Flag1734.fourierApproxDQ_match`: the named hypothesis `Flag1734.FourierApproxDQ`,
the re-cut of the sealed step `Decomp139.fourier_approximation`, is PROVED: the two leaves
`weighted_window_bound` and `exponent_pair_half` of `Prep1121FourierS2` are closed on main, so the
assembly `Prep1121FourierS2.fourier_approximation_of_leaves` has axioms propext, Classical.choice
and Quot.sound only. No existing file is changed and no
sorry is added. Binary Goldbach is open.
-/
import LeanLab.Song2020.Flag1734
import LeanLab.Song2020.Prep1121FourierS2

namespace LeanLab.Song2020.Audit1122FourierDQ

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Song2020.Decomp139

/-- PROVED. Song 2020 pages 3 to 5, Lemma 1 with the S2 bound: the named hypothesis
`FourierApproxDQ` of Flag1734 holds, by the closed split in Prep1121FourierS2. -/
theorem fourierApproxDQ_of_leaves : Flag1734.FourierApproxDQ :=
  Prep1121FourierS2.fourier_approximation_of_leaves

/-- The same, read through the match theorem of Flag1734: the right side of
`fourierApproxDQ_match` is the exact type of the sealed `Decomp139.fourier_approximation`. -/
theorem fourier_approximation_type_of_leaves :
    type_of% @LeanLab.Song2020.Decomp139.fourier_approximation :=
  Flag1734.fourierApproxDQ_match.mp fourierApproxDQ_of_leaves

end LeanLab.Song2020.Audit1122FourierDQ

#print axioms LeanLab.Song2020.Audit1122FourierDQ.fourierApproxDQ_of_leaves
#print axioms LeanLab.Song2020.Audit1122FourierDQ.fourier_approximation_type_of_leaves
