import LeanLab.ExceptionalSet.Prep1122MainWire

/-!
P0082, J. Brüdern and A. Perelli, Ann. Inst. Fourier 48 (1998), doi 10.5802/aif.1621,
Theorem 1 page 354, assembled through pages 359 and 362 to 370.
Burst burst-20261122 unit P1122-0115, the top theorem wiring through lemma 9, lemma 4 and
lemma 10.

`Prep1122MainWire.theorem1_of_named_citation_walls` proves `Theorem1` from six named walls,
one of them the Erdős–Turán wall `ErdosTuranDQ4`, used there only to produce `Lemma4`.
`Prep1121Lemma9Wire.lemma4_of_karacuba` proves `Lemma4` from `KaracubaThm1Named` alone, through
the one-sided Beurling–Selberg majorant of `Selberg524`. The result below replays the six-wall
assembly with that `Lemma4` and with `Prep1121Lemma9Wire.lemma9_of_karacuba` for `Lemma9`, so
`Theorem1` is CONDITIONAL ON five named citation walls. No sealed declaration is changed, nothing
is admitted and no new definition is made. The constant `c` obtained is ineffective: the real
zero input `Task672.realZeroDistanceHyp_proved672` comes from the Siegel theorem.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Prep1122Theorem1FiveWalls

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable Theorem1)
open LeanLab.ExceptionalSet.Prep1122MainWire

/-- P0082 page 354 Theorem 1, assembled through pages 359 and 362 to 370.
CONDITIONAL ON exactly five named citation walls: Karacuba 1971 Theorem 1, the nonexceptional
major formula of Lemma 2, the coprime major formula of Lemma 3, the prime product case and the
near-zero major formula. The Erdős–Turán wall of `theorem1_of_named_citation_walls` is
discharged by `Prep1121Lemma9Wire.lemma4_of_karacuba`. -/
theorem theorem1_of_five_citation_walls
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (hL : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.Lemma2NoExcBP)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.BPLemma3CoprimeHyp)
    (hP : LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected.PrimeProductSelectedP0082)
    (hII : LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.CaseIIdMajorLowerHyp) :
    Theorem1 := by
  have h10 := LeanLab.ExceptionalSet.U1539.DQLemma10.lemma10_of_karacuba_named hK
  have h4 := LeanLab.ExceptionalSet.Prep1121Lemma9Wire.lemma4_of_karacuba hK
  have h9 := LeanLab.ExceptionalSet.Prep1121Lemma9Wire.lemma9_of_karacuba hK
  have hadj := LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.adjacent_count_of_hyps
    h4 hL LeanLab.ExceptionalSet.UpJ200.Prep1121SingSeries.singularSeriesEvenLowerBP_split
    hL3 hP hII LeanLab.ExceptionalSet.Task672.realZeroDistanceHyp_proved672
  have hcoeff := coefficient_lower_of_inputs hadj (odd_moment_of_inputs h4 h9 h10)
  have hmajor := major_bound_of_inputs hcoeff h4
  have hminor := minor_bound_of_lemma10 h10
  intro γ h1 h2
  obtain ⟨κ, B, hκ, hB, N₀, hblock⟩ :=
    block_bound_of_arc_inputs hmajor hminor γ h1 h2
  obtain ⟨c, hc, C, hC, M₀, hdyadic⟩ :=
    LeanLab.ExceptionalSet.DecompJ200.leaf_block_dissection γ κ B h1 h2 hκ hB
      (fun n => ¬ Solvable γ n) N₀ hblock
  have heq (M : ℕ) : LeanLab.ExceptionalSet.DecompJ200.Eγ_dyadic γ M =
      LeanLab.ExceptionalSet.DecompJ200.dyadicCount (fun n => ¬ Solvable γ n) M := by
    unfold LeanLab.ExceptionalSet.DecompJ200.Eγ_dyadic
      LeanLab.ExceptionalSet.DecompJ200.dyadicCount
    congr!
  exact LeanLab.ExceptionalSet.DecompJ200.leaf_theorem1_from_sums γ h1 h2
    ⟨c, hc, C, hC, M₀, fun M hM => by rw [heq]; exact hdyadic M hM⟩
    (LeanLab.ExceptionalSet.DecompJ200.leaf_dyadic_trivial γ)
    (LeanLab.ExceptionalSet.DecompJ200.leaf_dyadic_sum γ)
    (LeanLab.ExceptionalSet.DecompJ200.leaf_dyadic_sum_exp γ h1 h2)

/-- P0082 page 354: density zero of the exceptional set for each `1 < γ < 3/2`,
CONDITIONAL ON the same five named citation walls. -/
theorem densityZero_of_five_citation_walls
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (hL : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.Lemma2NoExcBP)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.BPLemma3CoprimeHyp)
    (hP : LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected.PrimeProductSelectedP0082)
    (hII : LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.CaseIIdMajorLowerHyp)
    {γ : ℝ} (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    Tendsto (fun N : ℕ => (LeanLab.ExceptionalSet.BrudernPerelli1998.Eγ γ N : ℝ) / N)
      atTop (nhds 0) :=
  LeanLab.ExceptionalSet.BrudernPerelli1998.densityZero_of_theorem1
    (theorem1_of_five_citation_walls hK hL hL3 hP hII) h1 h2

#print axioms theorem1_of_five_citation_walls
#print axioms densityZero_of_five_citation_walls

end LeanLab.ExceptionalSet.Prep1122Theorem1FiveWalls
