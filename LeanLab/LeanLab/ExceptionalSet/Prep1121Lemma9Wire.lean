/-
P0082 J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst. Fourier 48
(1998) 353-378. The main result, Theorem 1, wired to the named citation walls of the lane and
to the one remaining section 6 moment input.

The lane already holds each piece, and the top assembly is fed here by terms:
  * Lemma 10, page 370-371, from Karacuba 1971 Theorem 1, p. 244, `KaracubaThm1Named`;
  * Lemma 4, page 359, from the Erdős-Turán inequality `ErdosTuranDQ4` and Lemma 10;
  * Lemma 9, page 368, from those two, through the page 370 trapezoid;
  * the pointwise character cases of pages 362 to 364, from the six DQ case hypotheses;
  * the page 354 and page 366 assembly of `Decomp467c`.

The fourth analytic input of that assembly, the odd coefficient second moment of pages 366 to
369, displays 29 and 30, is NOT supplied: its only source in the tree is
`Decomp371c.leaf_odd_moment`, a `sorry` leaf, and every split of it weakens a statement it still
imports. It is therefore kept as an explicit hypothesis below, so that nothing admitted enters
the axioms of any statement in this file. That moment is the missing input of this wire.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.Decomp467c
import LeanLab.ExceptionalSet.UpJ200.DQDecomp559bRoute
import LeanLab.ExceptionalSet.DQLemma4Decisions
import LeanLab.ExceptionalSet.DQLemma10S1
import LeanLab.ExceptionalSet.DQLemma9Named

namespace LeanLab.ExceptionalSet.Prep1121Lemma9Wire

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Theorem1)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE Lemma4 Lemma9 Lemma10)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- Lemma 10 of P0082, pages 370 and 371, Karacuba's Theorem 1 with the change of notation,
from the cited Karacuba 1971 Theorem 1, p. 244, only. CONDITIONAL ON `KaracubaThm1Named`. -/
theorem lemma10_of_named (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named) :
    Lemma10 :=
  LeanLab.ExceptionalSet.U1539.DQLemma10.lemma10_of_karacuba_named hK

/-- Lemma 4 of P0082, page 359, from the cited Erdős-Turán inequality in the explicit
Kuipers-Niederreiter form `ErdosTuranDQ4` and Lemma 10 through Theorem 2.
CONDITIONAL ON `ErdosTuranDQ4` and `KaracubaThm1Named`. -/
theorem lemma4_of_named (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4)
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named) : Lemma4 :=
  LeanLab.ExceptionalSet.DQLemma4.lemma4_of_erdosTuran_lemma10 hET (lemma10_of_named hK)

/-- Lemma 9 of P0082, page 368, proved on page 370: a large value of the even phase sum
localizes near a half integer with a bounded height. CONDITIONAL ON `ErdosTuranDQ4` and
`KaracubaThm1Named`. -/
theorem lemma9_of_named (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4)
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named) : Lemma9 :=
  LeanLab.ExceptionalSet.DQLemma9Named.lemma9_of_named hET hK

/-- Theorem 1 of P0082, page 354: for `1 < γ < 3/2` the number of `n ≤ N` whose even neighbour
of `F γ n` is not a sum of two odd primes is at most `C N exp(-c (log N)^{3-2γ})`, with `c` and
`C` effective. The page 366 block bound is fed by Lemma 4 and Lemma 10 above and by the pointwise
character cases of the six DQ case hypotheses. CONDITIONAL ON `ErdosTuranDQ4`,
`KaracubaThm1Named`, those six hypotheses and the odd second moment `hodd`. -/
theorem main_theorem_of_named (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4)
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (hL : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.Lemma2NoExcBP)
    (hSa : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.SingularSeriesEvenLowerBP)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.BPLemma3CoprimeHyp)
    (hH : LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected.PrimeProductSelectedP0082)
    (hII : LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.CaseIIdMajorLowerHyp)
    (hZ : LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.RealZeroDistanceHyp)
    (hodd : ∀ (γ : ℝ), 1 < γ → γ < 3 / 2 →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
          ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            (∑ n ∈ window γ N,
              ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)‖ ^ 2) ≤
                B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) :
    Theorem1 :=
  LeanLab.ExceptionalSet.Decomp467c.brudernPerelli_from_inputs
    (fun γ h1 h2 =>
      LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.pointwise_lower_of_hyps
        hL hSa hL3 hH hII hZ γ h1 h2)
    (lemma4_of_named hET hK)
    hodd
    (lemma10_of_named hK)

end LeanLab.ExceptionalSet.Prep1121Lemma9Wire

