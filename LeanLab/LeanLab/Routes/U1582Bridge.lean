/-
U-1582, cloud run 20261028T0803Z-11675, idea I-0138. AI wrote this Lean code.
Binary Goldbach is OPEN; nothing here is progress on it.

BUILT on main 2026-10-28 after the architect moved encoding A to Perelli1996/StatementsA,
namespace EncA; the note below is the earlier state. Earlier: NOT BUILT. This bridge imports `LeanLab.Routes.U1579Perelli`, which builds only on the PC,
where Perelli1996/Statements.lean carries `deg`, `nRange`, `err`, `F2`; in the clone at
a321cfd8 it fails with Unknown constant `LeanLab.Perelli1996.deg`. Claims nothing until a
PC build log exists. It instantiates U1582's abstract `ReductionAt` by U1579's
`PerelliReduction` at one polynomial F, k = deg F, Target = Thm1Exact F; the density
definitions of U1582 have the same bodies as U1579's, so the arguments pass by unfolding.

Plain math: Perelli 1996 Theorem 1 holds for H ≥ N^h, h > 2/(7k), and Theorem 2 for
h > 1/(7k), CONDITIONAL ON PerelliReduction or PerelliReduction2, Chen-Gupta-Li 7/3 and
Huxley's printed near one bound on [3/4, 1]; no LogFreeNearOne input.
-/
import Mathlib
import LeanLab.Routes.U1579Perelli
import LeanLab.Routes.U1582Huxley

namespace LeanLab.Routes.U1582Bridge
open Polynomial
open LeanLab.Perelli1996.EncA (Admissible deg)

/-- CONDITIONAL ON `U1579.PerelliReduction`, `U1579.ChenDensity`, `U1582.HuxleyNearOne (3/4)`:
Perelli's Theorem 1 at every H = N^h, h > 2/(7k). NOT BUILT. -/
theorem thm1_bridge (hR : U1579.PerelliReduction) (hZ : U1579.ChenDensity)
    (hH : U1582.HuxleyNearOne (3 / 4)) {F : ℤ[X]} (hF : Admissible F) {h : ℝ}
    (hh : 2 / (7 * deg F) < h) : U1579.Thm1Exact F h :=
  U1582.thm1_of_chen_huxley (k := deg F) (Target := U1579.Thm1Exact F)
    (fun A A' σ₀ hA hσ hZ' hL h h1 h2 => hR A A' σ₀ hA hσ hZ' hL F h h1 h2) hZ hH
    (U1579.deg_pos hF) hh

/-- CONDITIONAL ON `U1579.PerelliReduction2`, `U1579.ChenDensity`,
`U1582.HuxleyNearOne (3/4)`: Perelli's Theorem 2 at every H = N^h, h > 1/(7k). NOT BUILT. -/
theorem thm2_bridge (hR : U1579.PerelliReduction2) (hZ : U1579.ChenDensity)
    (hH : U1582.HuxleyNearOne (3 / 4)) {F : ℤ[X]} (hF : Admissible F) {h : ℝ}
    (hh : 1 / (7 * deg F) < h) : U1579.Thm2Exact F h :=
  U1582.thm2_of_chen_huxley (k := deg F) (Target := U1579.Thm2Exact F)
    (fun A A' σ₀ hA hσ hZ' hL h h1 h2 => hR A A' σ₀ hA hσ hZ' hL F h h1 h2) hZ hH
    (U1579.deg_pos hF) hh

end LeanLab.Routes.U1582Bridge
#print axioms LeanLab.Routes.U1582Bridge.thm1_bridge
#print axioms LeanLab.Routes.U1582Bridge.thm2_bridge
