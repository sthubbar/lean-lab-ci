import LeanLab.Ported.Prove2Me.Def_axler_theta_chain_base

/-!
Upper state comparisons on the existing Prove2Me Axler blocks.
Source Schoenfeld 1976 page 356 display 5.1 star, derived finite checker.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task666
open LeanLab.Ported.Prove2Me.Task666
open AxlerChain AxlerTheta RosserSieveData RosserFastCompute RosserScan
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def guardGo (A gbase m : ℕ) : ℕ → List Blk → Bool
  | _, [] => true
  | U, B :: rest =>
    let cnt := bitCount (depthFor (B.2.1 - B.1))
      (m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1))
    forceNat (U + cnt * logUpNum B.2.1) fun U' =>
      (if B.2.1 ≤ A then true else
        decide (U' * 100000 < 100063 * scale * max B.1 A)) &&
      guardGo A gbase m U' rest

def guardGroup (A : ℕ) (G : Grp) : Bool :=
  forceNat (mask G.1 G.2.1) fun m => guardGo A G.1 m G.2.2.2.1 G.2.2.2.2.2.2

end LeanLab.LiuWang2002.Task666
