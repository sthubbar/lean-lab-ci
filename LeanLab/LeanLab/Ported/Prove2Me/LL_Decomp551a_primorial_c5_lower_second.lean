/-
Ported from Prove2Me, mission 6d14203d.
Theorem LL_Decomp551a.primorial_c5_lower_second.
Author bwdaugherty. Accepted 2026-11-17. Apache 2.0.
The shared proof and certificate chain are imported from P2M655Range24.
AI wrote the Lean code. Binary Goldbach is open.
-/

import LeanLab.LiuWang2002.P2M655Range24

namespace LeanLab.Ported.Prove2Me.LL_Decomp551a

theorem primorial_c5_lower_second (n : ℕ) (hn : 20000000 < n) (hn' : n ≤ 24000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact LeanLab.LiuWang2002.P2M655.Range24.primorial_range n (by omega) (by omega)

end LeanLab.Ported.Prove2Me.LL_Decomp551a
#print axioms LeanLab.Ported.Prove2Me.LL_Decomp551a.primorial_c5_lower_second
