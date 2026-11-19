/-
Ported from Prove2Me, mission 6d14203d.
Theorem LL_Decomp551a.primorial_c5_upper_second.
Author bwdaugherty. Accepted 2026-11-17. Apache 2.0.
The shared proof and certificate chain are imported from P2M655Assembly.
AI wrote the Lean code. Binary Goldbach is open.
-/

import LeanLab.LiuWang2002.P2M655Assembly

namespace LeanLab.Ported.Prove2Me.LL_Decomp551a

theorem primorial_c5_upper_second (n : ℕ) (hn : 28000000 < n) (hn' : n ≤ 32000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact LeanLab.LiuWang2002.P2M655.primorial_range_16m_32m n (by omega) (by omega)

end LeanLab.Ported.Prove2Me.LL_Decomp551a
#print axioms LeanLab.Ported.Prove2Me.LL_Decomp551a.primorial_c5_upper_second
