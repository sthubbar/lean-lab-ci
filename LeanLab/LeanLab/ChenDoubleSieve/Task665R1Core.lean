import LeanLab.Ported.Prove2Me.Decomp587jR1J16

/-!
The row two D2,17 checker for Wu 2004 page 26 and Table 1 page 30.
The existing R1J16 verifier is from Prove2Me mission 87d77bf0.
The accepted theorem is LL_Decomp587j.r1j16_short.
Author kmehltretter82. Apache 2.0. Accepted 2026-11-19.
AI wrote the new bridge. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task665R1
open Wu04Functional Task587
open LeanLab.Ported.Prove2Me.Decomp587jR1J16.SolBuchstabR1J16

def j17Cell : Cell4 := .c31 A_num B_num B_num 432752

def checkJ17 (pa pb : Nat) (t : CTree) : Bool :=
  match evalTree pa pb t j17Cell with
  | some v => Nat.ble v 92979000
  | none => false

/-- An accepted tree bounds the exact row two D2,17 integral on its phi interval. -/
theorem j17_interval_bound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {pa pb : Nat} {t : CTree} {φ : ℝ}
    (hpa : (pa : ℝ) / D_grid ≤ φ) (hpb : φ ≤ (pb : ℝ) / D_grid)
    (hchk : checkJ17 pa pb t = true) :
    buchstabIntegral ω 2 (fun j => (r1j17_lo j : ℝ)) (fun j => (r1j17_hi j : ℝ)) φ ≤
      ((92979 / 1000000000) : ℝ) := by
  exact task665_r1j17_interval_bound hω hz hpa hpb hchk

end LeanLab.ChenDoubleSieve.Task665R1
#print axioms LeanLab.ChenDoubleSieve.Task665R1.j17_interval_bound
