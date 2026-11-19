import LeanLab.LiuWang2002.P2M655Data06
import LeanLab.LiuWang2002.P2M655Data08
import LeanLab.LiuWang2002.P2M655Data13

/-!
A negative result for the coarse endpoint interpolation route.
Source Schoenfeld 1976 page 356 display 5.1 star, derived certificate checks.
The data are from Prove2Me mission 6d14203d, author bwdaugherty, Apache 2.0.
This compares sufficient integer bounds. It asserts no paper error.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task655
open P2M655.ThetaSieve

/-- The coarse record endpoint upper bounds fail the fixed point comparison
at the three initial endpoints that the earlier checkpoint supplies require. -/
theorem coarse_endpoints_fail :
    (6000000 : ℕ) * (LLo 68 - LHi 25) < (Seg.hi' PrimData6.s3) ∧
    (8000000 : ℕ) * (LLo 68 - LHi 25) < (Seg.hi' PrimData8.s5) ∧
    (12000000 : ℕ) * (LLo 68 - LHi 25) < (Seg.hi' PrimData13.s0) := by
  first | exact? | decide +kernel

end LeanLab.LiuWang2002.Task655

#print axioms LeanLab.LiuWang2002.Task655.coarse_endpoints_fail
