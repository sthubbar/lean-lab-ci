/-
P0032 U-6740, CLOUD 20261020T2113Z-cloud51. AI-written Lean code, Claude.
The sieve form of A equals its pack, from the four quarter checks.
-/
import LeanLab.RieselVaughan1983.T230Gen.SieveA0
import LeanLab.RieselVaughan1983.T230Gen.SieveA1
import LeanLab.RieselVaughan1983.T230Gen.SieveA1z

namespace LeanLab.RieselVaughan1983.Table230BigEval

open LeanLab.RieselVaughan1983 LeanLab.RieselVaughan1983.Table230Big

/-- The sieve form of `A` is the pack. -/
theorem As_eq : As = pack fa 17 0 :=
  pack_split fa 16 0 65536 _ (by norm_num)
    (pack_split fa 15 0 32768 _ (by norm_num) Aq0 Aq1)
    (pack_split fa 15 65536 98304 _ (by norm_num) Aq2 Aq3)

end LeanLab.RieselVaughan1983.Table230BigEval
