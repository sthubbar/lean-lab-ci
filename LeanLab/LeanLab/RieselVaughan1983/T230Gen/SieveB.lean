/-
P0032 U-6740, CLOUD 20261020T2113Z-cloud51. AI-written Lean code, Claude.
The sieve form of B equals its pack, from the four quarter checks.
-/
import LeanLab.RieselVaughan1983.T230Gen.SieveB0
import LeanLab.RieselVaughan1983.T230Gen.SieveB1

namespace LeanLab.RieselVaughan1983.Table230BigEval

open LeanLab.RieselVaughan1983 LeanLab.RieselVaughan1983.Table230Big

/-- The sieve form of `B` is the pack. -/
theorem Bs_eq : Bs = pack fb 17 0 :=
  pack_split fb 16 0 65536 _ (by norm_num)
    (pack_split fb 15 0 32768 _ (by norm_num) Bq0 Bq1)
    (pack_split fb 15 65536 98304 _ (by norm_num) Bq2 Bq3)

end LeanLab.RieselVaughan1983.Table230BigEval
