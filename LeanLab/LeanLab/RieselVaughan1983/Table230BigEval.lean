/-
P0032 Riesel-Vaughan 1983, (2.30) second value, `T(99989) ≤ 80096031`, PROVED by kernel computation.
Unit U-6740, CLOUD 20261020T2113Z-cloud51, track T1. AI-written Lean code, Claude. Checked only
by the Lean kernel, `decide +kernel`, no `native_decide`. Binary Goldbach is OPEN.

* `As_eq`, `Bs_eq`, in `T230Gen/SieveA` and `T230Gen/SieveB`: the sieve forms of the packed
  prime indicators equal the packs, whose meaning is `packA`, `packB` in `Table230Big`.
* `chunk_0` to `chunk_24`, in `T230Gen/Chunks0` to `Chunks8`: the 25 block values; their sum is
  88066516657397235646, against 80096031 · 2^40 = 88066517423206957056.
* `table230Big`: `T(99989) ≤ 80096031`. The exact value is 80096030.3034584..., margin 0.6965.
* `table230`: all of (2.30) and (2.31).
Generator of the literals: `T230Big_gen.py` in this folder.
-/
import LeanLab.RieselVaughan1983.Table230Big
import LeanLab.RieselVaughan1983.T230Gen.SieveA
import LeanLab.RieselVaughan1983.T230Gen.SieveB
import LeanLab.RieselVaughan1983.T230Gen.Chunks0
import LeanLab.RieselVaughan1983.T230Gen.Chunks1
import LeanLab.RieselVaughan1983.T230Gen.Chunks2
import LeanLab.RieselVaughan1983.T230Gen.Chunks3
import LeanLab.RieselVaughan1983.T230Gen.Chunks4
import LeanLab.RieselVaughan1983.T230Gen.Chunks5
import LeanLab.RieselVaughan1983.T230Gen.Chunks6
import LeanLab.RieselVaughan1983.T230Gen.Chunks7
import LeanLab.RieselVaughan1983.T230Gen.Chunks8

open Finset

namespace LeanLab.RieselVaughan1983.Table230BigEval

open LeanLab.RieselVaughan1983 LeanLab.RieselVaughan1983.Table230Small
  LeanLab.RieselVaughan1983.Table230Big

/-- The 25 blocks sum to 88066516657397235646 ≤ 80096031 · 2^40. -/
theorem chunks_le : ∑ j ∈ range 25, chunk j ≤ 80096031 * M := by
  simp only [sum_range_succ, sum_range_zero, chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5,
    chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15,
    chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23, chunk_24]
  unfold M
  norm_num

/-- **(2.30), second value**: `T(99989) ≤ 80096031`. -/
theorem table230Big : Table230Big := table230Big_of_eval As_eq Bs_eq chunks_le

/-- **(2.30) and (2.31)** in full. -/
theorem table230 : Table230 := table230_of_big table230Big

end LeanLab.RieselVaughan1983.Table230BigEval
