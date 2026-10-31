/-
U-1437 timing sample: one window over even and odd N in [987040002, 996940000], the span of Top50/BitVG68.
AI-written Lean code, Claude, run 20261021T1603Z-28836. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.U1437Fast.Sieve

set_option Elab.async false

namespace LeanLab.Verifications.U1437Fast

open LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem t1_win : tm 987039949 987040002 996940000 &&& gm (sfm 987039949 9900051) (P10k.take 16) = tm 987039949 987040002 996940000 := by
  decide +kernel

end LeanLab.Verifications.U1437Fast
