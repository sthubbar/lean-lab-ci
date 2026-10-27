/-
U-1437 timing sample: ten windows of 990000 over even and odd N in [987040002, 996940000], the span of Top50/BitVG68.
AI-written Lean code, Claude, run 20261021T1603Z-28836. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.U1437Fast.Sieve

set_option Elab.async false

namespace LeanLab.Verifications.U1437Fast

open LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem t10_win0 : tm 987039949 987040002 988030001 &&& gm (sfm 987039949 990052) (P10k.take 16) = tm 987039949 987040002 988030001 := by
  decide +kernel

theorem t10_win1 : tm 988029949 988030002 989020001 &&& gm (sfm 988029949 990052) (P10k.take 16) = tm 988029949 988030002 989020001 := by
  decide +kernel

theorem t10_win2 : tm 989019949 989020002 990010001 &&& gm (sfm 989019949 990052) (P10k.take 16) = tm 989019949 989020002 990010001 := by
  decide +kernel

theorem t10_win3 : tm 990009949 990010002 991000001 &&& gm (sfm 990009949 990052) (P10k.take 16) = tm 990009949 990010002 991000001 := by
  decide +kernel

theorem t10_win4 : tm 990999949 991000002 991990001 &&& gm (sfm 990999949 990052) (P10k.take 16) = tm 990999949 991000002 991990001 := by
  decide +kernel

theorem t10_win5 : tm 991989949 991990002 992980001 &&& gm (sfm 991989949 990052) (P10k.take 16) = tm 991989949 991990002 992980001 := by
  decide +kernel

theorem t10_win6 : tm 992979949 992980002 993970001 &&& gm (sfm 992979949 990052) (P10k.take 16) = tm 992979949 992980002 993970001 := by
  decide +kernel

theorem t10_win7 : tm 993969949 993970002 994960001 &&& gm (sfm 993969949 990052) (P10k.take 16) = tm 993969949 993970002 994960001 := by
  decide +kernel

theorem t10_win8 : tm 994959949 994960002 995950001 &&& gm (sfm 994959949 990052) (P10k.take 16) = tm 994959949 994960002 995950001 := by
  decide +kernel

theorem t10_win9 : tm 995949949 995950002 996940001 &&& gm (sfm 995949949 990052) (P10k.take 16) = tm 995949949 995950002 996940001 := by
  decide +kernel

end LeanLab.Verifications.U1437Fast
