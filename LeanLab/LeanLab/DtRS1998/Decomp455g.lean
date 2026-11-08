/-
AI wrote this Lean code for CODEX task455.
P0037 Section 5.2 page 212, bit array sieve paragraph.
Table 2 page 214 row 300. These are alternative certificate windows.
Every small prime is kernel checked. No large prime is asserted here.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455gWindows0
import LeanLab.DtRS1998.Decomp455gWindows1
import LeanLab.DtRS1998.Decomp455gWindows2
import LeanLab.DtRS1998.Decomp455gWindows3
import LeanLab.DtRS1998.Decomp455gWindows4
import LeanLab.DtRS1998.Decomp455gWindows5
import LeanLab.DtRS1998.Decomp455gWindows6
import LeanLab.DtRS1998.Decomp455gWindows7
import LeanLab.DtRS1998.Decomp455gWindows8
import LeanLab.DtRS1998.Decomp455gWindows9
import LeanLab.DtRS1998.Decomp455gWindows10
import LeanLab.DtRS1998.Decomp455gWindows11
import LeanLab.DtRS1998.Decomp455gWindows12
import LeanLab.DtRS1998.Decomp455gWindows13
import LeanLab.DtRS1998.Decomp455gWindows14
import LeanLab.DtRS1998.Decomp455gWindows15
import LeanLab.DtRS1998.Decomp455gWindows16
import LeanLab.DtRS1998.Decomp455gWindows17
import LeanLab.DtRS1998.Decomp455gWindows18
import LeanLab.DtRS1998.Decomp455gWindows19
import LeanLab.DtRS1998.Decomp455gWindows20
import LeanLab.DtRS1998.Decomp455gWindows21
import LeanLab.DtRS1998.Decomp455gWindows22
import LeanLab.DtRS1998.Decomp455gWindows23
import LeanLab.DtRS1998.Decomp455gWindows24

namespace LeanLab.DtRS1998.Decomp455g

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
The complete lowest quarter of the fixed certificate has small prime complements.
This is exactly the sealed cover_block1 after unfolding offsets.
No 300 digit primality assertion is used. -/
theorem cover_block1 : ∀ j : ℕ, j < 125000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj
  by_cases h0 : j < 1000000
  · exact Decomp455f.prefix1 j (Nat.zero_le _) h0
  by_cases h1 : j < 2000000
  · exact window1 j (by omega) h1
  by_cases h2 : j < 3000000
  · exact window2 j (by omega) h2
  by_cases h3 : j < 4000000
  · exact window3 j (by omega) h3
  by_cases h4 : j < 5000000
  · exact window4 j (by omega) h4
  by_cases h5 : j < 6000000
  · exact window5 j (by omega) h5
  by_cases h6 : j < 7000000
  · exact window6 j (by omega) h6
  by_cases h7 : j < 8000000
  · exact window7 j (by omega) h7
  by_cases h8 : j < 9000000
  · exact window8 j (by omega) h8
  by_cases h9 : j < 10000000
  · exact window9 j (by omega) h9
  by_cases h10 : j < 11000000
  · exact window10 j (by omega) h10
  by_cases h11 : j < 12000000
  · exact window11 j (by omega) h11
  by_cases h12 : j < 13000000
  · exact window12 j (by omega) h12
  by_cases h13 : j < 14000000
  · exact window13 j (by omega) h13
  by_cases h14 : j < 15000000
  · exact window14 j (by omega) h14
  by_cases h15 : j < 16000000
  · exact window15 j (by omega) h15
  by_cases h16 : j < 17000000
  · exact window16 j (by omega) h16
  by_cases h17 : j < 18000000
  · exact window17 j (by omega) h17
  by_cases h18 : j < 19000000
  · exact window18 j (by omega) h18
  by_cases h19 : j < 20000000
  · exact window19 j (by omega) h19
  by_cases h20 : j < 21000000
  · exact window20 j (by omega) h20
  by_cases h21 : j < 22000000
  · exact window21 j (by omega) h21
  by_cases h22 : j < 23000000
  · exact window22 j (by omega) h22
  by_cases h23 : j < 24000000
  · exact window23 j (by omega) h23
  by_cases h24 : j < 25000000
  · exact window24 j (by omega) h24
  by_cases h25 : j < 26000000
  · exact window25 j (by omega) h25
  by_cases h26 : j < 27000000
  · exact window26 j (by omega) h26
  by_cases h27 : j < 28000000
  · exact window27 j (by omega) h27
  by_cases h28 : j < 29000000
  · exact window28 j (by omega) h28
  by_cases h29 : j < 30000000
  · exact window29 j (by omega) h29
  by_cases h30 : j < 31000000
  · exact window30 j (by omega) h30
  by_cases h31 : j < 32000000
  · exact window31 j (by omega) h31
  by_cases h32 : j < 33000000
  · exact window32 j (by omega) h32
  by_cases h33 : j < 34000000
  · exact window33 j (by omega) h33
  by_cases h34 : j < 35000000
  · exact window34 j (by omega) h34
  by_cases h35 : j < 36000000
  · exact window35 j (by omega) h35
  by_cases h36 : j < 37000000
  · exact window36 j (by omega) h36
  by_cases h37 : j < 38000000
  · exact window37 j (by omega) h37
  by_cases h38 : j < 39000000
  · exact window38 j (by omega) h38
  by_cases h39 : j < 40000000
  · exact window39 j (by omega) h39
  by_cases h40 : j < 41000000
  · exact window40 j (by omega) h40
  by_cases h41 : j < 42000000
  · exact window41 j (by omega) h41
  by_cases h42 : j < 43000000
  · exact window42 j (by omega) h42
  by_cases h43 : j < 44000000
  · exact window43 j (by omega) h43
  by_cases h44 : j < 45000000
  · exact window44 j (by omega) h44
  by_cases h45 : j < 46000000
  · exact window45 j (by omega) h45
  by_cases h46 : j < 47000000
  · exact window46 j (by omega) h46
  by_cases h47 : j < 48000000
  · exact window47 j (by omega) h47
  by_cases h48 : j < 49000000
  · exact window48 j (by omega) h48
  by_cases h49 : j < 50000000
  · exact window49 j (by omega) h49
  by_cases h50 : j < 51000000
  · exact window50 j (by omega) h50
  by_cases h51 : j < 52000000
  · exact window51 j (by omega) h51
  by_cases h52 : j < 53000000
  · exact window52 j (by omega) h52
  by_cases h53 : j < 54000000
  · exact window53 j (by omega) h53
  by_cases h54 : j < 55000000
  · exact window54 j (by omega) h54
  by_cases h55 : j < 56000000
  · exact window55 j (by omega) h55
  by_cases h56 : j < 57000000
  · exact window56 j (by omega) h56
  by_cases h57 : j < 58000000
  · exact window57 j (by omega) h57
  by_cases h58 : j < 59000000
  · exact window58 j (by omega) h58
  by_cases h59 : j < 60000000
  · exact window59 j (by omega) h59
  by_cases h60 : j < 61000000
  · exact window60 j (by omega) h60
  by_cases h61 : j < 62000000
  · exact window61 j (by omega) h61
  by_cases h62 : j < 63000000
  · exact window62 j (by omega) h62
  by_cases h63 : j < 64000000
  · exact window63 j (by omega) h63
  by_cases h64 : j < 65000000
  · exact window64 j (by omega) h64
  by_cases h65 : j < 66000000
  · exact window65 j (by omega) h65
  by_cases h66 : j < 67000000
  · exact window66 j (by omega) h66
  by_cases h67 : j < 68000000
  · exact window67 j (by omega) h67
  by_cases h68 : j < 69000000
  · exact window68 j (by omega) h68
  by_cases h69 : j < 70000000
  · exact window69 j (by omega) h69
  by_cases h70 : j < 71000000
  · exact window70 j (by omega) h70
  by_cases h71 : j < 72000000
  · exact window71 j (by omega) h71
  by_cases h72 : j < 73000000
  · exact window72 j (by omega) h72
  by_cases h73 : j < 74000000
  · exact window73 j (by omega) h73
  by_cases h74 : j < 75000000
  · exact window74 j (by omega) h74
  by_cases h75 : j < 76000000
  · exact window75 j (by omega) h75
  by_cases h76 : j < 77000000
  · exact window76 j (by omega) h76
  by_cases h77 : j < 78000000
  · exact window77 j (by omega) h77
  by_cases h78 : j < 79000000
  · exact window78 j (by omega) h78
  by_cases h79 : j < 80000000
  · exact window79 j (by omega) h79
  by_cases h80 : j < 81000000
  · exact window80 j (by omega) h80
  by_cases h81 : j < 82000000
  · exact window81 j (by omega) h81
  by_cases h82 : j < 83000000
  · exact window82 j (by omega) h82
  by_cases h83 : j < 84000000
  · exact window83 j (by omega) h83
  by_cases h84 : j < 85000000
  · exact window84 j (by omega) h84
  by_cases h85 : j < 86000000
  · exact window85 j (by omega) h85
  by_cases h86 : j < 87000000
  · exact window86 j (by omega) h86
  by_cases h87 : j < 88000000
  · exact window87 j (by omega) h87
  by_cases h88 : j < 89000000
  · exact window88 j (by omega) h88
  by_cases h89 : j < 90000000
  · exact window89 j (by omega) h89
  by_cases h90 : j < 91000000
  · exact window90 j (by omega) h90
  by_cases h91 : j < 92000000
  · exact window91 j (by omega) h91
  by_cases h92 : j < 93000000
  · exact window92 j (by omega) h92
  by_cases h93 : j < 94000000
  · exact window93 j (by omega) h93
  by_cases h94 : j < 95000000
  · exact window94 j (by omega) h94
  by_cases h95 : j < 96000000
  · exact window95 j (by omega) h95
  by_cases h96 : j < 97000000
  · exact window96 j (by omega) h96
  by_cases h97 : j < 98000000
  · exact window97 j (by omega) h97
  by_cases h98 : j < 99000000
  · exact window98 j (by omega) h98
  by_cases h99 : j < 100000000
  · exact window99 j (by omega) h99
  by_cases h100 : j < 101000000
  · exact window100 j (by omega) h100
  by_cases h101 : j < 102000000
  · exact window101 j (by omega) h101
  by_cases h102 : j < 103000000
  · exact window102 j (by omega) h102
  by_cases h103 : j < 104000000
  · exact window103 j (by omega) h103
  by_cases h104 : j < 105000000
  · exact window104 j (by omega) h104
  by_cases h105 : j < 106000000
  · exact window105 j (by omega) h105
  by_cases h106 : j < 107000000
  · exact window106 j (by omega) h106
  by_cases h107 : j < 108000000
  · exact window107 j (by omega) h107
  by_cases h108 : j < 109000000
  · exact window108 j (by omega) h108
  by_cases h109 : j < 110000000
  · exact window109 j (by omega) h109
  by_cases h110 : j < 111000000
  · exact window110 j (by omega) h110
  by_cases h111 : j < 112000000
  · exact window111 j (by omega) h111
  by_cases h112 : j < 113000000
  · exact window112 j (by omega) h112
  by_cases h113 : j < 114000000
  · exact window113 j (by omega) h113
  by_cases h114 : j < 115000000
  · exact window114 j (by omega) h114
  by_cases h115 : j < 116000000
  · exact window115 j (by omega) h115
  by_cases h116 : j < 117000000
  · exact window116 j (by omega) h116
  by_cases h117 : j < 118000000
  · exact window117 j (by omega) h117
  by_cases h118 : j < 119000000
  · exact window118 j (by omega) h118
  by_cases h119 : j < 120000000
  · exact window119 j (by omega) h119
  by_cases h120 : j < 121000000
  · exact window120 j (by omega) h120
  by_cases h121 : j < 122000000
  · exact window121 j (by omega) h121
  by_cases h122 : j < 123000000
  · exact window122 j (by omega) h122
  by_cases h123 : j < 124000000
  · exact window123 j (by omega) h123
  exact window124 j (by omega) hj

#print axioms cover_block1

end LeanLab.DtRS1998.Decomp455g
