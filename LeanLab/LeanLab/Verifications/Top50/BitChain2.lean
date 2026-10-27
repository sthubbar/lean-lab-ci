/-
Chain block 2 of the kernel Goldbach windows past 10^8: windows 101 to 150, from
EvenGoldbachUpTo 199000000 to EvenGoldbachUpTo 298000000, so the blocks compose. Each step is upTo_extend2 in BitSieve2.lean.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2
import LeanLab.Verifications.Top50.BitW101
import LeanLab.Verifications.Top50.BitW102
import LeanLab.Verifications.Top50.BitW103
import LeanLab.Verifications.Top50.BitW104
import LeanLab.Verifications.Top50.BitW105
import LeanLab.Verifications.Top50.BitW106
import LeanLab.Verifications.Top50.BitW107
import LeanLab.Verifications.Top50.BitW108
import LeanLab.Verifications.Top50.BitW109
import LeanLab.Verifications.Top50.BitW110
import LeanLab.Verifications.Top50.BitW111
import LeanLab.Verifications.Top50.BitW112
import LeanLab.Verifications.Top50.BitW113
import LeanLab.Verifications.Top50.BitW114
import LeanLab.Verifications.Top50.BitW115
import LeanLab.Verifications.Top50.BitW116
import LeanLab.Verifications.Top50.BitW117
import LeanLab.Verifications.Top50.BitW118
import LeanLab.Verifications.Top50.BitW119
import LeanLab.Verifications.Top50.BitW120
import LeanLab.Verifications.Top50.BitW121
import LeanLab.Verifications.Top50.BitW122
import LeanLab.Verifications.Top50.BitW123
import LeanLab.Verifications.Top50.BitW124
import LeanLab.Verifications.Top50.BitW125
import LeanLab.Verifications.Top50.BitW126
import LeanLab.Verifications.Top50.BitW127
import LeanLab.Verifications.Top50.BitW128
import LeanLab.Verifications.Top50.BitW129
import LeanLab.Verifications.Top50.BitW130
import LeanLab.Verifications.Top50.BitW131
import LeanLab.Verifications.Top50.BitW132
import LeanLab.Verifications.Top50.BitW133
import LeanLab.Verifications.Top50.BitW134
import LeanLab.Verifications.Top50.BitW135
import LeanLab.Verifications.Top50.BitW136
import LeanLab.Verifications.Top50.BitW137
import LeanLab.Verifications.Top50.BitW138
import LeanLab.Verifications.Top50.BitW139
import LeanLab.Verifications.Top50.BitW140
import LeanLab.Verifications.Top50.BitW141
import LeanLab.Verifications.Top50.BitW142
import LeanLab.Verifications.Top50.BitW143
import LeanLab.Verifications.Top50.BitW144
import LeanLab.Verifications.Top50.BitW145
import LeanLab.Verifications.Top50.BitW146
import LeanLab.Verifications.Top50.BitW147
import LeanLab.Verifications.Top50.BitW148
import LeanLab.Verifications.Top50.BitW149
import LeanLab.Verifications.Top50.BitW150

namespace LeanLab.Verifications.Top50.Bits

theorem upTo_w101 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 200980000 :=
  upTo_extend2 (a := 199000000) (A := 199000002) (lo := 198998190) (W := 1981810) h
    ⟨99500000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_101

theorem upTo_w102 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 202960000 :=
  upTo_extend2 (a := 200980000) (A := 200980002) (lo := 200978190) (W := 1981810) (upTo_w101 h)
    ⟨100490000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_102

theorem upTo_w103 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 204940000 :=
  upTo_extend2 (a := 202960000) (A := 202960002) (lo := 202958190) (W := 1981810) (upTo_w102 h)
    ⟨101480000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_103

theorem upTo_w104 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 206920000 :=
  upTo_extend2 (a := 204940000) (A := 204940002) (lo := 204938190) (W := 1981810) (upTo_w103 h)
    ⟨102470000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_104

theorem upTo_w105 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 208900000 :=
  upTo_extend2 (a := 206920000) (A := 206920002) (lo := 206918190) (W := 1981810) (upTo_w104 h)
    ⟨103460000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_105

theorem upTo_w106 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 210880000 :=
  upTo_extend2 (a := 208900000) (A := 208900002) (lo := 208898190) (W := 1981810) (upTo_w105 h)
    ⟨104450000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_106

theorem upTo_w107 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 212860000 :=
  upTo_extend2 (a := 210880000) (A := 210880002) (lo := 210878190) (W := 1981810) (upTo_w106 h)
    ⟨105440000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_107

theorem upTo_w108 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 214840000 :=
  upTo_extend2 (a := 212860000) (A := 212860002) (lo := 212858190) (W := 1981810) (upTo_w107 h)
    ⟨106430000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_108

theorem upTo_w109 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 216820000 :=
  upTo_extend2 (a := 214840000) (A := 214840002) (lo := 214838190) (W := 1981810) (upTo_w108 h)
    ⟨107420000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_109

theorem upTo_w110 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 218800000 :=
  upTo_extend2 (a := 216820000) (A := 216820002) (lo := 216818190) (W := 1981810) (upTo_w109 h)
    ⟨108410000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_110

theorem upTo_w111 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 220780000 :=
  upTo_extend2 (a := 218800000) (A := 218800002) (lo := 218798190) (W := 1981810) (upTo_w110 h)
    ⟨109400000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_111

theorem upTo_w112 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 222760000 :=
  upTo_extend2 (a := 220780000) (A := 220780002) (lo := 220778190) (W := 1981810) (upTo_w111 h)
    ⟨110390000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_112

theorem upTo_w113 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 224740000 :=
  upTo_extend2 (a := 222760000) (A := 222760002) (lo := 222758190) (W := 1981810) (upTo_w112 h)
    ⟨111380000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_113

theorem upTo_w114 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 226720000 :=
  upTo_extend2 (a := 224740000) (A := 224740002) (lo := 224738190) (W := 1981810) (upTo_w113 h)
    ⟨112370000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_114

theorem upTo_w115 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 228700000 :=
  upTo_extend2 (a := 226720000) (A := 226720002) (lo := 226718190) (W := 1981810) (upTo_w114 h)
    ⟨113360000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_115

theorem upTo_w116 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 230680000 :=
  upTo_extend2 (a := 228700000) (A := 228700002) (lo := 228698190) (W := 1981810) (upTo_w115 h)
    ⟨114350000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_116

theorem upTo_w117 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 232660000 :=
  upTo_extend2 (a := 230680000) (A := 230680002) (lo := 230678190) (W := 1981810) (upTo_w116 h)
    ⟨115340000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_117

theorem upTo_w118 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 234640000 :=
  upTo_extend2 (a := 232660000) (A := 232660002) (lo := 232658190) (W := 1981810) (upTo_w117 h)
    ⟨116330000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_118

theorem upTo_w119 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 236620000 :=
  upTo_extend2 (a := 234640000) (A := 234640002) (lo := 234638190) (W := 1981810) (upTo_w118 h)
    ⟨117320000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_119

theorem upTo_w120 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 238600000 :=
  upTo_extend2 (a := 236620000) (A := 236620002) (lo := 236618190) (W := 1981810) (upTo_w119 h)
    ⟨118310000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_120

theorem upTo_w121 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 240580000 :=
  upTo_extend2 (a := 238600000) (A := 238600002) (lo := 238598190) (W := 1981810) (upTo_w120 h)
    ⟨119300000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_121

theorem upTo_w122 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 242560000 :=
  upTo_extend2 (a := 240580000) (A := 240580002) (lo := 240578190) (W := 1981810) (upTo_w121 h)
    ⟨120290000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_122

theorem upTo_w123 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 244540000 :=
  upTo_extend2 (a := 242560000) (A := 242560002) (lo := 242558190) (W := 1981810) (upTo_w122 h)
    ⟨121280000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_123

theorem upTo_w124 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 246520000 :=
  upTo_extend2 (a := 244540000) (A := 244540002) (lo := 244538190) (W := 1981810) (upTo_w123 h)
    ⟨122270000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_124

theorem upTo_w125 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 248500000 :=
  upTo_extend2 (a := 246520000) (A := 246520002) (lo := 246518190) (W := 1981810) (upTo_w124 h)
    ⟨123260000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_125

theorem upTo_w126 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 250480000 :=
  upTo_extend2 (a := 248500000) (A := 248500002) (lo := 248498190) (W := 1981810) (upTo_w125 h)
    ⟨124250000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_126

theorem upTo_w127 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 252460000 :=
  upTo_extend2 (a := 250480000) (A := 250480002) (lo := 250478190) (W := 1981810) (upTo_w126 h)
    ⟨125240000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_127

theorem upTo_w128 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 254440000 :=
  upTo_extend2 (a := 252460000) (A := 252460002) (lo := 252458190) (W := 1981810) (upTo_w127 h)
    ⟨126230000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_128

theorem upTo_w129 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 256420000 :=
  upTo_extend2 (a := 254440000) (A := 254440002) (lo := 254438190) (W := 1981810) (upTo_w128 h)
    ⟨127220000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_129

theorem upTo_w130 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 258400000 :=
  upTo_extend2 (a := 256420000) (A := 256420002) (lo := 256418190) (W := 1981810) (upTo_w129 h)
    ⟨128210000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_130

theorem upTo_w131 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 260380000 :=
  upTo_extend2 (a := 258400000) (A := 258400002) (lo := 258398190) (W := 1981810) (upTo_w130 h)
    ⟨129200000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_131

theorem upTo_w132 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 262360000 :=
  upTo_extend2 (a := 260380000) (A := 260380002) (lo := 260378190) (W := 1981810) (upTo_w131 h)
    ⟨130190000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_132

theorem upTo_w133 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 264340000 :=
  upTo_extend2 (a := 262360000) (A := 262360002) (lo := 262358190) (W := 1981810) (upTo_w132 h)
    ⟨131180000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_133

theorem upTo_w134 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 266320000 :=
  upTo_extend2 (a := 264340000) (A := 264340002) (lo := 264338190) (W := 1981810) (upTo_w133 h)
    ⟨132170000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_134

theorem upTo_w135 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 268300000 :=
  upTo_extend2 (a := 266320000) (A := 266320002) (lo := 266318190) (W := 1981810) (upTo_w134 h)
    ⟨133160000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_135

theorem upTo_w136 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 270280000 :=
  upTo_extend2 (a := 268300000) (A := 268300002) (lo := 268298190) (W := 1981810) (upTo_w135 h)
    ⟨134150000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_136

theorem upTo_w137 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 272260000 :=
  upTo_extend2 (a := 270280000) (A := 270280002) (lo := 270278190) (W := 1981810) (upTo_w136 h)
    ⟨135140000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_137

theorem upTo_w138 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 274240000 :=
  upTo_extend2 (a := 272260000) (A := 272260002) (lo := 272258190) (W := 1981810) (upTo_w137 h)
    ⟨136130000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_138

theorem upTo_w139 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 276220000 :=
  upTo_extend2 (a := 274240000) (A := 274240002) (lo := 274238190) (W := 1981810) (upTo_w138 h)
    ⟨137120000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_139

theorem upTo_w140 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 278200000 :=
  upTo_extend2 (a := 276220000) (A := 276220002) (lo := 276218190) (W := 1981810) (upTo_w139 h)
    ⟨138110000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_140

theorem upTo_w141 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 280180000 :=
  upTo_extend2 (a := 278200000) (A := 278200002) (lo := 278198190) (W := 1981810) (upTo_w140 h)
    ⟨139100000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_141

theorem upTo_w142 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 282160000 :=
  upTo_extend2 (a := 280180000) (A := 280180002) (lo := 280178190) (W := 1981810) (upTo_w141 h)
    ⟨140090000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_142

theorem upTo_w143 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 284140000 :=
  upTo_extend2 (a := 282160000) (A := 282160002) (lo := 282158190) (W := 1981810) (upTo_w142 h)
    ⟨141080000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_143

theorem upTo_w144 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 286120000 :=
  upTo_extend2 (a := 284140000) (A := 284140002) (lo := 284138190) (W := 1981810) (upTo_w143 h)
    ⟨142070000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_144

theorem upTo_w145 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 288100000 :=
  upTo_extend2 (a := 286120000) (A := 286120002) (lo := 286118190) (W := 1981810) (upTo_w144 h)
    ⟨143060000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_145

theorem upTo_w146 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 290080000 :=
  upTo_extend2 (a := 288100000) (A := 288100002) (lo := 288098190) (W := 1981810) (upTo_w145 h)
    ⟨144050000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_146

theorem upTo_w147 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 292060000 :=
  upTo_extend2 (a := 290080000) (A := 290080002) (lo := 290078190) (W := 1981810) (upTo_w146 h)
    ⟨145040000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_147

theorem upTo_w148 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 294040000 :=
  upTo_extend2 (a := 292060000) (A := 292060002) (lo := 292058190) (W := 1981810) (upTo_w147 h)
    ⟨146030000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_148

theorem upTo_w149 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 296020000 :=
  upTo_extend2 (a := 294040000) (A := 294040002) (lo := 294038190) (W := 1981810) (upTo_w148 h)
    ⟨147020000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_149

theorem upTo_w150 (h : EvenGoldbachUpTo 199000000) : EvenGoldbachUpTo 298000000 :=
  upTo_extend2 (a := 296020000) (A := 296020002) (lo := 296018190) (W := 1981810) (upTo_w149 h)
    ⟨148010000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_150

end LeanLab.Verifications.Top50.Bits
