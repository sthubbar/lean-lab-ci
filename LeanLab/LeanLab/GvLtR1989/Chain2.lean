/-
P0042 Granville, van de Lune, te Riele 1989, both numerical claims extended to the even range 6 to 323740000,
joining Chain.lean at 218800000 with blocks 124 to 176 of W111 to W163.
Kernel checked with no cited input. Far below the paper's 2·10^10.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0204Z-8469, unit U-0381. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Chain
import LeanLab.GvLtR1989.W111
import LeanLab.GvLtR1989.W112
import LeanLab.GvLtR1989.W113
import LeanLab.GvLtR1989.W114
import LeanLab.GvLtR1989.W115
import LeanLab.GvLtR1989.W116
import LeanLab.GvLtR1989.W117
import LeanLab.GvLtR1989.W118
import LeanLab.GvLtR1989.W119
import LeanLab.GvLtR1989.W120
import LeanLab.GvLtR1989.W121
import LeanLab.GvLtR1989.W122
import LeanLab.GvLtR1989.W123
import LeanLab.GvLtR1989.W124
import LeanLab.GvLtR1989.W125
import LeanLab.GvLtR1989.W126
import LeanLab.GvLtR1989.W127
import LeanLab.GvLtR1989.W128
import LeanLab.GvLtR1989.W129
import LeanLab.GvLtR1989.W130
import LeanLab.GvLtR1989.W131
import LeanLab.GvLtR1989.W132
import LeanLab.GvLtR1989.W133
import LeanLab.GvLtR1989.W134
import LeanLab.GvLtR1989.W135
import LeanLab.GvLtR1989.W136
import LeanLab.GvLtR1989.W137
import LeanLab.GvLtR1989.W138
import LeanLab.GvLtR1989.W139
import LeanLab.GvLtR1989.W140
import LeanLab.GvLtR1989.W141
import LeanLab.GvLtR1989.W142
import LeanLab.GvLtR1989.W143
import LeanLab.GvLtR1989.W144
import LeanLab.GvLtR1989.W145
import LeanLab.GvLtR1989.W146
import LeanLab.GvLtR1989.W147
import LeanLab.GvLtR1989.W148
import LeanLab.GvLtR1989.W149
import LeanLab.GvLtR1989.W150
import LeanLab.GvLtR1989.W151
import LeanLab.GvLtR1989.W152
import LeanLab.GvLtR1989.W153
import LeanLab.GvLtR1989.W154
import LeanLab.GvLtR1989.W155
import LeanLab.GvLtR1989.W156
import LeanLab.GvLtR1989.W157
import LeanLab.GvLtR1989.W158
import LeanLab.GvLtR1989.W159
import LeanLab.GvLtR1989.W160
import LeanLab.GvLtR1989.W161
import LeanLab.GvLtR1989.W162
import LeanLab.GvLtR1989.W163

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem c1x_124 : ∀ n, Even n → 6 ≤ n → n ≤ 220780000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_123 r1_124 (by norm_num) (by decide)
theorem c1x_125 : ∀ n, Even n → 6 ≤ n → n ≤ 222760000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_124 r1_125 (by norm_num) (by decide)
theorem c1x_126 : ∀ n, Even n → 6 ≤ n → n ≤ 224740000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_125 r1_126 (by norm_num) (by decide)
theorem c1x_127 : ∀ n, Even n → 6 ≤ n → n ≤ 226720000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_126 r1_127 (by norm_num) (by decide)
theorem c1x_128 : ∀ n, Even n → 6 ≤ n → n ≤ 228700000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_127 r1_128 (by norm_num) (by decide)
theorem c1x_129 : ∀ n, Even n → 6 ≤ n → n ≤ 230680000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_128 r1_129 (by norm_num) (by decide)
theorem c1x_130 : ∀ n, Even n → 6 ≤ n → n ≤ 232660000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_129 r1_130 (by norm_num) (by decide)
theorem c1x_131 : ∀ n, Even n → 6 ≤ n → n ≤ 234640000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_130 r1_131 (by norm_num) (by decide)
theorem c1x_132 : ∀ n, Even n → 6 ≤ n → n ≤ 236620000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_131 r1_132 (by norm_num) (by decide)
theorem c1x_133 : ∀ n, Even n → 6 ≤ n → n ≤ 238600000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_132 r1_133 (by norm_num) (by decide)
theorem c1x_134 : ∀ n, Even n → 6 ≤ n → n ≤ 240580000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_133 r1_134 (by norm_num) (by decide)
theorem c1x_135 : ∀ n, Even n → 6 ≤ n → n ≤ 242560000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_134 r1_135 (by norm_num) (by decide)
theorem c1x_136 : ∀ n, Even n → 6 ≤ n → n ≤ 244540000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_135 r1_136 (by norm_num) (by decide)
theorem c1x_137 : ∀ n, Even n → 6 ≤ n → n ≤ 246520000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_136 r1_137 (by norm_num) (by decide)
theorem c1x_138 : ∀ n, Even n → 6 ≤ n → n ≤ 248500000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_137 r1_138 (by norm_num) (by decide)
theorem c1x_139 : ∀ n, Even n → 6 ≤ n → n ≤ 250480000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_138 r1_139 (by norm_num) (by decide)
theorem c1x_140 : ∀ n, Even n → 6 ≤ n → n ≤ 252460000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_139 r1_140 (by norm_num) (by decide)
theorem c1x_141 : ∀ n, Even n → 6 ≤ n → n ≤ 254440000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_140 r1_141 (by norm_num) (by decide)
theorem c1x_142 : ∀ n, Even n → 6 ≤ n → n ≤ 256420000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_141 r1_142 (by norm_num) (by decide)
theorem c1x_143 : ∀ n, Even n → 6 ≤ n → n ≤ 258400000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_142 r1_143 (by norm_num) (by decide)
theorem c1x_144 : ∀ n, Even n → 6 ≤ n → n ≤ 260380000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_143 r1_144 (by norm_num) (by decide)
theorem c1x_145 : ∀ n, Even n → 6 ≤ n → n ≤ 262360000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_144 r1_145 (by norm_num) (by decide)
theorem c1x_146 : ∀ n, Even n → 6 ≤ n → n ≤ 264340000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_145 r1_146 (by norm_num) (by decide)
theorem c1x_147 : ∀ n, Even n → 6 ≤ n → n ≤ 266320000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_146 r1_147 (by norm_num) (by decide)
theorem c1x_148 : ∀ n, Even n → 6 ≤ n → n ≤ 268300000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_147 r1_148 (by norm_num) (by decide)
theorem c1x_149 : ∀ n, Even n → 6 ≤ n → n ≤ 270280000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_148 r1_149 (by norm_num) (by decide)
theorem c1x_150 : ∀ n, Even n → 6 ≤ n → n ≤ 272260000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_149 r1_150 (by norm_num) (by decide)
theorem c1x_151 : ∀ n, Even n → 6 ≤ n → n ≤ 274240000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_150 r1_151 (by norm_num) (by decide)
theorem c1x_152 : ∀ n, Even n → 6 ≤ n → n ≤ 276220000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_151 r1_152 (by norm_num) (by decide)
theorem c1x_153 : ∀ n, Even n → 6 ≤ n → n ≤ 278200000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_152 r1_153 (by norm_num) (by decide)
theorem c1x_154 : ∀ n, Even n → 6 ≤ n → n ≤ 280180000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_153 r1_154 (by norm_num) (by decide)
theorem c1x_155 : ∀ n, Even n → 6 ≤ n → n ≤ 282160000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_154 r1_155 (by norm_num) (by decide)
theorem c1x_156 : ∀ n, Even n → 6 ≤ n → n ≤ 284140000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_155 r1_156 (by norm_num) (by decide)
theorem c1x_157 : ∀ n, Even n → 6 ≤ n → n ≤ 286120000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_156 r1_157 (by norm_num) (by decide)
theorem c1x_158 : ∀ n, Even n → 6 ≤ n → n ≤ 288100000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_157 r1_158 (by norm_num) (by decide)
theorem c1x_159 : ∀ n, Even n → 6 ≤ n → n ≤ 290080000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_158 r1_159 (by norm_num) (by decide)
theorem c1x_160 : ∀ n, Even n → 6 ≤ n → n ≤ 292060000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_159 r1_160 (by norm_num) (by decide)
theorem c1x_161 : ∀ n, Even n → 6 ≤ n → n ≤ 294040000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_160 r1_161 (by norm_num) (by decide)
theorem c1x_162 : ∀ n, Even n → 6 ≤ n → n ≤ 296020000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_161 r1_162 (by norm_num) (by decide)
theorem c1x_163 : ∀ n, Even n → 6 ≤ n → n ≤ 298000000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_162 r1_163 (by norm_num) (by decide)
theorem c1x_164 : ∀ n, Even n → 6 ≤ n → n ≤ 299980000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_163 r1_164 (by norm_num) (by decide)
theorem c1x_165 : ∀ n, Even n → 6 ≤ n → n ≤ 301960000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_164 r1_165 (by norm_num) (by decide)
theorem c1x_166 : ∀ n, Even n → 6 ≤ n → n ≤ 303940000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_165 r1_166 (by norm_num) (by decide)
theorem c1x_167 : ∀ n, Even n → 6 ≤ n → n ≤ 305920000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_166 r1_167 (by norm_num) (by decide)
theorem c1x_168 : ∀ n, Even n → 6 ≤ n → n ≤ 307900000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_167 r1_168 (by norm_num) (by decide)
theorem c1x_169 : ∀ n, Even n → 6 ≤ n → n ≤ 309880000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_168 r1_169 (by norm_num) (by decide)
theorem c1x_170 : ∀ n, Even n → 6 ≤ n → n ≤ 311860000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_169 r1_170 (by norm_num) (by decide)
theorem c1x_171 : ∀ n, Even n → 6 ≤ n → n ≤ 313840000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_170 r1_171 (by norm_num) (by decide)
theorem c1x_172 : ∀ n, Even n → 6 ≤ n → n ≤ 315820000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_171 r1_172 (by norm_num) (by decide)
theorem c1x_173 : ∀ n, Even n → 6 ≤ n → n ≤ 317800000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_172 r1_173 (by norm_num) (by decide)
theorem c1x_174 : ∀ n, Even n → 6 ≤ n → n ≤ 319780000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_173 r1_174 (by norm_num) (by decide)
theorem c1x_175 : ∀ n, Even n → 6 ≤ n → n ≤ 321760000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_174 r1_175 (by norm_num) (by decide)
theorem c1x_176 : ∀ n, Even n → 6 ≤ n → n ≤ 323740000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1x_175 r1_176 (by norm_num) (by decide)
theorem c2x_124 : ∀ n, Even n → 8 ≤ n → n ≤ 220780000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_123 r2_124 (by norm_num) (by decide)
theorem c2x_125 : ∀ n, Even n → 8 ≤ n → n ≤ 222760000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_124 r2_125 (by norm_num) (by decide)
theorem c2x_126 : ∀ n, Even n → 8 ≤ n → n ≤ 224740000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_125 r2_126 (by norm_num) (by decide)
theorem c2x_127 : ∀ n, Even n → 8 ≤ n → n ≤ 226720000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_126 r2_127 (by norm_num) (by decide)
theorem c2x_128 : ∀ n, Even n → 8 ≤ n → n ≤ 228700000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_127 r2_128 (by norm_num) (by decide)
theorem c2x_129 : ∀ n, Even n → 8 ≤ n → n ≤ 230680000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_128 r2_129 (by norm_num) (by decide)
theorem c2x_130 : ∀ n, Even n → 8 ≤ n → n ≤ 232660000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_129 r2_130 (by norm_num) (by decide)
theorem c2x_131 : ∀ n, Even n → 8 ≤ n → n ≤ 234640000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_130 r2_131 (by norm_num) (by decide)
theorem c2x_132 : ∀ n, Even n → 8 ≤ n → n ≤ 236620000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_131 r2_132 (by norm_num) (by decide)
theorem c2x_133 : ∀ n, Even n → 8 ≤ n → n ≤ 238600000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_132 r2_133 (by norm_num) (by decide)
theorem c2x_134 : ∀ n, Even n → 8 ≤ n → n ≤ 240580000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_133 r2_134 (by norm_num) (by decide)
theorem c2x_135 : ∀ n, Even n → 8 ≤ n → n ≤ 242560000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_134 r2_135 (by norm_num) (by decide)
theorem c2x_136 : ∀ n, Even n → 8 ≤ n → n ≤ 244540000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_135 r2_136 (by norm_num) (by decide)
theorem c2x_137 : ∀ n, Even n → 8 ≤ n → n ≤ 246520000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_136 r2_137 (by norm_num) (by decide)
theorem c2x_138 : ∀ n, Even n → 8 ≤ n → n ≤ 248500000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_137 r2_138 (by norm_num) (by decide)
theorem c2x_139 : ∀ n, Even n → 8 ≤ n → n ≤ 250480000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_138 r2_139 (by norm_num) (by decide)
theorem c2x_140 : ∀ n, Even n → 8 ≤ n → n ≤ 252460000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_139 r2_140 (by norm_num) (by decide)
theorem c2x_141 : ∀ n, Even n → 8 ≤ n → n ≤ 254440000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_140 r2_141 (by norm_num) (by decide)
theorem c2x_142 : ∀ n, Even n → 8 ≤ n → n ≤ 256420000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_141 r2_142 (by norm_num) (by decide)
theorem c2x_143 : ∀ n, Even n → 8 ≤ n → n ≤ 258400000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_142 r2_143 (by norm_num) (by decide)
theorem c2x_144 : ∀ n, Even n → 8 ≤ n → n ≤ 260380000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_143 r2_144 (by norm_num) (by decide)
theorem c2x_145 : ∀ n, Even n → 8 ≤ n → n ≤ 262360000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_144 r2_145 (by norm_num) (by decide)
theorem c2x_146 : ∀ n, Even n → 8 ≤ n → n ≤ 264340000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_145 r2_146 (by norm_num) (by decide)
theorem c2x_147 : ∀ n, Even n → 8 ≤ n → n ≤ 266320000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_146 r2_147 (by norm_num) (by decide)
theorem c2x_148 : ∀ n, Even n → 8 ≤ n → n ≤ 268300000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_147 r2_148 (by norm_num) (by decide)
theorem c2x_149 : ∀ n, Even n → 8 ≤ n → n ≤ 270280000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_148 r2_149 (by norm_num) (by decide)
theorem c2x_150 : ∀ n, Even n → 8 ≤ n → n ≤ 272260000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_149 r2_150 (by norm_num) (by decide)
theorem c2x_151 : ∀ n, Even n → 8 ≤ n → n ≤ 274240000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_150 r2_151 (by norm_num) (by decide)
theorem c2x_152 : ∀ n, Even n → 8 ≤ n → n ≤ 276220000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_151 r2_152 (by norm_num) (by decide)
theorem c2x_153 : ∀ n, Even n → 8 ≤ n → n ≤ 278200000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_152 r2_153 (by norm_num) (by decide)
theorem c2x_154 : ∀ n, Even n → 8 ≤ n → n ≤ 280180000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_153 r2_154 (by norm_num) (by decide)
theorem c2x_155 : ∀ n, Even n → 8 ≤ n → n ≤ 282160000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_154 r2_155 (by norm_num) (by decide)
theorem c2x_156 : ∀ n, Even n → 8 ≤ n → n ≤ 284140000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_155 r2_156 (by norm_num) (by decide)
theorem c2x_157 : ∀ n, Even n → 8 ≤ n → n ≤ 286120000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_156 r2_157 (by norm_num) (by decide)
theorem c2x_158 : ∀ n, Even n → 8 ≤ n → n ≤ 288100000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_157 r2_158 (by norm_num) (by decide)
theorem c2x_159 : ∀ n, Even n → 8 ≤ n → n ≤ 290080000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_158 r2_159 (by norm_num) (by decide)
theorem c2x_160 : ∀ n, Even n → 8 ≤ n → n ≤ 292060000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_159 r2_160 (by norm_num) (by decide)
theorem c2x_161 : ∀ n, Even n → 8 ≤ n → n ≤ 294040000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_160 r2_161 (by norm_num) (by decide)
theorem c2x_162 : ∀ n, Even n → 8 ≤ n → n ≤ 296020000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_161 r2_162 (by norm_num) (by decide)
theorem c2x_163 : ∀ n, Even n → 8 ≤ n → n ≤ 298000000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_162 r2_163 (by norm_num) (by decide)
theorem c2x_164 : ∀ n, Even n → 8 ≤ n → n ≤ 299980000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_163 r2_164 (by norm_num) (by decide)
theorem c2x_165 : ∀ n, Even n → 8 ≤ n → n ≤ 301960000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_164 r2_165 (by norm_num) (by decide)
theorem c2x_166 : ∀ n, Even n → 8 ≤ n → n ≤ 303940000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_165 r2_166 (by norm_num) (by decide)
theorem c2x_167 : ∀ n, Even n → 8 ≤ n → n ≤ 305920000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_166 r2_167 (by norm_num) (by decide)
theorem c2x_168 : ∀ n, Even n → 8 ≤ n → n ≤ 307900000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_167 r2_168 (by norm_num) (by decide)
theorem c2x_169 : ∀ n, Even n → 8 ≤ n → n ≤ 309880000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_168 r2_169 (by norm_num) (by decide)
theorem c2x_170 : ∀ n, Even n → 8 ≤ n → n ≤ 311860000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_169 r2_170 (by norm_num) (by decide)
theorem c2x_171 : ∀ n, Even n → 8 ≤ n → n ≤ 313840000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_170 r2_171 (by norm_num) (by decide)
theorem c2x_172 : ∀ n, Even n → 8 ≤ n → n ≤ 315820000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_171 r2_172 (by norm_num) (by decide)
theorem c2x_173 : ∀ n, Even n → 8 ≤ n → n ≤ 317800000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_172 r2_173 (by norm_num) (by decide)
theorem c2x_174 : ∀ n, Even n → 8 ≤ n → n ≤ 319780000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_173 r2_174 (by norm_num) (by decide)
theorem c2x_175 : ∀ n, Even n → 8 ≤ n → n ≤ 321760000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_174 r2_175 (by norm_num) (by decide)
theorem c2x_176 : ∀ n, Even n → 8 ≤ n → n ≤ 323740000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2x_175 r2_176 (by norm_num) (by decide)
theorem mb_124 : ∀ n, Even n → 218800002 ≤ n → n ≤ 220780000 → minGB n ≤ 1321 := mono bnd_124 (by norm_num)
theorem mb_125 : ∀ n, Even n → 220780002 ≤ n → n ≤ 222760000 → minGB n ≤ 1321 := mono bnd_125 (by norm_num)
theorem mb_126 : ∀ n, Even n → 222760002 ≤ n → n ≤ 224740000 → minGB n ≤ 1321 := mono bnd_126 (by norm_num)
theorem mb_127 : ∀ n, Even n → 224740002 ≤ n → n ≤ 226720000 → minGB n ≤ 1321 := mono bnd_127 (by norm_num)
theorem mb_128 : ∀ n, Even n → 226720002 ≤ n → n ≤ 228700000 → minGB n ≤ 1321 := mono bnd_128 (by norm_num)
theorem mb_129 : ∀ n, Even n → 228700002 ≤ n → n ≤ 230680000 → minGB n ≤ 1321 := mono bnd_129 (by norm_num)
theorem mb_130 : ∀ n, Even n → 230680002 ≤ n → n ≤ 232660000 → minGB n ≤ 1321 := mono bnd_130 (by norm_num)
theorem mb_131 : ∀ n, Even n → 232660002 ≤ n → n ≤ 234640000 → minGB n ≤ 1321 := mono bnd_131 (by norm_num)
theorem mb_132 : ∀ n, Even n → 234640002 ≤ n → n ≤ 236620000 → minGB n ≤ 1321 := mono bnd_132 (by norm_num)
theorem mb_133 : ∀ n, Even n → 236620002 ≤ n → n ≤ 238600000 → minGB n ≤ 1321 := mono bnd_133 (by norm_num)
theorem mb_134 : ∀ n, Even n → 238600002 ≤ n → n ≤ 240580000 → minGB n ≤ 1321 := mono bnd_134 (by norm_num)
theorem mb_135 : ∀ n, Even n → 240580002 ≤ n → n ≤ 242560000 → minGB n ≤ 1321 := mono bnd_135 (by norm_num)
theorem mb_136 : ∀ n, Even n → 242560002 ≤ n → n ≤ 244540000 → minGB n ≤ 1321 := mono bnd_136 (by norm_num)
theorem mb_137 : ∀ n, Even n → 244540002 ≤ n → n ≤ 246520000 → minGB n ≤ 1321 := mono bnd_137 (by norm_num)
theorem mb_138 : ∀ n, Even n → 246520002 ≤ n → n ≤ 248500000 → minGB n ≤ 1321 := mono bnd_138 (by norm_num)
theorem mb_139 : ∀ n, Even n → 248500002 ≤ n → n ≤ 250480000 → minGB n ≤ 1321 := mono bnd_139 (by norm_num)
theorem mb_140 : ∀ n, Even n → 250480002 ≤ n → n ≤ 252460000 → minGB n ≤ 1321 := mono bnd_140 (by norm_num)
theorem mb_141 : ∀ n, Even n → 252460002 ≤ n → n ≤ 254440000 → minGB n ≤ 1321 := mono bnd_141 (by norm_num)
theorem mb_142 : ∀ n, Even n → 254440002 ≤ n → n ≤ 256420000 → minGB n ≤ 1321 := mono bnd_142 (by norm_num)
theorem mb_143 : ∀ n, Even n → 256420002 ≤ n → n ≤ 258400000 → minGB n ≤ 1321 := mono bnd_143 (by norm_num)
theorem mb_144 : ∀ n, Even n → 258400002 ≤ n → n ≤ 260380000 → minGB n ≤ 1321 := mono bnd_144 (by norm_num)
theorem mb_145 : ∀ n, Even n → 260380002 ≤ n → n ≤ 262360000 → minGB n ≤ 1321 := mono bnd_145 (by norm_num)
theorem mb_146 : ∀ n, Even n → 262360002 ≤ n → n ≤ 264340000 → minGB n ≤ 1321 := mono bnd_146 (by norm_num)
theorem mb_147 : ∀ n, Even n → 264340002 ≤ n → n ≤ 266320000 → minGB n ≤ 1321 := mono bnd_147 (by norm_num)
theorem mb_148 : ∀ n, Even n → 266320002 ≤ n → n ≤ 268300000 → minGB n ≤ 1321 := mono bnd_148 (by norm_num)
theorem mb_149 : ∀ n, Even n → 268300002 ≤ n → n ≤ 270280000 → minGB n ≤ 1321 := mono bnd_149 (by norm_num)
theorem mb_150 : ∀ n, Even n → 270280002 ≤ n → n ≤ 272260000 → minGB n ≤ 1321 := mono bnd_150 (by norm_num)
theorem mb_151 : ∀ n, Even n → 272260002 ≤ n → n ≤ 274240000 → minGB n ≤ 1321 := mono bnd_151 (by norm_num)
theorem mb_152 : ∀ n, Even n → 274240002 ≤ n → n ≤ 276220000 → minGB n ≤ 1321 := mono bnd_152 (by norm_num)
theorem mb_153 : ∀ n, Even n → 276220002 ≤ n → n ≤ 278200000 → minGB n ≤ 1321 := mono bnd_153 (by norm_num)
theorem mb_154 : ∀ n, Even n → 278200002 ≤ n → n ≤ 280180000 → minGB n ≤ 1321 := mono bnd_154 (by norm_num)
theorem mb_155 : ∀ n, Even n → 280180002 ≤ n → n ≤ 282160000 → minGB n ≤ 1321 := mono bnd_155 (by norm_num)
theorem mb_156 : ∀ n, Even n → 282160002 ≤ n → n ≤ 284140000 → minGB n ≤ 1321 := mono bnd_156 (by norm_num)
theorem mb_157 : ∀ n, Even n → 284140002 ≤ n → n ≤ 286120000 → minGB n ≤ 1321 := mono bnd_157 (by norm_num)
theorem mb_158 : ∀ n, Even n → 286120002 ≤ n → n ≤ 288100000 → minGB n ≤ 1321 := mono bnd_158 (by norm_num)
theorem mb_159 : ∀ n, Even n → 288100002 ≤ n → n ≤ 290080000 → minGB n ≤ 1321 := mono bnd_159 (by norm_num)
theorem mb_160 : ∀ n, Even n → 290080002 ≤ n → n ≤ 292060000 → minGB n ≤ 1321 := mono bnd_160 (by norm_num)
theorem mb_161 : ∀ n, Even n → 292060002 ≤ n → n ≤ 294040000 → minGB n ≤ 1321 := mono bnd_161 (by norm_num)
theorem mb_162 : ∀ n, Even n → 294040002 ≤ n → n ≤ 296020000 → minGB n ≤ 1321 := mono bnd_162 (by norm_num)
theorem mb_163 : ∀ n, Even n → 296020002 ≤ n → n ≤ 298000000 → minGB n ≤ 1321 := mono bnd_163 (by norm_num)
theorem mb_164 : ∀ n, Even n → 298000002 ≤ n → n ≤ 299980000 → minGB n ≤ 1321 := mono bnd_164 (by norm_num)
theorem mb_165 : ∀ n, Even n → 299980002 ≤ n → n ≤ 301960000 → minGB n ≤ 1321 := mono bnd_165 (by norm_num)
theorem mb_166 : ∀ n, Even n → 301960002 ≤ n → n ≤ 303940000 → minGB n ≤ 1321 := mono bnd_166 (by norm_num)
theorem mb_167 : ∀ n, Even n → 303940002 ≤ n → n ≤ 305920000 → minGB n ≤ 1321 := mono bnd_167 (by norm_num)
theorem mb_168 : ∀ n, Even n → 305920002 ≤ n → n ≤ 307900000 → minGB n ≤ 1321 := mono bnd_168 (by norm_num)
theorem mb_169 : ∀ n, Even n → 307900002 ≤ n → n ≤ 309880000 → minGB n ≤ 1321 := mono bnd_169 (by norm_num)
theorem mb_170 : ∀ n, Even n → 309880002 ≤ n → n ≤ 311860000 → minGB n ≤ 1321 := mono bnd_170 (by norm_num)
theorem mb_171 : ∀ n, Even n → 311860002 ≤ n → n ≤ 313840000 → minGB n ≤ 1321 := mono bnd_171 (by norm_num)
theorem mb_172 : ∀ n, Even n → 313840002 ≤ n → n ≤ 315820000 → minGB n ≤ 1321 := mono bnd_172 (by norm_num)
theorem mb_173 : ∀ n, Even n → 315820002 ≤ n → n ≤ 317800000 → minGB n ≤ 1321 := mono bnd_173 (by norm_num)
theorem mb_174 : ∀ n, Even n → 317800002 ≤ n → n ≤ 319780000 → minGB n ≤ 1321 := mono bnd_174 (by norm_num)
theorem mb_175 : ∀ n, Even n → 319780002 ≤ n → n ≤ 321760000 → minGB n ≤ 1321 := mono bnd_175 (by norm_num)
theorem mb_176 : ∀ n, Even n → 321760002 ≤ n → n ≤ 323740000 → minGB n ≤ 1321 := mono bnd_176 (by norm_num)
theorem c3x_124 : ∀ n, Even n → 6 ≤ n → n ≤ 220780000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_123 mb_124 (by norm_num) (by decide)
theorem c3x_125 : ∀ n, Even n → 6 ≤ n → n ≤ 222760000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_124 mb_125 (by norm_num) (by decide)
theorem c3x_126 : ∀ n, Even n → 6 ≤ n → n ≤ 224740000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_125 mb_126 (by norm_num) (by decide)
theorem c3x_127 : ∀ n, Even n → 6 ≤ n → n ≤ 226720000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_126 mb_127 (by norm_num) (by decide)
theorem c3x_128 : ∀ n, Even n → 6 ≤ n → n ≤ 228700000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_127 mb_128 (by norm_num) (by decide)
theorem c3x_129 : ∀ n, Even n → 6 ≤ n → n ≤ 230680000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_128 mb_129 (by norm_num) (by decide)
theorem c3x_130 : ∀ n, Even n → 6 ≤ n → n ≤ 232660000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_129 mb_130 (by norm_num) (by decide)
theorem c3x_131 : ∀ n, Even n → 6 ≤ n → n ≤ 234640000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_130 mb_131 (by norm_num) (by decide)
theorem c3x_132 : ∀ n, Even n → 6 ≤ n → n ≤ 236620000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_131 mb_132 (by norm_num) (by decide)
theorem c3x_133 : ∀ n, Even n → 6 ≤ n → n ≤ 238600000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_132 mb_133 (by norm_num) (by decide)
theorem c3x_134 : ∀ n, Even n → 6 ≤ n → n ≤ 240580000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_133 mb_134 (by norm_num) (by decide)
theorem c3x_135 : ∀ n, Even n → 6 ≤ n → n ≤ 242560000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_134 mb_135 (by norm_num) (by decide)
theorem c3x_136 : ∀ n, Even n → 6 ≤ n → n ≤ 244540000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_135 mb_136 (by norm_num) (by decide)
theorem c3x_137 : ∀ n, Even n → 6 ≤ n → n ≤ 246520000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_136 mb_137 (by norm_num) (by decide)
theorem c3x_138 : ∀ n, Even n → 6 ≤ n → n ≤ 248500000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_137 mb_138 (by norm_num) (by decide)
theorem c3x_139 : ∀ n, Even n → 6 ≤ n → n ≤ 250480000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_138 mb_139 (by norm_num) (by decide)
theorem c3x_140 : ∀ n, Even n → 6 ≤ n → n ≤ 252460000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_139 mb_140 (by norm_num) (by decide)
theorem c3x_141 : ∀ n, Even n → 6 ≤ n → n ≤ 254440000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_140 mb_141 (by norm_num) (by decide)
theorem c3x_142 : ∀ n, Even n → 6 ≤ n → n ≤ 256420000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_141 mb_142 (by norm_num) (by decide)
theorem c3x_143 : ∀ n, Even n → 6 ≤ n → n ≤ 258400000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_142 mb_143 (by norm_num) (by decide)
theorem c3x_144 : ∀ n, Even n → 6 ≤ n → n ≤ 260380000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_143 mb_144 (by norm_num) (by decide)
theorem c3x_145 : ∀ n, Even n → 6 ≤ n → n ≤ 262360000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_144 mb_145 (by norm_num) (by decide)
theorem c3x_146 : ∀ n, Even n → 6 ≤ n → n ≤ 264340000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_145 mb_146 (by norm_num) (by decide)
theorem c3x_147 : ∀ n, Even n → 6 ≤ n → n ≤ 266320000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_146 mb_147 (by norm_num) (by decide)
theorem c3x_148 : ∀ n, Even n → 6 ≤ n → n ≤ 268300000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_147 mb_148 (by norm_num) (by decide)
theorem c3x_149 : ∀ n, Even n → 6 ≤ n → n ≤ 270280000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_148 mb_149 (by norm_num) (by decide)
theorem c3x_150 : ∀ n, Even n → 6 ≤ n → n ≤ 272260000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_149 mb_150 (by norm_num) (by decide)
theorem c3x_151 : ∀ n, Even n → 6 ≤ n → n ≤ 274240000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_150 mb_151 (by norm_num) (by decide)
theorem c3x_152 : ∀ n, Even n → 6 ≤ n → n ≤ 276220000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_151 mb_152 (by norm_num) (by decide)
theorem c3x_153 : ∀ n, Even n → 6 ≤ n → n ≤ 278200000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_152 mb_153 (by norm_num) (by decide)
theorem c3x_154 : ∀ n, Even n → 6 ≤ n → n ≤ 280180000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_153 mb_154 (by norm_num) (by decide)
theorem c3x_155 : ∀ n, Even n → 6 ≤ n → n ≤ 282160000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_154 mb_155 (by norm_num) (by decide)
theorem c3x_156 : ∀ n, Even n → 6 ≤ n → n ≤ 284140000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_155 mb_156 (by norm_num) (by decide)
theorem c3x_157 : ∀ n, Even n → 6 ≤ n → n ≤ 286120000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_156 mb_157 (by norm_num) (by decide)
theorem c3x_158 : ∀ n, Even n → 6 ≤ n → n ≤ 288100000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_157 mb_158 (by norm_num) (by decide)
theorem c3x_159 : ∀ n, Even n → 6 ≤ n → n ≤ 290080000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_158 mb_159 (by norm_num) (by decide)
theorem c3x_160 : ∀ n, Even n → 6 ≤ n → n ≤ 292060000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_159 mb_160 (by norm_num) (by decide)
theorem c3x_161 : ∀ n, Even n → 6 ≤ n → n ≤ 294040000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_160 mb_161 (by norm_num) (by decide)
theorem c3x_162 : ∀ n, Even n → 6 ≤ n → n ≤ 296020000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_161 mb_162 (by norm_num) (by decide)
theorem c3x_163 : ∀ n, Even n → 6 ≤ n → n ≤ 298000000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_162 mb_163 (by norm_num) (by decide)
theorem c3x_164 : ∀ n, Even n → 6 ≤ n → n ≤ 299980000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_163 mb_164 (by norm_num) (by decide)
theorem c3x_165 : ∀ n, Even n → 6 ≤ n → n ≤ 301960000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_164 mb_165 (by norm_num) (by decide)
theorem c3x_166 : ∀ n, Even n → 6 ≤ n → n ≤ 303940000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_165 mb_166 (by norm_num) (by decide)
theorem c3x_167 : ∀ n, Even n → 6 ≤ n → n ≤ 305920000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_166 mb_167 (by norm_num) (by decide)
theorem c3x_168 : ∀ n, Even n → 6 ≤ n → n ≤ 307900000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_167 mb_168 (by norm_num) (by decide)
theorem c3x_169 : ∀ n, Even n → 6 ≤ n → n ≤ 309880000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_168 mb_169 (by norm_num) (by decide)
theorem c3x_170 : ∀ n, Even n → 6 ≤ n → n ≤ 311860000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_169 mb_170 (by norm_num) (by decide)
theorem c3x_171 : ∀ n, Even n → 6 ≤ n → n ≤ 313840000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_170 mb_171 (by norm_num) (by decide)
theorem c3x_172 : ∀ n, Even n → 6 ≤ n → n ≤ 315820000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_171 mb_172 (by norm_num) (by decide)
theorem c3x_173 : ∀ n, Even n → 6 ≤ n → n ≤ 317800000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_172 mb_173 (by norm_num) (by decide)
theorem c3x_174 : ∀ n, Even n → 6 ≤ n → n ≤ 319780000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_173 mb_174 (by norm_num) (by decide)
theorem c3x_175 : ∀ n, Even n → 6 ≤ n → n ≤ 321760000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_174 mb_175 (by norm_num) (by decide)
theorem c3x_176 : ∀ n, Even n → 6 ≤ n → n ≤ 323740000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3x_175 mb_176 (by norm_num) (by decide)

/-- **P0042 ratio claim, extended.** For every even n with 6 ≤ n ≤ 323740000,
p(n) < 1.603 log² n log log n, the constant of Granville, van de Lune, te Riele. -/
theorem gvltr_ratio_upTo2 : ∀ n : ℕ, Even n → 6 ≤ n → n ≤ 323740000 →
    (minGB n : ℝ) < 1.603 * Real.log n ^ 2 * Real.log (Real.log n) := c1x_176

/-- Sharper on the same range from n = 8: p(n) < 1.25 log² n log log n. -/
theorem ratio125_upTo2 : ∀ n : ℕ, Even n → 8 ≤ n → n ≤ 323740000 →
    (minGB n : ℝ) < 1.25 * Real.log n ^ 2 * Real.log (Real.log n) := c2x_176

/-- **P0042 Table 3 claim, extended**: minGB n ≤ 1321 for even n from 4 to 323740000. -/
theorem gvltr_max_upTo2 : ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 323740000 → minGB n ≤ 1321 := by
  intro n hn h4 hN
  by_cases h : n = 4
  · subst h
    exact le_trans (minGB_le_of Nat.prime_two (by norm_num)) (by norm_num)
  · apply c3x_176 n hn _ hN
    obtain ⟨k, hk⟩ := hn
    omega

theorem gvltr_max_2029_upTo2 : ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 323740000 → minGB n ≤ 2029 :=
  fun n hn h4 hN => le_trans (gvltr_max_upTo2 n hn h4 hN) (by norm_num)

end LeanLab.GvLtR1989
