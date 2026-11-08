/-
AI wrote this Lean code for CODEX task455.
P0037 Section 5.2 page 212, bit array sieve paragraph.
Table 2 page 214 row 300. These are alternative certificate windows.
Every small prime is kernel checked. No large prime is asserted here.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455hWindows0
import LeanLab.DtRS1998.Decomp455hWindows1
import LeanLab.DtRS1998.Decomp455hWindows2
import LeanLab.DtRS1998.Decomp455hWindows3
import LeanLab.DtRS1998.Decomp455hWindows4
import LeanLab.DtRS1998.Decomp455hWindows5
import LeanLab.DtRS1998.Decomp455hWindows6
import LeanLab.DtRS1998.Decomp455hWindows7
import LeanLab.DtRS1998.Decomp455hWindows8
import LeanLab.DtRS1998.Decomp455hWindows9
import LeanLab.DtRS1998.Decomp455hWindows10
import LeanLab.DtRS1998.Decomp455hWindows11
import LeanLab.DtRS1998.Decomp455hWindows12
import LeanLab.DtRS1998.Decomp455hWindows13
import LeanLab.DtRS1998.Decomp455hWindows14
import LeanLab.DtRS1998.Decomp455hWindows15
import LeanLab.DtRS1998.Decomp455hWindows16
import LeanLab.DtRS1998.Decomp455hWindows17
import LeanLab.DtRS1998.Decomp455hWindows18
import LeanLab.DtRS1998.Decomp455hWindows19
import LeanLab.DtRS1998.Decomp455hWindows20
import LeanLab.DtRS1998.Decomp455hWindows21
import LeanLab.DtRS1998.Decomp455hWindows22
import LeanLab.DtRS1998.Decomp455hWindows23
import LeanLab.DtRS1998.Decomp455hWindows24

namespace LeanLab.DtRS1998.Decomp455h

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
The complete coverage quarter 2 has small prime complements.
No 300 digit primality assertion is used. -/
theorem cover_block2 : ∀ j : ℕ, 125000000 ≤ j → j < 250000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj
  by_cases h0 : j < 126000000
  · exact Decomp455f.prefix2 j hj0 h0
  by_cases h126 : j < 127000000
  · exact window126 j (by omega) h126
  by_cases h127 : j < 128000000
  · exact window127 j (by omega) h127
  by_cases h128 : j < 129000000
  · exact window128 j (by omega) h128
  by_cases h129 : j < 130000000
  · exact window129 j (by omega) h129
  by_cases h130 : j < 131000000
  · exact window130 j (by omega) h130
  by_cases h131 : j < 132000000
  · exact window131 j (by omega) h131
  by_cases h132 : j < 133000000
  · exact window132 j (by omega) h132
  by_cases h133 : j < 134000000
  · exact window133 j (by omega) h133
  by_cases h134 : j < 135000000
  · exact window134 j (by omega) h134
  by_cases h135 : j < 136000000
  · exact window135 j (by omega) h135
  by_cases h136 : j < 137000000
  · exact window136 j (by omega) h136
  by_cases h137 : j < 138000000
  · exact window137 j (by omega) h137
  by_cases h138 : j < 139000000
  · exact window138 j (by omega) h138
  by_cases h139 : j < 140000000
  · exact window139 j (by omega) h139
  by_cases h140 : j < 141000000
  · exact window140 j (by omega) h140
  by_cases h141 : j < 142000000
  · exact window141 j (by omega) h141
  by_cases h142 : j < 143000000
  · exact window142 j (by omega) h142
  by_cases h143 : j < 144000000
  · exact window143 j (by omega) h143
  by_cases h144 : j < 145000000
  · exact window144 j (by omega) h144
  by_cases h145 : j < 146000000
  · exact window145 j (by omega) h145
  by_cases h146 : j < 147000000
  · exact window146 j (by omega) h146
  by_cases h147 : j < 148000000
  · exact window147 j (by omega) h147
  by_cases h148 : j < 149000000
  · exact window148 j (by omega) h148
  by_cases h149 : j < 150000000
  · exact window149 j (by omega) h149
  by_cases h150 : j < 151000000
  · exact window150 j (by omega) h150
  by_cases h151 : j < 152000000
  · exact window151 j (by omega) h151
  by_cases h152 : j < 153000000
  · exact window152 j (by omega) h152
  by_cases h153 : j < 154000000
  · exact window153 j (by omega) h153
  by_cases h154 : j < 155000000
  · exact window154 j (by omega) h154
  by_cases h155 : j < 156000000
  · exact window155 j (by omega) h155
  by_cases h156 : j < 157000000
  · exact window156 j (by omega) h156
  by_cases h157 : j < 158000000
  · exact window157 j (by omega) h157
  by_cases h158 : j < 159000000
  · exact window158 j (by omega) h158
  by_cases h159 : j < 160000000
  · exact window159 j (by omega) h159
  by_cases h160 : j < 161000000
  · exact window160 j (by omega) h160
  by_cases h161 : j < 162000000
  · exact window161 j (by omega) h161
  by_cases h162 : j < 163000000
  · exact window162 j (by omega) h162
  by_cases h163 : j < 164000000
  · exact window163 j (by omega) h163
  by_cases h164 : j < 165000000
  · exact window164 j (by omega) h164
  by_cases h165 : j < 166000000
  · exact window165 j (by omega) h165
  by_cases h166 : j < 167000000
  · exact window166 j (by omega) h166
  by_cases h167 : j < 168000000
  · exact window167 j (by omega) h167
  by_cases h168 : j < 169000000
  · exact window168 j (by omega) h168
  by_cases h169 : j < 170000000
  · exact window169 j (by omega) h169
  by_cases h170 : j < 171000000
  · exact window170 j (by omega) h170
  by_cases h171 : j < 172000000
  · exact window171 j (by omega) h171
  by_cases h172 : j < 173000000
  · exact window172 j (by omega) h172
  by_cases h173 : j < 174000000
  · exact window173 j (by omega) h173
  by_cases h174 : j < 175000000
  · exact window174 j (by omega) h174
  by_cases h175 : j < 176000000
  · exact window175 j (by omega) h175
  by_cases h176 : j < 177000000
  · exact window176 j (by omega) h176
  by_cases h177 : j < 178000000
  · exact window177 j (by omega) h177
  by_cases h178 : j < 179000000
  · exact window178 j (by omega) h178
  by_cases h179 : j < 180000000
  · exact window179 j (by omega) h179
  by_cases h180 : j < 181000000
  · exact window180 j (by omega) h180
  by_cases h181 : j < 182000000
  · exact window181 j (by omega) h181
  by_cases h182 : j < 183000000
  · exact window182 j (by omega) h182
  by_cases h183 : j < 184000000
  · exact window183 j (by omega) h183
  by_cases h184 : j < 185000000
  · exact window184 j (by omega) h184
  by_cases h185 : j < 186000000
  · exact window185 j (by omega) h185
  by_cases h186 : j < 187000000
  · exact window186 j (by omega) h186
  by_cases h187 : j < 188000000
  · exact window187 j (by omega) h187
  by_cases h188 : j < 189000000
  · exact window188 j (by omega) h188
  by_cases h189 : j < 190000000
  · exact window189 j (by omega) h189
  by_cases h190 : j < 191000000
  · exact window190 j (by omega) h190
  by_cases h191 : j < 192000000
  · exact window191 j (by omega) h191
  by_cases h192 : j < 193000000
  · exact window192 j (by omega) h192
  by_cases h193 : j < 194000000
  · exact window193 j (by omega) h193
  by_cases h194 : j < 195000000
  · exact window194 j (by omega) h194
  by_cases h195 : j < 196000000
  · exact window195 j (by omega) h195
  by_cases h196 : j < 197000000
  · exact window196 j (by omega) h196
  by_cases h197 : j < 198000000
  · exact window197 j (by omega) h197
  by_cases h198 : j < 199000000
  · exact window198 j (by omega) h198
  by_cases h199 : j < 200000000
  · exact window199 j (by omega) h199
  by_cases h200 : j < 201000000
  · exact window200 j (by omega) h200
  by_cases h201 : j < 202000000
  · exact window201 j (by omega) h201
  by_cases h202 : j < 203000000
  · exact window202 j (by omega) h202
  by_cases h203 : j < 204000000
  · exact window203 j (by omega) h203
  by_cases h204 : j < 205000000
  · exact window204 j (by omega) h204
  by_cases h205 : j < 206000000
  · exact window205 j (by omega) h205
  by_cases h206 : j < 207000000
  · exact window206 j (by omega) h206
  by_cases h207 : j < 208000000
  · exact window207 j (by omega) h207
  by_cases h208 : j < 209000000
  · exact window208 j (by omega) h208
  by_cases h209 : j < 210000000
  · exact window209 j (by omega) h209
  by_cases h210 : j < 211000000
  · exact window210 j (by omega) h210
  by_cases h211 : j < 212000000
  · exact window211 j (by omega) h211
  by_cases h212 : j < 213000000
  · exact window212 j (by omega) h212
  by_cases h213 : j < 214000000
  · exact window213 j (by omega) h213
  by_cases h214 : j < 215000000
  · exact window214 j (by omega) h214
  by_cases h215 : j < 216000000
  · exact window215 j (by omega) h215
  by_cases h216 : j < 217000000
  · exact window216 j (by omega) h216
  by_cases h217 : j < 218000000
  · exact window217 j (by omega) h217
  by_cases h218 : j < 219000000
  · exact window218 j (by omega) h218
  by_cases h219 : j < 220000000
  · exact window219 j (by omega) h219
  by_cases h220 : j < 221000000
  · exact window220 j (by omega) h220
  by_cases h221 : j < 222000000
  · exact window221 j (by omega) h221
  by_cases h222 : j < 223000000
  · exact window222 j (by omega) h222
  by_cases h223 : j < 224000000
  · exact window223 j (by omega) h223
  by_cases h224 : j < 225000000
  · exact window224 j (by omega) h224
  by_cases h225 : j < 226000000
  · exact window225 j (by omega) h225
  by_cases h226 : j < 227000000
  · exact window226 j (by omega) h226
  by_cases h227 : j < 228000000
  · exact window227 j (by omega) h227
  by_cases h228 : j < 229000000
  · exact window228 j (by omega) h228
  by_cases h229 : j < 230000000
  · exact window229 j (by omega) h229
  by_cases h230 : j < 231000000
  · exact window230 j (by omega) h230
  by_cases h231 : j < 232000000
  · exact window231 j (by omega) h231
  by_cases h232 : j < 233000000
  · exact window232 j (by omega) h232
  by_cases h233 : j < 234000000
  · exact window233 j (by omega) h233
  by_cases h234 : j < 235000000
  · exact window234 j (by omega) h234
  by_cases h235 : j < 236000000
  · exact window235 j (by omega) h235
  by_cases h236 : j < 237000000
  · exact window236 j (by omega) h236
  by_cases h237 : j < 238000000
  · exact window237 j (by omega) h237
  by_cases h238 : j < 239000000
  · exact window238 j (by omega) h238
  by_cases h239 : j < 240000000
  · exact window239 j (by omega) h239
  by_cases h240 : j < 241000000
  · exact window240 j (by omega) h240
  by_cases h241 : j < 242000000
  · exact window241 j (by omega) h241
  by_cases h242 : j < 243000000
  · exact window242 j (by omega) h242
  by_cases h243 : j < 244000000
  · exact window243 j (by omega) h243
  by_cases h244 : j < 245000000
  · exact window244 j (by omega) h244
  by_cases h245 : j < 246000000
  · exact window245 j (by omega) h245
  by_cases h246 : j < 247000000
  · exact window246 j (by omega) h246
  by_cases h247 : j < 248000000
  · exact window247 j (by omega) h247
  by_cases h248 : j < 249000000
  · exact window248 j (by omega) h248
  exact window249 j (by omega) (by omega)

#print axioms cover_block2

end LeanLab.DtRS1998.Decomp455h
