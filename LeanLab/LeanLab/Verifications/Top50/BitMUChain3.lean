/-
Chain block MU3: windows MU201 to MU300, from SmallGBUpTo 1789 199000000 to SmallGBUpTo 1789 298000000.
Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.MinGBBase
import LeanLab.Verifications.Top50.BitMUG21
import LeanLab.Verifications.Top50.BitMUG22
import LeanLab.Verifications.Top50.BitMUG23
import LeanLab.Verifications.Top50.BitMUG24
import LeanLab.Verifications.Top50.BitMUG25
import LeanLab.Verifications.Top50.BitMUG26
import LeanLab.Verifications.Top50.BitMUG27
import LeanLab.Verifications.Top50.BitMUG28
import LeanLab.Verifications.Top50.BitMUG29
import LeanLab.Verifications.Top50.BitMUG30

namespace LeanLab.Verifications.Top50.Bits

theorem msmall_u201 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 199990000 :=
  small_extend2 (a := 199000000) (A := 199000002) (lo := 198998190) (W := 991810) h
    ⟨99500000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u201

theorem msmall_u202 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 200980000 :=
  small_extend2 (a := 199990000) (A := 199990002) (lo := 199988190) (W := 991810) (msmall_u201 h)
    ⟨99995000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u202

theorem msmall_u203 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 201970000 :=
  small_extend2 (a := 200980000) (A := 200980002) (lo := 200978190) (W := 991810) (msmall_u202 h)
    ⟨100490000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u203

theorem msmall_u204 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 202960000 :=
  small_extend2 (a := 201970000) (A := 201970002) (lo := 201968190) (W := 991810) (msmall_u203 h)
    ⟨100985000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u204

theorem msmall_u205 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 203950000 :=
  small_extend2 (a := 202960000) (A := 202960002) (lo := 202958190) (W := 991810) (msmall_u204 h)
    ⟨101480000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u205

theorem msmall_u206 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 204940000 :=
  small_extend2 (a := 203950000) (A := 203950002) (lo := 203948190) (W := 991810) (msmall_u205 h)
    ⟨101975000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u206

theorem msmall_u207 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 205930000 :=
  small_extend2 (a := 204940000) (A := 204940002) (lo := 204938190) (W := 991810) (msmall_u206 h)
    ⟨102470000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u207

theorem msmall_u208 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 206920000 :=
  small_extend2 (a := 205930000) (A := 205930002) (lo := 205928190) (W := 991810) (msmall_u207 h)
    ⟨102965000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u208

theorem msmall_u209 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 207910000 :=
  small_extend2 (a := 206920000) (A := 206920002) (lo := 206918190) (W := 991810) (msmall_u208 h)
    ⟨103460000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u209

theorem msmall_u210 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 208900000 :=
  small_extend2 (a := 207910000) (A := 207910002) (lo := 207908190) (W := 991810) (msmall_u209 h)
    ⟨103955000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u210

theorem msmall_u211 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 209890000 :=
  small_extend2 (a := 208900000) (A := 208900002) (lo := 208898190) (W := 991810) (msmall_u210 h)
    ⟨104450000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u211

theorem msmall_u212 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 210880000 :=
  small_extend2 (a := 209890000) (A := 209890002) (lo := 209888190) (W := 991810) (msmall_u211 h)
    ⟨104945000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u212

theorem msmall_u213 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 211870000 :=
  small_extend2 (a := 210880000) (A := 210880002) (lo := 210878190) (W := 991810) (msmall_u212 h)
    ⟨105440000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u213

theorem msmall_u214 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 212860000 :=
  small_extend2 (a := 211870000) (A := 211870002) (lo := 211868190) (W := 991810) (msmall_u213 h)
    ⟨105935000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u214

theorem msmall_u215 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 213850000 :=
  small_extend2 (a := 212860000) (A := 212860002) (lo := 212858190) (W := 991810) (msmall_u214 h)
    ⟨106430000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u215

theorem msmall_u216 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 214840000 :=
  small_extend2 (a := 213850000) (A := 213850002) (lo := 213848190) (W := 991810) (msmall_u215 h)
    ⟨106925000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u216

theorem msmall_u217 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 215830000 :=
  small_extend2 (a := 214840000) (A := 214840002) (lo := 214838190) (W := 991810) (msmall_u216 h)
    ⟨107420000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u217

theorem msmall_u218 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 216820000 :=
  small_extend2 (a := 215830000) (A := 215830002) (lo := 215828190) (W := 991810) (msmall_u217 h)
    ⟨107915000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u218

theorem msmall_u219 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 217810000 :=
  small_extend2 (a := 216820000) (A := 216820002) (lo := 216818190) (W := 991810) (msmall_u218 h)
    ⟨108410000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u219

theorem msmall_u220 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 218800000 :=
  small_extend2 (a := 217810000) (A := 217810002) (lo := 217808190) (W := 991810) (msmall_u219 h)
    ⟨108905000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u220

theorem msmall_u221 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 219790000 :=
  small_extend2 (a := 218800000) (A := 218800002) (lo := 218798190) (W := 991810) (msmall_u220 h)
    ⟨109400000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u221

theorem msmall_u222 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 220780000 :=
  small_extend2 (a := 219790000) (A := 219790002) (lo := 219788190) (W := 991810) (msmall_u221 h)
    ⟨109895000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u222

theorem msmall_u223 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 221770000 :=
  small_extend2 (a := 220780000) (A := 220780002) (lo := 220778190) (W := 991810) (msmall_u222 h)
    ⟨110390000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u223

theorem msmall_u224 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 222760000 :=
  small_extend2 (a := 221770000) (A := 221770002) (lo := 221768190) (W := 991810) (msmall_u223 h)
    ⟨110885000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u224

theorem msmall_u225 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 223750000 :=
  small_extend2 (a := 222760000) (A := 222760002) (lo := 222758190) (W := 991810) (msmall_u224 h)
    ⟨111380000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u225

theorem msmall_u226 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 224740000 :=
  small_extend2 (a := 223750000) (A := 223750002) (lo := 223748190) (W := 991810) (msmall_u225 h)
    ⟨111875000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u226

theorem msmall_u227 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 225730000 :=
  small_extend2 (a := 224740000) (A := 224740002) (lo := 224738190) (W := 991810) (msmall_u226 h)
    ⟨112370000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u227

theorem msmall_u228 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 226720000 :=
  small_extend2 (a := 225730000) (A := 225730002) (lo := 225728190) (W := 991810) (msmall_u227 h)
    ⟨112865000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u228

theorem msmall_u229 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 227710000 :=
  small_extend2 (a := 226720000) (A := 226720002) (lo := 226718190) (W := 991810) (msmall_u228 h)
    ⟨113360000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u229

theorem msmall_u230 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 228700000 :=
  small_extend2 (a := 227710000) (A := 227710002) (lo := 227708190) (W := 991810) (msmall_u229 h)
    ⟨113855000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u230

theorem msmall_u231 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 229690000 :=
  small_extend2 (a := 228700000) (A := 228700002) (lo := 228698190) (W := 991810) (msmall_u230 h)
    ⟨114350000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u231

theorem msmall_u232 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 230680000 :=
  small_extend2 (a := 229690000) (A := 229690002) (lo := 229688190) (W := 991810) (msmall_u231 h)
    ⟨114845000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u232

theorem msmall_u233 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 231670000 :=
  small_extend2 (a := 230680000) (A := 230680002) (lo := 230678190) (W := 991810) (msmall_u232 h)
    ⟨115340000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u233

theorem msmall_u234 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 232660000 :=
  small_extend2 (a := 231670000) (A := 231670002) (lo := 231668190) (W := 991810) (msmall_u233 h)
    ⟨115835000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u234

theorem msmall_u235 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 233650000 :=
  small_extend2 (a := 232660000) (A := 232660002) (lo := 232658190) (W := 991810) (msmall_u234 h)
    ⟨116330000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u235

theorem msmall_u236 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 234640000 :=
  small_extend2 (a := 233650000) (A := 233650002) (lo := 233648190) (W := 991810) (msmall_u235 h)
    ⟨116825000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u236

theorem msmall_u237 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 235630000 :=
  small_extend2 (a := 234640000) (A := 234640002) (lo := 234638190) (W := 991810) (msmall_u236 h)
    ⟨117320000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u237

theorem msmall_u238 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 236620000 :=
  small_extend2 (a := 235630000) (A := 235630002) (lo := 235628190) (W := 991810) (msmall_u237 h)
    ⟨117815000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u238

theorem msmall_u239 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 237610000 :=
  small_extend2 (a := 236620000) (A := 236620002) (lo := 236618190) (W := 991810) (msmall_u238 h)
    ⟨118310000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u239

theorem msmall_u240 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 238600000 :=
  small_extend2 (a := 237610000) (A := 237610002) (lo := 237608190) (W := 991810) (msmall_u239 h)
    ⟨118805000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u240

theorem msmall_u241 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 239590000 :=
  small_extend2 (a := 238600000) (A := 238600002) (lo := 238598190) (W := 991810) (msmall_u240 h)
    ⟨119300000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u241

theorem msmall_u242 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 240580000 :=
  small_extend2 (a := 239590000) (A := 239590002) (lo := 239588190) (W := 991810) (msmall_u241 h)
    ⟨119795000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u242

theorem msmall_u243 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 241570000 :=
  small_extend2 (a := 240580000) (A := 240580002) (lo := 240578190) (W := 991810) (msmall_u242 h)
    ⟨120290000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u243

theorem msmall_u244 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 242560000 :=
  small_extend2 (a := 241570000) (A := 241570002) (lo := 241568190) (W := 991810) (msmall_u243 h)
    ⟨120785000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u244

theorem msmall_u245 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 243550000 :=
  small_extend2 (a := 242560000) (A := 242560002) (lo := 242558190) (W := 991810) (msmall_u244 h)
    ⟨121280000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u245

theorem msmall_u246 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 244540000 :=
  small_extend2 (a := 243550000) (A := 243550002) (lo := 243548190) (W := 991810) (msmall_u245 h)
    ⟨121775000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u246

theorem msmall_u247 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 245530000 :=
  small_extend2 (a := 244540000) (A := 244540002) (lo := 244538190) (W := 991810) (msmall_u246 h)
    ⟨122270000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u247

theorem msmall_u248 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 246520000 :=
  small_extend2 (a := 245530000) (A := 245530002) (lo := 245528190) (W := 991810) (msmall_u247 h)
    ⟨122765000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u248

theorem msmall_u249 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 247510000 :=
  small_extend2 (a := 246520000) (A := 246520002) (lo := 246518190) (W := 991810) (msmall_u248 h)
    ⟨123260000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u249

theorem msmall_u250 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 248500000 :=
  small_extend2 (a := 247510000) (A := 247510002) (lo := 247508190) (W := 991810) (msmall_u249 h)
    ⟨123755000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u250

theorem msmall_u251 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 249490000 :=
  small_extend2 (a := 248500000) (A := 248500002) (lo := 248498190) (W := 991810) (msmall_u250 h)
    ⟨124250000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u251

theorem msmall_u252 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 250480000 :=
  small_extend2 (a := 249490000) (A := 249490002) (lo := 249488190) (W := 991810) (msmall_u251 h)
    ⟨124745000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u252

theorem msmall_u253 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 251470000 :=
  small_extend2 (a := 250480000) (A := 250480002) (lo := 250478190) (W := 991810) (msmall_u252 h)
    ⟨125240000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u253

theorem msmall_u254 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 252460000 :=
  small_extend2 (a := 251470000) (A := 251470002) (lo := 251468190) (W := 991810) (msmall_u253 h)
    ⟨125735000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u254

theorem msmall_u255 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 253450000 :=
  small_extend2 (a := 252460000) (A := 252460002) (lo := 252458190) (W := 991810) (msmall_u254 h)
    ⟨126230000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u255

theorem msmall_u256 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 254440000 :=
  small_extend2 (a := 253450000) (A := 253450002) (lo := 253448190) (W := 991810) (msmall_u255 h)
    ⟨126725000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u256

theorem msmall_u257 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 255430000 :=
  small_extend2 (a := 254440000) (A := 254440002) (lo := 254438190) (W := 991810) (msmall_u256 h)
    ⟨127220000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u257

theorem msmall_u258 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 256420000 :=
  small_extend2 (a := 255430000) (A := 255430002) (lo := 255428190) (W := 991810) (msmall_u257 h)
    ⟨127715000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u258

theorem msmall_u259 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 257410000 :=
  small_extend2 (a := 256420000) (A := 256420002) (lo := 256418190) (W := 991810) (msmall_u258 h)
    ⟨128210000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u259

theorem msmall_u260 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 258400000 :=
  small_extend2 (a := 257410000) (A := 257410002) (lo := 257408190) (W := 991810) (msmall_u259 h)
    ⟨128705000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u260

theorem msmall_u261 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 259390000 :=
  small_extend2 (a := 258400000) (A := 258400002) (lo := 258398190) (W := 991810) (msmall_u260 h)
    ⟨129200000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u261

theorem msmall_u262 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 260380000 :=
  small_extend2 (a := 259390000) (A := 259390002) (lo := 259388190) (W := 991810) (msmall_u261 h)
    ⟨129695000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u262

theorem msmall_u263 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 261370000 :=
  small_extend2 (a := 260380000) (A := 260380002) (lo := 260378190) (W := 991810) (msmall_u262 h)
    ⟨130190000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u263

theorem msmall_u264 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 262360000 :=
  small_extend2 (a := 261370000) (A := 261370002) (lo := 261368190) (W := 991810) (msmall_u263 h)
    ⟨130685000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u264

theorem msmall_u265 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 263350000 :=
  small_extend2 (a := 262360000) (A := 262360002) (lo := 262358190) (W := 991810) (msmall_u264 h)
    ⟨131180000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u265

theorem msmall_u266 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 264340000 :=
  small_extend2 (a := 263350000) (A := 263350002) (lo := 263348190) (W := 991810) (msmall_u265 h)
    ⟨131675000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u266

theorem msmall_u267 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 265330000 :=
  small_extend2 (a := 264340000) (A := 264340002) (lo := 264338190) (W := 991810) (msmall_u266 h)
    ⟨132170000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u267

theorem msmall_u268 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 266320000 :=
  small_extend2 (a := 265330000) (A := 265330002) (lo := 265328190) (W := 991810) (msmall_u267 h)
    ⟨132665000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u268

theorem msmall_u269 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 267310000 :=
  small_extend2 (a := 266320000) (A := 266320002) (lo := 266318190) (W := 991810) (msmall_u268 h)
    ⟨133160000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u269

theorem msmall_u270 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 268300000 :=
  small_extend2 (a := 267310000) (A := 267310002) (lo := 267308190) (W := 991810) (msmall_u269 h)
    ⟨133655000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u270

theorem msmall_u271 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 269290000 :=
  small_extend2 (a := 268300000) (A := 268300002) (lo := 268298190) (W := 991810) (msmall_u270 h)
    ⟨134150000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u271

theorem msmall_u272 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 270280000 :=
  small_extend2 (a := 269290000) (A := 269290002) (lo := 269288190) (W := 991810) (msmall_u271 h)
    ⟨134645000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u272

theorem msmall_u273 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 271270000 :=
  small_extend2 (a := 270280000) (A := 270280002) (lo := 270278190) (W := 991810) (msmall_u272 h)
    ⟨135140000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u273

theorem msmall_u274 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 272260000 :=
  small_extend2 (a := 271270000) (A := 271270002) (lo := 271268190) (W := 991810) (msmall_u273 h)
    ⟨135635000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u274

theorem msmall_u275 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 273250000 :=
  small_extend2 (a := 272260000) (A := 272260002) (lo := 272258190) (W := 991810) (msmall_u274 h)
    ⟨136130000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u275

theorem msmall_u276 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 274240000 :=
  small_extend2 (a := 273250000) (A := 273250002) (lo := 273248190) (W := 991810) (msmall_u275 h)
    ⟨136625000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u276

theorem msmall_u277 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 275230000 :=
  small_extend2 (a := 274240000) (A := 274240002) (lo := 274238190) (W := 991810) (msmall_u276 h)
    ⟨137120000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u277

theorem msmall_u278 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 276220000 :=
  small_extend2 (a := 275230000) (A := 275230002) (lo := 275228190) (W := 991810) (msmall_u277 h)
    ⟨137615000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u278

theorem msmall_u279 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 277210000 :=
  small_extend2 (a := 276220000) (A := 276220002) (lo := 276218190) (W := 991810) (msmall_u278 h)
    ⟨138110000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u279

theorem msmall_u280 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 278200000 :=
  small_extend2 (a := 277210000) (A := 277210002) (lo := 277208190) (W := 991810) (msmall_u279 h)
    ⟨138605000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u280

theorem msmall_u281 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 279190000 :=
  small_extend2 (a := 278200000) (A := 278200002) (lo := 278198190) (W := 991810) (msmall_u280 h)
    ⟨139100000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u281

theorem msmall_u282 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 280180000 :=
  small_extend2 (a := 279190000) (A := 279190002) (lo := 279188190) (W := 991810) (msmall_u281 h)
    ⟨139595000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u282

theorem msmall_u283 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 281170000 :=
  small_extend2 (a := 280180000) (A := 280180002) (lo := 280178190) (W := 991810) (msmall_u282 h)
    ⟨140090000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u283

theorem msmall_u284 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 282160000 :=
  small_extend2 (a := 281170000) (A := 281170002) (lo := 281168190) (W := 991810) (msmall_u283 h)
    ⟨140585000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u284

theorem msmall_u285 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 283150000 :=
  small_extend2 (a := 282160000) (A := 282160002) (lo := 282158190) (W := 991810) (msmall_u284 h)
    ⟨141080000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u285

theorem msmall_u286 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 284140000 :=
  small_extend2 (a := 283150000) (A := 283150002) (lo := 283148190) (W := 991810) (msmall_u285 h)
    ⟨141575000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u286

theorem msmall_u287 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 285130000 :=
  small_extend2 (a := 284140000) (A := 284140002) (lo := 284138190) (W := 991810) (msmall_u286 h)
    ⟨142070000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u287

theorem msmall_u288 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 286120000 :=
  small_extend2 (a := 285130000) (A := 285130002) (lo := 285128190) (W := 991810) (msmall_u287 h)
    ⟨142565000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u288

theorem msmall_u289 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 287110000 :=
  small_extend2 (a := 286120000) (A := 286120002) (lo := 286118190) (W := 991810) (msmall_u288 h)
    ⟨143060000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u289

theorem msmall_u290 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 288100000 :=
  small_extend2 (a := 287110000) (A := 287110002) (lo := 287108190) (W := 991810) (msmall_u289 h)
    ⟨143555000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u290

theorem msmall_u291 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 289090000 :=
  small_extend2 (a := 288100000) (A := 288100002) (lo := 288098190) (W := 991810) (msmall_u290 h)
    ⟨144050000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u291

theorem msmall_u292 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 290080000 :=
  small_extend2 (a := 289090000) (A := 289090002) (lo := 289088190) (W := 991810) (msmall_u291 h)
    ⟨144545000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u292

theorem msmall_u293 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 291070000 :=
  small_extend2 (a := 290080000) (A := 290080002) (lo := 290078190) (W := 991810) (msmall_u292 h)
    ⟨145040000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u293

theorem msmall_u294 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 292060000 :=
  small_extend2 (a := 291070000) (A := 291070002) (lo := 291068190) (W := 991810) (msmall_u293 h)
    ⟨145535000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u294

theorem msmall_u295 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 293050000 :=
  small_extend2 (a := 292060000) (A := 292060002) (lo := 292058190) (W := 991810) (msmall_u294 h)
    ⟨146030000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u295

theorem msmall_u296 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 294040000 :=
  small_extend2 (a := 293050000) (A := 293050002) (lo := 293048190) (W := 991810) (msmall_u295 h)
    ⟨146525000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u296

theorem msmall_u297 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 295030000 :=
  small_extend2 (a := 294040000) (A := 294040002) (lo := 294038190) (W := 991810) (msmall_u296 h)
    ⟨147020000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u297

theorem msmall_u298 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 296020000 :=
  small_extend2 (a := 295030000) (A := 295030002) (lo := 295028190) (W := 991810) (msmall_u297 h)
    ⟨147515000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u298

theorem msmall_u299 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 297010000 :=
  small_extend2 (a := 296020000) (A := 296020002) (lo := 296018190) (W := 991810) (msmall_u298 h)
    ⟨148010000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u299

theorem msmall_u300 (h : SmallGBUpTo 1789 199000000) : SmallGBUpTo 1789 298000000 :=
  small_extend2 (a := 297010000) (A := 297010002) (lo := 297008190) (W := 991810) (msmall_u299 h)
    ⟨148505000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u300

end LeanLab.Verifications.Top50.Bits
