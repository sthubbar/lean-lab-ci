/-
Chain block MU4: windows MU301 to MU327, from SmallGBUpTo 1789 298000000 to SmallGBUpTo 1789 324730000.
Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.MinGBBase
import LeanLab.Verifications.Top50.BitMUG31
import LeanLab.Verifications.Top50.BitMUG32
import LeanLab.Verifications.Top50.BitMUG33

namespace LeanLab.Verifications.Top50.Bits

theorem msmall_u301 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 298990000 :=
  small_extend2 (a := 298000000) (A := 298000002) (lo := 297998190) (W := 991810) h
    ⟨149000000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u301

theorem msmall_u302 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 299980000 :=
  small_extend2 (a := 298990000) (A := 298990002) (lo := 298988190) (W := 991810) (msmall_u301 h)
    ⟨149495000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u302

theorem msmall_u303 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 300970000 :=
  small_extend2 (a := 299980000) (A := 299980002) (lo := 299978190) (W := 991810) (msmall_u302 h)
    ⟨149990000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u303

theorem msmall_u304 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 301960000 :=
  small_extend2 (a := 300970000) (A := 300970002) (lo := 300968190) (W := 991810) (msmall_u303 h)
    ⟨150485000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u304

theorem msmall_u305 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 302950000 :=
  small_extend2 (a := 301960000) (A := 301960002) (lo := 301958190) (W := 991810) (msmall_u304 h)
    ⟨150980000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u305

theorem msmall_u306 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 303940000 :=
  small_extend2 (a := 302950000) (A := 302950002) (lo := 302948190) (W := 991810) (msmall_u305 h)
    ⟨151475000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u306

theorem msmall_u307 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 304930000 :=
  small_extend2 (a := 303940000) (A := 303940002) (lo := 303938190) (W := 991810) (msmall_u306 h)
    ⟨151970000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u307

theorem msmall_u308 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 305920000 :=
  small_extend2 (a := 304930000) (A := 304930002) (lo := 304928190) (W := 991810) (msmall_u307 h)
    ⟨152465000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u308

theorem msmall_u309 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 306910000 :=
  small_extend2 (a := 305920000) (A := 305920002) (lo := 305918190) (W := 991810) (msmall_u308 h)
    ⟨152960000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u309

theorem msmall_u310 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 307900000 :=
  small_extend2 (a := 306910000) (A := 306910002) (lo := 306908190) (W := 991810) (msmall_u309 h)
    ⟨153455000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u310

theorem msmall_u311 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 308890000 :=
  small_extend2 (a := 307900000) (A := 307900002) (lo := 307898190) (W := 991810) (msmall_u310 h)
    ⟨153950000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u311

theorem msmall_u312 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 309880000 :=
  small_extend2 (a := 308890000) (A := 308890002) (lo := 308888190) (W := 991810) (msmall_u311 h)
    ⟨154445000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u312

theorem msmall_u313 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 310870000 :=
  small_extend2 (a := 309880000) (A := 309880002) (lo := 309878190) (W := 991810) (msmall_u312 h)
    ⟨154940000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u313

theorem msmall_u314 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 311860000 :=
  small_extend2 (a := 310870000) (A := 310870002) (lo := 310868190) (W := 991810) (msmall_u313 h)
    ⟨155435000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u314

theorem msmall_u315 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 312850000 :=
  small_extend2 (a := 311860000) (A := 311860002) (lo := 311858190) (W := 991810) (msmall_u314 h)
    ⟨155930000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u315

theorem msmall_u316 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 313840000 :=
  small_extend2 (a := 312850000) (A := 312850002) (lo := 312848190) (W := 991810) (msmall_u315 h)
    ⟨156425000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u316

theorem msmall_u317 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 314830000 :=
  small_extend2 (a := 313840000) (A := 313840002) (lo := 313838190) (W := 991810) (msmall_u316 h)
    ⟨156920000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u317

theorem msmall_u318 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 315820000 :=
  small_extend2 (a := 314830000) (A := 314830002) (lo := 314828190) (W := 991810) (msmall_u317 h)
    ⟨157415000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u318

theorem msmall_u319 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 316810000 :=
  small_extend2 (a := 315820000) (A := 315820002) (lo := 315818190) (W := 991810) (msmall_u318 h)
    ⟨157910000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u319

theorem msmall_u320 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 317800000 :=
  small_extend2 (a := 316810000) (A := 316810002) (lo := 316808190) (W := 991810) (msmall_u319 h)
    ⟨158405000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u320

theorem msmall_u321 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 318790000 :=
  small_extend2 (a := 317800000) (A := 317800002) (lo := 317798190) (W := 991810) (msmall_u320 h)
    ⟨158900000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u321

theorem msmall_u322 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 319780000 :=
  small_extend2 (a := 318790000) (A := 318790002) (lo := 318788190) (W := 991810) (msmall_u321 h)
    ⟨159395000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u322

theorem msmall_u323 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 320770000 :=
  small_extend2 (a := 319780000) (A := 319780002) (lo := 319778190) (W := 991810) (msmall_u322 h)
    ⟨159890000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u323

theorem msmall_u324 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 321760000 :=
  small_extend2 (a := 320770000) (A := 320770002) (lo := 320768190) (W := 991810) (msmall_u323 h)
    ⟨160385000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u324

theorem msmall_u325 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 322750000 :=
  small_extend2 (a := 321760000) (A := 321760002) (lo := 321758190) (W := 991810) (msmall_u324 h)
    ⟨160880000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u325

theorem msmall_u326 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 323740000 :=
  small_extend2 (a := 322750000) (A := 322750002) (lo := 322748190) (W := 991810) (msmall_u325 h)
    ⟨161375000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u326

theorem msmall_u327 (h : SmallGBUpTo 1789 298000000) : SmallGBUpTo 1789 324730000 :=
  small_extend2 (a := 323740000) (A := 323740002) (lo := 323738190) (W := 991810) (msmall_u326 h)
    ⟨161870000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u327

end LeanLab.Verifications.Top50.Bits
