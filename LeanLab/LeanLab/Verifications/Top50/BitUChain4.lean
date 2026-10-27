/-
Chain block U4 of the kernel Goldbach windows from 10^6: windows U301 to U327, from
SmallGBUpTo 1811 298000000 to SmallGBUpTo 1811 324730000, so the blocks compose. Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.SmallGB
import LeanLab.Verifications.Top50.BitUG31
import LeanLab.Verifications.Top50.BitUG32
import LeanLab.Verifications.Top50.BitUG33

namespace LeanLab.Verifications.Top50.Bits

theorem small_u301 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 298990000 :=
  small_extend2 (a := 298000000) (A := 298000002) (lo := 297998190) (W := 991810) h
    ⟨149000000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u301

theorem small_u302 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 299980000 :=
  small_extend2 (a := 298990000) (A := 298990002) (lo := 298988190) (W := 991810) (small_u301 h)
    ⟨149495000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u302

theorem small_u303 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 300970000 :=
  small_extend2 (a := 299980000) (A := 299980002) (lo := 299978190) (W := 991810) (small_u302 h)
    ⟨149990000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u303

theorem small_u304 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 301960000 :=
  small_extend2 (a := 300970000) (A := 300970002) (lo := 300968190) (W := 991810) (small_u303 h)
    ⟨150485000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u304

theorem small_u305 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 302950000 :=
  small_extend2 (a := 301960000) (A := 301960002) (lo := 301958190) (W := 991810) (small_u304 h)
    ⟨150980000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u305

theorem small_u306 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 303940000 :=
  small_extend2 (a := 302950000) (A := 302950002) (lo := 302948190) (W := 991810) (small_u305 h)
    ⟨151475000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u306

theorem small_u307 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 304930000 :=
  small_extend2 (a := 303940000) (A := 303940002) (lo := 303938190) (W := 991810) (small_u306 h)
    ⟨151970000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u307

theorem small_u308 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 305920000 :=
  small_extend2 (a := 304930000) (A := 304930002) (lo := 304928190) (W := 991810) (small_u307 h)
    ⟨152465000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u308

theorem small_u309 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 306910000 :=
  small_extend2 (a := 305920000) (A := 305920002) (lo := 305918190) (W := 991810) (small_u308 h)
    ⟨152960000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u309

theorem small_u310 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 307900000 :=
  small_extend2 (a := 306910000) (A := 306910002) (lo := 306908190) (W := 991810) (small_u309 h)
    ⟨153455000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u310

theorem small_u311 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 308890000 :=
  small_extend2 (a := 307900000) (A := 307900002) (lo := 307898190) (W := 991810) (small_u310 h)
    ⟨153950000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u311

theorem small_u312 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 309880000 :=
  small_extend2 (a := 308890000) (A := 308890002) (lo := 308888190) (W := 991810) (small_u311 h)
    ⟨154445000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u312

theorem small_u313 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 310870000 :=
  small_extend2 (a := 309880000) (A := 309880002) (lo := 309878190) (W := 991810) (small_u312 h)
    ⟨154940000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u313

theorem small_u314 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 311860000 :=
  small_extend2 (a := 310870000) (A := 310870002) (lo := 310868190) (W := 991810) (small_u313 h)
    ⟨155435000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u314

theorem small_u315 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 312850000 :=
  small_extend2 (a := 311860000) (A := 311860002) (lo := 311858190) (W := 991810) (small_u314 h)
    ⟨155930000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u315

theorem small_u316 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 313840000 :=
  small_extend2 (a := 312850000) (A := 312850002) (lo := 312848190) (W := 991810) (small_u315 h)
    ⟨156425000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u316

theorem small_u317 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 314830000 :=
  small_extend2 (a := 313840000) (A := 313840002) (lo := 313838190) (W := 991810) (small_u316 h)
    ⟨156920000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u317

theorem small_u318 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 315820000 :=
  small_extend2 (a := 314830000) (A := 314830002) (lo := 314828190) (W := 991810) (small_u317 h)
    ⟨157415000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u318

theorem small_u319 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 316810000 :=
  small_extend2 (a := 315820000) (A := 315820002) (lo := 315818190) (W := 991810) (small_u318 h)
    ⟨157910000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u319

theorem small_u320 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 317800000 :=
  small_extend2 (a := 316810000) (A := 316810002) (lo := 316808190) (W := 991810) (small_u319 h)
    ⟨158405000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u320

theorem small_u321 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 318790000 :=
  small_extend2 (a := 317800000) (A := 317800002) (lo := 317798190) (W := 991810) (small_u320 h)
    ⟨158900000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u321

theorem small_u322 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 319780000 :=
  small_extend2 (a := 318790000) (A := 318790002) (lo := 318788190) (W := 991810) (small_u321 h)
    ⟨159395000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u322

theorem small_u323 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 320770000 :=
  small_extend2 (a := 319780000) (A := 319780002) (lo := 319778190) (W := 991810) (small_u322 h)
    ⟨159890000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u323

theorem small_u324 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 321760000 :=
  small_extend2 (a := 320770000) (A := 320770002) (lo := 320768190) (W := 991810) (small_u323 h)
    ⟨160385000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u324

theorem small_u325 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 322750000 :=
  small_extend2 (a := 321760000) (A := 321760002) (lo := 321758190) (W := 991810) (small_u324 h)
    ⟨160880000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u325

theorem small_u326 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 323740000 :=
  small_extend2 (a := 322750000) (A := 322750002) (lo := 322748190) (W := 991810) (small_u325 h)
    ⟨161375000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u326

theorem small_u327 (h : SmallGBUpTo 1811 298000000) : SmallGBUpTo 1811 324730000 :=
  small_extend2 (a := 323740000) (A := 323740002) (lo := 323738190) (W := 991810) (small_u326 h)
    ⟨161870000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u327

end LeanLab.Verifications.Top50.Bits
