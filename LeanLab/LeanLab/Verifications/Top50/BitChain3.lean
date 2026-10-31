/-
Chain block 3 of the kernel Goldbach windows past 10^8: windows 151 to 163, from
EvenGoldbachUpTo 298000000 to EvenGoldbachUpTo 323740000, so the blocks compose. Each step is upTo_extend2 in BitSieve2.lean.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2
import LeanLab.Verifications.Top50.BitW151
import LeanLab.Verifications.Top50.BitW152
import LeanLab.Verifications.Top50.BitW153
import LeanLab.Verifications.Top50.BitW154
import LeanLab.Verifications.Top50.BitW155
import LeanLab.Verifications.Top50.BitW156
import LeanLab.Verifications.Top50.BitW157
import LeanLab.Verifications.Top50.BitW158
import LeanLab.Verifications.Top50.BitW159
import LeanLab.Verifications.Top50.BitW160
import LeanLab.Verifications.Top50.BitW161
import LeanLab.Verifications.Top50.BitW162
import LeanLab.Verifications.Top50.BitW163

namespace LeanLab.Verifications.Top50.Bits

theorem upTo_w151 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 299980000 :=
  upTo_extend2 (a := 298000000) (A := 298000002) (lo := 297998190) (W := 1981810) h
    ⟨149000000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_151

theorem upTo_w152 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 301960000 :=
  upTo_extend2 (a := 299980000) (A := 299980002) (lo := 299978190) (W := 1981810) (upTo_w151 h)
    ⟨149990000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_152

theorem upTo_w153 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 303940000 :=
  upTo_extend2 (a := 301960000) (A := 301960002) (lo := 301958190) (W := 1981810) (upTo_w152 h)
    ⟨150980000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_153

theorem upTo_w154 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 305920000 :=
  upTo_extend2 (a := 303940000) (A := 303940002) (lo := 303938190) (W := 1981810) (upTo_w153 h)
    ⟨151970000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_154

theorem upTo_w155 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 307900000 :=
  upTo_extend2 (a := 305920000) (A := 305920002) (lo := 305918190) (W := 1981810) (upTo_w154 h)
    ⟨152960000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_155

theorem upTo_w156 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 309880000 :=
  upTo_extend2 (a := 307900000) (A := 307900002) (lo := 307898190) (W := 1981810) (upTo_w155 h)
    ⟨153950000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_156

theorem upTo_w157 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 311860000 :=
  upTo_extend2 (a := 309880000) (A := 309880002) (lo := 309878190) (W := 1981810) (upTo_w156 h)
    ⟨154940000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_157

theorem upTo_w158 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 313840000 :=
  upTo_extend2 (a := 311860000) (A := 311860002) (lo := 311858190) (W := 1981810) (upTo_w157 h)
    ⟨155930000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_158

theorem upTo_w159 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 315820000 :=
  upTo_extend2 (a := 313840000) (A := 313840002) (lo := 313838190) (W := 1981810) (upTo_w158 h)
    ⟨156920000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_159

theorem upTo_w160 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 317800000 :=
  upTo_extend2 (a := 315820000) (A := 315820002) (lo := 315818190) (W := 1981810) (upTo_w159 h)
    ⟨157910000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_160

theorem upTo_w161 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 319780000 :=
  upTo_extend2 (a := 317800000) (A := 317800002) (lo := 317798190) (W := 1981810) (upTo_w160 h)
    ⟨158900000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_161

theorem upTo_w162 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 321760000 :=
  upTo_extend2 (a := 319780000) (A := 319780002) (lo := 319778190) (W := 1981810) (upTo_w161 h)
    ⟨159890000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_162

theorem upTo_w163 (h : EvenGoldbachUpTo 298000000) : EvenGoldbachUpTo 323740000 :=
  upTo_extend2 (a := 321760000) (A := 321760002) (lo := 321758190) (W := 1981810) (upTo_w162 h)
    ⟨160880000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_163

end LeanLab.Verifications.Top50.Bits
