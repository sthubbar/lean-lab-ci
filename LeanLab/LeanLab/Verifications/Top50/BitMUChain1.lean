/-
Chain block MU1: windows MU1 to MU100, from SmallGBUpTo 1789 1000000 to SmallGBUpTo 1789 100000000.
Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.MinGBBase
import LeanLab.Verifications.Top50.BitMUG1
import LeanLab.Verifications.Top50.BitMUG2
import LeanLab.Verifications.Top50.BitMUG3
import LeanLab.Verifications.Top50.BitMUG4
import LeanLab.Verifications.Top50.BitMUG5
import LeanLab.Verifications.Top50.BitMUG6
import LeanLab.Verifications.Top50.BitMUG7
import LeanLab.Verifications.Top50.BitMUG8
import LeanLab.Verifications.Top50.BitMUG9
import LeanLab.Verifications.Top50.BitMUG10

namespace LeanLab.Verifications.Top50.Bits

theorem msmall_u1 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 1990000 :=
  small_extend2 (a := 1000000) (A := 1000002) (lo := 998190) (W := 991810) h
    ⟨500000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u1

theorem msmall_u2 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 2980000 :=
  small_extend2 (a := 1990000) (A := 1990002) (lo := 1988190) (W := 991810) (msmall_u1 h)
    ⟨995000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u2

theorem msmall_u3 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 3970000 :=
  small_extend2 (a := 2980000) (A := 2980002) (lo := 2978190) (W := 991810) (msmall_u2 h)
    ⟨1490000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u3

theorem msmall_u4 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 4960000 :=
  small_extend2 (a := 3970000) (A := 3970002) (lo := 3968190) (W := 991810) (msmall_u3 h)
    ⟨1985000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u4

theorem msmall_u5 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 5950000 :=
  small_extend2 (a := 4960000) (A := 4960002) (lo := 4958190) (W := 991810) (msmall_u4 h)
    ⟨2480000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u5

theorem msmall_u6 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 6940000 :=
  small_extend2 (a := 5950000) (A := 5950002) (lo := 5948190) (W := 991810) (msmall_u5 h)
    ⟨2975000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u6

theorem msmall_u7 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 7930000 :=
  small_extend2 (a := 6940000) (A := 6940002) (lo := 6938190) (W := 991810) (msmall_u6 h)
    ⟨3470000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u7

theorem msmall_u8 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 8920000 :=
  small_extend2 (a := 7930000) (A := 7930002) (lo := 7928190) (W := 991810) (msmall_u7 h)
    ⟨3965000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u8

theorem msmall_u9 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 9910000 :=
  small_extend2 (a := 8920000) (A := 8920002) (lo := 8918190) (W := 991810) (msmall_u8 h)
    ⟨4460000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u9

theorem msmall_u10 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 10900000 :=
  small_extend2 (a := 9910000) (A := 9910002) (lo := 9908190) (W := 991810) (msmall_u9 h)
    ⟨4955000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u10

theorem msmall_u11 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 11890000 :=
  small_extend2 (a := 10900000) (A := 10900002) (lo := 10898190) (W := 991810) (msmall_u10 h)
    ⟨5450000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u11

theorem msmall_u12 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 12880000 :=
  small_extend2 (a := 11890000) (A := 11890002) (lo := 11888190) (W := 991810) (msmall_u11 h)
    ⟨5945000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u12

theorem msmall_u13 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 13870000 :=
  small_extend2 (a := 12880000) (A := 12880002) (lo := 12878190) (W := 991810) (msmall_u12 h)
    ⟨6440000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u13

theorem msmall_u14 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 14860000 :=
  small_extend2 (a := 13870000) (A := 13870002) (lo := 13868190) (W := 991810) (msmall_u13 h)
    ⟨6935000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u14

theorem msmall_u15 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 15850000 :=
  small_extend2 (a := 14860000) (A := 14860002) (lo := 14858190) (W := 991810) (msmall_u14 h)
    ⟨7430000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u15

theorem msmall_u16 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 16840000 :=
  small_extend2 (a := 15850000) (A := 15850002) (lo := 15848190) (W := 991810) (msmall_u15 h)
    ⟨7925000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u16

theorem msmall_u17 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 17830000 :=
  small_extend2 (a := 16840000) (A := 16840002) (lo := 16838190) (W := 991810) (msmall_u16 h)
    ⟨8420000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u17

theorem msmall_u18 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 18820000 :=
  small_extend2 (a := 17830000) (A := 17830002) (lo := 17828190) (W := 991810) (msmall_u17 h)
    ⟨8915000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u18

theorem msmall_u19 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 19810000 :=
  small_extend2 (a := 18820000) (A := 18820002) (lo := 18818190) (W := 991810) (msmall_u18 h)
    ⟨9410000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u19

theorem msmall_u20 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 20800000 :=
  small_extend2 (a := 19810000) (A := 19810002) (lo := 19808190) (W := 991810) (msmall_u19 h)
    ⟨9905000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u20

theorem msmall_u21 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 21790000 :=
  small_extend2 (a := 20800000) (A := 20800002) (lo := 20798190) (W := 991810) (msmall_u20 h)
    ⟨10400000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u21

theorem msmall_u22 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 22780000 :=
  small_extend2 (a := 21790000) (A := 21790002) (lo := 21788190) (W := 991810) (msmall_u21 h)
    ⟨10895000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u22

theorem msmall_u23 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 23770000 :=
  small_extend2 (a := 22780000) (A := 22780002) (lo := 22778190) (W := 991810) (msmall_u22 h)
    ⟨11390000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u23

theorem msmall_u24 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 24760000 :=
  small_extend2 (a := 23770000) (A := 23770002) (lo := 23768190) (W := 991810) (msmall_u23 h)
    ⟨11885000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u24

theorem msmall_u25 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 25750000 :=
  small_extend2 (a := 24760000) (A := 24760002) (lo := 24758190) (W := 991810) (msmall_u24 h)
    ⟨12380000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u25

theorem msmall_u26 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 26740000 :=
  small_extend2 (a := 25750000) (A := 25750002) (lo := 25748190) (W := 991810) (msmall_u25 h)
    ⟨12875000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u26

theorem msmall_u27 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 27730000 :=
  small_extend2 (a := 26740000) (A := 26740002) (lo := 26738190) (W := 991810) (msmall_u26 h)
    ⟨13370000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u27

theorem msmall_u28 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 28720000 :=
  small_extend2 (a := 27730000) (A := 27730002) (lo := 27728190) (W := 991810) (msmall_u27 h)
    ⟨13865000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u28

theorem msmall_u29 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 29710000 :=
  small_extend2 (a := 28720000) (A := 28720002) (lo := 28718190) (W := 991810) (msmall_u28 h)
    ⟨14360000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u29

theorem msmall_u30 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 30700000 :=
  small_extend2 (a := 29710000) (A := 29710002) (lo := 29708190) (W := 991810) (msmall_u29 h)
    ⟨14855000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u30

theorem msmall_u31 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 31690000 :=
  small_extend2 (a := 30700000) (A := 30700002) (lo := 30698190) (W := 991810) (msmall_u30 h)
    ⟨15350000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u31

theorem msmall_u32 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 32680000 :=
  small_extend2 (a := 31690000) (A := 31690002) (lo := 31688190) (W := 991810) (msmall_u31 h)
    ⟨15845000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u32

theorem msmall_u33 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 33670000 :=
  small_extend2 (a := 32680000) (A := 32680002) (lo := 32678190) (W := 991810) (msmall_u32 h)
    ⟨16340000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u33

theorem msmall_u34 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 34660000 :=
  small_extend2 (a := 33670000) (A := 33670002) (lo := 33668190) (W := 991810) (msmall_u33 h)
    ⟨16835000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u34

theorem msmall_u35 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 35650000 :=
  small_extend2 (a := 34660000) (A := 34660002) (lo := 34658190) (W := 991810) (msmall_u34 h)
    ⟨17330000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u35

theorem msmall_u36 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 36640000 :=
  small_extend2 (a := 35650000) (A := 35650002) (lo := 35648190) (W := 991810) (msmall_u35 h)
    ⟨17825000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u36

theorem msmall_u37 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 37630000 :=
  small_extend2 (a := 36640000) (A := 36640002) (lo := 36638190) (W := 991810) (msmall_u36 h)
    ⟨18320000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u37

theorem msmall_u38 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 38620000 :=
  small_extend2 (a := 37630000) (A := 37630002) (lo := 37628190) (W := 991810) (msmall_u37 h)
    ⟨18815000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u38

theorem msmall_u39 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 39610000 :=
  small_extend2 (a := 38620000) (A := 38620002) (lo := 38618190) (W := 991810) (msmall_u38 h)
    ⟨19310000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u39

theorem msmall_u40 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 40600000 :=
  small_extend2 (a := 39610000) (A := 39610002) (lo := 39608190) (W := 991810) (msmall_u39 h)
    ⟨19805000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u40

theorem msmall_u41 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 41590000 :=
  small_extend2 (a := 40600000) (A := 40600002) (lo := 40598190) (W := 991810) (msmall_u40 h)
    ⟨20300000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u41

theorem msmall_u42 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 42580000 :=
  small_extend2 (a := 41590000) (A := 41590002) (lo := 41588190) (W := 991810) (msmall_u41 h)
    ⟨20795000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u42

theorem msmall_u43 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 43570000 :=
  small_extend2 (a := 42580000) (A := 42580002) (lo := 42578190) (W := 991810) (msmall_u42 h)
    ⟨21290000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u43

theorem msmall_u44 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 44560000 :=
  small_extend2 (a := 43570000) (A := 43570002) (lo := 43568190) (W := 991810) (msmall_u43 h)
    ⟨21785000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u44

theorem msmall_u45 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 45550000 :=
  small_extend2 (a := 44560000) (A := 44560002) (lo := 44558190) (W := 991810) (msmall_u44 h)
    ⟨22280000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u45

theorem msmall_u46 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 46540000 :=
  small_extend2 (a := 45550000) (A := 45550002) (lo := 45548190) (W := 991810) (msmall_u45 h)
    ⟨22775000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u46

theorem msmall_u47 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 47530000 :=
  small_extend2 (a := 46540000) (A := 46540002) (lo := 46538190) (W := 991810) (msmall_u46 h)
    ⟨23270000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u47

theorem msmall_u48 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 48520000 :=
  small_extend2 (a := 47530000) (A := 47530002) (lo := 47528190) (W := 991810) (msmall_u47 h)
    ⟨23765000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u48

theorem msmall_u49 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 49510000 :=
  small_extend2 (a := 48520000) (A := 48520002) (lo := 48518190) (W := 991810) (msmall_u48 h)
    ⟨24260000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u49

theorem msmall_u50 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 50500000 :=
  small_extend2 (a := 49510000) (A := 49510002) (lo := 49508190) (W := 991810) (msmall_u49 h)
    ⟨24755000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u50

theorem msmall_u51 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 51490000 :=
  small_extend2 (a := 50500000) (A := 50500002) (lo := 50498190) (W := 991810) (msmall_u50 h)
    ⟨25250000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u51

theorem msmall_u52 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 52480000 :=
  small_extend2 (a := 51490000) (A := 51490002) (lo := 51488190) (W := 991810) (msmall_u51 h)
    ⟨25745000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u52

theorem msmall_u53 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 53470000 :=
  small_extend2 (a := 52480000) (A := 52480002) (lo := 52478190) (W := 991810) (msmall_u52 h)
    ⟨26240000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u53

theorem msmall_u54 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 54460000 :=
  small_extend2 (a := 53470000) (A := 53470002) (lo := 53468190) (W := 991810) (msmall_u53 h)
    ⟨26735000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u54

theorem msmall_u55 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 55450000 :=
  small_extend2 (a := 54460000) (A := 54460002) (lo := 54458190) (W := 991810) (msmall_u54 h)
    ⟨27230000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u55

theorem msmall_u56 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 56440000 :=
  small_extend2 (a := 55450000) (A := 55450002) (lo := 55448190) (W := 991810) (msmall_u55 h)
    ⟨27725000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u56

theorem msmall_u57 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 57430000 :=
  small_extend2 (a := 56440000) (A := 56440002) (lo := 56438190) (W := 991810) (msmall_u56 h)
    ⟨28220000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u57

theorem msmall_u58 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 58420000 :=
  small_extend2 (a := 57430000) (A := 57430002) (lo := 57428190) (W := 991810) (msmall_u57 h)
    ⟨28715000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u58

theorem msmall_u59 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 59410000 :=
  small_extend2 (a := 58420000) (A := 58420002) (lo := 58418190) (W := 991810) (msmall_u58 h)
    ⟨29210000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u59

theorem msmall_u60 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 60400000 :=
  small_extend2 (a := 59410000) (A := 59410002) (lo := 59408190) (W := 991810) (msmall_u59 h)
    ⟨29705000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u60

theorem msmall_u61 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 61390000 :=
  small_extend2 (a := 60400000) (A := 60400002) (lo := 60398190) (W := 991810) (msmall_u60 h)
    ⟨30200000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u61

theorem msmall_u62 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 62380000 :=
  small_extend2 (a := 61390000) (A := 61390002) (lo := 61388190) (W := 991810) (msmall_u61 h)
    ⟨30695000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u62

theorem msmall_u63 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 63370000 :=
  small_extend2 (a := 62380000) (A := 62380002) (lo := 62378190) (W := 991810) (msmall_u62 h)
    ⟨31190000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u63

theorem msmall_u64 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 64360000 :=
  small_extend2 (a := 63370000) (A := 63370002) (lo := 63368190) (W := 991810) (msmall_u63 h)
    ⟨31685000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u64

theorem msmall_u65 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 65350000 :=
  small_extend2 (a := 64360000) (A := 64360002) (lo := 64358190) (W := 991810) (msmall_u64 h)
    ⟨32180000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u65

theorem msmall_u66 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 66340000 :=
  small_extend2 (a := 65350000) (A := 65350002) (lo := 65348190) (W := 991810) (msmall_u65 h)
    ⟨32675000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u66

theorem msmall_u67 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 67330000 :=
  small_extend2 (a := 66340000) (A := 66340002) (lo := 66338190) (W := 991810) (msmall_u66 h)
    ⟨33170000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u67

theorem msmall_u68 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 68320000 :=
  small_extend2 (a := 67330000) (A := 67330002) (lo := 67328190) (W := 991810) (msmall_u67 h)
    ⟨33665000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u68

theorem msmall_u69 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 69310000 :=
  small_extend2 (a := 68320000) (A := 68320002) (lo := 68318190) (W := 991810) (msmall_u68 h)
    ⟨34160000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u69

theorem msmall_u70 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 70300000 :=
  small_extend2 (a := 69310000) (A := 69310002) (lo := 69308190) (W := 991810) (msmall_u69 h)
    ⟨34655000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u70

theorem msmall_u71 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 71290000 :=
  small_extend2 (a := 70300000) (A := 70300002) (lo := 70298190) (W := 991810) (msmall_u70 h)
    ⟨35150000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u71

theorem msmall_u72 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 72280000 :=
  small_extend2 (a := 71290000) (A := 71290002) (lo := 71288190) (W := 991810) (msmall_u71 h)
    ⟨35645000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u72

theorem msmall_u73 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 73270000 :=
  small_extend2 (a := 72280000) (A := 72280002) (lo := 72278190) (W := 991810) (msmall_u72 h)
    ⟨36140000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u73

theorem msmall_u74 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 74260000 :=
  small_extend2 (a := 73270000) (A := 73270002) (lo := 73268190) (W := 991810) (msmall_u73 h)
    ⟨36635000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u74

theorem msmall_u75 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 75250000 :=
  small_extend2 (a := 74260000) (A := 74260002) (lo := 74258190) (W := 991810) (msmall_u74 h)
    ⟨37130000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u75

theorem msmall_u76 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 76240000 :=
  small_extend2 (a := 75250000) (A := 75250002) (lo := 75248190) (W := 991810) (msmall_u75 h)
    ⟨37625000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u76

theorem msmall_u77 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 77230000 :=
  small_extend2 (a := 76240000) (A := 76240002) (lo := 76238190) (W := 991810) (msmall_u76 h)
    ⟨38120000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u77

theorem msmall_u78 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 78220000 :=
  small_extend2 (a := 77230000) (A := 77230002) (lo := 77228190) (W := 991810) (msmall_u77 h)
    ⟨38615000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u78

theorem msmall_u79 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 79210000 :=
  small_extend2 (a := 78220000) (A := 78220002) (lo := 78218190) (W := 991810) (msmall_u78 h)
    ⟨39110000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u79

theorem msmall_u80 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 80200000 :=
  small_extend2 (a := 79210000) (A := 79210002) (lo := 79208190) (W := 991810) (msmall_u79 h)
    ⟨39605000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u80

theorem msmall_u81 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 81190000 :=
  small_extend2 (a := 80200000) (A := 80200002) (lo := 80198190) (W := 991810) (msmall_u80 h)
    ⟨40100000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u81

theorem msmall_u82 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 82180000 :=
  small_extend2 (a := 81190000) (A := 81190002) (lo := 81188190) (W := 991810) (msmall_u81 h)
    ⟨40595000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u82

theorem msmall_u83 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 83170000 :=
  small_extend2 (a := 82180000) (A := 82180002) (lo := 82178190) (W := 991810) (msmall_u82 h)
    ⟨41090000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u83

theorem msmall_u84 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 84160000 :=
  small_extend2 (a := 83170000) (A := 83170002) (lo := 83168190) (W := 991810) (msmall_u83 h)
    ⟨41585000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u84

theorem msmall_u85 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 85150000 :=
  small_extend2 (a := 84160000) (A := 84160002) (lo := 84158190) (W := 991810) (msmall_u84 h)
    ⟨42080000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u85

theorem msmall_u86 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 86140000 :=
  small_extend2 (a := 85150000) (A := 85150002) (lo := 85148190) (W := 991810) (msmall_u85 h)
    ⟨42575000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u86

theorem msmall_u87 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 87130000 :=
  small_extend2 (a := 86140000) (A := 86140002) (lo := 86138190) (W := 991810) (msmall_u86 h)
    ⟨43070000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u87

theorem msmall_u88 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 88120000 :=
  small_extend2 (a := 87130000) (A := 87130002) (lo := 87128190) (W := 991810) (msmall_u87 h)
    ⟨43565000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u88

theorem msmall_u89 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 89110000 :=
  small_extend2 (a := 88120000) (A := 88120002) (lo := 88118190) (W := 991810) (msmall_u88 h)
    ⟨44060000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u89

theorem msmall_u90 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 90100000 :=
  small_extend2 (a := 89110000) (A := 89110002) (lo := 89108190) (W := 991810) (msmall_u89 h)
    ⟨44555000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u90

theorem msmall_u91 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 91090000 :=
  small_extend2 (a := 90100000) (A := 90100002) (lo := 90098190) (W := 991810) (msmall_u90 h)
    ⟨45050000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u91

theorem msmall_u92 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 92080000 :=
  small_extend2 (a := 91090000) (A := 91090002) (lo := 91088190) (W := 991810) (msmall_u91 h)
    ⟨45545000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u92

theorem msmall_u93 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 93070000 :=
  small_extend2 (a := 92080000) (A := 92080002) (lo := 92078190) (W := 991810) (msmall_u92 h)
    ⟨46040000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u93

theorem msmall_u94 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 94060000 :=
  small_extend2 (a := 93070000) (A := 93070002) (lo := 93068190) (W := 991810) (msmall_u93 h)
    ⟨46535000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u94

theorem msmall_u95 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 95050000 :=
  small_extend2 (a := 94060000) (A := 94060002) (lo := 94058190) (W := 991810) (msmall_u94 h)
    ⟨47030000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u95

theorem msmall_u96 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 96040000 :=
  small_extend2 (a := 95050000) (A := 95050002) (lo := 95048190) (W := 991810) (msmall_u95 h)
    ⟨47525000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u96

theorem msmall_u97 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 97030000 :=
  small_extend2 (a := 96040000) (A := 96040002) (lo := 96038190) (W := 991810) (msmall_u96 h)
    ⟨48020000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u97

theorem msmall_u98 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 98020000 :=
  small_extend2 (a := 97030000) (A := 97030002) (lo := 97028190) (W := 991810) (msmall_u97 h)
    ⟨48515000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u98

theorem msmall_u99 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 99010000 :=
  small_extend2 (a := 98020000) (A := 98020002) (lo := 98018190) (W := 991810) (msmall_u98 h)
    ⟨49010000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u99

theorem msmall_u100 (h : SmallGBUpTo 1789 1000000) : SmallGBUpTo 1789 100000000 :=
  small_extend2 (a := 99010000) (A := 99010002) (lo := 99008190) (W := 991810) (msmall_u99 h)
    ⟨49505000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_u100

end LeanLab.Verifications.Top50.Bits
