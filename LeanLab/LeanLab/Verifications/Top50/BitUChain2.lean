/-
Chain block U2 of the kernel Goldbach windows from 10^6: windows U101 to U200, from
SmallGBUpTo 1811 100000000 to SmallGBUpTo 1811 199000000, so the blocks compose. Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.SmallGB
import LeanLab.Verifications.Top50.BitUG11
import LeanLab.Verifications.Top50.BitUG12
import LeanLab.Verifications.Top50.BitUG13
import LeanLab.Verifications.Top50.BitUG14
import LeanLab.Verifications.Top50.BitUG15
import LeanLab.Verifications.Top50.BitUG16
import LeanLab.Verifications.Top50.BitUG17
import LeanLab.Verifications.Top50.BitUG18
import LeanLab.Verifications.Top50.BitUG19
import LeanLab.Verifications.Top50.BitUG20

namespace LeanLab.Verifications.Top50.Bits

theorem small_u101 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 100990000 :=
  small_extend2 (a := 100000000) (A := 100000002) (lo := 99998190) (W := 991810) h
    ⟨50000000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u101

theorem small_u102 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 101980000 :=
  small_extend2 (a := 100990000) (A := 100990002) (lo := 100988190) (W := 991810) (small_u101 h)
    ⟨50495000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u102

theorem small_u103 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 102970000 :=
  small_extend2 (a := 101980000) (A := 101980002) (lo := 101978190) (W := 991810) (small_u102 h)
    ⟨50990000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u103

theorem small_u104 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 103960000 :=
  small_extend2 (a := 102970000) (A := 102970002) (lo := 102968190) (W := 991810) (small_u103 h)
    ⟨51485000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u104

theorem small_u105 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 104950000 :=
  small_extend2 (a := 103960000) (A := 103960002) (lo := 103958190) (W := 991810) (small_u104 h)
    ⟨51980000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u105

theorem small_u106 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 105940000 :=
  small_extend2 (a := 104950000) (A := 104950002) (lo := 104948190) (W := 991810) (small_u105 h)
    ⟨52475000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u106

theorem small_u107 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 106930000 :=
  small_extend2 (a := 105940000) (A := 105940002) (lo := 105938190) (W := 991810) (small_u106 h)
    ⟨52970000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u107

theorem small_u108 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 107920000 :=
  small_extend2 (a := 106930000) (A := 106930002) (lo := 106928190) (W := 991810) (small_u107 h)
    ⟨53465000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u108

theorem small_u109 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 108910000 :=
  small_extend2 (a := 107920000) (A := 107920002) (lo := 107918190) (W := 991810) (small_u108 h)
    ⟨53960000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u109

theorem small_u110 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 109900000 :=
  small_extend2 (a := 108910000) (A := 108910002) (lo := 108908190) (W := 991810) (small_u109 h)
    ⟨54455000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u110

theorem small_u111 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 110890000 :=
  small_extend2 (a := 109900000) (A := 109900002) (lo := 109898190) (W := 991810) (small_u110 h)
    ⟨54950000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u111

theorem small_u112 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 111880000 :=
  small_extend2 (a := 110890000) (A := 110890002) (lo := 110888190) (W := 991810) (small_u111 h)
    ⟨55445000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u112

theorem small_u113 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 112870000 :=
  small_extend2 (a := 111880000) (A := 111880002) (lo := 111878190) (W := 991810) (small_u112 h)
    ⟨55940000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u113

theorem small_u114 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 113860000 :=
  small_extend2 (a := 112870000) (A := 112870002) (lo := 112868190) (W := 991810) (small_u113 h)
    ⟨56435000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u114

theorem small_u115 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 114850000 :=
  small_extend2 (a := 113860000) (A := 113860002) (lo := 113858190) (W := 991810) (small_u114 h)
    ⟨56930000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u115

theorem small_u116 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 115840000 :=
  small_extend2 (a := 114850000) (A := 114850002) (lo := 114848190) (W := 991810) (small_u115 h)
    ⟨57425000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u116

theorem small_u117 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 116830000 :=
  small_extend2 (a := 115840000) (A := 115840002) (lo := 115838190) (W := 991810) (small_u116 h)
    ⟨57920000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u117

theorem small_u118 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 117820000 :=
  small_extend2 (a := 116830000) (A := 116830002) (lo := 116828190) (W := 991810) (small_u117 h)
    ⟨58415000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u118

theorem small_u119 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 118810000 :=
  small_extend2 (a := 117820000) (A := 117820002) (lo := 117818190) (W := 991810) (small_u118 h)
    ⟨58910000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u119

theorem small_u120 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 119800000 :=
  small_extend2 (a := 118810000) (A := 118810002) (lo := 118808190) (W := 991810) (small_u119 h)
    ⟨59405000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u120

theorem small_u121 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 120790000 :=
  small_extend2 (a := 119800000) (A := 119800002) (lo := 119798190) (W := 991810) (small_u120 h)
    ⟨59900000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u121

theorem small_u122 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 121780000 :=
  small_extend2 (a := 120790000) (A := 120790002) (lo := 120788190) (W := 991810) (small_u121 h)
    ⟨60395000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u122

theorem small_u123 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 122770000 :=
  small_extend2 (a := 121780000) (A := 121780002) (lo := 121778190) (W := 991810) (small_u122 h)
    ⟨60890000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u123

theorem small_u124 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 123760000 :=
  small_extend2 (a := 122770000) (A := 122770002) (lo := 122768190) (W := 991810) (small_u123 h)
    ⟨61385000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u124

theorem small_u125 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 124750000 :=
  small_extend2 (a := 123760000) (A := 123760002) (lo := 123758190) (W := 991810) (small_u124 h)
    ⟨61880000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u125

theorem small_u126 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 125740000 :=
  small_extend2 (a := 124750000) (A := 124750002) (lo := 124748190) (W := 991810) (small_u125 h)
    ⟨62375000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u126

theorem small_u127 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 126730000 :=
  small_extend2 (a := 125740000) (A := 125740002) (lo := 125738190) (W := 991810) (small_u126 h)
    ⟨62870000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u127

theorem small_u128 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 127720000 :=
  small_extend2 (a := 126730000) (A := 126730002) (lo := 126728190) (W := 991810) (small_u127 h)
    ⟨63365000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u128

theorem small_u129 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 128710000 :=
  small_extend2 (a := 127720000) (A := 127720002) (lo := 127718190) (W := 991810) (small_u128 h)
    ⟨63860000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u129

theorem small_u130 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 129700000 :=
  small_extend2 (a := 128710000) (A := 128710002) (lo := 128708190) (W := 991810) (small_u129 h)
    ⟨64355000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u130

theorem small_u131 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 130690000 :=
  small_extend2 (a := 129700000) (A := 129700002) (lo := 129698190) (W := 991810) (small_u130 h)
    ⟨64850000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u131

theorem small_u132 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 131680000 :=
  small_extend2 (a := 130690000) (A := 130690002) (lo := 130688190) (W := 991810) (small_u131 h)
    ⟨65345000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u132

theorem small_u133 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 132670000 :=
  small_extend2 (a := 131680000) (A := 131680002) (lo := 131678190) (W := 991810) (small_u132 h)
    ⟨65840000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u133

theorem small_u134 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 133660000 :=
  small_extend2 (a := 132670000) (A := 132670002) (lo := 132668190) (W := 991810) (small_u133 h)
    ⟨66335000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u134

theorem small_u135 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 134650000 :=
  small_extend2 (a := 133660000) (A := 133660002) (lo := 133658190) (W := 991810) (small_u134 h)
    ⟨66830000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u135

theorem small_u136 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 135640000 :=
  small_extend2 (a := 134650000) (A := 134650002) (lo := 134648190) (W := 991810) (small_u135 h)
    ⟨67325000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u136

theorem small_u137 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 136630000 :=
  small_extend2 (a := 135640000) (A := 135640002) (lo := 135638190) (W := 991810) (small_u136 h)
    ⟨67820000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u137

theorem small_u138 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 137620000 :=
  small_extend2 (a := 136630000) (A := 136630002) (lo := 136628190) (W := 991810) (small_u137 h)
    ⟨68315000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u138

theorem small_u139 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 138610000 :=
  small_extend2 (a := 137620000) (A := 137620002) (lo := 137618190) (W := 991810) (small_u138 h)
    ⟨68810000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u139

theorem small_u140 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 139600000 :=
  small_extend2 (a := 138610000) (A := 138610002) (lo := 138608190) (W := 991810) (small_u139 h)
    ⟨69305000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u140

theorem small_u141 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 140590000 :=
  small_extend2 (a := 139600000) (A := 139600002) (lo := 139598190) (W := 991810) (small_u140 h)
    ⟨69800000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u141

theorem small_u142 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 141580000 :=
  small_extend2 (a := 140590000) (A := 140590002) (lo := 140588190) (W := 991810) (small_u141 h)
    ⟨70295000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u142

theorem small_u143 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 142570000 :=
  small_extend2 (a := 141580000) (A := 141580002) (lo := 141578190) (W := 991810) (small_u142 h)
    ⟨70790000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u143

theorem small_u144 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 143560000 :=
  small_extend2 (a := 142570000) (A := 142570002) (lo := 142568190) (W := 991810) (small_u143 h)
    ⟨71285000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u144

theorem small_u145 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 144550000 :=
  small_extend2 (a := 143560000) (A := 143560002) (lo := 143558190) (W := 991810) (small_u144 h)
    ⟨71780000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u145

theorem small_u146 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 145540000 :=
  small_extend2 (a := 144550000) (A := 144550002) (lo := 144548190) (W := 991810) (small_u145 h)
    ⟨72275000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u146

theorem small_u147 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 146530000 :=
  small_extend2 (a := 145540000) (A := 145540002) (lo := 145538190) (W := 991810) (small_u146 h)
    ⟨72770000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u147

theorem small_u148 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 147520000 :=
  small_extend2 (a := 146530000) (A := 146530002) (lo := 146528190) (W := 991810) (small_u147 h)
    ⟨73265000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u148

theorem small_u149 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 148510000 :=
  small_extend2 (a := 147520000) (A := 147520002) (lo := 147518190) (W := 991810) (small_u148 h)
    ⟨73760000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u149

theorem small_u150 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 149500000 :=
  small_extend2 (a := 148510000) (A := 148510002) (lo := 148508190) (W := 991810) (small_u149 h)
    ⟨74255000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u150

theorem small_u151 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 150490000 :=
  small_extend2 (a := 149500000) (A := 149500002) (lo := 149498190) (W := 991810) (small_u150 h)
    ⟨74750000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u151

theorem small_u152 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 151480000 :=
  small_extend2 (a := 150490000) (A := 150490002) (lo := 150488190) (W := 991810) (small_u151 h)
    ⟨75245000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u152

theorem small_u153 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 152470000 :=
  small_extend2 (a := 151480000) (A := 151480002) (lo := 151478190) (W := 991810) (small_u152 h)
    ⟨75740000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u153

theorem small_u154 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 153460000 :=
  small_extend2 (a := 152470000) (A := 152470002) (lo := 152468190) (W := 991810) (small_u153 h)
    ⟨76235000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u154

theorem small_u155 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 154450000 :=
  small_extend2 (a := 153460000) (A := 153460002) (lo := 153458190) (W := 991810) (small_u154 h)
    ⟨76730000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u155

theorem small_u156 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 155440000 :=
  small_extend2 (a := 154450000) (A := 154450002) (lo := 154448190) (W := 991810) (small_u155 h)
    ⟨77225000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u156

theorem small_u157 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 156430000 :=
  small_extend2 (a := 155440000) (A := 155440002) (lo := 155438190) (W := 991810) (small_u156 h)
    ⟨77720000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u157

theorem small_u158 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 157420000 :=
  small_extend2 (a := 156430000) (A := 156430002) (lo := 156428190) (W := 991810) (small_u157 h)
    ⟨78215000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u158

theorem small_u159 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 158410000 :=
  small_extend2 (a := 157420000) (A := 157420002) (lo := 157418190) (W := 991810) (small_u158 h)
    ⟨78710000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u159

theorem small_u160 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 159400000 :=
  small_extend2 (a := 158410000) (A := 158410002) (lo := 158408190) (W := 991810) (small_u159 h)
    ⟨79205000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u160

theorem small_u161 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 160390000 :=
  small_extend2 (a := 159400000) (A := 159400002) (lo := 159398190) (W := 991810) (small_u160 h)
    ⟨79700000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u161

theorem small_u162 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 161380000 :=
  small_extend2 (a := 160390000) (A := 160390002) (lo := 160388190) (W := 991810) (small_u161 h)
    ⟨80195000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u162

theorem small_u163 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 162370000 :=
  small_extend2 (a := 161380000) (A := 161380002) (lo := 161378190) (W := 991810) (small_u162 h)
    ⟨80690000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u163

theorem small_u164 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 163360000 :=
  small_extend2 (a := 162370000) (A := 162370002) (lo := 162368190) (W := 991810) (small_u163 h)
    ⟨81185000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u164

theorem small_u165 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 164350000 :=
  small_extend2 (a := 163360000) (A := 163360002) (lo := 163358190) (W := 991810) (small_u164 h)
    ⟨81680000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u165

theorem small_u166 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 165340000 :=
  small_extend2 (a := 164350000) (A := 164350002) (lo := 164348190) (W := 991810) (small_u165 h)
    ⟨82175000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u166

theorem small_u167 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 166330000 :=
  small_extend2 (a := 165340000) (A := 165340002) (lo := 165338190) (W := 991810) (small_u166 h)
    ⟨82670000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u167

theorem small_u168 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 167320000 :=
  small_extend2 (a := 166330000) (A := 166330002) (lo := 166328190) (W := 991810) (small_u167 h)
    ⟨83165000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u168

theorem small_u169 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 168310000 :=
  small_extend2 (a := 167320000) (A := 167320002) (lo := 167318190) (W := 991810) (small_u168 h)
    ⟨83660000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u169

theorem small_u170 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 169300000 :=
  small_extend2 (a := 168310000) (A := 168310002) (lo := 168308190) (W := 991810) (small_u169 h)
    ⟨84155000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u170

theorem small_u171 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 170290000 :=
  small_extend2 (a := 169300000) (A := 169300002) (lo := 169298190) (W := 991810) (small_u170 h)
    ⟨84650000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u171

theorem small_u172 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 171280000 :=
  small_extend2 (a := 170290000) (A := 170290002) (lo := 170288190) (W := 991810) (small_u171 h)
    ⟨85145000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u172

theorem small_u173 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 172270000 :=
  small_extend2 (a := 171280000) (A := 171280002) (lo := 171278190) (W := 991810) (small_u172 h)
    ⟨85640000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u173

theorem small_u174 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 173260000 :=
  small_extend2 (a := 172270000) (A := 172270002) (lo := 172268190) (W := 991810) (small_u173 h)
    ⟨86135000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u174

theorem small_u175 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 174250000 :=
  small_extend2 (a := 173260000) (A := 173260002) (lo := 173258190) (W := 991810) (small_u174 h)
    ⟨86630000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u175

theorem small_u176 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 175240000 :=
  small_extend2 (a := 174250000) (A := 174250002) (lo := 174248190) (W := 991810) (small_u175 h)
    ⟨87125000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u176

theorem small_u177 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 176230000 :=
  small_extend2 (a := 175240000) (A := 175240002) (lo := 175238190) (W := 991810) (small_u176 h)
    ⟨87620000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u177

theorem small_u178 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 177220000 :=
  small_extend2 (a := 176230000) (A := 176230002) (lo := 176228190) (W := 991810) (small_u177 h)
    ⟨88115000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u178

theorem small_u179 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 178210000 :=
  small_extend2 (a := 177220000) (A := 177220002) (lo := 177218190) (W := 991810) (small_u178 h)
    ⟨88610000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u179

theorem small_u180 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 179200000 :=
  small_extend2 (a := 178210000) (A := 178210002) (lo := 178208190) (W := 991810) (small_u179 h)
    ⟨89105000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u180

theorem small_u181 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 180190000 :=
  small_extend2 (a := 179200000) (A := 179200002) (lo := 179198190) (W := 991810) (small_u180 h)
    ⟨89600000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u181

theorem small_u182 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 181180000 :=
  small_extend2 (a := 180190000) (A := 180190002) (lo := 180188190) (W := 991810) (small_u181 h)
    ⟨90095000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u182

theorem small_u183 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 182170000 :=
  small_extend2 (a := 181180000) (A := 181180002) (lo := 181178190) (W := 991810) (small_u182 h)
    ⟨90590000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u183

theorem small_u184 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 183160000 :=
  small_extend2 (a := 182170000) (A := 182170002) (lo := 182168190) (W := 991810) (small_u183 h)
    ⟨91085000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u184

theorem small_u185 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 184150000 :=
  small_extend2 (a := 183160000) (A := 183160002) (lo := 183158190) (W := 991810) (small_u184 h)
    ⟨91580000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u185

theorem small_u186 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 185140000 :=
  small_extend2 (a := 184150000) (A := 184150002) (lo := 184148190) (W := 991810) (small_u185 h)
    ⟨92075000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u186

theorem small_u187 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 186130000 :=
  small_extend2 (a := 185140000) (A := 185140002) (lo := 185138190) (W := 991810) (small_u186 h)
    ⟨92570000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u187

theorem small_u188 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 187120000 :=
  small_extend2 (a := 186130000) (A := 186130002) (lo := 186128190) (W := 991810) (small_u187 h)
    ⟨93065000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u188

theorem small_u189 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 188110000 :=
  small_extend2 (a := 187120000) (A := 187120002) (lo := 187118190) (W := 991810) (small_u188 h)
    ⟨93560000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u189

theorem small_u190 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 189100000 :=
  small_extend2 (a := 188110000) (A := 188110002) (lo := 188108190) (W := 991810) (small_u189 h)
    ⟨94055000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u190

theorem small_u191 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 190090000 :=
  small_extend2 (a := 189100000) (A := 189100002) (lo := 189098190) (W := 991810) (small_u190 h)
    ⟨94550000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u191

theorem small_u192 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 191080000 :=
  small_extend2 (a := 190090000) (A := 190090002) (lo := 190088190) (W := 991810) (small_u191 h)
    ⟨95045000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u192

theorem small_u193 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 192070000 :=
  small_extend2 (a := 191080000) (A := 191080002) (lo := 191078190) (W := 991810) (small_u192 h)
    ⟨95540000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u193

theorem small_u194 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 193060000 :=
  small_extend2 (a := 192070000) (A := 192070002) (lo := 192068190) (W := 991810) (small_u193 h)
    ⟨96035000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u194

theorem small_u195 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 194050000 :=
  small_extend2 (a := 193060000) (A := 193060002) (lo := 193058190) (W := 991810) (small_u194 h)
    ⟨96530000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u195

theorem small_u196 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 195040000 :=
  small_extend2 (a := 194050000) (A := 194050002) (lo := 194048190) (W := 991810) (small_u195 h)
    ⟨97025000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u196

theorem small_u197 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 196030000 :=
  small_extend2 (a := 195040000) (A := 195040002) (lo := 195038190) (W := 991810) (small_u196 h)
    ⟨97520000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u197

theorem small_u198 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 197020000 :=
  small_extend2 (a := 196030000) (A := 196030002) (lo := 196028190) (W := 991810) (small_u197 h)
    ⟨98015000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u198

theorem small_u199 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 198010000 :=
  small_extend2 (a := 197020000) (A := 197020002) (lo := 197018190) (W := 991810) (small_u198 h)
    ⟨98510000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u199

theorem small_u200 (h : SmallGBUpTo 1811 100000000) : SmallGBUpTo 1811 199000000 :=
  small_extend2 (a := 198010000) (A := 198010002) (lo := 198008190) (W := 991810) (small_u199 h)
    ⟨99005000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_u200

end LeanLab.Verifications.Top50.Bits
