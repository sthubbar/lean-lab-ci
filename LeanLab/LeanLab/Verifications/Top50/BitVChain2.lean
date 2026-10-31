/-
Chain block V2 of the kernel Goldbach windows past 323740000: windows V101 to V200, from
SmallGBUpTo 1811 422740000 to SmallGBUpTo 1811 521740000, so the blocks compose. Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.SmallGB
import LeanLab.Verifications.Top50.BitVG11
import LeanLab.Verifications.Top50.BitVG12
import LeanLab.Verifications.Top50.BitVG13
import LeanLab.Verifications.Top50.BitVG14
import LeanLab.Verifications.Top50.BitVG15
import LeanLab.Verifications.Top50.BitVG16
import LeanLab.Verifications.Top50.BitVG17
import LeanLab.Verifications.Top50.BitVG18
import LeanLab.Verifications.Top50.BitVG19
import LeanLab.Verifications.Top50.BitVG20

namespace LeanLab.Verifications.Top50.Bits

theorem small_v101 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 423730000 :=
  small_extend2 (a := 422740000) (A := 422740002) (lo := 422738190) (W := 991810) h
    ⟨211370000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v101

theorem small_v102 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 424720000 :=
  small_extend2 (a := 423730000) (A := 423730002) (lo := 423728190) (W := 991810) (small_v101 h)
    ⟨211865000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v102

theorem small_v103 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 425710000 :=
  small_extend2 (a := 424720000) (A := 424720002) (lo := 424718190) (W := 991810) (small_v102 h)
    ⟨212360000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v103

theorem small_v104 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 426700000 :=
  small_extend2 (a := 425710000) (A := 425710002) (lo := 425708190) (W := 991810) (small_v103 h)
    ⟨212855000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v104

theorem small_v105 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 427690000 :=
  small_extend2 (a := 426700000) (A := 426700002) (lo := 426698190) (W := 991810) (small_v104 h)
    ⟨213350000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v105

theorem small_v106 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 428680000 :=
  small_extend2 (a := 427690000) (A := 427690002) (lo := 427688190) (W := 991810) (small_v105 h)
    ⟨213845000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v106

theorem small_v107 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 429670000 :=
  small_extend2 (a := 428680000) (A := 428680002) (lo := 428678190) (W := 991810) (small_v106 h)
    ⟨214340000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v107

theorem small_v108 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 430660000 :=
  small_extend2 (a := 429670000) (A := 429670002) (lo := 429668190) (W := 991810) (small_v107 h)
    ⟨214835000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v108

theorem small_v109 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 431650000 :=
  small_extend2 (a := 430660000) (A := 430660002) (lo := 430658190) (W := 991810) (small_v108 h)
    ⟨215330000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v109

theorem small_v110 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 432640000 :=
  small_extend2 (a := 431650000) (A := 431650002) (lo := 431648190) (W := 991810) (small_v109 h)
    ⟨215825000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v110

theorem small_v111 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 433630000 :=
  small_extend2 (a := 432640000) (A := 432640002) (lo := 432638190) (W := 991810) (small_v110 h)
    ⟨216320000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v111

theorem small_v112 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 434620000 :=
  small_extend2 (a := 433630000) (A := 433630002) (lo := 433628190) (W := 991810) (small_v111 h)
    ⟨216815000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v112

theorem small_v113 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 435610000 :=
  small_extend2 (a := 434620000) (A := 434620002) (lo := 434618190) (W := 991810) (small_v112 h)
    ⟨217310000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v113

theorem small_v114 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 436600000 :=
  small_extend2 (a := 435610000) (A := 435610002) (lo := 435608190) (W := 991810) (small_v113 h)
    ⟨217805000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v114

theorem small_v115 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 437590000 :=
  small_extend2 (a := 436600000) (A := 436600002) (lo := 436598190) (W := 991810) (small_v114 h)
    ⟨218300000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v115

theorem small_v116 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 438580000 :=
  small_extend2 (a := 437590000) (A := 437590002) (lo := 437588190) (W := 991810) (small_v115 h)
    ⟨218795000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v116

theorem small_v117 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 439570000 :=
  small_extend2 (a := 438580000) (A := 438580002) (lo := 438578190) (W := 991810) (small_v116 h)
    ⟨219290000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v117

theorem small_v118 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 440560000 :=
  small_extend2 (a := 439570000) (A := 439570002) (lo := 439568190) (W := 991810) (small_v117 h)
    ⟨219785000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v118

theorem small_v119 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 441550000 :=
  small_extend2 (a := 440560000) (A := 440560002) (lo := 440558190) (W := 991810) (small_v118 h)
    ⟨220280000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v119

theorem small_v120 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 442540000 :=
  small_extend2 (a := 441550000) (A := 441550002) (lo := 441548190) (W := 991810) (small_v119 h)
    ⟨220775000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v120

theorem small_v121 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 443530000 :=
  small_extend2 (a := 442540000) (A := 442540002) (lo := 442538190) (W := 991810) (small_v120 h)
    ⟨221270000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v121

theorem small_v122 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 444520000 :=
  small_extend2 (a := 443530000) (A := 443530002) (lo := 443528190) (W := 991810) (small_v121 h)
    ⟨221765000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v122

theorem small_v123 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 445510000 :=
  small_extend2 (a := 444520000) (A := 444520002) (lo := 444518190) (W := 991810) (small_v122 h)
    ⟨222260000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v123

theorem small_v124 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 446500000 :=
  small_extend2 (a := 445510000) (A := 445510002) (lo := 445508190) (W := 991810) (small_v123 h)
    ⟨222755000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v124

theorem small_v125 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 447490000 :=
  small_extend2 (a := 446500000) (A := 446500002) (lo := 446498190) (W := 991810) (small_v124 h)
    ⟨223250000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v125

theorem small_v126 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 448480000 :=
  small_extend2 (a := 447490000) (A := 447490002) (lo := 447488190) (W := 991810) (small_v125 h)
    ⟨223745000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v126

theorem small_v127 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 449470000 :=
  small_extend2 (a := 448480000) (A := 448480002) (lo := 448478190) (W := 991810) (small_v126 h)
    ⟨224240000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v127

theorem small_v128 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 450460000 :=
  small_extend2 (a := 449470000) (A := 449470002) (lo := 449468190) (W := 991810) (small_v127 h)
    ⟨224735000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v128

theorem small_v129 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 451450000 :=
  small_extend2 (a := 450460000) (A := 450460002) (lo := 450458190) (W := 991810) (small_v128 h)
    ⟨225230000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v129

theorem small_v130 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 452440000 :=
  small_extend2 (a := 451450000) (A := 451450002) (lo := 451448190) (W := 991810) (small_v129 h)
    ⟨225725000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v130

theorem small_v131 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 453430000 :=
  small_extend2 (a := 452440000) (A := 452440002) (lo := 452438190) (W := 991810) (small_v130 h)
    ⟨226220000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v131

theorem small_v132 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 454420000 :=
  small_extend2 (a := 453430000) (A := 453430002) (lo := 453428190) (W := 991810) (small_v131 h)
    ⟨226715000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v132

theorem small_v133 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 455410000 :=
  small_extend2 (a := 454420000) (A := 454420002) (lo := 454418190) (W := 991810) (small_v132 h)
    ⟨227210000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v133

theorem small_v134 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 456400000 :=
  small_extend2 (a := 455410000) (A := 455410002) (lo := 455408190) (W := 991810) (small_v133 h)
    ⟨227705000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v134

theorem small_v135 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 457390000 :=
  small_extend2 (a := 456400000) (A := 456400002) (lo := 456398190) (W := 991810) (small_v134 h)
    ⟨228200000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v135

theorem small_v136 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 458380000 :=
  small_extend2 (a := 457390000) (A := 457390002) (lo := 457388190) (W := 991810) (small_v135 h)
    ⟨228695000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v136

theorem small_v137 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 459370000 :=
  small_extend2 (a := 458380000) (A := 458380002) (lo := 458378190) (W := 991810) (small_v136 h)
    ⟨229190000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v137

theorem small_v138 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 460360000 :=
  small_extend2 (a := 459370000) (A := 459370002) (lo := 459368190) (W := 991810) (small_v137 h)
    ⟨229685000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v138

theorem small_v139 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 461350000 :=
  small_extend2 (a := 460360000) (A := 460360002) (lo := 460358190) (W := 991810) (small_v138 h)
    ⟨230180000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v139

theorem small_v140 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 462340000 :=
  small_extend2 (a := 461350000) (A := 461350002) (lo := 461348190) (W := 991810) (small_v139 h)
    ⟨230675000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v140

theorem small_v141 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 463330000 :=
  small_extend2 (a := 462340000) (A := 462340002) (lo := 462338190) (W := 991810) (small_v140 h)
    ⟨231170000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v141

theorem small_v142 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 464320000 :=
  small_extend2 (a := 463330000) (A := 463330002) (lo := 463328190) (W := 991810) (small_v141 h)
    ⟨231665000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v142

theorem small_v143 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 465310000 :=
  small_extend2 (a := 464320000) (A := 464320002) (lo := 464318190) (W := 991810) (small_v142 h)
    ⟨232160000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v143

theorem small_v144 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 466300000 :=
  small_extend2 (a := 465310000) (A := 465310002) (lo := 465308190) (W := 991810) (small_v143 h)
    ⟨232655000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v144

theorem small_v145 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 467290000 :=
  small_extend2 (a := 466300000) (A := 466300002) (lo := 466298190) (W := 991810) (small_v144 h)
    ⟨233150000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v145

theorem small_v146 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 468280000 :=
  small_extend2 (a := 467290000) (A := 467290002) (lo := 467288190) (W := 991810) (small_v145 h)
    ⟨233645000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v146

theorem small_v147 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 469270000 :=
  small_extend2 (a := 468280000) (A := 468280002) (lo := 468278190) (W := 991810) (small_v146 h)
    ⟨234140000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v147

theorem small_v148 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 470260000 :=
  small_extend2 (a := 469270000) (A := 469270002) (lo := 469268190) (W := 991810) (small_v147 h)
    ⟨234635000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v148

theorem small_v149 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 471250000 :=
  small_extend2 (a := 470260000) (A := 470260002) (lo := 470258190) (W := 991810) (small_v148 h)
    ⟨235130000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v149

theorem small_v150 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 472240000 :=
  small_extend2 (a := 471250000) (A := 471250002) (lo := 471248190) (W := 991810) (small_v149 h)
    ⟨235625000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v150

theorem small_v151 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 473230000 :=
  small_extend2 (a := 472240000) (A := 472240002) (lo := 472238190) (W := 991810) (small_v150 h)
    ⟨236120000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v151

theorem small_v152 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 474220000 :=
  small_extend2 (a := 473230000) (A := 473230002) (lo := 473228190) (W := 991810) (small_v151 h)
    ⟨236615000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v152

theorem small_v153 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 475210000 :=
  small_extend2 (a := 474220000) (A := 474220002) (lo := 474218190) (W := 991810) (small_v152 h)
    ⟨237110000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v153

theorem small_v154 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 476200000 :=
  small_extend2 (a := 475210000) (A := 475210002) (lo := 475208190) (W := 991810) (small_v153 h)
    ⟨237605000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v154

theorem small_v155 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 477190000 :=
  small_extend2 (a := 476200000) (A := 476200002) (lo := 476198190) (W := 991810) (small_v154 h)
    ⟨238100000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v155

theorem small_v156 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 478180000 :=
  small_extend2 (a := 477190000) (A := 477190002) (lo := 477188190) (W := 991810) (small_v155 h)
    ⟨238595000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v156

theorem small_v157 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 479170000 :=
  small_extend2 (a := 478180000) (A := 478180002) (lo := 478178190) (W := 991810) (small_v156 h)
    ⟨239090000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v157

theorem small_v158 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 480160000 :=
  small_extend2 (a := 479170000) (A := 479170002) (lo := 479168190) (W := 991810) (small_v157 h)
    ⟨239585000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v158

theorem small_v159 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 481150000 :=
  small_extend2 (a := 480160000) (A := 480160002) (lo := 480158190) (W := 991810) (small_v158 h)
    ⟨240080000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v159

theorem small_v160 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 482140000 :=
  small_extend2 (a := 481150000) (A := 481150002) (lo := 481148190) (W := 991810) (small_v159 h)
    ⟨240575000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v160

theorem small_v161 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 483130000 :=
  small_extend2 (a := 482140000) (A := 482140002) (lo := 482138190) (W := 991810) (small_v160 h)
    ⟨241070000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v161

theorem small_v162 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 484120000 :=
  small_extend2 (a := 483130000) (A := 483130002) (lo := 483128190) (W := 991810) (small_v161 h)
    ⟨241565000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v162

theorem small_v163 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 485110000 :=
  small_extend2 (a := 484120000) (A := 484120002) (lo := 484118190) (W := 991810) (small_v162 h)
    ⟨242060000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v163

theorem small_v164 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 486100000 :=
  small_extend2 (a := 485110000) (A := 485110002) (lo := 485108190) (W := 991810) (small_v163 h)
    ⟨242555000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v164

theorem small_v165 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 487090000 :=
  small_extend2 (a := 486100000) (A := 486100002) (lo := 486098190) (W := 991810) (small_v164 h)
    ⟨243050000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v165

theorem small_v166 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 488080000 :=
  small_extend2 (a := 487090000) (A := 487090002) (lo := 487088190) (W := 991810) (small_v165 h)
    ⟨243545000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v166

theorem small_v167 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 489070000 :=
  small_extend2 (a := 488080000) (A := 488080002) (lo := 488078190) (W := 991810) (small_v166 h)
    ⟨244040000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v167

theorem small_v168 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 490060000 :=
  small_extend2 (a := 489070000) (A := 489070002) (lo := 489068190) (W := 991810) (small_v167 h)
    ⟨244535000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v168

theorem small_v169 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 491050000 :=
  small_extend2 (a := 490060000) (A := 490060002) (lo := 490058190) (W := 991810) (small_v168 h)
    ⟨245030000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v169

theorem small_v170 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 492040000 :=
  small_extend2 (a := 491050000) (A := 491050002) (lo := 491048190) (W := 991810) (small_v169 h)
    ⟨245525000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v170

theorem small_v171 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 493030000 :=
  small_extend2 (a := 492040000) (A := 492040002) (lo := 492038190) (W := 991810) (small_v170 h)
    ⟨246020000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v171

theorem small_v172 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 494020000 :=
  small_extend2 (a := 493030000) (A := 493030002) (lo := 493028190) (W := 991810) (small_v171 h)
    ⟨246515000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v172

theorem small_v173 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 495010000 :=
  small_extend2 (a := 494020000) (A := 494020002) (lo := 494018190) (W := 991810) (small_v172 h)
    ⟨247010000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v173

theorem small_v174 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 496000000 :=
  small_extend2 (a := 495010000) (A := 495010002) (lo := 495008190) (W := 991810) (small_v173 h)
    ⟨247505000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v174

theorem small_v175 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 496990000 :=
  small_extend2 (a := 496000000) (A := 496000002) (lo := 495998190) (W := 991810) (small_v174 h)
    ⟨248000000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v175

theorem small_v176 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 497980000 :=
  small_extend2 (a := 496990000) (A := 496990002) (lo := 496988190) (W := 991810) (small_v175 h)
    ⟨248495000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v176

theorem small_v177 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 498970000 :=
  small_extend2 (a := 497980000) (A := 497980002) (lo := 497978190) (W := 991810) (small_v176 h)
    ⟨248990000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v177

theorem small_v178 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 499960000 :=
  small_extend2 (a := 498970000) (A := 498970002) (lo := 498968190) (W := 991810) (small_v177 h)
    ⟨249485000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v178

theorem small_v179 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 500950000 :=
  small_extend2 (a := 499960000) (A := 499960002) (lo := 499958190) (W := 991810) (small_v178 h)
    ⟨249980000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v179

theorem small_v180 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 501940000 :=
  small_extend2 (a := 500950000) (A := 500950002) (lo := 500948190) (W := 991810) (small_v179 h)
    ⟨250475000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v180

theorem small_v181 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 502930000 :=
  small_extend2 (a := 501940000) (A := 501940002) (lo := 501938190) (W := 991810) (small_v180 h)
    ⟨250970000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v181

theorem small_v182 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 503920000 :=
  small_extend2 (a := 502930000) (A := 502930002) (lo := 502928190) (W := 991810) (small_v181 h)
    ⟨251465000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v182

theorem small_v183 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 504910000 :=
  small_extend2 (a := 503920000) (A := 503920002) (lo := 503918190) (W := 991810) (small_v182 h)
    ⟨251960000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v183

theorem small_v184 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 505900000 :=
  small_extend2 (a := 504910000) (A := 504910002) (lo := 504908190) (W := 991810) (small_v183 h)
    ⟨252455000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v184

theorem small_v185 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 506890000 :=
  small_extend2 (a := 505900000) (A := 505900002) (lo := 505898190) (W := 991810) (small_v184 h)
    ⟨252950000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v185

theorem small_v186 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 507880000 :=
  small_extend2 (a := 506890000) (A := 506890002) (lo := 506888190) (W := 991810) (small_v185 h)
    ⟨253445000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v186

theorem small_v187 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 508870000 :=
  small_extend2 (a := 507880000) (A := 507880002) (lo := 507878190) (W := 991810) (small_v186 h)
    ⟨253940000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v187

theorem small_v188 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 509860000 :=
  small_extend2 (a := 508870000) (A := 508870002) (lo := 508868190) (W := 991810) (small_v187 h)
    ⟨254435000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v188

theorem small_v189 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 510850000 :=
  small_extend2 (a := 509860000) (A := 509860002) (lo := 509858190) (W := 991810) (small_v188 h)
    ⟨254930000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v189

theorem small_v190 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 511840000 :=
  small_extend2 (a := 510850000) (A := 510850002) (lo := 510848190) (W := 991810) (small_v189 h)
    ⟨255425000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v190

theorem small_v191 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 512830000 :=
  small_extend2 (a := 511840000) (A := 511840002) (lo := 511838190) (W := 991810) (small_v190 h)
    ⟨255920000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v191

theorem small_v192 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 513820000 :=
  small_extend2 (a := 512830000) (A := 512830002) (lo := 512828190) (W := 991810) (small_v191 h)
    ⟨256415000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v192

theorem small_v193 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 514810000 :=
  small_extend2 (a := 513820000) (A := 513820002) (lo := 513818190) (W := 991810) (small_v192 h)
    ⟨256910000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v193

theorem small_v194 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 515800000 :=
  small_extend2 (a := 514810000) (A := 514810002) (lo := 514808190) (W := 991810) (small_v193 h)
    ⟨257405000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v194

theorem small_v195 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 516790000 :=
  small_extend2 (a := 515800000) (A := 515800002) (lo := 515798190) (W := 991810) (small_v194 h)
    ⟨257900000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v195

theorem small_v196 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 517780000 :=
  small_extend2 (a := 516790000) (A := 516790002) (lo := 516788190) (W := 991810) (small_v195 h)
    ⟨258395000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v196

theorem small_v197 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 518770000 :=
  small_extend2 (a := 517780000) (A := 517780002) (lo := 517778190) (W := 991810) (small_v196 h)
    ⟨258890000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v197

theorem small_v198 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 519760000 :=
  small_extend2 (a := 518770000) (A := 518770002) (lo := 518768190) (W := 991810) (small_v197 h)
    ⟨259385000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v198

theorem small_v199 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 520750000 :=
  small_extend2 (a := 519760000) (A := 519760002) (lo := 519758190) (W := 991810) (small_v198 h)
    ⟨259880000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v199

theorem small_v200 (h : SmallGBUpTo 1811 422740000) : SmallGBUpTo 1811 521740000 :=
  small_extend2 (a := 520750000) (A := 520750002) (lo := 520748190) (W := 991810) (small_v199 h)
    ⟨260375000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v200

end LeanLab.Verifications.Top50.Bits
