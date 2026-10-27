/-
Chain block 1 of the kernel Goldbach windows past 10^8: windows 51 to 100, from
EvenGoldbachUpTo 100000000 to EvenGoldbachUpTo 199000000, so the blocks compose. Each step is upTo_extend2 in BitSieve2.lean.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2
import LeanLab.Verifications.Top50.BitW51
import LeanLab.Verifications.Top50.BitW52
import LeanLab.Verifications.Top50.BitW53
import LeanLab.Verifications.Top50.BitW54
import LeanLab.Verifications.Top50.BitW55
import LeanLab.Verifications.Top50.BitW56
import LeanLab.Verifications.Top50.BitW57
import LeanLab.Verifications.Top50.BitW58
import LeanLab.Verifications.Top50.BitW59
import LeanLab.Verifications.Top50.BitW60
import LeanLab.Verifications.Top50.BitW61
import LeanLab.Verifications.Top50.BitW62
import LeanLab.Verifications.Top50.BitW63
import LeanLab.Verifications.Top50.BitW64
import LeanLab.Verifications.Top50.BitW65
import LeanLab.Verifications.Top50.BitW66
import LeanLab.Verifications.Top50.BitW67
import LeanLab.Verifications.Top50.BitW68
import LeanLab.Verifications.Top50.BitW69
import LeanLab.Verifications.Top50.BitW70
import LeanLab.Verifications.Top50.BitW71
import LeanLab.Verifications.Top50.BitW72
import LeanLab.Verifications.Top50.BitW73
import LeanLab.Verifications.Top50.BitW74
import LeanLab.Verifications.Top50.BitW75
import LeanLab.Verifications.Top50.BitW76
import LeanLab.Verifications.Top50.BitW77
import LeanLab.Verifications.Top50.BitW78
import LeanLab.Verifications.Top50.BitW79
import LeanLab.Verifications.Top50.BitW80
import LeanLab.Verifications.Top50.BitW81
import LeanLab.Verifications.Top50.BitW82
import LeanLab.Verifications.Top50.BitW83
import LeanLab.Verifications.Top50.BitW84
import LeanLab.Verifications.Top50.BitW85
import LeanLab.Verifications.Top50.BitW86
import LeanLab.Verifications.Top50.BitW87
import LeanLab.Verifications.Top50.BitW88
import LeanLab.Verifications.Top50.BitW89
import LeanLab.Verifications.Top50.BitW90
import LeanLab.Verifications.Top50.BitW91
import LeanLab.Verifications.Top50.BitW92
import LeanLab.Verifications.Top50.BitW93
import LeanLab.Verifications.Top50.BitW94
import LeanLab.Verifications.Top50.BitW95
import LeanLab.Verifications.Top50.BitW96
import LeanLab.Verifications.Top50.BitW97
import LeanLab.Verifications.Top50.BitW98
import LeanLab.Verifications.Top50.BitW99
import LeanLab.Verifications.Top50.BitW100

namespace LeanLab.Verifications.Top50.Bits

theorem upTo_w51 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 101980000 :=
  upTo_extend2 (a := 100000000) (A := 100000002) (lo := 99998190) (W := 1981810) h
    ⟨50000000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_51

theorem upTo_w52 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 103960000 :=
  upTo_extend2 (a := 101980000) (A := 101980002) (lo := 101978190) (W := 1981810) (upTo_w51 h)
    ⟨50990000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_52

theorem upTo_w53 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 105940000 :=
  upTo_extend2 (a := 103960000) (A := 103960002) (lo := 103958190) (W := 1981810) (upTo_w52 h)
    ⟨51980000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_53

theorem upTo_w54 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 107920000 :=
  upTo_extend2 (a := 105940000) (A := 105940002) (lo := 105938190) (W := 1981810) (upTo_w53 h)
    ⟨52970000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_54

theorem upTo_w55 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 109900000 :=
  upTo_extend2 (a := 107920000) (A := 107920002) (lo := 107918190) (W := 1981810) (upTo_w54 h)
    ⟨53960000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_55

theorem upTo_w56 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 111880000 :=
  upTo_extend2 (a := 109900000) (A := 109900002) (lo := 109898190) (W := 1981810) (upTo_w55 h)
    ⟨54950000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_56

theorem upTo_w57 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 113860000 :=
  upTo_extend2 (a := 111880000) (A := 111880002) (lo := 111878190) (W := 1981810) (upTo_w56 h)
    ⟨55940000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_57

theorem upTo_w58 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 115840000 :=
  upTo_extend2 (a := 113860000) (A := 113860002) (lo := 113858190) (W := 1981810) (upTo_w57 h)
    ⟨56930000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_58

theorem upTo_w59 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 117820000 :=
  upTo_extend2 (a := 115840000) (A := 115840002) (lo := 115838190) (W := 1981810) (upTo_w58 h)
    ⟨57920000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_59

theorem upTo_w60 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 119800000 :=
  upTo_extend2 (a := 117820000) (A := 117820002) (lo := 117818190) (W := 1981810) (upTo_w59 h)
    ⟨58910000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_60

theorem upTo_w61 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 121780000 :=
  upTo_extend2 (a := 119800000) (A := 119800002) (lo := 119798190) (W := 1981810) (upTo_w60 h)
    ⟨59900000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_61

theorem upTo_w62 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 123760000 :=
  upTo_extend2 (a := 121780000) (A := 121780002) (lo := 121778190) (W := 1981810) (upTo_w61 h)
    ⟨60890000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_62

theorem upTo_w63 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 125740000 :=
  upTo_extend2 (a := 123760000) (A := 123760002) (lo := 123758190) (W := 1981810) (upTo_w62 h)
    ⟨61880000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_63

theorem upTo_w64 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 127720000 :=
  upTo_extend2 (a := 125740000) (A := 125740002) (lo := 125738190) (W := 1981810) (upTo_w63 h)
    ⟨62870000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_64

theorem upTo_w65 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 129700000 :=
  upTo_extend2 (a := 127720000) (A := 127720002) (lo := 127718190) (W := 1981810) (upTo_w64 h)
    ⟨63860000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_65

theorem upTo_w66 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 131680000 :=
  upTo_extend2 (a := 129700000) (A := 129700002) (lo := 129698190) (W := 1981810) (upTo_w65 h)
    ⟨64850000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_66

theorem upTo_w67 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 133660000 :=
  upTo_extend2 (a := 131680000) (A := 131680002) (lo := 131678190) (W := 1981810) (upTo_w66 h)
    ⟨65840000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_67

theorem upTo_w68 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 135640000 :=
  upTo_extend2 (a := 133660000) (A := 133660002) (lo := 133658190) (W := 1981810) (upTo_w67 h)
    ⟨66830000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_68

theorem upTo_w69 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 137620000 :=
  upTo_extend2 (a := 135640000) (A := 135640002) (lo := 135638190) (W := 1981810) (upTo_w68 h)
    ⟨67820000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_69

theorem upTo_w70 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 139600000 :=
  upTo_extend2 (a := 137620000) (A := 137620002) (lo := 137618190) (W := 1981810) (upTo_w69 h)
    ⟨68810000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_70

theorem upTo_w71 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 141580000 :=
  upTo_extend2 (a := 139600000) (A := 139600002) (lo := 139598190) (W := 1981810) (upTo_w70 h)
    ⟨69800000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_71

theorem upTo_w72 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 143560000 :=
  upTo_extend2 (a := 141580000) (A := 141580002) (lo := 141578190) (W := 1981810) (upTo_w71 h)
    ⟨70790000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_72

theorem upTo_w73 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 145540000 :=
  upTo_extend2 (a := 143560000) (A := 143560002) (lo := 143558190) (W := 1981810) (upTo_w72 h)
    ⟨71780000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_73

theorem upTo_w74 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 147520000 :=
  upTo_extend2 (a := 145540000) (A := 145540002) (lo := 145538190) (W := 1981810) (upTo_w73 h)
    ⟨72770000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_74

theorem upTo_w75 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 149500000 :=
  upTo_extend2 (a := 147520000) (A := 147520002) (lo := 147518190) (W := 1981810) (upTo_w74 h)
    ⟨73760000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_75

theorem upTo_w76 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 151480000 :=
  upTo_extend2 (a := 149500000) (A := 149500002) (lo := 149498190) (W := 1981810) (upTo_w75 h)
    ⟨74750000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_76

theorem upTo_w77 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 153460000 :=
  upTo_extend2 (a := 151480000) (A := 151480002) (lo := 151478190) (W := 1981810) (upTo_w76 h)
    ⟨75740000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_77

theorem upTo_w78 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 155440000 :=
  upTo_extend2 (a := 153460000) (A := 153460002) (lo := 153458190) (W := 1981810) (upTo_w77 h)
    ⟨76730000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_78

theorem upTo_w79 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 157420000 :=
  upTo_extend2 (a := 155440000) (A := 155440002) (lo := 155438190) (W := 1981810) (upTo_w78 h)
    ⟨77720000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_79

theorem upTo_w80 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 159400000 :=
  upTo_extend2 (a := 157420000) (A := 157420002) (lo := 157418190) (W := 1981810) (upTo_w79 h)
    ⟨78710000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_80

theorem upTo_w81 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 161380000 :=
  upTo_extend2 (a := 159400000) (A := 159400002) (lo := 159398190) (W := 1981810) (upTo_w80 h)
    ⟨79700000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_81

theorem upTo_w82 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 163360000 :=
  upTo_extend2 (a := 161380000) (A := 161380002) (lo := 161378190) (W := 1981810) (upTo_w81 h)
    ⟨80690000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_82

theorem upTo_w83 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 165340000 :=
  upTo_extend2 (a := 163360000) (A := 163360002) (lo := 163358190) (W := 1981810) (upTo_w82 h)
    ⟨81680000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_83

theorem upTo_w84 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 167320000 :=
  upTo_extend2 (a := 165340000) (A := 165340002) (lo := 165338190) (W := 1981810) (upTo_w83 h)
    ⟨82670000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_84

theorem upTo_w85 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 169300000 :=
  upTo_extend2 (a := 167320000) (A := 167320002) (lo := 167318190) (W := 1981810) (upTo_w84 h)
    ⟨83660000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_85

theorem upTo_w86 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 171280000 :=
  upTo_extend2 (a := 169300000) (A := 169300002) (lo := 169298190) (W := 1981810) (upTo_w85 h)
    ⟨84650000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_86

theorem upTo_w87 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 173260000 :=
  upTo_extend2 (a := 171280000) (A := 171280002) (lo := 171278190) (W := 1981810) (upTo_w86 h)
    ⟨85640000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_87

theorem upTo_w88 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 175240000 :=
  upTo_extend2 (a := 173260000) (A := 173260002) (lo := 173258190) (W := 1981810) (upTo_w87 h)
    ⟨86630000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_88

theorem upTo_w89 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 177220000 :=
  upTo_extend2 (a := 175240000) (A := 175240002) (lo := 175238190) (W := 1981810) (upTo_w88 h)
    ⟨87620000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_89

theorem upTo_w90 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 179200000 :=
  upTo_extend2 (a := 177220000) (A := 177220002) (lo := 177218190) (W := 1981810) (upTo_w89 h)
    ⟨88610000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_90

theorem upTo_w91 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 181180000 :=
  upTo_extend2 (a := 179200000) (A := 179200002) (lo := 179198190) (W := 1981810) (upTo_w90 h)
    ⟨89600000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_91

theorem upTo_w92 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 183160000 :=
  upTo_extend2 (a := 181180000) (A := 181180002) (lo := 181178190) (W := 1981810) (upTo_w91 h)
    ⟨90590000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_92

theorem upTo_w93 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 185140000 :=
  upTo_extend2 (a := 183160000) (A := 183160002) (lo := 183158190) (W := 1981810) (upTo_w92 h)
    ⟨91580000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_93

theorem upTo_w94 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 187120000 :=
  upTo_extend2 (a := 185140000) (A := 185140002) (lo := 185138190) (W := 1981810) (upTo_w93 h)
    ⟨92570000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_94

theorem upTo_w95 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 189100000 :=
  upTo_extend2 (a := 187120000) (A := 187120002) (lo := 187118190) (W := 1981810) (upTo_w94 h)
    ⟨93560000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_95

theorem upTo_w96 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 191080000 :=
  upTo_extend2 (a := 189100000) (A := 189100002) (lo := 189098190) (W := 1981810) (upTo_w95 h)
    ⟨94550000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_96

theorem upTo_w97 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 193060000 :=
  upTo_extend2 (a := 191080000) (A := 191080002) (lo := 191078190) (W := 1981810) (upTo_w96 h)
    ⟨95540000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_97

theorem upTo_w98 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 195040000 :=
  upTo_extend2 (a := 193060000) (A := 193060002) (lo := 193058190) (W := 1981810) (upTo_w97 h)
    ⟨96530000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_98

theorem upTo_w99 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 197020000 :=
  upTo_extend2 (a := 195040000) (A := 195040002) (lo := 195038190) (W := 1981810) (upTo_w98 h)
    ⟨97520000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_99

theorem upTo_w100 (h : EvenGoldbachUpTo 100000000) : EvenGoldbachUpTo 199000000 :=
  upTo_extend2 (a := 197020000) (A := 197020002) (lo := 197018190) (W := 1981810) (upTo_w99 h)
    ⟨98510000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) window_100

end LeanLab.Verifications.Top50.Bits
