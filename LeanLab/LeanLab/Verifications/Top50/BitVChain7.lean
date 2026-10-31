/-
Chain block V7 of the kernel Goldbach windows past 323740000: windows V601 to V684, from
SmallGBUpTo 1811 917740000 to SmallGBUpTo 1811 1000900000, so the blocks compose. Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.SmallGB
import LeanLab.Verifications.Top50.BitVG61
import LeanLab.Verifications.Top50.BitVG62
import LeanLab.Verifications.Top50.BitVG63
import LeanLab.Verifications.Top50.BitVG64
import LeanLab.Verifications.Top50.BitVG65
import LeanLab.Verifications.Top50.BitVG66
import LeanLab.Verifications.Top50.BitVG67
import LeanLab.Verifications.Top50.BitVG68
import LeanLab.Verifications.Top50.BitVG69

namespace LeanLab.Verifications.Top50.Bits

theorem small_v601 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 918730000 :=
  small_extend2 (a := 917740000) (A := 917740002) (lo := 917738190) (W := 991810) h
    ⟨458870000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v601

theorem small_v602 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 919720000 :=
  small_extend2 (a := 918730000) (A := 918730002) (lo := 918728190) (W := 991810) (small_v601 h)
    ⟨459365000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v602

theorem small_v603 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 920710000 :=
  small_extend2 (a := 919720000) (A := 919720002) (lo := 919718190) (W := 991810) (small_v602 h)
    ⟨459860000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v603

theorem small_v604 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 921700000 :=
  small_extend2 (a := 920710000) (A := 920710002) (lo := 920708190) (W := 991810) (small_v603 h)
    ⟨460355000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v604

theorem small_v605 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 922690000 :=
  small_extend2 (a := 921700000) (A := 921700002) (lo := 921698190) (W := 991810) (small_v604 h)
    ⟨460850000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v605

theorem small_v606 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 923680000 :=
  small_extend2 (a := 922690000) (A := 922690002) (lo := 922688190) (W := 991810) (small_v605 h)
    ⟨461345000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v606

theorem small_v607 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 924670000 :=
  small_extend2 (a := 923680000) (A := 923680002) (lo := 923678190) (W := 991810) (small_v606 h)
    ⟨461840000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v607

theorem small_v608 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 925660000 :=
  small_extend2 (a := 924670000) (A := 924670002) (lo := 924668190) (W := 991810) (small_v607 h)
    ⟨462335000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v608

theorem small_v609 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 926650000 :=
  small_extend2 (a := 925660000) (A := 925660002) (lo := 925658190) (W := 991810) (small_v608 h)
    ⟨462830000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v609

theorem small_v610 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 927640000 :=
  small_extend2 (a := 926650000) (A := 926650002) (lo := 926648190) (W := 991810) (small_v609 h)
    ⟨463325000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v610

theorem small_v611 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 928630000 :=
  small_extend2 (a := 927640000) (A := 927640002) (lo := 927638190) (W := 991810) (small_v610 h)
    ⟨463820000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v611

theorem small_v612 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 929620000 :=
  small_extend2 (a := 928630000) (A := 928630002) (lo := 928628190) (W := 991810) (small_v611 h)
    ⟨464315000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v612

theorem small_v613 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 930610000 :=
  small_extend2 (a := 929620000) (A := 929620002) (lo := 929618190) (W := 991810) (small_v612 h)
    ⟨464810000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v613

theorem small_v614 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 931600000 :=
  small_extend2 (a := 930610000) (A := 930610002) (lo := 930608190) (W := 991810) (small_v613 h)
    ⟨465305000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v614

theorem small_v615 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 932590000 :=
  small_extend2 (a := 931600000) (A := 931600002) (lo := 931598190) (W := 991810) (small_v614 h)
    ⟨465800000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v615

theorem small_v616 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 933580000 :=
  small_extend2 (a := 932590000) (A := 932590002) (lo := 932588190) (W := 991810) (small_v615 h)
    ⟨466295000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v616

theorem small_v617 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 934570000 :=
  small_extend2 (a := 933580000) (A := 933580002) (lo := 933578190) (W := 991810) (small_v616 h)
    ⟨466790000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v617

theorem small_v618 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 935560000 :=
  small_extend2 (a := 934570000) (A := 934570002) (lo := 934568190) (W := 991810) (small_v617 h)
    ⟨467285000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v618

theorem small_v619 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 936550000 :=
  small_extend2 (a := 935560000) (A := 935560002) (lo := 935558190) (W := 991810) (small_v618 h)
    ⟨467780000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v619

theorem small_v620 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 937540000 :=
  small_extend2 (a := 936550000) (A := 936550002) (lo := 936548190) (W := 991810) (small_v619 h)
    ⟨468275000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v620

theorem small_v621 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 938530000 :=
  small_extend2 (a := 937540000) (A := 937540002) (lo := 937538190) (W := 991810) (small_v620 h)
    ⟨468770000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v621

theorem small_v622 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 939520000 :=
  small_extend2 (a := 938530000) (A := 938530002) (lo := 938528190) (W := 991810) (small_v621 h)
    ⟨469265000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v622

theorem small_v623 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 940510000 :=
  small_extend2 (a := 939520000) (A := 939520002) (lo := 939518190) (W := 991810) (small_v622 h)
    ⟨469760000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v623

theorem small_v624 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 941500000 :=
  small_extend2 (a := 940510000) (A := 940510002) (lo := 940508190) (W := 991810) (small_v623 h)
    ⟨470255000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v624

theorem small_v625 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 942490000 :=
  small_extend2 (a := 941500000) (A := 941500002) (lo := 941498190) (W := 991810) (small_v624 h)
    ⟨470750000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v625

theorem small_v626 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 943480000 :=
  small_extend2 (a := 942490000) (A := 942490002) (lo := 942488190) (W := 991810) (small_v625 h)
    ⟨471245000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v626

theorem small_v627 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 944470000 :=
  small_extend2 (a := 943480000) (A := 943480002) (lo := 943478190) (W := 991810) (small_v626 h)
    ⟨471740000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v627

theorem small_v628 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 945460000 :=
  small_extend2 (a := 944470000) (A := 944470002) (lo := 944468190) (W := 991810) (small_v627 h)
    ⟨472235000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v628

theorem small_v629 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 946450000 :=
  small_extend2 (a := 945460000) (A := 945460002) (lo := 945458190) (W := 991810) (small_v628 h)
    ⟨472730000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v629

theorem small_v630 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 947440000 :=
  small_extend2 (a := 946450000) (A := 946450002) (lo := 946448190) (W := 991810) (small_v629 h)
    ⟨473225000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v630

theorem small_v631 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 948430000 :=
  small_extend2 (a := 947440000) (A := 947440002) (lo := 947438190) (W := 991810) (small_v630 h)
    ⟨473720000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v631

theorem small_v632 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 949420000 :=
  small_extend2 (a := 948430000) (A := 948430002) (lo := 948428190) (W := 991810) (small_v631 h)
    ⟨474215000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v632

theorem small_v633 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 950410000 :=
  small_extend2 (a := 949420000) (A := 949420002) (lo := 949418190) (W := 991810) (small_v632 h)
    ⟨474710000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v633

theorem small_v634 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 951400000 :=
  small_extend2 (a := 950410000) (A := 950410002) (lo := 950408190) (W := 991810) (small_v633 h)
    ⟨475205000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v634

theorem small_v635 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 952390000 :=
  small_extend2 (a := 951400000) (A := 951400002) (lo := 951398190) (W := 991810) (small_v634 h)
    ⟨475700000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v635

theorem small_v636 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 953380000 :=
  small_extend2 (a := 952390000) (A := 952390002) (lo := 952388190) (W := 991810) (small_v635 h)
    ⟨476195000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v636

theorem small_v637 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 954370000 :=
  small_extend2 (a := 953380000) (A := 953380002) (lo := 953378190) (W := 991810) (small_v636 h)
    ⟨476690000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v637

theorem small_v638 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 955360000 :=
  small_extend2 (a := 954370000) (A := 954370002) (lo := 954368190) (W := 991810) (small_v637 h)
    ⟨477185000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v638

theorem small_v639 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 956350000 :=
  small_extend2 (a := 955360000) (A := 955360002) (lo := 955358190) (W := 991810) (small_v638 h)
    ⟨477680000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v639

theorem small_v640 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 957340000 :=
  small_extend2 (a := 956350000) (A := 956350002) (lo := 956348190) (W := 991810) (small_v639 h)
    ⟨478175000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v640

theorem small_v641 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 958330000 :=
  small_extend2 (a := 957340000) (A := 957340002) (lo := 957338190) (W := 991810) (small_v640 h)
    ⟨478670000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v641

theorem small_v642 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 959320000 :=
  small_extend2 (a := 958330000) (A := 958330002) (lo := 958328190) (W := 991810) (small_v641 h)
    ⟨479165000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v642

theorem small_v643 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 960310000 :=
  small_extend2 (a := 959320000) (A := 959320002) (lo := 959318190) (W := 991810) (small_v642 h)
    ⟨479660000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v643

theorem small_v644 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 961300000 :=
  small_extend2 (a := 960310000) (A := 960310002) (lo := 960308190) (W := 991810) (small_v643 h)
    ⟨480155000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v644

theorem small_v645 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 962290000 :=
  small_extend2 (a := 961300000) (A := 961300002) (lo := 961298190) (W := 991810) (small_v644 h)
    ⟨480650000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v645

theorem small_v646 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 963280000 :=
  small_extend2 (a := 962290000) (A := 962290002) (lo := 962288190) (W := 991810) (small_v645 h)
    ⟨481145000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v646

theorem small_v647 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 964270000 :=
  small_extend2 (a := 963280000) (A := 963280002) (lo := 963278190) (W := 991810) (small_v646 h)
    ⟨481640000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v647

theorem small_v648 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 965260000 :=
  small_extend2 (a := 964270000) (A := 964270002) (lo := 964268190) (W := 991810) (small_v647 h)
    ⟨482135000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v648

theorem small_v649 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 966250000 :=
  small_extend2 (a := 965260000) (A := 965260002) (lo := 965258190) (W := 991810) (small_v648 h)
    ⟨482630000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v649

theorem small_v650 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 967240000 :=
  small_extend2 (a := 966250000) (A := 966250002) (lo := 966248190) (W := 991810) (small_v649 h)
    ⟨483125000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v650

theorem small_v651 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 968230000 :=
  small_extend2 (a := 967240000) (A := 967240002) (lo := 967238190) (W := 991810) (small_v650 h)
    ⟨483620000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v651

theorem small_v652 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 969220000 :=
  small_extend2 (a := 968230000) (A := 968230002) (lo := 968228190) (W := 991810) (small_v651 h)
    ⟨484115000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v652

theorem small_v653 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 970210000 :=
  small_extend2 (a := 969220000) (A := 969220002) (lo := 969218190) (W := 991810) (small_v652 h)
    ⟨484610000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v653

theorem small_v654 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 971200000 :=
  small_extend2 (a := 970210000) (A := 970210002) (lo := 970208190) (W := 991810) (small_v653 h)
    ⟨485105000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v654

theorem small_v655 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 972190000 :=
  small_extend2 (a := 971200000) (A := 971200002) (lo := 971198190) (W := 991810) (small_v654 h)
    ⟨485600000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v655

theorem small_v656 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 973180000 :=
  small_extend2 (a := 972190000) (A := 972190002) (lo := 972188190) (W := 991810) (small_v655 h)
    ⟨486095000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v656

theorem small_v657 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 974170000 :=
  small_extend2 (a := 973180000) (A := 973180002) (lo := 973178190) (W := 991810) (small_v656 h)
    ⟨486590000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v657

theorem small_v658 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 975160000 :=
  small_extend2 (a := 974170000) (A := 974170002) (lo := 974168190) (W := 991810) (small_v657 h)
    ⟨487085000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v658

theorem small_v659 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 976150000 :=
  small_extend2 (a := 975160000) (A := 975160002) (lo := 975158190) (W := 991810) (small_v658 h)
    ⟨487580000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v659

theorem small_v660 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 977140000 :=
  small_extend2 (a := 976150000) (A := 976150002) (lo := 976148190) (W := 991810) (small_v659 h)
    ⟨488075000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v660

theorem small_v661 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 978130000 :=
  small_extend2 (a := 977140000) (A := 977140002) (lo := 977138190) (W := 991810) (small_v660 h)
    ⟨488570000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v661

theorem small_v662 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 979120000 :=
  small_extend2 (a := 978130000) (A := 978130002) (lo := 978128190) (W := 991810) (small_v661 h)
    ⟨489065000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v662

theorem small_v663 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 980110000 :=
  small_extend2 (a := 979120000) (A := 979120002) (lo := 979118190) (W := 991810) (small_v662 h)
    ⟨489560000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v663

theorem small_v664 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 981100000 :=
  small_extend2 (a := 980110000) (A := 980110002) (lo := 980108190) (W := 991810) (small_v663 h)
    ⟨490055000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v664

theorem small_v665 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 982090000 :=
  small_extend2 (a := 981100000) (A := 981100002) (lo := 981098190) (W := 991810) (small_v664 h)
    ⟨490550000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v665

theorem small_v666 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 983080000 :=
  small_extend2 (a := 982090000) (A := 982090002) (lo := 982088190) (W := 991810) (small_v665 h)
    ⟨491045000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v666

theorem small_v667 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 984070000 :=
  small_extend2 (a := 983080000) (A := 983080002) (lo := 983078190) (W := 991810) (small_v666 h)
    ⟨491540000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v667

theorem small_v668 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 985060000 :=
  small_extend2 (a := 984070000) (A := 984070002) (lo := 984068190) (W := 991810) (small_v667 h)
    ⟨492035000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v668

theorem small_v669 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 986050000 :=
  small_extend2 (a := 985060000) (A := 985060002) (lo := 985058190) (W := 991810) (small_v668 h)
    ⟨492530000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v669

theorem small_v670 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 987040000 :=
  small_extend2 (a := 986050000) (A := 986050002) (lo := 986048190) (W := 991810) (small_v669 h)
    ⟨493025000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v670

theorem small_v671 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 988030000 :=
  small_extend2 (a := 987040000) (A := 987040002) (lo := 987038190) (W := 991810) (small_v670 h)
    ⟨493520000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v671

theorem small_v672 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 989020000 :=
  small_extend2 (a := 988030000) (A := 988030002) (lo := 988028190) (W := 991810) (small_v671 h)
    ⟨494015000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v672

theorem small_v673 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 990010000 :=
  small_extend2 (a := 989020000) (A := 989020002) (lo := 989018190) (W := 991810) (small_v672 h)
    ⟨494510000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v673

theorem small_v674 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 991000000 :=
  small_extend2 (a := 990010000) (A := 990010002) (lo := 990008190) (W := 991810) (small_v673 h)
    ⟨495005000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v674

theorem small_v675 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 991990000 :=
  small_extend2 (a := 991000000) (A := 991000002) (lo := 990998190) (W := 991810) (small_v674 h)
    ⟨495500000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v675

theorem small_v676 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 992980000 :=
  small_extend2 (a := 991990000) (A := 991990002) (lo := 991988190) (W := 991810) (small_v675 h)
    ⟨495995000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v676

theorem small_v677 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 993970000 :=
  small_extend2 (a := 992980000) (A := 992980002) (lo := 992978190) (W := 991810) (small_v676 h)
    ⟨496490000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v677

theorem small_v678 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 994960000 :=
  small_extend2 (a := 993970000) (A := 993970002) (lo := 993968190) (W := 991810) (small_v677 h)
    ⟨496985000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v678

theorem small_v679 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 995950000 :=
  small_extend2 (a := 994960000) (A := 994960002) (lo := 994958190) (W := 991810) (small_v678 h)
    ⟨497480000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v679

theorem small_v680 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 996940000 :=
  small_extend2 (a := 995950000) (A := 995950002) (lo := 995948190) (W := 991810) (small_v679 h)
    ⟨497975000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v680

theorem small_v681 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 997930000 :=
  small_extend2 (a := 996940000) (A := 996940002) (lo := 996938190) (W := 991810) (small_v680 h)
    ⟨498470000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v681

theorem small_v682 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 998920000 :=
  small_extend2 (a := 997930000) (A := 997930002) (lo := 997928190) (W := 991810) (small_v681 h)
    ⟨498965000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v682

theorem small_v683 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 999910000 :=
  small_extend2 (a := 998920000) (A := 998920002) (lo := 998918190) (W := 991810) (small_v682 h)
    ⟨499460000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v683

theorem small_v684 (h : SmallGBUpTo 1811 917740000) : SmallGBUpTo 1811 1000900000 :=
  small_extend2 (a := 999910000) (A := 999910002) (lo := 999908190) (W := 991810) (small_v683 h)
    ⟨499955000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v684

end LeanLab.Verifications.Top50.Bits
