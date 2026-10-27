/-
Chain block MV6: windows MV501 to MV600, from SmallGBUpTo 1789 818740000 to SmallGBUpTo 1789 917740000.
Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.MinGBBase
import LeanLab.Verifications.Top50.BitMVG51
import LeanLab.Verifications.Top50.BitMVG52
import LeanLab.Verifications.Top50.BitMVG53
import LeanLab.Verifications.Top50.BitMVG54
import LeanLab.Verifications.Top50.BitMVG55
import LeanLab.Verifications.Top50.BitMVG56
import LeanLab.Verifications.Top50.BitMVG57
import LeanLab.Verifications.Top50.BitMVG58
import LeanLab.Verifications.Top50.BitMVG59
import LeanLab.Verifications.Top50.BitMVG60

namespace LeanLab.Verifications.Top50.Bits

theorem msmall_v501 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 819730000 :=
  small_extend2 (a := 818740000) (A := 818740002) (lo := 818738190) (W := 991810) h
    ⟨409370000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v501

theorem msmall_v502 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 820720000 :=
  small_extend2 (a := 819730000) (A := 819730002) (lo := 819728190) (W := 991810) (msmall_v501 h)
    ⟨409865000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v502

theorem msmall_v503 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 821710000 :=
  small_extend2 (a := 820720000) (A := 820720002) (lo := 820718190) (W := 991810) (msmall_v502 h)
    ⟨410360000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v503

theorem msmall_v504 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 822700000 :=
  small_extend2 (a := 821710000) (A := 821710002) (lo := 821708190) (W := 991810) (msmall_v503 h)
    ⟨410855000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v504

theorem msmall_v505 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 823690000 :=
  small_extend2 (a := 822700000) (A := 822700002) (lo := 822698190) (W := 991810) (msmall_v504 h)
    ⟨411350000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v505

theorem msmall_v506 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 824680000 :=
  small_extend2 (a := 823690000) (A := 823690002) (lo := 823688190) (W := 991810) (msmall_v505 h)
    ⟨411845000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v506

theorem msmall_v507 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 825670000 :=
  small_extend2 (a := 824680000) (A := 824680002) (lo := 824678190) (W := 991810) (msmall_v506 h)
    ⟨412340000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v507

theorem msmall_v508 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 826660000 :=
  small_extend2 (a := 825670000) (A := 825670002) (lo := 825668190) (W := 991810) (msmall_v507 h)
    ⟨412835000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v508

theorem msmall_v509 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 827650000 :=
  small_extend2 (a := 826660000) (A := 826660002) (lo := 826658190) (W := 991810) (msmall_v508 h)
    ⟨413330000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v509

theorem msmall_v510 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 828640000 :=
  small_extend2 (a := 827650000) (A := 827650002) (lo := 827648190) (W := 991810) (msmall_v509 h)
    ⟨413825000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v510

theorem msmall_v511 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 829630000 :=
  small_extend2 (a := 828640000) (A := 828640002) (lo := 828638190) (W := 991810) (msmall_v510 h)
    ⟨414320000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v511

theorem msmall_v512 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 830620000 :=
  small_extend2 (a := 829630000) (A := 829630002) (lo := 829628190) (W := 991810) (msmall_v511 h)
    ⟨414815000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v512

theorem msmall_v513 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 831610000 :=
  small_extend2 (a := 830620000) (A := 830620002) (lo := 830618190) (W := 991810) (msmall_v512 h)
    ⟨415310000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v513

theorem msmall_v514 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 832600000 :=
  small_extend2 (a := 831610000) (A := 831610002) (lo := 831608190) (W := 991810) (msmall_v513 h)
    ⟨415805000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v514

theorem msmall_v515 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 833590000 :=
  small_extend2 (a := 832600000) (A := 832600002) (lo := 832598190) (W := 991810) (msmall_v514 h)
    ⟨416300000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v515

theorem msmall_v516 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 834580000 :=
  small_extend2 (a := 833590000) (A := 833590002) (lo := 833588190) (W := 991810) (msmall_v515 h)
    ⟨416795000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v516

theorem msmall_v517 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 835570000 :=
  small_extend2 (a := 834580000) (A := 834580002) (lo := 834578190) (W := 991810) (msmall_v516 h)
    ⟨417290000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v517

theorem msmall_v518 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 836560000 :=
  small_extend2 (a := 835570000) (A := 835570002) (lo := 835568190) (W := 991810) (msmall_v517 h)
    ⟨417785000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v518

theorem msmall_v519 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 837550000 :=
  small_extend2 (a := 836560000) (A := 836560002) (lo := 836558190) (W := 991810) (msmall_v518 h)
    ⟨418280000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v519

theorem msmall_v520 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 838540000 :=
  small_extend2 (a := 837550000) (A := 837550002) (lo := 837548190) (W := 991810) (msmall_v519 h)
    ⟨418775000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v520

theorem msmall_v521 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 839530000 :=
  small_extend2 (a := 838540000) (A := 838540002) (lo := 838538190) (W := 991810) (msmall_v520 h)
    ⟨419270000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v521

theorem msmall_v522 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 840520000 :=
  small_extend2 (a := 839530000) (A := 839530002) (lo := 839528190) (W := 991810) (msmall_v521 h)
    ⟨419765000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v522

theorem msmall_v523 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 841510000 :=
  small_extend2 (a := 840520000) (A := 840520002) (lo := 840518190) (W := 991810) (msmall_v522 h)
    ⟨420260000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v523

theorem msmall_v524 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 842500000 :=
  small_extend2 (a := 841510000) (A := 841510002) (lo := 841508190) (W := 991810) (msmall_v523 h)
    ⟨420755000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v524

theorem msmall_v525 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 843490000 :=
  small_extend2 (a := 842500000) (A := 842500002) (lo := 842498190) (W := 991810) (msmall_v524 h)
    ⟨421250000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v525

theorem msmall_v526 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 844480000 :=
  small_extend2 (a := 843490000) (A := 843490002) (lo := 843488190) (W := 991810) (msmall_v525 h)
    ⟨421745000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v526

theorem msmall_v527 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 845470000 :=
  small_extend2 (a := 844480000) (A := 844480002) (lo := 844478190) (W := 991810) (msmall_v526 h)
    ⟨422240000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v527

theorem msmall_v528 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 846460000 :=
  small_extend2 (a := 845470000) (A := 845470002) (lo := 845468190) (W := 991810) (msmall_v527 h)
    ⟨422735000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v528

theorem msmall_v529 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 847450000 :=
  small_extend2 (a := 846460000) (A := 846460002) (lo := 846458190) (W := 991810) (msmall_v528 h)
    ⟨423230000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v529

theorem msmall_v530 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 848440000 :=
  small_extend2 (a := 847450000) (A := 847450002) (lo := 847448190) (W := 991810) (msmall_v529 h)
    ⟨423725000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v530

theorem msmall_v531 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 849430000 :=
  small_extend2 (a := 848440000) (A := 848440002) (lo := 848438190) (W := 991810) (msmall_v530 h)
    ⟨424220000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v531

theorem msmall_v532 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 850420000 :=
  small_extend2 (a := 849430000) (A := 849430002) (lo := 849428190) (W := 991810) (msmall_v531 h)
    ⟨424715000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v532

theorem msmall_v533 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 851410000 :=
  small_extend2 (a := 850420000) (A := 850420002) (lo := 850418190) (W := 991810) (msmall_v532 h)
    ⟨425210000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v533

theorem msmall_v534 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 852400000 :=
  small_extend2 (a := 851410000) (A := 851410002) (lo := 851408190) (W := 991810) (msmall_v533 h)
    ⟨425705000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v534

theorem msmall_v535 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 853390000 :=
  small_extend2 (a := 852400000) (A := 852400002) (lo := 852398190) (W := 991810) (msmall_v534 h)
    ⟨426200000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v535

theorem msmall_v536 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 854380000 :=
  small_extend2 (a := 853390000) (A := 853390002) (lo := 853388190) (W := 991810) (msmall_v535 h)
    ⟨426695000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v536

theorem msmall_v537 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 855370000 :=
  small_extend2 (a := 854380000) (A := 854380002) (lo := 854378190) (W := 991810) (msmall_v536 h)
    ⟨427190000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v537

theorem msmall_v538 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 856360000 :=
  small_extend2 (a := 855370000) (A := 855370002) (lo := 855368190) (W := 991810) (msmall_v537 h)
    ⟨427685000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v538

theorem msmall_v539 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 857350000 :=
  small_extend2 (a := 856360000) (A := 856360002) (lo := 856358190) (W := 991810) (msmall_v538 h)
    ⟨428180000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v539

theorem msmall_v540 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 858340000 :=
  small_extend2 (a := 857350000) (A := 857350002) (lo := 857348190) (W := 991810) (msmall_v539 h)
    ⟨428675000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v540

theorem msmall_v541 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 859330000 :=
  small_extend2 (a := 858340000) (A := 858340002) (lo := 858338190) (W := 991810) (msmall_v540 h)
    ⟨429170000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v541

theorem msmall_v542 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 860320000 :=
  small_extend2 (a := 859330000) (A := 859330002) (lo := 859328190) (W := 991810) (msmall_v541 h)
    ⟨429665000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v542

theorem msmall_v543 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 861310000 :=
  small_extend2 (a := 860320000) (A := 860320002) (lo := 860318190) (W := 991810) (msmall_v542 h)
    ⟨430160000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v543

theorem msmall_v544 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 862300000 :=
  small_extend2 (a := 861310000) (A := 861310002) (lo := 861308190) (W := 991810) (msmall_v543 h)
    ⟨430655000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v544

theorem msmall_v545 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 863290000 :=
  small_extend2 (a := 862300000) (A := 862300002) (lo := 862298190) (W := 991810) (msmall_v544 h)
    ⟨431150000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v545

theorem msmall_v546 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 864280000 :=
  small_extend2 (a := 863290000) (A := 863290002) (lo := 863288190) (W := 991810) (msmall_v545 h)
    ⟨431645000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v546

theorem msmall_v547 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 865270000 :=
  small_extend2 (a := 864280000) (A := 864280002) (lo := 864278190) (W := 991810) (msmall_v546 h)
    ⟨432140000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v547

theorem msmall_v548 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 866260000 :=
  small_extend2 (a := 865270000) (A := 865270002) (lo := 865268190) (W := 991810) (msmall_v547 h)
    ⟨432635000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v548

theorem msmall_v549 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 867250000 :=
  small_extend2 (a := 866260000) (A := 866260002) (lo := 866258190) (W := 991810) (msmall_v548 h)
    ⟨433130000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v549

theorem msmall_v550 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 868240000 :=
  small_extend2 (a := 867250000) (A := 867250002) (lo := 867248190) (W := 991810) (msmall_v549 h)
    ⟨433625000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v550

theorem msmall_v551 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 869230000 :=
  small_extend2 (a := 868240000) (A := 868240002) (lo := 868238190) (W := 991810) (msmall_v550 h)
    ⟨434120000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v551

theorem msmall_v552 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 870220000 :=
  small_extend2 (a := 869230000) (A := 869230002) (lo := 869228190) (W := 991810) (msmall_v551 h)
    ⟨434615000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v552

theorem msmall_v553 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 871210000 :=
  small_extend2 (a := 870220000) (A := 870220002) (lo := 870218190) (W := 991810) (msmall_v552 h)
    ⟨435110000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v553

theorem msmall_v554 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 872200000 :=
  small_extend2 (a := 871210000) (A := 871210002) (lo := 871208190) (W := 991810) (msmall_v553 h)
    ⟨435605000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v554

theorem msmall_v555 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 873190000 :=
  small_extend2 (a := 872200000) (A := 872200002) (lo := 872198190) (W := 991810) (msmall_v554 h)
    ⟨436100000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v555

theorem msmall_v556 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 874180000 :=
  small_extend2 (a := 873190000) (A := 873190002) (lo := 873188190) (W := 991810) (msmall_v555 h)
    ⟨436595000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v556

theorem msmall_v557 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 875170000 :=
  small_extend2 (a := 874180000) (A := 874180002) (lo := 874178190) (W := 991810) (msmall_v556 h)
    ⟨437090000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v557

theorem msmall_v558 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 876160000 :=
  small_extend2 (a := 875170000) (A := 875170002) (lo := 875168190) (W := 991810) (msmall_v557 h)
    ⟨437585000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v558

theorem msmall_v559 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 877150000 :=
  small_extend2 (a := 876160000) (A := 876160002) (lo := 876158190) (W := 991810) (msmall_v558 h)
    ⟨438080000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v559

theorem msmall_v560 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 878140000 :=
  small_extend2 (a := 877150000) (A := 877150002) (lo := 877148190) (W := 991810) (msmall_v559 h)
    ⟨438575000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v560

theorem msmall_v561 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 879130000 :=
  small_extend2 (a := 878140000) (A := 878140002) (lo := 878138190) (W := 991810) (msmall_v560 h)
    ⟨439070000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v561

theorem msmall_v562 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 880120000 :=
  small_extend2 (a := 879130000) (A := 879130002) (lo := 879128190) (W := 991810) (msmall_v561 h)
    ⟨439565000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v562

theorem msmall_v563 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 881110000 :=
  small_extend2 (a := 880120000) (A := 880120002) (lo := 880118190) (W := 991810) (msmall_v562 h)
    ⟨440060000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v563

theorem msmall_v564 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 882100000 :=
  small_extend2 (a := 881110000) (A := 881110002) (lo := 881108190) (W := 991810) (msmall_v563 h)
    ⟨440555000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v564

theorem msmall_v565 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 883090000 :=
  small_extend2 (a := 882100000) (A := 882100002) (lo := 882098190) (W := 991810) (msmall_v564 h)
    ⟨441050000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v565

theorem msmall_v566 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 884080000 :=
  small_extend2 (a := 883090000) (A := 883090002) (lo := 883088190) (W := 991810) (msmall_v565 h)
    ⟨441545000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v566

theorem msmall_v567 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 885070000 :=
  small_extend2 (a := 884080000) (A := 884080002) (lo := 884078190) (W := 991810) (msmall_v566 h)
    ⟨442040000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v567

theorem msmall_v568 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 886060000 :=
  small_extend2 (a := 885070000) (A := 885070002) (lo := 885068190) (W := 991810) (msmall_v567 h)
    ⟨442535000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v568

theorem msmall_v569 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 887050000 :=
  small_extend2 (a := 886060000) (A := 886060002) (lo := 886058190) (W := 991810) (msmall_v568 h)
    ⟨443030000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v569

theorem msmall_v570 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 888040000 :=
  small_extend2 (a := 887050000) (A := 887050002) (lo := 887048190) (W := 991810) (msmall_v569 h)
    ⟨443525000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v570

theorem msmall_v571 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 889030000 :=
  small_extend2 (a := 888040000) (A := 888040002) (lo := 888038190) (W := 991810) (msmall_v570 h)
    ⟨444020000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v571

theorem msmall_v572 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 890020000 :=
  small_extend2 (a := 889030000) (A := 889030002) (lo := 889028190) (W := 991810) (msmall_v571 h)
    ⟨444515000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v572

theorem msmall_v573 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 891010000 :=
  small_extend2 (a := 890020000) (A := 890020002) (lo := 890018190) (W := 991810) (msmall_v572 h)
    ⟨445010000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v573

theorem msmall_v574 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 892000000 :=
  small_extend2 (a := 891010000) (A := 891010002) (lo := 891008190) (W := 991810) (msmall_v573 h)
    ⟨445505000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v574

theorem msmall_v575 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 892990000 :=
  small_extend2 (a := 892000000) (A := 892000002) (lo := 891998190) (W := 991810) (msmall_v574 h)
    ⟨446000000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v575

theorem msmall_v576 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 893980000 :=
  small_extend2 (a := 892990000) (A := 892990002) (lo := 892988190) (W := 991810) (msmall_v575 h)
    ⟨446495000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v576

theorem msmall_v577 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 894970000 :=
  small_extend2 (a := 893980000) (A := 893980002) (lo := 893978190) (W := 991810) (msmall_v576 h)
    ⟨446990000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v577

theorem msmall_v578 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 895960000 :=
  small_extend2 (a := 894970000) (A := 894970002) (lo := 894968190) (W := 991810) (msmall_v577 h)
    ⟨447485000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v578

theorem msmall_v579 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 896950000 :=
  small_extend2 (a := 895960000) (A := 895960002) (lo := 895958190) (W := 991810) (msmall_v578 h)
    ⟨447980000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v579

theorem msmall_v580 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 897940000 :=
  small_extend2 (a := 896950000) (A := 896950002) (lo := 896948190) (W := 991810) (msmall_v579 h)
    ⟨448475000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v580

theorem msmall_v581 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 898930000 :=
  small_extend2 (a := 897940000) (A := 897940002) (lo := 897938190) (W := 991810) (msmall_v580 h)
    ⟨448970000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v581

theorem msmall_v582 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 899920000 :=
  small_extend2 (a := 898930000) (A := 898930002) (lo := 898928190) (W := 991810) (msmall_v581 h)
    ⟨449465000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v582

theorem msmall_v583 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 900910000 :=
  small_extend2 (a := 899920000) (A := 899920002) (lo := 899918190) (W := 991810) (msmall_v582 h)
    ⟨449960000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v583

theorem msmall_v584 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 901900000 :=
  small_extend2 (a := 900910000) (A := 900910002) (lo := 900908190) (W := 991810) (msmall_v583 h)
    ⟨450455000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v584

theorem msmall_v585 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 902890000 :=
  small_extend2 (a := 901900000) (A := 901900002) (lo := 901898190) (W := 991810) (msmall_v584 h)
    ⟨450950000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v585

theorem msmall_v586 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 903880000 :=
  small_extend2 (a := 902890000) (A := 902890002) (lo := 902888190) (W := 991810) (msmall_v585 h)
    ⟨451445000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v586

theorem msmall_v587 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 904870000 :=
  small_extend2 (a := 903880000) (A := 903880002) (lo := 903878190) (W := 991810) (msmall_v586 h)
    ⟨451940000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v587

theorem msmall_v588 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 905860000 :=
  small_extend2 (a := 904870000) (A := 904870002) (lo := 904868190) (W := 991810) (msmall_v587 h)
    ⟨452435000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v588

theorem msmall_v589 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 906850000 :=
  small_extend2 (a := 905860000) (A := 905860002) (lo := 905858190) (W := 991810) (msmall_v588 h)
    ⟨452930000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v589

theorem msmall_v590 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 907840000 :=
  small_extend2 (a := 906850000) (A := 906850002) (lo := 906848190) (W := 991810) (msmall_v589 h)
    ⟨453425000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v590

theorem msmall_v591 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 908830000 :=
  small_extend2 (a := 907840000) (A := 907840002) (lo := 907838190) (W := 991810) (msmall_v590 h)
    ⟨453920000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v591

theorem msmall_v592 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 909820000 :=
  small_extend2 (a := 908830000) (A := 908830002) (lo := 908828190) (W := 991810) (msmall_v591 h)
    ⟨454415000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v592

theorem msmall_v593 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 910810000 :=
  small_extend2 (a := 909820000) (A := 909820002) (lo := 909818190) (W := 991810) (msmall_v592 h)
    ⟨454910000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v593

theorem msmall_v594 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 911800000 :=
  small_extend2 (a := 910810000) (A := 910810002) (lo := 910808190) (W := 991810) (msmall_v593 h)
    ⟨455405000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v594

theorem msmall_v595 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 912790000 :=
  small_extend2 (a := 911800000) (A := 911800002) (lo := 911798190) (W := 991810) (msmall_v594 h)
    ⟨455900000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v595

theorem msmall_v596 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 913780000 :=
  small_extend2 (a := 912790000) (A := 912790002) (lo := 912788190) (W := 991810) (msmall_v595 h)
    ⟨456395000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v596

theorem msmall_v597 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 914770000 :=
  small_extend2 (a := 913780000) (A := 913780002) (lo := 913778190) (W := 991810) (msmall_v596 h)
    ⟨456890000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v597

theorem msmall_v598 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 915760000 :=
  small_extend2 (a := 914770000) (A := 914770002) (lo := 914768190) (W := 991810) (msmall_v597 h)
    ⟨457385000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v598

theorem msmall_v599 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 916750000 :=
  small_extend2 (a := 915760000) (A := 915760002) (lo := 915758190) (W := 991810) (msmall_v598 h)
    ⟨457880000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v599

theorem msmall_v600 (h : SmallGBUpTo 1789 818740000) : SmallGBUpTo 1789 917740000 :=
  small_extend2 (a := 916750000) (A := 916750002) (lo := 916748190) (W := 991810) (msmall_v599 h)
    ⟨458375000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v600

end LeanLab.Verifications.Top50.Bits
