/-
Chain block MV5: windows MV401 to MV500, from SmallGBUpTo 1789 719740000 to SmallGBUpTo 1789 818740000.
Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.MinGBBase
import LeanLab.Verifications.Top50.BitMVG41
import LeanLab.Verifications.Top50.BitMVG42
import LeanLab.Verifications.Top50.BitMVG43
import LeanLab.Verifications.Top50.BitMVG44
import LeanLab.Verifications.Top50.BitMVG45
import LeanLab.Verifications.Top50.BitMVG46
import LeanLab.Verifications.Top50.BitMVG47
import LeanLab.Verifications.Top50.BitMVG48
import LeanLab.Verifications.Top50.BitMVG49
import LeanLab.Verifications.Top50.BitMVG50

namespace LeanLab.Verifications.Top50.Bits

theorem msmall_v401 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 720730000 :=
  small_extend2 (a := 719740000) (A := 719740002) (lo := 719738190) (W := 991810) h
    ⟨359870000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v401

theorem msmall_v402 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 721720000 :=
  small_extend2 (a := 720730000) (A := 720730002) (lo := 720728190) (W := 991810) (msmall_v401 h)
    ⟨360365000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v402

theorem msmall_v403 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 722710000 :=
  small_extend2 (a := 721720000) (A := 721720002) (lo := 721718190) (W := 991810) (msmall_v402 h)
    ⟨360860000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v403

theorem msmall_v404 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 723700000 :=
  small_extend2 (a := 722710000) (A := 722710002) (lo := 722708190) (W := 991810) (msmall_v403 h)
    ⟨361355000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v404

theorem msmall_v405 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 724690000 :=
  small_extend2 (a := 723700000) (A := 723700002) (lo := 723698190) (W := 991810) (msmall_v404 h)
    ⟨361850000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v405

theorem msmall_v406 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 725680000 :=
  small_extend2 (a := 724690000) (A := 724690002) (lo := 724688190) (W := 991810) (msmall_v405 h)
    ⟨362345000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v406

theorem msmall_v407 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 726670000 :=
  small_extend2 (a := 725680000) (A := 725680002) (lo := 725678190) (W := 991810) (msmall_v406 h)
    ⟨362840000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v407

theorem msmall_v408 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 727660000 :=
  small_extend2 (a := 726670000) (A := 726670002) (lo := 726668190) (W := 991810) (msmall_v407 h)
    ⟨363335000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v408

theorem msmall_v409 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 728650000 :=
  small_extend2 (a := 727660000) (A := 727660002) (lo := 727658190) (W := 991810) (msmall_v408 h)
    ⟨363830000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v409

theorem msmall_v410 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 729640000 :=
  small_extend2 (a := 728650000) (A := 728650002) (lo := 728648190) (W := 991810) (msmall_v409 h)
    ⟨364325000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v410

theorem msmall_v411 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 730630000 :=
  small_extend2 (a := 729640000) (A := 729640002) (lo := 729638190) (W := 991810) (msmall_v410 h)
    ⟨364820000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v411

theorem msmall_v412 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 731620000 :=
  small_extend2 (a := 730630000) (A := 730630002) (lo := 730628190) (W := 991810) (msmall_v411 h)
    ⟨365315000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v412

theorem msmall_v413 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 732610000 :=
  small_extend2 (a := 731620000) (A := 731620002) (lo := 731618190) (W := 991810) (msmall_v412 h)
    ⟨365810000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v413

theorem msmall_v414 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 733600000 :=
  small_extend2 (a := 732610000) (A := 732610002) (lo := 732608190) (W := 991810) (msmall_v413 h)
    ⟨366305000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v414

theorem msmall_v415 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 734590000 :=
  small_extend2 (a := 733600000) (A := 733600002) (lo := 733598190) (W := 991810) (msmall_v414 h)
    ⟨366800000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v415

theorem msmall_v416 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 735580000 :=
  small_extend2 (a := 734590000) (A := 734590002) (lo := 734588190) (W := 991810) (msmall_v415 h)
    ⟨367295000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v416

theorem msmall_v417 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 736570000 :=
  small_extend2 (a := 735580000) (A := 735580002) (lo := 735578190) (W := 991810) (msmall_v416 h)
    ⟨367790000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v417

theorem msmall_v418 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 737560000 :=
  small_extend2 (a := 736570000) (A := 736570002) (lo := 736568190) (W := 991810) (msmall_v417 h)
    ⟨368285000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v418

theorem msmall_v419 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 738550000 :=
  small_extend2 (a := 737560000) (A := 737560002) (lo := 737558190) (W := 991810) (msmall_v418 h)
    ⟨368780000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v419

theorem msmall_v420 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 739540000 :=
  small_extend2 (a := 738550000) (A := 738550002) (lo := 738548190) (W := 991810) (msmall_v419 h)
    ⟨369275000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v420

theorem msmall_v421 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 740530000 :=
  small_extend2 (a := 739540000) (A := 739540002) (lo := 739538190) (W := 991810) (msmall_v420 h)
    ⟨369770000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v421

theorem msmall_v422 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 741520000 :=
  small_extend2 (a := 740530000) (A := 740530002) (lo := 740528190) (W := 991810) (msmall_v421 h)
    ⟨370265000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v422

theorem msmall_v423 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 742510000 :=
  small_extend2 (a := 741520000) (A := 741520002) (lo := 741518190) (W := 991810) (msmall_v422 h)
    ⟨370760000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v423

theorem msmall_v424 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 743500000 :=
  small_extend2 (a := 742510000) (A := 742510002) (lo := 742508190) (W := 991810) (msmall_v423 h)
    ⟨371255000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v424

theorem msmall_v425 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 744490000 :=
  small_extend2 (a := 743500000) (A := 743500002) (lo := 743498190) (W := 991810) (msmall_v424 h)
    ⟨371750000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v425

theorem msmall_v426 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 745480000 :=
  small_extend2 (a := 744490000) (A := 744490002) (lo := 744488190) (W := 991810) (msmall_v425 h)
    ⟨372245000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v426

theorem msmall_v427 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 746470000 :=
  small_extend2 (a := 745480000) (A := 745480002) (lo := 745478190) (W := 991810) (msmall_v426 h)
    ⟨372740000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v427

theorem msmall_v428 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 747460000 :=
  small_extend2 (a := 746470000) (A := 746470002) (lo := 746468190) (W := 991810) (msmall_v427 h)
    ⟨373235000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v428

theorem msmall_v429 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 748450000 :=
  small_extend2 (a := 747460000) (A := 747460002) (lo := 747458190) (W := 991810) (msmall_v428 h)
    ⟨373730000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v429

theorem msmall_v430 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 749440000 :=
  small_extend2 (a := 748450000) (A := 748450002) (lo := 748448190) (W := 991810) (msmall_v429 h)
    ⟨374225000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v430

theorem msmall_v431 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 750430000 :=
  small_extend2 (a := 749440000) (A := 749440002) (lo := 749438190) (W := 991810) (msmall_v430 h)
    ⟨374720000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v431

theorem msmall_v432 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 751420000 :=
  small_extend2 (a := 750430000) (A := 750430002) (lo := 750428190) (W := 991810) (msmall_v431 h)
    ⟨375215000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v432

theorem msmall_v433 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 752410000 :=
  small_extend2 (a := 751420000) (A := 751420002) (lo := 751418190) (W := 991810) (msmall_v432 h)
    ⟨375710000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v433

theorem msmall_v434 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 753400000 :=
  small_extend2 (a := 752410000) (A := 752410002) (lo := 752408190) (W := 991810) (msmall_v433 h)
    ⟨376205000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v434

theorem msmall_v435 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 754390000 :=
  small_extend2 (a := 753400000) (A := 753400002) (lo := 753398190) (W := 991810) (msmall_v434 h)
    ⟨376700000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v435

theorem msmall_v436 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 755380000 :=
  small_extend2 (a := 754390000) (A := 754390002) (lo := 754388190) (W := 991810) (msmall_v435 h)
    ⟨377195000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v436

theorem msmall_v437 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 756370000 :=
  small_extend2 (a := 755380000) (A := 755380002) (lo := 755378190) (W := 991810) (msmall_v436 h)
    ⟨377690000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v437

theorem msmall_v438 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 757360000 :=
  small_extend2 (a := 756370000) (A := 756370002) (lo := 756368190) (W := 991810) (msmall_v437 h)
    ⟨378185000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v438

theorem msmall_v439 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 758350000 :=
  small_extend2 (a := 757360000) (A := 757360002) (lo := 757358190) (W := 991810) (msmall_v438 h)
    ⟨378680000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v439

theorem msmall_v440 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 759340000 :=
  small_extend2 (a := 758350000) (A := 758350002) (lo := 758348190) (W := 991810) (msmall_v439 h)
    ⟨379175000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v440

theorem msmall_v441 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 760330000 :=
  small_extend2 (a := 759340000) (A := 759340002) (lo := 759338190) (W := 991810) (msmall_v440 h)
    ⟨379670000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v441

theorem msmall_v442 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 761320000 :=
  small_extend2 (a := 760330000) (A := 760330002) (lo := 760328190) (W := 991810) (msmall_v441 h)
    ⟨380165000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v442

theorem msmall_v443 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 762310000 :=
  small_extend2 (a := 761320000) (A := 761320002) (lo := 761318190) (W := 991810) (msmall_v442 h)
    ⟨380660000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v443

theorem msmall_v444 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 763300000 :=
  small_extend2 (a := 762310000) (A := 762310002) (lo := 762308190) (W := 991810) (msmall_v443 h)
    ⟨381155000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v444

theorem msmall_v445 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 764290000 :=
  small_extend2 (a := 763300000) (A := 763300002) (lo := 763298190) (W := 991810) (msmall_v444 h)
    ⟨381650000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v445

theorem msmall_v446 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 765280000 :=
  small_extend2 (a := 764290000) (A := 764290002) (lo := 764288190) (W := 991810) (msmall_v445 h)
    ⟨382145000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v446

theorem msmall_v447 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 766270000 :=
  small_extend2 (a := 765280000) (A := 765280002) (lo := 765278190) (W := 991810) (msmall_v446 h)
    ⟨382640000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v447

theorem msmall_v448 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 767260000 :=
  small_extend2 (a := 766270000) (A := 766270002) (lo := 766268190) (W := 991810) (msmall_v447 h)
    ⟨383135000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v448

theorem msmall_v449 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 768250000 :=
  small_extend2 (a := 767260000) (A := 767260002) (lo := 767258190) (W := 991810) (msmall_v448 h)
    ⟨383630000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v449

theorem msmall_v450 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 769240000 :=
  small_extend2 (a := 768250000) (A := 768250002) (lo := 768248190) (W := 991810) (msmall_v449 h)
    ⟨384125000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v450

theorem msmall_v451 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 770230000 :=
  small_extend2 (a := 769240000) (A := 769240002) (lo := 769238190) (W := 991810) (msmall_v450 h)
    ⟨384620000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v451

theorem msmall_v452 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 771220000 :=
  small_extend2 (a := 770230000) (A := 770230002) (lo := 770228190) (W := 991810) (msmall_v451 h)
    ⟨385115000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v452

theorem msmall_v453 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 772210000 :=
  small_extend2 (a := 771220000) (A := 771220002) (lo := 771218190) (W := 991810) (msmall_v452 h)
    ⟨385610000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v453

theorem msmall_v454 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 773200000 :=
  small_extend2 (a := 772210000) (A := 772210002) (lo := 772208190) (W := 991810) (msmall_v453 h)
    ⟨386105000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v454

theorem msmall_v455 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 774190000 :=
  small_extend2 (a := 773200000) (A := 773200002) (lo := 773198190) (W := 991810) (msmall_v454 h)
    ⟨386600000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v455

theorem msmall_v456 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 775180000 :=
  small_extend2 (a := 774190000) (A := 774190002) (lo := 774188190) (W := 991810) (msmall_v455 h)
    ⟨387095000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v456

theorem msmall_v457 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 776170000 :=
  small_extend2 (a := 775180000) (A := 775180002) (lo := 775178190) (W := 991810) (msmall_v456 h)
    ⟨387590000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v457

theorem msmall_v458 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 777160000 :=
  small_extend2 (a := 776170000) (A := 776170002) (lo := 776168190) (W := 991810) (msmall_v457 h)
    ⟨388085000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v458

theorem msmall_v459 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 778150000 :=
  small_extend2 (a := 777160000) (A := 777160002) (lo := 777158190) (W := 991810) (msmall_v458 h)
    ⟨388580000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v459

theorem msmall_v460 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 779140000 :=
  small_extend2 (a := 778150000) (A := 778150002) (lo := 778148190) (W := 991810) (msmall_v459 h)
    ⟨389075000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v460

theorem msmall_v461 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 780130000 :=
  small_extend2 (a := 779140000) (A := 779140002) (lo := 779138190) (W := 991810) (msmall_v460 h)
    ⟨389570000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v461

theorem msmall_v462 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 781120000 :=
  small_extend2 (a := 780130000) (A := 780130002) (lo := 780128190) (W := 991810) (msmall_v461 h)
    ⟨390065000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v462

theorem msmall_v463 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 782110000 :=
  small_extend2 (a := 781120000) (A := 781120002) (lo := 781118190) (W := 991810) (msmall_v462 h)
    ⟨390560000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v463

theorem msmall_v464 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 783100000 :=
  small_extend2 (a := 782110000) (A := 782110002) (lo := 782108190) (W := 991810) (msmall_v463 h)
    ⟨391055000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v464

theorem msmall_v465 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 784090000 :=
  small_extend2 (a := 783100000) (A := 783100002) (lo := 783098190) (W := 991810) (msmall_v464 h)
    ⟨391550000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v465

theorem msmall_v466 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 785080000 :=
  small_extend2 (a := 784090000) (A := 784090002) (lo := 784088190) (W := 991810) (msmall_v465 h)
    ⟨392045000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v466

theorem msmall_v467 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 786070000 :=
  small_extend2 (a := 785080000) (A := 785080002) (lo := 785078190) (W := 991810) (msmall_v466 h)
    ⟨392540000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v467

theorem msmall_v468 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 787060000 :=
  small_extend2 (a := 786070000) (A := 786070002) (lo := 786068190) (W := 991810) (msmall_v467 h)
    ⟨393035000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v468

theorem msmall_v469 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 788050000 :=
  small_extend2 (a := 787060000) (A := 787060002) (lo := 787058190) (W := 991810) (msmall_v468 h)
    ⟨393530000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v469

theorem msmall_v470 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 789040000 :=
  small_extend2 (a := 788050000) (A := 788050002) (lo := 788048190) (W := 991810) (msmall_v469 h)
    ⟨394025000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v470

theorem msmall_v471 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 790030000 :=
  small_extend2 (a := 789040000) (A := 789040002) (lo := 789038190) (W := 991810) (msmall_v470 h)
    ⟨394520000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v471

theorem msmall_v472 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 791020000 :=
  small_extend2 (a := 790030000) (A := 790030002) (lo := 790028190) (W := 991810) (msmall_v471 h)
    ⟨395015000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v472

theorem msmall_v473 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 792010000 :=
  small_extend2 (a := 791020000) (A := 791020002) (lo := 791018190) (W := 991810) (msmall_v472 h)
    ⟨395510000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v473

theorem msmall_v474 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 793000000 :=
  small_extend2 (a := 792010000) (A := 792010002) (lo := 792008190) (W := 991810) (msmall_v473 h)
    ⟨396005000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v474

theorem msmall_v475 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 793990000 :=
  small_extend2 (a := 793000000) (A := 793000002) (lo := 792998190) (W := 991810) (msmall_v474 h)
    ⟨396500000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v475

theorem msmall_v476 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 794980000 :=
  small_extend2 (a := 793990000) (A := 793990002) (lo := 793988190) (W := 991810) (msmall_v475 h)
    ⟨396995000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v476

theorem msmall_v477 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 795970000 :=
  small_extend2 (a := 794980000) (A := 794980002) (lo := 794978190) (W := 991810) (msmall_v476 h)
    ⟨397490000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v477

theorem msmall_v478 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 796960000 :=
  small_extend2 (a := 795970000) (A := 795970002) (lo := 795968190) (W := 991810) (msmall_v477 h)
    ⟨397985000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v478

theorem msmall_v479 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 797950000 :=
  small_extend2 (a := 796960000) (A := 796960002) (lo := 796958190) (W := 991810) (msmall_v478 h)
    ⟨398480000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v479

theorem msmall_v480 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 798940000 :=
  small_extend2 (a := 797950000) (A := 797950002) (lo := 797948190) (W := 991810) (msmall_v479 h)
    ⟨398975000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v480

theorem msmall_v481 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 799930000 :=
  small_extend2 (a := 798940000) (A := 798940002) (lo := 798938190) (W := 991810) (msmall_v480 h)
    ⟨399470000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v481

theorem msmall_v482 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 800920000 :=
  small_extend2 (a := 799930000) (A := 799930002) (lo := 799928190) (W := 991810) (msmall_v481 h)
    ⟨399965000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v482

theorem msmall_v483 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 801910000 :=
  small_extend2 (a := 800920000) (A := 800920002) (lo := 800918190) (W := 991810) (msmall_v482 h)
    ⟨400460000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v483

theorem msmall_v484 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 802900000 :=
  small_extend2 (a := 801910000) (A := 801910002) (lo := 801908190) (W := 991810) (msmall_v483 h)
    ⟨400955000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v484

theorem msmall_v485 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 803890000 :=
  small_extend2 (a := 802900000) (A := 802900002) (lo := 802898190) (W := 991810) (msmall_v484 h)
    ⟨401450000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v485

theorem msmall_v486 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 804880000 :=
  small_extend2 (a := 803890000) (A := 803890002) (lo := 803888190) (W := 991810) (msmall_v485 h)
    ⟨401945000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v486

theorem msmall_v487 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 805870000 :=
  small_extend2 (a := 804880000) (A := 804880002) (lo := 804878190) (W := 991810) (msmall_v486 h)
    ⟨402440000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v487

theorem msmall_v488 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 806860000 :=
  small_extend2 (a := 805870000) (A := 805870002) (lo := 805868190) (W := 991810) (msmall_v487 h)
    ⟨402935000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v488

theorem msmall_v489 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 807850000 :=
  small_extend2 (a := 806860000) (A := 806860002) (lo := 806858190) (W := 991810) (msmall_v488 h)
    ⟨403430000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v489

theorem msmall_v490 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 808840000 :=
  small_extend2 (a := 807850000) (A := 807850002) (lo := 807848190) (W := 991810) (msmall_v489 h)
    ⟨403925000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v490

theorem msmall_v491 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 809830000 :=
  small_extend2 (a := 808840000) (A := 808840002) (lo := 808838190) (W := 991810) (msmall_v490 h)
    ⟨404420000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v491

theorem msmall_v492 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 810820000 :=
  small_extend2 (a := 809830000) (A := 809830002) (lo := 809828190) (W := 991810) (msmall_v491 h)
    ⟨404915000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v492

theorem msmall_v493 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 811810000 :=
  small_extend2 (a := 810820000) (A := 810820002) (lo := 810818190) (W := 991810) (msmall_v492 h)
    ⟨405410000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v493

theorem msmall_v494 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 812800000 :=
  small_extend2 (a := 811810000) (A := 811810002) (lo := 811808190) (W := 991810) (msmall_v493 h)
    ⟨405905000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v494

theorem msmall_v495 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 813790000 :=
  small_extend2 (a := 812800000) (A := 812800002) (lo := 812798190) (W := 991810) (msmall_v494 h)
    ⟨406400000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v495

theorem msmall_v496 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 814780000 :=
  small_extend2 (a := 813790000) (A := 813790002) (lo := 813788190) (W := 991810) (msmall_v495 h)
    ⟨406895000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v496

theorem msmall_v497 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 815770000 :=
  small_extend2 (a := 814780000) (A := 814780002) (lo := 814778190) (W := 991810) (msmall_v496 h)
    ⟨407390000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v497

theorem msmall_v498 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 816760000 :=
  small_extend2 (a := 815770000) (A := 815770002) (lo := 815768190) (W := 991810) (msmall_v497 h)
    ⟨407885000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v498

theorem msmall_v499 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 817750000 :=
  small_extend2 (a := 816760000) (A := 816760002) (lo := 816758190) (W := 991810) (msmall_v498 h)
    ⟨408380000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v499

theorem msmall_v500 (h : SmallGBUpTo 1789 719740000) : SmallGBUpTo 1789 818740000 :=
  small_extend2 (a := 817750000) (A := 817750002) (lo := 817748190) (W := 991810) (msmall_v499 h)
    ⟨408875000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v500

end LeanLab.Verifications.Top50.Bits
