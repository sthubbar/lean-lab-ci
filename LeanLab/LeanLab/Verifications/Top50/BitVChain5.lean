/-
Chain block V5 of the kernel Goldbach windows past 323740000: windows V401 to V500, from
SmallGBUpTo 1811 719740000 to SmallGBUpTo 1811 818740000, so the blocks compose. Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.SmallGB
import LeanLab.Verifications.Top50.BitVG41
import LeanLab.Verifications.Top50.BitVG42
import LeanLab.Verifications.Top50.BitVG43
import LeanLab.Verifications.Top50.BitVG44
import LeanLab.Verifications.Top50.BitVG45
import LeanLab.Verifications.Top50.BitVG46
import LeanLab.Verifications.Top50.BitVG47
import LeanLab.Verifications.Top50.BitVG48
import LeanLab.Verifications.Top50.BitVG49
import LeanLab.Verifications.Top50.BitVG50

namespace LeanLab.Verifications.Top50.Bits

theorem small_v401 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 720730000 :=
  small_extend2 (a := 719740000) (A := 719740002) (lo := 719738190) (W := 991810) h
    ⟨359870000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v401

theorem small_v402 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 721720000 :=
  small_extend2 (a := 720730000) (A := 720730002) (lo := 720728190) (W := 991810) (small_v401 h)
    ⟨360365000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v402

theorem small_v403 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 722710000 :=
  small_extend2 (a := 721720000) (A := 721720002) (lo := 721718190) (W := 991810) (small_v402 h)
    ⟨360860000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v403

theorem small_v404 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 723700000 :=
  small_extend2 (a := 722710000) (A := 722710002) (lo := 722708190) (W := 991810) (small_v403 h)
    ⟨361355000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v404

theorem small_v405 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 724690000 :=
  small_extend2 (a := 723700000) (A := 723700002) (lo := 723698190) (W := 991810) (small_v404 h)
    ⟨361850000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v405

theorem small_v406 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 725680000 :=
  small_extend2 (a := 724690000) (A := 724690002) (lo := 724688190) (W := 991810) (small_v405 h)
    ⟨362345000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v406

theorem small_v407 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 726670000 :=
  small_extend2 (a := 725680000) (A := 725680002) (lo := 725678190) (W := 991810) (small_v406 h)
    ⟨362840000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v407

theorem small_v408 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 727660000 :=
  small_extend2 (a := 726670000) (A := 726670002) (lo := 726668190) (W := 991810) (small_v407 h)
    ⟨363335000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v408

theorem small_v409 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 728650000 :=
  small_extend2 (a := 727660000) (A := 727660002) (lo := 727658190) (W := 991810) (small_v408 h)
    ⟨363830000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v409

theorem small_v410 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 729640000 :=
  small_extend2 (a := 728650000) (A := 728650002) (lo := 728648190) (W := 991810) (small_v409 h)
    ⟨364325000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v410

theorem small_v411 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 730630000 :=
  small_extend2 (a := 729640000) (A := 729640002) (lo := 729638190) (W := 991810) (small_v410 h)
    ⟨364820000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v411

theorem small_v412 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 731620000 :=
  small_extend2 (a := 730630000) (A := 730630002) (lo := 730628190) (W := 991810) (small_v411 h)
    ⟨365315000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v412

theorem small_v413 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 732610000 :=
  small_extend2 (a := 731620000) (A := 731620002) (lo := 731618190) (W := 991810) (small_v412 h)
    ⟨365810000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v413

theorem small_v414 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 733600000 :=
  small_extend2 (a := 732610000) (A := 732610002) (lo := 732608190) (W := 991810) (small_v413 h)
    ⟨366305000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v414

theorem small_v415 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 734590000 :=
  small_extend2 (a := 733600000) (A := 733600002) (lo := 733598190) (W := 991810) (small_v414 h)
    ⟨366800000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v415

theorem small_v416 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 735580000 :=
  small_extend2 (a := 734590000) (A := 734590002) (lo := 734588190) (W := 991810) (small_v415 h)
    ⟨367295000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v416

theorem small_v417 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 736570000 :=
  small_extend2 (a := 735580000) (A := 735580002) (lo := 735578190) (W := 991810) (small_v416 h)
    ⟨367790000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v417

theorem small_v418 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 737560000 :=
  small_extend2 (a := 736570000) (A := 736570002) (lo := 736568190) (W := 991810) (small_v417 h)
    ⟨368285000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v418

theorem small_v419 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 738550000 :=
  small_extend2 (a := 737560000) (A := 737560002) (lo := 737558190) (W := 991810) (small_v418 h)
    ⟨368780000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v419

theorem small_v420 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 739540000 :=
  small_extend2 (a := 738550000) (A := 738550002) (lo := 738548190) (W := 991810) (small_v419 h)
    ⟨369275000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v420

theorem small_v421 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 740530000 :=
  small_extend2 (a := 739540000) (A := 739540002) (lo := 739538190) (W := 991810) (small_v420 h)
    ⟨369770000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v421

theorem small_v422 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 741520000 :=
  small_extend2 (a := 740530000) (A := 740530002) (lo := 740528190) (W := 991810) (small_v421 h)
    ⟨370265000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v422

theorem small_v423 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 742510000 :=
  small_extend2 (a := 741520000) (A := 741520002) (lo := 741518190) (W := 991810) (small_v422 h)
    ⟨370760000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v423

theorem small_v424 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 743500000 :=
  small_extend2 (a := 742510000) (A := 742510002) (lo := 742508190) (W := 991810) (small_v423 h)
    ⟨371255000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v424

theorem small_v425 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 744490000 :=
  small_extend2 (a := 743500000) (A := 743500002) (lo := 743498190) (W := 991810) (small_v424 h)
    ⟨371750000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v425

theorem small_v426 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 745480000 :=
  small_extend2 (a := 744490000) (A := 744490002) (lo := 744488190) (W := 991810) (small_v425 h)
    ⟨372245000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v426

theorem small_v427 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 746470000 :=
  small_extend2 (a := 745480000) (A := 745480002) (lo := 745478190) (W := 991810) (small_v426 h)
    ⟨372740000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v427

theorem small_v428 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 747460000 :=
  small_extend2 (a := 746470000) (A := 746470002) (lo := 746468190) (W := 991810) (small_v427 h)
    ⟨373235000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v428

theorem small_v429 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 748450000 :=
  small_extend2 (a := 747460000) (A := 747460002) (lo := 747458190) (W := 991810) (small_v428 h)
    ⟨373730000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v429

theorem small_v430 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 749440000 :=
  small_extend2 (a := 748450000) (A := 748450002) (lo := 748448190) (W := 991810) (small_v429 h)
    ⟨374225000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v430

theorem small_v431 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 750430000 :=
  small_extend2 (a := 749440000) (A := 749440002) (lo := 749438190) (W := 991810) (small_v430 h)
    ⟨374720000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v431

theorem small_v432 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 751420000 :=
  small_extend2 (a := 750430000) (A := 750430002) (lo := 750428190) (W := 991810) (small_v431 h)
    ⟨375215000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v432

theorem small_v433 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 752410000 :=
  small_extend2 (a := 751420000) (A := 751420002) (lo := 751418190) (W := 991810) (small_v432 h)
    ⟨375710000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v433

theorem small_v434 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 753400000 :=
  small_extend2 (a := 752410000) (A := 752410002) (lo := 752408190) (W := 991810) (small_v433 h)
    ⟨376205000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v434

theorem small_v435 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 754390000 :=
  small_extend2 (a := 753400000) (A := 753400002) (lo := 753398190) (W := 991810) (small_v434 h)
    ⟨376700000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v435

theorem small_v436 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 755380000 :=
  small_extend2 (a := 754390000) (A := 754390002) (lo := 754388190) (W := 991810) (small_v435 h)
    ⟨377195000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v436

theorem small_v437 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 756370000 :=
  small_extend2 (a := 755380000) (A := 755380002) (lo := 755378190) (W := 991810) (small_v436 h)
    ⟨377690000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v437

theorem small_v438 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 757360000 :=
  small_extend2 (a := 756370000) (A := 756370002) (lo := 756368190) (W := 991810) (small_v437 h)
    ⟨378185000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v438

theorem small_v439 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 758350000 :=
  small_extend2 (a := 757360000) (A := 757360002) (lo := 757358190) (W := 991810) (small_v438 h)
    ⟨378680000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v439

theorem small_v440 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 759340000 :=
  small_extend2 (a := 758350000) (A := 758350002) (lo := 758348190) (W := 991810) (small_v439 h)
    ⟨379175000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v440

theorem small_v441 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 760330000 :=
  small_extend2 (a := 759340000) (A := 759340002) (lo := 759338190) (W := 991810) (small_v440 h)
    ⟨379670000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v441

theorem small_v442 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 761320000 :=
  small_extend2 (a := 760330000) (A := 760330002) (lo := 760328190) (W := 991810) (small_v441 h)
    ⟨380165000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v442

theorem small_v443 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 762310000 :=
  small_extend2 (a := 761320000) (A := 761320002) (lo := 761318190) (W := 991810) (small_v442 h)
    ⟨380660000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v443

theorem small_v444 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 763300000 :=
  small_extend2 (a := 762310000) (A := 762310002) (lo := 762308190) (W := 991810) (small_v443 h)
    ⟨381155000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v444

theorem small_v445 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 764290000 :=
  small_extend2 (a := 763300000) (A := 763300002) (lo := 763298190) (W := 991810) (small_v444 h)
    ⟨381650000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v445

theorem small_v446 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 765280000 :=
  small_extend2 (a := 764290000) (A := 764290002) (lo := 764288190) (W := 991810) (small_v445 h)
    ⟨382145000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v446

theorem small_v447 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 766270000 :=
  small_extend2 (a := 765280000) (A := 765280002) (lo := 765278190) (W := 991810) (small_v446 h)
    ⟨382640000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v447

theorem small_v448 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 767260000 :=
  small_extend2 (a := 766270000) (A := 766270002) (lo := 766268190) (W := 991810) (small_v447 h)
    ⟨383135000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v448

theorem small_v449 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 768250000 :=
  small_extend2 (a := 767260000) (A := 767260002) (lo := 767258190) (W := 991810) (small_v448 h)
    ⟨383630000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v449

theorem small_v450 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 769240000 :=
  small_extend2 (a := 768250000) (A := 768250002) (lo := 768248190) (W := 991810) (small_v449 h)
    ⟨384125000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v450

theorem small_v451 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 770230000 :=
  small_extend2 (a := 769240000) (A := 769240002) (lo := 769238190) (W := 991810) (small_v450 h)
    ⟨384620000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v451

theorem small_v452 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 771220000 :=
  small_extend2 (a := 770230000) (A := 770230002) (lo := 770228190) (W := 991810) (small_v451 h)
    ⟨385115000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v452

theorem small_v453 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 772210000 :=
  small_extend2 (a := 771220000) (A := 771220002) (lo := 771218190) (W := 991810) (small_v452 h)
    ⟨385610000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v453

theorem small_v454 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 773200000 :=
  small_extend2 (a := 772210000) (A := 772210002) (lo := 772208190) (W := 991810) (small_v453 h)
    ⟨386105000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v454

theorem small_v455 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 774190000 :=
  small_extend2 (a := 773200000) (A := 773200002) (lo := 773198190) (W := 991810) (small_v454 h)
    ⟨386600000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v455

theorem small_v456 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 775180000 :=
  small_extend2 (a := 774190000) (A := 774190002) (lo := 774188190) (W := 991810) (small_v455 h)
    ⟨387095000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v456

theorem small_v457 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 776170000 :=
  small_extend2 (a := 775180000) (A := 775180002) (lo := 775178190) (W := 991810) (small_v456 h)
    ⟨387590000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v457

theorem small_v458 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 777160000 :=
  small_extend2 (a := 776170000) (A := 776170002) (lo := 776168190) (W := 991810) (small_v457 h)
    ⟨388085000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v458

theorem small_v459 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 778150000 :=
  small_extend2 (a := 777160000) (A := 777160002) (lo := 777158190) (W := 991810) (small_v458 h)
    ⟨388580000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v459

theorem small_v460 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 779140000 :=
  small_extend2 (a := 778150000) (A := 778150002) (lo := 778148190) (W := 991810) (small_v459 h)
    ⟨389075000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v460

theorem small_v461 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 780130000 :=
  small_extend2 (a := 779140000) (A := 779140002) (lo := 779138190) (W := 991810) (small_v460 h)
    ⟨389570000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v461

theorem small_v462 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 781120000 :=
  small_extend2 (a := 780130000) (A := 780130002) (lo := 780128190) (W := 991810) (small_v461 h)
    ⟨390065000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v462

theorem small_v463 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 782110000 :=
  small_extend2 (a := 781120000) (A := 781120002) (lo := 781118190) (W := 991810) (small_v462 h)
    ⟨390560000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v463

theorem small_v464 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 783100000 :=
  small_extend2 (a := 782110000) (A := 782110002) (lo := 782108190) (W := 991810) (small_v463 h)
    ⟨391055000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v464

theorem small_v465 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 784090000 :=
  small_extend2 (a := 783100000) (A := 783100002) (lo := 783098190) (W := 991810) (small_v464 h)
    ⟨391550000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v465

theorem small_v466 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 785080000 :=
  small_extend2 (a := 784090000) (A := 784090002) (lo := 784088190) (W := 991810) (small_v465 h)
    ⟨392045000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v466

theorem small_v467 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 786070000 :=
  small_extend2 (a := 785080000) (A := 785080002) (lo := 785078190) (W := 991810) (small_v466 h)
    ⟨392540000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v467

theorem small_v468 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 787060000 :=
  small_extend2 (a := 786070000) (A := 786070002) (lo := 786068190) (W := 991810) (small_v467 h)
    ⟨393035000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v468

theorem small_v469 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 788050000 :=
  small_extend2 (a := 787060000) (A := 787060002) (lo := 787058190) (W := 991810) (small_v468 h)
    ⟨393530000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v469

theorem small_v470 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 789040000 :=
  small_extend2 (a := 788050000) (A := 788050002) (lo := 788048190) (W := 991810) (small_v469 h)
    ⟨394025000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v470

theorem small_v471 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 790030000 :=
  small_extend2 (a := 789040000) (A := 789040002) (lo := 789038190) (W := 991810) (small_v470 h)
    ⟨394520000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v471

theorem small_v472 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 791020000 :=
  small_extend2 (a := 790030000) (A := 790030002) (lo := 790028190) (W := 991810) (small_v471 h)
    ⟨395015000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v472

theorem small_v473 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 792010000 :=
  small_extend2 (a := 791020000) (A := 791020002) (lo := 791018190) (W := 991810) (small_v472 h)
    ⟨395510000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v473

theorem small_v474 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 793000000 :=
  small_extend2 (a := 792010000) (A := 792010002) (lo := 792008190) (W := 991810) (small_v473 h)
    ⟨396005000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v474

theorem small_v475 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 793990000 :=
  small_extend2 (a := 793000000) (A := 793000002) (lo := 792998190) (W := 991810) (small_v474 h)
    ⟨396500000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v475

theorem small_v476 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 794980000 :=
  small_extend2 (a := 793990000) (A := 793990002) (lo := 793988190) (W := 991810) (small_v475 h)
    ⟨396995000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v476

theorem small_v477 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 795970000 :=
  small_extend2 (a := 794980000) (A := 794980002) (lo := 794978190) (W := 991810) (small_v476 h)
    ⟨397490000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v477

theorem small_v478 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 796960000 :=
  small_extend2 (a := 795970000) (A := 795970002) (lo := 795968190) (W := 991810) (small_v477 h)
    ⟨397985000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v478

theorem small_v479 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 797950000 :=
  small_extend2 (a := 796960000) (A := 796960002) (lo := 796958190) (W := 991810) (small_v478 h)
    ⟨398480000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v479

theorem small_v480 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 798940000 :=
  small_extend2 (a := 797950000) (A := 797950002) (lo := 797948190) (W := 991810) (small_v479 h)
    ⟨398975000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v480

theorem small_v481 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 799930000 :=
  small_extend2 (a := 798940000) (A := 798940002) (lo := 798938190) (W := 991810) (small_v480 h)
    ⟨399470000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v481

theorem small_v482 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 800920000 :=
  small_extend2 (a := 799930000) (A := 799930002) (lo := 799928190) (W := 991810) (small_v481 h)
    ⟨399965000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v482

theorem small_v483 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 801910000 :=
  small_extend2 (a := 800920000) (A := 800920002) (lo := 800918190) (W := 991810) (small_v482 h)
    ⟨400460000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v483

theorem small_v484 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 802900000 :=
  small_extend2 (a := 801910000) (A := 801910002) (lo := 801908190) (W := 991810) (small_v483 h)
    ⟨400955000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v484

theorem small_v485 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 803890000 :=
  small_extend2 (a := 802900000) (A := 802900002) (lo := 802898190) (W := 991810) (small_v484 h)
    ⟨401450000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v485

theorem small_v486 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 804880000 :=
  small_extend2 (a := 803890000) (A := 803890002) (lo := 803888190) (W := 991810) (small_v485 h)
    ⟨401945000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v486

theorem small_v487 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 805870000 :=
  small_extend2 (a := 804880000) (A := 804880002) (lo := 804878190) (W := 991810) (small_v486 h)
    ⟨402440000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v487

theorem small_v488 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 806860000 :=
  small_extend2 (a := 805870000) (A := 805870002) (lo := 805868190) (W := 991810) (small_v487 h)
    ⟨402935000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v488

theorem small_v489 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 807850000 :=
  small_extend2 (a := 806860000) (A := 806860002) (lo := 806858190) (W := 991810) (small_v488 h)
    ⟨403430000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v489

theorem small_v490 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 808840000 :=
  small_extend2 (a := 807850000) (A := 807850002) (lo := 807848190) (W := 991810) (small_v489 h)
    ⟨403925000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v490

theorem small_v491 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 809830000 :=
  small_extend2 (a := 808840000) (A := 808840002) (lo := 808838190) (W := 991810) (small_v490 h)
    ⟨404420000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v491

theorem small_v492 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 810820000 :=
  small_extend2 (a := 809830000) (A := 809830002) (lo := 809828190) (W := 991810) (small_v491 h)
    ⟨404915000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v492

theorem small_v493 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 811810000 :=
  small_extend2 (a := 810820000) (A := 810820002) (lo := 810818190) (W := 991810) (small_v492 h)
    ⟨405410000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v493

theorem small_v494 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 812800000 :=
  small_extend2 (a := 811810000) (A := 811810002) (lo := 811808190) (W := 991810) (small_v493 h)
    ⟨405905000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v494

theorem small_v495 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 813790000 :=
  small_extend2 (a := 812800000) (A := 812800002) (lo := 812798190) (W := 991810) (small_v494 h)
    ⟨406400000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v495

theorem small_v496 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 814780000 :=
  small_extend2 (a := 813790000) (A := 813790002) (lo := 813788190) (W := 991810) (small_v495 h)
    ⟨406895000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v496

theorem small_v497 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 815770000 :=
  small_extend2 (a := 814780000) (A := 814780002) (lo := 814778190) (W := 991810) (small_v496 h)
    ⟨407390000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v497

theorem small_v498 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 816760000 :=
  small_extend2 (a := 815770000) (A := 815770002) (lo := 815768190) (W := 991810) (small_v497 h)
    ⟨407885000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v498

theorem small_v499 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 817750000 :=
  small_extend2 (a := 816760000) (A := 816760002) (lo := 816758190) (W := 991810) (small_v498 h)
    ⟨408380000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v499

theorem small_v500 (h : SmallGBUpTo 1811 719740000) : SmallGBUpTo 1811 818740000 :=
  small_extend2 (a := 817750000) (A := 817750002) (lo := 817748190) (W := 991810) (small_v499 h)
    ⟨408875000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v500

end LeanLab.Verifications.Top50.Bits
