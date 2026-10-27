/-
Chain block V4 of the kernel Goldbach windows past 323740000: windows V301 to V400, from
SmallGBUpTo 1811 620740000 to SmallGBUpTo 1811 719740000, so the blocks compose. Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.SmallGB
import LeanLab.Verifications.Top50.BitVG31
import LeanLab.Verifications.Top50.BitVG32
import LeanLab.Verifications.Top50.BitVG33
import LeanLab.Verifications.Top50.BitVG34
import LeanLab.Verifications.Top50.BitVG35
import LeanLab.Verifications.Top50.BitVG36
import LeanLab.Verifications.Top50.BitVG37
import LeanLab.Verifications.Top50.BitVG38
import LeanLab.Verifications.Top50.BitVG39
import LeanLab.Verifications.Top50.BitVG40

namespace LeanLab.Verifications.Top50.Bits

theorem small_v301 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 621730000 :=
  small_extend2 (a := 620740000) (A := 620740002) (lo := 620738190) (W := 991810) h
    ⟨310370000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v301

theorem small_v302 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 622720000 :=
  small_extend2 (a := 621730000) (A := 621730002) (lo := 621728190) (W := 991810) (small_v301 h)
    ⟨310865000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v302

theorem small_v303 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 623710000 :=
  small_extend2 (a := 622720000) (A := 622720002) (lo := 622718190) (W := 991810) (small_v302 h)
    ⟨311360000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v303

theorem small_v304 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 624700000 :=
  small_extend2 (a := 623710000) (A := 623710002) (lo := 623708190) (W := 991810) (small_v303 h)
    ⟨311855000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v304

theorem small_v305 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 625690000 :=
  small_extend2 (a := 624700000) (A := 624700002) (lo := 624698190) (W := 991810) (small_v304 h)
    ⟨312350000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v305

theorem small_v306 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 626680000 :=
  small_extend2 (a := 625690000) (A := 625690002) (lo := 625688190) (W := 991810) (small_v305 h)
    ⟨312845000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v306

theorem small_v307 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 627670000 :=
  small_extend2 (a := 626680000) (A := 626680002) (lo := 626678190) (W := 991810) (small_v306 h)
    ⟨313340000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v307

theorem small_v308 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 628660000 :=
  small_extend2 (a := 627670000) (A := 627670002) (lo := 627668190) (W := 991810) (small_v307 h)
    ⟨313835000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v308

theorem small_v309 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 629650000 :=
  small_extend2 (a := 628660000) (A := 628660002) (lo := 628658190) (W := 991810) (small_v308 h)
    ⟨314330000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v309

theorem small_v310 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 630640000 :=
  small_extend2 (a := 629650000) (A := 629650002) (lo := 629648190) (W := 991810) (small_v309 h)
    ⟨314825000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v310

theorem small_v311 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 631630000 :=
  small_extend2 (a := 630640000) (A := 630640002) (lo := 630638190) (W := 991810) (small_v310 h)
    ⟨315320000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v311

theorem small_v312 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 632620000 :=
  small_extend2 (a := 631630000) (A := 631630002) (lo := 631628190) (W := 991810) (small_v311 h)
    ⟨315815000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v312

theorem small_v313 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 633610000 :=
  small_extend2 (a := 632620000) (A := 632620002) (lo := 632618190) (W := 991810) (small_v312 h)
    ⟨316310000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v313

theorem small_v314 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 634600000 :=
  small_extend2 (a := 633610000) (A := 633610002) (lo := 633608190) (W := 991810) (small_v313 h)
    ⟨316805000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v314

theorem small_v315 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 635590000 :=
  small_extend2 (a := 634600000) (A := 634600002) (lo := 634598190) (W := 991810) (small_v314 h)
    ⟨317300000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v315

theorem small_v316 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 636580000 :=
  small_extend2 (a := 635590000) (A := 635590002) (lo := 635588190) (W := 991810) (small_v315 h)
    ⟨317795000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v316

theorem small_v317 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 637570000 :=
  small_extend2 (a := 636580000) (A := 636580002) (lo := 636578190) (W := 991810) (small_v316 h)
    ⟨318290000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v317

theorem small_v318 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 638560000 :=
  small_extend2 (a := 637570000) (A := 637570002) (lo := 637568190) (W := 991810) (small_v317 h)
    ⟨318785000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v318

theorem small_v319 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 639550000 :=
  small_extend2 (a := 638560000) (A := 638560002) (lo := 638558190) (W := 991810) (small_v318 h)
    ⟨319280000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v319

theorem small_v320 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 640540000 :=
  small_extend2 (a := 639550000) (A := 639550002) (lo := 639548190) (W := 991810) (small_v319 h)
    ⟨319775000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v320

theorem small_v321 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 641530000 :=
  small_extend2 (a := 640540000) (A := 640540002) (lo := 640538190) (W := 991810) (small_v320 h)
    ⟨320270000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v321

theorem small_v322 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 642520000 :=
  small_extend2 (a := 641530000) (A := 641530002) (lo := 641528190) (W := 991810) (small_v321 h)
    ⟨320765000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v322

theorem small_v323 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 643510000 :=
  small_extend2 (a := 642520000) (A := 642520002) (lo := 642518190) (W := 991810) (small_v322 h)
    ⟨321260000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v323

theorem small_v324 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 644500000 :=
  small_extend2 (a := 643510000) (A := 643510002) (lo := 643508190) (W := 991810) (small_v323 h)
    ⟨321755000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v324

theorem small_v325 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 645490000 :=
  small_extend2 (a := 644500000) (A := 644500002) (lo := 644498190) (W := 991810) (small_v324 h)
    ⟨322250000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v325

theorem small_v326 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 646480000 :=
  small_extend2 (a := 645490000) (A := 645490002) (lo := 645488190) (W := 991810) (small_v325 h)
    ⟨322745000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v326

theorem small_v327 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 647470000 :=
  small_extend2 (a := 646480000) (A := 646480002) (lo := 646478190) (W := 991810) (small_v326 h)
    ⟨323240000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v327

theorem small_v328 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 648460000 :=
  small_extend2 (a := 647470000) (A := 647470002) (lo := 647468190) (W := 991810) (small_v327 h)
    ⟨323735000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v328

theorem small_v329 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 649450000 :=
  small_extend2 (a := 648460000) (A := 648460002) (lo := 648458190) (W := 991810) (small_v328 h)
    ⟨324230000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v329

theorem small_v330 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 650440000 :=
  small_extend2 (a := 649450000) (A := 649450002) (lo := 649448190) (W := 991810) (small_v329 h)
    ⟨324725000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v330

theorem small_v331 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 651430000 :=
  small_extend2 (a := 650440000) (A := 650440002) (lo := 650438190) (W := 991810) (small_v330 h)
    ⟨325220000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v331

theorem small_v332 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 652420000 :=
  small_extend2 (a := 651430000) (A := 651430002) (lo := 651428190) (W := 991810) (small_v331 h)
    ⟨325715000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v332

theorem small_v333 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 653410000 :=
  small_extend2 (a := 652420000) (A := 652420002) (lo := 652418190) (W := 991810) (small_v332 h)
    ⟨326210000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v333

theorem small_v334 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 654400000 :=
  small_extend2 (a := 653410000) (A := 653410002) (lo := 653408190) (W := 991810) (small_v333 h)
    ⟨326705000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v334

theorem small_v335 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 655390000 :=
  small_extend2 (a := 654400000) (A := 654400002) (lo := 654398190) (W := 991810) (small_v334 h)
    ⟨327200000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v335

theorem small_v336 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 656380000 :=
  small_extend2 (a := 655390000) (A := 655390002) (lo := 655388190) (W := 991810) (small_v335 h)
    ⟨327695000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v336

theorem small_v337 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 657370000 :=
  small_extend2 (a := 656380000) (A := 656380002) (lo := 656378190) (W := 991810) (small_v336 h)
    ⟨328190000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v337

theorem small_v338 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 658360000 :=
  small_extend2 (a := 657370000) (A := 657370002) (lo := 657368190) (W := 991810) (small_v337 h)
    ⟨328685000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v338

theorem small_v339 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 659350000 :=
  small_extend2 (a := 658360000) (A := 658360002) (lo := 658358190) (W := 991810) (small_v338 h)
    ⟨329180000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v339

theorem small_v340 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 660340000 :=
  small_extend2 (a := 659350000) (A := 659350002) (lo := 659348190) (W := 991810) (small_v339 h)
    ⟨329675000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v340

theorem small_v341 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 661330000 :=
  small_extend2 (a := 660340000) (A := 660340002) (lo := 660338190) (W := 991810) (small_v340 h)
    ⟨330170000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v341

theorem small_v342 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 662320000 :=
  small_extend2 (a := 661330000) (A := 661330002) (lo := 661328190) (W := 991810) (small_v341 h)
    ⟨330665000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v342

theorem small_v343 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 663310000 :=
  small_extend2 (a := 662320000) (A := 662320002) (lo := 662318190) (W := 991810) (small_v342 h)
    ⟨331160000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v343

theorem small_v344 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 664300000 :=
  small_extend2 (a := 663310000) (A := 663310002) (lo := 663308190) (W := 991810) (small_v343 h)
    ⟨331655000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v344

theorem small_v345 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 665290000 :=
  small_extend2 (a := 664300000) (A := 664300002) (lo := 664298190) (W := 991810) (small_v344 h)
    ⟨332150000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v345

theorem small_v346 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 666280000 :=
  small_extend2 (a := 665290000) (A := 665290002) (lo := 665288190) (W := 991810) (small_v345 h)
    ⟨332645000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v346

theorem small_v347 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 667270000 :=
  small_extend2 (a := 666280000) (A := 666280002) (lo := 666278190) (W := 991810) (small_v346 h)
    ⟨333140000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v347

theorem small_v348 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 668260000 :=
  small_extend2 (a := 667270000) (A := 667270002) (lo := 667268190) (W := 991810) (small_v347 h)
    ⟨333635000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v348

theorem small_v349 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 669250000 :=
  small_extend2 (a := 668260000) (A := 668260002) (lo := 668258190) (W := 991810) (small_v348 h)
    ⟨334130000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v349

theorem small_v350 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 670240000 :=
  small_extend2 (a := 669250000) (A := 669250002) (lo := 669248190) (W := 991810) (small_v349 h)
    ⟨334625000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v350

theorem small_v351 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 671230000 :=
  small_extend2 (a := 670240000) (A := 670240002) (lo := 670238190) (W := 991810) (small_v350 h)
    ⟨335120000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v351

theorem small_v352 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 672220000 :=
  small_extend2 (a := 671230000) (A := 671230002) (lo := 671228190) (W := 991810) (small_v351 h)
    ⟨335615000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v352

theorem small_v353 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 673210000 :=
  small_extend2 (a := 672220000) (A := 672220002) (lo := 672218190) (W := 991810) (small_v352 h)
    ⟨336110000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v353

theorem small_v354 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 674200000 :=
  small_extend2 (a := 673210000) (A := 673210002) (lo := 673208190) (W := 991810) (small_v353 h)
    ⟨336605000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v354

theorem small_v355 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 675190000 :=
  small_extend2 (a := 674200000) (A := 674200002) (lo := 674198190) (W := 991810) (small_v354 h)
    ⟨337100000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v355

theorem small_v356 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 676180000 :=
  small_extend2 (a := 675190000) (A := 675190002) (lo := 675188190) (W := 991810) (small_v355 h)
    ⟨337595000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v356

theorem small_v357 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 677170000 :=
  small_extend2 (a := 676180000) (A := 676180002) (lo := 676178190) (W := 991810) (small_v356 h)
    ⟨338090000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v357

theorem small_v358 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 678160000 :=
  small_extend2 (a := 677170000) (A := 677170002) (lo := 677168190) (W := 991810) (small_v357 h)
    ⟨338585000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v358

theorem small_v359 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 679150000 :=
  small_extend2 (a := 678160000) (A := 678160002) (lo := 678158190) (W := 991810) (small_v358 h)
    ⟨339080000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v359

theorem small_v360 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 680140000 :=
  small_extend2 (a := 679150000) (A := 679150002) (lo := 679148190) (W := 991810) (small_v359 h)
    ⟨339575000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v360

theorem small_v361 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 681130000 :=
  small_extend2 (a := 680140000) (A := 680140002) (lo := 680138190) (W := 991810) (small_v360 h)
    ⟨340070000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v361

theorem small_v362 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 682120000 :=
  small_extend2 (a := 681130000) (A := 681130002) (lo := 681128190) (W := 991810) (small_v361 h)
    ⟨340565000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v362

theorem small_v363 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 683110000 :=
  small_extend2 (a := 682120000) (A := 682120002) (lo := 682118190) (W := 991810) (small_v362 h)
    ⟨341060000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v363

theorem small_v364 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 684100000 :=
  small_extend2 (a := 683110000) (A := 683110002) (lo := 683108190) (W := 991810) (small_v363 h)
    ⟨341555000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v364

theorem small_v365 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 685090000 :=
  small_extend2 (a := 684100000) (A := 684100002) (lo := 684098190) (W := 991810) (small_v364 h)
    ⟨342050000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v365

theorem small_v366 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 686080000 :=
  small_extend2 (a := 685090000) (A := 685090002) (lo := 685088190) (W := 991810) (small_v365 h)
    ⟨342545000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v366

theorem small_v367 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 687070000 :=
  small_extend2 (a := 686080000) (A := 686080002) (lo := 686078190) (W := 991810) (small_v366 h)
    ⟨343040000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v367

theorem small_v368 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 688060000 :=
  small_extend2 (a := 687070000) (A := 687070002) (lo := 687068190) (W := 991810) (small_v367 h)
    ⟨343535000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v368

theorem small_v369 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 689050000 :=
  small_extend2 (a := 688060000) (A := 688060002) (lo := 688058190) (W := 991810) (small_v368 h)
    ⟨344030000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v369

theorem small_v370 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 690040000 :=
  small_extend2 (a := 689050000) (A := 689050002) (lo := 689048190) (W := 991810) (small_v369 h)
    ⟨344525000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v370

theorem small_v371 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 691030000 :=
  small_extend2 (a := 690040000) (A := 690040002) (lo := 690038190) (W := 991810) (small_v370 h)
    ⟨345020000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v371

theorem small_v372 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 692020000 :=
  small_extend2 (a := 691030000) (A := 691030002) (lo := 691028190) (W := 991810) (small_v371 h)
    ⟨345515000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v372

theorem small_v373 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 693010000 :=
  small_extend2 (a := 692020000) (A := 692020002) (lo := 692018190) (W := 991810) (small_v372 h)
    ⟨346010000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v373

theorem small_v374 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 694000000 :=
  small_extend2 (a := 693010000) (A := 693010002) (lo := 693008190) (W := 991810) (small_v373 h)
    ⟨346505000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v374

theorem small_v375 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 694990000 :=
  small_extend2 (a := 694000000) (A := 694000002) (lo := 693998190) (W := 991810) (small_v374 h)
    ⟨347000000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v375

theorem small_v376 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 695980000 :=
  small_extend2 (a := 694990000) (A := 694990002) (lo := 694988190) (W := 991810) (small_v375 h)
    ⟨347495000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v376

theorem small_v377 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 696970000 :=
  small_extend2 (a := 695980000) (A := 695980002) (lo := 695978190) (W := 991810) (small_v376 h)
    ⟨347990000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v377

theorem small_v378 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 697960000 :=
  small_extend2 (a := 696970000) (A := 696970002) (lo := 696968190) (W := 991810) (small_v377 h)
    ⟨348485000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v378

theorem small_v379 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 698950000 :=
  small_extend2 (a := 697960000) (A := 697960002) (lo := 697958190) (W := 991810) (small_v378 h)
    ⟨348980000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v379

theorem small_v380 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 699940000 :=
  small_extend2 (a := 698950000) (A := 698950002) (lo := 698948190) (W := 991810) (small_v379 h)
    ⟨349475000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v380

theorem small_v381 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 700930000 :=
  small_extend2 (a := 699940000) (A := 699940002) (lo := 699938190) (W := 991810) (small_v380 h)
    ⟨349970000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v381

theorem small_v382 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 701920000 :=
  small_extend2 (a := 700930000) (A := 700930002) (lo := 700928190) (W := 991810) (small_v381 h)
    ⟨350465000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v382

theorem small_v383 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 702910000 :=
  small_extend2 (a := 701920000) (A := 701920002) (lo := 701918190) (W := 991810) (small_v382 h)
    ⟨350960000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v383

theorem small_v384 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 703900000 :=
  small_extend2 (a := 702910000) (A := 702910002) (lo := 702908190) (W := 991810) (small_v383 h)
    ⟨351455000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v384

theorem small_v385 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 704890000 :=
  small_extend2 (a := 703900000) (A := 703900002) (lo := 703898190) (W := 991810) (small_v384 h)
    ⟨351950000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v385

theorem small_v386 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 705880000 :=
  small_extend2 (a := 704890000) (A := 704890002) (lo := 704888190) (W := 991810) (small_v385 h)
    ⟨352445000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v386

theorem small_v387 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 706870000 :=
  small_extend2 (a := 705880000) (A := 705880002) (lo := 705878190) (W := 991810) (small_v386 h)
    ⟨352940000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v387

theorem small_v388 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 707860000 :=
  small_extend2 (a := 706870000) (A := 706870002) (lo := 706868190) (W := 991810) (small_v387 h)
    ⟨353435000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v388

theorem small_v389 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 708850000 :=
  small_extend2 (a := 707860000) (A := 707860002) (lo := 707858190) (W := 991810) (small_v388 h)
    ⟨353930000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v389

theorem small_v390 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 709840000 :=
  small_extend2 (a := 708850000) (A := 708850002) (lo := 708848190) (W := 991810) (small_v389 h)
    ⟨354425000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v390

theorem small_v391 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 710830000 :=
  small_extend2 (a := 709840000) (A := 709840002) (lo := 709838190) (W := 991810) (small_v390 h)
    ⟨354920000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v391

theorem small_v392 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 711820000 :=
  small_extend2 (a := 710830000) (A := 710830002) (lo := 710828190) (W := 991810) (small_v391 h)
    ⟨355415000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v392

theorem small_v393 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 712810000 :=
  small_extend2 (a := 711820000) (A := 711820002) (lo := 711818190) (W := 991810) (small_v392 h)
    ⟨355910000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v393

theorem small_v394 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 713800000 :=
  small_extend2 (a := 712810000) (A := 712810002) (lo := 712808190) (W := 991810) (small_v393 h)
    ⟨356405000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v394

theorem small_v395 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 714790000 :=
  small_extend2 (a := 713800000) (A := 713800002) (lo := 713798190) (W := 991810) (small_v394 h)
    ⟨356900000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v395

theorem small_v396 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 715780000 :=
  small_extend2 (a := 714790000) (A := 714790002) (lo := 714788190) (W := 991810) (small_v395 h)
    ⟨357395000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v396

theorem small_v397 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 716770000 :=
  small_extend2 (a := 715780000) (A := 715780002) (lo := 715778190) (W := 991810) (small_v396 h)
    ⟨357890000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v397

theorem small_v398 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 717760000 :=
  small_extend2 (a := 716770000) (A := 716770002) (lo := 716768190) (W := 991810) (small_v397 h)
    ⟨358385000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v398

theorem small_v399 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 718750000 :=
  small_extend2 (a := 717760000) (A := 717760002) (lo := 717758190) (W := 991810) (small_v398 h)
    ⟨358880000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v399

theorem small_v400 (h : SmallGBUpTo 1811 620740000) : SmallGBUpTo 1811 719740000 :=
  small_extend2 (a := 718750000) (A := 718750002) (lo := 718748190) (W := 991810) (small_v399 h)
    ⟨359375000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v400

end LeanLab.Verifications.Top50.Bits
