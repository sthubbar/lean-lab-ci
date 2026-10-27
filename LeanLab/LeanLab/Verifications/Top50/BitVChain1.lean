/-
Chain block V1 of the kernel Goldbach windows past 323740000: windows V1 to V100, from
SmallGBUpTo 1811 323740000 to SmallGBUpTo 1811 422740000, so the blocks compose. Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.SmallGB
import LeanLab.Verifications.Top50.BitVG1
import LeanLab.Verifications.Top50.BitVG2
import LeanLab.Verifications.Top50.BitVG3
import LeanLab.Verifications.Top50.BitVG4
import LeanLab.Verifications.Top50.BitVG5
import LeanLab.Verifications.Top50.BitVG6
import LeanLab.Verifications.Top50.BitVG7
import LeanLab.Verifications.Top50.BitVG8
import LeanLab.Verifications.Top50.BitVG9
import LeanLab.Verifications.Top50.BitVG10

namespace LeanLab.Verifications.Top50.Bits

theorem small_v1 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 324730000 :=
  small_extend2 (a := 323740000) (A := 323740002) (lo := 323738190) (W := 991810) h
    ⟨161870000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v1

theorem small_v2 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 325720000 :=
  small_extend2 (a := 324730000) (A := 324730002) (lo := 324728190) (W := 991810) (small_v1 h)
    ⟨162365000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v2

theorem small_v3 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 326710000 :=
  small_extend2 (a := 325720000) (A := 325720002) (lo := 325718190) (W := 991810) (small_v2 h)
    ⟨162860000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v3

theorem small_v4 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 327700000 :=
  small_extend2 (a := 326710000) (A := 326710002) (lo := 326708190) (W := 991810) (small_v3 h)
    ⟨163355000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v4

theorem small_v5 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 328690000 :=
  small_extend2 (a := 327700000) (A := 327700002) (lo := 327698190) (W := 991810) (small_v4 h)
    ⟨163850000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v5

theorem small_v6 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 329680000 :=
  small_extend2 (a := 328690000) (A := 328690002) (lo := 328688190) (W := 991810) (small_v5 h)
    ⟨164345000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v6

theorem small_v7 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 330670000 :=
  small_extend2 (a := 329680000) (A := 329680002) (lo := 329678190) (W := 991810) (small_v6 h)
    ⟨164840000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v7

theorem small_v8 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 331660000 :=
  small_extend2 (a := 330670000) (A := 330670002) (lo := 330668190) (W := 991810) (small_v7 h)
    ⟨165335000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v8

theorem small_v9 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 332650000 :=
  small_extend2 (a := 331660000) (A := 331660002) (lo := 331658190) (W := 991810) (small_v8 h)
    ⟨165830000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v9

theorem small_v10 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 333640000 :=
  small_extend2 (a := 332650000) (A := 332650002) (lo := 332648190) (W := 991810) (small_v9 h)
    ⟨166325000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v10

theorem small_v11 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 334630000 :=
  small_extend2 (a := 333640000) (A := 333640002) (lo := 333638190) (W := 991810) (small_v10 h)
    ⟨166820000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v11

theorem small_v12 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 335620000 :=
  small_extend2 (a := 334630000) (A := 334630002) (lo := 334628190) (W := 991810) (small_v11 h)
    ⟨167315000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v12

theorem small_v13 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 336610000 :=
  small_extend2 (a := 335620000) (A := 335620002) (lo := 335618190) (W := 991810) (small_v12 h)
    ⟨167810000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v13

theorem small_v14 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 337600000 :=
  small_extend2 (a := 336610000) (A := 336610002) (lo := 336608190) (W := 991810) (small_v13 h)
    ⟨168305000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v14

theorem small_v15 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 338590000 :=
  small_extend2 (a := 337600000) (A := 337600002) (lo := 337598190) (W := 991810) (small_v14 h)
    ⟨168800000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v15

theorem small_v16 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 339580000 :=
  small_extend2 (a := 338590000) (A := 338590002) (lo := 338588190) (W := 991810) (small_v15 h)
    ⟨169295000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v16

theorem small_v17 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 340570000 :=
  small_extend2 (a := 339580000) (A := 339580002) (lo := 339578190) (W := 991810) (small_v16 h)
    ⟨169790000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v17

theorem small_v18 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 341560000 :=
  small_extend2 (a := 340570000) (A := 340570002) (lo := 340568190) (W := 991810) (small_v17 h)
    ⟨170285000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v18

theorem small_v19 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 342550000 :=
  small_extend2 (a := 341560000) (A := 341560002) (lo := 341558190) (W := 991810) (small_v18 h)
    ⟨170780000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v19

theorem small_v20 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 343540000 :=
  small_extend2 (a := 342550000) (A := 342550002) (lo := 342548190) (W := 991810) (small_v19 h)
    ⟨171275000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v20

theorem small_v21 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 344530000 :=
  small_extend2 (a := 343540000) (A := 343540002) (lo := 343538190) (W := 991810) (small_v20 h)
    ⟨171770000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v21

theorem small_v22 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 345520000 :=
  small_extend2 (a := 344530000) (A := 344530002) (lo := 344528190) (W := 991810) (small_v21 h)
    ⟨172265000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v22

theorem small_v23 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 346510000 :=
  small_extend2 (a := 345520000) (A := 345520002) (lo := 345518190) (W := 991810) (small_v22 h)
    ⟨172760000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v23

theorem small_v24 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 347500000 :=
  small_extend2 (a := 346510000) (A := 346510002) (lo := 346508190) (W := 991810) (small_v23 h)
    ⟨173255000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v24

theorem small_v25 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 348490000 :=
  small_extend2 (a := 347500000) (A := 347500002) (lo := 347498190) (W := 991810) (small_v24 h)
    ⟨173750000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v25

theorem small_v26 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 349480000 :=
  small_extend2 (a := 348490000) (A := 348490002) (lo := 348488190) (W := 991810) (small_v25 h)
    ⟨174245000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v26

theorem small_v27 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 350470000 :=
  small_extend2 (a := 349480000) (A := 349480002) (lo := 349478190) (W := 991810) (small_v26 h)
    ⟨174740000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v27

theorem small_v28 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 351460000 :=
  small_extend2 (a := 350470000) (A := 350470002) (lo := 350468190) (W := 991810) (small_v27 h)
    ⟨175235000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v28

theorem small_v29 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 352450000 :=
  small_extend2 (a := 351460000) (A := 351460002) (lo := 351458190) (W := 991810) (small_v28 h)
    ⟨175730000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v29

theorem small_v30 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 353440000 :=
  small_extend2 (a := 352450000) (A := 352450002) (lo := 352448190) (W := 991810) (small_v29 h)
    ⟨176225000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v30

theorem small_v31 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 354430000 :=
  small_extend2 (a := 353440000) (A := 353440002) (lo := 353438190) (W := 991810) (small_v30 h)
    ⟨176720000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v31

theorem small_v32 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 355420000 :=
  small_extend2 (a := 354430000) (A := 354430002) (lo := 354428190) (W := 991810) (small_v31 h)
    ⟨177215000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v32

theorem small_v33 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 356410000 :=
  small_extend2 (a := 355420000) (A := 355420002) (lo := 355418190) (W := 991810) (small_v32 h)
    ⟨177710000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v33

theorem small_v34 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 357400000 :=
  small_extend2 (a := 356410000) (A := 356410002) (lo := 356408190) (W := 991810) (small_v33 h)
    ⟨178205000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v34

theorem small_v35 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 358390000 :=
  small_extend2 (a := 357400000) (A := 357400002) (lo := 357398190) (W := 991810) (small_v34 h)
    ⟨178700000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v35

theorem small_v36 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 359380000 :=
  small_extend2 (a := 358390000) (A := 358390002) (lo := 358388190) (W := 991810) (small_v35 h)
    ⟨179195000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v36

theorem small_v37 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 360370000 :=
  small_extend2 (a := 359380000) (A := 359380002) (lo := 359378190) (W := 991810) (small_v36 h)
    ⟨179690000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v37

theorem small_v38 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 361360000 :=
  small_extend2 (a := 360370000) (A := 360370002) (lo := 360368190) (W := 991810) (small_v37 h)
    ⟨180185000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v38

theorem small_v39 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 362350000 :=
  small_extend2 (a := 361360000) (A := 361360002) (lo := 361358190) (W := 991810) (small_v38 h)
    ⟨180680000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v39

theorem small_v40 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 363340000 :=
  small_extend2 (a := 362350000) (A := 362350002) (lo := 362348190) (W := 991810) (small_v39 h)
    ⟨181175000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v40

theorem small_v41 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 364330000 :=
  small_extend2 (a := 363340000) (A := 363340002) (lo := 363338190) (W := 991810) (small_v40 h)
    ⟨181670000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v41

theorem small_v42 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 365320000 :=
  small_extend2 (a := 364330000) (A := 364330002) (lo := 364328190) (W := 991810) (small_v41 h)
    ⟨182165000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v42

theorem small_v43 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 366310000 :=
  small_extend2 (a := 365320000) (A := 365320002) (lo := 365318190) (W := 991810) (small_v42 h)
    ⟨182660000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v43

theorem small_v44 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 367300000 :=
  small_extend2 (a := 366310000) (A := 366310002) (lo := 366308190) (W := 991810) (small_v43 h)
    ⟨183155000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v44

theorem small_v45 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 368290000 :=
  small_extend2 (a := 367300000) (A := 367300002) (lo := 367298190) (W := 991810) (small_v44 h)
    ⟨183650000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v45

theorem small_v46 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 369280000 :=
  small_extend2 (a := 368290000) (A := 368290002) (lo := 368288190) (W := 991810) (small_v45 h)
    ⟨184145000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v46

theorem small_v47 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 370270000 :=
  small_extend2 (a := 369280000) (A := 369280002) (lo := 369278190) (W := 991810) (small_v46 h)
    ⟨184640000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v47

theorem small_v48 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 371260000 :=
  small_extend2 (a := 370270000) (A := 370270002) (lo := 370268190) (W := 991810) (small_v47 h)
    ⟨185135000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v48

theorem small_v49 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 372250000 :=
  small_extend2 (a := 371260000) (A := 371260002) (lo := 371258190) (W := 991810) (small_v48 h)
    ⟨185630000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v49

theorem small_v50 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 373240000 :=
  small_extend2 (a := 372250000) (A := 372250002) (lo := 372248190) (W := 991810) (small_v49 h)
    ⟨186125000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v50

theorem small_v51 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 374230000 :=
  small_extend2 (a := 373240000) (A := 373240002) (lo := 373238190) (W := 991810) (small_v50 h)
    ⟨186620000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v51

theorem small_v52 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 375220000 :=
  small_extend2 (a := 374230000) (A := 374230002) (lo := 374228190) (W := 991810) (small_v51 h)
    ⟨187115000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v52

theorem small_v53 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 376210000 :=
  small_extend2 (a := 375220000) (A := 375220002) (lo := 375218190) (W := 991810) (small_v52 h)
    ⟨187610000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v53

theorem small_v54 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 377200000 :=
  small_extend2 (a := 376210000) (A := 376210002) (lo := 376208190) (W := 991810) (small_v53 h)
    ⟨188105000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v54

theorem small_v55 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 378190000 :=
  small_extend2 (a := 377200000) (A := 377200002) (lo := 377198190) (W := 991810) (small_v54 h)
    ⟨188600000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v55

theorem small_v56 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 379180000 :=
  small_extend2 (a := 378190000) (A := 378190002) (lo := 378188190) (W := 991810) (small_v55 h)
    ⟨189095000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v56

theorem small_v57 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 380170000 :=
  small_extend2 (a := 379180000) (A := 379180002) (lo := 379178190) (W := 991810) (small_v56 h)
    ⟨189590000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v57

theorem small_v58 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 381160000 :=
  small_extend2 (a := 380170000) (A := 380170002) (lo := 380168190) (W := 991810) (small_v57 h)
    ⟨190085000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v58

theorem small_v59 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 382150000 :=
  small_extend2 (a := 381160000) (A := 381160002) (lo := 381158190) (W := 991810) (small_v58 h)
    ⟨190580000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v59

theorem small_v60 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 383140000 :=
  small_extend2 (a := 382150000) (A := 382150002) (lo := 382148190) (W := 991810) (small_v59 h)
    ⟨191075000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v60

theorem small_v61 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 384130000 :=
  small_extend2 (a := 383140000) (A := 383140002) (lo := 383138190) (W := 991810) (small_v60 h)
    ⟨191570000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v61

theorem small_v62 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 385120000 :=
  small_extend2 (a := 384130000) (A := 384130002) (lo := 384128190) (W := 991810) (small_v61 h)
    ⟨192065000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v62

theorem small_v63 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 386110000 :=
  small_extend2 (a := 385120000) (A := 385120002) (lo := 385118190) (W := 991810) (small_v62 h)
    ⟨192560000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v63

theorem small_v64 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 387100000 :=
  small_extend2 (a := 386110000) (A := 386110002) (lo := 386108190) (W := 991810) (small_v63 h)
    ⟨193055000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v64

theorem small_v65 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 388090000 :=
  small_extend2 (a := 387100000) (A := 387100002) (lo := 387098190) (W := 991810) (small_v64 h)
    ⟨193550000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v65

theorem small_v66 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 389080000 :=
  small_extend2 (a := 388090000) (A := 388090002) (lo := 388088190) (W := 991810) (small_v65 h)
    ⟨194045000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v66

theorem small_v67 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 390070000 :=
  small_extend2 (a := 389080000) (A := 389080002) (lo := 389078190) (W := 991810) (small_v66 h)
    ⟨194540000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v67

theorem small_v68 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 391060000 :=
  small_extend2 (a := 390070000) (A := 390070002) (lo := 390068190) (W := 991810) (small_v67 h)
    ⟨195035000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v68

theorem small_v69 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 392050000 :=
  small_extend2 (a := 391060000) (A := 391060002) (lo := 391058190) (W := 991810) (small_v68 h)
    ⟨195530000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v69

theorem small_v70 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 393040000 :=
  small_extend2 (a := 392050000) (A := 392050002) (lo := 392048190) (W := 991810) (small_v69 h)
    ⟨196025000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v70

theorem small_v71 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 394030000 :=
  small_extend2 (a := 393040000) (A := 393040002) (lo := 393038190) (W := 991810) (small_v70 h)
    ⟨196520000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v71

theorem small_v72 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 395020000 :=
  small_extend2 (a := 394030000) (A := 394030002) (lo := 394028190) (W := 991810) (small_v71 h)
    ⟨197015000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v72

theorem small_v73 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 396010000 :=
  small_extend2 (a := 395020000) (A := 395020002) (lo := 395018190) (W := 991810) (small_v72 h)
    ⟨197510000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v73

theorem small_v74 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 397000000 :=
  small_extend2 (a := 396010000) (A := 396010002) (lo := 396008190) (W := 991810) (small_v73 h)
    ⟨198005000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v74

theorem small_v75 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 397990000 :=
  small_extend2 (a := 397000000) (A := 397000002) (lo := 396998190) (W := 991810) (small_v74 h)
    ⟨198500000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v75

theorem small_v76 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 398980000 :=
  small_extend2 (a := 397990000) (A := 397990002) (lo := 397988190) (W := 991810) (small_v75 h)
    ⟨198995000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v76

theorem small_v77 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 399970000 :=
  small_extend2 (a := 398980000) (A := 398980002) (lo := 398978190) (W := 991810) (small_v76 h)
    ⟨199490000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v77

theorem small_v78 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 400960000 :=
  small_extend2 (a := 399970000) (A := 399970002) (lo := 399968190) (W := 991810) (small_v77 h)
    ⟨199985000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v78

theorem small_v79 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 401950000 :=
  small_extend2 (a := 400960000) (A := 400960002) (lo := 400958190) (W := 991810) (small_v78 h)
    ⟨200480000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v79

theorem small_v80 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 402940000 :=
  small_extend2 (a := 401950000) (A := 401950002) (lo := 401948190) (W := 991810) (small_v79 h)
    ⟨200975000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v80

theorem small_v81 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 403930000 :=
  small_extend2 (a := 402940000) (A := 402940002) (lo := 402938190) (W := 991810) (small_v80 h)
    ⟨201470000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v81

theorem small_v82 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 404920000 :=
  small_extend2 (a := 403930000) (A := 403930002) (lo := 403928190) (W := 991810) (small_v81 h)
    ⟨201965000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v82

theorem small_v83 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 405910000 :=
  small_extend2 (a := 404920000) (A := 404920002) (lo := 404918190) (W := 991810) (small_v82 h)
    ⟨202460000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v83

theorem small_v84 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 406900000 :=
  small_extend2 (a := 405910000) (A := 405910002) (lo := 405908190) (W := 991810) (small_v83 h)
    ⟨202955000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v84

theorem small_v85 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 407890000 :=
  small_extend2 (a := 406900000) (A := 406900002) (lo := 406898190) (W := 991810) (small_v84 h)
    ⟨203450000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v85

theorem small_v86 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 408880000 :=
  small_extend2 (a := 407890000) (A := 407890002) (lo := 407888190) (W := 991810) (small_v85 h)
    ⟨203945000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v86

theorem small_v87 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 409870000 :=
  small_extend2 (a := 408880000) (A := 408880002) (lo := 408878190) (W := 991810) (small_v86 h)
    ⟨204440000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v87

theorem small_v88 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 410860000 :=
  small_extend2 (a := 409870000) (A := 409870002) (lo := 409868190) (W := 991810) (small_v87 h)
    ⟨204935000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v88

theorem small_v89 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 411850000 :=
  small_extend2 (a := 410860000) (A := 410860002) (lo := 410858190) (W := 991810) (small_v88 h)
    ⟨205430000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v89

theorem small_v90 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 412840000 :=
  small_extend2 (a := 411850000) (A := 411850002) (lo := 411848190) (W := 991810) (small_v89 h)
    ⟨205925000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v90

theorem small_v91 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 413830000 :=
  small_extend2 (a := 412840000) (A := 412840002) (lo := 412838190) (W := 991810) (small_v90 h)
    ⟨206420000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v91

theorem small_v92 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 414820000 :=
  small_extend2 (a := 413830000) (A := 413830002) (lo := 413828190) (W := 991810) (small_v91 h)
    ⟨206915000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v92

theorem small_v93 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 415810000 :=
  small_extend2 (a := 414820000) (A := 414820002) (lo := 414818190) (W := 991810) (small_v92 h)
    ⟨207410000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v93

theorem small_v94 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 416800000 :=
  small_extend2 (a := 415810000) (A := 415810002) (lo := 415808190) (W := 991810) (small_v93 h)
    ⟨207905000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v94

theorem small_v95 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 417790000 :=
  small_extend2 (a := 416800000) (A := 416800002) (lo := 416798190) (W := 991810) (small_v94 h)
    ⟨208400000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v95

theorem small_v96 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 418780000 :=
  small_extend2 (a := 417790000) (A := 417790002) (lo := 417788190) (W := 991810) (small_v95 h)
    ⟨208895000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v96

theorem small_v97 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 419770000 :=
  small_extend2 (a := 418780000) (A := 418780002) (lo := 418778190) (W := 991810) (small_v96 h)
    ⟨209390000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v97

theorem small_v98 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 420760000 :=
  small_extend2 (a := 419770000) (A := 419770002) (lo := 419768190) (W := 991810) (small_v97 h)
    ⟨209885000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v98

theorem small_v99 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 421750000 :=
  small_extend2 (a := 420760000) (A := 420760002) (lo := 420758190) (W := 991810) (small_v98 h)
    ⟨210380000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v99

theorem small_v100 (h : SmallGBUpTo 1811 323740000) : SmallGBUpTo 1811 422740000 :=
  small_extend2 (a := 421750000) (A := 421750002) (lo := 421748190) (W := 991810) (small_v99 h)
    ⟨210875000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 280) take280_le window_v100

end LeanLab.Verifications.Top50.Bits
