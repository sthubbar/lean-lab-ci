/-
Chain block MV1: windows MV1 to MV100, from SmallGBUpTo 1789 323740000 to SmallGBUpTo 1789 422740000.
Each step is small_extend2 in SmallGB.lean.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.MinGBBase
import LeanLab.Verifications.Top50.BitMVG1
import LeanLab.Verifications.Top50.BitMVG2
import LeanLab.Verifications.Top50.BitMVG3
import LeanLab.Verifications.Top50.BitMVG4
import LeanLab.Verifications.Top50.BitMVG5
import LeanLab.Verifications.Top50.BitMVG6
import LeanLab.Verifications.Top50.BitMVG7
import LeanLab.Verifications.Top50.BitMVG8
import LeanLab.Verifications.Top50.BitMVG9
import LeanLab.Verifications.Top50.BitMVG10

namespace LeanLab.Verifications.Top50.Bits

theorem msmall_v1 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 324730000 :=
  small_extend2 (a := 323740000) (A := 323740002) (lo := 323738190) (W := 991810) h
    ⟨161870000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v1

theorem msmall_v2 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 325720000 :=
  small_extend2 (a := 324730000) (A := 324730002) (lo := 324728190) (W := 991810) (msmall_v1 h)
    ⟨162365000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v2

theorem msmall_v3 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 326710000 :=
  small_extend2 (a := 325720000) (A := 325720002) (lo := 325718190) (W := 991810) (msmall_v2 h)
    ⟨162860000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v3

theorem msmall_v4 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 327700000 :=
  small_extend2 (a := 326710000) (A := 326710002) (lo := 326708190) (W := 991810) (msmall_v3 h)
    ⟨163355000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v4

theorem msmall_v5 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 328690000 :=
  small_extend2 (a := 327700000) (A := 327700002) (lo := 327698190) (W := 991810) (msmall_v4 h)
    ⟨163850000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v5

theorem msmall_v6 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 329680000 :=
  small_extend2 (a := 328690000) (A := 328690002) (lo := 328688190) (W := 991810) (msmall_v5 h)
    ⟨164345000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v6

theorem msmall_v7 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 330670000 :=
  small_extend2 (a := 329680000) (A := 329680002) (lo := 329678190) (W := 991810) (msmall_v6 h)
    ⟨164840000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v7

theorem msmall_v8 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 331660000 :=
  small_extend2 (a := 330670000) (A := 330670002) (lo := 330668190) (W := 991810) (msmall_v7 h)
    ⟨165335000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v8

theorem msmall_v9 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 332650000 :=
  small_extend2 (a := 331660000) (A := 331660002) (lo := 331658190) (W := 991810) (msmall_v8 h)
    ⟨165830000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v9

theorem msmall_v10 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 333640000 :=
  small_extend2 (a := 332650000) (A := 332650002) (lo := 332648190) (W := 991810) (msmall_v9 h)
    ⟨166325000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v10

theorem msmall_v11 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 334630000 :=
  small_extend2 (a := 333640000) (A := 333640002) (lo := 333638190) (W := 991810) (msmall_v10 h)
    ⟨166820000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v11

theorem msmall_v12 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 335620000 :=
  small_extend2 (a := 334630000) (A := 334630002) (lo := 334628190) (W := 991810) (msmall_v11 h)
    ⟨167315000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v12

theorem msmall_v13 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 336610000 :=
  small_extend2 (a := 335620000) (A := 335620002) (lo := 335618190) (W := 991810) (msmall_v12 h)
    ⟨167810000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v13

theorem msmall_v14 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 337600000 :=
  small_extend2 (a := 336610000) (A := 336610002) (lo := 336608190) (W := 991810) (msmall_v13 h)
    ⟨168305000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v14

theorem msmall_v15 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 338590000 :=
  small_extend2 (a := 337600000) (A := 337600002) (lo := 337598190) (W := 991810) (msmall_v14 h)
    ⟨168800000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v15

theorem msmall_v16 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 339580000 :=
  small_extend2 (a := 338590000) (A := 338590002) (lo := 338588190) (W := 991810) (msmall_v15 h)
    ⟨169295000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v16

theorem msmall_v17 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 340570000 :=
  small_extend2 (a := 339580000) (A := 339580002) (lo := 339578190) (W := 991810) (msmall_v16 h)
    ⟨169790000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v17

theorem msmall_v18 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 341560000 :=
  small_extend2 (a := 340570000) (A := 340570002) (lo := 340568190) (W := 991810) (msmall_v17 h)
    ⟨170285000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v18

theorem msmall_v19 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 342550000 :=
  small_extend2 (a := 341560000) (A := 341560002) (lo := 341558190) (W := 991810) (msmall_v18 h)
    ⟨170780000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v19

theorem msmall_v20 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 343540000 :=
  small_extend2 (a := 342550000) (A := 342550002) (lo := 342548190) (W := 991810) (msmall_v19 h)
    ⟨171275000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v20

theorem msmall_v21 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 344530000 :=
  small_extend2 (a := 343540000) (A := 343540002) (lo := 343538190) (W := 991810) (msmall_v20 h)
    ⟨171770000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v21

theorem msmall_v22 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 345520000 :=
  small_extend2 (a := 344530000) (A := 344530002) (lo := 344528190) (W := 991810) (msmall_v21 h)
    ⟨172265000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v22

theorem msmall_v23 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 346510000 :=
  small_extend2 (a := 345520000) (A := 345520002) (lo := 345518190) (W := 991810) (msmall_v22 h)
    ⟨172760000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v23

theorem msmall_v24 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 347500000 :=
  small_extend2 (a := 346510000) (A := 346510002) (lo := 346508190) (W := 991810) (msmall_v23 h)
    ⟨173255000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v24

theorem msmall_v25 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 348490000 :=
  small_extend2 (a := 347500000) (A := 347500002) (lo := 347498190) (W := 991810) (msmall_v24 h)
    ⟨173750000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v25

theorem msmall_v26 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 349480000 :=
  small_extend2 (a := 348490000) (A := 348490002) (lo := 348488190) (W := 991810) (msmall_v25 h)
    ⟨174245000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v26

theorem msmall_v27 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 350470000 :=
  small_extend2 (a := 349480000) (A := 349480002) (lo := 349478190) (W := 991810) (msmall_v26 h)
    ⟨174740000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v27

theorem msmall_v28 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 351460000 :=
  small_extend2 (a := 350470000) (A := 350470002) (lo := 350468190) (W := 991810) (msmall_v27 h)
    ⟨175235000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v28

theorem msmall_v29 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 352450000 :=
  small_extend2 (a := 351460000) (A := 351460002) (lo := 351458190) (W := 991810) (msmall_v28 h)
    ⟨175730000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v29

theorem msmall_v30 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 353440000 :=
  small_extend2 (a := 352450000) (A := 352450002) (lo := 352448190) (W := 991810) (msmall_v29 h)
    ⟨176225000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v30

theorem msmall_v31 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 354430000 :=
  small_extend2 (a := 353440000) (A := 353440002) (lo := 353438190) (W := 991810) (msmall_v30 h)
    ⟨176720000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v31

theorem msmall_v32 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 355420000 :=
  small_extend2 (a := 354430000) (A := 354430002) (lo := 354428190) (W := 991810) (msmall_v31 h)
    ⟨177215000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v32

theorem msmall_v33 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 356410000 :=
  small_extend2 (a := 355420000) (A := 355420002) (lo := 355418190) (W := 991810) (msmall_v32 h)
    ⟨177710000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v33

theorem msmall_v34 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 357400000 :=
  small_extend2 (a := 356410000) (A := 356410002) (lo := 356408190) (W := 991810) (msmall_v33 h)
    ⟨178205000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v34

theorem msmall_v35 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 358390000 :=
  small_extend2 (a := 357400000) (A := 357400002) (lo := 357398190) (W := 991810) (msmall_v34 h)
    ⟨178700000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v35

theorem msmall_v36 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 359380000 :=
  small_extend2 (a := 358390000) (A := 358390002) (lo := 358388190) (W := 991810) (msmall_v35 h)
    ⟨179195000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v36

theorem msmall_v37 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 360370000 :=
  small_extend2 (a := 359380000) (A := 359380002) (lo := 359378190) (W := 991810) (msmall_v36 h)
    ⟨179690000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v37

theorem msmall_v38 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 361360000 :=
  small_extend2 (a := 360370000) (A := 360370002) (lo := 360368190) (W := 991810) (msmall_v37 h)
    ⟨180185000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v38

theorem msmall_v39 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 362350000 :=
  small_extend2 (a := 361360000) (A := 361360002) (lo := 361358190) (W := 991810) (msmall_v38 h)
    ⟨180680000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v39

theorem msmall_v40 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 363340000 :=
  small_extend2 (a := 362350000) (A := 362350002) (lo := 362348190) (W := 991810) (msmall_v39 h)
    ⟨181175000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v40

theorem msmall_v41 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 364330000 :=
  small_extend2 (a := 363340000) (A := 363340002) (lo := 363338190) (W := 991810) (msmall_v40 h)
    ⟨181670000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v41

theorem msmall_v42 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 365320000 :=
  small_extend2 (a := 364330000) (A := 364330002) (lo := 364328190) (W := 991810) (msmall_v41 h)
    ⟨182165000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v42

theorem msmall_v43 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 366310000 :=
  small_extend2 (a := 365320000) (A := 365320002) (lo := 365318190) (W := 991810) (msmall_v42 h)
    ⟨182660000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v43

theorem msmall_v44 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 367300000 :=
  small_extend2 (a := 366310000) (A := 366310002) (lo := 366308190) (W := 991810) (msmall_v43 h)
    ⟨183155000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v44

theorem msmall_v45 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 368290000 :=
  small_extend2 (a := 367300000) (A := 367300002) (lo := 367298190) (W := 991810) (msmall_v44 h)
    ⟨183650000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v45

theorem msmall_v46 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 369280000 :=
  small_extend2 (a := 368290000) (A := 368290002) (lo := 368288190) (W := 991810) (msmall_v45 h)
    ⟨184145000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v46

theorem msmall_v47 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 370270000 :=
  small_extend2 (a := 369280000) (A := 369280002) (lo := 369278190) (W := 991810) (msmall_v46 h)
    ⟨184640000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v47

theorem msmall_v48 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 371260000 :=
  small_extend2 (a := 370270000) (A := 370270002) (lo := 370268190) (W := 991810) (msmall_v47 h)
    ⟨185135000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v48

theorem msmall_v49 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 372250000 :=
  small_extend2 (a := 371260000) (A := 371260002) (lo := 371258190) (W := 991810) (msmall_v48 h)
    ⟨185630000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v49

theorem msmall_v50 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 373240000 :=
  small_extend2 (a := 372250000) (A := 372250002) (lo := 372248190) (W := 991810) (msmall_v49 h)
    ⟨186125000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v50

theorem msmall_v51 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 374230000 :=
  small_extend2 (a := 373240000) (A := 373240002) (lo := 373238190) (W := 991810) (msmall_v50 h)
    ⟨186620000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v51

theorem msmall_v52 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 375220000 :=
  small_extend2 (a := 374230000) (A := 374230002) (lo := 374228190) (W := 991810) (msmall_v51 h)
    ⟨187115000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v52

theorem msmall_v53 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 376210000 :=
  small_extend2 (a := 375220000) (A := 375220002) (lo := 375218190) (W := 991810) (msmall_v52 h)
    ⟨187610000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v53

theorem msmall_v54 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 377200000 :=
  small_extend2 (a := 376210000) (A := 376210002) (lo := 376208190) (W := 991810) (msmall_v53 h)
    ⟨188105000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v54

theorem msmall_v55 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 378190000 :=
  small_extend2 (a := 377200000) (A := 377200002) (lo := 377198190) (W := 991810) (msmall_v54 h)
    ⟨188600000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v55

theorem msmall_v56 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 379180000 :=
  small_extend2 (a := 378190000) (A := 378190002) (lo := 378188190) (W := 991810) (msmall_v55 h)
    ⟨189095000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v56

theorem msmall_v57 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 380170000 :=
  small_extend2 (a := 379180000) (A := 379180002) (lo := 379178190) (W := 991810) (msmall_v56 h)
    ⟨189590000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v57

theorem msmall_v58 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 381160000 :=
  small_extend2 (a := 380170000) (A := 380170002) (lo := 380168190) (W := 991810) (msmall_v57 h)
    ⟨190085000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v58

theorem msmall_v59 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 382150000 :=
  small_extend2 (a := 381160000) (A := 381160002) (lo := 381158190) (W := 991810) (msmall_v58 h)
    ⟨190580000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v59

theorem msmall_v60 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 383140000 :=
  small_extend2 (a := 382150000) (A := 382150002) (lo := 382148190) (W := 991810) (msmall_v59 h)
    ⟨191075000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v60

theorem msmall_v61 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 384130000 :=
  small_extend2 (a := 383140000) (A := 383140002) (lo := 383138190) (W := 991810) (msmall_v60 h)
    ⟨191570000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v61

theorem msmall_v62 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 385120000 :=
  small_extend2 (a := 384130000) (A := 384130002) (lo := 384128190) (W := 991810) (msmall_v61 h)
    ⟨192065000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v62

theorem msmall_v63 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 386110000 :=
  small_extend2 (a := 385120000) (A := 385120002) (lo := 385118190) (W := 991810) (msmall_v62 h)
    ⟨192560000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v63

theorem msmall_v64 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 387100000 :=
  small_extend2 (a := 386110000) (A := 386110002) (lo := 386108190) (W := 991810) (msmall_v63 h)
    ⟨193055000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v64

theorem msmall_v65 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 388090000 :=
  small_extend2 (a := 387100000) (A := 387100002) (lo := 387098190) (W := 991810) (msmall_v64 h)
    ⟨193550000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v65

theorem msmall_v66 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 389080000 :=
  small_extend2 (a := 388090000) (A := 388090002) (lo := 388088190) (W := 991810) (msmall_v65 h)
    ⟨194045000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v66

theorem msmall_v67 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 390070000 :=
  small_extend2 (a := 389080000) (A := 389080002) (lo := 389078190) (W := 991810) (msmall_v66 h)
    ⟨194540000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v67

theorem msmall_v68 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 391060000 :=
  small_extend2 (a := 390070000) (A := 390070002) (lo := 390068190) (W := 991810) (msmall_v67 h)
    ⟨195035000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v68

theorem msmall_v69 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 392050000 :=
  small_extend2 (a := 391060000) (A := 391060002) (lo := 391058190) (W := 991810) (msmall_v68 h)
    ⟨195530000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v69

theorem msmall_v70 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 393040000 :=
  small_extend2 (a := 392050000) (A := 392050002) (lo := 392048190) (W := 991810) (msmall_v69 h)
    ⟨196025000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v70

theorem msmall_v71 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 394030000 :=
  small_extend2 (a := 393040000) (A := 393040002) (lo := 393038190) (W := 991810) (msmall_v70 h)
    ⟨196520000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v71

theorem msmall_v72 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 395020000 :=
  small_extend2 (a := 394030000) (A := 394030002) (lo := 394028190) (W := 991810) (msmall_v71 h)
    ⟨197015000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v72

theorem msmall_v73 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 396010000 :=
  small_extend2 (a := 395020000) (A := 395020002) (lo := 395018190) (W := 991810) (msmall_v72 h)
    ⟨197510000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v73

theorem msmall_v74 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 397000000 :=
  small_extend2 (a := 396010000) (A := 396010002) (lo := 396008190) (W := 991810) (msmall_v73 h)
    ⟨198005000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v74

theorem msmall_v75 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 397990000 :=
  small_extend2 (a := 397000000) (A := 397000002) (lo := 396998190) (W := 991810) (msmall_v74 h)
    ⟨198500000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v75

theorem msmall_v76 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 398980000 :=
  small_extend2 (a := 397990000) (A := 397990002) (lo := 397988190) (W := 991810) (msmall_v75 h)
    ⟨198995000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v76

theorem msmall_v77 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 399970000 :=
  small_extend2 (a := 398980000) (A := 398980002) (lo := 398978190) (W := 991810) (msmall_v76 h)
    ⟨199490000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v77

theorem msmall_v78 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 400960000 :=
  small_extend2 (a := 399970000) (A := 399970002) (lo := 399968190) (W := 991810) (msmall_v77 h)
    ⟨199985000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v78

theorem msmall_v79 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 401950000 :=
  small_extend2 (a := 400960000) (A := 400960002) (lo := 400958190) (W := 991810) (msmall_v78 h)
    ⟨200480000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v79

theorem msmall_v80 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 402940000 :=
  small_extend2 (a := 401950000) (A := 401950002) (lo := 401948190) (W := 991810) (msmall_v79 h)
    ⟨200975000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v80

theorem msmall_v81 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 403930000 :=
  small_extend2 (a := 402940000) (A := 402940002) (lo := 402938190) (W := 991810) (msmall_v80 h)
    ⟨201470000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v81

theorem msmall_v82 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 404920000 :=
  small_extend2 (a := 403930000) (A := 403930002) (lo := 403928190) (W := 991810) (msmall_v81 h)
    ⟨201965000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v82

theorem msmall_v83 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 405910000 :=
  small_extend2 (a := 404920000) (A := 404920002) (lo := 404918190) (W := 991810) (msmall_v82 h)
    ⟨202460000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v83

theorem msmall_v84 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 406900000 :=
  small_extend2 (a := 405910000) (A := 405910002) (lo := 405908190) (W := 991810) (msmall_v83 h)
    ⟨202955000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v84

theorem msmall_v85 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 407890000 :=
  small_extend2 (a := 406900000) (A := 406900002) (lo := 406898190) (W := 991810) (msmall_v84 h)
    ⟨203450000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v85

theorem msmall_v86 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 408880000 :=
  small_extend2 (a := 407890000) (A := 407890002) (lo := 407888190) (W := 991810) (msmall_v85 h)
    ⟨203945000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v86

theorem msmall_v87 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 409870000 :=
  small_extend2 (a := 408880000) (A := 408880002) (lo := 408878190) (W := 991810) (msmall_v86 h)
    ⟨204440000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v87

theorem msmall_v88 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 410860000 :=
  small_extend2 (a := 409870000) (A := 409870002) (lo := 409868190) (W := 991810) (msmall_v87 h)
    ⟨204935000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v88

theorem msmall_v89 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 411850000 :=
  small_extend2 (a := 410860000) (A := 410860002) (lo := 410858190) (W := 991810) (msmall_v88 h)
    ⟨205430000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v89

theorem msmall_v90 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 412840000 :=
  small_extend2 (a := 411850000) (A := 411850002) (lo := 411848190) (W := 991810) (msmall_v89 h)
    ⟨205925000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v90

theorem msmall_v91 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 413830000 :=
  small_extend2 (a := 412840000) (A := 412840002) (lo := 412838190) (W := 991810) (msmall_v90 h)
    ⟨206420000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v91

theorem msmall_v92 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 414820000 :=
  small_extend2 (a := 413830000) (A := 413830002) (lo := 413828190) (W := 991810) (msmall_v91 h)
    ⟨206915000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v92

theorem msmall_v93 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 415810000 :=
  small_extend2 (a := 414820000) (A := 414820002) (lo := 414818190) (W := 991810) (msmall_v92 h)
    ⟨207410000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v93

theorem msmall_v94 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 416800000 :=
  small_extend2 (a := 415810000) (A := 415810002) (lo := 415808190) (W := 991810) (msmall_v93 h)
    ⟨207905000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v94

theorem msmall_v95 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 417790000 :=
  small_extend2 (a := 416800000) (A := 416800002) (lo := 416798190) (W := 991810) (msmall_v94 h)
    ⟨208400000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v95

theorem msmall_v96 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 418780000 :=
  small_extend2 (a := 417790000) (A := 417790002) (lo := 417788190) (W := 991810) (msmall_v95 h)
    ⟨208895000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v96

theorem msmall_v97 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 419770000 :=
  small_extend2 (a := 418780000) (A := 418780002) (lo := 418778190) (W := 991810) (msmall_v96 h)
    ⟨209390000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v97

theorem msmall_v98 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 420760000 :=
  small_extend2 (a := 419770000) (A := 419770002) (lo := 419768190) (W := 991810) (msmall_v97 h)
    ⟨209885000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v98

theorem msmall_v99 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 421750000 :=
  small_extend2 (a := 420760000) (A := 420760002) (lo := 420758190) (W := 991810) (msmall_v98 h)
    ⟨210380000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v99

theorem msmall_v100 (h : SmallGBUpTo 1789 323740000) : SmallGBUpTo 1789 422740000 :=
  small_extend2 (a := 421750000) (A := 421750002) (lo := 421748190) (W := 991810) (msmall_v99 h)
    ⟨210875000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 278) take278_le mwindow_v100

end LeanLab.Verifications.Top50.Bits
