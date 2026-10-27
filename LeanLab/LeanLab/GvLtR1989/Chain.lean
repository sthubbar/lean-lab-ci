/-
P0042 Granville, van de Lune, te Riele 1989, both numerical claims on the even range 6 to 218800000:
`gvltr_ratio_upTo`, minGB n < 1.603 log² n log log n, the paper's constant;
`ratio125_upTo`, the sharper constant 1.25 from n = 8, the lab's own observation;
`gvltr_max_upTo`, minGB n ≤ 1321 ≤ 2029.
Kernel checked with no cited input, 124 blocks. Far below the paper's 2·10^10.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Small
import LeanLab.GvLtR1989.W1
import LeanLab.GvLtR1989.W2aa
import LeanLab.GvLtR1989.W2ab
import LeanLab.GvLtR1989.W2b
import LeanLab.GvLtR1989.W3
import LeanLab.GvLtR1989.W4
import LeanLab.GvLtR1989.W5
import LeanLab.GvLtR1989.W6
import LeanLab.GvLtR1989.W7
import LeanLab.GvLtR1989.W8
import LeanLab.GvLtR1989.W9
import LeanLab.GvLtR1989.W10
import LeanLab.GvLtR1989.W11
import LeanLab.GvLtR1989.W12
import LeanLab.GvLtR1989.W13
import LeanLab.GvLtR1989.W14
import LeanLab.GvLtR1989.W15
import LeanLab.GvLtR1989.W16
import LeanLab.GvLtR1989.W17
import LeanLab.GvLtR1989.W18
import LeanLab.GvLtR1989.W19
import LeanLab.GvLtR1989.W20
import LeanLab.GvLtR1989.W21
import LeanLab.GvLtR1989.W22
import LeanLab.GvLtR1989.W23
import LeanLab.GvLtR1989.W24
import LeanLab.GvLtR1989.W25
import LeanLab.GvLtR1989.W26
import LeanLab.GvLtR1989.W27
import LeanLab.GvLtR1989.W28
import LeanLab.GvLtR1989.W29
import LeanLab.GvLtR1989.W30
import LeanLab.GvLtR1989.W31
import LeanLab.GvLtR1989.W32
import LeanLab.GvLtR1989.W33
import LeanLab.GvLtR1989.W34
import LeanLab.GvLtR1989.W35
import LeanLab.GvLtR1989.W36
import LeanLab.GvLtR1989.W37
import LeanLab.GvLtR1989.W38
import LeanLab.GvLtR1989.W39
import LeanLab.GvLtR1989.W40
import LeanLab.GvLtR1989.W41
import LeanLab.GvLtR1989.W42
import LeanLab.GvLtR1989.W43
import LeanLab.GvLtR1989.W44
import LeanLab.GvLtR1989.W45
import LeanLab.GvLtR1989.W46
import LeanLab.GvLtR1989.W47
import LeanLab.GvLtR1989.W48
import LeanLab.GvLtR1989.W49
import LeanLab.GvLtR1989.W50
import LeanLab.GvLtR1989.W51
import LeanLab.GvLtR1989.W52
import LeanLab.GvLtR1989.W53
import LeanLab.GvLtR1989.W54
import LeanLab.GvLtR1989.W55
import LeanLab.GvLtR1989.W56
import LeanLab.GvLtR1989.W57
import LeanLab.GvLtR1989.W58
import LeanLab.GvLtR1989.W59
import LeanLab.GvLtR1989.W60
import LeanLab.GvLtR1989.W61
import LeanLab.GvLtR1989.W62
import LeanLab.GvLtR1989.W63
import LeanLab.GvLtR1989.W64
import LeanLab.GvLtR1989.W65
import LeanLab.GvLtR1989.W66
import LeanLab.GvLtR1989.W67
import LeanLab.GvLtR1989.W68
import LeanLab.GvLtR1989.W69
import LeanLab.GvLtR1989.W70
import LeanLab.GvLtR1989.W71
import LeanLab.GvLtR1989.W72
import LeanLab.GvLtR1989.W73
import LeanLab.GvLtR1989.W74
import LeanLab.GvLtR1989.W75
import LeanLab.GvLtR1989.W76
import LeanLab.GvLtR1989.W77
import LeanLab.GvLtR1989.W78
import LeanLab.GvLtR1989.W79
import LeanLab.GvLtR1989.W80
import LeanLab.GvLtR1989.W81
import LeanLab.GvLtR1989.W82
import LeanLab.GvLtR1989.W83
import LeanLab.GvLtR1989.W84
import LeanLab.GvLtR1989.W85
import LeanLab.GvLtR1989.W86
import LeanLab.GvLtR1989.W87
import LeanLab.GvLtR1989.W88
import LeanLab.GvLtR1989.W89
import LeanLab.GvLtR1989.W90
import LeanLab.GvLtR1989.W91
import LeanLab.GvLtR1989.W92
import LeanLab.GvLtR1989.W93
import LeanLab.GvLtR1989.W94
import LeanLab.GvLtR1989.W95
import LeanLab.GvLtR1989.W96
import LeanLab.GvLtR1989.W97
import LeanLab.GvLtR1989.W98
import LeanLab.GvLtR1989.W99
import LeanLab.GvLtR1989.W100
import LeanLab.GvLtR1989.W101
import LeanLab.GvLtR1989.W102
import LeanLab.GvLtR1989.W103
import LeanLab.GvLtR1989.W104
import LeanLab.GvLtR1989.W105
import LeanLab.GvLtR1989.W106
import LeanLab.GvLtR1989.W107
import LeanLab.GvLtR1989.W108
import LeanLab.GvLtR1989.W109
import LeanLab.GvLtR1989.W110

namespace LeanLab.GvLtR1989

open LeanLab.Verifications

theorem c1_0 : ∀ n, Even n → 6 ≤ n → n ≤ 6 → (Ratio 1.603) n := r1_0
theorem c1_1 : ∀ n, Even n → 6 ≤ n → n ≤ 8 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_0 r1_1 (by norm_num) (by decide)
theorem c1_2 : ∀ n, Even n → 6 ≤ n → n ≤ 28 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_1 r1_2 (by norm_num) (by decide)
theorem c1_3 : ∀ n, Even n → 6 ≤ n → n ≤ 96 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_2 r1_3 (by norm_num) (by decide)
theorem c1_4 : ∀ n, Even n → 6 ≤ n → n ≤ 552 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_3 r1_4 (by norm_num) (by decide)
theorem c1_5 : ∀ n, Even n → 6 ≤ n → n ≤ 2638 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_4 r1_5 (by norm_num) (by decide)
theorem c1_6 : ∀ n, Even n → 6 ≤ n → n ≤ 7424 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_5 r1_6 (by norm_num) (by decide)
theorem c1_7 : ∀ n, Even n → 6 ≤ n → n ≤ 54242 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_6 r1_7 (by norm_num) (by decide)
theorem c1_8 : ∀ n, Even n → 6 ≤ n → n ≤ 194426 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_7 r1_8 (by norm_num) (by decide)
theorem c1_9 : ∀ n, Even n → 6 ≤ n → n ≤ 503218 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_8 r1_9 (by norm_num) (by decide)
theorem c1_10 : ∀ n, Even n → 6 ≤ n → n ≤ 999998 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_9 r1_10 (by norm_num) (by decide)
theorem c1_11 : ∀ n, Even n → 6 ≤ n → n ≤ 1000000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_10 r1_11 (by norm_num) (by decide)
theorem c1_12 : ∀ n, Even n → 6 ≤ n → n ≤ 2980000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_11 r1_12 (by norm_num) (by decide)
theorem c1_13 : ∀ n, Even n → 6 ≤ n → n ≤ 3475000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_12 r1_13 (by norm_num) (by decide)
theorem c1_14 : ∀ n, Even n → 6 ≤ n → n ≤ 3970000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_13 r1_14 (by norm_num) (by decide)
theorem c1_15 : ∀ n, Even n → 6 ≤ n → n ≤ 4960000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_14 r1_15 (by norm_num) (by decide)
theorem c1_16 : ∀ n, Even n → 6 ≤ n → n ≤ 6940000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_15 r1_16 (by norm_num) (by decide)
theorem c1_17 : ∀ n, Even n → 6 ≤ n → n ≤ 8920000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_16 r1_17 (by norm_num) (by decide)
theorem c1_18 : ∀ n, Even n → 6 ≤ n → n ≤ 10900000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_17 r1_18 (by norm_num) (by decide)
theorem c1_19 : ∀ n, Even n → 6 ≤ n → n ≤ 12880000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_18 r1_19 (by norm_num) (by decide)
theorem c1_20 : ∀ n, Even n → 6 ≤ n → n ≤ 14860000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_19 r1_20 (by norm_num) (by decide)
theorem c1_21 : ∀ n, Even n → 6 ≤ n → n ≤ 16840000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_20 r1_21 (by norm_num) (by decide)
theorem c1_22 : ∀ n, Even n → 6 ≤ n → n ≤ 18820000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_21 r1_22 (by norm_num) (by decide)
theorem c1_23 : ∀ n, Even n → 6 ≤ n → n ≤ 20800000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_22 r1_23 (by norm_num) (by decide)
theorem c1_24 : ∀ n, Even n → 6 ≤ n → n ≤ 22780000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_23 r1_24 (by norm_num) (by decide)
theorem c1_25 : ∀ n, Even n → 6 ≤ n → n ≤ 24760000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_24 r1_25 (by norm_num) (by decide)
theorem c1_26 : ∀ n, Even n → 6 ≤ n → n ≤ 26740000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_25 r1_26 (by norm_num) (by decide)
theorem c1_27 : ∀ n, Even n → 6 ≤ n → n ≤ 28720000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_26 r1_27 (by norm_num) (by decide)
theorem c1_28 : ∀ n, Even n → 6 ≤ n → n ≤ 30700000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_27 r1_28 (by norm_num) (by decide)
theorem c1_29 : ∀ n, Even n → 6 ≤ n → n ≤ 32680000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_28 r1_29 (by norm_num) (by decide)
theorem c1_30 : ∀ n, Even n → 6 ≤ n → n ≤ 34660000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_29 r1_30 (by norm_num) (by decide)
theorem c1_31 : ∀ n, Even n → 6 ≤ n → n ≤ 36640000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_30 r1_31 (by norm_num) (by decide)
theorem c1_32 : ∀ n, Even n → 6 ≤ n → n ≤ 38620000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_31 r1_32 (by norm_num) (by decide)
theorem c1_33 : ∀ n, Even n → 6 ≤ n → n ≤ 40600000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_32 r1_33 (by norm_num) (by decide)
theorem c1_34 : ∀ n, Even n → 6 ≤ n → n ≤ 42580000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_33 r1_34 (by norm_num) (by decide)
theorem c1_35 : ∀ n, Even n → 6 ≤ n → n ≤ 44560000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_34 r1_35 (by norm_num) (by decide)
theorem c1_36 : ∀ n, Even n → 6 ≤ n → n ≤ 46540000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_35 r1_36 (by norm_num) (by decide)
theorem c1_37 : ∀ n, Even n → 6 ≤ n → n ≤ 48520000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_36 r1_37 (by norm_num) (by decide)
theorem c1_38 : ∀ n, Even n → 6 ≤ n → n ≤ 50500000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_37 r1_38 (by norm_num) (by decide)
theorem c1_39 : ∀ n, Even n → 6 ≤ n → n ≤ 52480000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_38 r1_39 (by norm_num) (by decide)
theorem c1_40 : ∀ n, Even n → 6 ≤ n → n ≤ 54460000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_39 r1_40 (by norm_num) (by decide)
theorem c1_41 : ∀ n, Even n → 6 ≤ n → n ≤ 56440000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_40 r1_41 (by norm_num) (by decide)
theorem c1_42 : ∀ n, Even n → 6 ≤ n → n ≤ 58420000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_41 r1_42 (by norm_num) (by decide)
theorem c1_43 : ∀ n, Even n → 6 ≤ n → n ≤ 60400000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_42 r1_43 (by norm_num) (by decide)
theorem c1_44 : ∀ n, Even n → 6 ≤ n → n ≤ 62380000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_43 r1_44 (by norm_num) (by decide)
theorem c1_45 : ∀ n, Even n → 6 ≤ n → n ≤ 64360000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_44 r1_45 (by norm_num) (by decide)
theorem c1_46 : ∀ n, Even n → 6 ≤ n → n ≤ 66340000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_45 r1_46 (by norm_num) (by decide)
theorem c1_47 : ∀ n, Even n → 6 ≤ n → n ≤ 68320000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_46 r1_47 (by norm_num) (by decide)
theorem c1_48 : ∀ n, Even n → 6 ≤ n → n ≤ 70300000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_47 r1_48 (by norm_num) (by decide)
theorem c1_49 : ∀ n, Even n → 6 ≤ n → n ≤ 72280000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_48 r1_49 (by norm_num) (by decide)
theorem c1_50 : ∀ n, Even n → 6 ≤ n → n ≤ 74260000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_49 r1_50 (by norm_num) (by decide)
theorem c1_51 : ∀ n, Even n → 6 ≤ n → n ≤ 76240000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_50 r1_51 (by norm_num) (by decide)
theorem c1_52 : ∀ n, Even n → 6 ≤ n → n ≤ 78220000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_51 r1_52 (by norm_num) (by decide)
theorem c1_53 : ∀ n, Even n → 6 ≤ n → n ≤ 80200000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_52 r1_53 (by norm_num) (by decide)
theorem c1_54 : ∀ n, Even n → 6 ≤ n → n ≤ 82180000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_53 r1_54 (by norm_num) (by decide)
theorem c1_55 : ∀ n, Even n → 6 ≤ n → n ≤ 84160000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_54 r1_55 (by norm_num) (by decide)
theorem c1_56 : ∀ n, Even n → 6 ≤ n → n ≤ 86140000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_55 r1_56 (by norm_num) (by decide)
theorem c1_57 : ∀ n, Even n → 6 ≤ n → n ≤ 88120000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_56 r1_57 (by norm_num) (by decide)
theorem c1_58 : ∀ n, Even n → 6 ≤ n → n ≤ 90100000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_57 r1_58 (by norm_num) (by decide)
theorem c1_59 : ∀ n, Even n → 6 ≤ n → n ≤ 92080000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_58 r1_59 (by norm_num) (by decide)
theorem c1_60 : ∀ n, Even n → 6 ≤ n → n ≤ 94060000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_59 r1_60 (by norm_num) (by decide)
theorem c1_61 : ∀ n, Even n → 6 ≤ n → n ≤ 96040000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_60 r1_61 (by norm_num) (by decide)
theorem c1_62 : ∀ n, Even n → 6 ≤ n → n ≤ 98020000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_61 r1_62 (by norm_num) (by decide)
theorem c1_63 : ∀ n, Even n → 6 ≤ n → n ≤ 100000000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_62 r1_63 (by norm_num) (by decide)
theorem c1_64 : ∀ n, Even n → 6 ≤ n → n ≤ 101980000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_63 r1_64 (by norm_num) (by decide)
theorem c1_65 : ∀ n, Even n → 6 ≤ n → n ≤ 103960000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_64 r1_65 (by norm_num) (by decide)
theorem c1_66 : ∀ n, Even n → 6 ≤ n → n ≤ 105940000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_65 r1_66 (by norm_num) (by decide)
theorem c1_67 : ∀ n, Even n → 6 ≤ n → n ≤ 107920000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_66 r1_67 (by norm_num) (by decide)
theorem c1_68 : ∀ n, Even n → 6 ≤ n → n ≤ 109900000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_67 r1_68 (by norm_num) (by decide)
theorem c1_69 : ∀ n, Even n → 6 ≤ n → n ≤ 111880000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_68 r1_69 (by norm_num) (by decide)
theorem c1_70 : ∀ n, Even n → 6 ≤ n → n ≤ 113860000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_69 r1_70 (by norm_num) (by decide)
theorem c1_71 : ∀ n, Even n → 6 ≤ n → n ≤ 115840000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_70 r1_71 (by norm_num) (by decide)
theorem c1_72 : ∀ n, Even n → 6 ≤ n → n ≤ 117820000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_71 r1_72 (by norm_num) (by decide)
theorem c1_73 : ∀ n, Even n → 6 ≤ n → n ≤ 119800000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_72 r1_73 (by norm_num) (by decide)
theorem c1_74 : ∀ n, Even n → 6 ≤ n → n ≤ 121780000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_73 r1_74 (by norm_num) (by decide)
theorem c1_75 : ∀ n, Even n → 6 ≤ n → n ≤ 123760000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_74 r1_75 (by norm_num) (by decide)
theorem c1_76 : ∀ n, Even n → 6 ≤ n → n ≤ 125740000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_75 r1_76 (by norm_num) (by decide)
theorem c1_77 : ∀ n, Even n → 6 ≤ n → n ≤ 127720000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_76 r1_77 (by norm_num) (by decide)
theorem c1_78 : ∀ n, Even n → 6 ≤ n → n ≤ 129700000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_77 r1_78 (by norm_num) (by decide)
theorem c1_79 : ∀ n, Even n → 6 ≤ n → n ≤ 131680000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_78 r1_79 (by norm_num) (by decide)
theorem c1_80 : ∀ n, Even n → 6 ≤ n → n ≤ 133660000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_79 r1_80 (by norm_num) (by decide)
theorem c1_81 : ∀ n, Even n → 6 ≤ n → n ≤ 135640000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_80 r1_81 (by norm_num) (by decide)
theorem c1_82 : ∀ n, Even n → 6 ≤ n → n ≤ 137620000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_81 r1_82 (by norm_num) (by decide)
theorem c1_83 : ∀ n, Even n → 6 ≤ n → n ≤ 139600000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_82 r1_83 (by norm_num) (by decide)
theorem c1_84 : ∀ n, Even n → 6 ≤ n → n ≤ 141580000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_83 r1_84 (by norm_num) (by decide)
theorem c1_85 : ∀ n, Even n → 6 ≤ n → n ≤ 143560000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_84 r1_85 (by norm_num) (by decide)
theorem c1_86 : ∀ n, Even n → 6 ≤ n → n ≤ 145540000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_85 r1_86 (by norm_num) (by decide)
theorem c1_87 : ∀ n, Even n → 6 ≤ n → n ≤ 147520000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_86 r1_87 (by norm_num) (by decide)
theorem c1_88 : ∀ n, Even n → 6 ≤ n → n ≤ 149500000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_87 r1_88 (by norm_num) (by decide)
theorem c1_89 : ∀ n, Even n → 6 ≤ n → n ≤ 151480000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_88 r1_89 (by norm_num) (by decide)
theorem c1_90 : ∀ n, Even n → 6 ≤ n → n ≤ 153460000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_89 r1_90 (by norm_num) (by decide)
theorem c1_91 : ∀ n, Even n → 6 ≤ n → n ≤ 155440000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_90 r1_91 (by norm_num) (by decide)
theorem c1_92 : ∀ n, Even n → 6 ≤ n → n ≤ 157420000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_91 r1_92 (by norm_num) (by decide)
theorem c1_93 : ∀ n, Even n → 6 ≤ n → n ≤ 159400000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_92 r1_93 (by norm_num) (by decide)
theorem c1_94 : ∀ n, Even n → 6 ≤ n → n ≤ 161380000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_93 r1_94 (by norm_num) (by decide)
theorem c1_95 : ∀ n, Even n → 6 ≤ n → n ≤ 163360000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_94 r1_95 (by norm_num) (by decide)
theorem c1_96 : ∀ n, Even n → 6 ≤ n → n ≤ 165340000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_95 r1_96 (by norm_num) (by decide)
theorem c1_97 : ∀ n, Even n → 6 ≤ n → n ≤ 167320000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_96 r1_97 (by norm_num) (by decide)
theorem c1_98 : ∀ n, Even n → 6 ≤ n → n ≤ 169300000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_97 r1_98 (by norm_num) (by decide)
theorem c1_99 : ∀ n, Even n → 6 ≤ n → n ≤ 171280000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_98 r1_99 (by norm_num) (by decide)
theorem c1_100 : ∀ n, Even n → 6 ≤ n → n ≤ 173260000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_99 r1_100 (by norm_num) (by decide)
theorem c1_101 : ∀ n, Even n → 6 ≤ n → n ≤ 175240000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_100 r1_101 (by norm_num) (by decide)
theorem c1_102 : ∀ n, Even n → 6 ≤ n → n ≤ 177220000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_101 r1_102 (by norm_num) (by decide)
theorem c1_103 : ∀ n, Even n → 6 ≤ n → n ≤ 179200000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_102 r1_103 (by norm_num) (by decide)
theorem c1_104 : ∀ n, Even n → 6 ≤ n → n ≤ 181180000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_103 r1_104 (by norm_num) (by decide)
theorem c1_105 : ∀ n, Even n → 6 ≤ n → n ≤ 183160000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_104 r1_105 (by norm_num) (by decide)
theorem c1_106 : ∀ n, Even n → 6 ≤ n → n ≤ 185140000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_105 r1_106 (by norm_num) (by decide)
theorem c1_107 : ∀ n, Even n → 6 ≤ n → n ≤ 187120000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_106 r1_107 (by norm_num) (by decide)
theorem c1_108 : ∀ n, Even n → 6 ≤ n → n ≤ 189100000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_107 r1_108 (by norm_num) (by decide)
theorem c1_109 : ∀ n, Even n → 6 ≤ n → n ≤ 191080000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_108 r1_109 (by norm_num) (by decide)
theorem c1_110 : ∀ n, Even n → 6 ≤ n → n ≤ 193060000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_109 r1_110 (by norm_num) (by decide)
theorem c1_111 : ∀ n, Even n → 6 ≤ n → n ≤ 195040000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_110 r1_111 (by norm_num) (by decide)
theorem c1_112 : ∀ n, Even n → 6 ≤ n → n ≤ 197020000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_111 r1_112 (by norm_num) (by decide)
theorem c1_113 : ∀ n, Even n → 6 ≤ n → n ≤ 199000000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_112 r1_113 (by norm_num) (by decide)
theorem c1_114 : ∀ n, Even n → 6 ≤ n → n ≤ 200980000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_113 r1_114 (by norm_num) (by decide)
theorem c1_115 : ∀ n, Even n → 6 ≤ n → n ≤ 202960000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_114 r1_115 (by norm_num) (by decide)
theorem c1_116 : ∀ n, Even n → 6 ≤ n → n ≤ 204940000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_115 r1_116 (by norm_num) (by decide)
theorem c1_117 : ∀ n, Even n → 6 ≤ n → n ≤ 206920000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_116 r1_117 (by norm_num) (by decide)
theorem c1_118 : ∀ n, Even n → 6 ≤ n → n ≤ 208900000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_117 r1_118 (by norm_num) (by decide)
theorem c1_119 : ∀ n, Even n → 6 ≤ n → n ≤ 210880000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_118 r1_119 (by norm_num) (by decide)
theorem c1_120 : ∀ n, Even n → 6 ≤ n → n ≤ 212860000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_119 r1_120 (by norm_num) (by decide)
theorem c1_121 : ∀ n, Even n → 6 ≤ n → n ≤ 214840000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_120 r1_121 (by norm_num) (by decide)
theorem c1_122 : ∀ n, Even n → 6 ≤ n → n ≤ 216820000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_121 r1_122 (by norm_num) (by decide)
theorem c1_123 : ∀ n, Even n → 6 ≤ n → n ≤ 218800000 → (Ratio 1.603) n :=
  join (P := (Ratio 1.603)) c1_122 r1_123 (by norm_num) (by decide)
theorem c2_0 : ∀ n, Even n → 8 ≤ n → n ≤ 8 → (Ratio 1.25) n := r2_1
theorem c2_2 : ∀ n, Even n → 8 ≤ n → n ≤ 28 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_0 r2_2 (by norm_num) (by decide)
theorem c2_3 : ∀ n, Even n → 8 ≤ n → n ≤ 96 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_2 r2_3 (by norm_num) (by decide)
theorem c2_4 : ∀ n, Even n → 8 ≤ n → n ≤ 552 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_3 r2_4 (by norm_num) (by decide)
theorem c2_5 : ∀ n, Even n → 8 ≤ n → n ≤ 2638 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_4 r2_5 (by norm_num) (by decide)
theorem c2_6 : ∀ n, Even n → 8 ≤ n → n ≤ 7424 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_5 r2_6 (by norm_num) (by decide)
theorem c2_7 : ∀ n, Even n → 8 ≤ n → n ≤ 54242 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_6 r2_7 (by norm_num) (by decide)
theorem c2_8 : ∀ n, Even n → 8 ≤ n → n ≤ 194426 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_7 r2_8 (by norm_num) (by decide)
theorem c2_9 : ∀ n, Even n → 8 ≤ n → n ≤ 503218 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_8 r2_9 (by norm_num) (by decide)
theorem c2_10 : ∀ n, Even n → 8 ≤ n → n ≤ 999998 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_9 r2_10 (by norm_num) (by decide)
theorem c2_11 : ∀ n, Even n → 8 ≤ n → n ≤ 1000000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_10 r2_11 (by norm_num) (by decide)
theorem c2_12 : ∀ n, Even n → 8 ≤ n → n ≤ 2980000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_11 r2_12 (by norm_num) (by decide)
theorem c2_13 : ∀ n, Even n → 8 ≤ n → n ≤ 3475000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_12 r2_13 (by norm_num) (by decide)
theorem c2_14 : ∀ n, Even n → 8 ≤ n → n ≤ 3970000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_13 r2_14 (by norm_num) (by decide)
theorem c2_15 : ∀ n, Even n → 8 ≤ n → n ≤ 4960000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_14 r2_15 (by norm_num) (by decide)
theorem c2_16 : ∀ n, Even n → 8 ≤ n → n ≤ 6940000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_15 r2_16 (by norm_num) (by decide)
theorem c2_17 : ∀ n, Even n → 8 ≤ n → n ≤ 8920000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_16 r2_17 (by norm_num) (by decide)
theorem c2_18 : ∀ n, Even n → 8 ≤ n → n ≤ 10900000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_17 r2_18 (by norm_num) (by decide)
theorem c2_19 : ∀ n, Even n → 8 ≤ n → n ≤ 12880000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_18 r2_19 (by norm_num) (by decide)
theorem c2_20 : ∀ n, Even n → 8 ≤ n → n ≤ 14860000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_19 r2_20 (by norm_num) (by decide)
theorem c2_21 : ∀ n, Even n → 8 ≤ n → n ≤ 16840000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_20 r2_21 (by norm_num) (by decide)
theorem c2_22 : ∀ n, Even n → 8 ≤ n → n ≤ 18820000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_21 r2_22 (by norm_num) (by decide)
theorem c2_23 : ∀ n, Even n → 8 ≤ n → n ≤ 20800000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_22 r2_23 (by norm_num) (by decide)
theorem c2_24 : ∀ n, Even n → 8 ≤ n → n ≤ 22780000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_23 r2_24 (by norm_num) (by decide)
theorem c2_25 : ∀ n, Even n → 8 ≤ n → n ≤ 24760000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_24 r2_25 (by norm_num) (by decide)
theorem c2_26 : ∀ n, Even n → 8 ≤ n → n ≤ 26740000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_25 r2_26 (by norm_num) (by decide)
theorem c2_27 : ∀ n, Even n → 8 ≤ n → n ≤ 28720000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_26 r2_27 (by norm_num) (by decide)
theorem c2_28 : ∀ n, Even n → 8 ≤ n → n ≤ 30700000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_27 r2_28 (by norm_num) (by decide)
theorem c2_29 : ∀ n, Even n → 8 ≤ n → n ≤ 32680000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_28 r2_29 (by norm_num) (by decide)
theorem c2_30 : ∀ n, Even n → 8 ≤ n → n ≤ 34660000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_29 r2_30 (by norm_num) (by decide)
theorem c2_31 : ∀ n, Even n → 8 ≤ n → n ≤ 36640000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_30 r2_31 (by norm_num) (by decide)
theorem c2_32 : ∀ n, Even n → 8 ≤ n → n ≤ 38620000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_31 r2_32 (by norm_num) (by decide)
theorem c2_33 : ∀ n, Even n → 8 ≤ n → n ≤ 40600000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_32 r2_33 (by norm_num) (by decide)
theorem c2_34 : ∀ n, Even n → 8 ≤ n → n ≤ 42580000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_33 r2_34 (by norm_num) (by decide)
theorem c2_35 : ∀ n, Even n → 8 ≤ n → n ≤ 44560000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_34 r2_35 (by norm_num) (by decide)
theorem c2_36 : ∀ n, Even n → 8 ≤ n → n ≤ 46540000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_35 r2_36 (by norm_num) (by decide)
theorem c2_37 : ∀ n, Even n → 8 ≤ n → n ≤ 48520000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_36 r2_37 (by norm_num) (by decide)
theorem c2_38 : ∀ n, Even n → 8 ≤ n → n ≤ 50500000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_37 r2_38 (by norm_num) (by decide)
theorem c2_39 : ∀ n, Even n → 8 ≤ n → n ≤ 52480000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_38 r2_39 (by norm_num) (by decide)
theorem c2_40 : ∀ n, Even n → 8 ≤ n → n ≤ 54460000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_39 r2_40 (by norm_num) (by decide)
theorem c2_41 : ∀ n, Even n → 8 ≤ n → n ≤ 56440000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_40 r2_41 (by norm_num) (by decide)
theorem c2_42 : ∀ n, Even n → 8 ≤ n → n ≤ 58420000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_41 r2_42 (by norm_num) (by decide)
theorem c2_43 : ∀ n, Even n → 8 ≤ n → n ≤ 60400000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_42 r2_43 (by norm_num) (by decide)
theorem c2_44 : ∀ n, Even n → 8 ≤ n → n ≤ 62380000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_43 r2_44 (by norm_num) (by decide)
theorem c2_45 : ∀ n, Even n → 8 ≤ n → n ≤ 64360000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_44 r2_45 (by norm_num) (by decide)
theorem c2_46 : ∀ n, Even n → 8 ≤ n → n ≤ 66340000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_45 r2_46 (by norm_num) (by decide)
theorem c2_47 : ∀ n, Even n → 8 ≤ n → n ≤ 68320000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_46 r2_47 (by norm_num) (by decide)
theorem c2_48 : ∀ n, Even n → 8 ≤ n → n ≤ 70300000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_47 r2_48 (by norm_num) (by decide)
theorem c2_49 : ∀ n, Even n → 8 ≤ n → n ≤ 72280000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_48 r2_49 (by norm_num) (by decide)
theorem c2_50 : ∀ n, Even n → 8 ≤ n → n ≤ 74260000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_49 r2_50 (by norm_num) (by decide)
theorem c2_51 : ∀ n, Even n → 8 ≤ n → n ≤ 76240000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_50 r2_51 (by norm_num) (by decide)
theorem c2_52 : ∀ n, Even n → 8 ≤ n → n ≤ 78220000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_51 r2_52 (by norm_num) (by decide)
theorem c2_53 : ∀ n, Even n → 8 ≤ n → n ≤ 80200000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_52 r2_53 (by norm_num) (by decide)
theorem c2_54 : ∀ n, Even n → 8 ≤ n → n ≤ 82180000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_53 r2_54 (by norm_num) (by decide)
theorem c2_55 : ∀ n, Even n → 8 ≤ n → n ≤ 84160000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_54 r2_55 (by norm_num) (by decide)
theorem c2_56 : ∀ n, Even n → 8 ≤ n → n ≤ 86140000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_55 r2_56 (by norm_num) (by decide)
theorem c2_57 : ∀ n, Even n → 8 ≤ n → n ≤ 88120000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_56 r2_57 (by norm_num) (by decide)
theorem c2_58 : ∀ n, Even n → 8 ≤ n → n ≤ 90100000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_57 r2_58 (by norm_num) (by decide)
theorem c2_59 : ∀ n, Even n → 8 ≤ n → n ≤ 92080000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_58 r2_59 (by norm_num) (by decide)
theorem c2_60 : ∀ n, Even n → 8 ≤ n → n ≤ 94060000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_59 r2_60 (by norm_num) (by decide)
theorem c2_61 : ∀ n, Even n → 8 ≤ n → n ≤ 96040000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_60 r2_61 (by norm_num) (by decide)
theorem c2_62 : ∀ n, Even n → 8 ≤ n → n ≤ 98020000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_61 r2_62 (by norm_num) (by decide)
theorem c2_63 : ∀ n, Even n → 8 ≤ n → n ≤ 100000000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_62 r2_63 (by norm_num) (by decide)
theorem c2_64 : ∀ n, Even n → 8 ≤ n → n ≤ 101980000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_63 r2_64 (by norm_num) (by decide)
theorem c2_65 : ∀ n, Even n → 8 ≤ n → n ≤ 103960000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_64 r2_65 (by norm_num) (by decide)
theorem c2_66 : ∀ n, Even n → 8 ≤ n → n ≤ 105940000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_65 r2_66 (by norm_num) (by decide)
theorem c2_67 : ∀ n, Even n → 8 ≤ n → n ≤ 107920000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_66 r2_67 (by norm_num) (by decide)
theorem c2_68 : ∀ n, Even n → 8 ≤ n → n ≤ 109900000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_67 r2_68 (by norm_num) (by decide)
theorem c2_69 : ∀ n, Even n → 8 ≤ n → n ≤ 111880000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_68 r2_69 (by norm_num) (by decide)
theorem c2_70 : ∀ n, Even n → 8 ≤ n → n ≤ 113860000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_69 r2_70 (by norm_num) (by decide)
theorem c2_71 : ∀ n, Even n → 8 ≤ n → n ≤ 115840000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_70 r2_71 (by norm_num) (by decide)
theorem c2_72 : ∀ n, Even n → 8 ≤ n → n ≤ 117820000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_71 r2_72 (by norm_num) (by decide)
theorem c2_73 : ∀ n, Even n → 8 ≤ n → n ≤ 119800000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_72 r2_73 (by norm_num) (by decide)
theorem c2_74 : ∀ n, Even n → 8 ≤ n → n ≤ 121780000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_73 r2_74 (by norm_num) (by decide)
theorem c2_75 : ∀ n, Even n → 8 ≤ n → n ≤ 123760000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_74 r2_75 (by norm_num) (by decide)
theorem c2_76 : ∀ n, Even n → 8 ≤ n → n ≤ 125740000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_75 r2_76 (by norm_num) (by decide)
theorem c2_77 : ∀ n, Even n → 8 ≤ n → n ≤ 127720000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_76 r2_77 (by norm_num) (by decide)
theorem c2_78 : ∀ n, Even n → 8 ≤ n → n ≤ 129700000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_77 r2_78 (by norm_num) (by decide)
theorem c2_79 : ∀ n, Even n → 8 ≤ n → n ≤ 131680000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_78 r2_79 (by norm_num) (by decide)
theorem c2_80 : ∀ n, Even n → 8 ≤ n → n ≤ 133660000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_79 r2_80 (by norm_num) (by decide)
theorem c2_81 : ∀ n, Even n → 8 ≤ n → n ≤ 135640000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_80 r2_81 (by norm_num) (by decide)
theorem c2_82 : ∀ n, Even n → 8 ≤ n → n ≤ 137620000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_81 r2_82 (by norm_num) (by decide)
theorem c2_83 : ∀ n, Even n → 8 ≤ n → n ≤ 139600000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_82 r2_83 (by norm_num) (by decide)
theorem c2_84 : ∀ n, Even n → 8 ≤ n → n ≤ 141580000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_83 r2_84 (by norm_num) (by decide)
theorem c2_85 : ∀ n, Even n → 8 ≤ n → n ≤ 143560000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_84 r2_85 (by norm_num) (by decide)
theorem c2_86 : ∀ n, Even n → 8 ≤ n → n ≤ 145540000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_85 r2_86 (by norm_num) (by decide)
theorem c2_87 : ∀ n, Even n → 8 ≤ n → n ≤ 147520000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_86 r2_87 (by norm_num) (by decide)
theorem c2_88 : ∀ n, Even n → 8 ≤ n → n ≤ 149500000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_87 r2_88 (by norm_num) (by decide)
theorem c2_89 : ∀ n, Even n → 8 ≤ n → n ≤ 151480000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_88 r2_89 (by norm_num) (by decide)
theorem c2_90 : ∀ n, Even n → 8 ≤ n → n ≤ 153460000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_89 r2_90 (by norm_num) (by decide)
theorem c2_91 : ∀ n, Even n → 8 ≤ n → n ≤ 155440000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_90 r2_91 (by norm_num) (by decide)
theorem c2_92 : ∀ n, Even n → 8 ≤ n → n ≤ 157420000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_91 r2_92 (by norm_num) (by decide)
theorem c2_93 : ∀ n, Even n → 8 ≤ n → n ≤ 159400000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_92 r2_93 (by norm_num) (by decide)
theorem c2_94 : ∀ n, Even n → 8 ≤ n → n ≤ 161380000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_93 r2_94 (by norm_num) (by decide)
theorem c2_95 : ∀ n, Even n → 8 ≤ n → n ≤ 163360000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_94 r2_95 (by norm_num) (by decide)
theorem c2_96 : ∀ n, Even n → 8 ≤ n → n ≤ 165340000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_95 r2_96 (by norm_num) (by decide)
theorem c2_97 : ∀ n, Even n → 8 ≤ n → n ≤ 167320000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_96 r2_97 (by norm_num) (by decide)
theorem c2_98 : ∀ n, Even n → 8 ≤ n → n ≤ 169300000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_97 r2_98 (by norm_num) (by decide)
theorem c2_99 : ∀ n, Even n → 8 ≤ n → n ≤ 171280000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_98 r2_99 (by norm_num) (by decide)
theorem c2_100 : ∀ n, Even n → 8 ≤ n → n ≤ 173260000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_99 r2_100 (by norm_num) (by decide)
theorem c2_101 : ∀ n, Even n → 8 ≤ n → n ≤ 175240000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_100 r2_101 (by norm_num) (by decide)
theorem c2_102 : ∀ n, Even n → 8 ≤ n → n ≤ 177220000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_101 r2_102 (by norm_num) (by decide)
theorem c2_103 : ∀ n, Even n → 8 ≤ n → n ≤ 179200000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_102 r2_103 (by norm_num) (by decide)
theorem c2_104 : ∀ n, Even n → 8 ≤ n → n ≤ 181180000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_103 r2_104 (by norm_num) (by decide)
theorem c2_105 : ∀ n, Even n → 8 ≤ n → n ≤ 183160000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_104 r2_105 (by norm_num) (by decide)
theorem c2_106 : ∀ n, Even n → 8 ≤ n → n ≤ 185140000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_105 r2_106 (by norm_num) (by decide)
theorem c2_107 : ∀ n, Even n → 8 ≤ n → n ≤ 187120000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_106 r2_107 (by norm_num) (by decide)
theorem c2_108 : ∀ n, Even n → 8 ≤ n → n ≤ 189100000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_107 r2_108 (by norm_num) (by decide)
theorem c2_109 : ∀ n, Even n → 8 ≤ n → n ≤ 191080000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_108 r2_109 (by norm_num) (by decide)
theorem c2_110 : ∀ n, Even n → 8 ≤ n → n ≤ 193060000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_109 r2_110 (by norm_num) (by decide)
theorem c2_111 : ∀ n, Even n → 8 ≤ n → n ≤ 195040000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_110 r2_111 (by norm_num) (by decide)
theorem c2_112 : ∀ n, Even n → 8 ≤ n → n ≤ 197020000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_111 r2_112 (by norm_num) (by decide)
theorem c2_113 : ∀ n, Even n → 8 ≤ n → n ≤ 199000000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_112 r2_113 (by norm_num) (by decide)
theorem c2_114 : ∀ n, Even n → 8 ≤ n → n ≤ 200980000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_113 r2_114 (by norm_num) (by decide)
theorem c2_115 : ∀ n, Even n → 8 ≤ n → n ≤ 202960000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_114 r2_115 (by norm_num) (by decide)
theorem c2_116 : ∀ n, Even n → 8 ≤ n → n ≤ 204940000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_115 r2_116 (by norm_num) (by decide)
theorem c2_117 : ∀ n, Even n → 8 ≤ n → n ≤ 206920000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_116 r2_117 (by norm_num) (by decide)
theorem c2_118 : ∀ n, Even n → 8 ≤ n → n ≤ 208900000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_117 r2_118 (by norm_num) (by decide)
theorem c2_119 : ∀ n, Even n → 8 ≤ n → n ≤ 210880000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_118 r2_119 (by norm_num) (by decide)
theorem c2_120 : ∀ n, Even n → 8 ≤ n → n ≤ 212860000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_119 r2_120 (by norm_num) (by decide)
theorem c2_121 : ∀ n, Even n → 8 ≤ n → n ≤ 214840000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_120 r2_121 (by norm_num) (by decide)
theorem c2_122 : ∀ n, Even n → 8 ≤ n → n ≤ 216820000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_121 r2_122 (by norm_num) (by decide)
theorem c2_123 : ∀ n, Even n → 8 ≤ n → n ≤ 218800000 → (Ratio 1.25) n :=
  join (P := (Ratio 1.25)) c2_122 r2_123 (by norm_num) (by decide)
theorem mb_0 : ∀ n, Even n → 6 ≤ n → n ≤ 6 → minGB n ≤ 1321 := mono bnd_0 (by norm_num)
theorem mb_1 : ∀ n, Even n → 8 ≤ n → n ≤ 8 → minGB n ≤ 1321 := mono bnd_1 (by norm_num)
theorem mb_2 : ∀ n, Even n → 10 ≤ n → n ≤ 28 → minGB n ≤ 1321 := mono bnd_2 (by norm_num)
theorem mb_3 : ∀ n, Even n → 30 ≤ n → n ≤ 96 → minGB n ≤ 1321 := mono bnd_3 (by norm_num)
theorem mb_4 : ∀ n, Even n → 98 ≤ n → n ≤ 552 → minGB n ≤ 1321 := mono bnd_4 (by norm_num)
theorem mb_5 : ∀ n, Even n → 554 ≤ n → n ≤ 2638 → minGB n ≤ 1321 := mono bnd_5 (by norm_num)
theorem mb_6 : ∀ n, Even n → 2640 ≤ n → n ≤ 7424 → minGB n ≤ 1321 := mono bnd_6 (by norm_num)
theorem mb_7 : ∀ n, Even n → 7426 ≤ n → n ≤ 54242 → minGB n ≤ 1321 := mono bnd_7 (by norm_num)
theorem mb_8 : ∀ n, Even n → 54244 ≤ n → n ≤ 194426 → minGB n ≤ 1321 := mono bnd_8 (by norm_num)
theorem mb_9 : ∀ n, Even n → 194428 ≤ n → n ≤ 503218 → minGB n ≤ 1321 := mono bnd_9 (by norm_num)
theorem mb_10 : ∀ n, Even n → 503220 ≤ n → n ≤ 999998 → minGB n ≤ 1321 := mono bnd_10 (by norm_num)
theorem mb_11 : ∀ n, Even n → 1000000 ≤ n → n ≤ 1000000 → minGB n ≤ 1321 := mono bnd_11 (by norm_num)
theorem mb_12 : ∀ n, Even n → 1000002 ≤ n → n ≤ 2980000 → minGB n ≤ 1321 := mono bnd_12 (by norm_num)
theorem mb_13 : ∀ n, Even n → 2980002 ≤ n → n ≤ 3475000 → minGB n ≤ 1321 := mono bnd_13 (by norm_num)
theorem mb_14 : ∀ n, Even n → 3475002 ≤ n → n ≤ 3970000 → minGB n ≤ 1321 := mono bnd_14 (by norm_num)
theorem mb_15 : ∀ n, Even n → 3970002 ≤ n → n ≤ 4960000 → minGB n ≤ 1321 := mono bnd_15 (by norm_num)
theorem mb_16 : ∀ n, Even n → 4960002 ≤ n → n ≤ 6940000 → minGB n ≤ 1321 := mono bnd_16 (by norm_num)
theorem mb_17 : ∀ n, Even n → 6940002 ≤ n → n ≤ 8920000 → minGB n ≤ 1321 := mono bnd_17 (by norm_num)
theorem mb_18 : ∀ n, Even n → 8920002 ≤ n → n ≤ 10900000 → minGB n ≤ 1321 := mono bnd_18 (by norm_num)
theorem mb_19 : ∀ n, Even n → 10900002 ≤ n → n ≤ 12880000 → minGB n ≤ 1321 := mono bnd_19 (by norm_num)
theorem mb_20 : ∀ n, Even n → 12880002 ≤ n → n ≤ 14860000 → minGB n ≤ 1321 := mono bnd_20 (by norm_num)
theorem mb_21 : ∀ n, Even n → 14860002 ≤ n → n ≤ 16840000 → minGB n ≤ 1321 := mono bnd_21 (by norm_num)
theorem mb_22 : ∀ n, Even n → 16840002 ≤ n → n ≤ 18820000 → minGB n ≤ 1321 := mono bnd_22 (by norm_num)
theorem mb_23 : ∀ n, Even n → 18820002 ≤ n → n ≤ 20800000 → minGB n ≤ 1321 := mono bnd_23 (by norm_num)
theorem mb_24 : ∀ n, Even n → 20800002 ≤ n → n ≤ 22780000 → minGB n ≤ 1321 := mono bnd_24 (by norm_num)
theorem mb_25 : ∀ n, Even n → 22780002 ≤ n → n ≤ 24760000 → minGB n ≤ 1321 := mono bnd_25 (by norm_num)
theorem mb_26 : ∀ n, Even n → 24760002 ≤ n → n ≤ 26740000 → minGB n ≤ 1321 := mono bnd_26 (by norm_num)
theorem mb_27 : ∀ n, Even n → 26740002 ≤ n → n ≤ 28720000 → minGB n ≤ 1321 := mono bnd_27 (by norm_num)
theorem mb_28 : ∀ n, Even n → 28720002 ≤ n → n ≤ 30700000 → minGB n ≤ 1321 := mono bnd_28 (by norm_num)
theorem mb_29 : ∀ n, Even n → 30700002 ≤ n → n ≤ 32680000 → minGB n ≤ 1321 := mono bnd_29 (by norm_num)
theorem mb_30 : ∀ n, Even n → 32680002 ≤ n → n ≤ 34660000 → minGB n ≤ 1321 := mono bnd_30 (by norm_num)
theorem mb_31 : ∀ n, Even n → 34660002 ≤ n → n ≤ 36640000 → minGB n ≤ 1321 := mono bnd_31 (by norm_num)
theorem mb_32 : ∀ n, Even n → 36640002 ≤ n → n ≤ 38620000 → minGB n ≤ 1321 := mono bnd_32 (by norm_num)
theorem mb_33 : ∀ n, Even n → 38620002 ≤ n → n ≤ 40600000 → minGB n ≤ 1321 := mono bnd_33 (by norm_num)
theorem mb_34 : ∀ n, Even n → 40600002 ≤ n → n ≤ 42580000 → minGB n ≤ 1321 := mono bnd_34 (by norm_num)
theorem mb_35 : ∀ n, Even n → 42580002 ≤ n → n ≤ 44560000 → minGB n ≤ 1321 := mono bnd_35 (by norm_num)
theorem mb_36 : ∀ n, Even n → 44560002 ≤ n → n ≤ 46540000 → minGB n ≤ 1321 := mono bnd_36 (by norm_num)
theorem mb_37 : ∀ n, Even n → 46540002 ≤ n → n ≤ 48520000 → minGB n ≤ 1321 := mono bnd_37 (by norm_num)
theorem mb_38 : ∀ n, Even n → 48520002 ≤ n → n ≤ 50500000 → minGB n ≤ 1321 := mono bnd_38 (by norm_num)
theorem mb_39 : ∀ n, Even n → 50500002 ≤ n → n ≤ 52480000 → minGB n ≤ 1321 := mono bnd_39 (by norm_num)
theorem mb_40 : ∀ n, Even n → 52480002 ≤ n → n ≤ 54460000 → minGB n ≤ 1321 := mono bnd_40 (by norm_num)
theorem mb_41 : ∀ n, Even n → 54460002 ≤ n → n ≤ 56440000 → minGB n ≤ 1321 := mono bnd_41 (by norm_num)
theorem mb_42 : ∀ n, Even n → 56440002 ≤ n → n ≤ 58420000 → minGB n ≤ 1321 := mono bnd_42 (by norm_num)
theorem mb_43 : ∀ n, Even n → 58420002 ≤ n → n ≤ 60400000 → minGB n ≤ 1321 := mono bnd_43 (by norm_num)
theorem mb_44 : ∀ n, Even n → 60400002 ≤ n → n ≤ 62380000 → minGB n ≤ 1321 := mono bnd_44 (by norm_num)
theorem mb_45 : ∀ n, Even n → 62380002 ≤ n → n ≤ 64360000 → minGB n ≤ 1321 := mono bnd_45 (by norm_num)
theorem mb_46 : ∀ n, Even n → 64360002 ≤ n → n ≤ 66340000 → minGB n ≤ 1321 := mono bnd_46 (by norm_num)
theorem mb_47 : ∀ n, Even n → 66340002 ≤ n → n ≤ 68320000 → minGB n ≤ 1321 := mono bnd_47 (by norm_num)
theorem mb_48 : ∀ n, Even n → 68320002 ≤ n → n ≤ 70300000 → minGB n ≤ 1321 := mono bnd_48 (by norm_num)
theorem mb_49 : ∀ n, Even n → 70300002 ≤ n → n ≤ 72280000 → minGB n ≤ 1321 := mono bnd_49 (by norm_num)
theorem mb_50 : ∀ n, Even n → 72280002 ≤ n → n ≤ 74260000 → minGB n ≤ 1321 := mono bnd_50 (by norm_num)
theorem mb_51 : ∀ n, Even n → 74260002 ≤ n → n ≤ 76240000 → minGB n ≤ 1321 := mono bnd_51 (by norm_num)
theorem mb_52 : ∀ n, Even n → 76240002 ≤ n → n ≤ 78220000 → minGB n ≤ 1321 := mono bnd_52 (by norm_num)
theorem mb_53 : ∀ n, Even n → 78220002 ≤ n → n ≤ 80200000 → minGB n ≤ 1321 := mono bnd_53 (by norm_num)
theorem mb_54 : ∀ n, Even n → 80200002 ≤ n → n ≤ 82180000 → minGB n ≤ 1321 := mono bnd_54 (by norm_num)
theorem mb_55 : ∀ n, Even n → 82180002 ≤ n → n ≤ 84160000 → minGB n ≤ 1321 := mono bnd_55 (by norm_num)
theorem mb_56 : ∀ n, Even n → 84160002 ≤ n → n ≤ 86140000 → minGB n ≤ 1321 := mono bnd_56 (by norm_num)
theorem mb_57 : ∀ n, Even n → 86140002 ≤ n → n ≤ 88120000 → minGB n ≤ 1321 := mono bnd_57 (by norm_num)
theorem mb_58 : ∀ n, Even n → 88120002 ≤ n → n ≤ 90100000 → minGB n ≤ 1321 := mono bnd_58 (by norm_num)
theorem mb_59 : ∀ n, Even n → 90100002 ≤ n → n ≤ 92080000 → minGB n ≤ 1321 := mono bnd_59 (by norm_num)
theorem mb_60 : ∀ n, Even n → 92080002 ≤ n → n ≤ 94060000 → minGB n ≤ 1321 := mono bnd_60 (by norm_num)
theorem mb_61 : ∀ n, Even n → 94060002 ≤ n → n ≤ 96040000 → minGB n ≤ 1321 := mono bnd_61 (by norm_num)
theorem mb_62 : ∀ n, Even n → 96040002 ≤ n → n ≤ 98020000 → minGB n ≤ 1321 := mono bnd_62 (by norm_num)
theorem mb_63 : ∀ n, Even n → 98020002 ≤ n → n ≤ 100000000 → minGB n ≤ 1321 := mono bnd_63 (by norm_num)
theorem mb_64 : ∀ n, Even n → 100000002 ≤ n → n ≤ 101980000 → minGB n ≤ 1321 := mono bnd_64 (by norm_num)
theorem mb_65 : ∀ n, Even n → 101980002 ≤ n → n ≤ 103960000 → minGB n ≤ 1321 := mono bnd_65 (by norm_num)
theorem mb_66 : ∀ n, Even n → 103960002 ≤ n → n ≤ 105940000 → minGB n ≤ 1321 := mono bnd_66 (by norm_num)
theorem mb_67 : ∀ n, Even n → 105940002 ≤ n → n ≤ 107920000 → minGB n ≤ 1321 := mono bnd_67 (by norm_num)
theorem mb_68 : ∀ n, Even n → 107920002 ≤ n → n ≤ 109900000 → minGB n ≤ 1321 := mono bnd_68 (by norm_num)
theorem mb_69 : ∀ n, Even n → 109900002 ≤ n → n ≤ 111880000 → minGB n ≤ 1321 := mono bnd_69 (by norm_num)
theorem mb_70 : ∀ n, Even n → 111880002 ≤ n → n ≤ 113860000 → minGB n ≤ 1321 := mono bnd_70 (by norm_num)
theorem mb_71 : ∀ n, Even n → 113860002 ≤ n → n ≤ 115840000 → minGB n ≤ 1321 := mono bnd_71 (by norm_num)
theorem mb_72 : ∀ n, Even n → 115840002 ≤ n → n ≤ 117820000 → minGB n ≤ 1321 := mono bnd_72 (by norm_num)
theorem mb_73 : ∀ n, Even n → 117820002 ≤ n → n ≤ 119800000 → minGB n ≤ 1321 := mono bnd_73 (by norm_num)
theorem mb_74 : ∀ n, Even n → 119800002 ≤ n → n ≤ 121780000 → minGB n ≤ 1321 := mono bnd_74 (by norm_num)
theorem mb_75 : ∀ n, Even n → 121780002 ≤ n → n ≤ 123760000 → minGB n ≤ 1321 := mono bnd_75 (by norm_num)
theorem mb_76 : ∀ n, Even n → 123760002 ≤ n → n ≤ 125740000 → minGB n ≤ 1321 := mono bnd_76 (by norm_num)
theorem mb_77 : ∀ n, Even n → 125740002 ≤ n → n ≤ 127720000 → minGB n ≤ 1321 := mono bnd_77 (by norm_num)
theorem mb_78 : ∀ n, Even n → 127720002 ≤ n → n ≤ 129700000 → minGB n ≤ 1321 := mono bnd_78 (by norm_num)
theorem mb_79 : ∀ n, Even n → 129700002 ≤ n → n ≤ 131680000 → minGB n ≤ 1321 := mono bnd_79 (by norm_num)
theorem mb_80 : ∀ n, Even n → 131680002 ≤ n → n ≤ 133660000 → minGB n ≤ 1321 := mono bnd_80 (by norm_num)
theorem mb_81 : ∀ n, Even n → 133660002 ≤ n → n ≤ 135640000 → minGB n ≤ 1321 := mono bnd_81 (by norm_num)
theorem mb_82 : ∀ n, Even n → 135640002 ≤ n → n ≤ 137620000 → minGB n ≤ 1321 := mono bnd_82 (by norm_num)
theorem mb_83 : ∀ n, Even n → 137620002 ≤ n → n ≤ 139600000 → minGB n ≤ 1321 := mono bnd_83 (by norm_num)
theorem mb_84 : ∀ n, Even n → 139600002 ≤ n → n ≤ 141580000 → minGB n ≤ 1321 := mono bnd_84 (by norm_num)
theorem mb_85 : ∀ n, Even n → 141580002 ≤ n → n ≤ 143560000 → minGB n ≤ 1321 := mono bnd_85 (by norm_num)
theorem mb_86 : ∀ n, Even n → 143560002 ≤ n → n ≤ 145540000 → minGB n ≤ 1321 := mono bnd_86 (by norm_num)
theorem mb_87 : ∀ n, Even n → 145540002 ≤ n → n ≤ 147520000 → minGB n ≤ 1321 := mono bnd_87 (by norm_num)
theorem mb_88 : ∀ n, Even n → 147520002 ≤ n → n ≤ 149500000 → minGB n ≤ 1321 := mono bnd_88 (by norm_num)
theorem mb_89 : ∀ n, Even n → 149500002 ≤ n → n ≤ 151480000 → minGB n ≤ 1321 := mono bnd_89 (by norm_num)
theorem mb_90 : ∀ n, Even n → 151480002 ≤ n → n ≤ 153460000 → minGB n ≤ 1321 := mono bnd_90 (by norm_num)
theorem mb_91 : ∀ n, Even n → 153460002 ≤ n → n ≤ 155440000 → minGB n ≤ 1321 := mono bnd_91 (by norm_num)
theorem mb_92 : ∀ n, Even n → 155440002 ≤ n → n ≤ 157420000 → minGB n ≤ 1321 := mono bnd_92 (by norm_num)
theorem mb_93 : ∀ n, Even n → 157420002 ≤ n → n ≤ 159400000 → minGB n ≤ 1321 := mono bnd_93 (by norm_num)
theorem mb_94 : ∀ n, Even n → 159400002 ≤ n → n ≤ 161380000 → minGB n ≤ 1321 := mono bnd_94 (by norm_num)
theorem mb_95 : ∀ n, Even n → 161380002 ≤ n → n ≤ 163360000 → minGB n ≤ 1321 := mono bnd_95 (by norm_num)
theorem mb_96 : ∀ n, Even n → 163360002 ≤ n → n ≤ 165340000 → minGB n ≤ 1321 := mono bnd_96 (by norm_num)
theorem mb_97 : ∀ n, Even n → 165340002 ≤ n → n ≤ 167320000 → minGB n ≤ 1321 := mono bnd_97 (by norm_num)
theorem mb_98 : ∀ n, Even n → 167320002 ≤ n → n ≤ 169300000 → minGB n ≤ 1321 := mono bnd_98 (by norm_num)
theorem mb_99 : ∀ n, Even n → 169300002 ≤ n → n ≤ 171280000 → minGB n ≤ 1321 := mono bnd_99 (by norm_num)
theorem mb_100 : ∀ n, Even n → 171280002 ≤ n → n ≤ 173260000 → minGB n ≤ 1321 := mono bnd_100 (by norm_num)
theorem mb_101 : ∀ n, Even n → 173260002 ≤ n → n ≤ 175240000 → minGB n ≤ 1321 := mono bnd_101 (by norm_num)
theorem mb_102 : ∀ n, Even n → 175240002 ≤ n → n ≤ 177220000 → minGB n ≤ 1321 := mono bnd_102 (by norm_num)
theorem mb_103 : ∀ n, Even n → 177220002 ≤ n → n ≤ 179200000 → minGB n ≤ 1321 := mono bnd_103 (by norm_num)
theorem mb_104 : ∀ n, Even n → 179200002 ≤ n → n ≤ 181180000 → minGB n ≤ 1321 := mono bnd_104 (by norm_num)
theorem mb_105 : ∀ n, Even n → 181180002 ≤ n → n ≤ 183160000 → minGB n ≤ 1321 := mono bnd_105 (by norm_num)
theorem mb_106 : ∀ n, Even n → 183160002 ≤ n → n ≤ 185140000 → minGB n ≤ 1321 := mono bnd_106 (by norm_num)
theorem mb_107 : ∀ n, Even n → 185140002 ≤ n → n ≤ 187120000 → minGB n ≤ 1321 := mono bnd_107 (by norm_num)
theorem mb_108 : ∀ n, Even n → 187120002 ≤ n → n ≤ 189100000 → minGB n ≤ 1321 := mono bnd_108 (by norm_num)
theorem mb_109 : ∀ n, Even n → 189100002 ≤ n → n ≤ 191080000 → minGB n ≤ 1321 := mono bnd_109 (by norm_num)
theorem mb_110 : ∀ n, Even n → 191080002 ≤ n → n ≤ 193060000 → minGB n ≤ 1321 := mono bnd_110 (by norm_num)
theorem mb_111 : ∀ n, Even n → 193060002 ≤ n → n ≤ 195040000 → minGB n ≤ 1321 := mono bnd_111 (by norm_num)
theorem mb_112 : ∀ n, Even n → 195040002 ≤ n → n ≤ 197020000 → minGB n ≤ 1321 := mono bnd_112 (by norm_num)
theorem mb_113 : ∀ n, Even n → 197020002 ≤ n → n ≤ 199000000 → minGB n ≤ 1321 := mono bnd_113 (by norm_num)
theorem mb_114 : ∀ n, Even n → 199000002 ≤ n → n ≤ 200980000 → minGB n ≤ 1321 := mono bnd_114 (by norm_num)
theorem mb_115 : ∀ n, Even n → 200980002 ≤ n → n ≤ 202960000 → minGB n ≤ 1321 := mono bnd_115 (by norm_num)
theorem mb_116 : ∀ n, Even n → 202960002 ≤ n → n ≤ 204940000 → minGB n ≤ 1321 := mono bnd_116 (by norm_num)
theorem mb_117 : ∀ n, Even n → 204940002 ≤ n → n ≤ 206920000 → minGB n ≤ 1321 := mono bnd_117 (by norm_num)
theorem mb_118 : ∀ n, Even n → 206920002 ≤ n → n ≤ 208900000 → minGB n ≤ 1321 := mono bnd_118 (by norm_num)
theorem mb_119 : ∀ n, Even n → 208900002 ≤ n → n ≤ 210880000 → minGB n ≤ 1321 := mono bnd_119 (by norm_num)
theorem mb_120 : ∀ n, Even n → 210880002 ≤ n → n ≤ 212860000 → minGB n ≤ 1321 := mono bnd_120 (by norm_num)
theorem mb_121 : ∀ n, Even n → 212860002 ≤ n → n ≤ 214840000 → minGB n ≤ 1321 := mono bnd_121 (by norm_num)
theorem mb_122 : ∀ n, Even n → 214840002 ≤ n → n ≤ 216820000 → minGB n ≤ 1321 := mono bnd_122 (by norm_num)
theorem mb_123 : ∀ n, Even n → 216820002 ≤ n → n ≤ 218800000 → minGB n ≤ 1321 := mono bnd_123 (by norm_num)
theorem c3_0 : ∀ n, Even n → 6 ≤ n → n ≤ 6 → (fun n => minGB n ≤ 1321) n := mb_0
theorem c3_1 : ∀ n, Even n → 6 ≤ n → n ≤ 8 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_0 mb_1 (by norm_num) (by decide)
theorem c3_2 : ∀ n, Even n → 6 ≤ n → n ≤ 28 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_1 mb_2 (by norm_num) (by decide)
theorem c3_3 : ∀ n, Even n → 6 ≤ n → n ≤ 96 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_2 mb_3 (by norm_num) (by decide)
theorem c3_4 : ∀ n, Even n → 6 ≤ n → n ≤ 552 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_3 mb_4 (by norm_num) (by decide)
theorem c3_5 : ∀ n, Even n → 6 ≤ n → n ≤ 2638 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_4 mb_5 (by norm_num) (by decide)
theorem c3_6 : ∀ n, Even n → 6 ≤ n → n ≤ 7424 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_5 mb_6 (by norm_num) (by decide)
theorem c3_7 : ∀ n, Even n → 6 ≤ n → n ≤ 54242 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_6 mb_7 (by norm_num) (by decide)
theorem c3_8 : ∀ n, Even n → 6 ≤ n → n ≤ 194426 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_7 mb_8 (by norm_num) (by decide)
theorem c3_9 : ∀ n, Even n → 6 ≤ n → n ≤ 503218 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_8 mb_9 (by norm_num) (by decide)
theorem c3_10 : ∀ n, Even n → 6 ≤ n → n ≤ 999998 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_9 mb_10 (by norm_num) (by decide)
theorem c3_11 : ∀ n, Even n → 6 ≤ n → n ≤ 1000000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_10 mb_11 (by norm_num) (by decide)
theorem c3_12 : ∀ n, Even n → 6 ≤ n → n ≤ 2980000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_11 mb_12 (by norm_num) (by decide)
theorem c3_13 : ∀ n, Even n → 6 ≤ n → n ≤ 3475000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_12 mb_13 (by norm_num) (by decide)
theorem c3_14 : ∀ n, Even n → 6 ≤ n → n ≤ 3970000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_13 mb_14 (by norm_num) (by decide)
theorem c3_15 : ∀ n, Even n → 6 ≤ n → n ≤ 4960000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_14 mb_15 (by norm_num) (by decide)
theorem c3_16 : ∀ n, Even n → 6 ≤ n → n ≤ 6940000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_15 mb_16 (by norm_num) (by decide)
theorem c3_17 : ∀ n, Even n → 6 ≤ n → n ≤ 8920000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_16 mb_17 (by norm_num) (by decide)
theorem c3_18 : ∀ n, Even n → 6 ≤ n → n ≤ 10900000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_17 mb_18 (by norm_num) (by decide)
theorem c3_19 : ∀ n, Even n → 6 ≤ n → n ≤ 12880000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_18 mb_19 (by norm_num) (by decide)
theorem c3_20 : ∀ n, Even n → 6 ≤ n → n ≤ 14860000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_19 mb_20 (by norm_num) (by decide)
theorem c3_21 : ∀ n, Even n → 6 ≤ n → n ≤ 16840000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_20 mb_21 (by norm_num) (by decide)
theorem c3_22 : ∀ n, Even n → 6 ≤ n → n ≤ 18820000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_21 mb_22 (by norm_num) (by decide)
theorem c3_23 : ∀ n, Even n → 6 ≤ n → n ≤ 20800000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_22 mb_23 (by norm_num) (by decide)
theorem c3_24 : ∀ n, Even n → 6 ≤ n → n ≤ 22780000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_23 mb_24 (by norm_num) (by decide)
theorem c3_25 : ∀ n, Even n → 6 ≤ n → n ≤ 24760000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_24 mb_25 (by norm_num) (by decide)
theorem c3_26 : ∀ n, Even n → 6 ≤ n → n ≤ 26740000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_25 mb_26 (by norm_num) (by decide)
theorem c3_27 : ∀ n, Even n → 6 ≤ n → n ≤ 28720000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_26 mb_27 (by norm_num) (by decide)
theorem c3_28 : ∀ n, Even n → 6 ≤ n → n ≤ 30700000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_27 mb_28 (by norm_num) (by decide)
theorem c3_29 : ∀ n, Even n → 6 ≤ n → n ≤ 32680000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_28 mb_29 (by norm_num) (by decide)
theorem c3_30 : ∀ n, Even n → 6 ≤ n → n ≤ 34660000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_29 mb_30 (by norm_num) (by decide)
theorem c3_31 : ∀ n, Even n → 6 ≤ n → n ≤ 36640000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_30 mb_31 (by norm_num) (by decide)
theorem c3_32 : ∀ n, Even n → 6 ≤ n → n ≤ 38620000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_31 mb_32 (by norm_num) (by decide)
theorem c3_33 : ∀ n, Even n → 6 ≤ n → n ≤ 40600000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_32 mb_33 (by norm_num) (by decide)
theorem c3_34 : ∀ n, Even n → 6 ≤ n → n ≤ 42580000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_33 mb_34 (by norm_num) (by decide)
theorem c3_35 : ∀ n, Even n → 6 ≤ n → n ≤ 44560000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_34 mb_35 (by norm_num) (by decide)
theorem c3_36 : ∀ n, Even n → 6 ≤ n → n ≤ 46540000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_35 mb_36 (by norm_num) (by decide)
theorem c3_37 : ∀ n, Even n → 6 ≤ n → n ≤ 48520000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_36 mb_37 (by norm_num) (by decide)
theorem c3_38 : ∀ n, Even n → 6 ≤ n → n ≤ 50500000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_37 mb_38 (by norm_num) (by decide)
theorem c3_39 : ∀ n, Even n → 6 ≤ n → n ≤ 52480000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_38 mb_39 (by norm_num) (by decide)
theorem c3_40 : ∀ n, Even n → 6 ≤ n → n ≤ 54460000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_39 mb_40 (by norm_num) (by decide)
theorem c3_41 : ∀ n, Even n → 6 ≤ n → n ≤ 56440000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_40 mb_41 (by norm_num) (by decide)
theorem c3_42 : ∀ n, Even n → 6 ≤ n → n ≤ 58420000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_41 mb_42 (by norm_num) (by decide)
theorem c3_43 : ∀ n, Even n → 6 ≤ n → n ≤ 60400000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_42 mb_43 (by norm_num) (by decide)
theorem c3_44 : ∀ n, Even n → 6 ≤ n → n ≤ 62380000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_43 mb_44 (by norm_num) (by decide)
theorem c3_45 : ∀ n, Even n → 6 ≤ n → n ≤ 64360000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_44 mb_45 (by norm_num) (by decide)
theorem c3_46 : ∀ n, Even n → 6 ≤ n → n ≤ 66340000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_45 mb_46 (by norm_num) (by decide)
theorem c3_47 : ∀ n, Even n → 6 ≤ n → n ≤ 68320000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_46 mb_47 (by norm_num) (by decide)
theorem c3_48 : ∀ n, Even n → 6 ≤ n → n ≤ 70300000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_47 mb_48 (by norm_num) (by decide)
theorem c3_49 : ∀ n, Even n → 6 ≤ n → n ≤ 72280000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_48 mb_49 (by norm_num) (by decide)
theorem c3_50 : ∀ n, Even n → 6 ≤ n → n ≤ 74260000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_49 mb_50 (by norm_num) (by decide)
theorem c3_51 : ∀ n, Even n → 6 ≤ n → n ≤ 76240000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_50 mb_51 (by norm_num) (by decide)
theorem c3_52 : ∀ n, Even n → 6 ≤ n → n ≤ 78220000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_51 mb_52 (by norm_num) (by decide)
theorem c3_53 : ∀ n, Even n → 6 ≤ n → n ≤ 80200000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_52 mb_53 (by norm_num) (by decide)
theorem c3_54 : ∀ n, Even n → 6 ≤ n → n ≤ 82180000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_53 mb_54 (by norm_num) (by decide)
theorem c3_55 : ∀ n, Even n → 6 ≤ n → n ≤ 84160000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_54 mb_55 (by norm_num) (by decide)
theorem c3_56 : ∀ n, Even n → 6 ≤ n → n ≤ 86140000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_55 mb_56 (by norm_num) (by decide)
theorem c3_57 : ∀ n, Even n → 6 ≤ n → n ≤ 88120000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_56 mb_57 (by norm_num) (by decide)
theorem c3_58 : ∀ n, Even n → 6 ≤ n → n ≤ 90100000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_57 mb_58 (by norm_num) (by decide)
theorem c3_59 : ∀ n, Even n → 6 ≤ n → n ≤ 92080000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_58 mb_59 (by norm_num) (by decide)
theorem c3_60 : ∀ n, Even n → 6 ≤ n → n ≤ 94060000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_59 mb_60 (by norm_num) (by decide)
theorem c3_61 : ∀ n, Even n → 6 ≤ n → n ≤ 96040000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_60 mb_61 (by norm_num) (by decide)
theorem c3_62 : ∀ n, Even n → 6 ≤ n → n ≤ 98020000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_61 mb_62 (by norm_num) (by decide)
theorem c3_63 : ∀ n, Even n → 6 ≤ n → n ≤ 100000000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_62 mb_63 (by norm_num) (by decide)
theorem c3_64 : ∀ n, Even n → 6 ≤ n → n ≤ 101980000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_63 mb_64 (by norm_num) (by decide)
theorem c3_65 : ∀ n, Even n → 6 ≤ n → n ≤ 103960000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_64 mb_65 (by norm_num) (by decide)
theorem c3_66 : ∀ n, Even n → 6 ≤ n → n ≤ 105940000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_65 mb_66 (by norm_num) (by decide)
theorem c3_67 : ∀ n, Even n → 6 ≤ n → n ≤ 107920000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_66 mb_67 (by norm_num) (by decide)
theorem c3_68 : ∀ n, Even n → 6 ≤ n → n ≤ 109900000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_67 mb_68 (by norm_num) (by decide)
theorem c3_69 : ∀ n, Even n → 6 ≤ n → n ≤ 111880000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_68 mb_69 (by norm_num) (by decide)
theorem c3_70 : ∀ n, Even n → 6 ≤ n → n ≤ 113860000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_69 mb_70 (by norm_num) (by decide)
theorem c3_71 : ∀ n, Even n → 6 ≤ n → n ≤ 115840000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_70 mb_71 (by norm_num) (by decide)
theorem c3_72 : ∀ n, Even n → 6 ≤ n → n ≤ 117820000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_71 mb_72 (by norm_num) (by decide)
theorem c3_73 : ∀ n, Even n → 6 ≤ n → n ≤ 119800000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_72 mb_73 (by norm_num) (by decide)
theorem c3_74 : ∀ n, Even n → 6 ≤ n → n ≤ 121780000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_73 mb_74 (by norm_num) (by decide)
theorem c3_75 : ∀ n, Even n → 6 ≤ n → n ≤ 123760000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_74 mb_75 (by norm_num) (by decide)
theorem c3_76 : ∀ n, Even n → 6 ≤ n → n ≤ 125740000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_75 mb_76 (by norm_num) (by decide)
theorem c3_77 : ∀ n, Even n → 6 ≤ n → n ≤ 127720000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_76 mb_77 (by norm_num) (by decide)
theorem c3_78 : ∀ n, Even n → 6 ≤ n → n ≤ 129700000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_77 mb_78 (by norm_num) (by decide)
theorem c3_79 : ∀ n, Even n → 6 ≤ n → n ≤ 131680000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_78 mb_79 (by norm_num) (by decide)
theorem c3_80 : ∀ n, Even n → 6 ≤ n → n ≤ 133660000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_79 mb_80 (by norm_num) (by decide)
theorem c3_81 : ∀ n, Even n → 6 ≤ n → n ≤ 135640000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_80 mb_81 (by norm_num) (by decide)
theorem c3_82 : ∀ n, Even n → 6 ≤ n → n ≤ 137620000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_81 mb_82 (by norm_num) (by decide)
theorem c3_83 : ∀ n, Even n → 6 ≤ n → n ≤ 139600000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_82 mb_83 (by norm_num) (by decide)
theorem c3_84 : ∀ n, Even n → 6 ≤ n → n ≤ 141580000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_83 mb_84 (by norm_num) (by decide)
theorem c3_85 : ∀ n, Even n → 6 ≤ n → n ≤ 143560000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_84 mb_85 (by norm_num) (by decide)
theorem c3_86 : ∀ n, Even n → 6 ≤ n → n ≤ 145540000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_85 mb_86 (by norm_num) (by decide)
theorem c3_87 : ∀ n, Even n → 6 ≤ n → n ≤ 147520000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_86 mb_87 (by norm_num) (by decide)
theorem c3_88 : ∀ n, Even n → 6 ≤ n → n ≤ 149500000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_87 mb_88 (by norm_num) (by decide)
theorem c3_89 : ∀ n, Even n → 6 ≤ n → n ≤ 151480000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_88 mb_89 (by norm_num) (by decide)
theorem c3_90 : ∀ n, Even n → 6 ≤ n → n ≤ 153460000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_89 mb_90 (by norm_num) (by decide)
theorem c3_91 : ∀ n, Even n → 6 ≤ n → n ≤ 155440000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_90 mb_91 (by norm_num) (by decide)
theorem c3_92 : ∀ n, Even n → 6 ≤ n → n ≤ 157420000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_91 mb_92 (by norm_num) (by decide)
theorem c3_93 : ∀ n, Even n → 6 ≤ n → n ≤ 159400000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_92 mb_93 (by norm_num) (by decide)
theorem c3_94 : ∀ n, Even n → 6 ≤ n → n ≤ 161380000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_93 mb_94 (by norm_num) (by decide)
theorem c3_95 : ∀ n, Even n → 6 ≤ n → n ≤ 163360000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_94 mb_95 (by norm_num) (by decide)
theorem c3_96 : ∀ n, Even n → 6 ≤ n → n ≤ 165340000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_95 mb_96 (by norm_num) (by decide)
theorem c3_97 : ∀ n, Even n → 6 ≤ n → n ≤ 167320000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_96 mb_97 (by norm_num) (by decide)
theorem c3_98 : ∀ n, Even n → 6 ≤ n → n ≤ 169300000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_97 mb_98 (by norm_num) (by decide)
theorem c3_99 : ∀ n, Even n → 6 ≤ n → n ≤ 171280000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_98 mb_99 (by norm_num) (by decide)
theorem c3_100 : ∀ n, Even n → 6 ≤ n → n ≤ 173260000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_99 mb_100 (by norm_num) (by decide)
theorem c3_101 : ∀ n, Even n → 6 ≤ n → n ≤ 175240000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_100 mb_101 (by norm_num) (by decide)
theorem c3_102 : ∀ n, Even n → 6 ≤ n → n ≤ 177220000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_101 mb_102 (by norm_num) (by decide)
theorem c3_103 : ∀ n, Even n → 6 ≤ n → n ≤ 179200000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_102 mb_103 (by norm_num) (by decide)
theorem c3_104 : ∀ n, Even n → 6 ≤ n → n ≤ 181180000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_103 mb_104 (by norm_num) (by decide)
theorem c3_105 : ∀ n, Even n → 6 ≤ n → n ≤ 183160000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_104 mb_105 (by norm_num) (by decide)
theorem c3_106 : ∀ n, Even n → 6 ≤ n → n ≤ 185140000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_105 mb_106 (by norm_num) (by decide)
theorem c3_107 : ∀ n, Even n → 6 ≤ n → n ≤ 187120000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_106 mb_107 (by norm_num) (by decide)
theorem c3_108 : ∀ n, Even n → 6 ≤ n → n ≤ 189100000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_107 mb_108 (by norm_num) (by decide)
theorem c3_109 : ∀ n, Even n → 6 ≤ n → n ≤ 191080000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_108 mb_109 (by norm_num) (by decide)
theorem c3_110 : ∀ n, Even n → 6 ≤ n → n ≤ 193060000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_109 mb_110 (by norm_num) (by decide)
theorem c3_111 : ∀ n, Even n → 6 ≤ n → n ≤ 195040000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_110 mb_111 (by norm_num) (by decide)
theorem c3_112 : ∀ n, Even n → 6 ≤ n → n ≤ 197020000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_111 mb_112 (by norm_num) (by decide)
theorem c3_113 : ∀ n, Even n → 6 ≤ n → n ≤ 199000000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_112 mb_113 (by norm_num) (by decide)
theorem c3_114 : ∀ n, Even n → 6 ≤ n → n ≤ 200980000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_113 mb_114 (by norm_num) (by decide)
theorem c3_115 : ∀ n, Even n → 6 ≤ n → n ≤ 202960000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_114 mb_115 (by norm_num) (by decide)
theorem c3_116 : ∀ n, Even n → 6 ≤ n → n ≤ 204940000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_115 mb_116 (by norm_num) (by decide)
theorem c3_117 : ∀ n, Even n → 6 ≤ n → n ≤ 206920000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_116 mb_117 (by norm_num) (by decide)
theorem c3_118 : ∀ n, Even n → 6 ≤ n → n ≤ 208900000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_117 mb_118 (by norm_num) (by decide)
theorem c3_119 : ∀ n, Even n → 6 ≤ n → n ≤ 210880000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_118 mb_119 (by norm_num) (by decide)
theorem c3_120 : ∀ n, Even n → 6 ≤ n → n ≤ 212860000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_119 mb_120 (by norm_num) (by decide)
theorem c3_121 : ∀ n, Even n → 6 ≤ n → n ≤ 214840000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_120 mb_121 (by norm_num) (by decide)
theorem c3_122 : ∀ n, Even n → 6 ≤ n → n ≤ 216820000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_121 mb_122 (by norm_num) (by decide)
theorem c3_123 : ∀ n, Even n → 6 ≤ n → n ≤ 218800000 → (fun n => minGB n ≤ 1321) n :=
  join (P := (fun n => minGB n ≤ 1321)) c3_122 mb_123 (by norm_num) (by decide)

/-- **P0042 ratio claim on the lab's range.** For every even n with 6 ≤ n ≤ 218800000,
p(n) < 1.603 log² n log log n, the constant of Granville, van de Lune, te Riele. -/
theorem gvltr_ratio_upTo : ∀ n : ℕ, Even n → 6 ≤ n → n ≤ 218800000 →
    (minGB n : ℝ) < 1.603 * Real.log n ^ 2 * Real.log (Real.log n) := c1_123

/-- Sharper on the same range from n = 8: p(n) < 1.25 log² n log log n. The largest ratio
in the range is about 1.2350, at n = 187852862 with p(n) = 1321, a Python computation. -/
theorem ratio125_upTo : ∀ n : ℕ, Even n → 8 ≤ n → n ≤ 218800000 →
    (minGB n : ℝ) < 1.25 * Real.log n ^ 2 * Real.log (Real.log n) := c2_123

/-- **P0042 Table 3 claim on the lab's range**, sharper: minGB n ≤ 1321 for even n from 4 to 218800000. -/
theorem gvltr_max_upTo : ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 218800000 → minGB n ≤ 1321 := by
  intro n hn h4 hN
  by_cases h : n = 4
  · subst h
    exact le_trans (minGB_le_of Nat.prime_two (by norm_num)) (by norm_num)
  · apply c3_123 n hn _ hN
    obtain ⟨k, hk⟩ := hn
    omega

theorem gvltr_max_2029_upTo : ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 218800000 → minGB n ≤ 2029 :=
  fun n hn h4 hN => le_trans (gvltr_max_upTo n hn h4 hN) (by norm_num)

end LeanLab.GvLtR1989
