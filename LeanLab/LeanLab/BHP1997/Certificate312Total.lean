/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_00
import LeanLab.BHP1997.Certificate312Rows_01
import LeanLab.BHP1997.Certificate312Rows_02
import LeanLab.BHP1997.Certificate312Rows_03
import LeanLab.BHP1997.Certificate312Rows_04
import LeanLab.BHP1997.Certificate312Rows_05
import LeanLab.BHP1997.Certificate312Rows_06
import LeanLab.BHP1997.Certificate312Rows_07
import LeanLab.BHP1997.Certificate312Rows_08
import LeanLab.BHP1997.Certificate312Rows_09
import LeanLab.BHP1997.Certificate312Rows_10
import LeanLab.BHP1997.Certificate312Rows_11
import LeanLab.BHP1997.Certificate312Rows_12
import LeanLab.BHP1997.Certificate312Rows_13
import LeanLab.BHP1997.Certificate312Rows_14
import LeanLab.BHP1997.Certificate312Rows_15
import LeanLab.BHP1997.Certificate312Rows_16
import LeanLab.BHP1997.Certificate312Rows_17
import LeanLab.BHP1997.Certificate312Rows_18
import LeanLab.BHP1997.Certificate312Rows_19
import LeanLab.BHP1997.Certificate312Rows_20
import LeanLab.BHP1997.Certificate312Rows_21
import LeanLab.BHP1997.Certificate312Rows_22
import LeanLab.BHP1997.Certificate312Rows_23
import LeanLab.BHP1997.Certificate312Rows_24
import LeanLab.BHP1997.Certificate312Rows_25
import LeanLab.BHP1997.Certificate312Rows_26
import LeanLab.BHP1997.Certificate312Rows_27
import LeanLab.BHP1997.Certificate312Rows_28
import LeanLab.BHP1997.Certificate312Rows_29
import LeanLab.BHP1997.Certificate312Rows_30
import LeanLab.BHP1997.Certificate312Rows_31
import LeanLab.BHP1997.Certificate312Rows_32
import LeanLab.BHP1997.Certificate312Rows_33
import LeanLab.BHP1997.Certificate312Rows_34
import LeanLab.BHP1997.Certificate312Rows_35
import LeanLab.BHP1997.Certificate312Rows_36
import LeanLab.BHP1997.Certificate312Rows_37
import LeanLab.BHP1997.Certificate312Rows_38
import LeanLab.BHP1997.Certificate312Rows_39
import LeanLab.BHP1997.Certificate312Rows_40
import LeanLab.BHP1997.Certificate312Rows_41
import LeanLab.BHP1997.Certificate312Rows_42
import LeanLab.BHP1997.Certificate312Rows_43
import LeanLab.BHP1997.Certificate312Rows_44
import LeanLab.BHP1997.Certificate312Rows_45
import LeanLab.BHP1997.Certificate312Rows_46
import LeanLab.BHP1997.Certificate312Rows_47
import LeanLab.BHP1997.Certificate312Rows_48
import LeanLab.BHP1997.Certificate312Rows_49
import LeanLab.BHP1997.Certificate312Rows_50
import LeanLab.BHP1997.Certificate312Rows_51
import LeanLab.BHP1997.Certificate312Rows_52
import LeanLab.BHP1997.Certificate312Rows_53
import LeanLab.BHP1997.Certificate312Rows_54
import LeanLab.BHP1997.Certificate312Rows_55
import LeanLab.BHP1997.Certificate312Rows_56
import LeanLab.BHP1997.Certificate312Rows_57
import LeanLab.BHP1997.Certificate312Rows_58
import LeanLab.BHP1997.Certificate312Rows_59
import LeanLab.BHP1997.Certificate312Rows_60
import LeanLab.BHP1997.Certificate312Rows_61
import LeanLab.BHP1997.Certificate312Rows_62
import LeanLab.BHP1997.Certificate312Rows_63

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Page 51. Assemble the exact unchanged E2 grid total from bounded row blocks. -/
theorem lower_two_grid_total : lowerTwoGridTotal = 1132433915806 := by
  let row : ℕ → ℕ := fun i => ∑ j ∈ Finset.range 4096, lowerTwoGridWeight i j
  change (∑ i ∈ Finset.range 4096, row i) = 1132433915806
  have h0 : (∑ i ∈ Finset.range 0, row i) = 0 := by simp only [Finset.sum_range_zero]
  have h64 : (∑ i ∈ Finset.range 64, row i) = 0 := by
    calc
      _ = (∑ i ∈ Finset.range 0, row i) + (∑ i ∈ Finset.range 64, row (0+i)) :=
        Finset.sum_range_add row 0 64
      _ = 0 + 0 := congrArg₂ (fun a b : ℕ => a+b) h0 lowerTwo_rows312_00
      _ = 0 := by decide
  have h128 : (∑ i ∈ Finset.range 128, row i) = 0 := by
    calc
      _ = (∑ i ∈ Finset.range 64, row i) + (∑ i ∈ Finset.range 64, row (64+i)) :=
        Finset.sum_range_add row 64 64
      _ = 0 + 0 := congrArg₂ (fun a b : ℕ => a+b) h64 lowerTwo_rows312_01
      _ = 0 := by decide
  have h192 : (∑ i ∈ Finset.range 192, row i) = 0 := by
    calc
      _ = (∑ i ∈ Finset.range 128, row i) + (∑ i ∈ Finset.range 64, row (128+i)) :=
        Finset.sum_range_add row 128 64
      _ = 0 + 0 := congrArg₂ (fun a b : ℕ => a+b) h128 lowerTwo_rows312_02
      _ = 0 := by decide
  have h256 : (∑ i ∈ Finset.range 256, row i) = 0 := by
    calc
      _ = (∑ i ∈ Finset.range 192, row i) + (∑ i ∈ Finset.range 64, row (192+i)) :=
        Finset.sum_range_add row 192 64
      _ = 0 + 0 := congrArg₂ (fun a b : ℕ => a+b) h192 lowerTwo_rows312_03
      _ = 0 := by decide
  have h320 : (∑ i ∈ Finset.range 320, row i) = 0 := by
    calc
      _ = (∑ i ∈ Finset.range 256, row i) + (∑ i ∈ Finset.range 64, row (256+i)) :=
        Finset.sum_range_add row 256 64
      _ = 0 + 0 := congrArg₂ (fun a b : ℕ => a+b) h256 lowerTwo_rows312_04
      _ = 0 := by decide
  have h384 : (∑ i ∈ Finset.range 384, row i) = 0 := by
    calc
      _ = (∑ i ∈ Finset.range 320, row i) + (∑ i ∈ Finset.range 64, row (320+i)) :=
        Finset.sum_range_add row 320 64
      _ = 0 + 0 := congrArg₂ (fun a b : ℕ => a+b) h320 lowerTwo_rows312_05
      _ = 0 := by decide
  have h448 : (∑ i ∈ Finset.range 448, row i) = 0 := by
    calc
      _ = (∑ i ∈ Finset.range 384, row i) + (∑ i ∈ Finset.range 64, row (384+i)) :=
        Finset.sum_range_add row 384 64
      _ = 0 + 0 := congrArg₂ (fun a b : ℕ => a+b) h384 lowerTwo_rows312_06
      _ = 0 := by decide
  have h512 : (∑ i ∈ Finset.range 512, row i) = 0 := by
    calc
      _ = (∑ i ∈ Finset.range 448, row i) + (∑ i ∈ Finset.range 64, row (448+i)) :=
        Finset.sum_range_add row 448 64
      _ = 0 + 0 := congrArg₂ (fun a b : ℕ => a+b) h448 lowerTwo_rows312_07
      _ = 0 := by decide
  have h576 : (∑ i ∈ Finset.range 576, row i) = 0 := by
    calc
      _ = (∑ i ∈ Finset.range 512, row i) + (∑ i ∈ Finset.range 64, row (512+i)) :=
        Finset.sum_range_add row 512 64
      _ = 0 + 0 := congrArg₂ (fun a b : ℕ => a+b) h512 lowerTwo_rows312_08
      _ = 0 := by decide
  have h640 : (∑ i ∈ Finset.range 640, row i) = 0 := by
    calc
      _ = (∑ i ∈ Finset.range 576, row i) + (∑ i ∈ Finset.range 64, row (576+i)) :=
        Finset.sum_range_add row 576 64
      _ = 0 + 0 := congrArg₂ (fun a b : ℕ => a+b) h576 lowerTwo_rows312_09
      _ = 0 := by decide
  have h704 : (∑ i ∈ Finset.range 704, row i) = 3444078 := by
    calc
      _ = (∑ i ∈ Finset.range 640, row i) + (∑ i ∈ Finset.range 64, row (640+i)) :=
        Finset.sum_range_add row 640 64
      _ = 0 + 3444078 := congrArg₂ (fun a b : ℕ => a+b) h640 lowerTwo_rows312_10
      _ = 3444078 := by decide
  have h768 : (∑ i ∈ Finset.range 768, row i) = 375862570 := by
    calc
      _ = (∑ i ∈ Finset.range 704, row i) + (∑ i ∈ Finset.range 64, row (704+i)) :=
        Finset.sum_range_add row 704 64
      _ = 3444078 + 372418492 := congrArg₂ (fun a b : ℕ => a+b) h704 lowerTwo_rows312_11
      _ = 375862570 := by decide
  have h832 : (∑ i ∈ Finset.range 832, row i) = 4685242940 := by
    calc
      _ = (∑ i ∈ Finset.range 768, row i) + (∑ i ∈ Finset.range 64, row (768+i)) :=
        Finset.sum_range_add row 768 64
      _ = 375862570 + 4309380370 := congrArg₂ (fun a b : ℕ => a+b) h768 lowerTwo_rows312_12
      _ = 4685242940 := by decide
  have h896 : (∑ i ∈ Finset.range 896, row i) = 13514506387 := by
    calc
      _ = (∑ i ∈ Finset.range 832, row i) + (∑ i ∈ Finset.range 64, row (832+i)) :=
        Finset.sum_range_add row 832 64
      _ = 4685242940 + 8829263447 := congrArg₂ (fun a b : ℕ => a+b) h832 lowerTwo_rows312_13
      _ = 13514506387 := by decide
  have h960 : (∑ i ∈ Finset.range 960, row i) = 26524410553 := by
    calc
      _ = (∑ i ∈ Finset.range 896, row i) + (∑ i ∈ Finset.range 64, row (896+i)) :=
        Finset.sum_range_add row 896 64
      _ = 13514506387 + 13009904166 := congrArg₂ (fun a b : ℕ => a+b) h896 lowerTwo_rows312_14
      _ = 26524410553 := by decide
  have h1024 : (∑ i ∈ Finset.range 1024, row i) = 43415874939 := by
    calc
      _ = (∑ i ∈ Finset.range 960, row i) + (∑ i ∈ Finset.range 64, row (960+i)) :=
        Finset.sum_range_add row 960 64
      _ = 26524410553 + 16891464386 := congrArg₂ (fun a b : ℕ => a+b) h960 lowerTwo_rows312_15
      _ = 43415874939 := by decide
  have h1088 : (∑ i ∈ Finset.range 1088, row i) = 61751225962 := by
    calc
      _ = (∑ i ∈ Finset.range 1024, row i) + (∑ i ∈ Finset.range 64, row (1024+i)) :=
        Finset.sum_range_add row 1024 64
      _ = 43415874939 + 18335351023 := congrArg₂ (fun a b : ℕ => a+b) h1024 lowerTwo_rows312_16
      _ = 61751225962 := by decide
  have h1152 : (∑ i ∈ Finset.range 1152, row i) = 79352569623 := by
    calc
      _ = (∑ i ∈ Finset.range 1088, row i) + (∑ i ∈ Finset.range 64, row (1088+i)) :=
        Finset.sum_range_add row 1088 64
      _ = 61751225962 + 17601343661 := congrArg₂ (fun a b : ℕ => a+b) h1088 lowerTwo_rows312_17
      _ = 79352569623 := by decide
  have h1216 : (∑ i ∈ Finset.range 1216, row i) = 98010155058 := by
    calc
      _ = (∑ i ∈ Finset.range 1152, row i) + (∑ i ∈ Finset.range 64, row (1152+i)) :=
        Finset.sum_range_add row 1152 64
      _ = 79352569623 + 18657585435 := congrArg₂ (fun a b : ℕ => a+b) h1152 lowerTwo_rows312_18
      _ = 98010155058 := by decide
  have h1280 : (∑ i ∈ Finset.range 1280, row i) = 117415870269 := by
    calc
      _ = (∑ i ∈ Finset.range 1216, row i) + (∑ i ∈ Finset.range 64, row (1216+i)) :=
        Finset.sum_range_add row 1216 64
      _ = 98010155058 + 19405715211 := congrArg₂ (fun a b : ℕ => a+b) h1216 lowerTwo_rows312_19
      _ = 117415870269 := by decide
  have h1344 : (∑ i ∈ Finset.range 1344, row i) = 137352194121 := by
    calc
      _ = (∑ i ∈ Finset.range 1280, row i) + (∑ i ∈ Finset.range 64, row (1280+i)) :=
        Finset.sum_range_add row 1280 64
      _ = 117415870269 + 19936323852 := congrArg₂ (fun a b : ℕ => a+b) h1280 lowerTwo_rows312_20
      _ = 137352194121 := by decide
  have h1408 : (∑ i ∈ Finset.range 1408, row i) = 158530969314 := by
    calc
      _ = (∑ i ∈ Finset.range 1344, row i) + (∑ i ∈ Finset.range 64, row (1344+i)) :=
        Finset.sum_range_add row 1344 64
      _ = 137352194121 + 21178775193 := congrArg₂ (fun a b : ℕ => a+b) h1344 lowerTwo_rows312_21
      _ = 158530969314 := by decide
  have h1472 : (∑ i ∈ Finset.range 1472, row i) = 181445341524 := by
    calc
      _ = (∑ i ∈ Finset.range 1408, row i) + (∑ i ∈ Finset.range 64, row (1408+i)) :=
        Finset.sum_range_add row 1408 64
      _ = 158530969314 + 22914372210 := congrArg₂ (fun a b : ℕ => a+b) h1408 lowerTwo_rows312_22
      _ = 181445341524 := by decide
  have h1536 : (∑ i ∈ Finset.range 1536, row i) = 205946840205 := by
    calc
      _ = (∑ i ∈ Finset.range 1472, row i) + (∑ i ∈ Finset.range 64, row (1472+i)) :=
        Finset.sum_range_add row 1472 64
      _ = 181445341524 + 24501498681 := congrArg₂ (fun a b : ℕ => a+b) h1472 lowerTwo_rows312_23
      _ = 205946840205 := by decide
  have h1600 : (∑ i ∈ Finset.range 1600, row i) = 231893518459 := by
    calc
      _ = (∑ i ∈ Finset.range 1536, row i) + (∑ i ∈ Finset.range 64, row (1536+i)) :=
        Finset.sum_range_add row 1536 64
      _ = 205946840205 + 25946678254 := congrArg₂ (fun a b : ℕ => a+b) h1536 lowerTwo_rows312_24
      _ = 231893518459 := by decide
  have h1664 : (∑ i ∈ Finset.range 1664, row i) = 259199543318 := by
    calc
      _ = (∑ i ∈ Finset.range 1600, row i) + (∑ i ∈ Finset.range 64, row (1600+i)) :=
        Finset.sum_range_add row 1600 64
      _ = 231893518459 + 27306024859 := congrArg₂ (fun a b : ℕ => a+b) h1600 lowerTwo_rows312_25
      _ = 259199543318 := by decide
  have h1728 : (∑ i ∈ Finset.range 1728, row i) = 287786595010 := by
    calc
      _ = (∑ i ∈ Finset.range 1664, row i) + (∑ i ∈ Finset.range 64, row (1664+i)) :=
        Finset.sum_range_add row 1664 64
      _ = 259199543318 + 28587051692 := congrArg₂ (fun a b : ℕ => a+b) h1664 lowerTwo_rows312_26
      _ = 287786595010 := by decide
  have h1792 : (∑ i ∈ Finset.range 1792, row i) = 317568739557 := by
    calc
      _ = (∑ i ∈ Finset.range 1728, row i) + (∑ i ∈ Finset.range 64, row (1728+i)) :=
        Finset.sum_range_add row 1728 64
      _ = 287786595010 + 29782144547 := congrArg₂ (fun a b : ℕ => a+b) h1728 lowerTwo_rows312_27
      _ = 317568739557 := by decide
  have h1856 : (∑ i ∈ Finset.range 1856, row i) = 348453770975 := by
    calc
      _ = (∑ i ∈ Finset.range 1792, row i) + (∑ i ∈ Finset.range 64, row (1792+i)) :=
        Finset.sum_range_add row 1792 64
      _ = 317568739557 + 30885031418 := congrArg₂ (fun a b : ℕ => a+b) h1792 lowerTwo_rows312_28
      _ = 348453770975 := by decide
  have h1920 : (∑ i ∈ Finset.range 1920, row i) = 380190112074 := by
    calc
      _ = (∑ i ∈ Finset.range 1856, row i) + (∑ i ∈ Finset.range 64, row (1856+i)) :=
        Finset.sum_range_add row 1856 64
      _ = 348453770975 + 31736341099 := congrArg₂ (fun a b : ℕ => a+b) h1856 lowerTwo_rows312_29
      _ = 380190112074 := by decide
  have h1984 : (∑ i ∈ Finset.range 1984, row i) = 411257454215 := by
    calc
      _ = (∑ i ∈ Finset.range 1920, row i) + (∑ i ∈ Finset.range 64, row (1920+i)) :=
        Finset.sum_range_add row 1920 64
      _ = 380190112074 + 31067342141 := congrArg₂ (fun a b : ℕ => a+b) h1920 lowerTwo_rows312_30
      _ = 411257454215 := by decide
  have h2048 : (∑ i ∈ Finset.range 2048, row i) = 441083572921 := by
    calc
      _ = (∑ i ∈ Finset.range 1984, row i) + (∑ i ∈ Finset.range 64, row (1984+i)) :=
        Finset.sum_range_add row 1984 64
      _ = 411257454215 + 29826118706 := congrArg₂ (fun a b : ℕ => a+b) h1984 lowerTwo_rows312_31
      _ = 441083572921 := by decide
  have h2112 : (∑ i ∈ Finset.range 2112, row i) = 470293676264 := by
    calc
      _ = (∑ i ∈ Finset.range 2048, row i) + (∑ i ∈ Finset.range 64, row (2048+i)) :=
        Finset.sum_range_add row 2048 64
      _ = 441083572921 + 29210103343 := congrArg₂ (fun a b : ℕ => a+b) h2048 lowerTwo_rows312_32
      _ = 470293676264 := by decide
  have h2176 : (∑ i ∈ Finset.range 2176, row i) = 499938951008 := by
    calc
      _ = (∑ i ∈ Finset.range 2112, row i) + (∑ i ∈ Finset.range 64, row (2112+i)) :=
        Finset.sum_range_add row 2112 64
      _ = 470293676264 + 29645274744 := congrArg₂ (fun a b : ℕ => a+b) h2112 lowerTwo_rows312_33
      _ = 499938951008 := by decide
  have h2240 : (∑ i ∈ Finset.range 2240, row i) = 529925504685 := by
    calc
      _ = (∑ i ∈ Finset.range 2176, row i) + (∑ i ∈ Finset.range 64, row (2176+i)) :=
        Finset.sum_range_add row 2176 64
      _ = 499938951008 + 29986553677 := congrArg₂ (fun a b : ℕ => a+b) h2176 lowerTwo_rows312_34
      _ = 529925504685 := by decide
  have h2304 : (∑ i ∈ Finset.range 2304, row i) = 560013878207 := by
    calc
      _ = (∑ i ∈ Finset.range 2240, row i) + (∑ i ∈ Finset.range 64, row (2240+i)) :=
        Finset.sum_range_add row 2240 64
      _ = 529925504685 + 30088373522 := congrArg₂ (fun a b : ℕ => a+b) h2240 lowerTwo_rows312_35
      _ = 560013878207 := by decide
  have h2368 : (∑ i ∈ Finset.range 2368, row i) = 588888346759 := by
    calc
      _ = (∑ i ∈ Finset.range 2304, row i) + (∑ i ∈ Finset.range 64, row (2304+i)) :=
        Finset.sum_range_add row 2304 64
      _ = 560013878207 + 28874468552 := congrArg₂ (fun a b : ℕ => a+b) h2304 lowerTwo_rows312_36
      _ = 588888346759 := by decide
  have h2432 : (∑ i ∈ Finset.range 2432, row i) = 616213139457 := by
    calc
      _ = (∑ i ∈ Finset.range 2368, row i) + (∑ i ∈ Finset.range 64, row (2368+i)) :=
        Finset.sum_range_add row 2368 64
      _ = 588888346759 + 27324792698 := congrArg₂ (fun a b : ℕ => a+b) h2368 lowerTwo_rows312_37
      _ = 616213139457 := by decide
  have h2496 : (∑ i ∈ Finset.range 2496, row i) = 641880099234 := by
    calc
      _ = (∑ i ∈ Finset.range 2432, row i) + (∑ i ∈ Finset.range 64, row (2432+i)) :=
        Finset.sum_range_add row 2432 64
      _ = 616213139457 + 25666959777 := congrArg₂ (fun a b : ℕ => a+b) h2432 lowerTwo_rows312_38
      _ = 641880099234 := by decide
  have h2560 : (∑ i ∈ Finset.range 2560, row i) = 665752713874 := by
    calc
      _ = (∑ i ∈ Finset.range 2496, row i) + (∑ i ∈ Finset.range 64, row (2496+i)) :=
        Finset.sum_range_add row 2496 64
      _ = 641880099234 + 23872614640 := congrArg₂ (fun a b : ℕ => a+b) h2496 lowerTwo_rows312_39
      _ = 665752713874 := by decide
  have h2624 : (∑ i ∈ Finset.range 2624, row i) = 688144232120 := by
    calc
      _ = (∑ i ∈ Finset.range 2560, row i) + (∑ i ∈ Finset.range 64, row (2560+i)) :=
        Finset.sum_range_add row 2560 64
      _ = 665752713874 + 22391518246 := congrArg₂ (fun a b : ℕ => a+b) h2560 lowerTwo_rows312_40
      _ = 688144232120 := by decide
  have h2688 : (∑ i ∈ Finset.range 2688, row i) = 710026908230 := by
    calc
      _ = (∑ i ∈ Finset.range 2624, row i) + (∑ i ∈ Finset.range 64, row (2624+i)) :=
        Finset.sum_range_add row 2624 64
      _ = 688144232120 + 21882676110 := congrArg₂ (fun a b : ℕ => a+b) h2624 lowerTwo_rows312_41
      _ = 710026908230 := by decide
  have h2752 : (∑ i ∈ Finset.range 2752, row i) = 731322802486 := by
    calc
      _ = (∑ i ∈ Finset.range 2688, row i) + (∑ i ∈ Finset.range 64, row (2688+i)) :=
        Finset.sum_range_add row 2688 64
      _ = 710026908230 + 21295894256 := congrArg₂ (fun a b : ℕ => a+b) h2688 lowerTwo_rows312_42
      _ = 731322802486 := by decide
  have h2816 : (∑ i ∈ Finset.range 2816, row i) = 753295188209 := by
    calc
      _ = (∑ i ∈ Finset.range 2752, row i) + (∑ i ∈ Finset.range 64, row (2752+i)) :=
        Finset.sum_range_add row 2752 64
      _ = 731322802486 + 21972385723 := congrArg₂ (fun a b : ℕ => a+b) h2752 lowerTwo_rows312_43
      _ = 753295188209 := by decide
  have h2880 : (∑ i ∈ Finset.range 2880, row i) = 776593383399 := by
    calc
      _ = (∑ i ∈ Finset.range 2816, row i) + (∑ i ∈ Finset.range 64, row (2816+i)) :=
        Finset.sum_range_add row 2816 64
      _ = 753295188209 + 23298195190 := congrArg₂ (fun a b : ℕ => a+b) h2816 lowerTwo_rows312_44
      _ = 776593383399 := by decide
  have h2944 : (∑ i ∈ Finset.range 2944, row i) = 801374122889 := by
    calc
      _ = (∑ i ∈ Finset.range 2880, row i) + (∑ i ∈ Finset.range 64, row (2880+i)) :=
        Finset.sum_range_add row 2880 64
      _ = 776593383399 + 24780739490 := congrArg₂ (fun a b : ℕ => a+b) h2880 lowerTwo_rows312_45
      _ = 801374122889 := by decide
  have h3008 : (∑ i ∈ Finset.range 3008, row i) = 827805067457 := by
    calc
      _ = (∑ i ∈ Finset.range 2944, row i) + (∑ i ∈ Finset.range 64, row (2944+i)) :=
        Finset.sum_range_add row 2944 64
      _ = 801374122889 + 26430944568 := congrArg₂ (fun a b : ℕ => a+b) h2944 lowerTwo_rows312_46
      _ = 827805067457 := by decide
  have h3072 : (∑ i ∈ Finset.range 3072, row i) = 856068014366 := by
    calc
      _ = (∑ i ∈ Finset.range 3008, row i) + (∑ i ∈ Finset.range 64, row (3008+i)) :=
        Finset.sum_range_add row 3008 64
      _ = 827805067457 + 28262946909 := congrArg₂ (fun a b : ℕ => a+b) h3008 lowerTwo_rows312_47
      _ = 856068014366 := by decide
  have h3136 : (∑ i ∈ Finset.range 3136, row i) = 886361257013 := by
    calc
      _ = (∑ i ∈ Finset.range 3072, row i) + (∑ i ∈ Finset.range 64, row (3072+i)) :=
        Finset.sum_range_add row 3072 64
      _ = 856068014366 + 30293242647 := congrArg₂ (fun a b : ℕ => a+b) h3072 lowerTwo_rows312_48
      _ = 886361257013 := by decide
  have h3200 : (∑ i ∈ Finset.range 3200, row i) = 916355726414 := by
    calc
      _ = (∑ i ∈ Finset.range 3136, row i) + (∑ i ∈ Finset.range 64, row (3136+i)) :=
        Finset.sum_range_add row 3136 64
      _ = 886361257013 + 29994469401 := congrArg₂ (fun a b : ℕ => a+b) h3136 lowerTwo_rows312_49
      _ = 916355726414 := by decide
  have h3264 : (∑ i ∈ Finset.range 3264, row i) = 943496427660 := by
    calc
      _ = (∑ i ∈ Finset.range 3200, row i) + (∑ i ∈ Finset.range 64, row (3200+i)) :=
        Finset.sum_range_add row 3200 64
      _ = 916355726414 + 27140701246 := congrArg₂ (fun a b : ℕ => a+b) h3200 lowerTwo_rows312_50
      _ = 943496427660 := by decide
  have h3328 : (∑ i ∈ Finset.range 3328, row i) = 966948846479 := by
    calc
      _ = (∑ i ∈ Finset.range 3264, row i) + (∑ i ∈ Finset.range 64, row (3264+i)) :=
        Finset.sum_range_add row 3264 64
      _ = 943496427660 + 23452418819 := congrArg₂ (fun a b : ℕ => a+b) h3264 lowerTwo_rows312_51
      _ = 966948846479 := by decide
  have h3392 : (∑ i ∈ Finset.range 3392, row i) = 984806651938 := by
    calc
      _ = (∑ i ∈ Finset.range 3328, row i) + (∑ i ∈ Finset.range 64, row (3328+i)) :=
        Finset.sum_range_add row 3328 64
      _ = 966948846479 + 17857805459 := congrArg₂ (fun a b : ℕ => a+b) h3328 lowerTwo_rows312_52
      _ = 984806651938 := by decide
  have h3456 : (∑ i ∈ Finset.range 3456, row i) = 996345232587 := by
    calc
      _ = (∑ i ∈ Finset.range 3392, row i) + (∑ i ∈ Finset.range 64, row (3392+i)) :=
        Finset.sum_range_add row 3392 64
      _ = 984806651938 + 11538580649 := congrArg₂ (fun a b : ℕ => a+b) h3392 lowerTwo_rows312_53
      _ = 996345232587 := by decide
  have h3520 : (∑ i ∈ Finset.range 3520, row i) = 1006809306270 := by
    calc
      _ = (∑ i ∈ Finset.range 3456, row i) + (∑ i ∈ Finset.range 64, row (3456+i)) :=
        Finset.sum_range_add row 3456 64
      _ = 996345232587 + 10464073683 := congrArg₂ (fun a b : ℕ => a+b) h3456 lowerTwo_rows312_54
      _ = 1006809306270 := by decide
  have h3584 : (∑ i ∈ Finset.range 3584, row i) = 1016738616631 := by
    calc
      _ = (∑ i ∈ Finset.range 3520, row i) + (∑ i ∈ Finset.range 64, row (3520+i)) :=
        Finset.sum_range_add row 3520 64
      _ = 1006809306270 + 9929310361 := congrArg₂ (fun a b : ℕ => a+b) h3520 lowerTwo_rows312_55
      _ = 1016738616631 := by decide
  have h3648 : (∑ i ∈ Finset.range 3648, row i) = 1026129121401 := by
    calc
      _ = (∑ i ∈ Finset.range 3584, row i) + (∑ i ∈ Finset.range 64, row (3584+i)) :=
        Finset.sum_range_add row 3584 64
      _ = 1016738616631 + 9390504770 := congrArg₂ (fun a b : ℕ => a+b) h3584 lowerTwo_rows312_56
      _ = 1026129121401 := by decide
  have h3712 : (∑ i ∈ Finset.range 3712, row i) = 1034976011400 := by
    calc
      _ = (∑ i ∈ Finset.range 3648, row i) + (∑ i ∈ Finset.range 64, row (3648+i)) :=
        Finset.sum_range_add row 3648 64
      _ = 1026129121401 + 8846889999 := congrArg₂ (fun a b : ℕ => a+b) h3648 lowerTwo_rows312_57
      _ = 1034976011400 := by decide
  have h3776 : (∑ i ∈ Finset.range 3776, row i) = 1043273689207 := by
    calc
      _ = (∑ i ∈ Finset.range 3712, row i) + (∑ i ∈ Finset.range 64, row (3712+i)) :=
        Finset.sum_range_add row 3712 64
      _ = 1034976011400 + 8297677807 := congrArg₂ (fun a b : ℕ => a+b) h3712 lowerTwo_rows312_58
      _ = 1043273689207 := by decide
  have h3840 : (∑ i ∈ Finset.range 3840, row i) = 1051368588347 := by
    calc
      _ = (∑ i ∈ Finset.range 3776, row i) + (∑ i ∈ Finset.range 64, row (3776+i)) :=
        Finset.sum_range_add row 3776 64
      _ = 1043273689207 + 8094899140 := congrArg₂ (fun a b : ℕ => a+b) h3776 lowerTwo_rows312_59
      _ = 1051368588347 := by decide
  have h3904 : (∑ i ∈ Finset.range 3904, row i) = 1063086137250 := by
    calc
      _ = (∑ i ∈ Finset.range 3840, row i) + (∑ i ∈ Finset.range 64, row (3840+i)) :=
        Finset.sum_range_add row 3840 64
      _ = 1051368588347 + 11717548903 := congrArg₂ (fun a b : ℕ => a+b) h3840 lowerTwo_rows312_60
      _ = 1063086137250 := by decide
  have h3968 : (∑ i ∈ Finset.range 3968, row i) = 1079737949535 := by
    calc
      _ = (∑ i ∈ Finset.range 3904, row i) + (∑ i ∈ Finset.range 64, row (3904+i)) :=
        Finset.sum_range_add row 3904 64
      _ = 1063086137250 + 16651812285 := congrArg₂ (fun a b : ℕ => a+b) h3904 lowerTwo_rows312_61
      _ = 1079737949535 := by decide
  have h4032 : (∑ i ∈ Finset.range 4032, row i) = 1102151558896 := by
    calc
      _ = (∑ i ∈ Finset.range 3968, row i) + (∑ i ∈ Finset.range 64, row (3968+i)) :=
        Finset.sum_range_add row 3968 64
      _ = 1079737949535 + 22413609361 := congrArg₂ (fun a b : ℕ => a+b) h3968 lowerTwo_rows312_62
      _ = 1102151558896 := by decide
  have h4096 : (∑ i ∈ Finset.range 4096, row i) = 1132433915806 := by
    calc
      _ = (∑ i ∈ Finset.range 4032, row i) + (∑ i ∈ Finset.range 64, row (4032+i)) :=
        Finset.sum_range_add row 4032 64
      _ = 1102151558896 + 30282356910 := congrArg₂ (fun a b : ℕ => a+b) h4032 lowerTwo_rows312_63
      _ = 1132433915806 := by decide
  exact h4096

end LeanLab.BHP1997.DecompC165d
