/- AI wrote this Lean code for CODEX task700. Goldbach is open.
Assembly of the finite squarefree count in Buthe 2014 display 4.6.
https://arxiv.org/abs/1410.7561v2 -/
import LeanLab.BS2022GRH.SquarefreeSound700
import LeanLab.BS2022GRH.Witness700Cert00
import LeanLab.BS2022GRH.Witness700Cert01
import LeanLab.BS2022GRH.Witness700Cert02
import LeanLab.BS2022GRH.Witness700Cert03
import LeanLab.BS2022GRH.Witness700Cert04
import LeanLab.BS2022GRH.Witness700Cert05
import LeanLab.BS2022GRH.Witness700Cert06
import LeanLab.BS2022GRH.Witness700Cert07
import LeanLab.BS2022GRH.Witness700Cert08
import LeanLab.BS2022GRH.Witness700Cert09
import LeanLab.BS2022GRH.Witness700Cert10
import LeanLab.BS2022GRH.Witness700Cert11
import LeanLab.BS2022GRH.Witness700Cert12
import LeanLab.BS2022GRH.Witness700Cert13
import LeanLab.BS2022GRH.Witness700Cert14
import LeanLab.BS2022GRH.Witness700Cert15
import LeanLab.BS2022GRH.Witness700Cert16
import LeanLab.BS2022GRH.Witness700Cert17
import LeanLab.BS2022GRH.Witness700Cert18
import LeanLab.BS2022GRH.Witness700Cert19
import LeanLab.BS2022GRH.Witness700Cert20
import LeanLab.BS2022GRH.Witness700Cert21
import LeanLab.BS2022GRH.Witness700Cert22
import LeanLab.BS2022GRH.Witness700Cert23
import LeanLab.BS2022GRH.Witness700Cert24
import LeanLab.BS2022GRH.Witness700Cert25
import LeanLab.BS2022GRH.Witness700Cert26
import LeanLab.BS2022GRH.Witness700Cert27

set_option maxRecDepth 100000
namespace LeanLab.BS2022GRH.FiniteCount700
open Witness700 SquarefreeSound700

/-- Every integer up to 438652 has a certified upper count in the rational budget. -/
theorem certified_bounds :
    sqCount 438652 ≤ 266651 ∧ ∀ N : ℕ, N ≤ 438652 →
      ∃ c : ℕ, sqCount N ≤ c ∧ good N c = true := by
  have hbase : sqCount 0 ≤ 0 := by simp [sqCount]
  have h000 := verify_sound rows000 0 0 4000 2433 hbase cert000
  have h001 := verify_sound rows001 4000 2433 8000 4865 h000.1 cert001
  have h002 := verify_sound rows002 8000 4865 12000 7293 h001.1 cert002
  have h003 := verify_sound rows003 12000 7293 16000 9728 h002.1 cert003
  have h004 := verify_sound rows004 16000 9728 20000 12160 h003.1 cert004
  have h005 := verify_sound rows005 20000 12160 24000 14592 h004.1 cert005
  have h006 := verify_sound rows006 24000 14592 28000 17023 h005.1 cert006
  have h007 := verify_sound rows007 28000 17023 32000 19452 h006.1 cert007
  have h008 := verify_sound rows008 32000 19452 36000 21885 h007.1 cert008
  have h009 := verify_sound rows009 36000 21885 40000 24310 h008.1 cert009
  have h010 := verify_sound rows010 40000 24310 44000 26754 h009.1 cert010
  have h011 := verify_sound rows011 44000 26754 48000 29190 h010.1 cert011
  have h012 := verify_sound rows012 48000 29190 52000 31621 h011.1 cert012
  have h013 := verify_sound rows013 52000 31621 56000 34045 h012.1 cert013
  have h014 := verify_sound rows014 56000 34045 60000 36473 h013.1 cert014
  have h015 := verify_sound rows015 60000 36473 64000 38910 h014.1 cert015
  have h016 := verify_sound rows016 64000 38910 68000 41342 h015.1 cert016
  have h017 := verify_sound rows017 68000 41342 72000 43773 h016.1 cert017
  have h018 := verify_sound rows018 72000 43773 76000 46198 h017.1 cert018
  have h019 := verify_sound rows019 76000 46198 80000 48627 h018.1 cert019
  have h020 := verify_sound rows020 80000 48627 84000 51061 h019.1 cert020
  have h021 := verify_sound rows021 84000 51061 88000 53495 h020.1 cert021
  have h022 := verify_sound rows022 88000 53495 92000 55932 h021.1 cert022
  have h023 := verify_sound rows023 92000 55932 96000 58364 h022.1 cert023
  have h024 := verify_sound rows024 96000 58364 100000 60794 h023.1 cert024
  have h025 := verify_sound rows025 100000 60794 104000 63225 h024.1 cert025
  have h026 := verify_sound rows026 104000 63225 108000 65664 h025.1 cert026
  have h027 := verify_sound rows027 108000 65664 112000 68094 h026.1 cert027
  have h028 := verify_sound rows028 112000 68094 116000 70522 h027.1 cert028
  have h029 := verify_sound rows029 116000 70522 120000 72948 h028.1 cert029
  have h030 := verify_sound rows030 120000 72948 124000 75383 h029.1 cert030
  have h031 := verify_sound rows031 124000 75383 128000 77821 h030.1 cert031
  have h032 := verify_sound rows032 128000 77821 132000 80254 h031.1 cert032
  have h033 := verify_sound rows033 132000 80254 136000 82678 h032.1 cert033
  have h034 := verify_sound rows034 136000 82678 140000 85112 h033.1 cert034
  have h035 := verify_sound rows035 140000 85112 144000 87547 h034.1 cert035
  have h036 := verify_sound rows036 144000 87547 148000 89979 h035.1 cert036
  have h037 := verify_sound rows037 148000 89979 152000 92408 h036.1 cert037
  have h038 := verify_sound rows038 152000 92408 156000 94841 h037.1 cert038
  have h039 := verify_sound rows039 156000 94841 160000 97267 h038.1 cert039
  have h040 := verify_sound rows040 160000 97267 164000 99691 h039.1 cert040
  have h041 := verify_sound rows041 164000 99691 168000 102129 h040.1 cert041
  have h042 := verify_sound rows042 168000 102129 172000 104559 h041.1 cert042
  have h043 := verify_sound rows043 172000 104559 176000 106994 h042.1 cert043
  have h044 := verify_sound rows044 176000 106994 180000 109423 h043.1 cert044
  have h045 := verify_sound rows045 180000 109423 184000 111861 h044.1 cert045
  have h046 := verify_sound rows046 184000 111861 188000 114293 h045.1 cert046
  have h047 := verify_sound rows047 188000 114293 192000 116723 h046.1 cert047
  have h048 := verify_sound rows048 192000 116723 196000 119149 h047.1 cert048
  have h049 := verify_sound rows049 196000 119149 200000 121581 h048.1 cert049
  have h050 := verify_sound rows050 200000 121581 204000 124016 h049.1 cert050
  have h051 := verify_sound rows051 204000 124016 208000 126443 h050.1 cert051
  have h052 := verify_sound rows052 208000 126443 212000 128883 h051.1 cert052
  have h053 := verify_sound rows053 212000 128883 216000 131315 h052.1 cert053
  have h054 := verify_sound rows054 216000 131315 220000 133744 h053.1 cert054
  have h055 := verify_sound rows055 220000 133744 224000 136174 h054.1 cert055
  have h056 := verify_sound rows056 224000 136174 228000 138608 h055.1 cert056
  have h057 := verify_sound rows057 228000 138608 232000 141038 h056.1 cert057
  have h058 := verify_sound rows058 232000 141038 236000 143476 h057.1 cert058
  have h059 := verify_sound rows059 236000 143476 240000 145906 h058.1 cert059
  have h060 := verify_sound rows060 240000 145906 244000 148330 h059.1 cert060
  have h061 := verify_sound rows061 244000 148330 248000 150763 h060.1 cert061
  have h062 := verify_sound rows062 248000 150763 252000 153194 h061.1 cert062
  have h063 := verify_sound rows063 252000 153194 256000 155626 h062.1 cert063
  have h064 := verify_sound rows064 256000 155626 260000 158063 h063.1 cert064
  have h065 := verify_sound rows065 260000 158063 264000 160491 h064.1 cert065
  have h066 := verify_sound rows066 264000 160491 268000 162926 h065.1 cert066
  have h067 := verify_sound rows067 268000 162926 272000 165347 h066.1 cert067
  have h068 := verify_sound rows068 272000 165347 276000 167784 h067.1 cert068
  have h069 := verify_sound rows069 276000 167784 280000 170220 h068.1 cert069
  have h070 := verify_sound rows070 280000 170220 284000 172658 h069.1 cert070
  have h071 := verify_sound rows071 284000 172658 288000 175092 h070.1 cert071
  have h072 := verify_sound rows072 288000 175092 292000 177521 h071.1 cert072
  have h073 := verify_sound rows073 292000 177521 296000 179953 h072.1 cert073
  have h074 := verify_sound rows074 296000 179953 300000 182378 h073.1 cert074
  have h075 := verify_sound rows075 300000 182378 304000 184816 h074.1 cert075
  have h076 := verify_sound rows076 304000 184816 308000 187250 h075.1 cert076
  have h077 := verify_sound rows077 308000 187250 312000 189681 h076.1 cert077
  have h078 := verify_sound rows078 312000 189681 316000 192116 h077.1 cert078
  have h079 := verify_sound rows079 316000 192116 320000 194547 h078.1 cert079
  have h080 := verify_sound rows080 320000 194547 324000 196976 h079.1 cert080
  have h081 := verify_sound rows081 324000 196976 328000 199408 h080.1 cert081
  have h082 := verify_sound rows082 328000 199408 332000 201837 h081.1 cert082
  have h083 := verify_sound rows083 332000 201837 336000 204271 h082.1 cert083
  have h084 := verify_sound rows084 336000 204271 340000 206712 h083.1 cert084
  have h085 := verify_sound rows085 340000 206712 344000 209141 h084.1 cert085
  have h086 := verify_sound rows086 344000 209141 348000 211573 h085.1 cert086
  have h087 := verify_sound rows087 348000 211573 352000 214004 h086.1 cert087
  have h088 := verify_sound rows088 352000 214004 356000 216433 h087.1 cert088
  have h089 := verify_sound rows089 356000 216433 360000 218866 h088.1 cert089
  have h090 := verify_sound rows090 360000 218866 364000 221300 h089.1 cert090
  have h091 := verify_sound rows091 364000 221300 368000 223722 h090.1 cert091
  have h092 := verify_sound rows092 368000 223722 372000 226153 h091.1 cert092
  have h093 := verify_sound rows093 372000 226153 376000 228578 h092.1 cert093
  have h094 := verify_sound rows094 376000 228578 380000 231009 h093.1 cert094
  have h095 := verify_sound rows095 380000 231009 384000 233445 h094.1 cert095
  have h096 := verify_sound rows096 384000 233445 388000 235873 h095.1 cert096
  have h097 := verify_sound rows097 388000 235873 392000 238306 h096.1 cert097
  have h098 := verify_sound rows098 392000 238306 396000 240734 h097.1 cert098
  have h099 := verify_sound rows099 396000 240734 400000 243165 h098.1 cert099
  have h100 := verify_sound rows100 400000 243165 404000 245593 h099.1 cert100
  have h101 := verify_sound rows101 404000 245593 408000 248023 h100.1 cert101
  have h102 := verify_sound rows102 408000 248023 412000 250465 h101.1 cert102
  have h103 := verify_sound rows103 412000 250465 416000 252893 h102.1 cert103
  have h104 := verify_sound rows104 416000 252893 420000 255314 h103.1 cert104
  have h105 := verify_sound rows105 420000 255314 424000 257751 h104.1 cert105
  have h106 := verify_sound rows106 424000 257751 428000 260183 h105.1 cert106
  have h107 := verify_sound rows107 428000 260183 432000 262613 h106.1 cert107
  have h108 := verify_sound rows108 432000 262613 436000 265039 h107.1 cert108
  have h109 := verify_sound rows109 436000 265039 438652 266651 h108.1 cert109
  refine ⟨h109.1, ?_⟩
  intro N hN
  by_cases hzero : N=0
  · subst N; exact ⟨0, hbase, by decide⟩
  by_cases hguard0 : N ≤ 4000
  · exact h000.2 N (Nat.pos_of_ne_zero hzero) hguard0
  by_cases hguard1 : N ≤ 8000
  · exact h001.2 N (Nat.lt_of_not_ge hguard0) hguard1
  by_cases hguard2 : N ≤ 12000
  · exact h002.2 N (Nat.lt_of_not_ge hguard1) hguard2
  by_cases hguard3 : N ≤ 16000
  · exact h003.2 N (Nat.lt_of_not_ge hguard2) hguard3
  by_cases hguard4 : N ≤ 20000
  · exact h004.2 N (Nat.lt_of_not_ge hguard3) hguard4
  by_cases hguard5 : N ≤ 24000
  · exact h005.2 N (Nat.lt_of_not_ge hguard4) hguard5
  by_cases hguard6 : N ≤ 28000
  · exact h006.2 N (Nat.lt_of_not_ge hguard5) hguard6
  by_cases hguard7 : N ≤ 32000
  · exact h007.2 N (Nat.lt_of_not_ge hguard6) hguard7
  by_cases hguard8 : N ≤ 36000
  · exact h008.2 N (Nat.lt_of_not_ge hguard7) hguard8
  by_cases hguard9 : N ≤ 40000
  · exact h009.2 N (Nat.lt_of_not_ge hguard8) hguard9
  by_cases hguard10 : N ≤ 44000
  · exact h010.2 N (Nat.lt_of_not_ge hguard9) hguard10
  by_cases hguard11 : N ≤ 48000
  · exact h011.2 N (Nat.lt_of_not_ge hguard10) hguard11
  by_cases hguard12 : N ≤ 52000
  · exact h012.2 N (Nat.lt_of_not_ge hguard11) hguard12
  by_cases hguard13 : N ≤ 56000
  · exact h013.2 N (Nat.lt_of_not_ge hguard12) hguard13
  by_cases hguard14 : N ≤ 60000
  · exact h014.2 N (Nat.lt_of_not_ge hguard13) hguard14
  by_cases hguard15 : N ≤ 64000
  · exact h015.2 N (Nat.lt_of_not_ge hguard14) hguard15
  by_cases hguard16 : N ≤ 68000
  · exact h016.2 N (Nat.lt_of_not_ge hguard15) hguard16
  by_cases hguard17 : N ≤ 72000
  · exact h017.2 N (Nat.lt_of_not_ge hguard16) hguard17
  by_cases hguard18 : N ≤ 76000
  · exact h018.2 N (Nat.lt_of_not_ge hguard17) hguard18
  by_cases hguard19 : N ≤ 80000
  · exact h019.2 N (Nat.lt_of_not_ge hguard18) hguard19
  by_cases hguard20 : N ≤ 84000
  · exact h020.2 N (Nat.lt_of_not_ge hguard19) hguard20
  by_cases hguard21 : N ≤ 88000
  · exact h021.2 N (Nat.lt_of_not_ge hguard20) hguard21
  by_cases hguard22 : N ≤ 92000
  · exact h022.2 N (Nat.lt_of_not_ge hguard21) hguard22
  by_cases hguard23 : N ≤ 96000
  · exact h023.2 N (Nat.lt_of_not_ge hguard22) hguard23
  by_cases hguard24 : N ≤ 100000
  · exact h024.2 N (Nat.lt_of_not_ge hguard23) hguard24
  by_cases hguard25 : N ≤ 104000
  · exact h025.2 N (Nat.lt_of_not_ge hguard24) hguard25
  by_cases hguard26 : N ≤ 108000
  · exact h026.2 N (Nat.lt_of_not_ge hguard25) hguard26
  by_cases hguard27 : N ≤ 112000
  · exact h027.2 N (Nat.lt_of_not_ge hguard26) hguard27
  by_cases hguard28 : N ≤ 116000
  · exact h028.2 N (Nat.lt_of_not_ge hguard27) hguard28
  by_cases hguard29 : N ≤ 120000
  · exact h029.2 N (Nat.lt_of_not_ge hguard28) hguard29
  by_cases hguard30 : N ≤ 124000
  · exact h030.2 N (Nat.lt_of_not_ge hguard29) hguard30
  by_cases hguard31 : N ≤ 128000
  · exact h031.2 N (Nat.lt_of_not_ge hguard30) hguard31
  by_cases hguard32 : N ≤ 132000
  · exact h032.2 N (Nat.lt_of_not_ge hguard31) hguard32
  by_cases hguard33 : N ≤ 136000
  · exact h033.2 N (Nat.lt_of_not_ge hguard32) hguard33
  by_cases hguard34 : N ≤ 140000
  · exact h034.2 N (Nat.lt_of_not_ge hguard33) hguard34
  by_cases hguard35 : N ≤ 144000
  · exact h035.2 N (Nat.lt_of_not_ge hguard34) hguard35
  by_cases hguard36 : N ≤ 148000
  · exact h036.2 N (Nat.lt_of_not_ge hguard35) hguard36
  by_cases hguard37 : N ≤ 152000
  · exact h037.2 N (Nat.lt_of_not_ge hguard36) hguard37
  by_cases hguard38 : N ≤ 156000
  · exact h038.2 N (Nat.lt_of_not_ge hguard37) hguard38
  by_cases hguard39 : N ≤ 160000
  · exact h039.2 N (Nat.lt_of_not_ge hguard38) hguard39
  by_cases hguard40 : N ≤ 164000
  · exact h040.2 N (Nat.lt_of_not_ge hguard39) hguard40
  by_cases hguard41 : N ≤ 168000
  · exact h041.2 N (Nat.lt_of_not_ge hguard40) hguard41
  by_cases hguard42 : N ≤ 172000
  · exact h042.2 N (Nat.lt_of_not_ge hguard41) hguard42
  by_cases hguard43 : N ≤ 176000
  · exact h043.2 N (Nat.lt_of_not_ge hguard42) hguard43
  by_cases hguard44 : N ≤ 180000
  · exact h044.2 N (Nat.lt_of_not_ge hguard43) hguard44
  by_cases hguard45 : N ≤ 184000
  · exact h045.2 N (Nat.lt_of_not_ge hguard44) hguard45
  by_cases hguard46 : N ≤ 188000
  · exact h046.2 N (Nat.lt_of_not_ge hguard45) hguard46
  by_cases hguard47 : N ≤ 192000
  · exact h047.2 N (Nat.lt_of_not_ge hguard46) hguard47
  by_cases hguard48 : N ≤ 196000
  · exact h048.2 N (Nat.lt_of_not_ge hguard47) hguard48
  by_cases hguard49 : N ≤ 200000
  · exact h049.2 N (Nat.lt_of_not_ge hguard48) hguard49
  by_cases hguard50 : N ≤ 204000
  · exact h050.2 N (Nat.lt_of_not_ge hguard49) hguard50
  by_cases hguard51 : N ≤ 208000
  · exact h051.2 N (Nat.lt_of_not_ge hguard50) hguard51
  by_cases hguard52 : N ≤ 212000
  · exact h052.2 N (Nat.lt_of_not_ge hguard51) hguard52
  by_cases hguard53 : N ≤ 216000
  · exact h053.2 N (Nat.lt_of_not_ge hguard52) hguard53
  by_cases hguard54 : N ≤ 220000
  · exact h054.2 N (Nat.lt_of_not_ge hguard53) hguard54
  by_cases hguard55 : N ≤ 224000
  · exact h055.2 N (Nat.lt_of_not_ge hguard54) hguard55
  by_cases hguard56 : N ≤ 228000
  · exact h056.2 N (Nat.lt_of_not_ge hguard55) hguard56
  by_cases hguard57 : N ≤ 232000
  · exact h057.2 N (Nat.lt_of_not_ge hguard56) hguard57
  by_cases hguard58 : N ≤ 236000
  · exact h058.2 N (Nat.lt_of_not_ge hguard57) hguard58
  by_cases hguard59 : N ≤ 240000
  · exact h059.2 N (Nat.lt_of_not_ge hguard58) hguard59
  by_cases hguard60 : N ≤ 244000
  · exact h060.2 N (Nat.lt_of_not_ge hguard59) hguard60
  by_cases hguard61 : N ≤ 248000
  · exact h061.2 N (Nat.lt_of_not_ge hguard60) hguard61
  by_cases hguard62 : N ≤ 252000
  · exact h062.2 N (Nat.lt_of_not_ge hguard61) hguard62
  by_cases hguard63 : N ≤ 256000
  · exact h063.2 N (Nat.lt_of_not_ge hguard62) hguard63
  by_cases hguard64 : N ≤ 260000
  · exact h064.2 N (Nat.lt_of_not_ge hguard63) hguard64
  by_cases hguard65 : N ≤ 264000
  · exact h065.2 N (Nat.lt_of_not_ge hguard64) hguard65
  by_cases hguard66 : N ≤ 268000
  · exact h066.2 N (Nat.lt_of_not_ge hguard65) hguard66
  by_cases hguard67 : N ≤ 272000
  · exact h067.2 N (Nat.lt_of_not_ge hguard66) hguard67
  by_cases hguard68 : N ≤ 276000
  · exact h068.2 N (Nat.lt_of_not_ge hguard67) hguard68
  by_cases hguard69 : N ≤ 280000
  · exact h069.2 N (Nat.lt_of_not_ge hguard68) hguard69
  by_cases hguard70 : N ≤ 284000
  · exact h070.2 N (Nat.lt_of_not_ge hguard69) hguard70
  by_cases hguard71 : N ≤ 288000
  · exact h071.2 N (Nat.lt_of_not_ge hguard70) hguard71
  by_cases hguard72 : N ≤ 292000
  · exact h072.2 N (Nat.lt_of_not_ge hguard71) hguard72
  by_cases hguard73 : N ≤ 296000
  · exact h073.2 N (Nat.lt_of_not_ge hguard72) hguard73
  by_cases hguard74 : N ≤ 300000
  · exact h074.2 N (Nat.lt_of_not_ge hguard73) hguard74
  by_cases hguard75 : N ≤ 304000
  · exact h075.2 N (Nat.lt_of_not_ge hguard74) hguard75
  by_cases hguard76 : N ≤ 308000
  · exact h076.2 N (Nat.lt_of_not_ge hguard75) hguard76
  by_cases hguard77 : N ≤ 312000
  · exact h077.2 N (Nat.lt_of_not_ge hguard76) hguard77
  by_cases hguard78 : N ≤ 316000
  · exact h078.2 N (Nat.lt_of_not_ge hguard77) hguard78
  by_cases hguard79 : N ≤ 320000
  · exact h079.2 N (Nat.lt_of_not_ge hguard78) hguard79
  by_cases hguard80 : N ≤ 324000
  · exact h080.2 N (Nat.lt_of_not_ge hguard79) hguard80
  by_cases hguard81 : N ≤ 328000
  · exact h081.2 N (Nat.lt_of_not_ge hguard80) hguard81
  by_cases hguard82 : N ≤ 332000
  · exact h082.2 N (Nat.lt_of_not_ge hguard81) hguard82
  by_cases hguard83 : N ≤ 336000
  · exact h083.2 N (Nat.lt_of_not_ge hguard82) hguard83
  by_cases hguard84 : N ≤ 340000
  · exact h084.2 N (Nat.lt_of_not_ge hguard83) hguard84
  by_cases hguard85 : N ≤ 344000
  · exact h085.2 N (Nat.lt_of_not_ge hguard84) hguard85
  by_cases hguard86 : N ≤ 348000
  · exact h086.2 N (Nat.lt_of_not_ge hguard85) hguard86
  by_cases hguard87 : N ≤ 352000
  · exact h087.2 N (Nat.lt_of_not_ge hguard86) hguard87
  by_cases hguard88 : N ≤ 356000
  · exact h088.2 N (Nat.lt_of_not_ge hguard87) hguard88
  by_cases hguard89 : N ≤ 360000
  · exact h089.2 N (Nat.lt_of_not_ge hguard88) hguard89
  by_cases hguard90 : N ≤ 364000
  · exact h090.2 N (Nat.lt_of_not_ge hguard89) hguard90
  by_cases hguard91 : N ≤ 368000
  · exact h091.2 N (Nat.lt_of_not_ge hguard90) hguard91
  by_cases hguard92 : N ≤ 372000
  · exact h092.2 N (Nat.lt_of_not_ge hguard91) hguard92
  by_cases hguard93 : N ≤ 376000
  · exact h093.2 N (Nat.lt_of_not_ge hguard92) hguard93
  by_cases hguard94 : N ≤ 380000
  · exact h094.2 N (Nat.lt_of_not_ge hguard93) hguard94
  by_cases hguard95 : N ≤ 384000
  · exact h095.2 N (Nat.lt_of_not_ge hguard94) hguard95
  by_cases hguard96 : N ≤ 388000
  · exact h096.2 N (Nat.lt_of_not_ge hguard95) hguard96
  by_cases hguard97 : N ≤ 392000
  · exact h097.2 N (Nat.lt_of_not_ge hguard96) hguard97
  by_cases hguard98 : N ≤ 396000
  · exact h098.2 N (Nat.lt_of_not_ge hguard97) hguard98
  by_cases hguard99 : N ≤ 400000
  · exact h099.2 N (Nat.lt_of_not_ge hguard98) hguard99
  by_cases hguard100 : N ≤ 404000
  · exact h100.2 N (Nat.lt_of_not_ge hguard99) hguard100
  by_cases hguard101 : N ≤ 408000
  · exact h101.2 N (Nat.lt_of_not_ge hguard100) hguard101
  by_cases hguard102 : N ≤ 412000
  · exact h102.2 N (Nat.lt_of_not_ge hguard101) hguard102
  by_cases hguard103 : N ≤ 416000
  · exact h103.2 N (Nat.lt_of_not_ge hguard102) hguard103
  by_cases hguard104 : N ≤ 420000
  · exact h104.2 N (Nat.lt_of_not_ge hguard103) hguard104
  by_cases hguard105 : N ≤ 424000
  · exact h105.2 N (Nat.lt_of_not_ge hguard104) hguard105
  by_cases hguard106 : N ≤ 428000
  · exact h106.2 N (Nat.lt_of_not_ge hguard105) hguard106
  by_cases hguard107 : N ≤ 432000
  · exact h107.2 N (Nat.lt_of_not_ge hguard106) hguard107
  by_cases hguard108 : N ≤ 436000
  · exact h108.2 N (Nat.lt_of_not_ge hguard107) hguard108
  exact h109.2 N (Nat.lt_of_not_ge hguard108) hN

/-- The finite range upper budget at each integer. -/
theorem certified_count (N : ℕ) (hN : N ≤ 438652) :
    ∃ c : ℕ, sqCount N ≤ c ∧ good N c = true :=
  certified_bounds.2 N hN

/-- The upper count at the finite range endpoint. -/
theorem certified_count_endpoint : sqCount 438652 ≤ 266651 := certified_bounds.1

end LeanLab.BS2022GRH.FiniteCount700

#print axioms LeanLab.BS2022GRH.FiniteCount700.certified_count

#print axioms LeanLab.BS2022GRH.FiniteCount700.certified_bounds
#print axioms LeanLab.BS2022GRH.FiniteCount700.certified_count_endpoint
