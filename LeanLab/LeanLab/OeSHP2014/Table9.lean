/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Table 9: the 127 record-breaking first
occurrences P(g) of prime gaps below 4·10^18, g from 1 to 1306; the next, g = 1346, has
P(g) above 4·10^18. PROVED, zero sorry: every row is a prime gap, P(g) and P(g) + g
consecutive primes, and P(g) increases with g. Cited: that each is the FIRST gap of size g,
and that the record list is complete. Table 8, the maximal gaps, is the lab's gapTable,
Verifications/Top50/GapsSummary.lean, all 75 rows found in the paper's text this run.
Run 20261018T1103Z-12430, unit U-0946. AI-written Lean code, Claude, 2026-10-18.
-/
import Mathlib
import LeanLab.OeSHP2014.T9_1
import LeanLab.OeSHP2014.T9_2
import LeanLab.OeSHP2014.T9_3
import LeanLab.OeSHP2014.T9_4
import LeanLab.OeSHP2014.T9_5
import LeanLab.OeSHP2014.T9_6

namespace LeanLab.OeSHP2014

open LeanLab.Verifications.Top50.Gaps

set_option maxRecDepth 20000

/-- Table 9, rows (g, P(g)). -/
def table9 : List (ℕ × ℕ) := [
    (1, 2),
    (2, 3),
    (4, 7),
    (6, 23),
    (8, 89),
    (10, 139),
    (12, 199),
    (16, 1831),
    (26, 2477),
    (28, 2971),
    (30, 4297),
    (32, 5591),
    (36, 9551),
    (38, 30593),
    (46, 81463),
    (56, 82073),
    (64, 89689),
    (66, 162143),
    (70, 173359),
    (74, 404597),
    (80, 542603),
    (88, 544279),
    (92, 927869),
    (94, 1100977),
    (102, 1444309),
    (108, 2238823),
    (116, 5845193),
    (124, 6752623),
    (134, 6958667),
    (140, 7621259),
    (142, 10343761),
    (144, 11981443),
    (150, 13626257),
    (156, 17983717),
    (158, 49269581),
    (166, 83751121),
    (186, 147684137),
    (194, 166726367),
    (200, 378043979),
    (224, 409866323),
    (226, 519653371),
    (228, 895858039),
    (254, 1202442089),
    (256, 1872851947),
    (264, 2357881993),
    (278, 4260928601),
    (294, 5692630189),
    (298, 8650524583),
    (314, 8948418749),
    (316, 12109172293),
    (328, 13086861181),
    (334, 30827138509),
    (362, 35877724601),
    (368, 51430518413),
    (370, 59942358571),
    (388, 156798792223),
    (422, 280974865361),
    (436, 367459059871),
    (442, 417470554687),
    (452, 466855187471),
    (466, 565855695631),
    (470, 681753256133),
    (472, 865244709607),
    (482, 1051602787181),
    (488, 1275363152099),
    (506, 1339347750707),
    (508, 1841086484491),
    (510, 2209016910131),
    (518, 2296497058133),
    (520, 2336167262449),
    (536, 5371284217763),
    (568, 6010330572331),
    (576, 8817792098461),
    (580, 9383081340541),
    (590, 20761252261751),
    (608, 20767330530329),
    (624, 24923033918059),
    (626, 33605480400197),
    (628, 34140047613391),
    (632, 45678685880759),
    (646, 51027160468351),
    (654, 54916086007427),
    (656, 65862966031241),
    (676, 78610833115261),
    (680, 82385435331119),
    (688, 110526670235599),
    (708, 143679495784681),
    (722, 218356872845927),
    (752, 255294593822687),
    (764, 323811481625339),
    (768, 423683030575549),
    (774, 469789142849483),
    (780, 471911699384963),
    (782, 726507223559111),
    (796, 1271309838631957),
    (812, 1710270958551941),
    (848, 2537070652896083),
    (866, 2759317684446707),
    (882, 3371055452381147),
    (886, 4127074165753081),
    (898, 4198168149492463),
    (922, 4286129201882221),
    (926, 6381944136489827),
    (928, 10244316228469423),
    (932, 10676480515967939),
    (968, 19124990244992669),
    (980, 19403684901755939),
    (986, 34847474118974633),
    (1006, 37343192296558573),
    (1018, 37967240836435909),
    (1040, 46246848392875127),
    (1048, 88089672331629091),
    (1052, 89219242873419107),
    (1066, 98436147540371287),
    (1094, 139033656446725643),
    (1114, 198887512806988729),
    (1124, 203153416523088323),
    (1144, 236552906662007587),
    (1150, 293464161465135373),
    (1172, 400240934741322419),
    (1186, 404444692323376357),
    (1192, 703390724952490921),
    (1202, 819615344996114321),
    (1208, 1331711247969025019),
    (1264, 1798556720194308703),
    (1290, 2980707563031238363),
    (1306, 3278018069102480227)]

theorem table9_length : table9.length = 127 := by decide

theorem table9_isGap : ∀ x ∈ table9, IsGapAt x.2 x.1 := by
  intro x hx
  simp only [table9, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact gap9_1
  · exact gap9_2
  · exact gap9_4
  · exact gap9_6
  · exact gap9_8
  · exact gap9_10
  · exact gap9_12
  · exact gap9_16
  · exact gap9_26
  · exact gap9_28
  · exact gap9_30
  · exact gap9_32
  · exact gap9_36
  · exact gap9_38
  · exact gap9_46
  · exact gap9_56
  · exact gap9_64
  · exact gap9_66
  · exact gap9_70
  · exact gap9_74
  · exact gap9_80
  · exact gap9_88
  · exact gap9_92
  · exact gap9_94
  · exact gap9_102
  · exact gap9_108
  · exact gap9_116
  · exact gap9_124
  · exact gap9_134
  · exact gap9_140
  · exact gap9_142
  · exact gap9_144
  · exact gap9_150
  · exact gap9_156
  · exact gap9_158
  · exact gap9_166
  · exact gap9_186
  · exact gap9_194
  · exact gap9_200
  · exact gap9_224
  · exact gap9_226
  · exact gap9_228
  · exact gap9_254
  · exact gap9_256
  · exact gap9_264
  · exact gap9_278
  · exact gap9_294
  · exact gap9_298
  · exact gap9_314
  · exact gap9_316
  · exact gap9_328
  · exact gap9_334
  · exact gap9_362
  · exact gap9_368
  · exact gap9_370
  · exact gap9_388
  · exact gap9_422
  · exact gap9_436
  · exact gap9_442
  · exact gap9_452
  · exact gap9_466
  · exact gap9_470
  · exact gap9_472
  · exact gap9_482
  · exact gap9_488
  · exact gap9_506
  · exact gap9_508
  · exact gap9_510
  · exact gap9_518
  · exact gap9_520
  · exact gap9_536
  · exact gap9_568
  · exact gap9_576
  · exact gap9_580
  · exact gap9_590
  · exact gap9_608
  · exact gap9_624
  · exact gap9_626
  · exact gap9_628
  · exact gap9_632
  · exact gap9_646
  · exact gap9_654
  · exact gap9_656
  · exact gap9_676
  · exact gap9_680
  · exact gap9_688
  · exact gap9_708
  · exact gap9_722
  · exact gap9_752
  · exact gap9_764
  · exact gap9_768
  · exact gap9_774
  · exact gap9_780
  · exact gap9_782
  · exact gap9_796
  · exact gap9_812
  · exact gap9_848
  · exact gap9_866
  · exact gap9_882
  · exact gap9_886
  · exact gap9_898
  · exact gap9_922
  · exact gap9_926
  · exact gap9_928
  · exact gap9_932
  · exact gap9_968
  · exact gap9_980
  · exact gap9_986
  · exact gap9_1006
  · exact gap9_1018
  · exact gap9_1040
  · exact gap9_1048
  · exact gap9_1052
  · exact gap9_1066
  · exact gap9_1094
  · exact gap9_1114
  · exact gap9_1124
  · exact gap9_1144
  · exact gap9_1150
  · exact gap9_1172
  · exact gap9_1186
  · exact gap9_1192
  · exact gap9_1202
  · exact gap9_1208
  · exact gap9_1264
  · exact gap9_1290
  · exact gap9_1306

theorem table9_increasing : (table9.map Prod.fst).Pairwise (· < ·) ∧
    (table9.map Prod.snd).Pairwise (· < ·) := by decide +kernel

end LeanLab.OeSHP2014
