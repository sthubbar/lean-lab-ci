/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Empirical verification of the even Goldbach
conjecture and computation of prime gaps up to 4·10^18, Math. Comp. 83 (2014) 2033 to 2060.
Read in Claude in Chrome 2026-10-18 from the AMS free PDF, its text taken from the PDF content
streams in the page; run 20261018T1103Z-12430, unit U-0946.
PROVED, zero sorry: Table 4, 68 records of p(n) from 6 to 3325581707333960528, is the lab's
recTable without the row n = 4, p = 2, the paper counting odd primes only; every row has
minGB n = p. Table 5, 131 records of S(p) from p = 3 to 8387, each with minGB S(p) = p, S(p)
increasing, and Sinisalo 1993's 67 rows among them; the next row, p = 8423, has S(p) above
4·10^18. NOT proved: that S(p) is the least such n and that both record lists are complete,
the authors' computation, cited; nor the 4·10^18 range, `Verifications.oesilva`, cited.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.RecordsSummary
import LeanLab.Sinisalo1993.Tables
import LeanLab.OeSHP2014.T5_1
import LeanLab.OeSHP2014.T5_2
import LeanLab.OeSHP2014.T5_3
import LeanLab.OeSHP2014.T5_4

namespace LeanLab.OeSHP2014

open LeanLab.Verifications LeanLab.Verifications.Top50

set_option maxRecDepth 20000

/-- Table 4, rows (n, p(n)). -/
def table4 : List (ℕ × ℕ) := [
    (6, 3),
    (12, 5),
    (30, 7),
    (98, 19),
    (220, 23),
    (308, 31),
    (556, 47),
    (992, 73),
    (2642, 103),
    (5372, 139),
    (7426, 173),
    (43532, 211),
    (54244, 233),
    (63274, 293),
    (113672, 313),
    (128168, 331),
    (194428, 359),
    (194470, 383),
    (413572, 389),
    (503222, 523),
    (1077422, 601),
    (3526958, 727),
    (3807404, 751),
    (10759922, 829),
    (24106882, 929),
    (27789878, 997),
    (37998938, 1039),
    (60119912, 1093),
    (113632822, 1163),
    (187852862, 1321),
    (335070838, 1427),
    (419911924, 1583),
    (721013438, 1789),
    (1847133842, 1861),
    (7473202036, 1877),
    (11001080372, 1879),
    (12703943222, 2029),
    (21248558888, 2089),
    (35884080836, 2803),
    (105963812462, 3061),
    (244885595672, 3163),
    (599533546358, 3457),
    (3132059294006, 3463),
    (3620821173302, 3529),
    (4438327672994, 3613),
    (5320503815888, 3769),
    (8342945544436, 3917),
    (10591605900482, 4003),
    (12982270197518, 4027),
    (15197900994218, 4057),
    (28998050650046, 4327),
    (46878442766282, 4519),
    (76903574497118, 4909),
    (184162477860248, 5077),
    (217361316706568, 5209),
    (389965026819938, 5569),
    (1047610575836828, 6469),
    (6253262345930828, 6961),
    (24925556008175266, 7559),
    (31284177910528922, 7753),
    (121005022304007026, 8443),
    (255329126688555994, 8501),
    (258549426916149682, 8933),
    (555274351556750822, 8941),
    (887123803077837868, 9161),
    (906030579562279642, 9341),
    (2795935116574469638, 9629),
    (3325581707333960528, 9781)]

theorem table4_length : table4.length = 68 := rfl

/-- Table 4 is recTable from n = 6 on. -/
theorem table4_eq_recTable : table4 = (recTable.drop 1).map (fun x => (x.2, x.1)) := by
  decide +kernel

theorem table4_minGB : ∀ x ∈ table4, minGB x.1 = x.2 := by
  intro x hx
  rw [table4_eq_recTable] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact recTable_minGB _ (List.mem_of_mem_drop hy)

/-- Table 5, rows (p, S(p)). -/
def table5 : List (ℕ × ℕ) := [
    (3, 6),
    (5, 12),
    (7, 30),
    (11, 124),
    (17, 418),
    (37, 1274),
    (53, 2512),
    (59, 3526),
    (71, 4618),
    (83, 7432),
    (89, 12778),
    (101, 26098),
    (131, 34192),
    (149, 37768),
    (167, 59914),
    (179, 88786),
    (191, 97768),
    (197, 112558),
    (223, 221942),
    (257, 237544),
    (263, 485326),
    (281, 642358),
    (317, 686638),
    (347, 1042078),
    (379, 1172918),
    (401, 2041402),
    (419, 2406448),
    (463, 4288574),
    (487, 4938848),
    (509, 9292156),
    (521, 14341888),
    (569, 17726098),
    (593, 20757292),
    (659, 32507242),
    (739, 34362758),
    (743, 37890844),
    (761, 49358128),
    (773, 68788066),
    (839, 129796642),
    (853, 144516902),
    (911, 150386932),
    (941, 206892484),
    (977, 247013164),
    (1031, 299434108),
    (1049, 379410652),
    (1061, 554463808),
    (1091, 678546502),
    (1097, 1168888534),
    (1283, 1673268292),
    (1301, 1927528888),
    (1327, 2331465314),
    (1429, 2538833642),
    (1439, 2816593312),
    (1451, 4407165118),
    (1493, 5801828806),
    (1559, 8946630856),
    (1571, 21439965412),
    (1787, 26070202114),
    (1811, 30325742068),
    (1867, 30834371756),
    (1873, 32652627542),
    (1889, 44460316708),
    (1907, 64243962808),
    (1997, 65334725368),
    (2027, 113843130358),
    (2153, 244808993116),
    (2351, 384619217512),
    (2441, 743891046202),
    (2459, 838813974892),
    (2663, 1578084723724),
    (2837, 2541246752056),
    (2963, 3228317220754),
    (2969, 6046500599278),
    (3023, 7119550817194),
    (3137, 7405567522324),
    (3203, 10770353852014),
    (3323, 17455158897256),
    (3449, 18566952590488),
    (3557, 36361448359204),
    (3659, 39028377647218),
    (3677, 40854680372224),
    (3701, 44776706182504),
    (3761, 54133015834948),
    (3863, 60913048745092),
    (3923, 103252325578522),
    (4073, 129987700025542),
    (4079, 143521252289068),
    (4127, 194539179143308),
    (4133, 215285889979816),
    (4241, 280780621153342),
    (4373, 319245515537554),
    (4457, 332638450261204),
    (4523, 445685413500946),
    (4621, 557249554749362),
    (4643, 650204506020934),
    (4679, 666956025101272),
    (4721, 814410862537738),
    (4733, 1025203842512482),
    (4817, 1246578722803144),
    (4937, 1842054285136636),
    (5051, 2303608290775108),
    (5087, 2748443296352086),
    (5227, 3771671520132578),
    (5333, 4463039219937862),
    (5471, 5122498676196358),
    (5483, 6198478168628056),
    (5501, 14211744403075144),
    (5879, 15812379959645512),
    (5903, 20017986381370774),
    (5987, 31821625829250454),
    (6131, 48033787978024768),
    (6263, 55104008958365746),
    (6491, 107157207101894788),
    (6761, 182745307201020658),
    (6899, 237098616193722886),
    (7013, 296540042727113116),
    (7187, 344205743816095468),
    (7307, 370581106766909188),
    (7489, 411411629991722966),
    (7577, 558619547569907716),
    (7649, 754276228832957188),
    (7691, 813695622192168004),
    (7703, 1473611722331822212),
    (7853, 1599566025914318344),
    (7949, 1793167785904803016),
    (8039, 2043437180188810768),
    (8087, 2758163428100238178),
    (8243, 3244400084505812356),
    (8273, 3511797567359760604),
    (8369, 3714759793830649402),
    (8387, 3878297017437646306)]

theorem table5_length : table5.length = 131 := rfl


theorem table5_minGB : ∀ x ∈ table5, minGB x.2 = x.1 := by
  intro x hx
  simp only [table5, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Sinisalo1993.minGB_S_3
  · exact Sinisalo1993.minGB_S_5
  · exact Sinisalo1993.minGB_S_7
  · exact Sinisalo1993.minGB_S_11
  · exact Sinisalo1993.minGB_S_17
  · exact Sinisalo1993.minGB_S_37
  · exact Sinisalo1993.minGB_S_53
  · exact Sinisalo1993.minGB_S_59
  · exact Sinisalo1993.minGB_S_71
  · exact Sinisalo1993.minGB_S_83
  · exact Sinisalo1993.minGB_S_89
  · exact Sinisalo1993.minGB_S_101
  · exact Sinisalo1993.minGB_S_131
  · exact Sinisalo1993.minGB_S_149
  · exact Sinisalo1993.minGB_S_167
  · exact Sinisalo1993.minGB_S_179
  · exact Sinisalo1993.minGB_S_191
  · exact Sinisalo1993.minGB_S_197
  · exact Sinisalo1993.minGB_S_223
  · exact Sinisalo1993.minGB_S_257
  · exact Sinisalo1993.minGB_S_263
  · exact Sinisalo1993.minGB_S_281
  · exact Sinisalo1993.minGB_S_317
  · exact Sinisalo1993.minGB_S_347
  · exact Sinisalo1993.minGB_S_379
  · exact Sinisalo1993.minGB_S_401
  · exact Sinisalo1993.minGB_S_419
  · exact Sinisalo1993.minGB_S_463
  · exact Sinisalo1993.minGB_S_487
  · exact Sinisalo1993.minGB_S_509
  · exact Sinisalo1993.minGB_S_521
  · exact Sinisalo1993.minGB_S_569
  · exact Sinisalo1993.minGB_S_593
  · exact Sinisalo1993.minGB_S_659
  · exact Sinisalo1993.minGB_S_739
  · exact Sinisalo1993.minGB_S_743
  · exact Sinisalo1993.minGB_S_761
  · exact Sinisalo1993.minGB_S_773
  · exact Sinisalo1993.minGB_S_839
  · exact Sinisalo1993.minGB_S_853
  · exact Sinisalo1993.minGB_S_911
  · exact Sinisalo1993.minGB_S_941
  · exact Sinisalo1993.minGB_S_977
  · exact Sinisalo1993.minGB_S_1031
  · exact Sinisalo1993.minGB_S_1049
  · exact Sinisalo1993.minGB_S_1061
  · exact Sinisalo1993.minGB_S_1091
  · exact Sinisalo1993.minGB_S_1097
  · exact Sinisalo1993.minGB_S_1283
  · exact Sinisalo1993.minGB_S_1301
  · exact Sinisalo1993.minGB_S_1327
  · exact Sinisalo1993.minGB_S_1429
  · exact Sinisalo1993.minGB_S_1439
  · exact Sinisalo1993.minGB_S_1451
  · exact Sinisalo1993.minGB_S_1493
  · exact Sinisalo1993.minGB_S_1559
  · exact Sinisalo1993.minGB_S_1571
  · exact Sinisalo1993.minGB_S_1787
  · exact Sinisalo1993.minGB_S_1811
  · exact Sinisalo1993.minGB_S_1867
  · exact Sinisalo1993.minGB_S_1873
  · exact Sinisalo1993.minGB_S_1889
  · exact Sinisalo1993.minGB_S_1907
  · exact Sinisalo1993.minGB_S_1997
  · exact Sinisalo1993.minGB_S_2027
  · exact Sinisalo1993.minGB_S_2153
  · exact Sinisalo1993.minGB_S_2351
  · exact OeSHP2014.minGB_S_2441
  · exact OeSHP2014.minGB_S_2459
  · exact OeSHP2014.minGB_S_2663
  · exact OeSHP2014.minGB_S_2837
  · exact OeSHP2014.minGB_S_2963
  · exact OeSHP2014.minGB_S_2969
  · exact OeSHP2014.minGB_S_3023
  · exact OeSHP2014.minGB_S_3137
  · exact OeSHP2014.minGB_S_3203
  · exact OeSHP2014.minGB_S_3323
  · exact OeSHP2014.minGB_S_3449
  · exact OeSHP2014.minGB_S_3557
  · exact OeSHP2014.minGB_S_3659
  · exact OeSHP2014.minGB_S_3677
  · exact OeSHP2014.minGB_S_3701
  · exact OeSHP2014.minGB_S_3761
  · exact OeSHP2014.minGB_S_3863
  · exact OeSHP2014.minGB_S_3923
  · exact OeSHP2014.minGB_S_4073
  · exact OeSHP2014.minGB_S_4079
  · exact OeSHP2014.minGB_S_4127
  · exact OeSHP2014.minGB_S_4133
  · exact OeSHP2014.minGB_S_4241
  · exact OeSHP2014.minGB_S_4373
  · exact OeSHP2014.minGB_S_4457
  · exact OeSHP2014.minGB_S_4523
  · exact OeSHP2014.minGB_S_4621
  · exact OeSHP2014.minGB_S_4643
  · exact OeSHP2014.minGB_S_4679
  · exact OeSHP2014.minGB_S_4721
  · exact OeSHP2014.minGB_S_4733
  · exact OeSHP2014.minGB_S_4817
  · exact OeSHP2014.minGB_S_4937
  · exact OeSHP2014.minGB_S_5051
  · exact OeSHP2014.minGB_S_5087
  · exact OeSHP2014.minGB_S_5227
  · exact OeSHP2014.minGB_S_5333
  · exact OeSHP2014.minGB_S_5471
  · exact OeSHP2014.minGB_S_5483
  · exact OeSHP2014.minGB_S_5501
  · exact OeSHP2014.minGB_S_5879
  · exact OeSHP2014.minGB_S_5903
  · exact OeSHP2014.minGB_S_5987
  · exact OeSHP2014.minGB_S_6131
  · exact OeSHP2014.minGB_S_6263
  · exact OeSHP2014.minGB_S_6491
  · exact OeSHP2014.minGB_S_6761
  · exact OeSHP2014.minGB_S_6899
  · exact OeSHP2014.minGB_S_7013
  · exact OeSHP2014.minGB_S_7187
  · exact OeSHP2014.minGB_S_7307
  · exact OeSHP2014.minGB_S_7489
  · exact OeSHP2014.minGB_S_7577
  · exact OeSHP2014.minGB_S_7649
  · exact OeSHP2014.minGB_S_7691
  · exact OeSHP2014.minGB_S_7703
  · exact OeSHP2014.minGB_S_7853
  · exact OeSHP2014.minGB_S_7949
  · exact OeSHP2014.minGB_S_8039
  · exact OeSHP2014.minGB_S_8087
  · exact OeSHP2014.minGB_S_8243
  · exact OeSHP2014.minGB_S_8273
  · exact OeSHP2014.minGB_S_8369
  · exact OeSHP2014.minGB_S_8387

theorem table5_increasing : (table5.map Prod.fst).Pairwise (· < ·) ∧
    (table5.map Prod.snd).Pairwise (· < ·) := by decide +kernel

theorem table5_below : ∀ x ∈ table5, x.2 ≤ 4 * 10 ^ 18 := by decide +kernel

/-- Sinisalo 1993 Table 2 is the start of Table 5. -/
theorem sinisalo_sublist : Sinisalo1993.table2 = table5.take 67 := by decide +kernel

end LeanLab.OeSHP2014
