/-
Maximal prime gap records below 4e18, OEIS A002386 rows 1 to 75, read 2026-10-17; row 75 is the
1476 gap of P0005. PROVED, zero sorry: for each listed p, the gap g to the next prime is as
tabulated, and the 75 gaps strictly increase. NOT proved: that each is a maximal gap, that is,
no earlier gap is as long, and that 1476 is the largest gap below 4e18. Those are the
searches of Nicely, Oliveira e Silva and others, cited in OeSHPTables.lean as maxGap.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Gaps1
import LeanLab.Verifications.Top50.Gaps2
import LeanLab.Verifications.Top50.Gaps3

namespace LeanLab.Verifications.Top50.Gaps

/-- A002386 rows 1 to 75 with their gaps, as pairs (p, g). -/
def gapTable : List (ℕ × ℕ) := [
    (2, 1),
    (3, 2),
    (7, 4),
    (23, 6),
    (89, 8),
    (113, 14),
    (523, 18),
    (887, 20),
    (1129, 22),
    (1327, 34),
    (9551, 36),
    (15683, 44),
    (19609, 52),
    (31397, 72),
    (155921, 86),
    (360653, 96),
    (370261, 112),
    (492113, 114),
    (1349533, 118),
    (1357201, 132),
    (2010733, 148),
    (4652353, 154),
    (17051707, 180),
    (20831323, 210),
    (47326693, 220),
    (122164747, 222),
    (189695659, 234),
    (191912783, 248),
    (387096133, 250),
    (436273009, 282),
    (1294268491, 288),
    (1453168141, 292),
    (2300942549, 320),
    (3842610773, 336),
    (4302407359, 354),
    (10726904659, 382),
    (20678048297, 384),
    (22367084959, 394),
    (25056082087, 456),
    (42652618343, 464),
    (127976334671, 468),
    (182226896239, 474),
    (241160624143, 486),
    (297501075799, 490),
    (303371455241, 500),
    (304599508537, 514),
    (416608695821, 516),
    (461690510011, 532),
    (614487453523, 534),
    (738832927927, 540),
    (1346294310749, 582),
    (1408695493609, 588),
    (1968188556461, 602),
    (2614941710599, 652),
    (7177162611713, 674),
    (13829048559701, 716),
    (19581334192423, 766),
    (42842283925351, 778),
    (90874329411493, 804),
    (171231342420521, 806),
    (218209405436543, 906),
    (1189459969825483, 916),
    (1686994940955803, 924),
    (1693182318746371, 1132),
    (43841547845541059, 1184),
    (55350776431903243, 1198),
    (80873624627234849, 1220),
    (203986478517455989, 1224),
    (218034721194214273, 1248),
    (305405826521087869, 1272),
    (352521223451364323, 1328),
    (401429925999153707, 1356),
    (418032645936712127, 1370),
    (804212830686677669, 1442),
    (1425172824437699411, 1476)]

/-- Every listed p is followed by the next prime exactly g later. -/
theorem gapTable_isGap : ∀ x ∈ gapTable, IsGapAt x.1 x.2 := by
  intro x hx
  simp only [gapTable, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Gaps1.gap_2
  · exact Gaps1.gap_3
  · exact Gaps1.gap_7
  · exact Gaps1.gap_23
  · exact Gaps1.gap_89
  · exact Gaps1.gap_113
  · exact Gaps1.gap_523
  · exact Gaps1.gap_887
  · exact Gaps1.gap_1129
  · exact Gaps1.gap_1327
  · exact Gaps1.gap_9551
  · exact Gaps1.gap_15683
  · exact Gaps1.gap_19609
  · exact Gaps1.gap_31397
  · exact Gaps1.gap_155921
  · exact Gaps1.gap_360653
  · exact Gaps1.gap_370261
  · exact Gaps1.gap_492113
  · exact Gaps1.gap_1349533
  · exact Gaps1.gap_1357201
  · exact Gaps1.gap_2010733
  · exact Gaps1.gap_4652353
  · exact Gaps1.gap_17051707
  · exact Gaps1.gap_20831323
  · exact Gaps1.gap_47326693
  · exact Gaps1.gap_122164747
  · exact Gaps1.gap_189695659
  · exact Gaps1.gap_191912783
  · exact Gaps1.gap_387096133
  · exact Gaps1.gap_436273009
  · exact Gaps1.gap_1294268491
  · exact Gaps1.gap_1453168141
  · exact Gaps1.gap_2300942549
  · exact Gaps1.gap_3842610773
  · exact Gaps1.gap_4302407359
  · exact Gaps1.gap_10726904659
  · exact Gaps1.gap_20678048297
  · exact Gaps1.gap_22367084959
  · exact Gaps1.gap_25056082087
  · exact Gaps1.gap_42652618343
  · exact Gaps2.gap_127976334671
  · exact Gaps2.gap_182226896239
  · exact Gaps2.gap_241160624143
  · exact Gaps2.gap_297501075799
  · exact Gaps2.gap_303371455241
  · exact Gaps2.gap_304599508537
  · exact Gaps2.gap_416608695821
  · exact Gaps2.gap_461690510011
  · exact Gaps2.gap_614487453523
  · exact Gaps2.gap_738832927927
  · exact Gaps2.gap_1346294310749
  · exact Gaps2.gap_1408695493609
  · exact Gaps2.gap_1968188556461
  · exact Gaps2.gap_2614941710599
  · exact Gaps2.gap_7177162611713
  · exact Gaps2.gap_13829048559701
  · exact Gaps2.gap_19581334192423
  · exact Gaps2.gap_42842283925351
  · exact Gaps2.gap_90874329411493
  · exact Gaps2.gap_171231342420521
  · exact Gaps3.gap_218209405436543
  · exact Gaps3.gap_1189459969825483
  · exact Gaps3.gap_1686994940955803
  · exact Gaps3.gap_1693182318746371
  · exact Gaps3.gap_43841547845541059
  · exact Gaps3.gap_55350776431903243
  · exact Gaps3.gap_80873624627234849
  · exact Gaps3.gap_203986478517455989
  · exact Gaps3.gap_218034721194214273
  · exact Gaps3.gap_305405826521087869
  · exact Gaps3.gap_352521223451364323
  · exact Gaps3.gap_401429925999153707
  · exact Gaps3.gap_418032645936712127
  · exact Gaps3.gap_804212830686677669
  · exact Gaps3.gap_1425172824437699411

/-- The listed gaps strictly increase, as maximal gap records must. -/
theorem gapTable_increasing : (gapTable.map Prod.snd).Pairwise (· < ·) := by decide +kernel

/-- The last row: the gap 1476 after 1425172824437699411, zero sorry. -/
theorem gap_1476 : IsGapAt 1425172824437699411 1476 := Gaps3.gap_1425172824437699411

end LeanLab.Verifications.Top50.Gaps
