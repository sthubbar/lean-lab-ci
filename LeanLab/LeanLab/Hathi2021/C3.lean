/-
P0080 Hathi 2021, arXiv 2109.13174v3, page 11: **`c₃ ≤ 1.3904`**, and the sharper `c₃ ≤ 1.3903998`.
`c₃ = ∏_{p > 5} (1 + 1/c(p))/(1 + 1/(p - 1))`, true value 1.3903990, so the printed bound has slack
about 1.0·10⁻⁶. Head: the rounded-up chain over survivors `7 ≤ n < 2000007`, 100 kernel windows of
20000 in C3W0 to C3W9, last value 1390398781179656047 at scale 10¹⁸. Tail: `T(2000007)`, C3Tail.lean.
Unit U-6154, CLOUD 20261020T0717Z-cloud37. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN. KNOWN mathematics; this checks a printed constant.
-/
import LeanLab.Hathi2021.C3Tail
import LeanLab.Hathi2021.C3W0
import LeanLab.Hathi2021.C3W1
import LeanLab.Hathi2021.C3W2
import LeanLab.Hathi2021.C3W3
import LeanLab.Hathi2021.C3W4
import LeanLab.Hathi2021.C3W5
import LeanLab.Hathi2021.C3W6
import LeanLab.Hathi2021.C3W7
import LeanLab.Hathi2021.C3W8
import LeanLab.Hathi2021.C3W9

namespace LeanLab.Hathi2021.C3
open Real Finset

/-- The 100 windows composed: the chain over `7 ≤ n < 2000007`. -/
theorem chain_total : chainFrom 1000000000000000000 7 2000000 = 1390398781179656047 := by
  have e0 : chainFrom 1000000000000000000 7 20000 = 1390366936226152044 := w0
  have e1 : chainFrom 1000000000000000000 7 40000 = 1390383952519771231 := by
    rw [show (40000 : ℕ) = 20000 + 20000 from rfl, chainFrom_add, e0]; exact w1
  have e2 : chainFrom 1000000000000000000 7 60000 = 1390389326648478337 := by
    rw [show (60000 : ℕ) = 40000 + 20000 from rfl, chainFrom_add, e1]; exact w2
  have e3 : chainFrom 1000000000000000000 7 80000 = 1390391902863964598 := by
    rw [show (80000 : ℕ) = 60000 + 20000 from rfl, chainFrom_add, e2]; exact w3
  have e4 : chainFrom 1000000000000000000 7 100000 = 1390393429496423025 := by
    rw [show (100000 : ℕ) = 80000 + 20000 from rfl, chainFrom_add, e3]; exact w4
  have e5 : chainFrom 1000000000000000000 7 120000 = 1390394419179976699 := by
    rw [show (120000 : ℕ) = 100000 + 20000 from rfl, chainFrom_add, e4]; exact w5
  have e6 : chainFrom 1000000000000000000 7 140000 = 1390395126729664792 := by
    rw [show (140000 : ℕ) = 120000 + 20000 from rfl, chainFrom_add, e5]; exact w6
  have e7 : chainFrom 1000000000000000000 7 160000 = 1390395646379883685 := by
    rw [show (160000 : ℕ) = 140000 + 20000 from rfl, chainFrom_add, e6]; exact w7
  have e8 : chainFrom 1000000000000000000 7 180000 = 1390396046319286623 := by
    rw [show (180000 : ℕ) = 160000 + 20000 from rfl, chainFrom_add, e7]; exact w8
  have e9 : chainFrom 1000000000000000000 7 200000 = 1390396363308644442 := by
    rw [show (200000 : ℕ) = 180000 + 20000 from rfl, chainFrom_add, e8]; exact w9
  have e10 : chainFrom 1000000000000000000 7 220000 = 1390396621219459607 := by
    rw [show (220000 : ℕ) = 200000 + 20000 from rfl, chainFrom_add, e9]; exact w10
  have e11 : chainFrom 1000000000000000000 7 240000 = 1390396832398981856 := by
    rw [show (240000 : ℕ) = 220000 + 20000 from rfl, chainFrom_add, e10]; exact w11
  have e12 : chainFrom 1000000000000000000 7 260000 = 1390397012652997381 := by
    rw [show (260000 : ℕ) = 240000 + 20000 from rfl, chainFrom_add, e11]; exact w12
  have e13 : chainFrom 1000000000000000000 7 280000 = 1390397164993174461 := by
    rw [show (280000 : ℕ) = 260000 + 20000 from rfl, chainFrom_add, e12]; exact w13
  have e14 : chainFrom 1000000000000000000 7 300000 = 1390397294537688844 := by
    rw [show (300000 : ℕ) = 280000 + 20000 from rfl, chainFrom_add, e13]; exact w14
  have e15 : chainFrom 1000000000000000000 7 320000 = 1390397411184197116 := by
    rw [show (320000 : ℕ) = 300000 + 20000 from rfl, chainFrom_add, e14]; exact w15
  have e16 : chainFrom 1000000000000000000 7 340000 = 1390397511813145563 := by
    rw [show (340000 : ℕ) = 320000 + 20000 from rfl, chainFrom_add, e15]; exact w16
  have e17 : chainFrom 1000000000000000000 7 360000 = 1390397601301655123 := by
    rw [show (360000 : ℕ) = 340000 + 20000 from rfl, chainFrom_add, e16]; exact w17
  have e18 : chainFrom 1000000000000000000 7 380000 = 1390397679690435042 := by
    rw [show (380000 : ℕ) = 360000 + 20000 from rfl, chainFrom_add, e17]; exact w18
  have e19 : chainFrom 1000000000000000000 7 400000 = 1390397751012400226 := by
    rw [show (400000 : ℕ) = 380000 + 20000 from rfl, chainFrom_add, e18]; exact w19
  have e20 : chainFrom 1000000000000000000 7 420000 = 1390397814318420057 := by
    rw [show (420000 : ℕ) = 400000 + 20000 from rfl, chainFrom_add, e19]; exact w20
  have e21 : chainFrom 1000000000000000000 7 440000 = 1390397872623453514 := by
    rw [show (440000 : ℕ) = 420000 + 20000 from rfl, chainFrom_add, e20]; exact w21
  have e22 : chainFrom 1000000000000000000 7 460000 = 1390397924761258946 := by
    rw [show (460000 : ℕ) = 440000 + 20000 from rfl, chainFrom_add, e21]; exact w22
  have e23 : chainFrom 1000000000000000000 7 480000 = 1390397973459015431 := by
    rw [show (480000 : ℕ) = 460000 + 20000 from rfl, chainFrom_add, e22]; exact w23
  have e24 : chainFrom 1000000000000000000 7 500000 = 1390398017854859606 := by
    rw [show (500000 : ℕ) = 480000 + 20000 from rfl, chainFrom_add, e23]; exact w24
  have e25 : chainFrom 1000000000000000000 7 520000 = 1390398058564022036 := by
    rw [show (520000 : ℕ) = 500000 + 20000 from rfl, chainFrom_add, e24]; exact w25
  have e26 : chainFrom 1000000000000000000 7 540000 = 1390398095984189157 := by
    rw [show (540000 : ℕ) = 520000 + 20000 from rfl, chainFrom_add, e25]; exact w26
  have e27 : chainFrom 1000000000000000000 7 560000 = 1390398130469078636 := by
    rw [show (560000 : ℕ) = 540000 + 20000 from rfl, chainFrom_add, e26]; exact w27
  have e28 : chainFrom 1000000000000000000 7 580000 = 1390398162932953228 := by
    rw [show (580000 : ℕ) = 560000 + 20000 from rfl, chainFrom_add, e27]; exact w28
  have e29 : chainFrom 1000000000000000000 7 600000 = 1390398193081967242 := by
    rw [show (600000 : ℕ) = 580000 + 20000 from rfl, chainFrom_add, e28]; exact w29
  have e30 : chainFrom 1000000000000000000 7 620000 = 1390398221395310036 := by
    rw [show (620000 : ℕ) = 600000 + 20000 from rfl, chainFrom_add, e29]; exact w30
  have e31 : chainFrom 1000000000000000000 7 640000 = 1390398246994876671 := by
    rw [show (640000 : ℕ) = 620000 + 20000 from rfl, chainFrom_add, e30]; exact w31
  have e32 : chainFrom 1000000000000000000 7 660000 = 1390398271534374887 := by
    rw [show (660000 : ℕ) = 640000 + 20000 from rfl, chainFrom_add, e31]; exact w32
  have e33 : chainFrom 1000000000000000000 7 680000 = 1390398294752873607 := by
    rw [show (680000 : ℕ) = 660000 + 20000 from rfl, chainFrom_add, e32]; exact w33
  have e34 : chainFrom 1000000000000000000 7 700000 = 1390398316371285417 := by
    rw [show (700000 : ℕ) = 680000 + 20000 from rfl, chainFrom_add, e33]; exact w34
  have e35 : chainFrom 1000000000000000000 7 720000 = 1390398336863355640 := by
    rw [show (720000 : ℕ) = 700000 + 20000 from rfl, chainFrom_add, e34]; exact w35
  have e36 : chainFrom 1000000000000000000 7 740000 = 1390398356464248092 := by
    rw [show (740000 : ℕ) = 720000 + 20000 from rfl, chainFrom_add, e35]; exact w36
  have e37 : chainFrom 1000000000000000000 7 760000 = 1390398374344587347 := by
    rw [show (760000 : ℕ) = 740000 + 20000 from rfl, chainFrom_add, e36]; exact w37
  have e38 : chainFrom 1000000000000000000 7 780000 = 1390398391822393565 := by
    rw [show (780000 : ℕ) = 760000 + 20000 from rfl, chainFrom_add, e37]; exact w38
  have e39 : chainFrom 1000000000000000000 7 800000 = 1390398408345295646 := by
    rw [show (800000 : ℕ) = 780000 + 20000 from rfl, chainFrom_add, e38]; exact w39
  have e40 : chainFrom 1000000000000000000 7 820000 = 1390398423871497540 := by
    rw [show (820000 : ℕ) = 800000 + 20000 from rfl, chainFrom_add, e39]; exact w40
  have e41 : chainFrom 1000000000000000000 7 840000 = 1390398438753244221 := by
    rw [show (840000 : ℕ) = 820000 + 20000 from rfl, chainFrom_add, e40]; exact w41
  have e42 : chainFrom 1000000000000000000 7 860000 = 1390398452726938691 := by
    rw [show (860000 : ℕ) = 840000 + 20000 from rfl, chainFrom_add, e41]; exact w42
  have e43 : chainFrom 1000000000000000000 7 880000 = 1390398466342323496 := by
    rw [show (880000 : ℕ) = 860000 + 20000 from rfl, chainFrom_add, e42]; exact w43
  have e44 : chainFrom 1000000000000000000 7 900000 = 1390398479081116229 := by
    rw [show (900000 : ℕ) = 880000 + 20000 from rfl, chainFrom_add, e43]; exact w44
  have e45 : chainFrom 1000000000000000000 7 920000 = 1390398491331936259 := by
    rw [show (920000 : ℕ) = 900000 + 20000 from rfl, chainFrom_add, e44]; exact w45
  have e46 : chainFrom 1000000000000000000 7 940000 = 1390398503030728679 := by
    rw [show (940000 : ℕ) = 920000 + 20000 from rfl, chainFrom_add, e45]; exact w46
  have e47 : chainFrom 1000000000000000000 7 960000 = 1390398514041510150 := by
    rw [show (960000 : ℕ) = 940000 + 20000 from rfl, chainFrom_add, e46]; exact w47
  have e48 : chainFrom 1000000000000000000 7 980000 = 1390398524751962459 := by
    rw [show (980000 : ℕ) = 960000 + 20000 from rfl, chainFrom_add, e47]; exact w48
  have e49 : chainFrom 1000000000000000000 7 1000000 = 1390398534909428606 := by
    rw [show (1000000 : ℕ) = 980000 + 20000 from rfl, chainFrom_add, e48]; exact w49
  have e50 : chainFrom 1000000000000000000 7 1020000 = 1390398544943787554 := by
    rw [show (1020000 : ℕ) = 1000000 + 20000 from rfl, chainFrom_add, e49]; exact w50
  have e51 : chainFrom 1000000000000000000 7 1040000 = 1390398554331111813 := by
    rw [show (1040000 : ℕ) = 1020000 + 20000 from rfl, chainFrom_add, e50]; exact w51
  have e52 : chainFrom 1000000000000000000 7 1060000 = 1390398563344373881 := by
    rw [show (1060000 : ℕ) = 1040000 + 20000 from rfl, chainFrom_add, e51]; exact w52
  have e53 : chainFrom 1000000000000000000 7 1080000 = 1390398572075843516 := by
    rw [show (1080000 : ℕ) = 1060000 + 20000 from rfl, chainFrom_add, e52]; exact w53
  have e54 : chainFrom 1000000000000000000 7 1100000 = 1390398580526192571 := by
    rw [show (1100000 : ℕ) = 1080000 + 20000 from rfl, chainFrom_add, e53]; exact w54
  have e55 : chainFrom 1000000000000000000 7 1120000 = 1390398588727034997 := by
    rw [show (1120000 : ℕ) = 1100000 + 20000 from rfl, chainFrom_add, e54]; exact w55
  have e56 : chainFrom 1000000000000000000 7 1140000 = 1390398596540456944 := by
    rw [show (1140000 : ℕ) = 1120000 + 20000 from rfl, chainFrom_add, e55]; exact w56
  have e57 : chainFrom 1000000000000000000 7 1160000 = 1390398604046360429 := by
    rw [show (1160000 : ℕ) = 1140000 + 20000 from rfl, chainFrom_add, e56]; exact w57
  have e58 : chainFrom 1000000000000000000 7 1180000 = 1390398611462210317 := by
    rw [show (1180000 : ℕ) = 1160000 + 20000 from rfl, chainFrom_add, e57]; exact w58
  have e59 : chainFrom 1000000000000000000 7 1200000 = 1390398618572415241 := by
    rw [show (1200000 : ℕ) = 1180000 + 20000 from rfl, chainFrom_add, e58]; exact w59
  have e60 : chainFrom 1000000000000000000 7 1220000 = 1390398625312844823 := by
    rw [show (1220000 : ℕ) = 1200000 + 20000 from rfl, chainFrom_add, e59]; exact w60
  have e61 : chainFrom 1000000000000000000 7 1240000 = 1390398631685903951 := by
    rw [show (1240000 : ℕ) = 1220000 + 20000 from rfl, chainFrom_add, e60]; exact w61
  have e62 : chainFrom 1000000000000000000 7 1260000 = 1390398638079327284 := by
    rw [show (1260000 : ℕ) = 1240000 + 20000 from rfl, chainFrom_add, e61]; exact w62
  have e63 : chainFrom 1000000000000000000 7 1280000 = 1390398644235196449 := by
    rw [show (1280000 : ℕ) = 1260000 + 20000 from rfl, chainFrom_add, e62]; exact w63
  have e64 : chainFrom 1000000000000000000 7 1300000 = 1390398650130755724 := by
    rw [show (1300000 : ℕ) = 1280000 + 20000 from rfl, chainFrom_add, e63]; exact w64
  have e65 : chainFrom 1000000000000000000 7 1320000 = 1390398655851611888 := by
    rw [show (1320000 : ℕ) = 1300000 + 20000 from rfl, chainFrom_add, e64]; exact w65
  have e66 : chainFrom 1000000000000000000 7 1340000 = 1390398661429226448 := by
    rw [show (1340000 : ℕ) = 1320000 + 20000 from rfl, chainFrom_add, e65]; exact w66
  have e67 : chainFrom 1000000000000000000 7 1360000 = 1390398666793008254 := by
    rw [show (1360000 : ℕ) = 1340000 + 20000 from rfl, chainFrom_add, e66]; exact w67
  have e68 : chainFrom 1000000000000000000 7 1380000 = 1390398672096698682 := by
    rw [show (1380000 : ℕ) = 1360000 + 20000 from rfl, chainFrom_add, e67]; exact w68
  have e69 : chainFrom 1000000000000000000 7 1400000 = 1390398677262123798 := by
    rw [show (1400000 : ℕ) = 1380000 + 20000 from rfl, chainFrom_add, e68]; exact w69
  have e70 : chainFrom 1000000000000000000 7 1420000 = 1390398682021537644 := by
    rw [show (1420000 : ℕ) = 1400000 + 20000 from rfl, chainFrom_add, e69]; exact w70
  have e71 : chainFrom 1000000000000000000 7 1440000 = 1390398686920503628 := by
    rw [show (1440000 : ℕ) = 1420000 + 20000 from rfl, chainFrom_add, e70]; exact w71
  have e72 : chainFrom 1000000000000000000 7 1460000 = 1390398691563218583 := by
    rw [show (1460000 : ℕ) = 1440000 + 20000 from rfl, chainFrom_add, e71]; exact w72
  have e73 : chainFrom 1000000000000000000 7 1480000 = 1390398696135079908 := by
    rw [show (1480000 : ℕ) = 1460000 + 20000 from rfl, chainFrom_add, e72]; exact w73
  have e74 : chainFrom 1000000000000000000 7 1500000 = 1390398700525949070 := by
    rw [show (1500000 : ℕ) = 1480000 + 20000 from rfl, chainFrom_add, e73]; exact w74
  have e75 : chainFrom 1000000000000000000 7 1520000 = 1390398704899310971 := by
    rw [show (1520000 : ℕ) = 1500000 + 20000 from rfl, chainFrom_add, e74]; exact w75
  have e76 : chainFrom 1000000000000000000 7 1540000 = 1390398708988566590 := by
    rw [show (1540000 : ℕ) = 1520000 + 20000 from rfl, chainFrom_add, e75]; exact w76
  have e77 : chainFrom 1000000000000000000 7 1560000 = 1390398713068172121 := by
    rw [show (1560000 : ℕ) = 1540000 + 20000 from rfl, chainFrom_add, e76]; exact w77
  have e78 : chainFrom 1000000000000000000 7 1580000 = 1390398716968703803 := by
    rw [show (1580000 : ℕ) = 1560000 + 20000 from rfl, chainFrom_add, e77]; exact w78
  have e79 : chainFrom 1000000000000000000 7 1600000 = 1390398720730778547 := by
    rw [show (1600000 : ℕ) = 1580000 + 20000 from rfl, chainFrom_add, e78]; exact w79
  have e80 : chainFrom 1000000000000000000 7 1620000 = 1390398724523969380 := by
    rw [show (1620000 : ℕ) = 1600000 + 20000 from rfl, chainFrom_add, e79]; exact w80
  have e81 : chainFrom 1000000000000000000 7 1640000 = 1390398728190420211 := by
    rw [show (1640000 : ℕ) = 1620000 + 20000 from rfl, chainFrom_add, e80]; exact w81
  have e82 : chainFrom 1000000000000000000 7 1660000 = 1390398731747617802 := by
    rw [show (1660000 : ℕ) = 1640000 + 20000 from rfl, chainFrom_add, e81]; exact w82
  have e83 : chainFrom 1000000000000000000 7 1680000 = 1390398735282104884 := by
    rw [show (1680000 : ℕ) = 1660000 + 20000 from rfl, chainFrom_add, e82]; exact w83
  have e84 : chainFrom 1000000000000000000 7 1700000 = 1390398738660141085 := by
    rw [show (1700000 : ℕ) = 1680000 + 20000 from rfl, chainFrom_add, e83]; exact w84
  have e85 : chainFrom 1000000000000000000 7 1720000 = 1390398741946026187 := by
    rw [show (1720000 : ℕ) = 1700000 + 20000 from rfl, chainFrom_add, e84]; exact w85
  have e86 : chainFrom 1000000000000000000 7 1740000 = 1390398745149050279 := by
    rw [show (1740000 : ℕ) = 1720000 + 20000 from rfl, chainFrom_add, e85]; exact w86
  have e87 : chainFrom 1000000000000000000 7 1760000 = 1390398748304810059 := by
    rw [show (1760000 : ℕ) = 1740000 + 20000 from rfl, chainFrom_add, e86]; exact w87
  have e88 : chainFrom 1000000000000000000 7 1780000 = 1390398751368862905 := by
    rw [show (1780000 : ℕ) = 1760000 + 20000 from rfl, chainFrom_add, e87]; exact w88
  have e89 : chainFrom 1000000000000000000 7 1800000 = 1390398754404283901 := by
    rw [show (1800000 : ℕ) = 1780000 + 20000 from rfl, chainFrom_add, e88]; exact w89
  have e90 : chainFrom 1000000000000000000 7 1820000 = 1390398757324596550 := by
    rw [show (1820000 : ℕ) = 1800000 + 20000 from rfl, chainFrom_add, e89]; exact w90
  have e91 : chainFrom 1000000000000000000 7 1840000 = 1390398760217115282 := by
    rw [show (1840000 : ℕ) = 1820000 + 20000 from rfl, chainFrom_add, e90]; exact w91
  have e92 : chainFrom 1000000000000000000 7 1860000 = 1390398763077113462 := by
    rw [show (1860000 : ℕ) = 1840000 + 20000 from rfl, chainFrom_add, e91]; exact w92
  have e93 : chainFrom 1000000000000000000 7 1880000 = 1390398765844782125 := by
    rw [show (1880000 : ℕ) = 1860000 + 20000 from rfl, chainFrom_add, e92]; exact w93
  have e94 : chainFrom 1000000000000000000 7 1900000 = 1390398768546420875 := by
    rw [show (1900000 : ℕ) = 1880000 + 20000 from rfl, chainFrom_add, e93]; exact w94
  have e95 : chainFrom 1000000000000000000 7 1920000 = 1390398771187629645 := by
    rw [show (1920000 : ℕ) = 1900000 + 20000 from rfl, chainFrom_add, e94]; exact w95
  have e96 : chainFrom 1000000000000000000 7 1940000 = 1390398773791288124 := by
    rw [show (1940000 : ℕ) = 1920000 + 20000 from rfl, chainFrom_add, e95]; exact w96
  have e97 : chainFrom 1000000000000000000 7 1960000 = 1390398776307255561 := by
    rw [show (1960000 : ℕ) = 1940000 + 20000 from rfl, chainFrom_add, e96]; exact w97
  have e98 : chainFrom 1000000000000000000 7 1980000 = 1390398778713142977 := by
    rw [show (1980000 : ℕ) = 1960000 + 20000 from rfl, chainFrom_add, e97]; exact w98
  have e99 : chainFrom 1000000000000000000 7 2000000 = 1390398781179656047 := by
    rw [show (2000000 : ℕ) = 1980000 + 20000 from rfl, chainFrom_add, e98]; exact w99
  exact e99

lemma TT_X : TT 2000007 ≤ 501 / 3000 * (8 / 1999994) := by
  unfold TT fr mr; norm_num

/-- **`c₃ ≤ 1.3903998`.** Zero sorry. True value 1.3903990. -/
theorem c3_le_13903998 : c3 ≤ (13903998 / 10000000 : ℝ) := by
  rw [c3_eq_exp, ← summable_lF.sum_add_tsum_nat_add 2000007, Real.exp_add, exp_head]
  have hc := chain_bound 1000000000000000000 7 (le_refl 7) 2000000
  rw [chain_total] at hc
  have hpr := prime_prod_le_surv 2000007
  set P := ∏ n ∈ (range 2000007).filter (fun n => n.Prime ∧ 5 < n), epsF n with hP
  set Q := ∏ n ∈ (Ico 7 (7 + 2000000)).filter (fun n => surv n = true), epsF n with hQ
  have hQ' : Q = ∏ n ∈ (Ico 7 2000007).filter (fun n => surv n = true), epsF n := rfl
  have hP0 : 0 ≤ P := prod_nonneg fun n hn => (epsF_pos (seven_le (mem_filter.mp hn).2.1 (mem_filter.mp hn).2.2)).le
  have hQle : Q ≤ (1390398781179656047 : ℝ) / 10 ^ 18 := by
    rw [le_div_iff₀ (by positivity), mul_comm]; push_cast at hc; linarith
  have ht := tail_le 2000007 (by norm_num)
  have hTT := TT_X
  have he : Real.exp (∑' k, lF (k + 2000007)) ≤ 1 / (1 - 501 / 3000 * (8 / 1999994)) := by
    calc Real.exp (∑' k, lF (k + 2000007)) ≤ Real.exp (501 / 3000 * (8 / 1999994)) :=
          Real.exp_le_exp.mpr (ht.trans hTT)
      _ ≤ _ := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
  have he0 : 0 ≤ Real.exp (∑' k, lF (k + 2000007)) := (Real.exp_pos _).le
  calc P * Real.exp (∑' k, lF (k + 2000007))
      ≤ (1390398781179656047 : ℝ) / 10 ^ 18 * (1 / (1 - 501 / 3000 * (8 / 1999994))) :=
        mul_le_mul (hpr.trans hQle) he he0 (by positivity)
    _ ≤ _ := by norm_num

/-- **Hathi 2021, page 11: `c₃ ≤ 1.3904`.** Zero sorry. -/
theorem c3_le : c3 ≤ (13904 / 10000 : ℝ) := by
  have := c3_le_13903998; linarith

end LeanLab.Hathi2021.C3
