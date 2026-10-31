/-
P0080 Hathi 2021, c₃ chain windows 0 to 9, each 20000 numbers from 7 + 20000 i.
Unit U-6154, CLOUD 20261020T0717Z-cloud37. AI-written Lean code, Claude. Checked only by the
Lean kernel, decide +kernel. Values from gen/c3_chain_U6154.py. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.C3Defs

set_option maxRecDepth 200000

namespace LeanLab.Hathi2021.C3

theorem w0 : chainFrom 1000000000000000000 7 20000 = 1390366936226152044 := by decide +kernel

theorem w1 : chainFrom 1390366936226152044 20007 20000 = 1390383952519771231 := by decide +kernel

theorem w2 : chainFrom 1390383952519771231 40007 20000 = 1390389326648478337 := by decide +kernel

theorem w3 : chainFrom 1390389326648478337 60007 20000 = 1390391902863964598 := by decide +kernel

theorem w4 : chainFrom 1390391902863964598 80007 20000 = 1390393429496423025 := by decide +kernel

theorem w5 : chainFrom 1390393429496423025 100007 20000 = 1390394419179976699 := by decide +kernel

theorem w6 : chainFrom 1390394419179976699 120007 20000 = 1390395126729664792 := by decide +kernel

theorem w7 : chainFrom 1390395126729664792 140007 20000 = 1390395646379883685 := by decide +kernel

theorem w8 : chainFrom 1390395646379883685 160007 20000 = 1390396046319286623 := by decide +kernel

theorem w9 : chainFrom 1390396046319286623 180007 20000 = 1390396363308644442 := by decide +kernel


end LeanLab.Hathi2021.C3
