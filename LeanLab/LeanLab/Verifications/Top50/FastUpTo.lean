/-
EvenGoldbachUpTo 100000, zero sorry, by the kernel checker of FastCheck.lean in blocks.
Every even n with 4 ≤ n ≤ 100000 is a sum of two primes. This is far below the 4e18 of
P0005; its point is that the kernel checks it with no cited input. AI-written Lean code,
Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.FastB1
import LeanLab.Verifications.Top50.FastB2
import LeanLab.Verifications.Top50.FastB3
import LeanLab.Verifications.Top50.FastB4
import LeanLab.Verifications.Top50.FastB5
import LeanLab.Verifications.Top50.FastB6
import LeanLab.Verifications.Top50.FastB7
import LeanLab.Verifications.Top50.FastB8
import LeanLab.Verifications.Top50.FastB9
import LeanLab.Verifications.Top50.FastB10
import LeanLab.Verifications.Top50.FastB11
import LeanLab.Verifications.Top50.FastB12
import LeanLab.Verifications.Top50.FastB13
import LeanLab.Verifications.Top50.FastB14
import LeanLab.Verifications.Top50.FastB15
import LeanLab.Verifications.Top50.FastB16
import LeanLab.Verifications.Top50.FastB17

namespace LeanLab.Verifications.Top50.Fast

theorem upTo_11400 : EvenGoldbachUpTo 11400 :=
  upTo_of_blocks upTo_1400 ⟨700, rfl⟩ 5000 (by norm_num) (by norm_num) fastBlock_1

theorem upTo_21400 : EvenGoldbachUpTo 21400 :=
  upTo_of_blocks upTo_11400 ⟨5700, rfl⟩ 5000 (by norm_num) (by norm_num) fastBlock_2

theorem upTo_31400 : EvenGoldbachUpTo 31400 :=
  upTo_of_blocks upTo_21400 ⟨10700, rfl⟩ 5000 (by norm_num) (by norm_num) fastBlock_3

theorem upTo_36400 : EvenGoldbachUpTo 36400 :=
  upTo_of_blocks upTo_31400 ⟨15700, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_4

theorem upTo_41400 : EvenGoldbachUpTo 41400 :=
  upTo_of_blocks upTo_36400 ⟨18200, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_5

theorem upTo_46400 : EvenGoldbachUpTo 46400 :=
  upTo_of_blocks upTo_41400 ⟨20700, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_6

theorem upTo_51400 : EvenGoldbachUpTo 51400 :=
  upTo_of_blocks upTo_46400 ⟨23200, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_7

theorem upTo_56400 : EvenGoldbachUpTo 56400 :=
  upTo_of_blocks upTo_51400 ⟨25700, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_8

theorem upTo_61400 : EvenGoldbachUpTo 61400 :=
  upTo_of_blocks upTo_56400 ⟨28200, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_9

theorem upTo_66400 : EvenGoldbachUpTo 66400 :=
  upTo_of_blocks upTo_61400 ⟨30700, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_10

theorem upTo_71400 : EvenGoldbachUpTo 71400 :=
  upTo_of_blocks upTo_66400 ⟨33200, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_11

theorem upTo_76400 : EvenGoldbachUpTo 76400 :=
  upTo_of_blocks upTo_71400 ⟨35700, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_12

theorem upTo_81400 : EvenGoldbachUpTo 81400 :=
  upTo_of_blocks upTo_76400 ⟨38200, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_13

theorem upTo_86400 : EvenGoldbachUpTo 86400 :=
  upTo_of_blocks upTo_81400 ⟨40700, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_14

theorem upTo_91400 : EvenGoldbachUpTo 91400 :=
  upTo_of_blocks upTo_86400 ⟨43200, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_15

theorem upTo_96400 : EvenGoldbachUpTo 96400 :=
  upTo_of_blocks upTo_91400 ⟨45700, rfl⟩ 2500 (by norm_num) (by norm_num) fastBlock_16

theorem upTo_100000 : EvenGoldbachUpTo 100000 :=
  upTo_of_blocks upTo_96400 ⟨48200, rfl⟩ 1800 (by norm_num) (by norm_num) fastBlock_17

/-- Even Goldbach to 10^5, checked by the Lean kernel, zero sorry. -/
theorem evenGoldbachUpTo_1e5 : EvenGoldbachUpTo (10 ^ 5) := upTo_100000

end LeanLab.Verifications.Top50.Fast
