/-
P0037 Deshouillers, te Riele, Saouter 1998, Theorem 2 at B = 10^40: every even integer in
[10^40, 10^40 + 10^8] is a sum of two primes. Kernel checked, no cited input: 101 shifted windows,
173 certified primes q near 10^40, small primes p ≤ 10^8 + 21839 from the lab's sieve bitmap.
AI-written Lean code, Claude, 2026-10-18, run 20261018T1002Z-987, unit U-0938. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.DtRS1998.W40_1
import LeanLab.DtRS1998.W40_2
import LeanLab.DtRS1998.W40_3
import LeanLab.DtRS1998.W40_4
import LeanLab.DtRS1998.W40_5
import LeanLab.DtRS1998.W40_6
import LeanLab.DtRS1998.W40_7
import LeanLab.DtRS1998.W40_8
import LeanLab.DtRS1998.W40_9
import LeanLab.DtRS1998.W40_10
import LeanLab.DtRS1998.W40_11

namespace LeanLab.DtRS1998.I40

open LeanLab.DtRS1998

theorem c2 : GoldbachOn (Bq + 0) (Bq + 1999998) :=
  goldbachOn_join (b := Bq + 999998) (by norm_num [Bq]) w1 (by simpa using w2)

theorem c3 : GoldbachOn (Bq + 0) (Bq + 2999998) :=
  goldbachOn_join (b := Bq + 1999998) (by norm_num [Bq]) c2 (by simpa using w3)

theorem c4 : GoldbachOn (Bq + 0) (Bq + 3999998) :=
  goldbachOn_join (b := Bq + 2999998) (by norm_num [Bq]) c3 (by simpa using w4)

theorem c5 : GoldbachOn (Bq + 0) (Bq + 4999998) :=
  goldbachOn_join (b := Bq + 3999998) (by norm_num [Bq]) c4 (by simpa using w5)

theorem c6 : GoldbachOn (Bq + 0) (Bq + 5999998) :=
  goldbachOn_join (b := Bq + 4999998) (by norm_num [Bq]) c5 (by simpa using w6)

theorem c7 : GoldbachOn (Bq + 0) (Bq + 6999998) :=
  goldbachOn_join (b := Bq + 5999998) (by norm_num [Bq]) c6 (by simpa using w7)

theorem c8 : GoldbachOn (Bq + 0) (Bq + 7999998) :=
  goldbachOn_join (b := Bq + 6999998) (by norm_num [Bq]) c7 (by simpa using w8)

theorem c9 : GoldbachOn (Bq + 0) (Bq + 8999998) :=
  goldbachOn_join (b := Bq + 7999998) (by norm_num [Bq]) c8 (by simpa using w9)

theorem c10 : GoldbachOn (Bq + 0) (Bq + 9999998) :=
  goldbachOn_join (b := Bq + 8999998) (by norm_num [Bq]) c9 (by simpa using w10)

theorem c11 : GoldbachOn (Bq + 0) (Bq + 10999998) :=
  goldbachOn_join (b := Bq + 9999998) (by norm_num [Bq]) c10 (by simpa using w11)

theorem c12 : GoldbachOn (Bq + 0) (Bq + 11999998) :=
  goldbachOn_join (b := Bq + 10999998) (by norm_num [Bq]) c11 (by simpa using w12)

theorem c13 : GoldbachOn (Bq + 0) (Bq + 12999998) :=
  goldbachOn_join (b := Bq + 11999998) (by norm_num [Bq]) c12 (by simpa using w13)

theorem c14 : GoldbachOn (Bq + 0) (Bq + 13999998) :=
  goldbachOn_join (b := Bq + 12999998) (by norm_num [Bq]) c13 (by simpa using w14)

theorem c15 : GoldbachOn (Bq + 0) (Bq + 14999998) :=
  goldbachOn_join (b := Bq + 13999998) (by norm_num [Bq]) c14 (by simpa using w15)

theorem c16 : GoldbachOn (Bq + 0) (Bq + 15999998) :=
  goldbachOn_join (b := Bq + 14999998) (by norm_num [Bq]) c15 (by simpa using w16)

theorem c17 : GoldbachOn (Bq + 0) (Bq + 16999998) :=
  goldbachOn_join (b := Bq + 15999998) (by norm_num [Bq]) c16 (by simpa using w17)

theorem c18 : GoldbachOn (Bq + 0) (Bq + 17999998) :=
  goldbachOn_join (b := Bq + 16999998) (by norm_num [Bq]) c17 (by simpa using w18)

theorem c19 : GoldbachOn (Bq + 0) (Bq + 18999998) :=
  goldbachOn_join (b := Bq + 17999998) (by norm_num [Bq]) c18 (by simpa using w19)

theorem c20 : GoldbachOn (Bq + 0) (Bq + 19999998) :=
  goldbachOn_join (b := Bq + 18999998) (by norm_num [Bq]) c19 (by simpa using w20)

theorem c21 : GoldbachOn (Bq + 0) (Bq + 20999998) :=
  goldbachOn_join (b := Bq + 19999998) (by norm_num [Bq]) c20 (by simpa using w21)

theorem c22 : GoldbachOn (Bq + 0) (Bq + 21999998) :=
  goldbachOn_join (b := Bq + 20999998) (by norm_num [Bq]) c21 (by simpa using w22)

theorem c23 : GoldbachOn (Bq + 0) (Bq + 22999998) :=
  goldbachOn_join (b := Bq + 21999998) (by norm_num [Bq]) c22 (by simpa using w23)

theorem c24 : GoldbachOn (Bq + 0) (Bq + 23999998) :=
  goldbachOn_join (b := Bq + 22999998) (by norm_num [Bq]) c23 (by simpa using w24)

theorem c25 : GoldbachOn (Bq + 0) (Bq + 24999998) :=
  goldbachOn_join (b := Bq + 23999998) (by norm_num [Bq]) c24 (by simpa using w25)

theorem c26 : GoldbachOn (Bq + 0) (Bq + 25999998) :=
  goldbachOn_join (b := Bq + 24999998) (by norm_num [Bq]) c25 (by simpa using w26)

theorem c27 : GoldbachOn (Bq + 0) (Bq + 26999998) :=
  goldbachOn_join (b := Bq + 25999998) (by norm_num [Bq]) c26 (by simpa using w27)

theorem c28 : GoldbachOn (Bq + 0) (Bq + 27999998) :=
  goldbachOn_join (b := Bq + 26999998) (by norm_num [Bq]) c27 (by simpa using w28)

theorem c29 : GoldbachOn (Bq + 0) (Bq + 28999998) :=
  goldbachOn_join (b := Bq + 27999998) (by norm_num [Bq]) c28 (by simpa using w29)

theorem c30 : GoldbachOn (Bq + 0) (Bq + 29999998) :=
  goldbachOn_join (b := Bq + 28999998) (by norm_num [Bq]) c29 (by simpa using w30)

theorem c31 : GoldbachOn (Bq + 0) (Bq + 30999998) :=
  goldbachOn_join (b := Bq + 29999998) (by norm_num [Bq]) c30 (by simpa using w31)

theorem c32 : GoldbachOn (Bq + 0) (Bq + 31999998) :=
  goldbachOn_join (b := Bq + 30999998) (by norm_num [Bq]) c31 (by simpa using w32)

theorem c33 : GoldbachOn (Bq + 0) (Bq + 32999998) :=
  goldbachOn_join (b := Bq + 31999998) (by norm_num [Bq]) c32 (by simpa using w33)

theorem c34 : GoldbachOn (Bq + 0) (Bq + 33999998) :=
  goldbachOn_join (b := Bq + 32999998) (by norm_num [Bq]) c33 (by simpa using w34)

theorem c35 : GoldbachOn (Bq + 0) (Bq + 34999998) :=
  goldbachOn_join (b := Bq + 33999998) (by norm_num [Bq]) c34 (by simpa using w35)

theorem c36 : GoldbachOn (Bq + 0) (Bq + 35999998) :=
  goldbachOn_join (b := Bq + 34999998) (by norm_num [Bq]) c35 (by simpa using w36)

theorem c37 : GoldbachOn (Bq + 0) (Bq + 36999998) :=
  goldbachOn_join (b := Bq + 35999998) (by norm_num [Bq]) c36 (by simpa using w37)

theorem c38 : GoldbachOn (Bq + 0) (Bq + 37999998) :=
  goldbachOn_join (b := Bq + 36999998) (by norm_num [Bq]) c37 (by simpa using w38)

theorem c39 : GoldbachOn (Bq + 0) (Bq + 38999998) :=
  goldbachOn_join (b := Bq + 37999998) (by norm_num [Bq]) c38 (by simpa using w39)

theorem c40 : GoldbachOn (Bq + 0) (Bq + 39999998) :=
  goldbachOn_join (b := Bq + 38999998) (by norm_num [Bq]) c39 (by simpa using w40)

theorem c41 : GoldbachOn (Bq + 0) (Bq + 40999998) :=
  goldbachOn_join (b := Bq + 39999998) (by norm_num [Bq]) c40 (by simpa using w41)

theorem c42 : GoldbachOn (Bq + 0) (Bq + 41999998) :=
  goldbachOn_join (b := Bq + 40999998) (by norm_num [Bq]) c41 (by simpa using w42)

theorem c43 : GoldbachOn (Bq + 0) (Bq + 42999998) :=
  goldbachOn_join (b := Bq + 41999998) (by norm_num [Bq]) c42 (by simpa using w43)

theorem c44 : GoldbachOn (Bq + 0) (Bq + 43999998) :=
  goldbachOn_join (b := Bq + 42999998) (by norm_num [Bq]) c43 (by simpa using w44)

theorem c45 : GoldbachOn (Bq + 0) (Bq + 44999998) :=
  goldbachOn_join (b := Bq + 43999998) (by norm_num [Bq]) c44 (by simpa using w45)

theorem c46 : GoldbachOn (Bq + 0) (Bq + 45999998) :=
  goldbachOn_join (b := Bq + 44999998) (by norm_num [Bq]) c45 (by simpa using w46)

theorem c47 : GoldbachOn (Bq + 0) (Bq + 46999998) :=
  goldbachOn_join (b := Bq + 45999998) (by norm_num [Bq]) c46 (by simpa using w47)

theorem c48 : GoldbachOn (Bq + 0) (Bq + 47999998) :=
  goldbachOn_join (b := Bq + 46999998) (by norm_num [Bq]) c47 (by simpa using w48)

theorem c49 : GoldbachOn (Bq + 0) (Bq + 48999998) :=
  goldbachOn_join (b := Bq + 47999998) (by norm_num [Bq]) c48 (by simpa using w49)

theorem c50 : GoldbachOn (Bq + 0) (Bq + 49999998) :=
  goldbachOn_join (b := Bq + 48999998) (by norm_num [Bq]) c49 (by simpa using w50)

theorem c51 : GoldbachOn (Bq + 0) (Bq + 50999998) :=
  goldbachOn_join (b := Bq + 49999998) (by norm_num [Bq]) c50 (by simpa using w51)

theorem c52 : GoldbachOn (Bq + 0) (Bq + 51999998) :=
  goldbachOn_join (b := Bq + 50999998) (by norm_num [Bq]) c51 (by simpa using w52)

theorem c53 : GoldbachOn (Bq + 0) (Bq + 52999998) :=
  goldbachOn_join (b := Bq + 51999998) (by norm_num [Bq]) c52 (by simpa using w53)

theorem c54 : GoldbachOn (Bq + 0) (Bq + 53999998) :=
  goldbachOn_join (b := Bq + 52999998) (by norm_num [Bq]) c53 (by simpa using w54)

theorem c55 : GoldbachOn (Bq + 0) (Bq + 54999998) :=
  goldbachOn_join (b := Bq + 53999998) (by norm_num [Bq]) c54 (by simpa using w55)

theorem c56 : GoldbachOn (Bq + 0) (Bq + 55999998) :=
  goldbachOn_join (b := Bq + 54999998) (by norm_num [Bq]) c55 (by simpa using w56)

theorem c57 : GoldbachOn (Bq + 0) (Bq + 56999998) :=
  goldbachOn_join (b := Bq + 55999998) (by norm_num [Bq]) c56 (by simpa using w57)

theorem c58 : GoldbachOn (Bq + 0) (Bq + 57999998) :=
  goldbachOn_join (b := Bq + 56999998) (by norm_num [Bq]) c57 (by simpa using w58)

theorem c59 : GoldbachOn (Bq + 0) (Bq + 58999998) :=
  goldbachOn_join (b := Bq + 57999998) (by norm_num [Bq]) c58 (by simpa using w59)

theorem c60 : GoldbachOn (Bq + 0) (Bq + 59999998) :=
  goldbachOn_join (b := Bq + 58999998) (by norm_num [Bq]) c59 (by simpa using w60)

theorem c61 : GoldbachOn (Bq + 0) (Bq + 60999998) :=
  goldbachOn_join (b := Bq + 59999998) (by norm_num [Bq]) c60 (by simpa using w61)

theorem c62 : GoldbachOn (Bq + 0) (Bq + 61999998) :=
  goldbachOn_join (b := Bq + 60999998) (by norm_num [Bq]) c61 (by simpa using w62)

theorem c63 : GoldbachOn (Bq + 0) (Bq + 62999998) :=
  goldbachOn_join (b := Bq + 61999998) (by norm_num [Bq]) c62 (by simpa using w63)

theorem c64 : GoldbachOn (Bq + 0) (Bq + 63999998) :=
  goldbachOn_join (b := Bq + 62999998) (by norm_num [Bq]) c63 (by simpa using w64)

theorem c65 : GoldbachOn (Bq + 0) (Bq + 64999998) :=
  goldbachOn_join (b := Bq + 63999998) (by norm_num [Bq]) c64 (by simpa using w65)

theorem c66 : GoldbachOn (Bq + 0) (Bq + 65999998) :=
  goldbachOn_join (b := Bq + 64999998) (by norm_num [Bq]) c65 (by simpa using w66)

theorem c67 : GoldbachOn (Bq + 0) (Bq + 66999998) :=
  goldbachOn_join (b := Bq + 65999998) (by norm_num [Bq]) c66 (by simpa using w67)

theorem c68 : GoldbachOn (Bq + 0) (Bq + 67999998) :=
  goldbachOn_join (b := Bq + 66999998) (by norm_num [Bq]) c67 (by simpa using w68)

theorem c69 : GoldbachOn (Bq + 0) (Bq + 68999998) :=
  goldbachOn_join (b := Bq + 67999998) (by norm_num [Bq]) c68 (by simpa using w69)

theorem c70 : GoldbachOn (Bq + 0) (Bq + 69999998) :=
  goldbachOn_join (b := Bq + 68999998) (by norm_num [Bq]) c69 (by simpa using w70)

theorem c71 : GoldbachOn (Bq + 0) (Bq + 70999998) :=
  goldbachOn_join (b := Bq + 69999998) (by norm_num [Bq]) c70 (by simpa using w71)

theorem c72 : GoldbachOn (Bq + 0) (Bq + 71999998) :=
  goldbachOn_join (b := Bq + 70999998) (by norm_num [Bq]) c71 (by simpa using w72)

theorem c73 : GoldbachOn (Bq + 0) (Bq + 72999998) :=
  goldbachOn_join (b := Bq + 71999998) (by norm_num [Bq]) c72 (by simpa using w73)

theorem c74 : GoldbachOn (Bq + 0) (Bq + 73999998) :=
  goldbachOn_join (b := Bq + 72999998) (by norm_num [Bq]) c73 (by simpa using w74)

theorem c75 : GoldbachOn (Bq + 0) (Bq + 74999998) :=
  goldbachOn_join (b := Bq + 73999998) (by norm_num [Bq]) c74 (by simpa using w75)

theorem c76 : GoldbachOn (Bq + 0) (Bq + 75999998) :=
  goldbachOn_join (b := Bq + 74999998) (by norm_num [Bq]) c75 (by simpa using w76)

theorem c77 : GoldbachOn (Bq + 0) (Bq + 76999998) :=
  goldbachOn_join (b := Bq + 75999998) (by norm_num [Bq]) c76 (by simpa using w77)

theorem c78 : GoldbachOn (Bq + 0) (Bq + 77999998) :=
  goldbachOn_join (b := Bq + 76999998) (by norm_num [Bq]) c77 (by simpa using w78)

theorem c79 : GoldbachOn (Bq + 0) (Bq + 78999998) :=
  goldbachOn_join (b := Bq + 77999998) (by norm_num [Bq]) c78 (by simpa using w79)

theorem c80 : GoldbachOn (Bq + 0) (Bq + 79999998) :=
  goldbachOn_join (b := Bq + 78999998) (by norm_num [Bq]) c79 (by simpa using w80)

theorem c81 : GoldbachOn (Bq + 0) (Bq + 80999998) :=
  goldbachOn_join (b := Bq + 79999998) (by norm_num [Bq]) c80 (by simpa using w81)

theorem c82 : GoldbachOn (Bq + 0) (Bq + 81999998) :=
  goldbachOn_join (b := Bq + 80999998) (by norm_num [Bq]) c81 (by simpa using w82)

theorem c83 : GoldbachOn (Bq + 0) (Bq + 82999998) :=
  goldbachOn_join (b := Bq + 81999998) (by norm_num [Bq]) c82 (by simpa using w83)

theorem c84 : GoldbachOn (Bq + 0) (Bq + 83999998) :=
  goldbachOn_join (b := Bq + 82999998) (by norm_num [Bq]) c83 (by simpa using w84)

theorem c85 : GoldbachOn (Bq + 0) (Bq + 84999998) :=
  goldbachOn_join (b := Bq + 83999998) (by norm_num [Bq]) c84 (by simpa using w85)

theorem c86 : GoldbachOn (Bq + 0) (Bq + 85999998) :=
  goldbachOn_join (b := Bq + 84999998) (by norm_num [Bq]) c85 (by simpa using w86)

theorem c87 : GoldbachOn (Bq + 0) (Bq + 86999998) :=
  goldbachOn_join (b := Bq + 85999998) (by norm_num [Bq]) c86 (by simpa using w87)

theorem c88 : GoldbachOn (Bq + 0) (Bq + 87999998) :=
  goldbachOn_join (b := Bq + 86999998) (by norm_num [Bq]) c87 (by simpa using w88)

theorem c89 : GoldbachOn (Bq + 0) (Bq + 88999998) :=
  goldbachOn_join (b := Bq + 87999998) (by norm_num [Bq]) c88 (by simpa using w89)

theorem c90 : GoldbachOn (Bq + 0) (Bq + 89999998) :=
  goldbachOn_join (b := Bq + 88999998) (by norm_num [Bq]) c89 (by simpa using w90)

theorem c91 : GoldbachOn (Bq + 0) (Bq + 90999998) :=
  goldbachOn_join (b := Bq + 89999998) (by norm_num [Bq]) c90 (by simpa using w91)

theorem c92 : GoldbachOn (Bq + 0) (Bq + 91999998) :=
  goldbachOn_join (b := Bq + 90999998) (by norm_num [Bq]) c91 (by simpa using w92)

theorem c93 : GoldbachOn (Bq + 0) (Bq + 92999998) :=
  goldbachOn_join (b := Bq + 91999998) (by norm_num [Bq]) c92 (by simpa using w93)

theorem c94 : GoldbachOn (Bq + 0) (Bq + 93999998) :=
  goldbachOn_join (b := Bq + 92999998) (by norm_num [Bq]) c93 (by simpa using w94)

theorem c95 : GoldbachOn (Bq + 0) (Bq + 94999998) :=
  goldbachOn_join (b := Bq + 93999998) (by norm_num [Bq]) c94 (by simpa using w95)

theorem c96 : GoldbachOn (Bq + 0) (Bq + 95999998) :=
  goldbachOn_join (b := Bq + 94999998) (by norm_num [Bq]) c95 (by simpa using w96)

theorem c97 : GoldbachOn (Bq + 0) (Bq + 96999998) :=
  goldbachOn_join (b := Bq + 95999998) (by norm_num [Bq]) c96 (by simpa using w97)

theorem c98 : GoldbachOn (Bq + 0) (Bq + 97999998) :=
  goldbachOn_join (b := Bq + 96999998) (by norm_num [Bq]) c97 (by simpa using w98)

theorem c99 : GoldbachOn (Bq + 0) (Bq + 98999998) :=
  goldbachOn_join (b := Bq + 97999998) (by norm_num [Bq]) c98 (by simpa using w99)

theorem c100 : GoldbachOn (Bq + 0) (Bq + 99999998) :=
  goldbachOn_join (b := Bq + 98999998) (by norm_num [Bq]) c99 (by simpa using w100)

theorem c101 : GoldbachOn (Bq + 0) (Bq + 100000000) :=
  goldbachOn_join (b := Bq + 99999998) (by norm_num [Bq]) c100 (by simpa using w101)

/-- **DtRS 1998 Theorem 2 at B = 10^40**. -/
theorem theorem2 : ∀ n, 10 ^ 40 ≤ n → n ≤ 10 ^ 40 + 10 ^ 8 → Even n → IsGoldbachSum n := by
  intro n h1 h2 he
  exact c101 n (by simpa [Bq] using h1) (by simpa [Bq] using h2) (even_iff_two_dvd.mp he)

end LeanLab.DtRS1998.I40
