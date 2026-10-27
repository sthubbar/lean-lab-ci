/-
Saouter 1998, P0018, unit U-0361, run 20261018T0103Z-27139. Saouter's step with B = 10^9: even Goldbach to 10^9
and 200 checked ladder blocks, 100000 Lucas-certified primes from 3 to 99999689365487 with gaps at most
B - 4, give ternary Goldbach to 100000689365487. Each block's primes and chain are checked in B9/BlockK.lean,
Mathlib-free; here the facts are only glued. AI-written Lean code, Claude, 2026-10-18.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/
import LeanLab.Saouter1998.B9.Step
import LeanLab.Saouter1998.B9.Block1
import LeanLab.Saouter1998.B9.Block2
import LeanLab.Saouter1998.B9.Block3
import LeanLab.Saouter1998.B9.Block4
import LeanLab.Saouter1998.B9.Block5
import LeanLab.Saouter1998.B9.Block6
import LeanLab.Saouter1998.B9.Block7
import LeanLab.Saouter1998.B9.Block8
import LeanLab.Saouter1998.B9.Block9
import LeanLab.Saouter1998.B9.Block10
import LeanLab.Saouter1998.B9.Block11
import LeanLab.Saouter1998.B9.Block12
import LeanLab.Saouter1998.B9.Block13
import LeanLab.Saouter1998.B9.Block14
import LeanLab.Saouter1998.B9.Block15
import LeanLab.Saouter1998.B9.Block16
import LeanLab.Saouter1998.B9.Block17
import LeanLab.Saouter1998.B9.Block18
import LeanLab.Saouter1998.B9.Block19
import LeanLab.Saouter1998.B9.Block20
import LeanLab.Saouter1998.B9.Block21
import LeanLab.Saouter1998.B9.Block22
import LeanLab.Saouter1998.B9.Block23
import LeanLab.Saouter1998.B9.Block24
import LeanLab.Saouter1998.B9.Block25
import LeanLab.Saouter1998.B9.Block26
import LeanLab.Saouter1998.B9.Block27
import LeanLab.Saouter1998.B9.Block28
import LeanLab.Saouter1998.B9.Block29
import LeanLab.Saouter1998.B9.Block30
import LeanLab.Saouter1998.B9.Block31
import LeanLab.Saouter1998.B9.Block32
import LeanLab.Saouter1998.B9.Block33
import LeanLab.Saouter1998.B9.Block34
import LeanLab.Saouter1998.B9.Block35
import LeanLab.Saouter1998.B9.Block36
import LeanLab.Saouter1998.B9.Block37
import LeanLab.Saouter1998.B9.Block38
import LeanLab.Saouter1998.B9.Block39
import LeanLab.Saouter1998.B9.Block40
import LeanLab.Saouter1998.B9.Block41
import LeanLab.Saouter1998.B9.Block42
import LeanLab.Saouter1998.B9.Block43
import LeanLab.Saouter1998.B9.Block44
import LeanLab.Saouter1998.B9.Block45
import LeanLab.Saouter1998.B9.Block46
import LeanLab.Saouter1998.B9.Block47
import LeanLab.Saouter1998.B9.Block48
import LeanLab.Saouter1998.B9.Block49
import LeanLab.Saouter1998.B9.Block50
import LeanLab.Saouter1998.B9.Block51
import LeanLab.Saouter1998.B9.Block52
import LeanLab.Saouter1998.B9.Block53
import LeanLab.Saouter1998.B9.Block54
import LeanLab.Saouter1998.B9.Block55
import LeanLab.Saouter1998.B9.Block56
import LeanLab.Saouter1998.B9.Block57
import LeanLab.Saouter1998.B9.Block58
import LeanLab.Saouter1998.B9.Block59
import LeanLab.Saouter1998.B9.Block60
import LeanLab.Saouter1998.B9.Block61
import LeanLab.Saouter1998.B9.Block62
import LeanLab.Saouter1998.B9.Block63
import LeanLab.Saouter1998.B9.Block64
import LeanLab.Saouter1998.B9.Block65
import LeanLab.Saouter1998.B9.Block66
import LeanLab.Saouter1998.B9.Block67
import LeanLab.Saouter1998.B9.Block68
import LeanLab.Saouter1998.B9.Block69
import LeanLab.Saouter1998.B9.Block70
import LeanLab.Saouter1998.B9.Block71
import LeanLab.Saouter1998.B9.Block72
import LeanLab.Saouter1998.B9.Block73
import LeanLab.Saouter1998.B9.Block74
import LeanLab.Saouter1998.B9.Block75
import LeanLab.Saouter1998.B9.Block76
import LeanLab.Saouter1998.B9.Block77
import LeanLab.Saouter1998.B9.Block78
import LeanLab.Saouter1998.B9.Block79
import LeanLab.Saouter1998.B9.Block80
import LeanLab.Saouter1998.B9.Block81
import LeanLab.Saouter1998.B9.Block82
import LeanLab.Saouter1998.B9.Block83
import LeanLab.Saouter1998.B9.Block84
import LeanLab.Saouter1998.B9.Block85
import LeanLab.Saouter1998.B9.Block86
import LeanLab.Saouter1998.B9.Block87
import LeanLab.Saouter1998.B9.Block88
import LeanLab.Saouter1998.B9.Block89
import LeanLab.Saouter1998.B9.Block90
import LeanLab.Saouter1998.B9.Block91
import LeanLab.Saouter1998.B9.Block92
import LeanLab.Saouter1998.B9.Block93
import LeanLab.Saouter1998.B9.Block94
import LeanLab.Saouter1998.B9.Block95
import LeanLab.Saouter1998.B9.Block96
import LeanLab.Saouter1998.B9.Block97
import LeanLab.Saouter1998.B9.Block98
import LeanLab.Saouter1998.B9.Block99
import LeanLab.Saouter1998.B9.Block100
import LeanLab.Saouter1998.B9.Block101
import LeanLab.Saouter1998.B9.Block102
import LeanLab.Saouter1998.B9.Block103
import LeanLab.Saouter1998.B9.Block104
import LeanLab.Saouter1998.B9.Block105
import LeanLab.Saouter1998.B9.Block106
import LeanLab.Saouter1998.B9.Block107
import LeanLab.Saouter1998.B9.Block108
import LeanLab.Saouter1998.B9.Block109
import LeanLab.Saouter1998.B9.Block110
import LeanLab.Saouter1998.B9.Block111
import LeanLab.Saouter1998.B9.Block112
import LeanLab.Saouter1998.B9.Block113
import LeanLab.Saouter1998.B9.Block114
import LeanLab.Saouter1998.B9.Block115
import LeanLab.Saouter1998.B9.Block116
import LeanLab.Saouter1998.B9.Block117
import LeanLab.Saouter1998.B9.Block118
import LeanLab.Saouter1998.B9.Block119
import LeanLab.Saouter1998.B9.Block120
import LeanLab.Saouter1998.B9.Block121
import LeanLab.Saouter1998.B9.Block122
import LeanLab.Saouter1998.B9.Block123
import LeanLab.Saouter1998.B9.Block124
import LeanLab.Saouter1998.B9.Block125
import LeanLab.Saouter1998.B9.Block126
import LeanLab.Saouter1998.B9.Block127
import LeanLab.Saouter1998.B9.Block128
import LeanLab.Saouter1998.B9.Block129
import LeanLab.Saouter1998.B9.Block130
import LeanLab.Saouter1998.B9.Block131
import LeanLab.Saouter1998.B9.Block132
import LeanLab.Saouter1998.B9.Block133
import LeanLab.Saouter1998.B9.Block134
import LeanLab.Saouter1998.B9.Block135
import LeanLab.Saouter1998.B9.Block136
import LeanLab.Saouter1998.B9.Block137
import LeanLab.Saouter1998.B9.Block138
import LeanLab.Saouter1998.B9.Block139
import LeanLab.Saouter1998.B9.Block140
import LeanLab.Saouter1998.B9.Block141
import LeanLab.Saouter1998.B9.Block142
import LeanLab.Saouter1998.B9.Block143
import LeanLab.Saouter1998.B9.Block144
import LeanLab.Saouter1998.B9.Block145
import LeanLab.Saouter1998.B9.Block146
import LeanLab.Saouter1998.B9.Block147
import LeanLab.Saouter1998.B9.Block148
import LeanLab.Saouter1998.B9.Block149
import LeanLab.Saouter1998.B9.Block150
import LeanLab.Saouter1998.B9.Block151
import LeanLab.Saouter1998.B9.Block152
import LeanLab.Saouter1998.B9.Block153
import LeanLab.Saouter1998.B9.Block154
import LeanLab.Saouter1998.B9.Block155
import LeanLab.Saouter1998.B9.Block156
import LeanLab.Saouter1998.B9.Block157
import LeanLab.Saouter1998.B9.Block158
import LeanLab.Saouter1998.B9.Block159
import LeanLab.Saouter1998.B9.Block160
import LeanLab.Saouter1998.B9.Block161
import LeanLab.Saouter1998.B9.Block162
import LeanLab.Saouter1998.B9.Block163
import LeanLab.Saouter1998.B9.Block164
import LeanLab.Saouter1998.B9.Block165
import LeanLab.Saouter1998.B9.Block166
import LeanLab.Saouter1998.B9.Block167
import LeanLab.Saouter1998.B9.Block168
import LeanLab.Saouter1998.B9.Block169
import LeanLab.Saouter1998.B9.Block170
import LeanLab.Saouter1998.B9.Block171
import LeanLab.Saouter1998.B9.Block172
import LeanLab.Saouter1998.B9.Block173
import LeanLab.Saouter1998.B9.Block174
import LeanLab.Saouter1998.B9.Block175
import LeanLab.Saouter1998.B9.Block176
import LeanLab.Saouter1998.B9.Block177
import LeanLab.Saouter1998.B9.Block178
import LeanLab.Saouter1998.B9.Block179
import LeanLab.Saouter1998.B9.Block180
import LeanLab.Saouter1998.B9.Block181
import LeanLab.Saouter1998.B9.Block182
import LeanLab.Saouter1998.B9.Block183
import LeanLab.Saouter1998.B9.Block184
import LeanLab.Saouter1998.B9.Block185
import LeanLab.Saouter1998.B9.Block186
import LeanLab.Saouter1998.B9.Block187
import LeanLab.Saouter1998.B9.Block188
import LeanLab.Saouter1998.B9.Block189
import LeanLab.Saouter1998.B9.Block190
import LeanLab.Saouter1998.B9.Block191
import LeanLab.Saouter1998.B9.Block192
import LeanLab.Saouter1998.B9.Block193
import LeanLab.Saouter1998.B9.Block194
import LeanLab.Saouter1998.B9.Block195
import LeanLab.Saouter1998.B9.Block196
import LeanLab.Saouter1998.B9.Block197
import LeanLab.Saouter1998.B9.Block198
import LeanLab.Saouter1998.B9.Block199
import LeanLab.Saouter1998.B9.Block200

namespace LeanLab.Saouter1998.B9

open LeanLab.HelfgottPlatt

theorem s1 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (499999750043 + 1000000000) ∧ Nat.Prime 499999750043 ∧ 3 ≤ 499999750043 :=
  step hB (by norm_num) (base hB) Nat.prime_three le_rfl c1 k1

theorem s2 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (999999374797 + 1000000000) ∧ Nat.Prime 999999374797 ∧ 3 ≤ 999999374797 :=
  step hB (by norm_num) (s1 hB).1 (s1 hB).2.1 (s1 hB).2.2 c2 k2

theorem s3 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (1499998891393 + 1000000000) ∧ Nat.Prime 1499998891393 ∧ 3 ≤ 1499998891393 :=
  step hB (by norm_num) (s2 hB).1 (s2 hB).2.1 (s2 hB).2.2 c3 k3

theorem s4 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (1999998348181 + 1000000000) ∧ Nat.Prime 1999998348181 ∧ 3 ≤ 1999998348181 :=
  step hB (by norm_num) (s3 hB).1 (s3 hB).2.1 (s3 hB).2.2 c4 k4

theorem s5 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (2499997772161 + 1000000000) ∧ Nat.Prime 2499997772161 ∧ 3 ≤ 2499997772161 :=
  step hB (by norm_num) (s4 hB).1 (s4 hB).2.1 (s4 hB).2.2 c5 k5

theorem s6 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (2999997150541 + 1000000000) ∧ Nat.Prime 2999997150541 ∧ 3 ≤ 2999997150541 :=
  step hB (by norm_num) (s5 hB).1 (s5 hB).2.1 (s5 hB).2.2 c6 k6

theorem s7 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (3499996517321 + 1000000000) ∧ Nat.Prime 3499996517321 ∧ 3 ≤ 3499996517321 :=
  step hB (by norm_num) (s6 hB).1 (s6 hB).2.1 (s6 hB).2.2 c7 k7

theorem s8 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (3999995866631 + 1000000000) ∧ Nat.Prime 3999995866631 ∧ 3 ≤ 3999995866631 :=
  step hB (by norm_num) (s7 hB).1 (s7 hB).2.1 (s7 hB).2.2 c8 k8

theorem s9 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (4499995201157 + 1000000000) ∧ Nat.Prime 4499995201157 ∧ 3 ≤ 4499995201157 :=
  step hB (by norm_num) (s8 hB).1 (s8 hB).2.1 (s8 hB).2.2 c9 k9

theorem s10 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (4999994547277 + 1000000000) ∧ Nat.Prime 4999994547277 ∧ 3 ≤ 4999994547277 :=
  step hB (by norm_num) (s9 hB).1 (s9 hB).2.1 (s9 hB).2.2 c10 k10

theorem s11 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (5499993807017 + 1000000000) ∧ Nat.Prime 5499993807017 ∧ 3 ≤ 5499993807017 :=
  step hB (by norm_num) (s10 hB).1 (s10 hB).2.1 (s10 hB).2.2 c11 k11

theorem s12 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (5999993062631 + 1000000000) ∧ Nat.Prime 5999993062631 ∧ 3 ≤ 5999993062631 :=
  step hB (by norm_num) (s11 hB).1 (s11 hB).2.1 (s11 hB).2.2 c12 k12

theorem s13 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (6499992244531 + 1000000000) ∧ Nat.Prime 6499992244531 ∧ 3 ≤ 6499992244531 :=
  step hB (by norm_num) (s12 hB).1 (s12 hB).2.1 (s12 hB).2.2 c13 k13

theorem s14 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (6999991408843 + 1000000000) ∧ Nat.Prime 6999991408843 ∧ 3 ≤ 6999991408843 :=
  step hB (by norm_num) (s13 hB).1 (s13 hB).2.1 (s13 hB).2.2 c14 k14

theorem s15 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (7499990581799 + 1000000000) ∧ Nat.Prime 7499990581799 ∧ 3 ≤ 7499990581799 :=
  step hB (by norm_num) (s14 hB).1 (s14 hB).2.1 (s14 hB).2.2 c15 k15

theorem s16 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (7999989767641 + 1000000000) ∧ Nat.Prime 7999989767641 ∧ 3 ≤ 7999989767641 :=
  step hB (by norm_num) (s15 hB).1 (s15 hB).2.1 (s15 hB).2.2 c16 k16

theorem s17 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (8499988894651 + 1000000000) ∧ Nat.Prime 8499988894651 ∧ 3 ≤ 8499988894651 :=
  step hB (by norm_num) (s16 hB).1 (s16 hB).2.1 (s16 hB).2.2 c17 k17

theorem s18 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (8999987979331 + 1000000000) ∧ Nat.Prime 8999987979331 ∧ 3 ≤ 8999987979331 :=
  step hB (by norm_num) (s17 hB).1 (s17 hB).2.1 (s17 hB).2.2 c18 k18

theorem s19 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (9499987083043 + 1000000000) ∧ Nat.Prime 9499987083043 ∧ 3 ≤ 9499987083043 :=
  step hB (by norm_num) (s18 hB).1 (s18 hB).2.1 (s18 hB).2.2 c19 k19

theorem s20 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (9999986210761 + 1000000000) ∧ Nat.Prime 9999986210761 ∧ 3 ≤ 9999986210761 :=
  step hB (by norm_num) (s19 hB).1 (s19 hB).2.1 (s19 hB).2.2 c20 k20

theorem s21 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (10499985285701 + 1000000000) ∧ Nat.Prime 10499985285701 ∧ 3 ≤ 10499985285701 :=
  step hB (by norm_num) (s20 hB).1 (s20 hB).2.1 (s20 hB).2.2 c21 k21

theorem s22 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (10999984372217 + 1000000000) ∧ Nat.Prime 10999984372217 ∧ 3 ≤ 10999984372217 :=
  step hB (by norm_num) (s21 hB).1 (s21 hB).2.1 (s21 hB).2.2 c22 k22

theorem s23 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (11499983481601 + 1000000000) ∧ Nat.Prime 11499983481601 ∧ 3 ≤ 11499983481601 :=
  step hB (by norm_num) (s22 hB).1 (s22 hB).2.1 (s22 hB).2.2 c23 k23

theorem s24 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (11999982456859 + 1000000000) ∧ Nat.Prime 11999982456859 ∧ 3 ≤ 11999982456859 :=
  step hB (by norm_num) (s23 hB).1 (s23 hB).2.1 (s23 hB).2.2 c24 k24

theorem s25 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (12499981350683 + 1000000000) ∧ Nat.Prime 12499981350683 ∧ 3 ≤ 12499981350683 :=
  step hB (by norm_num) (s24 hB).1 (s24 hB).2.1 (s24 hB).2.2 c25 k25

theorem s26 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (12999980260741 + 1000000000) ∧ Nat.Prime 12999980260741 ∧ 3 ≤ 12999980260741 :=
  step hB (by norm_num) (s25 hB).1 (s25 hB).2.1 (s25 hB).2.2 c26 k26

theorem s27 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (13499979247883 + 1000000000) ∧ Nat.Prime 13499979247883 ∧ 3 ≤ 13499979247883 :=
  step hB (by norm_num) (s26 hB).1 (s26 hB).2.1 (s26 hB).2.2 c27 k27

theorem s28 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (13999978329173 + 1000000000) ∧ Nat.Prime 13999978329173 ∧ 3 ≤ 13999978329173 :=
  step hB (by norm_num) (s27 hB).1 (s27 hB).2.1 (s27 hB).2.2 c28 k28

theorem s29 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (14499977229761 + 1000000000) ∧ Nat.Prime 14499977229761 ∧ 3 ≤ 14499977229761 :=
  step hB (by norm_num) (s28 hB).1 (s28 hB).2.1 (s28 hB).2.2 c29 k29

theorem s30 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (14999976109031 + 1000000000) ∧ Nat.Prime 14999976109031 ∧ 3 ≤ 14999976109031 :=
  step hB (by norm_num) (s29 hB).1 (s29 hB).2.1 (s29 hB).2.2 c30 k30

theorem s31 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (15499975030219 + 1000000000) ∧ Nat.Prime 15499975030219 ∧ 3 ≤ 15499975030219 :=
  step hB (by norm_num) (s30 hB).1 (s30 hB).2.1 (s30 hB).2.2 c31 k31

theorem s32 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (15999973976473 + 1000000000) ∧ Nat.Prime 15999973976473 ∧ 3 ≤ 15999973976473 :=
  step hB (by norm_num) (s31 hB).1 (s31 hB).2.1 (s31 hB).2.2 c32 k32

theorem s33 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (16499972836289 + 1000000000) ∧ Nat.Prime 16499972836289 ∧ 3 ≤ 16499972836289 :=
  step hB (by norm_num) (s32 hB).1 (s32 hB).2.1 (s32 hB).2.2 c33 k33

theorem s34 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (16999971785701 + 1000000000) ∧ Nat.Prime 16999971785701 ∧ 3 ≤ 16999971785701 :=
  step hB (by norm_num) (s33 hB).1 (s33 hB).2.1 (s33 hB).2.2 c34 k34

theorem s35 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (17499970632701 + 1000000000) ∧ Nat.Prime 17499970632701 ∧ 3 ≤ 17499970632701 :=
  step hB (by norm_num) (s34 hB).1 (s34 hB).2.1 (s34 hB).2.2 c35 k35

theorem s36 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (17999969365453 + 1000000000) ∧ Nat.Prime 17999969365453 ∧ 3 ≤ 17999969365453 :=
  step hB (by norm_num) (s35 hB).1 (s35 hB).2.1 (s35 hB).2.2 c36 k36

theorem s37 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (18499968296239 + 1000000000) ∧ Nat.Prime 18499968296239 ∧ 3 ≤ 18499968296239 :=
  step hB (by norm_num) (s36 hB).1 (s36 hB).2.1 (s36 hB).2.2 c37 k37

theorem s38 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (18999967127341 + 1000000000) ∧ Nat.Prime 18999967127341 ∧ 3 ≤ 18999967127341 :=
  step hB (by norm_num) (s37 hB).1 (s37 hB).2.1 (s37 hB).2.2 c38 k38

theorem s39 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (19499965987903 + 1000000000) ∧ Nat.Prime 19499965987903 ∧ 3 ≤ 19499965987903 :=
  step hB (by norm_num) (s38 hB).1 (s38 hB).2.1 (s38 hB).2.2 c39 k39

theorem s40 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (19999964782297 + 1000000000) ∧ Nat.Prime 19999964782297 ∧ 3 ≤ 19999964782297 :=
  step hB (by norm_num) (s39 hB).1 (s39 hB).2.1 (s39 hB).2.2 c40 k40

theorem s41 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (20499963574091 + 1000000000) ∧ Nat.Prime 20499963574091 ∧ 3 ≤ 20499963574091 :=
  step hB (by norm_num) (s40 hB).1 (s40 hB).2.1 (s40 hB).2.2 c41 k41

theorem s42 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (20999962326199 + 1000000000) ∧ Nat.Prime 20999962326199 ∧ 3 ≤ 20999962326199 :=
  step hB (by norm_num) (s41 hB).1 (s41 hB).2.1 (s41 hB).2.2 c42 k42

theorem s43 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (21499961076751 + 1000000000) ∧ Nat.Prime 21499961076751 ∧ 3 ≤ 21499961076751 :=
  step hB (by norm_num) (s42 hB).1 (s42 hB).2.1 (s42 hB).2.2 c43 k43

theorem s44 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (21999959907641 + 1000000000) ∧ Nat.Prime 21999959907641 ∧ 3 ≤ 21999959907641 :=
  step hB (by norm_num) (s43 hB).1 (s43 hB).2.1 (s43 hB).2.2 c44 k44

theorem s45 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (22499958642709 + 1000000000) ∧ Nat.Prime 22499958642709 ∧ 3 ≤ 22499958642709 :=
  step hB (by norm_num) (s44 hB).1 (s44 hB).2.1 (s44 hB).2.2 c45 k45

theorem s46 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (22999957449613 + 1000000000) ∧ Nat.Prime 22999957449613 ∧ 3 ≤ 22999957449613 :=
  step hB (by norm_num) (s45 hB).1 (s45 hB).2.1 (s45 hB).2.2 c46 k46

theorem s47 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (23499956214349 + 1000000000) ∧ Nat.Prime 23499956214349 ∧ 3 ≤ 23499956214349 :=
  step hB (by norm_num) (s46 hB).1 (s46 hB).2.1 (s46 hB).2.2 c47 k47

theorem s48 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (23999954982709 + 1000000000) ∧ Nat.Prime 23999954982709 ∧ 3 ≤ 23999954982709 :=
  step hB (by norm_num) (s47 hB).1 (s47 hB).2.1 (s47 hB).2.2 c48 k48

theorem s49 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (24499953743539 + 1000000000) ∧ Nat.Prime 24499953743539 ∧ 3 ≤ 24499953743539 :=
  step hB (by norm_num) (s48 hB).1 (s48 hB).2.1 (s48 hB).2.2 c49 k49

theorem s50 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (24999952420901 + 1000000000) ∧ Nat.Prime 24999952420901 ∧ 3 ≤ 24999952420901 :=
  step hB (by norm_num) (s49 hB).1 (s49 hB).2.1 (s49 hB).2.2 c50 k50

theorem s51 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (25499951119147 + 1000000000) ∧ Nat.Prime 25499951119147 ∧ 3 ≤ 25499951119147 :=
  step hB (by norm_num) (s50 hB).1 (s50 hB).2.1 (s50 hB).2.2 c51 k51

theorem s52 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (25999949882759 + 1000000000) ∧ Nat.Prime 25999949882759 ∧ 3 ≤ 25999949882759 :=
  step hB (by norm_num) (s51 hB).1 (s51 hB).2.1 (s51 hB).2.2 c52 k52

theorem s53 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (26499948576851 + 1000000000) ∧ Nat.Prime 26499948576851 ∧ 3 ≤ 26499948576851 :=
  step hB (by norm_num) (s52 hB).1 (s52 hB).2.1 (s52 hB).2.2 c53 k53

theorem s54 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (26999947271593 + 1000000000) ∧ Nat.Prime 26999947271593 ∧ 3 ≤ 26999947271593 :=
  step hB (by norm_num) (s53 hB).1 (s53 hB).2.1 (s53 hB).2.2 c54 k54

theorem s55 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (27499945933321 + 1000000000) ∧ Nat.Prime 27499945933321 ∧ 3 ≤ 27499945933321 :=
  step hB (by norm_num) (s54 hB).1 (s54 hB).2.1 (s54 hB).2.2 c55 k55

theorem s56 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (27999944540093 + 1000000000) ∧ Nat.Prime 27999944540093 ∧ 3 ≤ 27999944540093 :=
  step hB (by norm_num) (s55 hB).1 (s55 hB).2.1 (s55 hB).2.2 c56 k56

theorem s57 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (28499943295969 + 1000000000) ∧ Nat.Prime 28499943295969 ∧ 3 ≤ 28499943295969 :=
  step hB (by norm_num) (s56 hB).1 (s56 hB).2.1 (s56 hB).2.2 c57 k57

theorem s58 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (28999941953737 + 1000000000) ∧ Nat.Prime 28999941953737 ∧ 3 ≤ 28999941953737 :=
  step hB (by norm_num) (s57 hB).1 (s57 hB).2.1 (s57 hB).2.2 c58 k58

theorem s59 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (29499940537453 + 1000000000) ∧ Nat.Prime 29499940537453 ∧ 3 ≤ 29499940537453 :=
  step hB (by norm_num) (s58 hB).1 (s58 hB).2.1 (s58 hB).2.2 c59 k59

theorem s60 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (29999939179519 + 1000000000) ∧ Nat.Prime 29999939179519 ∧ 3 ≤ 29999939179519 :=
  step hB (by norm_num) (s59 hB).1 (s59 hB).2.1 (s59 hB).2.2 c60 k60

theorem s61 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (30499937847979 + 1000000000) ∧ Nat.Prime 30499937847979 ∧ 3 ≤ 30499937847979 :=
  step hB (by norm_num) (s60 hB).1 (s60 hB).2.1 (s60 hB).2.2 c61 k61

theorem s62 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (30999936528653 + 1000000000) ∧ Nat.Prime 30999936528653 ∧ 3 ≤ 30999936528653 :=
  step hB (by norm_num) (s61 hB).1 (s61 hB).2.1 (s61 hB).2.2 c62 k62

theorem s63 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (31499935190263 + 1000000000) ∧ Nat.Prime 31499935190263 ∧ 3 ≤ 31499935190263 :=
  step hB (by norm_num) (s62 hB).1 (s62 hB).2.1 (s62 hB).2.2 c63 k63

theorem s64 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (31999933793851 + 1000000000) ∧ Nat.Prime 31999933793851 ∧ 3 ≤ 31999933793851 :=
  step hB (by norm_num) (s63 hB).1 (s63 hB).2.1 (s63 hB).2.2 c64 k64

theorem s65 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (32499932317451 + 1000000000) ∧ Nat.Prime 32499932317451 ∧ 3 ≤ 32499932317451 :=
  step hB (by norm_num) (s64 hB).1 (s64 hB).2.1 (s64 hB).2.2 c65 k65

theorem s66 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (32999930880901 + 1000000000) ∧ Nat.Prime 32999930880901 ∧ 3 ≤ 32999930880901 :=
  step hB (by norm_num) (s65 hB).1 (s65 hB).2.1 (s65 hB).2.2 c66 k66

theorem s67 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (33499929495691 + 1000000000) ∧ Nat.Prime 33499929495691 ∧ 3 ≤ 33499929495691 :=
  step hB (by norm_num) (s66 hB).1 (s66 hB).2.1 (s66 hB).2.2 c67 k67

theorem s68 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (33999928009601 + 1000000000) ∧ Nat.Prime 33999928009601 ∧ 3 ≤ 33999928009601 :=
  step hB (by norm_num) (s67 hB).1 (s67 hB).2.1 (s67 hB).2.2 c68 k68

theorem s69 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (34499926509827 + 1000000000) ∧ Nat.Prime 34499926509827 ∧ 3 ≤ 34499926509827 :=
  step hB (by norm_num) (s68 hB).1 (s68 hB).2.1 (s68 hB).2.2 c69 k69

theorem s70 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (34999925099941 + 1000000000) ∧ Nat.Prime 34999925099941 ∧ 3 ≤ 34999925099941 :=
  step hB (by norm_num) (s69 hB).1 (s69 hB).2.1 (s69 hB).2.2 c70 k70

theorem s71 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (35499923611153 + 1000000000) ∧ Nat.Prime 35499923611153 ∧ 3 ≤ 35499923611153 :=
  step hB (by norm_num) (s70 hB).1 (s70 hB).2.1 (s70 hB).2.2 c71 k71

theorem s72 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (35999921994041 + 1000000000) ∧ Nat.Prime 35999921994041 ∧ 3 ≤ 35999921994041 :=
  step hB (by norm_num) (s71 hB).1 (s71 hB).2.1 (s71 hB).2.2 c72 k72

theorem s73 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (36499920478081 + 1000000000) ∧ Nat.Prime 36499920478081 ∧ 3 ≤ 36499920478081 :=
  step hB (by norm_num) (s72 hB).1 (s72 hB).2.1 (s72 hB).2.2 c73 k73

theorem s74 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (36999919034521 + 1000000000) ∧ Nat.Prime 36999919034521 ∧ 3 ≤ 36999919034521 :=
  step hB (by norm_num) (s73 hB).1 (s73 hB).2.1 (s73 hB).2.2 c74 k74

theorem s75 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (37499917628713 + 1000000000) ∧ Nat.Prime 37499917628713 ∧ 3 ≤ 37499917628713 :=
  step hB (by norm_num) (s74 hB).1 (s74 hB).2.1 (s74 hB).2.2 c75 k75

theorem s76 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (37999916198443 + 1000000000) ∧ Nat.Prime 37999916198443 ∧ 3 ≤ 37999916198443 :=
  step hB (by norm_num) (s75 hB).1 (s75 hB).2.1 (s75 hB).2.2 c76 k76

theorem s77 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (38499914641411 + 1000000000) ∧ Nat.Prime 38499914641411 ∧ 3 ≤ 38499914641411 :=
  step hB (by norm_num) (s76 hB).1 (s76 hB).2.1 (s76 hB).2.2 c77 k77

theorem s78 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (38999913142511 + 1000000000) ∧ Nat.Prime 38999913142511 ∧ 3 ≤ 38999913142511 :=
  step hB (by norm_num) (s77 hB).1 (s77 hB).2.1 (s77 hB).2.2 c78 k78

theorem s79 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (39499911687601 + 1000000000) ∧ Nat.Prime 39499911687601 ∧ 3 ≤ 39499911687601 :=
  step hB (by norm_num) (s78 hB).1 (s78 hB).2.1 (s78 hB).2.2 c79 k79

theorem s80 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (39999910194931 + 1000000000) ∧ Nat.Prime 39999910194931 ∧ 3 ≤ 39999910194931 :=
  step hB (by norm_num) (s79 hB).1 (s79 hB).2.1 (s79 hB).2.2 c80 k80

theorem s81 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (40499908635187 + 1000000000) ∧ Nat.Prime 40499908635187 ∧ 3 ≤ 40499908635187 :=
  step hB (by norm_num) (s80 hB).1 (s80 hB).2.1 (s80 hB).2.2 c81 k81

theorem s82 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (40999907036791 + 1000000000) ∧ Nat.Prime 40999907036791 ∧ 3 ≤ 40999907036791 :=
  step hB (by norm_num) (s81 hB).1 (s81 hB).2.1 (s81 hB).2.2 c82 k82

theorem s83 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (41499905631409 + 1000000000) ∧ Nat.Prime 41499905631409 ∧ 3 ≤ 41499905631409 :=
  step hB (by norm_num) (s82 hB).1 (s82 hB).2.1 (s82 hB).2.2 c83 k83

theorem s84 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (41999904049951 + 1000000000) ∧ Nat.Prime 41999904049951 ∧ 3 ≤ 41999904049951 :=
  step hB (by norm_num) (s83 hB).1 (s83 hB).2.1 (s83 hB).2.2 c84 k84

theorem s85 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (42499902375967 + 1000000000) ∧ Nat.Prime 42499902375967 ∧ 3 ≤ 42499902375967 :=
  step hB (by norm_num) (s84 hB).1 (s84 hB).2.1 (s84 hB).2.2 c85 k85

theorem s86 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (42999900793951 + 1000000000) ∧ Nat.Prime 42999900793951 ∧ 3 ≤ 42999900793951 :=
  step hB (by norm_num) (s85 hB).1 (s85 hB).2.1 (s85 hB).2.2 c86 k86

theorem s87 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (43499899203463 + 1000000000) ∧ Nat.Prime 43499899203463 ∧ 3 ≤ 43499899203463 :=
  step hB (by norm_num) (s86 hB).1 (s86 hB).2.1 (s86 hB).2.2 c87 k87

theorem s88 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (43999897535749 + 1000000000) ∧ Nat.Prime 43999897535749 ∧ 3 ≤ 43999897535749 :=
  step hB (by norm_num) (s87 hB).1 (s87 hB).2.1 (s87 hB).2.2 c88 k88

theorem s89 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (44499896051651 + 1000000000) ∧ Nat.Prime 44499896051651 ∧ 3 ≤ 44499896051651 :=
  step hB (by norm_num) (s88 hB).1 (s88 hB).2.1 (s88 hB).2.2 c89 k89

theorem s90 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (44999894525527 + 1000000000) ∧ Nat.Prime 44999894525527 ∧ 3 ≤ 44999894525527 :=
  step hB (by norm_num) (s89 hB).1 (s89 hB).2.1 (s89 hB).2.2 c90 k90

theorem s91 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (45499892851997 + 1000000000) ∧ Nat.Prime 45499892851997 ∧ 3 ≤ 45499892851997 :=
  step hB (by norm_num) (s90 hB).1 (s90 hB).2.1 (s90 hB).2.2 c91 k91

theorem s92 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (45999891318977 + 1000000000) ∧ Nat.Prime 45999891318977 ∧ 3 ≤ 45999891318977 :=
  step hB (by norm_num) (s91 hB).1 (s91 hB).2.1 (s91 hB).2.2 c92 k92

theorem s93 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (46499889836401 + 1000000000) ∧ Nat.Prime 46499889836401 ∧ 3 ≤ 46499889836401 :=
  step hB (by norm_num) (s92 hB).1 (s92 hB).2.1 (s92 hB).2.2 c93 k93

theorem s94 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (46999888153177 + 1000000000) ∧ Nat.Prime 46999888153177 ∧ 3 ≤ 46999888153177 :=
  step hB (by norm_num) (s93 hB).1 (s93 hB).2.1 (s93 hB).2.2 c94 k94

theorem s95 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (47499886564369 + 1000000000) ∧ Nat.Prime 47499886564369 ∧ 3 ≤ 47499886564369 :=
  step hB (by norm_num) (s94 hB).1 (s94 hB).2.1 (s94 hB).2.2 c95 k95

theorem s96 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (47999884945937 + 1000000000) ∧ Nat.Prime 47999884945937 ∧ 3 ≤ 47999884945937 :=
  step hB (by norm_num) (s95 hB).1 (s95 hB).2.1 (s95 hB).2.2 c96 k96

theorem s97 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (48499883251639 + 1000000000) ∧ Nat.Prime 48499883251639 ∧ 3 ≤ 48499883251639 :=
  step hB (by norm_num) (s96 hB).1 (s96 hB).2.1 (s96 hB).2.2 c97 k97

theorem s98 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (48999881741507 + 1000000000) ∧ Nat.Prime 48999881741507 ∧ 3 ≤ 48999881741507 :=
  step hB (by norm_num) (s97 hB).1 (s97 hB).2.1 (s97 hB).2.2 c98 k98

theorem s99 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (49499880091267 + 1000000000) ∧ Nat.Prime 49499880091267 ∧ 3 ≤ 49499880091267 :=
  step hB (by norm_num) (s98 hB).1 (s98 hB).2.1 (s98 hB).2.2 c99 k99

theorem s100 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (49999878523379 + 1000000000) ∧ Nat.Prime 49999878523379 ∧ 3 ≤ 49999878523379 :=
  step hB (by norm_num) (s99 hB).1 (s99 hB).2.1 (s99 hB).2.2 c100 k100

theorem s101 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (50499876981397 + 1000000000) ∧ Nat.Prime 50499876981397 ∧ 3 ≤ 50499876981397 :=
  step hB (by norm_num) (s100 hB).1 (s100 hB).2.1 (s100 hB).2.2 c101 k101

theorem s102 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (50999875341713 + 1000000000) ∧ Nat.Prime 50999875341713 ∧ 3 ≤ 50999875341713 :=
  step hB (by norm_num) (s101 hB).1 (s101 hB).2.1 (s101 hB).2.2 c102 k102

theorem s103 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (51499873574159 + 1000000000) ∧ Nat.Prime 51499873574159 ∧ 3 ≤ 51499873574159 :=
  step hB (by norm_num) (s102 hB).1 (s102 hB).2.1 (s102 hB).2.2 c103 k103

theorem s104 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (51999871882711 + 1000000000) ∧ Nat.Prime 51999871882711 ∧ 3 ≤ 51999871882711 :=
  step hB (by norm_num) (s103 hB).1 (s103 hB).2.1 (s103 hB).2.2 c104 k104

theorem s105 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (52499870310707 + 1000000000) ∧ Nat.Prime 52499870310707 ∧ 3 ≤ 52499870310707 :=
  step hB (by norm_num) (s104 hB).1 (s104 hB).2.1 (s104 hB).2.2 c105 k105

theorem s106 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (52999868766673 + 1000000000) ∧ Nat.Prime 52999868766673 ∧ 3 ≤ 52999868766673 :=
  step hB (by norm_num) (s105 hB).1 (s105 hB).2.1 (s105 hB).2.2 c106 k106

theorem s107 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (53499867088501 + 1000000000) ∧ Nat.Prime 53499867088501 ∧ 3 ≤ 53499867088501 :=
  step hB (by norm_num) (s106 hB).1 (s106 hB).2.1 (s106 hB).2.2 c107 k107

theorem s108 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (53999865422771 + 1000000000) ∧ Nat.Prime 53999865422771 ∧ 3 ≤ 53999865422771 :=
  step hB (by norm_num) (s107 hB).1 (s107 hB).2.1 (s107 hB).2.2 c108 k108

theorem s109 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (54499863693049 + 1000000000) ∧ Nat.Prime 54499863693049 ∧ 3 ≤ 54499863693049 :=
  step hB (by norm_num) (s108 hB).1 (s108 hB).2.1 (s108 hB).2.2 c109 k109

theorem s110 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (54999862020167 + 1000000000) ∧ Nat.Prime 54999862020167 ∧ 3 ≤ 54999862020167 :=
  step hB (by norm_num) (s109 hB).1 (s109 hB).2.1 (s109 hB).2.2 c110 k110

theorem s111 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (55499860377289 + 1000000000) ∧ Nat.Prime 55499860377289 ∧ 3 ≤ 55499860377289 :=
  step hB (by norm_num) (s110 hB).1 (s110 hB).2.1 (s110 hB).2.2 c111 k111

theorem s112 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (55999858709713 + 1000000000) ∧ Nat.Prime 55999858709713 ∧ 3 ≤ 55999858709713 :=
  step hB (by norm_num) (s111 hB).1 (s111 hB).2.1 (s111 hB).2.2 c112 k112

theorem s113 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (56499856903783 + 1000000000) ∧ Nat.Prime 56499856903783 ∧ 3 ≤ 56499856903783 :=
  step hB (by norm_num) (s112 hB).1 (s112 hB).2.1 (s112 hB).2.2 c113 k113

theorem s114 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (56999855172487 + 1000000000) ∧ Nat.Prime 56999855172487 ∧ 3 ≤ 56999855172487 :=
  step hB (by norm_num) (s113 hB).1 (s113 hB).2.1 (s113 hB).2.2 c114 k114

theorem s115 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (57499853362681 + 1000000000) ∧ Nat.Prime 57499853362681 ∧ 3 ≤ 57499853362681 :=
  step hB (by norm_num) (s114 hB).1 (s114 hB).2.1 (s114 hB).2.2 c115 k115

theorem s116 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (57999851637701 + 1000000000) ∧ Nat.Prime 57999851637701 ∧ 3 ≤ 57999851637701 :=
  step hB (by norm_num) (s115 hB).1 (s115 hB).2.1 (s115 hB).2.2 c116 k116

theorem s117 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (58499849966737 + 1000000000) ∧ Nat.Prime 58499849966737 ∧ 3 ≤ 58499849966737 :=
  step hB (by norm_num) (s116 hB).1 (s116 hB).2.1 (s116 hB).2.2 c117 k117

theorem s118 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (58999848237271 + 1000000000) ∧ Nat.Prime 58999848237271 ∧ 3 ≤ 58999848237271 :=
  step hB (by norm_num) (s117 hB).1 (s117 hB).2.1 (s117 hB).2.2 c118 k118

theorem s119 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (59499846458443 + 1000000000) ∧ Nat.Prime 59499846458443 ∧ 3 ≤ 59499846458443 :=
  step hB (by norm_num) (s118 hB).1 (s118 hB).2.1 (s118 hB).2.2 c119 k119

theorem s120 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (59999844769201 + 1000000000) ∧ Nat.Prime 59999844769201 ∧ 3 ≤ 59999844769201 :=
  step hB (by norm_num) (s119 hB).1 (s119 hB).2.1 (s119 hB).2.2 c120 k120

theorem s121 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (60499842894709 + 1000000000) ∧ Nat.Prime 60499842894709 ∧ 3 ≤ 60499842894709 :=
  step hB (by norm_num) (s120 hB).1 (s120 hB).2.1 (s120 hB).2.2 c121 k121

theorem s122 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (60999841174001 + 1000000000) ∧ Nat.Prime 60999841174001 ∧ 3 ≤ 60999841174001 :=
  step hB (by norm_num) (s121 hB).1 (s121 hB).2.1 (s121 hB).2.2 c122 k122

theorem s123 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (61499839405201 + 1000000000) ∧ Nat.Prime 61499839405201 ∧ 3 ≤ 61499839405201 :=
  step hB (by norm_num) (s122 hB).1 (s122 hB).2.1 (s122 hB).2.2 c123 k123

theorem s124 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (61999837634269 + 1000000000) ∧ Nat.Prime 61999837634269 ∧ 3 ≤ 61999837634269 :=
  step hB (by norm_num) (s123 hB).1 (s123 hB).2.1 (s123 hB).2.2 c124 k124

theorem s125 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (62499835827937 + 1000000000) ∧ Nat.Prime 62499835827937 ∧ 3 ≤ 62499835827937 :=
  step hB (by norm_num) (s124 hB).1 (s124 hB).2.1 (s124 hB).2.2 c125 k125

theorem s126 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (62999834102341 + 1000000000) ∧ Nat.Prime 62999834102341 ∧ 3 ≤ 62999834102341 :=
  step hB (by norm_num) (s125 hB).1 (s125 hB).2.1 (s125 hB).2.2 c126 k126

theorem s127 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (63499832226001 + 1000000000) ∧ Nat.Prime 63499832226001 ∧ 3 ≤ 63499832226001 :=
  step hB (by norm_num) (s126 hB).1 (s126 hB).2.1 (s126 hB).2.2 c127 k127

theorem s128 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (63999830430901 + 1000000000) ∧ Nat.Prime 63999830430901 ∧ 3 ≤ 63999830430901 :=
  step hB (by norm_num) (s127 hB).1 (s127 hB).2.1 (s127 hB).2.2 c128 k128

theorem s129 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (64499828590189 + 1000000000) ∧ Nat.Prime 64499828590189 ∧ 3 ≤ 64499828590189 :=
  step hB (by norm_num) (s128 hB).1 (s128 hB).2.1 (s128 hB).2.2 c129 k129

theorem s130 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (64999826828821 + 1000000000) ∧ Nat.Prime 64999826828821 ∧ 3 ≤ 64999826828821 :=
  step hB (by norm_num) (s129 hB).1 (s129 hB).2.1 (s129 hB).2.2 c130 k130

theorem s131 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (65499824899637 + 1000000000) ∧ Nat.Prime 65499824899637 ∧ 3 ≤ 65499824899637 :=
  step hB (by norm_num) (s130 hB).1 (s130 hB).2.1 (s130 hB).2.2 c131 k131

theorem s132 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (65999822994361 + 1000000000) ∧ Nat.Prime 65999822994361 ∧ 3 ≤ 65999822994361 :=
  step hB (by norm_num) (s131 hB).1 (s131 hB).2.1 (s131 hB).2.2 c132 k132

theorem s133 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (66499821202673 + 1000000000) ∧ Nat.Prime 66499821202673 ∧ 3 ≤ 66499821202673 :=
  step hB (by norm_num) (s132 hB).1 (s132 hB).2.1 (s132 hB).2.2 c133 k133

theorem s134 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (66999819401401 + 1000000000) ∧ Nat.Prime 66999819401401 ∧ 3 ≤ 66999819401401 :=
  step hB (by norm_num) (s133 hB).1 (s133 hB).2.1 (s133 hB).2.2 c134 k134

theorem s135 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (67499817541561 + 1000000000) ∧ Nat.Prime 67499817541561 ∧ 3 ≤ 67499817541561 :=
  step hB (by norm_num) (s134 hB).1 (s134 hB).2.1 (s134 hB).2.2 c135 k135

theorem s136 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (67999815768301 + 1000000000) ∧ Nat.Prime 67999815768301 ∧ 3 ≤ 67999815768301 :=
  step hB (by norm_num) (s135 hB).1 (s135 hB).2.1 (s135 hB).2.2 c136 k136

theorem s137 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (68499813960241 + 1000000000) ∧ Nat.Prime 68499813960241 ∧ 3 ≤ 68499813960241 :=
  step hB (by norm_num) (s136 hB).1 (s136 hB).2.1 (s136 hB).2.2 c137 k137

theorem s138 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (68999811936067 + 1000000000) ∧ Nat.Prime 68999811936067 ∧ 3 ≤ 68999811936067 :=
  step hB (by norm_num) (s137 hB).1 (s137 hB).2.1 (s137 hB).2.2 c138 k138

theorem s139 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (69499809929441 + 1000000000) ∧ Nat.Prime 69499809929441 ∧ 3 ≤ 69499809929441 :=
  step hB (by norm_num) (s138 hB).1 (s138 hB).2.1 (s138 hB).2.2 c139 k139

theorem s140 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (69999808033717 + 1000000000) ∧ Nat.Prime 69999808033717 ∧ 3 ≤ 69999808033717 :=
  step hB (by norm_num) (s139 hB).1 (s139 hB).2.1 (s139 hB).2.2 c140 k140

theorem s141 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (70499806180651 + 1000000000) ∧ Nat.Prime 70499806180651 ∧ 3 ≤ 70499806180651 :=
  step hB (by norm_num) (s140 hB).1 (s140 hB).2.1 (s140 hB).2.2 c141 k141

theorem s142 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (70999804465153 + 1000000000) ∧ Nat.Prime 70999804465153 ∧ 3 ≤ 70999804465153 :=
  step hB (by norm_num) (s141 hB).1 (s141 hB).2.1 (s141 hB).2.2 c142 k142

theorem s143 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (71499802625161 + 1000000000) ∧ Nat.Prime 71499802625161 ∧ 3 ≤ 71499802625161 :=
  step hB (by norm_num) (s142 hB).1 (s142 hB).2.1 (s142 hB).2.2 c143 k143

theorem s144 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (71999800739777 + 1000000000) ∧ Nat.Prime 71999800739777 ∧ 3 ≤ 71999800739777 :=
  step hB (by norm_num) (s143 hB).1 (s143 hB).2.1 (s143 hB).2.2 c144 k144

theorem s145 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (72499798825177 + 1000000000) ∧ Nat.Prime 72499798825177 ∧ 3 ≤ 72499798825177 :=
  step hB (by norm_num) (s144 hB).1 (s144 hB).2.1 (s144 hB).2.2 c145 k145

theorem s146 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (72999797047867 + 1000000000) ∧ Nat.Prime 72999797047867 ∧ 3 ≤ 72999797047867 :=
  step hB (by norm_num) (s145 hB).1 (s145 hB).2.1 (s145 hB).2.2 c146 k146

theorem s147 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (73499795141081 + 1000000000) ∧ Nat.Prime 73499795141081 ∧ 3 ≤ 73499795141081 :=
  step hB (by norm_num) (s146 hB).1 (s146 hB).2.1 (s146 hB).2.2 c147 k147

theorem s148 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (73999793266831 + 1000000000) ∧ Nat.Prime 73999793266831 ∧ 3 ≤ 73999793266831 :=
  step hB (by norm_num) (s147 hB).1 (s147 hB).2.1 (s147 hB).2.2 c148 k148

theorem s149 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (74499791379877 + 1000000000) ∧ Nat.Prime 74499791379877 ∧ 3 ≤ 74499791379877 :=
  step hB (by norm_num) (s148 hB).1 (s148 hB).2.1 (s148 hB).2.2 c149 k149

theorem s150 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (74999789507131 + 1000000000) ∧ Nat.Prime 74999789507131 ∧ 3 ≤ 74999789507131 :=
  step hB (by norm_num) (s149 hB).1 (s149 hB).2.1 (s149 hB).2.2 c150 k150

theorem s151 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (75499787601389 + 1000000000) ∧ Nat.Prime 75499787601389 ∧ 3 ≤ 75499787601389 :=
  step hB (by norm_num) (s150 hB).1 (s150 hB).2.1 (s150 hB).2.2 c151 k151

theorem s152 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (75999785559121 + 1000000000) ∧ Nat.Prime 75999785559121 ∧ 3 ≤ 75999785559121 :=
  step hB (by norm_num) (s151 hB).1 (s151 hB).2.1 (s151 hB).2.2 c152 k152

theorem s153 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (76499783738659 + 1000000000) ∧ Nat.Prime 76499783738659 ∧ 3 ≤ 76499783738659 :=
  step hB (by norm_num) (s152 hB).1 (s152 hB).2.1 (s152 hB).2.2 c153 k153

theorem s154 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (76999781966273 + 1000000000) ∧ Nat.Prime 76999781966273 ∧ 3 ≤ 76999781966273 :=
  step hB (by norm_num) (s153 hB).1 (s153 hB).2.1 (s153 hB).2.2 c154 k154

theorem s155 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (77499780078121 + 1000000000) ∧ Nat.Prime 77499780078121 ∧ 3 ≤ 77499780078121 :=
  step hB (by norm_num) (s154 hB).1 (s154 hB).2.1 (s154 hB).2.2 c155 k155

theorem s156 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (77999778213769 + 1000000000) ∧ Nat.Prime 77999778213769 ∧ 3 ≤ 77999778213769 :=
  step hB (by norm_num) (s155 hB).1 (s155 hB).2.1 (s155 hB).2.2 c156 k156

theorem s157 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (78499776271153 + 1000000000) ∧ Nat.Prime 78499776271153 ∧ 3 ≤ 78499776271153 :=
  step hB (by norm_num) (s156 hB).1 (s156 hB).2.1 (s156 hB).2.2 c157 k157

theorem s158 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (78999774327431 + 1000000000) ∧ Nat.Prime 78999774327431 ∧ 3 ≤ 78999774327431 :=
  step hB (by norm_num) (s157 hB).1 (s157 hB).2.1 (s157 hB).2.2 c158 k158

theorem s159 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (79499772384667 + 1000000000) ∧ Nat.Prime 79499772384667 ∧ 3 ≤ 79499772384667 :=
  step hB (by norm_num) (s158 hB).1 (s158 hB).2.1 (s158 hB).2.2 c159 k159

theorem s160 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (79999770326401 + 1000000000) ∧ Nat.Prime 79999770326401 ∧ 3 ≤ 79999770326401 :=
  step hB (by norm_num) (s159 hB).1 (s159 hB).2.1 (s159 hB).2.2 c160 k160

theorem s161 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (80499768553531 + 1000000000) ∧ Nat.Prime 80499768553531 ∧ 3 ≤ 80499768553531 :=
  step hB (by norm_num) (s160 hB).1 (s160 hB).2.1 (s160 hB).2.2 c161 k161

theorem s162 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (80999766448751 + 1000000000) ∧ Nat.Prime 80999766448751 ∧ 3 ≤ 80999766448751 :=
  step hB (by norm_num) (s161 hB).1 (s161 hB).2.1 (s161 hB).2.2 c162 k162

theorem s163 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (81499764550433 + 1000000000) ∧ Nat.Prime 81499764550433 ∧ 3 ≤ 81499764550433 :=
  step hB (by norm_num) (s162 hB).1 (s162 hB).2.1 (s162 hB).2.2 c163 k163

theorem s164 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (81999762671179 + 1000000000) ∧ Nat.Prime 81999762671179 ∧ 3 ≤ 81999762671179 :=
  step hB (by norm_num) (s163 hB).1 (s163 hB).2.1 (s163 hB).2.2 c164 k164

theorem s165 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (82499760635821 + 1000000000) ∧ Nat.Prime 82499760635821 ∧ 3 ≤ 82499760635821 :=
  step hB (by norm_num) (s164 hB).1 (s164 hB).2.1 (s164 hB).2.2 c165 k165

theorem s166 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (82999758676321 + 1000000000) ∧ Nat.Prime 82999758676321 ∧ 3 ≤ 82999758676321 :=
  step hB (by norm_num) (s165 hB).1 (s165 hB).2.1 (s165 hB).2.2 c166 k166

theorem s167 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (83499756717203 + 1000000000) ∧ Nat.Prime 83499756717203 ∧ 3 ≤ 83499756717203 :=
  step hB (by norm_num) (s166 hB).1 (s166 hB).2.1 (s166 hB).2.2 c167 k167

theorem s168 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (83999754719819 + 1000000000) ∧ Nat.Prime 83999754719819 ∧ 3 ≤ 83999754719819 :=
  step hB (by norm_num) (s167 hB).1 (s167 hB).2.1 (s167 hB).2.2 c168 k168

theorem s169 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (84499752639251 + 1000000000) ∧ Nat.Prime 84499752639251 ∧ 3 ≤ 84499752639251 :=
  step hB (by norm_num) (s168 hB).1 (s168 hB).2.1 (s168 hB).2.2 c169 k169

theorem s170 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (84999750583991 + 1000000000) ∧ Nat.Prime 84999750583991 ∧ 3 ≤ 84999750583991 :=
  step hB (by norm_num) (s169 hB).1 (s169 hB).2.1 (s169 hB).2.2 c170 k170

theorem s171 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (85499748586481 + 1000000000) ∧ Nat.Prime 85499748586481 ∧ 3 ≤ 85499748586481 :=
  step hB (by norm_num) (s170 hB).1 (s170 hB).2.1 (s170 hB).2.2 c171 k171

theorem s172 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (85999746611413 + 1000000000) ∧ Nat.Prime 85999746611413 ∧ 3 ≤ 85999746611413 :=
  step hB (by norm_num) (s171 hB).1 (s171 hB).2.1 (s171 hB).2.2 c172 k172

theorem s173 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (86499744816673 + 1000000000) ∧ Nat.Prime 86499744816673 ∧ 3 ≤ 86499744816673 :=
  step hB (by norm_num) (s172 hB).1 (s172 hB).2.1 (s172 hB).2.2 c173 k173

theorem s174 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (86999742860977 + 1000000000) ∧ Nat.Prime 86999742860977 ∧ 3 ≤ 86999742860977 :=
  step hB (by norm_num) (s173 hB).1 (s173 hB).2.1 (s173 hB).2.2 c174 k174

theorem s175 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (87499740891929 + 1000000000) ∧ Nat.Prime 87499740891929 ∧ 3 ≤ 87499740891929 :=
  step hB (by norm_num) (s174 hB).1 (s174 hB).2.1 (s174 hB).2.2 c175 k175

theorem s176 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (87999738765409 + 1000000000) ∧ Nat.Prime 87999738765409 ∧ 3 ≤ 87999738765409 :=
  step hB (by norm_num) (s175 hB).1 (s175 hB).2.1 (s175 hB).2.2 c176 k176

theorem s177 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (88499736645113 + 1000000000) ∧ Nat.Prime 88499736645113 ∧ 3 ≤ 88499736645113 :=
  step hB (by norm_num) (s176 hB).1 (s176 hB).2.1 (s176 hB).2.2 c177 k177

theorem s178 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (88999734702451 + 1000000000) ∧ Nat.Prime 88999734702451 ∧ 3 ≤ 88999734702451 :=
  step hB (by norm_num) (s177 hB).1 (s177 hB).2.1 (s177 hB).2.2 c178 k178

theorem s179 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (89499732656251 + 1000000000) ∧ Nat.Prime 89499732656251 ∧ 3 ≤ 89499732656251 :=
  step hB (by norm_num) (s178 hB).1 (s178 hB).2.1 (s178 hB).2.2 c179 k179

theorem s180 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (89999730522469 + 1000000000) ∧ Nat.Prime 89999730522469 ∧ 3 ≤ 89999730522469 :=
  step hB (by norm_num) (s179 hB).1 (s179 hB).2.1 (s179 hB).2.2 c180 k180

theorem s181 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (90499728370627 + 1000000000) ∧ Nat.Prime 90499728370627 ∧ 3 ≤ 90499728370627 :=
  step hB (by norm_num) (s180 hB).1 (s180 hB).2.1 (s180 hB).2.2 c181 k181

theorem s182 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (90999726499657 + 1000000000) ∧ Nat.Prime 90999726499657 ∧ 3 ≤ 90999726499657 :=
  step hB (by norm_num) (s181 hB).1 (s181 hB).2.1 (s181 hB).2.2 c182 k182

theorem s183 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (91499724569221 + 1000000000) ∧ Nat.Prime 91499724569221 ∧ 3 ≤ 91499724569221 :=
  step hB (by norm_num) (s182 hB).1 (s182 hB).2.1 (s182 hB).2.2 c183 k183

theorem s184 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (91999722545243 + 1000000000) ∧ Nat.Prime 91999722545243 ∧ 3 ≤ 91999722545243 :=
  step hB (by norm_num) (s183 hB).1 (s183 hB).2.1 (s183 hB).2.2 c184 k184

theorem s185 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (92499720514541 + 1000000000) ∧ Nat.Prime 92499720514541 ∧ 3 ≤ 92499720514541 :=
  step hB (by norm_num) (s184 hB).1 (s184 hB).2.1 (s184 hB).2.2 c185 k185

theorem s186 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (92999718344737 + 1000000000) ∧ Nat.Prime 92999718344737 ∧ 3 ≤ 92999718344737 :=
  step hB (by norm_num) (s185 hB).1 (s185 hB).2.1 (s185 hB).2.2 c186 k186

theorem s187 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (93499716211529 + 1000000000) ∧ Nat.Prime 93499716211529 ∧ 3 ≤ 93499716211529 :=
  step hB (by norm_num) (s186 hB).1 (s186 hB).2.1 (s186 hB).2.2 c187 k187

theorem s188 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (93999714073021 + 1000000000) ∧ Nat.Prime 93999714073021 ∧ 3 ≤ 93999714073021 :=
  step hB (by norm_num) (s187 hB).1 (s187 hB).2.1 (s187 hB).2.2 c188 k188

theorem s189 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (94499712016753 + 1000000000) ∧ Nat.Prime 94499712016753 ∧ 3 ≤ 94499712016753 :=
  step hB (by norm_num) (s188 hB).1 (s188 hB).2.1 (s188 hB).2.2 c189 k189

theorem s190 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (94999709983289 + 1000000000) ∧ Nat.Prime 94999709983289 ∧ 3 ≤ 94999709983289 :=
  step hB (by norm_num) (s189 hB).1 (s189 hB).2.1 (s189 hB).2.2 c190 k190

theorem s191 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (95499707978201 + 1000000000) ∧ Nat.Prime 95499707978201 ∧ 3 ≤ 95499707978201 :=
  step hB (by norm_num) (s190 hB).1 (s190 hB).2.1 (s190 hB).2.2 c191 k191

theorem s192 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (95999705961281 + 1000000000) ∧ Nat.Prime 95999705961281 ∧ 3 ≤ 95999705961281 :=
  step hB (by norm_num) (s191 hB).1 (s191 hB).2.1 (s191 hB).2.2 c192 k192

theorem s193 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (96499703825201 + 1000000000) ∧ Nat.Prime 96499703825201 ∧ 3 ≤ 96499703825201 :=
  step hB (by norm_num) (s192 hB).1 (s192 hB).2.1 (s192 hB).2.2 c193 k193

theorem s194 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (96999701728441 + 1000000000) ∧ Nat.Prime 96999701728441 ∧ 3 ≤ 96999701728441 :=
  step hB (by norm_num) (s193 hB).1 (s193 hB).2.1 (s193 hB).2.2 c194 k194

theorem s195 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (97499699613577 + 1000000000) ∧ Nat.Prime 97499699613577 ∧ 3 ≤ 97499699613577 :=
  step hB (by norm_num) (s194 hB).1 (s194 hB).2.1 (s194 hB).2.2 c195 k195

theorem s196 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (97999697595221 + 1000000000) ∧ Nat.Prime 97999697595221 ∧ 3 ≤ 97999697595221 :=
  step hB (by norm_num) (s195 hB).1 (s195 hB).2.1 (s195 hB).2.2 c196 k196

theorem s197 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (98499695480653 + 1000000000) ∧ Nat.Prime 98499695480653 ∧ 3 ≤ 98499695480653 :=
  step hB (by norm_num) (s196 hB).1 (s196 hB).2.1 (s196 hB).2.2 c197 k197

theorem s198 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (98999693365607 + 1000000000) ∧ Nat.Prime 98999693365607 ∧ 3 ≤ 98999693365607 :=
  step hB (by norm_num) (s197 hB).1 (s197 hB).2.1 (s197 hB).2.2 c198 k198

theorem s199 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (99499691508229 + 1000000000) ∧ Nat.Prime 99499691508229 ∧ 3 ≤ 99499691508229 :=
  step hB (by norm_num) (s198 hB).1 (s198 hB).2.1 (s198 hB).2.2 c199 k199

theorem s200 (hB : EvenGoldbachUpTo 1000000000) :
    TernaryGoldbachUpTo (99999689365487 + 1000000000) ∧ Nat.Prime 99999689365487 ∧ 3 ≤ 99999689365487 :=
  step hB (by norm_num) (s199 hB).1 (s199 hB).2.1 (s199 hB).2.2 c200 k200

/-- Saouter's step: even Goldbach to 10^9 and this ladder give ternary Goldbach to 100000689365487. -/
theorem ternary_of_even (hB : EvenGoldbachUpTo 1000000000) : TernaryGoldbachUpTo 100000689365487 :=
  (s200 hB).1

end LeanLab.Saouter1998.B9
