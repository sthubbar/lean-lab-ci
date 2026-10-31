/-
Saouter 1998, P0018, unit U-0360, run 20261017T2003Z-30240. Saouter's step block by block:
even Goldbach to B = 10^8 and 201 checked ladder blocks, 100006 Lucas-certified primes from 3 to
9999906444119 with gaps at most B - 4, give ternary Goldbach to 10000006444119. Each block's primes are
checked in BlockK.lean and its chain in ChkK.lean, both Mathlib-free; here the facts are only
glued, so no list is unfolded. AI-written Lean code, Claude, 2026-10-17.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/
import LeanLab.Saouter1998.Lucas
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Chk1
import LeanLab.Saouter1998.Chk2
import LeanLab.Saouter1998.Chk3
import LeanLab.Saouter1998.Chk4
import LeanLab.Saouter1998.Chk5
import LeanLab.Saouter1998.Chk6
import LeanLab.Saouter1998.Chk7
import LeanLab.Saouter1998.Chk8
import LeanLab.Saouter1998.Chk9
import LeanLab.Saouter1998.Chk10
import LeanLab.Saouter1998.Chk11
import LeanLab.Saouter1998.Chk12
import LeanLab.Saouter1998.Chk13
import LeanLab.Saouter1998.Chk14
import LeanLab.Saouter1998.Chk15
import LeanLab.Saouter1998.Chk16
import LeanLab.Saouter1998.Chk17
import LeanLab.Saouter1998.Chk18
import LeanLab.Saouter1998.Chk19
import LeanLab.Saouter1998.Chk20
import LeanLab.Saouter1998.Chk21
import LeanLab.Saouter1998.Chk22
import LeanLab.Saouter1998.Chk23
import LeanLab.Saouter1998.Chk24
import LeanLab.Saouter1998.Chk25
import LeanLab.Saouter1998.Chk26
import LeanLab.Saouter1998.Chk27
import LeanLab.Saouter1998.Chk28
import LeanLab.Saouter1998.Chk29
import LeanLab.Saouter1998.Chk30
import LeanLab.Saouter1998.Chk31
import LeanLab.Saouter1998.Chk32
import LeanLab.Saouter1998.Chk33
import LeanLab.Saouter1998.Chk34
import LeanLab.Saouter1998.Chk35
import LeanLab.Saouter1998.Chk36
import LeanLab.Saouter1998.Chk37
import LeanLab.Saouter1998.Chk38
import LeanLab.Saouter1998.Chk39
import LeanLab.Saouter1998.Chk40
import LeanLab.Saouter1998.Chk41
import LeanLab.Saouter1998.Chk42
import LeanLab.Saouter1998.Chk43
import LeanLab.Saouter1998.Chk44
import LeanLab.Saouter1998.Chk45
import LeanLab.Saouter1998.Chk46
import LeanLab.Saouter1998.Chk47
import LeanLab.Saouter1998.Chk48
import LeanLab.Saouter1998.Chk49
import LeanLab.Saouter1998.Chk50
import LeanLab.Saouter1998.Chk51
import LeanLab.Saouter1998.Chk52
import LeanLab.Saouter1998.Chk53
import LeanLab.Saouter1998.Chk54
import LeanLab.Saouter1998.Chk55
import LeanLab.Saouter1998.Chk56
import LeanLab.Saouter1998.Chk57
import LeanLab.Saouter1998.Chk58
import LeanLab.Saouter1998.Chk59
import LeanLab.Saouter1998.Chk60
import LeanLab.Saouter1998.Chk61
import LeanLab.Saouter1998.Chk62
import LeanLab.Saouter1998.Chk63
import LeanLab.Saouter1998.Chk64
import LeanLab.Saouter1998.Chk65
import LeanLab.Saouter1998.Chk66
import LeanLab.Saouter1998.Chk67
import LeanLab.Saouter1998.Chk68
import LeanLab.Saouter1998.Chk69
import LeanLab.Saouter1998.Chk70
import LeanLab.Saouter1998.Chk71
import LeanLab.Saouter1998.Chk72
import LeanLab.Saouter1998.Chk73
import LeanLab.Saouter1998.Chk74
import LeanLab.Saouter1998.Chk75
import LeanLab.Saouter1998.Chk76
import LeanLab.Saouter1998.Chk77
import LeanLab.Saouter1998.Chk78
import LeanLab.Saouter1998.Chk79
import LeanLab.Saouter1998.Chk80
import LeanLab.Saouter1998.Chk81
import LeanLab.Saouter1998.Chk82
import LeanLab.Saouter1998.Chk83
import LeanLab.Saouter1998.Chk84
import LeanLab.Saouter1998.Chk85
import LeanLab.Saouter1998.Chk86
import LeanLab.Saouter1998.Chk87
import LeanLab.Saouter1998.Chk88
import LeanLab.Saouter1998.Chk89
import LeanLab.Saouter1998.Chk90
import LeanLab.Saouter1998.Chk91
import LeanLab.Saouter1998.Chk92
import LeanLab.Saouter1998.Chk93
import LeanLab.Saouter1998.Chk94
import LeanLab.Saouter1998.Chk95
import LeanLab.Saouter1998.Chk96
import LeanLab.Saouter1998.Chk97
import LeanLab.Saouter1998.Chk98
import LeanLab.Saouter1998.Chk99
import LeanLab.Saouter1998.Chk100
import LeanLab.Saouter1998.Chk101
import LeanLab.Saouter1998.Chk102
import LeanLab.Saouter1998.Chk103
import LeanLab.Saouter1998.Chk104
import LeanLab.Saouter1998.Chk105
import LeanLab.Saouter1998.Chk106
import LeanLab.Saouter1998.Chk107
import LeanLab.Saouter1998.Chk108
import LeanLab.Saouter1998.Chk109
import LeanLab.Saouter1998.Chk110
import LeanLab.Saouter1998.Chk111
import LeanLab.Saouter1998.Chk112
import LeanLab.Saouter1998.Chk113
import LeanLab.Saouter1998.Chk114
import LeanLab.Saouter1998.Chk115
import LeanLab.Saouter1998.Chk116
import LeanLab.Saouter1998.Chk117
import LeanLab.Saouter1998.Chk118
import LeanLab.Saouter1998.Chk119
import LeanLab.Saouter1998.Chk120
import LeanLab.Saouter1998.Chk121
import LeanLab.Saouter1998.Chk122
import LeanLab.Saouter1998.Chk123
import LeanLab.Saouter1998.Chk124
import LeanLab.Saouter1998.Chk125
import LeanLab.Saouter1998.Chk126
import LeanLab.Saouter1998.Chk127
import LeanLab.Saouter1998.Chk128
import LeanLab.Saouter1998.Chk129
import LeanLab.Saouter1998.Chk130
import LeanLab.Saouter1998.Chk131
import LeanLab.Saouter1998.Chk132
import LeanLab.Saouter1998.Chk133
import LeanLab.Saouter1998.Chk134
import LeanLab.Saouter1998.Chk135
import LeanLab.Saouter1998.Chk136
import LeanLab.Saouter1998.Chk137
import LeanLab.Saouter1998.Chk138
import LeanLab.Saouter1998.Chk139
import LeanLab.Saouter1998.Chk140
import LeanLab.Saouter1998.Chk141
import LeanLab.Saouter1998.Chk142
import LeanLab.Saouter1998.Chk143
import LeanLab.Saouter1998.Chk144
import LeanLab.Saouter1998.Chk145
import LeanLab.Saouter1998.Chk146
import LeanLab.Saouter1998.Chk147
import LeanLab.Saouter1998.Chk148
import LeanLab.Saouter1998.Chk149
import LeanLab.Saouter1998.Chk150
import LeanLab.Saouter1998.Chk151
import LeanLab.Saouter1998.Chk152
import LeanLab.Saouter1998.Chk153
import LeanLab.Saouter1998.Chk154
import LeanLab.Saouter1998.Chk155
import LeanLab.Saouter1998.Chk156
import LeanLab.Saouter1998.Chk157
import LeanLab.Saouter1998.Chk158
import LeanLab.Saouter1998.Chk159
import LeanLab.Saouter1998.Chk160
import LeanLab.Saouter1998.Chk161
import LeanLab.Saouter1998.Chk162
import LeanLab.Saouter1998.Chk163
import LeanLab.Saouter1998.Chk164
import LeanLab.Saouter1998.Chk165
import LeanLab.Saouter1998.Chk166
import LeanLab.Saouter1998.Chk167
import LeanLab.Saouter1998.Chk168
import LeanLab.Saouter1998.Chk169
import LeanLab.Saouter1998.Chk170
import LeanLab.Saouter1998.Chk171
import LeanLab.Saouter1998.Chk172
import LeanLab.Saouter1998.Chk173
import LeanLab.Saouter1998.Chk174
import LeanLab.Saouter1998.Chk175
import LeanLab.Saouter1998.Chk176
import LeanLab.Saouter1998.Chk177
import LeanLab.Saouter1998.Chk178
import LeanLab.Saouter1998.Chk179
import LeanLab.Saouter1998.Chk180
import LeanLab.Saouter1998.Chk181
import LeanLab.Saouter1998.Chk182
import LeanLab.Saouter1998.Chk183
import LeanLab.Saouter1998.Chk184
import LeanLab.Saouter1998.Chk185
import LeanLab.Saouter1998.Chk186
import LeanLab.Saouter1998.Chk187
import LeanLab.Saouter1998.Chk188
import LeanLab.Saouter1998.Chk189
import LeanLab.Saouter1998.Chk190
import LeanLab.Saouter1998.Chk191
import LeanLab.Saouter1998.Chk192
import LeanLab.Saouter1998.Chk193
import LeanLab.Saouter1998.Chk194
import LeanLab.Saouter1998.Chk195
import LeanLab.Saouter1998.Chk196
import LeanLab.Saouter1998.Chk197
import LeanLab.Saouter1998.Chk198
import LeanLab.Saouter1998.Chk199
import LeanLab.Saouter1998.Chk200
import LeanLab.Saouter1998.Chk201

namespace LeanLab.Saouter1998

open LeanLab.HelfgottPlatt

theorem chainC_sound (B : ℕ) : ∀ (l : List ℕ) (a : ℕ), Core.chainC B a l = true →
    (a :: l).IsChain (LadderStep B)
  | [], a, _ => List.IsChain.singleton a
  | b :: t, a, h => by
    simp only [Core.chainC, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.IsChain.cons_cons ⟨h.1.1, h.1.2⟩ (chainC_sound B t b h.2)

/-- One block of Saouter's ladder extends the ternary range from `a + B` to `last + B`. -/
theorem step {B a last : ℕ} {C : List Core.Cert} (hB : EvenGoldbachUpTo B) (h4 : 4 ≤ B)
    (hT : TernaryGoldbachUpTo (a + B)) (ha : a.Prime) (ha3 : 3 ≤ a)
    (hc : C.all Core.certB = true) (hk : Core.chk B a last C = true) :
    TernaryGoldbachUpTo (last + B) ∧ last.Prime ∧ 3 ≤ last := by
  simp only [Core.chk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
  obtain ⟨⟨hch, hlast⟩, hal⟩ := hk
  have hpr := all_prime_of_certs hc
  have hmem : last ∈ C.map Prod.fst := List.mem_of_getLast? hlast
  have hD : (C.map Prod.fst).getLastD a = last := by
    rw [List.getLastD_eq_getLast?, hlast]; rfl
  refine ⟨?_, hpr last hmem, by omega⟩
  intro n hn h7 hnX
  by_cases hs : n ≤ a + B
  · exact hT n hn h7 hs
  · exact ternary_of_ladder_aux hB (C.map Prod.fst) a ha ha3 hpr (chainC_sound B _ a hch) n hn
      (by omega) (by rw [hD]; exact hnX)

/-- The bottom rung: the prime 3 alone covers odd n up to 3 + B. -/
theorem base {B : ℕ} (hB : EvenGoldbachUpTo B) : TernaryGoldbachUpTo (3 + B) :=
  ternary_of_ladder hB [] (by simp) (List.IsChain.singleton 3) le_rfl

theorem s1 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (49999525831 + 100000000) ∧ Nat.Prime 49999525831 ∧ 3 ≤ 49999525831 :=
  step hB (by norm_num) (base hB) Nat.prime_three le_rfl Core.c1 Core.k1

theorem s2 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (99998778769 + 100000000) ∧ Nat.Prime 99998778769 ∧ 3 ≤ 99998778769 :=
  step hB (by norm_num) (s1 hB).1 (s1 hB).2.1 (s1 hB).2.2 Core.c2 Core.k2

theorem s3 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (149997895169 + 100000000) ∧ Nat.Prime 149997895169 ∧ 3 ≤ 149997895169 :=
  step hB (by norm_num) (s2 hB).1 (s2 hB).2.1 (s2 hB).2.2 Core.c3 Core.k3

theorem s4 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (199996939057 + 100000000) ∧ Nat.Prime 199996939057 ∧ 3 ≤ 199996939057 :=
  step hB (by norm_num) (s3 hB).1 (s3 hB).2.1 (s3 hB).2.2 Core.c4 Core.k4

theorem s5 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (249995872513 + 100000000) ∧ Nat.Prime 249995872513 ∧ 3 ≤ 249995872513 :=
  step hB (by norm_num) (s4 hB).1 (s4 hB).2.1 (s4 hB).2.2 Core.c5 Core.k5

theorem s6 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (299994659353 + 100000000) ∧ Nat.Prime 299994659353 ∧ 3 ≤ 299994659353 :=
  step hB (by norm_num) (s5 hB).1 (s5 hB).2.1 (s5 hB).2.2 Core.c6 Core.k6

theorem s7 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (349993422133 + 100000000) ∧ Nat.Prime 349993422133 ∧ 3 ≤ 349993422133 :=
  step hB (by norm_num) (s6 hB).1 (s6 hB).2.1 (s6 hB).2.2 Core.c7 Core.k7

theorem s8 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (399992045329 + 100000000) ∧ Nat.Prime 399992045329 ∧ 3 ≤ 399992045329 :=
  step hB (by norm_num) (s7 hB).1 (s7 hB).2.1 (s7 hB).2.2 Core.c8 Core.k8

theorem s9 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (449990672977 + 100000000) ∧ Nat.Prime 449990672977 ∧ 3 ≤ 449990672977 :=
  step hB (by norm_num) (s8 hB).1 (s8 hB).2.1 (s8 hB).2.2 Core.c9 Core.k9

theorem s10 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (499989290813 + 100000000) ∧ Nat.Prime 499989290813 ∧ 3 ≤ 499989290813 :=
  step hB (by norm_num) (s9 hB).1 (s9 hB).2.1 (s9 hB).2.2 Core.c10 Core.k10

theorem s11 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (549987712639 + 100000000) ∧ Nat.Prime 549987712639 ∧ 3 ≤ 549987712639 :=
  step hB (by norm_num) (s10 hB).1 (s10 hB).2.1 (s10 hB).2.2 Core.c11 Core.k11

theorem s12 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (599986137631 + 100000000) ∧ Nat.Prime 599986137631 ∧ 3 ≤ 599986137631 :=
  step hB (by norm_num) (s11 hB).1 (s11 hB).2.1 (s11 hB).2.2 Core.c12 Core.k12

theorem s13 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (649984398383 + 100000000) ∧ Nat.Prime 649984398383 ∧ 3 ≤ 649984398383 :=
  step hB (by norm_num) (s12 hB).1 (s12 hB).2.1 (s12 hB).2.2 Core.c13 Core.k13

theorem s14 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (699982754857 + 100000000) ∧ Nat.Prime 699982754857 ∧ 3 ≤ 699982754857 :=
  step hB (by norm_num) (s13 hB).1 (s13 hB).2.1 (s13 hB).2.2 Core.c14 Core.k14

theorem s15 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (749980954001 + 100000000) ∧ Nat.Prime 749980954001 ∧ 3 ≤ 749980954001 :=
  step hB (by norm_num) (s14 hB).1 (s14 hB).2.1 (s14 hB).2.2 Core.c15 Core.k15

theorem s16 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (799979091781 + 100000000) ∧ Nat.Prime 799979091781 ∧ 3 ≤ 799979091781 :=
  step hB (by norm_num) (s15 hB).1 (s15 hB).2.1 (s15 hB).2.2 Core.c16 Core.k16

theorem s17 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (849977158627 + 100000000) ∧ Nat.Prime 849977158627 ∧ 3 ≤ 849977158627 :=
  step hB (by norm_num) (s16 hB).1 (s16 hB).2.1 (s16 hB).2.2 Core.c17 Core.k17

theorem s18 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (899975181943 + 100000000) ∧ Nat.Prime 899975181943 ∧ 3 ≤ 899975181943 :=
  step hB (by norm_num) (s17 hB).1 (s17 hB).2.1 (s17 hB).2.2 Core.c18 Core.k18

theorem s19 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (949973295251 + 100000000) ∧ Nat.Prime 949973295251 ∧ 3 ≤ 949973295251 :=
  step hB (by norm_num) (s18 hB).1 (s18 hB).2.1 (s18 hB).2.2 Core.c19 Core.k19

theorem s20 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (999971466257 + 100000000) ∧ Nat.Prime 999971466257 ∧ 3 ≤ 999971466257 :=
  step hB (by norm_num) (s19 hB).1 (s19 hB).2.1 (s19 hB).2.2 Core.c20 Core.k20

theorem s21 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1049969417473 + 100000000) ∧ Nat.Prime 1049969417473 ∧ 3 ≤ 1049969417473 :=
  step hB (by norm_num) (s20 hB).1 (s20 hB).2.1 (s20 hB).2.2 Core.c21 Core.k21

theorem s22 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1099967335507 + 100000000) ∧ Nat.Prime 1099967335507 ∧ 3 ≤ 1099967335507 :=
  step hB (by norm_num) (s21 hB).1 (s21 hB).2.1 (s21 hB).2.2 Core.c22 Core.k22

theorem s23 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1149965521697 + 100000000) ∧ Nat.Prime 1149965521697 ∧ 3 ≤ 1149965521697 :=
  step hB (by norm_num) (s22 hB).1 (s22 hB).2.1 (s22 hB).2.2 Core.c23 Core.k23

theorem s24 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1199963535553 + 100000000) ∧ Nat.Prime 1199963535553 ∧ 3 ≤ 1199963535553 :=
  step hB (by norm_num) (s23 hB).1 (s23 hB).2.1 (s23 hB).2.2 Core.c24 Core.k24

theorem s25 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1249961413537 + 100000000) ∧ Nat.Prime 1249961413537 ∧ 3 ≤ 1249961413537 :=
  step hB (by norm_num) (s24 hB).1 (s24 hB).2.1 (s24 hB).2.2 Core.c25 Core.k25

theorem s26 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1299959333801 + 100000000) ∧ Nat.Prime 1299959333801 ∧ 3 ≤ 1299959333801 :=
  step hB (by norm_num) (s25 hB).1 (s25 hB).2.1 (s25 hB).2.2 Core.c26 Core.k26

theorem s27 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1349957002109 + 100000000) ∧ Nat.Prime 1349957002109 ∧ 3 ≤ 1349957002109 :=
  step hB (by norm_num) (s26 hB).1 (s26 hB).2.1 (s26 hB).2.2 Core.c27 Core.k27

theorem s28 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1399954676563 + 100000000) ∧ Nat.Prime 1399954676563 ∧ 3 ≤ 1399954676563 :=
  step hB (by norm_num) (s27 hB).1 (s27 hB).2.1 (s27 hB).2.2 Core.c28 Core.k28

theorem s29 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1449952484609 + 100000000) ∧ Nat.Prime 1449952484609 ∧ 3 ≤ 1449952484609 :=
  step hB (by norm_num) (s28 hB).1 (s28 hB).2.1 (s28 hB).2.2 Core.c29 Core.k29

theorem s30 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1499950056767 + 100000000) ∧ Nat.Prime 1499950056767 ∧ 3 ≤ 1499950056767 :=
  step hB (by norm_num) (s29 hB).1 (s29 hB).2.1 (s29 hB).2.2 Core.c30 Core.k30

theorem s31 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1549947804929 + 100000000) ∧ Nat.Prime 1549947804929 ∧ 3 ≤ 1549947804929 :=
  step hB (by norm_num) (s30 hB).1 (s30 hB).2.1 (s30 hB).2.2 Core.c31 Core.k31

theorem s32 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1599945566147 + 100000000) ∧ Nat.Prime 1599945566147 ∧ 3 ≤ 1599945566147 :=
  step hB (by norm_num) (s31 hB).1 (s31 hB).2.1 (s31 hB).2.2 Core.c32 Core.k32

theorem s33 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1649943270509 + 100000000) ∧ Nat.Prime 1649943270509 ∧ 3 ≤ 1649943270509 :=
  step hB (by norm_num) (s32 hB).1 (s32 hB).2.1 (s32 hB).2.2 Core.c33 Core.k33

theorem s34 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1699940825857 + 100000000) ∧ Nat.Prime 1699940825857 ∧ 3 ≤ 1699940825857 :=
  step hB (by norm_num) (s33 hB).1 (s33 hB).2.1 (s33 hB).2.2 Core.c34 Core.k34

theorem s35 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1749938551723 + 100000000) ∧ Nat.Prime 1749938551723 ∧ 3 ≤ 1749938551723 :=
  step hB (by norm_num) (s34 hB).1 (s34 hB).2.1 (s34 hB).2.2 Core.c35 Core.k35

theorem s36 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1799936287909 + 100000000) ∧ Nat.Prime 1799936287909 ∧ 3 ≤ 1799936287909 :=
  step hB (by norm_num) (s35 hB).1 (s35 hB).2.1 (s35 hB).2.2 Core.c36 Core.k36

theorem s37 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1849933636601 + 100000000) ∧ Nat.Prime 1849933636601 ∧ 3 ≤ 1849933636601 :=
  step hB (by norm_num) (s36 hB).1 (s36 hB).2.1 (s36 hB).2.2 Core.c37 Core.k37

theorem s38 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1899931095523 + 100000000) ∧ Nat.Prime 1899931095523 ∧ 3 ≤ 1899931095523 :=
  step hB (by norm_num) (s37 hB).1 (s37 hB).2.1 (s37 hB).2.2 Core.c38 Core.k38

theorem s39 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1949928566321 + 100000000) ∧ Nat.Prime 1949928566321 ∧ 3 ≤ 1949928566321 :=
  step hB (by norm_num) (s38 hB).1 (s38 hB).2.1 (s38 hB).2.2 Core.c39 Core.k39

theorem s40 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (1999926001217 + 100000000) ∧ Nat.Prime 1999926001217 ∧ 3 ≤ 1999926001217 :=
  step hB (by norm_num) (s39 hB).1 (s39 hB).2.1 (s39 hB).2.2 Core.c40 Core.k40

theorem s41 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2049923415901 + 100000000) ∧ Nat.Prime 2049923415901 ∧ 3 ≤ 2049923415901 :=
  step hB (by norm_num) (s40 hB).1 (s40 hB).2.1 (s40 hB).2.2 Core.c41 Core.k41

theorem s42 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2099920830841 + 100000000) ∧ Nat.Prime 2099920830841 ∧ 3 ≤ 2099920830841 :=
  step hB (by norm_num) (s41 hB).1 (s41 hB).2.1 (s41 hB).2.2 Core.c42 Core.k42

theorem s43 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2149918238821 + 100000000) ∧ Nat.Prime 2149918238821 ∧ 3 ≤ 2149918238821 :=
  step hB (by norm_num) (s42 hB).1 (s42 hB).2.1 (s42 hB).2.2 Core.c43 Core.k43

theorem s44 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2199915524831 + 100000000) ∧ Nat.Prime 2199915524831 ∧ 3 ≤ 2199915524831 :=
  step hB (by norm_num) (s43 hB).1 (s43 hB).2.1 (s43 hB).2.2 Core.c44 Core.k44

theorem s45 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2249912815697 + 100000000) ∧ Nat.Prime 2249912815697 ∧ 3 ≤ 2249912815697 :=
  step hB (by norm_num) (s44 hB).1 (s44 hB).2.1 (s44 hB).2.2 Core.c45 Core.k45

theorem s46 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2299910084839 + 100000000) ∧ Nat.Prime 2299910084839 ∧ 3 ≤ 2299910084839 :=
  step hB (by norm_num) (s45 hB).1 (s45 hB).2.1 (s45 hB).2.2 Core.c46 Core.k46

theorem s47 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2349907452511 + 100000000) ∧ Nat.Prime 2349907452511 ∧ 3 ≤ 2349907452511 :=
  step hB (by norm_num) (s46 hB).1 (s46 hB).2.1 (s46 hB).2.2 Core.c47 Core.k47

theorem s48 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2399904695431 + 100000000) ∧ Nat.Prime 2399904695431 ∧ 3 ≤ 2399904695431 :=
  step hB (by norm_num) (s47 hB).1 (s47 hB).2.1 (s47 hB).2.2 Core.c48 Core.k48

theorem s49 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2449901772151 + 100000000) ∧ Nat.Prime 2449901772151 ∧ 3 ≤ 2449901772151 :=
  step hB (by norm_num) (s48 hB).1 (s48 hB).2.1 (s48 hB).2.2 Core.c49 Core.k49

theorem s50 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2499899066761 + 100000000) ∧ Nat.Prime 2499899066761 ∧ 3 ≤ 2499899066761 :=
  step hB (by norm_num) (s49 hB).1 (s49 hB).2.1 (s49 hB).2.2 Core.c50 Core.k50

theorem s51 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2549896240841 + 100000000) ∧ Nat.Prime 2549896240841 ∧ 3 ≤ 2549896240841 :=
  step hB (by norm_num) (s50 hB).1 (s50 hB).2.1 (s50 hB).2.2 Core.c51 Core.k51

theorem s52 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2599893440609 + 100000000) ∧ Nat.Prime 2599893440609 ∧ 3 ≤ 2599893440609 :=
  step hB (by norm_num) (s51 hB).1 (s51 hB).2.1 (s51 hB).2.2 Core.c52 Core.k52

theorem s53 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2649890566357 + 100000000) ∧ Nat.Prime 2649890566357 ∧ 3 ≤ 2649890566357 :=
  step hB (by norm_num) (s52 hB).1 (s52 hB).2.1 (s52 hB).2.2 Core.c53 Core.k53

theorem s54 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2699887316641 + 100000000) ∧ Nat.Prime 2699887316641 ∧ 3 ≤ 2699887316641 :=
  step hB (by norm_num) (s53 hB).1 (s53 hB).2.1 (s53 hB).2.2 Core.c54 Core.k54

theorem s55 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2749884144961 + 100000000) ∧ Nat.Prime 2749884144961 ∧ 3 ≤ 2749884144961 :=
  step hB (by norm_num) (s54 hB).1 (s54 hB).2.1 (s54 hB).2.2 Core.c55 Core.k55

theorem s56 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2799881248583 + 100000000) ∧ Nat.Prime 2799881248583 ∧ 3 ≤ 2799881248583 :=
  step hB (by norm_num) (s55 hB).1 (s55 hB).2.1 (s55 hB).2.2 Core.c56 Core.k56

theorem s57 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2849878348381 + 100000000) ∧ Nat.Prime 2849878348381 ∧ 3 ≤ 2849878348381 :=
  step hB (by norm_num) (s56 hB).1 (s56 hB).2.1 (s56 hB).2.2 Core.c57 Core.k57

theorem s58 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2899875397633 + 100000000) ∧ Nat.Prime 2899875397633 ∧ 3 ≤ 2899875397633 :=
  step hB (by norm_num) (s57 hB).1 (s57 hB).2.1 (s57 hB).2.2 Core.c58 Core.k58

theorem s59 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2949872463871 + 100000000) ∧ Nat.Prime 2949872463871 ∧ 3 ≤ 2949872463871 :=
  step hB (by norm_num) (s58 hB).1 (s58 hB).2.1 (s58 hB).2.2 Core.c59 Core.k59

theorem s60 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (2999869589987 + 100000000) ∧ Nat.Prime 2999869589987 ∧ 3 ≤ 2999869589987 :=
  step hB (by norm_num) (s59 hB).1 (s59 hB).2.1 (s59 hB).2.2 Core.c60 Core.k60

theorem s61 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3049866869677 + 100000000) ∧ Nat.Prime 3049866869677 ∧ 3 ≤ 3049866869677 :=
  step hB (by norm_num) (s60 hB).1 (s60 hB).2.1 (s60 hB).2.2 Core.c61 Core.k61

theorem s62 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3099863790217 + 100000000) ∧ Nat.Prime 3099863790217 ∧ 3 ≤ 3099863790217 :=
  step hB (by norm_num) (s61 hB).1 (s61 hB).2.1 (s61 hB).2.2 Core.c62 Core.k62

theorem s63 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3149860852547 + 100000000) ∧ Nat.Prime 3149860852547 ∧ 3 ≤ 3149860852547 :=
  step hB (by norm_num) (s62 hB).1 (s62 hB).2.1 (s62 hB).2.2 Core.c63 Core.k63

theorem s64 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3199857798301 + 100000000) ∧ Nat.Prime 3199857798301 ∧ 3 ≤ 3199857798301 :=
  step hB (by norm_num) (s63 hB).1 (s63 hB).2.1 (s63 hB).2.2 Core.c64 Core.k64

theorem s65 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3249854691301 + 100000000) ∧ Nat.Prime 3249854691301 ∧ 3 ≤ 3249854691301 :=
  step hB (by norm_num) (s64 hB).1 (s64 hB).2.1 (s64 hB).2.2 Core.c65 Core.k65

theorem s66 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3299851646849 + 100000000) ∧ Nat.Prime 3299851646849 ∧ 3 ≤ 3299851646849 :=
  step hB (by norm_num) (s65 hB).1 (s65 hB).2.1 (s65 hB).2.2 Core.c66 Core.k66

theorem s67 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3349848360931 + 100000000) ∧ Nat.Prime 3349848360931 ∧ 3 ≤ 3349848360931 :=
  step hB (by norm_num) (s66 hB).1 (s66 hB).2.1 (s66 hB).2.2 Core.c67 Core.k67

theorem s68 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3399845328401 + 100000000) ∧ Nat.Prime 3399845328401 ∧ 3 ≤ 3399845328401 :=
  step hB (by norm_num) (s67 hB).1 (s67 hB).2.1 (s67 hB).2.2 Core.c68 Core.k68

theorem s69 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3449841996439 + 100000000) ∧ Nat.Prime 3449841996439 ∧ 3 ≤ 3449841996439 :=
  step hB (by norm_num) (s68 hB).1 (s68 hB).2.1 (s68 hB).2.2 Core.c69 Core.k69

theorem s70 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3499838585627 + 100000000) ∧ Nat.Prime 3499838585627 ∧ 3 ≤ 3499838585627 :=
  step hB (by norm_num) (s69 hB).1 (s69 hB).2.1 (s69 hB).2.2 Core.c70 Core.k70

theorem s71 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3549835637389 + 100000000) ∧ Nat.Prime 3549835637389 ∧ 3 ≤ 3549835637389 :=
  step hB (by norm_num) (s70 hB).1 (s70 hB).2.1 (s70 hB).2.2 Core.c71 Core.k71

theorem s72 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3599832375847 + 100000000) ∧ Nat.Prime 3599832375847 ∧ 3 ≤ 3599832375847 :=
  step hB (by norm_num) (s71 hB).1 (s71 hB).2.1 (s71 hB).2.2 Core.c72 Core.k72

theorem s73 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3649829335489 + 100000000) ∧ Nat.Prime 3649829335489 ∧ 3 ≤ 3649829335489 :=
  step hB (by norm_num) (s72 hB).1 (s72 hB).2.1 (s72 hB).2.2 Core.c73 Core.k73

theorem s74 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3699826023991 + 100000000) ∧ Nat.Prime 3699826023991 ∧ 3 ≤ 3699826023991 :=
  step hB (by norm_num) (s73 hB).1 (s73 hB).2.1 (s73 hB).2.2 Core.c74 Core.k74

theorem s75 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3749822863931 + 100000000) ∧ Nat.Prime 3749822863931 ∧ 3 ≤ 3749822863931 :=
  step hB (by norm_num) (s74 hB).1 (s74 hB).2.1 (s74 hB).2.2 Core.c75 Core.k75

theorem s76 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3799819620367 + 100000000) ∧ Nat.Prime 3799819620367 ∧ 3 ≤ 3799819620367 :=
  step hB (by norm_num) (s75 hB).1 (s75 hB).2.1 (s75 hB).2.2 Core.c76 Core.k76

theorem s77 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3849816328381 + 100000000) ∧ Nat.Prime 3849816328381 ∧ 3 ≤ 3849816328381 :=
  step hB (by norm_num) (s76 hB).1 (s76 hB).2.1 (s76 hB).2.2 Core.c77 Core.k77

theorem s78 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3899813177089 + 100000000) ∧ Nat.Prime 3899813177089 ∧ 3 ≤ 3899813177089 :=
  step hB (by norm_num) (s77 hB).1 (s77 hB).2.1 (s77 hB).2.2 Core.c78 Core.k78

theorem s79 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3949810009081 + 100000000) ∧ Nat.Prime 3949810009081 ∧ 3 ≤ 3949810009081 :=
  step hB (by norm_num) (s78 hB).1 (s78 hB).2.1 (s78 hB).2.2 Core.c79 Core.k79

theorem s80 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (3999806674931 + 100000000) ∧ Nat.Prime 3999806674931 ∧ 3 ≤ 3999806674931 :=
  step hB (by norm_num) (s79 hB).1 (s79 hB).2.1 (s79 hB).2.2 Core.c80 Core.k80

theorem s81 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4049803237481 + 100000000) ∧ Nat.Prime 4049803237481 ∧ 3 ≤ 4049803237481 :=
  step hB (by norm_num) (s80 hB).1 (s80 hB).2.1 (s80 hB).2.2 Core.c81 Core.k81

theorem s82 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4099799759401 + 100000000) ∧ Nat.Prime 4099799759401 ∧ 3 ≤ 4099799759401 :=
  step hB (by norm_num) (s81 hB).1 (s81 hB).2.1 (s81 hB).2.2 Core.c82 Core.k82

theorem s83 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4149796264837 + 100000000) ∧ Nat.Prime 4149796264837 ∧ 3 ≤ 4149796264837 :=
  step hB (by norm_num) (s82 hB).1 (s82 hB).2.1 (s82 hB).2.2 Core.c83 Core.k83

theorem s84 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4199792840029 + 100000000) ∧ Nat.Prime 4199792840029 ∧ 3 ≤ 4199792840029 :=
  step hB (by norm_num) (s83 hB).1 (s83 hB).2.1 (s83 hB).2.2 Core.c84 Core.k84

theorem s85 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4249789512751 + 100000000) ∧ Nat.Prime 4249789512751 ∧ 3 ≤ 4249789512751 :=
  step hB (by norm_num) (s84 hB).1 (s84 hB).2.1 (s84 hB).2.2 Core.c85 Core.k85

theorem s86 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4299785825821 + 100000000) ∧ Nat.Prime 4299785825821 ∧ 3 ≤ 4299785825821 :=
  step hB (by norm_num) (s85 hB).1 (s85 hB).2.1 (s85 hB).2.2 Core.c86 Core.k86

theorem s87 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4349782240759 + 100000000) ∧ Nat.Prime 4349782240759 ∧ 3 ≤ 4349782240759 :=
  step hB (by norm_num) (s86 hB).1 (s86 hB).2.1 (s86 hB).2.2 Core.c87 Core.k87

theorem s88 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4399778861057 + 100000000) ∧ Nat.Prime 4399778861057 ∧ 3 ≤ 4399778861057 :=
  step hB (by norm_num) (s87 hB).1 (s87 hB).2.1 (s87 hB).2.2 Core.c88 Core.k88

theorem s89 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4449775250051 + 100000000) ∧ Nat.Prime 4449775250051 ∧ 3 ≤ 4449775250051 :=
  step hB (by norm_num) (s88 hB).1 (s88 hB).2.1 (s88 hB).2.2 Core.c89 Core.k89

theorem s90 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4499771725357 + 100000000) ∧ Nat.Prime 4499771725357 ∧ 3 ≤ 4499771725357 :=
  step hB (by norm_num) (s89 hB).1 (s89 hB).2.1 (s89 hB).2.2 Core.c90 Core.k90

theorem s91 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4549767995917 + 100000000) ∧ Nat.Prime 4549767995917 ∧ 3 ≤ 4549767995917 :=
  step hB (by norm_num) (s90 hB).1 (s90 hB).2.1 (s90 hB).2.2 Core.c91 Core.k91

theorem s92 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4599764705953 + 100000000) ∧ Nat.Prime 4599764705953 ∧ 3 ≤ 4599764705953 :=
  step hB (by norm_num) (s91 hB).1 (s91 hB).2.1 (s91 hB).2.2 Core.c92 Core.k92

theorem s93 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4649761119739 + 100000000) ∧ Nat.Prime 4649761119739 ∧ 3 ≤ 4649761119739 :=
  step hB (by norm_num) (s92 hB).1 (s92 hB).2.1 (s92 hB).2.2 Core.c93 Core.k93

theorem s94 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4699757548361 + 100000000) ∧ Nat.Prime 4699757548361 ∧ 3 ≤ 4699757548361 :=
  step hB (by norm_num) (s93 hB).1 (s93 hB).2.1 (s93 hB).2.2 Core.c94 Core.k94

theorem s95 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4749753856051 + 100000000) ∧ Nat.Prime 4749753856051 ∧ 3 ≤ 4749753856051 :=
  step hB (by norm_num) (s94 hB).1 (s94 hB).2.1 (s94 hB).2.2 Core.c95 Core.k95

theorem s96 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4799750121589 + 100000000) ∧ Nat.Prime 4799750121589 ∧ 3 ≤ 4799750121589 :=
  step hB (by norm_num) (s95 hB).1 (s95 hB).2.1 (s95 hB).2.2 Core.c96 Core.k96

theorem s97 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4849746276343 + 100000000) ∧ Nat.Prime 4849746276343 ∧ 3 ≤ 4849746276343 :=
  step hB (by norm_num) (s96 hB).1 (s96 hB).2.1 (s96 hB).2.2 Core.c97 Core.k97

theorem s98 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4899742671211 + 100000000) ∧ Nat.Prime 4899742671211 ∧ 3 ≤ 4899742671211 :=
  step hB (by norm_num) (s97 hB).1 (s97 hB).2.1 (s97 hB).2.2 Core.c98 Core.k98

theorem s99 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4949739087287 + 100000000) ∧ Nat.Prime 4949739087287 ∧ 3 ≤ 4949739087287 :=
  step hB (by norm_num) (s98 hB).1 (s98 hB).2.1 (s98 hB).2.2 Core.c99 Core.k99

theorem s100 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (4999735789313 + 100000000) ∧ Nat.Prime 4999735789313 ∧ 3 ≤ 4999735789313 :=
  step hB (by norm_num) (s99 hB).1 (s99 hB).2.1 (s99 hB).2.2 Core.c100 Core.k100

theorem s101 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5049731849471 + 100000000) ∧ Nat.Prime 5049731849471 ∧ 3 ≤ 5049731849471 :=
  step hB (by norm_num) (s100 hB).1 (s100 hB).2.1 (s100 hB).2.2 Core.c101 Core.k101

theorem s102 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5099728205881 + 100000000) ∧ Nat.Prime 5099728205881 ∧ 3 ≤ 5099728205881 :=
  step hB (by norm_num) (s101 hB).1 (s101 hB).2.1 (s101 hB).2.2 Core.c102 Core.k102

theorem s103 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5149724194273 + 100000000) ∧ Nat.Prime 5149724194273 ∧ 3 ≤ 5149724194273 :=
  step hB (by norm_num) (s102 hB).1 (s102 hB).2.1 (s102 hB).2.2 Core.c103 Core.k103

theorem s104 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5199720709597 + 100000000) ∧ Nat.Prime 5199720709597 ∧ 3 ≤ 5199720709597 :=
  step hB (by norm_num) (s103 hB).1 (s103 hB).2.1 (s103 hB).2.2 Core.c104 Core.k104

theorem s105 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5249717105257 + 100000000) ∧ Nat.Prime 5249717105257 ∧ 3 ≤ 5249717105257 :=
  step hB (by norm_num) (s104 hB).1 (s104 hB).2.1 (s104 hB).2.2 Core.c105 Core.k105

theorem s106 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5299713408761 + 100000000) ∧ Nat.Prime 5299713408761 ∧ 3 ≤ 5299713408761 :=
  step hB (by norm_num) (s105 hB).1 (s105 hB).2.1 (s105 hB).2.2 Core.c106 Core.k106

theorem s107 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5349709722911 + 100000000) ∧ Nat.Prime 5349709722911 ∧ 3 ≤ 5349709722911 :=
  step hB (by norm_num) (s106 hB).1 (s106 hB).2.1 (s106 hB).2.2 Core.c107 Core.k107

theorem s108 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5399705721169 + 100000000) ∧ Nat.Prime 5399705721169 ∧ 3 ≤ 5399705721169 :=
  step hB (by norm_num) (s107 hB).1 (s107 hB).2.1 (s107 hB).2.2 Core.c108 Core.k108

theorem s109 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5449702119049 + 100000000) ∧ Nat.Prime 5449702119049 ∧ 3 ≤ 5449702119049 :=
  step hB (by norm_num) (s108 hB).1 (s108 hB).2.1 (s108 hB).2.2 Core.c109 Core.k109

theorem s110 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5499698246659 + 100000000) ∧ Nat.Prime 5499698246659 ∧ 3 ≤ 5499698246659 :=
  step hB (by norm_num) (s109 hB).1 (s109 hB).2.1 (s109 hB).2.2 Core.c110 Core.k110

theorem s111 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5549694424751 + 100000000) ∧ Nat.Prime 5549694424751 ∧ 3 ≤ 5549694424751 :=
  step hB (by norm_num) (s110 hB).1 (s110 hB).2.1 (s110 hB).2.2 Core.c111 Core.k111

theorem s112 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5599690524877 + 100000000) ∧ Nat.Prime 5599690524877 ∧ 3 ≤ 5599690524877 :=
  step hB (by norm_num) (s111 hB).1 (s111 hB).2.1 (s111 hB).2.2 Core.c112 Core.k112

theorem s113 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5649686847127 + 100000000) ∧ Nat.Prime 5649686847127 ∧ 3 ≤ 5649686847127 :=
  step hB (by norm_num) (s112 hB).1 (s112 hB).2.1 (s112 hB).2.2 Core.c113 Core.k113

theorem s114 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5699683190419 + 100000000) ∧ Nat.Prime 5699683190419 ∧ 3 ≤ 5699683190419 :=
  step hB (by norm_num) (s113 hB).1 (s113 hB).2.1 (s113 hB).2.2 Core.c114 Core.k114

theorem s115 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5749679239103 + 100000000) ∧ Nat.Prime 5749679239103 ∧ 3 ≤ 5749679239103 :=
  step hB (by norm_num) (s114 hB).1 (s114 hB).2.1 (s114 hB).2.2 Core.c115 Core.k115

theorem s116 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5799675235951 + 100000000) ∧ Nat.Prime 5799675235951 ∧ 3 ≤ 5799675235951 :=
  step hB (by norm_num) (s115 hB).1 (s115 hB).2.1 (s115 hB).2.2 Core.c116 Core.k116

theorem s117 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5849671223761 + 100000000) ∧ Nat.Prime 5849671223761 ∧ 3 ≤ 5849671223761 :=
  step hB (by norm_num) (s116 hB).1 (s116 hB).2.1 (s116 hB).2.2 Core.c117 Core.k117

theorem s118 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5899667449201 + 100000000) ∧ Nat.Prime 5899667449201 ∧ 3 ≤ 5899667449201 :=
  step hB (by norm_num) (s117 hB).1 (s117 hB).2.1 (s117 hB).2.2 Core.c118 Core.k118

theorem s119 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5949663404257 + 100000000) ∧ Nat.Prime 5949663404257 ∧ 3 ≤ 5949663404257 :=
  step hB (by norm_num) (s118 hB).1 (s118 hB).2.1 (s118 hB).2.2 Core.c119 Core.k119

theorem s120 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (5999659252291 + 100000000) ∧ Nat.Prime 5999659252291 ∧ 3 ≤ 5999659252291 :=
  step hB (by norm_num) (s119 hB).1 (s119 hB).2.1 (s119 hB).2.2 Core.c120 Core.k120

theorem s121 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6049655348353 + 100000000) ∧ Nat.Prime 6049655348353 ∧ 3 ≤ 6049655348353 :=
  step hB (by norm_num) (s120 hB).1 (s120 hB).2.1 (s120 hB).2.2 Core.c121 Core.k121

theorem s122 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6099651520201 + 100000000) ∧ Nat.Prime 6099651520201 ∧ 3 ≤ 6099651520201 :=
  step hB (by norm_num) (s121 hB).1 (s121 hB).2.1 (s121 hB).2.2 Core.c122 Core.k122

theorem s123 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6149647379371 + 100000000) ∧ Nat.Prime 6149647379371 ∧ 3 ≤ 6149647379371 :=
  step hB (by norm_num) (s122 hB).1 (s122 hB).2.1 (s122 hB).2.2 Core.c123 Core.k123

theorem s124 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6199643482561 + 100000000) ∧ Nat.Prime 6199643482561 ∧ 3 ≤ 6199643482561 :=
  step hB (by norm_num) (s123 hB).1 (s123 hB).2.1 (s123 hB).2.2 Core.c124 Core.k124

theorem s125 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6249639243079 + 100000000) ∧ Nat.Prime 6249639243079 ∧ 3 ≤ 6249639243079 :=
  step hB (by norm_num) (s124 hB).1 (s124 hB).2.1 (s124 hB).2.2 Core.c125 Core.k125

theorem s126 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6299635319129 + 100000000) ∧ Nat.Prime 6299635319129 ∧ 3 ≤ 6299635319129 :=
  step hB (by norm_num) (s125 hB).1 (s125 hB).2.1 (s125 hB).2.2 Core.c126 Core.k126

theorem s127 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6349631325601 + 100000000) ∧ Nat.Prime 6349631325601 ∧ 3 ≤ 6349631325601 :=
  step hB (by norm_num) (s126 hB).1 (s126 hB).2.1 (s126 hB).2.2 Core.c127 Core.k127

theorem s128 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6399627328319 + 100000000) ∧ Nat.Prime 6399627328319 ∧ 3 ≤ 6399627328319 :=
  step hB (by norm_num) (s127 hB).1 (s127 hB).2.1 (s127 hB).2.2 Core.c128 Core.k128

theorem s129 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6449623394581 + 100000000) ∧ Nat.Prime 6449623394581 ∧ 3 ≤ 6449623394581 :=
  step hB (by norm_num) (s128 hB).1 (s128 hB).2.1 (s128 hB).2.2 Core.c129 Core.k129

theorem s130 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6499619672503 + 100000000) ∧ Nat.Prime 6499619672503 ∧ 3 ≤ 6499619672503 :=
  step hB (by norm_num) (s129 hB).1 (s129 hB).2.1 (s129 hB).2.2 Core.c130 Core.k130

theorem s131 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6549615709513 + 100000000) ∧ Nat.Prime 6549615709513 ∧ 3 ≤ 6549615709513 :=
  step hB (by norm_num) (s130 hB).1 (s130 hB).2.1 (s130 hB).2.2 Core.c131 Core.k131

theorem s132 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6599611810061 + 100000000) ∧ Nat.Prime 6599611810061 ∧ 3 ≤ 6599611810061 :=
  step hB (by norm_num) (s131 hB).1 (s131 hB).2.1 (s131 hB).2.2 Core.c132 Core.k132

theorem s133 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6649607720897 + 100000000) ∧ Nat.Prime 6649607720897 ∧ 3 ≤ 6649607720897 :=
  step hB (by norm_num) (s132 hB).1 (s132 hB).2.1 (s132 hB).2.2 Core.c133 Core.k133

theorem s134 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6699603519001 + 100000000) ∧ Nat.Prime 6699603519001 ∧ 3 ≤ 6699603519001 :=
  step hB (by norm_num) (s133 hB).1 (s133 hB).2.1 (s133 hB).2.2 Core.c134 Core.k134

theorem s135 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6749599545461 + 100000000) ∧ Nat.Prime 6749599545461 ∧ 3 ≤ 6749599545461 :=
  step hB (by norm_num) (s134 hB).1 (s134 hB).2.1 (s134 hB).2.2 Core.c135 Core.k135

theorem s136 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6799595173981 + 100000000) ∧ Nat.Prime 6799595173981 ∧ 3 ≤ 6799595173981 :=
  step hB (by norm_num) (s135 hB).1 (s135 hB).2.1 (s135 hB).2.2 Core.c136 Core.k136

theorem s137 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6849591295121 + 100000000) ∧ Nat.Prime 6849591295121 ∧ 3 ≤ 6849591295121 :=
  step hB (by norm_num) (s136 hB).1 (s136 hB).2.1 (s136 hB).2.2 Core.c137 Core.k137

theorem s138 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6899587100407 + 100000000) ∧ Nat.Prime 6899587100407 ∧ 3 ≤ 6899587100407 :=
  step hB (by norm_num) (s137 hB).1 (s137 hB).2.1 (s137 hB).2.2 Core.c138 Core.k138

theorem s139 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6949583074393 + 100000000) ∧ Nat.Prime 6949583074393 ∧ 3 ≤ 6949583074393 :=
  step hB (by norm_num) (s138 hB).1 (s138 hB).2.1 (s138 hB).2.2 Core.c139 Core.k139

theorem s140 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (6999578692261 + 100000000) ∧ Nat.Prime 6999578692261 ∧ 3 ≤ 6999578692261 :=
  step hB (by norm_num) (s139 hB).1 (s139 hB).2.1 (s139 hB).2.2 Core.c140 Core.k140

theorem s141 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7049574651907 + 100000000) ∧ Nat.Prime 7049574651907 ∧ 3 ≤ 7049574651907 :=
  step hB (by norm_num) (s140 hB).1 (s140 hB).2.1 (s140 hB).2.2 Core.c141 Core.k141

theorem s142 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7099570510709 + 100000000) ∧ Nat.Prime 7099570510709 ∧ 3 ≤ 7099570510709 :=
  step hB (by norm_num) (s141 hB).1 (s141 hB).2.1 (s141 hB).2.2 Core.c142 Core.k142

theorem s143 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7149566489627 + 100000000) ∧ Nat.Prime 7149566489627 ∧ 3 ≤ 7149566489627 :=
  step hB (by norm_num) (s142 hB).1 (s142 hB).2.1 (s142 hB).2.2 Core.c143 Core.k143

theorem s144 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7199562035651 + 100000000) ∧ Nat.Prime 7199562035651 ∧ 3 ≤ 7199562035651 :=
  step hB (by norm_num) (s143 hB).1 (s143 hB).2.1 (s143 hB).2.2 Core.c144 Core.k144

theorem s145 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7249557646549 + 100000000) ∧ Nat.Prime 7249557646549 ∧ 3 ≤ 7249557646549 :=
  step hB (by norm_num) (s144 hB).1 (s144 hB).2.1 (s144 hB).2.2 Core.c145 Core.k145

theorem s146 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7299553419341 + 100000000) ∧ Nat.Prime 7299553419341 ∧ 3 ≤ 7299553419341 :=
  step hB (by norm_num) (s145 hB).1 (s145 hB).2.1 (s145 hB).2.2 Core.c146 Core.k146

theorem s147 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7349549344171 + 100000000) ∧ Nat.Prime 7349549344171 ∧ 3 ≤ 7349549344171 :=
  step hB (by norm_num) (s146 hB).1 (s146 hB).2.1 (s146 hB).2.2 Core.c147 Core.k147

theorem s148 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7399544766769 + 100000000) ∧ Nat.Prime 7399544766769 ∧ 3 ≤ 7399544766769 :=
  step hB (by norm_num) (s147 hB).1 (s147 hB).2.1 (s147 hB).2.2 Core.c148 Core.k148

theorem s149 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7449540548473 + 100000000) ∧ Nat.Prime 7449540548473 ∧ 3 ≤ 7449540548473 :=
  step hB (by norm_num) (s148 hB).1 (s148 hB).2.1 (s148 hB).2.2 Core.c149 Core.k149

theorem s150 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7499536617907 + 100000000) ∧ Nat.Prime 7499536617907 ∧ 3 ≤ 7499536617907 :=
  step hB (by norm_num) (s149 hB).1 (s149 hB).2.1 (s149 hB).2.2 Core.c150 Core.k150

theorem s151 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7549531992953 + 100000000) ∧ Nat.Prime 7549531992953 ∧ 3 ≤ 7549531992953 :=
  step hB (by norm_num) (s150 hB).1 (s150 hB).2.1 (s150 hB).2.2 Core.c151 Core.k151

theorem s152 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7599527773241 + 100000000) ∧ Nat.Prime 7599527773241 ∧ 3 ≤ 7599527773241 :=
  step hB (by norm_num) (s151 hB).1 (s151 hB).2.1 (s151 hB).2.2 Core.c152 Core.k152

theorem s153 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7649523243547 + 100000000) ∧ Nat.Prime 7649523243547 ∧ 3 ≤ 7649523243547 :=
  step hB (by norm_num) (s152 hB).1 (s152 hB).2.1 (s152 hB).2.2 Core.c153 Core.k153

theorem s154 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7699518784751 + 100000000) ∧ Nat.Prime 7699518784751 ∧ 3 ≤ 7699518784751 :=
  step hB (by norm_num) (s153 hB).1 (s153 hB).2.1 (s153 hB).2.2 Core.c154 Core.k154

theorem s155 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7749514252801 + 100000000) ∧ Nat.Prime 7749514252801 ∧ 3 ≤ 7749514252801 :=
  step hB (by norm_num) (s154 hB).1 (s154 hB).2.1 (s154 hB).2.2 Core.c155 Core.k155

theorem s156 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7799509680257 + 100000000) ∧ Nat.Prime 7799509680257 ∧ 3 ≤ 7799509680257 :=
  step hB (by norm_num) (s155 hB).1 (s155 hB).2.1 (s155 hB).2.2 Core.c156 Core.k156

theorem s157 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7849505288353 + 100000000) ∧ Nat.Prime 7849505288353 ∧ 3 ≤ 7849505288353 :=
  step hB (by norm_num) (s156 hB).1 (s156 hB).2.1 (s156 hB).2.2 Core.c157 Core.k157

theorem s158 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7899500768689 + 100000000) ∧ Nat.Prime 7899500768689 ∧ 3 ≤ 7899500768689 :=
  step hB (by norm_num) (s157 hB).1 (s157 hB).2.1 (s157 hB).2.2 Core.c158 Core.k158

theorem s159 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7949496387493 + 100000000) ∧ Nat.Prime 7949496387493 ∧ 3 ≤ 7949496387493 :=
  step hB (by norm_num) (s158 hB).1 (s158 hB).2.1 (s158 hB).2.2 Core.c159 Core.k159

theorem s160 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (7999491901501 + 100000000) ∧ Nat.Prime 7999491901501 ∧ 3 ≤ 7999491901501 :=
  step hB (by norm_num) (s159 hB).1 (s159 hB).2.1 (s159 hB).2.2 Core.c160 Core.k160

theorem s161 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8049487656601 + 100000000) ∧ Nat.Prime 8049487656601 ∧ 3 ≤ 8049487656601 :=
  step hB (by norm_num) (s160 hB).1 (s160 hB).2.1 (s160 hB).2.2 Core.c161 Core.k161

theorem s162 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8099483288851 + 100000000) ∧ Nat.Prime 8099483288851 ∧ 3 ≤ 8099483288851 :=
  step hB (by norm_num) (s161 hB).1 (s161 hB).2.1 (s161 hB).2.2 Core.c162 Core.k162

theorem s163 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8149479076547 + 100000000) ∧ Nat.Prime 8149479076547 ∧ 3 ≤ 8149479076547 :=
  step hB (by norm_num) (s162 hB).1 (s162 hB).2.1 (s162 hB).2.2 Core.c163 Core.k163

theorem s164 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8199474395113 + 100000000) ∧ Nat.Prime 8199474395113 ∧ 3 ≤ 8199474395113 :=
  step hB (by norm_num) (s163 hB).1 (s163 hB).2.1 (s163 hB).2.2 Core.c164 Core.k164

theorem s165 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8249470017157 + 100000000) ∧ Nat.Prime 8249470017157 ∧ 3 ≤ 8249470017157 :=
  step hB (by norm_num) (s164 hB).1 (s164 hB).2.1 (s164 hB).2.2 Core.c165 Core.k165

theorem s166 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8299465480001 + 100000000) ∧ Nat.Prime 8299465480001 ∧ 3 ≤ 8299465480001 :=
  step hB (by norm_num) (s165 hB).1 (s165 hB).2.1 (s165 hB).2.2 Core.c166 Core.k166

theorem s167 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8349460889101 + 100000000) ∧ Nat.Prime 8349460889101 ∧ 3 ≤ 8349460889101 :=
  step hB (by norm_num) (s166 hB).1 (s166 hB).2.1 (s166 hB).2.2 Core.c167 Core.k167

theorem s168 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8399456500609 + 100000000) ∧ Nat.Prime 8399456500609 ∧ 3 ≤ 8399456500609 :=
  step hB (by norm_num) (s167 hB).1 (s167 hB).2.1 (s167 hB).2.2 Core.c168 Core.k168

theorem s169 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8449451947523 + 100000000) ∧ Nat.Prime 8449451947523 ∧ 3 ≤ 8449451947523 :=
  step hB (by norm_num) (s168 hB).1 (s168 hB).2.1 (s168 hB).2.2 Core.c169 Core.k169

theorem s170 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8499447267737 + 100000000) ∧ Nat.Prime 8499447267737 ∧ 3 ≤ 8499447267737 :=
  step hB (by norm_num) (s169 hB).1 (s169 hB).2.1 (s169 hB).2.2 Core.c170 Core.k170

theorem s171 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8549442335719 + 100000000) ∧ Nat.Prime 8549442335719 ∧ 3 ≤ 8549442335719 :=
  step hB (by norm_num) (s170 hB).1 (s170 hB).2.1 (s170 hB).2.2 Core.c171 Core.k171

theorem s172 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8599438177201 + 100000000) ∧ Nat.Prime 8599438177201 ∧ 3 ≤ 8599438177201 :=
  step hB (by norm_num) (s171 hB).1 (s171 hB).2.1 (s171 hB).2.2 Core.c172 Core.k172

theorem s173 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8649433753117 + 100000000) ∧ Nat.Prime 8649433753117 ∧ 3 ≤ 8649433753117 :=
  step hB (by norm_num) (s172 hB).1 (s172 hB).2.1 (s172 hB).2.2 Core.c173 Core.k173

theorem s174 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8699429222401 + 100000000) ∧ Nat.Prime 8699429222401 ∧ 3 ≤ 8699429222401 :=
  step hB (by norm_num) (s173 hB).1 (s173 hB).2.1 (s173 hB).2.2 Core.c174 Core.k174

theorem s175 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8749424791693 + 100000000) ∧ Nat.Prime 8749424791693 ∧ 3 ≤ 8749424791693 :=
  step hB (by norm_num) (s174 hB).1 (s174 hB).2.1 (s174 hB).2.2 Core.c175 Core.k175

theorem s176 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8799420210521 + 100000000) ∧ Nat.Prime 8799420210521 ∧ 3 ≤ 8799420210521 :=
  step hB (by norm_num) (s175 hB).1 (s175 hB).2.1 (s175 hB).2.2 Core.c176 Core.k176

theorem s177 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8849415499541 + 100000000) ∧ Nat.Prime 8849415499541 ∧ 3 ≤ 8849415499541 :=
  step hB (by norm_num) (s176 hB).1 (s176 hB).2.1 (s176 hB).2.2 Core.c177 Core.k177

theorem s178 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8899410649117 + 100000000) ∧ Nat.Prime 8899410649117 ∧ 3 ≤ 8899410649117 :=
  step hB (by norm_num) (s177 hB).1 (s177 hB).2.1 (s177 hB).2.2 Core.c178 Core.k178

theorem s179 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8949405890041 + 100000000) ∧ Nat.Prime 8949405890041 ∧ 3 ≤ 8949405890041 :=
  step hB (by norm_num) (s178 hB).1 (s178 hB).2.1 (s178 hB).2.2 Core.c179 Core.k179

theorem s180 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (8999400877039 + 100000000) ∧ Nat.Prime 8999400877039 ∧ 3 ≤ 8999400877039 :=
  step hB (by norm_num) (s179 hB).1 (s179 hB).2.1 (s179 hB).2.2 Core.c180 Core.k180

theorem s181 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9049396397101 + 100000000) ∧ Nat.Prime 9049396397101 ∧ 3 ≤ 9049396397101 :=
  step hB (by norm_num) (s180 hB).1 (s180 hB).2.1 (s180 hB).2.2 Core.c181 Core.k181

theorem s182 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9099391843117 + 100000000) ∧ Nat.Prime 9099391843117 ∧ 3 ≤ 9099391843117 :=
  step hB (by norm_num) (s181 hB).1 (s181 hB).2.1 (s181 hB).2.2 Core.c182 Core.k182

theorem s183 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9149387068973 + 100000000) ∧ Nat.Prime 9149387068973 ∧ 3 ≤ 9149387068973 :=
  step hB (by norm_num) (s182 hB).1 (s182 hB).2.1 (s182 hB).2.2 Core.c183 Core.k183

theorem s184 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9199382016697 + 100000000) ∧ Nat.Prime 9199382016697 ∧ 3 ≤ 9199382016697 :=
  step hB (by norm_num) (s183 hB).1 (s183 hB).2.1 (s183 hB).2.2 Core.c184 Core.k184

theorem s185 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9249377469197 + 100000000) ∧ Nat.Prime 9249377469197 ∧ 3 ≤ 9249377469197 :=
  step hB (by norm_num) (s184 hB).1 (s184 hB).2.1 (s184 hB).2.2 Core.c185 Core.k185

theorem s186 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9299373094229 + 100000000) ∧ Nat.Prime 9299373094229 ∧ 3 ≤ 9299373094229 :=
  step hB (by norm_num) (s185 hB).1 (s185 hB).2.1 (s185 hB).2.2 Core.c186 Core.k186

theorem s187 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9349368059113 + 100000000) ∧ Nat.Prime 9349368059113 ∧ 3 ≤ 9349368059113 :=
  step hB (by norm_num) (s186 hB).1 (s186 hB).2.1 (s186 hB).2.2 Core.c187 Core.k187

theorem s188 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9399363220801 + 100000000) ∧ Nat.Prime 9399363220801 ∧ 3 ≤ 9399363220801 :=
  step hB (by norm_num) (s187 hB).1 (s187 hB).2.1 (s187 hB).2.2 Core.c188 Core.k188

theorem s189 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9449358343853 + 100000000) ∧ Nat.Prime 9449358343853 ∧ 3 ≤ 9449358343853 :=
  step hB (by norm_num) (s188 hB).1 (s188 hB).2.1 (s188 hB).2.2 Core.c189 Core.k189

theorem s190 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9499353466247 + 100000000) ∧ Nat.Prime 9499353466247 ∧ 3 ≤ 9499353466247 :=
  step hB (by norm_num) (s189 hB).1 (s189 hB).2.1 (s189 hB).2.2 Core.c190 Core.k190

theorem s191 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9549348754861 + 100000000) ∧ Nat.Prime 9549348754861 ∧ 3 ≤ 9549348754861 :=
  step hB (by norm_num) (s190 hB).1 (s190 hB).2.1 (s190 hB).2.2 Core.c191 Core.k191

theorem s192 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9599344162547 + 100000000) ∧ Nat.Prime 9599344162547 ∧ 3 ≤ 9599344162547 :=
  step hB (by norm_num) (s191 hB).1 (s191 hB).2.1 (s191 hB).2.2 Core.c192 Core.k192

theorem s193 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9649339575553 + 100000000) ∧ Nat.Prime 9649339575553 ∧ 3 ≤ 9649339575553 :=
  step hB (by norm_num) (s192 hB).1 (s192 hB).2.1 (s192 hB).2.2 Core.c193 Core.k193

theorem s194 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9699335027251 + 100000000) ∧ Nat.Prime 9699335027251 ∧ 3 ≤ 9699335027251 :=
  step hB (by norm_num) (s193 hB).1 (s193 hB).2.1 (s193 hB).2.2 Core.c194 Core.k194

theorem s195 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9749330621801 + 100000000) ∧ Nat.Prime 9749330621801 ∧ 3 ≤ 9749330621801 :=
  step hB (by norm_num) (s194 hB).1 (s194 hB).2.1 (s194 hB).2.2 Core.c195 Core.k195

theorem s196 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9799325996491 + 100000000) ∧ Nat.Prime 9799325996491 ∧ 3 ≤ 9799325996491 :=
  step hB (by norm_num) (s195 hB).1 (s195 hB).2.1 (s195 hB).2.2 Core.c196 Core.k196

theorem s197 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9849321216197 + 100000000) ∧ Nat.Prime 9849321216197 ∧ 3 ≤ 9849321216197 :=
  step hB (by norm_num) (s196 hB).1 (s196 hB).2.1 (s196 hB).2.2 Core.c197 Core.k197

theorem s198 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9899316241541 + 100000000) ∧ Nat.Prime 9899316241541 ∧ 3 ≤ 9899316241541 :=
  step hB (by norm_num) (s197 hB).1 (s197 hB).2.1 (s197 hB).2.2 Core.c198 Core.k198

theorem s199 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9949311478289 + 100000000) ∧ Nat.Prime 9949311478289 ∧ 3 ≤ 9949311478289 :=
  step hB (by norm_num) (s198 hB).1 (s198 hB).2.1 (s198 hB).2.2 Core.c199 Core.k199

theorem s200 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9999306519511 + 100000000) ∧ Nat.Prime 9999306519511 ∧ 3 ≤ 9999306519511 :=
  step hB (by norm_num) (s199 hB).1 (s199 hB).2.1 (s199 hB).2.2 Core.c200 Core.k200

theorem s201 (hB : EvenGoldbachUpTo 100000000) :
    TernaryGoldbachUpTo (9999906444119 + 100000000) ∧ Nat.Prime 9999906444119 ∧ 3 ≤ 9999906444119 :=
  step hB (by norm_num) (s200 hB).1 (s200 hB).2.1 (s200 hB).2.2 Core.c201 Core.k201

/-- Saouter's step: even Goldbach to 10^8 and this ladder give ternary Goldbach to 10000006444119. -/
theorem ternary_of_even (hB : EvenGoldbachUpTo 100000000) : TernaryGoldbachUpTo 10000006444119 :=
  (s201 hB).1

end LeanLab.Saouter1998
