/-
EvenGoldbachUpTo 100000000, zero sorry: every even n with 4 ≤ n ≤ 10^8 is a sum of two primes,
checked by the Lean kernel with no cited input. From EvenGoldbachUpTo 10^6 in BitUpTo1e6.lean
and 50 windows of 1980000, each one bignum equality, BitW1 to BitW50, sound by upTo_extend in
BitSieve.lean. Far below the 4e18 of P0005; the point is that nothing here is cited.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitUpTo1e6
import LeanLab.Verifications.Top50.BitW1
import LeanLab.Verifications.Top50.BitW2
import LeanLab.Verifications.Top50.BitW3
import LeanLab.Verifications.Top50.BitW4
import LeanLab.Verifications.Top50.BitW5
import LeanLab.Verifications.Top50.BitW6
import LeanLab.Verifications.Top50.BitW7
import LeanLab.Verifications.Top50.BitW8
import LeanLab.Verifications.Top50.BitW9
import LeanLab.Verifications.Top50.BitW10
import LeanLab.Verifications.Top50.BitW11
import LeanLab.Verifications.Top50.BitW12
import LeanLab.Verifications.Top50.BitW13
import LeanLab.Verifications.Top50.BitW14
import LeanLab.Verifications.Top50.BitW15
import LeanLab.Verifications.Top50.BitW16
import LeanLab.Verifications.Top50.BitW17
import LeanLab.Verifications.Top50.BitW18
import LeanLab.Verifications.Top50.BitW19
import LeanLab.Verifications.Top50.BitW20
import LeanLab.Verifications.Top50.BitW21
import LeanLab.Verifications.Top50.BitW22
import LeanLab.Verifications.Top50.BitW23
import LeanLab.Verifications.Top50.BitW24
import LeanLab.Verifications.Top50.BitW25
import LeanLab.Verifications.Top50.BitW26
import LeanLab.Verifications.Top50.BitW27
import LeanLab.Verifications.Top50.BitW28
import LeanLab.Verifications.Top50.BitW29
import LeanLab.Verifications.Top50.BitW30
import LeanLab.Verifications.Top50.BitW31
import LeanLab.Verifications.Top50.BitW32
import LeanLab.Verifications.Top50.BitW33
import LeanLab.Verifications.Top50.BitW34
import LeanLab.Verifications.Top50.BitW35
import LeanLab.Verifications.Top50.BitW36
import LeanLab.Verifications.Top50.BitW37
import LeanLab.Verifications.Top50.BitW38
import LeanLab.Verifications.Top50.BitW39
import LeanLab.Verifications.Top50.BitW40
import LeanLab.Verifications.Top50.BitW41
import LeanLab.Verifications.Top50.BitW42
import LeanLab.Verifications.Top50.BitW43
import LeanLab.Verifications.Top50.BitW44
import LeanLab.Verifications.Top50.BitW45
import LeanLab.Verifications.Top50.BitW46
import LeanLab.Verifications.Top50.BitW47
import LeanLab.Verifications.Top50.BitW48
import LeanLab.Verifications.Top50.BitW49
import LeanLab.Verifications.Top50.BitW50

namespace LeanLab.Verifications.Top50.Bits

/-- `upTo_extend` with the window start as its own numeral, so no unfolding is needed. -/
theorem upTo_extend' {lo W a A B : ℕ} {Q : List ℕ} (ha : EvenGoldbachUpTo a) (hae : 2 ∣ a)
    (hA : a + 2 = A) (h2 : 2 ≤ lo) (hW : lo + W ≤ 10 ^ 8) (hlo : lo ≤ A)
    (hQ : ∀ q ∈ Q, q.Prime)
    (h : wem lo A B &&& gm (wpm lo W) Q = wem lo A B) : EvenGoldbachUpTo B := by
  subst hA
  exact upTo_extend ha hae h2 hW hlo hQ h


theorem upTo_w1 : EvenGoldbachUpTo 2980000 :=
  upTo_extend' (a := 1000000) (A := 1000002) (lo := 998902) (W := 1981098) evenGoldbachUpTo_1e6
    ⟨500000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_1

theorem upTo_w2 : EvenGoldbachUpTo 4960000 :=
  upTo_extend' (a := 2980000) (A := 2980002) (lo := 2978902) (W := 1981098) upTo_w1
    ⟨1490000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_2

theorem upTo_w3 : EvenGoldbachUpTo 6940000 :=
  upTo_extend' (a := 4960000) (A := 4960002) (lo := 4958902) (W := 1981098) upTo_w2
    ⟨2480000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_3

theorem upTo_w4 : EvenGoldbachUpTo 8920000 :=
  upTo_extend' (a := 6940000) (A := 6940002) (lo := 6938902) (W := 1981098) upTo_w3
    ⟨3470000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_4

theorem upTo_w5 : EvenGoldbachUpTo 10900000 :=
  upTo_extend' (a := 8920000) (A := 8920002) (lo := 8918902) (W := 1981098) upTo_w4
    ⟨4460000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_5

theorem upTo_w6 : EvenGoldbachUpTo 12880000 :=
  upTo_extend' (a := 10900000) (A := 10900002) (lo := 10898902) (W := 1981098) upTo_w5
    ⟨5450000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_6

theorem upTo_w7 : EvenGoldbachUpTo 14860000 :=
  upTo_extend' (a := 12880000) (A := 12880002) (lo := 12878902) (W := 1981098) upTo_w6
    ⟨6440000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_7

theorem upTo_w8 : EvenGoldbachUpTo 16840000 :=
  upTo_extend' (a := 14860000) (A := 14860002) (lo := 14858902) (W := 1981098) upTo_w7
    ⟨7430000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_8

theorem upTo_w9 : EvenGoldbachUpTo 18820000 :=
  upTo_extend' (a := 16840000) (A := 16840002) (lo := 16838902) (W := 1981098) upTo_w8
    ⟨8420000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_9

theorem upTo_w10 : EvenGoldbachUpTo 20800000 :=
  upTo_extend' (a := 18820000) (A := 18820002) (lo := 18818902) (W := 1981098) upTo_w9
    ⟨9410000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_10

theorem upTo_w11 : EvenGoldbachUpTo 22780000 :=
  upTo_extend' (a := 20800000) (A := 20800002) (lo := 20798902) (W := 1981098) upTo_w10
    ⟨10400000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_11

theorem upTo_w12 : EvenGoldbachUpTo 24760000 :=
  upTo_extend' (a := 22780000) (A := 22780002) (lo := 22778902) (W := 1981098) upTo_w11
    ⟨11390000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_12

theorem upTo_w13 : EvenGoldbachUpTo 26740000 :=
  upTo_extend' (a := 24760000) (A := 24760002) (lo := 24758902) (W := 1981098) upTo_w12
    ⟨12380000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_13

theorem upTo_w14 : EvenGoldbachUpTo 28720000 :=
  upTo_extend' (a := 26740000) (A := 26740002) (lo := 26738902) (W := 1981098) upTo_w13
    ⟨13370000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_14

theorem upTo_w15 : EvenGoldbachUpTo 30700000 :=
  upTo_extend' (a := 28720000) (A := 28720002) (lo := 28718902) (W := 1981098) upTo_w14
    ⟨14360000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_15

theorem upTo_w16 : EvenGoldbachUpTo 32680000 :=
  upTo_extend' (a := 30700000) (A := 30700002) (lo := 30698902) (W := 1981098) upTo_w15
    ⟨15350000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_16

theorem upTo_w17 : EvenGoldbachUpTo 34660000 :=
  upTo_extend' (a := 32680000) (A := 32680002) (lo := 32678902) (W := 1981098) upTo_w16
    ⟨16340000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_17

theorem upTo_w18 : EvenGoldbachUpTo 36640000 :=
  upTo_extend' (a := 34660000) (A := 34660002) (lo := 34658902) (W := 1981098) upTo_w17
    ⟨17330000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_18

theorem upTo_w19 : EvenGoldbachUpTo 38620000 :=
  upTo_extend' (a := 36640000) (A := 36640002) (lo := 36638902) (W := 1981098) upTo_w18
    ⟨18320000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_19

theorem upTo_w20 : EvenGoldbachUpTo 40600000 :=
  upTo_extend' (a := 38620000) (A := 38620002) (lo := 38618902) (W := 1981098) upTo_w19
    ⟨19310000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_20

theorem upTo_w21 : EvenGoldbachUpTo 42580000 :=
  upTo_extend' (a := 40600000) (A := 40600002) (lo := 40598902) (W := 1981098) upTo_w20
    ⟨20300000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_21

theorem upTo_w22 : EvenGoldbachUpTo 44560000 :=
  upTo_extend' (a := 42580000) (A := 42580002) (lo := 42578902) (W := 1981098) upTo_w21
    ⟨21290000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_22

theorem upTo_w23 : EvenGoldbachUpTo 46540000 :=
  upTo_extend' (a := 44560000) (A := 44560002) (lo := 44558902) (W := 1981098) upTo_w22
    ⟨22280000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_23

theorem upTo_w24 : EvenGoldbachUpTo 48520000 :=
  upTo_extend' (a := 46540000) (A := 46540002) (lo := 46538902) (W := 1981098) upTo_w23
    ⟨23270000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_24

theorem upTo_w25 : EvenGoldbachUpTo 50500000 :=
  upTo_extend' (a := 48520000) (A := 48520002) (lo := 48518902) (W := 1981098) upTo_w24
    ⟨24260000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_25

theorem upTo_w26 : EvenGoldbachUpTo 52480000 :=
  upTo_extend' (a := 50500000) (A := 50500002) (lo := 50498902) (W := 1981098) upTo_w25
    ⟨25250000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_26

theorem upTo_w27 : EvenGoldbachUpTo 54460000 :=
  upTo_extend' (a := 52480000) (A := 52480002) (lo := 52478902) (W := 1981098) upTo_w26
    ⟨26240000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_27

theorem upTo_w28 : EvenGoldbachUpTo 56440000 :=
  upTo_extend' (a := 54460000) (A := 54460002) (lo := 54458902) (W := 1981098) upTo_w27
    ⟨27230000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_28

theorem upTo_w29 : EvenGoldbachUpTo 58420000 :=
  upTo_extend' (a := 56440000) (A := 56440002) (lo := 56438902) (W := 1981098) upTo_w28
    ⟨28220000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_29

theorem upTo_w30 : EvenGoldbachUpTo 60400000 :=
  upTo_extend' (a := 58420000) (A := 58420002) (lo := 58418902) (W := 1981098) upTo_w29
    ⟨29210000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_30

theorem upTo_w31 : EvenGoldbachUpTo 62380000 :=
  upTo_extend' (a := 60400000) (A := 60400002) (lo := 60398902) (W := 1981098) upTo_w30
    ⟨30200000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_31

theorem upTo_w32 : EvenGoldbachUpTo 64360000 :=
  upTo_extend' (a := 62380000) (A := 62380002) (lo := 62378902) (W := 1981098) upTo_w31
    ⟨31190000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_32

theorem upTo_w33 : EvenGoldbachUpTo 66340000 :=
  upTo_extend' (a := 64360000) (A := 64360002) (lo := 64358902) (W := 1981098) upTo_w32
    ⟨32180000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_33

theorem upTo_w34 : EvenGoldbachUpTo 68320000 :=
  upTo_extend' (a := 66340000) (A := 66340002) (lo := 66338902) (W := 1981098) upTo_w33
    ⟨33170000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_34

theorem upTo_w35 : EvenGoldbachUpTo 70300000 :=
  upTo_extend' (a := 68320000) (A := 68320002) (lo := 68318902) (W := 1981098) upTo_w34
    ⟨34160000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_35

theorem upTo_w36 : EvenGoldbachUpTo 72280000 :=
  upTo_extend' (a := 70300000) (A := 70300002) (lo := 70298902) (W := 1981098) upTo_w35
    ⟨35150000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_36

theorem upTo_w37 : EvenGoldbachUpTo 74260000 :=
  upTo_extend' (a := 72280000) (A := 72280002) (lo := 72278902) (W := 1981098) upTo_w36
    ⟨36140000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_37

theorem upTo_w38 : EvenGoldbachUpTo 76240000 :=
  upTo_extend' (a := 74260000) (A := 74260002) (lo := 74258902) (W := 1981098) upTo_w37
    ⟨37130000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_38

theorem upTo_w39 : EvenGoldbachUpTo 78220000 :=
  upTo_extend' (a := 76240000) (A := 76240002) (lo := 76238902) (W := 1981098) upTo_w38
    ⟨38120000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_39

theorem upTo_w40 : EvenGoldbachUpTo 80200000 :=
  upTo_extend' (a := 78220000) (A := 78220002) (lo := 78218902) (W := 1981098) upTo_w39
    ⟨39110000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_40

theorem upTo_w41 : EvenGoldbachUpTo 82180000 :=
  upTo_extend' (a := 80200000) (A := 80200002) (lo := 80198902) (W := 1981098) upTo_w40
    ⟨40100000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_41

theorem upTo_w42 : EvenGoldbachUpTo 84160000 :=
  upTo_extend' (a := 82180000) (A := 82180002) (lo := 82178902) (W := 1981098) upTo_w41
    ⟨41090000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_42

theorem upTo_w43 : EvenGoldbachUpTo 86140000 :=
  upTo_extend' (a := 84160000) (A := 84160002) (lo := 84158902) (W := 1981098) upTo_w42
    ⟨42080000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_43

theorem upTo_w44 : EvenGoldbachUpTo 88120000 :=
  upTo_extend' (a := 86140000) (A := 86140002) (lo := 86138902) (W := 1981098) upTo_w43
    ⟨43070000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_44

theorem upTo_w45 : EvenGoldbachUpTo 90100000 :=
  upTo_extend' (a := 88120000) (A := 88120002) (lo := 88118902) (W := 1981098) upTo_w44
    ⟨44060000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_45

theorem upTo_w46 : EvenGoldbachUpTo 92080000 :=
  upTo_extend' (a := 90100000) (A := 90100002) (lo := 90098902) (W := 1981098) upTo_w45
    ⟨45050000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_46

theorem upTo_w47 : EvenGoldbachUpTo 94060000 :=
  upTo_extend' (a := 92080000) (A := 92080002) (lo := 92078902) (W := 1981098) upTo_w46
    ⟨46040000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_47

theorem upTo_w48 : EvenGoldbachUpTo 96040000 :=
  upTo_extend' (a := 94060000) (A := 94060002) (lo := 94058902) (W := 1981098) upTo_w47
    ⟨47030000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_48

theorem upTo_w49 : EvenGoldbachUpTo 98020000 :=
  upTo_extend' (a := 96040000) (A := 96040002) (lo := 96038902) (W := 1981098) upTo_w48
    ⟨48020000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_49

theorem evenGoldbachUpTo_1e8 : EvenGoldbachUpTo 100000000 :=
  upTo_extend' (a := 98020000) (A := 98020002) (lo := 98018902) (W := 1981098) upTo_w49
    ⟨49010000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) window_50

/-- Ternary corollary: every odd n with 7 ≤ n ≤ 10^8 + 3 is a sum of three primes, as 3 plus
an even Goldbach sum. Trivial next to Helfgott-Platt, kept because it is cited-input free. -/
theorem ternaryGoldbachUpTo_1e8 : TernaryGoldbachUpTo (10 ^ 8 + 3) := by
  intro n hn h7 hnN
  obtain ⟨p, q, hp, hq, hpq⟩ := evenGoldbachUpTo_1e8 (n - 3)
    (by obtain ⟨k, rfl⟩ := hn; exact ⟨k - 1, by omega⟩) (by omega) (by omega)
  exact ⟨p, q, 3, hp, hq, Nat.prime_three, by omega⟩

end LeanLab.Verifications.Top50.Bits
