/-
P0062 H. A. Helfgott, "The ternary Goldbach problem", overview, arXiv 1404.2224v2.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

The overview states one theorem, the Main Theorem, already in the lab as
`LeanLab.Ternary.helfgott`. Its explicit analytic estimates, (3.8) and Theorem 4.1, are
already stated in `LeanLab/HelfgottArcs/Statements.lean` as `major_1_1` and
`minorArcs_small`, `minorArcs_large`; that module is not built, so it is referenced, not
imported. This file records the overview's remaining numerical claims and corollaries and
links them, with zero sorry, to the lab's cited statements. No new `sorry` is added.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Ternary.Statements
import LeanLab.Verifications.Statements
import LeanLab.DERZ1997.Statements
import LeanLab.SchnirelmannConstant.Defs
import LeanLab.Tao2012.Statements

namespace LeanLab.HelfgottOverview
open LeanLab.Ternary LeanLab.SchnirelmannConstant

/-! ### Forms of the conjecture, section 1 -/

/-- Euler's form, p. 2: every integer greater than 1 is a sum of at most three primes.
For even `n` this needs binary Goldbach for `n` or `n - 2`; OPEN. -/
def EulerForm : Prop := ∀ n : ℕ, 1 < n → AtMostPrimes 3 n

/-- Descartes' statement, p. 1: every even number is made of one, two or three primes.
OPEN. -/
def DescartesForm : Prop := ∀ n : ℕ, Even n → 0 < n → AtMostPrimes 3 n

/-- The Main Theorem, p. 2: every odd integer greater than 5 is a sum of three primes.
This is `TernaryGoldbach`; the cited proof is `LeanLab.Ternary.helfgott`. -/
theorem main_theorem : ∀ n : ℕ, Odd n → 5 < n → IsTernarySum n :=
  fun n ho h5 => LeanLab.Ternary.helfgott n ho (by obtain ⟨k, rfl⟩ := ho; omega)

/-- "The strong conjecture implies the weak one: subtract 3", p. 2. -/
theorem ternary_of_binary (hB : BinaryGoldbach) : TernaryGoldbach := by
  intro n ho h7
  have he : Even (n - 3) := by obtain ⟨k, rfl⟩ := ho; exact ⟨k - 1, by omega⟩
  obtain ⟨p, q, hp, hq, hs⟩ := hB (n - 3) he (by omega)
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-- Binary Goldbach gives Euler's form. -/
theorem euler_of_binary (hB : BinaryGoldbach) : EulerForm := by
  intro n hn
  rcases Nat.even_or_odd n with he | ho
  · rcases Nat.lt_or_ge n 4 with h | h
    · have : n = 2 := by obtain ⟨k, rfl⟩ := he; omega
      subst this; exact (AtMostPrimes.prime Nat.prime_two).mono (by norm_num)
    · exact (AtMostPrimes.of_goldbach (hB n he h)).mono (by norm_num)
  · rcases Nat.lt_or_ge n 7 with h | h
    · obtain ⟨k, rfl⟩ := ho
      have : k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl
      · exact (AtMostPrimes.prime Nat.prime_three).mono (by norm_num)
      · exact (AtMostPrimes.prime (by norm_num : Nat.Prime 5)).mono (by norm_num)
    · obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := ternary_of_binary hB n ho h
      exact ((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add (AtMostPrimes.prime hr)

/-- Euler's form gives Descartes' statement. -/
theorem descartes_of_euler (h : EulerForm) : DescartesForm := by
  intro n he hn
  have : n ≠ 1 := by rintro rfl; exact (Nat.not_even_one) he
  exact h n (by omega)

/-! ### Corollaries of the Main Theorem, zero sorry from `TernaryGoldbach` -/

/-- Every odd `n > 1` is a sum of at most three primes: Tao's Conjecture 1.2. -/
theorem odd_atMost3 (hT : TernaryGoldbach) : LeanLab.Tao2012.Conjecture1_2 := by
  intro n ho hn
  rcases Nat.lt_or_ge n 7 with h | h
  · obtain ⟨k, rfl⟩ := ho
    have : k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl
    · exact (AtMostPrimes.prime Nat.prime_three).mono (by norm_num)
    · exact (AtMostPrimes.prime (by norm_num : Nat.Prime 5)).mono (by norm_num)
  · obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := hT n ho h
    exact ((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add (AtMostPrimes.prime hr)

/-- Every even `n` is a sum of at most four primes: `n = 3 + (n - 3)` for `n ≥ 8`. -/
theorem even_atMost4 (hT : TernaryGoldbach) : ∀ n : ℕ, Even n → AtMostPrimes 4 n := by
  intro n he
  rcases Nat.lt_or_ge n 8 with h | h
  · obtain ⟨k, rfl⟩ := he
    have hk : k < 4 := by omega
    interval_cases k
    · exact AtMostPrimes.zero.mono (by norm_num)
    · exact (AtMostPrimes.prime Nat.prime_two).mono (by norm_num)
    · exact ((AtMostPrimes.prime Nat.prime_two).add (AtMostPrimes.prime Nat.prime_two)).mono
        (by norm_num)
    · exact ((AtMostPrimes.prime Nat.prime_three).add
        (AtMostPrimes.prime Nat.prime_three)).mono (by norm_num)
  · have ho : Odd (n - 3) := by obtain ⟨k, rfl⟩ := he; exact ⟨k - 2, by omega⟩
    have := (AtMostPrimes.prime Nat.prime_three).add (odd_atMost3 hT (n - 3) ho (by omega))
    rwa [show 3 + (n - 3) = n by omega] at this

/-- Every `n > 1` is a sum of at most four primes. -/
theorem atMost4 (hT : TernaryGoldbach) : ∀ n : ℕ, 1 < n → AtMostPrimes 4 n := by
  intro n hn
  rcases Nat.even_or_odd n with he | ho
  · exact even_atMost4 hT n he
  · exact (odd_atMost3 hT n ho hn).mono (by norm_num)

/-- Every Schnirelmann-type bound `K ≥ 4` listed on p. 4: Klimov `6 · 10^9`, 115, 55,
Vaughan 27, Deshouillers 26, Riesel-Vaughan 19. -/
theorem atMostK (hT : TernaryGoldbach) (K : ℕ) (hK : 4 ≤ K) :
    ∀ n : ℕ, 1 < n → AtMostPrimes K n := fun n hn => (atMost4 hT n hn).mono hK

/-- Tao 2012 as stated on p. 5: every odd `n > 1` is a sum of at most five primes. -/
theorem tao_of_ternary (hT : TernaryGoldbach) :
    ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n :=
  fun n ho hn => (odd_atMost3 hT n ho hn).mono (by norm_num)

/-- Ramaré 1995 as stated on p. 5: every even `n > 1` is a sum of at most six primes. -/
theorem ramare_of_ternary (hT : TernaryGoldbach) :
    ∀ n : ℕ, Even n → 1 < n → AtMostPrimes 6 n :=
  fun n he _ => (even_atMost4 hT n he).mono (by norm_num)

/-- The corollaries, with the cited Main Theorem. -/
theorem corollaries : LeanLab.Tao2012.Conjecture1_2 ∧ (∀ n : ℕ, Even n → AtMostPrimes 4 n) ∧
    ∀ n : ℕ, 1 < n → AtMostPrimes 4 n :=
  ⟨odd_atMost3 helfgott, even_atMost4 helfgott, atMost4 helfgott⟩

/-! ### Thresholds of section 1 -/

/-- Helfgott-Platt as stated p. 4 and p. 25: every odd `5 < n ≤ 8.8 · 10^30`. -/
def HP88 : Prop := TernaryGoldbachUpTo (88 * 10 ^ 29)

theorem hp88_of (h : TernaryGoldbachUpTo 8875694145621773516800000000000) : HP88 :=
  fun n ho h7 hn => h n ho h7 (by omega)

/-- The home-computer check up to `10^27`, p. 4, follows from Helfgott-Platt. -/
theorem upTo1027_of (h : HP88) : TernaryGoldbachUpTo (10 ^ 27) :=
  fun n ho h7 hn => h n ho h7 (by omega)

/-- May 2013 version, p. 4: `C = 10^29`. It follows from December's `C = 10^27`. -/
theorem may2013_of_dec2013 (h : TernaryAbove (10 ^ 27)) : TernaryAbove (10 ^ 29) :=
  ternaryAbove_mono (by norm_num) h

/-- p. 4: `C = 10^29` with the check to `8.8 · 10^30` already gives every odd `n > 5`. -/
theorem main_of_may2013 (hA : TernaryAbove (10 ^ 29)) (hHP : HP88) : TernaryGoldbach := by
  intro n ho h7
  rcases le_or_gt ((10 : ℝ) ^ 29) n with hbig | hsmall
  · exact hA n ho hbig
  · have : n < 10 ^ 29 := by exact_mod_cast hsmall
    exact hHP n ho h7 (by omega)

/-- The overview's rounding of Liu-Wang, p. 3: `C = 2 · 10^1346`. -/
def LiuWangAsStated : Prop := TernaryAbove (2 * 10 ^ 1346)

/-- Chen-Wang 1989, p. 5: `C = exp(exp(11.503))`. -/
def ChenWang1989 : Prop := TernaryAbove (Real.exp (Real.exp 11.503))

/-- Borozdkin 1956, p. 3: `C = e^(e^16.038)`. -/
def Borozdkin1956 : Prop := TernaryAbove (Real.exp (Real.exp 16.038))

/-- Borozdkin 1939, p. 3: `C = exp(exp(exp(41.96)))`. -/
def Borozdkin1939 : Prop := TernaryAbove (Real.exp (Real.exp (Real.exp 41.96)))

/-! #### Kernel-checked bounds for `e^x` -/

theorem exp_nat_le_of {a d m : ℕ} (he : Real.exp 1 ≤ (a : ℝ) / 10 ^ d) :
    Real.exp m ≤ (a : ℝ) ^ m / 10 ^ (d * m) := by
  rw [← Real.exp_one_pow, pow_mul, ← div_pow]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le he m

theorem exp_nat_ge_of {a d m : ℕ} (he : (a : ℝ) / 10 ^ d ≤ Real.exp 1) :
    (a : ℝ) ^ m / 10 ^ (d * m) ≤ Real.exp m := by
  rw [← Real.exp_one_pow, pow_mul, ← div_pow]
  exact pow_le_pow_left₀ (by positivity) he m

/-- If `x ≤ m/q` and `a^m < c^q · 10^(kq) · 10^(dm)` with `e ≤ a/10^d`, then
`e^x < c · 10^k`. -/
theorem exp_lt_of {x : ℝ} {m q d a c k : ℕ} (hq : 0 < q) (hx : x ≤ (m : ℝ) / q)
    (he : Real.exp 1 ≤ (a : ℝ) / 10 ^ d) (h : a ^ m < c ^ q * 10 ^ (k * q) * 10 ^ (d * m)) :
    Real.exp x < (c : ℝ) * 10 ^ k := by
  have hR : (a : ℝ) ^ m < (c : ℝ) ^ q * 10 ^ (k * q) * 10 ^ (d * m) := by exact_mod_cast h
  have h1 : Real.exp ((m : ℝ) / q) ^ q = Real.exp m := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h2 : Real.exp (m : ℝ) < ((c : ℝ) * 10 ^ k) ^ q := by
    refine (exp_nat_le_of he).trans_lt ?_
    rw [div_lt_iff₀ (by positivity), mul_pow, ← pow_mul]
    exact hR
  have h3 : Real.exp ((m : ℝ) / q) < (c : ℝ) * 10 ^ k :=
    lt_of_pow_lt_pow_left₀ q (by positivity) (h1 ▸ h2)
  exact (Real.exp_le_exp.mpr hx).trans_lt h3

theorem lt_exp_of {m d a c k : ℕ} (he : (a : ℝ) / 10 ^ d ≤ Real.exp 1)
    (h : c * 10 ^ k * 10 ^ (d * m) < a ^ m) : (c : ℝ) * 10 ^ k < Real.exp m := by
  have hR : (c : ℝ) * 10 ^ k * 10 ^ (d * m) < (a : ℝ) ^ m := by exact_mod_cast h
  refine lt_of_lt_of_le ?_ (exp_nat_ge_of he)
  rw [lt_div_iff₀ (by positivity)]
  exact hR

theorem e_le : Real.exp 1 ≤ ((27182818286 : ℕ) : ℝ) / 10 ^ 10 := by
  have := Real.exp_one_lt_d9; push_cast; norm_num at this ⊢; linarith

theorem e_ge : ((27182818283 : ℕ) : ℝ) / 10 ^ 10 ≤ Real.exp 1 := by
  have := Real.exp_one_gt_d9; push_cast; norm_num at this ⊢; linarith

theorem exp_small_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ ∑ m ∈ Finset.range 14, x ^ m / m.factorial +
      x ^ 14 * ((Nat.succ 14 : ℕ) / ((Nat.factorial 14 : ℕ) * (14 : ℕ))) := by
  have := Real.exp_bound (x := x) (by rw [abs_of_nonneg h0]; exact h1) (n := 14) (by norm_num)
  rw [abs_of_nonneg h0] at this
  linarith [(abs_le.mp this).2]

theorem exp_nine_le : Real.exp 9 ≤ 2.7182818286 ^ 9 := by
  rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 9

theorem exp_eleven_le : Real.exp 11 ≤ 2.7182818286 ^ 11 := by
  rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 11

theorem exp_9715_le : Real.exp 9.715 ≤ ((66257 : ℕ) : ℝ) / (4 : ℕ) := by
  rw [show (9.715 : ℝ) = 9 + 0.715 by norm_num, Real.exp_add]
  have hs := exp_small_le (x := 0.715) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hs
  norm_num at hs
  have h9 := exp_nine_le
  have hp9 := Real.exp_pos 9
  have hp := Real.exp_pos 0.715
  push_cast
  nlinarith [mul_le_mul h9 hs (Real.exp_pos _).le (by norm_num)]

theorem exp_11503_le : Real.exp 11.503 ≤ ((198025 : ℕ) : ℝ) / (2 : ℕ) := by
  rw [show (11.503 : ℝ) = 11 + 0.503 by norm_num, Real.exp_add]
  have hs := exp_small_le (x := 0.503) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hs
  norm_num at hs
  have h11 := exp_eleven_le
  have hp := Real.exp_pos 0.503
  push_cast
  nlinarith [mul_le_mul h11 hs (Real.exp_pos _).le (by norm_num)]

/-- p. 5: `exp(exp(9.715)) < 6 · 10^7193`. PROVED. -/
theorem chenWang1996_bound : Real.exp (Real.exp 9.715) < 6 * 10 ^ 7193 := by
  have := exp_lt_of (x := Real.exp 9.715) (m := 66257) (q := 4) (d := 10) (a := 27182818286)
    (c := 6) (k := 7193) (by norm_num) exp_9715_le e_le (by decide +kernel)
  simpa using this

/-- p. 5: `exp(exp(11.503)) < 4 · 10^43000`. PROVED. -/
theorem chenWang1989_bound : Real.exp (Real.exp 11.503) < 4 * 10 ^ 43000 := by
  have := exp_lt_of (x := Real.exp 11.503) (m := 198025) (q := 2) (d := 10)
    (a := 27182818286) (c := 4) (k := 43000) (by norm_num) exp_11503_le e_le (by decide +kernel)
  simpa using this

/-- `2 · 10^1346 < e^3100`: the overview's `C = 2 · 10^1346` for Liu-Wang is smaller,
so stronger, than Liu-Wang's printed `e^3100`. PROVED. -/
theorem liuWang_rounding : (2 : ℝ) * 10 ^ 1346 < Real.exp 3100 := by
  have := lt_exp_of (m := 3100) (d := 10) (a := 27182818283) (c := 2) (k := 1346) e_ge
    (by decide +kernel)
  simpa using this

/-! #### Links between thresholds -/

/-- Helfgott's `10^27` gives the overview's form of Liu-Wang. -/
theorem liuWangAsStated_of_helfgott (h : TernaryAbove (10 ^ 27)) : LiuWangAsStated := by
  refine ternaryAbove_mono ?_ h
  have : (10 : ℝ) ^ 27 ≤ 10 ^ 1346 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ≤ 10 ^ 1346 := by positivity
  exact this.trans (le_mul_of_one_le_left h0 (by norm_num))

/-- The overview's form of Liu-Wang implies Liu-Wang's printed `e^3100`. -/
theorem liuWang_of_asStated (h : LiuWangAsStated) : TernaryAbove (Real.exp 3100) :=
  ternaryAbove_mono liuWang_rounding.le h

/-- Chen-Wang 1996 implies Chen-Wang 1989. -/
theorem chenWang1989_of_1996 (h : TernaryAbove (Real.exp (Real.exp 9.715))) : ChenWang1989 :=
  ternaryAbove_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))) h

/-- Chen-Wang 1989 implies Borozdkin 1956. -/
theorem borozdkin1956_of_chenWang (h : ChenWang1989) : Borozdkin1956 :=
  ternaryAbove_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))) h

theorem le_exp_4196 : (16.038 : ℝ) ≤ Real.exp 41.96 := by
  have := Real.add_one_le_exp (41.96 : ℝ); linarith

/-- Borozdkin 1956 implies Borozdkin 1939. -/
theorem borozdkin1939_of_1956 (h : Borozdkin1956) : Borozdkin1939 :=
  ternaryAbove_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr le_exp_4196)) h

/-- The whole historical chain of explicit constants from Helfgott's `10^27`. -/
theorem history_of_helfgott (h : TernaryAbove (10 ^ 27)) :
    TernaryAbove (10 ^ 29) ∧ LiuWangAsStated ∧ ChenWang1989 ∧ Borozdkin1956 ∧ Borozdkin1939 := by
  have h1 := liuWangAsStated_of_helfgott h
  have h2 := chenWang_of_liuWang (liuWang_of_asStated h1)
  have h3 := chenWang1989_of_1996 h2
  have h4 := borozdkin1956_of_chenWang h3
  exact ⟨may2013_of_dec2013 h, h1, h3, h4, borozdkin1939_of_1956 h4⟩

/-! ### Results under GRH, p. 5 -/

/-- Effinger's analysis of Hardy-Littlewood, under GRH: every odd `n ≥ 1.24 · 10^50`. -/
def Effinger1999 : Prop := LeanLab.DERZ1997.GRH → TernaryAbove (1.24e50)

/-- Lucke 1926, under GRH: every odd `n ≥ 10^32`. -/
def Lucke1926 : Prop := LeanLab.DERZ1997.GRH → TernaryAbove (10 ^ 32)

/-- Zinoviev's `10^20`, already cited in the lab, gives Lucke's `10^32`. -/
theorem lucke_of_zinoviev
    (hZ : LeanLab.DERZ1997.GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n) :
    Lucke1926 := by
  intro hG n ho hn
  refine hZ hG n ho ?_
  have : ((10 : ℕ) ^ 20 : ℝ) < n := by push_cast; linarith [show (10 : ℝ) ^ 20 < 10 ^ 32 by norm_num]
  exact_mod_cast this

/-- Lucke's `10^32` gives Effinger's `1.24 · 10^50`. -/
theorem effinger_of_lucke (h : Lucke1926) : Effinger1999 :=
  fun hG => ternaryAbove_mono (by norm_num) (h hG)

theorem lucke : Lucke1926 := lucke_of_zinoviev LeanLab.DERZ1997.zinoviev
theorem effinger : Effinger1999 := effinger_of_lucke lucke

/-! ### The toy example, p. 3 -/

/-- If `f(n) = n^2` and `g(n) = 100 n^(3/2)`, then `f(n) > g(n)` for `n > 10^4`. -/
theorem toy_example (x : ℝ) (hx : 10 ^ 4 < x) : 100 * x ^ (3 / 2 : ℝ) < x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hs : x ^ (2 : ℝ) = x ^ (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have h100 : (100 : ℝ) < x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.lt_sqrt (by norm_num)]; linarith
  have hp : 0 < x ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  rw [← Real.rpow_natCast x 2]; push_cast; rw [hs]
  nlinarith

end LeanLab.HelfgottOverview
