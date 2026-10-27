/-
P0022 Kaniecki 1995, Theorem, even half, in the lab's RH form
`SchnirelmannBounds.kaniecki_even_RH_of`: under RH every even n is a sum of at most four
primes. PROVED here CONDITIONAL ON the three cited inputs of `ChirreHagen2025.goldbach_10`
and Liu-Wang 2002, `Ternary.liuWang`'s type; neither Kaniecki's Lemmas 4 to 7 nor the 1476
gap table is used. Route: 4 ≤ n ≤ 4 · 10^18 by the even Goldbach check; n - 3 ≥ e^3100 by
Liu-Wang, n = 3 + three primes; in between, goldbach_10 at x = n - 4 - 10 log² n gives a
Goldbach number g with n - g even and 4 < n - g < 4 + 10 log² n ≤ 10^8, so n - g is a sum of
two primes by the check. `kaniecki_odd_of_inputs'` then gives the odd half as 3 plus an even
number, without the 1476 gap table. Unit U-1065, PC run 20261019T1204Z-858.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.KanieckiGap.Assembly

namespace LeanLab.KanieckiGap
open Real LeanLab.SchnirelmannConstant

theorem atMost2_of_goldbachSum {m : ℕ} (h : IsGoldbachSum m) : AtMostPrimes 2 m := by
  obtain ⟨p, q, hp, hq, rfl⟩ := h
  exact (AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)

/-- `log n ≤ 3101` when `n < e^3100 + 3`. -/
theorem log_le_3101 {n : ℕ} (hn : 0 < n) (h : (n : ℝ) < Real.exp 3100 + 3) :
    Real.log n ≤ 3101 := by
  have h1 : (1 : ℝ) ≤ Real.exp 3100 := Real.one_le_exp (by norm_num)
  have h2 : Real.exp 3100 + 3 ≤ Real.exp 3101 := by
    have : Real.exp 3101 = Real.exp 3100 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have he : (2.7 : ℝ) ≤ Real.exp 1 := (Real.exp_one_gt_d9).le.trans' (by norm_num)
    have h3 : (3101 : ℝ) ≤ Real.exp 3100 := by
      have := Real.add_one_le_exp (3100 : ℝ); linarith
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ Real.exp 3100)]
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc Real.log n ≤ Real.log (Real.exp 3101) := Real.log_le_log hpos (by linarith)
    _ = 3101 := Real.log_exp _

/-- **Every even number is a sum of at most four primes**, CONDITIONAL ON `G10`, even Goldbach
to `4 · 10^18` and Liu-Wang. -/
theorem even_atMost4_of (hG10 : G10) (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100)) :
    ∀ n : ℕ, Even n → AtMostPrimes 4 n := by
  intro n hn
  rcases Nat.lt_or_ge n 4 with hs | h4
  · -- n = 0 or n = 2
    obtain ⟨k, rfl⟩ := hn
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · exact AtMostPrimes.zero.mono (by norm_num)
    · exact (AtMostPrimes.prime Nat.prime_two).mono (by norm_num)
  rcases le_or_gt n (4 * 10 ^ 18) with hsmall | hbig
  · exact (atMost2_of_goldbachSum (hE n hn h4 hsmall)).mono (by norm_num)
  have hnR : (4 * 10 ^ 18 : ℝ) < n := by exact_mod_cast hbig
  rcases le_or_gt (Real.exp 3100) ((n : ℝ) - 3) with hlarge | hmid
  · -- n - 3 is odd and at least e^3100
    have hodd : Odd (n - 3) := by
      obtain ⟨k, hk⟩ := hn
      exact ⟨k - 2, by omega⟩
    have hcast : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    obtain ⟨p, q, r, hp, hq, hr, hsum⟩ := hLW (n - 3) hodd (by rw [hcast]; exact hlarge)
    have : n = 3 + (p + q + r) := by omega
    rw [this]
    exact ((AtMostPrimes.prime Nat.prime_three).add (((AtMostPrimes.prime hp).add
      (AtMostPrimes.prime hq)).add (AtMostPrimes.prime hr))).mono (by norm_num)
  · -- the middle range
    have hn0 : 0 < n := by omega
    have hL : Real.log n ≤ 3101 := log_le_3101 hn0 (by linarith)
    have hL0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hL2 : Real.log n ^ 2 ≤ 3101 ^ 2 := pow_le_pow_left₀ hL0 hL 2
    set x : ℝ := (n : ℝ) - 4 - 10 * Real.log n ^ 2 with hx
    have hx2 : 2 ≤ x := by rw [hx]; nlinarith
    obtain ⟨g, ⟨p, q, hp, hq, op, oq, hg⟩, hlo, hhi⟩ := hG10 x hx2
    have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hlx : Real.log x ≤ Real.log n := Real.log_le_log (by linarith) (by rw [hx]; nlinarith)
    have hsq : Real.log x ^ 2 ≤ Real.log n ^ 2 := pow_le_pow_left₀ hlx0 hlx 2
    have hgR : (g : ℝ) < (n : ℝ) - 4 := by rw [hx] at hhi; linarith
    have hgR' : (n : ℝ) - 4 - 10 * 3101 ^ 2 < g := by rw [hx] at hlo; nlinarith
    have hg4 : g + 4 < n := by exact_mod_cast (show (g : ℝ) + 4 < n by linarith)
    have hgm : n - g ≤ 100000000 := by
      have : (n : ℝ) < g + 100000000 := by nlinarith
      have : n < g + 100000000 := by exact_mod_cast this
      omega
    have hgeven : Even g := by rw [← hg]; exact op.add_odd oq
    have hmeven : Even (n - g) := by
      obtain ⟨a, ha⟩ := hn; obtain ⟨b, hb⟩ := hgeven; exact ⟨a - b, by omega⟩
    have hm : IsGoldbachSum (n - g) := hE (n - g) hmeven (by omega) (by omega)
    have h' : AtMostPrimes ((1 + 1) + 2) ((p + q) + (n - g)) :=
      ((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add (atMost2_of_goldbachSum hm)
    have e : (p + q) + (n - g) = n := by omega
    rw [e] at h'
    exact h'.mono (by norm_num)

/-- **Kaniecki 1995, even half, RH form, from goldbach_10's inputs and Liu-Wang.** -/
theorem kaniecki_even_of_inputs
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      LeanLab.ChirreHagen2025.Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hS : RiemannHypothesis → LeanLab.ChirreHagen2025.SchoenfeldTheta)
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100)) :
    RiemannHypothesis → ∀ n : ℕ, Even n → AtMostPrimes 4 n := fun hRH =>
  even_atMost4_of (LeanLab.ChirreHagen2025.goldbach_10 h2 hE hS hRH) hE hLW

/-- **Kaniecki 1995, odd half, without the gap table**: odd `n > 1` is `3` plus an even number,
so `even_atMost4_of` gives at most five primes. CONDITIONAL ON goldbach_10's three inputs and
Liu-Wang only; `kaniecki_odd_of_inputs` in Assembly.lean also took `GapBound1476`. -/
theorem kaniecki_odd_of_inputs'
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      LeanLab.ChirreHagen2025.Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hS : RiemannHypothesis → LeanLab.ChirreHagen2025.SchoenfeldTheta)
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100)) :
    RiemannHypothesis → ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := by
  intro hRH n ho h1
  have hev : Even (n - 3) := by obtain ⟨k, hk⟩ := ho; exact ⟨k - 1, by omega⟩
  have h4 := kaniecki_even_of_inputs h2 hE hS hLW hRH (n - 3) hev
  have h' : AtMostPrimes (1 + 4) (3 + (n - 3)) := (AtMostPrimes.prime Nat.prime_three).add h4
  have e : 3 + (n - 3) = n := by obtain ⟨k, hk⟩ := ho; omega
  rw [e] at h'
  exact h'

end LeanLab.KanieckiGap

#print axioms LeanLab.KanieckiGap.atMost2_of_goldbachSum
#print axioms LeanLab.KanieckiGap.log_le_3101
#print axioms LeanLab.KanieckiGap.even_atMost4_of
#print axioms LeanLab.KanieckiGap.kaniecki_even_of_inputs
#print axioms LeanLab.KanieckiGap.kaniecki_odd_of_inputs'
