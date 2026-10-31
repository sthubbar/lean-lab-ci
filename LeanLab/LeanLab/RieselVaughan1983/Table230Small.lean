/-
P0032 Riesel-Vaughan 1983, (2.30) and (2.31), page 48, three of the four computed values.
Unit U-6715, CLOUD 20261020T1816Z-cloud48, track T1. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

PROVED unconditional, by kernel computation, no `native_decide`:
* `tu79_eq`: `T(79) = 1683789818/5124735 ≈ 328.5613438`, so `t_79_le`: `T(79) ≤ 328.5614`.
* `s79`: `s(79) = 21`.
* `s99989`: `s(99989) = 9590`, by a trial division count against the 65 primes below 317,
  with `isP_iff` proving the test equals `Nat.Prime` below `317² = 100489`.
* `Tu_eq_TuQ`: the general bridge `T(u) = TuQ u`, a computable rational sum, valid for every `u`.
NOT proved: `T(99989) ≤ 80096031`, the Prop `Table230Big`; it is about 4.6·10⁷ pairs and the
margin in (6.8) is only about 2400 out of 8·10⁷, so no crude bound will do.
-/
import LeanLab.RieselVaughan1983.Lemma8

open Finset

namespace LeanLab.RieselVaughan1983.Table230Small

open LeanLab.RieselVaughan1983

/-! ### The weight through odd primes up to `u` -/

/-- For `0 < d ≤ u` the odd prime factors of `d` are the odd primes up to `u` dividing `d`. -/
lemma oddFactors_eq {u d : ℕ} (hd : 0 < d) (hdu : d ≤ u) :
    d.primeFactors.filter (2 < ·) = (oddPrimes u).filter (· ∣ d) := by
  ext p
  simp only [mem_filter, Nat.mem_primeFactors, mem_oddPrimes]
  constructor
  · rintro ⟨⟨hp, hpd, -⟩, h2⟩
    exact ⟨⟨by omega, (Nat.le_of_dvd hd hpd).trans hdu, hp⟩, hpd⟩
  · rintro ⟨⟨h3, -, hp⟩, hpd⟩
    exact ⟨⟨hp, hpd, by omega⟩, by omega⟩

/-- The computable rational form of `T(u)`, (2.27). -/
def TuQ (u : ℕ) : ℚ :=
  ∑ a ∈ oddPrimes u, ∑ b ∈ (oddPrimes u).filter (a < ·),
    ∏ p ∈ (oddPrimes u).filter (· ∣ (b - a)), (((p : ℚ) - 1) / ((p : ℚ) - 2))

/-- `T(u) = TuQ u` for every `u`. -/
theorem Tu_eq_TuQ (u : ℕ) : Tu u = (TuQ u : ℝ) := by
  unfold Tu TuQ
  push_cast
  refine sum_congr rfl (fun a ha => ?_)
  refine sum_congr (by ext b; simp) (fun b hb => ?_)
  rw [mem_filter, mem_oddPrimes] at hb
  rw [mem_oddPrimes] at ha
  unfold wt
  rw [oddFactors_eq (u := u) (by omega) (by omega)]

/-! ### `u = 79` -/

lemma oddPrimes79 : oddPrimes 79 =
    {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79} := by
  decide

/-- (2.31), first value: `s(79) = 21`. -/
theorem s79 : #(oddPrimes 79) = 21 := by rw [oddPrimes79]; rfl

/-- `T(79)` exactly. -/
theorem tuQ79 : TuQ 79 = 1683789818 / 5124735 := by
  unfold TuQ; rw [oddPrimes79]; decide +kernel

theorem tu79_eq : Tu 79 = 1683789818 / 5124735 := by
  rw [Tu_eq_TuQ, tuQ79]; push_cast; ring

/-- (2.30), first value: `T(79) ≤ 328.5614`. -/
theorem t_79_le : Tu 79 ≤ 3285614 / 10000 := by
  rw [tu79_eq]; norm_num

/-! ### `s(99989)` by trial division -/

/-- `true` when no listed `p` with `p² ≤ n` divides `n`; the list is ascending. -/
def noDiv (n : ℕ) : List ℕ → Bool
  | [] => true
  | p :: ps => if n < p * p then true else if n % p = 0 then false else noDiv n ps

/-- The primes below 317. -/
def smallPrimes : List ℕ :=
  (List.range' 2 315).filter (fun k => (List.range' 2 (k - 2)).all (fun m => k % m != 0))

/-- Trial division primality test, correct below `317²`. -/
def isP (n : ℕ) : Bool := 2 ≤ n && noDiv n smallPrimes

/-- Count of `isP` on `[lo, lo + len)`, added to `acc`. -/
def cnt : ℕ → ℕ → ℕ → ℕ
  | _, 0, acc => acc
  | lo, len + 1, acc => cnt (lo + 1) len (if isP lo then acc + 1 else acc)

lemma smallPrimes_prime : ∀ p ∈ smallPrimes, p.Prime := by decide +kernel

lemma smallPrimes_complete : ∀ p < 317, p.Prime → p ∈ smallPrimes := by decide +kernel

lemma smallPrimes_sorted : smallPrimes.Pairwise (· < ·) := by decide +kernel

lemma noDiv_spec (n : ℕ) (l : List ℕ) (hs : l.Pairwise (· < ·)) :
    noDiv n l = true ↔ ∀ p ∈ l, p * p ≤ n → ¬ p ∣ n := by
  induction l with
  | nil => simp [noDiv]
  | cons p ps ih =>
    rw [List.pairwise_cons] at hs
    have ih := ih hs.2
    unfold noDiv
    by_cases h1 : n < p * p
    · simp only [h1, if_true, true_iff, List.mem_cons]
      rintro q (rfl | hq) hqq
      · omega
      · have := hs.1 q hq
        have : p * p < q * q := Nat.mul_lt_mul'' this this
        omega
    · simp only [h1, if_false]
      by_cases h2 : n % p = 0
      · simp only [h2, if_true, Bool.false_eq_true, false_iff, not_forall, List.mem_cons]
        exact ⟨p, Or.inl rfl, by omega, not_not.mpr (Nat.dvd_of_mod_eq_zero h2)⟩
      · simp only [h2, if_false, ih, List.mem_cons]
        constructor
        · rintro h q (rfl | hq) hqq
          · exact fun hd => h2 (Nat.mod_eq_zero_of_dvd hd)
          · exact h q hq hqq
        · intro h q hq; exact h q (Or.inr hq)

/-- The trial division test is `Nat.Prime` below `317² = 100489`. -/
theorem isP_iff {n : ℕ} (hn : n < 100489) : isP n = true ↔ n.Prime := by
  unfold isP
  rw [Bool.and_eq_true, decide_eq_true_iff, noDiv_spec n _ smallPrimes_sorted]
  constructor
  · rintro ⟨h2, h⟩
    by_contra hnp
    have hn1 : n ≠ 1 := by omega
    have hm := Nat.minFac_prime hn1
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hle : n.minFac < 317 := by
      by_contra hc
      have : 317 * 317 ≤ n.minFac ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
      omega
    exact h _ (smallPrimes_complete _ hle hm) (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd n)
  · intro hp
    refine ⟨hp.two_le, fun q hq hqq hqd => ?_⟩
    have hqp := smallPrimes_prime q hq
    rcases (Nat.dvd_prime hp).1 hqd with h | h
    · exact hqp.one_lt.ne' h
    · subst h
      have := hp.two_le
      have : q * 2 ≤ q * q := Nat.mul_le_mul_left q this
      omega

lemma cnt_spec (lo len acc : ℕ) (h : lo + len ≤ 100489) :
    cnt lo len acc = acc + #((Ico lo (lo + len)).filter Nat.Prime) := by
  induction len generalizing lo acc with
  | zero => simp [cnt]
  | succ len ih =>
    unfold cnt
    rw [ih (lo + 1) _ (by omega)]
    have e : Ico lo (lo + (len + 1)) = insert lo (Ico (lo + 1) (lo + 1 + len)) := by
      ext x; simp only [mem_insert, mem_Ico]; omega
    rw [e, filter_insert]
    have hnot : lo ∉ (Ico (lo + 1) (lo + 1 + len)).filter Nat.Prime := by simp
    by_cases hp : lo.Prime
    · have : isP lo = true := (isP_iff (by omega)).2 hp
      rw [if_pos this, if_pos hp, card_insert_of_notMem hnot]; ring
    · have : ¬ isP lo = true := fun h => hp ((isP_iff (by omega)).1 h)
      rw [if_neg this, if_neg hp]

/- Chunks of 2000: a single chunk of 10000 costs the kernel over 1 GB more memory. -/
set_option Elab.async false

lemma cnt_add (a b lo acc : ℕ) : cnt lo (a + b) acc = cnt (lo + a) b (cnt lo a acc) := by
  induction a generalizing lo acc with
  | zero => simp [cnt]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [cnt]
    rw [ih, show lo + 1 + a = lo + (a + 1) by omega]

lemma cnt_split {lo a b acc lo' len : ℕ} (h1 : lo' = lo + a) (h2 : len = a + b) :
    cnt lo len acc = cnt lo' b (cnt lo a acc) := by
  rw [h1, h2, cnt_add]

set_option maxRecDepth 100000 in
lemma cnt_c0 : cnt 3 1997 0 = 302 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c1 : cnt 2000 2000 302 = 549 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c2 : cnt 4000 2000 549 = 782 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c3 : cnt 6000 2000 782 = 1006 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c4 : cnt 8000 2000 1006 = 1228 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c5 : cnt 10000 2000 1228 = 1437 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c6 : cnt 12000 2000 1437 = 1651 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c7 : cnt 14000 2000 1651 = 1861 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c8 : cnt 16000 2000 1861 = 2063 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c9 : cnt 18000 2000 2063 = 2261 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c10 : cnt 20000 2000 2261 = 2463 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c11 : cnt 22000 2000 2463 = 2667 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c12 : cnt 24000 2000 2667 = 2859 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c13 : cnt 26000 2000 2859 = 3054 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c14 : cnt 28000 2000 3054 = 3244 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c15 : cnt 30000 2000 3244 = 3431 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c16 : cnt 32000 2000 3431 = 3637 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c17 : cnt 34000 2000 3637 = 3823 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c18 : cnt 36000 2000 3823 = 4016 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c19 : cnt 38000 2000 4016 = 4202 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c20 : cnt 40000 2000 4202 = 4391 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c21 : cnt 42000 2000 4391 = 4578 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c22 : cnt 44000 2000 4578 = 4760 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c23 : cnt 46000 2000 4760 = 4945 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c24 : cnt 48000 2000 4945 = 5132 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c25 : cnt 50000 2000 5132 = 5318 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c26 : cnt 52000 2000 5318 = 5499 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c27 : cnt 54000 2000 5499 = 5682 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c28 : cnt 56000 2000 5682 = 5872 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c29 : cnt 58000 2000 5872 = 6056 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c30 : cnt 60000 2000 6056 = 6231 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c31 : cnt 62000 2000 6231 = 6412 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c32 : cnt 64000 2000 6412 = 6590 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c33 : cnt 66000 2000 6590 = 6773 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c34 : cnt 68000 2000 6773 = 6934 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c35 : cnt 70000 2000 6934 = 7127 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c36 : cnt 72000 2000 7127 = 7300 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c37 : cnt 74000 2000 7300 = 7483 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c38 : cnt 76000 2000 7483 = 7661 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c39 : cnt 78000 2000 7661 = 7836 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c40 : cnt 80000 2000 7836 = 8016 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c41 : cnt 82000 2000 8016 = 8189 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c42 : cnt 84000 2000 8189 = 8361 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c43 : cnt 86000 2000 8361 = 8542 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c44 : cnt 88000 2000 8542 = 8712 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c45 : cnt 90000 2000 8712 = 8886 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c46 : cnt 92000 2000 8886 = 9069 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c47 : cnt 94000 2000 9069 = 9251 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c48 : cnt 96000 2000 9251 = 9417 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cnt_c49 : cnt 98000 1990 9417 = 9590 := by decide +kernel

lemma cnt_99989 : cnt 3 99987 0 = 9590 := by
  rw [cnt_split (lo := 3) (a := 1997) (b := 97990) (lo' := 2000) (len := 99987) rfl rfl,
    cnt_c0]
  rw [cnt_split (lo := 2000) (a := 2000) (b := 95990) (lo' := 4000) (len := 97990) rfl rfl,
    cnt_c1]
  rw [cnt_split (lo := 4000) (a := 2000) (b := 93990) (lo' := 6000) (len := 95990) rfl rfl,
    cnt_c2]
  rw [cnt_split (lo := 6000) (a := 2000) (b := 91990) (lo' := 8000) (len := 93990) rfl rfl,
    cnt_c3]
  rw [cnt_split (lo := 8000) (a := 2000) (b := 89990) (lo' := 10000) (len := 91990) rfl rfl,
    cnt_c4]
  rw [cnt_split (lo := 10000) (a := 2000) (b := 87990) (lo' := 12000) (len := 89990) rfl rfl,
    cnt_c5]
  rw [cnt_split (lo := 12000) (a := 2000) (b := 85990) (lo' := 14000) (len := 87990) rfl rfl,
    cnt_c6]
  rw [cnt_split (lo := 14000) (a := 2000) (b := 83990) (lo' := 16000) (len := 85990) rfl rfl,
    cnt_c7]
  rw [cnt_split (lo := 16000) (a := 2000) (b := 81990) (lo' := 18000) (len := 83990) rfl rfl,
    cnt_c8]
  rw [cnt_split (lo := 18000) (a := 2000) (b := 79990) (lo' := 20000) (len := 81990) rfl rfl,
    cnt_c9]
  rw [cnt_split (lo := 20000) (a := 2000) (b := 77990) (lo' := 22000) (len := 79990) rfl rfl,
    cnt_c10]
  rw [cnt_split (lo := 22000) (a := 2000) (b := 75990) (lo' := 24000) (len := 77990) rfl rfl,
    cnt_c11]
  rw [cnt_split (lo := 24000) (a := 2000) (b := 73990) (lo' := 26000) (len := 75990) rfl rfl,
    cnt_c12]
  rw [cnt_split (lo := 26000) (a := 2000) (b := 71990) (lo' := 28000) (len := 73990) rfl rfl,
    cnt_c13]
  rw [cnt_split (lo := 28000) (a := 2000) (b := 69990) (lo' := 30000) (len := 71990) rfl rfl,
    cnt_c14]
  rw [cnt_split (lo := 30000) (a := 2000) (b := 67990) (lo' := 32000) (len := 69990) rfl rfl,
    cnt_c15]
  rw [cnt_split (lo := 32000) (a := 2000) (b := 65990) (lo' := 34000) (len := 67990) rfl rfl,
    cnt_c16]
  rw [cnt_split (lo := 34000) (a := 2000) (b := 63990) (lo' := 36000) (len := 65990) rfl rfl,
    cnt_c17]
  rw [cnt_split (lo := 36000) (a := 2000) (b := 61990) (lo' := 38000) (len := 63990) rfl rfl,
    cnt_c18]
  rw [cnt_split (lo := 38000) (a := 2000) (b := 59990) (lo' := 40000) (len := 61990) rfl rfl,
    cnt_c19]
  rw [cnt_split (lo := 40000) (a := 2000) (b := 57990) (lo' := 42000) (len := 59990) rfl rfl,
    cnt_c20]
  rw [cnt_split (lo := 42000) (a := 2000) (b := 55990) (lo' := 44000) (len := 57990) rfl rfl,
    cnt_c21]
  rw [cnt_split (lo := 44000) (a := 2000) (b := 53990) (lo' := 46000) (len := 55990) rfl rfl,
    cnt_c22]
  rw [cnt_split (lo := 46000) (a := 2000) (b := 51990) (lo' := 48000) (len := 53990) rfl rfl,
    cnt_c23]
  rw [cnt_split (lo := 48000) (a := 2000) (b := 49990) (lo' := 50000) (len := 51990) rfl rfl,
    cnt_c24]
  rw [cnt_split (lo := 50000) (a := 2000) (b := 47990) (lo' := 52000) (len := 49990) rfl rfl,
    cnt_c25]
  rw [cnt_split (lo := 52000) (a := 2000) (b := 45990) (lo' := 54000) (len := 47990) rfl rfl,
    cnt_c26]
  rw [cnt_split (lo := 54000) (a := 2000) (b := 43990) (lo' := 56000) (len := 45990) rfl rfl,
    cnt_c27]
  rw [cnt_split (lo := 56000) (a := 2000) (b := 41990) (lo' := 58000) (len := 43990) rfl rfl,
    cnt_c28]
  rw [cnt_split (lo := 58000) (a := 2000) (b := 39990) (lo' := 60000) (len := 41990) rfl rfl,
    cnt_c29]
  rw [cnt_split (lo := 60000) (a := 2000) (b := 37990) (lo' := 62000) (len := 39990) rfl rfl,
    cnt_c30]
  rw [cnt_split (lo := 62000) (a := 2000) (b := 35990) (lo' := 64000) (len := 37990) rfl rfl,
    cnt_c31]
  rw [cnt_split (lo := 64000) (a := 2000) (b := 33990) (lo' := 66000) (len := 35990) rfl rfl,
    cnt_c32]
  rw [cnt_split (lo := 66000) (a := 2000) (b := 31990) (lo' := 68000) (len := 33990) rfl rfl,
    cnt_c33]
  rw [cnt_split (lo := 68000) (a := 2000) (b := 29990) (lo' := 70000) (len := 31990) rfl rfl,
    cnt_c34]
  rw [cnt_split (lo := 70000) (a := 2000) (b := 27990) (lo' := 72000) (len := 29990) rfl rfl,
    cnt_c35]
  rw [cnt_split (lo := 72000) (a := 2000) (b := 25990) (lo' := 74000) (len := 27990) rfl rfl,
    cnt_c36]
  rw [cnt_split (lo := 74000) (a := 2000) (b := 23990) (lo' := 76000) (len := 25990) rfl rfl,
    cnt_c37]
  rw [cnt_split (lo := 76000) (a := 2000) (b := 21990) (lo' := 78000) (len := 23990) rfl rfl,
    cnt_c38]
  rw [cnt_split (lo := 78000) (a := 2000) (b := 19990) (lo' := 80000) (len := 21990) rfl rfl,
    cnt_c39]
  rw [cnt_split (lo := 80000) (a := 2000) (b := 17990) (lo' := 82000) (len := 19990) rfl rfl,
    cnt_c40]
  rw [cnt_split (lo := 82000) (a := 2000) (b := 15990) (lo' := 84000) (len := 17990) rfl rfl,
    cnt_c41]
  rw [cnt_split (lo := 84000) (a := 2000) (b := 13990) (lo' := 86000) (len := 15990) rfl rfl,
    cnt_c42]
  rw [cnt_split (lo := 86000) (a := 2000) (b := 11990) (lo' := 88000) (len := 13990) rfl rfl,
    cnt_c43]
  rw [cnt_split (lo := 88000) (a := 2000) (b := 9990) (lo' := 90000) (len := 11990) rfl rfl,
    cnt_c44]
  rw [cnt_split (lo := 90000) (a := 2000) (b := 7990) (lo' := 92000) (len := 9990) rfl rfl,
    cnt_c45]
  rw [cnt_split (lo := 92000) (a := 2000) (b := 5990) (lo' := 94000) (len := 7990) rfl rfl,
    cnt_c46]
  rw [cnt_split (lo := 94000) (a := 2000) (b := 3990) (lo' := 96000) (len := 5990) rfl rfl,
    cnt_c47]
  rw [cnt_split (lo := 96000) (a := 2000) (b := 1990) (lo' := 98000) (len := 3990) rfl rfl,
    cnt_c48]
  exact cnt_c49

/-- (2.31), second value: `s(99989) = 9590`. -/
theorem s99989 : #(oddPrimes 99989) = 9590 := by
  have e : oddPrimes 99989 = (Ico 3 (3 + 99987)).filter Nat.Prime := by
    ext p
    simp only [oddPrimes, mem_filter, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  have h : cnt 3 99987 0 = 0 + #((Ico 3 (3 + 99987)).filter Nat.Prime) :=
    cnt_spec 3 99987 0 (by norm_num)
  calc #(oddPrimes 99989) = 0 + #((Ico 3 (3 + 99987)).filter Nat.Prime) := by
        rw [e, Nat.zero_add]
    _ = cnt 3 99987 0 := h.symm
    _ = 9590 := cnt_99989

/-! ### `Table230` with only `T(99989)` left cited -/

/-- (2.30), second value, CITED, the paper's computation; reproduced in Python by
`T_check.py`. -/
def Table230Big : Prop := Tu 99989 ≤ 80096031

/-- `Table230` CONDITIONAL ON `Table230Big` only. -/
theorem table230_of_big (h : Table230Big) : Table230 :=
  ⟨t_79_le, h, s79, s99989⟩

end LeanLab.RieselVaughan1983.Table230Small
