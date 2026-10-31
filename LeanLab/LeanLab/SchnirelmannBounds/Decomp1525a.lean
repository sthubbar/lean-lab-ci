/-
Unit U-1525, run 20261025T2003Z-426, DECOMPOSE. P0066 R. C. Vaughan 1977, On the estimation of
Schnirelman's constant, J. reine angew. Math. 290, 93-108, read from copies/P0066.pdf (page
images 95, 97, 98, 99, 100, 101, 103, 104).

File a of three: the Euler-product constants of Lemma 1 (p. 95) and the arithmetic function g of
(3.3) (p. 97), the inputs of the sieve bound Lemma 8 (file b) and of the second-moment step
(5.10), whose numeric Euler bounds `EulerMassBound` and `EulerMomentBound` in
Vaughan1977Euler.lean are OPEN.

Route as Vaughan runs Schnirelmann's argument, and where each step lives:
* sieve upper bound for the representation count: Lemma 8, OPEN, split in Decomp1525b;
* second moment: Vaughan replaces Schnirelmann's Σ r(n)² by the Hölder moment
  Σ F(n) Π ((p-1)/(p-2))^{11/4}, (5.5)-(5.10); the bookkeeping is PROVED in the folder, the
  numeric Euler inputs (2.11), (2.12) are split here;
* first moment: Lemma 11, Ψ(x) ~ x²/log x, its `DistributionError` is split in Decomp1525c;
* Hölder in place of Cauchy-Schwarz, (5.4)-(5.5): PROVED, Vaughan1977Eq55.lean;
* density to basis: PROVED, Vaughan1977.lean through the lab's Mann theorem.
The classical Cauchy-Schwarz route with explicit constants is already PROVED in the lab's
SchnirelmannGoldbach folder (29920 primes), so it is not decomposed again here.

Only Mathlib and the Mathlib-only module Vaughan1977Eq56 are imported. `Cv` is the same
expression as `LeanLab.ChenExplicit.twinC`, the paper's C of (2.5).

AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SchnirelmannBounds.Vaughan1977Eq56

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Decomp1525a
open LeanLab.SchnirelmannBounds.Vaughan1977Eq56

/-- `s(q)`, p. 97: the squarefree kernel `Π_{p | q} p`. -/
def sk (q : ℕ) : ℕ := ∏ p ∈ q.primeFactors, p

/-- The local value `g(p^m)` of (3.3): `0` at `p = 2` and at `m = 1`, else `2^{m-2} p^{-m}`. -/
def gloc (p m : ℕ) : ℝ := if p = 2 ∨ m = 1 then 0 else (2 : ℝ) ^ (m - 2) / (p : ℝ) ^ m

/-- The multiplicative function `g` of (3.3), p. 97, with `g(0) = 0`. -/
def g (d : ℕ) : ℝ := if d = 0 then 0 else ∏ p ∈ d.primeFactors, gloc p (d.factorization p)

/-- `C` of (2.5): `Π_{p>2} p(p-2)/(p-1)² = Π_{p>2} (1 - 1/(p-1)²)`, the lab's `twinC`. -/
def Cv : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- `Γ` of (2.3): `Σ_{p>2} log p/(p-1)²`. -/
def Gam : ℝ := ∑' p : {p : ℕ // p.Prime ∧ 2 < p}, Real.log p / ((p : ℝ) - 1) ^ 2

/-- `C₀` of (2.4): `Π_{p>2} (1 + 1/(p^{1/2}(p-2)))`. -/
def C0v : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 + 1 / (Real.sqrt p * ((p : ℝ) - 2)))

theorem gloc_nonneg (p m : ℕ) : 0 ≤ gloc p m := by
  unfold gloc; split_ifs <;> positivity

theorem g_nonneg (d : ℕ) : 0 ≤ g d := by
  unfold g; split_ifs
  · exact le_rfl
  · exact Finset.prod_nonneg (fun p _ => gloc_nonneg _ _)

theorem g_one : g 1 = 1 := by simp [g]

/-- The positive prime power values of the multiplicative function in equation 3.3, page 97. -/
theorem g_prime_pow {p m : ℕ} (hp : p.Prime) (hm : 0 < m) : g (p ^ m) = gloc p m := by
  rw [g, if_neg (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow hm.ne' hp,
    Finset.prod_singleton, Nat.factorization_pow_self hp]

example : g 9 = 1 / 9 := by
  have h := g_prime_pow (p := 3) (m := 2) Nat.prime_three (by norm_num)
  norm_num [gloc] at h
  exact h

/-- Multiplicativity of the function g specified on page 97, equation 3.3. -/
theorem g_mul {a b : ℕ} (hab : a.Coprime b) : g (a*b) = g a * g b := by
  by_cases ha : a = 0
  · simp [ha, g]
  by_cases hb : b = 0
  · simp [hb, g]
  rw [g, if_neg (mul_ne_zero ha hb), Nat.primeFactors_mul ha hb,
    Finset.prod_union hab.disjoint_primeFactors, g, if_neg ha, g, if_neg hb]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_of_coprime_left hab
      (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)]
  · apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_of_coprime_right hab
      (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)]

example : g (9 * 25) = g 9 * g 25 := g_mul (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The local Euler sum from equation 3.3 on page 97 and the page 100 product. -/
theorem hasSum_g_prime_power {p : ℕ} (hp : p.Prime) :
    HasSum (fun m : ℕ => g (p^m))
      (1 + if 2 < p then 1/((p : ℝ)*((p : ℝ)-2)) else 0) := by
  by_cases hp2 : 2 < p
  · rw [if_pos hp2]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
    have hr0 : 0 ≤ (2 : ℝ)/p := by positivity
    have hr1 : (2 : ℝ)/p < 1 := (div_lt_one hp0).mpr hp2r
    have hgeom := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1/(p : ℝ)^2)
    have he (m : ℕ) : (1/(p : ℝ)^2) * ((2 : ℝ)/p)^m = g (p^(m+2)) := by
      rw [g_prime_pow hp (by omega), gloc, if_neg (by omega), Nat.add_sub_cancel,
        div_pow, pow_add]
      field_simp
    have hden : (1 : ℝ)-2/p ≠ 0 := by linarith
    have ht : HasSum (fun m : ℕ => g (p^(m+2))) (1/((p : ℝ)*((p : ℝ)-2))) := by
      convert hgeom using 1
      · funext m
        exact (he m).symm
      · field_simp
    have hpr : g p = 0 := by
      have h := g_prime_pow (p := p) (m := 1) hp (by norm_num)
      simpa [gloc] using h
    have h := (hasSum_nat_add_iff (f := fun m : ℕ => g (p^m)) 2).mp ht
    simpa [Finset.sum_range_succ, g_one, hpr, add_comm] using h
  · have he : p = 2 := by have := hp.two_le; omega
    subst p
    have hs : HasSum (fun m : ℕ => g (2^m)) (g (2^0)) :=
      hasSum_single 0 (fun m hm => by
        rw [g_prime_pow Nat.prime_two (Nat.pos_of_ne_zero hm)]
        simp [gloc])
    simpa [g_one] using hs

example : HasSum (fun m : ℕ => g (3^m)) (4/3 : ℝ) := by
  have h := hasSum_g_prime_power Nat.prime_three
  norm_num at h
  exact h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The nonnegative convergence step for the page 100 Euler products. -/
theorem summable_of_prime_power_sums {f a : ℕ → ℝ} (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m*n) = f m*f n)
    (hn : ∀ n, 0 ≤ f n) (ha : ∀ n, 0 ≤ a n) (has : Summable a)
    (hl : ∀ p : ℕ, p.Prime → HasSum (fun m : ℕ => f (p^m)) (1+a p)) :
    Summable f := by
  classical
  apply summable_of_sum_range_le (c := Real.exp (∑' n, a n)) hn
  intro N
  have hloc {p : ℕ} (hp : p.Prime) : Summable (fun m : ℕ => ‖f (p^m)‖) := by
    have heq : (fun m : ℕ => ‖f (p^m)‖) = (fun m : ℕ => f (p^m)) := by
      funext m
      exact Real.norm_of_nonneg (hn _)
    rw [heq]
    exact (hl p hp).summable
  obtain ⟨_, hs⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    h1 hmul hloc N
  have hi : HasSum ((Nat.smoothNumbers N).indicator f)
      (∏ p ∈ N.primesBelow, ∑' m : ℕ, f (p^m)) := hasSum_subtype_iff_indicator.mp hs
  have hi0 (n : ℕ) : 0 ≤ (Nat.smoothNumbers N).indicator f n := by
    by_cases h : n ∈ Nat.smoothNumbers N
    · simp [h, hn n]
    · simp [h]
  calc ∑ n ∈ range N, f n = ∑ n ∈ range N, (Nat.smoothNumbers N).indicator f n := by
         apply Finset.sum_congr rfl
         intro n hnN
         by_cases hz : n = 0
         · subst n
           simp [Set.indicator_apply, h0]
         · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hz)
             (Finset.mem_range.mp hnN))]
       _ ≤ ∏ p ∈ N.primesBelow, ∑' m : ℕ, f (p^m) :=
         sum_le_hasSum _ (fun n _ => hi0 n) hi
       _ = ∏ p ∈ N.primesBelow, (1+a p) := by
         apply Finset.prod_congr rfl
         intro p hp
         exact (hl p (Nat.prime_of_mem_primesBelow hp)).tsum_eq
       _ ≤ Real.exp (∑ p ∈ N.primesBelow, a p) := Real.prod_one_add_le_exp_sum _ ha
       _ ≤ Real.exp (∑' n, a n) := Real.exp_le_exp.mpr
         (has.sum_le_tsum _ (fun n _ => ha n))

/-- The certified primes through 1000 used in the page 96 head split. -/
def headPrimes : Finset ℕ := {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997}
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Prime table certificate for the finite heads of equations 2.11 and 2.12, page 96. -/
theorem head_prime_table : (1000 : ℕ).primesLE = headPrimes := by
  ext p
  simp only [Nat.mem_primesLE, headPrimes, Finset.mem_insert, Finset.mem_singleton]
  by_cases hp : p ≤ 1000
  · have hp0 : 0 ≤ p := Nat.zero_le _
    interval_cases p <;> norm_num
  · constructor
    · exact fun h => (hp h.1).elim
    · intro h
      omega


example : 3 ∈ headPrimes := by
  rw [← head_prime_table]
  exact Nat.mem_primesLE.mpr ⟨by norm_num, Nat.prime_three⟩

/-- Rational certificate data for the page 96 head products through 1000.
Each numerator divided by 10^8 bounds the mass factor. -/
def headMassNumerator : ℕ → ℕ
  | 3 => 386358567
  | 5 => 130146955
  | 7 => 110850086
  | 11 => 103360820
  | 13 => 102252799
  | 17 => 101213784
  | 19 => 100945627
  | 23 => 100620335
  | 29 => 100375654
  | 31 => 100325712
  | 37 => 100223750
  | 41 => 100180263
  | 43 => 100163127
  | 47 => 100135448
  | 53 => 100105484
  | 59 => 100084465
  | 61 => 100078841
  | 67 => 100064969
  | 71 => 100057661
  | 73 => 100054461
  | 79 => 100046310
  | 83 => 100041852
  | 89 => 100036282
  | 97 => 100030432
  | 101 => 100028024
  | 103 => 100026926
  | 107 => 100024915
  | 109 => 100023993
  | 113 => 100022296
  | 127 => 100017583
  | 131 => 100016510
  | 137 => 100015076
  | 139 => 100014639
  | 149 => 100012716
  | 151 => 100012377
  | 157 => 100011438
  | 163 => 100010602
  | 167 => 100010094
  | 173 => 100009398
  | 179 => 100008772
  | 181 => 100008577
  | 191 => 100007694
  | 193 => 100007534
  | 197 => 100007228
  | 199 => 100007082
  | 211 => 100006292
  | 223 => 100005628
  | 227 => 100005430
  | 229 => 100005334
  | 233 => 100005151
  | 239 => 100004894
  | 241 => 100004812
  | 251 => 100004434
  | 257 => 100004228
  | 263 => 100004036
  | 269 => 100003856
  | 271 => 100003799
  | 277 => 100003635
  | 281 => 100003532
  | 283 => 100003482
  | 293 => 100003247
  | 307 => 100002955
  | 311 => 100002879
  | 313 => 100002843
  | 317 => 100002771
  | 331 => 100002540
  | 337 => 100002450
  | 347 => 100002310
  | 349 => 100002284
  | 353 => 100002232
  | 359 => 100002157
  | 367 => 100002064
  | 373 => 100001998
  | 379 => 100001935
  | 383 => 100001894
  | 389 => 100001836
  | 397 => 100001762
  | 401 => 100001727
  | 409 => 100001660
  | 419 => 100001581
  | 421 => 100001566
  | 431 => 100001494
  | 433 => 100001480
  | 439 => 100001440
  | 443 => 100001414
  | 449 => 100001376
  | 457 => 100001328
  | 461 => 100001305
  | 463 => 100001294
  | 467 => 100001272
  | 479 => 100001209
  | 487 => 100001169
  | 491 => 100001150
  | 499 => 100001114
  | 503 => 100001096
  | 509 => 100001070
  | 521 => 100001021
  | 523 => 100001013
  | 541 => 100000947
  | 547 => 100000926
  | 557 => 100000893
  | 563 => 100000874
  | 569 => 100000856
  | 571 => 100000850
  | 577 => 100000832
  | 587 => 100000804
  | 593 => 100000788
  | 599 => 100000772
  | 601 => 100000767
  | 607 => 100000752
  | 613 => 100000737
  | 617 => 100000727
  | 619 => 100000723
  | 631 => 100000695
  | 641 => 100000674
  | 643 => 100000670
  | 647 => 100000661
  | 653 => 100000649
  | 659 => 100000637
  | 661 => 100000634
  | 673 => 100000611
  | 677 => 100000604
  | 683 => 100000593
  | 691 => 100000580
  | 701 => 100000563
  | 709 => 100000551
  | 719 => 100000535
  | 727 => 100000524
  | 733 => 100000515
  | 739 => 100000507
  | 743 => 100000501
  | 751 => 100000491
  | 757 => 100000483
  | 761 => 100000478
  | 769 => 100000468
  | 773 => 100000463
  | 787 => 100000447
  | 797 => 100000436
  | 809 => 100000423
  | 811 => 100000421
  | 821 => 100000410
  | 823 => 100000408
  | 827 => 100000404
  | 829 => 100000403
  | 839 => 100000393
  | 853 => 100000380
  | 857 => 100000377
  | 859 => 100000375
  | 863 => 100000371
  | 877 => 100000360
  | 881 => 100000356
  | 883 => 100000355
  | 887 => 100000352
  | 907 => 100000336
  | 911 => 100000333
  | 919 => 100000327
  | 929 => 100000320
  | 937 => 100000315
  | 941 => 100000312
  | 947 => 100000308
  | 953 => 100000305
  | 967 => 100000296
  | 971 => 100000293
  | 977 => 100000290
  | 983 => 100000286
  | 991 => 100000282
  | 997 => 100000278
  | _ => 100000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Rational upper bounds for the mass factors in the page 96 head. -/
theorem head_mass_factor_le {p : ℕ} (hp : p ∈ headPrimes) :
    1 + primeWeight p / ((p : ℝ)-1) ≤ (headMassNumerator p : ℝ)/100000000 := by
  have hc : ∀ q ∈ headPrimes,
      100000000 ≤ headMassNumerator q ∧ (q = 2 ∨
        (q-1)^11 * 100000000^4 ≤
          (100000000+(q-1)*(headMassNumerator q-100000000))^4 * (q-2)^11) := by
    intro q hq
    fin_cases hq <;> decide +kernel
  by_cases h2 : p = 2
  · subst p
    norm_num [primeWeight, headMassNumerator]
  have hpmem : p ∈ (1000 : ℕ).primesLE := by rwa [head_prime_table]
  have hpp := Nat.prime_of_mem_primesLE hpmem
  have hp3 : 2 < p := by have := hpp.two_le; omega
  let u := headMassNumerator p
  have hu : 100000000 ≤ u := (hc p hp).1
  have hnat : (p-1)^11 * 100000000^4 ≤
      (100000000+(p-1)*(u-100000000))^4 * (p-2)^11 := (hc p hp).2.resolve_left h2
  change 1 + primeWeight p / ((p : ℝ)-1) ≤ (u : ℝ)/100000000
  have hp2 : (2 : ℝ) < p := by exact_mod_cast hp3
  have hpone : 1 ≤ p := by omega
  have hptwo : 2 ≤ p := by omega
  have hraw : (((p-1 : ℕ) : ℝ))^11 * 100000000^4 ≤
      (100000000+((p-1 : ℕ) : ℝ)*((u-100000000 : ℕ) : ℝ))^4 *
        ((p-2 : ℕ) : ℝ)^11 := by exact_mod_cast hnat
  push_cast [Nat.cast_sub hpone, Nat.cast_sub hptwo, Nat.cast_sub hu] at hraw
  have hU : (1 : ℝ) ≤ (u : ℝ)/100000000 := by
    rw [le_div_iff₀ (by norm_num)]
    norm_num
    exact_mod_cast hu
  have hU0 : 0 ≤ (u : ℝ)/100000000-1 := by linarith
  have hd1 : (0 : ℝ) < p-1 := by linarith
  have hd2 : (0 : ℝ) < p-2 := by linarith
  have hx : 0 ≤ ((p : ℝ)-1)/((p : ℝ)-2) := div_nonneg hd1.le hd2.le
  have hy : 0 ≤ 1+((p : ℝ)-1)*((u : ℝ)/100000000-1) := add_nonneg zero_le_one (mul_nonneg hd1.le hU0)
  have hq : 1+((p : ℝ)-1)*((u : ℝ)/100000000-1) =
      (100000000+((p : ℝ)-1)*((u : ℝ)-100000000))/100000000 := by ring
  have hpow : (((p : ℝ)-1)/((p : ℝ)-2))^(11 : ℕ) ≤
      (1+((p : ℝ)-1)*((u : ℝ)/100000000-1))^(4 : ℕ) := by
    rw [hq, div_pow, div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    exact hraw
  have hr : (((p : ℝ)-1)/((p : ℝ)-2))^(11/4 : ℝ) ≤
      1+((p : ℝ)-1)*((u : ℝ)/100000000-1) := by
    apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hx _) hy (by norm_num : (0 : ℝ)<4)).mp
    rw [← Real.rpow_mul hx]
    norm_num
    exact hpow
  unfold primeWeight
  rw [if_neg (by omega : p ≠ 2)]
  have hdiv := (div_le_iff₀ (by linarith : (0 : ℝ) < p-1)).mpr
    (show (((p : ℝ)-1)/((p : ℝ)-2))^(11/4 : ℝ)-1 ≤
      ((u : ℝ)/100000000-1)*((p : ℝ)-1) by nlinarith only [hr])
  linarith

/-- Rational certificate data for the odd prime moment head on page 96.
Each numerator divided by 10^6 bounds p to the power 3/8 for odd primes through 1000. -/
def headMomentNumerator : ℕ → ℕ
  | 3 => 1509804
  | 5 => 1828580
  | 7 => 2074493
  | 11 => 2457663
  | 13 => 2616549
  | 17 => 2893466
  | 19 => 3016704
  | 23 => 3240768
  | 29 => 3535081
  | 31 => 3624605
  | 37 => 3873252
  | 41 => 4025261
  | 43 => 4097800
  | 47 => 4236788
  | 53 => 4432038
  | 59 => 4613915
  | 61 => 4671956
  | 67 => 4839250
  | 71 => 4945633
  | 73 => 4997423
  | 79 => 5147664
  | 83 => 5243899
  | 89 => 5382962
  | 97 => 5559547
  | 101 => 5644436
  | 103 => 5686094
  | 107 => 5767916
  | 109 => 5808112
  | 113 => 5887141
  | 127 => 6150727
  | 131 => 6222670
  | 137 => 6328055
  | 139 => 6362541
  | 149 => 6530477
  | 151 => 6563211
  | 157 => 6659819
  | 163 => 6754145
  | 167 => 6815829
  | 173 => 6906648
  | 179 => 6995519
  | 181 => 7024728
  | 191 => 7167827
  | 193 => 7195882
  | 197 => 7251450
  | 199 => 7278970
  | 211 => 7440566
  | 223 => 7596514
  | 227 => 7647328
  | 229 => 7672525
  | 233 => 7722510
  | 239 => 7796492
  | 241 => 7820894
  | 251 => 7941045
  | 257 => 8011705
  | 263 => 8081341
  | 269 => 8149991
  | 271 => 8172661
  | 277 => 8240052
  | 281 => 8284473
  | 283 => 8306536
  | 293 => 8415412
  | 307 => 8564005
  | 311 => 8605680
  | 313 => 8626391
  | 317 => 8667568
  | 331 => 8809181
  | 337 => 8868726
  | 347 => 8966513
  | 349 => 8985858
  | 353 => 9024342
  | 359 => 9081560
  | 367 => 9156928
  | 373 => 9212783
  | 379 => 9268079
  | 383 => 9304640
  | 389 => 9359036
  | 397 => 9430755
  | 401 => 9466276
  | 409 => 9536659
  | 419 => 9623439
  | 421 => 9640639
  | 431 => 9725882
  | 433 => 9742782
  | 439 => 9793191
  | 443 => 9826558
  | 449 => 9876257
  | 457 => 9941882
  | 461 => 9974425
  | 463 => 9990630
  | 467 => 10022910
  | 479 => 10118726
  | 487 => 10181772
  | 491 => 10213053
  | 499 => 10275139
  | 503 => 10305950
  | 509 => 10351879
  | 521 => 10442733
  | 523 => 10457748
  | 541 => 10591293
  | 547 => 10635190
  | 557 => 10707688
  | 563 => 10750797
  | 569 => 10793620
  | 571 => 10807831
  | 577 => 10850280
  | 587 => 10920419
  | 593 => 10962145
  | 599 => 11003607
  | 601 => 11017370
  | 607 => 11058489
  | 613 => 11099354
  | 617 => 11126459
  | 619 => 11139970
  | 631 => 11220469
  | 641 => 11286825
  | 643 => 11300018
  | 647 => 11326328
  | 653 => 11365602
  | 659 => 11404652
  | 661 => 11417620
  | 673 => 11494912
  | 677 => 11520485
  | 683 => 11558668
  | 691 => 11609253
  | 701 => 11671973
  | 709 => 11721747
  | 719 => 11783474
  | 727 => 11832470
  | 733 => 11868997
  | 739 => 11905337
  | 743 => 11929461
  | 751 => 11977467
  | 757 => 12013263
  | 761 => 12037028
  | 769 => 12084325
  | 773 => 12107858
  | 787 => 12189631
  | 797 => 12247484
  | 809 => 12316313
  | 811 => 12327722
  | 821 => 12384506
  | 823 => 12395811
  | 827 => 12418370
  | 829 => 12429623
  | 839 => 12485638
  | 853 => 12563363
  | 857 => 12585423
  | 859 => 12596429
  | 863 => 12618393
  | 877 => 12694771
  | 881 => 12716453
  | 883 => 12727271
  | 887 => 12748861
  | 907 => 12855908
  | 911 => 12877140
  | 919 => 12919429
  | 929 => 12971969
  | 937 => 13013747
  | 941 => 13034552
  | 947 => 13065657
  | 953 => 13096639
  | 967 => 13168459
  | 971 => 13188859
  | 977 => 13219361
  | 983 => 13249747
  | 991 => 13290081
  | 997 => 13320199
  | _ => 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- An elementary prime tail estimate for the page 95 and page 96 products.
The constant is a derived certificate bound. It is not printed in the paper. -/
theorem prime_sqrt_tail_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 1000 < p) :
    ∑ p ∈ s, 1/((p : ℝ)*Real.sqrt p) ≤ 0.0171 := by
  classical
  have taskSqrtTail (s : Finset ℕ) (hs : ∀ k ∈ s, 34 ≤ k) :
      ∑ k ∈ s, 1/((k : ℝ)*Real.sqrt k) ≤ 2/Real.sqrt 33 := by
    classical
    have anti : AntitoneOn (fun x : ℝ => x^(-3/2 : ℝ)) (Set.Ici 33) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [Set.mem_Ici.mp hx]) hxy (by norm_num)
    have hInt := anti.tsum_comp_add_le_integral 33
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3/2 : ℝ) < -1) (by norm_num))
      (fun t ht => Real.rpow_nonneg (by have h := Set.mem_Ioi.mp ht; norm_num at h; linarith) _)
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-3/2 : ℝ) < -1) (by norm_num)] at hInt
    have he (k : ℕ) : (k : ℝ)^(-3/2 : ℝ) = 1/((k : ℝ)*Real.sqrt k) := by
      rw [show (-3/2 : ℝ) = -(1+1/2) by norm_num, Real.rpow_neg (Nat.cast_nonneg k)]
      by_cases hk : k = 0
      · subst k; norm_num
      · rw [Real.rpow_add (by exact_mod_cast Nat.pos_of_ne_zero hk), Real.rpow_one,
          ← Real.sqrt_eq_rpow, one_div]
    have hInt2 : (∑' n : ℕ, ((n+33+1 : ℕ) : ℝ)^(-3/2 : ℝ)) ≤ 2/Real.sqrt 33 := by
      convert hInt using 1
      norm_num
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
      ring
    have hsum : Summable (fun n : ℕ => (n : ℝ)^(-3/2 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have hshift : Summable (fun n : ℕ => ((n+33+1 : ℕ) : ℝ)^(-3/2 : ℝ)) := by
      simpa only [Nat.add_assoc] using (summable_nat_add_iff 34).mpr hsum
    let e : ℕ → ℕ := fun k => k-34
    have hinj : Set.InjOn e (↑s : Set ℕ) := by
      intro k hk l hl he
      dsimp [e] at he
      have := hs k hk
      have := hs l hl
      omega
    calc _ = ∑ n ∈ s.image e, ((n+33+1 : ℕ) : ℝ)^(-3/2 : ℝ) := by
           rw [sum_image hinj]
           apply sum_congr rfl
           intro k hk
           have hk0 := hs k hk
           rw [show e k+33+1 = k by dsimp [e]; omega, he]
         _ ≤ ∑' n : ℕ, ((n+33+1 : ℕ) : ℝ)^(-3/2 : ℝ) :=
           hshift.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
         _ ≤ _ := hInt2
  have taskSqrtBlock (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 1020 ≤ p) :
      ∑ p ∈ s, 1/((p : ℝ)*Real.sqrt p) ≤ (8/((30 : ℝ)*Real.sqrt 30))*
        ∑ k ∈ Icc 34 (s.sup (fun p => p/30)), 1/((k : ℝ)*Real.sqrt k) := by
    classical
    let M := s.sup (fun p => p/30)
    let R := (range 30).filter (fun r => r.Coprime 30)
    let T := (Icc 34 M).product R
    let e : ℕ → ℕ × ℕ := fun p => (p/30,p%30)
    have hinj : Set.InjOn e (↑s : Set ℕ) := by
      intro p hp q hq he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      dsimp [e] at h1 h2
      omega
    have hsub : s.image e ⊆ T := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
      obtain ⟨hprime,hp0⟩ := hs p hp
      have hcop : p.Coprime 30 := hprime.coprime_iff_not_dvd.mpr (by
        intro hd
        have := Nat.le_of_dvd (by norm_num : 0 < 30) hd
        omega)
      have hmod : (p%30).Coprime 30 := (ZMod.coprime_mod_iff_coprime p 30).mpr hcop
      change (p / 30, p % 30) ∈ T
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, Finset.le_sup (f := fun p => p/30) hp⟩,
        mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by norm_num)),hmod⟩⟩
    have hcard : R.card = 8 := by decide +kernel
    calc _ ≤ ∑ p ∈ s, (1/((30 : ℝ)*Real.sqrt 30))*(1/((p/30 : ℕ)*Real.sqrt (p/30 : ℕ)) : ℝ) := by
           apply sum_le_sum
           intro p hp
           have hp0 := (hs p hp).2
           have hk : (0 : ℝ) < (p/30 : ℕ) := by exact_mod_cast (show 0 < p/30 by omega)
           have hpl : (30 : ℝ)*(p/30 : ℕ) ≤ p := by exact_mod_cast (show 30*(p/30) ≤ p by omega)
           have hd : (30 : ℝ)*(p/30 : ℕ)*Real.sqrt ((30 : ℝ)*(p/30 : ℕ)) ≤ (p : ℝ)*Real.sqrt p :=
             mul_le_mul hpl (Real.sqrt_le_sqrt hpl) (Real.sqrt_nonneg _) (Nat.cast_nonneg p)
           have hden : 0 < (30 : ℝ)*(p/30 : ℕ)*Real.sqrt ((30 : ℝ)*(p/30 : ℕ)) := by positivity
           have hbound := one_div_le_one_div_of_le hden hd
           calc _ ≤ 1/((30 : ℝ)*(p/30 : ℕ)*Real.sqrt ((30 : ℝ)*(p/30 : ℕ))) := hbound
                _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 30)]; ring
         _ = ∑ x ∈ s.image e, (1/((30 : ℝ)*Real.sqrt 30))*(1/((x.1 : ℝ)*Real.sqrt x.1)) := by
           rw [sum_image hinj]
         _ ≤ ∑ x ∈ T, (1/((30 : ℝ)*Real.sqrt 30))*(1/((x.1 : ℝ)*Real.sqrt x.1)) :=
           sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
         _ = _ := by
           dsimp [T]
           rw [sum_product]
           simp only [sum_const, nsmul_eq_mul, hcard]
           rw [← mul_sum]
           dsimp [M]
           rw [← mul_sum]
           ring
  let L := s.filter (fun p => p < 1020)
  let H := s.filter (fun p => 1020 ≤ p)
  have he : s = L ∪ H := by
    ext p
    by_cases hp : p ∈ s <;> simp [L,H,hp] <;> omega
  have hd : Disjoint L H := by
    apply disjoint_left.mpr
    intro p hp hq
    have := (mem_filter.mp hp).2
    have := (mem_filter.mp hq).2
    omega
  have hsub : L ⊆ ({1009,1013,1019} : Finset ℕ) := by
    intro p hp
    obtain ⟨hps,hp1⟩ := mem_filter.mp hp
    obtain ⟨hprime,hp0⟩ := hs p hps
    interval_cases p
    all_goals norm_num at hprime
    all_goals norm_num
  have hL : ∑ p ∈ L, 1/((p : ℝ)*Real.sqrt p) ≤ 3/31000 := by
    have hcard : L.card ≤ 3 := by simpa using card_le_card hsub
    calc _ ≤ ∑ p ∈ L, (1/31000 : ℝ) := by
           apply sum_le_sum
           intro p hp
           have hp0 : (1000 : ℝ) ≤ p := by exact_mod_cast (hs p (mem_filter.mp hp).1).2.le
           have hsq : (31 : ℝ) ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by linarith)
           apply one_div_le_one_div_of_le (by norm_num)
           nlinarith
         _ ≤ _ := by simp only [sum_const, nsmul_eq_mul, mul_one_div]; gcongr; exact_mod_cast hcard
  have hH := taskSqrtBlock H (fun p hp => ⟨(hs p (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩)
  have hk := taskSqrtTail (Icc 34 (H.sup (fun p => p/30))) (fun k hk => (mem_Icc.mp hk).1)
  have hH2 : ∑ p ∈ H, 1/((p : ℝ)*Real.sqrt p) ≤
      (8/((30 : ℝ)*Real.sqrt 30))*(2/Real.sqrt 33) :=
    hH.trans (mul_le_mul_of_nonneg_left hk (by positivity))
  have h30 : (5.47 : ℝ) ≤ Real.sqrt 30 := Real.le_sqrt_of_sq_le (by norm_num)
  have h33 : (5.74 : ℝ) ≤ Real.sqrt 33 := Real.le_sqrt_of_sq_le (by norm_num)
  have hB : (8/((30 : ℝ)*Real.sqrt 30))*(2/Real.sqrt 33) ≤ (8/(30*5.47 : ℝ))*(2/5.74) := by
    apply mul_le_mul
    · exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
    · exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h33
    · positivity
    · positivity
  rw [he,sum_union hd]
  have hH3 := hH2.trans hB
  norm_num at hH3
  linarith

/-! ### Leaves: the Euler products of Lemma 1 and of the proof of Lemma 7 -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- LEAF. `Σ_{d ≥ 1} g(d) = C^{-1}`: the Euler product of `g` is
`Π_{p>2} (1 + 1/(p(p-2))) = Π_{p>2} (p-1)²/(p(p-2))`. Vaughan 1977 p. 100, display after
(3.12), "by (3.3) and (2.5), Σ g(d) = C^{-1}". Unit U-1525. -/
theorem hasSum_g : HasSum g (1 / Cv) := by
  classical
  have h0 : g 0 = 0 := by simp [g]
  have h1 : g 1 = 1 := g_one
  have hm : ∀ {m n : ℕ}, m.Coprime n → g (m*n) = g m*g n := fun {_ _} h => g_mul h
  have hn : ∀ n, 0 ≤ g n := g_nonneg
  let a : ℕ → ℝ := fun n => if 2 < n then 1/((n : ℝ)*((n : ℝ)-2)) else 0
  have ha (n : ℕ) : 0 ≤ a n := by
    dsimp [a]
    split_ifs with h
    · have hn : (2 : ℝ) < n := by exact_mod_cast h
      exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg n) (by linarith))
    · exact le_rfl
  have hb (n : ℕ) : a n ≤ 3 * (1/(n : ℝ)^2) := by
    dsimp [a]
    split_ifs with h
    · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have hn0 : (0 : ℝ) < n := by linarith
      have hn2 : (0 : ℝ) < n-2 := by linarith
      have ht : 1/((n : ℝ)*((n : ℝ)-2)) ≤ 3/(n : ℝ)^2 := by
        rw [div_le_div_iff₀ (mul_pos hn0 hn2) (sq_pos_of_pos hn0)]
        nlinarith [mul_nonneg hn0.le (show (0 : ℝ) ≤ n-3 by linarith)]
      simpa only [div_eq_mul_inv, one_mul] using ht
    · positivity
  have hasA : Summable a := Summable.of_nonneg_of_le ha hb (hasSum_zeta_two.summable.mul_left 3)
  have hs0 : Summable g := summable_of_prime_power_sums h0 h1 hm hn ha hasA
    (fun p hp => hasSum_g_prime_power hp)
  have heq : (fun n => ‖g n‖) = g := by
    funext n
    exact Real.norm_of_nonneg (hn n)
  have hsn : Summable (fun n => ‖g n‖) := by rw [heq]; exact hs0
  have h2 : HasSum (fun m : ℕ => g (2^m)) 1 := by
    simpa using hasSum_g_prime_power Nat.prime_two
  have hl (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
      HasSum (fun m : ℕ => g (p^m)) (1+1/((p : ℝ)*((p : ℝ)-2))) := by
    simpa only [if_pos hp2] using hasSum_g_prime_power hp
  have hs := hsn.of_norm
  have hge := hs.le_tsum 1 (fun n _ => hn n)
  rw [h1] at hge
  have hprod := EulerProduct.eulerProduct_hasProd_mulIndicator h1 hm hsn h0
  have hodd : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      1+1/((p : ℝ)*((p : ℝ)-2))) (∑' n, g n) := by
    apply (hasProd_subtype_iff_mulIndicator
      (f := fun p : ℕ => (1 : ℝ)+1/((p : ℝ)*((p : ℝ)-2)))
      (s := {p : ℕ | p.Prime ∧ 2 < p})).mpr
    apply hprod.congr_fun
    intro p
    by_cases hp : p.Prime
    · by_cases ht : p = 2
      · subst p
        simp [Set.mulIndicator_apply, Nat.prime_two, h2.tsum_eq]
      · have hp3 : 2 < p := by have := hp.two_le; omega
        simp [Set.mulIndicator_apply, hp, hp3, (hl p hp hp3).tsum_eq]
    · simp [Set.mulIndicator_apply, hp]
  have he (p : {p : ℕ // p.Prime ∧ 2 < p}) :
      1-1/((p : ℝ)-1)^2 = (1+1/((p : ℝ)*((p : ℝ)-2)))⁻¹ := by
    have hp2 : (2 : ℝ) < p := by exact_mod_cast p.2.2
    have hx : (p : ℝ) ≠ 0 := by linarith
    have hd : (p : ℝ)-2 ≠ 0 := by linarith
    have hd1 : (p : ℝ)-1 ≠ 0 := by linarith
    have hc : (p : ℝ)*((p : ℝ)-2)+1 ≠ 0 := by positivity
    field_simp [hx, hd, hd1, hc]
    <;> ring
  have hi := (hodd.inv₀ (by linarith : (∑' n, g n) ≠ 0)).congr_fun he
  have hCv : Cv = (∑' n, g n)⁻¹ := by simpa only [Cv] using hi.tprod_eq
  rw [hCv, one_div, inv_inv]
  exact hs.hasSum


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- LEAF. (2.8): `Γ < 0.535`. Vaughan 1977 p. 95, Lemma 1; the paper sums to `p ≤ 139` and
bounds the tail by partial summation with `θ(u) < 1.001102u`; summing further and bounding the
tail by `Σ_{n>M} log n/(n-1)²` also works. Unit U-1525. -/
theorem gam_lt : Gam < 0.535 := by
  have term_bound {p : ℕ} (hp : 1000 < p) :
      Real.log p/((p : ℝ)-1)^2 ≤ 1.234*(p : ℝ)^(-7/4 : ℝ) := by
    have hpR : (1001 : ℝ) ≤ p := by exact_mod_cast hp
    have hp0 : (0 : ℝ) < p := by linarith
    have hexp : Real.exp 4 ≤ (1000 : ℝ) := by
      have h := pow_le_pow_left₀ (Real.exp_nonneg 1) Real.exp_one_lt_three.le 4
      rw [← Real.exp_nat_mul] at h
      norm_num at h
      linarith
    have hlog : Real.log 1000 ≤ (6.91 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1000)).mpr
      calc (1000 : ℝ) ≤ ∑ k ∈ range 31, (6.91 : ℝ)^k/(k.factorial : ℝ) := by norm_num [sum_range_succ]
           _ ≤ _ := Real.sum_le_exp_of_nonneg (by norm_num) 31
    have hroot : (5.62 : ℝ) ≤ (1000 : ℝ)^(1/4 : ℝ) := by
      apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 5.62)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1000) _) (by norm_num : (4 : ℕ) ≠ 0)).mp
      rw [← Real.rpow_natCast ((1000 : ℝ)^(1/4 : ℝ)) 4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1000)]
      norm_num
    have hratio : Real.log p/(p : ℝ)^(1/4 : ℝ) ≤ (1.23 : ℝ) := by
      have hm := Real.log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 1/4)
      have hmono := hm (a := (1000 : ℝ)) (b := (p : ℝ))
        (by simpa using hexp) (by simpa using hexp.trans (by linarith : (1000 : ℝ) ≤ p)) (by linarith)
      calc _ ≤ Real.log 1000/(1000 : ℝ)^(1/4 : ℝ) := hmono
           _ ≤ (6.91 : ℝ)/5.62 := div_le_div₀ (by positivity) hlog (by norm_num) hroot
           _ ≤ _ := by norm_num
    have hlogp : Real.log p ≤ 1.23*(p : ℝ)^(1/4 : ℝ) :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hp0 _)).mp hratio
    have hd1 : (0 : ℝ) < p-1 := by linarith
    have hden : (p : ℝ)^2 ≤ 1.003*((p : ℝ)-1)^2 := by
      nlinarith [sq_nonneg ((p : ℝ)-1001)]
    have hr : (p : ℝ)^(1/4 : ℝ)/(p : ℝ)^2 = (p : ℝ)^(-7/4 : ℝ) := by
      rw [← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_sub hp0]
      norm_num
    calc _ ≤ (1.23*(p : ℝ)^(1/4 : ℝ))/((p : ℝ)-1)^2 :=
           div_le_div_of_nonneg_right hlogp (sq_nonneg _)
         _ ≤ (1.23*1.003)*(p : ℝ)^(1/4 : ℝ)/(p : ℝ)^2 := by
           rw [div_le_div_iff₀ (sq_pos_of_pos hd1) (sq_pos_of_pos hp0)]
           have h := mul_le_mul_of_nonneg_left hden
             (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1.23) (Real.rpow_nonneg hp0.le (1/4 : ℝ)))
           nlinarith only [h]
         _ = (1.23*1.003)*(p : ℝ)^(-7/4 : ℝ) := by rw [mul_div_assoc,hr]
         _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hp0.le _)
  -- The finite logarithm head and the total power tail budget remain open.
  sorry

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- LEAF. The Euler product behind (2.4): `Σ_d s(d)^{1/2} g(d) = C₀`, the local factor at
`p > 2` being `1 + p^{1/2}/(p(p-2))`. Vaughan 1977 p. 100, last display, "by (3.3) and (2.4)".
Unit U-1525. -/
theorem hasSum_sqrt_g : HasSum (fun d => Real.sqrt (sk d) * g d) C0v := by
  classical
  let F : ℕ → ℝ := fun d => Real.sqrt (sk d)*g d
  let a : ℕ → ℝ := fun p => if 2 < p then 1/(Real.sqrt p*((p : ℝ)-2)) else 0
  have h0 : F 0 = 0 := by simp [F, g]
  have h1 : F 1 = 1 := by simp [F, sk, g_one]
  have hn (d : ℕ) : 0 ≤ F d := mul_nonneg (Real.sqrt_nonneg _) (g_nonneg d)
  have hm {m n : ℕ} (hc : m.Coprime n) : F (m*n) = F m*F n := by
    have hr : sk (m*n) = sk m*sk n := by
      unfold sk
      rw [hc.primeFactors_mul, Finset.prod_union hc.disjoint_primeFactors]
    dsimp [F]
    rw [hr, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg (sk m)), g_mul hc]
    ring
  have hl (p : ℕ) (hp : p.Prime) : HasSum (fun m : ℕ => F (p^m)) (1+a p) := by
    have hsPow (m : ℕ) (hm : m ≠ 0) : sk (p^m) = p := by
      rw [sk, Nat.primeFactors_prime_pow hm hp, Finset.prod_singleton]
    have he : (fun m : ℕ => F (p^m)) =
        (fun m : ℕ => Real.sqrt p*g (p^m)+(if m = 0 then 1-Real.sqrt p else 0)) := by
      funext m
      by_cases hm : m = 0
      · subst m
        simp [F, g_one, sk]
      · simp [F, hsPow m hm, hm]
    have hw : HasSum (fun m : ℕ => F (p^m))
        (1+Real.sqrt p*(if 2 < p then 1/((p : ℝ)*((p : ℝ)-2)) else 0)) := by
      rw [he]
      convert ((hasSum_g_prime_power hp).mul_left (Real.sqrt p)).add
        (hasSum_ite_eq 0 (1-Real.sqrt p)) using 1 <;> ring
    by_cases ht : 2 < p
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
      have heq : Real.sqrt p / (p : ℝ) = 1 / Real.sqrt p := by
        rw [div_eq_div_iff hp0.ne' hs.ne']
        simpa [pow_two] using Real.sq_sqrt (Nat.cast_nonneg p)
      have he2 : Real.sqrt p*(1/((p : ℝ)*((p : ℝ)-2))) =
          1/(Real.sqrt p*((p : ℝ)-2)) := by
        simpa only [div_div, mul_one_div] using
          congrArg (fun x : ℝ => x/((p : ℝ)-2)) heq
      simpa only [a, if_pos ht, he2] using hw
    · simpa only [a, if_neg ht, mul_zero] using hw
  have ha (n : ℕ) : 0 ≤ a n := by
    dsimp [a]
    split_ifs with h
    · have hn : (2 : ℝ) < n := by exact_mod_cast h
      exact div_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
    · exact le_rfl
  have hb (n : ℕ) : a n ≤ 3 * (1/(n : ℝ)^(3/2 : ℝ)) := by
    dsimp [a]
    split_ifs with h
    · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have hn0 : (0 : ℝ) < n := by linarith
      have hn2 : (0 : ℝ) < n-2 := by linarith
      have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      have hr : (n : ℝ)^(3/2 : ℝ) = (n : ℝ)*Real.sqrt n := by
        rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add hn0,
          Real.rpow_one, ← Real.sqrt_eq_rpow]
      have ht : 1/(Real.sqrt n*((n : ℝ)-2)) ≤ 3/(n : ℝ)^(3/2 : ℝ) := by
        rw [hr, div_le_div_iff₀ (mul_pos hs hn2) (mul_pos hn0 hs)]
        nlinarith [mul_nonneg hs.le (show (0 : ℝ) ≤ n-3 by linarith)]
      simpa only [div_eq_mul_inv, one_mul] using ht
    · positivity
  have hz : Summable (fun n : ℕ => 1/(n : ℝ)^(3/2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hasA : Summable a := Summable.of_nonneg_of_le ha hb (hz.mul_left 3)
  have hs0 : Summable F := summable_of_prime_power_sums h0 h1 hm hn ha hasA hl
  have heq : (fun n => ‖F n‖) = F := by
    funext n
    exact Real.norm_of_nonneg (hn n)
  have hsn : Summable (fun n => ‖F n‖) := by rw [heq]; exact hs0
  have h2 : HasSum (fun m : ℕ => F (2^m)) 1 := by simpa [a] using hl 2 Nat.prime_two
  have hprod := EulerProduct.eulerProduct_hasProd_mulIndicator h1 hm hsn h0
  have hodd : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      1+1/(Real.sqrt p*((p : ℝ)-2))) (∑' n, F n) := by
    apply (hasProd_subtype_iff_mulIndicator
      (f := fun p : ℕ => (1 : ℝ)+1/(Real.sqrt p*((p : ℝ)-2)))
      (s := {p : ℕ | p.Prime ∧ 2 < p})).mpr
    apply hprod.congr_fun
    intro p
    by_cases hp : p.Prime
    · by_cases ht : p = 2
      · subst p
        simp [Nat.prime_two, h2.tsum_eq]
      · have hp3 : 2 < p := by have := hp.two_le; omega
        simp [hp, hp3, a, (hl p hp).tsum_eq]
    · simp [hp]
  have he : C0v = ∑' n, F n := hodd.tprod_eq
  rw [he]
  exact hsn.of_norm.hasSum

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- LEAF. (2.9): `C₀ < 2.35`. Vaughan 1977 p. 95, Lemma 1: the product over `2 < p ≤ 139` is
below 2.267 and the tail below `exp(0.0358)`. Unit U-1525. -/
theorem C0v_lt : C0v < 2.35 := by
  classical
  have hhead (s : Finset ℕ) (hsub : s ⊆ headPrimes) :
      ∏ p ∈ s, (1+1/(Real.sqrt p*((p : ℝ)-2))) ≤ (2.307 : ℝ) := by
    let u : ℕ → ℕ := fun p => match p with
      | 3 => 1577351
      | 5 => 1149072
      | 7 => 1075593
      | 11 => 1033502
      | 13 => 1025214
      | 17 => 1016170
      | 19 => 1013496
      | 23 => 1009930
      | 29 => 1006878
      | 31 => 1006194
      | 37 => 1004698
      | 41 => 1004005
      | 43 => 1003720
      | 47 => 1003242
      | 53 => 1002694
      | 59 => 1002285
      | 61 => 1002171
      | 67 => 1001880
      | 71 => 1001720
      | 73 => 1001649
      | 79 => 1001462
      | 83 => 1001356
      | 89 => 1001219
      | 97 => 1001069
      | 101 => 1001006
      | 103 => 1000976
      | 107 => 1000921
      | 109 => 1000896
      | 113 => 1000848
      | 127 => 1000710
      | 131 => 1000678
      | 137 => 1000633
      | 139 => 1000620
      | 149 => 1000558
      | 151 => 1000547
      | 157 => 1000515
      | 163 => 1000487
      | 167 => 1000469
      | 173 => 1000445
      | 179 => 1000423
      | 181 => 1000416
      | 191 => 1000383
      | 193 => 1000377
      | 197 => 1000366
      | 199 => 1000360
      | 211 => 1000330
      | 223 => 1000304
      | 227 => 1000295
      | 229 => 1000292
      | 233 => 1000284
      | 239 => 1000273
      | 241 => 1000270
      | 251 => 1000254
      | 257 => 1000245
      | 263 => 1000237
      | 269 => 1000229
      | 271 => 1000226
      | 277 => 1000219
      | 281 => 1000214
      | 283 => 1000212
      | 293 => 1000201
      | 307 => 1000188
      | 311 => 1000184
      | 313 => 1000182
      | 317 => 1000179
      | 331 => 1000168
      | 337 => 1000163
      | 347 => 1000156
      | 349 => 1000155
      | 353 => 1000152
      | 359 => 1000148
      | 367 => 1000144
      | 373 => 1000140
      | 379 => 1000137
      | 383 => 1000135
      | 389 => 1000132
      | 397 => 1000128
      | 401 => 1000126
      | 409 => 1000122
      | 419 => 1000118
      | 421 => 1000117
      | 431 => 1000113
      | 433 => 1000112
      | 439 => 1000110
      | 443 => 1000108
      | 449 => 1000106
      | 457 => 1000103
      | 461 => 1000102
      | 463 => 1000101
      | 467 => 1000100
      | 479 => 1000096
      | 487 => 1000094
      | 491 => 1000093
      | 499 => 1000091
      | 503 => 1000089
      | 509 => 1000088
      | 521 => 1000085
      | 523 => 1000084
      | 541 => 1000080
      | 547 => 1000079
      | 557 => 1000077
      | 563 => 1000076
      | 569 => 1000074
      | 571 => 1000074
      | 577 => 1000073
      | 587 => 1000071
      | 593 => 1000070
      | 599 => 1000069
      | 601 => 1000069
      | 607 => 1000068
      | 613 => 1000067
      | 617 => 1000066
      | 619 => 1000066
      | 631 => 1000064
      | 641 => 1000062
      | 643 => 1000062
      | 647 => 1000061
      | 653 => 1000061
      | 659 => 1000060
      | 661 => 1000060
      | 673 => 1000058
      | 677 => 1000057
      | 683 => 1000057
      | 691 => 1000056
      | 701 => 1000055
      | 709 => 1000054
      | 719 => 1000053
      | 727 => 1000052
      | 733 => 1000051
      | 739 => 1000050
      | 743 => 1000050
      | 751 => 1000049
      | 757 => 1000049
      | 761 => 1000048
      | 769 => 1000048
      | 773 => 1000047
      | 787 => 1000046
      | 797 => 1000045
      | 809 => 1000044
      | 811 => 1000044
      | 821 => 1000043
      | 823 => 1000043
      | 827 => 1000043
      | 829 => 1000042
      | 839 => 1000042
      | 853 => 1000041
      | 857 => 1000040
      | 859 => 1000040
      | 863 => 1000040
      | 877 => 1000039
      | 881 => 1000039
      | 883 => 1000039
      | 887 => 1000038
      | 907 => 1000037
      | 911 => 1000037
      | 919 => 1000036
      | 929 => 1000036
      | 937 => 1000035
      | 941 => 1000035
      | 947 => 1000035
      | 953 => 1000035
      | 967 => 1000034
      | 971 => 1000034
      | 977 => 1000033
      | 983 => 1000033
      | 991 => 1000033
      | 997 => 1000032
      | _ => 1000000
  
    have hc : ∀ p ∈ headPrimes, 1000000 ≤ u p ∧
        (p = 2 ∨ 1000000^2 ≤ (u p-1000000)^2*p*(p-2)^2) := by
      intro p hp
      fin_cases hp <;> decide +kernel
    have hnum : 1000*(∏ p ∈ headPrimes, u p) ≤ 2307*1000000^168 := by decide +kernel
    have hcard : headPrimes.card = 168 := by decide +kernel
    have hreal : (∏ p ∈ headPrimes, (u p : ℝ)/1000000) ≤ 2.307 := by
      rw [Finset.prod_div_distrib, Finset.prod_const, hcard,
        div_le_iff₀ (by positivity : (0 : ℝ) < 1000000^168)]
      have hn : (1000 : ℝ)*(∏ p ∈ headPrimes, (u p : ℝ)) ≤
          2307*(1000000 : ℝ)^168 := by exact_mod_cast hnum
      nlinarith only [hn]
    have hpp (p : ℕ) (hp : p ∈ headPrimes) : p.Prime := by
      rw [← head_prime_table] at hp
      exact Nat.prime_of_mem_primesLE hp
    have hnonneg (p : ℕ) (hp : p ∈ headPrimes) : 0 ≤ 1/(Real.sqrt p*((p : ℝ)-2)) := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hpp p hp).two_le
      exact div_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
    have hfactor (p : ℕ) (hp : p ∈ headPrimes) :
        1+1/(Real.sqrt p*((p : ℝ)-2)) ≤ (u p : ℝ)/1000000 := by
      obtain ⟨hu,hc⟩ := hc p hp
      rcases hc with hp2 | hc
      · subst p
        norm_num [u]
      · have hne : p ≠ 2 := by intro h; subst p; norm_num at hc
        have hp3 : 3 ≤ p := by have := (hpp p hp).two_le; omega
        have hp2 : 2 ≤ p := by omega
        have hpos : (0 : ℝ) < p := by exact_mod_cast (hpp p hp).pos
        have hd : (0 : ℝ) < (p : ℝ)-2 := by
          have hh : (3 : ℝ) ≤ p := by exact_mod_cast hp3
          linarith
        have hden : 0 < Real.sqrt p*((p : ℝ)-2) := mul_pos (Real.sqrt_pos.mpr hpos) hd
        have hrealc : (1000000 : ℝ)^2 ≤ ((u p : ℝ)-1000000)^2*(p : ℝ)*((p : ℝ)-2)^2 := by
          exact_mod_cast hc
        have hsq : (1000000 : ℝ)^2 ≤ (((u p : ℝ)-1000000)*(Real.sqrt p*((p : ℝ)-2)))^2 := by
          calc _ ≤ ((u p : ℝ)-1000000)^2*(p : ℝ)*((p : ℝ)-2)^2 := hrealc
               _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hpos.le]; ring
        have hur : (1000000 : ℝ) ≤ u p := by exact_mod_cast hu
        have hh : (1000000 : ℝ) ≤ ((u p : ℝ)-1000000)*(Real.sqrt p*((p : ℝ)-2)) := by
          have hnn := mul_nonneg (sub_nonneg.mpr hur) hden.le
          nlinarith only [hsq,hnn]
        have hfrac : 1/(Real.sqrt p*((p : ℝ)-2)) ≤ ((u p : ℝ)-1000000)/1000000 := by
          rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 1000000)]
          nlinarith only [hh]
        calc _ ≤ 1+((u p : ℝ)-1000000)/1000000 := by linarith only [hfrac]
             _ = _ := by ring
    calc _ ≤ ∏ p ∈ headPrimes, (1+1/(Real.sqrt p*((p : ℝ)-2))) :=
           prod_le_prod_of_subset_of_one_le₀ hsub
             (fun p hp => by linarith [hnonneg p (hsub hp)])
             (fun p hp _ => by linarith [hnonneg p hp])
         _ ≤ ∏ p ∈ headPrimes, (u p : ℝ)/1000000 :=
           prod_le_prod₀ (fun p hp => by linarith [hnonneg p hp]) hfactor
         _ ≤ _ := hreal
  have hbound : C0v ≤ 2.348 := by
    unfold C0v
    apply tprod_le_of_prod_le' (by norm_num : (1 : ℝ) ≤ 2.348)
    intro s
    let S := s.image (fun p : {p : ℕ // p.Prime ∧ 2 < p} => p.val)
    let L := S.filter (fun p => p ≤ 1000)
    let H := S.filter (fun p => ¬ p ≤ 1000)
    have hprime (p : ℕ) (hp : p ∈ S) : p.Prime ∧ 2 < p := by
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
      exact q.property
    have he : S = L ∪ H := by
      ext p
      by_cases hp : p ∈ S <;> simp [L,H,hp] <;> omega
    have hd : Disjoint L H := by
      apply disjoint_left.mpr
      intro p hp hq
      exact (mem_filter.mp hq).2 (mem_filter.mp hp).2
    have hL := hhead L (by
      intro p hp
      rw [← head_prime_table]
      exact Nat.mem_primesLE.mpr ⟨(mem_filter.mp hp).2,(hprime p (mem_filter.mp hp).1).1⟩)
    have hsum : ∑ p ∈ H, 1/(Real.sqrt p*((p : ℝ)-2)) ≤ 0.0172 := by
      calc _ ≤ ∑ p ∈ H, (1.003 : ℝ)*(1/((p : ℝ)*Real.sqrt p)) := by
             apply sum_le_sum
             intro p hp
             have hpN : 1000 < p := by have := (mem_filter.mp hp).2; omega
             have hpR : (1001 : ℝ) ≤ p := by exact_mod_cast hpN
             have hp0 : (0 : ℝ) < p := by linarith
             have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
             have hd2 : (0 : ℝ) < p-2 := by linarith
             rw [mul_one_div, div_le_div_iff₀ (mul_pos hs hd2) (mul_pos hp0 hs)]
             have hi : (p : ℝ) ≤ 1.003*((p : ℝ)-2) := by linarith
             nlinarith [mul_le_mul_of_nonneg_right hi hs.le]
           _ = (1.003 : ℝ)*∑ p ∈ H, 1/((p : ℝ)*Real.sqrt p) := (mul_sum _ _ _).symm
           _ ≤ (1.003 : ℝ)*0.0171 := mul_le_mul_of_nonneg_left
             (prime_sqrt_tail_le H (fun p hp => ⟨(hprime p (mem_filter.mp hp).1).1, by have := (mem_filter.mp hp).2; omega⟩)) (by norm_num)
           _ ≤ _ := by norm_num
    have hH : ∏ p ∈ H, (1+1/(Real.sqrt p*((p : ℝ)-2))) ≤ Real.exp 0.0172 := by
      calc _ ≤ ∏ p ∈ H, Real.exp (1/(Real.sqrt p*((p : ℝ)-2))) := by
             apply prod_le_prod₀
             · intro p hp
               have hpN : 1000 < p := by have := (mem_filter.mp hp).2; omega
               have hpR : (1001 : ℝ) ≤ p := by exact_mod_cast hpN
               have hn : 0 ≤ 1/(Real.sqrt p*((p : ℝ)-2)) := by
                 apply div_nonneg zero_le_one
                 exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
               linarith
             · intro p hp
               simpa only [add_comm] using Real.add_one_le_exp (1/(Real.sqrt p*((p : ℝ)-2)))
           _ = Real.exp (∑ p ∈ H, 1/(Real.sqrt p*((p : ℝ)-2))) := (Real.exp_sum _ _).symm
           _ ≤ _ := Real.exp_le_exp.mpr hsum
    have hnn : 0 ≤ ∏ p ∈ H, (1+1/(Real.sqrt p*((p : ℝ)-2))) := by
      apply prod_nonneg
      intro p hp
      have hpN : 1000 < p := by have := (mem_filter.mp hp).2; omega
      have hpR : (1001 : ℝ) ≤ p := by exact_mod_cast hpN
      have hn : 0 ≤ 1/(Real.sqrt p*((p : ℝ)-2)) := by
        apply div_nonneg zero_le_one
        exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
      linarith
    calc _ = ∏ p ∈ S, (1+1/(Real.sqrt p*((p : ℝ)-2))) := by
           dsimp [S]
           rw [prod_image (by intros a ha b hb hab; exact Subtype.ext hab)]
         _ = (∏ p ∈ L, (1+1/(Real.sqrt p*((p : ℝ)-2))))*
             ∏ p ∈ H, (1+1/(Real.sqrt p*((p : ℝ)-2))) := by rw [he,prod_union hd]
         _ ≤ 2.307*Real.exp 0.0172 := mul_le_mul hL hH hnn (by norm_num)
         _ ≤ 2.307*(1/(1-(0.0172 : ℝ))) := mul_le_mul_of_nonneg_left
           (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)) (by norm_num)
         _ ≤ _ := by norm_num
  exact lt_of_le_of_lt hbound (by norm_num)

open Filter TrivSqZeroExt in
open scoped Topology TrivSqZeroExt in
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- LEAF. (3.12): `Σ_d g(d) log s(d) = Γ Σ_d g(d) = Γ/C`, by writing `log s(d) = Σ_{p|d} log p`
and inverting the order of summation; the local ratio at `p` is `1/(p-1)²`. Vaughan 1977
p. 100, (3.12), with (2.3), (3.3). Unit U-1525. -/
theorem hasSum_g_log : HasSum (fun d => g d * Real.log (sk d)) (Gam / Cv) := by
  classical
  have taskUnipotent {ι : Type} {b : ι → ℝ} {B : ℝ} (h : HasSum b B) :
      HasProd (fun i => (1 : TrivSqZeroExt ℝ ℝ)+inr (b i)) (1+inr B) := by
    classical
    have he (s : Finset ι) : (∏ i ∈ s, ((1 : TrivSqZeroExt ℝ ℝ)+inr (b i))) =
        1+inr (∑ i ∈ s,b i) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, ih]
        ext <;> simp <;> ring
    change Tendsto _ atTop _
    simp_rw [he]
    exact tendsto_const_nhds.add (TrivSqZeroExt.continuous_inr.tendsto B |>.comp h)
  have taskDualEuler {F : ℕ → TrivSqZeroExt ℝ ℝ}
      {a b : {p : ℕ // p.Prime ∧ 2 < p} → ℝ} {A B : ℝ}
      (h0 : F 0 = 0) (h1 : F 1 = 1)
      (hm : ∀ {m n : ℕ}, m.Coprime n → F (m*n) = F m*F n)
      (hsn : Summable (fun n => ‖F n‖))
      (h2 : HasSum (fun m : ℕ => F (2^m)) 1)
      (hl : ∀ p : {p : ℕ // p.Prime ∧ 2 < p},
        HasSum (fun m : ℕ => F (p.val^m)) (inl (a p)*(1+inr (b p))))
      (hpa : HasProd a A) (hsb : HasSum b B) :
      HasSum (fun n => (F n).snd) (A*B) := by
    classical
    have hprod := EulerProduct.eulerProduct_hasProd_mulIndicator h1 hm hsn h0
    have hodd : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
        inl (a p)*(1+inr (b p))) (∑' n,F n) := by
      let k (p : ℕ) : TrivSqZeroExt ℝ ℝ := if h : p.Prime ∧ 2 < p then
        inl (a ⟨p,h⟩)*(1+inr (b ⟨p,h⟩)) else 1
      have hfull : HasProd ({p : ℕ | p.Prime ∧ 2 < p}.mulIndicator k) (∑' n,F n) := by
        apply hprod.congr_fun
        intro p
        by_cases hp : p.Prime
        · by_cases ht : p = 2
          · subst p
            simp [k,hp,h2.tsum_eq]
          · have hp3 : 2 < p := by have := hp.two_le; omega
            simp [k,hp,hp3,(hl ⟨p,hp,hp3⟩).tsum_eq]
        · simp [k,hp]
      have ht := (hasProd_subtype_iff_mulIndicator (f := k)
        (s := {p : ℕ | p.Prime ∧ 2 < p})).mpr hfull
      exact ht.congr_fun (fun p => by
        dsimp only [Function.comp_apply,k]
        rw [dif_pos (show p.val.Prime ∧ 2 < p.val from p.property)]
        rfl)
    have hscalar : HasProd (fun p => (inl (a p) : TrivSqZeroExt ℝ ℝ)) (inl A) := by
      exact hpa.map (inlHom ℝ ℝ).toMonoidHom TrivSqZeroExt.continuous_inl
    have hd := hscalar.mul (taskUnipotent hsb)
    have he := hodd.unique hd
    have hs := TrivSqZeroExt.hasSum_snd ℝ hsn.of_norm.hasSum
    rw [he] at hs
    simpa using hs
  have taskLogSummable : Summable (fun d => g d*Real.log (sk d)) := by
    have hn (d : ℕ) : 0 ≤ g d*Real.log (sk d) :=
      mul_nonneg (g_nonneg d) (Real.log_natCast_nonneg _)
    have hb (d : ℕ) : g d*Real.log (sk d) ≤ 2*(Real.sqrt (sk d)*g d) := by
      have h := Real.log_le_rpow_div (Nat.cast_nonneg (sk d)) (by norm_num : (0 : ℝ) < 1/2)
      rw [← Real.sqrt_eq_rpow] at h
      have hh := mul_le_mul_of_nonneg_left h (g_nonneg d)
      nlinarith only [hh]
    exact Summable.of_nonneg_of_le hn hb (hasSum_sqrt_g.summable.mul_left 2)
  have taskGammaSum : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => Real.log p/((p : ℝ)-1)^2) := by
    let a : ℕ → ℝ := fun n => if 2 < n then Real.log n/((n : ℝ)-1)^2 else 0
    have ha (n : ℕ) : 0 ≤ a n := by
      dsimp [a]
      split_ifs <;> positivity
    have hb (n : ℕ) : a n ≤ 8*(1/(n : ℝ)^(3/2 : ℝ)) := by
      dsimp [a]
      split_ifs with h
      · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
        have hn0 : (0 : ℝ) < n := by linarith
        have hn1 : (0 : ℝ) < n-1 := by linarith
        have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        have hr : (n : ℝ)^(3/2 : ℝ) = (n : ℝ)*Real.sqrt n := by
          rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add hn0,
            Real.rpow_one, ← Real.sqrt_eq_rpow]
        have hl := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ)<1/2)
        rw [← Real.sqrt_eq_rpow] at hl
        have hden : (n : ℝ)^2 ≤ 4*((n : ℝ)-1)^2 := by nlinarith
        calc _ ≤ (2*Real.sqrt n)/((n : ℝ)-1)^2 := div_le_div_of_nonneg_right (by linarith only [hl]) (sq_nonneg _)
             _ ≤ _ := by
               rw [hr,mul_one_div,div_le_div_iff₀ (sq_pos_of_pos hn1) (mul_pos hn0 hs)]
               have he := Real.sq_sqrt hn0.le
               nlinarith [hden]
      · positivity
    have hz : Summable (fun n : ℕ => 1/(n : ℝ)^(3/2 : ℝ)) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num)
    have hs : Summable a := Summable.of_nonneg_of_le ha hb (hz.mul_left 8)
    have ht := hs.subtype (fun p => p.Prime ∧ 2 < p)
    exact ht.congr (fun p => by dsimp [a]; rw [if_pos p.property.2])
  
  let a : ℕ → ℝ := fun p => if 2 < p then 1/((p : ℝ)*((p : ℝ)-2)) else 0
  let F : ℕ → TrivSqZeroExt ℝ ℝ := fun d => inl (g d)+inr (g d*Real.log (sk d))
  have h0 : F 0 = 0 := by simp [F,g]
  have h1 : F 1 = 1 := by simp [F,g_one,sk]
  have hskn (n : ℕ) : sk n ≠ 0 := by
    unfold sk
    apply prod_ne_zero_iff.mpr
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hm {m n : ℕ} (hc : m.Coprime n) : F (m*n) = F m*F n := by
    have hr : sk (m*n) = sk m*sk n := by
      unfold sk
      rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
    have hl : Real.log (sk (m*n)) = Real.log (sk m)+Real.log (sk n) := by
      rw [hr,Nat.cast_mul,Real.log_mul (by exact_mod_cast hskn m) (by exact_mod_cast hskn n)]
    ext <;> simp [F,g_mul hc,hl,smul_eq_mul] <;> ring
  have hn (d : ℕ) : ‖F d‖ = g d+g d*Real.log (sk d) := by
    simp [F,TrivSqZeroExt.norm_def,Real.norm_of_nonneg (g_nonneg d),
      Real.norm_of_nonneg (mul_nonneg (g_nonneg d) (Real.log_natCast_nonneg _))]
  have hsn : Summable (fun n => ‖F n‖) := by
    simp_rw [hn]
    exact hasSum_g.summable.add taskLogSummable
  have hloc (p : ℕ) (hp : p.Prime) : HasSum (fun m : ℕ => F (p^m))
      (inl (1+a p)+inr (Real.log p*a p)) := by
    have hsPow (m : ℕ) (hm : m ≠ 0) : sk (p^m) = p := by
      rw [sk,Nat.primeFactors_prime_pow hm hp,Finset.prod_singleton]
    have he : (fun m : ℕ => g (p^m)*Real.log (sk (p^m))) =
        (fun m : ℕ => Real.log p*g (p^m)+(if m = 0 then -Real.log p else 0)) := by
      funext m
      by_cases hm : m = 0
      · subst m
        simp [g_one,sk]
      · simp [hsPow m hm,hm,mul_comm]
    have hg : HasSum (fun m : ℕ => g (p^m)) (1+a p) := hasSum_g_prime_power hp
    have hw : HasSum (fun m : ℕ => g (p^m)*Real.log (sk (p^m))) (Real.log p*a p) := by
      rw [he]
      convert (hg.mul_left (Real.log p)).add (hasSum_ite_eq 0 (-Real.log p)) using 1 <;> ring
    exact (TrivSqZeroExt.hasSum_inl ℝ hg).add (TrivSqZeroExt.hasSum_inr ℝ hw)
  have h2 : HasSum (fun m : ℕ => F (2^m)) 1 := by simpa [a] using hloc 2 Nat.prime_two
  have hpa : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} => 1+a p.val) (1/Cv) := by
    have hg0 : g 0 = 0 := by simp [g]
    have hgm : ∀ {m n : ℕ}, m.Coprime n → g (m*n) = g m*g n := fun {_ _} h => g_mul h
    have hprod := EulerProduct.eulerProduct_hasProd_mulIndicator g_one hgm hasSum_g.summable.norm hg0
    have hodd : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} => 1+a p.val) (∑' n,g n) := by
      apply (hasProd_subtype_iff_mulIndicator (f := fun p : ℕ => 1+a p)
        (s := {p : ℕ | p.Prime ∧ 2 < p})).mpr
      apply hprod.congr_fun
      intro p
      by_cases hp : p.Prime
      · by_cases ht : p = 2
        · subst p
          simp [Nat.prime_two,a,(hasSum_g_prime_power Nat.prime_two).tsum_eq]
        · have hp3 : 2 < p := by have := hp.two_le; omega
          simp [hp,hp3,a,(hasSum_g_prime_power hp).tsum_eq]
      · simp [hp]
    rwa [hasSum_g.tsum_eq] at hodd
  have hnorm (p : {p : ℕ // p.Prime ∧ 2 < p}) :
      (inl (1+a p.val)+inr (Real.log p*a p.val) : TrivSqZeroExt ℝ ℝ) =
      inl (1+a p.val)*(1+inr (Real.log p/((p : ℝ)-1)^2)) := by
    have hp2 : (2 : ℝ) < p := by exact_mod_cast p.property.2
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hd2 : (p : ℝ)-2 ≠ 0 := by linarith
    have hd1 : (p : ℝ)-1 ≠ 0 := by linarith
    ext <;> simp [a,p.property.2,smul_eq_mul]
    field_simp
    <;> ring
  have hb : HasSum (fun p : {p : ℕ // p.Prime ∧ 2 < p} => Real.log p/((p : ℝ)-1)^2) Gam :=
    taskGammaSum.hasSum
  have hh := taskDualEuler h0 h1 hm hsn h2
    (a := fun p => 1+a p.val)
    (b := fun p => Real.log p/((p : ℝ)-1)^2)
    (fun p => by rw [← hnorm p]; exact hloc p.val p.property.1) hpa hb
  convert hh using 1
  · funext n
    simp [F]
  · ring

/-! ### Assembly: the tail of `Σ g` (Rankin's trick, p. 100) -/

/-- **PROVED from `hasSum_sqrt_g`**: `Σ_{s(d) > z} g(d) ≤ C₀ z^{-1/2}`, Vaughan 1977 p. 100,
last display. -/
theorem tail_le {z : ℝ} (hz : 0 < z) :
    ∑' d, (if z < (sk d : ℝ) then g d else 0) ≤ C0v / Real.sqrt z := by
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
  have hbound : ∀ d, (if z < (sk d : ℝ) then g d else 0) ≤ Real.sqrt (sk d) * g d / Real.sqrt z := by
    intro d
    split_ifs with h
    · rw [le_div_iff₀ hsz]
      have : Real.sqrt z ≤ Real.sqrt (sk d) := Real.sqrt_le_sqrt h.le
      nlinarith [g_nonneg d]
    · exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (g_nonneg d)) hsz.le
  have hnn : ∀ d, 0 ≤ (if z < (sk d : ℝ) then g d else 0) := by
    intro d; split_ifs
    · exact g_nonneg d
    · exact le_rfl
  have hs2 : Summable (fun d => Real.sqrt (sk d) * g d / Real.sqrt z) :=
    hasSum_sqrt_g.summable.div_const _
  have hs1 : Summable (fun d => if z < (sk d : ℝ) then g d else 0) :=
    Summable.of_nonneg_of_le hnn hbound hs2
  calc ∑' d, (if z < (sk d : ℝ) then g d else 0)
      ≤ ∑' d, Real.sqrt (sk d) * g d / Real.sqrt z := hs1.tsum_le_tsum hbound hs2
    _ = C0v / Real.sqrt z := by rw [tsum_div_const, hasSum_sqrt_g.tsum_eq]

/-- **PROVED from `hasSum_g` and `tail_le`'s summability**: the split
`Σ_{s(d) ≤ z} g(d) + Σ_{s(d) > z} g(d) = C^{-1}` used on p. 100. -/
theorem split_sum (z : ℝ) :
    (∑' d, (if (sk d : ℝ) ≤ z then g d else 0)) + ∑' d, (if z < (sk d : ℝ) then g d else 0)
      = 1 / Cv := by
  have hle : ∀ d, (if (sk d : ℝ) ≤ z then g d else 0) ≤ g d := by
    intro d; split_ifs
    · exact le_rfl
    · exact g_nonneg d
  have hle' : ∀ d, (if z < (sk d : ℝ) then g d else 0) ≤ g d := by
    intro d; split_ifs
    · exact le_rfl
    · exact g_nonneg d
  have hnn : ∀ d, 0 ≤ (if (sk d : ℝ) ≤ z then g d else 0) := by
    intro d; split_ifs
    · exact g_nonneg d
    · exact le_rfl
  have hnn' : ∀ d, 0 ≤ (if z < (sk d : ℝ) then g d else 0) := by
    intro d; split_ifs
    · exact g_nonneg d
    · exact le_rfl
  have s1 := Summable.of_nonneg_of_le hnn hle hasSum_g.summable
  have s2 := Summable.of_nonneg_of_le hnn' hle' hasSum_g.summable
  rw [← s1.tsum_add s2, ← hasSum_g.tsum_eq]
  congr 1; funext d
  by_cases h : (sk d : ℝ) ≤ z
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

/-! ### Leaves: the numeric Euler bounds (2.11) and (2.12) -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- LEAF. Head of (2.11): `Π_{p ≤ min(N,1000)} (1 + (((p-1)/(p-2))^{11/4} - 1)/(p-1)) ≤ 6.2083`
for every `N`, the factor at `p = 2` being 1. Numerically the full head to 1000 is
6.20826. Vaughan 1977 p. 96, proof of (2.11), which takes the head to 307 (6.2022 to 6.2023).
Unit U-1525. -/
theorem C1_head (N : ℕ) :
    ∏ p ∈ N.primesLE.filter (· ≤ 1000), (1 + primeWeight p / ((p : ℝ) - 1)) ≤ 6.2083 := by
  have hnum : 10000 * (∏ p ∈ headPrimes, headMassNumerator p) ≤
      62083 * 100000000^168 := by decide +kernel
  have hcard : headPrimes.card = 168 := by decide +kernel
  have hreal : (∏ p ∈ headPrimes, (headMassNumerator p : ℝ)/100000000) ≤ 6.2083 := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hcard,
      div_le_iff₀ (by positivity : (0 : ℝ) < 100000000^168)]
    have hn : (10000 : ℝ) * (∏ p ∈ headPrimes, (headMassNumerator p : ℝ)) ≤
        62083 * (100000000 : ℝ)^168 := by exact_mod_cast hnum
    nlinarith only [hn]
  have hsub : N.primesLE.filter (· ≤ 1000) ⊆ headPrimes := by
    intro p hp
    rw [← head_prime_table]
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_filter.mp hp).2,
      Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1⟩
  have hpp (p : ℕ) (hp : p ∈ headPrimes) : p.Prime := by
    rw [← head_prime_table] at hp
    exact Nat.prime_of_mem_primesLE hp
  have hn (p : ℕ) (hp : p.Prime) : 0 ≤ primeWeight p / ((p : ℝ)-1) := by
    have hw := f_nonneg p
    rw [f_prime hp] at hw
    apply div_nonneg hw
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  calc _ ≤ ∏ p ∈ headPrimes, (1 + primeWeight p / ((p : ℝ)-1)) :=
         Finset.prod_le_prod_of_subset_of_one_le₀ hsub
           (fun p hp => by linarith [hn p (hpp p (hsub hp))])
           (fun p hp _ => by linarith [hn p (hpp p hp)])
       _ ≤ ∏ p ∈ headPrimes, (headMassNumerator p : ℝ)/100000000 :=
         Finset.prod_le_prod₀ (fun p hp => by linarith [hn p (hpp p hp)])
           (fun p hp => head_mass_factor_le hp)
       _ ≤ _ := hreal


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- LEAF. Tail of (2.11): `Π_{1000 < p ≤ N} (1 + (((p-1)/(p-2))^{11/4} - 1)/(p-1)) ≤ 1.0007`;
the true value is below 1.00036, the log of the factor is about `2.75/p²`, so Mathlib's
`θ(x) ≤ log 4 · x` with partial summation suffices. Vaughan 1977 p. 96, proof of (2.11), with
(2.13). Unit U-1525. -/
theorem C1_tail (N : ℕ) :
    ∏ p ∈ N.primesLE.filter (fun p => ¬ p ≤ 1000), (1 + primeWeight p / ((p : ℝ) - 1))
      ≤ 1.0007 := by
  classical
  have rpow_11_4_le_cubic {x : ℝ} (hx : 0 < x) :
      x ^ (11/4 : ℝ) ≤ (3*x^3+x^2)/4 := by
    have h := Real.geom_mean_le_arith_mean2_weighted
      (w₁ := (3/4 : ℝ)) (w₂ := (1/4 : ℝ)) (p₁ := x^3) (p₂ := x^2)
      (by norm_num) (by norm_num) (by positivity) (by positivity) (by norm_num)
    rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx.le,
      ← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le, ← Real.rpow_add hx] at h
    norm_num at h
    nlinarith only [h]
  have mass_tail_factor_le {p : ℕ} (hp : 1000 < p) :
      primeWeight p / ((p : ℝ)-1) ≤ (2.77 : ℝ) / (p : ℝ)^2 := by
    have hp1 : (1001 : ℝ) ≤ p := by exact_mod_cast hp
    have hd2 : (0 : ℝ) < p-2 := by linarith
    have hd1 : (0 : ℝ) < p-1 := by linarith
    let t : ℝ := 1 / ((p : ℝ)-2)
    have ht0 : 0 ≤ t := by positivity
    have ht : t ≤ 1/999 := by
      dsimp [t]
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    have ht2 : t^2 ≤ (1/999 : ℝ)^2 := pow_le_pow_left₀ ht0 ht 2
    have hc : 11/4 + 5/2*t + 3/4*t^2 ≤ (2.753 : ℝ) := by nlinarith
    have hr : ((p : ℝ)-1)/((p : ℝ)-2) = 1+t := by dsimp [t]; field_simp; ring
    have hpow := rpow_11_4_le_cubic (x := 1+t) (by positivity)
    have hm := mul_le_mul_of_nonneg_right hc ht0
    have hw : primeWeight p ≤ 2.753*t := by
      unfold primeWeight
      rw [if_neg (by omega : p ≠ 2), hr]
      nlinarith only [hpow, hm]
    have hd : (p : ℝ)^2 ≤ 1.004*((p : ℝ)-2)*((p : ℝ)-1) := by
      nlinarith [sq_nonneg ((p : ℝ)-1001)]
    calc _ ≤ (2.753*t)/((p : ℝ)-1) := div_le_div_of_nonneg_right hw hd1.le
         _ = 2.753 / (((p : ℝ)-2)*((p : ℝ)-1)) := by dsimp [t]; field_simp [hd1.ne', hd2.ne'] <;> ring
         _ ≤ (2.753*1.004) / (p : ℝ)^2 := by
           rw [div_le_div_iff₀ (mul_pos hd2 hd1) (sq_pos_of_pos (by linarith : (0 : ℝ)<p))]
           nlinarith only [hd]
         _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
  have taskSmall (s : Finset ℕ) (hs : ∀ k ∈ s, 5 ≤ k) :
      ∑ k ∈ s, 1 / (k : ℝ)^2 ≤ 0.223 := by
    let M := max 20 (s.sup id)
    have hM : 20 ≤ M := le_max_left _ _
    have hsub : s ⊆ Icc 5 M := by
      intro k hk
      exact mem_Icc.mpr ⟨hs k hk, (Finset.le_sup (f := id) hk).trans (le_max_right _ _)⟩
    have he : Icc 5 M = Icc (5 : ℕ) 20 ∪ Ioc 20 M := by
      ext k
      simp only [mem_union, mem_Icc, mem_Ioc]
      omega
    have hd : Disjoint (Icc (5 : ℕ) 20) (Ioc 20 M) := by
      apply Finset.disjoint_left.mpr
      intro k hk1 hk2
      have := (mem_Icc.mp hk1).2
      have := (mem_Ioc.mp hk2).1
      omega
    have hnum : (∑ k ∈ Icc (5 : ℕ) 20, 1 / (k : ℝ)^2) + 1/20 ≤ 0.223 := by
      norm_num [show Icc (5 : ℕ) 20 = ({5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20} : Finset ℕ) by decide]
    calc _ ≤ ∑ k ∈ Icc 5 M, 1 / (k : ℝ)^2 :=
           sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
         _ = (∑ k ∈ Icc (5 : ℕ) 20, 1 / (k : ℝ)^2) + ∑ k ∈ Ioc 20 M, 1 / (k : ℝ)^2 := by rw [he, sum_union hd]
         _ ≤ (∑ k ∈ Icc (5 : ℕ) 20, 1 / (k : ℝ)^2) + 1/20 := by
           gcongr
           have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (by norm_num : (20 : ℕ) ≠ 0) hM
           simp only [← one_div] at h
           exact h.trans (by simp [one_div])
         _ ≤ _ := hnum
  have taskBlock (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 1050 ≤ p) :
      ∑ p ∈ s, 1/(p : ℝ)^2 ≤ (48/(210 : ℝ)^2)*
        ∑ k ∈ Icc 5 (s.sup (fun p => p/210)), 1/(k : ℝ)^2 := by
    classical
    let M := s.sup (fun p => p/210)
    let R := (range 210).filter (fun r => r.Coprime 210)
    let T := (Icc 5 M).product R
    let e : ℕ → ℕ × ℕ := fun p => (p/210,p%210)
    have hinj : Set.InjOn e (↑s : Set ℕ) := by
      intro p hp q hq he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      dsimp [e] at h1 h2
      omega
    have hsub : s.image e ⊆ T := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
      obtain ⟨hprime,hp0⟩ := hs p hp
      have hcop : p.Coprime 210 := hprime.coprime_iff_not_dvd.mpr (by
        intro hd
        have := Nat.le_of_dvd (by norm_num : 0 < 210) hd
        omega)
      have hmod : (p%210).Coprime 210 := (ZMod.coprime_mod_iff_coprime p 210).mpr hcop
      change (p / 210, p % 210) ∈ T
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, Finset.le_sup (f := fun p => p/210) hp⟩,
        mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by norm_num)),hmod⟩⟩
    have hcard : R.card = 48 := by decide +kernel
    calc _ ≤ ∑ p ∈ s, (1/(210 : ℝ)^2)*(1/(p/210 : ℕ)^2 : ℝ) := by
           apply sum_le_sum
           intro p hp
           have hp0 := (hs p hp).2
           have hk : (0 : ℝ) < (p/210 : ℕ) := by exact_mod_cast (show 0 < p/210 by omega)
           have hpl : (210 : ℝ)*(p/210 : ℕ) ≤ p := by exact_mod_cast (show 210*(p/210) ≤ p by omega)
           have hpp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
           rw [one_div_mul_one_div, ← mul_pow]
           exact one_div_le_one_div_of_le (sq_pos_of_pos (mul_pos (by norm_num) hk))
             (pow_le_pow_left₀ (by positivity) hpl 2)
         _ = ∑ x ∈ s.image e, (1/(210 : ℝ)^2)*(1/(x.1 : ℝ)^2) := by
           rw [sum_image hinj]
         _ ≤ ∑ x ∈ T, (1/(210 : ℝ)^2)*(1/(x.1 : ℝ)^2) :=
           sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
         _ = _ := by
           dsimp [T]
           rw [sum_product]
           simp only [sum_const, nsmul_eq_mul, hcard]
           rw [← mul_sum]
           dsimp [M]
           rw [← mul_sum]
           ring
  have taskPrimeTail (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 1000 < p) :
      (2.77 : ℝ)*(∑ p ∈ s, 1/(p : ℝ)^2) ≤ 0.000696 := by
    classical
    let L := s.filter (fun p => p < 1050)
    let H := s.filter (fun p => 1050 ≤ p)
    have he : s = L ∪ H := by
      ext p
      by_cases hp : p ∈ s <;> simp [L, H, hp] <;> omega
    have hd : Disjoint L H := by
      apply disjoint_left.mpr
      intro p hp hq
      have := (mem_filter.mp hp).2
      have := (mem_filter.mp hq).2
      omega
    have hsub : L ⊆ ({1009,1013,1019,1021,1031,1033,1039,1049} : Finset ℕ) := by
      intro p hp
      obtain ⟨hps, hp1⟩ := mem_filter.mp hp
      obtain ⟨hprime,hp0⟩ := hs p hps
      interval_cases p
      all_goals norm_num at hprime
      all_goals norm_num
    have hL : ∑ p ∈ L, 1/(p : ℝ)^2 ≤ 8/(1000 : ℝ)^2 := by
      calc _ ≤ ∑ p ∈ ({1009,1013,1019,1021,1031,1033,1039,1049} : Finset ℕ), 1/(p : ℝ)^2 :=
             sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
           _ ≤ _ := by norm_num
    have hH := taskBlock H (fun p hp => ⟨(hs p (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩)
    have hk := taskSmall (Icc 5 (H.sup (fun p => p/210))) (fun k hk => (mem_Icc.mp hk).1)
    have hH2 : ∑ p ∈ H, 1/(p : ℝ)^2 ≤ (48/(210 : ℝ)^2)*0.223 :=
      hH.trans (mul_le_mul_of_nonneg_left hk (by norm_num))
    rw [he, sum_union hd]
    nlinarith only [hL,hH2]
  let S := N.primesLE.filter (fun p => ¬ p ≤ 1000)
  have hs (p : ℕ) (hp : p ∈ S) : p.Prime ∧ 1000 < p := by
    obtain ⟨hp,hp0⟩ := mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hp).2, by omega⟩
  have hn (p : ℕ) (hp : p ∈ S) : 0 ≤ primeWeight p/((p : ℝ)-1) := by
    have hpr := (hs p hp).1
    have hw : 0 ≤ primeWeight p := by rw [← f_prime hpr]; exact f_nonneg _
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
    exact div_nonneg hw (by linarith)
  have hsum : ∑ p ∈ S, primeWeight p/((p : ℝ)-1) ≤ 0.000696 := by
    calc _ ≤ ∑ p ∈ S, (2.77 : ℝ)/(p : ℝ)^2 :=
           sum_le_sum (fun p hp => mass_tail_factor_le (hs p hp).2)
         _ = (2.77 : ℝ)*∑ p ∈ S, 1/(p : ℝ)^2 := by rw [mul_sum]; congr 1; ext p; ring
         _ ≤ _ := taskPrimeTail S hs
  calc _ ≤ ∏ p ∈ S, Real.exp (primeWeight p/((p : ℝ)-1)) :=
         prod_le_prod₀ (fun p hp => by linarith [hn p hp])
           (fun p hp => by simpa only [add_comm] using Real.add_one_le_exp (primeWeight p/((p : ℝ)-1)))
       _ = Real.exp (∑ p ∈ S, primeWeight p/((p : ℝ)-1)) := (Real.exp_sum _ _).symm
       _ ≤ Real.exp 0.000696 := Real.exp_le_exp.mpr hsum
       _ ≤ 1/(1-(0.000696 : ℝ)) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
       _ ≤ _ := by norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- LEAF. Head of (2.12): `Π_{p ≤ min(N,1000)} (1 + p^{3/8}(((p-1)/(p-2))^{11/4} - 1)/(p-1))
≤ 14.17`; numerically the head to 1000 is 14.1644. Vaughan 1977 p. 96, proof of (2.12).
Unit U-1525. -/
theorem C2_head (N : ℕ) :
    ∏ p ∈ N.primesLE.filter (· ≤ 1000),
      (1 + (p : ℝ) ^ (3 / 8 : ℝ) * primeWeight p / ((p : ℝ) - 1)) ≤ 14.17 := by
  have hc : ∀ p ∈ headPrimes, 100000000 ≤ headMassNumerator p ∧ (p = 2 ∨
      p^3 * 1000000^8 ≤ (headMomentNumerator p)^8) := by
    intro p hp
    fin_cases hp <;> decide +kernel
  have hnum : 100 * (∏ p ∈ headPrimes,
      (100000000000000 + headMomentNumerator p*(headMassNumerator p-100000000))) ≤
      1417 * 100000000000000^168 := by decide +kernel
  have hcard : headPrimes.card = 168 := by decide +kernel
  have heprod : (∏ p ∈ headPrimes,
      (1 + (headMomentNumerator p : ℝ)/1000000 *
        ((headMassNumerator p : ℝ)/100000000-1))) =
      (∏ p ∈ headPrimes,
        ((100000000000000 + headMomentNumerator p*(headMassNumerator p-100000000) : ℕ) : ℝ)) /
          100000000000000^168 := by
    calc
      _ = ∏ p ∈ headPrimes,
          ((100000000000000 + headMomentNumerator p*(headMassNumerator p-100000000) : ℕ) : ℝ) /
            100000000000000 := by
        apply Finset.prod_congr rfl
        intro p hp
        push_cast [Nat.cast_sub (hc p hp).1]
        ring
      _ = _ := by rw [Finset.prod_div_distrib, Finset.prod_const, hcard]
  have hreal : (∏ p ∈ headPrimes,
      (1 + (headMomentNumerator p : ℝ)/1000000 *
        ((headMassNumerator p : ℝ)/100000000-1))) ≤ 14.17 := by
    rw [heprod, div_le_iff₀ (by positivity : (0 : ℝ) < 100000000000000^168)]
    have hn : (100 : ℝ) * (∏ p ∈ headPrimes,
        ((100000000000000 + headMomentNumerator p*(headMassNumerator p-100000000) : ℕ) : ℝ)) ≤
          1417 * (100000000000000 : ℝ)^168 := by exact_mod_cast hnum
    nlinarith only [hn]
  have hpp (p : ℕ) (hp : p ∈ headPrimes) : p.Prime := by
    have hm : p ∈ (1000 : ℕ).primesLE := by rwa [head_prime_table]
    exact Nat.prime_of_mem_primesLE hm
  have hw (p : ℕ) (hp : p ∈ headPrimes) : 0 ≤ primeWeight p := by
    have h := f_nonneg p
    rwa [f_prime (hpp p hp)] at h
  have hd (p : ℕ) (hp : p ∈ headPrimes) : (0 : ℝ) < p-1 := by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hpp p hp).two_le
    linarith
  have hfac (p : ℕ) (hp : p ∈ headPrimes) :
      1 + (p : ℝ)^(3/8 : ℝ)*primeWeight p/((p : ℝ)-1) ≤
        1 + (headMomentNumerator p : ℝ)/1000000 *
          ((headMassNumerator p : ℝ)/100000000-1) := by
    by_cases h2 : p = 2
    · subst p
      norm_num [primeWeight, headMassNumerator]
    have hnat := (hc p hp).2.resolve_left h2
    have hpow : (p : ℝ)^(3 : ℕ) ≤ ((headMomentNumerator p : ℝ)/1000000)^(8 : ℕ) := by
      rw [div_pow, le_div_iff₀ (by positivity : (0 : ℝ) < 1000000^8)]
      exact_mod_cast hnat
    have hr : (p : ℝ)^(3/8 : ℝ) ≤ (headMomentNumerator p : ℝ)/1000000 := by
      apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (Nat.cast_nonneg p) _)
        (by positivity) (by norm_num : (0 : ℝ)<8)).mp
      rw [← Real.rpow_mul (Nat.cast_nonneg p)]
      norm_num
      exact hpow
    have hmass : primeWeight p/((p : ℝ)-1) ≤ (headMassNumerator p : ℝ)/100000000-1 := by
      linarith [head_mass_factor_le hp]
    have hmul := mul_le_mul hr hmass (div_nonneg (hw p hp) (hd p hp).le) (by positivity)
    calc _ = 1 + (p : ℝ)^(3/8 : ℝ) * (primeWeight p/((p : ℝ)-1)) := by ring
         _ ≤ _ := by linarith only [hmul]
  have hsub : N.primesLE.filter (· ≤ 1000) ⊆ headPrimes := by
    intro p hp
    rw [← head_prime_table]
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_filter.mp hp).2,
      Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1⟩
  have hn (p : ℕ) (hp : p ∈ headPrimes) :
      0 ≤ (p : ℝ)^(3/8 : ℝ)*primeWeight p/((p : ℝ)-1) :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hw p hp)) (hd p hp).le
  calc _ ≤ ∏ p ∈ headPrimes, (1 + (p : ℝ)^(3/8 : ℝ)*primeWeight p/((p : ℝ)-1)) :=
         Finset.prod_le_prod_of_subset_of_one_le₀ hsub
           (fun p hp => by linarith [hn p (hsub hp)])
           (fun p hp _ => by linarith [hn p hp])
       _ ≤ ∏ p ∈ headPrimes, (1 + (headMomentNumerator p : ℝ)/1000000 *
           ((headMassNumerator p : ℝ)/100000000-1)) :=
         Finset.prod_le_prod₀ (fun p hp => by linarith [hn p hp]) hfac
       _ ≤ _ := hreal


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- LEAF. Tail of (2.12): `Π_{1000 < p ≤ N} (1 + p^{3/8}(((p-1)/(p-2))^{11/4} - 1)/(p-1)) ≤ 1.02`;
the true value is below 1.0071, the log of the factor is about `2.75 p^{-13/8}`. Vaughan 1977
p. 96, proof of (2.12), with (2.13). Unit U-1525. -/
theorem C2_tail (N : ℕ) :
    ∏ p ∈ N.primesLE.filter (fun p => ¬ p ≤ 1000),
      (1 + (p : ℝ) ^ (3 / 8 : ℝ) * primeWeight p / ((p : ℝ) - 1)) ≤ 1.02 := by
  classical
  have rpow_11_4_le_cubic {x : ℝ} (hx : 0 < x) :
      x ^ (11/4 : ℝ) ≤ (3*x^3+x^2)/4 := by
    have h := Real.geom_mean_le_arith_mean2_weighted
      (w₁ := (3/4 : ℝ)) (w₂ := (1/4 : ℝ)) (p₁ := x^3) (p₂ := x^2)
      (by norm_num) (by norm_num) (by positivity) (by positivity) (by norm_num)
    rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx.le,
      ← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le, ← Real.rpow_add hx] at h
    norm_num at h
    nlinarith only [h]
  have mass_tail_factor_le {p : ℕ} (hp : 1000 < p) :
      primeWeight p / ((p : ℝ)-1) ≤ (2.77 : ℝ) / (p : ℝ)^2 := by
    have hp1 : (1001 : ℝ) ≤ p := by exact_mod_cast hp
    have hd2 : (0 : ℝ) < p-2 := by linarith
    have hd1 : (0 : ℝ) < p-1 := by linarith
    let t : ℝ := 1 / ((p : ℝ)-2)
    have ht0 : 0 ≤ t := by positivity
    have ht : t ≤ 1/999 := by
      dsimp [t]
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    have ht2 : t^2 ≤ (1/999 : ℝ)^2 := pow_le_pow_left₀ ht0 ht 2
    have hc : 11/4 + 5/2*t + 3/4*t^2 ≤ (2.753 : ℝ) := by nlinarith
    have hr : ((p : ℝ)-1)/((p : ℝ)-2) = 1+t := by dsimp [t]; field_simp; ring
    have hpow := rpow_11_4_le_cubic (x := 1+t) (by positivity)
    have hm := mul_le_mul_of_nonneg_right hc ht0
    have hw : primeWeight p ≤ 2.753*t := by
      unfold primeWeight
      rw [if_neg (by omega : p ≠ 2), hr]
      nlinarith only [hpow, hm]
    have hd : (p : ℝ)^2 ≤ 1.004*((p : ℝ)-2)*((p : ℝ)-1) := by
      nlinarith [sq_nonneg ((p : ℝ)-1001)]
    calc _ ≤ (2.753*t)/((p : ℝ)-1) := div_le_div_of_nonneg_right hw hd1.le
         _ = 2.753 / (((p : ℝ)-2)*((p : ℝ)-1)) := by dsimp [t]; field_simp [hd1.ne', hd2.ne'] <;> ring
         _ ≤ (2.753*1.004) / (p : ℝ)^2 := by
           rw [div_le_div_iff₀ (mul_pos hd2 hd1) (sq_pos_of_pos (by linarith : (0 : ℝ)<p))]
           nlinarith only [hd]
         _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
  have taskMomentPoint {p : ℕ} (hp : 1000 < p) :
      (p : ℝ)^(3/8 : ℝ)*primeWeight p/((p : ℝ)-1) ≤
        (2.77/2.37 : ℝ)*(1/((p : ℝ)*Real.sqrt p)) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hbase : (2.37 : ℝ)^8 ≤ p := by
      calc (2.37 : ℝ)^8 ≤ (1001 : ℝ) := by norm_num
           _ ≤ p := by exact_mod_cast hp
    have hsmall : (2.37 : ℝ) ≤ (p : ℝ)^(1/8 : ℝ) := by
      apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 2.37)
        (Real.rpow_nonneg hp0.le _) (by norm_num : (8 : ℕ) ≠ 0)).mp
      rw [← Real.rpow_natCast ((p : ℝ)^(1/8 : ℝ)) 8, ← Real.rpow_mul hp0.le]
      norm_num
      norm_num at hbase
      exact hbase
    have hsplit : (p : ℝ)^(3/8 : ℝ)*(p : ℝ)^(1/8 : ℝ) = Real.sqrt p := by
      rw [← Real.rpow_add hp0, show (3/8 : ℝ)+1/8 = 1/2 by norm_num, ← Real.sqrt_eq_rpow]
    have hp38 : (p : ℝ)^(3/8 : ℝ) ≤ Real.sqrt p/2.37 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2.37)]
      have h := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hp0.le (3/8 : ℝ))
      rwa [hsplit] at h
    have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
    have hmass := mass_tail_factor_le hp
    calc _ = (p : ℝ)^(3/8 : ℝ)*(primeWeight p/((p : ℝ)-1)) := by ring
         _ ≤ (p : ℝ)^(3/8 : ℝ)*((2.77 : ℝ)/(p : ℝ)^2) :=
           mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hp0.le _)
         _ ≤ (Real.sqrt p/2.37)*((2.77 : ℝ)/(p : ℝ)^2) :=
           mul_le_mul_of_nonneg_right hp38 (by positivity)
         _ = _ := by
           have he := Real.sq_sqrt hp0.le
           field_simp [hp0.ne', hs.ne']
           nlinarith [he]
  have taskTail122 (s : Finset ℕ) (hs : ∀ k ∈ s, 122 ≤ k) :
      ∑ k ∈ s, 1/((k : ℝ)*Real.sqrt k) ≤ 2/Real.sqrt 121 := by
    classical
    have anti : AntitoneOn (fun x : ℝ => x^(-3/2 : ℝ)) (Set.Ici 121) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [Set.mem_Ici.mp hx]) hxy (by norm_num)
    have hInt := anti.tsum_comp_add_le_integral 121
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3/2 : ℝ) < -1) (by norm_num))
      (fun t ht => Real.rpow_nonneg (by have h := Set.mem_Ioi.mp ht; norm_num at h; linarith) _)
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-3/2 : ℝ) < -1) (by norm_num)] at hInt
    have he (k : ℕ) : (k : ℝ)^(-3/2 : ℝ) = 1/((k : ℝ)*Real.sqrt k) := by
      rw [show (-3/2 : ℝ) = -(1+1/2) by norm_num, Real.rpow_neg (Nat.cast_nonneg k)]
      by_cases hk : k = 0
      · subst k; norm_num
      · rw [Real.rpow_add (by exact_mod_cast Nat.pos_of_ne_zero hk), Real.rpow_one,
          ← Real.sqrt_eq_rpow, one_div]
    have hInt2 : (∑' n : ℕ, ((n+121+1 : ℕ) : ℝ)^(-3/2 : ℝ)) ≤ 2/Real.sqrt 121 := by
      convert hInt using 1
      norm_num
    have hsum : Summable (fun n : ℕ => (n : ℝ)^(-3/2 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have hshift : Summable (fun n : ℕ => ((n+121+1 : ℕ) : ℝ)^(-3/2 : ℝ)) := by
      simpa only [Nat.add_assoc] using (summable_nat_add_iff 122).mpr hsum
    let e : ℕ → ℕ := fun k => k-122
    have hinj : Set.InjOn e (↑s : Set ℕ) := by
      intro k hk l hl he
      dsimp [e] at he
      have := hs k hk
      have := hs l hl
      omega
    calc _ = ∑ n ∈ s.image e, ((n+121+1 : ℕ) : ℝ)^(-3/2 : ℝ) := by
           rw [sum_image hinj]
           apply sum_congr rfl
           intro k hk
           have hk0 := hs k hk
           rw [show e k+121+1 = k by dsimp [e]; omega, he]
         _ ≤ ∑' n : ℕ, ((n+121+1 : ℕ) : ℝ)^(-3/2 : ℝ) :=
           hshift.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
         _ ≤ _ := hInt2
  have taskSharpSeries (s : Finset ℕ) (hs : ∀ k ∈ s, 34 ≤ k) :
      ∑ k ∈ s, 1/((k : ℝ)*Real.sqrt k) ≤ 0.345915 := by
    classical
    let v : ℕ → ℕ := fun k => match k with
      | 34 => 504408
      | 35 => 482946
      | 36 => 462963
      | 37 => 444322
      | 38 => 426899
      | 39 => 410586
      | 40 => 395285
      | 41 => 380912
      | 42 => 367389
      | 43 => 354648
      | 44 => 342627
      | 45 => 331270
      | 46 => 320526
      | 47 => 310352
      | 48 => 300704
      | 49 => 291546
      | 50 => 282843
      | 51 => 274565
      | 52 => 266683
      | 53 => 259171
      | 54 => 252006
      | 55 => 245164
      | 56 => 238627
      | 57 => 232375
      | 58 => 226391
      | 59 => 220660
      | 60 => 215166
      | 61 => 209897
      | 62 => 204839
      | 63 => 199982
      | 64 => 195313
      | 65 => 190823
      | 66 => 186503
      | 67 => 182343
      | 68 => 178336
      | 69 => 174473
      | 70 => 170747
      | 71 => 167153
      | 72 => 163683
      | 73 => 160331
      | 74 => 157092
      | 75 => 153961
      | 76 => 150932
      | 77 => 148001
      | 78 => 145164
      | 79 => 142417
      | 80 => 139755
      | 81 => 137175
      | 82 => 134673
      | 83 => 132247
      | 84 => 129892
      | 85 => 127607
      | 86 => 125387
      | 87 => 123232
      | 88 => 121137
      | 89 => 119101
      | 90 => 117122
      | 91 => 115197
      | 92 => 113324
      | 93 => 111501
      | 94 => 109726
      | 95 => 107998
      | 96 => 106315
      | 97 => 104675
      | 98 => 103077
      | 99 => 101519
      | 100 => 100000
      | 101 => 98519
      | 102 => 97074
      | 103 => 95664
      | 104 => 94287
      | 105 => 92943
      | 106 => 91631
      | 107 => 90350
      | 108 => 89098
      | 109 => 87874
      | 110 => 86679
      | 111 => 85510
      | 112 => 84368
      | 113 => 83250
      | 114 => 82157
      | 115 => 81088
      | 116 => 80042
      | 117 => 79018
      | 118 => 78015
      | 119 => 77034
      | 120 => 76073
      | 121 => 75132
      | _ => 0
    have hc : ∀ k ∈ Icc 34 121, 100000000^2 ≤ (v k)^2*k^3 := by
      intro k hk
      fin_cases hk <;> decide +kernel
    have hsumv : (∑ k ∈ Icc 34 121, v k) ≤ 16409500 := by decide +kernel
    have hhead : ∑ k ∈ Icc (34 : ℕ) 121, 1/((k : ℝ)*Real.sqrt k) ≤ 0.164095 := by
      calc _ ≤ ∑ k ∈ Icc (34 : ℕ) 121, (v k : ℝ)/100000000 := by
             apply sum_le_sum
             intro k hk
             have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := (mem_Icc.mp hk).1; omega)
             have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
             have hnat := hc k hk
             have hreal : (100000000 : ℝ)^2 ≤ (v k : ℝ)^2*(k : ℝ)^3 := by exact_mod_cast hnat
             have he := Real.sq_sqrt hk0.le
             have hsq : (100000000 : ℝ)^2 ≤ ((v k : ℝ)*(k : ℝ)*Real.sqrt k)^2 := by
               calc _ ≤ (v k : ℝ)^2*(k : ℝ)^3 := hreal
                    _ = _ := by rw [mul_pow,he]; ring
             have hnn : 0 ≤ (v k : ℝ)*(k : ℝ)*Real.sqrt k := by positivity
             have hh : (100000000 : ℝ) ≤ (v k : ℝ)*(k : ℝ)*Real.sqrt k := by nlinarith only [hsq,hnn]
             rw [div_le_div_iff₀ (mul_pos hk0 hs) (by norm_num : (0 : ℝ)<100000000)]
             nlinarith only [hh]
           _ = (∑ k ∈ Icc 34 121, (v k : ℝ))/100000000 := (sum_div _ _ _).symm
           _ ≤ _ := by
             have h : (∑ k ∈ Icc (34 : ℕ) 121, (v k : ℝ)) ≤ 16409500 := by exact_mod_cast hsumv
             linarith
    let L := s.filter (fun k => k ≤ 121)
    let H := s.filter (fun k => ¬ k ≤ 121)
    have he : s = L ∪ H := by
      ext k
      by_cases hk : k ∈ s <;> simp [L,H,hk] <;> omega
    have hd : Disjoint L H := by
      apply disjoint_left.mpr
      intro k hk hl
      exact (mem_filter.mp hl).2 (mem_filter.mp hk).2
    have hL : ∑ k ∈ L, 1/((k : ℝ)*Real.sqrt k) ≤ 0.164095 := by
      calc _ ≤ ∑ k ∈ Icc (34 : ℕ) 121, 1/((k : ℝ)*Real.sqrt k) :=
             sum_le_sum_of_subset_of_nonneg (fun k hk => mem_Icc.mpr ⟨hs k (mem_filter.mp hk).1,(mem_filter.mp hk).2⟩) (by intros; positivity)
           _ ≤ _ := hhead
    have hH := taskTail122 H (fun k hk => by have := (mem_filter.mp hk).2; omega)
    have hH2 : ∑ k ∈ H, 1/((k : ℝ)*Real.sqrt k) ≤ (2/11 : ℝ) := by
      convert hH using 1 <;> norm_num
    rw [he,sum_union hd]
    linarith only [hL,hH2]
  have taskSqrtBlock (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 1020 ≤ p) :
      ∑ p ∈ s, 1/((p : ℝ)*Real.sqrt p) ≤ (8/((30 : ℝ)*Real.sqrt 30))*
        ∑ k ∈ Icc 34 (s.sup (fun p => p/30)), 1/((k : ℝ)*Real.sqrt k) := by
    classical
    let M := s.sup (fun p => p/30)
    let R := (range 30).filter (fun r => r.Coprime 30)
    let T := (Icc 34 M).product R
    let e : ℕ → ℕ × ℕ := fun p => (p/30,p%30)
    have hinj : Set.InjOn e (↑s : Set ℕ) := by
      intro p hp q hq he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      dsimp [e] at h1 h2
      omega
    have hsub : s.image e ⊆ T := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
      obtain ⟨hprime,hp0⟩ := hs p hp
      have hcop : p.Coprime 30 := hprime.coprime_iff_not_dvd.mpr (by
        intro hd
        have := Nat.le_of_dvd (by norm_num : 0 < 30) hd
        omega)
      have hmod : (p%30).Coprime 30 := (ZMod.coprime_mod_iff_coprime p 30).mpr hcop
      change (p / 30, p % 30) ∈ T
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, Finset.le_sup (f := fun p => p/30) hp⟩,
        mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by norm_num)),hmod⟩⟩
    have hcard : R.card = 8 := by decide +kernel
    calc _ ≤ ∑ p ∈ s, (1/((30 : ℝ)*Real.sqrt 30))*(1/((p/30 : ℕ)*Real.sqrt (p/30 : ℕ)) : ℝ) := by
           apply sum_le_sum
           intro p hp
           have hp0 := (hs p hp).2
           have hk : (0 : ℝ) < (p/30 : ℕ) := by exact_mod_cast (show 0 < p/30 by omega)
           have hpl : (30 : ℝ)*(p/30 : ℕ) ≤ p := by exact_mod_cast (show 30*(p/30) ≤ p by omega)
           have hd : (30 : ℝ)*(p/30 : ℕ)*Real.sqrt ((30 : ℝ)*(p/30 : ℕ)) ≤ (p : ℝ)*Real.sqrt p :=
             mul_le_mul hpl (Real.sqrt_le_sqrt hpl) (Real.sqrt_nonneg _) (Nat.cast_nonneg p)
           have hden : 0 < (30 : ℝ)*(p/30 : ℕ)*Real.sqrt ((30 : ℝ)*(p/30 : ℕ)) := by positivity
           have hbound := one_div_le_one_div_of_le hden hd
           calc _ ≤ 1/((30 : ℝ)*(p/30 : ℕ)*Real.sqrt ((30 : ℝ)*(p/30 : ℕ))) := hbound
                _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 30)]; ring
         _ = ∑ x ∈ s.image e, (1/((30 : ℝ)*Real.sqrt 30))*(1/((x.1 : ℝ)*Real.sqrt x.1)) := by
           rw [sum_image hinj]
         _ ≤ ∑ x ∈ T, (1/((30 : ℝ)*Real.sqrt 30))*(1/((x.1 : ℝ)*Real.sqrt x.1)) :=
           sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
         _ = _ := by
           dsimp [T]
           rw [sum_product]
           simp only [sum_const, nsmul_eq_mul, hcard]
           rw [← mul_sum]
           dsimp [M]
           rw [← mul_sum]
           ring
  have taskSharpPrime (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 1000 < p) :
      ∑ p ∈ s, 1/((p : ℝ)*Real.sqrt p) ≤ 0.01694 := by
    classical
    let L := s.filter (fun p => p < 1020)
    let H := s.filter (fun p => 1020 ≤ p)
    have he : s = L ∪ H := by
      ext p
      by_cases hp : p ∈ s <;> simp [L,H,hp] <;> omega
    have hd : Disjoint L H := by
      apply disjoint_left.mpr
      intro p hp hq
      have := (mem_filter.mp hp).2
      have := (mem_filter.mp hq).2
      omega
    have hsub : L ⊆ ({1009,1013,1019} : Finset ℕ) := by
      intro p hp
      obtain ⟨hps,hp1⟩ := mem_filter.mp hp
      obtain ⟨hprime,hp0⟩ := hs p hps
      interval_cases p
      all_goals norm_num at hprime
      all_goals norm_num
    have hL : ∑ p ∈ L, 1/((p : ℝ)*Real.sqrt p) ≤ 3/31000 := by
      have hcard : L.card ≤ 3 := by simpa using card_le_card hsub
      calc _ ≤ ∑ p ∈ L, (1/31000 : ℝ) := by
             apply sum_le_sum
             intro p hp
             have hp0 : (1000 : ℝ) ≤ p := by exact_mod_cast (hs p (mem_filter.mp hp).1).2.le
             have hsq : (31 : ℝ) ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by linarith)
             apply one_div_le_one_div_of_le (by norm_num)
             nlinarith
           _ ≤ _ := by simp only [sum_const, nsmul_eq_mul, mul_one_div]; gcongr; exact_mod_cast hcard
    have hH := taskSqrtBlock H (fun p hp => ⟨(hs p (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩)
    have hk := taskSharpSeries (Icc 34 (H.sup (fun p => p/30))) (fun k hk => (mem_Icc.mp hk).1)
    have hH2 : ∑ p ∈ H, 1/((p : ℝ)*Real.sqrt p) ≤
        (8/((30 : ℝ)*Real.sqrt 30))*(0.345915 : ℝ) :=
      hH.trans (mul_le_mul_of_nonneg_left hk (by positivity))
    have h30 : (5.477 : ℝ) ≤ Real.sqrt 30 := Real.le_sqrt_of_sq_le (by norm_num)
    have hB : (8/((30 : ℝ)*Real.sqrt 30))*(0.345915 : ℝ) ≤ (8/(30*5.477 : ℝ))*(0.345915 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
    rw [he,sum_union hd]
    have hH3 := hH2.trans hB
    norm_num at hH3
    linarith
  let S := N.primesLE.filter (fun p => ¬ p ≤ 1000)
  have hs (p : ℕ) (hp : p ∈ S) : p.Prime ∧ 1000 < p := by
    obtain ⟨hp,hp0⟩ := mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hp).2, by omega⟩
  have hn (p : ℕ) (hp : p ∈ S) : 0 ≤ (p : ℝ)^(3/8 : ℝ)*primeWeight p/((p : ℝ)-1) := by
    have hpr := (hs p hp).1
    have hw : 0 ≤ primeWeight p := by rw [← f_prime hpr]; exact f_nonneg _
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) hw) (by linarith)
  have hsum : ∑ p ∈ S, (p : ℝ)^(3/8 : ℝ)*primeWeight p/((p : ℝ)-1) ≤ 0.0198 := by
    calc _ ≤ ∑ p ∈ S, (2.77/2.37 : ℝ)*(1/((p : ℝ)*Real.sqrt p)) :=
           sum_le_sum (fun p hp => taskMomentPoint (hs p hp).2)
         _ = (2.77/2.37 : ℝ)*∑ p ∈ S, 1/((p : ℝ)*Real.sqrt p) := (mul_sum _ _ _).symm
         _ ≤ (2.77/2.37 : ℝ)*0.01694 := mul_le_mul_of_nonneg_left (taskSharpPrime S hs) (by norm_num)
         _ ≤ _ := by norm_num
  calc _ ≤ ∏ p ∈ S, Real.exp ((p : ℝ)^(3/8 : ℝ)*primeWeight p/((p : ℝ)-1)) :=
         prod_le_prod₀ (fun p hp => by linarith [hn p hp])
           (fun p hp => by simpa only [add_comm] using Real.add_one_le_exp ((p : ℝ)^(3/8 : ℝ)*primeWeight p/((p : ℝ)-1)))
       _ = Real.exp (∑ p ∈ S, (p : ℝ)^(3/8 : ℝ)*primeWeight p/((p : ℝ)-1)) := (Real.exp_sum _ _).symm
       _ ≤ Real.exp 0.0198 := Real.exp_le_exp.mpr hsum
       _ ≤ (2+(0.0198 : ℝ))/(2-0.0198) := Real.exp_le_two_add_div_two_sub (by norm_num) (by norm_num)
       _ ≤ _ := by norm_num

/-! ### Assembly: `EulerMassBound 6.2130` and `EulerMomentBound`, unfolded -/

theorem primeWeight_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ primeWeight p := by
  unfold primeWeight
  split_ifs with h2
  · exact le_rfl
  · have h3 : (3 : ℝ) ≤ p := by
      have := hp.two_le
      have : 3 ≤ p := by omega
      exact_mod_cast this
    have hb : 1 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
      rw [one_le_div (by linarith)]; linarith
    have := Real.one_le_rpow hb (by norm_num : (0 : ℝ) ≤ 11 / 4)
    linarith

theorem factor_nonneg {p : ℕ} (hp : p.Prime) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ 1 + c * primeWeight p / ((p : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : 0 ≤ c * primeWeight p / ((p : ℝ) - 1) :=
    div_nonneg (mul_nonneg hc (primeWeight_nonneg hp)) (by linarith)
  linarith

/-- **(2.11) upper half, PROVED from `C1_head` and `C1_tail`**: for every `N`,
`Π_{p ≤ N} (1 + f(p)/(p-1)) ≤ 6.2130`. This is `Vaughan1977Euler.EulerMassBound 6.2130`
unfolded, the input of `statement27_of_euler` with `C = 6.2130`. -/
theorem eulerMass_62130 (N : ℕ) :
    ∏ p ∈ N.primesLE, (1 + primeWeight p / ((p : ℝ) - 1)) ≤ 6.2130 := by
  rw [← Finset.prod_filter_mul_prod_filter_not N.primesLE (fun p : ℕ => p ≤ 1000)]
  have hnn : ∀ s : Finset ℕ, s ⊆ N.primesLE →
      0 ≤ ∏ p ∈ s, (1 + primeWeight p / ((p : ℝ) - 1)) := by
    intro s hs
    apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesLE.mp (hs hp)).2
    simpa using factor_nonneg hpp 1 zero_le_one
  have h1 := C1_head N
  have h2 := C1_tail N
  have h0' := hnn (N.primesLE.filter (fun p : ℕ => ¬ p ≤ 1000)) (Finset.filter_subset _ _)
  calc _ ≤ 6.2083 * 1.0007 := mul_le_mul h1 h2 h0' (by norm_num)
    _ ≤ 6.2130 := by norm_num

/-- **(2.12), PROVED from `C2_head` and `C2_tail`**: for every `N`,
`Π_{p ≤ N} (1 + p^{3/8} f(p)/(p-1)) ≤ 14.46`. This is `Vaughan1977Euler.EulerMomentBound`
unfolded. -/
theorem eulerMoment_1446 (N : ℕ) :
    ∏ p ∈ N.primesLE, (1 + (p : ℝ) ^ (3 / 8 : ℝ) * primeWeight p / ((p : ℝ) - 1)) ≤ 14.46 := by
  rw [← Finset.prod_filter_mul_prod_filter_not N.primesLE (fun p : ℕ => p ≤ 1000)]
  have hnn : ∀ s : Finset ℕ, s ⊆ N.primesLE →
      0 ≤ ∏ p ∈ s, (1 + (p : ℝ) ^ (3 / 8 : ℝ) * primeWeight p / ((p : ℝ) - 1)) := by
    intro s hs
    apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesLE.mp (hs hp)).2
    exact factor_nonneg hpp _ (by positivity)
  have h1 := C2_head N
  have h2 := C2_tail N
  have h0' := hnn (N.primesLE.filter (fun p : ℕ => ¬ p ≤ 1000)) (Finset.filter_subset _ _)
  calc _ ≤ 14.17 * 1.02 := mul_le_mul h1 h2 h0' (by norm_num)
    _ ≤ 14.46 := by norm_num

end LeanLab.SchnirelmannBounds.Decomp1525a

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.g_prime_pow

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.g_mul

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.head_prime_table

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.head_mass_factor_le

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.C1_head

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.C2_head

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.hasSum_g_prime_power

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.summable_of_prime_power_sums

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.hasSum_g
#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.split_sum

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.hasSum_sqrt_g
#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.tail_le

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.C1_tail

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.prime_sqrt_tail_le

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.C2_tail

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.C0v_lt
#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.eulerMass_62130
#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.eulerMoment_1446

#print axioms LeanLab.SchnirelmannBounds.Decomp1525a.hasSum_g_log
