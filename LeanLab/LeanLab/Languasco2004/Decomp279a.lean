/-
Jia 1996, https://doi.org/10.4064/aa-77-3-207-287, pages 207 to 287.
AI wrote the Lean code. Goldbach is open. Analytic leaves stay OPEN.
-/
import LeanLab.Languasco2004.StatementsA

namespace LeanLab.Languasco2004.Decomp279a
open Finset Real LeanLab.Languasco2004.EncA
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 208: the basic interval length A. -/
def windowLength (N ε : ℝ) : ℝ := N ^ (7 / 108 + 12 * ε)
/-- Page 208: the localization length Y. -/
def localization (N ε : ℝ) : ℝ := N ^ (7 / 12 + ε)
/-- Page 263: even integers in the basic interval, open at its left end. -/
def window (N ε : ℝ) : Finset ℕ :=
  (Ioc ⌊N⌋₊ ⌊N + windowLength N ε⌋₊).filter Even
/-- Page 262 display 43: the restricted prime representation count T. -/
def representations (N Y : ℝ) (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun p : ℕ => p.Prime ∧ (n - p).Prime ∧
    N - Y < (p : ℝ) ∧ (p : ℝ) ≤ N ∧ ((n - p : ℕ) : ℝ) ≤ 2 * Y)).card
/-- Page 262 display 45: the singular factor C of n. -/
def singular (n : ℕ) : ℝ :=
  (∏' p : Nat.Primes, if (p : ℕ) ∣ n then 1 else
    1 - 1 / ((p : ℝ) - 1) ^ 2) *
  ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1))
/-- Page 262 display 44: the common main term. -/
def scale (N Y : ℝ) (n : ℕ) : ℝ := singular n * Y / (Real.log Y * Real.log N)
/-- Pages 262 and 263: S of A_d and z. Every prime dividing d is at least z
in the uses below, so sifting a or a divided by d gives the same count. -/
def sifted (N Y : ℝ) (n d : ℕ) (z : ℝ) : ℕ :=
  ((Icc 1 n).filter (fun a => d ∣ a ∧ (n - a).Prime ∧
    N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
    ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n → ¬ p ∣ a)).card
/-- Page 263 Lemma 22: the initial sifted term. -/
def initial (N Y : ℝ) (n : ℕ) : ℝ := sifted N Y n 1 (Y ^ (16 / 135 : ℝ))
/-- Page 265 Lemma 23: the single prime subtraction term. -/
def subtraction (N Y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)),
    (sifted N Y n p (Y ^ (16 / 135 : ℝ)) : ℝ)
/-- Page 267 display 52: the double prime recovery term Omega. -/
def recovery (N Y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)),
    ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
      Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))),
      (sifted N Y n (p * q) q : ℝ)

/-- LEAF. Page 263 Lemma 22, proved on pages 263 to 265.
The exceptional set is the set of failures of this single sieve bound. -/
theorem initial_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        initial N (localization N ε) n < 4.735124 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Page 265 Lemma 23, proved on pages 265 to 267.
This leaf controls the failures of the single subtraction bound. -/
theorem subtraction_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        6.822470 * scale N (localization N ε) n < subtraction N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Page 286 display 65, proved by Lemmas 24 to 28 on pages 269 to 286.
Only the double sieve recovery term occurs in this leaf. -/
theorem recovery_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        recovery N (localization N ε) n < 2.104057 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- `4 / p ^ 2` is summable over the primes. -/
private lemma summable_four_div_prime_sq : Summable (fun p : Nat.Primes => 4 / (p : ℝ) ^ 2) := by
  have hb : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have h4 : Summable (fun p : Nat.Primes => 4 * (p : ℝ) ^ (-2 : ℝ)) := hb.mul_left 4
  refine h4.congr (fun p => ?_)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast Nat.Prime.two_le p.prop
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by linarith
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hp0, Real.rpow_two, div_eq_mul_inv]

/-- The sifted factor `1 - 1/(p-1)^2` with the primes dividing `n` set to `1`,
written as `1 + (-u p)` with `u` summable. -/
private lemma summable_sift_factor (n : ℕ) :
    Summable (fun p : Nat.Primes => if (p : ℕ) ∣ n then 0 else 1 / ((p : ℝ) - 1) ^ 2) := by
  refine Summable.of_nonneg_of_le (f := fun p : Nat.Primes => 4 / (p : ℝ) ^ 2)
    (fun p => ?_) (fun p => ?_) summable_four_div_prime_sq
  · split_ifs <;> positivity
  · split_ifs with h
    · positivity
    · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast Nat.Prime.two_le p.prop
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

/-- The infinite product in `singular` is positive for even `n`. -/
private lemma tprod_singular_factor_pos (n : ℕ) (hn : Even n) :
    0 < ∏' p : Nat.Primes, (if (p : ℕ) ∣ n then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hgsum := summable_sift_factor n
  have hpos : ∀ p : Nat.Primes,
      0 < 1 + -(if (p : ℕ) ∣ n then 0 else 1 / ((p : ℝ) - 1) ^ 2) := by
    intro p
    by_cases h : (p : ℕ) ∣ n
    · simp only [h, ite_true]; norm_num
    · simp only [h, ite_false]
      have hpne : (p : ℕ) ≠ 2 := by
        intro he
        exact h (he ▸ (even_iff_two_dvd.mp hn))
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        have h3 : 3 ≤ (p : ℕ) := by
          have := Nat.Prime.two_le p.prop
          omega
        exact_mod_cast h3
      have hd : (1 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
      have hpos' : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by linarith
      have hlt : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
        rw [div_lt_one hpos']
        exact hd
      linarith
  have hlog : Summable (fun p : Nat.Primes =>
      Real.log (1 + -(if (p : ℕ) ∣ n then 0 else 1 / ((p : ℝ) - 1) ^ 2))) :=
    Real.summable_log_one_add_of_summable hgsum.neg
  have hmain : (0 : ℝ) <
      ∏' p : Nat.Primes, (1 + -(if (p : ℕ) ∣ n then 0 else 1 / ((p : ℝ) - 1) ^ 2)) := by
    rw [← Real.rexp_tsum_eq_tprod hpos hlog]
    exact Real.exp_pos _
  have heq : (∏' p : Nat.Primes,
        (1 + -(if (p : ℕ) ∣ n then 0 else 1 / ((p : ℝ) - 1) ^ 2)))
      = ∏' p : Nat.Primes, (if (p : ℕ) ∣ n then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    apply tprod_congr
    intro p
    by_cases h : (p : ℕ) ∣ n <;> simp [h, sub_eq_add_neg]
  rwa [heq] at hmain

/-- `singular n` is positive for even `n`. -/
private lemma singular_pos {n : ℕ} (hn : Even n) : 0 < singular n := by
  unfold singular
  refine mul_pos (tprod_singular_factor_pos n hn) ?_
  refine Finset.prod_pos (fun p hp => ?_)
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.Prime.two_le hpp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2' : (0 : ℝ) < 1 / ((p : ℝ) - 1) := one_div_pos.mpr h1
  linarith

/-- `scale` is positive. -/
private lemma scale_pos {N Y : ℝ} {n : ℕ} (hn : Even n) (hN : 1 < N) (hY : 1 < Y) :
    0 < scale N Y n := by
  unfold scale
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hlogN : 0 < Real.log N := Real.log_pos hN
  exact div_pos (mul_pos (singular_pos hn) (by linarith)) (mul_pos hlogY hlogN)

/-- `representations` reindexed by `a = n - p`: it counts the addends `a` that are
themselves prime. This is the interface between `representations` (indexed by `p`) and the
sieve terms of `singular`/`sifted` (indexed by `a`). -/
private lemma representations_eq_count (N Y : ℝ) (n : ℕ) :
    representations N Y n =
      ((Icc 1 n).filter (fun a : ℕ => a.Prime ∧ (n - a).Prime ∧
        N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧ (a : ℝ) ≤ 2 * Y)).card := by
  unfold representations
  refine Finset.card_bij (fun p _ => n - p) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hp1, hpP, hqP, hgt, hle, h2Y⟩ := hp
    have hpn : p ≤ n := by
      have := Finset.mem_range.mp hp1
      omega
    have hsub : n - (n - p) = p := Nat.sub_sub_self hpn
    have hq2 : 2 ≤ n - p := hqP.two_le
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · exact hqP
    · rw [hsub]; exact hpP
    · rw [hsub]; exact hgt
    · rw [hsub]; exact hle
    · exact h2Y
  · intro p₁ hp₁ p₂ hp₂ heq
    rw [Finset.mem_filter, Finset.mem_range] at hp₁ hp₂
    omega
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨ha1, ha2⟩, haP, hqP, hgt, hle, h2Y⟩ := ha
    have hsub : n - (n - a) = a := Nat.sub_sub_self ha2
    refine ⟨n - a, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · exact hqP
      · rw [hsub]; exact haP
      · exact hgt
      · exact hle
      · rw [hsub]; exact h2Y
    · rw [hsub]

/-- The basic window length is at most the localization length in the range `ε` of the file
(`7/108 + 12ε ≤ 7/12 + ε`). -/
private lemma windowLength_le_localization {N ε : ℝ} (hN : 1 ≤ N) (hε : 11 * ε ≤ 14 / 27) :
    windowLength N ε ≤ localization N ε := by
  unfold windowLength localization
  exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- Every `n` of the window lies below `N + localization`. This is what makes the extra
condition `a ≤ 2Y` of `representations` automatic on the sieve side. -/
private lemma window_le_N_add_localization {N ε : ℝ} (hN : 1 ≤ N)
    (hε : 11 * ε ≤ 14 / 27) {n : ℕ} (hn : n ∈ window N ε) :
    (n : ℝ) ≤ N + localization N ε := by
  obtain ⟨hnI, -⟩ := Finset.mem_filter.mp hn
  rw [Finset.mem_Ioc] at hnI
  have hA0 : 0 ≤ windowLength N ε := by
    unfold windowLength
    exact Real.rpow_nonneg (by linarith) _
  have h2 : ((⌊N + windowLength N ε⌋₊ : ℕ) : ℝ) ≤ N + windowLength N ε :=
    Nat.floor_le (by linarith)
  have h3 : (n : ℝ) ≤ ((⌊N + windowLength N ε⌋₊ : ℕ) : ℝ) := by exact_mod_cast hnI.2
  have h4 := windowLength_le_localization hN hε
  linarith

/-- The universal product obtained by removing the prime two is positive. -/
private lemma bridge_tail_product_pos :
    0 < ∏' p : Nat.Primes, (1 - if (p : ℕ) ∣ 2 then 0 else 1 / ((p : ℝ) - 1) ^ 2) := by
  have h := tprod_singular_factor_pos 2 (by norm_num)
  have heq : (∏' p : Nat.Primes, (1 - if (p : ℕ) ∣ 2 then 0 else 1 / ((p : ℝ) - 1) ^ 2)) =
      ∏' p : Nat.Primes, (if (p : ℕ) ∣ 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    apply tprod_congr
    intro p
    by_cases hp : (p : ℕ) ∣ 2 <;> simp [hp]
  rwa [heq]

/-- Every factor of the universal product without the prime two is positive. -/
private lemma bridge_tail_factor_pos (p : Nat.Primes) :
    0 < 1 - (if (p : ℕ) ∣ 2 then 0 else 1 / ((p : ℝ) - 1) ^ 2) := by
  split_ifs with hp
  · norm_num
  · have hpne : (p : ℕ) ≠ 2 := by
      intro he
      apply hp
      rw [he]
    have hp3N : 3 ≤ (p : ℕ) := by
      have h2 := p.prop.two_le
      omega
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3N
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hpos' : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos hp1
    have hlt : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
      rw [div_lt_one hpos']
      nlinarith
    linarith

/-- For even `n`, the singular series is bounded below by the universal product
whose only omitted prime is two. -/
private lemma bridge_tail_le_singular (n : ℕ) (hn : Even n) :
    (∏' p : Nat.Primes, (1 - if (p : ℕ) ∣ 2 then 0 else 1 / ((p : ℝ) - 1) ^ 2)) ≤
      singular n := by
  let loss : Nat.Primes → ℝ := fun p =>
    if (p : ℕ) ∣ n then 0 else 1 / ((p : ℝ) - 1) ^ 2
  let tailLoss : Nat.Primes → ℝ := fun p =>
    if (p : ℕ) ∣ 2 then 0 else 1 / ((p : ℝ) - 1) ^ 2
  have hln : ∀ p, 0 ≤ loss p := by
    intro p
    unfold loss
    split_ifs <;> positivity
  have hle : ∀ p, loss p ≤ tailLoss p := by
    intro p
    by_cases hp2 : (p : ℕ) ∣ 2
    · have hpn : (p : ℕ) ∣ n := by
        have hpEq : (p : ℕ) = 2 := by
          have hlo := p.prop.two_le
          have hhi := Nat.le_of_dvd (by norm_num : 0 < 2) hp2
          omega
        rw [hpEq]
        exact even_iff_two_dvd.mp hn
      simp [loss, tailLoss, hp2, hpn]
    · by_cases hpn : (p : ℕ) ∣ n
      · simp only [loss, tailLoss, hp2, hpn, ite_true, ite_false]
        positivity
      · simp [loss, tailLoss, hp2, hpn]
  have hgsum : Summable loss := by
    simpa only [loss] using summable_sift_factor n
  have htsum : Summable tailLoss := by
    simpa only [tailLoss] using summable_sift_factor 2
  have htfac : ∀ p, 0 < 1 - tailLoss p := by
    intro p
    simpa only [tailLoss] using bridge_tail_factor_pos p
  have hm : Multipliable (fun p => 1 - loss p) := by
    simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hgsum.neg
  have htm : Multipliable (fun p => 1 - tailLoss p) := by
    simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable htsum.neg
  have hc : (∏' p : Nat.Primes, (1 - tailLoss p)) ≤ ∏' p : Nat.Primes, (1 - loss p) :=
    le_of_tendsto_of_tendsto' htm.hasProd hm.hasProd (fun s : Finset Nat.Primes =>
      Finset.prod_le_prod₀ (fun p _ => (htfac p).le) (fun p _ => by linarith [hle p]))
  have heq : (∏' p : Nat.Primes, if (p : ℕ) ∣ n then 1 else
      1 - 1 / ((p : ℝ) - 1) ^ 2) = ∏' p : Nat.Primes, (1 - loss p) := by
    apply tprod_congr
    intro p
    by_cases hp : (p : ℕ) ∣ n <;> simp [loss, hp]
  have hf : 1 ≤ ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
    apply Finset.one_le_prod₀
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by positivity
    linarith
  unfold singular
  rw [heq]
  exact hc.trans (le_mul_of_one_le_right (tprod_nonneg (fun p =>
    le_trans (htfac p).le (by linarith [hle p]))) hf)

/-- The cutoff and unit error is bounded by the main power with exponent slack. -/
private lemma bridge_error_le {Y : ℝ} (hY : 1 ≤ Y) :
    2 * Y / Y ^ (16 / 135 : ℝ) + 1 ≤ 5 * Y ^ (1 - 16 / 135 : ℝ) := by
  have hY0 : 0 < Y := by linarith
  have hd : 2 * Y / Y ^ (16 / 135 : ℝ) = 2 * Y ^ (1 - 16 / 135 : ℝ) := by
    rw [Real.rpow_sub hY0, Real.rpow_one]
    ring
  have h1 : 1 ≤ Y ^ (1 - 16 / 135 : ℝ) := Real.one_le_rpow hY (by norm_num)
  rw [hd]
  linarith

/-- The cutoff and unit error is eventually absorbed by `0.005` of the scale,
uniformly for even `n` and small positive `ε`. -/
private lemma bridge_error_absorption :
    ∃ N₀ : ℝ, ∀ ε N : ℝ, 0 < ε → ε < 1 / 12 → N₀ ≤ N → ∀ n : ℕ, Even n →
      0 < scale N (localization N ε) n ∧
      2 * localization N ε / (localization N ε) ^ (16 / 135 : ℝ) + 1 ≤
        0.005 * scale N (localization N ε) n := by
  let c : ℝ := ∏' p : Nat.Primes,
    (1 - if (p : ℕ) ∣ 2 then 0 else 1 / ((p : ℝ) - 1) ^ 2)
  let d : ℝ := 0.001 * c
  have hc : 0 < c := by simpa only [c] using bridge_tail_product_pos
  have hd : 0 < d := mul_pos (by norm_num) hc
  have hlittle := isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 28 / 405)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hlittle.bound hd)
  refine ⟨max N₁ 2, ?_⟩
  intro ε N hε he hN n hn
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNp : 0 < N := by linarith
  have hYp : 1 < localization N ε :=
    Real.one_lt_rpow (by linarith) (by positivity : (0 : ℝ) < 7 / 12 + ε)
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hLY : 0 < Real.log (localization N ε) := Real.log_pos hYp
  have hscale := scale_pos (N := N) (Y := localization N ε) hn (by linarith) hYp
  refine ⟨hscale, ?_⟩
  have hpow : N ^ (28 / 405 : ℝ) ≤ (localization N ε) ^ (16 / 135 : ℝ) := by
    unfold localization
    rw [← Real.rpow_mul hNp.le]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    nlinarith
  have hb := hN₁ N hN1
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL.le (2 : ℝ)),
    abs_of_nonneg (Real.rpow_nonneg hNp.le (28 / 405 : ℝ)), Real.rpow_two] at hb
  have hlog : Real.log N ^ (2 : ℕ) ≤ d * (localization N ε) ^ (16 / 135 : ℝ) :=
    hb.trans (mul_le_mul_of_nonneg_left hpow hd.le)
  have hlogY : Real.log (localization N ε) ≤ Real.log N := by
    rw [localization, Real.log_rpow hNp]
    nlinarith
  have hden : Real.log (localization N ε) * Real.log N ≤ Real.log N ^ (2 : ℕ) := by
    nlinarith
  have hmain : c * localization N ε ≤
      scale N (localization N ε) n * Real.log N ^ (2 : ℕ) := by
    calc c * localization N ε ≤ singular n * localization N ε :=
          mul_le_mul_of_nonneg_right
            (by simpa only [c] using bridge_tail_le_singular n hn) (by linarith)
        _ = scale N (localization N ε) n *
            (Real.log (localization N ε) * Real.log N) := by
          unfold scale
          rw [div_mul_cancel₀ _ (mul_ne_zero hLY.ne' hL.ne')]
        _ ≤ _ := mul_le_mul_of_nonneg_left hden hscale.le
  have hYid : (localization N ε) ^ (1 - 16 / 135 : ℝ) *
      (localization N ε) ^ (16 / 135 : ℝ) = localization N ε := by
    rw [← Real.rpow_add (by linarith : 0 < localization N ε)]
    norm_num
  have hbudget :
      (2 * localization N ε / (localization N ε) ^ (16 / 135 : ℝ) + 1) *
          Real.log N ^ (2 : ℕ) ≤ 0.005 * c * localization N ε := by
    calc
      (2 * localization N ε / (localization N ε) ^ (16 / 135 : ℝ) + 1) *
          Real.log N ^ (2 : ℕ) ≤
        (5 * (localization N ε) ^ (1 - 16 / 135 : ℝ)) *
          (d * (localization N ε) ^ (16 / 135 : ℝ)) :=
        mul_le_mul (bridge_error_le hYp.le) hlog (sq_nonneg _) (by positivity)
      _ = 0.005 * c * localization N ε := by
        calc _ = (5 * d) * ((localization N ε) ^ (1 - 16 / 135 : ℝ) *
              (localization N ε) ^ (16 / 135 : ℝ)) := by ring
          _ = _ := by rw [hYid]; dsimp [d]; ring
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hL)).mp
  calc
    (2 * localization N ε / (localization N ε) ^ (16 / 135 : ℝ) + 1) *
        Real.log N ^ (2 : ℕ) ≤ 0.005 * c * localization N ε := hbudget
    _ ≤ 0.005 * (scale N (localization N ε) n * Real.log N ^ (2 : ℕ)) := by
      nlinarith [hmain]
    _ = _ := by ring

/-- In the valid cutoff regime, every sieve count ranges over the same underlying set. -/
private lemma bridge_sifted_reduce (N Y : ℝ) (n d : ℕ) (w : ℝ) (hw : w ≤ N - Y) :
    sifted N Y n d w =
      (((Icc 1 n).filter (fun a => (n - a).Prime ∧ N - Y < ((n - a : ℕ) : ℝ) ∧
        ((n - a : ℕ) : ℝ) ≤ N)).filter (fun a =>
          (∀ p : ℕ, p.Prime → (p : ℝ) < w → ¬ p ∣ a) ∧ d ∣ a)).card := by
  unfold sifted
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨haI, hd, hprime, hlo, hhi, hs⟩
    obtain ⟨ha1, han⟩ := haI
    refine ⟨⟨⟨ha1, han⟩, hprime, hlo, hhi⟩, ?_, hd⟩
    intro p hp hpw hpa
    by_cases hpn : p ∣ n
    · have hdvd : p ∣ n - a := Nat.dvd_sub hpn hpa
      have heq : n - a = p := (hprime.dvd_iff_eq hp.ne_one).mp hdvd
      have heqR : ((n - a : ℕ) : ℝ) = (p : ℝ) := by exact_mod_cast heq
      linarith
    · exact hs p hp hpw hpn hpa
  · rintro ⟨⟨haI, hprime, hlo, hhi⟩, hrough, hd⟩
    exact ⟨haI, hd, hprime, hlo, hhi,
      fun p hp hpw _ hpa => hrough p hp hpw hpa⟩

/-- The three sieve terms interpolate to one finite weighted sum. -/
private lemma bridge_weight_sum
    (F P : Finset ℕ) (Q : ℕ → Finset ℕ) (N Y z : ℝ) (n : ℕ)
    (hF : F = (Icc 1 n).filter (fun a => (n - a).Prime ∧ N - Y < ((n - a : ℕ) : ℝ) ∧
      ((n - a : ℕ) : ℝ) ≤ N))
    (hP : P = (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
      z < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)))
    (hQ : ∀ p, Q p = (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
      z < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))))
    (hzdef : z = Y ^ (16 / 135 : ℝ)) (hz : z ≤ N - Y)
    (hQcut : ∀ p ∈ P, ∀ q ∈ Q p, (q : ℝ) ≤ N - Y) :
    initial N Y n - subtraction N Y n + recovery N Y n =
      ∑ a ∈ F, ((if (∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ a) then (1 : ℝ) else 0) -
        (∑ p ∈ P, if (∀ r : ℕ, r.Prime → (r : ℝ) < z → ¬ r ∣ a) ∧ p ∣ a
          then (1 : ℝ) else 0) +
        (∑ p ∈ P, ∑ q ∈ Q p, if
          (∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ a) ∧ p * q ∣ a
          then (1 : ℝ) else 0)) := by
  subst z
  have hinit : initial N Y n =
      ∑ a ∈ F, if (∀ p : ℕ, p.Prime → (p : ℝ) < Y ^ (16 / 135 : ℝ) → ¬ p ∣ a)
        then (1 : ℝ) else 0 := by
    unfold initial
    rw [bridge_sifted_reduce N Y n 1 _ hz]
    rw [← hF]
    simp only [one_dvd, and_true]
    exact (Finset.sum_boole (fun a : ℕ =>
      ∀ p : ℕ, p.Prime → (p : ℝ) < Y ^ (16 / 135 : ℝ) → ¬ p ∣ a) _).symm
  have hsub : subtraction N Y n =
      ∑ a ∈ F, ∑ p ∈ P, if
        (∀ r : ℕ, r.Prime → (r : ℝ) < Y ^ (16 / 135 : ℝ) → ¬ r ∣ a) ∧ p ∣ a
        then (1 : ℝ) else 0 := by
    unfold subtraction
    rw [← hP]
    calc
      _ = ∑ p ∈ P, ∑ a ∈ F, if
          (∀ r : ℕ, r.Prime → (r : ℝ) < Y ^ (16 / 135 : ℝ) → ¬ r ∣ a) ∧ p ∣ a
          then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [bridge_sifted_reduce N Y n p _ hz]
        rw [← hF]
        exact (Finset.sum_boole (fun a : ℕ =>
          (∀ r : ℕ, r.Prime → (r : ℝ) < Y ^ (16 / 135 : ℝ) → ¬ r ∣ a) ∧ p ∣ a) _).symm
      _ = _ := Finset.sum_comm
  have hrec : recovery N Y n =
      ∑ a ∈ F, ∑ p ∈ P, ∑ q ∈ Q p, if
        (∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ a) ∧ p * q ∣ a
        then (1 : ℝ) else 0 := by
    unfold recovery
    simp only [← hP, ← hQ]
    calc
      _ = ∑ p ∈ P, ∑ q ∈ Q p, ∑ a ∈ F, if
          (∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ a) ∧ p * q ∣ a
          then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [bridge_sifted_reduce N Y n (p * q) q (hQcut p hp q hq)]
        rw [← hF]
        exact (Finset.sum_boole (fun a : ℕ =>
          (∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ a) ∧ p * q ∣ a) _).symm
      _ = ∑ p ∈ P, ∑ a ∈ F, ∑ q ∈ Q p, if
          (∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ a) ∧ p * q ∣ a
          then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  calc
    _ = (∑ a ∈ F, if (∀ p : ℕ, p.Prime → (p : ℝ) < Y ^ (16 / 135 : ℝ) → ¬ p ∣ a)
          then (1 : ℝ) else 0) -
        (∑ a ∈ F, ∑ p ∈ P, if
          (∀ r : ℕ, r.Prime → (r : ℝ) < Y ^ (16 / 135 : ℝ) → ¬ r ∣ a) ∧ p ∣ a
          then (1 : ℝ) else 0) +
        (∑ a ∈ F, ∑ p ∈ P, ∑ q ∈ Q p, if
          (∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ a) ∧ p * q ∣ a
          then (1 : ℝ) else 0) := by rw [hinit, hsub, hrec]
    _ = _ := by
      conv_rhs => rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The sieve weight of an integer at least two is at most one. -/
private lemma bridge_weight_le_one
    {P : Finset ℕ} {R : Finset (ℕ × ℕ)} {a : ℕ} {z Y : ℝ}
    (ha2 : 2 ≤ a)
    (hrough : ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ a)
    (hR : ∀ x ∈ R, x.1 ∈ P ∧ (x.1).Prime ∧ (x.2).Prime ∧ z < (x.2 : ℝ) ∧
      (x.2 : ℝ) < (x.1 : ℝ) ∧ x.1 * x.2 ∣ a ∧
      (∀ r : ℕ, r.Prime → (r : ℝ) < (x.2 : ℝ) → ¬ r ∣ a)) :
    1 - ((P.filter (fun p => p ∣ a)).card : ℤ) + (R.card : ℤ) ≤ 1 := by
  classical
  have ha1 : a ≠ 1 := by omega
  set m : ℕ := a.minFac with hmdef
  have hmprime : m.Prime := Nat.minFac_prime ha1
  have hmdvd : m ∣ a := Nat.minFac_dvd a
  have hsecond : ∀ x ∈ R, x.2 = m := by
    intro x hx
    obtain ⟨-, -, hx2p, -, hlt, hdvd, hrough'⟩ := hR x hx
    have hqdvd : x.2 ∣ a := (dvd_mul_left x.2 x.1).trans hdvd
    have hle : m ≤ x.2 := Nat.minFac_le_of_dvd hx2p.two_le hqdvd
    have hnot : ¬ m < x.2 := by
      intro hcon
      exact (hrough' m hmprime (by exact_mod_cast hcon)) hmdvd
    omega
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1) (↑R : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hx' : x ∈ R := hx
    have hy' : y ∈ R := hy
    exact Prod.ext hxy (by rw [hsecond x hx', hsecond y hy'])
  have hcard : (R.image (fun x : ℕ × ℕ => x.1)).card = R.card :=
    Finset.card_image_of_injOn hinj
  have hsub : R.image (fun x : ℕ × ℕ => x.1) ⊆ P.filter (fun p => p ∣ a) := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hxP, -, -, -, -, hdvd, -⟩ := hR x hx
    exact Finset.mem_filter.mpr ⟨hxP, (dvd_mul_right x.1 x.2).trans hdvd⟩
  have hle : R.card ≤ (P.filter (fun p => p ∣ a)).card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hleZ : (R.card : ℤ) ≤ ((P.filter (fun p => p ∣ a)).card : ℤ) := by exact_mod_cast hle
  linarith

/-- If the least prime factor exceeds the cutoff, a composite integer has nonpositive weight. -/
private lemma bridge_composite_weight_le_zero
    {P : Finset ℕ} {R : Finset (ℕ × ℕ)} {a : ℕ} {z Y : ℝ}
    (ha2 : 2 ≤ a) (hac : ¬ a.Prime) (hY : 0 < Y)
    (ha2Y : (a : ℝ) < 2 * Y)
    (hmz : z < (a.minFac : ℝ))
    (hrough : ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ a)
    (hPmem : ∀ p : ℕ, p.Prime → z < (p : ℝ) → (p : ℝ) ≤ Real.sqrt (2 * Y) → p ∣ a → p ∈ P)
    (hR : ∀ x ∈ R, x.1 ∈ P ∧ (x.1).Prime ∧ (x.2).Prime ∧ z < (x.2 : ℝ) ∧
      (x.2 : ℝ) < (x.1 : ℝ) ∧ x.1 * x.2 ∣ a ∧
      (∀ r : ℕ, r.Prime → (r : ℝ) < (x.2 : ℝ) → ¬ r ∣ a)) :
    1 - ((P.filter (fun p => p ∣ a)).card : ℤ) + (R.card : ℤ) ≤ 0 := by
  classical
  have ha1 : a ≠ 1 := by omega
  have ha0 : a ≠ 0 := by omega
  set m : ℕ := a.minFac with hmdef
  have hmprime : m.Prime := Nat.minFac_prime ha1
  have hmdvd : m ∣ a := Nat.minFac_dvd a
  have hm2 : 2 ≤ m := hmprime.two_le
  have hmgt : z < (m : ℝ) := by simpa [hmdef] using hmz
  have hmsq : m * m ≤ a := by
    obtain ⟨b, hb⟩ : ∃ b : ℕ, a = m * b := ⟨a / m, (Nat.mul_div_cancel' hmdvd).symm⟩
    have hb1 : b ≠ 1 := by
      rintro rfl
      rw [mul_one] at hb
      exact hac (hb ▸ hmprime)
    have hb2 : 2 ≤ b := by
      rcases Nat.eq_zero_or_pos b with h0 | hpos
      · subst h0; rw [mul_zero] at hb; omega
      · omega
    have hbm : m ≤ b := by
      by_contra hcon
      push_neg at hcon
      have hbm' : (b.minFac).Prime := Nat.minFac_prime hb1
      have hbdvd : b.minFac ∣ b := Nat.minFac_dvd b
      have hble : b.minFac ≤ b := Nat.le_of_dvd (by omega) hbdvd
      have hlt : b.minFac < m := lt_of_le_of_lt hble hcon
      have hdiva : b.minFac ∣ a := by
        rw [hb]
        exact Dvd.dvd.mul_left hbdvd m
      have := Nat.minFac_le_of_dvd hbm'.two_le hdiva
      omega
    calc m * m ≤ m * b := Nat.mul_le_mul_left m hbm
      _ = a := hb.symm
  have hmsqrt : (m : ℝ) ≤ Real.sqrt (2 * Y) := by
    have hsq : ((m : ℝ)) ^ 2 ≤ 2 * Y := by
      have h1 : ((m * m : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hmsq
      push_cast at h1
      linarith
    exact (Real.le_sqrt (by positivity) (by linarith)).mpr hsq
  have hmP : m ∈ P := hPmem m hmprime hmgt hmsqrt hmdvd
  have hsecond : ∀ x ∈ R, x.2 = m := by
    intro x hx
    obtain ⟨-, -, hx2p, -, hlt, hdvd, hrough'⟩ := hR x hx
    have hqdvd : x.2 ∣ a := (dvd_mul_left x.2 x.1).trans hdvd
    have hle : m ≤ x.2 := Nat.minFac_le_of_dvd hx2p.two_le hqdvd
    have hnot : ¬ m < x.2 := by
      intro hcon
      exact (hrough' m hmprime (by exact_mod_cast hcon)) hmdvd
    omega
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1) (↑R : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    exact Prod.ext hxy (by rw [hsecond x hx, hsecond y hy])
  have hcard : (R.image (fun x : ℕ × ℕ => x.1)).card = R.card :=
    Finset.card_image_of_injOn hinj
  have hsub : R.image (fun x : ℕ × ℕ => x.1) ⊆ P.filter (fun p => p ∣ a) := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hxP, -, -, -, -, hdvd, -⟩ := hR x hx
    exact Finset.mem_filter.mpr ⟨hxP, (dvd_mul_right x.1 x.2).trans hdvd⟩
  have hnotmem : m ∉ R.image (fun x : ℕ × ℕ => x.1) := by
    intro hcon
    obtain ⟨x, hx, hx1⟩ := Finset.mem_image.mp hcon
    obtain ⟨-, -, -, -, hlt, -⟩ := hR x hx
    have h2 : x.2 = m := hsecond x hx
    rw [h2] at hlt
    rw [hx1] at hlt
    exact lt_irrefl _ hlt
  have hsub2 : R.image (fun x : ℕ × ℕ => x.1) ⊆ (P.filter (fun p => p ∣ a)).erase m := by
    intro p hp
    refine Finset.mem_erase.mpr ⟨?_, hsub hp⟩
    rintro rfl
    exact hnotmem hp
  have hmem : m ∈ P.filter (fun p => p ∣ a) := Finset.mem_filter.mpr ⟨hmP, hmdvd⟩
  have hcard2 : R.card ≤ (P.filter (fun p => p ∣ a)).card - 1 := by
    have h1 : (R.image (fun x : ℕ × ℕ => x.1)).card ≤ ((P.filter (fun p => p ∣ a)).erase m).card :=
      Finset.card_le_card hsub2
    rw [hcard, Finset.card_erase_of_mem hmem] at h1
    exact h1
  have hpos : 1 ≤ (P.filter (fun p => p ∣ a)).card := Finset.card_pos.mpr ⟨m, hmem⟩
  have hZ : (R.card : ℤ) ≤ ((P.filter (fun p => p ∣ a)).card : ℤ) - 1 := by
    have h1 : (R.card : ℤ) ≤ (((P.filter (fun p => p ∣ a)).card - 1 : ℕ) : ℤ) := by
      exact_mod_cast hcard2
    have h2 : (((P.filter (fun p => p ∣ a)).card - 1 : ℕ) : ℤ)
        = ((P.filter (fun p => p ∣ a)).card : ℤ) - 1 := by
      rw [Nat.cast_sub hpos]
      push_cast
      ring
    linarith
  linarith

/-- Positive multiples below a real bound have the usual real cardinality estimate. -/
private lemma bridge_multiples_count_le (s : Finset ℕ) (d : ℕ) (M : ℝ)
    (hd : 0 < d) (hM : 0 ≤ M)
    (hs : ∀ a ∈ s, 0 < a ∧ (a : ℝ) ≤ M ∧ d ∣ a) : (s.card : ℝ) ≤ M / d := by
  have hsub : s ⊆ (Ioc 0 ⌊M⌋₊).filter (fun a => d ∣ a) := by
    intro a ha
    obtain ⟨ha0, haM, hda⟩ := hs a ha
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨ha0, Nat.le_floor haM⟩, hda⟩
  have hc : s.card ≤ ⌊M⌋₊ / d := by
    simpa only [Nat.Ioc_filter_dvd_card_eq_div] using card_le_card hsub
  calc (s.card : ℝ) ≤ ((⌊M⌋₊ / d : ℕ) : ℝ) := by exact_mod_cast hc
       _ ≤ (⌊M⌋₊ : ℝ) / d := Nat.cast_div_le
       _ ≤ M / d := div_le_div_of_nonneg_right (Nat.floor_le hM) (by positivity)

/-- Pointwise sieve weight, bounded by the one/prime/strict-cutoff exceptional class. -/
private lemma bridge_point_weight_le
    (P : Finset ℕ) (Q : ℕ → Finset ℕ) (a : ℕ) (N Y z : ℝ) (n : ℕ)
    (ha1 : 1 ≤ a) (han : a ≤ n) (ha2Y : (a : ℝ) < 2 * Y) (hY : 0 < Y)
    (hP : P = (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
      z < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)))
    (hQ : ∀ p, Q p = (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
      z < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))))) :
    ((if (∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ a) then (1 : ℝ) else 0) -
      (∑ p ∈ P, if (∀ r : ℕ, r.Prime → (r : ℝ) < z → ¬ r ∣ a) ∧ p ∣ a
        then (1 : ℝ) else 0) +
      (∑ p ∈ P, ∑ q ∈ Q p, if
        (∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ a) ∧ p * q ∣ a
        then (1 : ℝ) else 0)) ≤
      if a = 1 ∨ a.Prime ∨ (a.minFac : ℝ) = z then (1 : ℝ) else 0 := by
  let R : Finset (ℕ × ℕ) := (P ×ˢ range (n + 1)).filter (fun x => x.2 ∈ Q x.1 ∧
    (∀ r : ℕ, r.Prime → (r : ℝ) < (x.2 : ℝ) → ¬ r ∣ a) ∧ x.1 * x.2 ∣ a)
  have hRsum : (∑ p ∈ P, ∑ q ∈ Q p, if
      (∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ a) ∧ p * q ∣ a
      then (1 : ℝ) else 0) = (R.card : ℝ) := by
    calc
      _ = ∑ x ∈ P ×ˢ range (n + 1), if x.2 ∈ Q x.1 ∧
          (∀ r : ℕ, r.Prime → (r : ℝ) < (x.2 : ℝ) → ¬ r ∣ a) ∧ x.1 * x.2 ∣ a
          then (1 : ℝ) else 0 := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro p hp
        have hsubq : Q p ⊆ range (n + 1) := by
          intro q hq
          have hq' : q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
              z < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))) := by
            rwa [← hQ p]
          exact (Finset.mem_filter.mp hq').1
        calc
          _ = ∑ q ∈ Q p, if q ∈ Q p ∧
              (∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ a) ∧ p * q ∣ a
              then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            simp only [hq, true_and]
          _ = _ := by
            apply Finset.sum_subset hsubq
            intro q hr hqnot
            simp only [hqnot, false_and, ↓reduceIte]
      _ = (R.card : ℝ) := by
        unfold R
        exact Finset.sum_boole (fun x : ℕ × ℕ => x.2 ∈ Q x.1 ∧
          (∀ r : ℕ, r.Prime → (r : ℝ) < (x.2 : ℝ) → ¬ r ∣ a) ∧ x.1 * x.2 ∣ a)
          (P ×ˢ range (n + 1))
  have hRdata : ∀ x ∈ R, x.1 ∈ P ∧ (x.1).Prime ∧ (x.2).Prime ∧ z < (x.2 : ℝ) ∧
      (x.2 : ℝ) < (x.1 : ℝ) ∧ x.1 * x.2 ∣ a ∧
      (∀ r : ℕ, r.Prime → (r : ℝ) < (x.2 : ℝ) → ¬ r ∣ a) := by
    intro x hx
    obtain ⟨hxE, hqQ, hxrough, hxdvd⟩ := Finset.mem_filter.mp hx
    obtain ⟨hpP, -⟩ := Finset.mem_product.mp hxE
    have hpP' : x.1 ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
        z < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)) := by rwa [← hP]
    have hqQ' : x.2 ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        z < (q : ℝ) ∧ (q : ℝ) < min (x.1 : ℝ) (Real.sqrt (2 * Y / (x.1 : ℝ)))) := by
      rwa [← hQ x.1]
    obtain ⟨-, hpPrime, -, -⟩ := Finset.mem_filter.mp hpP'
    obtain ⟨-, hqPrime, hqz, hqmin⟩ := Finset.mem_filter.mp hqQ'
    exact ⟨hpP, hpPrime, hqPrime, hqz, hqmin.trans_le (min_le_left _ _), hxdvd, hxrough⟩
  by_cases hrough : ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ a
  · have hPsum : (∑ p ∈ P, if
        (∀ r : ℕ, r.Prime → (r : ℝ) < z → ¬ r ∣ a) ∧ p ∣ a then (1 : ℝ) else 0) =
        (((P.filter (fun p => p ∣ a)).card : ℕ) : ℝ) := by
      calc
        _ = ∑ p ∈ P, if p ∣ a then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [and_iff_right hrough]
        _ = _ := Finset.sum_boole (fun p : ℕ => p ∣ a) P
    by_cases hclass : a = 1 ∨ a.Prime ∨ (a.minFac : ℝ) = z
    · by_cases ha1eq : a = 1
      · have hPe : P.filter (fun p => p ∣ a) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro p hp hpa
          have hpP : p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
              z < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)) := by rwa [← hP]
          have hpprime := (Finset.mem_filter.mp hpP).2.1
          subst a
          exact hpprime.ne_one (Nat.dvd_one.mp hpa)
        have hRe : R = ∅ := by
          unfold R
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx hcond
          have hxdata := hRdata x (Finset.mem_filter.mpr ⟨hx, hcond⟩)
          subst a
          have hx1a : x.1 ∣ 1 := (dvd_mul_right x.1 x.2).trans hcond.2.2
          exact hxdata.2.1.ne_one (Nat.dvd_one.mp hx1a)
        rw [hPsum, hRsum, hPe, hRe, if_pos hrough]
        norm_num [hclass]
      · have ha2 : 2 ≤ a := by omega
        have hc := bridge_weight_le_one (P := P) (R := R) (a := a) (z := z) (Y := Y)
          ha2 hrough hRdata
        have hcR : (1 : ℝ) - ((P.filter (fun p => p ∣ a)).card : ℝ) + (R.card : ℝ) ≤ 1 := by
          exact_mod_cast hc
        rw [hPsum, hRsum, if_pos hrough]
        simpa only [hclass, ite_true] using hcR
    · have ha2 : 2 ≤ a := by omega
      have hac : ¬ a.Prime := by push_neg at hclass; exact hclass.2.1
      have hm1 : (a.minFac : ℝ) ≠ z := by push_neg at hclass; exact hclass.2.2
      have hmprime : a.minFac.Prime := Nat.minFac_prime (by omega)
      have hmdvd : a.minFac ∣ a := Nat.minFac_dvd a
      have hzle : z ≤ (a.minFac : ℝ) := by
        apply le_of_not_gt
        intro hlt
        exact hrough a.minFac hmprime hlt hmdvd
      have hgt : z < (a.minFac : ℝ) := lt_of_le_of_ne hzle (Ne.symm hm1)
      have hPmem : ∀ p : ℕ, p.Prime → z < (p : ℝ) → (p : ℝ) ≤ Real.sqrt (2 * Y) →
          p ∣ a → p ∈ P := by
        intro p hp hzp hpsqrt hpa
        have hpa_le : p ≤ a := Nat.le_of_dvd (by omega) hpa
        rw [hP]
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, hzp, hpsqrt⟩
      have hc := bridge_composite_weight_le_zero (P := P) (R := R) (a := a) (z := z) (Y := Y)
        ha2 hac hY ha2Y hgt hrough hPmem hRdata
      have hcR : (1 : ℝ) - ((P.filter (fun p => p ∣ a)).card : ℝ) + (R.card : ℝ) ≤ 0 := by
        exact_mod_cast hc
      rw [hPsum, hRsum, if_pos hrough]
      simpa only [hclass, ite_true, ite_false] using hcR
  · have hsub0 : (∑ p ∈ P, if
        (∀ r : ℕ, r.Prime → (r : ℝ) < z → ¬ r ∣ a) ∧ p ∣ a then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exact if_neg (fun hc => hrough hc.1)
    have hrec0 : (∑ p ∈ P, ∑ q ∈ Q p, if
        (∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ a) ∧ p * q ∣ a
        then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      apply Finset.sum_eq_zero
      intro q hq
      have hq' : q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
          z < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))) := by
        rwa [← hQ p]
      have hqz := (Finset.mem_filter.mp hq').2.2.1
      exact if_neg (fun hc => hrough (fun r hr hrz => hc.1 r hr (hrz.trans hqz)))
    rw [hsub0, hrec0, if_neg hrough]
    split_ifs <;> norm_num

/-- The finite sieve inclusion-exclusion, with a prime count and its strict-cutoff error. -/
private lemma bridge_finite_bound (N Y z : ℝ) (n : ℕ)
    (hzdef : z = Y ^ (16 / 135 : ℝ)) (hz : z ≤ N - Y)
    (hsqrt : Real.sqrt (2 * Y) ≤ N - Y) (hnupper : (n : ℝ) ≤ N + Y) (hY : 0 < Y) :
    initial N Y n - subtraction N Y n + recovery N Y n ≤
      (representations N Y n : ℝ) + 2 * Y / z + 1 := by
  let F : Finset ℕ := (Icc 1 n).filter (fun a => (n - a).Prime ∧
    N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N)
  let P : Finset ℕ := (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    z < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y))
  let Q : ℕ → Finset ℕ := fun p => (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
    z < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))))
  have h2Yall : ∀ a ∈ F, (a : ℝ) < 2 * Y := by
    intro a ha
    have ha' : a ∈ (Icc 1 n).filter (fun a => (n - a).Prime ∧
        N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N) := by simpa only [F] using ha
    obtain ⟨haI, -, hlo, -⟩ := Finset.mem_filter.mp ha'
    have hcast : ((n - a : ℕ) : ℝ) = (n : ℝ) - a :=
      Nat.cast_sub (Finset.mem_Icc.mp haI).2
    linarith
  have hQcut : ∀ p ∈ P, ∀ q ∈ Q p, (q : ℝ) ≤ N - Y := by
    intro p hp q hq
    have hp' : p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
        z < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)) := by simpa only [P] using hp
    have hq' : q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        z < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))) := by
      simpa only [Q] using hq
    have hpSqrt := (Finset.mem_filter.mp hp').2.2.2
    have hqmin := (Finset.mem_filter.mp hq').2.2.2
    have hqp : (q : ℝ) < (p : ℝ) := hqmin.trans_le (min_le_left _ _)
    exact ((hqp.trans_le hpSqrt).trans_le hsqrt).le
  have hws := bridge_weight_sum F P Q N Y z n (by rfl) (by rfl) (fun p => by rfl)
    hzdef hz hQcut
  have hpoint : ∀ a ∈ F,
      ((if (∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ a) then (1 : ℝ) else 0) -
        (∑ p ∈ P, if (∀ r : ℕ, r.Prime → (r : ℝ) < z → ¬ r ∣ a) ∧ p ∣ a
          then (1 : ℝ) else 0) +
        (∑ p ∈ P, ∑ q ∈ Q p, if
          (∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ a) ∧ p * q ∣ a
          then (1 : ℝ) else 0)) ≤
      if a = 1 ∨ a.Prime ∨ (a.minFac : ℝ) = z then (1 : ℝ) else 0 := by
    intro a ha
    have ha' : a ∈ (Icc 1 n).filter (fun a => (n - a).Prime ∧
        N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N) := by simpa only [F] using ha
    have haI := Finset.mem_Icc.mp (Finset.mem_filter.mp ha').1
    exact bridge_point_weight_le P Q a N Y z n haI.1 haI.2 (h2Yall a ha) hY (by rfl) (fun p => by rfl)
  have hsum : initial N Y n - subtraction N Y n + recovery N Y n ≤
      ∑ a ∈ F, if a = 1 ∨ a.Prime ∨ (a.minFac : ℝ) = z then (1 : ℝ) else 0 := by
    rw [hws]
    exact Finset.sum_le_sum hpoint
  let G : Finset ℕ := F.filter (fun a => a = 1 ∨ a.Prime ∨ (a.minFac : ℝ) = z)
  let A : Finset ℕ := F.filter (fun a => a.Prime)
  let B : Finset ℕ := F.filter (fun a => ¬ a.Prime ∧ a ≠ 1 ∧ (a.minFac : ℝ) = z)
  have hGsum : (∑ a ∈ F, if a = 1 ∨ a.Prime ∨ (a.minFac : ℝ) = z then (1 : ℝ) else 0) =
      (G.card : ℝ) := Finset.sum_boole _ _
  rw [hGsum] at hsum
  have hAcard : A.card = representations N Y n := by
    rw [representations_eq_count]
    congr 1
    ext a
    constructor
    · intro ha
      have ha' : a ∈ F.filter (fun a => a.Prime) := by simpa only [A] using ha
      obtain ⟨haF, hap⟩ := Finset.mem_filter.mp ha'
      have haF' : a ∈ (Icc 1 n).filter (fun a => (n - a).Prime ∧
          N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N) := by
        simpa only [F] using haF
      obtain ⟨haI, hprime, hlo, hhi⟩ := Finset.mem_filter.mp haF'
      exact Finset.mem_filter.mpr ⟨haI, hap, hprime, hlo, hhi, (h2Yall a haF).le⟩
    · intro ha
      obtain ⟨haI, hap, hprime, hlo, hhi, haY⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      refine ⟨?_, hap⟩
      exact Finset.mem_filter.mpr ⟨haI, hprime, hlo, hhi⟩
  have hGsub : G ⊆ insert 1 (A ∪ B) := by
    intro a ha
    have haG : a ∈ F.filter (fun a => a = 1 ∨ a.Prime ∨ (a.minFac : ℝ) = z) := by
      simpa only [G] using ha
    obtain ⟨haF, hclass⟩ := Finset.mem_filter.mp haG
    rcases hclass with ha1 | hap | hm
    · exact Finset.mem_insert.mpr (Or.inl ha1)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨haF, hap⟩)))
    · by_cases ha1 : a = 1
      · exact Finset.mem_insert.mpr (Or.inl ha1)
      · by_cases hap : a.Prime
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨haF, hap⟩)))
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨haF, hap, ha1, hm⟩)))
  have hcardNat : G.card ≤ 1 + A.card + B.card := by
    have hc := (Finset.card_le_card hGsub).trans (Finset.card_insert_le _ _)
    have hu := Finset.card_union_le A B
    omega
  have hcardR : (G.card : ℝ) ≤ 1 + (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcardNat
  have hzpos : 0 < z := by
    rw [hzdef]
    exact Real.rpow_pos_of_pos hY _
  have hBreal : (B.card : ℝ) ≤ 2 * Y / z := by
    by_cases hB : B.Nonempty
    · obtain ⟨a₀, ha₀⟩ := hB
      have ha₀' : a₀ ∈ F.filter (fun a => ¬ a.Prime ∧ a ≠ 1 ∧ (a.minFac : ℝ) = z) := by
        simpa only [B] using ha₀
      obtain ⟨ha₀F, ha₀p, ha₀1, ha₀m⟩ := Finset.mem_filter.mp ha₀'
      have hmprime : a₀.minFac.Prime := Nat.minFac_prime ha₀1
      have hmpos : 0 < a₀.minFac := hmprime.pos
      have hdvd : ∀ a ∈ B, a₀.minFac ∣ a := by
        intro a ha
        have ha' : a ∈ F.filter (fun a => ¬ a.Prime ∧ a ≠ 1 ∧ (a.minFac : ℝ) = z) := by
          simpa only [B] using ha
        obtain ⟨haF, hap, ha1, ham⟩ := Finset.mem_filter.mp ha'
        have heq : a.minFac = a₀.minFac := by
          have hr : (a.minFac : ℝ) = (a₀.minFac : ℝ) := ham.trans ha₀m.symm
          exact_mod_cast hr
        rw [← heq]
        exact Nat.minFac_dvd a
      have hprops : ∀ a ∈ B, 0 < a ∧ (a : ℝ) ≤ 2 * Y ∧ a₀.minFac ∣ a := by
        intro a ha
        have haF := (Finset.mem_filter.mp ha).1
        have haF' : a ∈ F := haF
        have ha'' : a ∈ (Icc 1 n).filter (fun a => (n - a).Prime ∧
            N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N) := by
          simpa only [F] using haF'
        have ha1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha'').1).1
        exact ⟨ha1, (h2Yall a haF').le, hdvd a ha⟩
      have hc := bridge_multiples_count_le B a₀.minFac (2 * Y) hmpos (by linarith) hprops
      rw [ha₀m] at hc
      exact hc
    · have hB0 : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
      simp only [hB0, Finset.card_empty, Nat.cast_zero]
      exact div_nonneg (by linarith) hzpos.le
  rw [hAcard] at hcardR
  linarith

/-- A concrete localization regime supporting the finite sieve comparison. -/
private lemma bridge_localization_domain {ε N : ℝ} (hε : 0 < ε) (he : ε < 1 / 100)
    (hN : 64 ≤ N) : 1 < localization N ε ∧
      Real.sqrt (2 * localization N ε) ≤ N - localization N ε := by
  have hNp : 0 < N := by linarith
  have hY : 1 < localization N ε :=
    Real.one_lt_rpow (by linarith) (by positivity : (0 : ℝ) < 7 / 12 + ε)
  have hthird : (4 : ℝ) ≤ N ^ (1 / 3 : ℝ) := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
        _ ≤ N ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num at hN ⊢; exact hN)
          (by norm_num)
  have hYhi : localization N ε ≤ N ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hpowid : N ^ (1 / 3 : ℝ) * N ^ (2 / 3 : ℝ) = N := by
    rw [← Real.rpow_add hNp]
    norm_num
  have hfour : 4 * localization N ε ≤ N := by
    calc _ ≤ 4 * N ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left hYhi (by norm_num)
      _ ≤ N ^ (1 / 3 : ℝ) * N ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right hthird (Real.rpow_nonneg hNp.le _)
      _ = N := hpowid
  refine ⟨hY, ?_⟩
  have hs : Real.sqrt (2 * localization N ε) ≤ 2 * localization N ε := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [sq_nonneg (localization N ε - 1)]
  linarith

/-- LEAF. Page 263 displays 46 and 47 and page 286 final subtraction.
The elementary Buchstab identity has its error absorbed into 0.005 of the
positive main term. Cutoff boundary terms are absorbed too.
This leaf asserts no bound for any of the three sieve terms. -/
theorem representation_bridge :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ n ∈ window N ε,
      0 < scale N (localization N ε) n ∧
      initial N (localization N ε) n - subtraction N (localization N ε) n +
        recovery N (localization N ε) n - 0.005 * scale N (localization N ε) n ≤
        (representations N (localization N ε) n : ℝ) := by
  obtain ⟨Na, ha⟩ := bridge_error_absorption
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε hε he
  refine ⟨max Na 64, ?_⟩
  intro N hN n hn
  have hNa : Na ≤ N := (le_max_left _ _).trans hN
  have hN64 : 64 ≤ N := (le_max_right _ _).trans hN
  have hN1 : 1 < N := by linarith
  have hN1le : 1 ≤ N := by linarith
  have he100 : ε < 1 / 100 := he
  have he11 : 11 * ε ≤ 14 / 27 := by linarith
  obtain ⟨hnI, hnEven⟩ := Finset.mem_filter.mp hn
  obtain ⟨hY, hsqrt⟩ := bridge_localization_domain hε he100 hN64
  have hzsqrt : (localization N ε) ^ (16 / 135 : ℝ) ≤
      Real.sqrt (2 * localization N ε) := by
    rw [Real.sqrt_eq_rpow]
    calc
      (localization N ε) ^ (16 / 135 : ℝ) ≤ (localization N ε) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY.le (by norm_num)
      _ ≤ (2 * localization N ε) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hz : (localization N ε) ^ (16 / 135 : ℝ) ≤ N - localization N ε := hzsqrt.trans hsqrt
  have hnupper : (n : ℝ) ≤ N + localization N ε :=
    window_le_N_add_localization hN1le he11 hn
  have hfinite := bridge_finite_bound N (localization N ε)
    ((localization N ε) ^ (16 / 135 : ℝ)) n rfl hz hsqrt hnupper (by linarith)
  obtain ⟨hs, herr⟩ := ha ε N hε (by linarith) hNa n hnEven
  exact ⟨hs, by linarith⟩


/-- The rpow/log comparison used per block: for `1 ≤ N`, `X/2 ≤ N ≤ 3X` and `4 ≤ X`,
`N^a / log N^B ≤ 3^a * 2^B * X^a / log X^B`. -/
private lemma rpow_log_div_le {a B X N : ℝ} (ha : 0 < a) (hB : 0 < B) (hX : 1 ≤ X)
    (hX4 : 4 ≤ X) (hN1 : 1 ≤ N) (hNlo : X / 2 ≤ N) (hNhi : N ≤ 3 * X) :
    N ^ a / Real.log N ^ B ≤ 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hX0 : 0 < X := by linarith
  have hNa : N ^ a ≤ 3 ^ a * X ^ a := by
    have h1 : N ^ a ≤ (3 * X) ^ a := Real.rpow_le_rpow hN0.le hNhi ha.le
    rwa [Real.mul_rpow (by norm_num) hX0.le] at h1
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogN : Real.log X / 2 ≤ Real.log N := by
    have h1 : Real.log (X / 2) ≤ Real.log N := Real.log_le_log (by linarith) hNlo
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have h2 : Real.log 2 ≤ Real.log X / 2 := by
      have h3 : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) hX4
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h3
      norm_num at h3
      linarith
    linarith
  have hlogNpos : 0 < Real.log N := lt_of_lt_of_le (by linarith) hlogN
  have h2Bpos : (0 : ℝ) < 2 ^ B := Real.rpow_pos_of_pos (by norm_num) B
  have hlogXN : Real.log X ^ B ≤ 2 ^ B * Real.log N ^ B := by
    have h1 : (Real.log X / 2) ^ B ≤ Real.log N ^ B :=
      Real.rpow_le_rpow (by positivity) hlogN hB.le
    rw [Real.div_rpow hlogXpos.le (by norm_num)] at h1
    have h2 : 2 ^ B * (Real.log X ^ B / 2 ^ B) = Real.log X ^ B := by
      rw [mul_comm (2 ^ B) (Real.log X ^ B / 2 ^ B)]
      exact div_mul_cancel₀ _ (ne_of_gt h2Bpos)
    have h3 := mul_le_mul_of_nonneg_left h1 h2Bpos.le
    linarith [h2, h3]
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlogNpos B) (Real.rpow_pos_of_pos hlogXpos B)]
  have hmain : N ^ a * Real.log X ^ B ≤ (3 ^ a * X ^ a) * (2 ^ B * Real.log N ^ B) :=
    mul_le_mul hNa hlogXN (le_of_lt (Real.rpow_pos_of_pos hlogXpos B)) (by positivity)
  calc N ^ a * Real.log X ^ B ≤ (3 ^ a * X ^ a) * (2 ^ B * Real.log N ^ B) := hmain
    _ = (3 ^ a * 2 ^ B * X ^ a) * Real.log N ^ B := by ring

/-- LEAF. Elementary interval subdivision supporting Jia page 207 and P0089 page 225.
Fixed open windows imply bounds on longer closed windows with positive exponent
slack. This is a general counting statement for a predicate P. -/
theorem extend_windows (P : ℕ → Prop) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hlocal : ∀ B : ℝ, 0 < B → ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((Ioc ⌊N⌋₊ ⌊N + N ^ a⌋₊).filter P).card : ℝ) ≤ C * N ^ a / Real.log N ^ B) :
    ∀ B : ℝ, 0 < B → ∃ C X₀ : ℝ, ∀ X H : ℝ, X₀ ≤ X → X ^ b ≤ H → H ≤ X →
      (((Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P).card : ℝ) ≤ C * H / Real.log X ^ B := by
  intro B hB
  obtain ⟨C, N₀, hC⟩ := hlocal B hB
  set C₀ : ℝ := max C 0 with hC₀def
  have hC₀nonneg : 0 ≤ C₀ := by rw [hC₀def]; exact le_max_right _ _
  have hCC : C ≤ C₀ := by rw [hC₀def]; exact le_max_left _ _
  have hbpos : 0 < b := lt_trans ha hab
  -- eventual inequality log X ^ B ≤ X ^ b
  have hlogev : ∀ᶠ X : ℝ in Filter.atTop, Real.log X ^ B ≤ X ^ b := by
    have hbB : 0 < b / B := div_pos hbpos hB
    have h1 : Real.log =o[Filter.atTop] (fun x : ℝ => x ^ (b / B)) :=
      isLittleO_log_rpow_atTop hbB
    filter_upwards [h1.eventuallyLE, Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx1
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlognn,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
    calc Real.log x ^ B ≤ (x ^ (b / B)) ^ B := Real.rpow_le_rpow hlognn hx hB.le
      _ = x ^ b := by
            rw [← Real.rpow_mul hx0.le]
            congr 1
            field_simp
  rw [Filter.eventually_atTop] at hlogev
  obtain ⟨X₁, hX₁⟩ := hlogev
  set X₀ : ℝ := max (max (N₀ + 2) X₁) (max 4 (8 ^ (1 / a))) with hX₀def
  refine ⟨25 * C₀ * 3 ^ a * 2 ^ B + 1, X₀, ?_⟩
  intro X H hX hXb hHX
  rw [hX₀def] at hX
  have hX4 : 4 ≤ X :=
    le_trans (le_trans (le_max_left (4 : ℝ) (8 ^ (1 / a)))
      (le_max_right (max (N₀ + 2) X₁) (max 4 (8 ^ (1 / a))))) hX
  have hX8a : 8 ^ (1 / a) ≤ X :=
    le_trans (le_trans (le_max_right (4 : ℝ) (8 ^ (1 / a)))
      (le_max_right (max (N₀ + 2) X₁) (max 4 (8 ^ (1 / a))))) hX
  have hXN₀ : N₀ + 2 ≤ X :=
    le_trans (le_trans (le_max_left (N₀ + 2) X₁)
      (le_max_left (max (N₀ + 2) X₁) (max 4 (8 ^ (1 / a))))) hX
  have hXX₁ : X₁ ≤ X :=
    le_trans (le_trans (le_max_right (N₀ + 2) X₁)
      (le_max_left (max (N₀ + 2) X₁) (max 4 (8 ^ (1 / a))))) hX
  have hX1le : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hlogXB : Real.log X ^ B ≤ X ^ b := hX₁ X hXX₁
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos b) hXb
  have hH1 : 1 ≤ H := (Real.one_le_rpow hX1le hbpos.le).trans hXb
  have hXaH : X ^ a ≤ H :=
    (Real.rpow_le_rpow_of_exponent_le hX1le (le_of_lt hab)).trans hXb
  have hXa8 : 8 ≤ X ^ a := by
    have h1 : ((8 : ℝ) ^ (1 / a)) ^ a = 8 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8), div_mul_cancel₀ _ (ne_of_gt ha),
        Real.rpow_one]
    have h2 : ((8 : ℝ) ^ (1 / a)) ^ a ≤ X ^ a :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hX8a ha.le
    rwa [h1] at h2
  -- the block length, the number of blocks, and the left end
  set m : ℕ := ⌊X⌋₊ with hmdef
  have hmle : (m : ℝ) ≤ X := by rw [hmdef]; exact Nat.floor_le hXpos.le
  have hmgt : X - 1 < (m : ℝ) := by rw [hmdef]; linarith [Nat.lt_floor_add_one X]
  have hmge : X / 2 ≤ (m : ℝ) := by linarith
  set L : ℕ := ⌊X ^ a / 4⌋₊ with hLdef
  have hLle : (L : ℝ) ≤ X ^ a / 4 := by
    rw [hLdef]; exact Nat.floor_le (by positivity)
  have hLgt : X ^ a / 4 - 1 < (L : ℝ) := by
    rw [hLdef]; linarith [Nat.lt_floor_add_one (X ^ a / 4)]
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    apply Nat.le_floor
    rw [Nat.cast_one]
    linarith
  have hLpos : 0 < L := hL1
  have hLposR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLposR
  have hLXa : (L : ℝ) ≤ X ^ a / 4 := hLle
  set k : ℕ := ⌈(H + 2) / (L : ℝ)⌉₊ with hkdef
  have hkL : H + 2 ≤ (k : ℝ) * L := by
    have h := Nat.le_ceil ((H + 2) / (L : ℝ))
    have h2 := (div_le_iff₀ hLposR).mp h
    simpa only [hkdef] using h2
  have hkub : (k : ℝ) ≤ (H + 2) / (L : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (H + 2) / (L : ℝ) := by positivity
    have h := Nat.ceil_lt_add_one h0
    have : (k : ℝ) < (H + 2) / (L : ℝ) + 1 := by simpa only [hkdef] using h
    linarith
  have hk1 : 1 ≤ k := by
    have h1 : (L : ℝ) ≤ H + 2 := by linarith [hLle, hXaH, hL1]
    have hkne : k ≠ 0 := by
      intro h0
      rw [h0] at hkL
      simp only [Nat.cast_zero, zero_mul] at hkL
      linarith [hLposR]
    omega
  -- the cover
  have hcover : (Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P ⊆
      insert ⌈X⌉₊ ((range k).biUnion (fun j =>
        (Ioc (m + j * L) (m + (j + 1) * L)).filter P)) := by
    intro n hn
    rw [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hlo, hhi⟩, hP⟩ := hn
    rw [mem_insert]
    rcases eq_or_ne n ⌈X⌉₊ with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [mem_biUnion]
      have hmlt : m < n := by
        have hmc : m ≤ ⌈X⌉₊ := Nat.floor_le_ceil X
        omega
      have ht2 : (((n - m - 1 : ℕ)) : ℝ) < H + 2 := by
        have h1 : (n : ℝ) ≤ X + H :=
          le_trans (by exact_mod_cast hhi) (Nat.floor_le (by linarith))
        have h2 : (((n - m - 1 : ℕ)) : ℝ) = (n : ℝ) - (m : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n - m), Nat.cast_sub (by omega : m ≤ n)]
          push_cast
          ring
        rw [h2]
        linarith
      set j : ℕ := (n - m - 1) / L with hjdef
      set r : ℕ := (n - m - 1) % L with hrdef
      have htj : j * L + r = n - m - 1 := by
        rw [hjdef, hrdef, mul_comm]
        exact Nat.div_add_mod (n - m - 1) L
      have hrL : r < L := by rw [hrdef]; exact Nat.mod_lt _ hLpos
      refine ⟨j, ?_, ?_⟩
      · rw [mem_range]
        have hltR : (((j * L : ℕ)) : ℝ) < (k : ℝ) * L := by
          have ht1 : (((j * L : ℕ)) : ℝ) ≤ (((n - m - 1 : ℕ)) : ℝ) := by
            exact_mod_cast (by omega : j * L ≤ n - m - 1)
          linarith [ht1, ht2, hkL]
        have hlt : j * L < k * L := by exact_mod_cast hltR
        exact (Nat.mul_lt_mul_right hLpos).mp hlt
      · rw [mem_filter]
        refine ⟨?_, hP⟩
        rw [mem_Ioc]
        constructor
        · have h1 : m + j * L ≤ n - 1 := by omega
          omega
        · have h1 : n ≤ m + (j * L + L) := by omega
          have h2 : (j + 1) * L = j * L + L := by ring
          omega
  have hcard1 : ((Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P).card ≤
      ((range k).biUnion (fun j =>
        (Ioc (m + j * L) (m + (j + 1) * L)).filter P)).card + 1 :=
    (card_le_card hcover).trans (card_insert_le _ _)
  have hcard2 : (((range k).biUnion (fun j =>
        (Ioc (m + j * L) (m + (j + 1) * L)).filter P)).card : ℝ) ≤
      ∑ j ∈ range k, (((Ioc (m + j * L) (m + (j + 1) * L)).filter P).card : ℝ) := by
    have h := card_biUnion_le (s := range k)
      (t := fun j => (Ioc (m + j * L) (m + (j + 1) * L)).filter P)
    exact_mod_cast h
  have hterm : ∀ j ∈ range k, (((Ioc (m + j * L) (m + (j + 1) * L)).filter P).card : ℝ) ≤
      C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B := by
    intro j hj
    have hjk : j < k := mem_range.mp hj
    have hjL : (j : ℝ) * L ≤ H + 2 := by
      have hjk1 : j ≤ k - 1 := by omega
      have h1 : ((j : ℕ) : ℝ) * L ≤ ((k - 1 : ℕ) : ℝ) * L := by
        have : (j : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hjk1
        exact mul_le_mul_of_nonneg_right this hLposR.le
      have h2 : ((k - 1 : ℕ) : ℝ) * L < H + 2 := by
        have hku : (k : ℝ) < (H + 2) / (L : ℝ) + 1 := by
          have h0 : (0 : ℝ) ≤ (H + 2) / (L : ℝ) := by positivity
          have h := Nat.ceil_lt_add_one h0
          have : (k : ℝ) < (H + 2) / (L : ℝ) + 1 := by simpa only [hkdef] using h
          linarith
        have h3 : (k : ℝ) - 1 < (H + 2) / (L : ℝ) := by linarith
        have h4 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub hk1]
          norm_num
        rw [h4]
        exact (lt_div_iff₀ hLposR).mp h3
      linarith
    have hNhi : (((m + j * L : ℕ)) : ℝ) ≤ 3 * X := by
      have hcast : (((m + j * L : ℕ)) : ℝ) = (m : ℝ) + (j : ℝ) * L := by push_cast; ring
      rw [hcast]
      linarith [hmle, hjL, hHX]
    have hNlo : X / 2 ≤ (((m + j * L : ℕ)) : ℝ) := by
      have hcast : (((m + j * L : ℕ)) : ℝ) = (m : ℝ) + (j : ℝ) * L := by push_cast; ring
      rw [hcast]
      have : (0 : ℝ) ≤ (j : ℝ) * L := by positivity
      linarith
    have hN1 : 1 ≤ (((m + j * L : ℕ)) : ℝ) := by
      have hcast : (((m + j * L : ℕ)) : ℝ) = (m : ℝ) + (j : ℝ) * L := by push_cast; ring
      rw [hcast]
      linarith [hmge, hX4]
    have hN₀le : N₀ ≤ (((m + j * L : ℕ)) : ℝ) := by
      have hcast : (((m + j * L : ℕ)) : ℝ) = (m : ℝ) + (j : ℝ) * L := by push_cast; ring
      rw [hcast]
      have : N₀ ≤ (m : ℝ) := by linarith
      have : (0 : ℝ) ≤ (j : ℝ) * L := by positivity
      linarith
    have hloc := hC (((m + j * L : ℕ)) : ℝ) hN₀le
    simp only [Nat.floor_natCast] at hloc
    have hLpow : (L : ℝ) ≤ (((m + j * L : ℕ)) : ℝ) ^ a := by
      have h2 : X ^ a / 4 ≤ (X / 2) ^ a := by
        rw [Real.div_rpow hXpos.le (by norm_num)]
        have h2a : (2 : ℝ) ^ a ≤ 4 := by
          have h3 := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
            (by linarith : a ≤ 2)
          norm_num at h3
          linarith
        rw [div_le_div_iff₀ (by norm_num) (Real.rpow_pos_of_pos (by norm_num) a)]
        nlinarith [Real.rpow_pos_of_pos hXpos a]
      have h3 : (X / 2) ^ a ≤ (((m + j * L : ℕ)) : ℝ) ^ a :=
        Real.rpow_le_rpow (by positivity) (by linarith [hmge]) ha.le
      linarith
    have hfloor : m + (j + 1) * L ≤ ⌊(((m + j * L : ℕ)) : ℝ) +
        (((m + j * L : ℕ)) : ℝ) ^ a⌋₊ := by
      apply Nat.le_floor
      have hcast : (((m + (j + 1) * L : ℕ)) : ℝ) = (((m + j * L : ℕ)) : ℝ) + (L : ℝ) := by
        push_cast; ring
      rw [hcast]
      linarith
    have hsub : (Ioc (m + j * L) (m + (j + 1) * L)).filter P ⊆
        (Ioc (m + j * L) ⌊(((m + j * L : ℕ)) : ℝ) +
          (((m + j * L : ℕ)) : ℝ) ^ a⌋₊).filter P := by
      apply filter_subset_filter
      intro n hn
      rw [mem_Ioc] at hn ⊢
      obtain ⟨h1, h2⟩ := hn
      exact ⟨h1, le_trans h2 hfloor⟩
    have hcard_le : (((Ioc (m + j * L) (m + (j + 1) * L)).filter P).card : ℝ) ≤
        (((Ioc (m + j * L) ⌊(((m + j * L : ℕ)) : ℝ) +
          (((m + j * L : ℕ)) : ℝ) ^ a⌋₊).filter P).card : ℝ) :=
      Nat.cast_le.mpr (card_le_card hsub)
    have hCC' : C * (((m + j * L : ℕ)) : ℝ) ^ a / Real.log (((m + j * L : ℕ)) : ℝ) ^ B ≤
        C₀ * (((m + j * L : ℕ)) : ℝ) ^ a / Real.log (((m + j * L : ℕ)) : ℝ) ^ B := by
      apply div_le_div_of_nonneg_right _ (le_of_lt ?_)
      · exact mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg (by positivity) a)
      · exact Real.rpow_pos_of_pos (Real.log_pos (by linarith [hN1])) B
    have hrp := rpow_log_div_le ha hB hX1le hX4 hN1 hNlo hNhi
    calc (((Ioc (m + j * L) (m + (j + 1) * L)).filter P).card : ℝ)
        ≤ C * (((m + j * L : ℕ)) : ℝ) ^ a / Real.log (((m + j * L : ℕ)) : ℝ) ^ B :=
          hcard_le.trans hloc
      _ ≤ C₀ * (((m + j * L : ℕ)) : ℝ) ^ a / Real.log (((m + j * L : ℕ)) : ℝ) ^ B := hCC'
      _ = C₀ * ((((m + j * L : ℕ)) : ℝ) ^ a / Real.log (((m + j * L : ℕ)) : ℝ) ^ B) := by
          rw [mul_div_assoc]
      _ ≤ C₀ * (3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B) :=
          mul_le_mul_of_nonneg_left hrp hC₀nonneg
      _ = C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B := by
          rw [mul_div_assoc]
          ring
  have hLX : X ^ a / (L : ℝ) ≤ 8 := by
    have hXapos : 0 < X ^ a := Real.rpow_pos_of_pos hXpos a
    have hLge : X ^ a / 8 ≤ (L : ℝ) := by linarith [hLgt, hXa8]
    rw [div_le_iff₀ hLposR]
    linarith
  have hkX : (k : ℝ) * X ^ a ≤ 25 * H := by
    have h1 : (k : ℝ) * X ^ a ≤ ((H + 2) / (L : ℝ) + 1) * X ^ a :=
      mul_le_mul_of_nonneg_right hkub (Real.rpow_nonneg hXpos.le a)
    have h2 : ((H + 2) / (L : ℝ) + 1) * X ^ a = (H + 2) * (X ^ a / (L : ℝ)) + X ^ a := by
      field_simp
    have h3 : (H + 2) * (X ^ a / (L : ℝ)) + X ^ a ≤ 25 * H := by nlinarith [hLX, hXaH, hH1]
    linarith
  have hlogposX : 0 < Real.log X ^ B := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) B
  have hSnonneg : 0 ≤ C₀ * 3 ^ a * 2 ^ B :=
    mul_nonneg (mul_nonneg hC₀nonneg (Real.rpow_nonneg (by norm_num) a))
      (Real.rpow_nonneg (by norm_num) B)
  have hSlog : 0 ≤ C₀ * 3 ^ a * 2 ^ B / Real.log X ^ B := div_nonneg hSnonneg hlogposX.le
  have hfinal : (1 : ℝ) ≤ H / Real.log X ^ B := by
    rw [le_div_iff₀ hlogposX]
    linarith
  have hcard3 : (((Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P).card : ℝ) ≤
      1 + (k : ℝ) * (C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B) := by
    have h1 : (((Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P).card : ℝ) ≤
        (((range k).biUnion (fun j =>
          (Ioc (m + j * L) (m + (j + 1) * L)).filter P)).card : ℝ) + 1 := by
      exact_mod_cast hcard1
    have h2 : (((range k).biUnion (fun j =>
          (Ioc (m + j * L) (m + (j + 1) * L)).filter P)).card : ℝ) ≤
        ∑ j ∈ range k, (C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B) :=
      hcard2.trans (sum_le_sum hterm)
    have h3 : (∑ j ∈ range k, (C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B))
        = (k : ℝ) * (C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B) := by
      rw [sum_const, card_range, nsmul_eq_mul]
    linarith [h1, h2, h3]
  calc (((Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P).card : ℝ)
      ≤ 1 + (k : ℝ) * (C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B) := hcard3
    _ = 1 + ((k : ℝ) * X ^ a) * (C₀ * 3 ^ a * 2 ^ B / Real.log X ^ B) := by
          field_simp
    _ ≤ H / Real.log X ^ B + (25 * H) * (C₀ * 3 ^ a * 2 ^ B / Real.log X ^ B) := by
          have ha2 : ((k : ℝ) * X ^ a) * (C₀ * 3 ^ a * 2 ^ B / Real.log X ^ B) ≤
              (25 * H) * (C₀ * 3 ^ a * 2 ^ B / Real.log X ^ B) :=
            mul_le_mul_of_nonneg_right hkX hSlog
          linarith
    _ = (25 * C₀ * 3 ^ a * 2 ^ B + 1) * H / Real.log X ^ B := by
          field_simp
          ring


/-- Page 262 display 43: a positive restricted count supplies a Goldbach sum. -/
theorem goldbach_of_representations {N Y : ℝ} {n : ℕ}
    (h : 0 < representations N Y n) : IsGoldbachSum n := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  obtain ⟨hpRange, hpPrime, hqPrime, _⟩ := Finset.mem_filter.mp hp
  exact ⟨p, n - p, hpPrime, hqPrime,
    Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hpRange))⟩

/-- Page 286: the numerical sieve margin is positive after the error. -/
theorem positive_margin (u v w s t : ℝ) (hs : 0 < s)
    (hu : 4.735124 * s ≤ u) (hv : v ≤ 6.822470 * s)
    (hw : 2.104057 * s ≤ w) (ht : u - v + w - 0.005 * s ≤ t) : 0 < t := by linarith

/-- Page 286: the union of the three sieve exceptional sets retains the log bound.
CONDITIONAL ON the three analytic bounds and representation_bridge. -/
theorem local_exception_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((Ioc ⌊N⌋₊ ⌊N + windowLength N ε⌋₊).filter
        (fun n => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨ε₁, he₁, hi⟩ := initial_bound
  obtain ⟨ε₂, he₂, hj⟩ := subtraction_bound
  obtain ⟨ε₃, he₃, hk⟩ := recovery_bound
  obtain ⟨ε₄, he₄, hl⟩ := representation_bridge
  refine ⟨min (min ε₁ ε₂) (min ε₃ ε₄), lt_min (lt_min he₁ he₂) (lt_min he₃ he₄), ?_⟩
  intro ε B hε hεsmall hB
  have hε₁ : ε < ε₁ := hεsmall.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε₂ : ε < ε₂ := hεsmall.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε₃ : ε < ε₃ := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε₄ : ε < ε₄ := hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁, N₁, h₁⟩ := hi ε B hε hε₁ hB
  obtain ⟨C₂, N₂, h₂⟩ := hj ε B hε hε₂ hB
  obtain ⟨C₃, N₃, h₃⟩ := hk ε B hε hε₃ hB
  obtain ⟨N₄, h₄⟩ := hl ε hε hε₄
  refine ⟨C₁ + C₂ + C₃, max (max N₁ N₂) (max N₃ N₄), ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₃ : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₄ : N₄ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let bad₁ := (window N ε).filter (fun n =>
    initial N (localization N ε) n < 4.735124 * scale N (localization N ε) n)
  let bad₂ := (window N ε).filter (fun n =>
    6.822470 * scale N (localization N ε) n < subtraction N (localization N ε) n)
  let bad₃ := (window N ε).filter (fun n =>
    recovery N (localization N ε) n < 2.104057 * scale N (localization N ε) n)
  have hsub : ((Ioc ⌊N⌋₊ ⌊N + windowLength N ε⌋₊).filter
      (fun n => Even n ∧ ¬ IsGoldbachSum n)) ⊆ (bad₁ ∪ bad₂) ∪ bad₃ := by
    intro n hn
    obtain ⟨hnI, hne, hng⟩ := Finset.mem_filter.mp hn
    have hnw : n ∈ window N ε := Finset.mem_filter.mpr ⟨hnI, hne⟩
    by_contra hnBad
    have hb₁ : ¬ n ∈ bad₁ := fun h => hnBad (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl h))))
    have hb₂ : ¬ n ∈ bad₂ := fun h => hnBad (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr h))))
    have hb₃ : ¬ n ∈ bad₃ := fun h => hnBad (mem_union.mpr (Or.inr h))
    have hu : 4.735124 * scale N (localization N ε) n ≤ initial N (localization N ε) n :=
      le_of_not_gt (fun h => hb₁ (mem_filter.mpr ⟨hnw, h⟩))
    have hv : subtraction N (localization N ε) n ≤ 6.822470 * scale N (localization N ε) n :=
      le_of_not_gt (fun h => hb₂ (mem_filter.mpr ⟨hnw, h⟩))
    have hw : 2.104057 * scale N (localization N ε) n ≤ recovery N (localization N ε) n :=
      le_of_not_gt (fun h => hb₃ (mem_filter.mpr ⟨hnw, h⟩))
    obtain ⟨hs, ht⟩ := h₄ N hN₄ n hnw
    have hpos := positive_margin _ _ _ _ _ hs hu hv hw ht
    exact hng (goldbach_of_representations (by exact_mod_cast hpos))
  have hcard := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcardR : (((Ioc ⌊N⌋₊ ⌊N + windowLength N ε⌋₊).filter
      (fun n => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) ≤
      (bad₁.card : ℝ) + bad₂.card + bad₃.card := by exact_mod_cast hcard
  have hsum := add_le_add (add_le_add (h₁ N hN₁) (h₂ N hN₂)) (h₃ N hN₃)
  calc _ ≤ (bad₁.card : ℝ) + bad₂.card + bad₃.card := hcardR
       _ ≤ C₁ * windowLength N ε / Real.log N ^ B +
         C₂ * windowLength N ε / Real.log N ^ B +
         C₃ * windowLength N ε / Real.log N ^ B := hsum
       _ = _ := by ring

/-- The exact statement of EncA.jia from five smaller OPEN leaves.
CONDITIONAL ON initial_bound, subtraction_bound, recovery_bound,
representation_bridge and extend_windows. -/
theorem jia_from_leaves : Theorem1_5 := by
  intro ε hε
  let b : ℝ := min (7 / 108 + ε) (1 / 2)
  obtain ⟨ε₀, he₀, hlocal⟩ := local_exception_bound
  let η : ℝ := min (min (ε / 24) (1 / 2000)) (ε₀ / 2)
  have hη : 0 < η := lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hηsmall : η < ε₀ := (min_le_right _ _).trans_lt (by linarith)
  have hηε : η ≤ ε / 24 := (min_le_left _ _).trans (min_le_left _ _)
  have hηcap : η ≤ 1 / 2000 := (min_le_left _ _).trans (min_le_right _ _)
  have ha : (0 : ℝ) < 7 / 108 + 12 * η := by positivity
  have hab : 7 / 108 + 12 * η < b := by
    apply lt_min
    · linarith
    · linarith
  have hb : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hext := extend_windows (fun n => Even n ∧ ¬ IsGoldbachSum n)
    (7 / 108 + 12 * η) b ha hab hb
    (fun B hB => by
      obtain ⟨C, N₀, hC⟩ := hlocal η B hη hηsmall hB
      refine ⟨C, N₀, ?_⟩
      intro N hN
      convert hC N hN using 1 <;> unfold windowLength <;> congr 2 <;> ext n <;> simp)
  apply LogFrom_mono (r := b) (min_le_left _ _)
  intro B hB
  obtain ⟨C, X₀, hC⟩ := hext B hB
  refine ⟨C, X₀, ?_⟩
  intro X H hX hH hHu
  convert hC X H hX hH hHu using 1
  unfold LeanLab.LanguascoPerelli1996.EH
  congr 2
  ext n
  simp

#print axioms initial_bound
#print axioms subtraction_bound
#print axioms recovery_bound
#print axioms representation_bridge
#print axioms extend_windows
#print axioms goldbach_of_representations
#print axioms positive_margin
#print axioms local_exception_bound
#print axioms jia_from_leaves
end
end LeanLab.Languasco2004.Decomp279a
