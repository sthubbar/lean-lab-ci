/-
Jia 1996, page 262 display 45, page 263 displays 46 and 47,
and page 286 final assembly. Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The sealed representation bridge is not changed.
-/
import LeanLab.Languasco2004.Decomp316a

namespace LeanLab.Languasco2004.Decomp316d
open Finset Real Decomp279a Decomp316a
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 262 display 45: the loss in a prime Euler factor. -/
def primeLoss (p : Nat.Primes) : ℝ := 1 / ((p : ℝ) - 1) ^ 2

/-- Page 262 display 45: omit the prime two from the universal lower product. -/
def tailLoss (p : Nat.Primes) : ℝ := if (p : ℕ) = 2 then 0 else primeLoss p

/-- Page 262 display 45: a universal positive lower product for even n. -/
def tailProduct : ℝ := ∏' p : Nat.Primes, (1 - tailLoss p)

/-- Page 262 display 45: the losses are dominated by the convergent square series. -/
theorem summable_primeLoss : Summable primeLoss := by
  have h := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))).comp_injective
    (show Function.Injective (fun p : Nat.Primes => (p : ℕ)) from Subtype.val_injective)
  have h4 := h.mul_left 4
  apply h4.of_nonneg_of_le (fun p => by unfold primeLoss; positivity)
  intro p
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hp0 : 0 < (p : ℝ) := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  change 1 / ((p : ℝ) - 1) ^ 2 ≤ 4 * (1 / (p : ℝ) ^ 2)
  rw [mul_one_div, div_le_div_iff₀ (sq_pos_of_pos hp1) (sq_pos_of_pos hp0)]
  nlinarith [sq_nonneg ((p : ℝ) - 2)]

/-- Page 262 display 45: every factor in the lower product is positive. -/
theorem tail_factor_pos (p : Nat.Primes) : 0 < 1 - tailLoss p := by
  unfold tailLoss
  split_ifs with hp
  · norm_num
  · have hp3 : (3 : ℝ) ≤ p := by
      have h := p.property.two_le
      have : 3 ≤ (p : ℕ) := by omega
      exact_mod_cast this
    have hs : 1 < ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hdiv : 1 / ((p : ℝ) - 1) ^ 2 < 1 := (div_lt_one (by positivity)).mpr hs
    exact sub_pos.mpr hdiv

/-- Page 262 display 45: the lower Euler product converges and is nonzero. -/
theorem tailProduct_pos : 0 < tailProduct := by
  have hp0 : ∀ p, 0 ≤ primeLoss p := fun p => by unfold primeLoss; positivity
  have ht0 : ∀ p, 0 ≤ tailLoss p := fun p => by unfold tailLoss; split_ifs; exact le_rfl; exact hp0 p
  have ht : Summable tailLoss := summable_primeLoss.of_nonneg_of_le
    ht0 (fun p => by unfold tailLoss; split_ifs; exact hp0 p; exact le_rfl)
  have hn : Summable (fun p => ‖-tailLoss p‖) := by
    have heq : (fun p => ‖-tailLoss p‖) = tailLoss := by
      funext p
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (ht0 p)]
    rwa [heq]
  have hne := tprod_one_add_ne_zero_of_summable
    (fun p => (show 1 + -tailLoss p ≠ 0 from ne_of_gt (by simpa only [sub_eq_add_neg] using tail_factor_pos p))) hn
  have hnonneg : 0 ≤ tailProduct := tprod_nonneg (fun p => (tail_factor_pos p).le)
  exact lt_of_le_of_ne hnonneg (by simpa only [tailProduct, sub_eq_add_neg] using hne.symm)

/-- Page 262 display 45: all even n share the same positive singular lower bound. -/
theorem tailProduct_le_singular (n : ℕ) (hn : Even n) : tailProduct ≤ singular n := by
  have hp0 : ∀ p, 0 ≤ primeLoss p := fun p => by unfold primeLoss; positivity
  have ht0 : ∀ p, 0 ≤ tailLoss p := fun p => by unfold tailLoss; split_ifs; exact le_rfl; exact hp0 p
  let loss : Nat.Primes → ℝ := fun p => if (p : ℕ) ∣ n then 0 else primeLoss p
  have htwo : 2 ∣ n := even_iff_two_dvd.mp hn
  have hle : ∀ p, loss p ≤ tailLoss p := by
    intro p
    by_cases hp : (p : ℕ) = 2
    · simp [loss, tailLoss, hp, htwo]
    · simp only [tailLoss, hp, ite_false, loss]
      split_ifs
      · exact hp0 p
      · exact le_rfl
  have hln : ∀ p, 0 ≤ loss p := by
    intro p
    unfold loss
    split_ifs
    · exact le_rfl
    · exact hp0 p
  have hl : Summable loss := summable_primeLoss.of_nonneg_of_le hln (fun p => by
    unfold loss
    split_ifs
    · exact hp0 p
    · exact le_rfl)
  have ht : Summable tailLoss := summable_primeLoss.of_nonneg_of_le
    ht0 (fun p => by unfold tailLoss; split_ifs; exact hp0 p; exact le_rfl)
  have hm : Multipliable (fun p => 1 - loss p) := by
    simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hl.neg
  have htm : Multipliable (fun p => 1 - tailLoss p) := by
    simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable ht.neg
  have hc : tailProduct ≤ ∏' p, (1 - loss p) :=
    le_of_tendsto_of_tendsto' htm.hasProd hm.hasProd (fun s =>
      Finset.prod_le_prod₀ (fun p _ => (tail_factor_pos p).le) (fun p _ => by linarith [hle p]))
  have heq : (∏' p : Nat.Primes, if (p : ℕ) ∣ n then 1 else
      1 - 1 / ((p : ℝ) - 1) ^ 2) = ∏' p, (1 - loss p) := by
    congr 1
    ext p
    by_cases hp : (p : ℕ) ∣ n <;> simp [loss, primeLoss, hp]
  have hf : 1 ≤ ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
    apply Finset.one_le_prod₀
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hpos : 0 < (p : ℝ) - 1 := by linarith
    have : 0 ≤ 1 / ((p : ℝ) - 1) := by positivity
    linarith
  unfold singular
  rw [heq]
  exact hc.trans (le_mul_of_one_le_right (tprod_nonneg (fun p =>
    le_trans (tail_factor_pos p).le (by linarith [hle p]))) hf)

/-- Page 262 display 44: the common main term is positive at even n. -/
theorem scale_pos {N Y : ℝ} (n : ℕ) (hn : Even n) (hN : 1 < N) (hY : 1 < Y) :
    0 < scale N Y n := by
  exact div_pos (mul_pos (tailProduct_pos.trans_le (tailProduct_le_singular n hn))
    (by linarith)) (mul_pos (Real.log_pos hY) (Real.log_pos hN))

/-- Page 263 display 46, one sided prime extraction with explicit domain.
Only a = 1 can survive without giving a prime representation. -/
theorem prime_extraction (N Y : ℝ) (n : ℕ)
    (hn : (n : ℝ) ≤ N + Y) (hsmall : Real.sqrt (2 * Y) ≤ N - Y) :
    sifted N Y n 1 (Real.sqrt (2 * Y)) ≤ representations N Y n + 1 := by
  let s := (Icc 1 n).filter (fun a => 1 ∣ a ∧ (n - a).Prime ∧
    N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
    ∀ p : ℕ, p.Prime → (p : ℝ) < Real.sqrt (2 * Y) → ¬ p ∣ n → ¬ p ∣ a)
  let r := (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ (n - p).Prime ∧
    N - Y < (p : ℝ) ∧ (p : ℝ) ≤ N ∧ ((n - p : ℕ) : ℝ) ≤ 2 * Y)
  have hsub : s ⊆ insert 1 (r.image (fun p => n - p)) := by
    intro a ha
    by_cases ha1 : a = 1
    · exact mem_insert.mpr (Or.inl ha1)
    · obtain ⟨haI, _, hprime, hL, hU, hs⟩ := mem_filter.mp ha
      obtain ⟨ha0, han⟩ := mem_Icc.mp haI
      have hcast : ((n - a : ℕ) : ℝ) = (n : ℝ) - a := Nat.cast_sub han
      have haY : (a : ℝ) < 2 * Y := by linarith
      have hap : a.Prime := by
        by_contra hnp
        have hq : a.minFac.Prime := Nat.minFac_prime ha1
        have hqa : a.minFac ∣ a := Nat.minFac_dvd a
        have hqSq : (a.minFac : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) := by
          exact_mod_cast Nat.minFac_sq_le_self (by omega : 0 < a) hnp
        have hqLt : (a.minFac : ℝ) < Real.sqrt (2 * Y) :=
          (Real.lt_sqrt (by positivity)).mpr (lt_of_le_of_lt hqSq haY)
        have hqn : a.minFac ∣ n := by
          by_contra h
          exact hs _ hq hqLt h hqa
        have hqd : a.minFac ∣ n - a := Nat.dvd_sub hqn hqa
        have heq : n - a = a.minFac := (hprime.dvd_iff_eq hq.ne_one).mp hqd
        have heqR : ((n - a : ℕ) : ℝ) = a.minFac := by exact_mod_cast heq
        linarith
      apply mem_insert.mpr
      apply Or.inr
      apply mem_image.mpr
      refine ⟨n - a, ?_, Nat.sub_sub_self han⟩
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by omega), hprime, ?_, hL, hU, ?_⟩
      · simpa only [Nat.sub_sub_self han] using hap
      · simpa only [Nat.sub_sub_self han] using haY.le
  have hc := (card_le_card hsub).trans (card_insert_le _ _)
  have hi := card_image_le (s := r) (f := fun p => n - p)
  change s.card ≤ r.card + 1
  omega

/-- Page 263 displays 46 and 47: a conservative square root and cutoff
boundary error envelope. The extra unit covers the integer a = 1. -/
def errorEnvelope (Y : ℝ) : ℝ :=
  Real.sqrt (2 * Y) + 2 * Y / Y ^ (16 / 135 : ℝ) + 1

/-- Pages 263 and 286: the explicit error grows slower than the main scale. -/
theorem errorEnvelope_le {Y : ℝ} (hY : 1 ≤ Y) :
    errorEnvelope Y ≤ 5 * Y ^ (1 - 16 / 135 : ℝ) := by
  have hY0 : 0 < Y := by linarith
  have hhalf : Real.sqrt Y ≤ Y ^ (1 - 16 / 135 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
  have hs : Real.sqrt (2 * Y) ≤ 2 * Y ^ (1 - 16 / 135 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul (by norm_num : Real.sqrt 2 ≤ 2) hhalf (Real.sqrt_nonneg Y) (by norm_num)
  have hd : 2 * Y / Y ^ (16 / 135 : ℝ) = 2 * Y ^ (1 - 16 / 135 : ℝ) := by
    rw [Real.rpow_sub hY0, Real.rpow_one]
    ring
  have h1 : 1 ≤ Y ^ (1 - 16 / 135 : ℝ) := Real.one_le_rpow hY (by norm_num)
  unfold errorEnvelope
  rw [hd]
  linarith

/-- Page 286 final absorption: every fixed multiple of the explicit error
is eventually at most 0.005 of the scale, uniformly for small epsilon. -/
theorem error_absorption (K : ℝ) (hK : 0 < K) :
    ∃ N₀ : ℝ, ∀ ε N : ℝ, 0 < ε → ε < 1 / 12 → N₀ ≤ N → ∀ n : ℕ, Even n →
      0 < scale N (localization N ε) n ∧
      K * errorEnvelope (localization N ε) ≤ 0.005 * scale N (localization N ε) n := by
  let d : ℝ := 0.001 * tailProduct / K
  have hd : 0 < d := div_pos (mul_pos (by norm_num) tailProduct_pos) hK
  have hlittle := isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 28 / 405)
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
  have hscale := scale_pos (N := N) (Y := localization N ε) n hn (by linarith) hYp
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
  have hmain : tailProduct * localization N ε ≤ scale N (localization N ε) n * Real.log N ^ (2 : ℕ) := by
    calc tailProduct * localization N ε ≤ singular n * localization N ε :=
           mul_le_mul_of_nonneg_right (tailProduct_le_singular n hn) (by linarith)
         _ = scale N (localization N ε) n *
             (Real.log (localization N ε) * Real.log N) := by
           unfold scale
           rw [div_mul_cancel₀ _ (mul_ne_zero hLY.ne' hL.ne')]
         _ ≤ _ := mul_le_mul_of_nonneg_left hden hscale.le
  have hYid : (localization N ε) ^ (1 - 16 / 135 : ℝ) *
      (localization N ε) ^ (16 / 135 : ℝ) = localization N ε := by
    rw [← Real.rpow_add (by linarith : 0 < localization N ε)]
    norm_num
  have hbudget : K * errorEnvelope (localization N ε) * Real.log N ^ (2 : ℕ) ≤
      0.005 * tailProduct * localization N ε := by
    calc K * errorEnvelope (localization N ε) * Real.log N ^ (2 : ℕ) ≤
           (K * (5 * (localization N ε) ^ (1 - 16 / 135 : ℝ))) *
             (d * (localization N ε) ^ (16 / 135 : ℝ)) :=
           mul_le_mul (mul_le_mul_of_nonneg_left (errorEnvelope_le hYp.le) hK.le) hlog
             (sq_nonneg _) (by positivity)
         _ = 0.005 * tailProduct * localization N ε := by
           calc _ = (5 * K * d) * ((localization N ε) ^ (1 - 16 / 135 : ℝ) *
                 (localization N ε) ^ (16 / 135 : ℝ)) := by ring
                _ = _ := by rw [hYid]; dsimp [d]; field_simp; ring
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hL)).mp
  calc K * errorEnvelope (localization N ε) * Real.log N ^ (2 : ℕ) ≤
         0.005 * tailProduct * localization N ε := hbudget
       _ ≤ 0.005 * (scale N (localization N ε) n * Real.log N ^ (2 : ℕ)) := by
         nlinarith [hmain]
       _ = _ := by ring

/-- Pages 208 and 263: explicit sufficient conditions for prime extraction.
The cap 1/100 is a conservative supporting choice below the paper's small
epsilon range. It is not a claimed analytic threshold. -/
theorem localization_domain {ε N : ℝ} (hε : 0 < ε) (he : ε < 1 / 100) (hN : 64 ≤ N) :
    1 < localization N ε ∧ Real.sqrt (2 * localization N ε) ≤ N - localization N ε ∧
      windowLength N ε ≤ localization N ε := by
  have hNp : 0 < N := by linarith
  have hY : 1 < localization N ε :=
    Real.one_lt_rpow (by linarith) (by positivity : (0 : ℝ) < 7 / 12 + ε)
  have hthird : (4 : ℝ) ≤ N ^ (1 / 3 : ℝ) := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
           rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 4)]
           norm_num
         _ ≤ N ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num at hN ⊢; exact hN) (by norm_num)
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
  refine ⟨hY, ?_, ?_⟩
  · have hs : Real.sqrt (2 * localization N ε) ≤ 2 * localization N ε := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · linarith
      · nlinarith [sq_nonneg (localization N ε - 1)]
    linarith
  · unfold windowLength localization
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith

/-! ### Private finite combinatorics for the Buchstab comparison -/

/-- Box conditions and level extracted from membership in the finite sieve set. -/
private lemma mem_sieve {N Y : ℝ} {n d : ℕ} {z : ℝ} {a : ℕ}
    (ha : a ∈ (Icc 1 n).filter (fun b => d ∣ b ∧ (n - b).Prime ∧
      N - Y < ((n - b : ℕ) : ℝ) ∧ ((n - b : ℕ) : ℝ) ≤ N ∧
      ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n → ¬ p ∣ b)) :
    1 ≤ a ∧ a ≤ n ∧ d ∣ a ∧ (n - a).Prime ∧ N - Y < ((n - a : ℕ) : ℝ) ∧
      ((n - a : ℕ) : ℝ) ≤ N ∧ (∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n → ¬ p ∣ a) := by
  simp only [mem_filter, mem_Icc] at ha
  exact ⟨ha.1.1, ha.1.2, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2⟩

/-- Doubling the divisor and raising the cutoff shrinks the sieve set. -/
private lemma sieve_mem_mono {N Y : ℝ} {n d₁ d₂ : ℕ} {z₁ z₂ : ℝ}
    (hd : d₂ ∣ d₁) (hz : z₂ ≤ z₁) {a : ℕ}
    (ha : a ∈ (Icc 1 n).filter (fun b => d₁ ∣ b ∧ (n - b).Prime ∧
      N - Y < ((n - b : ℕ) : ℝ) ∧ ((n - b : ℕ) : ℝ) ≤ N ∧
      ∀ p : ℕ, p.Prime → (p : ℝ) < z₁ → ¬ p ∣ n → ¬ p ∣ b)) :
    a ∈ (Icc 1 n).filter (fun b => d₂ ∣ b ∧ (n - b).Prime ∧
      N - Y < ((n - b : ℕ) : ℝ) ∧ ((n - b : ℕ) : ℝ) ≤ N ∧
      ∀ p : ℕ, p.Prime → (p : ℝ) < z₂ → ¬ p ∣ n → ¬ p ∣ b) := by
  obtain ⟨ha1, han, hdvd, hprime, hlow, hupp, hlev⟩ := mem_sieve ha
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨ha1, han⟩, dvd_trans hd hdvd, hprime, hlow, hupp,
    fun p hp hpz hpn => hlev p hp (lt_of_lt_of_le hpz hz) hpn⟩

/-- The same statement at the level of the sifted counts. -/
private lemma sifted_mono {N Y : ℝ} {n d₁ d₂ : ℕ} {z₁ z₂ : ℝ}
    (hd : d₂ ∣ d₁) (hz : z₂ ≤ z₁) : sifted N Y n d₁ z₁ ≤ sifted N Y n d₂ z₂ := by
  apply card_le_card
  intro a ha
  exact sieve_mem_mono hd hz ha

/-- A sifted integer lies below twice the localization length. -/
private lemma sifted_le_two_mul {N Y : ℝ} {n d : ℕ} {z : ℝ} {a : ℕ}
    (hnN : (n : ℝ) ≤ N + Y)
    (ha : a ∈ (Icc 1 n).filter (fun b => d ∣ b ∧ (n - b).Prime ∧
      N - Y < ((n - b : ℕ) : ℝ) ∧ ((n - b : ℕ) : ℝ) ≤ N ∧
      ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n → ¬ p ∣ b)) :
    (a : ℝ) ≤ 2 * Y := by
  obtain ⟨ha1, han, -, -, hlow, -, -⟩ := mem_sieve ha
  have hcast : (a : ℝ) = (n : ℝ) - ((n - a : ℕ) : ℝ) := by
    rw [Nat.cast_sub han]; ring
  linarith

/-- A prime divisor below the square root cutoff never divides the window index. -/
private lemma prime_not_dvd_n {N Y : ℝ} {n d : ℕ} {z : ℝ} {a p : ℕ}
    (hNY : Real.sqrt (2 * Y) ≤ N - Y) (hp : p.Prime)
    (hpZ : (p : ℝ) ≤ Real.sqrt (2 * Y))
    (ha : a ∈ (Icc 1 n).filter (fun b => d ∣ b ∧ (n - b).Prime ∧
      N - Y < ((n - b : ℕ) : ℝ) ∧ ((n - b : ℕ) : ℝ) ≤ N ∧
      ∀ q : ℕ, q.Prime → (q : ℝ) < z → ¬ q ∣ n → ¬ q ∣ b))
    (hpa : p ∣ a) : ¬ p ∣ n := by
  obtain ⟨-, han, -, hprime, hlow, -, -⟩ := mem_sieve ha
  intro hpn
  have hdvd : p ∣ n - a := Nat.dvd_sub hpn hpa
  have hpe : n - a = p := (hprime.dvd_iff_eq hp.ne_one).mp hdvd
  have hcast : ((n - a : ℕ) : ℝ) = (p : ℝ) := by rw [hpe]
  linarith

/-- The least surviving prime above the cutoff is unique, so the recovery pairs
with a fixed larger prime are indexed by distinct integers. -/
private lemma pair_least_unique {N Y : ℝ} {n p q q' a : ℕ}
    (hNY : Real.sqrt (2 * Y) ≤ N - Y)
    (hq : q.Prime) (hqZ : (q : ℝ) ≤ Real.sqrt (2 * Y))
    (hq' : q'.Prime) (hq'Z : (q' : ℝ) ≤ Real.sqrt (2 * Y))
    (ha : a ∈ (Icc 1 n).filter (fun b => (p * q) ∣ b ∧ (n - b).Prime ∧
      N - Y < ((n - b : ℕ) : ℝ) ∧ ((n - b : ℕ) : ℝ) ≤ N ∧
      ∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ n → ¬ r ∣ b))
    (ha' : a ∈ (Icc 1 n).filter (fun b => (p * q') ∣ b ∧ (n - b).Prime ∧
      N - Y < ((n - b : ℕ) : ℝ) ∧ ((n - b : ℕ) : ℝ) ≤ N ∧
      ∀ r : ℕ, r.Prime → (r : ℝ) < (q' : ℝ) → ¬ r ∣ n → ¬ r ∣ b)) : q = q' := by
  have hqlev : ∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ n → ¬ r ∣ a :=
    (mem_sieve ha).2.2.2.2.2.2
  have hq'lev : ∀ r : ℕ, r.Prime → (r : ℝ) < (q' : ℝ) → ¬ r ∣ n → ¬ r ∣ a :=
    (mem_sieve ha').2.2.2.2.2.2
  have hqa : q ∣ a := dvd_trans (dvd_mul_left q p) (mem_sieve ha).2.2.1
  have hq'a : q' ∣ a := dvd_trans (dvd_mul_left q' p) (mem_sieve ha').2.2.1
  rcases lt_trichotomy q q' with h | h | h
  · exact absurd hqa (hq'lev q hq (by exact_mod_cast h) (prime_not_dvd_n hNY hq hqZ ha hqa))
  · exact h
  · exact absurd hq'a (hqlev q' hq' (by exact_mod_cast h) (prime_not_dvd_n hNY hq' hq'Z ha' hq'a))

/-- A finite union of disjoint sieve sets injects into the ambient set. -/
private lemma sum_card_le_card_of_subset {ι : Type*} (Q : Finset ι)
    (A : ι → Finset ℕ) (D : Finset ℕ) (hsub : ∀ q ∈ Q, A q ⊆ D)
    (hdisj : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → Disjoint (A x) (A y)) :
    ∑ q ∈ Q, (A q).card ≤ D.card := by
  rw [← Finset.card_biUnion hdisj]
  apply card_le_card
  intro a ha
  rw [mem_biUnion] at ha
  obtain ⟨q, hq, haq⟩ := ha
  exact hsub q hq haq

/-- A finite set of positive multiples of `d` below `M` has at most `M / d` elements. -/
private lemma card_multiples_le (S : Finset ℕ) (d : ℕ) (M : ℝ) (hd : 0 < d) (hM : 0 ≤ M)
    (hS : ∀ a ∈ S, 0 < a ∧ (a : ℝ) ≤ M ∧ d ∣ a) : (S.card : ℝ) ≤ M / d := by
  have hsub : S ⊆ (Ioc 0 ⌊M⌋₊).filter (fun a => d ∣ a) := by
    intro a ha
    obtain ⟨ha0, haM, hda⟩ := hS a ha
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨ha0, Nat.le_floor haM⟩, hda⟩
  have hc : S.card ≤ ⌊M⌋₊ / d := by
    simpa only [Nat.Ioc_filter_dvd_card_eq_div] using card_le_card hsub
  calc (S.card : ℝ) ≤ ((⌊M⌋₊ / d : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ (⌊M⌋₊ : ℝ) / d := Nat.cast_div_le
    _ ≤ M / d := div_le_div_of_nonneg_right (Nat.floor_le hM) (by positivity)

/-- The cutoff `Y ^ (16/135)` never exceeds the square root cutoff. -/
private lemma cutoff_le_sqrt {Y : ℝ} (hY : 1 ≤ Y) :
    Y ^ (16 / 135 : ℝ) ≤ Real.sqrt (2 * Y) := by
  calc Y ^ (16 / 135 : ℝ) ≤ Y ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
    _ = Real.sqrt Y := (Real.sqrt_eq_rpow Y).symm
    _ ≤ Real.sqrt (2 * Y) := Real.sqrt_le_sqrt (by linarith)

/-- The finite Buchstab comparison with the explicit cutoff envelope. -/
private lemma buchstab_ineq {N Y : ℝ} {n : ℕ} (hY : 1 < Y)
    (hNY : Real.sqrt (2 * Y) ≤ N - Y) (hnN : (n : ℝ) ≤ N + Y) :
    initial N Y n - subtraction N Y n + recovery N Y n ≤
      (sifted N Y n 1 (Real.sqrt (2 * Y)) : ℝ) + errorEnvelope Y := by
  have hY1 : 1 ≤ Y := hY.le
  have hYpos : 0 < Y := by linarith
  set z : ℝ := Y ^ (16 / 135 : ℝ) with hzdef
  have hzpos : 0 < z := Real.rpow_pos_of_pos hYpos _
  set Z : ℝ := Real.sqrt (2 * Y) with hZdef
  have hzZ : z ≤ Z := by rw [hzdef, hZdef]; exact cutoff_le_sqrt hY1
  set PP : Finset ℕ := (range (n + 1)).filter
    (fun p : ℕ => p.Prime ∧ z < (p : ℝ) ∧ (p : ℝ) ≤ Z) with hPP
  set QQ : ℕ → Finset ℕ := fun p => (range (n + 1)).filter
    (fun q : ℕ => q.Prime ∧ z < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))) with hQQ
  set Bs : Finset ℕ := (Icc 1 n).filter (fun a => (1 : ℕ) ∣ a ∧ (n - a).Prime ∧
      N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
      ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n → ¬ p ∣ a) with hBs
  set BZs : Finset ℕ := (Icc 1 n).filter (fun a => (1 : ℕ) ∣ a ∧ (n - a).Prime ∧
      N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
      ∀ p : ℕ, p.Prime → (p : ℝ) < Z → ¬ p ∣ n → ¬ p ∣ a) with hBZs
  set Bp : ℕ → Finset ℕ := fun p => (Icc 1 n).filter (fun a => p ∣ a ∧ (n - a).Prime ∧
      N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
      ∀ q : ℕ, q.Prime → (q : ℝ) < z → ¬ q ∣ n → ¬ q ∣ a) with hBp
  set Bpq : ℕ → ℕ → Finset ℕ := fun p q => (Icc 1 n).filter
    (fun a => (p * q) ∣ a ∧ (n - a).Prime ∧
      N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
      ∀ r : ℕ, r.Prime → (r : ℝ) < (q : ℝ) → ¬ r ∣ n → ¬ r ∣ a) with hBpq
  set Gp : ℕ → Finset ℕ := fun p => (Bp p).filter
    (fun a => ∀ r : ℕ, r.Prime → z ≤ (r : ℝ) → (r : ℝ) < (p : ℝ) → ¬ r ∣ a) with hGp
  set Bnd : Finset ℕ := Bs.filter (fun a => ∃ p : ℕ, p.Prime ∧ (p : ℝ) = z ∧ p ∣ a)
    with hBnd
  have hsB : sifted N Y n 1 z = Bs.card := by rw [hBs]; rfl
  have hsBZ : sifted N Y n 1 Z = BZs.card := by rw [hBZs]; rfl
  have hsBp : ∀ p : ℕ, sifted N Y n p z = (Bp p).card := fun p => by rw [hBp]; rfl
  have hsBpq : ∀ p q : ℕ, sifted N Y n (p * q) q = (Bpq p q).card := fun p q => by rw [hBpq]; rfl
  have hsubZ : BZs ⊆ Bs := by
    intro a ha
    rw [hBZs] at ha
    obtain ⟨ha1, han, -, hprime, hlow, hupp, hlev⟩ := mem_sieve ha
    rw [hBs]
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨ha1, han⟩, one_dvd a, hprime, hlow, hupp,
      fun p hp hpz hpn => hlev p hp (lt_of_lt_of_le hpz hzZ) hpn⟩
  have hcover : Bs \ BZs ⊆ Bnd ∪ PP.biUnion Gp := by
    intro a ha
    obtain ⟨haB, haZ⟩ := mem_sdiff.mp ha
    have haB' := haB
    rw [hBs] at haB'
    obtain ⟨ha1, han, -, hprime, hlow, hupp, hlevz⟩ := mem_sieve haB'
    have hane : 0 < a := by omega
    have hex : ∃ p : ℕ, p.Prime ∧ (p : ℝ) < Z ∧ ¬ p ∣ n ∧ p ∣ a := by
      by_contra hcon
      apply haZ
      rw [hBZs]
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨ha1, han⟩, one_dvd a, hprime, hlow, hupp,
        fun p hp hpZ hpn hpa => hcon ⟨p, hp, hpZ, hpn, hpa⟩⟩
    set m : ℕ := Nat.find hex with hmdef
    have hmspec : m.Prime ∧ (m : ℝ) < Z ∧ ¬ m ∣ n ∧ m ∣ a := Nat.find_spec hex
    have hmz : z ≤ (m : ℝ) := by
      by_contra h
      exact hlevz m hmspec.1 (not_le.mp h) hmspec.2.2.1 hmspec.2.2.2
    have hma : m ≤ a := Nat.le_of_dvd hane hmspec.2.2.2
    rcases lt_or_eq_of_le hmz with hlt | heq
    · have hmPP : m ∈ PP := by
        rw [hPP]
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), hmspec.1, hlt,
          le_of_lt hmspec.2.1⟩
      refine mem_union_right _ (mem_biUnion.mpr ⟨m, hmPP, ?_⟩)
      rw [hGp]
      refine mem_filter.mpr ⟨?_, ?_⟩
      · rw [hBp]
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨ha1, han⟩, hmspec.2.2.2, hprime, hlow, hupp,
          hlevz⟩
      · intro r hr hzr hrm hra
        have hrZ : (r : ℝ) < Z := lt_trans hrm hmspec.2.1
        have hrn : ¬ r ∣ n := prime_not_dvd_n hNY hr (le_of_lt hrZ) haB' hra
        have hrlt : r < m := by exact_mod_cast hrm
        have hle : m ≤ r := Nat.find_min' hex ⟨hr, hrZ, hrn, hra⟩
        omega
    · refine mem_union_left _ ?_
      rw [hBnd]
      exact mem_filter.mpr ⟨haB, m, hmspec.1, heq.symm, hmspec.2.2.2⟩
  have hcardsplit : Bs.card = BZs.card + (Bs \ BZs).card := by
    have h := Finset.card_sdiff_add_card_eq_card hsubZ
    omega
  have hcovercard : (Bs \ BZs).card ≤ Bnd.card + ∑ p ∈ PP, (Gp p).card :=
    (card_le_card hcover).trans
      ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have hpartnat : Bs.card ≤ BZs.card + Bnd.card + ∑ p ∈ PP, (Gp p).card := by omega
  have hpart : (Bs.card : ℝ) ≤
      (BZs.card : ℝ) + (Bnd.card : ℝ) + ∑ p ∈ PP, ((Gp p).card : ℝ) := by
    calc (Bs.card : ℝ) ≤ ((BZs.card + Bnd.card + ∑ p ∈ PP, (Gp p).card : ℕ) : ℝ) := by
          exact_mod_cast hpartnat
      _ = (BZs.card : ℝ) + (Bnd.card : ℝ) + ∑ p ∈ PP, ((Gp p).card : ℝ) := by
          push_cast; ring
  have hper : ∀ p ∈ PP, ∑ q ∈ QQ p, ((Bpq p q).card : ℝ) ≤
      (((Bp p) \ (Gp p)).card : ℝ) := by
    intro p hp
    have hp' := hp
    rw [hPP] at hp'
    obtain ⟨-, hpP, hpz, hpZ⟩ := mem_filter.mp hp'
    have hrow : ∑ q ∈ QQ p, (Bpq p q).card ≤ ((Bp p) \ (Gp p)).card := by
      apply sum_card_le_card_of_subset (QQ p) (fun q => Bpq p q) ((Bp p) \ (Gp p))
      · intro q hq a haq
        have hq' := hq
        rw [hQQ] at hq'
        obtain ⟨-, hqP, hqz, hqmin⟩ := mem_filter.mp hq'
        have hqp : (q : ℝ) < (p : ℝ) := lt_of_lt_of_le hqmin (min_le_left _ _)
        have haq' := haq
        rw [hBpq] at haq'
        have haBp : a ∈ Bp p := by
          rw [hBp]
          exact sieve_mem_mono (d₁ := p * q) (d₂ := p) (z₁ := q) (z₂ := z)
            (dvd_mul_right p q) (le_of_lt hqz) haq'
        refine mem_sdiff.mpr ⟨haBp, ?_⟩
        intro haG
        rw [hGp] at haG
        exact (mem_filter.mp haG).2 q hqP (le_of_lt hqz) hqp
          (dvd_trans (dvd_mul_left q p) (mem_sieve haq').2.2.1)
      · intro x hx y hy hxy
        rw [Finset.disjoint_left]
        intro a hax hay
        apply hxy
        have hx' := hx
        rw [hQQ] at hx'
        obtain ⟨-, hxP, hxz, hxmin⟩ := mem_filter.mp hx'
        have hy' := hy
        rw [hQQ] at hy'
        obtain ⟨-, hyP, hyz, hymin⟩ := mem_filter.mp hy'
        have hxZ : (x : ℝ) ≤ Z := le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hxmin
          (min_le_left _ _)) hpZ)
        have hyZ : (y : ℝ) ≤ Z := le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hymin
          (min_le_left _ _)) hpZ)
        have hax' := hax
        rw [hBpq] at hax'
        have hay' := hay
        rw [hBpq] at hay'
        exact pair_least_unique hNY hxP hxZ hyP hyZ hax' hay'
    have hrowR : ((∑ q ∈ QQ p, (Bpq p q).card : ℕ) : ℝ) ≤
        (((Bp p) \ (Gp p)).card : ℝ) := by exact_mod_cast hrow
    calc ∑ q ∈ QQ p, ((Bpq p q).card : ℝ) = ((∑ q ∈ QQ p, (Bpq p q).card : ℕ) : ℝ) := by
          push_cast; ring
      _ ≤ _ := hrowR
  have hbnd : (Bnd.card : ℝ) ≤ 2 * Y / z := by
    by_cases hexz : ∃ p : ℕ, p.Prime ∧ (p : ℝ) = z
    · obtain ⟨p₀, hp₀P, hp₀z⟩ := hexz
      have hS : ∀ a ∈ Bnd, 0 < a ∧ (a : ℝ) ≤ 2 * Y ∧ p₀ ∣ a := by
        intro a ha
        rw [hBnd] at ha
        obtain ⟨haB, hwit⟩ := mem_filter.mp ha
        obtain ⟨p, hpP, hpz, hpa⟩ := hwit
        have hpe : p = p₀ := by
          have hc : (p : ℝ) = (p₀ : ℝ) := by rw [hpz, hp₀z]
          exact_mod_cast hc
        rw [hpe] at hpa
        have haB' := haB
        rw [hBs] at haB'
        obtain ⟨ha1, -, -, -, -, -, -⟩ := mem_sieve haB'
        exact ⟨by omega, sifted_le_two_mul hnN haB', hpa⟩
      have h1 := card_multiples_le Bnd p₀ (2 * Y) hp₀P.pos (by positivity) hS
      rw [hp₀z] at h1
      exact h1
    · have hempty : Bnd = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro a ha
        rw [hBnd] at ha
        obtain ⟨-, ⟨p, hpP, hpz, -⟩⟩ := mem_filter.mp ha
        exact hexz ⟨p, hpP, hpz⟩
      rw [hempty]
      simp only [card_empty, Nat.cast_zero]
      positivity
  have hspl : ∀ p ∈ PP, (Bp p).card = (Gp p).card + ((Bp p) \ (Gp p)).card := by
    intro p _
    have hsubG : Gp p ⊆ Bp p := by rw [hGp]; exact filter_subset _ _
    have h := Finset.card_sdiff_add_card_eq_card hsubG
    omega
  have hsumsplit : ∑ p ∈ PP, ((Bp p).card : ℝ) =
      ∑ p ∈ PP, ((Gp p).card : ℝ) + ∑ p ∈ PP, (((Bp p) \ (Gp p)).card : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [hspl p hp]
    push_cast
    ring
  have hsumper : ∑ p ∈ PP, (∑ q ∈ QQ p, ((Bpq p q).card : ℝ)) ≤
      ∑ p ∈ PP, (((Bp p) \ (Gp p)).card : ℝ) := Finset.sum_le_sum hper
  have hinit : initial N Y n = (Bs.card : ℝ) := by rw [initial, ← hzdef, hsB]
  have hSZc : (sifted N Y n 1 Z : ℝ) = (BZs.card : ℝ) := by rw [hsBZ]
  have hsubc : subtraction N Y n = ∑ p ∈ PP, ((Bp p).card : ℝ) := by
    rw [subtraction, ← hzdef, ← hZdef, ← hPP]
    simp only [hsBp]
  have hQQ' : ∀ p : ℕ, QQ p = (range (n + 1)).filter
      (fun q : ℕ => q.Prime ∧ z < (q : ℝ) ∧
        (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))) := fun p => by rw [hQQ]
  have hrecc : recovery N Y n = ∑ p ∈ PP, ∑ q ∈ QQ p, ((Bpq p q).card : ℝ) := by
    rw [recovery, ← hzdef, ← hZdef, ← hPP]
    simp only [← hQQ', hsBpq]
  have henv : 2 * Y / z ≤ errorEnvelope Y := by
    rw [errorEnvelope, hzdef]
    have h := Real.sqrt_nonneg (2 * Y)
    linarith
  rw [hinit, hsubc, hrecc, hSZc]
  linarith [hpart, hsumsplit, hsumper, hbnd, henv]

/-- LEAF. Page 263 display 47 with explicit endpoint correction.
Only the finite Buchstab comparison is asserted. This statement has no
singular scale, no positivity claim and no asymptotic error absorption. -/
theorem buchstab_lower :
    ∃ K : ℝ, 0 < K ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ n ∈ window N ε,
        initial N (localization N ε) n - subtraction N (localization N ε) n +
          recovery N (localization N ε) n ≤
          (sifted N (localization N ε) n 1 (Real.sqrt (2 * localization N ε)) : ℝ) +
            K * errorEnvelope (localization N ε) := by
  refine ⟨1, one_pos, 1 / 100, by norm_num, ?_⟩
  intro ε hε he
  refine ⟨64, ?_⟩
  intro N hN n hn
  obtain ⟨hY, hsmall, hA⟩ := localization_domain hε he hN
  obtain ⟨hnI, -⟩ := mem_filter.mp hn
  obtain ⟨-, hnupper⟩ := mem_Ioc.mp hnI
  have hnN : (n : ℝ) ≤ N + localization N ε := by
    have hfloor : (⌊N + windowLength N ε⌋₊ : ℝ) ≤ N + windowLength N ε := by
      apply Nat.floor_le
      have h0 : (0 : ℝ) ≤ N := by linarith
      have hr := Real.rpow_nonneg h0 (7 / 108 + 12 * ε)
      unfold windowLength
      linarith
    have hn' : (n : ℝ) ≤ (⌊N + windowLength N ε⌋₊ : ℝ) := by exact_mod_cast hnupper
    linarith
  simpa only [one_mul] using buchstab_ineq hY hsmall hnN


/-- Pages 263 and 286: the exact sealed bridge follows from finite Buchstab.
CONDITIONAL ON buchstab_lower. Positivity, extraction and absorption are clean. -/
theorem representation_bridge_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ n ∈ window N ε,
      0 < scale N (localization N ε) n ∧
      initial N (localization N ε) n - subtraction N (localization N ε) n +
        recovery N (localization N ε) n - 0.005 * scale N (localization N ε) n ≤
        (representations N (localization N ε) n : ℝ) := by
  obtain ⟨K, hK, e, he, hbuch⟩ := buchstab_lower
  obtain ⟨Na, ha⟩ := error_absorption (K + 1) (by linarith)
  refine ⟨min e (1 / 100), lt_min he (by norm_num), ?_⟩
  intro ε hε heps
  obtain ⟨Nb, hb⟩ := hbuch ε hε (heps.trans_le (min_le_left _ _))
  refine ⟨max (max Na Nb) 64, ?_⟩
  intro N hN n hn
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN64 : 64 ≤ N := (le_max_right _ _).trans hN
  have he100 : ε < 1 / 100 := heps.trans_le (min_le_right _ _)
  obtain ⟨hY, hsmall, hA⟩ := localization_domain hε he100 hN64
  obtain ⟨hnI, hneven⟩ := mem_filter.mp hn
  have hnupper : (n : ℝ) ≤ N + localization N ε := by
    have hnfloor : (n : ℝ) ≤ ⌊N + windowLength N ε⌋₊ := by
      exact_mod_cast (mem_Ioc.mp hnI).2
    have hfloor : (⌊N + windowLength N ε⌋₊ : ℝ) ≤ N + windowLength N ε :=
      Nat.floor_le (by have : 0 ≤ windowLength N ε := Real.rpow_nonneg (by linarith) _; linarith)
    linarith
  obtain ⟨hs, herr⟩ := ha ε N hε (by linarith) hNa n hneven
  have hprime := prime_extraction N (localization N ε) n hnupper hsmall
  have hprimeR : (sifted N (localization N ε) n 1 (Real.sqrt (2 * localization N ε)) : ℝ) ≤
      representations N (localization N ε) n + 1 := by exact_mod_cast hprime
  have henv : 1 ≤ errorEnvelope (localization N ε) := by
    unfold errorEnvelope
    have hsqrt := Real.sqrt_nonneg (2 * localization N ε)
    have hdiv : 0 ≤ 2 * localization N ε / (localization N ε) ^ (16 / 135 : ℝ) := by positivity
    linarith
  have hb' := hb N hNb n hn
  exact ⟨hs, by nlinarith⟩

#print axioms summable_primeLoss
#print axioms tail_factor_pos
#print axioms tailProduct_pos
#print axioms tailProduct_le_singular
#print axioms scale_pos
#print axioms prime_extraction
#print axioms errorEnvelope_le
#print axioms error_absorption
#print axioms localization_domain
#print axioms buchstab_lower
#print axioms representation_bridge_from_parts
end
end LeanLab.Languasco2004.Decomp316d
