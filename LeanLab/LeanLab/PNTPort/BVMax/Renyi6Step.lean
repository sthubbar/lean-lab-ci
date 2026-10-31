import LeanLab.PNTPort.BVMax.Renyi7

/-!
# Rényi's theorem with `K = 6` by step weights, a second independent proof

Unit U-6801, CLOUD 20261021T0117Z-cloud55, idea I-5051. AI wrote the Lean code. Written in
parallel with U-6779, `Renyi6.lean`, which proves the same `K = 6` by Richert's logarithmic
weights; this file uses step weights `3/13, 2/13, 1/13` and imports only `Renyi7.lean`. All
names sit in the namespace `Step6`. Known mathematics,
a Kuhn type weighted sieve with weights that step down in `log q`, Richert type; Pan K = 4 and 5,
Chen K = 2 are far stronger.

The assembly of `Renyi7.lean` with three ranges of middle primes and one upper sieve level per
range. With `c = 22/625`, `z = N^c` and the boundaries `y₁ = N^{c 1.1^{13}}`, `y₂ = N^{c 1.1^{19}}`,
`y₃ = N^{c 1.1^{22}} = N^{0.28654}`:

* `Q₁ = (z, y₁]` gets weight `3/13` and its upper sieves sift up to `z`, level `N^{0.4830}`;
* `Q₂ = (y₁, y₂]` gets weight `2/13`, upper sieves up to `w₂ = N^{c/1.1³}`, level `N^{0.4868}`;
* `Q₃ = (y₂, y₃]` gets weight `1/13`, upper sieves up to `w₃ = N^{c/1.1⁷}`, level `N^{0.4720}`.

`bad6`: an element with `Ω ≥ 7`, all prime factors above `z` and no square of a middle prime has
`3 d₁ + 2 d₂ + d₃ ≥ 13` middle prime factors counted with these weights, because
`352 d₁ + 1215 d₂ + 2152 d₃ + 2865 (Ω - d) ≤ 10000` has no other solution. The ratios
`V_{w_i}/V_z` are at most `exp(0.300004) ≤ 1.35` and `exp(0.7000085) ≤ 2.014` by
`prod_one_sub_ge_exp` and `xDen_geom`. The subtracted part is at most
`(3 · 1.6114 + 2 · 1.0041 + 0.749)/13 < 0.584` of `X V_z` against `0.6168`; margin `0.0328`.
Numerics in `numerics/renyi6_check.py`.

Binary Goldbach is `Ω(m) = 1` and stays OPEN.
-/

namespace LeanLab.PNTPort.BVMax.Step6

open Finset LeanLab.PNTSieve.Bonferroni LeanLab.PNTPort.BVMax

/-- **Splitting off the middle primes, product form.** -/
lemma omega_split_prod (a : ℕ) (ha : a ≠ 0) (D : Finset ℕ) (hD : ∀ q ∈ D, q.Prime ∧ q ∣ a)
    (hsq : ∀ q ∈ D, ¬ q ^ 2 ∣ a) (Y : ℕ) (hsmall : ∀ r, r.Prime → r ∣ a → r ≤ Y → r ∈ D) :
    D.card ≤ ArithmeticFunction.cardFactors a ∧
    (∏ q ∈ D, q) * (Y + 1) ^ (ArithmeticFunction.cardFactors a - D.card) ≤ a := by
  classical
  have hgd : (∏ q ∈ D, q) ∣ a :=
    Finset.prod_primes_dvd a (fun q hq => (hD q hq).1.prime) (fun q hq => (hD q hq).2)
  obtain ⟨h, hh⟩ := hgd
  set g := ∏ q ∈ D, q with hg
  have hg0 : g ≠ 0 := by rw [hh] at ha; exact left_ne_zero_of_mul ha
  have hh0 : h ≠ 0 := by rw [hh] at ha; exact right_ne_zero_of_mul ha
  have hΩ : ArithmeticFunction.cardFactors a = D.card + ArithmeticFunction.cardFactors h := by
    rw [hh, ArithmeticFunction.cardFactors_mul hg0 hh0, hg,
      cardFactors_prod_primes D (fun q hq => (hD q hq).1)]
  have hbig : ∀ r ∈ h.primeFactorsList, Y + 1 ≤ r := by
    intro r hr
    have hrp := Nat.prime_of_mem_primeFactorsList hr
    have hrd := Nat.dvd_of_mem_primeFactorsList hr
    by_contra hlt
    push Not at hlt
    have hra : r ∣ a := by rw [hh]; exact dvd_mul_of_dvd_right hrd g
    have hrD := hsmall r hrp hra (by omega)
    have hrg : r ∣ g := Finset.dvd_prod_of_mem _ hrD
    exact hsq r hrD (by rw [hh, pow_two]; exact mul_dvd_mul hrg hrd)
  have h1 := pow_bigOmega_le h (Y + 1) hh0 hbig
  rw [hΩ, Nat.add_sub_cancel_left, hh]
  exact ⟨Nat.le_add_right _ _, Nat.mul_le_mul le_rfl h1⟩

/-- **The weight condition for `K = 6`**: weights `3, 2, 1` on the three ranges, total `≥ 13`. -/
lemma bad6 (n N z y1 y2 y3 : ℕ) (hn : n ≠ 0) (hnN : n ≤ N) (hy12 : y1 ≤ y2)
    (D1 D2 D3 : Finset ℕ)
    (h1 : ∀ q ∈ D1, q.Prime ∧ q ∣ n ∧ z < q ∧ q ≤ y1)
    (h2 : ∀ q ∈ D2, q.Prime ∧ q ∣ n ∧ y1 < q ∧ q ≤ y2)
    (h3 : ∀ q ∈ D3, q.Prime ∧ q ∣ n ∧ y2 < q ∧ q ≤ y3)
    (hsq : ∀ q ∈ D1 ∪ D2 ∪ D3, ¬ q ^ 2 ∣ n)
    (hsmall : ∀ r, r.Prime → r ∣ n → r ≤ y3 → r ∈ D1 ∪ D2 ∪ D3)
    (hℓ : 0 < Real.log N)
    (hl1 : 352 / 10000 * Real.log N ≤ Real.log ((z : ℝ) + 1))
    (hl2 : 1215 / 10000 * Real.log N ≤ Real.log ((y1 : ℝ) + 1))
    (hl3 : 2152 / 10000 * Real.log N ≤ Real.log ((y2 : ℝ) + 1))
    (hl4 : 2865 / 10000 * Real.log N ≤ Real.log ((y3 : ℝ) + 1))
    (hΩ : 7 ≤ ArithmeticFunction.cardFactors n) :
    13 ≤ 3 * D1.card + 2 * D2.card + D3.card := by
  classical
  have hd12 : Disjoint D1 D2 := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    have := (h1 q hq1).2.2.2
    have := (h2 q hq2).2.2.1
    omega
  have hd123 : Disjoint (D1 ∪ D2) D3 := by
    rw [Finset.disjoint_left]
    intro q hq hq3
    have := (h3 q hq3).2.2.1
    rcases mem_union.mp hq with hq | hq
    · have := (h1 q hq).2.2.2; omega
    · have := (h2 q hq).2.2.2; omega
  obtain ⟨hcard, hpow⟩ := omega_split_prod n hn (D1 ∪ D2 ∪ D3) (fun q hq => by
      rcases mem_union.mp hq with hq | hq
      · rcases mem_union.mp hq with hq | hq
        · exact ⟨(h1 q hq).1, (h1 q hq).2.1⟩
        · exact ⟨(h2 q hq).1, (h2 q hq).2.1⟩
      · exact ⟨(h3 q hq).1, (h3 q hq).2.1⟩) hsq y3 hsmall
  rw [card_union_of_disjoint hd123, card_union_of_disjoint hd12] at hcard hpow
  rw [prod_union hd123, prod_union hd12] at hpow
  have p1 : (z + 1) ^ D1.card ≤ ∏ q ∈ D1, q :=
    Finset.pow_card_le_prod D1 (fun q => q) (z + 1) (fun q hq => (h1 q hq).2.2.1)
  have p2 : (y1 + 1) ^ D2.card ≤ ∏ q ∈ D2, q :=
    Finset.pow_card_le_prod D2 (fun q => q) (y1 + 1) (fun q hq => (h2 q hq).2.2.1)
  have p3 : (y2 + 1) ^ D3.card ≤ ∏ q ∈ D3, q :=
    Finset.pow_card_le_prod D3 (fun q => q) (y2 + 1) (fun q hq => (h3 q hq).2.2.1)
  set d1 := D1.card with hd1
  set d2 := D2.card with hd2
  set d3 := D3.card with hd3
  set Ωn := ArithmeticFunction.cardFactors n with hΩn
  have hN : (z + 1) ^ d1 * (y1 + 1) ^ d2 * (y2 + 1) ^ d3 * (y3 + 1) ^ (Ωn - (d1 + d2 + d3)) ≤ N :=
    le_trans (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul p1 p2) p3) le_rfl) (hpow.trans hnN)
  have hNr : ((z : ℝ) + 1) ^ d1 * ((y1 : ℝ) + 1) ^ d2 * ((y2 : ℝ) + 1) ^ d3 *
      ((y3 : ℝ) + 1) ^ (Ωn - (d1 + d2 + d3)) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_le_log (by positivity) hNr
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow, Nat.cast_sub hcard] at hlog
  push_cast at hlog
  have hcr : ((d1 : ℝ) + d2 + d3) ≤ Ωn := by exact_mod_cast hcard
  have e1 : (d1 : ℝ) * (352 / 10000 * Real.log N) ≤ d1 * Real.log ((z : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hl1 (Nat.cast_nonneg _)
  have e2 : (d2 : ℝ) * (1215 / 10000 * Real.log N) ≤ d2 * Real.log ((y1 : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg _)
  have e3 : (d3 : ℝ) * (2152 / 10000 * Real.log N) ≤ d3 * Real.log ((y2 : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hl3 (Nat.cast_nonneg _)
  have e4 : ((Ωn : ℝ) - (d1 + d2 + d3)) * (2865 / 10000 * Real.log N) ≤
      ((Ωn : ℝ) - (d1 + d2 + d3)) * Real.log ((y3 : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hl4 (by linarith)
  have key : (((352 * d1 + 1215 * d2 + 2152 * d3 + 2865 * (Ωn - (d1 + d2 + d3)) : ℕ) : ℝ)) *
      Real.log N ≤ 10000 * Real.log N := by
    push_cast [Nat.cast_sub hcard]
    linarith
  have key2 := le_of_mul_le_mul_right key hℓ
  have key3 : 352 * d1 + 1215 * d2 + 2152 * d3 + 2865 * (Ωn - (d1 + d2 + d3)) ≤ 10000 := by
    exact_mod_cast key2
  by_contra hlt
  push Not at hlt
  omega

/-- The Mertens product ratio through `prod_one_sub_ge_exp`. -/
lemma prod_ratio (Ω Ω' : Finset ℕ) (h : Ω' ⊆ Ω) (s : ℝ)
    (hs : ∑ p ∈ Ω \ Ω', xDen p ≤ s) (hbig : ∀ p ∈ Ω \ Ω', (10000000 : ℝ) ≤ p) :
    ∏ p ∈ Ω', (1 - xDen p) ≤ Real.exp (s + 2 * s / 1000000) * ∏ p ∈ Ω, (1 - xDen p) := by
  have hx : ∀ p ∈ Ω \ Ω', xDen p ≤ 1 / 1000000 := by
    intro p hp
    have hp7 := hbig p hp
    have h3 : 3 ≤ p := by
      have : (3 : ℝ) ≤ p := by linarith
      exact_mod_cast this
    simp only [xDen, if_pos h3]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h0 : ∀ p ∈ Ω \ Ω', 0 ≤ xDen p := fun p _ => xDen_nonneg p
  have h12 : ∀ p ∈ Ω \ Ω', xDen p ≤ 1 / 2 := fun p hp => (hx p hp).trans (by norm_num)
  have hE := LeanLab.PNTSieve.Mertens.prod_one_sub_ge_exp (Ω \ Ω') xDen h0 h12
  have hsq0 : ∑ p ∈ Ω \ Ω', xDen p ^ 2 ≤ ∑ p ∈ Ω \ Ω', xDen p / 1000000 :=
    sum_le_sum (fun p hp => by
      have a1 := hx p hp
      have a2 := h0 p hp
      rw [pow_two]
      nlinarith)
  rw [← sum_div] at hsq0
  have hmono : Real.exp (-(s + 2 * s / 1000000)) ≤
      Real.exp (-(∑ p ∈ Ω \ Ω', xDen p + 2 * ∑ p ∈ Ω \ Ω', xDen p ^ 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have e : (∏ p ∈ Ω \ Ω', (1 - xDen p)) * ∏ p ∈ Ω', (1 - xDen p) = ∏ p ∈ Ω, (1 - xDen p) :=
    prod_sdiff h
  have hW0 : 0 ≤ ∏ p ∈ Ω', (1 - xDen p) := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have h1 : Real.exp (-(s + 2 * s / 1000000)) * ∏ p ∈ Ω', (1 - xDen p) ≤
      ∏ p ∈ Ω, (1 - xDen p) := by
    rw [← e]; exact mul_le_mul_of_nonneg_right (hmono.trans hE) hW0
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (s + 2 * s / 1000000)).le
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h2
  exact h2

lemma exp_le_135 : Real.exp (300004 / 1000000) ≤ 135 / 100 := by
  have h := Real.exp_bound' (x := 300004 / 1000000) (by norm_num) (by norm_num) (n := 4)
    (by norm_num)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma exp_le_2014 : Real.exp (7000085 / 10000000) ≤ 2014 / 1000 := by
  have h := Real.exp_bound' (x := 7000085 / 10000000) (by norm_num) (by norm_num) (n := 7)
    (by norm_num)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- Swapping the order of a divisor count. -/
lemma swap_count (Sz Q : Finset ℕ) :
    ∑ a ∈ Sz, ((Q.filter (fun q => q ∣ a)).card : ℝ) =
      ∑ q ∈ Q, ((Sz.filter (fun a => q ∣ a)).card : ℝ) := by
  classical
  rw [show (∑ a ∈ Sz, ((Q.filter (fun q => q ∣ a)).card : ℝ)) =
      ∑ a ∈ Sz, ∑ q ∈ Q, (if q ∣ a then (1 : ℝ) else 0) from
    sum_congr rfl (fun a _ => (sum_boole _ _).symm)]
  rw [sum_comm]
  exact sum_congr rfl (fun q _ => sum_boole _ _)

/-- The elements of the sifted set divisible by `q` are sifted from `A_q` by fewer primes. -/
lemma filter_le_sifted (A Ω Ω' Q : Finset ℕ) (h : Ω' ⊆ Ω) :
    ∑ q ∈ Q, (((A.filter (fun a => ∀ p ∈ Ω, ¬ p ∣ a)).filter (fun a => q ∣ a)).card : ℝ) ≤
      ∑ q ∈ Q, (sifted (A.filter (fun a => q ∣ a)) Ω' : ℝ) := by
  refine sum_le_sum (fun q _ => ?_)
  simp only [sifted]
  push_cast
  exact_mod_cast card_le_card (fun a ha => by
    simp only [mem_filter] at ha ⊢
    exact ⟨⟨ha.1.1, ha.2⟩, fun p hp => ha.1.2 p (h hp)⟩)

/-- Main term bookkeeping for one range. -/
lemma range_main (X V W ρ S R s κ : ℝ) (hX : 0 ≤ X) (hV0 : 0 ≤ V) (_hW0 : 0 ≤ W)
    (hWV : W ≤ R * V) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1916 / 10000) (hS0 : 0 ≤ S) (hS : S ≤ s)
    (hR0 : 0 ≤ R) (hκ : R * (12395 / 10000) * s ≤ κ) :
    X * W * (1 + 5 / 4 * ρ) * S ≤ X * V * κ := by
  have hs0 : 0 ≤ s := hS0.trans hS
  have a : (1 + 5 / 4 * ρ) * S ≤ 12395 / 10000 * s := mul_le_mul (by linarith) hS hS0 (by norm_num)
  have b : W * ((1 + 5 / 4 * ρ) * S) ≤ (R * V) * (12395 / 10000 * s) :=
    mul_le_mul hWV a (by positivity) (by positivity)
  have c : (R * V) * (12395 / 10000 * s) ≤ V * κ := by
    have := mul_le_mul_of_nonneg_left hκ hV0
    calc (R * V) * (12395 / 10000 * s) = V * (R * (12395 / 10000) * s) := by ring
      _ ≤ V * κ := this
  have d := mul_le_mul_of_nonneg_left (b.trans c) hX
  calc X * W * (1 + 5 / 4 * ρ) * S = X * (W * ((1 + 5 / 4 * ρ) * S)) := by ring
    _ ≤ X * (V * κ) := d
    _ = X * V * κ := by ring

set_option maxHeartbeats 1000000 in
/-- **The upper sieves of one range of middle primes**, all with the same block pack. -/
lemma range_upper {B K : ℝ} (N : ℕ)
    (hR : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p) → ∀ F : Finset (Finset ℕ),
      F ⊆ P.powerset → (∀ T ∈ F, ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
      ∑ T ∈ F, |rem (goldbachSeq N) xDen (liD ((N - 1 : ℕ) : ℝ)) T| ≤
        K * N / Real.log N ^ (5 : ℝ))
    (hE2 : Real.exp (49 / 100 * Real.log N) ≤ Real.sqrt N / Real.log N ^ B)
    (Bs : List Block) (hG : Good Bs) (M E : ℝ)
    (hmem : ∀ p ∈ univB Bs, (p : ℝ) ≤ Real.exp M ∧ p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p)
    (hlev : (lev Bs : ℝ) ≤ Real.exp (154 / 15 * M)) (hρ : rhoSum xDen Bs ≤ 1916 / 10000)
    (hME : E + 154 / 15 * M ≤ 49 / 100 * Real.log N)
    (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, Real.exp M < q ∧ (q : ℝ) ≤ Real.exp E ∧ q.Prime ∧ ¬ q ∣ N ∧ 3 ≤ q) :
    ∑ q ∈ Q, (sifted ((goldbachSeq N).filter (fun a => q ∣ a)) (univB Bs) : ℝ) ≤
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Bs) *
        ∑ q ∈ Q, xDen q + K * N / Real.log N ^ (5 : ℝ) := by
  classical
  set A := goldbachSeq N with hAdef
  set X := liD ((N - 1 : ℕ) : ℝ) with hXdef
  have hX : 0 ≤ X := by
    rw [hXdef]; unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  set Ω := univB Bs with hΩ
  have hρ5 : rhoSum xDen Bs ≤ 1 / 5 := hρ.trans (by norm_num)
  have hlt : ∀ q ∈ Q, ∀ p ∈ Ω, p < q := fun q hq p hp => by
    have h1 := (hmem p hp).1
    have h2 := (hQ q hq).1
    exact_mod_cast (lt_of_le_of_lt h1 h2)
  set F' := Ω.powerset.filter (fun S => cU Bs S ≠ 0) with hF'
  have hup : ∀ q ∈ Q, (sifted (A.filter (fun a => q ∣ a)) Ω : ℝ) ≤
      X * xDen q * (∏ p ∈ Ω, (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Bs) +
        ∑ S ∈ F', |rem A xDen X (insert q S)| := by
    intro q hq
    have hqp := (hQ q hq).2.2.1
    have h := blocks_upper_rel5 (A.filter (fun a => q ∣ a)) Bs hG xDen xDen_nonneg xDen_lt_one
      (X * xDen q) (mul_nonneg hX (xDen_nonneg q)) hρ5
    refine h.trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl (fun S hS => ?_)
    rw [hF', mem_filter, mem_powerset] at hS
    rw [rem_filter_dvd A xDen X hqp S (fun p hp => (hmem p (hS.1 hp)).2.1)
      (fun hqS => by have := hlt q hq q (hS.1 hqS); omega)]
  set G := (Q ×ˢ F').image (fun qs => insert qs.1 qs.2) with hGdef
  have hinj : Set.InjOn (fun qs : ℕ × Finset ℕ => insert qs.1 qs.2) ↑(Q ×ˢ F') := by
    rintro ⟨q1, S1⟩ h1 ⟨q2, S2⟩ h2 he
    simp only [coe_product, Set.mem_prod, mem_coe] at h1 h2
    simp only at he
    have hS1 : S1 ⊆ Ω := mem_powerset.mp (mem_filter.mp h1.2).1
    have hS2 : S2 ⊆ Ω := mem_powerset.mp (mem_filter.mp h2.2).1
    have hn1 : q1 ∉ S1 := fun h => by have := hlt q1 h1.1 q1 (hS1 h); omega
    have hn2 : q2 ∉ S2 := fun h => by have := hlt q2 h2.1 q2 (hS2 h); omega
    have hq : q1 = q2 := by
      have m1 : q1 ∈ insert q2 S2 := by rw [← he]; exact mem_insert_self q1 S1
      have m2 : q2 ∈ insert q1 S1 := by rw [he]; exact mem_insert_self q2 S2
      rcases mem_insert.mp m1 with h | h
      · exact h
      · have a1 := hlt q2 h2.1 q1 (hS2 h)
        rcases mem_insert.mp m2 with h' | h'
        · omega
        · have a2 := hlt q1 h1.1 q2 (hS1 h'); omega
    subst hq
    have e1 := erase_insert hn1
    have e2 := erase_insert hn2
    rw [he] at e1
    rw [e1] at e2
    rw [Prod.mk.injEq]
    exact ⟨rfl, e2⟩
  have hGR : ∑ T ∈ G, |rem A xDen X T| ≤ K * N / Real.log N ^ (5 : ℝ) := by
    refine hR (Ω ∪ Q) (fun p hp => ?_) G ?_ ?_
    · rcases mem_union.mp hp with h | h
      · exact ⟨(hmem p h).2.1, (hmem p h).2.2.1, (hmem p h).2.2.2⟩
      · obtain ⟨-, -, h3, h4, h5⟩ := hQ p h
        exact ⟨h3, h4, h5⟩
    · intro T hT
      obtain ⟨⟨q, S⟩, hqS, rfl⟩ := mem_image.mp hT
      rw [mem_product] at hqS
      have hS : S ⊆ Ω := mem_powerset.mp (mem_filter.mp hqS.2).1
      rw [mem_powerset]
      intro p hp
      rcases mem_insert.mp hp with h | h
      · exact mem_union_right _ (h ▸ hqS.1)
      · exact mem_union_left _ (hS h)
    · intro T hT
      obtain ⟨⟨q, S⟩, hqS, rfl⟩ := mem_image.mp hT
      rw [mem_product] at hqS
      have hS : S ⊆ Ω := mem_powerset.mp (mem_filter.mp hqS.2).1
      have hcU : cU Bs S ≠ 0 := (mem_filter.mp hqS.2).2
      have hn : q ∉ S := fun h => by have := hlt q hqS.1 q (hS h); omega
      simp only
      rw [prod_insert hn]
      have hSl := support_prod Bs hG S hS (Or.inr hcU)
      apply Nat.le_floor
      push_cast
      have hqr : (q : ℝ) ≤ Real.exp E := (hQ q hqS.1).2.1
      have hSr : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ Real.exp (154 / 15 * M) :=
        le_trans (by exact_mod_cast hSl) hlev
      push_cast at hSr
      calc (q : ℝ) * ∏ p ∈ S, (p : ℝ) ≤ Real.exp E * Real.exp (154 / 15 * M) :=
            mul_le_mul hqr hSr (by positivity) (Real.exp_pos _).le
        _ = Real.exp (E + 154 / 15 * M) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (49 / 100 * Real.log N) := Real.exp_le_exp.mpr hME
        _ ≤ _ := hE2
  refine (sum_le_sum hup).trans ?_
  rw [sum_add_distrib]
  have e1 : ∑ q ∈ Q, X * xDen q * (∏ p ∈ Ω, (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Bs) =
      X * (∏ p ∈ Ω, (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Bs) * ∑ q ∈ Q, xDen q := by
    rw [mul_sum]; refine sum_congr rfl (fun q _ => by ring)
  have e2 : ∑ q ∈ Q, ∑ S ∈ F', |rem A xDen X (insert q S)| = ∑ T ∈ G, |rem A xDen X T| := by
    rw [hGdef, sum_image hinj, sum_product]
  rw [e1, e2]
  linarith

lemma big_aux6 (ℓ : ℝ) (h : (2 : ℝ) ^ 2100 ≤ ℓ) :
    (2 : ℝ) ^ 2006 ≤ 22 / 625 * ℓ ∧ (2 : ℝ) ^ 2006 ≤ 16 / 605 * ℓ ∧
      (2 : ℝ) ^ 2006 ≤ 32000 / 1771561 * ℓ ∧ (10 : ℝ) ^ 30 ≤ ℓ := by
  have e : (2 : ℝ) ^ 2100 = 2 ^ 94 * 2 ^ 2006 := by rw [← pow_add]
  rw [e] at h
  clear e
  have h94 : (64 : ℝ) ≤ 2 ^ 94 :=
    calc (64 : ℝ) ≤ 2 ^ 6 := by norm_num
      _ ≤ 2 ^ 94 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h20 : (10 : ℝ) ^ 30 ≤ 2 ^ 2006 :=
    calc (10 : ℝ) ^ 30 ≤ 2 ^ 100 := by norm_num
      _ ≤ 2 ^ 2006 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  generalize (2 : ℝ) ^ 2006 = A at *
  generalize (2 : ℝ) ^ 94 = C at *
  have hA : 0 ≤ A := le_trans (by norm_num) h20
  have hm := mul_le_mul_of_nonneg_right h94 hA
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Rényi with `K = 6`, deterministic core with the count**, weights `1 - (3 d₁ + 2 d₂ + d₃)/13`
over three ranges of middle primes, each range with its own upper sieve level. -/
theorem renyi6s_count {B K : ℝ} (N : ℕ)
    (hR : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p) → ∀ F : Finset (Finset ℕ),
      F ⊆ P.powerset → (∀ T ∈ F, ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
      ∑ T ∈ F, |rem (goldbachSeq N) xDen (liD ((N - 1 : ℕ) : ℝ)) T| ≤
        K * N / Real.log N ^ (5 : ℝ))
    (hE : Even N) (hℓ6 : (2 : ℝ) ^ 2100 ≤ Real.log N)
    (hE2 : Real.exp (49 / 100 * Real.log N) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : 100 * |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    Real.exp (-36) * N / (2 * Real.log N ^ 2) ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 6)).card : ℝ) := by
  classical
  set ℓ := Real.log N with hℓ
  obtain ⟨hLbig0, hL2big, hL3big, h10⟩ := big_aux6 ℓ hℓ6
  clear hℓ6
  obtain ⟨Bs, hG, hmem, hcov, hlev, hρ, h3k⟩ := block_pack N (22 / 625 * ℓ) hLbig0
  obtain ⟨Bs2, hG2, hmem2, hcov2, hlev2, hρ2, -⟩ := block_pack N (16 / 605 * ℓ) hL2big
  obtain ⟨Bs3, hG3, hmem3, hcov3, hlev3, hρ3, -⟩ := block_pack N (32000 / 1771561 * ℓ) hL3big
  clear hLbig0 hL2big hL3big
  have hℓpos : 0 < ℓ := by linarith
  have hN1 : (1 : ℝ) < N := by
    by_contra h; push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hexpℓ : Real.exp ℓ = N := Real.exp_log hNpos
  have hN38 : (38 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    linarith
  have h4 : 4 ≤ N := by exact_mod_cast (show (4 : ℝ) ≤ N by linarith)
  -- the limits
  set L := 22 / 625 * ℓ with hL
  obtain ⟨hz3, hzr, hz1, hlogz1, hlogz2, hlogz3⟩ := floor_exp_facts L (by linarith)
  obtain ⟨hy13, hy1r, hy11, -, -, hlogy13⟩ := floor_exp_facts
    (379749833583241 / 3125000000000000 * ℓ) (by linarith)
  obtain ⟨hy23, hy2r, hy21, -, -, hlogy23⟩ := floor_exp_facts
    (672749994932560009201 / 3125000000000000000000 * ℓ) (by linarith)
  obtain ⟨hy33, hy3r, hy31, -, -, hlogy33⟩ := floor_exp_facts
    (895430243255237372246531 / 3125000000000000000000000 * ℓ) (by linarith)
  set z := ⌊Real.exp L⌋₊ with hz
  set y1 := ⌊Real.exp (379749833583241 / 3125000000000000 * ℓ)⌋₊ with hy1
  set y2 := ⌊Real.exp (672749994932560009201 / 3125000000000000000000 * ℓ)⌋₊ with hy2
  set y3 := ⌊Real.exp (895430243255237372246531 / 3125000000000000000000000 * ℓ)⌋₊ with hy3
  have hzy1 : z ≤ y1 := Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hy12 : y1 ≤ y2 := Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hy23 : y2 ≤ y3 := Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  set Ω := univB Bs with hΩ
  set Ω2 := univB Bs2 with hΩ2
  set Ω3 := univB Bs3 with hΩ3
  have hsub2 : Ω2 ⊆ Ω := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem2 p hp
    exact hcov p h2 h3 h4 (h1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hsub3 : Ω3 ⊆ Ω := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem3 p hp
    exact hcov p h2 h3 h4 (h1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hΩz : ∀ p ∈ Ω, p ≤ z := fun p hp => Nat.le_floor (hmem p hp).1
  set Q1 := (Ioc z y1).filter (fun q => q.Prime ∧ ¬ q ∣ N) with hQ1
  set Q2 := (Ioc y1 y2).filter (fun q => q.Prime ∧ ¬ q ∣ N) with hQ2
  set Q3 := (Ioc y2 y3).filter (fun q => q.Prime ∧ ¬ q ∣ N) with hQ3
  set Qa := (Ioc z y3).filter (fun q => q.Prime ∧ ¬ q ∣ N) with hQa
  have hQmem : ∀ a b : ℕ, ∀ q ∈ (Ioc a b).filter (fun q => q.Prime ∧ ¬ q ∣ N),
      a < q ∧ q ≤ b ∧ q.Prime ∧ ¬ q ∣ N := by
    intro a b q hq
    rw [mem_filter, mem_Ioc] at hq
    exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
  -- the sequence
  set A := goldbachSeq N with hAdef
  set X := liD ((N - 1 : ℕ) : ℝ) with hXdef
  have hX : 0 ≤ X := by
    rw [hXdef]; unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  have hlevel : ∀ e : ℝ, e ≤ 49 / 100 * ℓ → ∀ n : ℕ, (n : ℝ) ≤ Real.exp e →
      n ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := fun e he n hn =>
    Nat.le_floor (hn.trans ((Real.exp_le_exp.mpr he).trans hE2))
  -- the lower sieve
  have hρ5 : rhoSum xDen Bs ≤ 1 / 5 := hρ.trans (by norm_num)
  have hlow := blocks_main_rel5 A Bs hG xDen xDen_nonneg xDen_lt_one X hX hρ5
  have hlowR := hR Ω (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.1, (hmem p hp).2.2.2⟩)
    (Ω.powerset.filter (fun S => cL Bs S ≠ 0)) (filter_subset _ _) (fun T hT => by
      rw [mem_filter, mem_powerset] at hT
      refine (support_prod Bs hG T hT.1 (Or.inl hT.2)).trans
        (hlevel (154 / 15 * L) (by linarith) _ hlev))
  -- the upper sieves of the three ranges
  have hU1 := range_upper N hR hE2 Bs hG L (379749833583241 / 3125000000000000 * ℓ) hmem hlev hρ
    (by linarith) Q1 (fun q hq => by
      obtain ⟨h1, h2, h3, h4⟩ := hQmem _ _ q hq
      have h1' : (z : ℝ) + 1 ≤ q := by exact_mod_cast h1
      have h2' : (q : ℝ) ≤ y1 := by exact_mod_cast h2
      exact ⟨by linarith, h2'.trans hy1r, h3, h4, by omega⟩)
  have hU2 := range_upper N hR hE2 Bs2 hG2 (16 / 605 * ℓ)
    (672749994932560009201 / 3125000000000000000000 * ℓ) hmem2 hlev2 hρ2
    (by linarith) Q2 (fun q hq => by
      obtain ⟨h1, h2, h3, h4⟩ := hQmem _ _ q hq
      have h1' : (y1 : ℝ) + 1 ≤ q := by exact_mod_cast h1
      have hm : Real.exp (16 / 605 * ℓ) ≤ Real.exp (379749833583241 / 3125000000000000 * ℓ) :=
        Real.exp_le_exp.mpr (by linarith)
      have h2' : (q : ℝ) ≤ y2 := by exact_mod_cast h2
      exact ⟨by linarith, h2'.trans hy2r, h3, h4, by omega⟩)
  have hU3 := range_upper N hR hE2 Bs3 hG3 (32000 / 1771561 * ℓ)
    (895430243255237372246531 / 3125000000000000000000000 * ℓ) hmem3 hlev3 hρ3
    (by linarith) Q3 (fun q hq => by
      obtain ⟨h1, h2, h3, h4⟩ := hQmem _ _ q hq
      have h1' : (y2 : ℝ) + 1 ≤ q := by exact_mod_cast h1
      have hm : Real.exp (32000 / 1771561 * ℓ) ≤
          Real.exp (672749994932560009201 / 3125000000000000000000 * ℓ) :=
        Real.exp_le_exp.mpr (by linarith)
      have h2' : (q : ℝ) ≤ y3 := by exact_mod_cast h2
      exact ⟨by linarith, h2'.trans hy3r, h3, h4, by omega⟩)
  -- the densities
  set V := ∏ p ∈ Ω, (1 - xDen p) with hVdef
  set V2 := ∏ p ∈ Ω2, (1 - xDen p) with hV2def
  set V3 := ∏ p ∈ Ω3, (1 - xDen p) with hV3def
  have hV0 : 0 ≤ V := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have hV20 : 0 ≤ V2 := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have hV30 : 0 ≤ V3 := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have hgap : ∀ (Ω' : Finset ℕ) (Bs' : List Block) (v : ℝ), Ω' = univB Bs' →
      (∀ p, p.Prime → ¬ p ∣ N → 3 ≤ p → (p : ℝ) ≤ Real.exp (v * ℓ) → p ∈ univB Bs') →
      ∀ p ∈ Ω \ Ω', Real.exp (v * ℓ) < p := by
    intro Ω' Bs' v e hc p hp
    rw [mem_sdiff] at hp
    obtain ⟨-, h2, h3, h4⟩ := hmem p hp.1
    by_contra hc'
    push Not at hc'
    exact hp.2 (e ▸ hc p h2 h3 h4 hc')
  have hs2 : ∑ p ∈ Ω \ Ω2, xDen p ≤ 300003 / 1000000 := by
    have h := xDen_geom ℓ (16 / 605) (11 / 10) (by norm_num) (by norm_num)
      (by norm_num) (by linarith) 3 (Ω \ Ω2) (fun p hp => by
        have hg := hgap Ω2 Bs2 (16 / 605) rfl hcov2 p hp
        rw [mem_sdiff] at hp
        obtain ⟨h1, h2, -, -⟩ := hmem p hp.1
        refine ⟨h2, (Nat.floor_lt (Real.exp_pos _).le).mpr hg, ?_⟩
        apply Nat.le_floor
        refine h1.trans (le_of_eq ?_)
        congr 1
        rw [hL]; ring)
    refine h.trans ?_
    norm_num
  have hs3 : ∑ p ∈ Ω \ Ω3, xDen p ≤ 700007 / 1000000 := by
    have h := xDen_geom ℓ (32000 / 1771561) (11 / 10) (by norm_num) (by norm_num)
      (by norm_num) (by linarith) 7 (Ω \ Ω3) (fun p hp => by
        have hg := hgap Ω3 Bs3 (32000 / 1771561) rfl hcov3 p hp
        rw [mem_sdiff] at hp
        obtain ⟨h1, h2, -, -⟩ := hmem p hp.1
        refine ⟨h2, (Nat.floor_lt (Real.exp_pos _).le).mpr hg, ?_⟩
        apply Nat.le_floor
        refine h1.trans (le_of_eq ?_)
        congr 1
        rw [hL]; ring)
    refine h.trans ?_
    norm_num
  have hbig2 : ∀ p ∈ Ω \ Ω2, (10000000 : ℝ) ≤ p := fun p hp => by
    have hg := hgap Ω2 Bs2 (16 / 605) rfl hcov2 p hp
    have := Real.add_one_le_exp (16 / 605 * ℓ)
    linarith
  have hbig3 : ∀ p ∈ Ω \ Ω3, (10000000 : ℝ) ≤ p := fun p hp => by
    have hg := hgap Ω3 Bs3 (32000 / 1771561) rfl hcov3 p hp
    have := Real.add_one_le_exp (32000 / 1771561 * ℓ)
    linarith
  have hr2 : V2 ≤ 135 / 100 * V := by
    have h := prod_ratio Ω Ω2 hsub2 _ hs2 hbig2
    have he : Real.exp (300003 / 1000000 + 2 * (300003 / 1000000) / 1000000) ≤ 135 / 100 :=
      (Real.exp_le_exp.mpr (by norm_num)).trans exp_le_135
    exact h.trans (mul_le_mul_of_nonneg_right he hV0)
  have hr3 : V3 ≤ 2014 / 1000 * V := by
    have h := prod_ratio Ω Ω3 hsub3 _ hs3 hbig3
    have he : Real.exp (700007 / 1000000 + 2 * (700007 / 1000000) / 1000000) ≤ 2014 / 1000 :=
      (Real.exp_le_exp.mpr (by norm_num)).trans exp_le_2014
    exact h.trans (mul_le_mul_of_nonneg_right he hV0)
  have hsQ1 : ∑ q ∈ Q1, xDen q ≤ 1300013 / 1000000 := by
    have hY : (22 / 625 : ℝ) * (11 / 10) ^ 13 = 379749833583241 / 3125000000000000 := by norm_num
    have h := xDen_geom ℓ (22 / 625) (11 / 10) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) 13 Q1 (fun q hq => by
        rw [hY]
        obtain ⟨h1, h2, h3, -⟩ := hQmem _ _ q hq
        exact ⟨h3, h1, h2⟩)
    refine h.trans ?_
    norm_num
  have hsQ2 : ∑ q ∈ Q2, xDen q ≤ 600006 / 1000000 := by
    have hY : (379749833583241 / 3125000000000000 : ℝ) * (11 / 10) ^ 6 =
        672749994932560009201 / 3125000000000000000000 := by norm_num
    have h := xDen_geom ℓ (379749833583241 / 3125000000000000) (11 / 10) (by norm_num)
      (by norm_num) (by norm_num) (by linarith) 6 Q2 (fun q hq => by
        rw [hY]
        obtain ⟨h1, h2, h3, -⟩ := hQmem _ _ q hq
        exact ⟨h3, h1, h2⟩)
    refine h.trans ?_
    norm_num
  have hsQ3 : ∑ q ∈ Q3, xDen q ≤ 300003 / 1000000 := by
    have hY : (672749994932560009201 / 3125000000000000000000 : ℝ) * (11 / 10) ^ 3 =
        895430243255237372246531 / 3125000000000000000000000 := by norm_num
    have h := xDen_geom ℓ (672749994932560009201 / 3125000000000000000000) (11 / 10)
      (by norm_num) (by norm_num) (by norm_num) (by linarith) 3 Q3 (fun q hq => by
        rw [hY]
        obtain ⟨h1, h2, h3, -⟩ := hQmem _ _ q hq
        exact ⟨h3, h1, h2⟩)
    refine h.trans ?_
    norm_num
  have hρ0 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one Bs
  have hρ20 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one Bs2
  have hρ30 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one Bs3
  have hm1 := range_main X V V (rhoSum xDen Bs) (∑ q ∈ Q1, xDen q) 1 (1300013 / 1000000)
    (16114 / 10000) hX hV0 hV0 (by linarith) hρ0 hρ (sum_nonneg (fun p _ => xDen_nonneg p))
    hsQ1 (by norm_num) (by norm_num)
  have hm2 := range_main X V V2 (rhoSum xDen Bs2) (∑ q ∈ Q2, xDen q) (135 / 100)
    (600006 / 1000000) (10041 / 10000) hX hV0 hV20 hr2 hρ20 hρ2
    (sum_nonneg (fun p _ => xDen_nonneg p)) hsQ2 (by norm_num) (by norm_num)
  have hm3 := range_main X V V3 (rhoSum xDen Bs3) (∑ q ∈ Q3, xDen q) (2014 / 1000)
    (300003 / 1000000) (7490 / 10000) hX hV0 hV30 hr3 hρ30 hρ3
    (sum_nonneg (fun p _ => xDen_nonneg p)) hsQ3 (by norm_num) (by norm_num)
  have hXV0 : 0 ≤ X * V := mul_nonneg hX hV0
  have hlowmain : X * V * (6168 / 10000) ≤ X * V * (1 - 2 * rhoSum xDen Bs) :=
    mul_le_mul_of_nonneg_left (by linarith) hXV0
  -- absolute size of X V
  have hV2 : Real.exp (-36) * 625 / (22 * ℓ) ≤ V := by
    have hV := LeanLab.PNTSieve.Mertens.prod_one_sub_inv_pred_ge z hz3 Ω
      (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.2, Nat.le_floor (hmem p hp).1⟩)
    have hV' : Real.exp (-36) / Real.log z ≤ V := by
      refine hV.trans (le_of_eq (prod_congr rfl (fun p hp => ?_)))
      simp only [xDen, if_pos (hmem p hp).2.2.2]
    refine le_trans ?_ hV'
    have hlz : 0 < Real.log z := by linarith
    rw [div_le_div_iff₀ (by positivity) hlz]
    have := Real.exp_pos (-36 : ℝ)
    have : Real.log z * 625 ≤ 22 * ℓ := by linarith
    nlinarith
  have hliD := liD_ge N (by omega)
  have hXV : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 625 / (22 * ℓ)) ≤ X * V :=
    mul_le_mul hliD hV2 (by positivity) hX
  have hXV2 : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 625 / (22 * ℓ)) =
      625 / 22 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) := by
    field_simp
  have hXV' : 625 / 22 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) ≤ X * V := hXV2 ▸ hXV
  -- errors
  have h5r : ℓ ^ (5 : ℝ) = ℓ ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h3r : ℓ ^ (3 : ℝ) = ℓ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hKN : K * N / ℓ ^ (5 : ℝ) ≤ |K| * N / ℓ ^ 5 := by
    rw [h5r]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) hNpos.le)
      (by positivity)
  have hK0 : 0 ≤ |K| * N / ℓ ^ 5 := by positivity
  have herr : ((3 : ℝ) ^ Bs.length + 1) * (|K| * N / ℓ ^ 5) ≤ |K| * N / ℓ ^ (3 : ℝ) := by
    rw [h3r]
    have h1 : (3 : ℝ) ^ Bs.length + 1 ≤ ℓ ^ 2 := by
      have : 4 * L ^ 2 + 1 ≤ ℓ ^ 2 := by rw [hL]; nlinarith
      linarith
    calc ((3 : ℝ) ^ Bs.length + 1) * (|K| * N / ℓ ^ 5) ≤ ℓ ^ 2 * (|K| * N / ℓ ^ 5) :=
          mul_le_mul_of_nonneg_right h1 hK0
      _ = |K| * N / ℓ ^ 3 := by field_simp
  have hlow3 : (3 : ℝ) ^ Bs.length *
      ∑ S ∈ Ω.powerset.filter (fun S => cL Bs S ≠ 0), |rem A xDen X S| ≤
      (3 : ℝ) ^ Bs.length * (|K| * N / ℓ ^ 5) :=
    mul_le_mul_of_nonneg_left (hlowR.trans hKN) (by positivity)
  -- the sifted set and the weight
  set Sz := A.filter (fun a => ∀ p ∈ Ω, ¬ p ∣ a) with hSz
  have hcardSz : (sifted A Ω : ℝ) = (Sz.card : ℝ) := by simp [sifted, hSz]
  have hT1 := filter_le_sifted A Ω Ω Q1 subset_rfl
  have hT2 := filter_le_sifted A Ω Ω2 Q2 hsub2
  have hT3 := filter_le_sifted A Ω Ω3 Q3 hsub3
  rw [← hSz] at hT1 hT2 hT3
  set SQ := A.filter (fun a => ∃ q ∈ Qa, q ^ 2 ∣ a) with hSQ
  set small := (range (y3 + 1)).image (fun p => N - p) with hsmall_def
  have hsmall : small.card ≤ y3 + 1 := card_image_le.trans (by simp)
  set Gd := ((range N).filter Nat.Prime).filter
    (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 6) with hGd
  set U := small ∪ SQ ∪ Gd.image (fun p => N - p) with hU
  have hw : ∀ a ∈ Sz, 13 - (3 * ((Q1.filter (fun q => q ∣ a)).card : ℝ) +
      2 * ((Q2.filter (fun q => q ∣ a)).card : ℝ) + ((Q3.filter (fun q => q ∣ a)).card : ℝ)) ≤
      13 * (if a ∈ U then 1 else 0) := by
    intro a ha
    split_ifs with haU
    · have : (0 : ℝ) ≤ ((Q1.filter (fun q => q ∣ a)).card : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ ((Q2.filter (fun q => q ∣ a)).card : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ ((Q3.filter (fun q => q ∣ a)).card : ℝ) := Nat.cast_nonneg _
      linarith
    · rw [hSz, mem_filter] at ha
      obtain ⟨haA, haP⟩ := ha
      have haA' := haA
      rw [hAdef] at haA'
      unfold goldbachSeq at haA'
      obtain ⟨p, hp, rfl⟩ := mem_image.mp haA'
      rw [mem_filter, mem_range] at hp
      obtain ⟨hpN, hpp⟩ := hp
      simp only [hU, mem_union, not_or] at haU
      obtain ⟨⟨hns, hnsq⟩, hng⟩ := haU
      have hpy : y3 < p := by
        by_contra h
        push Not at h
        exact hns (mem_image.mpr ⟨p, mem_range.mpr (by omega), rfl⟩)
      have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
      have hmodd : Odd (N - p) := by
        rcases hE with ⟨a, ha⟩
        rcases hpodd with ⟨b, hb⟩
        exact ⟨a - b - 1, by omega⟩
      have hm0 : N - p ≠ 0 := by omega
      have hΩ7 : 7 ≤ ArithmeticFunction.cardFactors (N - p) := by
        by_contra hc
        push Not at hc
        exact hng (mem_image.mpr ⟨p, by
          rw [hGd, mem_filter, mem_filter, mem_range]; exact ⟨⟨hpN, hpp⟩, by omega⟩, rfl⟩)
      have hnsq' : ∀ q, q ∈ Qa → ¬ q ^ 2 ∣ N - p := fun q hq h2 =>
        hnsq (mem_filter.mpr ⟨haA, q, hq, h2⟩)
      have hQa : ∀ q, z < q → q ≤ y3 → q.Prime → ¬ q ∣ N → q ∈ Qa := fun q h1 h2 h3 h4 => by
        rw [hQa, mem_filter, mem_Ioc]; exact ⟨⟨h1, h2⟩, h3, h4⟩
      have hd1 : ∀ q ∈ Q1.filter (fun q => q ∣ N - p), q.Prime ∧ q ∣ N - p ∧ z < q ∧ q ≤ y1 :=
        fun q hq => by
          obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
          obtain ⟨a1, a2, a3, -⟩ := hQmem _ _ q hq1
          exact ⟨a3, hq2, a1, a2⟩
      have hd2 : ∀ q ∈ Q2.filter (fun q => q ∣ N - p), q.Prime ∧ q ∣ N - p ∧ y1 < q ∧ q ≤ y2 :=
        fun q hq => by
          obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
          obtain ⟨a1, a2, a3, -⟩ := hQmem _ _ q hq1
          exact ⟨a3, hq2, a1, a2⟩
      have hd3 : ∀ q ∈ Q3.filter (fun q => q ∣ N - p), q.Prime ∧ q ∣ N - p ∧ y2 < q ∧ q ≤ y3 :=
        fun q hq => by
          obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
          obtain ⟨a1, a2, a3, -⟩ := hQmem _ _ q hq1
          exact ⟨a3, hq2, a1, a2⟩
      have hsq : ∀ q ∈ Q1.filter (fun q => q ∣ N - p) ∪ Q2.filter (fun q => q ∣ N - p) ∪
          Q3.filter (fun q => q ∣ N - p), ¬ q ^ 2 ∣ N - p := by
        intro q hq
        apply hnsq' q
        rcases mem_union.mp hq with hq | hq
        · rcases mem_union.mp hq with hq | hq
          · obtain ⟨a1, a2, a3, a4⟩ := hd1 q hq
            exact hQa q a3 (by omega) a1 ((hQmem _ _ q (mem_filter.mp hq).1).2.2.2)
          · obtain ⟨a1, a2, a3, a4⟩ := hd2 q hq
            exact hQa q (by omega) (by omega) a1 ((hQmem _ _ q (mem_filter.mp hq).1).2.2.2)
        · obtain ⟨a1, a2, a3, a4⟩ := hd3 q hq
          exact hQa q (by omega) a4 a1 ((hQmem _ _ q (mem_filter.mp hq).1).2.2.2)
      have hsmallD : ∀ r, r.Prime → r ∣ N - p → r ≤ y3 →
          r ∈ Q1.filter (fun q => q ∣ N - p) ∪ Q2.filter (fun q => q ∣ N - p) ∪
            Q3.filter (fun q => q ∣ N - p) := by
        intro r hrp hrd hry
        have hr2 : r ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hrd)
        have hr3 : 3 ≤ r := by have := hrp.two_le; omega
        have hrN : ¬ r ∣ N := by
          intro hrN
          have : r ∣ p := by
            have h1 := Nat.dvd_sub hrN hrd
            rwa [Nat.sub_sub_self hpN.le] at h1
          have := (Nat.prime_dvd_prime_iff_eq hrp hpp).mp this
          omega
        have hrz : z < r := by
          by_contra hle
          push Not at hle
          exact haP r (hcov r hrp hrN hr3
            ((show (r : ℝ) ≤ z by exact_mod_cast hle).trans hzr)) hrd
        simp only [mem_union, mem_filter, hQ1, hQ2, hQ3, mem_Ioc]
        by_cases c1 : r ≤ y1
        · exact Or.inl (Or.inl ⟨⟨⟨hrz, c1⟩, hrp, hrN⟩, hrd⟩)
        · by_cases c2 : r ≤ y2
          · exact Or.inl (Or.inr ⟨⟨⟨by omega, c2⟩, hrp, hrN⟩, hrd⟩)
          · exact Or.inr ⟨⟨⟨by omega, hry⟩, hrp, hrN⟩, hrd⟩
      have hb := bad6 (N - p) N z y1 y2 y3 hm0 (Nat.sub_le N p) hy12 _ _ _ hd1 hd2 hd3 hsq
        hsmallD hℓpos (by linarith) (by linarith) (by linarith) (by linarith) hΩ7
      have hb' : (13 : ℝ) ≤ 3 * ((Q1.filter (fun q => q ∣ N - p)).card : ℝ) +
          2 * ((Q2.filter (fun q => q ∣ N - p)).card : ℝ) +
            ((Q3.filter (fun q => q ∣ N - p)).card : ℝ) := by exact_mod_cast hb
      linarith
  have hsumw := sum_le_sum hw
  rw [← mul_sum, sum_boole, sum_sub_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum,
    ← mul_sum, swap_count, swap_count, swap_count] at hsumw
  simp only [sum_const, nsmul_eq_mul, mul_one] at hsumw
  have hU1 : (Sz.filter (fun a => a ∈ U)).card ≤ U.card :=
    card_le_card (fun a ha => (mem_filter.mp ha).2)
  have hU2 : U.card ≤ small.card + SQ.card + Gd.card :=
    (card_union_le _ _).trans (Nat.add_le_add (card_union_le _ _) card_image_le)
  have hU3 : ((Sz.filter (fun a => a ∈ U)).card : ℝ) ≤ (y3 : ℝ) + 1 + SQ.card + Gd.card := by
    have : (Sz.filter (fun a => a ∈ U)).card ≤ (y3 + 1) + SQ.card + Gd.card := by omega
    exact_mod_cast this
  -- the squares
  have hSQ1 : (SQ.card : ℝ) ≤ 2 * N / ((z : ℝ) + 1) := by
    have h1 : SQ ⊆ Qa.biUnion (fun q => (Ioc 0 N).filter (fun x => q ^ 2 ∣ x)) := by
      intro a ha
      rw [hSQ, mem_filter] at ha
      obtain ⟨haA, q, hq, hqa⟩ := ha
      rw [mem_biUnion]
      refine ⟨q, hq, mem_filter.mpr ⟨?_, hqa⟩⟩
      rw [hAdef] at haA
      unfold goldbachSeq at haA
      obtain ⟨p, hp, rfl⟩ := mem_image.mp haA
      rw [mem_filter, mem_range] at hp
      rw [mem_Ioc]
      omega
    have h2 := (card_le_card h1).trans card_biUnion_le
    have h3 : ∀ q ∈ Qa, (((Ioc 0 N).filter (fun x => q ^ 2 ∣ x)).card : ℝ) ≤
        N * ((q : ℝ) ^ 2)⁻¹ := by
      intro q _
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := q ^ 2)
      push_cast at this
      rw [div_eq_mul_inv] at this
      exact this
    have h4 : ∑ q ∈ Qa, ((q : ℝ) ^ 2)⁻¹ ≤ 2 / ((z : ℝ) + 1) := by
      refine le_trans (sum_le_sum_of_subset_of_nonneg (?_ : Qa ⊆ Ioo z (y3 + 1))
        (fun _ _ _ => by positivity)) (sum_Ioo_inv_sq_le z (y3 + 1))
      intro q hq
      obtain ⟨h1, h2, -, -⟩ := hQmem _ _ q hq
      rw [mem_Ioo]
      omega
    calc (SQ.card : ℝ) ≤ ∑ q ∈ Qa, (((Ioc 0 N).filter (fun x => q ^ 2 ∣ x)).card : ℝ) := by
          exact_mod_cast h2
      _ ≤ ∑ q ∈ Qa, (N : ℝ) * ((q : ℝ) ^ 2)⁻¹ := sum_le_sum h3
      _ = N * ∑ q ∈ Qa, ((q : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
      _ ≤ N * (2 / ((z : ℝ) + 1)) := mul_le_mul_of_nonneg_left h4 hNpos.le
      _ = 2 * N / ((z : ℝ) + 1) := by ring
  have hSQ2 : 2 * N / ((z : ℝ) + 1) ≤ Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 100 := by
    have hcube := Real.pow_div_factorial_le_exp (x := L) (by linarith) 3
    have hT : ℓ ^ 3 / (732421875 / 5324) ≤ (z : ℝ) + 1 := by
      have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [h6] at hcube
      have e : ℓ ^ 3 / (732421875 / 5324) = L ^ 3 / 6 := by rw [hL]; ring
      linarith
    have hTpos : 0 < ℓ ^ 3 / (732421875 / 5324) := by positivity
    have hstep : 2 * N / ((z : ℝ) + 1) ≤ 2 * N / (ℓ ^ 3 / (732421875 / 5324)) :=
      div_le_div_of_nonneg_left (by positivity) hTpos hT
    refine hstep.trans ?_
    rw [div_div_eq_mul_div, div_le_iff₀ (pow_pos hℓpos 3)]
    have e3 : ℓ ^ 3 = ℓ ^ 2 * ℓ := by ring
    have e : Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 100 * ℓ ^ 3 =
        Real.exp (-36) * (((N : ℝ) - 2) * ℓ) / 100 := by
      rw [e3, show Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 100 * (ℓ ^ 2 * ℓ) =
        Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2 * ℓ ^ 2) * ℓ / 100 by ring,
        div_mul_cancel₀ _ (pow_pos hℓpos 2).ne']
      ring
    rw [e]
    have hem : (1 : ℝ) / 10 ^ 18 ≤ Real.exp (-36) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 36) exp_36_le
    have h1 : ((N : ℝ) - 2) * 10 ^ 30 ≤ ((N : ℝ) - 2) * ℓ :=
      mul_le_mul_of_nonneg_left h10 (by linarith)
    have h2 : (1 / 10 ^ 18) * (((N : ℝ) - 2) * ℓ) ≤ Real.exp (-36) * (((N : ℝ) - 2) * ℓ) :=
      mul_le_mul_of_nonneg_right hem (mul_nonneg (by linarith) hℓpos.le)
    linarith
  -- y3 is small
  have hy50 : 50 * ((y3 : ℝ) + 1) ≤ Real.exp (ℓ / 3) + 2 := by
    have h1 : Real.exp (ℓ / 3) =
        Real.exp ((895430243255237372246531 / 3125000000000000000000000 * ℓ)) *
          Real.exp ((438709270234287883260407 / 9375000000000000000000000 * ℓ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : (100 : ℝ) ≤
        Real.exp ((438709270234287883260407 / 9375000000000000000000000 * ℓ)) := by
      have := Real.add_one_le_exp ((438709270234287883260407 / 9375000000000000000000000 * ℓ))
      linarith
    have h3 : (1 : ℝ) ≤
        Real.exp ((895430243255237372246531 / 3125000000000000000000000 * ℓ)) :=
      Real.one_le_exp (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one h3)
    linarith
  have hc0 : Real.exp (-36) - Real.exp (-37) ≤ Real.exp (-36) := by
    have := Real.exp_pos (-37 : ℝ); linarith
  have hD : 0 ≤ ((N : ℝ) - 2) / ℓ ^ 2 := div_nonneg (by linarith) (by positivity)
  have hcD : (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 ≤
      Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hc0 hD
  have hK3 : 0 ≤ |K| * N / ℓ ^ (3 : ℝ) := by rw [h3r]; positivity
  have he36 := Real.exp_pos (-36 : ℝ)
  have hgoal : Real.exp (-36) * N / (2 * ℓ ^ 2) ≤
      3 / 4 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 3 / 4 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) * (2 * ℓ ^ 2) =
        3 / 2 * Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2 * ℓ ^ 2) := by ring
    rw [e, div_mul_cancel₀ _ (pow_pos hℓpos 2).ne']
    nlinarith [mul_nonneg he36.le (show (0 : ℝ) ≤ (N : ℝ) - 38 by linarith)]
  have hE3' : 100 * (|K| * N / ℓ ^ (3 : ℝ)) + Real.exp (ℓ / 3) + 2 ≤
      Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) := by
    have : 100 * |K| * N / ℓ ^ (3 : ℝ) = 100 * (|K| * N / ℓ ^ (3 : ℝ)) := by ring
    linarith
  rw [hcardSz] at hlow
  linarith

end LeanLab.PNTPort.BVMax.Step6
