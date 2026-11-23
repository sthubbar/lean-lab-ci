/-
P0069 pages 30 and 31, the three pm ranges in the written proof of Lemma 15.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp546a
import LeanLab.BakerHarmanPintz1997.Decomp409b
import LeanLab.BakerHarmanPintz1997.DecompJ612

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409c
open Finset Decomp1518
attribute [local instance] Classical.propDecidable

/-- Page 31, index zero is pm at most x to 0.4, index one is the remaining pm
at most x to 0.46, and index two is pm above x to 0.46. -/
def primeRegion (x : ℝ) (m p : ℕ) : Fin 3 :=
  if ((m * p : ℕ) : ℝ) ≤ x ^ (0.4 : ℝ) then 0
  else if ((m * p : ℕ) : ℝ) ≤ x ^ (0.46 : ℝ) then 1 else 2

/-- Page 31, the prime error sum restricted to one of its three pm ranges. -/
def primePart (j : Fin 3) (x : ℝ) (a b : ℕ → ℂ) (M N w z : ℝ) (k : ℕ) : ℂ :=
  ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    if m * n ∣ k then a m * b n *
      ∑ p ∈ ((k / (m * n)).primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter
          (fun p => primeRegion x m p = j), psi (k / (m * n) / p) (p : ℝ)
    else 0

/-- Page 31, the three restrictions partition the complete prime error sum exactly. -/
theorem primePart_sum (x : ℝ) (a b : ℕ → ℂ) (M N w z : ℝ) (k : ℕ) :
    jsum a b M N w z k = primePart 0 x a b M N w z k +
      primePart 1 x a b M N w z k + primePart 2 x a b M N w z k := by
  unfold jsum primePart
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hd : m * n ∣ k
  · simp only [hd, ite_true]
    rw [← mul_add, ← mul_add]
    congr 1
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    generalize primeRegion x m p = r
    fin_cases r <;> simp
  · simp [hd]

/-- Page 31, the displayed cofactor bound in the large pm case. -/
theorem large_prime_cofactor {x m n p h : ℝ} (hx : 0 < x)
    (hm : 0 ≤ m) (hp0 : 0 ≤ p) (hh : 0 ≤ h) (hmn : m ≤ n)
    (hprod : m * n * p * h ≤ x) (hp : p ≤ x ^ (0.1 : ℝ))
    (hmp : x ^ (0.46 : ℝ) < m * p) : h ≤ x ^ (0.18 : ℝ) := by
  have hm2 : m ^ 2 ≤ m * n := by nlinarith [mul_nonneg hm (sub_nonneg.mpr hmn)]
  have hb : h * (m * p) ^ 2 ≤ x ^ (1.1 : ℝ) := by
    calc
      _ = m ^ 2 * (p ^ 2 * h) := by ring
      _ ≤ (m * n) * (p ^ 2 * h) := mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = (m * n * p * h) * p := by ring
      _ ≤ x * x ^ (0.1 : ℝ) := mul_le_mul hprod hp hp0 hx.le
      _ = x ^ (1.1 : ℝ) := by
        calc
          _ = x ^ (1 : ℝ) * x ^ (0.1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ ((1 : ℝ) + 0.1) := (Real.rpow_add hx _ _).symm
          _ = _ := by norm_num
  exact cond422_z_le hx hmp hb

/-- Page 31, the two ratios in the large pm case, with the dyadic factor two retained. -/
theorem large_prime_ratios {x m n p : ℝ} (hx : 0 < x) (hn : 0 < n)
    (hp0 : 0 ≤ p) (hmn : m ≤ n) (hp : p ≤ x ^ (0.1 : ℝ))
    (hnx : n ≤ 2 * x ^ (0.4 : ℝ)) (hmp : x ^ (0.46 : ℝ) ≤ m * p) :
    m * p / n ≤ x ^ (0.1 : ℝ) ∧ n / (m * p) ≤ 2 * x ^ (-0.06 : ℝ) := by
  have hpow : 0 < x ^ (0.46 : ℝ) := Real.rpow_pos_of_pos hx _
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ p := (div_le_iff₀ hn).mpr (by nlinarith [mul_le_mul_of_nonneg_right hmn hp0])
      _ ≤ _ := hp
  · calc
      _ ≤ (2 * x ^ (0.4 : ℝ)) / x ^ (0.46 : ℝ) := by gcongr
      _ = 2 * x ^ (-0.06 : ℝ) := by
        rw [mul_div_assoc, ← Real.rpow_sub hx]
        congr 1
        norm_num

/-- Page 31, region two is exactly the window `x^0.4 < mp` and `x^0.46 < mp`. -/
theorem primeRegion_two_iff (x : ℝ) (m p : ℕ) :
    primeRegion x m p = 2 ↔
      x ^ (0.4 : ℝ) < (m : ℝ) * (p : ℝ) ∧ x ^ (0.46 : ℝ) < (m : ℝ) * (p : ℝ) := by
  simp only [primeRegion, Nat.cast_mul]
  by_cases h1 : (m : ℝ) * (p : ℝ) ≤ x ^ (0.4 : ℝ)
  · simp [h1]
  · by_cases h2 : (m : ℝ) * (p : ℝ) ≤ x ^ (0.46 : ℝ)
    · simp [h1, h2]
    · rw [if_neg h1, if_neg h2]
      constructor
      · intro _
        exact ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩
      · intro _
        rfl

/-- Page 31, the large pm case: for one region two term the cofactor
`h = k/(m*n/p)` satisfies `h ≤ x^0.18` and the two displayed ratios hold,
namely `mp/n ≤ x^0.1` and `n/(mp) ≤ 2 x^(-0.06)`.  The divisibility
hypotheses are exactly those forced by the prime filter in `primePart`. -/
theorem large_prime_term_bounds {x : ℝ} {k m n p : ℕ} (hx : 0 < x)
    (hk : (k : ℝ) ≤ x) (hn0 : 0 < n) (hmn : (m : ℝ) ≤ (n : ℝ))
    (hdiv : m * n ∣ k) (hp : p ∣ k / (m * n))
    (hpz : (p : ℝ) ≤ x ^ (0.1 : ℝ)) (hreg : primeRegion x m p = 2)
    (hnx : (n : ℝ) ≤ 2 * x ^ (0.4 : ℝ)) :
    ((k / (m * n) / p : ℕ) : ℝ) ≤ x ^ (0.18 : ℝ) ∧
    ((m : ℝ) * (p : ℝ)) / (n : ℝ) ≤ x ^ (0.1 : ℝ) ∧
    (n : ℝ) / ((m : ℝ) * (p : ℝ)) ≤ 2 * x ^ (-0.06 : ℝ) := by
  have hreg' := primeRegion_two_iff x m p
  have hmp : x ^ (0.46 : ℝ) < (m : ℝ) * (p : ℝ) := (hreg'.mp hreg).2
  have hpq : p * (k / (m * n) / p) = k / (m * n) := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hp
  have hmul : m * n * p * (k / (m * n) / p) = k := by
    calc
      m * n * p * (k / (m * n) / p) = (m * n) * (p * (k / (m * n) / p)) := by ring
      _ = (m * n) * (k / (m * n)) := by rw [hpq]
      _ = k := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdiv
  have hcast : ((m * n * p * (k / (m * n) / p) : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast congrArg (fun z : ℕ => (z : ℝ)) hmul
  have hprod : ((m : ℝ) * (n : ℝ)) * (p : ℝ) * ((k / (m * n) / p : ℕ) : ℝ) ≤ x := by
    have heq : ((m : ℝ) * (n : ℝ)) * (p : ℝ) * ((k / (m * n) / p : ℕ) : ℝ) = (k : ℝ) := by
      calc
        ((m : ℝ) * (n : ℝ)) * (p : ℝ) * ((k / (m * n) / p : ℕ) : ℝ)
            = (((m * n * p * (k / (m * n) / p) : ℕ) : ℝ)) := by
              rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
        _ = (k : ℝ) := hcast
    rw [heq]
    exact hk
  have hcof : ((k / (m * n) / p : ℕ) : ℝ) ≤ x ^ (0.18 : ℝ) :=
    large_prime_cofactor (x := x) (m := (m : ℝ)) (n := (n : ℝ)) (p := (p : ℝ))
      (h := ((k / (m * n) / p : ℕ) : ℝ)) hx (Nat.cast_nonneg m) (Nat.cast_nonneg p)
      (Nat.cast_nonneg _) hmn hprod hpz hmp
  have hrat := large_prime_ratios (x := x) (m := (m : ℝ)) (n := (n : ℝ)) (p := (p : ℝ))
    hx (by exact_mod_cast hn0) (Nat.cast_nonneg p) hmn hpz hnx (le_of_lt hmp)
  exact ⟨hcof, hrat.1, hrat.2⟩

/-- Page 31, region one is exactly the window `x^0.4 < mp` and `mp ≤ x^0.46`. -/
theorem primeRegion_one_iff (x : ℝ) (m p : ℕ) :
    primeRegion x m p = 1 ↔
      x ^ (0.4 : ℝ) < (m : ℝ) * (p : ℝ) ∧ (m : ℝ) * (p : ℝ) ≤ x ^ (0.46 : ℝ) := by
  simp only [primeRegion, Nat.cast_mul]
  by_cases h1 : (m : ℝ) * (p : ℝ) ≤ x ^ (0.4 : ℝ)
  · simp [h1]
  · by_cases h2 : (m : ℝ) * (p : ℝ) ≤ x ^ (0.46 : ℝ)
    · rw [if_neg h1, if_pos h2]
      exact ⟨fun _ => ⟨lt_of_not_ge h1, h2⟩, fun _ => rfl⟩
    · rw [if_neg h1, if_neg h2]
      simp [h2]

/-- Page 31, the divisor bounded coefficient input (3.1) for one primePart range:
with `k ≥ 1` and `‖a m‖ ≤ tau m ^ B`, `‖b n‖ ≤ tau n ^ B`, the norm of the prime error
sum of one region is at most `tau k ^ (2 * max B 0 + 3)`. This is the coefficient bound a
future Lemma 11 route to the three transfer leaves needs; the remaining gap for each leaf
is only the mean value input (4.1), see PROGRESS.md. -/
theorem primePart_norm_le {j : Fin 3} {x : ℝ} {a b : ℕ → ℂ} {M N w z : ℝ} {k : ℕ}
    (hk : 0 < k) (B : ℝ) (ha : ∀ m, ‖a m‖ ≤ tau m ^ B) (hb : ∀ n, ‖b n‖ ≤ tau n ^ B) :
    ‖primePart j x a b M N w z k‖ ≤ tau k ^ (2 * max B 0 + 3) := by
  have hk0 : k ≠ 0 := hk.ne'
  have htau1 : ∀ n : ℕ, n ≠ 0 → 1 ≤ tau n := by
    intro n hn
    simp only [tau, ArithmeticFunction.sigma_zero_apply]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩)
  have htaudvd : ∀ {l kk : ℕ}, l ∣ kk → kk ≠ 0 → tau l ≤ tau kk := by
    intro l kk hdl hkk
    simp only [tau, ArithmeticFunction.sigma_zero_apply]
    exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hkk hdl)
  have htau_card : ((k.divisors.card : ℕ) : ℝ) = tau k := by
    simp only [tau, ArithmeticFunction.sigma_zero_apply]
  have hpsi1 : ∀ (l : ℕ) (y : ℝ), ‖psi l y‖ ≤ 1 := by
    intro l y
    unfold psi
    split <;> simp
  have hpfl : ∀ {l : ℕ}, 0 < l → ((l.primeFactors).card : ℝ) ≤ tau l := by
    intro l hl
    have hsub : l.primeFactors ⊆ l.divisors := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ l := Nat.dvd_of_mem_primeFactors hp
      exact Nat.mem_divisors.mpr ⟨hpd, ne_of_gt hl⟩
    simp only [tau, ArithmeticFunction.sigma_zero_apply]
    exact_mod_cast card_le_card hsub
  have htauk0 : (0 : ℝ) < tau k := lt_of_lt_of_le zero_lt_one (htau1 k hk0)
  -- the per term bound
  have hterm : ∀ m n : ℕ,
      ‖(if m * n ∣ k then a m * b n *
        ∑ p ∈ ((k / (m * n)).primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter
            (fun p => primeRegion x m p = j), psi (k / (m * n) / p) (p : ℝ)
        else 0 : ℂ)‖ ≤ if m * n ∣ k then tau k ^ (2 * max B 0 + 1) else 0 := by
    intro m n
    by_cases hmn : m * n ∣ k
    · have hmk : m ∣ k := (Nat.dvd_mul_right m n).trans hmn
      have hnk : n ∣ k := (Nat.dvd_mul_left n m).trans hmn
      have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hmk hk
      have hn1 : 1 ≤ n := Nat.pos_of_dvd_of_pos hnk hk
      have hm0 : m ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hm1)
      have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn1)
      have htaum1 : 1 ≤ tau m := htau1 m hm0
      have htaun1 : 1 ≤ tau n := htau1 n hn0
      have ham : ‖a m‖ ≤ tau k ^ max B 0 := by
        calc ‖a m‖ ≤ tau m ^ B := ha m
          _ ≤ tau k ^ max B 0 := by
              by_cases hB : B ≤ 0
              · rw [max_eq_right hB, Real.rpow_zero]
                calc tau m ^ B ≤ tau m ^ 0 :=
                    Real.rpow_le_rpow_of_exponent_le htaum1 hB
                  _ = 1 := by rw [Real.rpow_zero]
              · have hBpos : 0 < B := lt_of_not_ge hB
                rw [max_eq_left hBpos.le]
                exact Real.rpow_le_rpow (le_trans zero_le_one htaum1)
                  (htaudvd hmk hk0) hBpos.le
      have hbn : ‖b n‖ ≤ tau k ^ max B 0 := by
        calc ‖b n‖ ≤ tau n ^ B := hb n
          _ ≤ tau k ^ max B 0 := by
              by_cases hB : B ≤ 0
              · rw [max_eq_right hB, Real.rpow_zero]
                calc tau n ^ B ≤ tau n ^ 0 :=
                    Real.rpow_le_rpow_of_exponent_le htaun1 hB
                  _ = 1 := by rw [Real.rpow_zero]
              · have hBpos : 0 < B := lt_of_not_ge hB
                rw [max_eq_left hBpos.le]
                exact Real.rpow_le_rpow (le_trans zero_le_one htaun1)
                  (htaudvd hnk hk0) hBpos.le
      have hl1 : 0 < k / (m * n) :=
        Nat.div_pos (Nat.le_of_dvd hk hmn) (by positivity)
      have hinner : ‖∑ p ∈ ((k / (m * n)).primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter
            (fun p => primeRegion x m p = j), psi (k / (m * n) / p) (p : ℝ)‖ ≤ tau k := by
        calc _ ≤ ∑ p ∈ ((k / (m * n)).primeFactors.filter
            (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter
              (fun p => primeRegion x m p = j),
            ‖psi (k / (m * n) / p) (p : ℝ)‖ := norm_sum_le _ _
          _ ≤ ∑ p ∈ ((k / (m * n)).primeFactors.filter
              (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter
                (fun p => primeRegion x m p = j), (1 : ℝ) :=
              Finset.sum_le_sum (fun p _ => hpsi1 _ _)
          _ ≤ ((k / (m * n)).primeFactors.card : ℝ) := by
              have hsub2 : ((k / (m * n)).primeFactors.filter
                  (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter
                    (fun p => primeRegion x m p = j) ⊆
                  (k / (m * n)).primeFactors := fun p hp =>
                (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
              have hcard2 : (((k / (m * n)).primeFactors.filter
                  (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter
                    (fun p => primeRegion x m p = j)).card ≤
                  (k / (m * n)).primeFactors.card := card_le_card hsub2
              refine le_trans ?_ (Nat.cast_le.2 hcard2)
              rw [Finset.sum_const, smul_eq_mul]
              norm_num
          _ ≤ tau (k / (m * n)) := hpfl hl1
          _ ≤ tau k := htaudvd (Nat.div_dvd_of_dvd hmn) hk0
      rw [if_pos hmn, if_pos hmn]
      have hprod : ‖a m * b n * ∑ p ∈ ((k / (m * n)).primeFactors.filter
            (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter
              (fun p => primeRegion x m p = j), psi (k / (m * n) / p) (p : ℝ)‖
          ≤ tau k ^ max B 0 * tau k ^ max B 0 * tau k := by
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul ham hbn (norm_nonneg _)
          (by positivity)) hinner (norm_nonneg _) (by positivity)
      have hpow : tau k ^ max B 0 * tau k ^ max B 0 * tau k
          = tau k ^ (2 * max B 0 + 1) := by
        have h3 : tau k ^ max B 0 * tau k ^ max B 0
            = tau k ^ (2 * max B 0) := by
          rw [← Real.rpow_add htauk0 (max B 0) (max B 0)]
          congr 1
          ring
        rw [h3, Real.rpow_add htauk0 (2 * max B 0) 1, Real.rpow_one]
    · rw [if_neg hmn]
      simp
  -- the double sum reduces to divisors of k
  have hP0 : (0 : ℝ) ≤ tau k ^ (2 * max B 0 + 1) :=
    Real.rpow_nonneg (by positivity) _
  unfold primePart
  calc ‖∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      if m * n ∣ k then a m * b n *
        ∑ p ∈ ((k / (m * n)).primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter
            (fun p => primeRegion x m p = j), psi (k / (m * n) / p) (p : ℝ)
        else 0‖
      ≤ ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
          (if m * n ∣ k then tau k ^ (2 * max B 0 + 1) else 0) := by
        refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun m _ => (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun n _ => hterm m n
    _ ≤ ∑ m ∈ k.divisors, ∑ n ∈ k.divisors, tau k ^ (2 * max B 0 + 1) := by
        have hinner1 : ∀ m : ℕ, m ∣ k →
            ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
              (if m * n ∣ k then tau k ^ (2 * max B 0 + 1) else 0)
              ≤ tau k * tau k ^ (2 * max B 0 + 1) := by
          intro m hmk
          have hstep : ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
              (if m * n ∣ k then tau k ^ (2 * max B 0 + 1) else 0)
              = ∑ n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n ∣ k),
                (if m * n ∣ k then tau k ^ (2 * max B 0 + 1) else 0) :=
            (Finset.sum_subset (Finset.filter_subset (fun n => n ∣ k) _)
              (fun n hmem hnot => by
                by_cases hmn : m * n ∣ k
                · obtain ⟨c, hc⟩ := hmn
                  exact absurd
                    (Finset.mem_filter.mpr ⟨hmem, ⟨m * c, by rw [hc]; ring⟩⟩)
                    hnot
                · rw [if_neg hmn])).symm
          rw [hstep]
          refine le_trans (Finset.sum_le_sum_of_subset ?_) ?_
          · intro n hn
            have hn1 : 1 ≤ n := by
              have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
              omega
            exact Finset.mem_divisors.mpr
              ⟨(Finset.mem_filter.mp hn).2,
                ne_of_gt (lt_of_lt_of_le zero_lt_one hn1)⟩
          · calc ∑ n ∈ k.divisors,
                (if m * n ∣ k then tau k ^ (2 * max B 0 + 1) else 0)
              ≤ ∑ n ∈ k.divisors, tau k ^ (2 * max B 0 + 1) :=
                Finset.sum_le_sum (fun n _ => by
                  by_cases hmn : m * n ∣ k
                  · rw [if_pos hmn]
                  · rw [if_neg hmn]; exact hP0)
            _ = tau k * tau k ^ (2 * max B 0 + 1) := by
                rw [Finset.sum_const, smul_eq_mul, htau_card]
                ring
        have hstep2 : ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
            ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
              (if m * n ∣ k then tau k ^ (2 * max B 0 + 1) else 0)
            = ∑ m ∈ (Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊).filter (fun m => m ∣ k),
              ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
                (if m * n ∣ k then tau k ^ (2 * max B 0 + 1) else 0) :=
          (Finset.sum_subset (Finset.filter_subset (fun m => m ∣ k) _)
            (fun m hmem hnot => Finset.sum_eq_zero fun n _ => by
              by_cases hmn : m * n ∣ k
              · obtain ⟨c, hc⟩ := hmn
                exact absurd
                  (Finset.mem_filter.mpr ⟨hmem, ⟨n * c, by rw [hc]; ring⟩⟩)
                  hnot
              · rw [if_neg hmn])).symm
        rw [hstep2]
        refine le_trans (Finset.sum_le_sum_of_subset ?_) ?_
        · intro m hm
          have hm1 : 1 ≤ m := by
            have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1
            omega
          exact Finset.mem_divisors.mpr
            ⟨(Finset.mem_filter.mp hm).2,
              ne_of_gt (lt_of_lt_of_le zero_lt_one hm1)⟩
        · calc ∑ m ∈ k.divisors, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
              (if m * n ∣ k then tau k ^ (2 * max B 0 + 1) else 0)
            ≤ ∑ m ∈ k.divisors, tau k * tau k ^ (2 * max B 0 + 1) :=
              Finset.sum_le_sum (fun m hm =>
                hinner1 m (Finset.mem_divisors.mp hm).2)
          _ = ((k.divisors.card : ℕ) : ℝ) *
                (tau k * tau k ^ (2 * max B 0 + 1)) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ = tau k * tau k * tau k ^ (2 * max B 0 + 1) := by
              rw [htau_card]
              ring
    _ = tau k ^ 2 * tau k ^ (2 * max B 0 + 1) := by
        rw [Real.rpow_two]
    _ = tau k ^ (2 * max B 0 + 3) := by
        rw [← Real.rpow_add htauk0 2 (2 * max B 0 + 1)]
        norm_num

/-- LEAF. OPEN. Page 31, the contribution with pm at most x to 0.4.
This is the terminating repeated Buchstab procedure, with the divisor bounded
coefficients treated as in the proof of Lemma13. It is only one prime error range. -/
theorem small_prime_transfer :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      Ev (fun x => z x = x ^ (0.1 : ℝ) ∧ M x ≤ N x ∧ N x ≤ x ^ (0.4 : ℝ)) →
      Holds42 ε fun x k => primePart 0 x (a x) (b x) (M x) (N x) (wof x) (z x) k := by
  sorry

/-- LEAF. OPEN. Page 31, x to 0.4 below pm at most x to 0.46.
The source groups m with p and invokes Lemma13 after removing the dependent cutoff.
This statement retains only that middle range, not the whole Lemma15 sum. -/
theorem middle_prime_transfer :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      Ev (fun x => z x = x ^ (0.1 : ℝ) ∧ M x ≤ N x ∧ N x ≤ x ^ (0.4 : ℝ)) →
      Holds42 ε fun x k => primePart 1 x (a x) (b x) (M x) (N x) (wof x) (z x) k := by
  sorry

/-- LEAF. OPEN. Page 31, pm above x to 0.46.
The source uses the cofactor upper bound x to 0.18 and the two displayed ratios,
then Theorem4. This statement concerns only the large pm prime error range. -/
theorem large_prime_transfer :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      Ev (fun x => z x = x ^ (0.1 : ℝ) ∧ M x ≤ N x ∧ N x ≤ x ^ (0.4 : ℝ)) →
      Holds42 ε fun x k => primePart 2 x (a x) (b x) (M x) (N x) (wof x) (z x) k := by
  -- The per term data of this range is proved in `large_prime_term_bounds`
  -- above: the cofactor bound `h ≤ x^0.18` and the two ratios `mp/n ≤ x^0.1`,
  -- `n/(mp) ≤ 2 x^(-0.06)`, which are exactly the numerical hypotheses of
  -- `Decomp546a.theorem4_large_block`.  What is still missing is the transfer
  -- from the Theorem 4 conclusion (3.9) (`Concl39`) to the interval sum
  -- bound on the large pm error, i.e. the Perron step of page 31; see
  -- PROGRESS.md, FREE-nv-glm5 task2439.
  sorry

/-- Pages 30 and 31, exact Lemma15 assembled from the smaller prime error ranges.
CONDITIONAL ON the three range leaves here and the three Lemma12 leaves in Decomp409b.
The existing Buchstab core and Holds42 addition are proved inputs. -/
theorem lemma15_decomposed : Lemma15 := by
  obtain ⟨εl, hεl, hl⟩ := lemma12_ev Decomp409b.lemma12_decomposed
  obtain ⟨εs, hεs, hs⟩ := small_prime_transfer
  obtain ⟨εm, hεm, hm⟩ := middle_prime_transfer
  obtain ⟨εg, hεg, hg⟩ := large_prime_transfer
  refine ⟨min εl (min εs (min εm εg)), lt_min hεl (lt_min hεs (lt_min hεm hεg)), ?_⟩
  intro ε hε hεsmall
  have hel : ε < εl := hεsmall.trans_le (min_le_left _ _)
  have hes : ε < εs := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hem : ε < εm := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heg : ε < εg := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  apply lemma15_core hε.le (hl ε hε hel)
  intro B a b M N z ha hb hcond
  have h0 := hs ε hε hes B a b M N z ha hb hcond
  have h1 := hm ε hε hem B a b M N z ha hb hcond
  have h2 := hg ε hε heg B a b M N z ha hb hcond
  have hadd := holds42_add (holds42_add h0 h1) h2
  apply holds42_congr_ev (c := fun x k =>
    primePart 0 x (a x) (b x) (M x) (N x) (wof x) (z x) k +
    primePart 1 x (a x) (b x) (M x) (N x) (wof x) (z x) k +
    primePart 2 x (a x) (b x) (M x) (N x) (wof x) (z x) k) _ hadd
  exact ⟨0, fun x hx k hk => (primePart_sum x (a x) (b x) (M x) (N x) (wof x) (z x) k).symm⟩

/-- Page 31 exact grouping u = mp in each of the three prime ranges.
The original dyadic support and the p dependent rough cutoff are retained. -/
theorem primePart_regroup (j : Fin 3) (x : ℝ) (a b : ℕ → ℂ) (M N w z : ℝ)
    {k : ℕ} (hk : 0 < k) :
    primePart j x a b M N w z k =
      ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊, if n ∣ k then
        ∑ u ∈ (k / n).divisors, ∑ p ∈ u.primeFactors,
          if u / p ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊ ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z ∧
            primeRegion x (u / p) p = j then
            a (u / p) * b n * psi (k / n / u) (p : ℝ) else 0 else 0 := by
  convert Decomp546a.restricted_prime_error_regroup hk
    (Ioc ⌊M⌋₊ ⌊2 * M⌋₊) (Ioc ⌊N⌋₊ ⌊2 * N⌋₊) a b w z
    (fun m p => primeRegion x m p = j) using 1 <;>
    (try dsimp only [primePart]) <;> congr!

example : primePart 2 1 (fun _ => 1) (fun _ => 1) 1 1 2 7 12 = 1 := by
  have hr : Rough 1 3 := fun p hp _ hd => hp.not_dvd_one hd
  have h3 : (3 : ℕ).primeFactors = {3} := (by norm_num : Nat.Prime 3).primeFactors
  norm_num [primePart, primeRegion, h3, psi, hr, Finset.filter_singleton]

#print axioms primeRegion
#print axioms primePart
#print axioms primePart_sum
#print axioms large_prime_cofactor
#print axioms large_prime_ratios
#print axioms primeRegion_two_iff
#print axioms large_prime_term_bounds
#print axioms small_prime_transfer
#print axioms middle_prime_transfer
#print axioms large_prime_transfer
#print axioms lemma15_decomposed
#print axioms primePart_regroup

end LeanLab.BakerHarmanPintz1997.Decomp409c
