/-
BURST 2026-11-22, S43 unit P1122-0147. SPLIT of the cited hypothesis A22Corr of
Prep1121KLMajorArc.lean along the remark of P0088 page 15.

Kumchev and Liu 2007, P0088, arXiv 0801.0130. Page 5 hypothesis (A2.2) is taken in
Prep1121KLMajorArc as the CITED named Prop A22Corr, for lambda0 the rough indicator of
page 8 display 34 with z0 = Y^(1/4) P^(-2), main term f2 of page 15, chi on the weight
only. Page 15 explains f2: "The first term in the above sum accounts for the primes in
the support of lambda0, and the second term accounts for products p1 p2 with
z0 < p1 <= p2", and points to [14, Lemma 5.1] and Mikawa and Peneva [19, Lemma 2]
for the case lambda2 = primes.

Here A22Corr is cut into two CITED named Props of the same shape:
A22PrimeCorr, the primes part with main term 1/log m, and A22P2Corr, the part for
products of two primes at least z0 with main term f2 - 1/log m. The reduction
A22Corr_of_parts is PROVED: on the square window every z0 rough m is either a prime
or such a product, never both, because m < z0^3 there.

The two parts stay CITED walls; nothing here proves them. AI wrote the Lean code.
Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121KLMajorArc

namespace LeanLab.KumchevLiu2007.Split1122KLA22Parts

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.KumchevLiu2007.Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 5 hypothesis (A2.2) and page 15: the defect of the primes part of
lambda0, the first term 1/log u of f2 on page 15, with chi on the weight only and the
same short interval filter as roughDefect. -/
noncomputable def primeSqDefect {q : ℕ} (χ : DirichletCharacter ℂ q) (Y _P δ t : ℝ) : ℂ :=
  ∑ m ∈ (squareWindow Y).filter
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t),
    ((if m.Prime then χ m else 0) -
      (if χ = 1 then ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0))

/-- P0088 page 5 hypothesis (A2.2) and page 15: the defect of the part of lambda0 on
products p1 p2 of primes with z0 <= p1 <= p2, main term the second term
f2 - 1/log u of f2 on page 15, z0 = Y^(1/4) P^(-2) of page 8 display 34, chi on the
weight only, the same short interval filter as roughDefect. -/
noncomputable def p2SqDefect {q : ℕ} (χ : DirichletCharacter ℂ q) (Y P δ t : ℝ) : ℂ :=
  ∑ m ∈ (squareWindow Y).filter
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t),
    ((if ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p1 : ℝ) ∧
          p1 ≤ p2 ∧ m = p1 * p2 then χ m else 0) -
      (if χ = 1 then
        ((f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) - 1 / Real.log (m : ℝ) : ℝ) : ℂ)
       else 0))

/-- CITED, NAMED HYPOTHESIS. P0088 page 5 (A2.2) in the case lambda2 = primes on the
squares window, main term 1/log m, chi on the weight only, as page 15 cites from
[14, Lemma 5.1] and Mikawa and Peneva [19, Lemma 2]. Same quantifiers and bound as
A22Corr. -/
def A22PrimeCorr : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ δ : ℝ,
        0 < δ → δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖primeSqDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) ≤
            C * ((q : ℝ) * (H / Real.log X ^ B)) ^ 2 * (Real.log X ^ B) ^ (-4 : ℤ)

/-- CITED, NAMED HYPOTHESIS. P0088 page 5 (A2.2) for the products p1 p2 with
z0 <= p1 <= p2 in the support of lambda0, main term the second term of f2, as asserted
on page 15 by the same Huxley type methods. Same quantifiers and bound as A22Corr. -/
def A22P2Corr : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ δ : ℝ,
        0 < δ → δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖p2SqDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) ≤
            C * ((q : ℝ) * (H / Real.log X ^ B)) ^ 2 * (Real.log X ^ B) ^ (-4 : ℤ)

/-- PROVED. P0088 page 15 remark on f2: for 2 <= m with z0 <= m < z0^3, the z0 rough
indicator of page 4 display 10 is the prime indicator plus the indicator of products
p1 p2 of primes with z0 <= p1 <= p2, and the two cases exclude each other. -/
theorem rough_eq_prime_add_p2 {z0 : ℝ} {m : ℕ} (hm : 2 ≤ m) (hz : 1 < z0)
    (hzm : z0 ≤ (m : ℝ)) (hm3 : (m : ℝ) < z0 ^ 3) :
    roughWeight z0 m = (if m.Prime then 1 else 0) +
      (if ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ z0 ≤ (p1 : ℝ) ∧ p1 ≤ p2 ∧ m = p1 * p2
        then 1 else 0) ∧
    ¬ (m.Prime ∧ ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ z0 ≤ (p1 : ℝ) ∧ p1 ≤ p2 ∧
        m = p1 * p2) := by
  have hexcl : ¬ (m.Prime ∧ ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ z0 ≤ (p1 : ℝ) ∧ p1 ≤ p2 ∧
      m = p1 * p2) := by
    rintro ⟨hp, p1, p2, h1, h2, -, -, rfl⟩
    exact Nat.not_prime_mul h1.ne_one h2.ne_one hp
  refine ⟨?_, hexcl⟩
  unfold roughWeight
  by_cases hp : m.Prime
  · have hq : ¬ ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ z0 ≤ (p1 : ℝ) ∧ p1 ≤ p2 ∧
        m = p1 * p2 := fun h => hexcl ⟨hp, h⟩
    rw [if_pos hp, if_neg hq, if_pos]
    · simp
    intro p hpp hpd
    rw [(Nat.prime_dvd_prime_iff_eq hpp hp).mp hpd]
    exact hzm
  · rw [if_neg hp]
    by_cases hq : ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ z0 ≤ (p1 : ℝ) ∧ p1 ≤ p2 ∧
        m = p1 * p2
    · rw [if_pos hq, if_pos]
      · simp
      obtain ⟨p1, p2, h1, h2, hz1, h12, rfl⟩ := hq
      intro p hpp hpd
      rcases (Nat.Prime.dvd_mul hpp).mp hpd with hd | hd
      · rw [(Nat.prime_dvd_prime_iff_eq hpp h1).mp hd]
        exact hz1
      · rw [(Nat.prime_dvd_prime_iff_eq hpp h2).mp hd]
        exact hz1.trans (by exact_mod_cast h12)
    · rw [if_neg hq, if_neg]
      · simp
      intro hall
      have hm1 : m ≠ 1 := by omega
      set p1 := m.minFac with hp1def
      have hp1 : p1.Prime := Nat.minFac_prime hm1
      have hd1 : p1 ∣ m := Nat.minFac_dvd m
      set k := m / p1 with hkdef
      have hmk : m = p1 * k := (Nat.mul_div_cancel' hd1).symm
      have hk1 : k ≠ 1 := by
        intro h
        rw [h, mul_one] at hmk
        exact hp (hmk ▸ hp1)
      have hk0 : k ≠ 0 := by
        intro h
        rw [h, mul_zero] at hmk
        omega
      have hkd : k ∣ m := ⟨p1, by rw [hmk]; ring⟩
      have hz1 : z0 ≤ (p1 : ℝ) := hall p1 hp1 hd1
      by_cases hkp : k.Prime
      · exact hq ⟨p1, k, hp1, hkp, hz1, Nat.minFac_le_of_dvd hkp.two_le hkd, hmk⟩
      · set p2 := k.minFac with hp2def
        have hp2 : p2.Prime := Nat.minFac_prime hk1
        have hd2 : p2 ∣ k := Nat.minFac_dvd k
        set j := k / p2 with hjdef
        have hkj : k = p2 * j := (Nat.mul_div_cancel' hd2).symm
        have hj1 : j ≠ 1 := by
          intro h
          rw [h, mul_one] at hkj
          exact hkp (hkj ▸ hp2)
        have hj0 : j ≠ 0 := by
          intro h
          rw [h, mul_zero] at hkj
          exact hk0 hkj
        have hp3 : j.minFac.Prime := Nat.minFac_prime hj1
        have hd3 : j.minFac ∣ j := Nat.minFac_dvd j
        have hz2 : z0 ≤ (p2 : ℝ) := hall p2 hp2 (hd2.trans hkd)
        have hz3 : z0 ≤ (j.minFac : ℝ) :=
          hall _ hp3 (hd3.trans (⟨p2, by rw [hkj]; ring⟩ : j ∣ k) |>.trans hkd)
        have hj3 : j.minFac ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hd3
        have hmj : (m : ℝ) = (p1 : ℝ) * ((p2 : ℝ) * (j : ℝ)) := by
          rw [hmk, hkj]; push_cast; ring
        have hj3r : (j.minFac : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3
        have hz0 : 0 ≤ z0 := by linarith
        have : z0 ^ 3 ≤ (m : ℝ) := by
          rw [hmj, pow_three]
          apply mul_le_mul hz1 _ (by positivity) (by positivity)
          exact mul_le_mul hz2 (hz3.trans hj3r) hz0 (by positivity)
        linarith

/-- PROVED. P0088 page 2 display 5 and page 8 display 34: for B > 0 and 0 < eps, for all
large X every m of the square window of Y = windowY X eps satisfies the hypotheses of
rough_eq_prime_add_p2 with z0 = Y^(1/4) (log X^B)^(-2). -/
theorem window_eventually {B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) :
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ m ∈ squareWindow (windowY X ε),
      2 ≤ m ∧ 1 < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
      windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (m : ℝ) ∧
      (m : ℝ) < (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) ^ 3 := by
  have hlo := isLittleO_log_rpow_rpow_atTop (6 * B) (by norm_num : (0 : ℝ) < 7 / 48)
  have hev := (hlo.bound (by norm_num : (0 : ℝ) < 1 / 2)).and
    (Filter.eventually_ge_atTop (3 : ℝ))
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨X0, fun X hX m hmw => ?_⟩
  obtain ⟨hb, hX3⟩ := hX0 X hX
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 ≤ Real.log X := by linarith
  set P := Real.log X ^ B with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hL1 hB.le
  have hP0 : 0 < P := by linarith
  set Y := windowY X ε with hYdef
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hXpos _
  set s := Y ^ (1 / 4 : ℝ) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hY0 _
  -- P^6 = log X ^ (6 B)
  have hP6 : P ^ 6 = Real.log X ^ (6 * B) := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0]
    congr 1; push_cast; ring
  -- s >= X^(7/48)
  have hsX : X ^ (7 / 48 : ℝ) ≤ s := by
    rw [hsdef, hYdef, windowY, ← Real.rpow_mul hXpos.le]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    nlinarith
  have hb' : 2 * P ^ 6 ≤ s := by
    rw [hP6]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0 _),
      Real.norm_of_nonneg (Real.rpow_nonneg hXpos.le _)] at hb
    linarith
  have hP26 : P ^ 2 ≤ P ^ 6 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP2pos : 0 < P ^ 2 := by positivity
  have hs2 : 2 ≤ s := by nlinarith [one_le_pow₀ (n := 6) hP1]
  have hsqrt : Real.sqrt Y = s ^ 2 := by
    rw [Real.sqrt_eq_rpow, hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
    norm_num
  have hz0 : s * P ^ (-2 : ℤ) = s / P ^ 2 := by
    rw [zpow_neg, zpow_ofNat, div_eq_mul_inv]
  rw [hz0]
  simp only [squareWindow, Finset.mem_filter] at hmw
  obtain ⟨-, hlo2, hhi⟩ := hmw
  rw [hsqrt] at hlo2 hhi
  have hzle : s / P ^ 2 ≤ s := div_le_self hs0.le (by nlinarith)
  have hss : s ≤ s ^ 2 / 2 := by nlinarith
  have hm2r : (2 : ℝ) ≤ m := by nlinarith
  refine ⟨by exact_mod_cast hm2r, ?_, by linarith, ?_⟩
  · rw [lt_div_iff₀ hP2pos]
    nlinarith
  · rw [div_pow, lt_div_iff₀ (by positivity)]
    calc (m : ℝ) * (P ^ 2) ^ 3 = (m : ℝ) * P ^ 6 := by ring
      _ < s ^ 2 * P ^ 6 := by
          apply mul_lt_mul_of_pos_right hhi (by positivity)
      _ ≤ s ^ 2 * s := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [one_le_pow₀ (n := 6) hP1]
      _ = s ^ 3 := by ring

/-- PROVED. P0088 page 5 (A2.2) and page 15: when every m of the square window splits
as in rough_eq_prime_add_p2, the roughDefect of Prep1121KLMajorArc is the sum of the
primes defect and the P2 defect, pointwise in t, using f2 = 1/log m + (f2 - 1/log m). -/
theorem roughDefect_eq_add {q : ℕ} (χ : DirichletCharacter ℂ q) (Y P δ : ℝ)
    (hsplit : ∀ m ∈ squareWindow Y,
      roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m = (if m.Prime then 1 else 0) +
        (if ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p1 : ℝ) ∧
          p1 ≤ p2 ∧ m = p1 * p2 then 1 else 0)) (t : ℝ) :
    roughDefect χ Y P δ t = primeSqDefect χ Y P δ t + p2SqDefect χ Y P δ t := by
  unfold roughDefect primeSqDefect p2SqDefect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hsplit m (Finset.mem_filter.mp hm).1]
  split_ifs <;> push_cast <;> ring

/-- PROVED. P0088 page 5 (A2.2): the squared norm of a short sum over squares in
(t, t + delta t], with coefficients free of t, is interval integrable in t. -/
theorem short_sum_sq_intervalIntegrable_mul (S : Finset ℕ) (c : ℕ → ℂ) (δ a b : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t), c m‖ ^ 2)
      volume a b := by
  have hrw : ∀ t : ℝ,
      (∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t), c m) =
        ∑ m ∈ S, if (t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t) then c m else 0 :=
    fun t => Finset.sum_filter _ _
  have hmeas : Measurable (fun t : ℝ =>
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t), c m‖ ^ 2) := by
    simp_rw [hrw]
    refine (Measurable.norm ?_).pow_const 2
    refine Finset.measurable_sum _ fun m _ => ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_le measurable_const (measurable_id.add (measurable_id.const_mul δ)))
  have hbound : ∀ t : ℝ,
      ‖‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t), c m‖ ^ 2‖ ≤
        (∑ m ∈ S, ‖c m‖) ^ 2 := by
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t), c m‖ ≤
        ∑ m ∈ S, ‖c m‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _))
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact (intervalIntegrable_const (c := (∑ m ∈ S, ‖c m‖) ^ 2)).mono_fun'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

/-- PROVED. P0088 page 5 (A2.2): t -> |primeSqDefect|^2 is interval integrable. -/
theorem primeSqDefect_sq_intervalIntegrable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Y P δ a b : ℝ) :
    IntervalIntegrable (fun t => ‖primeSqDefect χ Y P δ t‖ ^ 2) volume a b :=
  short_sum_sq_intervalIntegrable_mul (squareWindow Y) _ δ a b

/-- PROVED. P0088 page 5 (A2.2): t -> |p2SqDefect|^2 is interval integrable. -/
theorem p2SqDefect_sq_intervalIntegrable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Y P δ a b : ℝ) :
    IntervalIntegrable (fun t => ‖p2SqDefect χ Y P δ t‖ ^ 2) volume a b :=
  short_sum_sq_intervalIntegrable_mul (squareWindow Y) _ δ a b

/-- PROVED. The squared norm of a sum is at most twice the sum of the squared norms. -/
theorem norm_add_sq_le' (u v : ℂ) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le u v) 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- PROVED. P0088 page 5 (A2.2) and page 15: the primes part A22PrimeCorr and the P2
part A22P2Corr together imply A22Corr, with constant 2 (C1 + C2). -/
theorem A22Corr_of_parts (h1 : A22PrimeCorr) (h2 : A22P2Corr) : A22Corr := by
  intro B hB ε hε hε'
  obtain ⟨C1, X1, hC1, hX1⟩ := h1 B hB ε hε hε'
  obtain ⟨C2, X2, hC2, hX2⟩ := h2 B hB ε hε hε'
  obtain ⟨X3, hX3⟩ := window_eventually hB hε
  refine ⟨2 * (C1 + C2), max (max X1 X2) (max X3 1), by positivity, ?_⟩
  intro X H hX hHl hHu q hq hqP χ δ hδ hδu
  have hX1' : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2' : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3' : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXone : 1 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have e1 := hX1 X H hX1' hHl hHu q hq hqP χ δ hδ hδu
  have e2 := hX2 X H hX2' hHl hHu q hq hqP χ δ hδ hδu
  have hsplit : ∀ m ∈ squareWindow (windowY X ε),
      roughWeight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m =
        (if m.Prime then 1 else 0) +
        (if ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧
            windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p1 : ℝ) ∧
            p1 ≤ p2 ∧ m = p1 * p2 then 1 else 0) := by
    intro m hm
    obtain ⟨a1, a2, a3, a4⟩ := hX3 X hX3' m hm
    exact (rough_eq_prime_add_p2 a1 a2 a3 a4).1
  have hY0 : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  have hab : windowY X ε / 4 ≤ windowY X ε := by linarith
  set Y := windowY X ε
  set P := Real.log X ^ B
  set K := ((q : ℝ) * (H / P)) ^ 2 * P ^ (-4 : ℤ)
  have i1 := primeSqDefect_sq_intervalIntegrable χ Y P δ (Y / 4) Y
  have i2 := p2SqDefect_sq_intervalIntegrable χ Y P δ (Y / 4) Y
  have i0 : IntervalIntegrable (fun t => ‖roughDefect χ Y P δ t‖ ^ 2) volume (Y / 4) Y :=
    short_sum_sq_intervalIntegrable_mul (squareWindow Y) _ δ _ _
  have hpt : ∀ t ∈ Set.Icc (Y / 4) Y, ‖roughDefect χ Y P δ t‖ ^ 2 ≤
      2 * ‖primeSqDefect χ Y P δ t‖ ^ 2 + 2 * ‖p2SqDefect χ Y P δ t‖ ^ 2 := by
    intro t _
    rw [roughDefect_eq_add χ Y P δ hsplit t]
    exact norm_add_sq_le' _ _
  calc (∫ t in Y / 4..Y, ‖roughDefect χ Y P δ t‖ ^ 2)
      ≤ ∫ t in Y / 4..Y,
          (2 * ‖primeSqDefect χ Y P δ t‖ ^ 2 + 2 * ‖p2SqDefect χ Y P δ t‖ ^ 2) :=
        intervalIntegral.integral_mono_on hab i0
          ((i1.const_mul 2).add (i2.const_mul 2)) hpt
    _ = 2 * (∫ t in Y / 4..Y, ‖primeSqDefect χ Y P δ t‖ ^ 2) +
          2 * (∫ t in Y / 4..Y, ‖p2SqDefect χ Y P δ t‖ ^ 2) := by
        rw [intervalIntegral.integral_add (i1.const_mul 2) (i2.const_mul 2),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ 2 * (C1 * K) + 2 * (C2 * K) := by
        have e1' : (∫ t in Y / 4..Y, ‖primeSqDefect χ Y P δ t‖ ^ 2) ≤ C1 * K := by
          simpa [K, mul_assoc] using e1
        have e2' : (∫ t in Y / 4..Y, ‖p2SqDefect χ Y P δ t‖ ^ 2) ≤ C2 * K := by
          simpa [K, mul_assoc] using e2
        linarith
    _ = 2 * (C1 + C2) * ((q : ℝ) * (H / P)) ^ 2 * P ^ (-4 : ℤ) := by
        simp only [K]; ring

/-! Axiom checks. -/
#print axioms rough_eq_prime_add_p2
#print axioms window_eventually
#print axioms roughDefect_eq_add
#print axioms short_sum_sq_intervalIntegrable_mul
#print axioms primeSqDefect_sq_intervalIntegrable
#print axioms p2SqDefect_sq_intervalIntegrable
#print axioms norm_add_sq_le'
#print axioms A22Corr_of_parts

end LeanLab.KumchevLiu2007.Split1122KLA22Parts
