import LeanLab.PNTPort.LargeSieve.MontgomeryAP
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The divisor-weighted sieve sum for two residue classes

Lab proof, unit U-5554, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics.

With `c(ℓ) = (2ℓ - 1)/(ℓ - 1)² = ∑_{k ≥ 1} (k + 1) ℓ^{-k}`:

* `sum_tau_pf_eq_le`: `∑_{n ≤ Q, primeFactors n = P} τ(n)/n ≤ ∏_{ℓ ∈ P} c(ℓ)`.
* `sum_tau_le_sum_sqf`: `∑_{n ≤ Q} τ(n)/n ≤ ∑_{q ≤ Q squarefree} ∏_{ℓ ∣ q} c(ℓ)`.
* `sum_tau_ge`: `∑_{n ≤ Q} τ(n)/n ≥ log²(Q + 1)/2 - 3/4` for `Q ≥ 3`.
* `sum_sqf_c_le_coprime`: `∑_{q ≤ Q sqf} ∏ c ≤ (k/φ(k))² ∑_{q ≤ Q sqf, (q, k) = 1} ∏ c`, since
  `1 + c(ℓ) = (ℓ/(ℓ - 1))²`.
-/

namespace LeanLab.PNTPort.LargeSieve

open Finset Real

/-- `c(ℓ) = (2ℓ - 1)/(ℓ - 1)²`. -/
noncomputable def cW (ℓ : ℕ) : ℝ := (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2

/-- `τ(n)` as a real number. -/
noncomputable def tau (n : ℕ) : ℝ := (n.divisors.card : ℝ)

lemma tau_mul {m n : ℕ} (h : Nat.Coprime m n) : tau (m * n) = tau m * tau n := by
  unfold tau; rw [Nat.Coprime.card_divisors_mul h]; push_cast; ring

lemma tau_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : tau (p ^ k) = k + 1 := by
  unfold tau
  rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  push_cast; ring

lemma tau_nonneg (n : ℕ) : 0 ≤ tau n := Nat.cast_nonneg _

lemma geom_tau_le {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    ∑ k ∈ Icc 1 Q, ((k : ℝ) + 1) * (1 / (p : ℝ)) ^ k ≤ cW p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set x : ℝ := 1 / (p : ℝ)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by simp only [x]; rw [div_lt_one (by linarith)]; linarith
  have hnx : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hnx
  have h2 := hasSum_geometric_of_lt_one hx0 hx1
  have h3 := h1.add h2
  have hle := sum_le_hasSum (range (Q + 1)) (fun k _ => by positivity) h3
  have hsplit : ∑ k ∈ range (Q + 1), ((k : ℝ) * x ^ k + x ^ k) =
      1 + ∑ k ∈ Icc 1 Q, ((k : ℝ) + 1) * x ^ k := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [Nat.cast_zero, zero_mul, pow_zero, zero_add]
    congr 1
    rw [show Ico 1 (Q + 1) = Icc 1 Q by ext; simp]
    refine sum_congr rfl fun k _ => by ring
  rw [hsplit] at hle
  have hval : x / (1 - x) ^ 2 + (1 - x)⁻¹ - 1 = cW p := by
    simp only [x, cW]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have h1p : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by field_simp
    rw [h1p]
    field_simp
    ring
  linarith

/-- The divisor-weighted fibre of `n ↦ primeFactors n`. -/
theorem sum_tau_pf_eq_le (Q : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ n ∈ (Icc 1 Q).filter (fun n => n.primeFactors = P), tau n / n ≤ ∏ p ∈ P, cW p := by
  induction P using Finset.induction_on with
  | empty =>
    rw [prod_empty]
    have : (Icc 1 Q).filter (fun n => n.primeFactors = ∅) ⊆ {1} := by
      intro n hn
      rw [mem_filter, Nat.primeFactors_eq_empty, mem_Icc] at hn
      rw [mem_singleton]; omega
    refine (sum_le_sum_of_subset_of_nonneg this
      (fun _ _ _ => div_nonneg (tau_nonneg _) (Nat.cast_nonneg _))).trans ?_
    simp [tau]
  | insert p P' hpP' ih =>
    have hp : p.Prime := hP p (mem_insert_self _ _)
    have hP' : ∀ r ∈ P', r.Prime := fun r hr => hP r (mem_insert_of_mem hr)
    set T' := (Icc 1 Q).filter (fun n => n.primeFactors = P')
    have hsub : (Icc 1 Q).filter (fun n => n.primeFactors = insert p P') ⊆
        (Icc 1 Q ×ˢ T').image (fun km : ℕ × ℕ => p ^ km.1 * km.2) := by
      intro n hn
      rw [mem_filter, mem_Icc] at hn
      obtain ⟨⟨hn1, hnQ⟩, hpf⟩ := hn
      have hn0 : n ≠ 0 := by omega
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors (by rw [hpf]; exact mem_insert_self _ _)
      set k := n.factorization p
      have hk1 : 1 ≤ k := hp.factorization_pos_of_dvd hn0 hpn
      have hpk : p ^ k ∣ n := Nat.ordProj_dvd n p
      have hkQ : k ≤ Q := by
        have := Nat.lt_pow_self hp.one_lt (n := k)
        have := Nat.le_of_dvd (by omega) hpk
        omega
      set m := n / p ^ k
      have hm0 : 0 < m := Nat.ordCompl_pos p hn0
      have hmQ : m ≤ Q := (Nat.div_le_self n _).trans hnQ
      have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp hn0
      have hmn : n = p ^ k * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      have hpfm : m.primeFactors = P' := by
        ext r
        constructor
        · intro hr
          have hrn : r ∈ n.primeFactors :=
            Nat.primeFactors_mono (Nat.ordCompl_dvd n p) hn0 hr
          rw [hpf, mem_insert] at hrn
          rcases hrn with rfl | h
          · exact absurd (Nat.dvd_of_mem_primeFactors hr)
              ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop)
          · exact h
        · intro hr
          have hrn : r ∈ n.primeFactors := by rw [hpf]; exact mem_insert_of_mem hr
          have hrp : r ≠ p := fun h => hpP' (h ▸ hr)
          have hrprime := hP' r hr
          have hcr : Nat.Coprime r (p ^ k) :=
            Nat.Coprime.pow_right k ((Nat.coprime_primes hrprime hp).2 hrp)
          have hrd : r ∣ p ^ k * m := hmn ▸ Nat.dvd_of_mem_primeFactors hrn
          exact Nat.mem_primeFactors.2 ⟨hrprime, hcr.dvd_of_dvd_mul_left hrd, hm0.ne'⟩
      refine mem_image.2 ⟨(k, m), ?_, hmn.symm⟩
      rw [mem_product, mem_Icc]
      exact ⟨⟨hk1, hkQ⟩, mem_filter.2 ⟨mem_Icc.2 ⟨hm0, hmQ⟩, hpfm⟩⟩
    have hterm : ∀ km ∈ Icc 1 Q ×ˢ T', tau (p ^ km.1 * km.2) / ((p ^ km.1 * km.2 : ℕ) : ℝ) =
        (((km.1 : ℝ) + 1) * (1 / (p : ℝ)) ^ km.1) * (tau km.2 / km.2) := by
      intro km hkm
      rw [mem_product, mem_filter] at hkm
      have hcop : Nat.Coprime (p ^ km.1) km.2 := by
        apply Nat.Coprime.pow_left
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hd
        have hm0 : km.2 ≠ 0 := by have := (mem_Icc.1 hkm.2.1).1; omega
        have : p ∈ km.2.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hd, hm0⟩
        rw [hkm.2.2] at this
        exact hpP' this
      rw [tau_mul hcop, tau_prime_pow hp]
      push_cast
      rw [one_div_pow]
      field_simp
    calc ∑ n ∈ (Icc 1 Q).filter (fun n => n.primeFactors = insert p P'), tau n / n
        ≤ ∑ n ∈ (Icc 1 Q ×ˢ T').image (fun km : ℕ × ℕ => p ^ km.1 * km.2), tau n / n :=
          sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => div_nonneg (tau_nonneg _) (Nat.cast_nonneg _))
      _ ≤ ∑ km ∈ Icc 1 Q ×ˢ T', tau (p ^ km.1 * km.2) / ((p ^ km.1 * km.2 : ℕ) : ℝ) :=
          sum_image_le_of_nonneg' _ _ (fun n : ℕ => tau n / n)
            (fun _ => div_nonneg (tau_nonneg _) (Nat.cast_nonneg _))
      _ = (∑ k ∈ Icc 1 Q, ((k : ℝ) + 1) * (1 / (p : ℝ)) ^ k) * ∑ m ∈ T', tau m / m := by
          rw [sum_congr rfl hterm, sum_mul_sum, sum_product]
      _ ≤ cW p * ∏ r ∈ P', cW r := by
          apply mul_le_mul (geom_tau_le hp Q) (ih hP')
            (sum_nonneg fun _ _ => div_nonneg (tau_nonneg _) (Nat.cast_nonneg _))
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          unfold cW; exact div_nonneg (by linarith) (by positivity)
      _ = ∏ r ∈ insert p P', cW r := by rw [prod_insert hpP']

/-- `∑_{n ≤ Q} τ(n)/n ≤ ∑_{q ≤ Q sqf} ∏_{ℓ ∣ q} c(ℓ)`. -/
theorem sum_tau_le_sum_sqf (Q : ℕ) :
    ∑ n ∈ Icc 1 Q, tau n / n ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, cW p := by
  rw [← sum_fiberwise_of_maps_to (s := Icc 1 Q) (t := (Icc 1 Q).filter Squarefree) (g := rad)
    (fun n hn => by
      rw [mem_Icc] at hn
      refine mem_filter.2 ⟨mem_Icc.2 ⟨rad_pos n, ?_⟩, rad_sqf n⟩
      exact (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)).trans hn.2)]
  refine sum_le_sum fun q _ => ?_
  have hsub : (Icc 1 Q).filter (fun n => rad n = q) ⊆
      (Icc 1 Q).filter (fun n => n.primeFactors = q.primeFactors) := by
    intro n hn
    rw [mem_filter] at hn ⊢
    exact ⟨hn.1, by rw [← rad_pf n, hn.2]⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => div_nonneg (tau_nonneg _) (Nat.cast_nonneg _))).trans
    (sum_tau_pf_eq_le Q _ (fun p hp => Nat.prime_of_mem_primeFactors hp))

/-- `∑_{n ≤ Q} τ(n)/n = ∑_{a ≤ Q} (1/a) ∑_{b ≤ Q/a} 1/b`. -/
lemma sum_tau_eq (Q : ℕ) :
    ∑ n ∈ Icc 1 Q, tau n / n = ∑ a ∈ Icc 1 Q, (1 / (a : ℝ)) * ∑ b ∈ Icc 1 (Q / a), 1 / (b : ℝ) := by
  have h1 : ∀ n ∈ Icc 1 Q, tau n / n = ∑ x ∈ n.divisorsAntidiagonal, 1 / ((x.1 : ℝ) * x.2) := by
    intro n hn
    unfold tau
    rw [← Nat.map_div_right_divisors, sum_map, card_eq_sum_ones, Nat.cast_sum, sum_div]
    refine sum_congr rfl fun d hd => ?_
    show ((1 : ℕ) : ℝ) / n = 1 / ((d : ℝ) * ((n / d : ℕ) : ℝ))
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), Nat.cast_one]
  rw [sum_congr rfl h1, sum_sigma']
  simp_rw [mul_sum]
  rw [sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.2.1, x.2.2⟩) (fun x _ => ⟨x.1 * x.2, (x.1, x.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, a, b⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3, -⟩ := h
    have ha : 1 ≤ a := Nat.pos_of_ne_zero (by rintro rfl; simp at h3; omega)
    have hb : 1 ≤ b := Nat.pos_of_ne_zero (by rintro rfl; simp at h3; omega)
    refine ⟨⟨ha, ?_⟩, hb, ?_⟩
    · calc a ≤ a * b := Nat.le_mul_of_pos_right a hb
        _ ≤ Q := h3 ▸ h2
    · rw [Nat.le_div_iff_mul_le ha]; rw [mul_comm]; exact h3 ▸ h2
  · rintro ⟨a, b⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal] at h ⊢
    obtain ⟨⟨h1, -⟩, h3, h4⟩ := h
    rw [Nat.le_div_iff_mul_le h1] at h4
    refine ⟨⟨Nat.mul_pos h1 h3, by rw [mul_comm]; exact h4⟩, ?_⟩
    try simp only [true_and]
    positivity
  · rintro ⟨n, a, b⟩ h
    simp only [mem_sigma, Nat.mem_divisorsAntidiagonal] at h
    simp [h.2.1]
  · rintro ⟨a, b⟩ _; rfl
  · rintro ⟨n, a, b⟩ _
    simp only
    rw [one_div_mul_one_div]

lemma sum_log_div_le (Q : ℕ) (hQ : 3 ≤ Q) :
    ∑ a ∈ Icc 1 Q, Real.log (a : ℝ) / (a : ℝ) ≤ Real.log Q ^ 2 / 2 + 3 / 4 := by
  have hsplit : Icc 1 Q = (Icc 1 3 : Finset ℕ) ∪ Ico 4 (Q + 1) := by
    ext a; simp only [mem_Icc, mem_union, mem_Ico]; omega
  have hdisj : Disjoint (Icc 1 3 : Finset ℕ) (Ico 4 (Q + 1)) := by
    rw [disjoint_left]; intro a ha hb
    simp only [mem_Icc, mem_Ico] at ha hb; omega
  have hsmall : ∑ a ∈ (Icc 1 3 : Finset ℕ), Real.log (a : ℝ) / (a : ℝ) ≤ 3 / 4 := by
    rw [show (Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide]
    rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
    simp only [Nat.cast_one, Real.log_one, zero_div, zero_add, Nat.cast_ofNat]
    have h2 : Real.log 2 < 0.6932 := Real.log_two_lt_d9.trans (by norm_num)
    have h32 : Real.log (3 / 2) ≤ 3 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    rw [h3]
    linarith
  have hanti : AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Icc ((3 : ℕ) : ℝ) ((Q : ℕ) : ℝ)) := by
    apply Real.log_div_self_antitoneOn.mono
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ici]
    have he := Real.exp_one_lt_three
    push_cast at hx
    linarith [hx.1]
  have htail := AntitoneOn.sum_le_integral_Ico hQ hanti
  have hx3 : ∀ x ∈ Set.uIcc ((3 : ℕ) : ℝ) ((Q : ℕ) : ℝ), (3 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast hQ)] at hx
    push_cast at hx; exact hx.1
  have hint : ∫ x in ((3 : ℕ) : ℝ)..((Q : ℕ) : ℝ), Real.log x / x =
      Real.log Q ^ 2 / 2 - Real.log 3 ^ 2 / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Real.log x ^ 2 / 2)]
    · push_cast; ring
    · intro x hx
      have hx0 : 0 < x := by linarith [hx3 x hx]
      have := ((Real.hasDerivAt_log hx0.ne').pow 2).div_const 2
      convert this using 1
      field_simp
      ring
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div (Real.continuousOn_log.mono ?_) continuousOn_id
      · intro x hx h
        have := hx3 x hx
        have h0 : x = 0 := h
        linarith
      · intro x hx h
        have := hx3 x hx
        have h0 : x = 0 := h
        linarith
  rw [hint] at htail
  have hshift := Finset.sum_Ico_add' (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) 3 Q 1
  have hlog3 : 0 ≤ Real.log 3 ^ 2 / 2 := by positivity
  have htail' : ∑ a ∈ Ico 4 (Q + 1), Real.log (a : ℝ) / (a : ℝ) ≤ Real.log Q ^ 2 / 2 := by
    have : ∑ a ∈ Ico 4 (Q + 1), Real.log (a : ℝ) / (a : ℝ) =
        ∑ i ∈ Ico 3 Q, Real.log (((i + 1 : ℕ) : ℝ)) / (((i + 1 : ℕ) : ℝ)) := hshift.symm
    rw [this]
    linarith
  rw [hsplit, sum_union hdisj]
  linarith

/-- `∑_{n ≤ Q} τ(n)/n ≥ log²(Q + 1)/2 - 3/4` for `Q ≥ 3`. -/
theorem sum_tau_ge (Q : ℕ) (hQ : 3 ≤ Q) :
    Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4 ≤ ∑ n ∈ Icc 1 Q, tau n / n := by
  rw [sum_tau_eq]
  have hinner : ∀ a ∈ Icc 1 Q, Real.log (((Q : ℝ) + 1) / a) ≤ ∑ b ∈ Icc 1 (Q / a), 1 / (b : ℝ) := by
    intro a ha
    rw [mem_Icc] at ha
    have hH := log_add_one_le_harmonic (Q / a)
    rw [harmonic_eq_sum_Icc] at hH
    push_cast at hH
    simp_rw [one_div]
    refine le_trans ?_ hH
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.1
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ ha0]
    have : Q + 1 ≤ (Q / a + 1) * a := by
      have := Nat.lt_mul_div_succ Q (by omega : 0 < a); rw [mul_comm] at this; omega
    exact_mod_cast this
  have hlow : ∑ a ∈ Icc 1 Q, (1 / (a : ℝ)) * Real.log (((Q : ℝ) + 1) / a) ≤
      ∑ a ∈ Icc 1 Q, (1 / (a : ℝ)) * ∑ b ∈ Icc 1 (Q / a), 1 / (b : ℝ) :=
    sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hinner a ha) (by positivity)
  refine le_trans ?_ hlow
  have hexp : ∑ a ∈ Icc 1 Q, (1 / (a : ℝ)) * Real.log (((Q : ℝ) + 1) / a) =
      Real.log ((Q : ℝ) + 1) * ∑ a ∈ Icc 1 Q, 1 / (a : ℝ) - ∑ a ∈ Icc 1 Q, Real.log a / a := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun a ha => ?_
    rw [mem_Icc] at ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.1
    rw [Real.log_div (by positivity) ha0.ne']
    ring
  rw [hexp]
  have hH := log_add_one_le_harmonic Q
  rw [harmonic_eq_sum_Icc] at hH
  push_cast at hH
  simp_rw [← one_div] at hH
  have hL0 : 0 ≤ Real.log ((Q : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)])
  have h1 : Real.log ((Q : ℝ) + 1) ^ 2 ≤ Real.log ((Q : ℝ) + 1) * ∑ a ∈ Icc 1 Q, 1 / (a : ℝ) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hH hL0
  have h2 := sum_log_div_le Q hQ
  have h3 : Real.log Q ≤ Real.log ((Q : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < Q)) (by linarith)
  have h4 : Real.log Q ^ 2 ≤ Real.log ((Q : ℝ) + 1) ^ 2 := by
    have : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q))
    nlinarith
  linarith

/-- `∏_{ℓ ∣ q} c(ℓ)`. -/
noncomputable def fC (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, cW p

lemma cW_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ cW p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold cW; exact div_nonneg (by linarith) (by positivity)

lemma fC_nonneg (q : ℕ) : 0 ≤ fC q :=
  prod_nonneg fun _ hp => cW_nonneg (Nat.prime_of_mem_primeFactors hp)

lemma fC_mul {m n : ℕ} (h : Nat.Coprime m n) : fC (m * n) = fC m * fC n := by
  unfold fC
  rw [Nat.Coprime.primeFactors_mul h, prod_union h.disjoint_primeFactors]

noncomputable def fCA : ArithmeticFunction ℝ := ⟨fun d => if d = 0 then 0 else fC d, by simp⟩

lemma fCA_mult : fCA.IsMultiplicative := by
  refine ⟨by simp [fCA, fC], fun {m n} h => ?_⟩
  show (if m * n = 0 then 0 else fC (m * n)) = (if m = 0 then 0 else fC m) * (if n = 0 then 0 else fC n)
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, fC_mul h]

/-- `∑_{d ∣ rad k} fC d = (k/φ(k))²`. -/
theorem sum_divisors_rad_fC {k : ℕ} (hk : 1 ≤ k) :
    ∑ d ∈ (rad k).divisors, fC d = ((k : ℝ) / k.totient) ^ 2 := by
  have h1 := fCA_mult.prodPrimeFactors_one_add_of_squarefree (rad_sqf k)
  have h2 : ∑ d ∈ (rad k).divisors, fCA d = ∑ d ∈ (rad k).divisors, fC d := by
    refine sum_congr rfl fun d hd => ?_
    show (if d = 0 then 0 else fC d) = fC d
    rw [if_neg (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
  rw [← h2, ← h1, rad_pf]
  have h3 : ∀ p ∈ k.primeFactors, 1 + fCA p = ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    show 1 + (if p = 0 then 0 else fC p) = _
    rw [if_neg hpp.ne_zero]
    unfold fC cW
    rw [hpp.primeFactors, prod_singleton]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hne), add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hne)]
    ring
  rw [prod_congr rfl h3, prod_pow]
  congr 1
  rw [← sum_divisors_rad_fP hk]
  have h4 := fPA_mult.prodPrimeFactors_one_add_of_squarefree (rad_sqf k)
  have h5 : ∑ d ∈ (rad k).divisors, fPA d = ∑ d ∈ (rad k).divisors, fP d := by
    refine sum_congr rfl fun d hd => ?_
    show (if d = 0 then 0 else fP d) = fP d
    rw [if_neg (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
  rw [← h5, ← h4, rad_pf]
  refine prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  show _ = 1 + (if p = 0 then 0 else fP p)
  rw [if_neg hpp.ne_zero]
  unfold fP
  rw [hpp.primeFactors, prod_singleton]
  have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [eq_comm, eq_div_iff hne, add_mul, one_div, inv_mul_cancel₀ hne]
  ring

/-- Splitting off the part of `q` that divides `rad k`, for the weight `fC`. -/
theorem sum_sqf_c_le_coprime {k : ℕ} (hk : 1 ≤ k) (Q : ℕ) :
    ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q ≤
      ((k : ℝ) / k.totient) ^ 2 *
        ∑ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k), fC q := by
  set C := (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k)
  set D := (rad k).divisors
  set g : ℕ → ℕ × ℕ := fun q => (Nat.gcd q (rad k), q / Nat.gcd q (rad k))
  have hk0 : k ≠ 0 := by omega
  have hsplit : ∀ q, Squarefree q →
      q = (g q).1 * (g q).2 ∧ Nat.Coprime (g q).1 (g q).2 ∧ Squarefree (g q).2 := by
    intro q hq
    have hq' : q = (g q).1 * (g q).2 := (Nat.mul_div_cancel' (Nat.gcd_dvd_left q (rad k))).symm
    refine ⟨hq', ?_⟩
    have := hq' ▸ hq
    rw [Nat.squarefree_mul_iff] at this
    exact ⟨this.1, this.2.2⟩
  have hmaps : ∀ q ∈ (Icc 1 Q).filter Squarefree, g q ∈ D ×ˢ C := by
    intro q hq
    rw [mem_filter, mem_Icc] at hq
    obtain ⟨heq, hcop, hsqf⟩ := hsplit q hq.2
    rw [mem_product]
    refine ⟨Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, (rad_pos k).ne'⟩, ?_⟩
    rw [mem_filter, mem_Icc]
    have hq2pos : 0 < (g q).2 := by
      rcases Nat.eq_zero_or_pos (g q).2 with h | h
      · rw [h, mul_zero] at heq; omega
      · exact h
    refine ⟨⟨hq2pos, (Nat.div_le_self _ _).trans hq.1.2⟩, hsqf, ?_⟩
    apply Nat.coprime_of_dvd
    intro ℓ hℓ h1 h2
    have hℓd : ℓ ∣ (g q).1 := by
      apply Nat.dvd_gcd
      · exact h1.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
      · exact dvd_rad hk0 hℓ h2
    have := Nat.dvd_gcd hℓd h1
    rw [hcop.gcd_eq_one] at this
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 this)
  have hinj : Set.InjOn g ((Icc 1 Q).filter Squarefree) := by
    intro a ha b hb hab
    rw [mem_coe, mem_filter] at ha hb
    rw [(hsplit a ha.2).1, (hsplit b hb.2).1, hab]
  have hval : ∀ q ∈ (Icc 1 Q).filter Squarefree, fC q = fC (g q).1 * fC (g q).2 := by
    intro q hq
    rw [mem_filter] at hq
    obtain ⟨heq, hcop, -⟩ := hsplit q hq.2
    rw [← fC_mul hcop, ← heq]
  calc ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q
      = ∑ q ∈ (Icc 1 Q).filter Squarefree, fC (g q).1 * fC (g q).2 := sum_congr rfl hval
    _ = ∑ y ∈ ((Icc 1 Q).filter Squarefree).image g, fC y.1 * fC y.2 :=
        (sum_image (f := fun y : ℕ × ℕ => fC y.1 * fC y.2) hinj).symm
    _ ≤ ∑ y ∈ D ×ˢ C, fC y.1 * fC y.2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro y hy
          obtain ⟨q, hq, rfl⟩ := mem_image.1 hy
          exact hmaps q hq
        · intro y _ _; exact mul_nonneg (fC_nonneg _) (fC_nonneg _)
    _ = (∑ d ∈ D, fC d) * ∑ q ∈ C, fC q := by rw [sum_mul_sum, sum_product]
    _ = _ := by rw [sum_divisors_rad_fC hk]

end LeanLab.PNTPort.LargeSieve
