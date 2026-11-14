/-
PP1993 pages 46 to 48, displays 14 to 26.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
Full symmetric rational envelopes bound the Farey arcs used by the paper.
The geometry and analytic reductions are distinct OPEN leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RationalGlue489

namespace LeanLab.Languasco2004.Decomp489b
open Finset Real MeasureTheory Decomp279b Decomp413a Decomp413b Decomp489a Decomp489f
noncomputable section

/-- LEAF. Page 46 display 14 and page 47 display 15, geometric reduction.
Each local window meets at most two Farey arcs. The full symmetric envelope
only increases each nonnegative mass. The factor four also includes the
square of the principal plus remainder decomposition. -/
theorem farey_local_reduction :
    ∃ N₀ : ℝ, ∀ N Y H B P R : ℝ, N₀ ≤ N → 0 < Y → 16 ≤ H → 0 ≤ B →
      0 ≤ P → 0 ≤ R →
      (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder H → principalArcMass N Y H B q ≤ P) →
      (∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder H →
        1 ≤ a → a ≤ q → Nat.Coprime a q → remainderArcMass N Y H B q a ≤ R) →
      ∀ ξ : ℝ, localMass N Y H B ξ ≤ 4 * (P + R) := by
  exact RationalGlue489.local_reduction_from_cover

/-! ### Pointwise kernel bounds -/

/-- Each phase has norm one. -/
private lemma phase_norm489b (x : ℝ) : ‖phase x‖ = 1 := by
  unfold phase
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Integer powers of one phase are the phase of the multiple. -/
private lemma phase_pow489b (t : ℝ) (k : ℕ) : phase ((k : ℝ) * t) = phase t ^ k := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A finite unit circle geometric sum over the index set `Icc 1 M` is
bounded by two over the chord to one. -/
private lemma geom_Icc_norm_le489b {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) (M : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 M, z ^ k‖ ≤ 2 / ‖z - 1‖ := by
  have hIcc : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hshift : ∑ k ∈ Finset.range M, z ^ (1 + k) = z * ∑ k ∈ Finset.range M, z ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_add, pow_one]
  rw [hIcc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, hshift, geom_sum_eq hne,
    norm_mul, norm_div, hz, one_mul]
  have hnum : ‖z ^ M - 1‖ ≤ 2 := by
    calc ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow]; norm_num
  exact div_le_div_of_nonneg_right hnum (norm_nonneg _)

/-- Jordan's inequality controls the phase chord on a nearest integer cell. -/
private lemma phase_gap_lower489b {t : ℝ} (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖phase t - 1‖ := by
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi * t) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  have hcancel : (2 / Real.pi) * (Real.pi * |t|) = 2 * |t| := by
    field_simp
  rw [abs_mul, abs_of_pos Real.pi_pos, hcancel] at hs
  have heq : phase t = Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    unfold phase
    congr 1
    push_cast
    ring
  rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * t) / 2 = Real.pi * t by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The reciprocal distance bound for the second geometric model away from
the origin. -/
private lemma secondModel_pointwise_inv489b {Y t : ℝ} (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    ‖secondModel Y t‖ ≤ |t|⁻¹ := by
  have hat : 0 < |t| := abs_pos.mpr ht0
  have hgap := phase_gap_lower489b ht
  have hden : 0 < ‖phase t - 1‖ := by linarith
  have hne : phase t ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hden
    exact absurd hden (lt_irrefl 0)
  have hsum : secondModel Y t = ∑ k ∈ Finset.Icc 1 ⌊Y⌋₊, phase t ^ k := by
    unfold secondModel
    exact Finset.sum_congr rfl (fun k _ => phase_pow489b t k)
  rw [hsum]
  refine (geom_Icc_norm_le489b (phase_norm489b t) hne ⌊Y⌋₊).trans ?_
  have h1 : (2 : ℝ) / ‖phase t - 1‖ ≤ 2 / (4 * |t|) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hgap
  have h2 : 2 / (4 * |t|) = |t|⁻¹ / 2 := by
    rw [inv_eq_one_div]
    field_simp
    ring
  have h3 : |t|⁻¹ / 2 ≤ |t|⁻¹ := by
    have := inv_nonneg.mpr (le_of_lt hat)
    linarith
  linarith

/-- The trivial size bound for the second geometric model. -/
private lemma secondModel_norm_le_floor489b (Y t : ℝ) :
    ‖secondModel Y t‖ ≤ (⌊Y⌋₊ : ℝ) := by
  unfold secondModel
  calc ‖∑ k ∈ Finset.Icc 1 ⌊Y⌋₊, phase ((k : ℝ) * t)‖ ≤
      ∑ k ∈ Finset.Icc 1 ⌊Y⌋₊, ‖phase ((k : ℝ) * t)‖ := norm_sum_le _ _
    _ = ((Finset.Icc 1 ⌊Y⌋₊).card : ℝ) := by simp [phase_norm489b]
    _ = (⌊Y⌋₊ : ℝ) := by
      rw [Nat.card_Icc]
      have : ⌊Y⌋₊ + 1 - 1 = ⌊Y⌋₊ := by omega
      rw [this]

/-- The principal rational weight has norm at most one. -/
private lemma rationalWeight_norm_le489b {q : ℕ} (hq : 1 ≤ q) : ‖rationalWeight q‖ ≤ 1 := by
  have hpos : 0 < q := by omega
  have hphi1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    have h : 1 ≤ Nat.totient q := Nat.totient_pos.mpr hpos
    exact_mod_cast h
  have hphi0 : (0 : ℝ) < (Nat.totient q : ℝ) := by linarith
  have hmu : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
    have h : ArithmeticFunction.moebius q ^ 2 = if Squarefree q then 1 else 0 :=
      ArithmeticFunction.moebius_sq
    have hreal : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 =
        if Squarefree q then (1 : ℝ) else 0 := by
      have hc := congrArg (fun m : ℤ => (m : ℝ)) h
      push_cast at hc
      simpa using hc
    have hz : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 ≤ 1 := by
      rw [hreal]
      split_ifs <;> norm_num
    have habs : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ^ 2 ≤ 1 := by
      rw [sq_abs]; exact hz
    nlinarith [abs_nonneg ((ArithmeticFunction.moebius q : ℤ) : ℝ)]
  unfold rationalWeight
  rw [Complex.norm_div, Complex.norm_intCast, Complex.norm_natCast]
  have h1 : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| / (Nat.totient q : ℝ) ≤ 1 / (Nat.totient q : ℝ) := by
    apply div_le_div_of_nonneg_right hmu (le_of_lt hphi0)
  have h2 : 1 / (Nat.totient q : ℝ) ≤ 1 := by
    rw [div_le_one hphi0]
    exact hphi1
  linarith

/-! ### The elementary totient lower bound `φ n ^ 2 ≥ n / 2` -/

/-- For `n` not divisible by two the totient already dominates the square root. -/
private lemma totient_sq_of_not_two_dvd489b : ∀ n : ℕ, ¬ 2 ∣ n → (n : ℝ) ≤ (n.totient : ℝ) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h2n
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · have hn : n = 1 := by
        rcases Nat.lt_or_ge n 1 with h | h
        · have hz : n = 0 := by omega
          rw [hz] at h2n
          exact absurd (dvd_zero 2) h2n
        · have hle : n ≤ 2 := by omega
          interval_cases n
          · rfl
          · exact absurd (by norm_num) h2n
      subst hn
      simp
    · have hn0 : 0 < n := by omega
      have hn1 : n ≠ 1 := by omega
      set p := n.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime hn1
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      have hp2 : p ≠ 2 := by
        intro h
        rw [h] at hpdvd
        exact h2n hpdvd
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      set m := n / p with hmdef
      have hnm : n = p * m := (Nat.mul_div_cancel' hpdvd).symm
      have hm_lt : m < n := by
        rw [hmdef]
        exact Nat.div_lt_self hn0 (by omega)
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hnm; omega
        · exact h
      have h2m : ¬ 2 ∣ m := by
        intro h
        apply h2n
        rw [hnm]
        exact dvd_mul_of_dvd_right h p
      have hih : (m : ℝ) ≤ (m.totient : ℝ) ^ 2 := ih m hm_lt h2m
      have hcast : ((n : ℝ)) = (p : ℝ) * (m : ℝ) := by
        rw [hnm]; push_cast; ring
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        have := hp.two_le
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast ‹2 ≤ p›
        linarith
      have hp3r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      have hphi0 : (0 : ℝ) ≤ (m.totient : ℝ) := by positivity
      by_cases hsq : p * p ∣ n
      · have hpm : p ∣ m := by
          have h' : p * p ∣ p * m := by rwa [← hnm]
          exact Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < p) h'
        have hphi : (p * m).totient = p * m.totient := Nat.totient_mul_of_prime_of_dvd hp hpm
        have hcast2 : ((n.totient : ℝ)) = (p : ℝ) * (m.totient : ℝ) := by
          rw [hnm, hphi]; push_cast; ring
        have hstep1 : (p : ℝ) * (m : ℝ) ≤ (p : ℝ) * ((m.totient : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hih (le_of_lt hp0)
        have hstep2 : (p : ℝ) * ((p : ℝ) * (m : ℝ)) ≤
            (p : ℝ) * ((p : ℝ) * ((m.totient : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep1 (le_of_lt hp0)
        rw [hcast2, hcast]
        nlinarith [hstep2, hp3r, hm0, hphi0]
      · have hpm : ¬ p ∣ m := by
          intro h
          apply hsq
          rw [hnm]
          exact mul_dvd_mul_left p h
        have hphi : (p * m).totient = (p - 1) * m.totient :=
          Nat.totient_mul_of_prime_of_not_dvd hp hpm
        have hp1 : 1 ≤ p := by omega
        have hcast2 : ((n.totient : ℝ)) = ((p : ℝ) - 1) * (m.totient : ℝ) := by
          rw [hnm, hphi, Nat.cast_mul, Nat.cast_sub hp1]
          push_cast
          ring
        have hcoef : (p : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
        have hstep : (p : ℝ) * (m : ℝ) ≤ ((p : ℝ) - 1) ^ 2 * (m : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef hm0
        have hstep2 : ((p : ℝ) - 1) * (m : ℝ) ≤
            ((p : ℝ) - 1) * ((m.totient : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hih (by linarith)
        rw [hcast2, hcast]
        nlinarith [hstep, hstep2, hcoef, hm0, hih,
          sq_nonneg (((p : ℝ) - 1) * (m.totient : ℝ))]

/-- Two times the square of the totient dominates the argument. -/
private lemma totient_sq_bound489b : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * (n.totient : ℝ) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · norm_num
      · norm_num [Nat.totient_two]
    · by_cases h2 : 2 ∣ n
      · obtain ⟨m, hm⟩ := h2
        have hm1 : 1 ≤ m := by omega
        have hm_lt : m < n := by omega
        have hncast : ((n : ℝ)) = 2 * (m : ℝ) := by rw [hm]; push_cast; ring
        by_cases h2m : 2 ∣ m
        · have hphi : (2 * m).totient = 2 * m.totient :=
            Nat.totient_mul_of_prime_of_dvd Nat.prime_two h2m
          have hcast2 : ((n.totient : ℝ)) = 2 * (m.totient : ℝ) := by
            rw [hm, hphi]; push_cast; ring
          have hih := ih m hm_lt hm1
          rw [hcast2, hncast]
          nlinarith [sq_nonneg ((m.totient : ℝ)), hih]
        · have hphi : (2 * m).totient = (2 - 1) * m.totient :=
            Nat.totient_mul_of_prime_of_not_dvd Nat.prime_two h2m
          have hcast2 : ((n.totient : ℝ)) = (m.totient : ℝ) := by
            rw [hm, hphi]; push_cast; ring
          have hA := totient_sq_of_not_two_dvd489b m h2m
          rw [hcast2, hncast]
          nlinarith [sq_nonneg ((m.totient : ℝ)), hA]
      · have hA := totient_sq_of_not_two_dvd489b n h2
        nlinarith [sq_nonneg ((n.totient : ℝ)), hA]

/-! ### Elementary integral identities for the punctured envelope -/

/-- Reciprocal squares as an integer power. -/
private lemma inv_sq_eq_zpow489b (t : ℝ) : (t * t)⁻¹ = t ^ (-2 : ℤ) := by
  rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat, sq]

/-- The integral of the reciprocal square over an interval avoiding zero. -/
private lemma integral_inv_sq489b {a b : ℝ} (ha : (0 : ℝ) ∉ Set.uIcc a b) :
    ∫ x in a..b, (x * x)⁻¹ = a⁻¹ - b⁻¹ := by
  have hfun : (fun x : ℝ => (x * x)⁻¹) = fun x => x ^ (-2 : ℤ) := by
    funext x
    exact inv_sq_eq_zpow489b x
  rw [hfun, integral_zpow (Or.inr ⟨by norm_num, ha⟩),
    show (-2 : ℤ) + 1 = -1 by norm_num, zpow_neg_one, zpow_neg_one]
  have hb : b ≠ 0 := by
    rintro rfl
    exact ha Set.right_mem_uIcc
  have ha' : a ≠ 0 := by
    rintro rfl
    exact ha Set.left_mem_uIcc
  field_simp
  ring

/-- A set integral over a closed interval is the interval integral. -/
private lemma setIntegral_Icc_eq489b (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Icc a b, g x = ∫ x in a..b, g x := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- The squared kernel is dominated by the reciprocal square away from zero. -/
private lemma secondModel_sq_le_inv_sq489b {Y t : ℝ} (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    ‖secondModel Y t‖ ^ 2 ≤ (t * t)⁻¹ := by
  have h : ‖secondModel Y t‖ ≤ |t|⁻¹ := secondModel_pointwise_inv489b ht ht0
  have h2 : ‖secondModel Y t‖ ^ 2 ≤ (|t|⁻¹) ^ 2 := by
    calc ‖secondModel Y t‖ ^ 2 = ‖secondModel Y t‖ * ‖secondModel Y t‖ := by ring
      _ ≤ |t|⁻¹ * |t|⁻¹ := mul_self_le_mul_self (norm_nonneg _) h
      _ = (|t|⁻¹) ^ 2 := by ring
  have h3 : (|t|⁻¹) ^ 2 = (t * t)⁻¹ := by
    rw [inv_pow, sq_abs, sq]
  linarith

/-- The principal mass is bounded by the squared kernel integral. -/
private lemma principalArcMass_le_integral489b {N Y H B : ℝ} {q : ℕ} (hq : 1 ≤ q) :
    principalArcMass N Y H B q ≤ ∫ t in puncturedEnvelope N Y H B q, ‖secondModel Y t‖ ^ 2 := by
  have hw := rationalWeight_norm_le489b hq
  unfold principalArcMass
  apply setIntegral_mono_on
  · refine (Continuous.integrableOn_Icc ?_).mono_set (Set.sdiff_subset)
    unfold secondModel phase rationalWeight
    fun_prop
  · refine (Continuous.integrableOn_Icc ?_).mono_set (Set.sdiff_subset)
    unfold secondModel phase
    fun_prop
  · exact (MeasurableSet.diff measurableSet_Icc (by measurability))
  · intro t _
    calc ‖rationalWeight q * secondModel Y t‖ ^ 2
        = ‖rationalWeight q‖ ^ 2 * ‖secondModel Y t‖ ^ 2 := by
          rw [norm_mul, mul_pow]
      _ ≤ 1 ^ 2 * ‖secondModel Y t‖ ^ 2 := by
          have hw2 : ‖rationalWeight q‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
            nlinarith [norm_nonneg (rationalWeight q), hw]
          exact mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)
      _ = ‖secondModel Y t‖ ^ 2 := by ring

/-- The reciprocal square is continuous on any interval avoiding zero. -/
private lemma continuousOn_inv_sq489b {a b : ℝ} (h : (0 : ℝ) ∉ Set.uIcc a b) :
    ContinuousOn (fun t : ℝ => (t * t)⁻¹) (Set.uIcc a b) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro x hx
  have hx' : x ≠ 0 := by
    intro h0
    exact h (h0 ▸ hx)
  exact mul_ne_zero hx' hx'

/-- The reciprocal square as an interval integral, stated through the
closed interval. -/
private lemma setIntegral_Icc_inv_sq489b {a b : ℝ} (ha : (0 : ℝ) ∉ Set.uIcc a b)
    (hab : a ≤ b) :
    ∫ t in Set.Icc a b, (t * t)⁻¹ = a⁻¹ - b⁻¹ := by
  rw [setIntegral_Icc_eq489b _ hab, integral_inv_sq489b ha]

/-- Case `q ≤ L ^ B`: the puncture removes the peak and the reciprocal square
bound applies on the two remaining pieces. -/
private lemma punctured_mass_le_low489b {N Y H B : ℝ} {q : ℕ}
    (hq : 1 ≤ q) (hY : 0 < Y) (hlogN : 0 < Real.log N)
    (hqB : (q : ℝ) ≤ Real.log N ^ B)
    (hδc : Real.log N ^ (2 * B) / ((q : ℝ) * Y) ≤ 1 / ((q : ℝ) * fareyOrder H))
    (hc2 : 1 / ((q : ℝ) * fareyOrder H) ≤ 1 / 2) :
    principalArcMass N Y H B q ≤ 2 * ((q : ℝ) * Y) / Real.log N ^ (2 * B) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  set c := 1 / ((q : ℝ) * fareyOrder H) with hc
  set δ := Real.log N ^ (2 * B) / ((q : ℝ) * Y) with hd
  have hδpos : 0 < δ := by
    rw [hd]
    positivity
  have hcpos : 0 < c := lt_of_lt_of_le hδpos hδc
  have hset : puncturedEnvelope N Y H B q = Set.Icc (-c) (-δ) ∪ Set.Icc δ c := by
    unfold puncturedEnvelope
    rw [if_pos hqB, ← hc, ← hd]
    ext t
    simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, Set.mem_union]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases h4 : t ≤ -δ
      · exact Or.inl ⟨h1, h4⟩
      · push_neg at h4
        refine Or.inr ⟨?_, h2⟩
        by_contra h5
        push_neg at h5
        exact h3 ⟨h4, h5⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · refine ⟨⟨h1, by linarith [le_of_lt hδpos]⟩, ?_⟩
        intro hcon
        linarith [hcon.1, hcon.2, h2]
      · refine ⟨⟨by linarith [le_of_lt hδpos], h2⟩, ?_⟩
        intro hcon
        linarith [hcon.1, hcon.2, h1]
  have hFcont : Continuous (fun t : ℝ => ‖secondModel Y t‖ ^ 2) := by
    unfold secondModel phase
    fun_prop
  have hmass := principalArcMass_le_integral489b (N := N) (Y := Y) (H := H) (B := B)
    (q := q) hq
  rw [hset] at hmass
  have hdisj : Disjoint (Set.Icc (-c) (-δ)) (Set.Icc δ c) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    linarith [h1.2, h2.1]
  have hsplit : ∫ t in (Set.Icc (-c) (-δ) ∪ Set.Icc δ c), ‖secondModel Y t‖ ^ 2 =
      (∫ t in Set.Icc (-c) (-δ), ‖secondModel Y t‖ ^ 2) +
        ∫ t in Set.Icc δ c, ‖secondModel Y t‖ ^ 2 :=
    setIntegral_union (μ := volume) hdisj measurableSet_Icc hFcont.integrableOn_Icc
      hFcont.integrableOn_Icc
  rw [hsplit] at hmass
  have hleft : ∫ t in Set.Icc (-c) (-δ), ‖secondModel Y t‖ ^ 2 ≤ δ⁻¹ - c⁻¹ := by
    rw [setIntegral_Icc_eq489b _ (by linarith : -c ≤ -δ)]
    have hmono := intervalIntegral.integral_mono_on (by linarith : -c ≤ -δ)
      (hFcont.intervalIntegrable (-c) (-δ))
      ((continuousOn_inv_sq489b (by
        rw [Set.uIcc_of_le (by linarith : -c ≤ -δ)]
        simp only [Set.mem_Icc]
        intro h
        linarith [h.2, hδpos])).intervalIntegrable (μ := volume))
      (by
        intro t ht
        have ht1 : t ≤ -δ := ht.2
        have ht2 : -c ≤ t := ht.1
        have htabs : |t| ≤ 1 / 2 := by
          rw [abs_le]
          constructor <;> linarith [hc2]
        have ht0 : t ≠ 0 := by
          intro h0
          rw [h0] at ht1
          linarith [hδpos]
        exact secondModel_sq_le_inv_sq489b htabs ht0)
    have hval : (-c)⁻¹ - (-δ)⁻¹ = δ⁻¹ - c⁻¹ := by
      rw [inv_neg, inv_neg]
      ring
    rwa [integral_inv_sq489b (by
      rw [Set.uIcc_of_le (by linarith : -c ≤ -δ)]
      simp only [Set.mem_Icc]
      intro h
      linarith [h.2, hδpos]), hval] at hmono
  have hright : ∫ t in Set.Icc δ c, ‖secondModel Y t‖ ^ 2 ≤ δ⁻¹ - c⁻¹ := by
    rw [setIntegral_Icc_eq489b _ hδc]
    have hmono := intervalIntegral.integral_mono_on hδc
      (hFcont.intervalIntegrable δ c)
      ((continuousOn_inv_sq489b (by
        rw [Set.uIcc_of_le hδc]
        simp only [Set.mem_Icc]
        intro h
        linarith [h.1, hδpos])).intervalIntegrable (μ := volume))
      (by
        intro t ht
        have htabs : |t| ≤ 1 / 2 := by
          rw [abs_le]
          constructor <;> linarith [ht.1, ht.2, hc2]
        have ht0 : t ≠ 0 := by
          intro h0
          rw [h0] at ht
          linarith [hδpos, ht.1]
        exact secondModel_sq_le_inv_sq489b htabs ht0)
    rwa [integral_inv_sq489b (by
      rw [Set.uIcc_of_le hδc]
      simp only [Set.mem_Icc]
      intro h
      linarith [h.1, hδpos])] at hmono
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hcpos
  have hδinv : δ⁻¹ = ((q : ℝ) * Y) / Real.log N ^ (2 * B) := by
    rw [hd, inv_div]
  have hgoal2 : 2 * (((q : ℝ) * Y) / Real.log N ^ (2 * B)) =
      2 * ((q : ℝ) * Y) / Real.log N ^ (2 * B) := by ring
  linarith [hmass, hleft, hright, hcinv, hδinv, hgoal2]

/-- The principal rational weight is bounded by the reciprocal totient. -/
private lemma rationalWeight_norm_le_inv_totient489b {q : ℕ} (hq : 1 ≤ q) :
    ‖rationalWeight q‖ ≤ ((Nat.totient q : ℝ))⁻¹ := by
  have hpos : 0 < q := by omega
  have hphi1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    have h : 1 ≤ Nat.totient q := Nat.totient_pos.mpr hpos
    exact_mod_cast h
  have hphi0 : (0 : ℝ) < (Nat.totient q : ℝ) := by linarith
  have hmu : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
    have h : ArithmeticFunction.moebius q ^ 2 = if Squarefree q then 1 else 0 :=
      ArithmeticFunction.moebius_sq
    have hreal : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 =
        if Squarefree q then (1 : ℝ) else 0 := by
      have hc := congrArg (fun m : ℤ => (m : ℝ)) h
      push_cast at hc
      simpa using hc
    have hz : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 ≤ 1 := by
      rw [hreal]
      split_ifs <;> norm_num
    have habs : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ^ 2 ≤ 1 := by
      rw [sq_abs]; exact hz
    nlinarith [abs_nonneg ((ArithmeticFunction.moebius q : ℤ) : ℝ)]
  unfold rationalWeight
  rw [Complex.norm_div, Complex.norm_intCast, Complex.norm_natCast, inv_eq_one_div]
  exact div_le_div_of_nonneg_right hmu (le_of_lt hphi0)

/-- The squared kernel is bounded by the square of its floor. -/
private lemma secondModel_sq_le_floor_sq489b (Y t : ℝ) :
    ‖secondModel Y t‖ ^ 2 ≤ (⌊Y⌋₊ : ℝ) ^ 2 := by
  have h := secondModel_norm_le_floor489b Y t
  have h0 : (0 : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by positivity
  calc ‖secondModel Y t‖ ^ 2 = ‖secondModel Y t‖ * ‖secondModel Y t‖ := by ring
    _ ≤ (⌊Y⌋₊ : ℝ) * (⌊Y⌋₊ : ℝ) := mul_self_le_mul_self (norm_nonneg _) h
    _ = (⌊Y⌋₊ : ℝ) ^ 2 := by ring

/-- Case `q > L ^ B`: the envelope is the whole symmetric interval; the
totient factor supplies the saving. -/
private lemma unpunctured_mass_le_high489b {N Y H B : ℝ} {q : ℕ} {E : ℝ}
    (hq : 1 ≤ q) (hY : 0 < Y) (hY1 : 1 ≤ Y) (hlogN : 0 < Real.log N)
    (hQpos : 0 < fareyOrder H)
    (hqB : ¬ (q : ℝ) ≤ Real.log N ^ B)
    (hc2 : 1 / ((q : ℝ) * fareyOrder H) ≤ 1 / 2)
    (hφ : Real.log N ^ E ≤ (Nat.totient q : ℝ) ^ 2) :
    principalArcMass N Y H B q ≤ 4 * Y / Real.log N ^ E := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  set c := 1 / ((q : ℝ) * fareyOrder H) with hc
  set m := (⌊Y⌋₊ : ℝ) with hm
  have hm1 : 1 ≤ m := by
    rw [hm]
    have h : (1:ℕ) ≤ ⌊Y⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast h
  have hmpos : 0 < m := lt_of_lt_of_le one_pos hm1
  have hmY : m ≤ Y := by
    rw [hm]
    exact Nat.floor_le (show (0 : ℝ) ≤ Y by linarith)
  have hcpos : 0 < c := by
    rw [hc]
    exact one_div_pos.mpr (by positivity)
  have hFcont : Continuous (fun t : ℝ => ‖secondModel Y t‖ ^ 2) := by
    unfold secondModel phase
    fun_prop
  have hset : puncturedEnvelope N Y H B q = Set.Icc (-c) c := by
    unfold puncturedEnvelope
    rw [if_neg hqB, ← hc]
    simp
  have hw2 : ‖rationalWeight q‖ ^ 2 ≤ ((Nat.totient q : ℝ) ^ 2)⁻¹ := by
    have hphi1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
      have h : 1 ≤ Nat.totient q := Nat.totient_pos.mpr (by omega)
      exact_mod_cast h
    have hphi0 : (0 : ℝ) < (Nat.totient q : ℝ) := by linarith
    have h1 : ‖rationalWeight q‖ ≤ ((Nat.totient q : ℝ))⁻¹ :=
      rationalWeight_norm_le_inv_totient489b hq
    have h2 : ‖rationalWeight q‖ ^ 2 ≤ (((Nat.totient q : ℝ))⁻¹) ^ 2 := by
      calc ‖rationalWeight q‖ ^ 2 = ‖rationalWeight q‖ * ‖rationalWeight q‖ := by ring
        _ ≤ ((Nat.totient q : ℝ))⁻¹ * ((Nat.totient q : ℝ))⁻¹ :=
            mul_self_le_mul_self (norm_nonneg _) h1
        _ = (((Nat.totient q : ℝ))⁻¹) ^ 2 := by ring
    have h3 : (((Nat.totient q : ℝ))⁻¹) ^ 2 = ((Nat.totient q : ℝ) ^ 2)⁻¹ := by
      rw [inv_pow]
    linarith [h2, h3.le, h3.ge]
  have hbound4 : ∫ t in Set.Icc (-c) c, ‖secondModel Y t‖ ^ 2 ≤ 4 * m := by
    rw [setIntegral_Icc_eq489b _ (by linarith : -c ≤ c)]
    have hii : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => ‖secondModel Y t‖ ^ 2) volume a b :=
      fun a b => hFcont.intervalIntegrable a b
    by_cases hcM : 1 / m ≤ c
    · have h1 : ∫ t in -c..(-(1 / m)), ‖secondModel Y t‖ ^ 2 ≤ m := by
        have hmono := intervalIntegral.integral_mono_on (by linarith : -c ≤ -(1 / m))
          (hii _ _)
          ((continuousOn_inv_sq489b (by
            rw [Set.uIcc_of_le (by linarith : -c ≤ -(1 / m))]
            simp only [Set.mem_Icc]
            intro h
            have : (0:ℝ) < 1 / m := by positivity
            linarith [h.2])).intervalIntegrable (μ := volume))
          (by
            intro t ht
            have ht1 : t ≤ -(1 / m) := ht.2
            have hm0 : (0:ℝ) < 1 / m := by positivity
            have htabs : |t| ≤ 1 / 2 := by
              rw [abs_le]
              constructor <;> linarith [ht.1, hc2, ht1, hm0]
            have ht0 : t ≠ 0 := by
              intro h0
              rw [h0] at ht1
              have : (0:ℝ) < 1 / m := by positivity
              linarith
            exact secondModel_sq_le_inv_sq489b htabs ht0)
        have hval : ∫ t in -c..(-(1 / m)), (t * t)⁻¹ = -c⁻¹ + m := by
          have hm0 : (0:ℝ) < 1 / m := by positivity
          have hinv : (1 / m)⁻¹ = m := by
            rw [inv_div, div_one]
          rw [integral_inv_sq489b (by
            rw [Set.uIcc_of_le (by linarith : -c ≤ -(1 / m))]
            simp only [Set.mem_Icc]
            intro h
            linarith [h.2, hm0]), inv_neg, inv_neg, hinv, sub_neg_eq_add]
        rw [hval] at hmono
        have hcinv : 0 < c⁻¹ := inv_pos.mpr hcpos
        linarith [hmono, hcinv]
      have hm0 : (0:ℝ) < 1 / m := by positivity
      have h2 : ∫ t in (-(1 / m))..(1 / m), ‖secondModel Y t‖ ^ 2 ≤ 2 * m := by
        have hInt := intervalIntegral.integral_mono_on (by linarith : -(1 / m) ≤ (1 / m))
          (hii _ _) (intervalIntegrable_const (μ := volume))
          (fun t _ => secondModel_sq_le_floor_sq489b Y t)
        have hval : ∫ t in (-(1 / m))..(1 / m), m ^ 2 = m ^ 2 * (2 / m) := by
          rw [intervalIntegral.integral_const]
          ring
        have hsimp : m ^ 2 * (2 / m) = 2 * m := by
          field_simp
        linarith [hInt, hval.le, hsimp.le, hsimp.ge]
      have h3 : ∫ t in (1 / m)..c, ‖secondModel Y t‖ ^ 2 ≤ m := by
        have hmono := intervalIntegral.integral_mono_on hcM (hii _ _)
          ((continuousOn_inv_sq489b (by
            rw [Set.uIcc_of_le hcM]
            simp only [Set.mem_Icc]
            intro h
            linarith [h.1, hm0])).intervalIntegrable (μ := volume))
          (by
            intro t ht
            have htabs : |t| ≤ 1 / 2 := by
              rw [abs_le]
              constructor <;> linarith [ht.1, ht.2, hc2, hm0]
            have ht0 : t ≠ 0 := by
              intro h0
              rw [h0] at ht
              linarith [hm0, ht.1]
            exact secondModel_sq_le_inv_sq489b htabs ht0)
        have hval : ∫ t in (1 / m)..c, (t * t)⁻¹ = m - c⁻¹ := by
          have hm0 : (0:ℝ) < 1 / m := by positivity
          have hinv : (1 / m)⁻¹ = m := by
            rw [inv_div, div_one]
          rw [integral_inv_sq489b (by
            rw [Set.uIcc_of_le hcM]
            simp only [Set.mem_Icc]
            intro h
            linarith [h.1, hm0]), hinv]
        rw [hval] at hmono
        have hcinv : 0 < c⁻¹ := inv_pos.mpr hcpos
        linarith [hmono, hcinv]
      have e1 := intervalIntegral.integral_add_adjacent_intervals
        (hii (-c) (-(1 / m))) (hii (-(1 / m)) c)
      have e2 := intervalIntegral.integral_add_adjacent_intervals
        (hii (-(1 / m)) (1 / m)) (hii (1 / m) c)
      rw [← e1, ← e2]
      linarith [h1, h2, h3]
    · -- The middle interval already contains the whole range.
      have hInt := intervalIntegral.integral_mono_on (by linarith : -c ≤ c)
        (hii _ _) (intervalIntegrable_const (μ := volume))
        (fun t _ => secondModel_sq_le_floor_sq489b Y t)
      have hval : ∫ t in -c..c, m ^ 2 = m ^ 2 * (2 * c) := by
        rw [intervalIntegral.integral_const]
        ring
      have hsmall : m ^ 2 * (2 * c) ≤ 2 * m := by
        have hcm : c * m < 1 := by
          have h2 : c < 1 / m := not_le.mp hcM
          rw [lt_div_iff₀ hmpos] at h2
          linarith
        nlinarith [hcm, hmpos, hcpos]
      linarith [hInt, hval.le, hsmall]
  have hInt_nonneg : (0:ℝ) ≤ ∫ t in Set.Icc (-c) c, ‖secondModel Y t‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Icc (fun t _ => sq_nonneg _)
  have hmass_eq : principalArcMass N Y H B q =
      ∫ t in Set.Icc (-c) c, ‖rationalWeight q * secondModel Y t‖ ^ 2 := by
    unfold principalArcMass
    rw [hset]
  have hconst : ∫ t in Set.Icc (-c) c, ‖rationalWeight q * secondModel Y t‖ ^ 2 =
      ‖rationalWeight q‖ ^ 2 * ∫ t in Set.Icc (-c) c, ‖secondModel Y t‖ ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t _
    simp only [norm_mul, mul_pow]
  have hLpos : 0 < Real.log N ^ E := Real.rpow_pos_of_pos hlogN E
  have hφpos : 0 < (Nat.totient q : ℝ) ^ 2 := by
    have h : 0 < Nat.totient q := Nat.totient_pos.mpr (by omega)
    have h2 : (0:ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast h
    positivity
  have hφinv : ((Nat.totient q : ℝ) ^ 2)⁻¹ ≤ (Real.log N ^ E)⁻¹ :=
    (inv_le_inv₀ hφpos hLpos).mpr hφ
  have hstep1 : ‖rationalWeight q‖ ^ 2 * (∫ t in Set.Icc (-c) c, ‖secondModel Y t‖ ^ 2) ≤
      ((Nat.totient q : ℝ) ^ 2)⁻¹ * (4 * m) :=
    mul_le_mul hw2 hbound4 hInt_nonneg (by positivity)
  have hstep2 : ((Nat.totient q : ℝ) ^ 2)⁻¹ * (4 * m) ≤
      (Real.log N ^ E)⁻¹ * (4 * Y) := by
    apply mul_le_mul hφinv _ (by positivity) (le_of_lt (inv_pos.mpr hLpos))
    linarith
  have hstep3 : (Real.log N ^ E)⁻¹ * (4 * Y) = 4 * Y / Real.log N ^ E := by
    rw [inv_eq_one_div]
    ring
  rw [hmass_eq, hconst]
  linarith [hstep1, hstep2, hstep3.le, hstep3.ge]

/-- LEAF. Page 47 following display 15: only the principal rational term.
This is an elementary geometric sum tail estimate, separate from characters. -/
theorem principal_arc_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℝ, N₀ ≤ N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ fareyOrder (windowLength N η) →
      principalArcMass N (localization N η) (windowLength N η) (arcExponent η A) q ≤
        C * localization N η / Real.log N ^ (2 * A + 3) := by
  refine ⟨1, one_pos, ?_⟩
  intro η A hη hη1 hA
  refine ⟨4, Real.exp 100, by norm_num, ?_⟩
  intro N hN q hq hqQ
  have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 100) hN
  have hexp1 : (1 : ℝ) < Real.exp 100 := by
    have h := Real.exp_lt_exp.mpr (by norm_num : (0:ℝ) < 100)
    simpa using h
  have hNlt : (1 : ℝ) < N := lt_of_lt_of_le hexp1 hN
  have hN1 : 1 ≤ N := le_of_lt hNlt
  have hL100 : 100 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos 100) hN
    rwa [Real.log_exp] at h
  have hLpos : 0 < Real.log N := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log N := by linarith
  have hlen : 7 / 36 ≤ lengthExponent η := by
    unfold lengthExponent
    nlinarith [hη]
  have hH16 : 16 ≤ windowLength N η := by
    unfold windowLength
    have hstep1 : Real.exp (175 / 9) ≤ N ^ (7 / 36 : ℝ) := by
      have h2 := Real.rpow_le_rpow (le_of_lt (Real.exp_pos 100)) hN
        (by norm_num : (0:ℝ) ≤ 7 / 36)
      have h3 : (Real.exp 100) ^ (7 / 36 : ℝ) = Real.exp (175 / 9) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos 100), Real.log_exp]
        norm_num
      rwa [h3] at h2
    have hstep2 : N ^ (7 / 36 : ℝ) ≤ N ^ lengthExponent η :=
      Real.rpow_le_rpow_of_exponent_le hN1 hlen
    have hstep3 : (16 : ℝ) ≤ Real.exp (175 / 9) := by
      have h4 : Real.log 16 ≤ 175 / 9 := by
        have h5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 16 by norm_num)
        linarith
      exact (Real.log_le_iff_le_exp (x := 16) (y := 175 / 9) (by norm_num)).mp h4
    linarith
  have hQ2 : 2 ≤ fareyOrder (windowLength N η) := by
    unfold fareyOrder
    have h4 : (4 : ℝ) ≤ Real.sqrt (windowLength N η) := by
      have hsq : (4:ℝ) ^ 2 ≤ (Real.sqrt (windowLength N η)) ^ 2 := by
        rw [Real.sq_sqrt (by linarith : (0:ℝ) ≤ windowLength N η)]
        linarith
      nlinarith [Real.sqrt_nonneg (windowLength N η), hsq]
    linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hc2 : 1 / ((q : ℝ) * fareyOrder (windowLength N η)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hQ2, hq1]
  have hY1 : (1 : ℝ) ≤ localization N η := by
    unfold localization
    exact Real.one_le_rpow hN1 (by linarith : (0:ℝ) ≤ 7 / 12 + η)
  have hYpos : 0 < localization N η := lt_of_lt_of_le one_pos hY1
  have hexpB : 2 * A + 3 ≤ arcExponent η A := by
    unfold arcExponent
    have h3 : 0 < 2 * A + 25 := by linarith
    rw [show (3:ℝ) / η * (2 * A + 25) = 3 * (2 * A + 25) / η by field_simp]
    rw [le_div_iff₀ hη]
    nlinarith [hη1, hη, hA]
  have hexpB2 : 2 * (2 * A + 3) ≤ arcExponent η A := by
    unfold arcExponent
    have h3 : 0 < 2 * A + 25 := by linarith
    rw [show (3:ℝ) / η * (2 * A + 25) = 3 * (2 * A + 25) / η by field_simp]
    rw [le_div_iff₀ hη]
    nlinarith [hη1, hη, hA]
  have hLB : Real.log N ^ (2 * A + 3) ≤ Real.log N ^ arcExponent η A :=
    Real.rpow_le_rpow_of_exponent_le hL1 hexpB
  have hP2 : Real.log N ^ (3 : ℝ) ≤ Real.log N ^ (2 * A + 3) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hP3 : (2 : ℝ) ≤ Real.log N ^ (2 * A + 3) := by
    have hstep : Real.log N ^ (3 : ℝ) ≤ Real.log N ^ (2 * A + 3) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : (3:ℝ) ≤ 2 * A + 3)
    have hbig : (2 : ℝ) ≤ Real.log N ^ (3 : ℝ) := by
      have h3eq : Real.log N ^ (3 : ℝ) = (Real.log N) ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [h3eq]
      have hp1 : (100:ℝ) * 100 ≤ Real.log N * Real.log N :=
        mul_self_le_mul_self (by norm_num) hL100
      have hp2 : (100:ℝ) * 100 * 100 ≤ (Real.log N * Real.log N) * Real.log N :=
        mul_le_mul hp1 hL100 (by norm_num) (by positivity)
      calc (2:ℝ) ≤ 100 * 100 * 100 := by norm_num
        _ ≤ (Real.log N * Real.log N) * Real.log N := hp2
        _ = (Real.log N) ^ 3 := by ring
    linarith [hstep, hbig]
  have hcmp : (q : ℝ) ≤ Real.log N ^ arcExponent η A →
      2 * ((q : ℝ) * localization N η) / Real.log N ^ (2 * arcExponent η A) ≤
      4 * localization N η / Real.log N ^ (2 * A + 3) := by
    intro hqB
    have hB2 : Real.log N ^ (2 * arcExponent η A) =
        Real.log N ^ arcExponent η A * Real.log N ^ arcExponent η A := by
      rw [show (2 * arcExponent η A) = arcExponent η A + arcExponent η A by ring,
        Real.rpow_add hLpos]
    have hLA : 0 < Real.log N ^ (2 * A + 3) := Real.rpow_pos_of_pos hLpos _
    have hLBpos : 0 < Real.log N ^ arcExponent η A := Real.rpow_pos_of_pos hLpos _
    rw [hB2, div_le_div_iff₀ (by positivity) hLA]
    have h1 : (q : ℝ) * Real.log N ^ (2 * A + 3) ≤
        Real.log N ^ arcExponent η A * Real.log N ^ arcExponent η A := by
      have hqa : (q : ℝ) ≤ Real.log N ^ arcExponent η A := hqB
      have hb : Real.log N ^ (2 * A + 3) ≤ Real.log N ^ arcExponent η A := hLB
      nlinarith [hqa, hb, hq0, hLA, hLBpos]
    have hY0 : (0 : ℝ) ≤ localization N η := le_of_lt hYpos
    nlinarith [h1, hY0, hLA]
  by_cases hqB : (q : ℝ) ≤ Real.log N ^ arcExponent η A
  · by_cases hδc : Real.log N ^ (2 * arcExponent η A) / ((q : ℝ) * localization N η) ≤
        1 / ((q : ℝ) * fareyOrder (windowLength N η))
    · have h1 := punctured_mass_le_low489b (N := N) (Y := localization N η)
        (H := windowLength N η) (B := arcExponent η A) (q := q) hq hYpos hLpos hqB hδc hc2
      linarith [h1, hcmp hqB]
    · have hzero : principalArcMass N (localization N η) (windowLength N η) (arcExponent η A) q = 0 := by
        have hgt : 1 / ((q : ℝ) * fareyOrder (windowLength N η)) <
            Real.log N ^ (2 * arcExponent η A) / ((q : ℝ) * localization N η) := not_le.mp hδc
        have hemp : puncturedEnvelope N (localization N η) (windowLength N η)
            (arcExponent η A) q = ∅ := by
          unfold puncturedEnvelope
          rw [if_pos hqB]
          ext t
          simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
          rintro ⟨⟨h1, h2⟩, h3⟩
          exact h3 ⟨by linarith [hgt, h1], by linarith [hgt, h2]⟩
        unfold principalArcMass
        rw [hemp]
        simp
      rw [hzero]
      have : (0:ℝ) ≤ 4 * localization N η / Real.log N ^ (2 * A + 3) := by positivity
      linarith
  · have hqLB : Real.log N ^ arcExponent η A < (q : ℝ) := not_le.mp hqB
    have hφ : Real.log N ^ (2 * A + 3) ≤ (Nat.totient q : ℝ) ^ 2 := by
      have ht := totient_sq_bound489b q hq
      have hPP : Real.log N ^ (2 * A + 3) * Real.log N ^ (2 * A + 3) ≤
          Real.log N ^ arcExponent η A := by
        rw [← Real.rpow_add hLpos]
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hexpB2])
      have h1 : Real.log N ^ (2 * A + 3) * Real.log N ^ (2 * A + 3) <
          2 * (Nat.totient q : ℝ) ^ 2 := by linarith [hPP, hqLB, ht]
      have ht0 : (0 : ℝ) ≤ (Nat.totient q : ℝ) ^ 2 := by positivity
      nlinarith [h1, hP3, ht0]
    have h1 := unpunctured_mass_le_high489b (N := N) (Y := localization N η)
      (H := windowLength N η) (B := arcExponent η A) (q := q) (E := 2 * A + 3)
      hq hYpos hY1 hLpos (by linarith : 0 < fareyOrder (windowLength N η)) hqB hc2 hφ
    linarith [h1]


/-- LEAF. Page 47 displays 17 to 20: discard the bad characters using their
large modulus, their density and Parseval. The good character energy is
retained as a variable V, without estimating it. CONDITIONAL ON the two inputs. -/
theorem remainder_to_good
    (hzero : CharacterZeroFreeRegion) (hdensity : FixedModulusDensity) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℝ, N₀ ≤ N → ∀ V : ℝ, 0 ≤ V →
      (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder (windowLength N η) →
        goodEnergy q N (localization N η) (windowLength N η) (arcExponent η A) ≤ V) →
      ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder (windowLength N η) →
        1 ≤ a → a ≤ q → Nat.Coprime a q →
        remainderArcMass N (localization N η) (windowLength N η) (arcExponent η A) q a ≤
          C * (V + localization N η / Real.log N ^ (2 * A + 3)) := by sorry

/-- LEAF. Pages 47 and 48 displays 21 to 26: the short character energy
reduction before the final logarithmic parameter choice. U bounds each
value of the last supremum in display 26. CONDITIONAL ON the cited inputs.
The explicit formula to zero sum step remains inside this leaf. The
variable window reduction is a separate input from display 24. -/
theorem good_character_envelope
    (hdensity : FixedModulusDensity) (hgallagher : CharacterGallagher)
    (hexplicit : CharacterExplicitFormula) (hdyadic : DyadicCharacterReduction) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℝ, N₀ ≤ N → ∀ U : ℝ, 0 ≤ U →
      (∀ σ : ℝ, 1 / 2 ≤ σ →
        σ ≤ 1 - 2 * arcExponent η A * Real.log (Real.log N) / Real.log N →
        localization N η ^ (1 - η / 3 * (1 - σ)) ≤ U) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder (windowLength N η) →
        goodEnergy q N (localization N η) (windowLength N η) (arcExponent η A) ≤
          C * (Real.log N ^ (20 : ℕ) * U +
            localization N η / Real.log N ^ (2 * A + 3)) := by sorry

#print axioms fareyOrder
#print axioms puncturedEnvelope
#print axioms principalArcMass
#print axioms remainderArcMass
#print axioms goodCharacters
#print axioms goodEnergy
#print axioms farey_local_reduction
#print axioms principal_arc_bound
#print axioms remainder_to_good
#print axioms good_character_envelope
end
end LeanLab.Languasco2004.Decomp489b
