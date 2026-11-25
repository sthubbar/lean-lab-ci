/-
P0069 Baker Harman Pintz 1997, Section 5, pages 50 to 53.
CLOUD S130 split of DecompC165b.CoprimeTwinS72.section5_weights_coprime. The lab's Section 5
weights are explicit: b0 is LowerShortC165.lowerShortWeight, page 51, and b1 is
DecompC165d.upperNormCoeff, page 53. The construction proofs of DecompC165d.lower_short_weight
and DecompC165d.upper_short_weight_of_slack_leaf are repeated here with those explicit
weights, so the only new steps are the two support facts of the raw coefficients, both
PROVED here: every
term of the page 51 and page 53 coefficients is a rough number indicator with sifting level
at least Y to the power c1, c1 = 1/15 + 7 θ2/15 - ε, about 1/8, while Q is below Y to the
power θ2/2, about 1/16.
AI wrote the Lean code. CLOUD S130. Goldbach is open.
-/
import LeanLab.BHP1997.Theorem1CoprimeTwinS72
import LeanLab.BHP1997.DecompC165d

namespace LeanLab.BHP1997.S130CoprimeWeights
open Classical Complex Decomp132 DecompC165b DecompC165d
open LeanLab.BHP1997.Theorem1CoprimeTwinS72

/-- Page 53, a prime factor of n other than p1 is a prime factor of n / p1. -/
theorem mem_primeFactors_div {n p1 r : ℕ} (hp1 : p1 ∈ n.primeFactors)
    (hr : r ∈ n.primeFactors) (hne : r ≠ p1) : r ∈ (n / p1).primeFactors := by
  have hp' := Nat.mem_primeFactors.mp hp1
  have hr' := Nat.mem_primeFactors.mp hr
  have hn : n = p1 * (n / p1) := (Nat.mul_div_cancel' hp'.2.1).symm
  refine Nat.mem_primeFactors.mpr ⟨hr'.1, ?_, ?_⟩
  · have h1 : r ∣ p1 * (n / p1) := hn ▸ hr'.2.1
    rcases (Nat.Prime.dvd_mul hr'.1).mp h1 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr'.1 hp'.1).mp h) hne
    · exact h
  · intro h0
    rw [h0, mul_zero] at hn
    exact hp'.2.2 hn

/-- Page 53, ψ(n, w) vanishes when n has a prime factor below w. -/
theorem upperRough_eq_zero {n p : ℕ} {w : ℝ} (hp : p ∈ n.primeFactors) (hpw : (p : ℝ) < w) :
    upperRough n w = 0 := by
  unfold upperRough
  rw [if_neg]
  intro h
  linarith [h p hp]

/-- Page 3 and page 53: the Farey order Q is below Y to the power c1, since Q is at most
Y to the power θ2/2 over 2 and θ2/2 < c1. -/
theorem order_lt_c1 {ε x : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) (hY : 1 ≤ x ^ (11 / 20 + ε)) :
    (Section2MS.order512 ε x : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε := by
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := by linarith
  have hfl : (Section2MS.order512 ε x : ℝ) ≤
      ((x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) / 2 := by
    unfold Section2MS.order512 Section2MS.length512
    exact Nat.floor_le (by positivity)
  rw [← Real.rpow_mul hY0] at hfl
  have h1 : (x ^ (11 / 20 + ε)) ^ ((2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) * (1 / 2)) ≤
      (x ^ (11 / 20 + ε)) ^ upperC1 ε :=
    Real.rpow_le_rpow_of_exponent_le hY (by unfold upperC1; norm_num; linarith)
  have h2 : 0 < (x ^ (11 / 20 + ε)) ^ upperC1 ε := Real.rpow_pos_of_pos (by linarith) _
  linarith

/-- Page 51: a prime p dividing m but not the product P of the removed primes divides
m / P. -/
theorem prime_dvd_div_of_not_dvd {p m P : ℕ} (hp : p.Prime) (hpm : p ∣ m) (hP : P ∣ m)
    (hpP : ¬ p ∣ P) : p ∣ m / P := by
  have hn : m = P * (m / P) := (Nat.mul_div_cancel' hP).symm
  have h1 : p ∣ P * (m / P) := hn ▸ hpm
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
  · exact absurd h hpP
  · exact h

/-- Page 51: a prime below every prime of a list of primes does not divide one of them. -/
theorem prime_not_dvd_of_lt {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    ¬ p ∣ r := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq hp hr).mp h
  omega

/-- Page 51 display 5.15: ψ(n, r) vanishes when a prime p < r divides n. -/
theorem rough_eq_zero {n r p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hpr : p < r) :
    LowerShortC165.rough n r = 0 := by
  unfold LowerShortC165.rough
  rw [if_neg]
  intro h
  have := h p hp hpn
  omega

/-- Pages 50 and 51: a prime whose exponent β = log r / log Z is at least c1 is at least
Z to the power c1. -/
theorem le_of_expo {ε x c : ℝ} {r : ℕ} (hZ : 1 < LowerShortC165.scaleZ ε x) (hr : 0 < r)
    (h : c ≤ LowerShortC165.expo ε x r) :
    LowerShortC165.scaleZ ε x ^ c ≤ (r : ℝ) := by
  unfold LowerShortC165.expo at h
  have hl : 0 < Real.log (LowerShortC165.scaleZ ε x) := Real.log_pos hZ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h2 : c * Real.log (LowerShortC165.scaleZ ε x) ≤ Real.log r := by
    rwa [le_div_iff₀ hl] at h
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos (by linarith) _) hr',
    Real.log_rpow (by linarith)]
  exact h2

/-- P0069 page 50 display 5.15 and page 51, the support of the raw lower coefficient:
the prime term and every deleted term of E2 and E4 carries the indicator ψ(n, p) with p at
least Z to the power c1, so for large x the raw coefficient vanishes on m in J sharing a
factor with some q ≤ Q, since Q is below Y to the power θ2/2 and c1 exceeds θ2/2.
PROVED. -/
theorem lower_raw_rough_support {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m ∈ rightInterval ε x,
      ∀ q : ℕ, 1 ≤ q → q ≤ Section2MS.order512 ε x → Nat.gcd m q ≠ 1 →
        LowerShortC165.rawLower ε x m = 0 := by
  refine ⟨1, fun x hx m hm q hq hqQ hg => ?_⟩
  have hY : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx (by linarith)
  have hQ := order_lt_c1 hε8 hY
  have hZ : 1 < LowerShortC165.scaleZ ε x := by
    unfold LowerShortC165.scaleZ LowerShortC165.shortY
    linarith
  have hc1 : (0 : ℝ) ≤ upperC1 ε := by unfold upperC1; norm_num; linarith
  have hYZ : (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ LowerShortC165.scaleZ ε x ^ upperC1 ε := by
    apply Real.rpow_le_rpow (by linarith) _ hc1
    unfold LowerShortC165.scaleZ LowerShortC165.shortY
    linarith
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
  have hpm : p ∣ m := hpd.trans (Nat.gcd_dvd_left m q)
  have hpq : p ≤ q := Nat.le_of_dvd hq (hpd.trans (Nat.gcd_dvd_right m q))
  have hpY : (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε := by
    have h1 : (p : ℝ) ≤ q := by exact_mod_cast hpq
    have h2 : (q : ℝ) ≤ Section2MS.order512 ε x := by exact_mod_cast hqQ
    linarith
  have hpZ : (p : ℝ) < LowerShortC165.scaleZ ε x ^ upperC1 ε := lt_of_lt_of_le hpY hYZ
  -- the prime term: m > Y > Y ^ c1 > p, so m is not prime
  have hW : primeWeight m = 0 := by
    unfold primeWeight
    rw [if_neg]
    intro hmp
    have hpe : p = m := ((Nat.prime_dvd_prime_iff_eq hp hmp).mp hpm)
    have hmY : x ^ (11 / 20 + ε) < (m : ℝ) :=
      (Nat.floor_lt (by linarith)).mp (Finset.mem_Ioc.mp hm).1
    have hc1' : upperC1 ε ≤ 1 := by unfold upperC1; norm_num; linarith
    have hY1 : (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ x ^ (11 / 20 + ε) :=
      Real.rpow_le_self_of_one_le hY hc1'
    have : (p : ℝ) = m := by exact_mod_cast hpe
    linarith
  -- the E2 terms: p2 ≥ Z ^ c1 > p, and ψ(m / (p1 p2), p2) = 0
  have h2 : LowerShortC165.lowerTwoTerms ε x m = 0 := by
    unfold LowerShortC165.lowerTwoTerms
    apply Finset.sum_eq_zero
    intro p1 _
    apply Finset.sum_eq_zero
    intro p2 _
    split_ifs with hc
    · obtain ⟨hp1, hp2, h21, hdvd, hdisc⟩ := hc
      have hb := le_of_expo hZ hp2.pos hdisc.1
      have hpp2 : p < p2 := by
        have : (p : ℝ) < p2 := by unfold upperC1 at hpZ; linarith
        exact_mod_cast this
      have hnd : ¬ p ∣ p1 * p2 := by
        intro h
        rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact prime_not_dvd_of_lt hp hp1 (by omega) h
        · exact prime_not_dvd_of_lt hp hp2 hpp2 h
      exact rough_eq_zero hp (prime_dvd_div_of_not_dvd hp hpm hdvd hnd) hpp2
    · rfl
  -- the E4 terms: p4 ≥ Z ^ c1 > p, and ψ(m / (p1 p2 p3 p4), p4) = 0
  have h4 : LowerShortC165.lowerFourTerms ε x m = 0 := by
    unfold LowerShortC165.lowerFourTerms
    apply Finset.sum_eq_zero
    intro p1 _
    apply Finset.sum_eq_zero
    intro p2 _
    apply Finset.sum_eq_zero
    intro p3 _
    apply Finset.sum_eq_zero
    intro p4 _
    split_ifs with hc
    · obtain ⟨hp1, hp2, hp3, hp4, h21, h32, h43, hdvd, hreg⟩ := hc
      have hb := le_of_expo hZ hp4.pos hreg.1
      have hpp4 : p < p4 := by
        have : (p : ℝ) < p4 := by unfold upperC1 at hpZ; linarith
        exact_mod_cast this
      have hnd : ¬ p ∣ p1 * p2 * p3 * p4 := by
        intro h
        rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
            · exact prime_not_dvd_of_lt hp hp1 (by omega) h
            · exact prime_not_dvd_of_lt hp hp2 (by omega) h
          · exact prime_not_dvd_of_lt hp hp3 (by omega) h
        · exact prime_not_dvd_of_lt hp hp4 hpp4 h
      exact rough_eq_zero hp (prime_dvd_div_of_not_dvd hp hpm hdvd hnd) hpp4
    · rfl
  unfold LowerShortC165.rawLower
  rw [hW, h2, h4]
  ring

/-- P0069 page 53, the support of the raw upper coefficient g - h + j - kept part of k:
each of the four terms carries ψ(n, w) with w at least Y to the power c1 and its primes p1,
p2, p3 at least Y to the power c1, so for large x the raw coefficient vanishes on m in J
sharing a factor with some q ≤ Q. PROVED. -/
theorem upper_raw_rough_support {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m ∈ rightInterval ε x,
      ∀ q : ℕ, 1 ≤ q → q ≤ Section2MS.order512 ε x → Nat.gcd m q ≠ 1 →
        upperRawWeight ε (x ^ (11 / 20 + ε)) m = 0 := by
  refine ⟨1, fun x hx m hm q hq hqQ hg => ?_⟩
  have hY : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx (by linarith)
  have hQ := order_lt_c1 hε8 hY
  set Y := x ^ (11 / 20 + ε) with hYdef
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
  have hpm' : p ∣ m := hpd.trans (Nat.gcd_dvd_left m q)
  have hpq : p ≤ q := Nat.le_of_dvd hq (hpd.trans (Nat.gcd_dvd_right m q))
  have hm0 : m ≠ 0 := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  have hpm : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm', hm0⟩
  have hpY : (p : ℝ) < Y ^ upperC1 ε := by
    have h1 : (p : ℝ) ≤ q := by exact_mod_cast hpq
    have h2 : (q : ℝ) ≤ Section2MS.order512 ε x := by exact_mod_cast hqQ
    linarith
  have hG : upperG ε Y m = 0 := upperRough_eq_zero hpm hpY
  have hH : upperH ε Y m = 0 := by
    unfold upperH
    apply Finset.sum_eq_zero
    intro p1 hp1
    have hp1' := Finset.mem_filter.mp hp1
    have hne1 : p ≠ p1 := by rintro rfl; linarith [hp1'.2.1]
    exact upperRough_eq_zero (mem_primeFactors_div hp1'.1 hpm hne1) hpY
  have hJ : upperJ ε Y m = 0 := by
    unfold upperJ
    apply Finset.sum_eq_zero
    intro p1 hp1
    have hp1' := Finset.mem_filter.mp hp1
    have hne1 : p ≠ p1 := by rintro rfl; linarith [hp1'.2.1]
    have hpm1 := mem_primeFactors_div hp1'.1 hpm hne1
    apply Finset.sum_eq_zero
    intro p2 hp2
    have hp2' := Finset.mem_filter.mp hp2
    have hne2 : p ≠ p2 := by rintro rfl; linarith [hp2'.2.1]
    exact upperRough_eq_zero (mem_primeFactors_div hp2'.1 hpm1 hne2) hpY
  have hK : upperKept ε Y m = 0 := by
    unfold upperKept
    apply Finset.sum_eq_zero
    intro p1 hp1
    have hp1' := Finset.mem_filter.mp hp1
    have hne1 : p ≠ p1 := by rintro rfl; linarith [hp1'.2.1]
    have hpm1 := mem_primeFactors_div hp1'.1 hpm hne1
    apply Finset.sum_eq_zero
    intro p2 hp2
    have hp2' := Finset.mem_filter.mp hp2
    have hne2 : p ≠ p2 := by rintro rfl; linarith [hp2'.2.1]
    have hpm2 := mem_primeFactors_div hp2'.1 hpm1 hne2
    apply Finset.sum_eq_zero
    intro p3 hp3
    have hp3' := Finset.mem_filter.mp hp3
    have hne3 : p ≠ p3 := by rintro rfl; linarith [hp3'.2.1]
    have hpm3 := mem_primeFactors_div hp3'.1 hpm2 hne3
    split_ifs
    · exact upperRough_eq_zero hpm3 (lt_of_lt_of_le hpY hp3'.2.1)
    · rfl
  unfold upperRawWeight
  rw [hG, hH, hJ, hK]
  ring

/-- Page 51: the normalized lower weight b0 has the coprimality support. PROVED from
lower_raw_rough_support. -/
theorem lower_coprime_support (ω : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    CoprimeSupport ε (fun x m => (LowerShortC165.lowerShortWeight ω ε x m : ℂ)) := by
  obtain ⟨C, hC⟩ := lower_raw_rough_support hε hε8
  refine ⟨C, fun x hx m hm q hq hqQ hg => ?_⟩
  have h0 := hC x hx m hm q hq hqQ hg
  simp only [LowerShortC165.lowerShortWeight, h0, mul_zero, Complex.ofReal_zero]

/-- Page 53: the normalized upper weight b1 has the coprimality support, for every
rescaling factor lam. PROVED from upper_raw_rough_support. -/
theorem upper_coprime_support (lam : ℝ → ℕ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 10 ^ 8) :
    CoprimeSupport ε (fun x m => (upperNormCoeff ε lam x m : ℂ)) := by
  obtain ⟨C, hC⟩ := upper_raw_rough_support hε hε8
  refine ⟨C, fun x hx m hm q hq hqQ hg => ?_⟩
  have h0 := hC x hx m hm q hq hqQ hg
  simp only [upperNormCoeff, h0, mul_zero, ite_self, Complex.ofReal_zero]

/-- Pages 43 to 52: twin of DecompC165d.lower_short_weight with the explicit weight
LowerShortC165.lowerShortWeight and its coprimality support. Same proof as
DecompC165d.lower_short_weight_analytic and DecompC165d.lower_short_weight. CONDITIONAL. -/
theorem lower_short_weight_coprime (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ RightConditions ε B v0 b0 ∧
        (∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m) ∧
        CoprimeSupport ε (fun x m => (b0 x m : ℂ)) := by
  obtain ⟨ω, hω, hz⟩ := Task308.buchstab_model_exists
  refine ⟨4, 1/10^8, by norm_num, ?_⟩
  intro B ε hB hε hεη
  have hε8 : ε ≤ 1/10^8 := hεη.le
  refine ⟨LowerShortC165.lowerV0 ω ε, LowerShortC165.lowerShortWeight ω ε,
    lower_density_of_e2_bound hω hz hε.le hε8
      (lower_two_integral_bound hω hz hε.le hε8) le_rfl,
    ⟨LowerShortC165.lowerShortWeight_divisor_bound ω ε hB,
      LowerShortC165.lower_short_distribution ω hω hz hε hε8,
      LowerShortC165.lower_exceptional_mean_square h4 h9 ω hω hz hε hε8⟩,
    ⟨0, fun x _ m _ => LowerShortC165.lowerShortWeight_le_primeWeight ω ε x m⟩,
    lower_coprime_support ω hε hε8⟩

/-- Page 53: twin of DecompC165d.upper_short_weight with the explicit weight upperNormCoeff
and its coprimality support. Same proof as DecompC165d.upper_short_weight_of_slack_leaf.
CONDITIONAL. -/
theorem upper_short_weight_coprime (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
        v1 < 2.2 ∧ RightConditions ε B v1 b1 ∧
        (∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m) ∧
        CoprimeSupport ε (fun x m => (b1 x m : ℂ)) := by
  obtain ⟨ω, hω, hz⟩ := Task308.buchstab_model_exists
  obtain ⟨B0, η, hη, hrange⟩ := upper_thresholds
  refine ⟨B0, η, hη, fun B ε hB hε hεη => ?_⟩
  obtain ⟨hB0, hε0, hε8⟩ := hrange B ε hB hε hεη
  set P := ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
    upperDeletedIntegral ω ε with hP
  have hP22 : P < 2.2 := upper_density_bound hω hz hε0.le hε8 le_rfl
  have hδ : 0 < (2.2 - P) / 2 := by linarith
  obtain ⟨lam, Λ, hlam, ⟨X, hX⟩, hdist, hms⟩ :=
    upper_normalized_raw_conditions_slack h4 h9 hω hz hε0 hε8 hδ
  refine ⟨P + (2.2 - P) / 2, upperNormCoeff ε lam, by linarith,
    Task308.right_conditions_of_parts (upper_norm_coeff_divisor_bound hB0 hε0 hε8 hlam)
      hdist hms, ⟨max X 4, fun x hx m hm => ?_⟩, upper_coprime_support lam hε0 hε8⟩
  exact upper_prime_le_norm_coeff hε0 (le_of_max_le_right hx) hm
    (hX x (le_of_max_le_left hx) m hm)

/-- Pages 43 to 53: exactly the statement of
DecompC165b.CoprimeTwinS72.section5_weights_coprime, from the two twins above, combined as in
DecompC165d.section5_weights. No new sorry: CONDITIONAL only on the existing Section 5
leaves already used by DecompC165d.section5_weights, see #print axioms in the build log. -/
theorem section5_weights_coprime_of_s130 :
    type_of% @DecompC165b.CoprimeTwinS72.section5_weights_coprime := by
  intro h4 h9
  obtain ⟨B0, η0, hη0, h0⟩ := lower_short_weight_coprime h4 h9
  obtain ⟨B1, η1, hη1, h1⟩ := upper_short_weight_coprime h4 h9
  refine ⟨max B0 B1, min η0 η1, lt_min hη0 hη1, ?_⟩
  intro B ε hB hε hεη
  obtain ⟨v0, b0, hv0, hb0, ⟨X0, hs0⟩, hc0⟩ := h0 B ε
    (le_trans (le_max_left _ _) hB) hε (lt_of_lt_of_le hεη (min_le_left _ _))
  obtain ⟨v1, b1, hv1, hb1, ⟨X1, hs1⟩, hc1⟩ := h1 B ε
    (le_trans (le_max_right _ _) hB) hε (lt_of_lt_of_le hεη (min_le_right _ _))
  have hsand : ∀ x : ℝ, max X0 X1 ≤ x → ∀ m ∈ rightInterval ε x,
      b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m := fun x hx m hm =>
    ⟨hs0 x (le_trans (le_max_left _ _) hx) m hm,
      hs1 x (le_trans (le_max_right _ _) hx) m hm⟩
  have hmono : v0 ≤ v1 := DecompC165b.right_density_mono hε hb0 hb1
    ⟨max X0 X1, fun x hx m hm => (hsand x hx m hm).1.trans (hsand x hx m hm).2⟩
  exact ⟨v0, v1, b0, b1, hv0, hmono, hv1, hb0, hb1, ⟨max X0 X1, hsand⟩, hc0, hc1⟩

end LeanLab.BHP1997.S130CoprimeWeights
