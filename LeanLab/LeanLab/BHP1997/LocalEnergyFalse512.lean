/-
P0069 Baker Harman Pintz 1997, Section 2, pages 9 and 10, display 2.11, read against
the hypotheses of Theorem 2 on page 3.
The lab leaf `leaf_minor_local_energy512` asserts display 2.11 for every sequence b
that satisfies the hypotheses of Theorem 2 as the lab states them. Those hypotheses
test b only against Dirichlet characters, and a character vanishes on every integer
sharing a factor with its modulus. The sequence b(m) = e(m(1/4 + δ/2)) on even m and
0 on odd m, with δ = Y^(-1/2), satisfies every hypothesis and has a local energy of
size Y near the point 3/4 - δ/2, which lies on the minor arcs. So the leaf is false
as stated. This file proves the hypotheses side and assembles the refutation; the
energy lower bound is `counter_energy_lower512` in `LocalEnergyFalse512a`.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.LocalEnergyFalse512a

namespace LeanLab.BHP1997.Section2MS
open Classical Complex Thm2 MeasureTheory Set
open scoped ComplexConjugate

/-- P0069 page 3, Theorem 2, hypothesis on b: the unimodular phase e(r) has norm one. -/
private theorem norm_phase512 (r : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
  have h : (2 * Real.pi * Complex.I * (r : ℂ) : ℂ) =
      ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- P0069 page 3, hypotheses iii and iv of Theorem 2 for the counterexample: a bounded
sequence with f(m + p) = ρ f(m) and |1 - ρ| ≥ 1 has every interval sum of norm at
most 2p, by comparing the sum with its shift by p. -/
private theorem quasi_periodic_sum512 (f : ℕ → ℂ) (p : ℕ) (ρ : ℂ)
    (hf : ∀ m, ‖f m‖ ≤ 1) (hρ : ∀ m, f (m + p) = ρ * f m) (h1 : 1 ≤ ‖1 - ρ‖)
    (S : Finset ℕ) (hS : ∀ a ∈ S, ∀ c ∈ S, ∀ k, a ≤ k → k ≤ c → k ∈ S) :
    ‖∑ m ∈ S, f m‖ ≤ 2 * p := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = S.map (addRightEmbedding p) := ⟨_, rfl⟩
  have hsum : ∑ m ∈ T, f m = ρ * ∑ m ∈ S, f m := by
    rw [hT, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [addRightEmbedding_apply]
    exact hρ m
  have hdiff : (1 - ρ) * ∑ m ∈ S, f m = ∑ m ∈ S \ T, f m - ∑ m ∈ T \ S, f m := by
    rw [Finset.sum_sdiff_sub_sum_sdiff, hsum]; ring
  have hA : S \ T ⊆ Finset.Ico (S.min' hne) (S.min' hne + p) := by
    intro m hm
    rw [Finset.mem_sdiff] at hm
    rw [Finset.mem_Ico]
    have hmin := Finset.min'_le S m hm.1
    refine ⟨hmin, ?_⟩
    by_contra hlt
    push Not at hlt
    apply hm.2
    rw [hT, Finset.mem_map]
    refine ⟨m - p, hS _ (Finset.min'_mem S hne) m hm.1 (m - p) (by omega) (by omega), ?_⟩
    rw [addRightEmbedding_apply]
    omega
  have hB : T \ S ⊆ Finset.Ioc (S.max' hne) (S.max' hne + p) := by
    intro m hm
    rw [Finset.mem_sdiff, hT, Finset.mem_map] at hm
    obtain ⟨⟨k, hk, hkm⟩, hmS⟩ := hm
    rw [addRightEmbedding_apply] at hkm
    rw [Finset.mem_Ioc]
    have hkmax := Finset.le_max' S k hk
    refine ⟨?_, by omega⟩
    by_contra hle
    push Not at hle
    exact hmS (hS k hk _ (Finset.max'_mem S hne) m (by omega) hle)
  have hcA : ((S \ T).card : ℝ) ≤ p := by
    have h := Finset.card_le_card hA
    rw [Nat.card_Ico] at h
    exact_mod_cast (by omega : (S \ T).card ≤ p)
  have hcB : ((T \ S).card : ℝ) ≤ p := by
    have h := Finset.card_le_card hB
    rw [Nat.card_Ioc] at h
    exact_mod_cast (by omega : (T \ S).card ≤ p)
  have hbound : ∀ U : Finset ℕ, ‖∑ m ∈ U, f m‖ ≤ U.card := by
    intro U
    calc ‖∑ m ∈ U, f m‖ ≤ ∑ m ∈ U, ‖f m‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ U, (1 : ℝ) := Finset.sum_le_sum (fun m _ => hf m)
      _ = U.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hmain : ‖1 - ρ‖ * ‖∑ m ∈ S, f m‖ ≤ 2 * p := by
    rw [← norm_mul, hdiff]
    have hA' := hbound (S \ T)
    have hB' := hbound (T \ S)
    calc ‖∑ m ∈ S \ T, f m - ∑ m ∈ T \ S, f m‖
        ≤ ‖∑ m ∈ S \ T, f m‖ + ‖∑ m ∈ T \ S, f m‖ := norm_sub_le _ _
      _ ≤ 2 * p := by linarith
  exact le_trans (le_mul_of_one_le_left (norm_nonneg _) h1) hmain

/-- P0069 page 3, hypotheses iii and iv of Theorem 2 for the counterexample
b(m) = e(m(1/4 + δ/2)) on even m: every character sum of b over an interval has norm
at most 4q when qδ ≤ 1/8. For even q the summand vanishes, since a character mod q
vanishes on even m. For odd q the summand f has f(m + 2q) = -e(qδ) f(m). -/
private theorem phase_sum_bound512 (δ : ℝ) (hδ : 0 ≤ δ) (q : ℕ) (hq : 1 ≤ q)
    (hqδ : (q : ℝ) * δ ≤ 1 / 8) (χ : DirichletCharacter ℂ q) (S : Finset ℕ)
    (hS : ∀ a ∈ S, ∀ c ∈ S, ∀ k, a ≤ k → k ≤ c → k ∈ S) :
    ‖∑ m ∈ S, (if Even m then Complex.exp (2 * Real.pi * Complex.I *
        (((m : ℝ) * (1 / 4 + δ / 2) : ℝ) : ℂ)) else 0) * χ (m : ZMod q)‖ ≤ 4 * q := by
  rcases Nat.even_or_odd q with hqe | hqo
  · rw [Finset.sum_eq_zero]
    · rw [norm_zero]; positivity
    intro m _
    by_cases hm : Even m
    · have hnu : ¬ IsUnit ((m : ℕ) : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime]
        exact Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2) hm.two_dvd hqe.two_dvd
      rw [MulChar.map_nonunit χ hnu, mul_zero]
    · rw [ite_eq_right hm, zero_mul]
  · obtain ⟨f, hf⟩ : ∃ f : ℕ → ℂ, ∀ m : ℕ, f m =
        (if Even m then Complex.exp (2 * Real.pi * Complex.I *
          (((m : ℝ) * (1 / 4 + δ / 2) : ℝ) : ℂ)) else 0) * χ (m : ZMod q) := ⟨_, fun _ => rfl⟩
    rw [Finset.sum_congr rfl (fun m _ => (hf m).symm)]
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℂ, ρ = Complex.exp (2 * Real.pi * Complex.I *
        ((2 * (q : ℝ) * (1 / 4 + δ / 2) : ℝ) : ℂ)) := ⟨_, rfl⟩
    have hf1 : ∀ m, ‖f m‖ ≤ 1 := by
      intro m
      rw [hf m, norm_mul]
      by_cases hm : Even m
      · rw [ite_eq_left hm, norm_phase512, one_mul]
        exact DirichletCharacter.norm_le_one χ _
      · rw [ite_eq_right hm, norm_zero, zero_mul]
        exact zero_le_one
    have hshift : ∀ m, f (m + 2 * q) = ρ * f m := by
      intro m
      have he : Even (m + 2 * q) ↔ Even m := by
        rw [Nat.even_iff, Nat.even_iff]; omega
      have hc : ((m + 2 * q : ℕ) : ZMod q) = (m : ZMod q) := by
        rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]
      rw [hf, hf, hc]
      by_cases hm : Even m
      · rw [ite_eq_left (he.mpr hm), ite_eq_left hm, hρdef, ← mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      · rw [ite_eq_right (fun h => hm (he.mp h)), ite_eq_right hm, zero_mul, mul_zero]
    have hre : ρ.re = -Real.cos (2 * Real.pi * (q * δ)) := by
      have h : (2 * Real.pi * Complex.I * ((2 * (q : ℝ) * (1 / 4 + δ / 2) : ℝ) : ℂ) : ℂ) =
          ((2 * Real.pi * (q * δ) + q * Real.pi : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hρdef, h, Complex.exp_ofReal_mul_I_re, Real.cos_add_nat_mul_pi, hqo.neg_one_pow]
      ring
    have hcos : 0 ≤ Real.cos (2 * Real.pi * (q * δ)) := by
      apply Real.cos_nonneg_of_mem_Icc
      have hpi := Real.pi_pos
      have h0 : 0 ≤ (q : ℝ) * δ := mul_nonneg (Nat.cast_nonneg q) hδ
      have h2 := mul_le_mul_of_nonneg_left hqδ hpi.le
      have h3 := mul_nonneg hpi.le h0
      constructor <;> linarith
    have hnorm : 1 ≤ ‖1 - ρ‖ := by
      calc (1 : ℝ) ≤ (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re, hre]; linarith
        _ ≤ ‖1 - ρ‖ := Complex.re_le_norm _
    have key := quasi_periodic_sum512 f (2 * q) ρ hf1 hshift hnorm S hS
    calc ‖∑ m ∈ S, f m‖ ≤ 2 * ((2 * q : ℕ) : ℝ) := key
      _ = 4 * q := by push_cast; ring

/-- P0069 page 3, hypothesis iv of Theorem 2: there are at most q Dirichlet characters
mod q, so the sum over characters has at most q terms. -/
private theorem card_characters_le512 (q : ℕ) (hq : 1 ≤ q) :
    ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) ≤ q := by
  have : NeZero q := ⟨by omega⟩
  have h : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  rw [h]
  exact_mod_cast Nat.totient_le q

/-- P0069 page 3, the ranges q ≤ (log x)^A and q ≤ Q of Theorem 2: every power of
log x is eventually below any positive multiple of any positive power of x. -/
private theorem log_pow_le_rpow512 (k η c : ℝ) (hη : 0 < η) (hc : 0 < c) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Real.log x ^ k ≤ c * x ^ η := by
  have h := (isLittleO_log_rpow_rpow_atTop k hη).bound hc
  rw [Filter.eventually_atTop] at h
  obtain ⟨a, ha⟩ := h
  refine ⟨max a 0, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hx
  have h2 := ha x (le_trans (le_max_left _ _) hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 η)] at h2
  exact le_trans (le_abs_self _) h2

/-- P0069 page 3, the sizes in Theorem 2 for large x, with Y = x^θ₁, H = Y^θ₂ and
Q about H^(1/2)/2: a power of log x is below Y^(1/2)/8 and below H^(1/2)/160, and
4 H^(1/2) is below Y^(1/2). -/
private theorem large_x_facts512 (θ₁ θ₂ : ℝ) (h1 : 0 < θ₁) (h2 : 0 < θ₂) (h2' : θ₂ < 1)
    (A : ℝ) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      Real.log x ^ A ≤ 1 / 8 * (x ^ θ₁) ^ (1 / 2 : ℝ) ∧
      Real.log x ^ A ≤ 1 / 160 * ((x ^ θ₁) ^ θ₂) ^ (1 / 2 : ℝ) ∧
      4 * ((x ^ θ₁) ^ θ₂) ^ (1 / 2 : ℝ) ≤ (x ^ θ₁) ^ (1 / 2 : ℝ) := by
  obtain ⟨x₁, hx₁⟩ := log_pow_le_rpow512 A (θ₁ * (1 / 2)) (1 / 8)
    (mul_pos h1 (by norm_num)) (by norm_num)
  obtain ⟨x₂, hx₂⟩ := log_pow_le_rpow512 A (θ₁ * θ₂ * (1 / 2)) (1 / 160)
    (mul_pos (mul_pos h1 h2) (by norm_num)) (by norm_num)
  obtain ⟨x₃, hx₃⟩ := log_pow_le_rpow512 0 (θ₁ * (1 / 2) - θ₁ * θ₂ * (1 / 2)) (1 / 4)
    (by nlinarith) (by norm_num)
  refine ⟨max (max x₁ x₂) (max x₃ 2), le_trans (le_max_right _ _) (le_max_right _ _),
    fun x hx => ?_⟩
  have hxa : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc : x₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxd : 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxpos : 0 < x := by linarith
  have e1 : (x ^ θ₁) ^ (1 / 2 : ℝ) = x ^ (θ₁ * (1 / 2)) :=
    (Real.rpow_mul hxpos.le _ _).symm
  have e2 : ((x ^ θ₁) ^ θ₂) ^ (1 / 2 : ℝ) = x ^ (θ₁ * θ₂ * (1 / 2)) := by
    rw [← Real.rpow_mul hxpos.le, ← Real.rpow_mul hxpos.le]
  rw [e1, e2]
  refine ⟨hx₁ x hxa, hx₂ x hxb, ?_⟩
  have h := hx₃ x hxc
  rw [Real.rpow_zero] at h
  have hsplit : x ^ (θ₁ * (1 / 2)) =
      x ^ (θ₁ * θ₂ * (1 / 2)) * x ^ (θ₁ * (1 / 2) - θ₁ * θ₂ * (1 / 2)) := by
    rw [← Real.rpow_add hxpos]; congr 1; ring
  rw [hsplit]
  have hw : 0 ≤ x ^ (θ₁ * θ₂ * (1 / 2)) := Real.rpow_nonneg hxpos.le _
  nlinarith [mul_le_mul_of_nonneg_left h hw]

/-- P0069 page 3, hypothesis i of Theorem 2, for a = 0 and u = 0. -/
private theorem counter_hyp_i512 (ε : ℝ) (a : ℝ → ℕ → ℂ) (ha : ∀ x k, a x k = 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
        ‖∑ k ∈ (Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊).filter
            (fun k : ℕ => (k : ℝ) ≤ t),
          (a x k * χ (k : ZMod q) - delta χ * ((0 : ℝ) : ℂ) / Real.log x)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A _
  refine ⟨1, fun x hx q _ _ χ t _ => ?_⟩
  rw [Finset.sum_eq_zero, norm_zero]
  · exact mul_nonneg (mul_nonneg zero_le_one (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg (Real.log_nonneg hx) _)
  · intro k _
    rw [ha, Complex.ofReal_zero, mul_zero, zero_mul, zero_div, sub_zero]

/-- P0069 page 3, hypothesis ii of Theorem 2, the divisor bound with B = 0. -/
private theorem counter_hyp_ii512 (ε : ℝ) (a b : ℝ → ℕ → ℂ) (ha : ∀ x k, a x k = 0)
    (hb : ∀ (x : ℝ) (m : ℕ), b x m = if Even m then
      Complex.exp (2 * Real.pi * Complex.I *
        (((m : ℝ) * (1 / 4 + (x ^ (11 / 20 + ε)) ^ (-(1 / 2 : ℝ)) / 2) : ℝ) : ℂ)) else 0) :
    ∃ C : ℝ, ∀ (x : ℝ) (k : ℕ), ‖a x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (0 : ℝ) ∧
      ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (0 : ℝ) := by
  refine ⟨1, fun x k => ?_⟩
  rw [Real.rpow_zero, mul_one, ha, norm_zero, hb]
  refine ⟨zero_le_one, ?_⟩
  by_cases hk : Even k
  · rw [ite_eq_left hk, norm_phase512]
  · rw [ite_eq_right hk, norm_zero]
    exact zero_le_one

/-- P0069 page 3, hypothesis ii of Theorem 2, the sieve condition on a, for a = 0. -/
private theorem counter_hyp_iii512 (a : ℝ → ℕ → ℂ) (ha : ∀ x k, a x k = 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0 :=
  fun _ _ => ⟨0, fun x _ k _ => ha x k⟩

/-- P0069 page 3, hypothesis iii of Theorem 2, for the counterexample b and v = 0:
each character sum is at most 4q ≤ 4 (log x)^A, far below Y (log x)^(-A). -/
private theorem counter_hyp_iv512 (ε : ℝ) (hε : 0 < ε) (b : ℝ → ℕ → ℂ)
    (hb : ∀ (x : ℝ) (m : ℕ), b x m = if Even m then
      Complex.exp (2 * Real.pi * Complex.I *
        (((m : ℝ) * (1 / 4 + (x ^ (11 / 20 + ε)) ^ (-(1 / 2 : ℝ)) / 2) : ℝ) : ℂ)) else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
        t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊).filter
            (fun m : ℕ => (m : ℝ) ≤ t),
          (b x m * χ (m : ZMod q) -
            delta χ * ((0 : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A _
  obtain ⟨x₀, hx₀, hfacts⟩ := large_x_facts512 (11 / 20 + ε) (2 * (1 / 16 - 1 / 10 ^ 5))
    (by linarith) (by norm_num) (by norm_num) A
  refine ⟨x₀, fun x hx q hq hqA χ t _ => ?_⟩
  obtain ⟨hf1, -, -⟩ := hfacts x hx
  have hxpos : 0 < x := by linarith
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hxpos _
  have hΛinv : Real.log x ^ (-A) = (Real.log x ^ A)⁻¹ :=
    Real.rpow_neg (Real.log_nonneg (by linarith)) _
  simp only [hb, Complex.ofReal_zero, mul_zero, zero_div, sub_zero]
  rw [hΛinv]
  generalize x ^ (11 / 20 + ε) = Y at hf1 hYpos ⊢
  generalize Real.log x ^ A = Λ at hf1 hqA ⊢
  have hspos : 0 < Y ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hYpos _
  have hss : Y ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) = Y := by
    rw [← Real.rpow_add hYpos]; norm_num
  have hδ : Y ^ (-(1 / 2 : ℝ)) = (Y ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hYpos.le _
  generalize Y ^ (1 / 2 : ℝ) = s at hf1 hspos hss hδ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hΛpos : 0 < Λ := by linarith
  have hqδ : (q : ℝ) * Y ^ (-(1 / 2 : ℝ)) ≤ 1 / 8 := by
    rw [hδ, ← div_eq_mul_inv, div_le_iff₀ hspos]; linarith
  refine le_trans (phase_sum_bound512 (Y ^ (-(1 / 2 : ℝ))) (Real.rpow_nonneg hYpos.le _)
    q hq hqδ χ _ ?_) ?_
  · intro a ha c hc k hak hkc
    rw [Finset.mem_filter, Finset.mem_Ioc] at ha hc ⊢
    exact ⟨⟨lt_of_lt_of_le ha.1.1 hak, le_trans hkc hc.1.2⟩,
      le_trans (by exact_mod_cast hkc) hc.2⟩
  · rw [← div_eq_mul_inv, le_div_iff₀ hΛpos]
    have h1 : (q : ℝ) * Λ ≤ Λ * Λ := mul_le_mul_of_nonneg_right hqA hΛpos.le
    have h2 : Λ * Λ ≤ (1 / 8 * s) * (1 / 8 * s) :=
      mul_le_mul hf1 hf1 hΛpos.le (by positivity)
    have h3 : 2 * Y ≤ x₀ * Y := mul_le_mul_of_nonneg_right hx₀ hYpos.le
    nlinarith

/-- P0069 page 3, hypothesis iv of Theorem 2, for the counterexample b, v = 0 and no
exceptional characters: each window sum is at most 4q, there are at most q
characters and the y range has length 5Y/2, so the left side is at most 40 q³ Y,
far below (qQ)² Y (log x)^(-A) since Q is a power of x. -/
private theorem counter_hyp_v512 (ε : ℝ) (hε : 0 < ε) (b : ℝ → ℕ → ℂ)
    (hb : ∀ (x : ℝ) (m : ℕ), b x m = if Even m then
      Complex.exp (2 * Real.pi * Complex.I *
        (((m : ℝ) * (1 / 4 + (x ^ (11 / 20 + ε)) ^ (-(1 / 2 : ℝ)) / 2) : ℝ) : ℂ)) else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      q ≤ ⌊((x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) / 2⌋₊ →
      (((∅ : Finset (DirichletCharacter ℂ q)).card : ℝ) ≤
          C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ,
          ((q : ℝ) * (⌊((x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^
              (1 / 2 : ℝ) / 2⌋₊ : ℝ)) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * (q : ℝ) * (⌊((x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^
              (1 / 2 : ℝ) / 2⌋₊ : ℝ) / x ^ (11 / 20 + ε) →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ ∅,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                (b x m * χ (m : ZMod q) -
                  delta χ * ((0 : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
            C * ((q : ℝ) * (⌊((x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^
              (1 / 2 : ℝ) / 2⌋₊ : ℝ)) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
  intro A _
  obtain ⟨x₀, hx₀, hfacts⟩ := large_x_facts512 (11 / 20 + ε) (2 * (1 / 16 - 1 / 10 ^ 5))
    (by linarith) (by norm_num) (by norm_num) A
  refine ⟨x₀, fun x hx q hq hqQ => ?_⟩
  obtain ⟨-, hf2, hf3⟩ := hfacts x hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hxpos _
  refine ⟨?_, fun z _ _ => ?_⟩
  · rw [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg q) _))
      (Real.rpow_nonneg hlog.le _)
  have hΛinv : Real.log x ^ (-A) = (Real.log x ^ A)⁻¹ := Real.rpow_neg hlog.le _
  have hΛpos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlog _
  simp only [hb, Complex.ofReal_zero, mul_zero, zero_div, sub_zero, Finset.sdiff_empty]
  rw [hΛinv]
  generalize x ^ (11 / 20 + ε) = Y at hf2 hf3 hYpos hqQ ⊢
  generalize Real.log x ^ A = Λ at hf2 hΛpos ⊢
  have hspos : 0 < Y ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hYpos _
  have hδ : Y ^ (-(1 / 2 : ℝ)) = (Y ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hYpos.le _
  have hwnn : 0 ≤ (Y ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (Real.rpow_nonneg hYpos.le _) _
  generalize Y ^ (1 / 2 : ℝ) = s at hf3 hspos hδ
  generalize (Y ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) = w at hf2 hf3 hwnn hqQ ⊢
  have hQle : ((⌊w / 2⌋₊ : ℕ) : ℝ) ≤ w / 2 := Nat.floor_le (by linarith)
  have hQlt : w / 2 < ((⌊w / 2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hqQ' : (q : ℝ) ≤ ((⌊w / 2⌋₊ : ℕ) : ℝ) := by exact_mod_cast hqQ
  generalize ⌊w / 2⌋₊ = Q at hQle hQlt hqQ' ⊢
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqδ : (q : ℝ) * Y ^ (-(1 / 2 : ℝ)) ≤ 1 / 8 := by
    rw [hδ, ← div_eq_mul_inv, div_le_iff₀ hspos]; linarith
  have h40 : 40 * Λ ≤ Q := by linarith
  have hk : 40 * (q : ℝ) * Λ ≤ Q * Q := by
    have := mul_le_mul hqQ' h40 (by positivity) (by linarith)
    linarith
  have hqY : 0 ≤ (q : ℝ) ^ 2 * Y := mul_nonneg (sq_nonneg _) hYpos.le
  refine le_trans (Finset.sum_le_sum (g := fun _ => 40 * (q : ℝ) ^ 2 * Y) (fun χ _ => ?_)) ?_
  · refine le_trans (Real.le_norm_self _) (le_trans
      (intervalIntegral.norm_integral_le_of_norm_le_const (C := (4 * (q : ℝ)) ^ 2) ?_) ?_)
    · intro y _
      refine le_trans (le_of_eq (Real.norm_of_nonneg (sq_nonneg _)))
        (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
      refine phase_sum_bound512 (Y ^ (-(1 / 2 : ℝ))) (Real.rpow_nonneg hYpos.le _)
        q hq hqδ χ _ ?_
      intro a ha c hc k hak hkc
      rw [Finset.mem_filter, Finset.mem_Ioc] at ha hc ⊢
      exact ⟨⟨lt_of_lt_of_le ha.1.1 hak, le_trans hkc hc.1.2⟩,
        le_trans ha.2.1 (by exact_mod_cast hak), le_trans (by exact_mod_cast hkc) hc.2.2⟩
    · have habs : |3 * Y - Y / 2| = 5 / 2 * Y := by
        rw [abs_of_nonneg (by linarith)]; ring
      rw [habs]
      exact le_of_eq (by ring)
  · rw [Finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv, le_div_iff₀ hΛpos]
    have hcard := card_characters_le512 q hq
    calc ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) *
          (40 * (q : ℝ) ^ 2 * Y) * Λ
        ≤ (q : ℝ) * (40 * (q : ℝ) ^ 2 * Y) * Λ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (by linarith))
            hΛpos.le
      _ = (q : ℝ) ^ 2 * Y * (40 * (q : ℝ) * Λ) := by ring
      _ ≤ (q : ℝ) ^ 2 * Y * ((Q : ℝ) * Q) := mul_le_mul_of_nonneg_left hk hqY
      _ = 1 * (((q : ℝ) * Q) ^ 2 * Y) := by ring
      _ ≤ x₀ * (((q : ℝ) * Q) ^ 2 * Y) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (sq_nonneg _) hYpos.le)
      _ = x₀ * ((q : ℝ) * Q) ^ 2 * Y := by ring

/-- SUSPECTED FALSE, proved: P0069 pages 9 and 10, display 2.11, as stated in the lab
leaf `leaf_minor_local_energy512`, fails. Theorem 2 on page 3 restricts coprimality
only for a, and its hypotheses on b are tested only against Dirichlet characters.
The sequence b(m) = e(m(1/4 + δ/2)) on even m, 0 on odd m, δ = Y^(-1/2), with a = 0,
u = v = 0, B = 0 and no exceptional characters, satisfies every hypothesis, while its
local minor arc energy at ζ = 3/4 - δ/2 exceeds C Y / log x for large x. -/
theorem leaf_minor_local_energy512_false :
    ¬ (∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun _ b _ _ _ =>
        ∀ L : ℝ, 0 < L → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ ζ : ℝ,
            localMinorEnergy512 ε D x (b x) ζ ≤
              C * length512 ε x * Real.log x ^ (-L))) := by
  intro h
  obtain ⟨ε₀, hε₀, h⟩ := h 0
  have hεpos : 0 < min (ε₀ / 2) (1 / 100) := lt_min (by linarith) (by norm_num)
  have hεlt : min (ε₀ / 2) (1 / 100) < ε₀ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε1 : min (ε₀ / 2) (1 / 100) ≤ 1 / 100 := min_le_right _ _
  generalize min (ε₀ / 2) (1 / 100) = ε at hεpos hεlt hε1
  have hT := h ε hεpos hεlt
  obtain ⟨a, ha⟩ : ∃ a : ℝ → ℕ → ℂ, ∀ x k, a x k = 0 := ⟨fun _ _ => 0, fun _ _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℕ → ℂ, ∀ (x : ℝ) (m : ℕ), b x m = if Even m then
      Complex.exp (2 * Real.pi * Complex.I *
        (((m : ℝ) * (1 / 4 + (x ^ (11 / 20 + ε)) ^ (-(1 / 2 : ℝ)) / 2) : ℝ) : ℂ)) else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hconc := hT a b 0 0 (fun _ _ _ => ∅)
    (counter_hyp_i512 ε a ha) (counter_hyp_ii512 ε a b ha hb) (counter_hyp_iii512 a ha)
    (counter_hyp_iv512 ε hεpos b hb) (counter_hyp_v512 ε hεpos b hb)
  obtain ⟨D₀, hD⟩ := hconc 1 one_pos
  obtain ⟨C, hC⟩ := hD D₀ le_rfl
  obtain ⟨x₀, hx₀⟩ := counter_energy_lower512 ε hεpos hε1 b hb D₀ C
  have h1 := hC (max C x₀) (le_max_left _ _)
    (3 / 4 - ((max C x₀) ^ (11 / 20 + ε)) ^ (-(1 / 2 : ℝ)) / 2)
  have h2 := hx₀ (max C x₀) (le_max_right _ _)
  exact absurd h1 (not_le.mpr h2)

end LeanLab.BHP1997.Section2MS
