/-
Unit S6-28, burst-20261124. The leaf doubled_system_characters435 of
SPLIT_doubled_system_expansion435 is FALSE as formalized.

Over the arcs of denominator q the square mass is, by the orthogonality of the
characters, the sum over all characters of the Gauss sum square times the
character square integral, divided by the totient of q. A Gauss sum square is q
for a primitive character, so the true chain carries a factor q in front of the
nonprincipal sum, as in the PROVED weaker form doubled_system_characters487 of
Decomp487c. Without that factor the bound fails. The witness below is the
smallest one: N equal to one, so the log term vanishes, tau equal to four, and q
a large prime. The arcs then cover the interval from one over q to one minus one
over q, where the prime series of N equal to one has modulus at least one
twentieth, while every character series has modulus at most two.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_doubled_system_expansion435

namespace LeanLab.Linnik1951

open MeasureTheory

/-- The real number exp of minus n is the n-th power of exp of minus one. -/
theorem exp_neg_nat_S628 (n : ℕ) : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
  rw [← Real.exp_nat_mul]; congr 1; ring

theorem exp_neg_one_bounds_S628 : 0.3678 < Real.exp (-1) ∧ Real.exp (-1) < 0.368 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have he : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  rw [he]
  constructor
  · rw [lt_inv_comm₀ (by norm_num) hpos]; norm_num at h2 ⊢; linarith
  · rw [inv_lt_comm₀ hpos (by norm_num)]; norm_num at h1 ⊢; linarith

theorem summable_exp_neg_nat_S628 : Summable fun n : ℕ => Real.exp (-(n : ℝ)) := by
  have h := exp_neg_one_bounds_S628
  refine (summable_geometric_of_lt_one (Real.exp_pos _).le (by linarith [h.2])).congr ?_
  intro n; rw [exp_neg_nat_S628]

theorem tsum_exp_neg_nat_S628 : (∑' n : ℕ, Real.exp (-(n : ℝ))) = (1 - Real.exp (-1))⁻¹ := by
  have h := exp_neg_one_bounds_S628
  simp_rw [exp_neg_nat_S628]
  exact tsum_geometric_of_lt_one (Real.exp_pos _).le (by linarith [h.2])

/-- A prime series with coefficients dominated by exp of minus p has modulus at most two. -/
theorem norm_prime_series_le_S628 (g : Nat.Primes → ℂ)
    (hg : ∀ p : Nat.Primes, ‖g p‖ ≤ Real.exp (-((p : ℕ) : ℝ))) :
    ‖∑' p : Nat.Primes, g p‖ ≤ 2 := by
  have hs : Summable fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ)) :=
    summable_exp_neg_nat_S628.comp_injective Nat.Primes.coe_nat_injective
  have hgs : Summable fun p : Nat.Primes => ‖g p‖ :=
    hs.of_nonneg_of_le (fun p => norm_nonneg _) hg
  have h1 := norm_tsum_le_tsum_norm hgs
  have h2 : (∑' p : Nat.Primes, ‖g p‖) ≤ ∑' p : Nat.Primes, Real.exp (-((p : ℕ) : ℝ)) :=
    hgs.tsum_le_tsum hg hs
  have h3 : (∑' p : Nat.Primes, Real.exp (-((p : ℕ) : ℝ))) ≤
      ∑' n : ℕ, Real.exp (-(n : ℝ)) :=
    tsum_comp_le_tsum_of_inj summable_exp_neg_nat_S628 (fun n => (Real.exp_pos _).le)
      Nat.Primes.coe_nat_injective
  have h4 := exp_neg_one_bounds_S628
  have h5 : (1 - Real.exp (-1))⁻¹ ≤ 2 := by
    have := h4.2
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    norm_num
    linarith
  rw [tsum_exp_neg_nat_S628] at h3
  linarith

/-- Every character series at N equal to one has modulus at most two. -/
theorem character_one_le_S628 {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) :
    ‖characterPrime280 χ 1 z‖ ≤ 2 := by
  unfold characterPrime280
  refine norm_prime_series_le_S628 _ (fun p => ?_)
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Nat.cast_one, div_one]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (χ.norm_le_one _)

/-- The prime series at N equal to one has modulus at least one twentieth: the
term of the prime two dominates the rest. -/
theorem prime_one_lower_S628 (α : ℝ) : 1 / 20 ≤ ‖primeFourier111 1 α‖ := by
  classical
  let f : Nat.Primes → ℂ := fun p => (Real.exp (-((p : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)
  have hfdef : primeFourier111 1 α = ∑' p, f p := rfl
  rw [hfdef]
  have hnorm : ∀ p : Nat.Primes, ‖f p‖ = Real.exp (-((p : ℕ) : ℝ)) := by
    intro p
    simp only [f]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp
  have hs : Summable fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ)) :=
    summable_exp_neg_nat_S628.comp_injective Nat.Primes.coe_nat_injective
  have hfs : Summable f := by
    refine Summable.of_norm ?_
    simp_rw [hnorm]; exact hs
  set p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hsplit := hfs.tsum_eq_add_tsum_ite p2
  set h : ℕ → ℝ := fun n => if 3 ≤ n then Real.exp (-(n : ℝ)) else 0 with hh
  have hh0 : ∀ n, 0 ≤ h n := fun n => by
    rw [hh]; dsimp only; split_ifs <;> positivity
  have hhs : Summable h := summable_exp_neg_nat_S628.of_nonneg_of_le hh0 (fun n => by
    rw [hh]; dsimp only; split_ifs <;> first | exact le_rfl | positivity)
  have hrest : ∀ p : Nat.Primes, ‖(if p = p2 then 0 else f p)‖ ≤ h p := by
    intro p
    by_cases hp : p = p2
    · rw [if_pos hp, norm_zero]; exact hh0 _
    · rw [if_neg hp, hnorm, hh]
      have h3 : 3 ≤ (p : ℕ) := by
        have h2 := p.property.two_le
        have hne : (p : ℕ) ≠ 2 := fun he => hp (Subtype.ext he)
        omega
      simp [h3]
  have hrs : Summable fun p : Nat.Primes => ‖(if p = p2 then 0 else f p)‖ :=
    (hhs.comp_injective Nat.Primes.coe_nat_injective).of_nonneg_of_le
      (fun p => norm_nonneg _) hrest
  have hr1 := norm_tsum_le_tsum_norm hrs
  have hr2 := hrs.tsum_le_tsum hrest (hhs.comp_injective Nat.Primes.coe_nat_injective)
  have hr3 : (∑' p : Nat.Primes, h p) ≤ ∑' n : ℕ, h n :=
    tsum_comp_le_tsum_of_inj hhs hh0 Nat.Primes.coe_nat_injective
  have hr4 : (∑' n : ℕ, h n) = Real.exp (-1) ^ 3 * (1 - Real.exp (-1))⁻¹ := by
    rw [← hhs.sum_add_tsum_nat_add 3]
    have hz : (∑ i ∈ Finset.range 3, h i) = 0 := by
      simp [hh, Finset.sum_range_succ]
    rw [hz, zero_add]
    have hb := exp_neg_one_bounds_S628
    have heq : ∀ n : ℕ, h (n + 3) = Real.exp (-1) ^ 3 * Real.exp (-1) ^ n := by
      intro n
      rw [hh]; dsimp only
      rw [if_pos (by omega), ← pow_add, ← exp_neg_nat_S628]
      push_cast; ring_nf
    simp_rw [heq]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le (by linarith [hb.2])]
  have h2n : ‖f p2‖ = Real.exp (-1) ^ 2 := by
    rw [hnorm]; exact exp_neg_nat_S628 2
  have htri : ‖f p2‖ ≤ ‖∑' p, f p‖ + ‖∑' p, (if p = p2 then 0 else f p)‖ := by
    rw [hsplit]
    have := norm_sub_le (f p2 + ∑' p, (if p = p2 then 0 else f p))
      (∑' p, (if p = p2 then 0 else f p))
    rw [add_sub_cancel_right] at this
    exact this
  have hb := exp_neg_one_bounds_S628
  set t := Real.exp (-1) with ht
  have hkey : 1 / 20 ≤ t ^ 2 - t ^ 3 * (1 - t)⁻¹ := by
    have h1t : 0 < 1 - t := by linarith [hb.2]
    have ht0 : 0 ≤ t := (Real.exp_pos _).le
    have ht2 : (0.3678 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) hb.1.le 2
    have ht3 : t ^ 3 ≤ (0.368 : ℝ) ^ 3 := pow_le_pow_left₀ ht0 hb.2.le 3
    have hinv : t ^ 3 * (1 - t)⁻¹ = t ^ 3 / (1 - t) := (div_eq_mul_inv _ _).symm
    rw [hinv]
    have : t ^ 3 / (1 - t) ≤ t ^ 2 - 1 / 20 := by
      rw [div_le_iff₀ h1t]; nlinarith [hb.1, hb.2]
    linarith
  have : ‖∑' p, f p‖ ≥ t ^ 2 - t ^ 3 * (1 - t)⁻¹ := by
    rw [h2n] at htri
    linarith [hr1, hr2, hr3, hr4]
  linarith

/-- For a prime q at least four, the interval from one over q to one minus one over
q lies in the doubled system of denominator q at tau equal to four, inside the unit
interval. -/
theorem icc_subset_arcs_S628 (q : ℕ) (hq : q.Prime) (hq4 : 4 ≤ q) :
    Set.Icc (1 / (q : ℝ)) (1 - 1 / (q : ℝ)) ⊆ arcSystem111 q 4 ∩ Set.Icc 0 1 := by
  intro x hx
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨hx1, hx2⟩ := hx
  have hq1 : 1 / (q : ℝ) ≤ 1 / 4 := by
    have : (4 : ℝ) ≤ q := by exact_mod_cast hq4
    rw [div_le_div_iff₀ hqpos (by norm_num)]; linarith
  have hinv0 : 0 < 1 / (q : ℝ) := by positivity
  refine ⟨?_, ⟨by linarith, by linarith⟩⟩
  have hqx1 : 1 ≤ (q : ℝ) * x := by
    have := mul_le_mul_of_nonneg_left hx1 hqpos.le
    rwa [mul_one_div_cancel hqpos.ne'] at this
  have hqx2 : (q : ℝ) * x ≤ (q : ℝ) - 1 := by
    have := mul_le_mul_of_nonneg_left hx2 hqpos.le
    rwa [mul_sub, mul_one, mul_one_div_cancel hqpos.ne'] at this
  set a : ℤ := ⌊(q : ℝ) * x + 1 / 2⌋ with ha
  have ha1 : a ≤ (q : ℝ) * x + 1 / 2 := Int.floor_le _
  have ha2 : (q : ℝ) * x + 1 / 2 < a + 1 := Int.lt_floor_add_one _
  have hapos : 1 ≤ a := by
    rw [ha, Int.le_floor]; push_cast; linarith
  have haq : a ≤ (q : ℤ) - 1 := by
    have : (a : ℝ) < (q : ℝ) := by linarith
    have : a < (q : ℤ) := by exact_mod_cast this
    omega
  have hcop : Nat.Coprime a.natAbs (q : ℤ).natAbs := by
    rw [Int.natAbs_natCast]
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hq]
    intro hd
    have hcast : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg (by omega)
    have h1 : 1 ≤ a.natAbs := by omega
    have h2 : a.natAbs < q := by omega
    exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  refine ⟨(a : ℚ) / (q : ℚ), ?_, ?_⟩
  · have := Rat.den_div_eq_of_coprime (a := a) (b := (q : ℤ)) (by exact_mod_cast hqpos) hcop
    push_cast at this
    exact_mod_cast this
  · push_cast
    have hq0 : (q : ℝ) ≠ 0 := hqpos.ne'
    have heq : ((q : ℝ) * x - a) / q = x - (a : ℝ) / q := by
      rw [sub_div, mul_div_cancel_left₀ _ hq0]
    rw [← heq, abs_div, abs_of_pos hqpos, div_le_div_iff₀ hqpos (by positivity)]
    have hab : |(q : ℝ) * x - a| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg ((q : ℝ) * x - a)]

/-- The leaf doubled_system_characters435 is false: its negation, verbatim. -/
theorem not_doubled_system_characters435 : ¬ (
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q] (τ : ℝ), 1 ≤ N → 2 ≤ q → 4 ≤ τ →
      (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, ‖primeFourier111 N α‖ ^ 2) ≤
        B / (q.totient : ℝ) *
          ((∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
            (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
                ‖characterPrime280 χ N z‖ ^ 2)) +
        B * (2 / τ) * Real.log N ^ 6) := by
  classical
  rintro ⟨B, hB, hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (10000 * (B + 1))
  obtain ⟨q, hqn, hq⟩ := Nat.exists_infinite_primes (n + 4)
  have hq4 : 4 ≤ q := by omega
  haveI : NeZero q := ⟨by omega⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqbig : 10000 * (B + 1) < (q : ℝ) := by
    have : (n : ℝ) ≤ q := by exact_mod_cast (show n ≤ q by omega)
    linarith
  have hmain := hbound 1 q 4 le_rfl (by omega) (by norm_num)
  have hz : B * (2 / 4) * Real.log ((1 : ℕ) : ℝ) ^ 6 = 0 := by simp
  rw [hz, add_zero] at hmain
  set r : ℝ := 2 / ((q : ℝ) * 4) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr' : r = 1 / (2 * q) := by
    rw [hr, div_eq_div_iff (by positivity) (by positivity)]; ring
  -- upper bound for each character integral
  have hchar : ∀ χ : DirichletCharacter ℂ q,
      (∫ z in -r..r, ‖characterPrime280 χ 1 z‖ ^ 2) ≤ 8 * r := by
    intro χ
    have hc : Continuous fun z : ℝ => ‖characterPrime280 χ 1 z‖ ^ 2 :=
      (continuous_character_prime357 χ 1 le_rfl).norm.pow 2
    have hle : (∫ z in -r..r, ‖characterPrime280 χ 1 z‖ ^ 2) ≤ ∫ _z in -r..r, (4 : ℝ) := by
      refine intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) (fun z _ => ?_)
      have h2 := character_one_le_S628 χ z
      have h0 := norm_nonneg (characterPrime280 χ 1 z)
      nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    linarith
  have htot : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hcard : ((Finset.univ.filter
      (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) ≤ q.totient := by
    have h1 := Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ q))
      (fun χ => χ ≠ 1)
    have h2 : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    exact_mod_cast h2 ▸ h1
  have hsum : (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ∫ z in -r..r, ‖characterPrime280 χ 1 z‖ ^ 2) ≤ (q.totient : ℝ) * (8 * r) := by
    calc _ ≤ ∑ _χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          8 * r := Finset.sum_le_sum fun χ _ => hchar χ
      _ = _ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hrhs : B / (q.totient : ℝ) *
      ((∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) 1 z‖ ^ 2) +
        (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ∫ z in -r..r, ‖characterPrime280 χ 1 z‖ ^ 2)) ≤ 16 * B * r := by
    have hb := add_le_add (hchar 1) hsum
    have h1t : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hφ : B / (q.totient : ℝ) * ((q.totient : ℝ) * (8 * r)) = B * (8 * r) := by
      rw [← mul_assoc, div_mul_cancel₀ B htot.ne']
    have hφ2 : B / (q.totient : ℝ) * (8 * r) ≤ B * (8 * r) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [div_le_iff₀ htot]; nlinarith
    calc _ ≤ B / (q.totient : ℝ) * (8 * r + (q.totient : ℝ) * (8 * r)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = B / (q.totient : ℝ) * (8 * r) +
            B / (q.totient : ℝ) * ((q.totient : ℝ) * (8 * r)) := mul_add _ _ _
      _ ≤ 16 * B * r := by rw [hφ]; linarith
  -- lower bound for the arc mass
  have hcS : Continuous fun α : ℝ => ‖primeFourier111 1 α‖ ^ 2 :=
    (continuous_prime_fourier111 1 le_rfl).norm.pow 2
  have hsub := icc_subset_arcs_S628 q hq hq4
  have hmono : (∫ α in Set.Icc (1 / (q : ℝ)) (1 - 1 / (q : ℝ)), ‖primeFourier111 1 α‖ ^ 2) ≤
      ∫ α in arcSystem111 q 4 ∩ Set.Icc 0 1, ‖primeFourier111 1 α‖ ^ 2 := by
    refine setIntegral_mono_set ?_ ?_ hsub.eventuallyLE
    · exact (hcS.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.inter_subset_right
    · exact Filter.Eventually.of_forall (fun α => sq_nonneg _)
  have hq1 : 1 / (q : ℝ) ≤ 1 / 4 := by
    have : (4 : ℝ) ≤ q := by exact_mod_cast hq4
    rw [div_le_div_iff₀ hqpos (by norm_num)]; linarith
  have hab : 1 / (q : ℝ) ≤ 1 - 1 / (q : ℝ) := by linarith
  have hlow : (1 - 2 / (q : ℝ)) * (1 / 400) ≤
      ∫ α in Set.Icc (1 / (q : ℝ)) (1 - 1 / (q : ℝ)), ‖primeFourier111 1 α‖ ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    have hle : (∫ _α in (1 / (q : ℝ))..(1 - 1 / (q : ℝ)), (1 / 400 : ℝ)) ≤
        ∫ α in (1 / (q : ℝ))..(1 - 1 / (q : ℝ)), ‖primeFourier111 1 α‖ ^ 2 := by
      refine intervalIntegral.integral_mono_on hab (continuous_const.intervalIntegrable _ _)
        (hcS.intervalIntegrable _ _) (fun α _ => ?_)
      have h := prime_one_lower_S628 α
      nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    have : (1 - 1 / (q : ℝ) - 1 / (q : ℝ)) = 1 - 2 / (q : ℝ) := by ring
    rw [this] at hle
    exact hle
  have hfin := (hlow.trans hmono).trans hmain
  have hfin' := hfin.trans hrhs
  rw [hr'] at hfin'
  have h2q : 2 / (q : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hqpos (by norm_num)]; linarith
  have hlo : (1 / 800 : ℝ) ≤ 16 * B * (1 / (2 * q)) := by linarith
  have hhi : 16 * B * (1 / (2 * (q : ℝ))) < 1 / 800 := by
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    linarith
  linarith

end LeanLab.Linnik1951
