/-
Unit U-1622. Split of the doubled system mass of the exceptional file of this folder.
The target statement stays exactly as it is; this file adds three leaves and one
assembly.

The argument, from pages 155, 160 and 166 of the scan. The square integral of the
doubled prime system over the arc system clipped to the unit interval is first rewritten
as an integral over the radius interval of the sum of the shifted squares at the reduced
residues: the system is the finitely many doubled rational intervals of denominator q,
so a nonnegative continuous function integrates over it at most as its shifted sum.
The shifted sum is then bounded pointwise, for every z, by the finite unit character
calculation: orthogonality of the unit group turns the sum over the reduced residues
into the principal square plus q times the nonprincipal squares, divided by the totient,
and the Gauss squares are at most q. Integrating that pointwise bound over the radius
interval and doubling the constant absorbs the factor two from the doubled error
interval.

No analytic input is invented here: the pointwise character calculation and the two
geometry steps are leaves, and the assembly only integrates the pointwise bound and adds
the doubled error size.
-/
import LeanLab.Linnik1951.SPLIT1622_exceptional
import LeanLab.Linnik1951.GaussBound376

namespace LeanLab.Linnik1951

open MeasureTheory Filter Finset

/-- The reduced residues below q number the totient of q, in the form the assembly
uses for the counting of the doubled intervals. -/
private theorem card_reduced1622 (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  exact congrArg Finset.card (Finset.filter_congr (fun a _ => Nat.coprime_comm))

/-- LEAF. The covering step of the geometry. For q at least two and tau at least four,
every point of the arc system of denominator q that lies in the unit interval lies in
one of the doubled rational intervals of radius two over q tau about a reduced residue
below q. Only rational arithmetic and the positivity of q and tau are used; no
integration, no character and no bound on the prime system occurs. -/
theorem rational_cover1622 (q : ℕ) [NeZero q] (τ : ℝ) (hq : 2 ≤ q) (hτ : 4 ≤ τ) :
    arcSystem111 q τ ∩ Set.Icc 0 1 ⊆
      ⋃ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ)) ((a : ℝ) / q + 2 / ((q : ℝ) * τ)) := by
  rintro x ⟨⟨r, hrden, hrδ⟩, hx0, hx1⟩
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hRle : 2 / ((q : ℝ) * τ) ≤ 1 / (2 * (q : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [abs_le] at hrδ
  obtain ⟨hrlo, hrhi⟩ := hrδ
  have hrcq : (r : ℝ) = (r.num : ℝ) / (q : ℝ) := by
    rw [Rat.cast_def, hrden]
  have hcop : r.num.natAbs.Coprime q := by
    have h := r.reduced
    rwa [hrden] at h
  have hnum_nonneg : 0 ≤ r.num := by
    by_contra hneg
    push_neg at hneg
    have hle : (r.num : ℝ) ≤ -1 := by
      have : r.num ≤ -1 := by omega
      exact_mod_cast this
    have hrle : (r : ℝ) ≤ -1 / (q : ℝ) := by
      rw [hrcq, div_le_div_iff₀ hqpos hqpos]
      nlinarith
    have hxle : x ≤ -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) := by linarith
    have hneg' : -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) < 0 := by
      have hsplit : -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) = -(1 / (2 * (q : ℝ))) := by
        field_simp
        ring
      rw [hsplit]
      have : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    linarith
  have hnum_lt : r.num < (q : ℤ) := by
    by_contra hge
    push_neg at hge
    have hne : r.num ≠ (q : ℤ) := by
      intro he
      have hnat : r.num.natAbs = q := by
        rw [he]
        exact Int.natAbs_natCast q
      rw [hnat] at hcop
      have hq1 : q = 1 := Nat.coprime_self q |>.mp hcop
      omega
    have hge' : (q : ℤ) + 1 ≤ r.num := by omega
    have hcastZ : ((q : ℤ) : ℝ) + 1 ≤ (r.num : ℝ) := by exact_mod_cast hge'
    have hcast : (q : ℝ) + 1 ≤ (r.num : ℝ) := by
      have hqZ : ((q : ℤ) : ℝ) = (q : ℝ) := by push_cast; ring
      linarith
    have hrbig : 1 + 1 / (q : ℝ) ≤ (r : ℝ) := by
      rw [hrcq, le_div_iff₀ hqpos]
      have hmul : (1 + 1 / (q : ℝ)) * (q : ℝ) = (q : ℝ) + 1 := by
        field_simp
      rw [hmul]
      exact hcast
    have hxge : 1 + 1 / (2 * (q : ℝ)) ≤ x := by
      have hsplit : (1 : ℝ) + 1 / (q : ℝ) - 1 / (2 * (q : ℝ)) = 1 + 1 / (2 * (q : ℝ)) := by
        field_simp
        ring
      linarith
    have : (1 : ℝ) < 1 + 1 / (2 * (q : ℝ)) := by
      have : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    linarith
  set a := r.num.toNat with hadef
  have hanum : (a : ℤ) = r.num := Int.toNat_of_nonneg hnum_nonneg
  have halt : a < q := by
    have h' : (a : ℤ) < (q : ℤ) := by rw [hanum]; exact hnum_lt
    exact_mod_cast h'
  have hcopa : Nat.Coprime a q := by
    have hna : r.num.natAbs = a := by
      rw [hadef]
      have h1 : ((r.num.natAbs : ℕ) : ℤ) = r.num := Int.natAbs_of_nonneg hnum_nonneg
      have h2 : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum_nonneg
      exact_mod_cast h1.trans h2.symm
    rwa [hna] at hcop
  have hcasta : (a : ℝ) = (r.num : ℝ) := by
    have : (a : ℝ) = ((a : ℤ) : ℝ) := by push_cast; ring
    rw [this, hanum]
  have hmem : a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨halt, hcopa⟩
  have hxI : x ∈ Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ))
      ((a : ℝ) / q + 2 / ((q : ℝ) * τ)) := by
    have e1 : (a : ℝ) / q - 2 / ((q : ℝ) * τ) = (r : ℝ) - 2 / ((q : ℝ) * τ) := by
      rw [hcasta, hrcq]
    have e2 : (a : ℝ) / q + 2 / ((q : ℝ) * τ) = (r : ℝ) + 2 / ((q : ℝ) * τ) := by
      rw [hcasta, hrcq]
    rw [Set.mem_Icc, e1, e2]
    constructor <;> linarith
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨a, hmem, hxI⟩


/-- LEAF. The integral step of the geometry. For a nonnegative continuous function and a
cover of the clipped arc system by the doubled intervals of the reduced residues, the
integral over the clipped system is at most the integral over the radius interval of the
sum of the shifted values at the reduced residues. This is subadditivity of the integral
over a finite union together with translation of the interval, so it uses no property of
the function beyond nonnegativity and continuity, and none of the characters. -/
theorem rational_cover_integral1622 (q : ℕ) [NeZero q] (τ : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (hn : ∀ x : ℝ, 0 ≤ f x)
    (hcover : arcSystem111 q τ ∩ Set.Icc 0 1 ⊆
      ⋃ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ)) ((a : ℝ) / q + 2 / ((q : ℝ) * τ))) :
    (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, f α) ≤
      ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), f ((a : ℝ) / q + z) := by
  sorry



open MeasureTheory Finset

/-- The phase of the residue `m` modulo `q`, as an `n`-th power. -/
private theorem exp_phase_nat (q m a : ℕ) (hq : 0 < q) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (a : ℂ) / (q : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) ^ a := by
  rw [← Complex.exp_nat_mul]
  congr 1
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

/-- Complete residue sums vanish off the divisibility condition. -/
private theorem full_sum_nat (q m : ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (a : ℂ) / (q : ℂ))) =
      if q ∣ m then (q : ℂ) else 0 := by
  classical
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpower : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) ^ q = 1 := by
    rw [← exp_phase_nat q m q hq]
    have harg : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (q : ℂ) / (q : ℂ)
        = 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / ((1 : ℕ) : ℂ) := by
      field_simp
      ring
    rw [harg, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (by norm_num : (1 : ℕ) ≠ 0)]
    exact one_dvd m
  simp_rw [exp_phase_nat q m _ hq]
  by_cases hdiv : q ∣ m
  · rw [if_pos hdiv]
    have hone : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) = 1 := by
      rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hq.ne']
      exact hdiv
    rw [hone]
    simp
  · rw [if_neg hdiv]
    have hne : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) - 1 ≠ 0 := by
      intro h0
      apply hdiv
      rw [sub_eq_zero] at h0
      have := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := m) (N := q) hq.ne').mp h0
      exact this
    have hmul := geom_sum_mul (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ))) q
    rw [hpower, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right hne

/-- The sum over the multiples of a divisor reduces to the quotient modulus. -/
private theorem multiples_sum_nat (q d m : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    (∑ a ∈ (Finset.range q).filter (fun a => d ∣ a),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (a : ℂ) / (q : ℂ))) =
      if q / d ∣ m then ((q / d : ℕ) : ℂ) else 0 := by
  classical
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hq
  have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hd) hd0
  have hqeq : q = d * (q / d) := (Nat.mul_div_cancel' hd).symm
  have hfilter : (Finset.range q).filter (fun a => d ∣ a) =
      (Finset.range (q / d)).image (fun b => d * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ha, ⟨b, rfl⟩⟩
      rw [hqeq] at ha
      exact ⟨b, (Nat.mul_lt_mul_left hd0).mp ha, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨by rw [hqeq]; exact (Nat.mul_lt_mul_left hd0).mpr hb, ⟨b, rfl⟩⟩
  rw [hfilter, Finset.sum_image]
  · have heq (b : ℕ) :
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((d * b : ℕ) : ℂ) / (q : ℂ))
          = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) *
              (b : ℂ) / ((q / d : ℕ) : ℂ)) := by
      congr 1
      conv_lhs => rw [hqeq]
      have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
      have hqdC : ((q / d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hqd.ne'
      push_cast
      field_simp
    simp_rw [heq]
    exact full_sum_nat (q / d) m hqd
  · intro b _ c _ heq
    exact Nat.eq_of_mul_eq_mul_left hd0 heq

/-- Möbius inversion gives the coprimality indicator at every positive modulus. -/
private theorem coprime_indicator_nat (q a : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime a q then 1 else 0 := by
  classical
  have hset : q.divisors.filter (fun d => d ∣ a) = (Nat.gcd a q).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hg : Nat.gcd a q ≠ 0 := Nat.gcd_ne_zero_right hq.ne'
    simp [hg, hq.ne', and_comm]
  rw [← Finset.sum_filter, hset]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd a q))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply, Nat.coprime_iff_gcd_eq_one] using h

/-- The Ramanujan sum at argument one is the Möbius function of the modulus. -/
private theorem ramanujan_sum_one_nat (q : ℕ) (hq : 0 < q) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ))) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  classical
  have heq (a : ℕ) :
      (if Nat.Coprime a q then
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) else 0) =
        (∑ d ∈ q.divisors,
            if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) := by
    rw [coprime_indicator_nat q a hq]
    split_ifs <;> simp
  rw [Finset.sum_filter]
  simp_rw [heq, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hstep : ∀ d ∈ q.divisors,
      (∑ a ∈ Finset.range q,
          (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ))) =
        (ArithmeticFunction.moebius d : ℂ) *
          (if q / d ∣ 1 then ((q / d : ℕ) : ℂ) else 0) := by
    intro d hd
    have hdd : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hone : ∀ a ∈ Finset.range q,
        (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) =
          (ArithmeticFunction.moebius d : ℂ) *
            (if d ∣ a then
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) else 0) := by
      intro a _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hone, ← Finset.mul_sum, ← Finset.sum_filter,
      multiples_sum_nat q d 1 hq hdd]
  rw [Finset.sum_congr rfl hstep]
  rw [Finset.sum_eq_single q]
  · rw [Nat.div_self hq]
    simp
  · intro d hd hdne
    have hnot : ¬ q / d ∣ 1 := by
      intro h1
      have hqd1 : q / d = 1 := Nat.dvd_one.mp h1
      have h := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      rw [hqd1, mul_one] at h
      exact hdne h
    rw [if_neg hnot, mul_zero]
  · intro hnot
    exact absurd (Nat.mem_divisors_self q hq.ne') hnot



/-! ### The principal Gauss vector of the unit group

The unit sum of the additive character is the Ramanujan sum at argument one, so its
modulus is at most one, and the same holds for the conjugate sum that the Gauss vector of
the principal character is. -/

/-- The unit sum of the additive character has modulus at most one. -/
private theorem unit_sum_addChar_le_one (q : ℕ) [NeZero q] :
    ‖∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c‖ ≤ 1 := by
  classical
  have hq : 0 < q := NeZero.pos q
  have hfil : (Finset.range q).filter (fun a => IsUnit ((a : ℕ) : ZMod q))
      = (Finset.range q).filter (fun a => Nat.Coprime a q) := by
    refine Finset.filter_congr ?_
    intro a _
    exact ZMod.isUnit_iff_coprime a q
  have hconv :
      (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c)
        = ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) := by
    rw [Finset.sum_filter, LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range, ← Finset.sum_filter,
      hfil]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Int.cast_natCast a, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [hconv, ramanujan_sum_one_nat q hq, Complex.norm_intCast]
  have h1 : |(ArithmeticFunction.moebius q : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  exact_mod_cast h1

/-- The Gauss vector of the principal character at the unit shift one has modulus at most
one: it is the conjugate of the unit sum of the additive character. -/
private theorem unit_gauss_principal_le (q : ℕ) [NeZero q] :
    ‖∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
        ZMod.stdAddChar (-(1 * c))‖ ≤ 1 := by
  have hconj :
      (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar (-(1 * c)))
        = (starRingEnd ℂ)
            (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [LeanLab.PNTPort.LargeSieve.conj_stdAddChar]
    simp
  rw [hconj, Complex.norm_conj]
  exact unit_sum_addChar_le_one q

/-! ### Counting the primes that divide the modulus

At most `log_2 q` primes divide `q`, since their product is at most `q`; the correction
terms of the prime series are supported on exactly those primes. -/

/-- The number of distinct prime divisors of a positive integer obeys `2 ^ ω ≤ q`. -/
private theorem two_pow_primeFactors_card_le (q : ℕ) (hq : 0 < q) :
    2 ^ q.primeFactors.card ≤ q := by
  have h2 : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  exact h2.trans (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))

/-- The count of distinct prime divisors is at most twice the logarithm. -/
private theorem primeFactors_card_le_log (q : ℕ) (hq : 2 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ 2 * Real.log q := by
  have hq0 : 0 < q := by omega
  have hle : ((2 : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) := by
    exact_mod_cast two_pow_primeFactors_card_le q hq0
  have hpos : (0 : ℝ) < (2 : ℝ) ^ q.primeFactors.card := by positivity
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_pow] at hlog
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq : (1 : ℝ) < q)
  nlinarith

/-- The tail of the prime series at a unit residue is supported on the primes dividing `q`,
and each of its terms has modulus at most one. -/
private theorem corr_bound (N q : ℕ) [NeZero q] (hq : 2 ≤ q) (z : ℝ) (a : ZMod q) :
    ‖∑' p : Nat.Primes, (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖ ≤ 2 * Real.log q := by
  classical
  let emb : Function.Embedding {d // d ∈ q.primeFactors} Nat.Primes :=
    ⟨fun d => (⟨d.1, (Nat.mem_primeFactors.mp d.2).1⟩ : Nat.Primes),
      fun x y hxy => Subtype.ext (congrArg (fun p : Nat.Primes => (p : ℕ)) hxy)⟩
  set sf : Finset Nat.Primes := q.primeFactors.attach.map emb with hsf
  have hmem : ∀ p : Nat.Primes, p ∉ sf → IsUnit (((p : ℕ)) : ZMod q) := by
    intro p hp
    by_contra hnu
    apply hp
    have hpnot : ¬ Nat.Coprime (p : ℕ) q :=
      fun h => hnu ((ZMod.isUnit_iff_coprime (p : ℕ) q).mpr h)
    have hdvd : (p : ℕ) ∣ q := by
      have hg : Nat.gcd (p : ℕ) q ∣ (p : ℕ) := Nat.gcd_dvd_left _ _
      have hg1 : Nat.gcd (p : ℕ) q ≠ 1 := fun h => hpnot (Nat.coprime_iff_gcd_eq_one.mpr h)
      rcases Nat.Prime.eq_one_or_self_of_dvd p.2 (Nat.gcd (p : ℕ) q) hg with h1 | h1
      · exact absurd h1 hg1
      · exact h1 ▸ Nat.gcd_dvd_right _ _
    have hmem' : (p : ℕ) ∈ q.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨p.2, hdvd, by omega⟩
    rw [hsf, Finset.mem_map]
    exact ⟨⟨(p : ℕ), hmem'⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
  have hcard : sf.card = q.primeFactors.card := by
    rw [hsf]
    simp
  have hterm : ∀ p : Nat.Primes,
      ‖(if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖ ≤ 1 := by
    intro p
    by_cases hp : IsUnit (((p : ℕ)) : ZMod q)
    · rw [if_pos hp, norm_zero]; norm_num
    · rw [if_neg hp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_one_iff.mpr ?_
      rw [neg_div]
      exact neg_nonpos.mpr (div_nonneg (by positivity) (by positivity))
  have hzero : ∀ p : Nat.Primes, p ∉ sf →
      (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I)) = 0 := by
    intro p hp
    rw [if_pos (hmem p hp)]
  rw [tsum_eq_sum hzero]
  calc ‖∑ p ∈ sf, (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖
      ≤ ∑ p ∈ sf, ‖(if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ sf, (1 : ℝ) := Finset.sum_le_sum (fun p _ => hterm p)
    _ = (sf.card : ℝ) := by simp
    _ = (q.primeFactors.card : ℝ) := by rw [hcard]
    _ ≤ 2 * Real.log q := primeFactors_card_le_log q hq




open MeasureTheory Filter Finset

/-! ### Development towards `rational_pointwise_characters1622` (WIP, not yet used)

The character-table expansion of the additive character of the units, the first step of the
remaining route (see results/Linnik1951-SPLIT_doubled_system_characters1622-notes.md).
The unit Gauss vector is written out as an explicit finite sum at every use site.
-/

open MeasureTheory Filter Finset Complex
open LeanLab.PNTPort.LargeSieve
noncomputable section
variable {q : ℕ} [NeZero q]

/-- Character-table expansion of the additive character on the units. -/
private theorem sum_Gunit_mul_char (a b : ZMod q) (hb : IsUnit b) :
    ∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ b
      = (q.totient : ℂ) * ZMod.stdAddChar (-(a * b)) := by
  have hterm : ∀ χ : DirichletCharacter ℂ q,
      (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ b = ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
        ZMod.stdAddChar (-(a * c)) * χ (c⁻¹ * b) := by
    intro χ
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨-, hcu⟩ := hc
    rw [conj_char_of_isUnit χ hcu, mul_assoc, ← map_mul]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single b]
  · rw [← Finset.mul_sum, DirichletCharacter.sum_characters_eq,
      if_pos (ZMod.inv_mul_of_unit b hb)]
    ring
  · intro c hc hcb
    rw [← Finset.mul_sum, DirichletCharacter.sum_characters_eq, if_neg ?_]
    · simp
    · intro h
      apply hcb
      rw [Finset.mem_filter] at hc
      obtain ⟨-, hcu⟩ := hc
      have h2 : c * (c⁻¹ * b) = c * 1 := by rw [h]
      rw [← mul_assoc, ZMod.mul_inv_of_unit c hcu, one_mul, mul_one] at h2
      exact h2.symm
  · intro hnot
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩) hnot

/-- `G` is multiplicative in the additive shift: on units it is `χ a` times `G χ 1`. -/
private theorem Gunit_eq_mul (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) = χ a * (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) := by
  classical
  have hainv : a⁻¹ * a = 1 := ZMod.inv_mul_of_unit a ha
  have hbinv : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a ha
  have hau : IsUnit a⁻¹ := by
    obtain ⟨u, rfl⟩ := ha
    exact ⟨u⁻¹, by simp⟩
  have hinv2 : a⁻¹⁻¹ = a := by
    calc a⁻¹⁻¹ = a⁻¹⁻¹ * 1 := (mul_one _).symm
      _ = a⁻¹⁻¹ * (a⁻¹ * a) := by rw [hainv]
      _ = a⁻¹⁻¹ * a⁻¹ * a := by rw [mul_assoc]
      _ = 1 * a := by rw [ZMod.inv_mul_of_unit a⁻¹ hau]
      _ = a := one_mul a
  have hconj : (starRingEnd ℂ) (χ a⁻¹) = χ a := by
    rw [conj_char_of_isUnit χ hau, hinv2]
  have hstep : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))
      = ∑ d ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
          ZMod.stdAddChar (-d) * (starRingEnd ℂ) (χ (a⁻¹ * d)) := by
    skip
    refine Finset.sum_nbij' (fun c => a * c) (fun c => a⁻¹ * c) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨Finset.mem_univ _, ha.mul hc.2⟩
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨Finset.mem_univ _, hau.mul hc.2⟩
    · intro c hc
      show a⁻¹ * (a * c) = c
      rw [← mul_assoc, hainv, one_mul]
    · intro c hc
      show a * (a⁻¹ * c) = c
      rw [← mul_assoc, hbinv, one_mul]
    · intro c hc
      show ZMod.stdAddChar (-(a * c)) * (starRingEnd ℂ) (χ c)
        = ZMod.stdAddChar (-(a * c)) * (starRingEnd ℂ) (χ (a⁻¹ * (a * c)))
      rw [← mul_assoc, hainv, one_mul]
  rw [hstep]
  skip
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Finset.mem_filter] at hd
  simp only [map_mul, hconj, one_mul]
  ring



/-- A nontrivial Dirichlet character has vanishing sum over the units. -/
private theorem sum_unit_char_of_ne_one {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a = 0 := by
  classical
  have hex : ∃ u : (ZMod q)ˣ, ψ ((u : ZMod q)) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ (MulChar.ext_iff.mpr (fun u => by rw [h u]; simp))
  obtain ⟨u, hu⟩ := hex
  have huo : IsUnit ((u : ZMod q)) := u.isUnit
  have hji : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
      ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, (u⁻¹).isUnit.mul ha.2⟩
  have hbi : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a =
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ ((u : ZMod q) * a) := by
    refine Finset.sum_nbij' (fun a => ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a) (fun a => (u : ZMod q) * a)
      hji ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _, huo.mul ha.2⟩
    · intro a ha
      show (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a) = a
      have h1 : (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [← mul_assoc, h1, one_mul]
    · intro a ha
      show ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u : ZMod q) * a) = a
      have h1 : (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) * (u : ZMod q) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [← mul_assoc, h1, one_mul]
    · intro a ha
      show ψ a = ψ ((u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a))
      have h1 : (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [← mul_assoc, h1, one_mul]
  have hfac : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ ((u : ZMod q) * a)
      = ψ (u : ZMod q) * ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [map_mul]
  have hS : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a
      = ψ (u : ZMod q) * ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a :=
    hbi.trans hfac
  have hz : (1 - ψ (u : ZMod q)) *
      (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a) = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  refine (mul_eq_zero.1 hz).resolve_left ?_
  intro hc
  exact hu (sub_eq_zero.1 hc).symm

/-- `χ·conj χ'` summed over the units: the totient at `χ = χ'`, zero otherwise. -/
private theorem sum_unit_char_mul_inv (χ χ' : DirichletCharacter ℂ q) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), χ a * χ' a⁻¹
      = if χ = χ' then (q.totient : ℂ) else 0 := by
  classical
  set ψ : DirichletCharacter ℂ q := χ * χ'⁻¹ with hpsi
  have hpt : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
      χ a * χ' a⁻¹ = ψ a := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨-, hau⟩ := ha
    rw [hpsi, MulChar.mul_apply, MulChar.inv_apply_eq_inv']
    congr 1
    have hmul : χ' a⁻¹ * χ' a = 1 := by
      rw [← map_mul, ZMod.inv_mul_of_unit a hau, map_one]
    exact eq_inv_of_mul_eq_one_left hmul
  rw [Finset.sum_congr rfl hpt]
  by_cases hχ : χ = χ'
  · subst hχ
    rw [if_pos rfl]
    have hψ1 : ψ = 1 := by rw [hpsi]; simp
    rw [hψ1]
    have hconst : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        (1 : DirichletCharacter ℂ q) a = (1 : ℂ) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨v, rfl⟩ := ha.2
      simp
    rw [Finset.sum_congr rfl hconst, Finset.sum_filter]
    have hC : ∑ x : ZMod q, (if IsUnit x then (1 : ℂ) else 0) = (q.totient : ℂ) := by
      have hR := sum_isUnit_eq_totient (q := q)
      have h2 : ((∑ x : ZMod q, (if IsUnit x then (1 : ℝ) else 0) : ℝ) : ℂ) = (q.totient : ℂ) := by
        rw [hR]
        push_cast
        ring
      rw [← h2]
      push_cast
      ring_nf
      congr 1
      funext x
      by_cases hx : IsUnit x <;> simp [hx]
    exact hC
  · rw [if_neg hχ]
    refine sum_unit_char_of_ne_one ?_
    intro h
    apply hχ
    rw [hpsi] at h
    have h2 := congrArg (fun t => t * χ') h
    simp only [one_mul] at h2
    rwa [mul_assoc, inv_mul_cancel, mul_one] at h2

/-- The Gauss vectors of two characters are orthogonal over the units. -/
private theorem sum_Gunit_orth (χ χ' : DirichletCharacter ℂ q) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))
      = if χ = χ' then (q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)))) else 0 := by
  classical
  have hpt : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
      (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))
        = (χ a * χ' a⁻¹) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ' cG)))) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨-, hau⟩ := ha
    rw [Gunit_eq_mul χ hau, Gunit_eq_mul χ' hau, map_mul, conj_char_of_isUnit χ' hau]
    ring
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_mul, sum_unit_char_mul_inv]
  by_cases h : χ = χ'
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h, zero_mul]

/-- The principal Gauss vector: the additive character of the units is the conjugate of
the Ramanujan sum, so its norm is `|μ(q)|`. -/
private theorem Gunit_one_principal_le (hq : 0 < q) : ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ≤ 1 := by
  classical
  have hU : ∀ c : ZMod q, (1 : DirichletCharacter ℂ q) c = if IsUnit c then (1 : ℂ) else 0 := by
    intro c
    by_cases hc : IsUnit c
    · rw [if_pos hc]
      obtain ⟨v, rfl⟩ := hc
      simp
    · rw [if_neg hc, MulChar.map_nonunit _ hc]
  have hG : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))
      = ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar (-c) := by
    skip
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [Finset.mem_filter] at hc
    rw [hU c, if_pos hc.2]
    simp
  have hconj : ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar (-c)
      = (starRingEnd ℂ) (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
          ZMod.stdAddChar c) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro c _
    exact (LeanLab.PNTPort.LargeSieve.conj_stdAddChar c).symm
  have hram : ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c
      = LeanLab.Perelli1996.Ramanujan103.ramanujanSum q 1 := by
    rw [Finset.sum_filter, sum_zmod_eq_sum_range]
    unfold LeanLab.Perelli1996.Ramanujan103.ramanujanSum
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [Finset.mem_range] at hc
    by_cases hcop : Nat.Coprime c q
    · rw [if_pos ((ZMod.isUnit_iff_coprime c q).2 hcop), if_pos hcop]
      have hone : ((c : ZMod q)) = ((1 : ℤ) : ZMod q) * (c : ZMod q) := by simp
      rw [hone, stdAddChar_mul_natCast (q := q) 1 c]
      congr 1
      push_cast
      ring
    · rw [if_neg (fun h => hcop ((ZMod.isUnit_iff_coprime c q).1 h)), if_neg hcop]
  have hmu : LeanLab.Perelli1996.Ramanujan103.ramanujanSum q 1
      = ((ArithmeticFunction.moebius q : ℤ) : ℂ) :=
    LeanLab.Perelli1996.Ramanujan103.ramanujanSum_coprime q 1 hq (Nat.coprime_one_right q)
  rw [hG, hconj, norm_conj, hram, hmu, Complex.norm_intCast]
  have h1 : |(ArithmeticFunction.moebius q : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  exact_mod_cast h1

/-- `G χ 1` is the Gauss sum of `χ⁻¹`, so its square norm is at most the modulus. -/
private theorem Gunit_one_norm_sq_le (χ : DirichletCharacter ℂ q) : ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 ≤ (q : ℝ) := by
  have hcongr : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))
      = ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q) a := by
    skip
    rw [Finset.sum_filter (s := Finset.univ)]
    refine Finset.sum_congr rfl ?_
    intro a _
    by_cases ha : IsUnit a
    · rw [if_pos ha, MulChar.inv_apply_eq_inv']
      have h1 : (χ a)⁻¹ = (starRingEnd ℂ) (χ a) := by
        have hnorm : ‖χ a‖ = 1 := by
          rw [show a = ((ha.unit : (ZMod q)ˣ) : ZMod q) from ha.unit_spec.symm]
          exact DirichletCharacter.unit_norm_eq_one χ ha.unit
        rw [Complex.inv_eq_conj hnorm]
      rw [h1]
      have h2 : ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q) a = ZMod.stdAddChar (-(1 * a)) := by
        rw [AddChar.mulShift_apply]
        simp
      rw [h2]
      ring
    · rw [if_neg ha, MulChar.map_nonunit _ ha, zero_mul]
  rw [hcongr]
  have hgs : (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q) a)
      = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q)) := rfl
  rw [hgs, gaussSum_mulShift_eq, norm_mul, mul_pow]
  rw [show χ⁻¹⁻¹ = χ from inv_inv χ]
  have hχ1 : ‖χ (((-1 : (ZMod q)ˣ)) : ZMod q)‖ ^ 2 = 1 := by
    rw [normSq_char (χ := χ) (((-1 : (ZMod q)ˣ)) : ZMod q), if_pos ((-1 : (ZMod q)ˣ).isUnit)]
  rw [hχ1, one_mul]
  have hb := LeanLab.Linnik1951.gauss_norm_le376 (χ⁻¹)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hsq : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 ≤ (Real.sqrt (q : ℝ)) ^ 2 := by
    nlinarith [hb, norm_nonneg (gaussSum χ⁻¹ ZMod.stdAddChar)]
  rwa [Real.sq_sqrt hq0] at hsq

/-- Per-prime character expansion: on a prime whose residue is a unit, the additive character
of the shifted fraction is `1/φ` times the Gauss-weighted character sum. -/
private theorem char_expansion_pointwise (q : ℕ) [NeZero q] (a : ZMod q) (p : Nat.Primes)
    (hp : IsUnit ((p : ℕ) : ZMod q)) :
    ZMod.stdAddChar (-(a * ((p : ℕ) : ZMod q)))
      = (1 / (q.totient : ℂ)) *
          ∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q) := by
  rw [sum_Gunit_mul_char a ((p : ℕ) : ZMod q) hp]
  have hφ : ((q.totient : ℂ)) ≠ 0 := by
    have h := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast h.ne'
  field_simp

/-- Splitting the exponential of the shifted fraction into the residue phase and the shift. -/
private theorem exp_split_phase (q : ℕ) [NeZero q] (z : ℝ) (a : ZMod q) (p : Nat.Primes) :
    ZMod.stdAddChar (-(a * ((p : ℕ) : ZMod q))) *
        Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)
      = Complex.exp
          ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) := by
  have h1 : ((a.val : ℕ) : ZMod q) = a := ZMod.natCast_zmod_val a
  have h2 : ((((p : ℕ) : ℤ)) : ZMod q) = ((p : ℕ) : ZMod q) := Int.cast_natCast _
  have hpos : a * ((p : ℕ) : ZMod q) = ((↑((a.val : ℤ) * ((p : ℕ) : ℤ))) : ZMod q) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, h1]
  rw [(LeanLab.PNTPort.LargeSieve.conj_stdAddChar (a * ((p : ℕ) : ZMod q))).symm, hpos,
    ZMod.stdAddChar_coe, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast,
    map_ofNat]
  ring


/-- Pointwise expansion of the prime series at a shifted unit fraction. -/
private theorem prime_fourier_expansion (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) (a : ZMod q) :
    primeFourier111 N ((a.val : ℝ) / q + z) =
      (1 / (q.totient : ℂ)) *
          ∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z +
        ∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0
          else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
            Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
  classical
  have hφ : ((q.totient : ℂ)) ≠ 0 := by
    have h := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast h.ne'
  set F : Nat.Primes → DirichletCharacter ℂ q → ℂ := fun p χ =>
    (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (χ ((p : ℕ) : ZMod q) * (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) with hF
  have hsumF : ∀ χ : DirichletCharacter ℂ q, Summable (fun p : Nat.Primes => F p χ) := by
    intro χ
    have hb : Summable (fun p : Nat.Primes => ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * Real.exp (-((p : ℕ) : ℝ) / N)) :=
      ((damping_summable111 N hN).comp_injective Nat.Primes.coe_nat_injective).mul_left _
    refine Summable.of_norm_bounded hb (fun p => ?_)
    simp only [hF]
    rw [norm_mul, norm_mul, norm_mul]
    have he : ‖Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    have hce : ‖(Real.exp (-((p : ℕ) : ℝ) / N) : ℂ)‖ = Real.exp (-((p : ℕ) : ℝ) / N) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hχ : ‖χ ((p : ℕ) : ZMod q)‖ ≤ 1 := by
      have h2 : ‖χ ((p : ℕ) : ZMod q)‖ ^ 2 ≤ 1 := by
        rw [normSq_char]
        split_ifs <;> norm_num
      nlinarith [norm_nonneg (χ ((p : ℕ) : ZMod q))]
    rw [he, hce, mul_one]
    have hc0 : 0 ≤ Real.exp (-((p : ℕ) : ℝ) / N) := (Real.exp_pos _).le
    have hstep : ‖χ ((p : ℕ) : ZMod q)‖ * Real.exp (-((p : ℕ) : ℝ) / N)
        ≤ 1 * Real.exp (-((p : ℕ) : ℝ) / N) :=
      mul_le_mul_of_nonneg_right hχ hc0
    calc ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * (‖χ ((p : ℕ) : ZMod q)‖ * Real.exp (-((p : ℕ) : ℝ) / N))
        ≤ ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * (1 * Real.exp (-((p : ℕ) : ℝ) / N)) :=
          mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
      _ = ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * Real.exp (-((p : ℕ) : ℝ) / N) := by ring
  have hp_id : ∀ p : Nat.Primes,
      (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)
      = (1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q, F p χ)
          + (if IsUnit ((p : ℕ) : ZMod q) then 0
              else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
                Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
    intro p
    by_cases hp : IsUnit ((p : ℕ) : ZMod q)
    · rw [if_pos hp, add_zero, ← exp_split_phase (q := q) z a p]
      rw [char_expansion_pointwise (q := q) a p hp]
      have hL : (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          ((1 / (q.totient : ℂ)) *
            (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q)) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))
          = ∑ χ : DirichletCharacter ℂ q, (1 / (q.totient : ℂ)) * F p χ := by
        rw [show (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
            ((1 / (q.totient : ℂ)) *
              (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q)) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))
            = (1 / (q.totient : ℂ)) *
              ((∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q)) *
              ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) by ring]
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        simp only [hF]
        ring
      rw [hL, Finset.mul_sum]
    · have hS : (∑ χ : DirichletCharacter ℂ q, F p χ) = 0 := by
        refine Finset.sum_eq_zero (fun χ _ => ?_)
        simp only [hF]
        rw [MulChar.map_nonunit _ hp]
        ring
      rw [if_neg hp, hS, mul_zero, zero_add]
  have hsA : Summable (fun p : Nat.Primes => (1 / (q.totient : ℂ)) *
      (∑ χ : DirichletCharacter ℂ q, F p χ)) := by
    have h : Summable (fun p : Nat.Primes => ∑ χ : DirichletCharacter ℂ q, F p χ) :=
      summable_sum (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
        (f := fun (χ : DirichletCharacter ℂ q) (p : Nat.Primes) => F p χ)
        (fun χ (_ : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q))) => hsumF χ)
    exact h.mul_left _
  have hsB : Summable (fun p : Nat.Primes => (if IsUnit ((p : ℕ) : ZMod q) then 0
      else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) := by
    have hb := (damping_summable111 N hN).comp_injective Nat.Primes.coe_nat_injective
    refine Summable.of_norm_bounded hb (fun p => ?_)
    by_cases hp : IsUnit ((p : ℕ) : ZMod q)
    · rw [if_pos hp, norm_zero]
      exact (Real.exp_pos _).le
    · rw [if_neg hp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact le_rfl
  rw [primeFourier111, tsum_congr hp_id, Summable.tsum_add hsA hsB]
  congr 1
  rw [tsum_mul_left]
  congr 1
  have hswap : (∑' (p : Nat.Primes), ∑ χ : DirichletCharacter ℂ q, F p χ)
      = ∑ χ : DirichletCharacter ℂ q, ∑' (p : Nat.Primes), F p χ :=
    Summable.tsum_finsetSum (fun χ (_ : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q))) =>
      hsumF χ)
  rw [hswap]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  rw [characterPrime280, ← tsum_mul_left]

/-- The squared character combination summed over the reduced residues. The Gauss vectors of
distinct characters are orthogonal, so only the diagonal survives: the sum is the totient times
the character squares weighted by the squared Gauss norms at `1`. -/
private theorem sum_normSq_chi_combo (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        ‖∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z‖ ^ 2
      = (q.totient : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, ‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 := by
  classical
  have hreal : ∀ w : ℂ, ‖w‖ ^ 2 = (w * (starRingEnd ℂ) w).re := by
    intro w
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hresumA : ∀ f : ZMod q → ℂ,
      (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), (f a).re)
        = (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), f a).re := by
    intro f
    have h := map_sum Complex.reCLM f
      ((Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a))
    simpa only [Complex.reCLM_apply] using h.symm
  have hresumC : ∀ f : DirichletCharacter ℂ q → ℂ,
      (∑ χ : DirichletCharacter ℂ q, (f χ).re) = (∑ χ : DirichletCharacter ℂ q, f χ).re := by
    intro f
    have h := map_sum Complex.reCLM f (Finset.univ : Finset (DirichletCharacter ℂ q))
    simpa only [Complex.reCLM_apply] using h.symm
  have hre : ∀ χ : DirichletCharacter ℂ q,
      ((characterPrime280 χ N z * (starRingEnd ℂ) (characterPrime280 χ N z)) *
          ((q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)))))).re
        = (q.totient : ℝ) * (‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
    intro χ
    rw [Complex.mul_conj, Complex.mul_conj]
    rw [show ((q.totient : ℂ)) = (((q.totient : ℝ)) : ℂ) by simp]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    ring
  have hcomplex :
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)
        = ∑ χ : DirichletCharacter ℂ q,
            (characterPrime280 χ N z * (starRingEnd ℂ) (characterPrime280 χ N z)) *
              ((q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))))) := by
    have hexp : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)
        = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
            ∑ χ : DirichletCharacter ℂ q, ∑ χ' : DirichletCharacter ℂ q,
              ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z) *
                (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)) * characterPrime280 χ' N z) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_sum, Finset.sum_mul_sum]
    rw [hexp, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [Finset.sum_comm]
    have hfac : ∀ a : ZMod q,
        ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z) *
            (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)
        = (characterPrime280 χ N z * (starRingEnd ℂ) (characterPrime280 χ N z)) *
            ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)))) := by
      intro a
      rw [map_mul]
      ring
    rw [Finset.sum_eq_single χ]
    · have hstep : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
            ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z) *
              (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)
          = (characterPrime280 χ N z * (starRingEnd ℂ) (characterPrime280 χ N z)) *
              ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
                ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => hfac a)
      rw [hstep, sum_Gunit_orth χ χ, if_pos rfl]
    · intro χ' _ hne
      have hfac' : ∀ a : ZMod q,
          ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z) *
              (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)) * characterPrime280 χ' N z)
          = (characterPrime280 χ N z * (starRingEnd ℂ) (characterPrime280 χ' N z)) *
              ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))) := by
        intro a
        rw [map_mul]
        ring
      have hstep : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
            ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z) *
              (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)) * characterPrime280 χ' N z)
          = (characterPrime280 χ N z * (starRingEnd ℂ) (characterPrime280 χ' N z)) *
              ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
                ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => hfac' a)
      rw [hstep, sum_Gunit_orth χ χ', if_neg (fun h => hne h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ χ) h
  calc ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        ‖∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z‖ ^ 2
      = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          ((∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)).re := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        exact hreal _
    _ = (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)).re := by
        exact hresumA _
    _ = (∑ χ : DirichletCharacter ℂ q,
          (characterPrime280 χ N z * (starRingEnd ℂ) (characterPrime280 χ N z)) *
            ((q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)))))).re := by
        rw [hcomplex]
    _ = ∑ χ : DirichletCharacter ℂ q,
          (q.totient : ℝ) * (‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
        rw [← hresumC]
        exact Finset.sum_congr rfl (fun χ _ => hre χ)
    _ = (q.totient : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, ‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 := by
        rw [Finset.mul_sum]

end





open MeasureTheory Filter Finset

private theorem card_reduced_aux1622 (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  exact congrArg Finset.card (Finset.filter_congr (fun a _ => Nat.coprime_comm))

set_option maxHeartbeats 2000000 in
private theorem pointwise_assembly (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      (8 / (q.totient : ℝ)) *
        (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime280 χ N z‖ ^ 2) +
        8 * (q.totient : ℝ) * Real.log q ^ 2 := by
  classical
  have hq0 : 0 < q := by omega
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    have := Nat.totient_pos.mpr hq0
    exact_mod_cast this
  set S := Finset.univ.filter (fun c : ZMod q => IsUnit c) with hS
  set FF := Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) with hFF
  set X : ℝ := ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
      (q : ℝ) * ∑ χ ∈ FF, ‖characterPrime280 χ N z‖ ^ 2 with hX
  -- membership characterisations
  have hSmem : ∀ c : ZMod q, c ∈ S ↔ IsUnit c := by
    intro c
    rw [hS]
    simp
  have hRmem : ∀ a : ℕ, a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ↔
      a < q ∧ Nat.Coprime a q := by
    intro a
    simp
  have hX0 : 0 ≤ X := by
    rw [hX]
    have h1 : (0 : ℝ) ≤ ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
      positivity
    have h2 : (0 : ℝ) ≤ ∑ χ ∈ FF, ‖characterPrime280 χ N z‖ ^ 2 :=
      Finset.sum_nonneg (fun χ _ => by positivity)
    have h3 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    nlinarith
  -- step 1: the reduced residues of `range q` are the units of `ZMod q`
  have hbij : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2)
      = ∑ c ∈ S, ‖primeFourier111 N ((c.val : ℝ) / q + z)‖ ^ 2 := by
    refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod q)) (fun c : ZMod q => c.val)
      ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact (hSmem _).mpr ((ZMod.isUnit_iff_coprime a q).mpr ((hRmem a).mp ha).2)
    · intro c hc
      have hunit : IsUnit (((c.val : ℕ)) : ZMod q) := by
        rw [ZMod.natCast_zmod_val]
        exact (hSmem c).mp hc
      exact (hRmem c.val).mpr ⟨ZMod.val_lt c, (ZMod.isUnit_iff_coprime c.val q).mp hunit⟩
    · intro a ha
      exact ZMod.val_natCast_of_lt ((hRmem a).mp ha).1
    · intro c _
      exact ZMod.natCast_zmod_val c
    · intro a ha
      rw [ZMod.val_natCast_of_lt ((hRmem a).mp ha).1]
  have hcardS : S.card = q.totient := by
    have hb : S.card = ((Finset.range q).filter (fun a => Nat.Coprime a q)).card := by
      refine Finset.card_nbij' (fun c : ZMod q => c.val) (fun a : ℕ => (a : ZMod q))
        ?_ ?_ ?_ ?_
      · intro c hc
        have hunit : IsUnit (((c.val : ℕ)) : ZMod q) := by
          rw [ZMod.natCast_zmod_val]
          exact (hSmem c).mp hc
        exact (hRmem c.val).mpr ⟨ZMod.val_lt c, (ZMod.isUnit_iff_coprime c.val q).mp hunit⟩
      · intro a ha
        exact (hSmem _).mpr ((ZMod.isUnit_iff_coprime a q).mpr ((hRmem a).mp ha).2)
      · intro c _
        exact ZMod.natCast_zmod_val c
      · intro a ha
        exact ZMod.val_natCast_of_lt ((hRmem a).mp ha).1
    rw [hb, card_reduced_aux1622]
  -- the principal Gauss vector has norm at most one
  have hG1 : ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ^ 2 ≤ 1 := by
    have hG : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))
        = ∑ c ∈ S, ZMod.stdAddChar (-(1 * c)) := by
      rw [hS]
      skip
      refine Finset.sum_congr rfl (fun c hc => ?_)
      have h1 : (1 : DirichletCharacter ℂ q) c = 1 := by
        obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hc).2
        simp
      rw [h1, map_one, mul_one]
    rw [hG]
    nlinarith [unit_gauss_principal_le q,
      norm_nonneg (∑ c ∈ S, ZMod.stdAddChar (-(1 * c)))]
  -- the character sum is bounded by the bracket of the statement
  have hGbound : (∑ χ : DirichletCharacter ℂ q,
        ‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) ≤ X := by
    have hsplit_chi : (∑ χ : DirichletCharacter ℂ q,
          ‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
        = ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 *
            ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ^ 2
          + ∑ χ ∈ FF, ‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 := by
      have h := Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
        (p := fun χ : DirichletCharacter ℂ q => χ = 1)
        (f := fun χ => ‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
      rw [← h]
      have hsingle : (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => χ = 1) = {1} := by
        ext χ
        simp
      have hrest : (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => ¬ (χ = 1)) = FF := by
        rw [hFF]
      rw [hsingle, hrest, Finset.sum_singleton]
    rw [hsplit_chi, hX]
    have hb1 : ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 *
          ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ^ 2
        ≤ ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hG1 (by positivity)
    have hb2 : (∑ χ ∈ FF, ‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
        ≤ ∑ χ ∈ FF, ‖characterPrime280 χ N z‖ ^ 2 * (q : ℝ) :=
      Finset.sum_le_sum (fun χ _ =>
        mul_le_mul_of_nonneg_left (Gunit_one_norm_sq_le χ) (by positivity))
    have hb2' : (∑ χ ∈ FF, ‖characterPrime280 χ N z‖ ^ 2 * (q : ℝ))
        = (q : ℝ) * ∑ χ ∈ FF, ‖characterPrime280 χ N z‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun χ _ => by ring)
    linarith [hb1, hb2, hb2'.le]
  -- the squared phi-normalised character sums
  have hfac : ∀ c : ZMod q,
      ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)‖ ^ 2
        = (1 / (q.totient : ℝ)) ^ 2 *
            ‖∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z‖ ^ 2 := by
    intro c
    rw [norm_mul, norm_div, Complex.norm_natCast, norm_one, one_div, mul_pow]
  have hA : (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
        (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)‖ ^ 2)
      ≤ (1 / (q.totient : ℝ)) * X := by
    have horth := sum_normSq_chi_combo N q hN z
    have hsum : (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)‖ ^ 2)
        = (1 / (q.totient : ℝ)) ^ 2 *
            ((q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q,
              ‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
      rw [Finset.sum_congr rfl (fun c _ => hfac c), ← Finset.mul_sum]
      rw [hS, horth]
    rw [hsum]
    have heq : (1 / (q.totient : ℝ)) ^ 2 *
          ((q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q,
            ‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
        = (1 / (q.totient : ℝ)) * (∑ χ : DirichletCharacter ℂ q,
            ‖characterPrime280 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hGbound (by positivity)
  -- the bound at each residue
  have hpoint : ∀ c ∈ S, ‖primeFourier111 N ((c.val : ℝ) / q + z)‖ ^ 2 ≤
      2 * ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)‖ ^ 2 + 2 * (2 * Real.log q) ^ 2 := by
    intro c _
    have hexp := prime_fourier_expansion N q hN z c
    set A : ℂ := (1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
        (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z) with hAdef
    set Tt : ℂ := ∑' p : Nat.Primes, (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((c.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I)) with hTdef
    have hT : ‖Tt‖ ≤ 2 * Real.log q := by
      rw [hTdef]
      exact corr_bound N q hq z c
    have hlog : 0 ≤ Real.log q :=
      Real.log_nonneg (by linarith [show (1 : ℝ) ≤ 2 by norm_num,
        show (2 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq])
    have h3 : ‖A + Tt‖ ^ 2 ≤ (‖A‖ + 2 * Real.log q) ^ 2 := by
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      linarith [norm_add_le A Tt]
    have h4 : (‖A‖ + 2 * Real.log q) ^ 2 ≤
        2 * ‖A‖ ^ 2 + 2 * (2 * Real.log q) ^ 2 := by
      nlinarith [sq_nonneg (‖A‖ - 2 * Real.log q)]
    have hgoal : ‖A + Tt‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * (2 * Real.log q) ^ 2 := by
      linarith [h3, h4]
    rw [hexp, hAdef, hTdef]
    exact hgoal
  -- the correction terms
  have hcorr : (∑ c ∈ S, ‖primeFourier111 N ((c.val : ℝ) / q + z)‖ ^ 2) ≤
      2 * (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)‖ ^ 2)
        + 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 := by
    have h1 := Finset.sum_le_sum hpoint
    have h2 : (∑ c ∈ S, (2 * ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
            (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)‖ ^ 2 + 2 * (2 * Real.log q) ^ 2))
        = 2 * (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
            (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime280 χ N z)‖ ^ 2)
          + 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    linarith [h1, h2.le, h2.ge]
  -- the final comparison
  have hmain : (∑ c ∈ S, ‖primeFourier111 N ((c.val : ℝ) / q + z)‖ ^ 2) ≤
      2 * ((1 / (q.totient : ℝ)) * X) + 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 := by
    linarith [hcorr, hA]
  have hlast : 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 =
      8 * (q.totient : ℝ) * Real.log q ^ 2 := by
    rw [hcardS]
    ring
  have hfirst : 2 * ((1 / (q.totient : ℝ)) * X) ≤ (8 / (q.totient : ℝ)) * X := by
    have h1 : 2 * ((1 / (q.totient : ℝ)) * X) = (2 / (q.totient : ℝ)) * X := by ring
    have h2 : (2 / (q.totient : ℝ)) * X ≤ (8 / (q.totient : ℝ)) * X := by
      apply mul_le_mul_of_nonneg_right _ hX0
      apply div_le_div_of_nonneg_right _ hφpos.le
      norm_num
    linarith
  rw [hbij]
  linarith [hmain, hlast.le, hlast.ge, hfirst]


/-- LEAF. The finite unit character step, pointwise in z. At any z the sum of the squares
of the prime system shifted to the reduced residues below q is at most a constant over the
totient of q times the principal square plus q times the sum of the nonprincipal squares,
plus a constant times the totient of q times the square of the logarithm of q. The
orthogonality of the unit group gives the coefficient one over the totient, the Gauss
squares are bounded by q, and the primes dividing q are absorbed in the logarithmic term.
No tau, no integration and no growth hypothesis occurs. -/
theorem rational_pointwise_characters1622 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q], 1 ≤ N → 2 ≤ q → ∀ z : ℝ,
      (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      B / (q.totient : ℝ) *
        (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * Real.log q ^ 2 := by
  refine ⟨8, by norm_num, ?_⟩
  intro N q _ hN hq z
  exact pointwise_assembly N q hN hq z

/-- The doubled system mass, from the two geometry steps and the pointwise finite
character bound. The target statement is unchanged. -/
theorem doubled_system_characters1622_split :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q] (τ : ℝ), 1 ≤ N → 2 ≤ q → 4 ≤ τ →
      (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, ‖primeFourier111 N α‖ ^ 2) ≤
        B / (q.totient : ℝ) *
          ((∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
            (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
                ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * (2 / ((q : ℝ) * τ)) * Real.log q ^ 2 := by
  classical
  obtain ⟨B, hB, hb⟩ := rational_pointwise_characters1622
  refine ⟨2 * B, by positivity, ?_⟩
  intro N q _ τ hN hq hτ
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hτp : 0 < τ := by linarith
  set r := 2 / ((q : ℝ) * τ) with hrdef
  have hr : 0 < r := by positivity
  let F : Finset (DirichletCharacter ℂ q) := Finset.univ.filter (fun χ => χ ≠ 1)
  let J : ℝ → ℝ := fun z => ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
    (q : ℝ) * ∑ χ ∈ F, ‖characterPrime280 χ N z‖ ^ 2
  have hp : Continuous (fun z : ℝ => ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) :=
    (continuous_character_prime357 (1 : DirichletCharacter ℂ q) N hN).norm.pow 2
  have hc (χ : DirichletCharacter ℂ q) :
      Continuous (fun z : ℝ => ‖characterPrime280 χ N z‖ ^ 2) :=
    (continuous_character_prime357 χ N hN).norm.pow 2
  have hJ : Continuous J := hp.add ((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _)
  have hJ0 : ∀ z, 0 ≤ J z := by intro z; dsimp [J]; positivity
  have hS : Continuous (fun z => ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) :=
    continuous_finset_sum _ (fun a _ =>
      ((continuous_prime_fourier111 N hN).norm.pow 2).comp (continuous_const.add continuous_id))
  have hgeo := rational_cover_integral1622 q τ (fun α => ‖primeFourier111 N α‖ ^ 2)
    ((continuous_prime_fourier111 N hN).norm.pow 2) (fun α => sq_nonneg _)
    (rational_cover1622 q τ hq hτ)
  have hmono : (∫ z in -r..r, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      ∫ z in -r..r, B / (q.totient : ℝ) * J z + B * (q.totient : ℝ) * Real.log q ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith) (hS.intervalIntegrable _ _)
      (((hJ.const_mul _).add continuous_const).intervalIntegrable _ _)
      (fun z _ => hb N q hN hq z)
  have hsplit : (∫ z in -r..r, J z) =
      (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
        (q : ℝ) * ∑ χ ∈ F, ∫ z in -r..r, ‖characterPrime280 χ N z‖ ^ 2 := by
    dsimp [J]
    rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _)
      (((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finset_sum (fun χ _ => (hc χ).intervalIntegrable _ _)]
  have hpos : 0 ≤ B / (q.totient : ℝ) * (∫ z in -r..r, J z) :=
    mul_nonneg (div_nonneg hB.le (Nat.cast_nonneg _))
      (intervalIntegral.integral_nonneg_of_forall (by linarith) hJ0)
  rw [intervalIntegral.integral_add ((hJ.const_mul _).intervalIntegrable _ _)
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfinal : B / (q.totient : ℝ) * (∫ z in -r..r, J z) +
      (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) ≤
      (2 * B) / (q.totient : ℝ) * (∫ z in -r..r, J z) +
        (2 * B) * (q.totient : ℝ) * r * Real.log q ^ 2 := by
    calc
      _ ≤ 2 * (B / (q.totient : ℝ) * (∫ z in -r..r, J z)) +
          (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) := by linarith
      _ = _ := by ring
  have hh := hgeo.trans (hmono.trans hfinal)
  rw [hsplit] at hh
  exact hh

end LeanLab.Linnik1951
