import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
The real primitive conductor classification is cut here into the two numerical
ingredients it uses: the conductor divides eight times its odd radical, and the
conductor is never exactly twice its odd radical. The step from those two facts to
the three listed conductors is arithmetic and is discharged in the assembly below.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- The odd radical of a modulus is positive. -/
private theorem oddRad131_pos481 (r : ℕ) : 0 < oddRad131 r := by
  unfold oddRad131
  rcases Finset.eq_empty_or_nonempty (r.primeFactors.filter (fun p => 2 < p)) with h | ⟨p, hp⟩
  · rw [h, Finset.prod_empty]
    exact Nat.zero_lt_one
  · exact Finset.prod_pos
      (fun q hq => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos)

/-- The odd radical of a modulus divides that modulus. -/
private theorem oddRad131_dvd481 (r : ℕ) : oddRad131 r ∣ r := by
  unfold oddRad131
  refine Finset.prod_primes_dvd r (fun p hp => ?_) (fun p hp => ?_)
  · exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime
  · exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1

/-! ### Helper lemmas for the conductor classification -/

private lemma modEq_mul_of_coprime_dav481 {m n a b : ℕ} (h : m.Coprime n)
    (h1 : a ≡ b [MOD m]) (h2 : a ≡ b [MOD n]) : a ≡ b [MOD m * n] := by
  rw [Nat.modEq_iff_dvd] at h1 h2 ⊢
  simpa [Nat.cast_mul] using IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.mpr h) h1 h2

/-- A number congruent to `1` modulo an odd `m` and itself odd is congruent to `1`
modulo `2 * m`. -/
private lemma modEq_two_mul_of_odd_dav481 {m a : ℕ} (hm : Odd m) (ha : Odd a) (h : a ≡ 1 [MOD m]) :
    a ≡ 1 [MOD 2 * m] := by
  obtain ⟨c, hc⟩ := ha
  have ha1 : 1 ≤ a := by omega
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add ha1).mp h.symm
  have hmul : m * t = 2 * c := by omega
  have htEven : Even t := by
    by_contra hcon
    have hodd : Odd (m * t) := hm.mul (Nat.not_even_iff_odd.mp hcon)
    rw [hmul] at hodd
    exact Nat.not_even_iff_odd.mpr hodd ⟨c, by ring⟩
  obtain ⟨u, hu⟩ := htEven
  refine ((Nat.modEq_iff_exists_eq_add ha1).mpr ⟨u, ?_⟩).symm
  have htu : t = 2 * u := by omega
  rw [ht, htu]
  ring

/-- `(1 + x) ^ n = 1 + n * x` when `x ^ 2 = 0`. -/
private lemma one_add_pow_of_sq_eq_zero_dav481 {R : Type*} [CommSemiring R] {x : R} (hx : x ^ 2 = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + (n : R) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      have h1 : (1 + (n : R) * x) * (1 + x) = 1 + ((n : R) + 1) * x + (n : R) * x ^ 2 := by
        ring
      have h2 : ((n + 1 : ℕ) : R) = (n : R) + 1 := by push_cast; ring
      rw [h2, h1, hx, mul_zero, add_zero]

/-- A product of odd primes is odd, with no factor `2`. -/
private lemma odd_prod_primes_dav481 {s : Finset ℕ} (h : ∀ p ∈ s, Nat.Prime p) (h2 : ∀ p ∈ s, p ≠ 2) :
    Odd (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      refine Odd.mul ?_ (ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
        (fun p hp => h2 p (Finset.mem_insert_of_mem hp)))
      rcases (h a (Finset.mem_insert_self a s)).eq_two_or_odd with h3 | h3
      · exact absurd h3 (h2 a (Finset.mem_insert_self a s))
      · exact Nat.odd_iff.mpr h3

/-- A product over a subset of a set of primes divides the product over the set. -/
private lemma prod_subset_dvd_dav481 {S T : Finset ℕ} (h : S ⊆ T) : ∏ p ∈ S, p ∣ ∏ p ∈ T, p := by
  have hdvd : ∏ p ∈ T, (if p ∈ S then p else 1) ∣ ∏ p ∈ T, p := by
    refine Finset.prod_dvd_prod_of_dvd _ _ ?_
    intro p _
    by_cases hp : p ∈ S
    · rw [if_pos hp]
    · rw [if_neg hp]; exact one_dvd p
  have heq : ∏ p ∈ T, (if p ∈ S then p else 1) = ∏ p ∈ S, p := by
    rw [← Finset.prod_subset h (fun p _ hp => if_neg hp)]
    exact Finset.prod_congr rfl (fun p hp => if_pos hp)
  rwa [heq] at hdvd

/-! #### Squares modulo `2 ^ k` -/

private lemma lift_step_dav481 {a n b : ℕ} (hn : 3 ≤ n) (hbo : Odd b) (hb : b ^ 2 ≡ a [MOD 2 ^ n]) :
    ∃ b' : ℕ, Odd b' ∧ b' ^ 2 ≡ a [MOD 2 ^ (n + 1)] := by
  by_cases hcase : b ^ 2 ≡ a [MOD 2 ^ (n + 1)]
  · exact ⟨b, hbo, hcase⟩
  · have hdiv : (2 : ℤ) ^ n ∣ (a : ℤ) - ((b : ℤ)) ^ 2 := by
      have h := Nat.modEq_iff_dvd.mp hb
      simpa using h
    obtain ⟨t, ht⟩ := hdiv
    have htodd : Odd t := by
      rcases Int.even_or_odd t with hev | hod
      · exfalso
        apply hcase
        rw [Nat.modEq_iff_dvd]
        obtain ⟨s, hs⟩ := hev
        refine ⟨s, ?_⟩
        push_cast
        rw [show (2 : ℤ) ^ (n + 1) = (2 : ℤ) ^ n * 2 by rw [pow_succ], ht, hs]
        ring
      · exact hod
    obtain ⟨s, hs⟩ := htodd
    obtain ⟨c, hc⟩ := hbo
    have hbt : (2 : ℤ) ∣ (b : ℤ) - t := by
      refine ⟨(c : ℤ) - s, ?_⟩
      rw [hc, hs]
      push_cast
      ring
    refine ⟨b + 2 ^ (n - 1), ?_, ?_⟩
    · refine ⟨c + 2 ^ (n - 2), ?_⟩
      have h2n : 2 * 2 ^ (n - 2) = 2 ^ (n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hc, ← h2n]
      ring
    · rw [Nat.modEq_iff_dvd]
      push_cast
      have hp1 : (2 : ℤ) ^ n = (2 : ℤ) ^ (n - 1) * 2 := by
        have hn1 : n = n - 1 + 1 := by omega
        conv_lhs => rw [hn1]
        rw [pow_succ]
      have hp2 : (2 : ℤ) ^ (2 * (n - 1)) = ((2 : ℤ) ^ (n - 1)) ^ 2 := by
        rw [← pow_mul, mul_comm]
      have ha_exp : (a : ℤ) = (b : ℤ) ^ 2 + (2 : ℤ) ^ n * t := by linarith [ht]
      have hkey : (a : ℤ) - ((b : ℤ) + (2 : ℤ) ^ (n - 1)) ^ 2
          = -((2 : ℤ) ^ n * ((b : ℤ) - t)) - (2 : ℤ) ^ (2 * (n - 1)) := by
        rw [ha_exp, hp1, hp2]
        ring
      rw [hkey]
      have hA : (2 : ℤ) ^ (n + 1) ∣ -((2 : ℤ) ^ n * ((b : ℤ) - t)) := by
        have := mul_dvd_mul_left ((2 : ℤ) ^ n) hbt
        rw [← pow_succ] at this
        exact dvd_neg.mpr this
      have hB : (2 : ℤ) ^ (n + 1) ∣ (2 : ℤ) ^ (2 * (n - 1)) :=
        pow_dvd_pow 2 (by omega)
      exact dvd_sub hA hB

/-- Every integer congruent to `1` modulo `8` is a square modulo `2 ^ k` for `k ≥ 3`. -/
private lemma exists_sq_modEq_two_pow_dav481 {a : ℕ} (ha : a ≡ 1 [MOD 8]) :
    ∀ k : ℕ, 3 ≤ k → ∃ b : ℕ, Odd b ∧ b ^ 2 ≡ a [MOD 2 ^ k] := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨1, odd_one, by simpa using ha.symm⟩
  | succ n hn ih =>
      obtain ⟨b, hbo, hb⟩ := ih
      exact lift_step_dav481 hn hbo hb

/-! #### Real characters -/

section

variable {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}

private lemma chi_pow_apply_dav481 (x : ZMod r) (n : ℕ) : χ (x ^ n) = χ x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, map_mul, ih, pow_succ]

/-- A real character takes the value `1` on any element of odd order. -/
private lemma chi_eq_one_of_odd_pow_dav481 (hreal : ∀ a, (χ a).im = 0) {n : ℕ} (hn : Odd n)
    {u : (ZMod r)ˣ} (hu : u ^ n = 1) : χ (u : ZMod r) = 1 := by
  have h1 : (χ (u : ZMod r)) ^ n = 1 := by
    rw [← chi_pow_apply_dav481, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
  set z : ℝ := (χ (u : ZMod r)).re with hz
  have hzc : χ (u : ZMod r) = ((z : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hz]
    · simpa [hz] using hreal (u : ZMod r)
  have hzn : z ^ n = 1 := by
    have h2 : ((z ^ n : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, ← hzc, h1, Complex.ofReal_one]
    exact Complex.ofReal_inj.mp h2
  have hz1 : z = 1 := (Odd.strictMono_pow hn).injective (by rw [hzn, one_pow])
  rw [hzc, hz1]
  norm_num

/-- A real character is `±1` at every unit, so its square there is `1`. -/
private lemma chi_sq_eq_one_dav481 (hreal : ∀ a, (χ a).im = 0) (u : (ZMod r)ˣ) :
    (χ (u : ZMod r)) ^ 2 = 1 := by
  have h1 : (χ (u : ZMod r)) ^ Fintype.card (ZMod r)ˣ = 1 := by
    rw [← chi_pow_apply_dav481, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have hN0 : Fintype.card (ZMod r)ˣ ≠ 0 := Fintype.card_ne_zero
  set z : ℝ := (χ (u : ZMod r)).re with hz
  have hzc : χ (u : ZMod r) = ((z : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hz]
    · simpa [hz] using hreal (u : ZMod r)
  have hzn : z ^ (Fintype.card (ZMod r)ˣ) = 1 := by
    have h2 : ((z ^ (Fintype.card (ZMod r)ˣ) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, ← hzc, h1, Complex.ofReal_one]
    exact Complex.ofReal_inj.mp h2
  have hz2 : z ^ 2 = 1 := by
    have ht : (z ^ 2) ^ (Fintype.card (ZMod r)ˣ) = 1 := by
      rw [← pow_mul, mul_comm 2 (Fintype.card (ZMod r)ˣ), pow_mul, hzn, one_pow]
    rcases eq_or_lt_of_le (sq_nonneg z) with h | h
    · rw [← h, zero_pow hN0] at ht
      exact absurd ht zero_ne_one
    · rcases lt_trichotomy (z ^ 2) 1 with hlt | heq | hgt
      · exact absurd ht (ne_of_lt (pow_lt_one₀ h.le hlt hN0))
      · exact heq
      · exact absurd ht (ne_of_gt (one_lt_pow₀ hgt hN0))
  have hfin : (((z : ℝ)) : ℂ) ^ 2 = 1 := by
    rw [show (((z : ℝ)) : ℂ) ^ 2 = (((z ^ 2 : ℝ)) : ℂ) from (Complex.ofReal_pow z 2).symm,
      hz2, Complex.ofReal_one]
  rw [hzc]
  exact hfin

/-- If a character kills the kernel of the reduction to level `d`, its conductor divides `d`. -/
private lemma conductor_dvd_of_ker_dav481 {d : ℕ} (hd : d ∣ r)
    (h : ∀ u : (ZMod r)ˣ, ZMod.unitsMap hd u = 1 → χ (u : ZMod r) = 1) :
    χ.conductor ∣ d := by
  have hft : χ.FactorsThrough d := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    exact Units.ext (by rw [MulChar.coe_toUnitHom, h u hu, Units.val_one])
  exact (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mp hft

/-- The natural representative of a unit, as an element. -/
private lemma val_cast_dav481 (u : (ZMod r)ˣ) : (((u : ZMod r).val : ℕ) : ZMod r) = (u : ZMod r) :=
  ZMod.natCast_zmod_val _

/-- Membership in the kernel of the reduction map, read on the natural representative. -/
private lemma unitsMap_eq_one_iff_dav481 {d : ℕ} (hd : d ∣ r) (u : (ZMod r)ˣ) :
    ZMod.unitsMap hd u = 1 ↔ ((u : ZMod r).val) ≡ 1 [MOD d] := by
  constructor
  · intro h
    have h2 : ((↑(ZMod.unitsMap hd u) : ZMod d)) = 1 := by rw [h]; rfl
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val] at h2
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa using h2
  · intro h
    refine Units.ext ?_
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val, Units.val_one]
    simpa using (ZMod.natCast_eq_natCast_iff _ 1 d).mpr h

end

/-! #### The conductor lemmas -/

section

variable {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}

/-- `r` has no odd square divisor. -/
private lemma not_sq_dvd_of_real_primitive_dav481 (hprim : χ.IsPrimitive) (hreal : ∀ a, (χ a).im = 0)
    {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) : ¬ (p ^ 2 ∣ r) := by
  intro hsq
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · obtain ⟨k, hk⟩ := Nat.odd_iff.mpr h
      have h2 := hp.two_le
      omega
  have hr9 : 9 ≤ r := by
    have h1 : p * p ≤ r :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne r)) (by simpa [pow_two] using hsq)
    nlinarith
  have hr1 : r ≠ 1 := by omega
  haveI : Nontrivial (ZMod r) := ZMod.nontrivial_iff.mpr hr1
  obtain ⟨s, hs⟩ := hsq
  set d : ℕ := p * s with hd
  have hdp : d * p = r := by rw [hd, hs]; ring
  have hdvd : d ∣ r := ⟨p, by rw [hd, hs]; ring⟩
  have hd2 : ((d : ℕ) : ZMod r) ^ 2 = 0 := by
    have hdvd2 : r ∣ d ^ 2 := ⟨s, by rw [hd, hs]; ring⟩
    obtain ⟨k, hk⟩ := hdvd2
    have hzero : ((d ^ 2 : ℕ) : ZMod r) = 0 := by
      rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rwa [Nat.cast_pow] at hzero
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact Nat.odd_iff.mpr h
  have hker : ∀ u : (ZMod r)ˣ, ZMod.unitsMap hdvd u = 1 → χ (u : ZMod r) = 1 := by
    intro u hu
    set a : ℕ := (u : ZMod r).val with ha
    have hcast : ((a : ℕ) : ZMod r) = (u : ZMod r) := val_cast_dav481 u
    have hmod : a ≡ 1 [MOD d] := (unitsMap_eq_one_iff_dav481 hdvd u).mp hu
    have hane : a ≠ 0 := by
      intro h0
      exact Units.ne_zero u (by rw [← hcast, h0, Nat.cast_zero])
    have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr hane
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add ha1).mp hmod.symm
    have hx : (u : ZMod r) = 1 + ((d * t : ℕ) : ZMod r) := by
      rw [← hcast, ht]
      push_cast
      ring
    have hsquare : (((d * t : ℕ)) : ZMod r) ^ 2 = 0 := by
      rw [Nat.cast_mul, mul_pow, hd2, zero_mul]
    have hpe : ((p : ℕ) : ZMod r) * ((d * t : ℕ) : ZMod r) = 0 := by
      have hpdvd : r ∣ p * (d * t) := ⟨t, by rw [← hdp]; ring⟩
      obtain ⟨k, hk⟩ := hpdvd
      rw [← Nat.cast_mul, hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    have hupow : (u : ZMod r) ^ p = 1 := by
      rw [hx, one_add_pow_of_sq_eq_zero_dav481 hsquare p, hpe, add_zero]
    have hupow' : u ^ p = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact hupow
    exact chi_eq_one_of_odd_pow_dav481 hreal hpodd hupow'
  have hcond : χ.conductor ∣ d := conductor_dvd_of_ker_dav481 hdvd hker
  have hrd : r ∣ d := by rw [← hprim]; exact hcond
  have hdpos : 0 < d := by
    have hs0 : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h0 | hpos
      · rw [h0] at hs
        simp at hs
        omega
      · exact hpos
    rw [hd]
    positivity
  have hdlt : d < r := by
    have h1 : d * 1 < d * p := Nat.mul_lt_mul_of_pos_left (by omega : 1 < p) hdpos
    rw [hdp] at h1
    simpa using h1
  have hle : r ≤ d := Nat.le_of_dvd hdpos hrd
  omega

/-- The `2`-part of the conductor is at most `8`. -/
private lemma factorization_two_le_three_dav481 (hprim : χ.IsPrimitive) (hreal : ∀ a, (χ a).im = 0) :
    r.factorization 2 ≤ 3 := by
  by_contra hle
  have he3 : 3 ≤ r.factorization 2 := by omega
  have hrne : r ≠ 0 := NeZero.ne r
  set e : ℕ := r.factorization 2 with he
  set m : ℕ := r / 2 ^ e with hm
  have hKdvd : 2 ^ e ∣ r := by
    rw [he]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hrne).mpr le_rfl
  have hr_eq : 2 ^ e * m = r := by rw [hm]; exact Nat.mul_div_cancel' hKdvd
  have hmC : (2 : ℕ).Coprime m := by
    rw [hm, he]
    exact Nat.coprime_ordCompl Nat.prime_two hrne
  have hmOdd : Odd m := Nat.coprime_two_left.mp hmC
  have h8K : (8 : ℕ) ∣ 2 ^ e := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 (by omega)
  have hd : 8 * m ∣ r := by
    rw [← hr_eq]
    exact mul_dvd_mul_right h8K m
  have hmpos : 0 < m := by
    rw [hm]
    exact Nat.div_pos (Nat.le_of_dvd (by positivity) hKdvd) (by positivity)
  have hr2 : r ≠ 1 := by
    intro h1
    have h2 : 2 ^ e ≤ r := by
      rw [← hr_eq]
      calc 2 ^ e = 2 ^ e * 1 := (mul_one _).symm
        _ ≤ 2 ^ e * m := Nat.mul_le_mul_left _ hmpos
    have h3 : 2 ≤ 2 ^ e := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  haveI : Nontrivial (ZMod r) := ZMod.nontrivial_iff.mpr hr2
  have hmC' : m.Coprime (2 ^ e) := hmC.symm.pow_right e
  have hker : ∀ u : (ZMod r)ˣ, ZMod.unitsMap hd u = 1 → χ (u : ZMod r) = 1 := by
    intro u hu
    set a : ℕ := (u : ZMod r).val with ha
    have hcast : ((a : ℕ) : ZMod r) = (u : ZMod r) := val_cast_dav481 u
    have hmod : a ≡ 1 [MOD 8 * m] := (unitsMap_eq_one_iff_dav481 hd u).mp hu
    have hane : a ≠ 0 := by
      intro h0
      exact Units.ne_zero u (by rw [← hcast, h0, Nat.cast_zero])
    have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr hane
    have hmod8 : a ≡ 1 [MOD 8] := Nat.ModEq.of_dvd (dvd_mul_right 8 m) hmod
    have hmodm : a ≡ 1 [MOD m] := Nat.ModEq.of_dvd (dvd_mul_left m 8) hmod
    obtain ⟨b, hbo, hb⟩ := exists_sq_modEq_two_pow_dav481 hmod8 e he3
    obtain ⟨y, hyb, hym⟩ := Nat.chineseRemainder hmC'.symm b 1
    have hy2e : y ^ 2 ≡ a [MOD 2 ^ e] := (Nat.ModEq.pow 2 hyb).trans hb
    have hy2m : y ^ 2 ≡ a [MOD m] := by
      have h1 : y ^ 2 ≡ 1 [MOD m] := by
        simpa using Nat.ModEq.pow 2 hym
      exact h1.trans hmodm.symm
    have hy2 : y ^ 2 ≡ a [MOD 2 ^ e * m] := modEq_mul_of_coprime_dav481 hmC'.symm hy2e hy2m
    have hy2r : y ^ 2 ≡ a [MOD r] := by
      rw [← hr_eq]
      exact hy2
    have hyu : ((y : ℕ) : ZMod r) ^ 2 = (u : ZMod r) := by
      have h1 : (((y ^ 2 : ℕ)) : ZMod r) = ((a : ℕ) : ZMod r) :=
        (ZMod.natCast_eq_natCast_iff _ _ r).mpr hy2r
      rw [hcast] at h1
      rw [← h1]
      push_cast
      ring
    have hYu : IsUnit ((y : ℕ) : ZMod r) := by
      have h2 : IsUnit (((y : ℕ) : ZMod r) * ((y : ℕ) : ZMod r)) := by
        rw [← sq, hyu]
        exact u.isUnit
      exact isUnit_of_mul_isUnit_right h2
    obtain ⟨Y, hY⟩ := hYu
    have hyY : ((y : ℕ) : ZMod r) = ((Y : (ZMod r)ˣ) : ZMod r) := hY.symm
    have hchi : χ (u : ZMod r) = 1 := by
      rw [← hyu, hyY, chi_pow_apply_dav481, chi_sq_eq_one_dav481 hreal Y]
    exact hchi
  have hcond : χ.conductor ∣ 8 * m := conductor_dvd_of_ker_dav481 hd hker
  have hrd : r ∣ 8 * m := by rw [← hprim]; exact hcond
  have hlt8 : 8 * m < r := by
    rw [← hr_eq]
    have h8lt : 8 < 2 ^ e := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ < 2 ^ e := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact Nat.mul_lt_mul_of_pos_right h8lt hmpos
  have hle' : r ≤ 8 * m := Nat.le_of_dvd (Nat.mul_pos (by norm_num) hmpos) hrd
  omega

/-- The odd part of the conductor is squarefree. -/
private lemma squarefree_odd_part_dav481 (hprim : χ.IsPrimitive) (hreal : ∀ a, (χ a).im = 0) :
    Squarefree (r / 2 ^ r.factorization 2) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hdvd
  set m : ℕ := r / 2 ^ r.factorization 2 with hm
  have hrne : r ≠ 0 := NeZero.ne r
  have hKdvd : 2 ^ r.factorization 2 ∣ r :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hrne).mpr le_rfl
  have hr_eq : 2 ^ r.factorization 2 * m = r := by rw [hm]; exact Nat.mul_div_cancel' hKdvd
  have hmC : (2 : ℕ).Coprime m := by
    rw [hm]
    exact Nat.coprime_ordCompl Nat.prime_two hrne
  have hmOdd : Odd m := Nat.coprime_two_left.mp hmC
  have hqr : q ^ 2 ∣ r := by
    rw [← hr_eq]
    simpa [pow_two] using dvd_mul_of_dvd_right hdvd (2 ^ r.factorization 2)
  rcases hq.eq_two_or_odd with htwo | hodd
  · subst htwo
    obtain ⟨c, hc⟩ := hmOdd
    obtain ⟨k, hk⟩ := hdvd
    omega
  · exact not_sq_dvd_of_real_primitive_dav481 hprim hreal hq (by
      rintro rfl
      norm_num at hodd) (by simpa [pow_two] using hqr)

/-- The odd part of the conductor divides the odd radical. -/
private lemma odd_part_dvd_rad_dav481 (hprim : χ.IsPrimitive) (hreal : ∀ a, (χ a).im = 0) :
    (r / 2 ^ r.factorization 2) ∣ oddRad131 r := by
  set m : ℕ := r / 2 ^ r.factorization 2 with hm
  have hrne : r ≠ 0 := NeZero.ne r
  have hKdvd : 2 ^ r.factorization 2 ∣ r :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hrne).mpr le_rfl
  have hr_eq : 2 ^ r.factorization 2 * m = r := by rw [hm]; exact Nat.mul_div_cancel' hKdvd
  have hmC : (2 : ℕ).Coprime m := by
    rw [hm]
    exact Nat.coprime_ordCompl Nat.prime_two hrne
  have hmOdd : Odd m := Nat.coprime_two_left.mp hmC
  have hsqm : Squarefree m := squarefree_odd_part_dav481 hprim hreal
  have hmdvd : m ∣ r := ⟨2 ^ r.factorization 2, hr_eq.symm.trans (mul_comm _ _)⟩
  have hsub : m.primeFactors ⊆ r.primeFactors.filter (fun p => 2 < p) := by
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hqp, hqdvd, -⟩ := hq
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    refine ⟨⟨hqp, hqdvd.trans hmdvd, hrne⟩, ?_⟩
    rcases hqp.eq_two_or_odd with h | h
    · subst h
      obtain ⟨c, hc⟩ := hmOdd
      obtain ⟨k, hk⟩ := hqdvd
      omega
    · have h2 := hqp.two_le
      omega
  have hprod : ∏ p ∈ m.primeFactors, p ∣ ∏ p ∈ r.primeFactors.filter (fun p => 2 < p), p :=
    prod_subset_dvd_dav481 hsub
  rwa [Nat.prod_primeFactors_of_squarefree hsqm] at hprod

/-- LEAF: the conductor divides eight times its odd radical. -/
private theorem dvd_eight_odd_rad_dav481 (hprim : χ.IsPrimitive) (hreal : ∀ a, (χ a).im = 0) :
    r ∣ 8 * oddRad131 r := by
  have hrne : r ≠ 0 := NeZero.ne r
  have h2 : r.factorization 2 ≤ 3 := factorization_two_le_three_dav481 hprim hreal
  have hK8 : 2 ^ r.factorization 2 ∣ 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 h2
  have hm := odd_part_dvd_rad_dav481 hprim hreal
  have hr_eq : 2 ^ r.factorization 2 * (r / 2 ^ r.factorization 2) = r :=
    Nat.mul_div_cancel' ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hrne).mpr le_rfl)
  have hmain : 2 ^ r.factorization 2 * (r / 2 ^ r.factorization 2) ∣ 8 * oddRad131 r :=
    Nat.mul_dvd_mul hK8 hm
  rwa [hr_eq] at hmain

/-- LEAF: the conductor is not twice its odd radical. -/
private theorem ne_two_odd_rad_dav481 (hprim : χ.IsPrimitive) (hreal : ∀ a, (χ a).im = 0)
    (hr : 1 ≤ r) : r ≠ 2 * oddRad131 r := by
  intro heq
  have hrne : r ≠ 0 := NeZero.ne r
  have hmOdd : Odd (oddRad131 r) := by
    rw [oddRad131]
    refine odd_prod_primes_dav481 (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (fun p hp => ?_)
    have h := (Finset.mem_filter.mp hp).2
    omega
  have hmne : oddRad131 r ≠ 0 := by
    rw [oddRad131]
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero
  have hd : oddRad131 r ∣ r := ⟨2, heq.trans (mul_comm _ _)⟩
  have hr2 : r ≠ 1 := by
    rw [heq]
    have := hmne
    omega
  haveI : Nontrivial (ZMod r) := ZMod.nontrivial_iff.mpr hr2
  have hker : ∀ u : (ZMod r)ˣ, ZMod.unitsMap hd u = 1 → χ (u : ZMod r) = 1 := by
    intro u hu
    set a : ℕ := (u : ZMod r).val with ha
    have hcast : ((a : ℕ) : ZMod r) = (u : ZMod r) := val_cast_dav481 u
    have hmod : a ≡ 1 [MOD oddRad131 r] := (unitsMap_eq_one_iff_dav481 hd u).mp hu
    have haodd : Odd a := by
      have hc : a.Coprime r := (ZMod.unitsEquivCoprime u).2
      have h2r : 2 ∣ r := ⟨oddRad131 r, heq⟩
      have : a.Coprime 2 := hc.coprime_dvd_right h2r
      exact Nat.coprime_two_right.mp this
    have ha1 : 1 ≤ a := by
      obtain ⟨c, hc⟩ := haodd
      omega
    have haa : a ≡ 1 [MOD 2 * oddRad131 r] := modEq_two_mul_of_odd_dav481 hmOdd haodd hmod
    have har : a ≡ 1 [MOD r] := by
      rw [heq]
      exact haa
    have hu1 : (u : ZMod r) = 1 := by
      rw [← hcast]
      simpa using (ZMod.natCast_eq_natCast_iff a 1 r).mpr har
    rw [hu1, map_one]
  have hcond : χ.conductor ∣ oddRad131 r := conductor_dvd_of_ker_dav481 hd hker
  have hrd : r ∣ oddRad131 r := Eq.mp (congrArg (fun d => d ∣ oddRad131 r) hprim) hcond
  have h2m : 2 * oddRad131 r ∣ oddRad131 r := Eq.mp (congrArg (fun d => d ∣ oddRad131 r) heq) hrd
  have hpos : 0 < oddRad131 r := Nat.pos_of_ne_zero hmne
  have hle2 : 2 * oddRad131 r ≤ oddRad131 r := Nat.le_of_dvd hpos h2m
  omega

end

/-- LEAF. The power of two carried by the conductor of a real primitive character is at
most eight: the conductor divides eight times its odd radical. -/
theorem real_primitive_dvd_eight_odd_rad481 {r : ℕ} (hr : 1 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive) (hreal : ∀ a, (χ a).im = 0) :
    r ∣ 8 * oddRad131 r := by
  haveI : NeZero r := ⟨by omega⟩
  exact dvd_eight_odd_rad_dav481 hprim hreal

/-- LEAF. A real primitive character never has conductor exactly twice its odd radical:
the power of two outside the odd radical is not the first power. -/
theorem real_primitive_ne_two_odd_rad481 {r : ℕ} (hr : 1 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive) (hreal : ∀ a, (χ a).im = 0) :
    r ≠ 2 * oddRad131 r := by
  haveI : NeZero r := ⟨by omega⟩
  exact ne_two_odd_rad_dav481 hprim hreal hr

/-- The conductor of a real primitive character is its odd radical, or four or eight times
that radical, obtained by writing the conductor as the odd radical times a divisor of eight
and excluding the factor two. -/
theorem davenport_classification481_split : RealPrimitiveStatement481 := by
  intro r hr χ hprim hreal
  obtain ⟨c, hc⟩ := oddRad131_dvd481 r
  have hdv : oddRad131 r * c ∣ oddRad131 r * 8 := by
    rw [Nat.mul_comm (oddRad131 r) 8, ← hc]
    exact real_primitive_dvd_eight_odd_rad481 hr χ hprim hreal
  have hc8 : c ∣ 8 := Nat.dvd_of_mul_dvd_mul_left (oddRad131_pos481 r) hdv
  have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hc8 (by norm_num)
  have hcle : c ≤ 8 := Nat.le_of_dvd (by norm_num) hc8
  interval_cases c
  · left; omega
  · exact absurd (by omega : r = 2 * oddRad131 r)
      (real_primitive_ne_two_odd_rad481 hr χ hprim hreal)
  · norm_num at hc8
  · right; left; omega
  · norm_num at hc8
  · norm_num at hc8
  · norm_num at hc8
  · right; right; omega

end

end LeanLab.LPZ2007
