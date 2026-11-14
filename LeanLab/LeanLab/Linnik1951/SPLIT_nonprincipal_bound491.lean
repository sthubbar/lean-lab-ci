/-
The nonprincipal character block of the local major arc integral at an integer
residual, cut into three steps: the number of nonprincipal characters of the
modulus, the pairs of characters whose product is principal, and the pairs of
characters whose product is not principal.

The block is the double sum of the ordered character pair contribution over the
nonprincipal characters of the modulus. Summing over the second character index
first, for a fixed nonprincipal character, splits that inner sum into the pairs
whose product is the principal character and the pairs whose product is not: the
first group carries the full reduced residue phase and the second is where the
character square saves a factor of the modulus. Counting the nonprincipal
characters then multiplies the one-index bound by at most the totient, which is
what removes the modulus from the final bound.
-/
import LeanLab.Linnik1951.Decomp491b

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-! ### Sums over `ZMod q` and over `range q` -/

private lemma sum_range_eq_sum_zmod (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    ∑ a ∈ Finset.range q, f (a : ZMod q) = ∑ a : ZMod q, f a := by
  have h := Finset.sum_bij (M := ℂ) (s := Finset.range q) (t := (Finset.univ : Finset (ZMod q)))
    (f := fun a : ℕ => f (a : ZMod q)) (g := f) (fun a _ => (a : ZMod q))
    (fun a _ => Finset.mem_univ _)
    (fun a ha b hb hab => by
      have hv := congrArg ZMod.val hab
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using hv)
    (fun b _ => ⟨b.val, Finset.mem_range.mpr (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩)
    (fun a _ => rfl)
  simpa using h

private lemma stdAddChar_nat_eq (q : ℕ) [NeZero q] (a : ℕ) :
    ZMod.stdAddChar (a : ZMod q) =
      Complex.exp (((2 * Real.pi * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) := by
  rw [← Int.cast_natCast (R := ZMod q) a, ZMod.stdAddChar_coe (a : ℤ)]
  congr 1
  push_cast
  ring

/-- The conjugate reduced residue Gauss sum is the conjugate of the Gauss sum of
the Dirichlet character against the standard additive character. -/
private lemma conjugateGauss491_eq_star_gaussSum (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    conjugateGauss491 q χ = star (gaussSum χ (ZMod.stdAddChar (N := q))) := by
  classical
  set ee : ℕ → ℂ := fun a =>
    Complex.exp (((2 * Real.pi * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) with hee
  have hterm : ∀ a ∈ Finset.range q,
      χ a * ee a = χ (a : ZMod q) * ZMod.stdAddChar (a : ZMod q) := by
    intro a ha
    by_cases hc : Nat.Coprime a q
    · have heq : ZMod.stdAddChar (a : ZMod q) = ee a := (stdAddChar_nat_eq q a).trans rfl
      rw [heq]
    · have hunit : ¬ IsUnit ((a : ℕ) : ZMod q) := by rwa [ZMod.isUnit_iff_coprime]
      rw [MulChar.map_nonunit _ hunit, zero_mul, zero_mul]
  have hsub : ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), χ a * ee a
      = ∑ a ∈ Finset.range q, χ a * ee a := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro a ha hnot
    have hnc : ¬ Nat.Coprime a q := by
      intro hc; exact hnot (Finset.mem_filter.mpr ⟨ha, hc⟩)
    have hunit : ¬ IsUnit ((a : ℕ) : ZMod q) := by rwa [ZMod.isUnit_iff_coprime]
    rw [MulChar.map_nonunit _ hunit, zero_mul]
  unfold conjugateGauss491 gaussSum
  congr 1
  rw [hsub, Finset.sum_congr rfl hterm,
    sum_range_eq_sum_zmod q (fun x => χ x * ZMod.stdAddChar x)]

/-! ### The Gauss sum norm bound `‖τ(χ)‖ ≤ √q` -/

private lemma gaussSum_norm_le491 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ ≤ Real.sqrt q := by
  classical
  let e : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  let G : ZMod q → ℂ := fun a => gaussSum χ (e.mulShift a)
  have hortho (t : ZMod q) : ∑ a : ZMod q, e (t * a) = if t = 0 then (q : ℂ) else 0 := by
    by_cases ht : t = 0
    · subst ht
      simp [e]
    · rw [ite_eq_right ht]
      change ∑ a : ZMod q, (e.mulShift t) a = 0
      refine AddChar.sum_eq_zero_of_ne_one (R' := ℂ) ?_
      intro h1
      have h2 : ZMod.stdAddChar t = 1 := by
        have hv := DFunLike.congr_fun h1 (1 : ZMod q)
        simpa [e, AddChar.mulShift_apply] using hv
      exact ht (ZMod.injective_stdAddChar (by simpa using h2))
  have hnorm_e (x : ZMod q) : ‖e x‖ = 1 := by
    show ‖ZMod.stdAddChar x‖ = 1
    rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  have hstar (x : ZMod q) : star (e x) = e (-x) := by
    have h2 : e x * e (-x) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    have h1 : e x * star (e x) = 1 := by
      have h := Complex.mul_conj' (e x)
      rw [hnorm_e] at h
      simpa using h
    refine mul_left_cancel₀ (b := star (e x)) (c := e (-x)) ?_ (h1.trans h2.symm)
    intro h
    have hz := hnorm_e x
    rw [h, norm_zero] at hz
    norm_num at hz
  have henergy : (∑ a : ZMod q, G a * star (G a)) =
      q * ∑ x : ZMod q, χ x * star (χ x) := by
    simp only [G, gaussSum, star_sum, star_mul, AddChar.mulShift_apply]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    have hterm (a y : ZMod q) :
        χ x * e (a * x) * (star (e (a * y)) * star (χ y)) =
          (χ x * star (χ y)) * e ((x - y) * a) := by
      rw [hstar]
      calc
        _ = (χ x * star (χ y)) * (e (a * x) * e (-(a * y))) := by ring
        _ = _ := by rw [← AddChar.map_add_eq_mul]; congr 2 <;> ring
    simp_rw [hterm]
    simp_rw [← Finset.mul_sum, hortho]
    simp [sub_eq_zero, mul_ite]
    ring
  have hchars : (∑ x : ZMod q, χ x * star (χ x)) = (q.totient : ℂ) := by
    have ht (x : ZMod q) : χ x * star (χ x) = (1 : DirichletCharacter ℂ q) x := by
      by_cases hx : IsUnit x
      · change χ x * (starRingEnd ℂ) (χ x) = _
        rw [Complex.mul_conj', ← hx.unit_spec, χ.unit_norm_eq_one]
        simp [MulChar.one_apply hx]
      · simp [MulChar.map_nonunit _ hx]
    simp_rw [ht]
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  rw [hchars] at henergy
  change (∑ a : ZMod q, G a * (starRingEnd ℂ) (G a)) = _ at henergy
  simp_rw [Complex.mul_conj'] at henergy
  have hreal : (∑ a : ZMod q, ‖G a‖ ^ 2) = (q : ℝ) * q.totient := by
    exact_mod_cast henergy
  have hunit (u : (ZMod q)ˣ) : ‖G u‖ = ‖gaussSum χ e‖ := by
    dsimp [G]
    rw [gaussSum_mulShift_eq, norm_mul, DirichletCharacter.unit_norm_eq_one, one_mul]
  have htriv : (∑ a : ZMod q, ((1 : DirichletCharacter ℂ q) a).re) = (q.totient : ℝ) := by
    have h := MulChar.sum_one_eq_card_units (R := ZMod q) (R' := ℂ)
    rw [ZMod.card_units_eq_totient] at h
    have hh := congrArg (fun z : ℂ => Complex.reCLM z) h
    rw [map_sum] at hh
    simpa using hh
  have hlow : (q.totient : ℝ) * ‖gaussSum χ e‖ ^ 2 ≤ ∑ a : ZMod q, ‖G a‖ ^ 2 := by
    calc
      _ = ∑ a : ZMod q, ((1 : DirichletCharacter ℂ q) a).re * ‖gaussSum χ e‖ ^ 2 := by
        rw [← Finset.sum_mul, htriv]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : IsUnit a
        · rw [← ha.unit_spec, MulChar.one_apply (Units.isUnit ha.unit), Complex.one_re, one_mul,
            hunit]
        · rw [MulChar.map_nonunit _ ha, Complex.zero_re, zero_mul]
          positivity
  have hpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
  change ‖gaussSum χ e‖ ^ 2 ≤ (q : ℝ)
  rw [hreal] at hlow
  nlinarith

private lemma conjugateGauss491_norm_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖conjugateGauss491 q χ‖ ≤ Real.sqrt q := by
  rw [conjugateGauss491_eq_star_gaussSum, norm_star]
  exact gaussSum_norm_le491 q χ

/-! ### The Ramanujan sum bound -/

private lemma signedRamanujan491_norm_le (q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    ‖signedRamanujan491 q n‖ ≤ (q.totient : ℝ) := by
  classical
  have hterm : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    intro a ha
    exact Complex.norm_exp_ofReal_mul_I _
  have hcard : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    exact Finset.filter_congr (fun a _ => Nat.coprime_comm)
  unfold signedRamanujan491
  calc ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)‖
      ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)‖ :=
        norm_sum_le _ _
    _ = ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (1 : ℝ) :=
        Finset.sum_congr rfl hterm
    _ = (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (q.totient : ℝ) := by rw [hcard]

/-! ### Summability and pointwise bounds for the character prime series -/

private lemma primes_exp_summable (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun p : Nat.Primes => Real.exp (-(((p : ℕ) : ℝ)) / N)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hr0 : 0 ≤ Real.exp (-(1 / (N : ℝ))) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(1 / (N : ℝ))) < 1 := by
    rw [Real.exp_neg, inv_lt_one_iff₀]
    right
    exact Real.one_lt_exp_iff.mpr (by positivity)
  have hcomp : Summable (fun p : Nat.Primes => Real.exp (-(1 / (N : ℝ))) ^ (p : ℕ)) :=
    (summable_geometric_of_lt_one hr0 hr1).subtype _
  refine hcomp.congr (fun p => ?_)
  have hp : -(((p : ℕ) : ℝ)) / (N : ℝ) = ((p : ℕ) : ℝ) * (-(1 / (N : ℝ))) := by ring
  rw [hp, Real.exp_nat_mul]

private lemma characterPrime280_continuous (q : ℕ) (χ : DirichletCharacter ℂ q) (N : ℕ)
    (hN : 1 ≤ N) :
    Continuous (fun α : ℝ => characterPrime280 χ N α) := by
  unfold characterPrime280
  refine continuous_tsum (u := fun p : Nat.Primes => Real.exp (-(((p : ℕ) : ℝ)) / N))
    (f := fun (p : Nat.Primes) (α : ℝ) =>
    χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ)) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) ?_ ?_ ?_
  · intro p
    fun_prop
  · exact primes_exp_summable N hN
  · intro p x
    have h1 : ‖χ ((p : ℕ) : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ ((p : ℕ) : ZMod q)
    have h2 : 0 < Real.exp (-(((p : ℕ) : ℝ)) / N) := Real.exp_pos _
    have h3 : ‖((Real.exp (-(((p : ℕ) : ℝ)) / N) : ℝ) : ℂ)‖ =
        Real.exp (-(((p : ℕ) : ℝ)) / N) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2.le]
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, h3]
    nlinarith

private lemma characterPrime280_bound (q : ℕ) (χ : DirichletCharacter ℂ q) (N : ℕ)
    (hN : 1 ≤ N) (α : ℝ) :
    ‖characterPrime280 χ N α‖ ≤
      ∑' p : Nat.Primes, Real.exp (-(((p : ℕ) : ℝ)) / N) := by
  have hsum := primes_exp_summable N hN
  have hu : ∀ p : Nat.Primes,
      ‖χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ)) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)‖ ≤
        Real.exp (-(((p : ℕ) : ℝ)) / N) := by
    intro p
    have h1 : ‖χ ((p : ℕ) : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ ((p : ℕ) : ZMod q)
    have h2 : 0 < Real.exp (-(((p : ℕ) : ℝ)) / N) := Real.exp_pos _
    have h3 : ‖((Real.exp (-(((p : ℕ) : ℝ)) / N) : ℝ) : ℂ)‖ =
        Real.exp (-(((p : ℕ) : ℝ)) / N) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2.le]
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, h3]
    nlinarith
  have hs : Summable (fun p : Nat.Primes =>
      ‖χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ)) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)‖) :=
    hsum.of_nonneg_of_le (fun p => norm_nonneg _) hu
  unfold characterPrime280
  calc ‖∑' p : Nat.Primes, χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ)) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)‖
      ≤ _ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' p : Nat.Primes, Real.exp (-(((p : ℕ) : ℝ)) / N) :=
        hs.tsum_le_tsum hu hsum

/-! ### Window energy from the Mellin input -/

/-- The local character pair integral over the window is bounded by the Mellin
input applied to the two characters, through the elementary quadratic bound and
the uniform boundedness of the character prime series. -/
private lemma window_energy_le (hM : MellinBound280) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ∀ χ ψ : DirichletCharacter ℂ q, χ ≠ 1 → ψ ≠ 1 →
          ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            characterPrime280 χ N z * characterPrime280 ψ N z *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
          B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 := by
  classical
  obtain ⟨B, hB, N0, hN0⟩ := hM
  refine ⟨B, hB, max N0 1, ?_⟩
  intro N hN q hq hqQ
  letI : NeZero q := ⟨by omega⟩
  intro n χ ψ hχ hψ
  have hN1 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNge1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hτpos : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hQ7 : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
    refine le_trans hqQ (Real.rpow_le_rpow_of_exponent_le ?_ ?_)
    · exact_mod_cast hNge1
    · norm_num
  have hMχ₀ := hN0 N hN1 q hq hQ7 χ hχ
  have hMψ₀ := hN0 N hN1 q hq hQ7 ψ hψ
  have hS0 : 0 ≤ ∑' p : Nat.Primes, Real.exp (-(((p : ℕ) : ℝ)) / N) :=
    tsum_nonneg (fun p => (Real.exp_pos _).le)
  have hbχ : ∀ z : ℝ, ‖characterPrime280 χ N z‖ ≤
      ∑' p : Nat.Primes, Real.exp (-(((p : ℕ) : ℝ)) / N) :=
    fun z => characterPrime280_bound q χ N hNge1 z
  have hbψ : ∀ z : ℝ, ‖characterPrime280 ψ N z‖ ≤
      ∑' p : Nat.Primes, Real.exp (-(((p : ℕ) : ℝ)) / N) :=
    fun z => characterPrime280_bound q ψ N hNge1 z
  have hmeasχ : Measurable (fun z : ℝ => characterPrime280 χ N z) :=
    (characterPrime280_continuous q χ N hNge1).measurable
  have hmeasψ : Measurable (fun z : ℝ => characterPrime280 ψ N z) :=
    (characterPrime280_continuous q ψ N hNge1).measurable
  set a : ℝ := -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) with ha
  set b : ℝ := 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) with hb
  have hδpos : 0 < b := by rw [hb]; positivity
  have hab : a ≤ b := by rw [ha, hb]; linarith
  set S : ℝ := ∑' p : Nat.Primes, Real.exp (-(((p : ℕ) : ℝ)) / N) with hS
  have hMχ : ∫ z in a..b, ‖characterPrime280 χ N z‖ ^ 2 ≤
      B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 := hMχ₀
  have hMψ : ∫ z in a..b, ‖characterPrime280 ψ N z‖ ^ 2 ≤
      B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 := hMψ₀
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    infer_instance
  have hIχ : IntervalIntegrable (fun z : ℝ => ‖characterPrime280 χ N z‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff]
    refine Integrable.of_bound ?_ (S ^ 2) ?_
    · exact (hmeasχ.norm.pow_const 2).aestronglyMeasurable
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := hbχ z
      have h2 : 0 ≤ ‖characterPrime280 χ N z‖ := norm_nonneg _
      have h3 : 0 ≤ S := hS0
      nlinarith
  have hIψ : IntervalIntegrable (fun z : ℝ => ‖characterPrime280 ψ N z‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff]
    refine Integrable.of_bound ?_ (S ^ 2) ?_
    · exact (hmeasψ.norm.pow_const 2).aestronglyMeasurable
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := hbψ z
      have h2 : 0 ≤ ‖characterPrime280 ψ N z‖ := norm_nonneg _
      have h3 : 0 ≤ S := hS0
      nlinarith
  have hInorm : IntervalIntegrable (fun z : ℝ =>
      ‖characterPrime280 χ N z * characterPrime280 ψ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖) volume a b := by
    rw [intervalIntegrable_iff]
    refine Integrable.of_bound ?_ (S * S) ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact ((hmeasχ.mul hmeasψ).mul (by fun_prop : Measurable
        (fun z : ℝ => Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)))).norm
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      have h1 := hbχ z
      have h2 := hbψ z
      have h3 : 0 ≤ ‖characterPrime280 χ N z‖ := norm_nonneg _
      have h4 : 0 ≤ ‖characterPrime280 ψ N z‖ := norm_nonneg _
      have h5 : 0 ≤ S := hS0
      nlinarith
  have hIam : IntervalIntegrable (fun z : ℝ =>
      (‖characterPrime280 χ N z‖ ^ 2 + ‖characterPrime280 ψ N z‖ ^ 2) / 2) volume a b :=
    (hIχ.add hIψ).div_const 2
  have hstep1 : ‖∫ z in a..b, characterPrime280 χ N z * characterPrime280 ψ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
      ∫ z in a..b, ‖characterPrime280 χ N z * characterPrime280 ψ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    exact norm_integral_le_integral_norm _
  have hstep2 : ∫ z in a..b, ‖characterPrime280 χ N z * characterPrime280 ψ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
      ∫ z in a..b, (‖characterPrime280 χ N z‖ ^ 2 + ‖characterPrime280 ψ N z‖ ^ 2) / 2 := by
    refine intervalIntegral.integral_mono hab hInorm hIam (fun z => ?_)
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    nlinarith [sq_nonneg (‖characterPrime280 χ N z‖ - ‖characterPrime280 ψ N z‖)]
  have hlin : ∫ z in a..b, (‖characterPrime280 χ N z‖ ^ 2 + ‖characterPrime280 ψ N z‖ ^ 2) / 2 =
      ((∫ z in a..b, ‖characterPrime280 χ N z‖ ^ 2) +
        (∫ z in a..b, ‖characterPrime280 ψ N z‖ ^ 2)) / 2 := by
    rw [show (fun z : ℝ => (‖characterPrime280 χ N z‖ ^ 2 + ‖characterPrime280 ψ N z‖ ^ 2) / 2)
        = fun z => (1 / 2 : ℝ) * (‖characterPrime280 χ N z‖ ^ 2 + ‖characterPrime280 ψ N z‖ ^ 2)
        from by funext z; ring]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hIχ hIψ]
    ring
  have hgoal : ∫ z in a..b, (‖characterPrime280 χ N z‖ ^ 2 + ‖characterPrime280 ψ N z‖ ^ 2) / 2 ≤
      B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 := by
    rw [hlin]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc (∫ z in a..b, ‖characterPrime280 χ N z‖ ^ 2) +
          (∫ z in a..b, ‖characterPrime280 ψ N z‖ ^ 2)
        ≤ B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 +
          B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 :=
          add_le_add hMχ hMψ
      _ = B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 * 2 := by ring
  calc ‖∫ z in a..b, characterPrime280 χ N z * characterPrime280 ψ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖
      ≤ ∫ z in a..b, ‖characterPrime280 χ N z * characterPrime280 ψ N z *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ := hstep1
    _ ≤ ∫ z in a..b, (‖characterPrime280 χ N z‖ ^ 2 + ‖characterPrime280 ψ N z‖ ^ 2) / 2 := hstep2
    _ ≤ B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 := hgoal


/-! ### The principal product pair, `ψ = χ⁻¹` -/

private lemma characterPair491_principal_le (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖characterPair491 N q n χ χ⁻¹‖ ≤
            C * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 /
              (q.totient : ℝ) := by
  classical
  obtain ⟨B, hB, NB, hNB⟩ := window_energy_le hM
  refine ⟨B, hB, max NB 1, ?_⟩
  intro N hN q hq hqQ
  letI : NeZero q := ⟨by omega⟩
  intro n χ hχ
  have hN1 : NB < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNge1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hτpos : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h1
    apply hχ
    have hc := congrArg (fun x : DirichletCharacter ℂ q => x⁻¹) h1
    simpa using hc
  have hsum : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        χ a * χ⁻¹ a * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) *
          Complex.I)) = signedRamanujan491 q n := by
    unfold signedRamanujan491
    apply Finset.sum_congr rfl
    intro a ha
    have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
    have hunit : IsUnit ((a : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr hcop
    have h1 : χ ((a : ℕ) : ZMod q) * χ⁻¹ ((a : ℕ) : ZMod q) = 1 := by
      rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply hunit]
    rw [h1, one_mul]
  have hG1 : ‖conjugateGauss491 q χ‖ ≤ Real.sqrt (q : ℝ) := conjugateGauss491_norm_le q χ
  have hG2 : ‖conjugateGauss491 q χ⁻¹‖ ≤ Real.sqrt (q : ℝ) := conjugateGauss491_norm_le q χ⁻¹
  have hS : ‖signedRamanujan491 q n‖ ≤ (q.totient : ℝ) := signedRamanujan491_norm_le q hq n
  have hI := hNB N hN1 q hq hqQ n χ χ⁻¹ hχ hχinv
  have hfac : characterPair491 N q n χ χ⁻¹ =
      (1 / (q.totient : ℂ) ^ 2) * conjugateGauss491 q χ * conjugateGauss491 q χ⁻¹ *
        signedRamanujan491 q n *
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          characterPrime280 χ N z * characterPrime280 χ⁻¹ N z *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) := by
    unfold characterPair491
    rw [hsum]
  have hn1 : ‖(1 / (q.totient : ℂ) ^ 2)‖ = 1 / (q.totient : ℝ) ^ 2 := by
    rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
  have hqleq : ‖conjugateGauss491 q χ‖ * ‖conjugateGauss491 q χ⁻¹‖ ≤ (q : ℝ) := by
    have h := mul_le_mul hG1 hG2 (norm_nonneg _) (Real.sqrt_nonneg (q : ℝ))
    rwa [Real.mul_self_sqrt (le_of_lt hqpos)] at h
  have hb1 : (1 / (q.totient : ℝ) ^ 2) *
        (‖conjugateGauss491 q χ‖ * ‖conjugateGauss491 q χ⁻¹‖) ≤
      (1 / (q.totient : ℝ) ^ 2) * (q : ℝ) :=
    mul_le_mul_of_nonneg_left hqleq (by positivity)
  have hb2 : ((1 / (q.totient : ℝ) ^ 2) *
        (‖conjugateGauss491 q χ‖ * ‖conjugateGauss491 q χ⁻¹‖)) *
        ‖signedRamanujan491 q n‖ ≤
      ((1 / (q.totient : ℝ) ^ 2) * (q : ℝ)) * (q.totient : ℝ) :=
    mul_le_mul hb1 hS (norm_nonneg _) (by positivity)
  have hb3 : (((1 / (q.totient : ℝ) ^ 2) *
        (‖conjugateGauss491 q χ‖ * ‖conjugateGauss491 q χ⁻¹‖)) *
        ‖signedRamanujan491 q n‖) *
        ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          characterPrime280 χ N z * characterPrime280 χ⁻¹ N z *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
      (((1 / (q.totient : ℝ) ^ 2) * (q : ℝ)) * (q.totient : ℝ)) *
        (B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13) :=
    mul_le_mul hb2 hI (norm_nonneg _) (by positivity)
  have hgoal : (((1 / (q.totient : ℝ) ^ 2) * (q : ℝ)) * (q.totient : ℝ)) *
        (B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13) =
      B * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 / (q.totient : ℝ) := by
    field_simp
  rw [hfac]
  simp only [norm_mul, hn1]
  calc (1 / (q.totient : ℝ) ^ 2) * ‖conjugateGauss491 q χ‖ * ‖conjugateGauss491 q χ⁻¹‖ *
        ‖signedRamanujan491 q n‖ *
        ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          characterPrime280 χ N z * characterPrime280 χ⁻¹ N z *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖
      = ((1 / (q.totient : ℝ) ^ 2) * (‖conjugateGauss491 q χ‖ * ‖conjugateGauss491 q χ⁻¹‖)) *
          ‖signedRamanujan491 q n‖ *
          ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            characterPrime280 χ N z * characterPrime280 χ⁻¹ N z *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ := by ring
    _ ≤ (((1 / (q.totient : ℝ) ^ 2) * (q : ℝ)) * (q.totient : ℝ)) *
        (B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13) := hb3
    _ = B * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 / (q.totient : ℝ) := hgoal


/-- LEAF. Step one of the nonprincipal block, the counting step. The nonprincipal
characters of a positive modulus number at most the totient of the modulus, so
the outer sum of the block has at most that many terms. -/
theorem nonprincipal_character_count491 (q : ℕ) (hq : 1 ≤ q) :
    letI : NeZero q := ⟨by omega⟩
    (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card ≤ q.totient := by
  classical
  letI : NeZero q := ⟨by omega⟩
  have hcard : Nat.card (DirichletCharacter ℂ q) = q.totient :=
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Nat.card_eq_fintype_card] at hcard
  have hle := Finset.card_filter_le (univ : Finset (DirichletCharacter ℂ q))
    (fun χ => χ ≠ 1)
  simpa [hcard] using hle

/-- LEAF. Step two of the nonprincipal block, the pairs with a principal product,
for one fixed nonprincipal character. The reduced residue phase of such a pair is
an untwisted Ramanujan phase, bounded by the residue count, so this block of
pairs is bounded with one factor of the totient in the denominator and without
any character square saving. -/
theorem nonprincipal_principal_product491 (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ = 1),
            characterPair491 N q n χ ψ‖ ≤
            C * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 /
              (q.totient : ℝ) := by
  classical
  obtain ⟨C, hC, N0, hle⟩ := characterPair491_principal_le hM
  refine ⟨C, hC, N0, ?_⟩
  intro N hN q hq hqQ
  letI : NeZero q := ⟨by omega⟩
  intro n χ hχ
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h1
    apply hχ
    have hc := congrArg (fun x : DirichletCharacter ℂ q => x⁻¹) h1
    simpa using hc
  have hsingle : ∀ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
      (fun ψ => ψ * χ = 1), ψ = χ⁻¹ := by
    intro ψ hψ
    exact eq_inv_of_mul_eq_one_left (Finset.mem_filter.mp hψ).2
  have hsum : (∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
        (fun ψ => ψ * χ = 1), characterPair491 N q n χ ψ) =
      characterPair491 N q n χ χ⁻¹ := by
    refine Finset.sum_eq_single (χ⁻¹) ?_ ?_
    · intro ψ hψ hne
      exact absurd (hsingle ψ hψ) hne
    · intro hnot
      exfalso
      apply hnot
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hχinv⟩, by rw [inv_mul_cancel]⟩
  rw [hsum]
  exact hle N hN q hq hqQ n χ hχ

/-- LEAF. Step three of the nonprincipal block, the pairs with a nonprincipal
product, for one fixed nonprincipal character. Here the twisted reduced residue
phase is a character sum of nonprincipal product, and the character square
estimate saves the factor of the modulus needed for modulus uniformity, so this
block also carries one factor of the totient in the denominator. -/
theorem nonprincipal_off_product491 (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ ≠ 1),
            characterPair491 N q n χ ψ‖ ≤
            C * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 /
              (q.totient : ℝ) := by
  sorry

/-- The nonprincipal block, assembled from the two one-index estimates and the
character count. Each fixed nonprincipal character contributes its principal
product block and its nonprincipal product block, both bounded by the same
quantity, and there are at most a totient of such characters, so the totient
cancels and the modulus disappears from the bound. -/
theorem nonprincipal_bound491_split (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ‖nonprincipalTerm491 N q n‖ ≤
          C * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 := by
  obtain ⟨C1, hC1, N1, h1⟩ := nonprincipal_principal_product491 hM
  obtain ⟨C2, hC2, N2, h2⟩ := nonprincipal_off_product491 hM
  refine ⟨C1 + C2, add_pos hC1 hC2, max N1 (max N2 1), ?_⟩
  intro N hN q hq hqQ n
  letI : NeZero q := ⟨by omega⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNs : max N2 1 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_left _ _) hNs
  have hNgt : 1 < N := lt_of_le_of_lt (le_max_right N2 1) hNs
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hτ : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (show 0 < q by omega))
  have hCpos : (0 : ℝ) < C1 + C2 := add_pos hC1 hC2
  have hX : 0 ≤ (C1 + C2) *
      ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) / (q.totient : ℝ) := by
    apply div_nonneg
    · apply mul_nonneg hCpos.le
      exact mul_nonneg (div_nonneg hNpos.le hτ.le) (pow_nonneg hlog 13)
    · exact hφpos.le
  have hmain : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
          characterPair491 N q n χ ψ‖ ≤
        (C1 + C2) *
          ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) / (q.totient : ℝ) := by
    intro χ hχne
    have hA := h1 N hN1 q hq hqQ n χ hχne
    have hB := h2 N hN2 q hq hqQ n χ hχne
    have hsplit : (∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
            (fun ψ => ψ * χ = 1), characterPair491 N q n χ ψ) +
          (∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
            (fun ψ => ψ * χ ≠ 1), characterPair491 N q n χ ψ) =
        ∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
          characterPair491 N q n χ ψ :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    calc ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
          characterPair491 N q n χ ψ‖
        = ‖(∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ = 1), characterPair491 N q n χ ψ) +
            (∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ ≠ 1), characterPair491 N q n χ ψ)‖ := by
          rw [hsplit]
      _ ≤ ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ = 1), characterPair491 N q n χ ψ‖ +
            ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ ≠ 1), characterPair491 N q n χ ψ‖ := norm_add_le _ _
      _ ≤ C1 * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 /
              (q.totient : ℝ) +
            C2 * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 /
              (q.totient : ℝ) := add_le_add hA hB
      _ = (C1 + C2) *
          ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) / (q.totient : ℝ) := by
          ring
  change ‖∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
      ∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
        characterPair491 N q n χ ψ‖ ≤
    (C1 + C2) * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13
  calc ‖∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
        ∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
          characterPair491 N q n χ ψ‖
      ≤ ∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
          ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
            characterPair491 N q n χ ψ‖ := norm_sum_le _ _
    _ ≤ ∑ _χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
          (C1 + C2) *
            ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) /
              (q.totient : ℝ) := by
        apply Finset.sum_le_sum
        intro χ hχ
        exact hmain χ (by simpa using hχ)
    _ = ((univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) *
          ((C1 + C2) *
            ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) /
              (q.totient : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q.totient : ℝ) *
          ((C1 + C2) *
            ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) /
              (q.totient : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hX
        exact_mod_cast (nonprincipal_character_count491 q hq)
    _ = (C1 + C2) * ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ hφpos.ne'
    _ = (C1 + C2) * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 := by
        ring

end LeanLab.Linnik1951
