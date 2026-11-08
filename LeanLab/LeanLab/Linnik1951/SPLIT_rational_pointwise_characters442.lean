/-
Split of `rational_pointwise_characters442` into three leaves.

The pointwise bound has three layers, none of which uses an integral. First the
prime series at a shifted unit fraction splits over the residue cosets of the
modulus: the phase `exp (-2 pi i a b / q)` is constant on the coset of `b` and
the damped oscillation in the shift stays inside the coset sum. Second, on the
unit cosets alone the transformation matrix is the character table up to Gauss
numbers, so the sum of squares over reduced residues is the sum of the squared
character prime sums weighted by the squared Gauss numbers: the principal Gauss
number has modulus at most one and every other one has modulus `q` up to the
root of unity scale, which gives the totient divided bound. Third, the residue
cosets that are not coprime to the modulus can only contain the prime divisors
of the modulus themselves, so that part of the series is supported on at most
`log q / log 2` cosets with each coset sum of modulus at most one, which is
exactly the additive `totient q log q squared` term that the statement allows.

Leaves 1 to 3 record these three layers; the assembly below combines them with
the elementary square of a sum bound and a constant `8`. Nothing here changes
the statement of `rational_pointwise_characters442`: the theorem
`rational_pointwise_characters442_split` restates it character for character and
proves it from the three leaves without using the original theorem.
-/
import LeanLab.Linnik1951.Decomp442c

namespace LeanLab.Linnik1951

open MeasureTheory Finset



/-- The finite geometric sum of the `m`-th roots of unity vanishes for `m ≥ 2`. -/
private lemma geom_exp_sum442 (m : ℕ) (hm : 0 < m) :
    (∑ c ∈ range m, Complex.exp ((2 * Real.pi * ((c : ℝ) / (m : ℝ))) * Complex.I))
      = if m = 1 then 1 else 0 := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm.ne') with h1 | h2
  · subst h1; simp
  · rw [if_neg h2.ne']
    have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I * ((1 : ℝ) / (m : ℝ)))) m := by
      convert Complex.isPrimitiveRoot_exp_of_coprime 1 m hm.ne' (by simp) using 2
      push_cast
      ring
    set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((1 : ℝ) / (m : ℝ))) with hzspec
    have hterm : ∀ c : ℕ, Complex.exp ((2 * Real.pi * ((c : ℝ) / (m : ℝ))) * Complex.I) = z ^ c := by
      intro c
      rw [hzspec, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp
      try ring
      try ring
    calc (∑ c ∈ range m, Complex.exp ((2 * Real.pi * ((c : ℝ) / (m : ℝ))) * Complex.I))
        = ∑ c ∈ range m, z ^ c := Finset.sum_congr rfl (fun c _ => hterm c)
      _ = 0 := hprim.geom_sum_eq_zero h2

/-- The standard additive character on `ZMod q`, evaluated at a natural number. -/
private lemma stdAddChar_nat442 (q : ℕ) [NeZero q] (b : ℕ) :
    (ZMod.stdAddChar (b : ZMod q) : ℂ)
      = Complex.exp ((2 * Real.pi * ((b : ℝ) / (q : ℝ))) * Complex.I) := by
  rw [show ((b : ZMod q)) = ((b : ℤ) : ZMod q) by push_cast; ring]
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- The standard additive character at a negated product of natural numbers. -/
private lemma stdAddChar_nat_neg_mul442 (q : ℕ) [NeZero q] (a b : ℕ) :
    (ZMod.stdAddChar (-((a : ZMod q) * (b : ZMod q))) : ℂ)
      = Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) := by
  rw [show (-((a : ZMod q) * (b : ZMod q))) = ((-(a * b) : ℤ) : ZMod q) by push_cast; ring]
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring


/-- Reindexing: a sum over the unit group of `ZMod q` is a sum over the reduced
residue system in `range q`. -/
private lemma sum_units_eq_filter442 (q : ℕ) [NeZero q] (f : ℕ → ℂ) :
    (∑ u : (ZMod q)ˣ, f ((u : ZMod q).val))
      = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), f b := by
  classical
  refine Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val) ?_ ?_ ?_ ?_
  · intro u _
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _),
      ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ huv
    refine Units.ext ?_
    show (u : ZMod q) = (v : ZMod q)
    rw [← ZMod.natCast_zmod_val (u : ZMod q), ← ZMod.natCast_zmod_val (v : ZMod q), huv]
  · intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    refine ⟨ZMod.unitOfCoprime b hb2, Finset.mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hb1)]
  · intro u _
    rfl

/-- Reindexing: a sum over the unit group of `ZMod q` is a sum over the reduced
residue system in `range q`, real valued form. -/
private lemma sum_units_eq_filter_real442 (q : ℕ) [NeZero q] (f : ℕ → ℝ) :
    (∑ u : (ZMod q)ˣ, f ((u : ZMod q).val))
      = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), f b := by
  classical
  refine Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val) ?_ ?_ ?_ ?_
  · intro u _
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _),
      ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ huv
    refine Units.ext ?_
    show (u : ZMod q) = (v : ZMod q)
    rw [← ZMod.natCast_zmod_val (u : ZMod q), ← ZMod.natCast_zmod_val (v : ZMod q), huv]
  · intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    refine ⟨ZMod.unitOfCoprime b hb2, Finset.mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hb1)]
  · intro u _
    rfl

/-- A sum over `ZMod q` of a function vanishing off the units is a sum over the
unit group. -/
private lemma sum_zmod_eq_units442 (q : ℕ) [NeZero q] {M : Type*} [AddCommMonoid M]
    (G : ZMod q → M) (hG : ∀ x, ¬ IsUnit x → G x = 0) :
    (∑ x : ZMod q, G x) = ∑ u : (ZMod q)ˣ, G (u : ZMod q) := by
  classical
  have h1 : (∑ x : ZMod q, G x) = ∑ x ∈ (Finset.univ.filter (fun x => IsUnit x)), G x := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : IsUnit x
    · simp [h]
    · simp [h, hG x h]
  rw [h1]
  refine Finset.sum_bij (s := Finset.univ.filter (fun x => IsUnit x)) (t := Finset.univ)
    (f := G) (g := fun u : (ZMod q)ˣ => G (u : ZMod q))
    (fun x hx => (Finset.mem_filter.mp hx).2.unit) ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_univ _
  · intro x hx y hy hxy
    have hx' : x = ((Finset.mem_filter.mp hx).2.unit : ZMod q) :=
      ((Finset.mem_filter.mp hx).2.unit_spec).symm
    have hy' : y = ((Finset.mem_filter.mp hy).2.unit : ZMod q) :=
      ((Finset.mem_filter.mp hy).2.unit_spec).symm
    rw [hx', hy', hxy]
  · intro u _
    refine ⟨(u : ZMod q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩, ?_⟩
    exact Units.ext u.isUnit.unit_spec
  · intro x hx
    exact congrArg G ((Finset.mem_filter.mp hx).2.unit_spec).symm


/-- The conjugate of the standard additive character is its negative. -/
private lemma star_stdAddChar442 (q : ℕ) [NeZero q] (x : ZMod q) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hnorm : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  exact (Complex.inv_eq_conj hnorm).symm.trans (AddChar.map_neg_eq_inv _ x).symm

/-- Orthogonality of the character table of the unit group, in conjugate form. -/
private lemma char_orth_pair442 (q : ℕ) [NeZero q] (χ ξ : DirichletCharacter ℂ q)
    [Decidable (χ = ξ)] :
    (∑ u : (ZMod q)ˣ, χ (u : ZMod q) * star (ξ (u : ZMod q)))
      = if χ = ξ then (q.totient : ℂ) else 0 := by
  classical
  have hterm : ∀ u : (ZMod q)ˣ, χ (u : ZMod q) * star (ξ (u : ZMod q))
      = (χ * ξ⁻¹) (u : ZMod q) := by
    intro u
    rw [MulChar.mul_apply, MulChar.star_apply']
  simp only [hterm]
  rw [← sum_zmod_eq_units442 q (fun x => (χ * ξ⁻¹) x) (fun x hx => MulChar.map_nonunit _ hx)]
  rw [show (∑ x : ZMod q, (χ * ξ⁻¹) x) = if (χ * ξ⁻¹) = 1 then (q.totient : ℂ) else 0 from ?_]
  · have hiff : (χ * ξ⁻¹ = 1) ↔ χ = ξ := by
      constructor
      · intro h
        calc χ = χ * 1 := (mul_one χ).symm
          _ = χ * (ξ⁻¹ * ξ) := by rw [inv_mul_cancel]
          _ = (χ * ξ⁻¹) * ξ := by rw [mul_assoc]
          _ = 1 * ξ := by rw [h]
          _ = ξ := one_mul ξ
      · rintro rfl; simp
    by_cases h : χ = ξ
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]
  · by_cases h : (χ * ξ⁻¹) = 1
    · rw [if_pos h, show (∑ x : ZMod q, (χ * ξ⁻¹) x)
          = ∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x from by rw [h]]
      rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
    · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one h]


/-- The conjugate of a character value at a unit is its value at the inverse. -/
private lemma star_char_apply442 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (u : (ZMod q)ˣ) :
    star (χ (u : ZMod q)) = χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]

/-- Twisting the standard additive character by a unit and summing against the
inverse character multiplies the Gauss sum by the character value. -/
private lemma gauss_twist442 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (u : (ZMod q)ˣ) :
    (∑ v : ZMod q, ZMod.stdAddChar (-(v * (u : ZMod q))) * χ⁻¹ v)
      = star (gaussSum χ ZMod.stdAddChar) * χ (u : ZMod q) := by
  have hg : (∑ v : ZMod q, ZMod.stdAddChar (-(v * (u : ZMod q))) * χ⁻¹ v)
      = gaussSum χ⁻¹ (ZMod.stdAddChar⁻¹.mulShift (u : ZMod q)) := by
    rw [gaussSum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [AddChar.mulShift_apply, AddChar.inv_apply]
    calc ZMod.stdAddChar (-(v * (u : ZMod q))) * χ⁻¹ v
        = χ⁻¹ v * ZMod.stdAddChar (-(v * (u : ZMod q))) := mul_comm _ _
      _ = χ⁻¹ v * ZMod.stdAddChar (-((u : ZMod q) * v)) := by rw [mul_comm v (u : ZMod q)]
  rw [hg, gaussSum_mulShift_eq χ⁻¹ (ZMod.stdAddChar⁻¹) u, inv_inv]
  rw [show gaussSum χ⁻¹ (ZMod.stdAddChar⁻¹) = star (gaussSum χ ZMod.stdAddChar) from
    (star_gaussSum_eq χ ZMod.stdAddChar).symm]
  exact mul_comm _ _

/-- Parseval for the character table of the unit group: the mean square of a
character combination is the totient times the squared coefficients. -/
private lemma parseval_char442 (q : ℕ) [NeZero q] (f : DirichletCharacter ℂ q → ℂ) :
    (∑ u : (ZMod q)ˣ,
        (∑ χ : DirichletCharacter ℂ q, f χ * χ (u : ZMod q))
          * star (∑ χ : DirichletCharacter ℂ q, f χ * χ (u : ZMod q)))
      = (q.totient : ℂ) * ∑ χ : DirichletCharacter ℂ q, f χ * star (f χ) := by
  classical
  have hterm : ∀ u : (ZMod q)ˣ,
      (∑ χ : DirichletCharacter ℂ q, f χ * χ (u : ZMod q))
          * star (∑ χ : DirichletCharacter ℂ q, f χ * χ (u : ZMod q))
        = ∑ χ : DirichletCharacter ℂ q, ∑ ξ : DirichletCharacter ℂ q,
            (f χ * star (f ξ)) * (χ (u : ZMod q) * star (ξ (u : ZMod q))) := by
    intro u
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [star_mul]
    ring
  simp only [hterm]
  calc (∑ u : (ZMod q)ˣ, ∑ χ : DirichletCharacter ℂ q, ∑ ξ : DirichletCharacter ℂ q,
          (f χ * star (f ξ)) * (χ (u : ZMod q) * star (ξ (u : ZMod q))))
      = ∑ χ : DirichletCharacter ℂ q, ∑ u : (ZMod q)ˣ, ∑ ξ : DirichletCharacter ℂ q,
          (f χ * star (f ξ)) * (χ (u : ZMod q) * star (ξ (u : ZMod q))) := Finset.sum_comm
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ ξ : DirichletCharacter ℂ q, ∑ u : (ZMod q)ˣ,
          (f χ * star (f ξ)) * (χ (u : ZMod q) * star (ξ (u : ZMod q))) := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        exact Finset.sum_comm
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ ξ : DirichletCharacter ℂ q,
          (f χ * star (f ξ)) * (if χ = ξ then (q.totient : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun χ _ => Finset.sum_congr rfl (fun ξ _ => ?_))
        rw [← Finset.mul_sum, char_orth_pair442]
    _ = ∑ χ : DirichletCharacter ℂ q, f χ * star (f χ) * (q.totient : ℂ) := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [Finset.sum_eq_single χ]
        · rw [if_pos rfl]
        · intro ξ _ hξ
          rw [if_neg (fun h : χ = ξ => hξ h.symm), mul_zero]
        · intro h; exact absurd (Finset.mem_univ χ) h
    _ = (q.totient : ℂ) * ∑ χ : DirichletCharacter ℂ q, f χ * star (f χ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun χ _ => by ring)

/-- Expansion of a function on `ZMod q` in the character table of the unit group. -/
private lemma char_expansion442 (q : ℕ) [NeZero q] (G : ZMod q → ℂ) (u : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q, (∑ y : ZMod q, χ y * G y) * star (χ (u : ZMod q)))
      = (q.totient : ℂ) * G (u : ZMod q) := by
  classical
  have hterm : ∀ χ : DirichletCharacter ℂ q,
      (∑ y : ZMod q, χ y * G y) * star (χ (u : ZMod q))
        = ∑ y : ZMod q, G y * (χ y * star (χ (u : ZMod q))) := by
    intro χ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  simp only [hterm]
  rw [Finset.sum_comm]
  have horth : ∀ y : ZMod q, (∑ χ : DirichletCharacter ℂ q, χ y * star (χ (u : ZMod q)))
      = if (u : ZMod q) = y then (q.totient : ℂ) else 0 := by
    intro y
    have hfun : ∀ χ : DirichletCharacter ℂ q, χ y * star (χ (u : ZMod q))
        = χ (y * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
      intro χ
      rw [star_char_apply442, map_mul]
    simp only [hfun]
    rw [DirichletCharacter.sum_characters_eq]
    have hiff : y * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 ↔ ((u : ZMod q) = y) := by
      constructor
      · intro h
        have hy : y * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q) = (u : ZMod q) := by
          rw [h, one_mul]
        rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one] at hy
        exact hy.symm
      · intro h
        rw [← h, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    by_cases hy : (u : ZMod q) = y
    · rw [if_pos (hiff.mpr hy), if_pos hy]
    · rw [if_neg (fun h => hy (hiff.mp h)), if_neg hy]
  calc (∑ y : ZMod q, ∑ χ : DirichletCharacter ℂ q, G y * (χ y * star (χ (u : ZMod q))))
      = ∑ y : ZMod q, G y * (if (u : ZMod q) = y then (q.totient : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← Finset.mul_sum, horth]
    _ = (q.totient : ℂ) * G (u : ZMod q) := by
        rw [Finset.sum_eq_single ((u : ZMod q))]
        · rw [if_pos rfl]; ring
        · intro y _ hy
          rw [if_neg (fun h : (u : ZMod q) = y => hy h.symm), mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h


/-- Unit character values have modulus one. -/
private lemma norm_char_apply442 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (u : (ZMod q)ˣ) : ‖χ (u : ZMod q)‖ = 1 := by
  have hpow : ‖χ (u : ZMod q)‖ ^ orderOf u = 1 := by
    rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    simp
  have hn : orderOf u ≠ 0 := (orderOf_pos u).ne'
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    have hlt' : 1 < ‖χ (u : ZMod q)‖ ^ orderOf u := one_lt_pow₀ hcon hn
    rw [hpow] at hlt'
    exact lt_irrefl 1 hlt'
  · by_contra hcon
    rw [not_le] at hcon
    have hlt' : ‖χ (u : ZMod q)‖ ^ orderOf u < 1 := pow_lt_one₀ (norm_nonneg _) hcon hn
    rw [hpow] at hlt'
    exact lt_irrefl 1 hlt'

/-- Parseval for the discrete Fourier transform on `ZMod q`, in conjugate form. -/
private lemma parseval_zmod442 (q : ℕ) [NeZero q] (F : ZMod q → ℂ) :
    (∑ k : ZMod q, ZMod.dft F k * star (ZMod.dft F k))
      = (q : ℂ) * ∑ j : ZMod q, F j * star (F j) := by
  classical
  have hterm : ∀ k : ZMod q, ZMod.dft F k * star (ZMod.dft F k)
      = ∑ j : ZMod q, ∑ i : ZMod q, F j * star (F i) *
          (ZMod.stdAddChar (-(j * k)) * star (ZMod.stdAddChar (-(i * k)))) := by
    intro k
    have hdft : ZMod.dft F k = ∑ j : ZMod q, ZMod.stdAddChar (-(j * k)) * F j := by
      rw [ZMod.dft_apply]
      simp only [smul_eq_mul]
    rw [hdft, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [star_mul, star_stdAddChar442]
    ring
  simp only [hterm]
  rw [Finset.sum_comm]
  have hswap : (∑ j : ZMod q, ∑ k : ZMod q, ∑ i : ZMod q, F j * star (F i) *
        (ZMod.stdAddChar (-(j * k)) * star (ZMod.stdAddChar (-(i * k)))))
      = ∑ j : ZMod q, ∑ i : ZMod q, ∑ k : ZMod q, F j * star (F i) *
        (ZMod.stdAddChar (-(j * k)) * star (ZMod.stdAddChar (-(i * k)))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact Finset.sum_comm
  rw [hswap]
  have hinner : ∀ j i : ZMod q,
      (∑ k : ZMod q, F j * star (F i) *
        (ZMod.stdAddChar (-(j * k)) * star (ZMod.stdAddChar (-(i * k)))))
      = F j * star (F i) * ((if i = j then (q : ℂ) else 0)) := by
    intro j i
    rw [← Finset.mul_sum]
    have h1 : ∀ k : ZMod q, ZMod.stdAddChar (-(j * k)) * star (ZMod.stdAddChar (-(i * k)))
        = ZMod.stdAddChar (k * (i - j)) := by
      intro k
      rw [star_stdAddChar442, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp only [h1]
    rw [AddChar.sum_mulShift (i - j) (ZMod.isPrimitive_stdAddChar q)]
    by_cases hij : i = j
    · have h0 : i - j = 0 := by rw [hij, sub_self]
      rw [if_pos h0, if_pos hij, ZMod.card]
    · have h0 : ¬ (i - j = 0) := by rw [sub_eq_zero]; exact hij
      rw [if_neg h0, if_neg hij]
      push_cast
      ring
  simp only [hinner]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]; ring
  · intro i _ hi
    rw [if_neg (fun h : i = j => hi h), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Parseval for the discrete Fourier transform on `ZMod q`, in norm form. -/
private lemma parseval_norm_zmod442 (q : ℕ) [NeZero q] (F : ZMod q → ℂ) :
    (∑ k : ZMod q, ‖ZMod.dft F k‖ ^ 2) = (q : ℝ) * ∑ j : ZMod q, ‖F j‖ ^ 2 := by
  have hstep : ∀ z : ℂ, z * star z = (↑(‖z‖ ^ 2) : ℂ) := by
    intro z
    rw [show z * star z = z * (starRingEnd ℂ) z from rfl, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  have hre : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := by
    intro z
    rw [hstep]
    exact Complex.ofReal_re _
  calc (∑ k : ZMod q, ‖ZMod.dft F k‖ ^ 2)
      = (∑ k : ZMod q, ZMod.dft F k * star (ZMod.dft F k)).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl (fun k _ => (hre _).symm)
    _ = ((q : ℂ) * ∑ j : ZMod q, F j * star (F j)).re := by rw [parseval_zmod442]
    _ = (q : ℝ) * ∑ j : ZMod q, ‖F j‖ ^ 2 := by
        rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hq : ((q : ℂ) * (F j * star (F j))).re
            = (q : ℝ) * (F j * star (F j)).re := by
          rw [show (q : ℂ) = ((q : ℝ) : ℂ) from by push_cast; ring]
          exact Complex.re_ofReal_mul (q : ℝ) _
        rw [hq, hre]

/-- The non principal Gauss number has squared modulus at most the modulus. -/
private lemma gauss_bound_nonprincipal442 (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 ≤ (q : ℝ) := by
  classical
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    have h : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  have hchi : (∑ j : ZMod q, ‖(fun y : ZMod q => χ y) j‖ ^ 2) = (q.totient : ℝ) := by
    rw [sum_zmod_eq_units442 q (fun x => ‖χ x‖ ^ 2)
      (fun x hx => by rw [MulChar.map_nonunit _ hx]; simp)]
    have hunit : (∑ u : (ZMod q)ˣ, ‖χ (u : ZMod q)‖ ^ 2) = (q.totient : ℝ) := by
      have hone : ∀ u : (ZMod q)ˣ, ‖χ (u : ZMod q)‖ ^ 2 = (1 : ℝ) := by
        intro u
        rw [norm_char_apply442 q χ u]
        norm_num
      rw [Finset.sum_congr rfl (fun u _ => hone u), Finset.sum_const, Finset.card_univ,
        ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one]
    exact hunit
  have hPS := parseval_norm_zmod442 q (fun y : ZMod q => χ y)
  rw [hchi] at hPS
  have hterm : ∀ u : (ZMod q)ˣ,
      ‖ZMod.dft (fun y : ZMod q => χ y) (-(u : ZMod q))‖ ^ 2
        = ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 := by
    intro u
    rw [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift χ (-(u : ZMod q)), neg_neg]
    rw [gaussSum_mulShift_eq χ ZMod.stdAddChar u, norm_mul,
      show ‖χ⁻¹ (u : ZMod q)‖ = 1 from norm_char_apply442 q χ⁻¹ u, one_mul]
  have himg : (∑ u : (ZMod q)ˣ, ‖ZMod.dft (fun y : ZMod q => χ y) (-(u : ZMod q))‖ ^ 2)
      = ∑ x ∈ Finset.univ.image (fun u : (ZMod q)ˣ => -(u : ZMod q)),
          ‖ZMod.dft (fun y : ZMod q => χ y) x‖ ^ 2 := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Units.ext (neg_injective hab)
  have hlow : (q.totient : ℝ) * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2
      ≤ (q : ℝ) * (q.totient : ℝ) := by
    calc (q.totient : ℝ) * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2
        = ∑ _u : (ZMod q)ˣ, ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
      _ = ∑ u : (ZMod q)ˣ, ‖ZMod.dft (fun y : ZMod q => χ y) (-(u : ZMod q))‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun u _ => (hterm u).symm)
      _ = ∑ x ∈ Finset.univ.image (fun u : (ZMod q)ˣ => -(u : ZMod q)),
            ‖ZMod.dft (fun y : ZMod q => χ y) x‖ ^ 2 := himg
      _ ≤ ∑ x : ZMod q, ‖ZMod.dft (fun y : ZMod q => χ y) x‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => by positivity)
      _ = (q : ℝ) * (q.totient : ℝ) := hPS
  have : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * (q.totient : ℝ) ≤ (q : ℝ) * (q.totient : ℝ) := by
    linarith [hlow]
  exact le_of_mul_le_mul_right (by linarith [hlow]) hφpos


/-- The sum of the Möbius function over the divisors of a positive integer. -/
private lemma moebius_sum_eq442 (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ)) = if n = 1 then 1 else 0 := by
  have H : ∀ m > 0, (∑ i ∈ m.divisors,
      ((ArithmeticFunction.moebius i : ℤ) : ℂ)) = (if m = 1 then (1 : ℂ) else 0) := by
    refine (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (R := ℂ)
      (f := fun i => ((ArithmeticFunction.moebius i : ℤ) : ℂ))
      (g := fun m => if m = 1 then (1 : ℂ) else 0)).mpr ?_
    intro m hm
    have hmne : m ≠ 0 := hm.ne'
    rw [Finset.sum_eq_single (m, 1)]
    · rw [if_pos rfl, zsmul_eq_mul, mul_one]
    · intro x hx hx1
      have hmem := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have h1 : x.2 ≠ 1 := by
        intro h2
        exact hx1 (Prod.ext_iff.mpr ⟨by rw [← hmem, h2, mul_one], h2⟩)
      simp [h1]
    · intro h
      exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨by rw [mul_one], hmne⟩) h
  exact H n hn

/-- The principal Gauss number is a Möbius value. -/
private lemma gauss_principal_eq442 (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar
      = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  classical
  set psi : ℕ → ℂ := fun b => Complex.exp ((2 * Real.pi * ((b : ℝ) / (q : ℝ))) * Complex.I) with hpsi
  have hq0 : 0 < q := by omega
  have hqne : q ≠ 0 := by omega
  -- the Gauss sum is a sum of unit phases
  have hstep1 : gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar
      = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), psi b := by
    rw [gaussSum]
    rw [show (∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * ZMod.stdAddChar x)
        = ∑ u : (ZMod q)ˣ, (1 : DirichletCharacter ℂ q) (u : ZMod q) * ZMod.stdAddChar (u : ZMod q) from
      sum_zmod_eq_units442 q _ (fun x hx => by rw [MulChar.map_nonunit _ hx, zero_mul])]
    rw [show (∑ u : (ZMod q)ˣ, (1 : DirichletCharacter ℂ q) (u : ZMod q) * ZMod.stdAddChar (u : ZMod q))
        = ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (u : ZMod q) from by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [MulChar.one_apply u.isUnit, one_mul]]
    rw [show (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (u : ZMod q))
        = ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((((u : ZMod q)).val : ℕ) : ZMod q) from
      Finset.sum_congr rfl (fun u _ => by rw [ZMod.natCast_zmod_val])]
    rw [sum_units_eq_filter442 q (fun b => ZMod.stdAddChar (b : ZMod q))]
    exact Finset.sum_congr rfl (fun b _ => stdAddChar_nat442 q b)
  rw [hstep1]
  -- the indicator of coprimality as a divisor sum of `psi`
  have hind : ∀ b : ℕ, (if Nat.Coprime b q then (1 : ℂ) else 0)
      = ∑ d ∈ q.divisors, (if d ∣ b then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) := by
    intro b
    have hgcd : 0 < Nat.gcd b q := Nat.gcd_pos_of_pos_right b hq0
    have hdiv : (Nat.gcd b q).divisors = q.divisors.filter (fun d => d ∣ b) := by
      ext d
      rw [Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hdvd, -⟩
        exact ⟨⟨dvd_trans hdvd (Nat.gcd_dvd_right b q), hqne⟩,
          dvd_trans hdvd (Nat.gcd_dvd_left b q)⟩
      · rintro ⟨⟨hdvdq, -⟩, hdvdb⟩
        exact ⟨Nat.dvd_gcd hdvdb hdvdq, hgcd.ne'⟩
    rw [← Finset.sum_filter, ← hdiv, moebius_sum_eq442 (Nat.gcd b q) hgcd]
  have hstep2 : (∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), psi b)
      = ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ b ∈ (range q).filter (fun b => d ∣ b), psi b := by
    calc (∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), psi b)
        = ∑ b ∈ range q, (∑ d ∈ q.divisors, (if d ∣ b then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)) * psi b := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [← hind b]
          by_cases h : Nat.Coprime b q <;> simp [h]
      _ = ∑ b ∈ range q, ∑ d ∈ q.divisors,
            (if d ∣ b then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) * psi b := by
          refine Finset.sum_congr rfl (fun b _ => Finset.sum_mul (s := q.divisors)
            (f := fun d => (if d ∣ b then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)) (a := psi b))
      _ = ∑ d ∈ q.divisors, ∑ b ∈ range q,
            (if d ∣ b then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) * psi b := Finset.sum_comm
      _ = ∑ d ∈ q.divisors, ∑ b ∈ (range q).filter (fun b => d ∣ b),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) * psi b := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          by_cases h : d ∣ b <;> simp [h]
      _ = ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            ∑ b ∈ (range q).filter (fun b => d ∣ b), psi b := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.mul_sum]
  rw [hstep2]
  -- the inner sums are the geometric sums
  have hinner : ∀ d ∈ q.divisors, (∑ b ∈ (range q).filter (fun b => d ∣ b), psi b)
      = if d = q then 1 else 0 := by
    intro d hd
    have hdvd : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hbij : (∑ b ∈ (range q).filter (fun b => d ∣ b), psi b)
        = ∑ c ∈ range (q / d), psi (d * c) := by
      refine Finset.sum_bij (fun b _ => b / d) ?_ ?_ ?_ ?_
      · intro b hb
        obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
        refine Finset.mem_range.mpr ?_
        have hlt : b < q := Finset.mem_range.mp hb1
        have hbm : b = d * (b / d) := by
          rw [mul_comm]
          exact (Nat.div_mul_cancel hb2).symm
        have hqm : q = d * (q / d) := (Nat.mul_div_cancel' hdvd).symm
        have hmul : d * (b / d) < d * (q / d) := by
          rw [← hbm, ← hqm]
          exact hlt
        exact Nat.lt_of_mul_lt_mul_left hmul
      · intro b1 hb1 b2 hb2 heq
        obtain ⟨-, h1⟩ := Finset.mem_filter.mp hb1
        obtain ⟨-, h2⟩ := Finset.mem_filter.mp hb2
        rw [← Nat.div_mul_cancel h1, ← Nat.div_mul_cancel h2, heq]
      · intro c hc
        refine ⟨d * c, ?_, Nat.mul_div_cancel_left c hdpos⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, dvd_mul_right d c⟩
        have hc' := Finset.mem_range.mp hc
        have : d * c < d * (q / d) := Nat.mul_lt_mul_of_pos_left hc' hdpos
        rwa [Nat.mul_div_cancel' hdvd] at this
      · intro b hb
        obtain ⟨-, h2⟩ := Finset.mem_filter.mp hb
        rw [show d * (b / d) = b from by rw [mul_comm]; exact Nat.div_mul_cancel h2]
    rw [hbij]
    have hterm : ∀ c : ℕ, psi (d * c)
        = Complex.exp ((2 * Real.pi * ((c : ℝ) / ((q / d : ℕ) : ℝ))) * Complex.I) := by
      intro c
      rw [hpsi]
      simp only
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
      have hdc : (((d * c : ℕ)) : ℝ) = (d : ℝ) * (c : ℝ) := by push_cast; ring
      have hdq : ((q : ℝ)) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      rw [hdc, hdq]
      congr 1
      push_cast
      have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
      rw [mul_div_mul_left _ _ hdC]
    have hqd : 0 < q / d := Nat.div_pos (Nat.divisor_le hd) hdpos
    rw [Finset.sum_congr rfl (fun c _ => hterm c), geom_exp_sum442 (q / d) hqd]
    have heq : (q / d = 1) ↔ (d = q) := by
      constructor
      · intro h
        rw [← Nat.mul_div_cancel' hdvd, h, mul_one]
      · intro h
        rw [← h]
        exact Nat.div_self hdpos
    by_cases h : d = q
    · rw [if_pos (heq.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (heq.mp hh)), if_neg h]
  rw [Finset.sum_congr rfl (fun d hd => by rw [hinner d hd])]
  rw [Finset.sum_eq_single q]
  · rw [if_pos rfl, mul_one]
  · intro d _ hd
    rw [if_neg hd, mul_zero]
  · intro h
    exact absurd (Nat.mem_divisors.mpr ⟨dvd_rfl, hqne⟩) h

/-- The principal Gauss number has modulus at most one. -/
private lemma gauss_bound_principal442 (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ‖gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar‖ ^ 2 ≤ 1 := by
  rw [gauss_principal_eq442 q hq]
  have hcast : ((ArithmeticFunction.moebius q : ℤ) : ℂ)
      = ((((ArithmeticFunction.moebius q : ℤ)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have h := ArithmeticFunction.abs_moebius_le_one (n := q)
  have h' : |(((ArithmeticFunction.moebius q : ℤ)) : ℝ)| ≤ 1 := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ |(((ArithmeticFunction.moebius q : ℤ)) : ℝ)| := abs_nonneg _
  nlinarith


/-- Parseval for the character table of the unit group, in norm form. -/
private lemma parseval_norm_char442 (q : ℕ) [NeZero q] (f : DirichletCharacter ℂ q → ℂ) :
    (∑ u : (ZMod q)ˣ, ‖∑ χ : DirichletCharacter ℂ q, f χ * χ (u : ZMod q)‖ ^ 2)
      = (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖f χ‖ ^ 2 := by
  have hre : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := by
    intro z
    rw [show z * star z = z * (starRingEnd ℂ) z from rfl, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    exact Complex.ofReal_re _
  have h := congrArg Complex.re (parseval_char442 q f)
  rw [Complex.re_sum] at h
  have hR : (((q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q, f χ * star (f χ)).re
      = (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖f χ‖ ^ 2 := by
    rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    have hq : (((q.totient : ℂ)) * (f χ * star (f χ))).re
        = (q.totient : ℝ) * (f χ * star (f χ)).re := by
      rw [show ((q.totient : ℂ)) = (((q.totient : ℝ)) : ℂ) from by push_cast; ring]
      exact Complex.re_ofReal_mul (q.totient : ℝ) _
    rw [hq, hre]
  rw [hR] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun u _ => (hre _).symm)

/-- The mean square of the transformed coset series is bounded by the totient
inverse of the character prime sums, the principal one with weight one and the
others with weight the modulus. -/
private lemma core_orthogonality442 (q : ℕ) [NeZero q] (hq : 2 ≤ q) (G : ZMod q → ℂ)
    (hG : ∀ x, ¬ IsUnit x → G x = 0) :
    (∑ u : (ZMod q)ˣ, ‖∑ v : ZMod q,
        (ZMod.stdAddChar (-(v * (u : ZMod q))) : ℂ) * G v‖ ^ 2)
      ≤ 1 / (q.totient : ℝ) *
        (‖∑ x : ZMod q, G x‖ ^ 2
          + (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖∑ x : ZMod q, χ x * G x‖ ^ 2) := by
  classical
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    have h : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  have hφne : ((q.totient : ℂ)) ≠ 0 := by
    have h : ((q.totient : ℝ)) ≠ 0 := hφpos.ne'
    exact_mod_cast h
  set Coeff : DirichletCharacter ℂ q → ℂ := fun χ => ∑ x : ZMod q, χ x * G x with hCoeff
  set Tau : DirichletCharacter ℂ q → ℂ := fun χ => gaussSum χ ZMod.stdAddChar with hTau
  -- inversion of the coset series in the character table
  have hexp : ∀ u : (ZMod q)ˣ, G (u : ZMod q)
      = (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
          Coeff χ * star (χ (u : ZMod q)) := by
    intro u
    have h := char_expansion442 q G u
    have h1 : (1 / (q.totient : ℂ)) * ((q.totient : ℂ) * G (u : ZMod q)) = G (u : ZMod q) := by
      rw [← mul_assoc, one_div, inv_mul_cancel₀ hφne, one_mul]
    rw [← h1, ← h]
  -- the transformed series as a character combination
  have hT : ∀ u : (ZMod q)ˣ, (∑ v : ZMod q,
      (ZMod.stdAddChar (-(v * (u : ZMod q))) : ℂ) * G v)
      = ∑ χ : DirichletCharacter ℂ q,
          (1 / (q.totient : ℂ)) * ((Coeff χ * star (Tau χ)) * χ (u : ZMod q)) := by
    intro u
    have htwist : ∀ χ : DirichletCharacter ℂ q,
        (∑ v : (ZMod q)ˣ, (ZMod.stdAddChar (-((v : ZMod q) * (u : ZMod q))) : ℂ)
          * star (χ (v : ZMod q))) = star (Tau χ) * χ (u : ZMod q) := by
      intro χ
      rw [← sum_zmod_eq_units442 q
        (fun v : ZMod q => (ZMod.stdAddChar (-(v * (u : ZMod q))) : ℂ) * star (χ v))
        (fun v hv => by rw [MulChar.map_nonunit _ hv]; simp)]
      have h1 : ∀ v : ZMod q, star (χ v) = χ⁻¹ v := fun v => MulChar.star_apply' χ v
      simp only [h1]
      rw [hTau]
      exact gauss_twist442 q χ u
    calc (∑ v : ZMod q, (ZMod.stdAddChar (-(v * (u : ZMod q))) : ℂ) * G v)
        = ∑ v : (ZMod q)ˣ, (ZMod.stdAddChar (-((v : ZMod q) * (u : ZMod q))) : ℂ)
            * G (v : ZMod q) := by
          rw [sum_zmod_eq_units442 q
            (fun v : ZMod q => (ZMod.stdAddChar (-(v * (u : ZMod q))) : ℂ) * G v)
            (fun v hv => by rw [hG v hv, mul_zero])]
      _ = ∑ v : (ZMod q)ˣ, (ZMod.stdAddChar (-((v : ZMod q) * (u : ZMod q))) : ℂ)
            * ((1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
                Coeff χ * star (χ (v : ZMod q))) := by
          exact Finset.sum_congr rfl (fun v _ => by rw [hexp v])
      _ = ∑ v : (ZMod q)ˣ, (1 / (q.totient : ℂ)) *
            ((ZMod.stdAddChar (-((v : ZMod q) * (u : ZMod q))) : ℂ)
              * ∑ χ : DirichletCharacter ℂ q, Coeff χ * star (χ (v : ZMod q))) := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          ring
      _ = ∑ v : (ZMod q)ˣ, (1 / (q.totient : ℂ)) *
            ∑ χ : DirichletCharacter ℂ q,
              (ZMod.stdAddChar (-((v : ZMod q) * (u : ZMod q))) : ℂ)
                * (Coeff χ * star (χ (v : ZMod q))) := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ v : (ZMod q)ˣ, ∑ χ : DirichletCharacter ℂ q,
              (1 / (q.totient : ℂ)) * ((ZMod.stdAddChar (-((v : ZMod q) * (u : ZMod q))) : ℂ)
                * (Coeff χ * star (χ (v : ZMod q)))) := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ χ : DirichletCharacter ℂ q, ∑ v : (ZMod q)ˣ,
              (1 / (q.totient : ℂ)) * ((ZMod.stdAddChar (-((v : ZMod q) * (u : ZMod q))) : ℂ)
                * (Coeff χ * star (χ (v : ZMod q)))) := Finset.sum_comm
      _ = ∑ χ : DirichletCharacter ℂ q,
            (1 / (q.totient : ℂ)) * ((Coeff χ * star (Tau χ)) * χ (u : ZMod q)) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [← Finset.mul_sum]
          rw [show (∑ v : (ZMod q)ˣ, (ZMod.stdAddChar (-((v : ZMod q) * (u : ZMod q))) : ℂ)
              * (Coeff χ * star (χ (v : ZMod q))))
              = Coeff χ * ∑ v : (ZMod q)ˣ,
                  (ZMod.stdAddChar (-((v : ZMod q) * (u : ZMod q))) : ℂ) * star (χ (v : ZMod q)) from by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun v _ => by ring)]
          rw [htwist χ]
          ring

  have hkey : (∑ u : (ZMod q)ˣ, ‖∑ v : ZMod q,
      (ZMod.stdAddChar (-(v * (u : ZMod q))) : ℂ) * G v‖ ^ 2)
      = 1 / (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖Coeff χ‖ ^ 2 * ‖Tau χ‖ ^ 2 := by
    rw [show (∑ u : (ZMod q)ˣ, ‖∑ v : ZMod q,
        (ZMod.stdAddChar (-(v * (u : ZMod q))) : ℂ) * G v‖ ^ 2)
        = ∑ u : (ZMod q)ˣ, ‖∑ χ : DirichletCharacter ℂ q,
            ((1 / (q.totient : ℂ)) * (Coeff χ * star (Tau χ))) * χ (u : ZMod q)‖ ^ 2 from by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [hT u]
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (Finset.sum_congr rfl (fun χ _ => by ring))]
    rw [parseval_norm_char442 q (fun χ => (1 / (q.totient : ℂ)) * (Coeff χ * star (Tau χ)))]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    have hφnorm : ‖(1 / (q.totient : ℂ))‖ = 1 / (q.totient : ℝ) := by
      have h : ‖((q.totient : ℂ))‖ = ((q.totient : ℝ)) := by
        rw [show ((q.totient : ℂ)) = (((q.totient : ℝ)) : ℂ) from by push_cast; ring]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg q.totient)]
      rw [norm_div, norm_one, h]
    rw [norm_mul, norm_mul, norm_star, hφnorm]
    field_simp
    try ring
  rw [hkey]
  -- bound the character coefficients
  have hCoeffOne : Coeff 1 = ∑ x : ZMod q, G x := by
    rw [hCoeff]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : IsUnit x
    · rw [MulChar.one_apply hx, one_mul]
    · rw [MulChar.map_nonunit _ hx, zero_mul, hG x hx]
  have hsplit : (∑ χ : DirichletCharacter ℂ q, ‖Coeff χ‖ ^ 2 * ‖Tau χ‖ ^ 2)
      = ‖Coeff 1‖ ^ 2 * ‖Tau 1‖ ^ 2
        + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖Coeff χ‖ ^ 2 * ‖Tau χ‖ ^ 2 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have hbound : (∑ χ : DirichletCharacter ℂ q, ‖Coeff χ‖ ^ 2 * ‖Tau χ‖ ^ 2)
      ≤ ‖Coeff 1‖ ^ 2 + (q : ℝ) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Coeff χ‖ ^ 2 := by
    rw [hsplit]
    have hp : ‖Tau 1‖ ^ 2 ≤ 1 := by
      rw [hTau]
      exact gauss_bound_principal442 q hq
    have hn : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ‖Coeff χ‖ ^ 2 * ‖Tau χ‖ ^ 2 ≤ (q : ℝ) * ‖Coeff χ‖ ^ 2 := by
      intro χ hχ
      have hne : χ ≠ 1 := by
        have := Finset.mem_erase.mp hχ
        exact this.1
      have hb : ‖Tau χ‖ ^ 2 ≤ (q : ℝ) := by
        rw [hTau]
        exact gauss_bound_nonprincipal442 q hq χ hne
      have hc : (0 : ℝ) ≤ ‖Coeff χ‖ ^ 2 := by positivity
      calc ‖Coeff χ‖ ^ 2 * ‖Tau χ‖ ^ 2 ≤ ‖Coeff χ‖ ^ 2 * (q : ℝ) :=
            mul_le_mul_of_nonneg_left hb hc
        _ = (q : ℝ) * ‖Coeff χ‖ ^ 2 := by ring
    have hsum : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖Coeff χ‖ ^ 2 * ‖Tau χ‖ ^ 2)
        ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), (q : ℝ) * ‖Coeff χ‖ ^ 2 :=
      Finset.sum_le_sum hn
    have hfilter : (Finset.univ.erase (1 : DirichletCharacter ℂ q))
        = Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) := by
      ext χ
      simp [Finset.mem_erase, eq_comm]
    rw [hfilter] at hsum ⊢
    rw [← Finset.mul_sum] at hsum
    have h1 : ‖Coeff 1‖ ^ 2 * ‖Tau 1‖ ^ 2 ≤ ‖Coeff 1‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    linarith
  rw [hCoeffOne] at hbound
  have hφ : (0 : ℝ) ≤ 1 / (q.totient : ℝ) := by positivity
  calc 1 / (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖Coeff χ‖ ^ 2 * ‖Tau χ‖ ^ 2
      ≤ 1 / (q.totient : ℝ) * (‖∑ x : ZMod q, G x‖ ^ 2 + (q : ℝ) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Coeff χ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound hφ
    _ = 1 / (q.totient : ℝ) *
        (‖∑ x : ZMod q, G x‖ ^ 2
          + (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖∑ x : ZMod q, χ x * G x‖ ^ 2) := by
        rw [hCoeff]


/-- The character prime series is the character weighted sum of the coset series. -/
private lemma fiber442 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ)
    (χ : DirichletCharacter ℂ q) :
    characterPrime280 χ N z
      = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
          χ (b : ZMod q) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
            ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
  classical
  have hq0 : 0 < q := by omega
  set w : Nat.Primes → ℂ := fun p => (Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
    Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) with hw
  have hW : Summable w := by
    rw [hw]
    simpa only [neg_div] using prime_fourier_summable111 N hN z
  have hcoe : ∀ p : Nat.Primes, (((p : ℕ) : ZMod q)) = ((((p : ℕ)) % q : ℕ) : ZMod q) := by
    intro p
    rw [← ZMod.natCast_zmod_val ((p : ℕ) : ZMod q), ZMod.val_natCast]
  have hterm : ∀ p : Nat.Primes, χ (((p : ℕ)) : ZMod q) * w p
      = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
          (if ((p : ℕ) % q = b) then χ (b : ZMod q) * w p else 0) := by
    intro p
    by_cases hb : ((p : ℕ) % q) ∈ (range q).filter (fun b => Nat.Coprime b q)
    · rw [Finset.sum_eq_single ((p : ℕ) % q)]
      · rw [if_pos rfl, hcoe p]
      · intro b _ hne
        rw [if_neg (fun h : (p : ℕ) % q = b => hne h.symm)]
      · intro h
        exact absurd hb h
    · rw [Finset.sum_eq_zero]
      · have hnp : ¬ IsUnit ((((p : ℕ)) % q : ℕ) : ZMod q) := by
          intro hu
          exact hb (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq0),
            (ZMod.isUnit_iff_coprime _ _).mp hu⟩)
        rw [hcoe p, MulChar.map_nonunit _ hnp, zero_mul]
      · intro b hb2
        by_cases h : ((p : ℕ) % q = b)
        · exact absurd hb2 (h ▸ hb)
        · rw [if_neg h]
  have hfib : ∀ b ∈ (range q).filter (fun b => Nat.Coprime b q),
      Summable (fun p : Nat.Primes => if ((p : ℕ) % q = b) then χ (b : ZMod q) * w p else 0) := by
    intro b hb
    have hbco : Nat.Coprime b q := (Finset.mem_filter.mp hb).2
    have hunit : ((b : ZMod q)) = ((ZMod.unitOfCoprime b hbco : (ZMod q)ˣ) : ZMod q) :=
      ZMod.coe_unitOfCoprime b hbco
    have hnorm : ‖χ (b : ZMod q)‖ = 1 := by
      rw [hunit]
      exact norm_char_apply442 q χ (ZMod.unitOfCoprime b hbco)
    refine Summable.of_norm_bounded hW.norm (fun p => ?_)
    by_cases h : ((p : ℕ) % q = b)
    · rw [if_pos h, norm_mul, hnorm, one_mul]
    · rw [if_neg h, norm_zero]
      positivity
  have hmain : (∑' p : Nat.Primes, χ (((p : ℕ)) : ZMod q) * w p)
      = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
          χ (b : ZMod q) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then w p else 0) := by
    calc (∑' p : Nat.Primes, χ (((p : ℕ)) : ZMod q) * w p)
        = ∑' p : Nat.Primes, ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
            (if ((p : ℕ) % q = b) then χ (b : ZMod q) * w p else 0) :=
          tsum_congr hterm
      _ = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
            ∑' p : Nat.Primes, (if ((p : ℕ) % q = b) then χ (b : ZMod q) * w p else 0) :=
          Summable.tsum_finsetSum hfib
      _ = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
            χ (b : ZMod q) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then w p else 0) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [← tsum_mul_left]
          exact tsum_congr (fun p => by
            by_cases h : ((p : ℕ) % q = b) <;> simp [h])
  calc characterPrime280 χ N z
      = (∑' p : Nat.Primes, χ (((p : ℕ)) : ZMod q) * w p) := by
        rw [characterPrime280]
        exact tsum_congr (fun p => by rw [hw]; ring)
    _ = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
          χ (b : ZMod q) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then w p else 0) := hmain
    _ = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
          χ (b : ZMod q) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
            ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
        rw [hw]



/-- The phase of the prime term at the shifted reduced fraction is the coset
phase of the residue class of the prime, times the phase of the shift alone, on
the unit circle: only the exponent modulo `2 pi` matters. -/
private lemma circle_exp_coset442 (q : ℕ) (hq : 0 < q) (z : ℝ) (a : ℕ) (p : Nat.Primes) :
    Circle.exp (-(2 * Real.pi * ((a : ℝ) / (q : ℝ) + z) * ((p : ℕ) : ℝ))) =
      Circle.exp (-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ)))) *
        Circle.exp (-(2 * Real.pi * z * ((p : ℕ) : ℝ))) := by
  rw [← Circle.exp_add, Circle.exp_eq_exp]
  set n : ℕ := (p : ℕ) / q with hn
  refine ⟨-((a * n : ℕ) : ℤ), ?_⟩
  have hpq : ((p : ℕ) : ℝ) = (q : ℝ) * (n : ℝ) + ((((p : ℕ) % q : ℕ)) : ℝ) := by
    have h := Nat.div_add_mod (p : ℕ) q
    have h2 : ((q * ((p : ℕ) / q) + (p : ℕ) % q : ℕ) : ℝ) = ((p : ℕ) : ℝ) := by rw [h]
    rw [← hn] at h2
    push_cast at h2
    exact h2.symm
  have hqR : (q : ℝ) ≠ 0 := by
    have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact ne_of_gt hq'
  push_cast
  rw [hpq]
  field_simp
  ring

/-- The same identity for the complex exponential. -/
private lemma exp_arg_coset442 (q : ℕ) (hq : 0 < q) (z : ℝ) (a : ℕ) (p : Nat.Primes) :
    Complex.exp ((-(2 * Real.pi * ((a : ℝ) / (q : ℝ) + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) =
      Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) := by
  have h := circle_exp_coset442 q hq z a p
  have hcoe : ∀ t : ℝ, Complex.exp ((t : ℝ) * Complex.I) = ((Circle.exp t : Circle) : ℂ) :=
    fun t => (Circle.coe_exp t).symm
  rw [hcoe, hcoe, hcoe]
  simpa using congrArg (fun c : Circle => (c : ℂ)) h

/-- LEAF. Step 1 of 3: the residue coset splitting identity. The prime series at
the shifted reduced fraction is the sum, over the residue cosets of the
modulus, of the coset phase times the coset series, the latter carrying the
damping and the oscillation in the shift but not the shift by the fraction.
Each coset series is absolutely convergent, so the regrouping is an identity and
no estimate is involved. -/
theorem prime_class_split442 (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) (a : ℕ) :
    primeFourier111 N ((a : ℝ) / q + z) =
      (∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) +
      (∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) := by
  classical
  have hq0 : 0 < q := by omega
  have hW : Summable (fun p : Nat.Primes => ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) := by
    simpa only [neg_div] using prime_fourier_summable111 N hN z
  have hfib : ∀ b ∈ Finset.range q,
      Summable (fun p : Nat.Primes => if ((p : ℕ) % q = b) then
        (Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) else 0) := by
    intro b hb
    refine Summable.of_norm_bounded hW.norm (fun p => ?_)
    by_cases h : ((p : ℕ) % q = b)
    · rw [if_pos h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    · rw [if_neg h, norm_zero]
      positivity
  have hterm : ∀ p : Nat.Primes,
      (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * ((a : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) =
        ∑ b ∈ Finset.range q, (if ((p : ℕ) % q = b) then
            Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
              ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
    intro p
    have hsingle : (∑ b ∈ Finset.range q, (if ((p : ℕ) % q = b) then
            Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
              ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) =
          Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) *
              Complex.I) *
            ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
      refine (Finset.sum_eq_single (s := Finset.range q)
        (f := fun b => (if ((p : ℕ) % q = b) then
            Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
              ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0))
        ((p : ℕ) % q) ?_ ?_).trans (if_pos rfl)
      · intro b hb hne
        rw [if_neg (fun hh => hne hh.symm)]
      · intro hmem
        exfalso
        exact hmem (Finset.mem_range.mpr (Nat.mod_lt ((p : ℕ)) hq0))
    rw [hsingle, exp_arg_coset442 q hq0 z a p, neg_div]
    ring
  have hmain : primeFourier111 N ((a : ℝ) / q + z) =
      ∑ b ∈ Finset.range q, Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
    unfold primeFourier111
    trans ∑' p : Nat.Primes, ∑ b ∈ Finset.range q, (if ((p : ℕ) % q = b) then
            Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
              ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)
    · exact tsum_congr (fun p => hterm p)
    · rw [Summable.tsum_finsetSum hfib]
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [← tsum_mul_left]
      refine tsum_congr (fun p => ?_)
      by_cases h : ((p : ℕ) % q = b) <;> simp [h]
  rw [hmain, ← Finset.sum_filter_add_sum_filter_not (s := Finset.range q)
    (f := fun b => Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0))
    (p := fun b => Nat.Coprime b q)]

/-- LEAF. Step 2 of 3: unit character orthogonality with the Gauss numbers. On
the cosets coprime to the modulus the coset phases form the character table up
to Gauss numbers, so the sum of squared coset sums over the reduced residues is
the squared character prime sums weighted by the squared Gauss numbers, divided
by the totient. The principal Gauss number has modulus at most one, every other
one has squared modulus at most the modulus, and the coset sums are exactly the
character prime sums of the statement, the characters themselves vanishing on
the prime divisors of the modulus, so the two sides are identified character by
character. No integral and no shift estimate occurs. -/
theorem unit_character_orthogonality442 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (hq : 2 ≤ q)
    (z : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
      1 / (q.totient : ℝ) *
        (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2) := by

  classical
  have hq0 : 0 < q := by omega
  set w : Nat.Primes → ℂ := fun p => (Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
    Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) with hw
  set G : ZMod q → ℂ := fun x => if IsUnit x then
    (∑' p : Nat.Primes, if (((p : ℕ)) : ZMod q) = x then w p else 0) else 0 with hG
  have hG0 : ∀ x, ¬ IsUnit x → G x = 0 := fun x hx => by
    rw [hG]
    simp only [hx, if_false]
  have hcore := core_orthogonality442 q hq G hG0
  -- residue class description of the values of `G` at units
  have hGu : ∀ u : (ZMod q)ˣ, G (u : ZMod q)
      = ∑' p : Nat.Primes, if ((p : ℕ) % q = ((u : ZMod q)).val) then w p else 0 := by
    intro u
    have hcond : ∀ p : Nat.Primes, ((((p : ℕ)) : ZMod q) = (u : ZMod q)) ↔
        ((((p : ℕ)) % q) = ((u : ZMod q)).val) := by
      intro p
      constructor
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast] at hv
        rw [show ((u : ZMod q)) = ((((u : ZMod q)).val : ℕ) : ZMod q) from
          (ZMod.natCast_zmod_val _).symm] at hv
        rwa [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt (u : ZMod q))] at hv
      · intro h
        rw [← ZMod.natCast_zmod_val (((p : ℕ)) : ZMod q), ZMod.val_natCast, h,
          ZMod.natCast_zmod_val]
    rw [hG]
    simp only [u.isUnit, if_true]
    exact tsum_congr (fun p => by
      by_cases h : (((p : ℕ)) : ZMod q) = (u : ZMod q)
      · rw [if_pos h, if_pos ((hcond p).mp h)]
      · rw [if_neg h, if_neg (fun hh => h ((hcond p).mpr hh))])
  -- identification of the left hand side
  have hL : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2)
      = ∑ u : (ZMod q)ˣ, ‖∑ v : ZMod q,
          (ZMod.stdAddChar (-(v * (u : ZMod q))) : ℂ) * G v‖ ^ 2 := by
    rw [← sum_units_eq_filter_real442 q
      (fun a => ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2)]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    refine congrArg (fun z : ℂ => ‖z‖ ^ 2) ?_
    rw [show (∑ v : ZMod q, (ZMod.stdAddChar (-(v * (u : ZMod q))) : ℂ) * G v)
        = ∑ v : (ZMod q)ˣ, (ZMod.stdAddChar (-((v : ZMod q) * (u : ZMod q))) : ℂ)
            * G (v : ZMod q) from
      sum_zmod_eq_units442 q (fun v : ZMod q => (ZMod.stdAddChar (-(v * (u : ZMod q))) : ℂ) * G v)
        (fun v hv => by rw [hG0 v hv, mul_zero])]
    rw [← sum_units_eq_filter442 q (fun b =>
      (Complex.exp ((-(2 * Real.pi * (((u : ZMod q).val : ℝ) * (b : ℝ) / (q : ℝ))) : ℝ) * Complex.I) *
      (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then w p else 0) : ℂ))]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hexp : Complex.exp ((-(2 * Real.pi *
          (((u : ZMod q).val : ℝ) * ((v : ZMod q).val : ℝ) / (q : ℝ))) : ℝ) * Complex.I)
        = (ZMod.stdAddChar (-((v : ZMod q) * (u : ZMod q))) : ℂ) := by
      rw [show (-((v : ZMod q) * (u : ZMod q)))
          = -((((v : ZMod q).val : ℕ) : ZMod q) * ((((u : ZMod q).val : ℕ)) : ZMod q)) from by
        rw [ZMod.natCast_zmod_val ((v : ZMod q)), ZMod.natCast_zmod_val ((u : ZMod q))]]
      rw [stdAddChar_nat_neg_mul442]
      congr 1
      push_cast
      ring
    rw [hGu v, hexp]
  -- identification of the right hand side
  have hCoeff : ∀ χ : DirichletCharacter ℂ q, (∑ x : ZMod q, χ x * G x)
      = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
          χ (b : ZMod q) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
            ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
    intro χ
    rw [sum_zmod_eq_units442 q (fun x => χ x * G x) (fun x hx => by rw [hG0 x hx, mul_zero])]
    rw [show (∑ u : (ZMod q)ˣ, χ (u : ZMod q) * G (u : ZMod q))
        = ∑ u : (ZMod q)ˣ, χ ((u : ZMod q).val : ZMod q) *
            (∑' p : Nat.Primes, if ((p : ℕ) % q = ((u : ZMod q)).val) then w p else 0) from by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [hGu u]
      exact congrArg (fun z : ZMod q => χ z *
        ∑' p : Nat.Primes, if ((p : ℕ) % q = ((u : ZMod q)).val) then w p else 0)
        (ZMod.natCast_zmod_val ((u : ZMod q))).symm]
    rw [sum_units_eq_filter442 q (fun b => χ (b : ZMod q) *
      (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then w p else 0))]
  have hR : ∀ χ : DirichletCharacter ℂ q,
      ‖characterPrime280 χ N z‖ ^ 2 = ‖∑ x : ZMod q, χ x * G x‖ ^ 2 := by
    intro χ
    rw [fiber442 N q hN hq z χ, hCoeff χ]
  -- assembly
  rw [hL]
  refine le_trans hcore ?_
  have hR1 : ‖∑ x : ZMod q, G x‖ ^ 2
      = ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
    rw [hR 1]
    refine congrArg (fun z : ℝ => z ^ 2) ?_
    refine congrArg (fun z : ℂ => ‖z‖) ?_
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : IsUnit x
    · rw [MulChar.one_apply hx, one_mul]
    · rw [MulChar.map_nonunit _ hx, zero_mul, hG0 x hx]
  rw [hR1]
  rw [show (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖∑ x : ZMod q, χ x * G x‖ ^ 2)
      = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖characterPrime280 χ N z‖ ^ 2 from
    Finset.sum_congr rfl (fun χ _ => (hR χ).symm)]




/-- Membership of a prime in the prime divisors of the modulus, detected on its
residue class: a prime residue class is non invertible modulo the modulus exactly
when the prime divides the modulus. -/
private lemma mem_primeFactors_iff_not_coprime_mod442 (q : ℕ) (hq : 0 < q) (p : Nat.Primes) :
    ¬ Nat.Coprime ((p : ℕ) % q) q ↔ (p : ℕ) ∈ q.primeFactors := by
  have hp := p.property
  have hqne : q ≠ 0 := by omega
  have hgcd : Nat.gcd ((p : ℕ) % q) q = Nat.gcd (p : ℕ) q := by
    rw [← Nat.gcd_comm q ((p : ℕ))]
    exact (Nat.gcd_rec q ((p : ℕ))).symm
  have hcop : Nat.Coprime ((p : ℕ) % q) q ↔ Nat.Coprime (p : ℕ) q := by
    rw [Nat.Coprime, Nat.Coprime, hgcd]
  rw [hcop, Nat.mem_primeFactors]
  constructor
  · intro h
    refine ⟨hp, ?_, hqne⟩
    by_contra hpd
    exact h ((hp.coprime_iff_not_dvd).mpr hpd)
  · rintro ⟨-, hdvd, -⟩
    exact fun hc => (hp.coprime_iff_not_dvd).mp hc hdvd

/-- The number of distinct prime divisors of the modulus is at most twice its
logarithm, for `q >= 2`. -/
private lemma primeFactors_card_le_log442 (q : ℕ) (hq : 2 ≤ q) :
    ((q.primeFactors.card : ℕ) : ℝ) ≤ 2 * Real.log q := by
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2pos : (0 : ℝ) < Real.log 2 := by linarith
  have hpow : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p := by
    have hbase : ∏ p ∈ q.primeFactors, (2 : ℕ) ≤ ∏ p ∈ q.primeFactors, p := by
      apply Finset.prod_le_prod
      intro p hp
      exact (Nat.mem_primeFactors.mp hp).1.two_le
    simpa using hbase
  have hprod : ∏ p ∈ q.primeFactors, p ≤ q := by
    have hdvd : ∏ p ∈ q.primeFactors, p ∣ q := Nat.prod_primeFactors_dvd q
    exact Nat.le_of_dvd (by omega) hdvd
  have hpowq : 2 ^ q.primeFactors.card ≤ q := le_trans hpow hprod
  have h1 : ((q.primeFactors.card : ℕ) : ℝ) * Real.log 2 ≤ Real.log q := by
    have hcast : ((2 ^ q.primeFactors.card : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast hpowq
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ q.primeFactors.card : ℕ) : ℝ))
      hcast
    rwa [Nat.cast_pow, Real.log_pow] at hlog
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have h2 : ((q.primeFactors.card : ℕ) : ℝ) ≤ Real.log q / Real.log 2 := by
    rw [le_div_iff₀ h2pos]
    linarith
  have h3 : Real.log q / Real.log 2 ≤ 2 * Real.log q := by
    rw [div_le_iff₀ h2pos]
    nlinarith
  linarith

/-- Summing a coset-supported prime series over a set of residues and then summing
the coset sums exchanges the two summations. -/
private lemma sum_coset_swap442 (q : ℕ) (hq : 0 < q) (s : Finset ℕ) (hs : s ⊆ Finset.range q)
    (Ψ : ℕ → ℂ) (hΨ : ∀ b ∈ s, ‖Ψ b‖ ≤ 1) (w : Nat.Primes → ℂ) (hw : Summable w) :
    (∑ b ∈ s, Ψ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then w p else 0)) =
      ∑' p : Nat.Primes, if ((p : ℕ) % q) ∈ s then Ψ ((p : ℕ) % q) * w p else 0 := by
  classical
  have hfib : ∀ b ∈ s, Summable (fun p : Nat.Primes =>
      if ((p : ℕ) % q = b) then Ψ b * w p else 0) := by
    intro b hb
    refine Summable.of_norm_bounded hw.norm (fun p => ?_)
    by_cases h : ((p : ℕ) % q = b)
    · rw [if_pos h, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hΨ b hb)
    · rw [if_neg h, norm_zero]
      positivity
  trans ∑ b ∈ s, ∑' p : Nat.Primes, (if ((p : ℕ) % q = b) then Ψ b * w p else 0)
  · refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [← tsum_mul_left]
    exact tsum_congr (fun p => by by_cases h : ((p : ℕ) % q = b) <;> simp [h])
  · rw [← Summable.tsum_finsetSum hfib]
    refine tsum_congr (fun p => ?_)
    by_cases h : ((p : ℕ) % q) ∈ s
    · rw [if_pos h]
      refine (Finset.sum_eq_single ((p : ℕ) % q) ?_ ?_).trans (if_pos rfl)
      · intro b hb hne
        rw [if_neg (fun hh => hne hh.symm)]
      · intro hmem
        exact absurd h hmem
    · rw [if_neg h]
      refine Finset.sum_eq_zero (fun b hb => ?_)
      by_cases h2 : ((p : ℕ) % q = b)
      · rw [if_pos h2]
        exact absurd (h2 ▸ hb) h
      · rw [if_neg h2]

/-- LEAF. Step 3 of 3: the mass of the residue cosets that are not coprime to
the modulus. A prime in such a coset is divisible by the greatest common divisor
of the coset and the modulus, hence equals one of the prime divisors of the
modulus, so only one coset per prime divisor is nonempty. There are at most
`log q / log 2` of those, each coset series has modulus at most one because it
holds a single damped term, and therefore the squared sum over the reduced
residues of the non unit coset sums is at most the totient times the square of
`2 log q`. -/
theorem prime_divisor_class_mass442 (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
      (q.totient : ℝ) * (2 * Real.log q) ^ 2 := by
  classical
  have hq0 : 0 < q := by omega
  have hW : Summable (fun p : Nat.Primes => ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) := by
    simpa only [neg_div] using prime_fourier_summable111 N hN z
  have hinner : ∀ a : ℕ,
      ‖∑ b ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ≤
      ((q.primeFactors.card : ℕ) : ℝ) := by
    intro a
    have hsw := sum_coset_swap442 q hq0 ((Finset.range q).filter (fun b => ¬ Nat.Coprime b q))
      (Finset.filter_subset _ _)
      (fun b => Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I))
      (fun b hb => by rw [Complex.norm_exp_ofReal_mul_I])
      (fun p : Nat.Primes => ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
        Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) hW
    rw [hsw]
    have hsum : Summable (fun p : Nat.Primes => if ((p : ℕ) % q) ∈
        (Finset.range q).filter (fun b => ¬ Nat.Coprime b q) then
          Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) *
            Complex.I) *
            ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
      refine Summable.of_norm_bounded hW.norm (fun p => ?_)
      by_cases h : ((p : ℕ) % q) ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q)
      · rw [if_pos h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      · rw [if_neg h, norm_zero]
        positivity
    have hcond : ∀ p : Nat.Primes,
        (((p : ℕ) % q) ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q)) ↔
          ((p : ℕ) ∈ q.primeFactors) := by
      intro p
      rw [Finset.mem_filter, Finset.mem_range]
      simp only [Nat.mod_lt ((p : ℕ)) hq0, true_and]
      exact mem_primeFactors_iff_not_coprime_mod442 q hq0 p
    have hsupp : Function.support (fun n : ℕ =>
        if n ∈ q.primeFactors then Real.exp (-((n : ℝ) / N)) else 0) ⊆
        Set.range (fun p : Nat.Primes => (p : ℕ)) := by
      intro n hn
      simp only [Function.mem_support, ne_eq] at hn
      by_cases h : n ∈ q.primeFactors
      · exact ⟨⟨n, (Nat.mem_primeFactors.mp h).1⟩, rfl⟩
      · exact absurd (if_neg h) hn
    calc ‖∑' p : Nat.Primes, if ((p : ℕ) % q) ∈
            (Finset.range q).filter (fun b => ¬ Nat.Coprime b q) then
            Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) *
              Complex.I) *
              ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0‖
        ≤ ∑' p : Nat.Primes, ‖if ((p : ℕ) % q) ∈
            (Finset.range q).filter (fun b => ¬ Nat.Coprime b q) then
            Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) *
              Complex.I) *
              ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0‖ :=
          norm_tsum_le_tsum_norm hsum.norm
      _ = ∑' p : Nat.Primes, if ((p : ℕ) ∈ q.primeFactors) then
            Real.exp (-(((p : ℕ) : ℝ) / N)) else 0 := by
          refine tsum_congr (fun p => ?_)
          by_cases h : ((p : ℕ) % q) ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q)
          · rw [if_pos h, if_pos ((hcond p).mp h), norm_mul, norm_mul,
              Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          · rw [if_neg h, if_neg (fun hh => h ((hcond p).mpr hh)), norm_zero]
      _ = ∑' n : ℕ, (if n ∈ q.primeFactors then Real.exp (-((n : ℝ) / N)) else 0) :=
          Nat.Primes.coe_nat_injective.tsum_eq hsupp
      _ = ∑ n ∈ q.primeFactors, Real.exp (-((n : ℝ) / N)) := by
          rw [tsum_eq_sum (f := fun n : ℕ => if n ∈ q.primeFactors then Real.exp (-((n : ℝ) / N)) else 0)
            (s := q.primeFactors) (fun n hn => by rw [if_neg hn])]
          exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
      _ ≤ ∑ n ∈ q.primeFactors, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          refine Real.exp_le_one_iff.mpr ?_
          have h0 : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
          linarith
      _ = ((q.primeFactors.card : ℕ) : ℝ) := by simp
  have hinner2 : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖∑ b ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 ≤
      (((q.primeFactors.card : ℕ) : ℝ)) ^ 2 := by
    intro a ha
    have h1 := hinner a
    nlinarith [norm_nonneg (∑ b ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0))]
  have hcard : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    exact congrArg Finset.card (Finset.filter_congr (fun a _ => Nat.coprime_comm))
  have hphi : (0 : ℝ) ≤ (q.totient : ℝ) := by positivity
  have hstep : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖∑ b ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
      (q.totient : ℝ) * (((q.primeFactors.card : ℕ) : ℝ)) ^ 2 := by
    have h1 : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖∑ b ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q),
          Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
            Complex.I) *
          (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
            ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          (((q.primeFactors.card : ℕ) : ℝ)) ^ 2 := Finset.sum_le_sum hinner2
    have h2 : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          (((q.primeFactors.card : ℕ) : ℝ)) ^ 2) =
        (q.totient : ℝ) * (((q.primeFactors.card : ℕ) : ℝ)) ^ 2 := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
    exact h1.trans_eq h2
  have hω : (((q.primeFactors.card : ℕ) : ℝ)) ≤ 2 * Real.log q :=
    primeFactors_card_le_log442 q hq
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hsq : (((q.primeFactors.card : ℕ) : ℝ)) ^ 2 ≤ (2 * Real.log q) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ((q.primeFactors.card : ℕ) : ℝ) := by positivity
    nlinarith
  exact le_trans hstep (mul_le_mul_of_nonneg_left hsq hphi)

/-- Assembly of `rational_pointwise_characters442` from the three leaves. The
splitting identity writes each prime series as a unit part plus a non unit part,
the square of a sum is at most twice the squares, and the constants `2` and `8`
absorb the two leaf bounds into the single constant `8` of the statement. -/
theorem rational_pointwise_characters442_split :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q], 1 ≤ N → 2 ≤ q → ∀ z : ℝ,
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      B / (q.totient : ℝ) *
        (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * Real.log q ^ 2  := by
  classical
  refine ⟨8, by norm_num, ?_⟩
  intro N q _ hN hq z
  have hphi : (0 : ℝ) < (q.totient : ℝ) := by
    have h : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  have hpoint : ∀ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2 ≤
      2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 + 2 * ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 := by
    intro a ha
    rw [prime_class_split442 N q hN hq z a]
    have h1 : ‖(∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) + (∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0))‖ ≤
        ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ + ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ := norm_add_le _ _
    have h3 : (‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ + ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖) ^ 2 ≤
        2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 + 2 * ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ - ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖)]
    have h2 : ‖(∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) + (∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0))‖ ^ 2 ≤
        (‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ + ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    linarith
  have hsum : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) +
        2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) := by
    have h1 := Finset.sum_le_sum hpoint
    have h2 : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          (2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 + 2 * ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2)) =
        2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) +
          2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    linarith
  have hU := unit_character_orthogonality442 N q hN hq z
  have hT := prime_divisor_class_mass442 N q hN hq z
  have hX : (0 : ℝ) ≤ ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2 := by
    have ha : (0 : ℝ) ≤ ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
      positivity
    have hb : (0 : ℝ) ≤ ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖characterPrime280 χ N z‖ ^ 2 :=
      Finset.sum_nonneg (fun χ _ => by positivity)
    have hc : (0 : ℝ) ≤ (q : ℝ) := by positivity
    nlinarith
  have h1 : 2 * (1 / (q.totient : ℝ) * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) ≤
      8 / (q.totient : ℝ) * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2) := by
    have hpos : (0 : ℝ) ≤ 1 / (q.totient : ℝ) := div_nonneg zero_le_one hphi.le
    have hm := mul_le_mul_of_nonneg_left (by linarith : 2 * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2) ≤
      8 * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) hpos
    calc 2 * (1 / (q.totient : ℝ) * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) =
          (1 / (q.totient : ℝ)) * (2 * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) := by ring
      _ ≤ (1 / (q.totient : ℝ)) * (8 * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) := hm
      _ = 8 / (q.totient : ℝ) * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2) := by ring
  have h2 : 2 * ((q.totient : ℝ) * (2 * Real.log q) ^ 2) =
      8 * (q.totient : ℝ) * Real.log q ^ 2 := by ring
  have step1 : 2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) +
        2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
      2 * (1 / (q.totient : ℝ) * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) +
        2 * ((q.totient : ℝ) * (2 * Real.log q) ^ 2) := by
    linarith [hU, hT]
  linarith [hsum, step1, h1, h2]

end LeanLab.Linnik1951
