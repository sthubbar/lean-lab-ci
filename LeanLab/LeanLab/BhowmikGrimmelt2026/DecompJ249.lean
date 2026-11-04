/-
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import Mathlib.NumberTheory.DirichletCharacter.Basic
import LeanLab.Zinoviev1997.TotientTail

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- The Euler factor of the generalized singular series at a prime `p`. -/
noncomputable def eulerFactorGen {r₁ r₂ : ℕ} (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ) (p : ℕ) : ℂ :=
  ∑' k : ℕ, if h : p ^ k = 0 then 0 else @Aq r₁ r₂ χ₁ χ₂ N (p ^ k) ⟨h⟩

/-- The Euler factor of the ordinary singular series at a prime `p`. -/
noncomputable def eulerFactorSing (N : ℕ) (p : ℕ) : ℝ :=
  ∑' k : ℕ, (((ArithmeticFunction.moebius (p ^ k) : ℤ) : ℝ) ^ 2 / (Nat.totient (p ^ k) : ℝ) ^ 2) * (ramanujan (p ^ k) N).re

/-- The level `p ^ v_p(r)` of the `p` component of a character mod `r`. It is `1` when `p` is not
a prime factor of `r`, and also when `p` is not prime. -/
abbrev compLevel (r p : ℕ) : ℕ := p ^ r.factorization p

instance compLevel_neZero (r p : ℕ) : NeZero (compLevel r p) := by
  refine ⟨?_⟩
  by_cases hp : p.Prime
  · exact pow_ne_zero _ hp.ne_zero
  · simp [compLevel, Nat.factorization_eq_zero_of_not_prime r hp]

/-- `ψ` is the family of prime power components of `χ`: each `ψ p` is a primitive character mod
`p ^ v_p(r)` and `χ` is their product on the integers coprime to `r`. This is what the Euler
product needs, since `A_q(χ₁, χ₂)` factors through the components and not through `χ₁, χ₂`. -/
def IsPrimeComponents {r : ℕ} (χ : DirichletCharacter ℂ r)
    (ψ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r p)) : Prop :=
  (∀ p, (ψ p).IsPrimitive) ∧
    ∀ a : ℕ, a.Coprime r → χ (a : ZMod r) = ∏ p ∈ r.primeFactors, ψ p (a : ZMod (compLevel r p))

/-! ### Leaf 1: the prime power components of a primitive character -/

private lemma compLevel_dvd (r p : ℕ) [NeZero r] : compLevel r p ∣ r := by
  unfold compLevel
  by_cases hp : p.Prime
  · exact (Nat.Prime.pow_dvd_iff_le_factorization hp (NeZero.ne r)).mpr le_rfl
  · rw [Nat.factorization_eq_zero_of_not_prime r hp, pow_zero]
    exact one_dvd r

private lemma compLevel_mul_compl (r p : ℕ) [NeZero r] :
    compLevel r p * (r / compLevel r p) = r :=
  Nat.mul_div_cancel' (compLevel_dvd r p)

private lemma div_compLevel_dvd (r p : ℕ) [NeZero r] : r / compLevel r p ∣ r :=
  Nat.div_dvd_of_dvd (compLevel_dvd r p)

private lemma compLevel_coprime_compl (r p : ℕ) [NeZero r] :
    Nat.Coprime (compLevel r p) (r / compLevel r p) := by
  unfold compLevel
  by_cases hp : p.Prime
  · exact (Nat.coprime_ordCompl hp (NeZero.ne r)).pow_left _
  · rw [Nat.factorization_eq_zero_of_not_prime r hp, pow_zero]
    exact Nat.coprime_one_left _

private lemma div_compLevel_neZero (r p : ℕ) [NeZero r] : NeZero (r / compLevel r p) :=
  ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos r) (compLevel_dvd r p))
    (Nat.pos_of_neZero (compLevel r p))).ne'⟩

private lemma modEq_of_unitsMap_eq {r n : ℕ} [NeZero r] (hn : n ∣ r) {x y : (ZMod r)ˣ}
    (h : ZMod.unitsMap hn x = ZMod.unitsMap hn y) :
    (x : ZMod r).val ≡ (y : ZMod r).val [MOD n] := by
  have hv : ((ZMod.unitsMap hn x : (ZMod n)ˣ) : ZMod n) =
      ((ZMod.unitsMap hn y : (ZMod n)ˣ) : ZMod n) :=
    congrArg (fun z : (ZMod n)ˣ => (z : ZMod n)) h
  rw [ZMod.unitsMap_val, ZMod.unitsMap_val] at hv
  rw [← ZMod.natCast_val (i := (x : ZMod r)), ← ZMod.natCast_val (i := (y : ZMod r))] at hv
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hv

private lemma unitsMap_pair_injective (r p : ℕ) [NeZero r] :
    Function.Injective (fun x : (ZMod r)ˣ =>
      (ZMod.unitsMap (compLevel_dvd r p) x, ZMod.unitsMap (div_compLevel_dvd r p) x)) := by
  intro x y hxy
  have h1 := modEq_of_unitsMap_eq (compLevel_dvd r p) (x := x) (y := y)
    (congrArg Prod.fst hxy)
  have h2 := modEq_of_unitsMap_eq (div_compLevel_dvd r p) (x := x) (y := y)
    (congrArg Prod.snd hxy)
  have hall : (x : ZMod r).val ≡ (y : ZMod r).val [MOD r] := by
    have hml := (Nat.modEq_and_modEq_iff_modEq_mul (compLevel_coprime_compl r p)).mp ⟨h1, h2⟩
    rw [compLevel_mul_compl r p] at hml
    exact hml
  apply Units.ext
  rw [← ZMod.natCast_zmod_val (x : ZMod r), ← ZMod.natCast_zmod_val (y : ZMod r),
    ZMod.natCast_eq_natCast_iff]
  exact hall

private lemma unitsMap_pair_card (r p : ℕ) [NeZero r] [NeZero (r / compLevel r p)] :
    Fintype.card (ZMod r)ˣ =
      Fintype.card ((ZMod (compLevel r p))ˣ × (ZMod (r / compLevel r p))ˣ) := by
  rw [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient, ← Nat.totient_mul (compLevel_coprime_compl r p),
    compLevel_mul_compl r p]

private lemma unitsMap_pair_bijective (r p : ℕ) [NeZero r] [NeZero (r / compLevel r p)] :
    Function.Bijective (fun x : (ZMod r)ˣ =>
      (ZMod.unitsMap (compLevel_dvd r p) x, ZMod.unitsMap (div_compLevel_dvd r p) x)) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨unitsMap_pair_injective r p, unitsMap_pair_card r p⟩

private lemma unitsMap_pair_bijective' (r p : ℕ) [NeZero r] [NeZero (r / compLevel r p)] :
    Function.Bijective ((ZMod.unitsMap (compLevel_dvd r p)).prod
      (ZMod.unitsMap (div_compLevel_dvd r p))) := by
  have hinj : Function.Injective ((ZMod.unitsMap (compLevel_dvd r p)).prod
      (ZMod.unitsMap (div_compLevel_dvd r p))) := by
    intro x y h
    exact unitsMap_pair_injective r p (by simpa only [MonoidHom.prod_apply] using h)
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, unitsMap_pair_card r p⟩

private lemma prod_compLevel_eq (r : ℕ) [NeZero r] :
    ∏ p ∈ r.primeFactors, compLevel r p = r :=
  (Nat.prod_primeFactors_pow_factorization (NeZero.ne r)).symm

private lemma coprime_compLevel {r : ℕ} [NeZero r] {p q : ℕ} (hp : p ∈ r.primeFactors)
    (hq : q ∈ r.primeFactors) (hpq : p ≠ q) :
    Nat.Coprime (compLevel r p) (compLevel r q) := by
  unfold compLevel
  exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq) hpq

/-- A modulus congruence propagates to the product of the moduli. -/
private lemma modEq_prod {s : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ}
    (hcop : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → Nat.Coprime (f p) (f q))
    (h : ∀ p ∈ s, a ≡ b [MOD f p]) : a ≡ b [MOD ∏ p ∈ s, f p] := by
  induction s using Finset.induction_on with
  | empty => exact Nat.modEq_one
  | insert p s hp ih =>
    rw [Finset.prod_insert hp]
    have hrest : ∀ q ∈ s, ∀ t ∈ s, q ≠ t → Nat.Coprime (f q) (f t) :=
      fun q hq t ht => hcop q (Finset.mem_insert_of_mem hq) t (Finset.mem_insert_of_mem ht)
    have hpall : Nat.Coprime (f p) (∏ q ∈ s, f q) :=
      Nat.Coprime.prod_right (fun q hq => hcop p (Finset.mem_insert_self p s) q
        (Finset.mem_insert_of_mem hq) (fun hpq => hp (hpq ▸ hq)))
    exact (Nat.modEq_and_modEq_iff_modEq_mul hpall).mp
      ⟨h p (Finset.mem_insert_self p s), ih hrest (fun q hq => h q (Finset.mem_insert_of_mem hq))⟩

/-- Units of `ZMod r` are determined by their images modulo the prime power components. -/
private lemma units_ext_of_primeFactors {r : ℕ} [NeZero r] {y z : (ZMod r)ˣ}
    (h : ∀ p ∈ r.primeFactors, ZMod.unitsMap (compLevel_dvd r p) y
      = ZMod.unitsMap (compLevel_dvd r p) z) : y = z := by
  have hmodeq : (y : ZMod r).val ≡ (z : ZMod r).val [MOD ∏ p ∈ r.primeFactors, compLevel r p] :=
    modEq_prod (fun p hp q hq hpq => coprime_compLevel hp hq hpq)
      (fun p hp => modEq_of_unitsMap_eq (compLevel_dvd r p) (h p hp))
  rw [prod_compLevel_eq r] at hmodeq
  apply Units.ext
  rw [← ZMod.natCast_zmod_val (y : ZMod r), ← ZMod.natCast_zmod_val (z : ZMod r),
    ZMod.natCast_eq_natCast_iff]
  exact hmodeq

private lemma compLevel_dvd_div_compl {r p q : ℕ} [NeZero r] (hp : p ∈ r.primeFactors)
    (hq : q ∈ r.primeFactors) (hpq : p ≠ q) : compLevel r q ∣ r / compLevel r p := by
  have hcop : Nat.Coprime (compLevel r q) (compLevel r p) :=
    coprime_compLevel hq hp hpq.symm
  refine hcop.dvd_of_dvd_mul_left ?_
  rw [compLevel_mul_compl r p]
  exact compLevel_dvd r q

/-- A character that factors through `d` is trivial on the kernel of the reduction to `ZMod d`. -/
private lemma apply_eq_one_of_factorsThrough {m d : ℕ} [NeZero m] {ψ : DirichletCharacter ℂ m}
    (hd : ψ.FactorsThrough d) {u : (ZMod m)ˣ} (hu : ZMod.unitsMap hd.1 u = 1) :
    ψ (u : ZMod m) = 1 := by
  have hker := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd.1).mp hd hu
  rw [MonoidHom.mem_ker] at hker
  rw [← MulChar.coe_toUnitHom ψ u, hker, Units.val_one]

private lemma unitsMap_unitsMap {r n d : ℕ} (hn : n ∣ r) (hd : d ∣ n) (x : (ZMod r)ˣ) :
    ZMod.unitsMap hd (ZMod.unitsMap hn x) = ZMod.unitsMap (dvd_trans hd hn) x := by
  have h := congrFun (congrArg DFunLike.coe (ZMod.unitsMap_comp hd hn)) x
  simpa only [MonoidHom.coe_comp, Function.comp_apply] using h

private lemma unitsMap_eq_one_of_dvd {r n D : ℕ} (hn : n ∣ r) (hD : D ∣ r) (hnd : n ∣ D)
    {x : (ZMod r)ˣ} (hx : ZMod.unitsMap hD x = 1) : ZMod.unitsMap hn x = 1 := by
  have h : ZMod.unitsMap (dvd_trans hnd hD) x = 1 := by
    rw [← unitsMap_unitsMap hD hnd, hx, map_one]
  rwa [Subsingleton.elim (dvd_trans hnd hD) hn] at h

/-- LEAF. Standard fact behind Pintz's Main Lemma, used on page 23 of P0029: a primitive character
mod `r` is the product of primitive characters mod the prime powers exactly dividing `r`. -/
theorem exists_primeComponents {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) : ∃ ψ, IsPrimeComponents χ ψ := by
  classical
  let E : ∀ p : ℕ, (ZMod r)ˣ ≃* (ZMod (compLevel r p))ˣ × (ZMod (r / compLevel r p))ˣ := fun p =>
    MulEquiv.ofBijective
      ((ZMod.unitsMap (compLevel_dvd r p)).prod (ZMod.unitsMap (div_compLevel_dvd r p)))
      (by
        haveI : NeZero (r / compLevel r p) := div_compLevel_neZero r p
        exact unitsMap_pair_bijective' r p)
  have E_apply : ∀ (p : ℕ) (x : (ZMod r)ˣ),
      E p x = (ZMod.unitsMap (compLevel_dvd r p) x,
        ZMod.unitsMap (div_compLevel_dvd r p) x) := by
    intro p x
    rw [show E p = MulEquiv.ofBijective ((ZMod.unitsMap (compLevel_dvd r p)).prod
      (ZMod.unitsMap (div_compLevel_dvd r p))) (by
        haveI : NeZero (r / compLevel r p) := div_compLevel_neZero r p
        exact unitsMap_pair_bijective' r p) from rfl]
    rw [MulEquiv.ofBijective_apply, MonoidHom.prod_apply]
  let σ : ∀ p : ℕ, (ZMod (compLevel r p))ˣ →* (ZMod r)ˣ := fun p =>
    (E p).symm.toMonoidHom.comp ((MonoidHom.id _).prod 1)
  have σ_m : ∀ (p : ℕ) (u : (ZMod (compLevel r p))ˣ),
      ZMod.unitsMap (compLevel_dvd r p) (σ p u) = u := by
    intro p u
    have h := congrArg Prod.fst (MulEquiv.apply_symm_apply (E p) (u, 1))
    rw [E_apply] at h
    exact h
  have σ_l : ∀ (p : ℕ) (u : (ZMod (compLevel r p))ˣ),
      ZMod.unitsMap (div_compLevel_dvd r p) (σ p u) = 1 := by
    intro p u
    have h := congrArg Prod.snd (MulEquiv.apply_symm_apply (E p) (u, 1))
    rw [E_apply] at h
    exact h
  let ψ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r p) := fun p =>
    MulChar.ofUnitHom (χ.toUnitHom.comp (σ p))
  have ψ_val : ∀ (p : ℕ) (u : (ZMod (compLevel r p))ˣ),
      ψ p (u : ZMod (compLevel r p)) = χ (σ p u : ZMod r) := by
    intro p u
    rw [MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  have hprod : ∀ x : (ZMod r)ˣ, χ (x : ZMod r) =
      ∏ p ∈ r.primeFactors,
        ψ p ((ZMod.unitsMap (compLevel_dvd r p) x : (ZMod (compLevel r p))ˣ) :
          ZMod (compLevel r p)) := by
    intro x
    have hx : x = ∏ p ∈ r.primeFactors, σ p (ZMod.unitsMap (compLevel_dvd r p) x) := by
      refine units_ext_of_primeFactors (fun q hq => ?_)
      rw [map_prod]
      rw [Finset.prod_eq_single q]
      · rw [σ_m]
      · intro p hp hpq
        have h1 : ZMod.unitsMap (compLevel_dvd r q)
            (σ p (ZMod.unitsMap (compLevel_dvd r p) x))
            = ZMod.unitsMap (compLevel_dvd_div_compl hp hq hpq)
              (ZMod.unitsMap (div_compLevel_dvd r p)
                (σ p (ZMod.unitsMap (compLevel_dvd r p) x))) := by
          rw [unitsMap_unitsMap]
        rw [h1, σ_l, map_one]
      · intro hq'
        exact absurd hq hq'
    conv_lhs => rw [hx]
    rw [Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl fun p _ => (ψ_val p _).symm
  refine ⟨ψ, ?_, ?_⟩
  · intro p
    by_cases hmem : p ∈ r.primeFactors
    · have key : ∀ d : ℕ, d ∣ compLevel r p → (ψ p).FactorsThrough d → compLevel r p ∣ d := by
        intro d hdvd hd
        have hdl : d * (r / compLevel r p) ∣ r := by
          have h1 : d * (r / compLevel r p) ∣ compLevel r p * (r / compLevel r p) :=
            Nat.mul_dvd_mul_right hdvd _
          rwa [compLevel_mul_compl r p] at h1
        have hfac : χ.FactorsThrough (d * (r / compLevel r p)) := by
          rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hdl]
          intro x hx
          rw [MonoidHom.mem_ker] at hx ⊢
          refine Units.ext ?_
          rw [Units.val_one, MulChar.coe_toUnitHom, hprod x]
          rw [Finset.prod_eq_single p]
          · have h2 : ZMod.unitsMap hdvd (ZMod.unitsMap (compLevel_dvd r p) x) = 1 := by
              have hcomp : ZMod.unitsMap hdvd (ZMod.unitsMap (compLevel_dvd r p) x)
                  = ZMod.unitsMap (dvd_trans hdvd (compLevel_dvd r p)) x :=
                unitsMap_unitsMap (compLevel_dvd r p) hdvd x
              rw [hcomp]
              exact unitsMap_eq_one_of_dvd (dvd_trans hdvd (compLevel_dvd r p)) hdl
                (Nat.dvd_mul_right d _) hx
            exact apply_eq_one_of_factorsThrough hd h2
          · intro q hq hqp
            have h1 : ZMod.unitsMap (compLevel_dvd r q) x = 1 := by
              rw [unitsMap_eq_one_of_dvd (compLevel_dvd r q) hdl
                ((compLevel_dvd_div_compl hmem hq hqp.symm).trans (Nat.dvd_mul_left _ _)) hx]
            rw [h1, Units.val_one, map_one]
          · intro hp'
            exact absurd hmem hp'
        have hdiv : r ∣ d * (r / compLevel r p) := by
          have hc : χ.conductor = r := hχ
          have hmem' := DirichletCharacter.conductor_dvd_of_mem_conductorSet (χ := χ) hfac
          rwa [hc] at hmem'
        haveI : NeZero (r / compLevel r p) := div_compLevel_neZero r p
        have hl : 0 < r / compLevel r p := Nat.pos_of_neZero _
        have h2 : compLevel r p * (r / compLevel r p) ∣ d * (r / compLevel r p) := by
          rwa [compLevel_mul_compl r p]
        exact (Nat.mul_dvd_mul_iff_right hl).mp h2
      have hc1 : (ψ p).conductor ∣ compLevel r p := DirichletCharacter.conductor_dvd_level (ψ p)
      have hc2 : compLevel r p ∣ (ψ p).conductor :=
        key _ hc1 (DirichletCharacter.factorsThrough_conductor (ψ p))
      rw [DirichletCharacter.isPrimitive_def]
      exact Nat.dvd_antisymm hc1 hc2
    · have hfac0 : r.factorization p = 0 := by
        by_cases hpp : p.Prime
        · exact Nat.factorization_eq_zero_of_not_dvd
            (fun hd => hmem (Nat.mem_primeFactors.mpr ⟨hpp, hd, NeZero.ne r⟩))
        · exact Nat.factorization_eq_zero_of_not_prime r hpp
      have hm1 : compLevel r p = 1 := by
        unfold compLevel
        rw [hfac0, pow_zero]
      have hone : ψ p = 1 := DirichletCharacter.level_one' (ψ p) hm1
      rw [hone]
      exact hm1 ▸ DirichletCharacter.isPrimitive_one_level_one (R := ℂ)
  · intro a ha
    have hx := hprod (ZMod.unitOfCoprime a ha)
    rw [ZMod.coe_unitOfCoprime] at hx
    refine hx.trans (Finset.prod_congr rfl fun p _ => ?_)
    have harg : ((ZMod.unitsMap (compLevel_dvd r p) (ZMod.unitOfCoprime a ha) :
        (ZMod (compLevel r p))ˣ) : ZMod (compLevel r p)) = (a : ZMod (compLevel r p)) := by
      rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
      exact ZMod.cast_natCast (R := ZMod (compLevel r p)) (compLevel_dvd r p) a
    rw [harg]


/-! ### The exponential `ee` -/

private lemma ee_zero : ee 0 = 1 := by simp [ee]

private lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma ee_nat_mul (x : ℝ) (n : ℕ) : ee (n * x) = ee x ^ n := by
  unfold ee
  rw [show ((2 : ℂ) * Real.pi * Complex.I * ((n : ℝ) * x : ℝ)) =
    (n : ℂ) * (2 * Real.pi * Complex.I * (x : ℝ)) by push_cast; ring]
  rw [Complex.exp_nat_mul]

private lemma ee_int (n : ℤ) : ee (n : ℝ) = 1 := by
  unfold ee
  rw [show ((2 : ℂ) * Real.pi * Complex.I * ((n : ℝ) : ℂ)) =
    (n : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

private lemma ee_eq_one_iff {x : ℝ} : ee x = 1 ↔ ∃ n : ℤ, x = n := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hne : ((2 : ℂ) * Real.pi * Complex.I) ≠ 0 := by
      simp [Complex.ext_iff, Real.pi_ne_zero]
    have h2 : ((2 : ℂ) * Real.pi * Complex.I) * (x : ℂ) =
        ((2 : ℂ) * Real.pi * Complex.I) * (n : ℂ) := by
      rw [hn]
      push_cast
      ring
    have := mul_left_cancel₀ hne h2
    push_cast at this ⊢
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    ring

private lemma ee_div_eq_one_iff_dvd (k : ℤ) {q : ℕ} (hq : 0 < q) :
    ee ((k : ℝ) / q) = 1 ↔ (q : ℤ) ∣ k := by
  rw [ee_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hq' : ((q : ℝ)) ≠ 0 := by exact_mod_cast hq.ne'
    rw [div_eq_iff hq'] at hn
    refine ⟨n, ?_⟩
    have h2 : (k : ℝ) = (q : ℝ) * (n : ℝ) := by rw [mul_comm]; exact hn
    exact_mod_cast h2
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    push_cast
    field_simp

/-! ### Orthogonality of the exponential over a full residue system -/

private lemma sum_ee_mul_div (k : ℤ) {q : ℕ} (hq : 0 < q) :
    ∑ c ∈ Finset.range q, ee ((k : ℝ) * (c : ℝ) / q) =
      if (q : ℤ) ∣ k then (q : ℂ) else 0 := by
  split_ifs with hdvd
  · obtain ⟨t, rfl⟩ := hdvd
    have h1 : ∀ c ∈ Finset.range q, ee ((((q : ℤ) * t : ℤ) : ℝ) * (c : ℝ) / q) = 1 := by
      intro c _
      have : (((q : ℤ) * t : ℤ) : ℝ) * (c : ℝ) / q = ((t * c : ℤ) : ℝ) := by
        have hq' : ((q : ℝ)) ≠ 0 := by exact_mod_cast hq.ne'
        push_cast
        field_simp
      rw [this]
      exact ee_int _
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have hne : ee ((k : ℝ) / q) ≠ 1 := fun h => hdvd ((ee_div_eq_one_iff_dvd k hq).mp h)
    have hpow : ∀ c ∈ Finset.range q, ee ((k : ℝ) * (c : ℝ) / q) = ee ((k : ℝ) / q) ^ c := by
      intro c _
      rw [← ee_nat_mul]
      congr 1
      have hq' : ((q : ℝ)) ≠ 0 := by exact_mod_cast hq.ne'
      push_cast
      field_simp
    rw [Finset.sum_congr rfl hpow]
    have hqpow : ee ((k : ℝ) / q) ^ q = 1 := by
      rw [← ee_nat_mul]
      have : ((q : ℝ)) * ((k : ℝ) / q) = ((k : ℝ)) := by
        have hq' : ((q : ℝ)) ≠ 0 := by exact_mod_cast hq.ne'
        field_simp
      rw [this]
      exact ee_int k
    have hg := geom_sum_eq hne q
    rw [hqpow, sub_self, zero_div] at hg
    exact hg

/-! ### Möbius inversion over the divisors -/

private lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← h]
  simp [ArithmeticFunction.intCoe_apply]

/-! ### The divisor formula for the Ramanujan sum -/

private lemma ramanujan_eq_divisor_sum {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ramanujan q n = ∑ d ∈ (Nat.gcd q n.natAbs).divisors,
      (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) := by
  unfold ramanujan
  rw [Nat.gcd_comm q n.natAbs]
  rw [Finset.sum_filter]
  have step1 : ∀ r ∈ Finset.range q,
      (if Nat.Coprime r q then ee ((r : ℝ) * (n : ℝ) / q) else 0) =
      ∑ d ∈ (Nat.gcd r q).divisors, (((ArithmeticFunction.moebius d : ℤ) : ℂ) * ee ((r : ℝ) * (n : ℝ) / q)) := by
    intro r _
    rw [← Finset.sum_mul, sum_moebius_divisors]
    simp only [Nat.Coprime]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl step1]
  rw [Finset.sum_comm' (t' := q.divisors)
    (s' := fun d => (Finset.range q).filter (fun r => d ∣ r))]
  · have step2 : ∀ d ∈ q.divisors, ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r),
        (((ArithmeticFunction.moebius d : ℤ) : ℂ) * ee ((r : ℝ) * (n : ℝ) / q)) =
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (if (((q / d : ℕ) : ℤ)) ∣ n then ((q / d : ℕ) : ℂ) else 0) := by
      intro d hd
      have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdq) hd0
      rw [← Finset.mul_sum, ← sum_ee_mul_div n hqd]
      congr 1
      refine Finset.sum_nbij' (fun r => r / d) (fun s => d * s) ?_ ?_ ?_ ?_ ?_
      · intro r hr
        rw [Finset.mem_filter, Finset.mem_range] at hr
        rw [Finset.mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hdq hr.1
      · intro s hs
        rw [Finset.mem_range] at hs
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, dvd_mul_right d s⟩
        have := Nat.mul_lt_mul_of_pos_left hs hd0
        rwa [Nat.mul_div_cancel' hdq] at this
      · intro r hr
        rw [Finset.mem_filter] at hr
        exact Nat.mul_div_cancel' hr.2
      · intro s _; exact Nat.mul_div_cancel_left s hd0
      · intro r hr
        rw [Finset.mem_filter] at hr
        obtain ⟨s, rfl⟩ := hr.2
        rw [Nat.mul_div_cancel_left s hd0, Nat.cast_div hdq (by exact_mod_cast hd0.ne')]
        congr 1
        push_cast
        field_simp
    rw [Finset.sum_congr rfl step2]
    rw [← Finset.sum_filter_add_sum_filter_not q.divisors (fun d => (((q / d : ℕ) : ℤ)) ∣ n)]
    rw [Finset.sum_eq_zero (s := q.divisors.filter (fun d => ¬ (((q / d : ℕ) : ℤ)) ∣ n))
      (fun d hd => by rw [Finset.mem_filter] at hd; rw [if_neg hd.2, mul_zero]), add_zero]
    refine Finset.sum_nbij' (fun d => q / d) (fun e => q / e) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      rw [Nat.mem_divisors]
      refine ⟨Nat.dvd_gcd (Int.natCast_dvd.mp hd.2) (Nat.div_dvd_of_dvd hd.1.1), ?_⟩
      exact (Nat.gcd_pos_of_pos_right n.natAbs (by omega)).ne'
    · intro e he
      rw [Nat.mem_divisors] at he
      have heq : e ∣ q := (Nat.dvd_gcd_iff.1 he.1).2
      have hen : e ∣ n.natAbs := (Nat.dvd_gcd_iff.1 he.1).1
      have he0 : 0 < e := Nat.pos_of_dvd_of_pos heq (by omega)
      rw [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.div_dvd_of_dvd heq, by omega⟩, ?_⟩
      rw [Nat.div_div_self heq (by omega)]; exact Int.natCast_dvd.mpr hen
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 (by omega)
    · intro e he
      rw [Nat.mem_divisors] at he
      exact Nat.div_div_self (Nat.dvd_gcd_iff.1 he.1).2 (by omega)
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      rw [if_pos hd.2, Nat.div_div_self hd.1.1 (by omega)]
      ring
  · intro r d
    simp only [Finset.mem_range, Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff, ne_eq,
      Nat.gcd_eq_zero_iff]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨⟨h1, h2⟩, h3, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, by omega⟩

private lemma ramanujan_re_eq_divisor_sum {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    (ramanujan q n).re = ∑ d ∈ (Nat.gcd q n.natAbs).divisors,
      (d : ℝ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℝ) := by
  rw [ramanujan_eq_divisor_sum hq n]
  have hterm : ∀ d : ℕ, ((d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)) =
      (((d : ℤ) * ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) := by
    intro d; push_cast; ring
  simp only [hterm]
  rw [← Int.cast_sum]
  simp

private lemma ramanujan_one (n : ℤ) : ramanujan 1 n = 1 := by
  simp [ramanujan, ee_zero]

private lemma divisors_filter_dvd_gcd {q N : ℕ} (hq : 1 ≤ q) :
    q.divisors.filter (fun d => d ∣ N) = (Nat.gcd q N).divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h3⟩, (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left q N) (by omega)).ne'⟩
  · rintro ⟨⟨h1, h2⟩, _⟩
    exact ⟨⟨h1, by omega⟩, h2⟩

/-- The real part of the Ramanujan sum is multiplicative in the modulus. -/
private lemma ramanujan_re_mul {m n : ℕ} (N : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcop : Nat.Coprime m n) :
    (ramanujan (m * n) (N : ℤ)).re =
      (ramanujan m (N : ℤ)).re * (ramanujan n (N : ℤ)).re := by
  have hmn : 1 ≤ m * n := by have := Nat.mul_le_mul hm hn; simpa using this
  let G : ArithmeticFunction ℝ := ⟨fun d => if d ∣ N then (d : ℝ) else 0, by simp⟩
  have hGapp : ∀ d : ℕ, G d = if d ∣ N then (d : ℝ) else 0 := fun d => rfl
  have hGmult : G.IsMultiplicative := by
    refine ⟨by simp [hGapp], fun {a b} hab => ?_⟩
    simp only [hGapp]
    by_cases ha : a ∣ N
    · by_cases hb : b ∣ N
      · rw [if_pos (hab.mul_dvd_of_dvd_of_dvd ha hb), if_pos ha, if_pos hb]
        push_cast
        ring
      · rw [if_neg (fun h => hb (dvd_trans (dvd_mul_left b a) h)), if_neg hb, mul_zero]
    · rw [if_neg (fun h => ha (dvd_trans (dvd_mul_right a b) h)), if_neg ha, zero_mul]
  have hF : ∀ q : ℕ, 1 ≤ q →
      (ramanujan q (N : ℤ)).re = (G * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) q := by
    intro q hq
    rw [ramanujan_re_eq_divisor_sum hq (N : ℤ), Int.natAbs_natCast]
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal
        (fun a b => G a * (ArithmeticFunction.moebius : ArithmeticFunction ℝ) b)]
    simp only [hGapp, ArithmeticFunction.intCoe_apply, ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    rw [divisors_filter_dvd_gcd hq]
  have key : (G * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)).IsMultiplicative :=
    hGmult.mul ArithmeticFunction.isMultiplicative_moebius.intCast
  rw [hF (m * n) hmn, hF m hm, hF n hn]
  exact key.map_mul_of_coprime hcop

private lemma card_ramanujan_re_le (N : ℕ) (hN : 1 ≤ N) (q : ℕ) :
    |(ramanujan q (N : ℤ)).re| ≤ ∑ d ∈ N.divisors, (d : ℝ) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp [ramanujan]
    positivity
  · rw [ramanujan_re_eq_divisor_sum hq, Int.natAbs_natCast]
    have h1 : |∑ d ∈ (Nat.gcd q N).divisors,
        (d : ℝ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℝ)| ≤
        ∑ d ∈ (Nat.gcd q N).divisors, (d : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
      exact mul_le_of_le_one_right (Nat.cast_nonneg d)
        (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q / d))
    refine h1.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun _ _ _ => Nat.cast_nonneg _))
    exact Nat.divisors_subset_of_dvd (by omega) (Nat.gcd_dvd_right q N)

private lemma summable_eulerFactorSing (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun q : ℕ => ‖(((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
      (Nat.totient q : ℝ) ^ 2) * (ramanujan q (N : ℤ)).re‖) := by
  classical
  set B : ℝ := ∑ d ∈ N.divisors, (d : ℝ) with hBdef
  have hB : 0 ≤ B := Finset.sum_nonneg fun d _ => Nat.cast_nonneg d
  have hs : Summable (fun q : ℕ => B * (7 * (q : ℝ) ^ (-(7 : ℝ) / 4))) :=
    ((Real.summable_nat_rpow.mpr (by norm_num : (-(7 : ℝ) / 4) < -1)).mul_left 7).mul_left B
  refine Summable.of_norm_bounded hs (fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp [ArithmeticFunction.moebius, hB]
  · have hphi : (0 : ℝ) < (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq
    have hmu : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    have hc : |(ramanujan q (N : ℤ)).re| ≤ B := by
      rw [hBdef]; exact card_ramanujan_re_le N hN q
    have hsq : (0 : ℝ) < (Nat.totient q : ℝ) ^ 2 := pow_pos hphi 2
    have hfac : ‖(((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        (Nat.totient q : ℝ) ^ 2)‖ ≤ 1 / (Nat.totient q : ℝ) ^ 2 := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hsq, abs_pow]
      refine div_le_div_of_nonneg_right ?_ hsq.le
      nlinarith [abs_nonneg (((ArithmeticFunction.moebius q : ℤ) : ℝ))]
    have hinv : 1 / (Nat.totient q : ℝ) ^ 2 ≤ 7 * (q : ℝ) ^ (-(7 : ℝ) / 4) :=
      LeanLab.Zinoviev1997.inv_totient_sq_seven q hq
    calc ‖(((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2) *
          (ramanujan q (N : ℤ)).re‖
        ≤ ‖(((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            (Nat.totient q : ℝ) ^ 2)‖ * ‖(ramanujan q (N : ℤ)).re‖ := norm_mul_le _ _
      _ = ‖(((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            (Nat.totient q : ℝ) ^ 2)‖ * |(ramanujan q (N : ℤ)).re| := by
          rw [Real.norm_eq_abs (r := (ramanujan q (N : ℤ)).re)]
      _ ≤ (1 / (Nat.totient q : ℝ) ^ 2) * B :=
          mul_le_mul hfac hc (abs_nonneg _) (by positivity)
      _ ≤ (7 * (q : ℝ) ^ (-(7 : ℝ) / 4)) * B :=
          mul_le_mul_of_nonneg_right hinv hB
      _ = B * (7 * (q : ℝ) ^ (-(7 : ℝ) / 4)) := by ring

/-- LEAF page 23. The ordinary singular series converges to the product of its Euler factors.
`1 ≤ N` is the range of (6.5) in `Bound65`; at `N = 0` the product diverges, see
`Audit1610.euler_sing_eq_old_false`. -/
theorem euler_sing_eq (N : ℕ) (hN : 1 ≤ N) :
    Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorSing N p) atTop (𝓝 (singular N)) := by
  have hf1 : (fun q : ℕ => (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
      (Nat.totient q : ℝ) ^ 2) * (ramanujan q (N : ℤ)).re) 1 = 1 := by
    simp [ArithmeticFunction.moebius_apply_one, Nat.totient_one, ramanujan_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      (fun q : ℕ => (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        (Nat.totient q : ℝ) ^ 2) * (ramanujan q (N : ℤ)).re) (m * n) =
      (fun q : ℕ => (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        (Nat.totient q : ℝ) ^ 2) * (ramanujan q (N : ℤ)).re) m *
      (fun q : ℕ => (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        (Nat.totient q : ℝ) ^ 2) * (ramanujan q (N : ℤ)).re) n := by
    intro m n hcop
    simp only
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hn : n = 1 := by rwa [Nat.coprime_zero_left] at hcop
      subst hn
      simp [ArithmeticFunction.moebius]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hm1 : m = 1 := by rwa [Nat.coprime_zero_right] at hcop
      subst hm1
      simp [ArithmeticFunction.moebius]
    rw [ramanujan_re_mul N hm hn hcop,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop, Nat.totient_mul hcop]
    push_cast
    have h1 : (Nat.totient m : ℝ) ≠ 0 := by positivity
    have h2 : (Nat.totient n : ℝ) ≠ 0 := by positivity
    field_simp
  have hf0 : (fun q : ℕ => (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
      (Nat.totient q : ℝ) ^ 2) * (ramanujan q (N : ℤ)).re) 0 = 0 := by
    simp [ArithmeticFunction.moebius]
  have hsum := summable_eulerFactorSing N hN
  have h := EulerProduct.eulerProduct (R := ℝ) hf1 (@hmul) hsum hf0
  simpa only [singular, eulerFactorSing, Nat.primesBelow] using h


/-- LEAF page 23. The generalized singular series of primitive `χ₁, χ₂` converges to the product
of the Euler factors of their prime power components. `1 ≤ N` alone does not repair the old form:
`eulerFactorGen χ₁ χ₂` vanishes at every prime `p` unless `r₁, r₂` are powers of `p`, see
`Audit1610.euler_gen_eq_old_forces_zero`. -/
theorem euler_gen_eq {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : IsPrimeComponents χ₁ ψ₁) (h₂ : IsPrimeComponents χ₂ ψ₂) (N : ℤ) (hN : 1 ≤ N) :
    Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorGen (ψ₁ p) (ψ₂ p) N p)
      atTop (𝓝 (genSing χ₁ χ₂ N)) := by
  sorry

/-! ### Leaf 4: `local_bound` — the lifted Gauss sums vanish -/

private lemma ee_val_eq_stdAddChar {q : ℕ} [NeZero q] (m : ZMod q) :
    ee ((m.val : ℝ) / q) = ZMod.stdAddChar m := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  simp only [ee]
  congr 1
  push_cast
  ring

private lemma tauConj_eq_sum_stdAddChar {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    tauConj χ = ∑ m : ZMod q, starRingEnd ℂ (χ m) * ZMod.stdAddChar m := by
  simp only [tauConj, ee_val_eq_stdAddChar]

/-- The Gauss sum of a character lifted from level `p ^ a` to `p ^ k`, `a < k` and `k ≥ 2`,
vanishes: the shift `m ↦ m + p ^ (k - 1)` is Ψ-invariant but multiplies `e(m / p ^ k)` by
`e(1/p) ≠ 1`. (`k = 1` is genuinely excluded: the trivial character mod `1` lifted to mod `p` has
Gauss sum `-1`.) -/
private theorem tauConj_changeLevel_pow_eq_zero {p a k : ℕ} (hp : p.Prime) (hak : a < k)
    (hk2 : 2 ≤ k) [NeZero (p ^ k)] (χ : DirichletCharacter ℂ (p ^ a)) :
    tauConj (DirichletCharacter.changeLevel (Nat.pow_dvd_pow p hak.le) χ) = 0 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  set Ψ := DirichletCharacter.changeLevel (Nat.pow_dvd_pow p hak.le) χ with hΨ
  set d : ZMod (p ^ k) := ((p ^ (k - 1) : ℕ) : ZMod (p ^ k)) with hd
  have hdvd : p ^ a ∣ p ^ (k - 1) := Nat.pow_dvd_pow p (by omega)
  have hd0 : d ≠ 0 := by
    rw [hd, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have h1 : p ^ k ≤ p ^ (k - 1) := Nat.le_of_dvd (pow_pos hp.pos (k - 1)) h
    have h2 : k ≤ k - 1 := (Nat.pow_le_pow_iff_right hp.two_le).mp h1
    omega
  have hcastd : ZMod.castHom (Nat.pow_dvd_pow p hak.le) (ZMod (p ^ a)) d = 0 := by
    rw [hd, map_natCast, ZMod.natCast_eq_zero_iff]
    exact hdvd
  have hnil : IsNilpotent d := by
    refine ⟨2, ?_⟩
    rw [hd, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff, ← pow_mul]
    exact pow_dvd_pow _ (by omega)
  have hunit : ∀ m : ZMod (p ^ k), IsUnit (m + d) ↔ IsUnit m := by
    intro m
    constructor
    · intro h
      have := hnil.neg.isUnit_add_left_of_commute h (Commute.all _ _)
      simpa using this
    · intro h
      exact hnil.isUnit_add_left_of_commute h (Commute.all _ _)
  have hΨd : ∀ m : ZMod (p ^ k), Ψ (m + d) = Ψ m := by
    intro m
    by_cases h : IsUnit m
    · obtain ⟨u, rfl⟩ := h
      obtain ⟨v, hv⟩ := (hunit (u : ZMod (p ^ k))).mpr u.isUnit
      rw [← hv, hΨ,
        ← MulChar.coe_toUnitHom (DirichletCharacter.changeLevel (Nat.pow_dvd_pow p hak.le) χ) v,
        ← MulChar.coe_toUnitHom (DirichletCharacter.changeLevel (Nat.pow_dvd_pow p hak.le) χ) u,
        DirichletCharacter.changeLevel_toUnitHom]
      congr 1
      simp only [MonoidHom.comp_apply]
      congr 1
      refine Units.ext ?_
      rw [ZMod.unitsMap_val, ZMod.unitsMap_val]
      rw [show (↑v : ZMod (p ^ k)) = (↑u : ZMod (p ^ k)) + d from hv]
      change ZMod.castHom (Nat.pow_dvd_pow p hak.le) (ZMod (p ^ a)) ((↑u : ZMod (p ^ k)) + d)
        = ZMod.castHom (Nat.pow_dvd_pow p hak.le) (ZMod (p ^ a)) (↑u : ZMod (p ^ k))
      rw [map_add, hcastd, add_zero]
    · rw [MulChar.map_nonunit _ h, MulChar.map_nonunit _ (fun h' => h ((hunit m).mp h'))]
  have hs : ZMod.stdAddChar (N := p ^ k) d ≠ 1 := by
    intro h
    have h1 : ZMod.stdAddChar (N := p ^ k) d = ZMod.stdAddChar (N := p ^ k) 0 := by
      rw [h, AddChar.map_zero_eq_one]
    exact hd0 (ZMod.injective_stdAddChar h1)
  have hshift : tauConj Ψ = tauConj Ψ * ZMod.stdAddChar d := by
    rw [tauConj_eq_sum_stdAddChar, Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight d)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Equiv.coe_addRight, hΨd m, AddChar.map_add_eq_mul]
    ring
  have hzero : tauConj Ψ * (1 - ZMod.stdAddChar d) = 0 := by
    rw [mul_sub, mul_one, ← hshift, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hs

/-- The Ramanujan sum at a prime: `-1` unless `p ∣ N`, where it is `p - 1`. -/
private lemma ramanujan_prime_val {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (ramanujan p (N : ℤ)).re = if p ∣ N then (p : ℝ) - 1 else -1 := by
  rw [ramanujan_re_eq_divisor_sum hp.one_le, Int.natAbs_natCast]
  by_cases h : p ∣ N
  · rw [if_pos h, Nat.gcd_eq_left h, hp.divisors, Finset.sum_pair hp.one_lt.ne,
      Nat.div_one, Nat.div_self hp.pos, ArithmeticFunction.moebius_apply_prime hp,
      ArithmeticFunction.moebius_apply_one]
    push_cast
    ring
  · have hc : Nat.Coprime p N := hp.coprime_iff_not_dvd.mpr h
    rw [if_neg h, Nat.coprime_iff_gcd_eq_one.mp hc, Nat.divisors_one, Finset.sum_singleton,
      Nat.div_one, ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring

/-- The ordinary Euler factor at a prime is `1 + c_p(N) / φ(p)²`. -/
private lemma eulerFactorSing_prime_val {p : ℕ} (hp : p.Prime) (N : ℕ) :
    eulerFactorSing N p = 1 + (ramanujan p (N : ℤ)).re / (Nat.totient p : ℝ) ^ 2 := by
  have hne : ∀ k : ℕ, p ^ k ≠ 0 := fun k => pow_ne_zero k hp.ne_zero
  unfold eulerFactorSing
  rw [tsum_eq_sum (s := {0, 1}) ?_, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  · simp only [pow_zero, pow_one, Nat.totient_one, ArithmeticFunction.moebius_apply_one,
      ArithmeticFunction.moebius_apply_prime hp]
    rw [ramanujan_one]
    simp only [Complex.one_re]
    ring
  · intro k hk
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      omega
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp

private lemma eulerFactorSing_nonneg {p : ℕ} (hp : p.Prime) (N : ℕ) :
    0 ≤ eulerFactorSing N p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hφ1 : (1 : ℝ) ≤ (Nat.totient p : ℝ) := by
    rw [Nat.totient_prime hp]
    have h2 : 2 ≤ p := hp.two_le
    have h : (1 : ℕ) ≤ p - 1 := by omega
    exact_mod_cast h
  have hφ : (1 : ℝ) ≤ (Nat.totient p : ℝ) ^ 2 := by nlinarith
  have hφ0 : (0 : ℝ) < (Nat.totient p : ℝ) ^ 2 := by linarith
  rw [eulerFactorSing_prime_val hp N, ramanujan_prime_val hp N]
  split_ifs with h
  · have h1 : (0 : ℝ) ≤ ((p : ℝ) - 1) / (Nat.totient p : ℝ) ^ 2 :=
      div_nonneg (by linarith) hφ0.le
    linarith
  · have h2 : (1 : ℝ) / (Nat.totient p : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one hφ0]
      exact hφ
    have h3 : (1 : ℝ) + (-1) / (Nat.totient p : ℝ) ^ 2
        = 1 - 1 / (Nat.totient p : ℝ) ^ 2 := by
      rw [neg_div, sub_eq_add_neg]
    rw [h3]
    linarith

/-! ### Leaf 4: the Gauss sum of a primitive character has modulus `√q` -/

private lemma tauConj_eq_gaussSum_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    tauConj χ = gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) := by
  rw [gaussSum, tauConj]
  exact Finset.sum_congr rfl fun m _ => by
    rw [show (starRingEnd ℂ) (χ m) = star (χ m) from rfl, MulChar.star_apply',
      ee_val_eq_stdAddChar]

private lemma gaussSum_shift_apply {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift n)
      = ∑ a : ZMod q, χ a * ZMod.stdAddChar (N := q) (n * a) := by
  rw [gaussSum]
  exact Finset.sum_congr rfl fun a _ => by rw [AddChar.mulShift_apply]

private lemma star_stdAddChar {q : ℕ} [NeZero q] (m : ZMod q) :
    (starRingEnd ℂ) (ZMod.stdAddChar (N := q) m) = ZMod.stdAddChar (N := q) (-m) := by
  have h1 : ZMod.stdAddChar (N := q) (-m) * ZMod.stdAddChar (N := q) m = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h3 : ‖ZMod.stdAddChar (N := q) m‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  calc (starRingEnd ℂ) (ZMod.stdAddChar (N := q) m)
      = (ZMod.stdAddChar (N := q) m)⁻¹ := (Complex.inv_eq_conj h3).symm
    _ = ZMod.stdAddChar (N := q) (-m) := inv_eq_of_mul_eq_one_left h1

private lemma sum_stdAddChar_mul (q : ℕ) [NeZero q] (k : ZMod q) :
    ∑ n : ZMod q, ZMod.stdAddChar (N := q) (n * k) = if k = 0 then (q : ℂ) else 0 := by
  classical
  have hfun : (fun n : ZMod q => ZMod.stdAddChar (N := q) (n * k))
      = (ZMod.stdAddChar (N := q)).mulShift k := by
    funext n
    rw [AddChar.mulShift_apply, mul_comm]
  have hiff : ((ZMod.stdAddChar (N := q)).mulShift k = 0) ↔ k = 0 := by
    constructor
    · intro h
      have h1 : (ZMod.stdAddChar (N := q)).mulShift k 1 = (0 : AddChar (ZMod q) ℂ) 1 := by rw [h]
      rw [AddChar.mulShift_apply, mul_one, AddChar.zero_apply] at h1
      exact ZMod.injective_stdAddChar (by rw [h1, AddChar.map_zero_eq_one])
    · rintro rfl
      ext x
      rw [AddChar.mulShift_apply, zero_mul, AddChar.map_zero_eq_one, AddChar.zero_apply]
  rw [hfun, AddChar.sum_eq_ite, ZMod.card]
  by_cases h : k = 0
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]

/-- A character takes unit-modulus values on units. -/
private lemma norm_chi_apply_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (u : (ZMod q)ˣ) : ‖χ (u : ZMod q)‖ = 1 := by
  have hmem : χ.toUnitHom u ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) ℂ := by
    rw [MulChar.toUnitHom_eq]
    exact MulChar.apply_mem_rootsOfUnity u
  rw [← MulChar.coe_toUnitHom χ u]
  exact Complex.norm_eq_one_of_mem_rootsOfUnity hmem

private lemma card_isUnit (q : ℕ) [NeZero q] :
    (Finset.univ.filter (fun a : ZMod q => IsUnit a)).card = Nat.totient q := by
  classical
  rw [← ZMod.card_units_eq_totient, ← Fintype.card_subtype (fun a : ZMod q => IsUnit a)]
  exact Fintype.card_congr (Equiv.mk (fun x => x.2.unit) (fun u => ⟨u, u.isUnit⟩)
    (fun x => by ext; exact IsUnit.unit_spec x.2)
    (fun u => by ext; exact IsUnit.unit_spec u.isUnit))

/-- For a character, `χ a * conj (χ a)` is `1` on units and `0` on non-units. -/
private lemma chi_mul_star_chi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    χ a * (starRingEnd ℂ) (χ a) = if IsUnit a then 1 else 0 := by
  by_cases ha : IsUnit a
  · rw [if_pos ha]
    obtain ⟨u, rfl⟩ := ha
    have h1 := Complex.mul_conj (χ (u : ZMod q))
    rw [Complex.normSq_eq_norm_sq, norm_chi_apply_unit χ u] at h1
    rw [h1]
    norm_num
  · rw [if_neg ha, MulChar.map_nonunit χ ha]
    simp

private lemma sum_chi_mul_star_chi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, χ a * (starRingEnd ℂ) (χ a) = (Nat.totient q : ℂ) := by
  classical
  rw [Finset.sum_congr rfl fun a _ => chi_mul_star_chi χ a]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, card_isUnit]

/-- Parseval for the shifted Gauss sums: `∑_n ‖gaussSum χ (e · n)‖² = q · φ(q)`. -/
private lemma sum_gaussSum_shift_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ n : ZMod q, ‖gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift n)‖ ^ 2
      = (q : ℝ) * (Nat.totient q : ℝ) := by
  classical
  have hterm : ∀ n : ZMod q,
      gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift n)
        * (starRingEnd ℂ) (gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift n))
      = ∑ a : ZMod q, ∑ b : ZMod q,
          (χ a * (starRingEnd ℂ) (χ b)) * ZMod.stdAddChar (N := q) (n * (a - b)) := by
    intro n
    rw [gaussSum_shift_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hstar : (starRingEnd ℂ) (χ b * ZMod.stdAddChar (N := q) (n * b))
        = (starRingEnd ℂ) (χ b) * (starRingEnd ℂ) (ZMod.stdAddChar (N := q) (n * b)) :=
      map_mul _ _ _
    rw [hstar, star_stdAddChar]
    calc (χ a * ZMod.stdAddChar (N := q) (n * a))
          * ((starRingEnd ℂ) (χ b) * ZMod.stdAddChar (N := q) (-(n * b)))
        = (χ a * (starRingEnd ℂ) (χ b))
            * (ZMod.stdAddChar (N := q) (n * a) * ZMod.stdAddChar (N := q) (-(n * b))) := by
          ring
      _ = (χ a * (starRingEnd ℂ) (χ b)) * ZMod.stdAddChar (N := q) (n * a + -(n * b)) := by
          rw [← AddChar.map_add_eq_mul]
      _ = (χ a * (starRingEnd ℂ) (χ b)) * ZMod.stdAddChar (N := q) (n * (a - b)) := by
          rw [show n * a + -(n * b) = n * (a - b) by ring]
  have hcalc : ∑ n : ZMod q, gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift n)
        * (starRingEnd ℂ) (gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift n))
      = (q : ℂ) * (Nat.totient q : ℂ) := by
    rw [Finset.sum_congr rfl fun n _ => hterm n]
    rw [Finset.sum_comm]
    have hinner : ∀ a : ZMod q, ∑ n : ZMod q, ∑ b : ZMod q,
        (χ a * (starRingEnd ℂ) (χ b)) * ZMod.stdAddChar (N := q) (n * (a - b))
        = χ a * (starRingEnd ℂ) (χ a) * (q : ℂ) := by
      intro a
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single a]
      · rw [sub_self, ← Finset.mul_sum, sum_stdAddChar_mul, if_pos rfl]
      · intro b _ hba
        rw [← Finset.mul_sum, sum_stdAddChar_mul,
          if_neg (sub_ne_zero.mpr (Ne.symm hba)), mul_zero]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    rw [Finset.sum_congr rfl fun a _ => hinner a]
    rw [← Finset.sum_mul, sum_chi_mul_star_chi, mul_comm]
  have hreal : ∑ n : ZMod q, ‖gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift n)‖ ^ 2
      = (∑ n : ZMod q, gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift n)
          * (starRingEnd ℂ) (gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift n))).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [hreal, hcalc]
  simp

/-- The Gauss sum of a primitive character mod `q` has modulus `√q`. -/
private theorem norm_tauConj_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) : ‖tauConj χ‖ ^ 2 = (q : ℝ) := by
  classical
  have hχ' : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv,
      ← DirichletCharacter.isPrimitive_def]
    exact hχ
  have hshift : ∀ n : ZMod q,
      gaussSum χ⁻¹ ((ZMod.stdAddChar (N := q)).mulShift n)
        = χ n * gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) := by
    intro n
    rw [gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := q)) hχ' n, inv_inv]
  have hnorm2 : ∀ n : ZMod q,
      ‖gaussSum χ⁻¹ ((ZMod.stdAddChar (N := q)).mulShift n)‖ ^ 2
        = if IsUnit n then ‖gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))‖ ^ 2 else 0 := by
    intro n
    rw [hshift n, norm_mul]
    by_cases hn : IsUnit n
    · rw [if_pos hn]
      obtain ⟨u, rfl⟩ := hn
      rw [norm_chi_apply_unit χ u, one_mul]
    · rw [if_neg hn, MulChar.map_nonunit χ hn, norm_zero, zero_mul]
      norm_num
  have hunits : ∑ n : ZMod q,
      (if IsUnit n then ‖gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))‖ ^ 2 else 0)
      = (Nat.totient q : ℝ) * ‖gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))‖ ^ 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_isUnit]
  have hP := sum_gaussSum_shift_sq χ⁻¹
  rw [Finset.sum_congr rfl fun n _ => hnorm2 n, hunits] at hP
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    have h : 0 < Nat.totient q := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast h
  have hG : ‖gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))‖ ^ 2 = (q : ℝ) := by
    rw [mul_comm (q : ℝ) (Nat.totient q : ℝ)] at hP
    exact mul_left_cancel₀ hφpos.ne' hP
  rw [tauConj_eq_gaussSum_inv]
  exact hG

/-! ### Leaf 4: the twisted Ramanujan sum at a unit argument -/

private lemma ee_one : ee (1 : ℝ) = 1 := by
  simpa using ee_int (1 : ℤ)

private lemma ee_val_neg {q : ℕ} [NeZero q] (m : ZMod q) :
    ee (((-m).val : ℝ) / q) = ee (-((m.val : ℝ) / q)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hq' : 0 < q := NeZero.pos q
  have hv1 := ZMod.val_lt (-m)
  have hv2 := ZMod.val_lt m
  have hzero : (((-m).val + m.val : ℕ) : ZMod q) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, add_comm, add_neg_cancel]
  have hdvd : q ∣ ((-m).val + m.val) := by
    rwa [ZMod.natCast_eq_zero_iff] at hzero
  have hlt : (-m).val + m.val < 2 * q := by omega
  rcases Nat.eq_zero_or_pos ((-m).val + m.val) with h0 | hpos
  · have h1 : (-m).val = 0 := by omega
    have h2 : m.val = 0 := by omega
    rw [h1, h2]
    simp [ee_zero]
  · obtain ⟨k, hk⟩ := hdvd
    have hk1 : k = 1 := by
      have h1 : k < 2 := by
        have h2 : q * k < q * 2 := by rw [← hk]; simpa [mul_comm] using hlt
        exact (Nat.mul_lt_mul_left hq').mp h2
      have h2 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · rw [hk0, Nat.mul_zero] at hk
          omega
        · exact hkpos
      omega
    have hsum_eq : (-m).val + m.val = q := by
      rw [hk, hk1, Nat.mul_one]
    have hval : (-m).val = q - m.val := by omega
    have hcast : ((-m).val : ℝ) = (q : ℝ) - (m.val : ℝ) := by
      rw [hval, Nat.cast_sub (le_of_lt hv2)]
    rw [hcast, show ((q : ℝ) - (m.val : ℝ)) / q = 1 + (-((m.val : ℝ) / q)) by
      field_simp
      ring]
    rw [ee_add, ee_one, one_mul]

/-- `ee` only depends on the residue class. -/
private lemma ee_eq_of_modEq {q : ℕ} [NeZero q] {x y : ℕ} (h : x ≡ y [MOD q]) :
    ee ((x : ℝ) / q) = ee ((y : ℝ) / q) := by
  obtain ⟨k, hk⟩ := h.dvd
  have hq : ((q : ℝ)) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hxy : ((y : ℝ) / q) = ((x : ℝ) / q) + (k : ℝ) := by
    have h1 : (y : ℝ) - (x : ℝ) = (k : ℝ) * (q : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hk
      push_cast at this
      linarith
    field_simp
    linarith
  rw [hxy, ee_add, ee_int, mul_one]

/-- Reindexing `a ↦ a · N⁻¹` in the twisted Ramanujan sum. -/
private lemma cChi_eq_mul_sum {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (N : ℕ)
    (u : (ZMod q)ˣ) (hu : ((N : ℤ) : ZMod q) = (u : ZMod q)) :
    cChi ψ (N : ℤ) = ψ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) *
      ∑ b : ZMod q, ψ b * ee ((b.val : ℝ) / q) := by
  classical
  have hu' : (N : ZMod q) = (u : ZMod q) := by simpa using hu
  have huN : ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (N : ZMod q) = 1 := by
    rw [hu', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [cChi]
  rw [← Equiv.sum_comp (Units.mulRight u⁻¹)
    (fun a : ZMod q => ψ a * ee ((a.val : ℝ) * ((N : ℤ) : ℝ) / q))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Units.mulRight_apply]
  beta_reduce
  have hmul : ψ (b * ((u⁻¹ : (ZMod q)ˣ) : ZMod q))
      = ψ b * ψ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := ψ.map_mul' b _
  have hexp : ee (((b * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)).val : ℝ) * ((N : ℤ) : ℝ) / q)
      = ee ((b.val : ℝ) / q) := by
    have hL : (((b * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)).val : ℝ) * ((N : ℤ) : ℝ) / q)
        = ((((b * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)).val * N : ℕ)) : ℝ) / q := by
      push_cast
      ring
    rw [hL]
    refine ee_eq_of_modEq (q := q) ?_
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_assoc, huN, mul_one]
  rw [hmul, hexp]
  ring

/-- `star (ee x) = ee (-x)`. -/
private lemma star_ee {q : ℕ} [NeZero q] (m : ZMod q) :
    (starRingEnd ℂ) (ee ((m.val : ℝ) / q)) = ee (-((m.val : ℝ) / q)) := by
  conv_lhs => rw [ee_val_eq_stdAddChar m]
  rw [star_stdAddChar, ← ee_val_eq_stdAddChar (-m), ee_val_neg m]

private lemma starRingEnd_starRingEnd (z : ℂ) : (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := by
  have h : ∀ w : ℂ, (starRingEnd ℂ) w = star w := fun w => rfl
  rw [h, h, star_star]

private lemma norm_chi_apply_of_isUnit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a : ZMod q} (ha : IsUnit a) : ‖χ a‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  exact norm_chi_apply_unit χ u

/-- At a unit argument the twisted Ramanujan sum has the same modulus as the Gauss sum. -/
private lemma norm_cChi {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (N : ℕ)
    (hN : IsUnit ((N : ℤ) : ZMod q)) :
    ‖cChi ψ (N : ℤ)‖ = ‖tauConj ψ‖ := by
  classical
  obtain ⟨u, hu⟩ := hN
  rw [cChi_eq_mul_sum ψ N u hu.symm, norm_mul,
    norm_chi_apply_unit ψ u⁻¹, one_mul]
  have hG : (starRingEnd ℂ) (tauConj ψ)
      = ψ (-1) * ∑ b : ZMod q, ψ b * ee ((b.val : ℝ) / q) := by
    have h1 : (starRingEnd ℂ) (tauConj ψ)
        = ∑ b : ZMod q, ψ b * ee (-((b.val : ℝ) / q)) := by
      rw [tauConj, map_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [map_mul, starRingEnd_starRingEnd, star_ee]
    have h2 : ∑ b : ZMod q, ψ b * ee (-((b.val : ℝ) / q))
        = ψ (-1) * ∑ c : ZMod q, ψ c * ee ((c.val : ℝ) / q) := by
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.neg (ZMod q))
        (fun c : ZMod q => ψ (-1) * (ψ c * ee ((c.val : ℝ) / q)))]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [show (Equiv.neg (ZMod q)) b = -b from rfl, ee_val_neg b]
      rw [show ψ (-b) = ψ (-1) * ψ b from by
        rw [show (-b : ZMod q) = (-1) * b by ring]
        exact map_mul ψ.toMonoidHom (-1) b]
      have hsq : ψ (-1) * ψ (-1) = 1 := by
        have h := map_mul ψ.toMonoidHom (-1 : ZMod q) (-1)
        rw [show (-1 : ZMod q) * (-1) = 1 by ring, map_one] at h
        exact h.symm
      calc ψ b * ee (-((b.val : ℝ) / q))
          = (ψ (-1) * ψ (-1)) * (ψ b * ee (-((b.val : ℝ) / q))) := by
            rw [hsq, one_mul]
        _ = ψ (-1) * (ψ (-1) * ψ b * ee (-((b.val : ℝ) / q))) := by ring
    rw [h1, h2]
  set G : ℂ := ∑ b : ZMod q, ψ b * ee ((b.val : ℝ) / q) with hGdef
  have hnorm1 : ‖ψ (-1)‖ = 1 := norm_chi_apply_of_isUnit ψ (isUnit_one.neg)
  have hstep : ‖ψ (-1) * G‖ = ‖G‖ := by rw [norm_mul, hnorm1, one_mul]
  calc ‖G‖ = ‖ψ (-1) * G‖ := hstep.symm
    _ = ‖(starRingEnd ℂ) (tauConj ψ)‖ := by rw [hG]
    _ = ‖tauConj ψ‖ := by rw [Complex.norm_conj]

/-- For a primitive character and a unit argument the twisted Ramanujan sum has modulus `√q`. -/
private theorem norm_cChi_sq {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (N : ℕ)
    (hψ : ψ.IsPrimitive) (hN : IsUnit ((N : ℤ) : ZMod q)) :
    ‖cChi ψ (N : ℤ)‖ ^ 2 = (q : ℝ) := by
  rw [norm_cChi ψ N hN, norm_tauConj_sq ψ hψ]

/-- `ee(m·N/q)` as an additive-character value. -/
private lemma ee_mul_eq_stdAddChar {q : ℕ} [NeZero q] (m : ZMod q) (N : ℕ) :
    ee ((m.val : ℝ) * (N : ℝ) / q) = ZMod.stdAddChar (N := q) (m * (N : ZMod q)) := by
  rw [← ee_val_eq_stdAddChar (m * (N : ZMod q))]
  have hL : ((m.val : ℝ) * (N : ℝ) / q) = (((m.val * N : ℕ)) : ℝ) / q := by
    push_cast
    ring
  rw [hL]
  refine ee_eq_of_modEq (q := q) ?_
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- If `p ∤ N`, the twisted Ramanujan sum of a character lifted from a lower power of `p`
vanishes: the shift `x ↦ x + p ^ (k - 1)` leaves the character alone and multiplies the
exponential by `e(N/p) ≠ 1`. -/
private theorem cChi_changeLevel_pow_eq_zero {p b k : ℕ} (hp : p.Prime) (hbk : b < k)
    (hk2 : 2 ≤ k) [NeZero (p ^ k)] (φ : DirichletCharacter ℂ (p ^ b)) (N : ℕ) (hN : ¬ p ∣ N) :
    cChi (DirichletCharacter.changeLevel (Nat.pow_dvd_pow p hbk.le) φ) (N : ℤ) = 0 := by
  classical
  haveI : NeZero (p ^ b) := ⟨pow_ne_zero b hp.ne_zero⟩
  set Ψ := DirichletCharacter.changeLevel (Nat.pow_dvd_pow p hbk.le) φ with hΨ
  set d : ZMod (p ^ k) := ((p ^ (k - 1) : ℕ) : ZMod (p ^ k)) with hd
  have hdvd : p ^ b ∣ p ^ (k - 1) := Nat.pow_dvd_pow p (by omega)
  have hcastd : ZMod.castHom (Nat.pow_dvd_pow p hbk.le) (ZMod (p ^ b)) d = 0 := by
    rw [hd, map_natCast, ZMod.natCast_eq_zero_iff]
    exact hdvd
  have hnil : IsNilpotent d := by
    refine ⟨2, ?_⟩
    rw [hd, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff, ← pow_mul]
    exact pow_dvd_pow _ (by omega)
  have hunit : ∀ m : ZMod (p ^ k), IsUnit (m + d) ↔ IsUnit m := by
    intro m
    constructor
    · intro h
      have := hnil.neg.isUnit_add_left_of_commute h (Commute.all _ _)
      simpa using this
    · intro h
      exact hnil.isUnit_add_left_of_commute h (Commute.all _ _)
  have hΨd : ∀ m : ZMod (p ^ k), Ψ (m + d) = Ψ m := by
    intro m
    by_cases h : IsUnit m
    · obtain ⟨u, rfl⟩ := h
      obtain ⟨v, hv⟩ := (hunit (u : ZMod (p ^ k))).mpr u.isUnit
      rw [← hv, hΨ,
        ← MulChar.coe_toUnitHom (DirichletCharacter.changeLevel (Nat.pow_dvd_pow p hbk.le) φ) v,
        ← MulChar.coe_toUnitHom (DirichletCharacter.changeLevel (Nat.pow_dvd_pow p hbk.le) φ) u,
        DirichletCharacter.changeLevel_toUnitHom]
      congr 1
      simp only [MonoidHom.comp_apply]
      congr 1
      refine Units.ext ?_
      rw [ZMod.unitsMap_val, ZMod.unitsMap_val]
      rw [show (↑v : ZMod (p ^ k)) = (↑u : ZMod (p ^ k)) + d from hv]
      change ZMod.castHom (Nat.pow_dvd_pow p hbk.le) (ZMod (p ^ b)) ((↑u : ZMod (p ^ k)) + d)
        = ZMod.castHom (Nat.pow_dvd_pow p hbk.le) (ZMod (p ^ b)) (↑u : ZMod (p ^ k))
      rw [map_add, hcastd, add_zero]
    · rw [MulChar.map_nonunit _ h, MulChar.map_nonunit _ (fun h' => h ((hunit m).mp h'))]
  have hshift : cChi Ψ (N : ℤ)
      = cChi Ψ (N : ℤ) * ZMod.stdAddChar (N := p ^ k) (d * (N : ZMod (p ^ k))) := by
    rw [cChi, Finset.sum_mul]
    simp only [Int.cast_natCast]
    rw [show (∑ x : ZMod (p ^ k), Ψ x * ee ((x.val : ℝ) * (N : ℝ) / ((p ^ k : ℕ) : ℝ)))
        = ∑ x : ZMod (p ^ k),
            Ψ (x + d) * ee (((x + d).val : ℝ) * (N : ℝ) / ((p ^ k : ℕ) : ℝ)) from by
      rw [← Equiv.sum_comp (Equiv.addRight d)]
      simp only [Equiv.coe_addRight]]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hΨd x]
    have hexp : ee (((x + d).val : ℝ) * (N : ℝ) / ((p ^ k : ℕ) : ℝ))
        = ee ((x.val : ℝ) * (N : ℝ) / ((p ^ k : ℕ) : ℝ))
          * ZMod.stdAddChar (N := p ^ k) (d * (N : ZMod (p ^ k))) := by
      rw [ee_mul_eq_stdAddChar (x + d) N, ee_mul_eq_stdAddChar x N, add_mul,
        AddChar.map_add_eq_mul]
    rw [hexp]
    ring
  have hfac : ZMod.stdAddChar (N := p ^ k) (d * (N : ZMod (p ^ k))) ≠ 1 := by
    rw [← ee_mul_eq_stdAddChar d N]
    have hdv : (d.val : ℝ) = (p : ℝ) ^ (k - 1) := by
      rw [hd, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp.one_lt (by omega))]
      push_cast
      ring
    rw [hdv]
    have hpk : ((p : ℝ) ^ k) = (p : ℝ) ^ (k - 1) * (p : ℝ) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [show ((p : ℝ) ^ (k - 1) * (N : ℝ)) / (((p ^ k : ℕ)) : ℝ)
        = (N : ℝ) / (p : ℝ) by
      rw [Nat.cast_pow, hpk]
      field_simp]
    intro h
    exact hN (by
      have h2 : ((p : ℤ)) ∣ ((N : ℤ)) := (ee_div_eq_one_iff_dvd (N : ℤ) hp.pos).mp h
      exact_mod_cast h2)
  have hzero : cChi Ψ (N : ℤ) * (1 - ZMod.stdAddChar (N := p ^ k) (d * (N : ZMod (p ^ k)))) = 0 := by
    rw [mul_sub, mul_one, ← hshift, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hfac

/-- The twisted Ramanujan sum of the trivial character is the Ramanujan sum. -/
private lemma cChi_one_eq_ramanujan (q : ℕ) [NeZero q] (N : ℤ) :
    cChi (1 : DirichletCharacter ℂ q) N = ramanujan q N := by
  have hL : cChi (1 : DirichletCharacter ℂ q) N
      = ∑ a ∈ (Finset.univ.filter (fun a : ZMod q => IsUnit a)),
          ee ((a.val : ℝ) * (N : ℝ) / q) := by
    rw [cChi]
    rw [show (∑ a : ZMod q, (1 : DirichletCharacter ℂ q) a * ee ((a.val : ℝ) * (N : ℝ) / q))
        = ∑ a : ZMod q, (if IsUnit a then ee ((a.val : ℝ) * (N : ℝ) / q) else 0) from by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : IsUnit a
      · rw [if_pos h, MulChar.one_apply h, one_mul]
      · rw [if_neg h, MulChar.map_nonunit _ h, zero_mul]]
    rw [← Finset.sum_filter]
  rw [hL, ramanujan]
  refine Finset.sum_bij (fun a _ => a.val) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_range.mpr (ZMod.val_lt a), ?_⟩
    rw [← ZMod.natCast_zmod_val a] at ha
    exact (ZMod.isUnit_iff_coprime a.val q).mp ha.2
  · intro a₁ ha₁ a₂ ha₂ heq
    rw [← ZMod.natCast_zmod_val a₁, ← ZMod.natCast_zmod_val a₂, heq]
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_range] at hb
    refine ⟨(b : ZMod q), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [ZMod.isUnit_iff_coprime]
      exact hb.2
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hb.1]
  · intro a _
    rfl


/-- The trivial character mod `1` has Gauss sum `1`. -/
private lemma tauConj_one_level_one' : tauConj (1 : DirichletCharacter ℂ 1) = 1 := by
  unfold tauConj
  rw [Fintype.sum_subsingleton _ (0 : ZMod 1)]
  have h : (1 : DirichletCharacter ℂ 1) 0 = 1 := by
    have : (0 : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [this, map_one]
  simp [h, ZMod.val_zero, ee_zero]

/-- Sum of `1` against the standard additive character over the residues mod a prime. -/
private lemma sum_one_mul_std (p : ℕ) [Fact p.Prime] :
    ∑ m : ZMod p, (1 : DirichletCharacter ℂ p) m * ZMod.stdAddChar m = -1 := by
  have h0 : ∑ m : ZMod p, (ZMod.stdAddChar m : ℂ) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (fun h => by
      have := ZMod.isPrimitive_stdAddChar p
      have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
      have h2 := this h1
      apply h2
      ext x
      simp [AddChar.mulShift_apply, h])
  have hsplit : ∀ m : ZMod p, (1 : DirichletCharacter ℂ p) m * ZMod.stdAddChar m =
      ZMod.stdAddChar m - if m = 0 then 1 else 0 := by
    intro m
    by_cases h : m = 0
    · subst h
      simp [MulChar.map_zero, AddChar.map_zero_eq_one]
    · have hu : IsUnit m := isUnit_iff_ne_zero.mpr h
      obtain ⟨u, rfl⟩ := hu
      simp [MulChar.one_apply_coe]
  simp only [hsplit, Finset.sum_sub_distrib, h0]
  simp

/-- The trivial character mod a prime has Gauss sum `-1`. -/
private lemma tauConj_one_prime' (p : ℕ) [Fact p.Prime] :
    tauConj (1 : DirichletCharacter ℂ p) = -1 := by
  rw [tauConj_eq_sum_stdAddChar, ← sum_one_mul_std p]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  by_cases h : IsUnit m
  · obtain ⟨u, rfl⟩ := h
    simp [MulChar.one_apply_coe]
  · simp [MulChar.map_nonunit _ h]

private lemma cChi_one_level_one' (N : ℤ) : cChi (1 : DirichletCharacter ℂ 1) N = 1 := by
  unfold cChi
  rw [Fintype.sum_subsingleton _ (0 : ZMod 1)]
  have h : (1 : DirichletCharacter ℂ 1) 0 = 1 := by
    have : (0 : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [this, map_one]
  simp [h, ZMod.val_zero, ee_zero]

/-- The Gauss sum of the lift of a character of level `r` to level `p ^ k` (`r ∣ p ^ k`,
`r < p ^ k`, `k ≥ 2`) vanishes. -/
private theorem tauConj_changeLevel_eq_zero_of_lt {p k r : ℕ} (hp : p.Prime) (hk2 : 2 ≤ k)
    [NeZero (p ^ k)] (hr : r ∣ p ^ k) (hlt : r < p ^ k) (χ : DirichletCharacter ℂ r) :
    tauConj (DirichletCharacter.changeLevel hr χ) = 0 := by
  obtain ⟨a, hak, rfl⟩ := (Nat.dvd_prime_pow hp).mp hr
  have hak' : a < k := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  exact tauConj_changeLevel_pow_eq_zero hp hak' hk2 χ

/-- For `k ≥ 2` the term of the generalised Euler factor at `p ^ k` vanishes unless the first
character has level exactly `p ^ k`: the Gauss sum of a strictly lower lift is zero. -/
private theorem Aq_pow_eq_zero_of_ne_level {p k r₁ r₂ : ℕ} (hp : p.Prime) (hk2 : 2 ≤ k)
    [NeZero (p ^ k)] (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    (h : r₁ ≠ p ^ k) :
    @Aq r₁ r₂ χ₁ χ₂ N (p ^ k) _ = 0 := by
  unfold Aq
  by_cases hboth : r₁ ∣ p ^ k ∧ r₂ ∣ p ^ k
  · rw [dif_pos hboth]
    have hlt : r₁ < p ^ k := lt_of_le_of_ne (Nat.le_of_dvd (pow_pos hp.pos k) hboth.1) h
    rw [tauConj_changeLevel_eq_zero_of_lt hp hk2 hboth.1 hlt χ₁]
    simp
  · rw [dif_neg hboth]


/-- The Ramanujan sum is a real number. -/
private lemma ramanujan_eq_ofReal_re {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ramanujan q n = ((ramanujan q n).re : ℂ) := by
  set S : ℝ := ∑ d ∈ (Nat.gcd q n.natAbs).divisors,
    (d : ℝ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℝ) with hS
  have h1 : ramanujan q n = (S : ℂ) := by
    rw [ramanujan_eq_divisor_sum hq n, hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    push_cast
    ring
  have h2 : (ramanujan q n).re = S := by rw [h1, Complex.ofReal_re]
  rw [h1, Complex.ofReal_re]

/-- `Aq` is independent of the proof that the modulus is nonzero. -/
private lemma Aq_congr' {r₁ r₂ : ℕ} (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (N : ℤ) {q q' : ℕ} (h : q = q') [i : NeZero q] [i' : NeZero q'] :
    @Aq r₁ r₂ χ₁ χ₂ N q i = @Aq r₁ r₂ χ₁ χ₂ N q' i' := by
  subst h
  rfl

/-- `Aq` at `r₁ = r₂ = 1` and modulus `q`. -/
private lemma Aq_one_one (N : ℤ) (q : ℕ) [NeZero q] :
    Aq (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) N q
      = tauConj (1 : DirichletCharacter ℂ q) * tauConj (1 : DirichletCharacter ℂ q)
          * cChi (1 : DirichletCharacter ℂ q) N / (Nat.totient q : ℂ) ^ 2 := by
  unfold Aq
  rw [dif_pos ⟨one_dvd q, one_dvd q⟩]
  simp only [DirichletCharacter.changeLevel_one, one_mul]

private lemma Aq_at_one (N : ℤ) :
    Aq (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) N 1 = 1 := by
  rw [Aq_one_one, tauConj_one_level_one', cChi_one_level_one', Nat.totient_one]
  norm_num

private lemma Aq_at_prime (N : ℤ) (p : ℕ) [Fact p.Prime] :
    Aq (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) N p
      = ramanujan p N / (Nat.totient p : ℂ) ^ 2 := by
  rw [Aq_one_one, tauConj_one_prime', cChi_one_eq_ramanujan]
  rw [show (-1 : ℂ) * (-1) * ramanujan p N = ramanujan p N by ring]

/-- `local_bound` in the case `r₁ = r₂ = 1`: the two sides are equal. -/
private theorem local_bound_one_one (N : ℕ) (p : ℕ) (hp : p.Prime) :
    ‖eulerFactorGen (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) (N : ℤ) p‖
      ≤ eulerFactorSing N p := by
  haveI := Fact.mk hp
  have hne : ∀ k : ℕ, p ^ k ≠ 0 := fun k => pow_ne_zero k hp.ne_zero
  have hφ : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have h1 : ∀ k : ℕ, 2 ≤ k → (1 : ℕ) ≠ p ^ k := by
    intro k hk h
    have h2 : 1 < p ^ k := one_lt_pow₀ hp.one_lt (by omega)
    rw [← h] at h2
    exact absurd h2 (by norm_num)
  have hgen : eulerFactorGen (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) (N : ℤ) p
      = ((eulerFactorSing N p : ℝ) : ℂ) := by
    unfold eulerFactorGen
    rw [tsum_eq_sum (s := {0, 1}) ?_, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    · rw [dif_neg (hne 0), dif_neg (hne 1),
        Aq_congr' _ _ _ (pow_zero p) (i' := ⟨one_ne_zero⟩),
        Aq_congr' _ _ _ (pow_one p) (i' := ⟨hp.ne_zero⟩),
        Aq_at_one, Aq_at_prime, ramanujan_eq_ofReal_re hp.one_le,
        eulerFactorSing_prime_val hp N]
      push_cast
      ring
    · intro k hk
      have hk2 : 2 ≤ k := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        omega
      rw [dif_neg (hne k)]
      exact Aq_pow_eq_zero_of_ne_level hp hk2 (1 : DirichletCharacter ℂ 1)
        (1 : DirichletCharacter ℂ 1) (N : ℤ) (h1 k hk2)
  rw [hgen, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (eulerFactorSing_nonneg hp N)]


/-- A character invariant under a shift `d` whose exponential is not `1` has zero Gauss sum. -/
private lemma tauConj_eq_zero_of_shift {q : ℕ} [NeZero q] (Ψ : DirichletCharacter ℂ q) (d : ZMod q)
    (hd : ZMod.stdAddChar (N := q) d ≠ 1) (h : ∀ m : ZMod q, Ψ (m + d) = Ψ m) :
    tauConj Ψ = 0 := by
  have hshift : tauConj Ψ = tauConj Ψ * ZMod.stdAddChar (N := q) d := by
    rw [tauConj_eq_sum_stdAddChar, Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight d)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Equiv.coe_addRight, h m, AddChar.map_add_eq_mul]
    ring
  have hzero : tauConj Ψ * (1 - ZMod.stdAddChar (N := q) d) = 0 := by
    rw [mul_sub, mul_one, ← hshift, sub_self]
  rcases mul_eq_zero.mp hzero with h1 | h1
  · exact h1
  · exact absurd (sub_eq_zero.mp h1).symm hd

private lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

/-- The twisted Ramanujan sum is at most `φ(q)` in modulus. -/
private lemma norm_cChi_le_totient {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (N : ℤ) :
    ‖cChi ψ N‖ ≤ (Nat.totient q : ℝ) := by
  have hterm : ∀ a : ZMod q, ‖ψ a * ee ((a.val : ℝ) * (N : ℝ) / q)‖
      = if IsUnit a then 1 else 0 := by
    intro a
    rw [norm_mul, norm_ee, mul_one]
    by_cases ha : IsUnit a
    · rw [if_pos ha]
      obtain ⟨u, rfl⟩ := ha
      exact norm_chi_apply_unit ψ u
    · rw [if_neg ha, MulChar.map_nonunit _ ha, norm_zero]
  unfold cChi
  refine (norm_sum_le _ _).trans_eq ?_
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one, card_isUnit]


/-- `(1 + 2 ^ (a-1)) ^ 2 = 1` in `ZMod (2 ^ a)` for `a ≥ 2`. -/
private lemma two_pow_add_one_sq (a : ℕ) (ha : 2 ≤ a) :
    (((1 + 2 ^ (a - 1) : ℕ)) : ZMod (2 ^ a)) ^ 2 = 1 := by
  have h1 : 2 * 2 ^ (a - 1) = 2 ^ a := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : 2 ^ (a - 1) * 2 ^ (a - 1) = 2 ^ a * 2 ^ (a - 2) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hsq : (1 + 2 ^ (a - 1)) ^ 2 = 1 + 2 ^ a * (1 + 2 ^ (a - 2)) := by
    calc (1 + 2 ^ (a - 1)) ^ 2 = 1 + 2 * 2 ^ (a - 1) + 2 ^ (a - 1) * 2 ^ (a - 1) := by ring
      _ = 1 + 2 ^ a * (1 + 2 ^ (a - 2)) := by rw [h1, h2]; ring
  have hNat : (1 + 2 ^ (a - 1)) ^ 2 ≡ 1 [MOD 2 ^ a] := by
    rw [hsq]
    have hz : 2 ^ a * (1 + 2 ^ (a - 2)) ≡ 0 [MOD 2 ^ a] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
    simpa using Nat.ModEq.add_left 1 hz
  rw [← Nat.cast_pow]
  simpa using (ZMod.natCast_eq_natCast_iff ((1 + 2 ^ (a - 1)) ^ 2) 1 (2 ^ a)).mpr hNat

/-- A unit of `ZMod (2 ^ a)` that is `1` modulo `2 ^ (a-1)` is `1` or `1 + 2 ^ (a-1)`. -/
private lemma unitsMap_two_pow_eq_one {a : ℕ} (ha : 2 ≤ a) (u : (ZMod (2 ^ a))ˣ)
    (h : ZMod.unitsMap (Nat.pow_dvd_pow 2 (by omega : a - 1 ≤ a)) u = 1) :
    (u : ZMod (2 ^ a)) = 1 ∨
      (u : ZMod (2 ^ a)) = (((1 + 2 ^ (a - 1) : ℕ)) : ZMod (2 ^ a)) := by
  haveI : Fact (1 < 2 ^ a) := ⟨Nat.one_lt_pow (by omega) (by norm_num)⟩
  have hd1 : 1 < 2 ^ (a - 1) := by
    calc 1 < 2 := by norm_num
      _ ≤ 2 ^ (a - 1) := Nat.le_self_pow (by omega) 2
  have hval : ((u : ZMod (2 ^ a)).val) % 2 ^ (a - 1) = 1 := by
    have hv : ((ZMod.unitsMap (Nat.pow_dvd_pow 2 (by omega : a - 1 ≤ a)) u :
        (ZMod (2 ^ (a-1)))ˣ) : ZMod (2 ^ (a - 1))) = 1 := by rw [h]; exact Units.val_one
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val] at hv
    have h2 : ((u : ZMod (2 ^ a)).val) ≡ 1 [MOD 2 ^ (a - 1)] :=
      (ZMod.natCast_eq_natCast_iff _ 1 _).mp (by simpa using hv)
    rw [Nat.ModEq, Nat.mod_eq_of_lt hd1] at h2
    exact h2
  have hlt : (u : ZMod (2 ^ a)).val < 2 ^ a := ZMod.val_lt _
  set v := (u : ZMod (2 ^ a)).val with hvdef
  have h2a : 2 ^ a = 2 ^ (a - 1) * 2 := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    rw [pow_succ]
  have hlt' : v < 2 ^ (a - 1) * 2 := by rw [← h2a]; exact hlt
  have hdec : v = 2 ^ (a - 1) * (v / 2 ^ (a - 1)) + 1 := by
    have h4 := Nat.div_add_mod v (2 ^ (a - 1))
    rw [hval] at h4
    omega
  have hq : v / 2 ^ (a - 1) < 2 := by
    have hpos : 0 < 2 ^ (a - 1) := by positivity
    have hmul : 2 ^ (a - 1) * (v / 2 ^ (a - 1)) < 2 ^ (a - 1) * 2 := by omega
    exact (Nat.mul_lt_mul_left hpos).mp hmul
  rcases Nat.eq_zero_or_pos (v / 2 ^ (a - 1)) with hc | hc
  · left
    refine ZMod.val_injective (2 ^ a) ?_
    rw [ZMod.val_one]
    rw [hc] at hdec
    simpa using hdec
  · right
    have hc1 : v / 2 ^ (a - 1) = 1 := by omega
    refine ZMod.val_injective (2 ^ a) ?_
    rw [ZMod.val_natCast]
    have hle : 1 + 2 ^ (a - 1) < 2 ^ a := by rw [h2a]; omega
    rw [Nat.mod_eq_of_lt hle]
    rw [hc1] at hdec
    omega

/-- A primitive character mod `2 ^ a` (`a ≥ 2`) takes the value `-1` at `1 + 2 ^ (a-1)`. -/
private lemma primitive_two_pow_apply (a : ℕ) (ha : 2 ≤ a) (χ : DirichletCharacter ℂ (2 ^ a))
    (hχ : χ.IsPrimitive) :
    χ (((1 + 2 ^ (a - 1) : ℕ)) : ZMod (2 ^ a)) = -1 := by
  haveI : NeZero (2 ^ a) := ⟨(pow_pos (by norm_num) a).ne'⟩
  have hdiv : 2 ^ (a - 1) ∣ 2 ^ a := Nat.pow_dvd_pow 2 (by omega)
  set w : ZMod (2 ^ a) := (((1 + 2 ^ (a - 1) : ℕ)) : ZMod (2 ^ a)) with hw
  have hlt : 2 ^ (a - 1) < 2 ^ a := by
    conv_rhs => rw [show a = (a - 1) + 1 by omega]
    rw [pow_succ]
    have : 0 < 2 ^ (a - 1) := by positivity
    omega
  have hnotfac : ¬ χ.FactorsThrough (2 ^ (a - 1)) := by
    intro hf
    have hmem : 2 ^ (a - 1) ∈ χ.conductorSet := (DirichletCharacter.mem_conductorSet_iff χ).mpr hf
    have hdvd : χ.conductor ∣ 2 ^ (a - 1) := DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hmem
    rw [DirichletCharacter.isPrimitive_def] at hχ
    rw [hχ] at hdvd
    have hle : 2 ^ a ≤ 2 ^ (a - 1) := Nat.le_of_dvd (by positivity) hdvd
    omega
  have hker : ∃ u : (ZMod (2 ^ a))ˣ, ZMod.unitsMap hdiv u = 1 ∧ χ (u : ZMod (2 ^ a)) ≠ 1 := by
    by_contra hc
    push_neg at hc
    apply hnotfac
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hdiv]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    refine Units.ext ?_
    rw [Units.val_one, MulChar.coe_toUnitHom]
    exact hc u hu
  obtain ⟨u, hu1, hu2⟩ := hker
  have hsq : w ^ 2 = 1 := two_pow_add_one_sq a ha
  have hwne : χ w ≠ 1 := by
    rcases unitsMap_two_pow_eq_one ha u hu1 with h | h
    · rw [show (u : ZMod (2 ^ a)) = 1 from h, map_one] at hu2
      exact absurd rfl hu2
    · rwa [hw, ← h]
  have h2 : χ w ^ 2 = 1 := by rw [← map_pow, hsq, map_one]
  rcases sq_eq_one_iff.mp h2 with h | h
  · exact absurd h hwne
  · exact h

/-- Two primitive characters mod `2 ^ a` (`a ≥ 2`) multiply to `1` at `1 + 2 ^ (a-1)`. -/
private lemma mul_primitive_two_pow_apply (a : ℕ) (ha : 2 ≤ a)
    (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ a)) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    (χ₁ * χ₂) (((1 + 2 ^ (a - 1) : ℕ)) : ZMod (2 ^ a)) = 1 := by
  rw [MulChar.mul_apply, primitive_two_pow_apply a ha χ₁ h₁,
    primitive_two_pow_apply a ha χ₂ h₂]
  norm_num

/-- The product of two primitive characters mod `2 ^ a` (`a ≥ 2`) factors through `2 ^ (a-1)`. -/
private lemma factorsThrough_two_pow_mul_primitive (a : ℕ) (ha : 2 ≤ a)
    (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ a)) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    (χ₁ * χ₂).FactorsThrough (2 ^ (a - 1)) := by
  haveI : NeZero (2 ^ a) := ⟨(pow_pos (by norm_num) a).ne'⟩
  have hdiv : 2 ^ (a - 1) ∣ 2 ^ a := Nat.pow_dvd_pow 2 (by omega)
  have hw := mul_primitive_two_pow_apply a ha χ₁ χ₂ h₁ h₂
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hdiv]
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  rcases unitsMap_two_pow_eq_one ha u hu with h | h
  · refine Units.ext ?_
    rw [Units.val_one, MulChar.coe_toUnitHom, h, map_one]
  · refine Units.ext ?_
    rw [Units.val_one, MulChar.coe_toUnitHom, h, hw]

/-- The Gauss sum of the product of two primitive characters mod `2 ^ a` (`a ≥ 2`) vanishes. -/
private lemma tauConj_mul_primitive_two_pow_eq_zero (a : ℕ) (ha : 2 ≤ a)
    (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ a)) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    tauConj (χ₁ * χ₂) = 0 := by
  haveI : NeZero (2 ^ a) := ⟨(pow_pos (by norm_num) a).ne'⟩
  obtain ⟨h', χ₀, hχ₀⟩ := factorsThrough_two_pow_mul_primitive a ha χ₁ χ₂ h₁ h₂
  rw [hχ₀]
  refine tauConj_changeLevel_eq_zero_of_lt (p := 2) (k := a) (r := 2 ^ (a - 1)) (by norm_num) ha
    h' ?_ χ₀
  conv_rhs => rw [show a = (a - 1) + 1 by omega]
  rw [pow_succ]
  have : 0 < 2 ^ (a - 1) := by positivity
  omega


/-- `FactorsThrough` is monotone in the modulus. -/
private lemma factorsThrough_of_dvd {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} {c d : ℕ}
    (hcd : c ∣ d) (hdn : d ∣ n) (h : χ.FactorsThrough c) : χ.FactorsThrough d := by
  obtain ⟨hcn, χ₀, hχ₀⟩ := h
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hdn]
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  rw [hχ₀, DirichletCharacter.changeLevel_toUnitHom]
  show (MulChar.toUnitHom χ₀) (ZMod.unitsMap hcn u) = 1
  rw [← unitsMap_unitsMap hdn hcd u, hu, map_one, map_one]

/-- A character of level `p ^ k` that factors through a smaller divisor has zero Gauss sum. -/
private theorem tauConj_eq_zero_of_factorsThrough {p k d : ℕ} (hp : p.Prime) (hk2 : 2 ≤ k)
    [NeZero (p ^ k)] (_hd : d ∣ p ^ k) (hlt : d < p ^ k) {χ : DirichletCharacter ℂ (p ^ k)}
    (hf : χ.FactorsThrough d) : tauConj χ = 0 := by
  obtain ⟨h', χ₀, rfl⟩ := hf
  exact tauConj_changeLevel_eq_zero_of_lt hp hk2 h' hlt χ₀

/-- A character of level `p ^ k` (`k ≥ 2`) that is not primitive has zero Gauss sum. -/
private theorem tauConj_eq_zero_of_not_primitive {p k : ℕ} (hp : p.Prime) (hk2 : 2 ≤ k)
    [NeZero (p ^ k)] {χ : DirichletCharacter ℂ (p ^ k)} (hχ : ¬ χ.IsPrimitive) :
    tauConj χ = 0 := by
  obtain ⟨c, hc_le, hc_eq⟩ := (Nat.dvd_prime_pow hp).mp (DirichletCharacter.conductor_dvd_level χ)
  have hc_lt : c < k := by
    rcases lt_or_eq_of_le hc_le with h | h
    · exact h
    · exact absurd (by rw [DirichletCharacter.isPrimitive_def, hc_eq, h]) hχ
  have hfac : χ.FactorsThrough (p ^ (k - 1)) :=
    factorsThrough_of_dvd (c := p ^ c) (d := p ^ (k - 1))
      (Nat.pow_dvd_pow p (by omega))
      (Nat.pow_dvd_pow p (by omega))
      (by rw [← hc_eq]; exact DirichletCharacter.factorsThrough_conductor χ)
  exact tauConj_eq_zero_of_factorsThrough hp hk2 (Nat.pow_dvd_pow p (by omega))
    (Nat.pow_lt_pow_right hp.one_lt (by omega)) hfac


/-- The `Aq` of two characters of the same prime-power level, written out. -/
private lemma Aq_pow_level {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (N : ℤ) :
    Aq χ₁ χ₂ N q
      = tauConj χ₁ * tauConj χ₂ * cChi (χ₁ * χ₂) N / (Nat.totient q : ℂ) ^ 2 := by
  unfold Aq
  rw [dif_pos ⟨dvd_rfl, dvd_rfl⟩, DirichletCharacter.changeLevel_self,
    DirichletCharacter.changeLevel_self]

/-- The modulus of that term, with the totient cleared. -/
private lemma Aq_pow_level_norm {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (N : ℤ) :
    ‖Aq χ₁ χ₂ N q‖ * (Nat.totient q : ℝ) ^ 2
      = ‖tauConj χ₁‖ * ‖tauConj χ₂‖ * ‖cChi (χ₁ * χ₂) N‖ := by
  rw [Aq_pow_level, norm_div, norm_mul, norm_mul, norm_pow]
  norm_cast
  have hφ : (Nat.totient q : ℝ) ≠ 0 := by
    have h0 := Nat.totient_pos.mpr (NeZero.pos q)
    positivity
  field_simp

/-- The totient of a prime power, as a real number. -/
private lemma totient_pow_real {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (Nat.totient (p ^ a) : ℝ) = (p : ℝ) ^ (a - 1) * ((p : ℝ) - 1) := by
  rw [Nat.totient_prime_pow hp (by omega), Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub hp.one_le, Nat.cast_one]

/-- Case `p ∣ N` of the prime-power local bound: the crude bound `‖c‖ ≤ φ` suffices. -/
private theorem local_bound_pow_dvd {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (N : ℕ)
    [NeZero (p ^ a)] (hN : p ∣ N) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ a))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    ‖Aq χ₁ χ₂ (N : ℤ) (p ^ a)‖ ≤ eulerFactorSing N p := by
  haveI : NeZero (p ^ a) := ⟨(pow_pos hp.pos a).ne'⟩
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hφeq := totient_pow_real hp ha
  have hφpos : (0 : ℝ) < (Nat.totient (p ^ a) : ℝ) := by
    have h0 := Nat.totient_pos.mpr (NeZero.pos (p ^ a)); positivity
  have hτ₁ := norm_tauConj_sq χ₁ h₁
  have hτ₂ := norm_tauConj_sq χ₂ h₂
  have hc := norm_cChi_le_totient (χ₁ * χ₂) (N : ℤ)
  have hAB : ‖tauConj χ₁‖ * ‖tauConj χ₂‖ = (p : ℝ) ^ a := by
    have hnn : 0 ≤ ‖tauConj χ₁‖ * ‖tauConj χ₂‖ := by positivity
    have hsq : (‖tauConj χ₁‖ * ‖tauConj χ₂‖) ^ 2 = ((p : ℝ) ^ a) ^ 2 := by
      rw [mul_pow, hτ₁, hτ₂, Nat.cast_pow, ← pow_mul, ← pow_add]
      congr 1
      ring
    calc ‖tauConj χ₁‖ * ‖tauConj χ₂‖ = Real.sqrt ((‖tauConj χ₁‖ * ‖tauConj χ₂‖) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ = Real.sqrt (((p : ℝ) ^ a) ^ 2) := by rw [hsq]
      _ = (p : ℝ) ^ a := Real.sqrt_sq (by positivity)
  have hL : ‖Aq χ₁ χ₂ (N : ℤ) (p ^ a)‖ * (Nat.totient (p ^ a) : ℝ) ^ 2
      ≤ (p : ℝ) ^ a * (Nat.totient (p ^ a) : ℝ) := by
    rw [Aq_pow_level_norm, hAB]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hRHS : eulerFactorSing N p = (p : ℝ) ^ a / (Nat.totient (p ^ a) : ℝ) := by
    rw [eulerFactorSing_prime_val hp N, ramanujan_prime_val hp N, if_pos hN]
    have hφp : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [hφp, hφeq]
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hpa1 : (0 : ℝ) < (p : ℝ) ^ (a - 1) := by positivity
    have hpa : (p : ℝ) ^ a = (p : ℝ) ^ (a - 1) * (p : ℝ) := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega]
      rw [pow_succ]
    rw [hpa]
    field_simp
    ring
  rw [hRHS, le_div_iff₀ hφpos]
  have hkey : ‖Aq χ₁ χ₂ (N : ℤ) (p ^ a)‖ * (Nat.totient (p ^ a) : ℝ) ^ 2
      = ‖Aq χ₁ χ₂ (N : ℤ) (p ^ a)‖ * (Nat.totient (p ^ a) : ℝ) * (Nat.totient (p ^ a) : ℝ) := by
    ring
  rw [hkey] at hL
  exact le_of_mul_le_mul_right hL hφpos


/-- The product of the moduli of the two Gauss sums at a prime-power level. -/
private lemma tauConj_pair_norm {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    ‖tauConj χ₁‖ * ‖tauConj χ₂‖ = (q : ℝ) := by
  have hτ₁ := norm_tauConj_sq χ₁ h₁
  have hτ₂ := norm_tauConj_sq χ₂ h₂
  have hnn : 0 ≤ ‖tauConj χ₁‖ * ‖tauConj χ₂‖ := by positivity
  have hsq : (‖tauConj χ₁‖ * ‖tauConj χ₂‖) ^ 2 = ((q : ℝ)) ^ 2 := by
    rw [mul_pow, hτ₁, hτ₂]
    ring
  calc ‖tauConj χ₁‖ * ‖tauConj χ₂‖ = Real.sqrt ((‖tauConj χ₁‖ * ‖tauConj χ₂‖) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ = Real.sqrt (((q : ℝ)) ^ 2) := by rw [hsq]
    _ = (q : ℝ) := Real.sqrt_sq (by positivity)

/-- `1 - 1/(p-1)²` is nonnegative for a prime `p`. -/
private lemma one_sub_inv_sq_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h1 : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
  have h0 : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by linarith
  rw [sub_nonneg, div_le_one h0]
  linarith

/-- Case `p ∤ N` of the prime-power local bound. -/
private theorem local_bound_pow_not_dvd {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (N : ℕ)
    [NeZero (p ^ a)] (hN : ¬ p ∣ N) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ a))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    ‖Aq χ₁ χ₂ (N : ℤ) (p ^ a)‖ ≤ eulerFactorSing N p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hφpos : (0 : ℝ) < (Nat.totient (p ^ a) : ℝ) := by
    have h0 := Nat.totient_pos.mpr (NeZero.pos (p ^ a)); positivity
  have hRHS : eulerFactorSing N p = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
    rw [eulerFactorSing_prime_val hp N, ramanujan_prime_val hp N, if_neg hN]
    have hφp : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [hφp]
    field_simp
    ring
  rw [hRHS]
  have hNunit : IsUnit (((N : ℤ)) : ZMod (p ^ a)) := by
    have h' : IsUnit ((N : ℕ) : ZMod (p ^ a)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.coprime_pow_right_iff (by omega) N p).mpr (Nat.coprime_comm.mpr (hp.coprime_iff_not_dvd.mpr hN))
    simpa using h'
  by_cases hprod : (χ₁ * χ₂).IsPrimitive
  · have hc : ‖cChi (χ₁ * χ₂) (N : ℤ)‖ ^ 2 = (p : ℝ) ^ a := by
      rw [norm_cChi _ _ hNunit, norm_tauConj_sq _ hprod, Nat.cast_pow]
    have hpne2 : p ≠ 2 := by
      intro h2
      subst h2
      have hz := tauConj_mul_primitive_two_pow_eq_zero a ha χ₁ χ₂ h₁ h₂
      have hsq := norm_tauConj_sq (χ₁ * χ₂) hprod
      rw [hz, norm_zero] at hsq
      have hpos : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
      have hcast : ((2 ^ a : ℕ) : ℝ) = (2 : ℝ) ^ a := Nat.cast_pow 2 a
      rw [hcast] at hsq
      linarith
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      have h3 : 3 ≤ p := by
        rcases lt_or_eq_of_le hp.two_le with h | h
        · omega
        · exact absurd h.symm hpne2
      exact_mod_cast h3
    have hAB := tauConj_pair_norm χ₁ χ₂ h₁ h₂
    have hT2 : (‖tauConj χ₁‖ * ‖tauConj χ₂‖ * ‖cChi (χ₁ * χ₂) (N : ℤ)‖) ^ 2
        = (p : ℝ) ^ (3 * a) := by
      rw [mul_pow, hAB, Nat.cast_pow, ← pow_mul, hc, ← pow_add]
      congr 1
      ring
    have hsq : ‖Aq χ₁ χ₂ (N : ℤ) (p ^ a)‖ ^ 2 * ((Nat.totient (p ^ a) : ℝ) ^ 2) ^ 2
        = (p : ℝ) ^ (3 * a) := by
      have h := congrArg (fun z : ℝ => z ^ 2) (Aq_pow_level_norm χ₁ χ₂ (N : ℤ))
      rw [mul_pow, hT2] at h
      exact h
    have hφeq := totient_pow_real hp (by omega : 1 ≤ a)
    have hφ4 : ((Nat.totient (p ^ a) : ℝ) ^ 2) ^ 2
        = (p : ℝ) ^ (4 * (a - 1)) * ((p : ℝ) - 1) ^ 4 := by
      rw [hφeq]; ring
    rw [hφ4] at hsq
    have hpos4 : (0 : ℝ) < (p : ℝ) ^ (4 * (a - 1)) * ((p : ℝ) - 1) ^ 4 := by
      have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    have hAq2 : ‖Aq χ₁ χ₂ (N : ℤ) (p ^ a)‖ ^ 2
        = (p : ℝ) ^ (3 * a) / ((p : ℝ) ^ (4 * (a - 1)) * ((p : ℝ) - 1) ^ 4) := by
      rw [eq_div_iff hpos4.ne']
      exact hsq
    have hmain : (p : ℝ) ^ (3 * a) ≤ ((p : ℝ) ^ 2 - 2 * (p : ℝ)) ^ 2 * (p : ℝ) ^ (4 * (a - 1)) := by
      have hstep1 : (p : ℝ) ^ (3 * a) ≤ (p : ℝ) ^ (4 * (a - 1) + 2) := by
        apply pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (p : ℝ))
        omega
      have hstep3 : (p : ℝ) ^ 2 ≤ ((p : ℝ) ^ 2 - 2 * (p : ℝ)) ^ 2 := by
        have h1 : (p : ℝ) ≤ (p : ℝ) ^ 2 - 2 * (p : ℝ) := by nlinarith
        exact pow_le_pow_left₀ (le_of_lt hp0) h1 2
      calc (p : ℝ) ^ (3 * a) ≤ (p : ℝ) ^ (4 * (a - 1) + 2) := hstep1
        _ = (p : ℝ) ^ (4 * (a - 1)) * (p : ℝ) ^ 2 := by rw [pow_add]
        _ ≤ (p : ℝ) ^ (4 * (a - 1)) * ((p : ℝ) ^ 2 - 2 * (p : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hstep3 (by positivity)
        _ = ((p : ℝ) ^ 2 - 2 * (p : ℝ)) ^ 2 * (p : ℝ) ^ (4 * (a - 1)) := by ring
    have hgoal : ‖Aq χ₁ χ₂ (N : ℤ) (p ^ a)‖ ^ 2 ≤ (1 - 1 / ((p : ℝ) - 1) ^ 2) ^ 2 := by
      rw [hAq2, div_le_iff₀ hpos4]
      have hR : (1 - 1 / ((p : ℝ) - 1) ^ 2) ^ 2
            * ((p : ℝ) ^ (4 * (a - 1)) * ((p : ℝ) - 1) ^ 4)
          = ((p : ℝ) ^ 2 - 2 * (p : ℝ)) ^ 2 * (p : ℝ) ^ (4 * (a - 1)) := by
        have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring
      rw [hR]
      exact hmain
    have hle := Real.sqrt_le_sqrt hgoal
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (one_sub_inv_sq_nonneg hp)] at hle
  · have hc0 : cChi (χ₁ * χ₂) (N : ℤ) = 0 := by
      have hn := norm_cChi (χ₁ * χ₂) N hNunit
      rw [tauConj_eq_zero_of_not_primitive hp ha hprod, norm_zero] at hn
      exact norm_eq_zero.mp hn
    rw [Aq_pow_level, hc0]
    simp only [mul_zero, zero_div, norm_zero]
    exact one_sub_inv_sq_nonneg hp


/-- Every element of `ZMod 3` is `0`, `1` or `2`. -/
private lemma zmod_three_cases (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  have hv := ZMod.val_lt a
  have hc : a = ((a.val : ℕ) : ZMod 3) := (ZMod.natCast_zmod_val a).symm
  interval_cases a.val
  · left; rw [hc]; norm_num
  · right; left; rw [hc]; norm_num
  · right; right; rw [hc]; norm_num

/-- A character that factors through level `1` is trivial. -/
private lemma eq_one_of_factorsThrough_one {n : ℕ} {χ : DirichletCharacter ℂ n}
    (h : χ.FactorsThrough 1) : χ = 1 := by
  obtain ⟨h', χ₀, hχ₀⟩ := h
  have h1 : χ₀ = 1 := DirichletCharacter.level_one χ₀
  rw [hχ₀, h1, DirichletCharacter.changeLevel_one]

/-- A character mod `3` that is `1` at `2` is trivial. -/
private lemma eq_one_of_apply_two_eq_one (χ : DirichletCharacter ℂ 3) (h : χ 2 = 1) : χ = 1 := by
  have hu : IsUnit (2 : ZMod 3) := isUnit_iff_ne_zero.mpr (by decide)
  refine MulChar.ext ?_
  intro a
  rcases zmod_three_cases (↑a : ZMod 3) with h0 | h1 | h2
  · rw [h0, MulChar.map_zero, MulChar.map_zero]
  · rw [h1, map_one, MulChar.one_apply isUnit_one]
  · rw [h2, h, MulChar.one_apply hu]

/-- A primitive character mod `3` is `-1` at `2`. -/
private lemma apply_two_eq_neg_one_of_primitive (χ : DirichletCharacter ℂ 3) (hχ : χ.IsPrimitive) :
    χ 2 = -1 := by
  have hsq : χ 2 * χ 2 = 1 := by
    rw [← map_mul, show (2 : ZMod 3) * 2 = 1 by decide, map_one]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd (eq_one_of_apply_two_eq_one χ h) (by
      intro h1
      rw [h1, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
      exact absurd hχ.symm (by norm_num))
  · exact h

/-- Two primitive characters mod `3` multiply to the trivial one. -/
private lemma mul_primitive_three (χ₁ χ₂ : DirichletCharacter ℂ 3)
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) : χ₁ * χ₂ = 1 := by
  refine eq_one_of_apply_two_eq_one _ ?_
  rw [MulChar.mul_apply, apply_two_eq_neg_one_of_primitive χ₁ h₁,
    apply_two_eq_neg_one_of_primitive χ₂ h₂]
  norm_num

/-- A nonprincipal character of prime level is primitive. -/
private lemma isPrimitive_of_ne_one {p : ℕ} (hp : p.Prime) {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) : χ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd : χ.conductor ∣ p := DirichletCharacter.conductor_dvd_level χ
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (eq_one_of_factorsThrough_one (by
      have := DirichletCharacter.factorsThrough_conductor χ
      rwa [h] at this)) hχ
  · exact h



/-- Every element of `ZMod 2` is `0` or `1`. -/
private lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have hc : a = ((a.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val a).symm
  interval_cases a.val
  · left; rw [hc]; norm_num
  · right; rw [hc]; norm_num

/-- There is no primitive character mod `2`. -/
private lemma not_primitive_two (χ : DirichletCharacter ℂ 2) : ¬ χ.IsPrimitive := by
  intro hχ
  have h1 : χ = 1 := by
    refine MulChar.ext ?_
    intro a
    have hne : (a : ZMod 2) ≠ 0 := Units.ne_zero a
    rcases zmod_two_cases (a : ZMod 2) with h | h
    · exact absurd h hne
    · rw [h, map_one, MulChar.one_apply isUnit_one]
  rw [h1, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
  exact absurd hχ.symm (by norm_num)

/-- The `p ∤ N` part of the local bound at prime level, `p ≠ 3`. -/
private theorem local_bound_level_not_dvd {p : ℕ} (hp : p.Prime) [NeZero p] (N : ℕ) (hN1 : 1 ≤ N)
    (hN : ¬ p ∣ N) (hne3 : p ≠ 3) (χ₁ χ₂ : DirichletCharacter ℂ p)
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    ‖Aq χ₁ χ₂ N p‖ ≤ eulerFactorSing N p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hφp : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  haveI : NeZero 2 := ⟨by norm_num⟩
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by
    have h5 : 5 ≤ p := by
      rcases lt_or_eq_of_le hp.two_le with h2 | h2
      · rcases lt_or_eq_of_le (by omega : 3 ≤ p) with h3 | h3
        · have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
          omega
        · exact absurd h3.symm hne3
      · exfalso
        subst h2
        exact not_primitive_two χ₁ h₁
    exact_mod_cast h5
  have hRHS : eulerFactorSing N p = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
    rw [eulerFactorSing_prime_val hp N, ramanujan_prime_val hp N, if_neg hN, hφp]
    field_simp
    ring
  rw [hRHS]
  have hφpos : (0 : ℝ) < (Nat.totient p : ℝ) := by rw [hφp]; linarith
  have hNunit : IsUnit (((N : ℤ)) : ZMod p) := by
    have h' : IsUnit ((N : ℕ) : ZMod p) := by
      rw [ZMod.isUnit_iff_coprime]
      refine Nat.coprime_comm.mpr ?_
      exact hp.coprime_iff_not_dvd.mpr hN
    simpa using h'
  have hAB : ‖tauConj χ₁‖ * ‖tauConj χ₂‖ = (p : ℝ) := by
    exact tauConj_pair_norm χ₁ χ₂ h₁ h₂
  have hc : ‖cChi (χ₁ * χ₂) (N : ℤ)‖ ^ 2 ≤ (p : ℝ) := by
    by_cases hψ : χ₁ * χ₂ = 1
    · rw [hψ, cChi_one_eq_ramanujan, ramanujan_eq_ofReal_re hp.one_le,
        ramanujan_prime_val hp N, if_neg hN, Complex.norm_real, Real.norm_eq_abs,
        abs_neg, abs_one]
      norm_num
      exact hp.one_le
    · have hprim : (χ₁ * χ₂).IsPrimitive := isPrimitive_of_ne_one hp hψ
      rw [norm_cChi _ _ hNunit]
      exact le_of_eq (norm_tauConj_sq _ hprim)
  have hAq := Aq_pow_level_norm χ₁ χ₂ (N : ℤ)
  have hgoal : ‖Aq χ₁ χ₂ (N : ℤ) p‖ ^ 2 ≤ (1 - 1 / ((p : ℝ) - 1) ^ 2) ^ 2 := by
    have hφ2 : (0 : ℝ) < (Nat.totient p : ℝ) ^ 2 := by positivity
    have hsq : (‖Aq χ₁ χ₂ (N : ℤ) p‖ * (Nat.totient p : ℝ) ^ 2) ^ 2
        = (p : ℝ) ^ 2 * ‖cChi (χ₁ * χ₂) (N : ℤ)‖ ^ 2 := by
      rw [hAq, mul_pow, hAB]
    have h1 : ‖Aq χ₁ χ₂ (N : ℤ) p‖ ^ 2 * ((Nat.totient p : ℝ) ^ 2) ^ 2
        = (p : ℝ) ^ 2 * ‖cChi (χ₁ * χ₂) (N : ℤ)‖ ^ 2 := by
      rw [← hsq]; ring
    have h2 : ‖Aq χ₁ χ₂ (N : ℤ) p‖ ^ 2
        ≤ (p : ℝ) ^ 2 * (p : ℝ) / ((Nat.totient p : ℝ) ^ 2) ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((Nat.totient p : ℝ) ^ 2) ^ 2)]
      have h3 : (p : ℝ) ^ 2 * ‖cChi (χ₁ * χ₂) (N : ℤ)‖ ^ 2 ≤ (p : ℝ) ^ 2 * (p : ℝ) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      linarith [h1, h3]
    have hφ4 : ((Nat.totient p : ℝ) ^ 2) ^ 2 = ((p : ℝ) - 1) ^ 4 := by
      rw [hφp]; ring
    rw [hφ4] at h2
    have hR : (1 - 1 / ((p : ℝ) - 1) ^ 2) ^ 2 * ((p : ℝ) - 1) ^ 4
        = ((p : ℝ) ^ 2 - 2 * (p : ℝ)) ^ 2 := by
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    refine le_trans h2 ?_
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((p : ℝ) - 1) ^ 4), hR]
    have hstep : (p : ℝ) ≤ ((p : ℝ) - 2) ^ 2 := by nlinarith
    calc (p : ℝ) ^ 2 * (p : ℝ) = (p : ℝ) ^ 3 := by ring
      _ ≤ (p : ℝ) ^ 2 * ((p : ℝ) - 2) ^ 2 := by
          have hm := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 2)
          linarith [hm]
      _ = ((p : ℝ) ^ 2 - 2 * (p : ℝ)) ^ 2 := by ring
  have hle := Real.sqrt_le_sqrt hgoal
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (one_sub_inv_sq_nonneg hp)] at hle

/-- The `p = 3` part of the local bound at prime level. -/
private theorem local_bound_level_three (N : ℕ) (hN1 : 1 ≤ N) (hN : ¬ (3 : ℕ) ∣ N)
    (χ₁ χ₂ : DirichletCharacter ℂ 3) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    ‖Aq χ₁ χ₂ (N : ℤ) 3‖ ≤ eulerFactorSing N 3 := by
  have hp : Nat.Prime 3 := by norm_num
  haveI : NeZero 3 := ⟨by norm_num⟩
  have hψ : χ₁ * χ₂ = 1 := mul_primitive_three χ₁ χ₂ h₁ h₂
  have hc : ‖cChi (χ₁ * χ₂) (N : ℤ)‖ ≤ 1 := by
    rw [hψ, cChi_one_eq_ramanujan, ramanujan_eq_ofReal_re hp.one_le, ramanujan_prime_val hp N,
      if_neg hN, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_one]
  have hRHS : eulerFactorSing N 3 = 3 / 4 := by
    rw [eulerFactorSing_prime_val hp N, ramanujan_prime_val hp N, if_neg hN]
    norm_num [Nat.totient_prime]
  rw [hRHS]
  have hAB : ‖tauConj χ₁‖ * ‖tauConj χ₂‖ = 3 := by
    exact tauConj_pair_norm χ₁ χ₂ h₁ h₂
  have hAq := Aq_pow_level_norm χ₁ χ₂ (N : ℤ)
  have hφ3 : (Nat.totient 3 : ℝ) = 2 := by norm_num [Nat.totient_prime]
  have hval : ‖Aq χ₁ χ₂ (N : ℤ) 3‖ = ‖tauConj χ₁‖ * ‖tauConj χ₂‖ * ‖cChi (χ₁ * χ₂) (N : ℤ)‖ / 4 := by
    rw [eq_div_iff (by norm_num : (4 : ℝ) ≠ 0)]
    rw [← hAq, hφ3]
    ring
  rw [hval, hAB]
  nlinarith [hc, norm_nonneg (cChi (χ₁ * χ₂) (N : ℤ))]


/-- `Aq` is symmetric in its two characters. -/
private lemma Aq_comm {r₁ r₂ : ℕ} (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (N : ℤ) (q : ℕ) [NeZero q] : Aq χ₁ χ₂ N q = Aq χ₂ χ₁ N q := by
  unfold Aq
  by_cases h : r₁ ∣ q ∧ r₂ ∣ q
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩]
    have hmul : DirichletCharacter.changeLevel h.1 χ₁ * DirichletCharacter.changeLevel h.2 χ₂
        = DirichletCharacter.changeLevel h.2 χ₂ * DirichletCharacter.changeLevel h.1 χ₁ :=
      mul_comm _ _
    rw [hmul]
    ring
  · rw [dif_neg h, dif_neg (fun h' => h ⟨h'.2, h'.1⟩)]

/-- `eulerFactorGen` is symmetric in its two characters. -/
private lemma eulerFactorGen_comm {r₁ r₂ : ℕ} (χ₁ : DirichletCharacter ℂ r₁)
    (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ) (p : ℕ) :
    eulerFactorGen χ₁ χ₂ N p = eulerFactorGen χ₂ χ₁ N p := by
  unfold eulerFactorGen
  refine tsum_congr fun k => ?_
  by_cases h : p ^ k = 0
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, Aq_comm]

/-- The local factor at level `1 × p`. -/
private theorem local_bound_one_level_prime {p : ℕ} (hp : p.Prime) [NeZero p] (N : ℕ)
    (χ : DirichletCharacter ℂ p) (hχ : χ.IsPrimitive) :
    ‖Aq (1 : DirichletCharacter ℂ 1) χ N p‖ ≤ eulerFactorSing N p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hφp : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hτ : ‖tauConj χ‖ ^ 2 = (p : ℝ) := norm_tauConj_sq χ hχ
  have hτnn : 0 ≤ ‖tauConj χ‖ := norm_nonneg _
  have hτle : ‖tauConj χ‖ ≤ (p : ℝ) := by nlinarith [hτ]
  have hval : Aq (1 : DirichletCharacter ℂ 1) χ (N : ℤ) p
      = -tauConj χ * cChi χ (N : ℤ) / (Nat.totient p : ℂ) ^ 2 := by
    unfold Aq
    rw [dif_pos ⟨one_dvd p, dvd_rfl⟩, DirichletCharacter.changeLevel_one,
      DirichletCharacter.changeLevel_self, tauConj_one_prime', one_mul]
    ring
  have hnorm : ‖Aq (1 : DirichletCharacter ℂ 1) χ (N : ℤ) p‖
      = ‖tauConj χ‖ * ‖cChi χ (N : ℤ)‖ / (Nat.totient p : ℝ) ^ 2 := by
    rw [hval, norm_div, norm_mul, norm_neg, norm_pow]
    norm_cast
  by_cases hN : p ∣ N
  · have hRHS : eulerFactorSing N p = (p : ℝ) / ((p : ℝ) - 1) := by
      rw [eulerFactorSing_prime_val hp N, ramanujan_prime_val hp N, if_pos hN, hφp]
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [hRHS, hnorm, hφp, div_le_iff₀ (by positivity : (0 : ℝ) < ((p : ℝ) - 1) ^ 2)]
    have hR2 : (p : ℝ) / ((p : ℝ) - 1) * ((p : ℝ) - 1) ^ 2 = (p : ℝ) * ((p : ℝ) - 1) := by
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
    rw [hR2]
    have hc := norm_cChi_le_totient χ (N : ℤ)
    have h1 : ‖tauConj χ‖ * ‖cChi χ (N : ℤ)‖ ≤ ‖tauConj χ‖ * ((p : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left (by rw [← hφp]; exact hc) hτnn
    have h2 : ‖tauConj χ‖ * ((p : ℝ) - 1) ≤ (p : ℝ) * ((p : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hτle hp1.le
    linarith [h1, h2]
  · have hRHS : eulerFactorSing N p = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
      rw [eulerFactorSing_prime_val hp N, ramanujan_prime_val hp N, if_neg hN, hφp]
      field_simp
      ring
    have hNunit : IsUnit (((N : ℤ)) : ZMod p) := by
      have h' : IsUnit ((N : ℕ) : ZMod p) := by
        rw [ZMod.isUnit_iff_coprime]
        exact Nat.coprime_comm.mpr (hp.coprime_iff_not_dvd.mpr hN)
      simpa using h'
    have hc : ‖cChi χ (N : ℤ)‖ = ‖tauConj χ‖ := norm_cChi χ N hNunit
    have hR2 : (1 - 1 / ((p : ℝ) - 1) ^ 2)
        = ((p : ℝ) ^ 2 - 2 * (p : ℝ)) / ((p : ℝ) - 1) ^ 2 := by
      field_simp
      ring
    have hsq : ‖tauConj χ‖ * ‖tauConj χ‖ = (p : ℝ) := by
      rw [← hτ]; ring
    rw [hRHS, hR2, hnorm, hc, hsq, hφp]
    have hden : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      have h3 : 3 ≤ p := by
        rcases lt_or_eq_of_le hp.two_le with h | h
        · omega
        · exfalso
          subst h
          exact not_primitive_two χ hχ
      exact_mod_cast h3
    have hmain : (p : ℝ) ≤ (p : ℝ) ^ 2 - 2 * (p : ℝ) := by nlinarith
    calc (p : ℝ) ≤ (p : ℝ) ^ 2 - 2 * (p : ℝ) := hmain
      _ = ((p : ℝ) ^ 2 - 2 * (p : ℝ)) / ((p : ℝ) - 1) ^ 2 * ((p : ℝ) - 1) ^ 2 := by
          field_simp


/-- `Aq` vanishes when the modulus is not a common multiple of the two levels. -/
private lemma Aq_eq_zero_of_dvd_ne {r₁ r₂ : ℕ} (χ₁ : DirichletCharacter ℂ r₁)
    (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ) {q : ℕ} [NeZero q]
    (h : ¬ (r₁ ∣ q ∧ r₂ ∣ q)) : Aq χ₁ χ₂ N q = 0 := by
  unfold Aq
  rw [dif_neg h]

/-- The mirrored version of the vanishing of the lifted Gauss sum. -/
private theorem Aq_pow_eq_zero_of_ne_level_right {p k r₁ r₂ : ℕ} (hp : p.Prime) (hk2 : 2 ≤ k)
    [NeZero (p ^ k)] (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    (h : r₂ ≠ p ^ k) : @Aq r₁ r₂ χ₁ χ₂ N (p ^ k) _ = 0 := by
  rw [Aq_comm]
  exact Aq_pow_eq_zero_of_ne_level hp hk2 χ₂ χ₁ N h

/-- If both levels are `p ^ k` with `k ≥ 1`, the generalised Euler factor is that single term. -/
private lemma eulerFactorGen_eq_Aq_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (N : ℤ)
    [NeZero (p ^ k)] (χ₁ χ₂ : DirichletCharacter ℂ (p ^ k)) :
    eulerFactorGen χ₁ χ₂ N p = Aq χ₁ χ₂ N (p ^ k) := by
  haveI : ∀ j, NeZero (p ^ j) := fun j => ⟨pow_ne_zero j hp.ne_zero⟩
  unfold eulerFactorGen
  rw [tsum_eq_single k]
  · rw [dif_neg (pow_ne_zero k hp.ne_zero)]
  · intro j hj
    rw [dif_neg (pow_ne_zero j hp.ne_zero)]
    have hkpos : 0 < k := hk
    rcases Nat.eq_zero_or_pos j with h0 | hjpos
    · -- `j = 0`: `p ^ k` does not divide `1`
      subst h0
      exact Aq_eq_zero_of_dvd_ne _ _ _ (fun h => by
        obtain ⟨hd, -⟩ := h
        rw [pow_zero] at hd
        have hle : p ^ k ≤ 1 := Nat.le_of_dvd (by norm_num) hd
        have hlt : 1 < p ^ k := one_lt_pow₀ hp.one_lt (by omega)
        omega)
    · rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · -- `j = 1`: `p ^ k` does not divide `p` when `k ≥ 2`; `k = 1` contradicts `hj`
        have hj1 : j = 1 := by omega
        subst hj1
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · omega
        · exact Aq_eq_zero_of_dvd_ne _ _ _ (fun h => by
            obtain ⟨hd, -⟩ := h
            rw [pow_one] at hd
            have hle : p ^ k ≤ p := Nat.le_of_dvd hp.pos hd
            have h2 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
            have hlt : p < p ^ 2 := by
              have h := Nat.pow_lt_pow_right hp.one_lt (by norm_num : 1 < 2)
              simpa using h
            omega)
      · refine Aq_pow_eq_zero_of_ne_level (p := p) (k := j) hp hj2 χ₁ χ₂ N ?_
        intro hc
        exact hj (Nat.pow_right_injective hp.two_le hc).symm


/-- The local factor at level `1 × p`, in single-term form. -/
private lemma eulerFactorGen_one_prime {p : ℕ} (hp : p.Prime) [NeZero p] (N : ℤ)
    (χ : DirichletCharacter ℂ p) :
    eulerFactorGen (1 : DirichletCharacter ℂ 1) χ N p
      = Aq (1 : DirichletCharacter ℂ 1) χ N p := by
  haveI : ∀ j, NeZero (p ^ j) := fun j => ⟨pow_ne_zero j hp.ne_zero⟩
  unfold eulerFactorGen
  rw [tsum_eq_single 1]
  · rw [dif_neg (pow_ne_zero 1 hp.ne_zero)]
    exact Aq_congr' _ _ _ (pow_one p)
  · intro j hj
    rw [dif_neg (pow_ne_zero j hp.ne_zero)]
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      exact Aq_eq_zero_of_dvd_ne _ _ _ (fun h => by
        obtain ⟨-, h2⟩ := h
        rw [pow_zero] at h2
        exact absurd h2 (fun hc => hp.ne_one (Nat.dvd_one.mp hc)))
    · have hj2 : 2 ≤ j := by omega
      refine Aq_pow_eq_zero_of_ne_level_right (p := p) (k := j) hp hj2 _ _ N ?_
      intro hc
      have h1 : p ^ 1 = p ^ j := by rw [pow_one]; exact hc
      exact hj (Nat.pow_right_injective hp.two_le h1).symm


/-- The generalised Euler factor at level `q = p ^ k` (`k ≥ 1`) is the single term. -/
private lemma eulerFactorGen_eq_Aq_self {q : ℕ} [NeZero q] {p : ℕ} (hp : p.Prime) (N : ℤ)
    (k : ℕ) (hk : 1 ≤ k) (hq : q = p ^ k) (χ₁ χ₂ : DirichletCharacter ℂ q) :
    eulerFactorGen χ₁ χ₂ N p = Aq χ₁ χ₂ N q := by
  subst hq
  exact eulerFactorGen_eq_Aq_pow hp hk N χ₁ χ₂

/-- `local_bound_pow_dvd` with the modulus named `q`. -/
private theorem local_bound_pow_dvd' {q p a : ℕ} (hp : p.Prime) [NeZero q] (hq : q = p ^ a)
    (ha : 1 ≤ a) (N : ℕ) (hN : p ∣ N) (χ₁ χ₂ : DirichletCharacter ℂ q)
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    ‖Aq χ₁ χ₂ (N : ℤ) q‖ ≤ eulerFactorSing N p := by
  subst hq
  exact local_bound_pow_dvd hp ha N hN χ₁ χ₂ h₁ h₂

/-- `local_bound_pow_not_dvd` with the modulus named `q`. -/
private theorem local_bound_pow_not_dvd' {q p a : ℕ} (hp : p.Prime) [NeZero q] (hq : q = p ^ a)
    (ha : 2 ≤ a) (N : ℕ) (hN : ¬ p ∣ N) (χ₁ χ₂ : DirichletCharacter ℂ q)
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    ‖Aq χ₁ χ₂ (N : ℤ) q‖ ≤ eulerFactorSing N p := by
  subst hq
  exact local_bound_pow_not_dvd hp ha N hN χ₁ χ₂ h₁ h₂

/-- LEAF page 23. For primitive characters and any prime `p`, the norm of the generalized Euler
factor is at most the ordinary Euler factor. Primitivity is the hypothesis of (6.5). -/
theorem local_bound {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (N : ℕ) (hN : 1 ≤ N) (p : ℕ) (hp : p.Prime) :
    ‖eulerFactorGen χ₁ χ₂ N p‖ ≤ eulerFactorSing N p := by
  haveI : ∀ j, NeZero (p ^ j) := fun j => ⟨pow_ne_zero j hp.ne_zero⟩
  by_cases hEq : r₁ = r₂
  · subst hEq
    by_cases hpw : ∃ k, 1 ≤ k ∧ r₁ = p ^ k
    · obtain ⟨k, hk1, hk⟩ := hpw
      by_cases hk2 : 2 ≤ k
      · subst r₁
        haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
        rw [eulerFactorGen_eq_Aq_pow hp hk1 (N : ℤ) χ₁ χ₂]
        by_cases hpdvd : p ∣ N
        · exact local_bound_pow_dvd' hp rfl (by omega : 1 ≤ k) N hpdvd χ₁ χ₂ hχ₁ hχ₂
        · exact local_bound_pow_not_dvd' hp rfl hk2 N hpdvd χ₁ χ₂ hχ₁ hχ₂
      · have hk1' : k = 1 := by omega
        subst hk1'
        rw [pow_one] at hk
        subst r₁
        haveI : NeZero p := ⟨hp.ne_zero⟩
        rw [eulerFactorGen_eq_Aq_self (q := p) hp (N : ℤ) 1 le_rfl (pow_one p).symm χ₁ χ₂]
        by_cases hpdvd : p ∣ N
        · exact local_bound_pow_dvd' hp (pow_one p).symm le_rfl N hpdvd χ₁ χ₂ hχ₁ hχ₂
        · by_cases hp3 : p = 3
          · subst hp3
            exact local_bound_level_three N hN hpdvd χ₁ χ₂ hχ₁ hχ₂
          · exact local_bound_level_not_dvd hp N hN hpdvd hp3 χ₁ χ₂ hχ₁ hχ₂
    · by_cases hr1 : r₁ = 1
      · subst hr1
        rw [DirichletCharacter.level_one χ₁, DirichletCharacter.level_one χ₂]
        exact local_bound_one_one N p hp
      · have hzero : eulerFactorGen χ₁ χ₂ (N : ℤ) p = 0 := by
          unfold eulerFactorGen
          rw [tsum_eq_sum (s := (∅ : Finset ℕ)) ?_]
          · exact Finset.sum_empty
          · intro j _
            rw [dif_neg (pow_ne_zero j hp.ne_zero)]
            refine Aq_eq_zero_of_dvd_ne _ _ _ ?_
            rintro ⟨hd, -⟩
            obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hd
            rcases Nat.eq_zero_or_pos m with h0 | hpos
            · exact hr1 (by rw [hm, h0, pow_zero])
            · exact hpw ⟨m, hpos, hm⟩
        rw [hzero, norm_zero]
        exact eulerFactorSing_nonneg hp N
  · by_cases h01 : (r₁ = 1 ∧ r₂ = p) ∨ (r₁ = p ∧ r₂ = 1)
    · haveI : NeZero p := ⟨hp.ne_zero⟩
      rcases h01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1
        subst h2
        rw [DirichletCharacter.level_one χ₁, eulerFactorGen_one_prime hp (N : ℤ) χ₂]
        exact local_bound_one_level_prime hp N χ₂ hχ₂
      · subst h1
        subst h2
        rw [DirichletCharacter.level_one χ₂, eulerFactorGen_comm,
          eulerFactorGen_one_prime hp (N : ℤ) χ₁]
        exact local_bound_one_level_prime hp N χ₁ hχ₁
    · have hzero : eulerFactorGen χ₁ χ₂ (N : ℤ) p = 0 := by
        unfold eulerFactorGen
        rw [tsum_eq_sum (s := (∅ : Finset ℕ)) ?_]
        · exact Finset.sum_empty
        · intro j _
          rw [dif_neg (pow_ne_zero j hp.ne_zero)]
          rcases Nat.eq_zero_or_pos j with h0 | hpos
          · subst h0
            refine Aq_eq_zero_of_dvd_ne _ _ _ ?_
            rintro ⟨h1, h2⟩
            have h1' : r₁ = 1 := by
              have hh := h1; rw [pow_zero] at hh; exact Nat.dvd_one.mp hh
            have h2' : r₂ = 1 := by
              have hh := h2; rw [pow_zero] at hh; exact Nat.dvd_one.mp hh
            exact hEq (by rw [h1', h2'])
          · rcases Nat.lt_or_ge j 2 with hj2 | hj2
            · have hj1 : j = 1 := by omega
              subst hj1
              refine Aq_eq_zero_of_dvd_ne _ _ _ ?_
              rintro ⟨h1, h2⟩
              have h1p : r₁ ∣ p := by have hh := h1; rw [pow_one] at hh; exact hh
              have h2p : r₂ ∣ p := by have hh := h2; rw [pow_one] at hh; exact hh
              rcases (Nat.dvd_prime hp).mp h1p with h1 | h1 <;>
                rcases (Nat.dvd_prime hp).mp h2p with h2 | h2
              · exact hEq (by rw [h1, h2])
              · exact h01 (Or.inl ⟨h1, h2⟩)
              · exact h01 (Or.inr ⟨h1, h2⟩)
              · exact hEq (by rw [h1, h2])
            · by_cases hr1 : r₁ = p ^ j
              · exact Aq_pow_eq_zero_of_ne_level_right hp hj2 _ _ N
                  (fun hc => hEq (by rw [hr1, hc]))
              · exact Aq_pow_eq_zero_of_ne_level hp hj2 _ _ N hr1
      rw [hzero, norm_zero]
      exact eulerFactorSing_nonneg hp N

/-- LEAF page 23. If local factors satisfy the bound and the global series converge, then the limit norms satisfy the bound. -/
theorem prod_bound {F : ℕ → ℂ} {f : ℕ → ℝ} {L : ℂ} {l : ℝ}
    (hF : Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, F p) atTop (𝓝 L))
    (hf : Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, f p) atTop (𝓝 l))
    (h_bound : ∀ p, p.Prime → ‖F p‖ ≤ f p) : ‖L‖ ≤ l := by
  have H : ∀ X : ℕ, ‖∏ p ∈ (Finset.range X).filter Nat.Prime, F p‖ ≤ ∏ p ∈ (Finset.range X).filter Nat.Prime, f p := by
    intro X
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun p hp => h_bound p (Finset.mem_filter.mp hp).2)
  exact le_of_tendsto_of_tendsto' hF.norm hf H

/-- The assembly theorem for `bound65` (Pintz's Main Lemma on page 23). -/
theorem bound65_decomposed : Bound65 := by
  intro r₁ r₂ _ _ χ₁ χ₂ hχ₁ hχ₂ N hN
  obtain ⟨ψ₁, h₁⟩ := exists_primeComponents χ₁ hχ₁
  obtain ⟨ψ₂, h₂⟩ := exists_primeComponents χ₂ hχ₂
  exact prod_bound (euler_gen_eq χ₁ χ₂ hχ₁ hχ₂ ψ₁ ψ₂ h₁ h₂ N (by exact_mod_cast hN))
    (euler_sing_eq N hN)
    (fun p hp => local_bound (ψ₁ p) (ψ₂ p) (h₁.1 p) (h₂.1 p) N hN p hp)

end LeanLab.BhowmikGrimmelt2026
