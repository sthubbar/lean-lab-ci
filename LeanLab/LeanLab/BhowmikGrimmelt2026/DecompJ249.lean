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

/-- LEAF page 23. For primitive characters and any prime `p`, the norm of the generalized Euler
factor is at most the ordinary Euler factor. Primitivity is the hypothesis of (6.5). -/
theorem local_bound {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (N : ℕ) (hN : 1 ≤ N) (p : ℕ) (hp : p.Prime) :
    ‖eulerFactorGen χ₁ χ₂ N p‖ ≤ eulerFactorSing N p := by
  sorry

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
