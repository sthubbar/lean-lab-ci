/-
Supply for the finite smooth expansion in Decomp247a.
Source: Pintz Part I pages 19 and 20 displays 7.10 to 7.14.
Separate the finite character coefficient identity from summation over exponent vectors.
The tensor summation induction adapts Michael Stoll's Mathlib EulerProduct.Basic proof.
That source is copyright 2023 Michael Stoll and licensed under Apache 2.0.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp436a
import LeanLab.BhowmikGrimmelt2026.AqCRT443

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- Adjoining a new prime splits the tensor of local prime power coefficients.
Source: exponent bookkeeping for Pintz page 20 display 7.14. -/
theorem factored_tensor_split436 (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime)
    {p : ℕ} (hp : p.Prime) (hps : p ∉ s) (f : ℕ → ℕ → ℂ)
    {m : ℕ} (hm : m ∈ Nat.factoredNumbers s) (k : ℕ) :
    (∏ l ∈ insert p s, f l ((p ^ k * m).factorization l)) =
      f p k * ∏ l ∈ s, f l (m.factorization l) := by
  have hpm : ¬ p ∣ m := by
    intro hd
    exact hps (hm.2 p ((Nat.mem_primeFactorsList hm.1).mpr ⟨hp, hd⟩))
  rw [Finset.prod_insert hps]
  have hep : (p ^ k * m).factorization p = k := by
    rw [Nat.factorization_mul (pow_ne_zero k hp.ne_zero) hm.1, Finsupp.add_apply,
      Nat.factorization_pow_self hp, Nat.factorization_eq_zero_of_not_dvd hpm, add_zero]
  rw [hep]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  congr 1
  have hne : l ≠ p := by rintro rfl; exact hps hl
  rw [Nat.factorization_mul (pow_ne_zero k hp.ne_zero) hm.1, Finsupp.add_apply,
    Nat.factorization_pow]
  simp [hp.factorization, Finsupp.single_apply, hne, Ne.symm hne]

/-- Absolutely summable local sequences expand over numbers with the given prime factors.
No local sequence is required to have zeroth term one.
Source: finite prime expansion in Pintz page 20 display 7.14. -/
theorem factored_tensor_hasSum436 (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime)
    (f : ℕ → ℕ → ℂ) (hsum : ∀ p ∈ s, Summable (fun k => ‖f p k‖)) :
    Summable (fun m : Nat.factoredNumbers s => ‖∏ p ∈ s, f p (m.val.factorization p)‖) ∧
      HasSum (fun m : Nat.factoredNumbers s => ∏ p ∈ s, f p (m.val.factorization p))
        (∏ p ∈ s, ∑' k : ℕ, f p k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Nat.factoredNumbers_empty]
    simp only [Finset.prod_empty, norm_one]
    exact ⟨(Set.finite_singleton 1).summable (fun _ => (1 : ℝ)), hasSum_singleton 1 (fun _ => (1 : ℂ))⟩
  | @insert p s hps ih =>
    have hp := hprime p (Finset.mem_insert_self p s)
    have hpr : ∀ l ∈ s, l.Prime := fun l hl => hprime l (Finset.mem_insert_of_mem hl)
    have hsr : ∀ l ∈ s, Summable (fun k => ‖f l k‖) :=
      fun l hl => hsum l (Finset.mem_insert_of_mem hl)
    obtain ⟨hiNorm, hiSum⟩ := ih hpr hsr
    have hpSum := hsum p (Finset.mem_insert_self p s)
    have hterm (x : ℕ × Nat.factoredNumbers s) :
        (∏ l ∈ insert p s, f l ((p ^ x.1 * x.2.val).factorization l)) =
          f p x.1 * ∏ l ∈ s, f l (x.2.val.factorization l) :=
      factored_tensor_split436 s hpr hp hps f x.2.property x.1
    constructor
    · rw [← (Nat.equivProdNatFactoredNumbers hp hps).summable_iff]
      simp only [Function.comp_def, Nat.equivProdNatFactoredNumbers_apply']
      simpa only [hterm] using hpSum.mul_norm hiNorm
    · rw [Finset.prod_insert hps, ← (Nat.equivProdNatFactoredNumbers hp hps).hasSum_iff]
      simp only [Function.comp_def, Nat.equivProdNatFactoredNumbers_apply']
      have : T3Space ℂ := instT3Space
      simp_rw [hterm]
      apply hpSum.of_norm.hasSum.mul hiSum
      exact (hpSum.mul_norm hiNorm).of_norm

/-- The new coefficient majorant makes every prime power subsequence absolutely summable.
Source: Pintz page 20 display 7.13, before finite prime expansion.
CONDITIONAL ON twisted_fiber_bound436. -/
theorem component_power_summable436 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (N : ℤ) (hN : 1 ≤ N) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => ‖aqZero247 χ₁ χ₂ N (p ^ k)‖) := by
  obtain ⟨C, hC, hc⟩ := aqZero247_totient_supply436 χ₁ χ₂ hχ₁ hχ₂ N hN
  have hs := aqZero247_norm_summable_of_bound χ₁ χ₂ N C hC hc
  exact hs.comp_injective (Nat.pow_right_injective hp.two_le)

private lemma compLevel_dvd' (r p : ℕ) [NeZero r] : compLevel r p ∣ r := by
  by_cases hp : p.Prime
  · exact (Nat.Prime.pow_dvd_iff_le_factorization hp (NeZero.ne r)).mpr le_rfl
  · simp [compLevel, Nat.factorization_eq_zero_of_not_prime r hp]

private lemma compLevel_eq_one_of_not_dvd {r p : ℕ} [NeZero r] (h : ¬ p ∣ r) :
    compLevel r p = 1 := by
  rw [compLevel, Nat.factorization_eq_zero_of_not_dvd h, pow_zero]

private lemma one_lt_compLevel {r p : ℕ} [NeZero r] (hp : p.Prime) (h : p ∣ r) :
    1 < compLevel r p := by
  have hpos : 0 < r.factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hp (NeZero.ne r)).mp h
  calc 1 < p := hp.one_lt
    _ ≤ p ^ r.factorization p := Nat.le_self_pow (by omega) p

private lemma compLevel_ne_one_of_dvd {r p : ℕ} [NeZero r] (hp : p.Prime) (h : p ∣ r) :
    compLevel r p ≠ 1 := by
  have h := one_lt_compLevel hp h
  omega

private lemma val_zmod_one (a : ZMod 1) : a.val = 0 := by
  have h : a = 0 := Subsingleton.elim _ _
  rw [h]
  exact ZMod.val_zero

private lemma one_apply_zmod_one (a : ZMod 1) : (1 : DirichletCharacter ℂ 1) a = 1 := by
  have h : a = ((1 : (ZMod 1)ˣ) : ZMod 1) := Subsingleton.elim _ _
  rw [h]
  exact MulChar.one_apply_coe 1

private lemma tauConj_one_level_one : tauConj (1 : DirichletCharacter ℂ 1) = 1 := by
  simp [tauConj, one_apply_zmod_one, val_zmod_one, ee]

private lemma cChi_one_level_one (N : ℤ) : cChi (1 : DirichletCharacter ℂ 1) N = 1 := by
  simp [cChi, one_apply_zmod_one, val_zmod_one, ee]

private lemma Aq_one_arg_one {r₁ r₂ : ℕ} (h₁ : r₁ = 1) (h₂ : r₂ = 1) (N : ℤ) :
    Aq (1 : DirichletCharacter ℂ r₁) (1 : DirichletCharacter ℂ r₂) N 1 = 1 := by
  subst h₁
  subst h₂
  rw [Aq, dif_pos (show (1 : ℕ) ∣ 1 ∧ (1 : ℕ) ∣ 1 from ⟨one_dvd 1, one_dvd 1⟩)]
  simp [tauConj_one_level_one, cChi_one_level_one]

private lemma aqZero247_eq_Aq {r₁ r₂ : ℕ} (χ₁ : DirichletCharacter ℂ r₁)
    (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ) {q : ℕ} [NeZero q] :
    aqZero247 χ₁ χ₂ N q = Aq χ₁ χ₂ N q := by
  simp [aqZero247, NeZero.ne q]

private lemma aqZero247_arg_one_eq_one {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (N : ℤ) {p : ℕ} (h₁ : ¬ p ∣ r₁) (h₂ : ¬ p ∣ r₂) :
    aqZero247 (ψ₁ p) (ψ₂ p) N (p ^ 0) = 1 := by
  have e₁ : compLevel r₁ p = 1 := compLevel_eq_one_of_not_dvd h₁
  have e₂ : compLevel r₂ p = 1 := compLevel_eq_one_of_not_dvd h₂
  haveI : Subsingleton (DirichletCharacter ℂ (compLevel r₁ p)) := by
    rw [e₁]; infer_instance
  haveI : Subsingleton (DirichletCharacter ℂ (compLevel r₂ p)) := by
    rw [e₂]; infer_instance
  rw [Subsingleton.elim (ψ₁ p) 1, Subsingleton.elim (ψ₂ p) 1, pow_zero]
  have hone : aqZero247 (1 : DirichletCharacter ℂ (compLevel r₁ p))
      (1 : DirichletCharacter ℂ (compLevel r₂ p)) N 1
      = Aq (1 : DirichletCharacter ℂ (compLevel r₁ p))
          (1 : DirichletCharacter ℂ (compLevel r₂ p)) N 1 := by
    rw [aqZero247, dif_neg one_ne_zero]
  rw [hone]
  exact Aq_one_arg_one e₁ e₂ N

private lemma aqZero247_eq_local {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (N : ℤ) {p k : ℕ} (hp : p.Prime) [NeZero (p ^ k)]
    (h₁ : compLevel r₁ p ∣ p ^ k) (h₂ : compLevel r₂ p ∣ p ^ k) :
    aqZero247 (ψ₁ p) (ψ₂ p) N (p ^ k) =
      Aq (DirichletCharacter.changeLevel h₁ (ψ₁ p))
        (DirichletCharacter.changeLevel h₂ (ψ₂ p)) N (p ^ k) := by
  have hne : p ^ k ≠ 0 := NeZero.ne (p ^ k)
  symm
  rw [Aq, dif_pos (show p ^ k ∣ p ^ k ∧ p ^ k ∣ p ^ k from ⟨dvd_rfl, dvd_rfl⟩)]
  rw [aqZero247, dif_neg hne, Aq,
    dif_pos (show compLevel r₁ p ∣ p ^ k ∧ compLevel r₂ p ∣ p ^ k from ⟨h₁, h₂⟩)]
  simp only [DirichletCharacter.changeLevel_self]

private lemma factor_insert_eq {s : Finset ℕ} {p : ℕ} {e : ℕ → ℕ}
    {Ψ : ∀ q : ℕ, DirichletCharacter ℂ (q ^ e q)} {q : ℕ} (hq : q ∈ s) :
    (if h : q ^ e q ∣ p ^ e p * ∏ r ∈ s, r ^ e r then
        DirichletCharacter.changeLevel h (Ψ q) else 1) =
      DirichletCharacter.changeLevel (Nat.dvd_mul_left (∏ r ∈ s, r ^ e r) (p ^ e p))
        (if h : q ^ e q ∣ ∏ r ∈ s, r ^ e r then
          DirichletCharacter.changeLevel h (Ψ q) else 1) := by
  have hq' : q ^ e q ∣ ∏ r ∈ s, r ^ e r := Finset.dvd_prod_of_mem _ hq
  rw [dif_pos hq', dif_pos (hq'.trans (Nat.dvd_mul_left _ _)),
    ← DirichletCharacter.changeLevel_trans (Ψ q) hq'
      (Nat.dvd_mul_left (∏ r ∈ s, r ^ e r) (p ^ e p))]

private lemma prod_insert_changeLevel {s : Finset ℕ} {p : ℕ} (hps : p ∉ s) (e : ℕ → ℕ)
    (Ψ : ∀ q : ℕ, DirichletCharacter ℂ (q ^ e q)) :
    (∏ q ∈ insert p s, if h : q ^ e q ∣ p ^ e p * ∏ r ∈ s, r ^ e r then
        DirichletCharacter.changeLevel h (Ψ q) else 1) =
      DirichletCharacter.changeLevel (Nat.dvd_mul_right (p ^ e p) (∏ r ∈ s, r ^ e r)) (Ψ p) *
        DirichletCharacter.changeLevel (Nat.dvd_mul_left (∏ r ∈ s, r ^ e r) (p ^ e p))
          (∏ q ∈ s, if h : q ^ e q ∣ ∏ r ∈ s, r ^ e r then
            DirichletCharacter.changeLevel h (Ψ q) else 1) := by
  rw [Finset.prod_insert hps]
  have hpp : (if h : p ^ e p ∣ p ^ e p * ∏ r ∈ s, r ^ e r then
      DirichletCharacter.changeLevel h (Ψ p) else 1) =
      DirichletCharacter.changeLevel (Nat.dvd_mul_right (p ^ e p) (∏ r ∈ s, r ^ e r)) (Ψ p) :=
    dif_pos (Nat.dvd_mul_right _ _)
  rw [hpp, Finset.prod_congr rfl (fun q hq => factor_insert_eq (e := e) (Ψ := Ψ) hq)]
  congr 1
  exact (map_prod (DirichletCharacter.changeLevel
    (Nat.dvd_mul_left (∏ r ∈ s, r ^ e r) (p ^ e p)))
    (fun q => if h : q ^ e q ∣ ∏ r ∈ s, r ^ e r then
      DirichletCharacter.changeLevel h (Ψ q) else 1) s).symm

private theorem Aq_prod_prime_pow (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (e : ℕ → ℕ)
    (he : ∀ p ∈ s, 0 < e p) (Ψ₁ Ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (p ^ e p)) (N : ℤ) :
    ∀ (M : ℕ) [NeZero M], M = ∏ r ∈ s, r ^ e r →
      Aq (∏ q ∈ s, if h : q ^ e q ∣ M then
            DirichletCharacter.changeLevel h (Ψ₁ q) else 1)
         (∏ q ∈ s, if h : q ^ e q ∣ M then
            DirichletCharacter.changeLevel h (Ψ₂ q) else 1)
         N M =
        ∏ q ∈ s, aqZero247 (Ψ₁ q) (Ψ₂ q) N (q ^ e q) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro M _ hM
      subst hM
      have h1 : Aq (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) N 1 = 1 :=
        Aq_one_arg_one rfl rfl N
      show Aq (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) N 1 = 1
      exact h1
  | @insert p s hps ih =>
      intro M _ hM
      have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hpp : p.Prime := hs p (Finset.mem_insert_self p s)
      have hps' : ∀ q ∈ s, 0 < e q := fun q hq => he q (Finset.mem_insert_of_mem hq)
      haveI : NeZero (∏ r ∈ s, r ^ e r) := ⟨by
        rw [Finset.prod_ne_zero_iff]
        intro r hr
        exact pow_ne_zero _ (hsp r hr).ne_zero⟩
      haveI : NeZero (p ^ e p) := ⟨pow_ne_zero _ hpp.ne_zero⟩
      have ihs := ih hsp hps' (∏ r ∈ s, r ^ e r) rfl
      have hM' : M = p ^ e p * ∏ r ∈ s, r ^ e r := by
        rw [hM, Finset.prod_insert hps]
      subst hM'
      have hcop : (p ^ e p).Coprime (∏ r ∈ s, r ^ e r) := by
        refine Nat.Coprime.prod_right (fun q hq => ?_)
        exact Nat.Coprime.pow (e p) (e q)
          ((Nat.coprime_primes hpp (hsp q hq)).mpr (by rintro rfl; exact hps hq))
      rw [prod_insert_changeLevel hps e Ψ₁, prod_insert_changeLevel hps e Ψ₂,
        Finset.prod_insert hps,
        aqZero247_eq_Aq (Ψ₁ p) (Ψ₂ p) N,
        ← ihs,
        Aq_crt443 (m := p ^ e p) (n := ∏ r ∈ s, r ^ e r) hcop]

private lemma changeLevel_eq_prod_components {r n : ℕ} [NeZero r] [NeZero n]
    (χ : DirichletCharacter ℂ r) (ψ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r p))
    (hψ : IsPrimeComponents χ ψ) (hd : r ∣ n) :
    DirichletCharacter.changeLevel hd χ =
      ∏ p ∈ r.primeFactors,
        DirichletCharacter.changeLevel ((compLevel_dvd' r p).trans hd) (ψ p) := by
  classical
  apply MulChar.ext
  intro u
  let ev : DirichletCharacter ℂ n →* ℂ :=
    { toFun := fun η => η u
      map_one' := MulChar.one_apply_coe u
      map_mul' := fun a b => MulChar.mul_apply a b u }
  have he : (∏ p ∈ r.primeFactors,
      DirichletCharacter.changeLevel ((compLevel_dvd' r p).trans hd) (ψ p)) u =
      ∏ p ∈ r.primeFactors,
        (DirichletCharacter.changeLevel ((compLevel_dvd' r p).trans hd) (ψ p)) u :=
    map_prod ev _ _
  rw [he, DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.cast_eq_val]
  have hu : (u : ZMod n).val.Coprime r :=
    (ZMod.val_coe_unit_coprime u).of_dvd_right hd
  rw [hψ.2 _ hu]
  apply Finset.prod_congr rfl
  intro p hp
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.cast_eq_val]

private lemma changeLevel_eq_prod_primeFactors {r n : ℕ} [NeZero r] [NeZero n]
    (χ : DirichletCharacter ℂ r) (ψ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r p))
    (hψ : IsPrimeComponents χ ψ) (hd : r ∣ n) :
    DirichletCharacter.changeLevel hd χ =
      ∏ p ∈ n.primeFactors,
        DirichletCharacter.changeLevel ((compLevel_dvd' r p).trans hd) (ψ p) := by
  rw [changeLevel_eq_prod_components χ ψ hψ hd]
  refine Finset.prod_subset ?_ ?_
  · intro p hp
    obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hpp, hdvd.trans hd, NeZero.ne n⟩
  · intro x hx hx'
    have hxr : ¬ x ∣ r := fun h => hx' (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hx).1, h, NeZero.ne r⟩)
    have e : compLevel r x = 1 := compLevel_eq_one_of_not_dvd hxr
    haveI : Subsingleton (DirichletCharacter ℂ (compLevel r x)) := by rw [e]; infer_instance
    rw [Subsingleton.elim (ψ x) 1]
    exact DirichletCharacter.changeLevel_one _

private lemma component_product_zero_left {r₁ r₂ q : ℕ} [NeZero r₁] [NeZero r₂] [NeZero q]
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (N : ℤ) (X : ℕ) (hX : r₁ < X) (hbad : ¬ r₁ ∣ q) :
    (∏ p ∈ (Finset.range X).filter Nat.Prime,
      aqZero247 (ψ₁ p) (ψ₂ p) N (p ^ q.factorization p)) = 0 := by
  classical
  have hn : ¬ r₁.factorization ≤ q.factorization := fun h =>
    hbad ((Nat.factorization_le_iff_dvd (NeZero.ne r₁) (NeZero.ne q)).mp h)
  change ¬ ∀ p, r₁.factorization p ≤ q.factorization p at hn
  obtain ⟨p, hp⟩ := not_forall.mp hn
  have hlt : q.factorization p < r₁.factorization p := lt_of_not_ge hp
  have hprime : p.Prime := by
    by_contra h
    rw [Nat.factorization_eq_zero_of_not_prime r₁ h] at hlt
    omega
  have hdvd : p ∣ r₁ := Nat.dvd_of_factorization_pos (by omega)
  have hpX : p < X := lt_of_le_of_lt
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne r₁)) hdvd) hX
  have hlocal : ¬ compLevel r₁ p ∣ p ^ q.factorization p := by
    rw [compLevel, Nat.pow_dvd_pow_iff_le_right hprime.one_lt]
    omega
  refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpX, hprime⟩) ?_
  exact aqZero247_eq_zero_of_not_lcm_dvd (ψ₁ p) (ψ₂ p) N _
    (fun h => hlocal ((Nat.dvd_lcm_left _ _).trans h))

private lemma component_product_zero_right {r₁ r₂ q : ℕ} [NeZero r₁] [NeZero r₂] [NeZero q]
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (N : ℤ) (X : ℕ) (hX : r₂ < X) (hbad : ¬ r₂ ∣ q) :
    (∏ p ∈ (Finset.range X).filter Nat.Prime,
      aqZero247 (ψ₁ p) (ψ₂ p) N (p ^ q.factorization p)) = 0 := by
  classical
  have hn : ¬ r₂.factorization ≤ q.factorization := fun h =>
    hbad ((Nat.factorization_le_iff_dvd (NeZero.ne r₂) (NeZero.ne q)).mp h)
  change ¬ ∀ p, r₂.factorization p ≤ q.factorization p at hn
  obtain ⟨p, hp⟩ := not_forall.mp hn
  have hlt : q.factorization p < r₂.factorization p := lt_of_not_ge hp
  have hprime : p.Prime := by
    by_contra h
    rw [Nat.factorization_eq_zero_of_not_prime r₂ h] at hlt
    omega
  have hdvd : p ∣ r₂ := Nat.dvd_of_factorization_pos (by omega)
  have hpX : p < X := lt_of_le_of_lt
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne r₂)) hdvd) hX
  have hlocal : ¬ compLevel r₂ p ∣ p ^ q.factorization p := by
    rw [compLevel, Nat.pow_dvd_pow_iff_le_right hprime.one_lt]
    omega
  refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpX, hprime⟩) ?_
  exact aqZero247_eq_zero_of_not_lcm_dvd (ψ₁ p) (ψ₂ p) N _
    (fun h => hlocal ((Nat.dvd_lcm_right _ _).trans h))

/-- LEAF. Pintz Part I pages 19 and 20 displays 7.10 to 7.14.
OPEN finite CRT character identity with cancellation of the two Gauss phases
against the twisted Ramanujan phase. Every conductor prime is included.
This is one coefficient identity and contains no infinite sum or limit. -/
theorem aq_component_identity436 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : IsPrimeComponents χ₁ ψ₁) (h₂ : IsPrimeComponents χ₂ ψ₂)
    (N : ℤ) (hN : 1 ≤ N) (X : ℕ) (hX₁ : r₁ < X) (hX₂ : r₂ < X)
    (q : X.smoothNumbers) :
    aqZero247 χ₁ χ₂ N q = ∏ p ∈ (Finset.range X).filter Nat.Prime,
      aqZero247 (ψ₁ p) (ψ₂ p) N (p ^ q.val.factorization p) := by
  classical
  obtain ⟨hq0, hqX⟩ := q.property
  haveI : NeZero q.val := ⟨hq0⟩
  by_cases hd : r₁ ∣ q.val ∧ r₂ ∣ q.val
  · have hpf : ∀ p ∈ q.val.primeFactors, p.Prime :=
      fun p hp => (Nat.mem_primeFactors.mp hp).1
    have hfac₁ : r₁.factorization ≤ q.val.factorization :=
      (Nat.factorization_le_iff_dvd (NeZero.ne r₁) (NeZero.ne q.val)).mpr hd.1
    have hfac₂ : r₂.factorization ≤ q.val.factorization :=
      (Nat.factorization_le_iff_dvd (NeZero.ne r₂) (NeZero.ne q.val)).mpr hd.2
    have hlev₁ : ∀ p ∈ q.val.primeFactors, compLevel r₁ p ∣ p ^ q.val.factorization p := by
      intro p hp
      rw [compLevel, Nat.pow_dvd_pow_iff_le_right (hpf p hp).one_lt]
      exact hfac₁ p
    have hlev₂ : ∀ p ∈ q.val.primeFactors, compLevel r₂ p ∣ p ^ q.val.factorization p := by
      intro p hp
      rw [compLevel, Nat.pow_dvd_pow_iff_le_right (hpf p hp).one_lt]
      exact hfac₂ p
    have hposg : ∀ p ∈ q.val.primeFactors, 0 < q.val.factorization p := by
      intro p hp
      exact Nat.Prime.factorization_pos_of_dvd (hpf p hp) hq0
        (Nat.dvd_of_mem_primeFactors hp)
    set Ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (p ^ q.val.factorization p) :=
      fun p => if h : compLevel r₁ p ∣ p ^ q.val.factorization p then
        DirichletCharacter.changeLevel h (ψ₁ p) else 1 with hΨ₁
    set Ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (p ^ q.val.factorization p) :=
      fun p => if h : compLevel r₂ p ∣ p ^ q.val.factorization p then
        DirichletCharacter.changeLevel h (ψ₂ p) else 1 with hΨ₂
    set Ξ₁ : DirichletCharacter ℂ q.val :=
      ∏ p ∈ q.val.primeFactors, if h : compLevel r₁ p ∣ q.val then
        DirichletCharacter.changeLevel h (ψ₁ p) else 1 with hΞ₁def
    set Ξ₂ : DirichletCharacter ℂ q.val :=
      ∏ p ∈ q.val.primeFactors, if h : compLevel r₂ p ∣ q.val then
        DirichletCharacter.changeLevel h (ψ₂ p) else 1 with hΞ₂def
    have hΞ₁ : DirichletCharacter.changeLevel hd.1 χ₁ = Ξ₁ := by
      rw [hΞ₁def, changeLevel_eq_prod_primeFactors χ₁ ψ₁ h₁ hd.1]
      refine Finset.prod_congr rfl (fun p hp => ?_)
      rw [dif_pos ((compLevel_dvd' r₁ p).trans hd.1)]
    have hΞ₂ : DirichletCharacter.changeLevel hd.2 χ₂ = Ξ₂ := by
      rw [hΞ₂def, changeLevel_eq_prod_primeFactors χ₂ ψ₂ h₂ hd.2]
      refine Finset.prod_congr rfl (fun p hp => ?_)
      rw [dif_pos ((compLevel_dvd' r₂ p).trans hd.2)]
    have hcomp₁ : (∏ p ∈ q.val.primeFactors, if h : p ^ q.val.factorization p ∣ q.val then
          DirichletCharacter.changeLevel h (Ψ₁ p) else 1) = Ξ₁ := by
      rw [hΞ₁def]
      refine Finset.prod_congr rfl (fun p hp => ?_)
      have e₁ : Ψ₁ p = DirichletCharacter.changeLevel (hlev₁ p hp) (ψ₁ p) := by
        rw [hΨ₁]
        exact dif_pos (hlev₁ p hp)
      rw [e₁, dif_pos ((Nat.Prime.pow_dvd_iff_le_factorization (hpf p hp) hq0).mpr le_rfl),
        dif_pos ((compLevel_dvd' r₁ p).trans hd.1),
        ← DirichletCharacter.changeLevel_trans (ψ₁ p) (hlev₁ p hp)
          ((Nat.Prime.pow_dvd_iff_le_factorization (hpf p hp) hq0).mpr le_rfl)]
    have hcomp₂ : (∏ p ∈ q.val.primeFactors, if h : p ^ q.val.factorization p ∣ q.val then
          DirichletCharacter.changeLevel h (Ψ₂ p) else 1) = Ξ₂ := by
      rw [hΞ₂def]
      refine Finset.prod_congr rfl (fun p hp => ?_)
      have e₂ : Ψ₂ p = DirichletCharacter.changeLevel (hlev₂ p hp) (ψ₂ p) := by
        rw [hΨ₂]
        exact dif_pos (hlev₂ p hp)
      rw [e₂, dif_pos ((Nat.Prime.pow_dvd_iff_le_factorization (hpf p hp) hq0).mpr le_rfl),
        dif_pos ((compLevel_dvd' r₂ p).trans hd.2),
        ← DirichletCharacter.changeLevel_trans (ψ₂ p) (hlev₂ p hp)
          ((Nat.Prime.pow_dvd_iff_le_factorization (hpf p hp) hq0).mpr le_rfl)]
    have hmain : aqZero247 χ₁ χ₂ N q.val =
        ∏ p ∈ q.val.primeFactors,
          aqZero247 (ψ₁ p) (ψ₂ p) N (p ^ q.val.factorization p) := by
      rw [aqZero247_eq_Aq]
      have hMM : q.val = ∏ r ∈ q.val.primeFactors, r ^ q.val.factorization r :=
        Nat.prod_primeFactors_pow_factorization hq0
      have key := Aq_prod_prime_pow (s := q.val.primeFactors) hpf
        (fun p => q.val.factorization p) hposg Ψ₁ Ψ₂ N q.val hMM
      rw [hcomp₁, hcomp₂] at key
      have hcongr : Aq χ₁ χ₂ N q.val = Aq Ξ₁ Ξ₂ N q.val := by
        rw [Aq, Aq, dif_pos hd, dif_pos (show q.val ∣ q.val ∧ q.val ∣ q.val from
          ⟨dvd_rfl, dvd_rfl⟩), hΞ₁, hΞ₂]
        simp only [DirichletCharacter.changeLevel_self]
      rw [hcongr]
      refine key.trans (Finset.prod_congr rfl (fun p hp => ?_))
      haveI : NeZero (p ^ q.val.factorization p) := ⟨pow_ne_zero _ (hpf p hp).ne_zero⟩
      have e₁ : Ψ₁ p = DirichletCharacter.changeLevel (hlev₁ p hp) (ψ₁ p) := by
        rw [hΨ₁]
        exact dif_pos (hlev₁ p hp)
      have e₂ : Ψ₂ p = DirichletCharacter.changeLevel (hlev₂ p hp) (ψ₂ p) := by
        rw [hΨ₂]
        exact dif_pos (hlev₂ p hp)
      rw [e₁, e₂]
      exact (aqZero247_eq_Aq (DirichletCharacter.changeLevel (hlev₁ p hp) (ψ₁ p))
        (DirichletCharacter.changeLevel (hlev₂ p hp) (ψ₂ p)) N).trans
        (aqZero247_eq_local ψ₁ ψ₂ N (hpf p hp) (hlev₁ p hp) (hlev₂ p hp)).symm
    rw [hmain]
    refine Finset.prod_subset ?_ ?_
    · intro p hp
      obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (hqX p ((Nat.mem_primeFactorsList hq0).mpr ⟨hpp, hpdvd⟩)), hpp⟩
    · intro p hp hpn
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      have hpdvd : ¬ p ∣ q.val := fun h =>
        hpn (Nat.mem_primeFactors.mpr ⟨hpp, h, hq0⟩)
      rw [Nat.factorization_eq_zero_of_not_dvd hpdvd]
      exact aqZero247_arg_one_eq_one ψ₁ ψ₂ N
        (fun h => hpdvd (h.trans hd.1)) (fun h => hpdvd (h.trans hd.2))
  · rw [aqZero247_eq_zero_of_not_lcm_dvd χ₁ χ₂ N q.val
      (fun h => hd (Nat.lcm_dvd_iff.mp h))]
    by_cases hb₁ : r₁ ∣ q.val
    · exact (component_product_zero_right ψ₁ ψ₂ N X hX₂
        (fun h => hd ⟨hb₁, h⟩)).symm
    · exact (component_product_zero_left ψ₁ ψ₂ N X hX₁ hb₁).symm

/-- Exact aqZero247_smooth_expansion statement from the smaller CRT identity and local sums.
CONDITIONAL ON twisted_fiber_bound436 and aq_component_identity436.
Source: Pintz page 20 display 7.14. No old smooth expansion leaf is used. -/
theorem aqZero247_smooth_supply436 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : IsPrimeComponents χ₁ ψ₁) (h₂ : IsPrimeComponents χ₂ ψ₂)
    (N : ℤ) (hN : 1 ≤ N) (X : ℕ) (hX₁ : r₁ < X) (hX₂ : r₂ < X) :
    ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorGen (ψ₁ p) (ψ₂ p) N p =
      ∑' q : X.smoothNumbers, aqZero247 χ₁ χ₂ N q := by
  let s := (Finset.range X).filter Nat.Prime
  let f : ℕ → ℕ → ℂ := fun p k => aqZero247 (ψ₁ p) (ψ₂ p) N (p ^ k)
  have hs : ∀ p ∈ s, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hsum : ∀ p ∈ s, Summable (fun k => ‖f p k‖) := fun p hp =>
    component_power_summable436 (ψ₁ p) (ψ₂ p) (h₁.1 p) (h₂.1 p) N hN (hs p hp)
  have h := (factored_tensor_hasSum436 s hs f hsum).2.tsum_eq
  have hsets : Nat.factoredNumbers s = X.smoothNumbers := by
    simpa [s, Nat.primesBelow] using (Nat.smoothNumbers_eq_factoredNumbers_primesBelow X).symm
  have hlocal (p : ℕ) : (∑' k : ℕ, f p k) = eulerFactorGen (ψ₁ p) (ψ₂ p) N p := by
    rfl
  simp_rw [hlocal] at h
  rw [hsets] at h
  rw [← h]
  apply tsum_congr
  intro q
  exact (aq_component_identity436 χ₁ χ₂ hχ₁ hχ₂ ψ₁ ψ₂ h₁ h₂ N hN X hX₁ hX₂ q).symm

/-- Exact original euler_gen_eq statement from the two smaller arithmetic leaves.
CONDITIONAL ON twisted_fiber_bound436 and aq_component_identity436.
Source: Pintz pages 19 and 20 displays 7.13 to 7.15. -/
theorem euler_gen_eq_supply436 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : IsPrimeComponents χ₁ ψ₁) (h₂ : IsPrimeComponents χ₂ ψ₂) (N : ℤ) (hN : 1 ≤ N) :
    Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorGen (ψ₁ p) (ψ₂ p) N p)
      atTop (𝓝 (genSing χ₁ χ₂ N)) := by
  obtain ⟨C, hC, hc⟩ := aqZero247_totient_supply436 χ₁ χ₂ hχ₁ hχ₂ N hN
  have hsum := (aqZero247_norm_summable_of_bound χ₁ χ₂ N C hC hc).of_norm
  apply (aqZero247_smooth_tendsto χ₁ χ₂ N hsum).congr'
  filter_upwards [eventually_gt_atTop r₁, eventually_gt_atTop r₂] with X hX₁ hX₂
  exact (aqZero247_smooth_supply436 χ₁ χ₂ hχ₁ hχ₂ ψ₁ ψ₂ h₁ h₂ N hN X hX₁ hX₂).symm

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.factored_tensor_split436
#print axioms LeanLab.BhowmikGrimmelt2026.factored_tensor_hasSum436
#print axioms LeanLab.BhowmikGrimmelt2026.component_power_summable436
#print axioms LeanLab.BhowmikGrimmelt2026.aq_component_identity436
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_smooth_supply436

#print axioms LeanLab.BhowmikGrimmelt2026.euler_gen_eq_supply436
