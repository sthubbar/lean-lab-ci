/-
AI wrote the Lean code. Codex task324, 2026-11-09.
Yamada arXiv 1511.03409v2, printed pages 22 to 24, Lemma 7.2 eqs 99 to 104.
The two analytic leaves split the nonprincipal characters at conductor log to the tenth Y.
Their budgets record the allocations needed for the exact final assembly.
Budget324 records a QUESTION about the numerical conversion after eq 104.
The final assembly has no sorry of its own. It remains CONDITIONAL ON the two leaves.
The sealed lemma72 in Decomp1552b is unchanged. Binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.Decomp1552b
import LeanLab.PNTPort.BV.Characters
import LeanLab.PNTPort.LargeSieve.Bilinear

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.ChenExplicit.Decomp324
open D1552

/-- Weighted finite character sum for the products in Yamada page 23 eq 99. -/
def productCharSum {d : ℕ} (χ : DirichletCharacter ℂ d) (c : ℕ → ℝ)
    (X Y Z : ℝ) : ℂ :=
  ∑ n ∈ Ico 1 ⌈X⌉₊, ∑ p ∈ primesIco Z Y, (c n : ℂ) * χ (n * p : ℕ)

/-- The bilinear character sum factors into the two sums in Yamada page 23 eq 100. -/
theorem productCharSum_factor {d : ℕ} (χ : DirichletCharacter ℂ d) (c : ℕ → ℝ)
    (X Y Z : ℝ) :
    productCharSum χ c X Y Z =
      (∑ n ∈ Ico 1 ⌈X⌉₊, (c n : ℂ) * χ (n : ZMod d)) *
        ∑ p ∈ primesIco Z Y, χ (p : ZMod d) := by
  unfold productCharSum
  rw [sum_mul_sum]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro p hp
  rw [Nat.cast_mul, map_mul]
  ring

/-- Primitive character factorization for Yamada page 23 eq 100.
The exact identity retains the modulus coprimality filters. -/
theorem productCharSum_primitive {d : ℕ} (χ : DirichletCharacter ℂ d) (c : ℕ → ℝ)
    (X Y Z : ℝ) :
    productCharSum χ c X Y Z =
      (∑ n ∈ Ico 1 ⌈X⌉₊,
        if Nat.Coprime n d then (c n : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor) else 0) *
      ∑ p ∈ primesIco Z Y,
        if Nat.Coprime p d then χ.primitiveCharacter (p : ZMod χ.conductor) else 0 := by
  have hχ (n : ℕ) : χ (n : ZMod d) =
      if Nat.Coprime n d then χ.primitiveCharacter (n : ZMod χ.conductor) else 0 := by
    by_cases h : Nat.Coprime n d
    · rw [ite_eq_left h]
      have he := χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr h)
      push_cast at he
      exact he.symm
    · rw [ite_eq_right h]
      exact MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n d).mp hu))
  rw [productCharSum_factor]
  congr 1
  · apply sum_congr rfl
    intro n hn
    rw [hχ]
    split_ifs <;> simp
  · apply sum_congr rfl
    intro p hp
    exact hχ p

/-- Removing primes dividing s costs at most the number of distinct prime divisors of s. -/
theorem prime_sum_remove_divisors {d : ℕ} (χ : DirichletCharacter ℂ d)
    (s : ℕ) (hs : s ≠ 0) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ‖(∑ p ∈ P.filter (fun p => ¬ p ∣ s), χ (p : ZMod d)) -
      ∑ p ∈ P, χ (p : ZMod d)‖ ≤ (s.primeFactors.card : ℝ) := by
  have he := sum_filter_add_sum_filter_not P (fun p => p ∣ s)
    (fun p => χ (p : ZMod d))
  have hid : (∑ p ∈ P.filter (fun p => ¬ p ∣ s), χ (p : ZMod d)) -
      ∑ p ∈ P, χ (p : ZMod d) = -∑ p ∈ P.filter (fun p => p ∣ s), χ (p : ZMod d) := by
    rw [← he]
    ring
  rw [hid, norm_neg]
  have hsub : P.filter (fun p => p ∣ s) ⊆ s.primeFactors := by
    intro p hp
    obtain ⟨hpP, hps⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hP p hpP, hps, hs⟩
  calc
    _ ≤ ∑ p ∈ P.filter (fun p => p ∣ s), (1 : ℝ) :=
      norm_sum_le_of_le _ (fun p hp => DirichletCharacter.norm_le_one χ _)
    _ = ((P.filter (fun p => p ∣ s)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast card_le_card hsub

/-- Yamada page 23 eq 101: the deleted prime error over any set of characters
is at most phi of d times the number of distinct prime divisors of s. -/
theorem prime_sum_remove_divisors_sum {d : ℕ} [NeZero d]
    (A : Finset (DirichletCharacter ℂ d)) (s : ℕ) (hs : s ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ χ ∈ A, ‖(∑ p ∈ P.filter (fun p => ¬ p ∣ s), χ (p : ZMod d)) -
      ∑ p ∈ P, χ (p : ZMod d)‖ ≤ (d.totient : ℝ) * s.primeFactors.card := by
  have hcard : A.card ≤ d.totient := by
    calc
      _ ≤ Fintype.card (DirichletCharacter ℂ d) := card_le_univ _
      _ = _ := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  calc
    _ ≤ ∑ χ ∈ A, (s.primeFactors.card : ℝ) :=
      sum_le_sum (fun χ hχ => prime_sum_remove_divisors χ s hs P hP)
    _ = (A.card : ℝ) * s.primeFactors.card := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)

open LeanLab.PNTPort.LargeSieve

/-- A conductor block bound for Yamada page 24 eq 103.
This uses the existing library constant twice Q squared and a lower bound R on the conductor. -/
theorem conductor_block_le {Q : ℕ} (hQ : 1 ≤ Q) (R : ℝ) (hR : 0 < R)
    (a b : ℤ → ℂ) (M₁ M₂ : ℤ) (N₁ N₂ : ℕ) :
    (∑ i ∈ (primIdx Q).filter (fun i => R ≤ ((i.1 + 1 : ℕ) : ℝ)),
      (1 / ((i.1 + 1).totient : ℝ)) *
        ‖∑ m ∈ Ioc M₁ (M₁ + N₁), ∑ n ∈ Ioc M₂ (M₂ + N₂),
          a m * b n * i.2 ((m * n : ℤ))‖) ≤
      sqrt (((N₁ + 2 * (Q : ℝ) ^ 2) * ∑ m ∈ Ioc M₁ (M₁ + N₁), ‖a m‖ ^ 2) *
        ((N₂ + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M₂ (M₂ + N₂), ‖b n‖ ^ 2)) / R := by
  let f : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ := fun i =>
    ‖∑ m ∈ Ioc M₁ (M₁ + N₁), ∑ n ∈ Ioc M₂ (M₂ + N₂), a m * b n * i.2 ((m * n : ℤ))‖
  let S := (primIdx Q).filter (fun i => R ≤ ((i.1 + 1 : ℕ) : ℝ))
  have hf (i) : 0 ≤ f i := norm_nonneg _
  change (∑ i ∈ S, (1 / ((i.1 + 1).totient : ℝ)) * f i) ≤ _
  apply (le_div_iff₀ hR).mpr
  calc
    _ = ∑ i ∈ S, (R / ((i.1 + 1).totient : ℝ)) * f i := by
      rw [sum_mul]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ S, (((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient) * f i := by
      apply sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (hf i)
      exact div_le_div_of_nonneg_right (mem_filter.mp hi).2 (Nat.cast_nonneg _)
    _ ≤ ∑ i ∈ primIdx Q, (((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient) * f i :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i hi hnot => by positivity)
    _ ≤ _ := le_sqrt_of_sq_le (bilinear_large_sieve hQ a b M₁ M₂ N₁ N₂)

/-- Yamada page 23 eq 100: group one conductor fiber by unique primitive induction. -/
theorem conductor_fiber_sum {d r : ℕ} [NeZero d] (hr : r ∣ d)
    (f : DirichletCharacter ℂ d → ℝ) :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.conductor = r), f χ) =
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive),
        f (DirichletCharacter.changeLevel hr ψ) := by
  symm
  apply sum_bij (fun ψ hψ => DirichletCharacter.changeLevel hr ψ)
  · intro ψ hψ
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [DirichletCharacter.conductor_changeLevel]
    exact (DirichletCharacter.isPrimitive_def ψ).mp (mem_filter.mp hψ).2
  · intro ψ₁ h₁ ψ₂ h₂ he
    exact DirichletCharacter.changeLevel_injective hr he
  · intro χ hχ
    have hc := (mem_filter.mp hχ).2
    have hfact := χ.factorsThrough_conductor
    rw [hc] at hfact
    obtain ⟨hr', ψ, hψ⟩ := hfact
    have hprim : ψ.IsPrimitive := by
      change ψ.conductor = r
      rw [← DirichletCharacter.conductor_changeLevel ψ hr, ← hψ]
      exact hc
    exact ⟨ψ, mem_filter.mpr ⟨mem_univ _, hprim⟩, hψ.symm⟩
  · intro ψ hψ
    rfl

/-- Yamada page 23 eq 100: group the nonprincipal characters by conductors other than one. -/
theorem nonprincipal_sum_by_conductor (d : ℕ) [NeZero d]
    (f : DirichletCharacter ℂ d → ℝ) :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).erase 1, f χ) =
      ∑ r ∈ d.divisors.filter (fun r => r ≠ 1),
        if hr : r ∣ d then
          ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive),
            f (DirichletCharacter.changeLevel hr ψ)
        else 0 := by
  have hmaps : ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).erase 1,
      χ.conductor ∈ d.divisors.filter (fun r => r ≠ 1) := by
    intro χ hχ
    apply mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne d⟩, ?_⟩
    intro hc
    exact (mem_erase.mp hχ).1 (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hc)
  rw [← sum_fiberwise_of_maps_to hmaps f]
  apply sum_congr rfl
  intro r hr
  have hrd := (Nat.mem_divisors.mp (mem_filter.mp hr).1).1
  have hr1 := (mem_filter.mp hr).2
  rw [dite_eq_left hrd]
  have hfiber : ((univ : Finset (DirichletCharacter ℂ d)).erase 1).filter
      (fun χ => χ.conductor = r) = univ.filter (fun χ : DirichletCharacter ℂ d => χ.conductor = r) := by
    ext χ
    by_cases hc : χ.conductor = r
    · have hχ1 : χ ≠ 1 := by
        intro hχ
        rw [hχ, DirichletCharacter.conductor_one] at hc
        exact hr1 hc.symm
      simp [hc, hχ1]
    · simp [hc]
  rw [hfiber]
  exact conductor_fiber_sum hrd f

/-- The contribution from one conductor sector in Yamada eq 100.
The zero modulus contributes zero. The Boolean flag selects conductors below log to the tenth Y. -/
def sectorMass (small : Bool) (q₁ : ℕ) (c : ℕ → ℝ) (X Y Z : ℝ) : ℝ :=
  ∑ d ∈ (range ⌈√(X * Y) / log Y ^ 10⌉₊).filter (fun d => 0 < d ∧ ¬ q₁ ∣ d),
    if hd : d = 0 then 0 else
      letI : NeZero d := ⟨hd⟩
      (1 / (d.totient : ℝ)) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).erase 1,
          if (decide ((χ.conductor : ℝ) < log Y ^ 10) == small) then
            ‖productCharSum χ c X Y Z‖ else 0

/-- The zero coefficient instance has zero mass in either conductor sector. -/
theorem sectorMass_zero (small : Bool) (q₁ : ℕ) (X Y Z : ℝ) :
    sectorMass small q₁ (fun _ => 0) X Y Z = 0 := by
  unfold sectorMass
  apply sum_eq_zero
  intro d hd
  split_ifs <;> simp [productCharSum]

/-- Character orthogonality bounds a weighted residue discrepancy.
This is the finite reduction used before Yamada page 23 eq 100. -/
theorem weighted_residue_error_le {α : Type*} (s : Finset α) (m : α → ℕ) (w : α → ℝ)
    (d : ℕ) [NeZero d] (a : ℕ) (ha : Nat.Coprime a d) :
    |(∑ i ∈ s, if m i ≡ a [MOD d] then w i else 0) -
      (1 / (d.totient : ℝ)) * ∑ i ∈ s, if Nat.Coprime (m i) d then w i else 0| ≤
      (1 / (d.totient : ℝ)) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).erase 1,
          ‖∑ i ∈ s, (w i : ℂ) * χ (m i : ZMod d)‖ := by
  have hφ : (0 : ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hu : IsUnit (a : ZMod d) := (ZMod.isUnit_iff_coprime a d).mpr ha
  have horth :
      ((∑ i ∈ s, if m i ≡ a [MOD d] then w i else 0 : ℝ) : ℂ) * d.totient =
        ∑ χ : DirichletCharacter ℂ d, (starRingEnd ℂ) (χ a) *
          ∑ i ∈ s, (w i : ℂ) * χ (m i : ZMod d) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    have hterm (i : α) :
        (∑ χ : DirichletCharacter ℂ d,
          (starRingEnd ℂ) (χ a) * ((w i : ℂ) * χ (m i : ZMod d))) =
        if m i ≡ a [MOD d] then (w i : ℂ) * d.totient else 0 := by
      have hrew (χ : DirichletCharacter ℂ d) :
          (starRingEnd ℂ) (χ a) * ((w i : ℂ) * χ (m i : ZMod d)) =
            (w i : ℂ) * (χ (a : ZMod d)⁻¹ * χ (m i : ZMod d)) := by
        rw [LeanLab.PNTPort.LargeSieve.conj_char_of_isUnit χ hu]
        ring
      rw [sum_congr rfl (fun χ _ => hrew χ), ← mul_sum,
        DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu]
      by_cases hi : m i ≡ a [MOD d]
      · have he : (a : ZMod d) = m i :=
          (ZMod.natCast_eq_natCast_iff' a (m i) d).mpr hi.symm
        rw [ite_eq_left he, ite_eq_left hi]
      · have he : ¬ (a : ZMod d) = m i := by
          intro he
          exact hi ((ZMod.natCast_eq_natCast_iff' a (m i) d).mp he).symm
        rw [ite_eq_right he, ite_eq_right hi, mul_zero]
    rw [sum_congr rfl (fun i _ => hterm i)]
    push_cast
    rw [sum_mul]
    apply sum_congr rfl
    intro i hi
    split_ifs <;> simp
  have hprincipal : (∑ i ∈ s, (w i : ℂ) * (1 : DirichletCharacter ℂ d) (m i : ZMod d)) =
      ((∑ i ∈ s, if Nat.Coprime (m i) d then w i else 0 : ℝ) : ℂ) := by
    push_cast
    apply sum_congr rfl
    intro i hi
    by_cases h : Nat.Coprime (m i) d
    · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime (m i) d).mpr h), ite_eq_left h, mul_one]
    · rw [MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime (m i) d).mp hu)),
        ite_eq_right h, mul_zero]
      simp
  rw [← add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ d)),
    MulChar.one_apply hu, map_one, one_mul, hprincipal] at horth
  have hkey :
      (((∑ i ∈ s, if m i ≡ a [MOD d] then w i else 0) -
        (1 / (d.totient : ℝ)) * ∑ i ∈ s, if Nat.Coprime (m i) d then w i else 0 : ℝ) : ℂ) *
        d.totient =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).erase 1,
        (starRingEnd ℂ) (χ a) * ∑ i ∈ s, (w i : ℂ) * χ (m i : ZMod d) := by
    push_cast only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_natCast]
    have hφC : (d.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    have hcancel : ((1 : ℂ) / d.totient *
        ((∑ i ∈ s, if Nat.Coprime (m i) d then w i else 0 : ℝ) : ℂ)) * d.totient =
        ((∑ i ∈ s, if Nat.Coprime (m i) d then w i else 0 : ℝ) : ℂ) := by
      field_simp
    rw [sub_mul, hcancel, horth]
    ring
  have hn := congrArg norm hkey
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast] at hn
  conv_rhs => rw [one_div_mul_eq_div]
  rw [le_div_iff₀ hφ, hn]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro χ hχ
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

/-- Both conductor sectors together bound the residue discrepancy in Yamada eq 99. -/
theorem discrepancy_le_sectors (q₁ : ℕ) (c : ℕ → ℝ) (res : ℕ → ℕ)
    (X Y Z : ℝ) (hres : ∀ d, 0 < d → Nat.Coprime (res d) d) :
    (∑ d ∈ (range ⌈√(X * Y) / log Y ^ 10⌉₊).filter (fun d => 0 < d ∧ ¬ q₁ ∣ d),
      |∑ n ∈ Ico 1 ⌈X⌉₊, ∑ p ∈ primesIco Z Y,
          (if (n * p : ℕ) ≡ res d [MOD d] then c n else 0) -
        (1 / (d.totient : ℝ)) * ∑ n ∈ Ico 1 ⌈X⌉₊, ∑ p ∈ primesIco Z Y,
          (if Nat.Coprime (n * p) d then c n else 0)|) ≤
      sectorMass true q₁ c X Y Z + sectorMass false q₁ c X Y Z := by
  unfold sectorMass
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have hdpos := (mem_filter.mp hd).2.1
  have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
  haveI : NeZero d := ⟨hd0⟩
  simp only [dite_eq_right hd0]
  rw [← mul_add, ← sum_add_distrib]
  have hsplit (χ : DirichletCharacter ℂ d) :
      (if (decide ((χ.conductor : ℝ) < log Y ^ 10) == true) then
        ‖productCharSum χ c X Y Z‖ else 0) +
      (if (decide ((χ.conductor : ℝ) < log Y ^ 10) == false) then
        ‖productCharSum χ c X Y Z‖ else 0) = ‖productCharSum χ c X Y Z‖ := by
    by_cases h : (χ.conductor : ℝ) < log Y ^ 10 <;> simp [h]
  simp_rw [hsplit]
  have hb := weighted_residue_error_le ((Ico 1 ⌈X⌉₊).product (primesIco Z Y))
    (fun t : ℕ × ℕ => t.1 * t.2) (fun t => c t.1) d (res d) (hres d hdpos)
  simpa only [Finset.product_eq_sprod, sum_product, productCharSum] using hb

/-- LEAF. Yamada arXiv 1511.03409v2 page 23 eqs 101 and 102, with the outer s sum
on page 24 after eq 104. Choose the exceptional prime and bound only characters whose
conductor is below log to the tenth Y. The displayed budget is a derived allowance for
this sector of eq 99. It does not assert the large conductor estimate. -/
theorem small_conductor_sector (N : ℕ) (hE : Even N) (hN : exp (exp 36) < N) :
    ∃ q₁ : ℕ, D1552.Adm N q₁ ∧
      ∀ (c : ℕ → ℝ) (X Y Z : ℝ), (∀ n, |c n| ≤ 1) →
        log Y ^ 10 < X → X ≤ N / D1552.z8 N → X * Y < 2 * N →
        D1552.z8 N < Y → D1552.z8 N ≤ Z →
        sectorMass true q₁ c X Y Z ≤ exp (-146) * X * Y / log Y ^ 4 := by
  sorry

/-- LEAF. Yamada arXiv 1511.03409v2 page 24 eqs 103 and 104 and the outer s sum.
Bound only nonprincipal characters whose conductor is at least log to the tenth Y.
This bound is uniform in the omitted exceptional prime and has no residue choice. -/
theorem large_conductor_sector (N : ℕ) (hE : Even N) (hN : exp (exp 36) < N)
    (q₁ : ℕ) (c : ℕ → ℝ) (X Y Z : ℝ) (hc : ∀ n, |c n| ≤ 1)
    (hX : log Y ^ 10 < X) (hXupper : X ≤ N / D1552.z8 N)
    (hXY : X * Y < 2 * N) (hY : D1552.z8 N < Y) (hZ : D1552.z8 N ≤ Z) :
    sectorMass false q₁ c X Y Z ≤ 2 * exp (-145) * X * Y / log Y ^ 4 := by
  sorry

/-- The two sector allowances fit the Lemma 7.2 budget of Yamada page 23 eq 99. -/
theorem sector_budget (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    exp (-146) * X * Y / log Y ^ 4 + 2 * exp (-145) * X * Y / log Y ^ 4 ≤
      exp (-144) * X * Y / log Y ^ 4 := by
  have hcoef : exp (-146 : ℝ) + 2 * exp (-145 : ℝ) ≤ exp (-144 : ℝ) := by
    have he : (5 / 2 : ℝ) ≤ exp 1 := by
      have h2 := quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      norm_num at h2
      exact h2
    have he1 : exp (-145 : ℝ) = exp (-146 : ℝ) * exp 1 := by rw [← exp_add]; norm_num
    have he2 : exp (-144 : ℝ) = exp (-146 : ℝ) * exp 1 ^ 2 := by
      rw [← exp_nat_mul, ← exp_add]; norm_num
    rw [he1, he2]
    have ht : 1 + 2 * exp (1 : ℝ) ≤ exp 1 ^ 2 := by
      nlinarith [sq_nonneg (exp (1 : ℝ) - 5 / 2)]
    nlinarith only [mul_le_mul_of_nonneg_left ht (exp_nonneg (-146 : ℝ))]
  have hscale : 0 ≤ X * Y / log Y ^ 4 := by positivity
  have h := mul_le_mul_of_nonneg_right hcoef hscale
  convert h using 1 <;> ring

/-- The common size range is nonempty at X and Y equal to square root N. -/
theorem size_window (N : ℕ) (hN : exp (exp 36) < N) :
    log (sqrt (N : ℝ)) ^ 10 < sqrt (N : ℝ) ∧
      sqrt (N : ℝ) ≤ N / (N : ℝ) ^ ((1 : ℝ) / 8) ∧
      sqrt (N : ℝ) * sqrt (N : ℝ) < 2 * N ∧
      (N : ℝ) ^ ((1 : ℝ) / 8) < sqrt (N : ℝ) ∧
      (N : ℝ) ^ ((1 : ℝ) / 8) ≤ sqrt (N : ℝ) := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have h36 : (2 * (Nat.factorial 11 : ℝ)) < exp 36 := by
    have h := pow_div_factorial_le_exp 36 (by norm_num : (0 : ℝ) ≤ 36) 11
    norm_num at h ⊢
    linarith
  have hN1 : (1 : ℝ) < N := by
    have he : 1 < exp (exp (36 : ℝ)) := one_lt_exp_iff.mpr (exp_pos _)
    exact he.trans hN
  have hzpos : 0 < (N : ℝ) ^ ((1 : ℝ) / 8) := rpow_pos_of_pos hNp _
  have hspos : 0 < sqrt (N : ℝ) := sqrt_pos_of_pos hNp
  have ht : (Nat.factorial 11 : ℝ) < log (sqrt (N : ℝ)) := by
    rw [log_sqrt hNp.le]
    norm_num at h36 ⊢
    linarith only [h36, hL]
  have htpos : 0 < log (sqrt (N : ℝ)) := by
    exact (by positivity : (0 : ℝ) < Nat.factorial 11).trans ht
  have hpower : log (sqrt (N : ℝ)) ^ 10 < sqrt (N : ℝ) := by
    have he := pow_div_factorial_le_exp (log (sqrt (N : ℝ))) htpos.le 11
    rw [exp_log hspos] at he
    apply lt_of_lt_of_le _ he
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < Nat.factorial 11)).mpr
    calc
      _ < log (sqrt (N : ℝ)) ^ 10 * log (sqrt (N : ℝ)) :=
        mul_lt_mul_of_pos_left ht (pow_pos htpos 10)
      _ = _ := by ring
  have hupper : sqrt (N : ℝ) ≤ N / (N : ℝ) ^ ((1 : ℝ) / 8) := by
    apply (le_div_iff₀ hzpos).mpr
    rw [sqrt_eq_rpow, ← rpow_add hNp]
    calc
      _ ≤ (N : ℝ) ^ (1 : ℝ) :=
        rpow_le_rpow_of_exponent_le hN1.le (by norm_num)
      _ = _ := rpow_one _
  have hlow : (N : ℝ) ^ ((1 : ℝ) / 8) < sqrt (N : ℝ) := by
    rw [sqrt_eq_rpow]
    exact rpow_lt_rpow_of_exponent_lt hN1 (by norm_num)
  refine ⟨hpower, hupper, ?_, hlow, hlow.le⟩
  rw [mul_self_sqrt hNp.le]
  linarith

/-- Exact statement of the sealed lemma72, assembled from the strictly smaller sectors.
CONDITIONAL ON small_conductor_sector and large_conductor_sector. -/
theorem lemma72_from_sectors (N : ℕ) (hE : Even N) (hN : exp (exp 36) < N) :
    ∃ q₁ : ℕ, Adm N q₁ ∧ ∀ (c : ℕ → ℝ) (res : ℕ → ℕ) (X Y Z : ℝ), (∀ n, |c n| ≤ 1) →
      (∀ d, 0 < d → Nat.Coprime (res d) d) → log Y ^ 10 < X → X ≤ N / z8 N →
      X * Y < 2 * N → z8 N < Y → z8 N ≤ Z → Lemma72At q₁ c res X Y Z := by
  obtain ⟨q₁, hq, hs⟩ := small_conductor_sector N hE hN
  refine ⟨q₁, hq, ?_⟩
  intro c res X Y Z hc hres hX hXupper hXY hY hZ
  have hXp : 0 ≤ X := (by positivity : 0 ≤ log Y ^ 10).trans hX.le
  have hYp : 0 ≤ Y := (rpow_nonneg (Nat.cast_nonneg N) _).trans hY.le
  unfold Lemma72At
  calc
    _ ≤ sectorMass true q₁ c X Y Z + sectorMass false q₁ c X Y Z :=
      discrepancy_le_sectors q₁ c res X Y Z hres
    _ ≤ exp (-146) * X * Y / log Y ^ 4 + 2 * exp (-145) * X * Y / log Y ^ 4 :=
      add_le_add (hs c X Y Z hc hX hXupper hXY hY hZ)
        (large_conductor_sector N hE hN q₁ c X Y Z hc hX hXupper hXY hY hZ)
    _ ≤ _ := sector_budget X Y hXp hYp

end LeanLab.ChenExplicit.Decomp324
