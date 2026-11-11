import Mathlib

/-!
# Kaplan and Polo, A Goldbach theorem for Laurent series semidomains

Statements of the main results of Nathan Kaplan and Harold Polo,
"A Goldbach theorem for Laurent series semidomains", arXiv 2312.14888v2, 17 pages,
dated 18 Nov 2025.

A semidomain is a subsemiring of an integral domain (Definition 2.1, p.4), so we work with
`S : Subsemiring R` for an integral domain `R`. The Laurent polynomial semiring `S[x^{±1}]` is
Mathlib's `LaurentPolynomial S` and the semiring `S⟦x^{±1}⟧` of Laurent series with finitely many
negative terms is Mathlib's `LaurentSeries S = HahnSeries ℤ S` (a Hahn series over `ℤ` has
well founded support, that is, finitely many negative terms).

A multiplicative irreducible (atom of the monoid `S* = S \ {0}`) is Mathlib's `Irreducible`:
since `S` sits in a domain, `0` is never `Irreducible` and a nonzero element factors in `S*`
exactly when it factors in `S`. An additive atom of `(S, +)` is Mathlib's `AddIrreducible`.
-/

namespace LeanLab.KaplanPolo2023

open LaurentPolynomial Cardinal

universe u

variable {R : Type u} [CommRing R] [IsDomain R] (S : Subsemiring R)

/-! ## Definitions, Section 1 p.2 and Section 2.2 p.4 -/

/-- `S` is additively reduced: `0` is the only invertible element of `(S, +)`.
arXiv 2312.14888v2 p.4, Section 2.2. -/
def AdditivelyReduced : Prop := ∀ a : S, IsAddUnit a → a = 0

/-- `S` is additively atomic: every non invertible element of `(S, +)` is a finite sum of atoms
of `(S, +)`. arXiv 2312.14888v2 p.2 and p.3, Section 2.1. Mathlib has no notion of an atomic
monoid, so this is defined here minimally. -/
def AdditivelyAtomic : Prop :=
  ∀ s : S, ¬ IsAddUnit s → ∃ l : List S, (∀ a ∈ l, AddIrreducible a) ∧ l.sum = s

/-- The condition `A₊(S) = S^×`: the additive atoms of `S` are exactly the units of `S`.
arXiv 2312.14888v2 p.4, Section 2.2. -/
def AddAtomsEqUnits : Prop := ∀ a : S, AddIrreducible a ↔ IsUnit a

/-- `f` is a sum of at most `k` multiplicative irreducibles. -/
def IsSumOfAtMost {A : Type*} [Semiring A] (k : ℕ) (f : A) : Prop :=
  ∃ l : List A, l.length ≤ k ∧ (∀ g ∈ l, Irreducible g) ∧ l.sum = f

/-- `f` is a sum of exactly two multiplicative irreducibles. -/
def IsSumOfTwo {A : Type*} [Semiring A] (f : A) : Prop :=
  ∃ g h : A, Irreducible g ∧ Irreducible h ∧ f = g + h

/-- Form (a) of Theorem 3.6(B), p.8: `f = a x^{k₀} + b x^{k₁}` with `k₀ ≠ k₁`, `a, b ∈ S*` and
`a ∈ S^×` or `b ∈ S^×`. -/
def IsFormA (f : LaurentPolynomial S) : Prop :=
  ∃ (a b : S) (k₀ k₁ : ℤ), k₀ ≠ k₁ ∧ a ≠ 0 ∧ b ≠ 0 ∧ (IsUnit a ∨ IsUnit b) ∧
    f = C a * T k₀ + C b * T k₁

/-- Form (b) of Theorem 3.6(B), p.8: `f = a x^{k₀} + b x^{k₁} + c x^{k₂}` with pairwise distinct
exponents and `a, b, c ∈ S^×`. -/
def IsFormB (f : LaurentPolynomial S) : Prop :=
  ∃ (a b c : S) (k₀ k₁ k₂ : ℤ), k₀ ≠ k₁ ∧ k₀ ≠ k₂ ∧ k₁ ≠ k₂ ∧
    IsUnit a ∧ IsUnit b ∧ IsUnit c ∧ f = C a * T k₀ + C b * T k₁ + C c * T k₂

/-- A nonzero Laurent series `f` is monolithic if `f = g h` forces `g` or `h` to be a monomial.
arXiv 2312.14888v2 p.11 to p.12. -/
def Monolithic (f : LaurentSeries S) : Prop :=
  f ≠ 0 ∧ ∀ g h : LaurentSeries S, f = g * h → g.support.Subsingleton ∨ h.support.Subsingleton

/-- The set `R(f)` of unordered triples `(g₁, g₂, g₃)` with `f = g₁ + g₂ + g₃` and each
`gᵢ ∈ {0} ∪ A(S⟦x^{±1}⟧)`, encoded as multisets of cardinality three. arXiv 2312.14888v2 p.15. -/
def RSet (f : LaurentSeries S) : Set (Multiset (LaurentSeries S)) :=
  {m | Multiset.card m = 3 ∧ (∀ g ∈ m, g = 0 ∨ Irreducible g) ∧ m.sum = f}

/-- The value `f(1, ..., 1)` of a Laurent polynomial with coefficients in `ℕ₀`, in any number of
variables: the sum of its coefficients. -/
def sumCoeffs {M : Type*} [AddMonoid M] (f : AddMonoidAlgebra ℕ M) : ℕ :=
  f.coeff.sum fun _ c => c

/-! ## Section 3, Laurent polynomials -/

/-- SEALED For an additively reduced and additively atomic semidomain `S`, the following are
equivalent: (1) `A₊(S) = S^×`; (2) every `f ∈ S[x^{±1}]` with `|supp f| > 1` is a sum of at most two
multiplicative irreducibles; (3) for some `k ∈ ℕ` every such `f` is a sum of at most `k`
multiplicative irreducibles. arXiv 2312.14888v2 p.8 Theorem 3.6(A) -/
theorem theorem_3_6_A (hR : AdditivelyReduced S) (hA : AdditivelyAtomic S) :
    List.TFAE
      [ AddAtomsEqUnits S,
        ∀ f : LaurentPolynomial S, 1 < f.coeff.support.card → IsSumOfAtMost 2 f,
        ∃ k : ℕ, 1 ≤ k ∧
          ∀ f : LaurentPolynomial S, 1 < f.coeff.support.card → IsSumOfAtMost k f ] := by
  sorry

/-- SEALED Let `S` be additively reduced and additively atomic with `A₊(S) = S^×`. If
`f ∈ S[x^{±1}]` is neither `a x^{k₀} + b x^{k₁}` with `a` or `b` a unit nor
`a x^{k₀} + b x^{k₁} + c x^{k₂}` with `a, b, c` units, then `f` is the sum of exactly two
irreducible polynomials. The hypothesis `|supp f| > 1` is the standing convention of Section 3
and the scope of part (A). arXiv 2312.14888v2 p.8 Theorem 3.6(B) -/
theorem theorem_3_6_B (hR : AdditivelyReduced S) (hA : AdditivelyAtomic S)
    (hU : AddAtomsEqUnits S) (f : LaurentPolynomial S) (hf : 1 < f.coeff.support.card)
    (ha : ¬ IsFormA S f) (hb : ¬ IsFormB S f) : IsSumOfTwo f := by
  sorry

/-- SEALED Every `f ∈ ℕ₀[x^{±1}]` with `f(1) > 3` and `|supp f| > 1` is the sum of two
multiplicative irreducibles. arXiv 2312.14888v2 p.9 Corollary 3.7 -/
theorem corollary_3_7 (f : LaurentPolynomial ℕ) (h1 : 3 < sumCoeffs f)
    (hf : 1 < f.coeff.support.card) : IsSumOfTwo f := by
  sorry

/-- SEALED Fix `k ∈ ℕ`. Every `f ∈ ℕ₀[x₁^{±1}, ..., x_k^{±1}]` with `f(1, ..., 1) > 3` and
`|supp f| > 1` is the sum of two multiplicative irreducibles. The Laurent polynomial semiring in
`k` variables is `AddMonoidAlgebra ℕ (Fin k → ℤ)`. arXiv 2312.14888v2 p.10 Corollary 3.8 -/
theorem corollary_3_8 (k : ℕ) (hk : 1 ≤ k) (f : AddMonoidAlgebra ℕ (Fin k → ℤ))
    (h1 : 3 < sumCoeffs f) (hf : 1 < f.coeff.support.card) : IsSumOfTwo f := by
  sorry

/-! ## Section 4, Laurent series -/

/-- SEALED Let `S` be additively reduced and `f = ∑ sᵢ x^{kᵢ}` with `k` strictly increasing and
every `sᵢ ≠ 0`. If `k₁ - k₀ < k_{i+1} - kᵢ` for every `i ≥ 1` then `f` is monolithic.
arXiv 2312.14888v2 p.12 Lemma 4.2 -/
theorem lemma_4_2 (hR : AdditivelyReduced S) (f : LaurentSeries S) (k : ℕ → ℤ)
    (hk : StrictMono k) (hsupp : f.support = Set.range k)
    (hgap : ∀ i : ℕ, 1 ≤ i → k 1 - k 0 < k (i + 1) - k i) : Monolithic S f := by
  sorry

/-- SEALED Let `S` be additively reduced and `f = ∑ sᵢ x^{kᵢ}` with `k` strictly increasing and
every `sᵢ ≠ 0`. If for some `N ∈ ℕ` the sequence `(k_{N+i+1} - k_{N+i})_{i ∈ ℕ}` is strictly
increasing, then `f` is monolithic. arXiv 2312.14888v2 p.12 Lemma 4.3 -/
theorem lemma_4_3 (hR : AdditivelyReduced S) (f : LaurentSeries S) (k : ℕ → ℤ)
    (hk : StrictMono k) (hsupp : f.support = Set.range k) (N : ℕ) (hN : 1 ≤ N)
    (hinc : StrictMono fun i : ℕ => k (N + (i + 1) + 1) - k (N + (i + 1))) :
    Monolithic S f := by
  sorry

/-- SEALED For an additively reduced and additively atomic semidomain `S`, the following are
equivalent: (1) `A₊(S) = S^×`; (2) every `f ∈ S⟦x^{±1}⟧` with `|supp f| > 1` is a sum of at most
three multiplicative irreducibles; (3) for some `k ∈ ℕ` every such `f` is a sum of at most `k`
multiplicative irreducibles. arXiv 2312.14888v2 p.13 Theorem 4.4 -/
theorem theorem_4_4 (hR : AdditivelyReduced S) (hA : AdditivelyAtomic S) :
    List.TFAE
      [ AddAtomsEqUnits S,
        ∀ f : LaurentSeries S, f.support.Nontrivial → IsSumOfAtMost 3 f,
        ∃ k : ℕ, 1 ≤ k ∧ ∀ f : LaurentSeries S, f.support.Nontrivial → IsSumOfAtMost k f ] := by
  sorry

/-- SEALED Every `f ∈ ℕ₀⟦x^{±1}⟧` with `f(1) > 3` and `|supp f| > 1` is a sum of at most three
multiplicative irreducibles. For a series with infinite support `f(1)` diverges, so `f(1) > 3`
reads as: the support is infinite or the finite coefficient sum exceeds `3`.
arXiv 2312.14888v2 p.14 Corollary 4.5 -/
theorem corollary_4_5 (f : LaurentSeries ℕ)
    (h1 : f.support.Infinite ∨ 3 < ∑ᶠ n, f.coeff n) (hf : f.support.Nontrivial) :
    IsSumOfAtMost 3 f := by
  sorry

/-- SEALED Let `S` be additively reduced and additively atomic with `A₊(S) = S^×`. If
`f ∈ S⟦x^{±1}⟧` is not a polynomial then `|R(f)| ≥ 2^{ℵ₀}`. arXiv 2312.14888v2 p.15
Proposition 4.8 -/
theorem proposition_4_8 (hR : AdditivelyReduced S) (hA : AdditivelyAtomic S)
    (hU : AddAtomsEqUnits S) (f : LaurentSeries S) (hf : f.support.Infinite) :
    𝔠 ≤ #(RSet S f) := by
  sorry

/-! ## Vacuity instances, with `S = ℤ_{≥ 0}` inside the domain `ℤ` -/

section Vacuity

/-- The semidomain `ℕ₀` realised as the nonnegative integers inside `ℤ`. -/
abbrev N0 : Subsemiring ℤ := Subsemiring.nonneg ℤ

lemma N0_isAddUnit_iff (a : N0) : IsAddUnit a ↔ a = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h := congrArg Subtype.val u.val_neg
    have h1 := u.val.2
    have h2 := u.neg.2
    simp only [Subsemiring.mem_nonneg] at h1 h2
    apply Subtype.ext
    simp only [Subsemiring.coe_add, Subsemiring.coe_zero] at h
    show (u.val : ℤ) = 0
    omega
  · rintro rfl; exact isAddUnit_zero

lemma N0_isUnit_iff (a : N0) : IsUnit a ↔ (a : ℤ) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h := congrArg Subtype.val u.val_inv
    exact Int.eq_one_of_mul_eq_one_right u.val.2 h
  · intro h
    have : a = 1 := Subtype.ext h
    rw [this]; exact isUnit_one

lemma N0_addIrreducible_iff (a : N0) : AddIrreducible a ↔ (a : ℤ) = 1 := by
  constructor
  · intro h
    have hne : a ≠ 0 := fun h0 => h.not_isAddUnit (h0 ▸ isAddUnit_zero)
    have ha : (0 : ℤ) ≤ a := a.2
    have ha0 : (a : ℤ) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    by_contra h1
    have hb : (0 : ℤ) ≤ (a : ℤ) - 1 := by omega
    have key : a = 1 + ⟨(a : ℤ) - 1, hb⟩ := Subtype.ext (by simp)
    rcases h.isAddUnit_or_isAddUnit key with h2 | h2
    · rw [N0_isAddUnit_iff] at h2
      exact one_ne_zero h2
    · rw [N0_isAddUnit_iff] at h2
      have := congrArg Subtype.val h2
      simp at this
      omega
  · intro h
    refine ⟨fun hu => ?_, fun b c hbc => ?_⟩
    · rw [N0_isAddUnit_iff] at hu
      rw [hu] at h; simp at h
    · rw [N0_isAddUnit_iff, N0_isAddUnit_iff]
      have h' := congrArg Subtype.val hbc
      have hb : (0 : ℤ) ≤ b := b.2
      have hc : (0 : ℤ) ≤ c := c.2
      simp only [Subsemiring.coe_add] at h'
      by_cases hb0 : (b : ℤ) = 0
      · exact Or.inl (Subtype.ext hb0)
      · exact Or.inr (Subtype.ext (show (c : ℤ) = 0 by omega))

lemma N0_additivelyReduced : AdditivelyReduced N0 := fun a h => (N0_isAddUnit_iff a).1 h

lemma N0_additivelyAtomic : AdditivelyAtomic N0 := by
  intro s _
  refine ⟨List.replicate (s : ℤ).toNat 1, ?_, ?_⟩
  · intro a ha
    rw [List.eq_of_mem_replicate ha, N0_addIrreducible_iff]
    rfl
  · rw [List.sum_replicate, nsmul_eq_mul, mul_one]
    have hs : (0 : ℤ) ≤ s := s.2
    apply Subtype.ext
    exact Int.toNat_of_nonneg hs

lemma N0_addAtomsEqUnits : AddAtomsEqUnits N0 := fun a => by
  rw [N0_addIrreducible_iff, N0_isUnit_iff]

/-- Vacuity for Theorem 3.6(A) and Theorem 4.4: `ℤ_{≥0}` is additively reduced and additively
atomic. -/
example : AdditivelyReduced N0 ∧ AdditivelyAtomic N0 :=
  ⟨N0_additivelyReduced, N0_additivelyAtomic⟩

/-- The binomial `2 + 2x ∈ ℤ_{≥0}[x^{±1}]`. -/
noncomputable def twoTwo : LaurentPolynomial N0 :=
  AddMonoidAlgebra.ofCoeff (Finsupp.single 0 2 + Finsupp.single 1 2)

lemma N0_two_ne_zero : (2 : N0) ≠ 0 := fun h => by
  have := congrArg Subtype.val h; simp at this

lemma N0_two_not_unit : ¬ IsUnit (2 : N0) := by
  rw [N0_isUnit_iff]; simp

lemma twoTwo_coeff (n : ℤ) : twoTwo.coeff n = if n = 0 ∨ n = 1 then 2 else 0 := by
  simp only [twoTwo, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h0 : n = 0
  · subst h0; simp
  · by_cases h1 : n = 1
    · subst h1; simp
    · simp [h0, h1, Ne.symm h0, Ne.symm h1]

lemma coeff_CT (a : N0) (k n : ℤ) : (C a * T k : LaurentPolynomial N0).coeff n =
    if k = n then a else 0 := by
  rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Vacuity for Theorem 3.6(B): `2 + 2x` over `ℤ_{≥0}` has two support points and is of neither
excluded form. -/
example : AdditivelyReduced N0 ∧ AdditivelyAtomic N0 ∧ AddAtomsEqUnits N0 ∧
    1 < twoTwo.coeff.support.card ∧ ¬ IsFormA N0 twoTwo ∧ ¬ IsFormB N0 twoTwo := by
  refine ⟨N0_additivelyReduced, N0_additivelyAtomic, N0_addAtomsEqUnits, ?_, ?_, ?_⟩
  · rw [Finset.one_lt_card]
    refine ⟨0, ?_, 1, ?_, by norm_num⟩ <;>
      simp [Finsupp.mem_support_iff, twoTwo_coeff]
  · rintro ⟨a, b, k₀, k₁, h01, ha, hb, hu, hf⟩
    have e0 := congrArg (fun p : LaurentPolynomial N0 => p.coeff k₀) hf
    have e1 := congrArg (fun p : LaurentPolynomial N0 => p.coeff k₁) hf
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_CT, twoTwo_coeff] at e0 e1
    simp only [h01, Ne.symm h01, ite_true, ite_false, add_zero, zero_add] at e0 e1
    have ha2 : a = 2 := by
      split_ifs at e0 with h
      · exact e0.symm
      · exact absurd e0.symm ha
    have hb2 : b = 2 := by
      split_ifs at e1 with h
      · exact e1.symm
      · exact absurd e1.symm hb
    subst ha2 hb2
    rcases hu with h | h <;> exact N0_two_not_unit h
  · rintro ⟨a, b, c, k₀, k₁, k₂, h01, h02, h12, ha, hb, hc, hf⟩
    have e0 := congrArg (fun p : LaurentPolynomial N0 => p.coeff k₀) hf
    have e1 := congrArg (fun p : LaurentPolynomial N0 => p.coeff k₁) hf
    have e2 := congrArg (fun p : LaurentPolynomial N0 => p.coeff k₂) hf
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_CT, twoTwo_coeff] at e0 e1 e2
    simp only [h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12, ite_true, ite_false,
      add_zero, zero_add] at e0 e1 e2
    have hk0 : k₀ = 0 ∨ k₀ = 1 := by
      by_contra h; simp only [h, ite_false] at e0; exact ha.ne_zero e0.symm
    have hk1 : k₁ = 0 ∨ k₁ = 1 := by
      by_contra h; simp only [h, ite_false] at e1; exact hb.ne_zero e1.symm
    have hk2 : k₂ = 0 ∨ k₂ = 1 := by
      by_contra h; simp only [h, ite_false] at e2; exact hc.ne_zero e2.symm
    omega

/-- Vacuity for Corollary 3.7: `2 + 2x ∈ ℕ₀[x^{±1}]` has `f(1) = 4 > 3` and two support points. -/
example : ∃ f : LaurentPolynomial ℕ, 3 < sumCoeffs f ∧ 1 < f.coeff.support.card := by
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.single 0 2 + Finsupp.single 1 2), ?_, ?_⟩
  · simp only [sumCoeffs]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  · rw [Finset.one_lt_card]
    refine ⟨0, ?_, 1, ?_, by norm_num⟩ <;> simp

/-- Vacuity for Corollary 3.8 with `k = 1`: `2 + 2x₁` has `f(1) = 4 > 3` and two support
points. -/
example : ∃ f : AddMonoidAlgebra ℕ (Fin 1 → ℤ), 3 < sumCoeffs f ∧ 1 < f.coeff.support.card := by
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.single 0 2 + Finsupp.single (fun _ => 1) 2), ?_, ?_⟩
  · simp only [sumCoeffs]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  · have hne : (0 : Fin 1 → ℤ) ≠ fun _ => 1 := fun h => by
      have := congrFun h 0; simp at this
    rw [Finset.one_lt_card]
    refine ⟨0, ?_, fun _ => 1, ?_, hne⟩ <;> simp [hne, Ne.symm hne]

/-- The Laurent series over `T` whose coefficients are `1` on a set `A` bounded below and `0`
elsewhere. -/
noncomputable def indSeries {T : Type*} [Semiring T] (A : Set ℤ) (hA : BddBelow A) :
    LaurentSeries T where
  coeff := A.indicator 1
  isPWO_support' := (BddBelow.isWF (hA.mono Set.support_indicator_subset)).isPWO

lemma indSeries_support {T : Type*} [Semiring T] [Nontrivial T] (A : Set ℤ) (hA : BddBelow A) :
    (indSeries (T := T) A hA).support = A := by
  ext n
  simp only [HahnSeries.support, indSeries, Function.mem_support]
  by_cases h : n ∈ A <;> simp [h]

lemma range_bdd (k : ℕ → ℤ) (hk : StrictMono k) : BddBelow (Set.range k) :=
  ⟨k 0, by rintro _ ⟨i, rfl⟩; exact hk.monotone (Nat.zero_le i)⟩

lemma sq_strictMono : StrictMono fun i : ℕ => ((i : ℤ) ^ 2) := by
  intro a b h
  have : (a : ℤ) < b := by exact_mod_cast h
  have h0 : (0 : ℤ) ≤ a := by positivity
  nlinarith

/-- Vacuity for Lemma 4.2: `∑ x^{i^2}` over `ℤ_{≥0}` with `kᵢ = i²`, whose gaps `2i + 1` exceed
`k₁ - k₀ = 1` for `i ≥ 1`. -/
example : AdditivelyReduced N0 ∧ ∃ (f : LaurentSeries N0) (k : ℕ → ℤ), StrictMono k ∧
    f.support = Set.range k ∧ ∀ i : ℕ, 1 ≤ i → k 1 - k 0 < k (i + 1) - k i := by
  refine ⟨N0_additivelyReduced, indSeries _ (range_bdd _ sq_strictMono), _, sq_strictMono,
    indSeries_support _ _, ?_⟩
  intro i hi
  push_cast
  have : (1 : ℤ) ≤ i := by exact_mod_cast hi
  nlinarith

/-- Vacuity for Lemma 4.3: the same series with `N = 1`, gaps `2i + 1` strictly increasing. -/
example : AdditivelyReduced N0 ∧ ∃ (f : LaurentSeries N0) (k : ℕ → ℤ), StrictMono k ∧
    f.support = Set.range k ∧ ∃ N : ℕ, 1 ≤ N ∧
      StrictMono fun i : ℕ => k (N + (i + 1) + 1) - k (N + (i + 1)) := by
  refine ⟨N0_additivelyReduced, indSeries _ (range_bdd _ sq_strictMono), _, sq_strictMono,
    indSeries_support _ _, 1, le_rfl, ?_⟩
  intro a b h
  have : (a : ℤ) < b := by exact_mod_cast h
  simp only
  push_cast
  nlinarith

lemma Ici_bdd : BddBelow (Set.Ici (0 : ℤ)) := ⟨0, fun _ h => h⟩

/-- Vacuity for Corollary 4.5: `∑_{i ≥ 0} x^i ∈ ℕ₀⟦x^{±1}⟧` has infinite support. -/
example : ∃ f : LaurentSeries ℕ, (f.support.Infinite ∨ 3 < ∑ᶠ n, f.coeff n) ∧
    f.support.Nontrivial := by
  refine ⟨indSeries _ Ici_bdd, ?_, ?_⟩ <;> rw [indSeries_support]
  · exact Or.inl (Set.Ici_infinite 0)
  · exact (Set.Ici_infinite 0).nontrivial

/-- Vacuity for Proposition 4.8: over `ℤ_{≥0}` the series `∑_{i ≥ 0} x^i` is not a polynomial. -/
example : AdditivelyReduced N0 ∧ AdditivelyAtomic N0 ∧ AddAtomsEqUnits N0 ∧
    ∃ f : LaurentSeries N0, f.support.Infinite := by
  refine ⟨N0_additivelyReduced, N0_additivelyAtomic, N0_addAtomsEqUnits,
    indSeries _ Ici_bdd, ?_⟩
  rw [indSeries_support]
  exact Set.Ici_infinite 0

end Vacuity

end LeanLab.KaplanPolo2023
