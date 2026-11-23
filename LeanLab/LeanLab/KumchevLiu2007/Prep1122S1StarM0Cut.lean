/-
PREP 2026-11-22, route burst burst-20261122, unit P1122-0138. Cuts the open leaf
S1_sub_S1star_on_M0 of Prep1121DKLMajorCut.lean into smaller pieces.
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 5 below display 15, and page 6
display 25 with the line after it.

The paper's argument on M(q, a) inside M0 runs as follows. The arcs M(q, a) are
disjoint, so S1* at alpha is the one term mu(q)/phi(q) T1(beta), beta = alpha - a/q.
The orthogonality of the characters modulo q expands e(am/q) for m coprime to q
through the Gauss sums tau(chi). The principal character gives mu(q)/phi(q) T1(beta),
and what is left is a sum over chi of tau(chi^(-1)) chi(a)/phi(q) times W1(beta, chi).
The bound |tau(chi)| at most q^(1/2) gives display 25, and partial summation
against e(m beta) with (A1.2), here A12Corr, bounds each W1.

Five pieces carry those steps, all PROVED here:
* S1star_on_arc, the disjointness of the arcs, PROVED.
* char_expansion, the orthogonality step, PROVED.
* gaussSum_one_eq_moebius, the principal character term, the Ramanujan sum
  c_q(1) = mu(q), PROVED.
* norm_gaussSum_le_sqrt, |tau(chi)| at most q^(1/2) for every chi mod q, primitive
  or not, PROVED by Parseval over the additive characters mod q, which needs no
  reduction to the conductor.
* partial_summation_window, the partial summation step, PROVED.

The final theorem S1_sub_S1star_on_M0_of_leaves proves the exact statement of
Prep1121DKLMajorCut.S1_sub_S1star_on_M0 from these five, CONDITIONAL ON A12Corr
as the parent is. It admits no step of its own; the size bounds of the block range
are PROVED here in block_large. So the parent leaf now rests only on the named hypothesis A12Corr.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121DKLMajorCut
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace LeanLab.KumchevLiu2007.Prep1122S1StarM0Cut

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-! ## The five pieces of display 25, all PROVED -/

/-- Two reduced fractions a/q and a'/q' with q' a = q a' are the same pair. -/
lemma pair_eq_of_cross (q q' a' : ℕ) (a : ℤ) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (hcop' : Nat.Coprime a' q')
    (h : (q' : ℤ) * a = q * a') : q' = q ∧ a = a' := by
  have h1 : (q : ℤ) ∣ q' := by
    have : (q : ℤ) ∣ (q' : ℤ) * a := ⟨a', h⟩
    exact hcop.symm.dvd_of_dvd_mul_right this
  have hc' : IsCoprime (q' : ℤ) (a' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop'.symm
  have h2 : (q' : ℤ) ∣ q := by
    have : (q' : ℤ) ∣ (q : ℤ) * a' := ⟨a, h.symm⟩
    exact hc'.dvd_of_dvd_mul_right this
  have hqq : q' = q := by
    have := Int.dvd_antisymm (by positivity) (by positivity) h2 h1
    exact_mod_cast this
  refine ⟨hqq, ?_⟩
  subst hqq
  have hq0 : (q' : ℤ) ≠ 0 := by positivity
  exact mul_left_cancel₀ hq0 h

/-- PROVED, was LEAF: P0088 page 5, below display 15, "Since the intervals M(q, a) are disjoint,
this defines S_j* on M". MEDIUM. For alpha in the period interval with |q alpha - a|
at most (H/P)^(-1), q at most P and a coprime to q, no other arc of M contains alpha
once H exceeds 2 P^2, so S1*(alpha) is the single term mu(q)/phi(q) T1(alpha - a/q). -/
theorem S1star_on_arc (X Y H P α : ℝ) (q : ℕ) (a : ℤ) (hP : 1 ≤ P) (hH : 2 * P ^ 2 < H)
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hq1 : 1 ≤ q) (hqP : (q : ℝ) ≤ P) (hcop : IsCoprime a (q : ℤ))
    (hqa : |(q : ℝ) * α - a| ≤ (H / P)⁻¹) :
    S1star X Y H P α = ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) *
      T1 X Y (α - (a : ℝ) / q) := by
  obtain ⟨hα0, hα1⟩ := hα
  have hP0 : 0 < P := by linarith
  have hH0 : 0 < H := by nlinarith
  have hRinv : (H / P)⁻¹ = P / H := by rw [inv_div]
  rw [hRinv] at hqa
  have hPH : P / H < 1 / (2 * P) := by
    rw [div_lt_div_iff₀ hH0 (by positivity)]; nlinarith
  have hhalf : 1 / (2 * P) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have habs := abs_le.mp hqa
  have ha0 : 0 ≤ a := by
    have : (-1 : ℝ) < a := by nlinarith
    have : (-1 : ℤ) < a := by exact_mod_cast this
    omega
  have haq : a ≤ q := by
    have : (a : ℝ) < q + 1 := by nlinarith
    have : a < (q : ℤ) + 1 := by exact_mod_cast this
    omega
  have hcast : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by
    have : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
    exact_mod_cast this
  have hcopN : Nat.Coprime a.toNat q := by
    have := Int.isCoprime_iff_gcd_eq_one.mp hcop
    have h2 : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
    rw [← h2] at hcop
    exact Nat.isCoprime_iff_coprime.mp hcop
  have hqfl : q ≤ ⌊P⌋₊ := Nat.le_floor hqP
  have hatq : a.toNat ≤ q := by omega
  have hmem : (q, a.toNat) ∈ arcPairs P := by
    simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_range]
    exact ⟨⟨⟨hq1, hqfl⟩, by omega⟩, hatq, hcopN⟩
  have harc : α ∈ arc (H / P) (q, a.toNat) := by
    show |(q : ℝ) * α - ((a.toNat : ℕ) : ℝ)| ≤ (H / P)⁻¹
    rw [hcast, hRinv]; exact hqa
  unfold S1star
  rw [Finset.sum_eq_single (q, a.toNat)]
  · rw [Set.indicator_of_mem harc]
    simp only
    rw [hcast]
  · intro v hv hne
    apply Set.indicator_of_notMem
    intro hv'
    apply hne
    obtain ⟨q', a'⟩ := v
    simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_range] at hv
    obtain ⟨⟨⟨hq'1, hq'P⟩, _⟩, _, hcop'⟩ := hv
    have hv'' : |(q' : ℝ) * α - (a' : ℝ)| ≤ P / H := by
      have := hv'; simp only [arc, Set.mem_ofPred_eq] at this; rwa [hRinv] at this
    have hq'R : (q' : ℝ) ≤ P := by
      have : (q' : ℝ) ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast hq'P
      exact this.trans (Nat.floor_le hP0.le)
    have hk : |(((q' : ℤ) * a - q * a' : ℤ) : ℝ)| < 1 := by
      push_cast
      have e : (q' : ℝ) * a - q * a' = (q' : ℝ) * (a - q * α) + q * (q' * α - a') := by ring
      rw [e]
      calc |(q' : ℝ) * (a - q * α) + q * (q' * α - a')|
          ≤ |(q' : ℝ) * (a - q * α)| + |(q : ℝ) * (q' * α - a')| := abs_add_le _ _
        _ = q' * |(a : ℝ) - q * α| + q * |(q' : ℝ) * α - a'| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ q'),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ q)]
        _ ≤ P * (P / H) + P * (P / H) := by
            rw [abs_sub_comm]
            gcongr
        _ < 1 := by
            have : P * (P / H) + P * (P / H) = 2 * P ^ 2 / H := by ring
            rw [this, div_lt_one hH0]; exact hH
    have hk' : (q' : ℤ) * a - q * a' = 0 := by
      have : |((q' : ℤ) * a - q * a')| < 1 := by exact_mod_cast hk
      rw [abs_lt] at this; omega
    obtain ⟨h1, h2⟩ := pair_eq_of_cross q q' a' a hq1 hcop hcop' (by linarith)
    subst h1
    rw [h2]; simp
  · intro h; exact absurd hmem h

/-- Orthogonality: for `c` a unit mod `q`, the sum over characters of
`χ⁻¹ b * χ c` is `φ(q)` when `b = c` and `0` otherwise. -/
lemma sum_inv_mul_char (q : ℕ) [NeZero q] {c : ZMod q} (hc : IsUnit c) (b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c = if b = c then (Nat.totient q : ℂ) else 0 := by
  by_cases hb : IsUnit b
  · have : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c = χ (Ring.inverse b * c) := by
      intro χ; rw [MulChar.inv_apply, map_mul]
    simp_rw [this, DirichletCharacter.sum_characters_eq, Ring.inverse_mul_eq_iff_eq_mul _ _ _ hb,
      mul_one]
    by_cases h : b = c
    · simp [h]
    · simp [h, Ne.symm h]
  · have hbc : b ≠ c := fun h => hb (h ▸ hc)
    rw [show (if b = c then (Nat.totient q : ℂ) else 0) = 0 from by simp [hbc]]
    exact Finset.sum_eq_zero fun χ _ => by rw [MulChar.map_nonunit _ hb, zero_mul]

/-- PROVED, was LEAF: P0088 page 6 display 25, first step, "similarly to (18)", the orthogonality
of the characters modulo q. MEDIUM. For a and m coprime to q,
e(am/q) = sum over chi mod q of tau(chi^(-1)) chi(a) chi(m) / phi(q), where tau is the
Gauss sum with the additive character e(x/q). -/
theorem char_expansion (q : ℕ) [NeZero q] (a : ℤ) (m : ℕ) (ha : IsCoprime a (q : ℤ))
    (hm : Nat.Coprime m q) :
    ∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) * χ (a : ZMod q) /
        (Nat.totient q : ℂ) * χ (m : ZMod q) =
      fourier (m : ℤ) ((((a : ℝ) / q : ℝ)) : AddCircle (1 : ℝ)) := by
  set c : ZMod q := (a : ZMod q) * (m : ZMod q) with hcdef
  have hua : IsUnit (a : ZMod q) :=
    (ZMod.coe_int_isUnit_iff_isCoprime a q).mpr ha.symm
  have hum : IsUnit (m : ZMod q) := (ZMod.isUnit_iff_coprime m q).mpr hm
  have hc : IsUnit c := hua.mul hum
  have hφ : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have step : ∀ χ : DirichletCharacter ℂ q,
      gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) * χ (a : ZMod q) / (Nat.totient q : ℂ) *
        χ (m : ZMod q) =
      ∑ b : ZMod q, (ZMod.stdAddChar (N := q) b / (Nat.totient q : ℂ)) * (χ⁻¹ b * χ c) := by
    intro χ
    rw [gaussSum, hcdef, map_mul]
    simp only [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Finset.sum_congr rfl fun χ _ => step χ, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_inv_mul_char q hc]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [div_mul_cancel₀ _ hφ]
  have hc' : c = ((a * (m : ℤ) : ℤ) : ZMod q) := by rw [hcdef]; push_cast; rfl
  rw [hc', ZMod.stdAddChar_coe, fourier_coe_apply]
  congr 1
  push_cast
  field_simp


/-- The sum of all complex `n`-th roots of unity is `1` for `n = 1` and `0` for `n > 1`. -/
lemma sum_nthRootsFinset_one (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ Polynomial.nthRootsFinset n (1 : ℂ), x = if n = 1 then 1 else 0 := by
  have hn0 : n ≠ 0 := hn.ne'
  have : NeZero n := ⟨hn0⟩
  set ζ := Complex.exp (2 * π * I / n) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have : ∑ x ∈ Polynomial.nthRootsFinset n (1 : ℂ), x = ∑ i ∈ Finset.range n, ζ ^ i := by
    symm
    refine Finset.sum_nbij (fun i => ζ ^ i) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro i _
      rw [Polynomial.mem_nthRootsFinset hn, ← pow_mul, mul_comm, pow_mul,
        hζ.pow_eq_one, one_pow]
    · intro i hi j hj hij
      exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    · intro x hx
      try rw [Finset.mem_coe] at hx
      rw [Polynomial.mem_nthRootsFinset hn] at hx
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
      exact ⟨i, by simpa using hi, rfl⟩
  rw [this]
  by_cases h1 : n = 1
  · subst h1; simp
  · rw [show (if n = 1 then (1:ℂ) else 0) = 0 from by simp [h1]]
    exact hζ.geom_sum_eq_zero (by omega)

/-- The sum of the primitive complex `n`-th roots of unity is `μ(n)`. -/
lemma sum_primitiveRoots_eq_moebius (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ primitiveRoots n ℂ, x = ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n => ∑ x ∈ primitiveRoots n ℂ, x) (g := fun n => if n = 1 then (1 : ℂ) else 0)).mp
    (by
      intro n hn
      rw [← sum_nthRootsFinset_one n hn, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
        Finset.sum_biUnion]
      intro i _ j _ hij
      exact IsPrimitiveRoot.disjoint hij) n hn
  rw [← key, Finset.sum_eq_single (n, 1)]
  · simp
  · rintro ⟨d, e⟩ hde hne
    have he : e ≠ 1 := by
      rintro rfl
      rw [Nat.mem_divisorsAntidiagonal] at hde
      apply hne; simp at hde; simp [hde.1]
    simp [he]
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn.ne'⟩) h

/-- PROVED, was LEAF: P0088 page 6 display 25, the principal character term, which gives
mu(q)/phi(q) T1 as in the definition of S1* on page 5. MEDIUM. The Gauss sum of the
principal character mod q is the Ramanujan sum c_q(1), the sum of the primitive q-th
roots of unity, which is mu(q). -/
theorem gaussSum_one_eq_moebius (q : ℕ) [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) (ZMod.stdAddChar (N := q)) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← sum_primitiveRoots_eq_moebius q hq, gaussSum]
  have h1 : ∀ b : ZMod q, (1 : DirichletCharacter ℂ q) b * ZMod.stdAddChar b =
      if IsUnit b then ZMod.stdAddChar b else 0 := by
    intro b
    split_ifs with hb
    · rw [MulChar.one_apply hb, one_mul]
    · rw [MulChar.map_nonunit _ hb, zero_mul]
  simp_rw [h1]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij (fun b => ZMod.stdAddChar b) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [mem_primitiveRoots hq, Complex.isPrimitiveRoot_iff _ _ hq.ne']
    refine ⟨b.val, ZMod.val_lt b, ?_, ?_⟩
    · rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]; exact hb.2
    · rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]; congr 1; ring
  · intro b _ c _ h
    exact ZMod.injective_stdAddChar h
  · intro x hx
    try rw [Finset.mem_coe] at hx
    rw [mem_primitiveRoots hq, Complex.isPrimitiveRoot_iff _ _ hq.ne'] at hx
    obtain ⟨i, _, hi, rfl⟩ := hx
    refine ⟨(i : ZMod q), ?_, ?_⟩
    · try rw [Finset.mem_coe]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (ZMod.isUnit_iff_coprime i q).mpr hi⟩
    · show ZMod.stdAddChar (i : ZMod q) = _
      rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]; congr 1; ring


/-- Orthogonality of the additive characters `a ↦ e(a x / q)` mod `q`. -/
lemma stdAddChar_orth (q : ℕ) [NeZero q] (x y : ZMod q) :
    ∑ a : ZMod q, ZMod.stdAddChar (a * x) * (starRingEnd ℂ) (ZMod.stdAddChar (a * y)) =
      if x = y then (q : ℂ) else 0 := by
  have h : ∀ a : ZMod q, ZMod.stdAddChar (a * x) * (starRingEnd ℂ) (ZMod.stdAddChar (a * y))
      = ZMod.stdAddChar (a * (x - y)) := by
    intro a
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]; congr 1; ring
  simp_rw [h]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card]
  simp only [sub_eq_zero]
  split_ifs <;> simp

/-- Parseval for the discrete Fourier transform on `ZMod q`. -/
lemma parseval_zmod (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    ∑ a : ZMod q, (∑ x, f x * ZMod.stdAddChar (a * x)) *
        (starRingEnd ℂ) (∑ y, f y * ZMod.stdAddChar (a * y))
      = (q : ℂ) * ∑ x, f x * (starRingEnd ℂ) (f x) := by
  have key : ∀ x y : ZMod q, ∑ a : ZMod q, (f x * ZMod.stdAddChar (a * x)) *
      ((starRingEnd ℂ) (f y) * (starRingEnd ℂ) (ZMod.stdAddChar (a * y)))
      = f x * (starRingEnd ℂ) (f y) * (if x = y then (q : ℂ) else 0) := by
    intro x y
    rw [← stdAddChar_orth, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  calc ∑ a : ZMod q, (∑ x, f x * ZMod.stdAddChar (a * x)) *
        (starRingEnd ℂ) (∑ y, f y * ZMod.stdAddChar (a * y))
      = ∑ a : ZMod q, ∑ x, ∑ y, (f x * ZMod.stdAddChar (a * x)) *
          ((starRingEnd ℂ) (f y) * (starRingEnd ℂ) (ZMod.stdAddChar (a * y))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [map_mul (starRingEnd ℂ)]
    _ = ∑ x, ∑ y, ∑ a : ZMod q, (f x * ZMod.stdAddChar (a * x)) *
          ((starRingEnd ℂ) (f y) * (starRingEnd ℂ) (ZMod.stdAddChar (a * y))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, f x * (starRingEnd ℂ) (f y) * (if x = y then (q : ℂ) else 0) := by
        simp_rw [key]
    _ = (q : ℂ) * ∑ x, f x * (starRingEnd ℂ) (f x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring

/-- PROVED, was LEAF: P0088 page 6 display 25, the bound |tau(chi)| at most q^(1/2) that turns
1/phi(q) times the Gauss sum into the factor q^(-1/2 + eta). HARD. It holds for every
character chi mod q, primitive or not: for chi induced by a primitive chi* mod q*,
tau(chi) = mu(q/q*) chi*(q/q*) tau(chi*) and |tau(chi*)| = q*^(1/2). -/
theorem norm_gaussSum_le_sqrt (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ ≤ Real.sqrt q := by
  set ψ := ZMod.stdAddChar (N := q)
  set τ := gaussSum χ ψ
  have hτa : ∀ a : ZMod q, gaussSum χ (ψ.mulShift a) = ∑ x, χ x * ψ (a * x) := fun a => by
    simp only [gaussSum, AddChar.mulShift_apply]
  have hR : ∑ a : ZMod q, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 = q * ∑ x, ‖χ x‖ ^ 2 := by
    have h := parseval_zmod q (fun x => χ x)
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    exact_mod_cast h
  have hU : ∀ u : (ZMod q)ˣ, ‖gaussSum χ (ψ.mulShift (u : ZMod q))‖ = ‖τ‖ := by
    intro u
    have h := congrArg norm (gaussSum_mulShift χ ψ u)
    rw [norm_mul, DirichletCharacter.unit_norm_eq_one, one_mul] at h
    exact h
  let e : (ZMod q)ˣ ↪ ZMod q := ⟨((↑) : (ZMod q)ˣ → ZMod q), Units.val_injective⟩
  have hemb : ∑ u : (ZMod q)ˣ, ‖gaussSum χ (ψ.mulShift (u : ZMod q))‖ ^ 2
      ≤ ∑ a : ZMod q, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 := by
    calc ∑ u : (ZMod q)ˣ, ‖gaussSum χ (ψ.mulShift (u : ZMod q))‖ ^ 2
        = ∑ a ∈ Finset.univ.map e, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 :=
          by rw [Finset.sum_map]; rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => by positivity)
  have hC : ∑ x : ZMod q, ‖χ x‖ ^ 2 = (Nat.totient q : ℝ) := by
    have e1 : ∑ x : ZMod q, ‖χ x‖ ^ 2 = ∑ x ∈ Finset.univ.map e, ‖χ x‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      have : ¬ IsUnit x := by
        rintro ⟨u, rfl⟩; exact hx (Finset.mem_map.2 ⟨u, Finset.mem_univ _, rfl⟩)
      simp [χ.map_nonunit this]
    rw [e1, Finset.sum_map]
    simp [e, ZMod.card_units_eq_totient]
  have hsum : ∑ u : (ZMod q)ˣ, ‖gaussSum χ (ψ.mulShift (u : ZMod q))‖ ^ 2
      = (Nat.totient q : ℝ) * ‖τ‖ ^ 2 := by
    simp [hU, ZMod.card_units_eq_totient]
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have h1 : (Nat.totient q : ℝ) * ‖τ‖ ^ 2 ≤ (Nat.totient q : ℝ) * q := by
    rw [← hsum]; refine hemb.trans ?_; rw [hR, hC, mul_comm]
  have h2 : ‖τ‖ ^ 2 ≤ q := le_of_mul_le_mul_left h1 hφ
  calc ‖τ‖ = Real.sqrt (‖τ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt q := Real.sqrt_le_sqrt h2

/-- The unimodularity of the Fourier character. -/
lemma psum_norm_fourier (n : ℤ) (x : AddCircle (1 : ℝ)) : ‖fourier n x‖ = 1 := by
  simp [fourier_apply]

/-- The step bound |e(beta) - 1| at most 2 pi |beta|. -/
lemma psum_step (β : ℝ) :
    ‖fourier (1 : ℤ) (β : AddCircle (1 : ℝ)) - 1‖ ≤ 2 * π * |β| := by
  rw [fourier_coe_apply]
  have h : (2 * (π : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * (β : ℂ) / ((1 : ℝ) : ℂ))
      = Complex.I * ((2 * π * β : ℝ) : ℂ) := by push_cast; ring
  rw [h]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos Real.pi_pos]

/-- PROVED, was LEAF: P0088 page 6, the line after display 25, "Using partial summation, we
deduce from (25) and (A1.2)". MEDIUM. If every sum of the coefficients c over the
window primes' interval I1 cut to u at most m below v is at most K, then the sum of
c(m) e(m beta) over I1 is at most K (1 + 2 pi |beta| (Y + 1)). -/
theorem partial_summation_window (X Y K β : ℝ) (hY : 0 ≤ Y) (c : ℕ → ℂ)
    (hK : ∀ u v : ℝ, X - Y ≤ u → u ≤ v → v ≤ X →
      ‖∑ m ∈ (primeWindow X Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v), c m‖ ≤ K) :
    ‖∑ m ∈ primeWindow X Y, c m * fourier (m : ℤ) (β : AddCircle (1 : ℝ))‖ ≤
      K * (1 + 2 * π * |β| * (Y + 1)) := by
  set W := primeWindow X Y with hW
  have memW : ∀ m, m ∈ W ↔ m < ⌊X⌋₊ + 1 ∧ X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X := by
    intro m; simp [hW, primeWindow]
  -- K is nonnegative
  have hK0 : 0 ≤ K := by
    have := hK (X - Y) (X - Y) le_rfl le_rfl (by linarith)
    exact (norm_nonneg _).trans this
  set a : ℕ → ℂ := fun i => if i ∈ W then c i else 0 with ha
  set G : ℕ → ℂ := fun k => ∑ j ∈ Finset.range k, a j with hG
  have hGeq : ∀ k, G k = ∑ m ∈ W.filter (fun m => m < k), c m := by
    intro k
    simp only [hG, ha]
    rw [← Finset.sum_filter]
    congr 1
    ext m; simp [and_comm]
  have hGK : ∀ k, ‖G k‖ ≤ K := by
    intro k
    rw [hGeq]
    by_cases hk : (k : ℝ) ≤ X - Y
    · have : W.filter (fun m => m < k) = ∅ := by
        ext m
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hm hmk
        have := ((memW m).1 hm).2.1
        have : (m : ℝ) < k := by exact_mod_cast hmk
        linarith
      rw [this, Finset.sum_empty, norm_zero]; exact hK0
    · push Not at hk
      have := hK (X - Y) (min (k : ℝ) X) le_rfl (le_min hk.le (by linarith)) (min_le_right _ _)
      convert this using 3
      ext m
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hm, hmk⟩
        have h := (memW m).1 hm
        refine ⟨hm, h.2.1, lt_min (by exact_mod_cast hmk) h.2.2⟩
      · rintro ⟨hm, -, hmv⟩
        exact ⟨hm, by exact_mod_cast (lt_of_lt_of_le hmv (min_le_left _ _))⟩
  set N := ⌈X - Y⌉₊ with hN
  set L := ⌊X⌋₊ + 1 with hL
  have hWsub : ∀ m ∈ W, N ≤ m ∧ m < L := by
    intro m hm
    have h := (memW m).1 hm
    exact ⟨Nat.ceil_le.2 h.2.1, h.1⟩
  have hG0 : G N = 0 := by
    rw [hGeq]
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_filter] at hm
    exact absurd (hWsub m hm.1).1 (by omega)
  set f : ℕ → ℂ := fun i => fourier (i : ℤ) (β : AddCircle (1 : ℝ)) with hf
  have hsum : ∑ m ∈ W, c m * fourier (m : ℤ) (β : AddCircle (1 : ℝ)) =
      ∑ i ∈ Finset.Ico N L, f i • a i := by
    simp only [hf, ha, smul_eq_mul, mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have : (Finset.Ico N L).filter (fun i => i ∈ W) = W := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · exact fun h => h.2
      · intro hm; exact ⟨hWsub m hm, hm⟩
    rw [this]
    exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  rw [hsum]
  by_cases hNL : N < L
  · rw [Finset.sum_Ico_by_parts f a hNL]
    have hGN : (∑ j ∈ Finset.range N, a j) = 0 := hG0
    rw [hGN, smul_zero, sub_zero]
    have hdiff : ∀ i, ‖f (i + 1) - f i‖ ≤ 2 * π * |β| := by
      intro i
      have : f (i + 1) - f i = f i * (fourier (1 : ℤ) (β : AddCircle (1 : ℝ)) - 1) := by
        simp only [hf]
        rw [mul_sub, mul_one, ← fourier_add]
        push_cast; ring_nf
      rw [this, norm_mul, hf]
      simp only
      rw [psum_norm_fourier, one_mul]
      exact psum_step β
    have hcount : ((Finset.Ico N (L - 1)).card : ℝ) ≤ Y + 1 := by
      rw [Nat.card_Ico]
      have h1 : (⌊X⌋₊ : ℝ) ≤ X ∨ ⌊X⌋₊ = 0 := by
        by_cases hX : 0 ≤ X
        · exact Or.inl (Nat.floor_le hX)
        · right; exact Nat.floor_of_nonpos (by linarith)
      have h2 : X - Y ≤ (N : ℝ) := Nat.le_ceil _
      have hL1 : L - 1 = ⌊X⌋₊ := by omega
      rw [hL1]
      rcases h1 with h1 | h1
      · rcases le_total N ⌊X⌋₊ with h | h
        · rw [Nat.cast_sub h]; linarith
        · rw [Nat.sub_eq_zero_of_le h]; simp; linarith
      · rw [h1]; simp; linarith
    calc ‖f (L - 1) • G L - ∑ i ∈ Finset.Ico N (L - 1), (f (i + 1) - f i) • G (i + 1)‖
        ≤ ‖f (L - 1) • G L‖ + ‖∑ i ∈ Finset.Ico N (L - 1), (f (i + 1) - f i) • G (i + 1)‖ :=
          norm_sub_le _ _
      _ ≤ K + ∑ i ∈ Finset.Ico N (L - 1), (2 * π * |β|) * K := by
          gcongr
          · rw [norm_smul, hf]; simp only; rw [psum_norm_fourier, one_mul]; exact hGK L
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [norm_smul]
            exact mul_le_mul (hdiff i) (hGK _) (norm_nonneg _) (by positivity)
      _ = K + ((Finset.Ico N (L - 1)).card : ℝ) * (2 * π * |β|) * K := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ K + (Y + 1) * (2 * π * |β|) * K := by gcongr
      _ = K * (1 + 2 * π * |β| * (Y + 1)) := by ring
  · push Not at hNL
    rw [Finset.Ico_eq_empty_of_le hNL, Finset.sum_empty, norm_zero]
    positivity

/-! ## Proved pieces -/

/-- PROVED. The size facts of the block range: for large X, with P = (log X)^B,
2 P^6 is below X^(7/18), 4 P is at most X, and 2 X^(7/9) is at most X. -/
theorem block_large (B : ℝ) (_hB : 0 < B) : ∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X →
    2 * (Real.log X ^ B) ^ 6 < X ^ (7 / 18 : ℝ) ∧ 4 * Real.log X ^ B ≤ X ∧
      2 * X ^ (7 / 9 : ℝ) ≤ X ∧ 1 ≤ X := by
  have h1 := (isLittleO_log_rpow_rpow_atTop (6 * B) (by norm_num : (0 : ℝ) < 7 / 18)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have h2 := (isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have h3 := (isLittleO_log_rpow_rpow_atTop 0 (by norm_num : (0 : ℝ) < 2 / 9)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp
    (((h1.and h2).and h3).and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨X1, fun X hX => ?_⟩
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, hX1'⟩ := hX1 X hX
  have hX0 : 0 < X := by linarith
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX1'
  have hp1 : 0 < X ^ (7 / 18 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hp3 : 0 < X ^ (2 / 9 : ℝ) := Real.rpow_pos_of_pos hX0 _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL _), Real.norm_of_nonneg hp1.le] at k1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL _), Real.norm_of_nonneg (by positivity),
    Real.rpow_one] at k2
  rw [Real.rpow_zero, norm_one, Real.norm_of_nonneg hp3.le] at k3
  have h6 : (Real.log X ^ B) ^ 6 = Real.log X ^ (6 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]; norm_num; ring_nf
  refine ⟨?_, by linarith, ?_, hX1'⟩
  · rw [h6]; linarith
  · have hsplit : X = X ^ (2 / 9 : ℝ) * X ^ (7 / 9 : ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    have h79 : 0 ≤ X ^ (7 / 9 : ℝ) := (Real.rpow_pos_of_pos hX0 _).le
    calc 2 * X ^ (7 / 9 : ℝ) ≤ X ^ (2 / 9 : ℝ) * X ^ (7 / 9 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) h79
      _ = X := hsplit.symm

/-- The exact statement of Prep1121DKLMajorCut.S1_sub_S1star_on_M0, from the five
pieces above and block_large, CONDITIONAL ON A12Corr. No sorry of its own. -/
theorem S1_sub_S1star_on_M0_of_leaves (hA : A12Corr) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α ∈ Set.Ioc (0 : ℝ) 1 ∩
            majorArcs (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ)) (Real.log X ^ B),
          ‖primeSum X (windowY X ε) α - S1star X (windowY X ε) H (Real.log X ^ B) α‖ ≤
            C * windowY X ε * (Real.log X ^ B) ^ (-2 : ℝ) := by
  intro B hB ε hε hε'
  obtain ⟨CA, XA, hCA, hA'⟩ := hA B hB ε hε hε'
  obtain ⟨X1, hX1⟩ := block_large B hB
  refine ⟨CA * (1 + 4 * π), max (max XA X1) 3, by positivity, ?_⟩
  intro X H hX hlo hhi α hα
  have hXA : XA ≤ X := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hX
  have hXX1 : X1 ≤ X := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hX
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans hX
  obtain ⟨k6, k4, k79, -⟩ := hX1 X hXX1
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX3
  have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB.le
  have hY1 := Prep1121DKLMajorCut.windowY_ge_one (by linarith : (1 : ℝ) ≤ X) hε
  have hYX : windowY X ε ≤ X ^ (7 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hX718 : X ^ (7 / 18 : ℝ) ≤ X ^ (7 / 18 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set Y := windowY X ε with hYdef
  set P := Real.log X ^ B with hPdef
  have hP : 0 < P := by linarith
  have hY : 0 < Y := by linarith
  obtain ⟨hαI, q, hq1, hqP, a, hcop, hclose⟩ := hα
  have : NeZero q := ⟨by omega⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  -- the block range gives H above 2 P^2
  have hP4 : P ^ (-4 : ℤ) = (P ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
  have hH : 2 * P ^ 2 < H := by
    have h1 : 2 * P ^ 2 = 2 * P ^ 6 * (P ^ 4)⁻¹ := by field_simp
    have h2 : 2 * P ^ 6 * (P ^ 4)⁻¹ < X ^ (7 / 18 + ε) * (P ^ 4)⁻¹ :=
      mul_lt_mul_of_pos_right (k6.trans_le hX718) (by positivity)
    rw [hP4] at hlo
    linarith
  have hHpos : 0 < H := by nlinarith
  -- M0 lies in M, as in arcs_subset
  have hP2 : P ^ (-4 : ℤ) ≤ P ^ (-2 : ℤ) := zpow_le_zpow_right₀ hP1 (by norm_num)
  have hH2 : H ≤ Y * P ^ (-2 : ℤ) := hhi.trans (mul_le_mul_of_nonneg_left hP2 hY.le)
  have hinv : (Y * P ^ (-2 : ℤ) / P)⁻¹ ≤ (H / P)⁻¹ :=
    inv_anti₀ (div_pos hHpos hP) (div_le_div_of_nonneg_right hH2 hP.le)
  have hstar := S1star_on_arc X Y H P α q a hP1 hH hαI hq1 hqP hcop (hclose.trans hinv)
  have hw : (Y * P ^ (-2 : ℤ) / P)⁻¹ = P ^ 3 / Y := by
    rw [zpow_neg, zpow_two]; field_simp
  set β := α - (a : ℝ) / q with hβdef
  have hqβ : (q : ℝ) * |β| ≤ P ^ 3 / Y := by
    have e1 : (q : ℝ) * α - a = q * β := by rw [hβdef]; field_simp
    rw [e1, abs_mul, abs_of_pos hq0, hw] at hclose
    exact hclose
  -- no prime of the window divides q
  have hcopm : ∀ m ∈ primeWindow X Y, m.Prime → Nat.Coprime m q := by
    intro m hm hp
    simp only [primeWindow, Finset.mem_filter] at hm
    have hmX : X - Y ≤ (m : ℝ) := hm.2.1
    have hqm : (q : ℝ) < m := by linarith
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => ?_)
    have h' := Nat.le_of_dvd (by omega) h
    have h'' : (m : ℝ) ≤ q := by exact_mod_cast h'
    linarith
  have haU : IsUnit (a : ZMod q) := by
    obtain ⟨u, v, huv⟩ := hcop
    refine IsUnit.of_mul_eq_one (u : ZMod q) ?_
    have := congrArg (fun z : ℤ => (z : ZMod q)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
      add_zero, Int.cast_one] at this
    rw [mul_comm]; exact this
  have hsplit : ∀ m : ℕ, fourier (m : ℤ) (α : AddCircle (1 : ℝ)) =
      fourier (m : ℤ) ((((a : ℝ) / q : ℝ)) : AddCircle (1 : ℝ)) *
        fourier (m : ℤ) (β : AddCircle (1 : ℝ)) := by
    intro m
    rw [fourier_coe_apply, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
    congr 1
    rw [hβdef]; push_cast; ring
  -- the character expansion of display 25
  set ψ := (ZMod.stdAddChar (N := q)) with hψ
  let c : DirichletCharacter ℂ q → ℂ := fun χ =>
    gaussSum χ⁻¹ ψ * χ (a : ZMod q) / (Nat.totient q : ℂ)
  let d : DirichletCharacter ℂ q → ℕ → ℂ := fun χ m =>
    (if m.Prime then χ m else 0) -
      (if χ = 1 then ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0)
  have hc1 : c 1 = ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) := by
    simp only [c, inv_one, hψ, gaussSum_one_eq_moebius, MulChar.one_apply haU, mul_one]
  have hid : primeSum X Y α - S1star X Y H P α =
      ∑ χ : DirichletCharacter ℂ q, c χ *
        ∑ m ∈ primeWindow X Y, d χ m * fourier (m : ℤ) (β : AddCircle (1 : ℝ)) := by
    rw [hstar]
    unfold primeSum T1
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hd : ∀ χ : DirichletCharacter ℂ q,
        c χ * (d χ m * fourier (m : ℤ) (β : AddCircle (1 : ℝ))) =
        (c χ * (if m.Prime then χ m else 0) -
          (if χ = 1 then c χ * ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0)) *
            fourier (m : ℤ) (β : AddCircle (1 : ℝ)) := by
      intro χ; simp only [d]; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun χ _ => hd χ), ← Finset.sum_mul, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hc1]
    by_cases hp : m.Prime
    · have hce : ∑ χ : DirichletCharacter ℂ q, c χ * χ (m : ZMod q) =
          fourier (m : ℤ) ((((a : ℝ) / q : ℝ)) : AddCircle (1 : ℝ)) :=
        char_expansion q a m hcop (hcopm m hm hp)
      simp only [hp, ite_true]
      rw [hce, hsplit m]
      ring
    · simp only [hp, ite_false, mul_zero, Finset.sum_const_zero]
      ring
  -- each W1 by partial summation and A12Corr
  have hW : ∀ χ : DirichletCharacter ℂ q,
      ‖∑ m ∈ primeWindow X Y, d χ m * fourier (m : ℤ) (β : AddCircle (1 : ℝ))‖ ≤
        CA * Y * P ^ (-5 : ℤ) * (1 + 2 * π * |β| * (Y + 1)) := by
    intro χ
    refine partial_summation_window X Y _ β hY.le (d χ) ?_
    intro u v hu huv hv
    exact hA' X hXA q hq1 hqP χ u v hu huv hv
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hcn : ∀ χ : DirichletCharacter ℂ q, ‖c χ‖ ≤ Real.sqrt q / (Nat.totient q : ℝ) := by
    intro χ
    simp only [c, norm_div, norm_mul, Complex.norm_natCast]
    have h1 := norm_gaussSum_le_sqrt q χ⁻¹
    have h2 := DirichletCharacter.norm_le_one χ (a : ZMod q)
    refine div_le_div_of_nonneg_right ?_ hφ.le
    calc ‖gaussSum χ⁻¹ ψ‖ * ‖χ (a : ZMod q)‖ ≤ Real.sqrt q * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt q := mul_one _
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = Nat.totient q := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hP5 : 0 < P ^ (-5 : ℤ) := zpow_pos hP _
  have hK0 : 0 ≤ CA * Y * P ^ (-5 : ℤ) * (1 + 2 * π * |β| * (Y + 1)) := by
    have : 0 ≤ 1 + 2 * π * |β| * (Y + 1) := by
      have := abs_nonneg β; have := Real.pi_pos; positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hCA.le hY.le) hP5.le) this
  -- the final arithmetic of display 25 with |beta| at most P^3/(qY)
  have hs1 : 1 ≤ Real.sqrt q := Real.one_le_sqrt.2 (by exact_mod_cast hq1)
  have hss : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0.le
  have hsP : Real.sqrt q ≤ P := by
    have h := le_mul_of_one_le_right (Real.sqrt_nonneg (q : ℝ)) hs1
    rw [hss] at h
    linarith
  have hP3 : P ≤ P ^ 3 := le_self_pow₀ hP1 (by norm_num)
  have hsβ : Real.sqrt q * |β| ≤ P ^ 3 / Y := by
    calc Real.sqrt q * |β| ≤ Real.sqrt q * (Real.sqrt q * |β|) :=
          le_mul_of_one_le_left (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hs1
      _ = q * |β| := by rw [← mul_assoc, hss]
      _ ≤ P ^ 3 / Y := hqβ
  have hinner : Real.sqrt q * (1 + 2 * π * |β| * (Y + 1)) ≤ (1 + 4 * π) * P ^ 3 := by
    have h1 : Real.sqrt q * |β| * (Y + 1) ≤ 2 * P ^ 3 := by
      calc Real.sqrt q * |β| * (Y + 1) ≤ P ^ 3 / Y * (2 * Y) :=
            mul_le_mul hsβ (by linarith) (by positivity) (by positivity)
        _ = 2 * P ^ 3 := by field_simp
    have h2 : 2 * π * (Real.sqrt q * |β| * (Y + 1)) ≤ 2 * π * (2 * P ^ 3) :=
      mul_le_mul_of_nonneg_left h1 (by have := Real.pi_pos; positivity)
    have h3 : Real.sqrt q * (1 + 2 * π * |β| * (Y + 1)) =
        Real.sqrt q + 2 * π * (Real.sqrt q * |β| * (Y + 1)) := by ring
    rw [h3]
    nlinarith [h2, hsP, hP3]
  have hpow : P ^ (-5 : ℤ) * P ^ 3 = P ^ (-2 : ℝ) := by
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, ← zpow_natCast,
      ← zpow_add₀ hP.ne']
    norm_num
  rw [hid]
  calc ‖∑ χ : DirichletCharacter ℂ q, c χ *
          ∑ m ∈ primeWindow X Y, d χ m * fourier (m : ℤ) (β : AddCircle (1 : ℝ))‖
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖c χ *
          ∑ m ∈ primeWindow X Y, d χ m * fourier (m : ℤ) (β : AddCircle (1 : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _χ : DirichletCharacter ℂ q, Real.sqrt q / (Nat.totient q : ℝ) *
          (CA * Y * P ^ (-5 : ℤ) * (1 + 2 * π * |β| * (Y + 1))) := by
        refine Finset.sum_le_sum fun χ _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hcn χ) (hW χ) (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hφ.le)
    _ = Real.sqrt q * (CA * Y * P ^ (-5 : ℤ) * (1 + 2 * π * |β| * (Y + 1))) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        field_simp
    _ = CA * Y * P ^ (-5 : ℤ) * (Real.sqrt q * (1 + 2 * π * |β| * (Y + 1))) := by ring
    _ ≤ CA * Y * P ^ (-5 : ℤ) * ((1 + 4 * π) * P ^ 3) :=
        mul_le_mul_of_nonneg_left hinner (mul_nonneg (mul_nonneg hCA.le hY.le) hP5.le)
    _ = CA * (1 + 4 * π) * Y * (P ^ (-5 : ℤ) * P ^ 3) := by ring
    _ = CA * (1 + 4 * π) * Y * P ^ (-2 : ℝ) := by rw [hpow]

example : type_of% @Prep1121DKLMajorCut.S1_sub_S1star_on_M0 :=
  S1_sub_S1star_on_M0_of_leaves

end LeanLab.KumchevLiu2007.Prep1122S1StarM0Cut

#print axioms LeanLab.KumchevLiu2007.Prep1122S1StarM0Cut.S1star_on_arc
#print axioms LeanLab.KumchevLiu2007.Prep1122S1StarM0Cut.char_expansion
#print axioms LeanLab.KumchevLiu2007.Prep1122S1StarM0Cut.gaussSum_one_eq_moebius
#print axioms LeanLab.KumchevLiu2007.Prep1122S1StarM0Cut.norm_gaussSum_le_sqrt
#print axioms LeanLab.KumchevLiu2007.Prep1122S1StarM0Cut.partial_summation_window
#print axioms LeanLab.KumchevLiu2007.Prep1122S1StarM0Cut.block_large
#print axioms LeanLab.KumchevLiu2007.Prep1122S1StarM0Cut.S1_sub_S1star_on_M0_of_leaves
