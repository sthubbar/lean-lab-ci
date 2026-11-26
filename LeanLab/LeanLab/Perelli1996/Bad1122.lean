/-
P0083 Perelli 1996, pages 484 and 485, displays 19 through 24.
ROUTE BURST S79 burst-20261122 split of Char1122.leaf_bad_character_removal, display 24.
Display 20 and display 23 are new LEAFs; the step from them to 24, through the full
period Parseval bound of CharacterMoment632 and the totient factor of CharacterTail632,
is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Char1122
import LeanLab.Perelli1996.CharacterMoment632
import LeanLab.Perelli1996.CharacterTail632
import LeanLab.Perelli1996.BadMod1123

namespace LeanLab.Perelli1996.Bad1122
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp582a LeanLab.Perelli1996.Char1122
open scoped ArithmeticFunction.vonMangoldt
noncomputable section

attribute [local instance] Classical.propDecidable

/-- LEAF: Page 484 display 20, from the zero free region 19 of Prachar Chapter 8 together
with Siegel's theorem: for every ε' > 0, a bad character modulo q forces q ≫_{ε'} L^(1/(2ε')).
Here P stands for 1/(2ε'), so P > 0 is arbitrary, and L = log N.
Class HARD. Cited inputs: Prachar Chapter 8 and Siegel's theorem. -/
theorem leaf_bad_modulus_large (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) (P : ℝ) (hP : 0 < P) :
    ∃ c' N₀ : ℝ, 0 < c' ∧ 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), ¬ goodCharacter B ε N χ →
        c' * Real.log N ^ P ≤ q :=
  BadMod1123.leaf_bad_modulus_large_of_split1123 B ε hB hε P hP

/-- Page 485 display 23, the Gauss sum bound τ(χ) ≪ q^(1/2) used there:
|τ(χ)| ≤ √q for every Dirichlet character mod q. Montgomery and Vaughan Theorem 9.10.
Proof copied from DERZ1997.Decomp1529c.gaussSum_norm_le. -/
theorem gaussSum_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ √q := by
  classical
  let e136 : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  let G : ZMod q → ℂ := fun a => gaussSum χ (e136.mulShift a)
  have hortho (t : ZMod q) : ∑ a : ZMod q, e136 (t * a) = if t = 0 then (q : ℂ) else 0 := by
    by_cases ht : t = 0
    · simp [ht, e136]
    · rw [ite_eq_right ht]
      exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ht)
  have hstar (x : ZMod q) : star (e136 x) = e136 (-x) := by
    simpa [e136, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv] using
      (Complex.inv_eq_conj (Circle.norm_coe (ZMod.toCircle x))).symm
  have henergy : (∑ a : ZMod q, G a * star (G a)) =
      q * ∑ x : ZMod q, χ x * star (χ x) := by
    simp only [G, gaussSum, star_sum, star_mul, AddChar.mulShift_apply]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    have hterm (a y : ZMod q) :
        χ x * e136 (a * x) * (star (e136 (a * y)) * star (χ y)) =
          (χ x * star (χ y)) * e136 ((x - y) * a) := by
      rw [hstar]
      calc
        _ = (χ x * star (χ y)) * (e136 (a * x) * e136 (-(a * y))) := by ring
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
  have hunit (u : (ZMod q)ˣ) : ‖G u‖ = ‖gaussSum χ e136‖ := by
    dsimp [G]
    rw [gaussSum_mulShift_eq, norm_mul, DirichletCharacter.unit_norm_eq_one, one_mul]
  have htriv : (∑ a : ZMod q, ((1 : DirichletCharacter ℂ q) a).re) = (q.totient : ℝ) := by
    have h := MulChar.sum_one_eq_card_units (R := ZMod q) (R' := ℂ)
    rw [ZMod.card_units_eq_totient] at h
    have hh := congrArg (fun z : ℂ => Complex.reCLM z) h
    rw [map_sum] at hh
    simpa using hh
  have hlow : (q.totient : ℝ) * ‖gaussSum χ e136‖ ^ 2 ≤ ∑ a : ZMod q, ‖G a‖ ^ 2 := by
    calc
      _ = ∑ a : ZMod q, ((1 : DirichletCharacter ℂ q) a).re * ‖gaussSum χ e136‖ ^ 2 := by
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
  change ‖gaussSum χ e136‖ ^ 2 ≤ (q : ℝ)
  rw [hreal] at hlow
  nlinarith


/-- Page 484, additive characters through multiplicative ones: for a unit m mod q,
e(m/q) = φ(q)⁻¹ ∑_χ χ(m⁻¹) τ(χ). Proof copied from DERZ1997.Decomp1529c. -/
theorem stdAddChar_eq_sum_gauss {q : ℕ} [NeZero q] {m : ZMod q} (hm : IsUnit m) :
    ZMod.stdAddChar m = (1 / (q.totient : ℂ)) *
      ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * gaussSum χ ZMod.stdAddChar := by
  unfold gaussSum
  have h_inner : ∀ χ : DirichletCharacter ℂ q,
      χ m⁻¹ * ∑ a : ZMod q, χ a * ZMod.stdAddChar a =
      ∑ a : ZMod q, χ m⁻¹ * (χ a * ZMod.stdAddChar a) := by
    intro χ
    rw [Finset.mul_sum]
  simp_rw [h_inner]
  rw [Finset.sum_comm]
  have h_sum : ∀ a : ZMod q,
      ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * (χ a * ZMod.stdAddChar a) =
      (∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * χ a) * ZMod.stdAddChar a := by
    intro a
    have : (fun χ : DirichletCharacter ℂ q => χ m⁻¹ * (χ a * ZMod.stdAddChar a)) = (fun χ : DirichletCharacter ℂ q => (χ m⁻¹ * χ a) * ZMod.stdAddChar a) := by
      ext χ
      rw [mul_assoc]
    rw [this, Finset.sum_mul]
  simp_rw [h_sum]
  have h_char_sum : ∀ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * χ a = if m = a then (q.totient : ℂ) else 0 := by
    intro a
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hm]
  simp_rw [h_char_sum]
  have h_eval : ∑ a : ZMod q, (if m = a then (q.totient : ℂ) else 0) * ZMod.stdAddChar a = (q.totient : ℂ) * ZMod.stdAddChar m := by
    rw [Finset.sum_eq_single m]
    · split_ifs with h_if
      · rfl
      · contradiction
    · intro b _ hb
      split_ifs with h_if
      · exact False.elim (hb h_if.symm)
      · rw [zero_mul]
    · intro h
      exfalso
      exact h (Finset.mem_univ m)
  rw [h_eval, ← mul_assoc]
  have h_div : (1 / (q.totient : ℂ)) * (q.totient : ℂ) = 1 := by
    rw [one_div, inv_mul_cancel₀]
    have h_totient_pos : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast ne_of_gt h_totient_pos
  rw [h_div, one_mul]

/-- χ(m⁻¹) = χ⁻¹(m) at a unit m. -/
theorem char_inv_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {m : ZMod q} (hm : IsUnit m) : χ m⁻¹ = χ⁻¹ m := by
  rw [MulChar.inv_apply, ← hm.unit_spec, Ring.inverse_unit, ZMod.inv_coe_unit]

/-- Page 484, the character expansion coefficient: for units A and m mod q,
∑_χ χ(A) τ(χ̄) χ(m) = φ(q) e(Am/q). -/
theorem coeff_unit {q : ℕ} [NeZero q] {A m : ZMod q} (hA : IsUnit A) (hm : IsUnit m) :
    ∑ χ : DirichletCharacter ℂ q, χ A * gaussSum χ⁻¹ ZMod.stdAddChar * χ m =
      (q.totient : ℂ) * ZMod.stdAddChar (A * m) := by
  have hAm : IsUnit (A * m) := hA.mul hm
  have h1 : ∀ χ : DirichletCharacter ℂ q, χ A * gaussSum χ⁻¹ ZMod.stdAddChar * χ m =
      (fun ψ : DirichletCharacter ℂ q => ψ (A * m)⁻¹ * gaussSum ψ ZMod.stdAddChar) χ⁻¹ := by
    intro χ
    simp only
    rw [char_inv_unit χ⁻¹ hAm, inv_inv, map_mul]
    ring
  simp_rw [h1]
  have hre : (∑ x : DirichletCharacter ℂ q, x⁻¹ (A * m)⁻¹ * gaussSum x⁻¹ ZMod.stdAddChar) =
      ∑ ψ : DirichletCharacter ℂ q, ψ (A * m)⁻¹ * gaussSum ψ ZMod.stdAddChar :=
    Fintype.sum_equiv (Equiv.inv _) _ _ (fun x => rfl)
  rw [hre]
  rw [stdAddChar_eq_sum_gauss hAm, ← mul_assoc]
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  field_simp

/-- e(n(a/q + η)) = e(an/q) e(nη), with e(an/q) as the standard additive character. -/
theorem e_split (q : ℕ) [NeZero q] (a : ℤ) (n : ℕ) (η : ℝ) :
    Kernel.e ((n : ℝ) * ((a : ℝ) / q + η)) =
      ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) * Kernel.e ((n : ℝ) * η) := by
  have h := ZMod.stdAddChar_coe (N := q) (a * n)
  push_cast at h
  rw [h]
  unfold Kernel.e
  rw [← Complex.exp_add]
  congr 1
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  push_cast
  field_simp

/-- τ(χ₀) = c_q(1) = μ(q), from Ramanujan103.ramanujanSum_coprime. -/
theorem gaussSum_one' {q : ℕ} [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar = (ArithmeticFunction.moebius q : ℂ) := by
  classical
  have hsum : gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar =
      Ramanujan103.ramanujanSum q 1 := by
    unfold gaussSum Ramanujan103.ramanujanSum
    rw [Finset.sum_filter]
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _
      exact Finset.mem_range.mpr a.val_lt
    · intro a _ b _ h
      exact ZMod.val_injective q h
    · intro b hb
      refine ⟨(b : ZMod q), Finset.mem_univ _, ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)]
    · intro a _
      have hcop : IsUnit a ↔ Nat.Coprime a.val q := by
        rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
      by_cases ha : IsUnit a
      · rw [MulChar.one_apply ha, one_mul, if_pos (hcop.mp ha)]
        have he := ZMod.stdAddChar_coe (N := q) (a.val : ℤ)
        simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at he
        rw [he]
        unfold Kernel.e
        congr 1
        push_cast
        ring
      · rw [MulChar.map_nonunit _ ha, zero_mul, if_neg (fun h => ha (hcop.mpr h))]
  rw [hsum]
  exact Ramanujan103.ramanujanSum_coprime q 1 (NeZero.pos q) (Nat.coprime_one_right q)

/-- Page 484 before display 16, the exact character expansion of R(η,q,a): the
difference from φ(q)⁻¹ ∑_χ χ(a) τ(χ̄) W(χ,η) is the sum over n ≤ M not coprime to q. -/
theorem expansion_identity (M q : ℕ) [NeZero q] (a : ℤ) (hA : IsUnit (a : ZMod q)) (η : ℝ) :
    characterRemainder M q a η - (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
      χ (a : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar * twistedRemainder M χ η =
      ∑ n ∈ range (M + 1), if IsUnit (n : ZMod q) then 0 else
        (Λ n : ℂ) * Kernel.e ((n : ℝ) * ((a : ℝ) / q + η)) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  set A : ZMod q := (a : ZMod q)
  have hc : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q, χ A * gaussSum χ⁻¹ ZMod.stdAddChar * χ n =
      if IsUnit (n : ZMod q) then (q.totient : ℂ) * ZMod.stdAddChar (A * (n : ZMod q)) else 0 := by
    intro n
    split_ifs with hn
    · exact coeff_unit hA hn
    · apply Finset.sum_eq_zero; intro χ _; rw [MulChar.map_nonunit χ hn, mul_zero]
  have hsplit : ∀ χ : DirichletCharacter ℂ q,
      χ A * gaussSum χ⁻¹ ZMod.stdAddChar * twistedRemainder M χ η =
      (∑ n ∈ range (M + 1), (Λ n : ℂ) * Kernel.e ((n : ℝ) * η) *
        (χ A * gaussSum χ⁻¹ ZMod.stdAddChar * χ n)) -
      (if χ = 1 then χ A * gaussSum χ⁻¹ ZMod.stdAddChar * Kernel.T 0 (M + 1) η else 0) := by
    intro χ
    unfold twistedRemainder
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro n _; ring
    · split_ifs <;> simp
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hc]
  rw [Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ q), if_pos (Finset.mem_univ _),
    MulChar.one_apply hA, inv_one, gaussSum_one']
  unfold characterRemainder primeSum
  rw [mul_sub, Finset.mul_sum]
  have hterm : ∀ n ∈ range (M + 1), (Λ n : ℂ) * Kernel.e ((n : ℝ) * ((a : ℝ) / q + η)) -
      1 / (q.totient : ℂ) * ((Λ n : ℂ) * Kernel.e ((n : ℝ) * η) *
        (if IsUnit (n : ZMod q) then (q.totient : ℂ) * ZMod.stdAddChar (A * (n : ZMod q)) else 0)) =
      if IsUnit (n : ZMod q) then 0 else (Λ n : ℂ) * Kernel.e ((n : ℝ) * ((a : ℝ) / q + η)) := by
    intro n _
    rw [e_split q a n η]
    split_ifs
    · field_simp; ring
    · ring
  rw [← Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  push_cast
  ring

/-- For a prime p, ∑_{n ≤ M, p | n} Λ(n) = log p^K ≤ log(M+1) with K = ⌊log_p M⌋. -/
theorem prime_multiple_vonMangoldt_le (M p : ℕ) (hp : p.Prime) :
    (∑ n ∈ range (M + 1), if p ∣ n then Λ n else 0) ≤ Real.log (M + 1) := by
  set g : ℕ → ℝ := fun n => if p ∣ n then Λ n else 0 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    simp only [hg]; split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl
  set K := Nat.log p M
  have hsub : (range (M + 1)).filter (fun n => g n ≠ 0) ⊆ (p ^ K).divisors := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnM, hgn⟩ := hn
    have hpn : p ∣ n := by by_contra h; simp [hg, h] at hgn
    have hΛ : Λ n ≠ 0 := by simpa [hg, hpn] using hgn
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hΛ
    obtain ⟨r, k, hr, hk, hrk⟩ := hΛ
    have hr' : r.Prime := hr.nat_prime
    have hpr : p = r := by
      have : p ∣ r := hp.dvd_of_dvd_pow (hrk ▸ hpn)
      exact (Nat.prime_dvd_prime_iff_eq hp hr').mp this
    subst hpr
    have hkK : k ≤ K := Nat.le_log_of_pow_le hp.one_lt (by omega)
    rw [Nat.mem_divisors]
    exact ⟨hrk ▸ pow_dvd_pow p hkK, pow_ne_zero _ hp.ne_zero⟩
  calc (∑ n ∈ range (M + 1), g n) = ∑ n ∈ (range (M + 1)).filter (fun n => g n ≠ 0), g n :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ (p ^ K).divisors, g n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hg0 n)
    _ ≤ ∑ n ∈ (p ^ K).divisors, Λ n := by
        apply Finset.sum_le_sum; intro n _; simp only [hg]; split_ifs
        · exact le_rfl
        · exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log ((p ^ K : ℕ) : ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ ≤ Real.log (M + 1) := by
        have hle : p ^ K ≤ M + 1 := by
          rcases Nat.eq_zero_or_pos M with h | h
          · simp [K, h]
          · exact (Nat.pow_log_le_self p h.ne').trans (Nat.le_succ M)
        apply Real.log_le_log (by exact_mod_cast pow_pos hp.pos K)
        exact_mod_cast hle

/-- ∑_{n ≤ M, (n,q) > 1} Λ(n) ≤ ω(q) log(M+1) ≤ 2 log q log(M+1). -/
theorem nonunit_vonMangoldt_le (M q : ℕ) [NeZero q] :
    (∑ n ∈ range (M + 1), if IsUnit (n : ZMod q) then 0 else Λ n) ≤
      2 * Real.log q * Real.log (M + 1) := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hpt : ∀ n ∈ range (M + 1), (if IsUnit (n : ZMod q) then 0 else Λ n) ≤
      ∑ p ∈ q.primeFactors, if p ∣ n then Λ n else 0 := by
    intro n _
    split_ifs with hu
    · apply Finset.sum_nonneg; intro p _; split_ifs
      · exact ArithmeticFunction.vonMangoldt_nonneg
      · exact le_rfl
    · rw [ZMod.isUnit_iff_coprime] at hu
      obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hu
      have hmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, hq0⟩
      have := Finset.single_le_sum (f := fun p => if p ∣ n then Λ n else 0)
        (fun p _ => by
          show 0 ≤ (if p ∣ n then Λ n else 0)
          split_ifs
          · exact ArithmeticFunction.vonMangoldt_nonneg
          · exact le_rfl) hmem
      simpa [hpn] using this
  have hcardlog : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
    have h1 : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
      Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    have h2 : ∏ p ∈ q.primeFactors, p ≤ q :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (Nat.prod_primeFactors_dvd q)
    have h3 : ((2 ^ q.primeFactors.card : ℕ) : ℝ) ≤ q := by exact_mod_cast h1.trans h2
    have := Real.log_le_log (by positivity) h3
    rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at this
  have hlog2 := Real.log_two_gt_d9
  have hlogM : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by have := M.cast_nonneg (α := ℝ); linarith)
  have hcard : (q.primeFactors.card : ℝ) ≤ 2 * Real.log q := by
    have : (0 : ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
    nlinarith
  calc (∑ n ∈ range (M + 1), if IsUnit (n : ZMod q) then 0 else Λ n)
      ≤ ∑ n ∈ range (M + 1), ∑ p ∈ q.primeFactors, if p ∣ n then Λ n else 0 :=
        Finset.sum_le_sum hpt
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ range (M + 1), if p ∣ n then Λ n else 0 := Finset.sum_comm
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (M + 1) := by
        apply Finset.sum_le_sum; intro p hp
        exact prime_multiple_vonMangoldt_le M p (Nat.prime_of_mem_primeFactors hp)
    _ = (q.primeFactors.card : ℝ) * Real.log (M + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * Real.log q * Real.log (M + 1) := by gcongr

/-- Page 484, the prime powers p^k ≤ M with p | q contribute at most
2 log q log(M+1) to the character expansion of R(η,q,a). -/
theorem char_expansion_error (M q : ℕ) [NeZero q] (a : ℤ) (hcop : Nat.Coprime a.natAbs q) (η : ℝ) :
    ‖characterRemainder M q a η - (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
      χ (a : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar * twistedRemainder M χ η‖ ≤
      2 * Real.log q * Real.log (M + 1) := by
  have hA : IsUnit (a : ZMod q) := by
    have hu : IsUnit ((a.natAbs : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
    rcases Int.natAbs_eq a with h | h
    · rw [h]; simpa using hu
    · rw [h, Int.cast_neg, Int.cast_natCast]; exact hu.neg
  rw [expansion_identity M q a hA η]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => ?_).trans
    (nonunit_vonMangoldt_le M q))
  split_ifs
  · simp
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    unfold Kernel.e
    rw [Complex.norm_exp]
    simp

/-- The good character energy is nonnegative; the same as goodEnergy_nonneg below. -/
theorem goodEnergy_nonneg_aux (B ε N : ℝ) (M q : ℕ) [NeZero q] (Q : ℝ) (hQ : 0 < Q) :
    0 ≤ goodEnergy B ε N M q Q := by
  unfold goodEnergy
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro χ _
  split_ifs
  · apply intervalIntegral.integral_nonneg
    · have : 0 < 1 / ((q : ℝ) * Q) := by positivity
      linarith
    · intro η _; positivity
  · exact le_refl 0

/-- Page 485 display 22, from the density estimate 21 with T = N and
1 - σ = 10 (B/ε) log L / L: the number of characters mod q ≤ N that are not good is
at most C₀ L^(e₀), with e₀ depending only on B, ε and the density exponent d.
Each such character has a zero ρ ≠ 1 with σ ≤ Re ρ < 1, |Im ρ| ≤ N, since L(s,χ) has
no zero on Re s = 1 other than the pole, so bad_character_count_le applies. With q ≤ N, (qN)^(12(1-σ)/5) ≤ L^(48B/ε) and
log(qN)^d ≤ 2^d L^d, so e₀ = 48B/ε + d; compare the QUESTION on display 22 in the
burst-20261122 notes. CONDITIONAL ON display 21 through hDensity. -/
theorem bad_count (C d : ℝ) (hC : 0 < C) (hd : 0 < d) (hDensity : DensityInput C d)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ e₀ C₀ N₀ : ℝ, 0 ≤ e₀ ∧ 0 < C₀ ∧ 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ N →
        ((univ.filter (fun χ : DirichletCharacter ℂ q => ¬ goodCharacter B ε N χ)).card : ℝ) ≤
          C₀ * Real.log N ^ e₀ := by
  refine ⟨48 * (B / ε) + d, C * 2 ^ d, max 3 (Real.exp ((40 * (B / ε)) ^ 2 + 1)),
    by positivity, by positivity, le_max_left _ _, ?_⟩
  intro N hN q _ hqN
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNE : Real.exp ((40 * (B / ε)) ^ 2 + 1) ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := by linarith
  set L := Real.log N with hLdef
  have hLbig : (40 * (B / ε)) ^ 2 + 1 ≤ L := by
    rw [hLdef, ← Real.log_exp ((40 * (B / ε)) ^ 2 + 1)]
    exact Real.log_le_log (Real.exp_pos _) hNE
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg (40 * (B / ε))]
  have hL0 : 0 < L := by linarith
  have hBe : 0 < B / ε := by positivity
  -- log L ≤ 2 √L and the strip width
  set s := Real.sqrt L with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hL0
  have hss : s * s = L := Real.mul_self_sqrt hL0.le
  have hlogL : Real.log L ≤ 2 * s := by
    have h1 : Real.log s = Real.log L / 2 := Real.log_sqrt hL0.le
    have h2 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
    linarith
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hsbig : 40 * (B / ε) ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; linarith
  set δ := 10 * (B / ε) * Real.log L / L with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ hL0]
    have : 10 * (B / ε) * Real.log L ≤ 10 * (B / ε) * (2 * s) := by gcongr
    nlinarith
  set σ := 1 - 10 * (B / ε) * Real.log L / L with hσ
  have hσδ : σ = 1 - δ := by rw [hσ, hδ]
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hden := hDensity q N σ (by linarith) (by linarith) (by linarith)
  have hcount := LeanLab.Perelli1996.Decomp582a.bad_character_count_le N σ _ hden
    (univ.filter (fun χ : DirichletCharacter ℂ q => ¬ goodCharacter B ε N χ)) (by
      intro χ hχ
      have hb := (Finset.mem_filter.mp hχ).2
      unfold goodCharacter at hb
      push_neg at hb
      obtain ⟨ρ, hρ1, hρσ, hρre, hρim, hρz⟩ := hb
      refine ⟨ρ, hρz, hρσ, ?_, hρim⟩
      rcases hρre.lt_or_eq with h | h
      · exact h
      · exact absurd hρz (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hρ1) h.ge))
  refine hcount.trans ?_
  -- bound the density majorant
  have hqN0 : 0 < (q : ℝ) * N := by positivity
  have hqN2 : (q : ℝ) * N ≤ N ^ 2 := by nlinarith
  have hexp : 0 ≤ 12 * (1 - σ) / 5 := by rw [hσδ]; linarith
  have hP : ((q : ℝ) * N) ^ (12 * (1 - σ) / 5) ≤ L ^ (48 * (B / ε)) := by
    calc ((q : ℝ) * N) ^ (12 * (1 - σ) / 5) ≤ (N ^ 2) ^ (12 * (1 - σ) / 5) :=
          Real.rpow_le_rpow hqN0.le hqN2 hexp
      _ = L ^ (48 * (B / ε)) := by
          rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hL0,
            Real.log_pow, hσδ, hδ]
          congr 1
          rw [← hLdef]
          field_simp
          ring
  have hlog1 : 0 ≤ Real.log ((q : ℝ) * N) := Real.log_nonneg (by nlinarith)
  have hlog2 : Real.log ((q : ℝ) * N) ≤ 2 * L := by
    have := Real.log_le_log hqN0 hqN2
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hD : Real.log ((q : ℝ) * N) ^ d ≤ 2 ^ d * L ^ d := by
    rw [← Real.mul_rpow (by norm_num) hL0.le]
    exact Real.rpow_le_rpow hlog1 hlog2 hd.le
  have hsplitpow : L ^ (48 * (B / ε) + d) = L ^ (48 * (B / ε)) * L ^ d := Real.rpow_add hL0 _ _
  rw [hsplitpow]
  have h1 : 0 ≤ ((q : ℝ) * N) ^ (12 * (1 - σ) / 5) := by positivity
  have h2 : 0 ≤ Real.log ((q : ℝ) * N) ^ d := by positivity
  calc C * ((q : ℝ) * N) ^ (12 * (1 - σ) / 5) * Real.log ((q : ℝ) * N) ^ d
      ≤ C * L ^ (48 * (B / ε)) * (2 ^ d * L ^ d) := by gcongr
    _ = C * 2 ^ d * (L ^ (48 * (B / ε)) * L ^ d) := by ring

/-- Page 485 display 23, pointwise form: the expansion, Cauchy Schwarz over the good
characters and over the bad characters with |τ(χ)|² ≤ q and at most φ(q) characters. -/
theorem pointwise_bound (M q : ℕ) [NeZero q] (a : ℤ) (hcop : Nat.Coprime a.natAbs q)
    (p : DirichletCharacter ℂ q → Prop) (η : ℝ) :
    ‖characterRemainder M q a η‖ ^ 2 ≤
      3 * ((q : ℝ) / q.totient * ∑ χ ∈ univ.filter p, ‖twistedRemainder M χ η‖ ^ 2 +
        (q : ℝ) / (q.totient : ℝ) ^ 2 * ((univ.filter (fun χ => ¬ p χ)).card : ℝ) *
          ∑ χ ∈ univ.filter (fun χ => ¬ p χ), ‖twistedRemainder M χ η‖ ^ 2 +
        (2 * Real.log q * Real.log (M + 1)) ^ 2) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  set u : DirichletCharacter ℂ q → ℂ := fun χ =>
    χ (a : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar * twistedRemainder M χ η with hudef
  have hu : ∀ χ, ‖u χ‖ ≤ √(q : ℝ) * ‖twistedRemainder M χ η‖ := by
    intro χ
    simp only [hudef, norm_mul]
    have h1 : ‖χ (a : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have h2 := gaussSum_norm_le χ⁻¹
    have h3 := norm_nonneg (twistedRemainder M χ η)
    calc _ ≤ 1 * √(q : ℝ) * ‖twistedRemainder M χ η‖ := by gcongr
      _ = _ := by ring
  have hcs : ∀ s : Finset (DirichletCharacter ℂ q),
      ‖∑ χ ∈ s, u χ‖ ^ 2 ≤ (s.card : ℝ) * q * ∑ χ ∈ s, ‖twistedRemainder M χ η‖ ^ 2 := by
    intro s
    calc ‖∑ χ ∈ s, u χ‖ ^ 2 ≤ (∑ χ ∈ s, √(q : ℝ) * ‖twistedRemainder M χ η‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => hu χ)
      _ ≤ (s.card : ℝ) * ∑ χ ∈ s, (√(q : ℝ) * ‖twistedRemainder M χ η‖) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro χ _
          rw [mul_pow, Real.sq_sqrt hq0]
          ring
  have hcard : ((univ.filter p).card : ℝ) ≤ q.totient := by
    have h1 : (univ.filter p).card ≤ (univ : Finset (DirichletCharacter ℂ q)).card :=
      card_filter_le _ _
    have h2 : (univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    exact_mod_cast h2 ▸ h1
  have hE := char_expansion_error M q a hcop η
  set K := 2 * Real.log q * Real.log (M + 1)
  set G := univ.filter p
  set Bd := univ.filter (fun χ : DirichletCharacter ℂ q => ¬ p χ)
  set SG := ∑ χ ∈ G, ‖twistedRemainder M χ η‖ ^ 2
  set SB := ∑ χ ∈ Bd, ‖twistedRemainder M χ η‖ ^ 2
  have hSG : 0 ≤ SG := Finset.sum_nonneg fun _ _ => by positivity
  obtain ⟨x, hxd⟩ : ∃ x : ℂ, x = (1 / (q.totient : ℂ)) * ∑ χ ∈ G, u χ := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y : ℂ, y = (1 / (q.totient : ℂ)) * ∑ χ ∈ Bd, u χ := ⟨_, rfl⟩
  obtain ⟨z, hzd⟩ : ∃ z : ℂ,
      z = characterRemainder M q a η - (1 / (q.totient : ℂ)) * ∑ χ, u χ := ⟨_, rfl⟩
  have hR : characterRemainder M q a η = x + y + z := by
    have hs : ∑ χ, u χ = ∑ χ ∈ G, u χ + ∑ χ ∈ Bd, u χ :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    rw [hxd, hyd, hzd, hs]
    ring
  have hinv : ‖(1 / (q.totient : ℂ))‖ = 1 / (q.totient : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  have hx : ‖x‖ ^ 2 ≤ (q : ℝ) / q.totient * SG := by
    calc ‖x‖ ^ 2 = (1 / (q.totient : ℝ)) ^ 2 * ‖∑ χ ∈ G, u χ‖ ^ 2 := by
          rw [hxd, norm_mul, hinv, mul_pow]
      _ ≤ (1 / (q.totient : ℝ)) ^ 2 * ((G.card : ℝ) * q * SG) := by gcongr; exact hcs G
      _ ≤ (1 / (q.totient : ℝ)) ^ 2 * ((q.totient : ℝ) * q * SG) := by gcongr
      _ = _ := by field_simp
  have hy : ‖y‖ ^ 2 ≤ (q : ℝ) / (q.totient : ℝ) ^ 2 * (Bd.card : ℝ) * SB := by
    calc ‖y‖ ^ 2 = (1 / (q.totient : ℝ)) ^ 2 * ‖∑ χ ∈ Bd, u χ‖ ^ 2 := by
          rw [hyd, norm_mul, hinv, mul_pow]
      _ ≤ (1 / (q.totient : ℝ)) ^ 2 * ((Bd.card : ℝ) * q * SB) := by gcongr; exact hcs Bd
      _ = _ := by ring
  have hz : ‖z‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hzd ▸ hE) 2
  have htri : ‖characterRemainder M q a η‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    rw [hR]; exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  have h0 : 0 ≤ ‖characterRemainder M q a η‖ := norm_nonneg _
  have hx0 := norm_nonneg x
  have hy0 := norm_nonneg y
  have hz0 := norm_nonneg z
  have hsq : ‖characterRemainder M q a η‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖y‖ - ‖z‖), sq_nonneg (‖x‖ - ‖z‖)]
  linarith

/-- The character remainder R(η,q,a) of page 484 is continuous in η. -/
theorem continuous_characterRemainder (M q : ℕ) (a : ℤ) :
    Continuous (characterRemainder M q a) := by
  unfold characterRemainder primeSum
  simp only [Kernel.T, Kernel.e]
  fun_prop

set_option maxHeartbeats 1600000 in
/-- Page 485 display 23, the statement of leaf_character_expansion below, proved
from char_expansion_error, bad_count, the Gauss sum bound and Cauchy Schwarz in
pointwise_bound, and the integration over |η| ≤ 1/(qQ). The term L⁴/(qQ) of 23 is
absorbed into N L^(-B). CONDITIONAL ON display 21 through hDensity only. -/
theorem character_expansion_bound (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d) (hDensity : DensityInput C d)
    (c : ℝ) (hc : 0 < c) (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ e C' N₀ : ℝ, 0 ≤ e ∧ 0 < C' ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ fareyOrder F N H B →
      ∀ a : ℤ, Nat.Coprime a.natAbs q →
      ∀ X : ℝ, 0 ≤ X →
      (∀ χ : DirichletCharacter ℂ q, ¬ goodCharacter B ε N χ →
        (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
          (1 / ((q : ℝ) * fareyOrder F N H B)), ‖twistedRemainder ⌊c * N⌋₊ χ η‖ ^ 2) ≤ X) →
      (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
        (1 / ((q : ℝ) * fareyOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q a η‖ ^ 2) ≤
        C' * ((q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ e * X +
          goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) + N * Real.log N ^ (-B)) := by
  obtain ⟨e₀, C₀, N₁, he₀, hC₀, hN₁, hcnt⟩ := bad_count C d hC hd hDensity ε B hε hB
  obtain ⟨NA, hNA, harc⟩ := arc_parameters F hF ε B hε hB
  obtain ⟨N₂, hN₂, hpow⟩ := power_loss_exceeds_log_loss 1 0 (4 + B) 1 (by norm_num) (by norm_num)
  set K0 : ℝ := 4 * (Real.log (c + 1) + 1) ^ 2 with hK0
  have hK0n : 0 ≤ K0 := by positivity
  refine ⟨2 * e₀, 3 * (C₀ ^ 2 + 1) * (K0 + 1), max (max N₁ NA) (max N₂ (Real.exp 1)),
    by positivity, by positivity, hN₁.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu q _ hqQ a hcop X hX hbad
  have hN1' : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNA' : NA ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN2' : N₂ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNE : Real.exp 1 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hNE
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hNE
  have hL0 : 0 < Real.log N := by linarith
  set Q := fareyOrder F N H B with hQdef
  have hQ2 : 2 ≤ Q := (harc N H hNA' hH).2
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  set r : ℝ := 1 / ((q : ℝ) * Q) with hr
  have hr0 : 0 < r := by positivity
  have hr2 : r ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  -- q ≤ N, as in Bad1122.bad_character_removal_of_split
  have hQN : Q ≤ N := by
    have hHk : H ^ F.natDegree ≤ N := by
      have h0 : 0 ≤ H := le_trans (by positivity) hH
      calc H ^ F.natDegree ≤ (N ^ (1 / (F.natDegree : ℝ))) ^ F.natDegree := by gcongr
        _ = N := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
          have : (F.natDegree : ℝ) ≠ 0 := by
            exact_mod_cast (show F.natDegree ≠ 0 by have := hF.1; omega)
          rw [one_div_mul_cancel this, Real.rpow_one]
    rw [hQdef]; unfold fareyOrder
    have hy : H ^ F.natDegree * Real.log N ^ (-B / 4) ≤ N := by
      have : Real.log N ^ (-B / 4) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
      have h0 : 0 ≤ H ^ F.natDegree := pow_nonneg (le_trans (by positivity) hH) _
      nlinarith
    have hs : Real.sqrt (H ^ F.natDegree * Real.log N ^ (-B / 4)) ≤ N := by
      rw [Real.sqrt_le_left]
      · nlinarith [hL1, Real.add_one_le_exp 1, hNE]
      · exact hN0.le
    linarith
  have hqN : (q : ℝ) ≤ N := hqQ.trans hQN
  have hlogq : Real.log q ≤ Real.log N := Real.log_le_log (by linarith) hqN
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  set M := ⌊c * N⌋₊ with hM
  have hM1 : ((M : ℝ) + 1) ≤ (c + 1) * N := by
    have := Nat.floor_le (show 0 ≤ c * N by positivity)
    nlinarith
  have hlogM : Real.log ((M : ℝ) + 1) ≤ (Real.log (c + 1) + 1) * Real.log N := by
    have h1 : Real.log ((M : ℝ) + 1) ≤ Real.log ((c + 1) * N) :=
      Real.log_le_log (by positivity) hM1
    rw [Real.log_mul (by positivity) hN0.ne'] at h1
    have : 0 ≤ Real.log (c + 1) := Real.log_nonneg (by linarith)
    nlinarith
  have hlogM0 : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by have := M.cast_nonneg (α := ℝ); linarith)
  set K := 2 * Real.log q * Real.log ((M : ℝ) + 1) with hKdef
  have hK0' : 0 ≤ K := by positivity
  have hKle : K ≤ 2 * (Real.log (c + 1) + 1) * Real.log N ^ 2 := by
    rw [hKdef]
    calc 2 * Real.log q * Real.log ((M : ℝ) + 1)
        ≤ 2 * Real.log N * ((Real.log (c + 1) + 1) * Real.log N) := by gcongr
      _ = _ := by ring
  have hK2 : K ^ 2 ≤ K0 * Real.log N ^ 4 := by
    calc K ^ 2 ≤ (2 * (Real.log (c + 1) + 1) * Real.log N ^ 2) ^ 2 := by gcongr
      _ = _ := by rw [hK0]; ring
  have hL4 : Real.log N ^ 4 ≤ N * Real.log N ^ (-B) := by
    have h := hpow N hN2'
    simp only [Real.rpow_zero, mul_one, one_mul, Real.rpow_one] at h
    have : Real.log N ^ (4 : ℕ) = Real.log N ^ (4 + B) * Real.log N ^ (-B) := by
      rw [← Real.rpow_add hL0, show (4 : ℝ) + B + -B = ((4 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [this]
    have : 0 < Real.log N ^ (-B) := by positivity
    nlinarith
  -- the pointwise bound with p = good
  set G := univ.filter (fun χ : DirichletCharacter ℂ q => goodCharacter B ε N χ)
  set Bd := univ.filter (fun χ : DirichletCharacter ℂ q => ¬ goodCharacter B ε N χ)
  have hcard : (Bd.card : ℝ) ≤ C₀ * Real.log N ^ e₀ := hcnt N hN1' q hqN
  have hWc : ∀ χ : DirichletCharacter ℂ q, Continuous fun η => ‖twistedRemainder M χ η‖ ^ 2 :=
    fun χ => ((continuous_twistedRemainder M χ).norm).pow 2
  have hWi : ∀ χ : DirichletCharacter ℂ q,
      IntervalIntegrable (fun η => ‖twistedRemainder M χ η‖ ^ 2) volume (-r) r :=
    fun χ => (hWc χ).intervalIntegrable _ _
  set fA : ℝ → ℝ := fun η => (q : ℝ) / q.totient * ∑ χ ∈ G, ‖twistedRemainder M χ η‖ ^ 2
  set fB : ℝ → ℝ := fun η => (q : ℝ) / (q.totient : ℝ) ^ 2 * (Bd.card : ℝ) *
      ∑ χ ∈ Bd, ‖twistedRemainder M χ η‖ ^ 2
  have hfAc : Continuous fA := continuous_const.mul (continuous_finsetSum _ fun χ _ => hWc χ)
  have hfBc : Continuous fB := continuous_const.mul (continuous_finsetSum _ fun χ _ => hWc χ)
  have hpt : ∀ η, ‖characterRemainder M q a η‖ ^ 2 ≤ 3 * (fA η + fB η + K ^ 2) := fun η =>
    pointwise_bound M q a hcop (fun χ => goodCharacter B ε N χ) η
  have hmono : (∫ η in (-r)..r, ‖characterRemainder M q a η‖ ^ 2) ≤
      ∫ η in (-r)..r, 3 * (fA η + fB η + K ^ 2) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (((continuous_characterRemainder M q a).norm).pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul ((hfAc.add hfBc).add continuous_const)).intervalIntegrable _ _
    · intro η _; exact hpt η
  have hIA : (∫ η in (-r)..r, fA η) = goodEnergy B ε N M q Q := by
    simp only [fA]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun χ _ => hWi χ)]
    unfold goodEnergy
    rw [Finset.sum_filter]
  have hIB : (∫ η in (-r)..r, fB η) ≤
      (q : ℝ) / (q.totient : ℝ) ^ 2 * (Bd.card : ℝ) * ((Bd.card : ℝ) * X) := by
    simp only [fB]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun χ _ => hWi χ)]
    gcongr
    calc (∑ χ ∈ Bd, ∫ η in (-r)..r, ‖twistedRemainder M χ η‖ ^ 2) ≤ ∑ χ ∈ Bd, X := by
          apply Finset.sum_le_sum
          intro χ hχ
          exact hbad χ (Finset.mem_filter.mp hχ).2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hI : (∫ η in (-r)..r, 3 * (fA η + fB η + K ^ 2)) =
      3 * ((∫ η in (-r)..r, fA η) + (∫ η in (-r)..r, fB η) + (r - -r) * K ^ 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_const, smul_eq_mul]
    · exact hfAc.intervalIntegrable _ _
    · exact hfBc.intervalIntegrable _ _
    · exact (hfAc.add hfBc).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  -- final arithmetic
  set gE := goodEnergy B ε N M q Q with hgE
  have hg0 : 0 ≤ gE := goodEnergy_nonneg_aux B ε N M q Q (by linarith)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hqpos
  set a1 := (q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ (2 * e₀) * X with ha1
  have ha1n : 0 ≤ a1 := by positivity
  have hnB : 0 ≤ N * Real.log N ^ (-B) := by positivity
  have hcard2 : (Bd.card : ℝ) * (Bd.card : ℝ) ≤ C₀ ^ 2 * Real.log N ^ (2 * e₀) := by
    have h0 : (0 : ℝ) ≤ Bd.card := Nat.cast_nonneg _
    have : Real.log N ^ (2 * e₀) = (Real.log N ^ e₀) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
    rw [this]
    nlinarith
  have hBterm : (q : ℝ) / (q.totient : ℝ) ^ 2 * (Bd.card : ℝ) * ((Bd.card : ℝ) * X) ≤
      C₀ ^ 2 * a1 := by
    have hc : 0 ≤ (q : ℝ) / (q.totient : ℝ) ^ 2 * X := by positivity
    calc (q : ℝ) / (q.totient : ℝ) ^ 2 * (Bd.card : ℝ) * ((Bd.card : ℝ) * X)
        = ((q : ℝ) / (q.totient : ℝ) ^ 2 * X) * ((Bd.card : ℝ) * (Bd.card : ℝ)) := by ring
      _ ≤ ((q : ℝ) / (q.totient : ℝ) ^ 2 * X) * (C₀ ^ 2 * Real.log N ^ (2 * e₀)) := by gcongr
      _ = C₀ ^ 2 * a1 := by rw [ha1]; ring
  have hKterm : (r - -r) * K ^ 2 ≤ K0 * (N * Real.log N ^ (-B)) := by
    have hK2n : 0 ≤ K ^ 2 := by positivity
    calc (r - -r) * K ^ 2 ≤ 1 * K ^ 2 := by gcongr; linarith
      _ ≤ K0 * Real.log N ^ 4 := by linarith
      _ ≤ K0 * (N * Real.log N ^ (-B)) := by gcongr
  calc (∫ η in (-r)..r, ‖characterRemainder M q a η‖ ^ 2)
      ≤ 3 * ((∫ η in (-r)..r, fA η) + (∫ η in (-r)..r, fB η) + (r - -r) * K ^ 2) := hI ▸ hmono
    _ ≤ 3 * (gE + C₀ ^ 2 * a1 + K0 * (N * Real.log N ^ (-B))) := by
        rw [hIA]; gcongr; exact hIB.trans hBterm
    _ ≤ 3 * (C₀ ^ 2 + 1) * (K0 + 1) * (a1 + gE + N * Real.log N ^ (-B)) := by
        have h1 : 0 ≤ C₀ ^ 2 * K0 := by positivity
        nlinarith [mul_nonneg h1 ha1n, mul_nonneg h1 hg0, mul_nonneg h1 hnB,
          mul_nonneg hK0n ha1n, mul_nonneg hK0n hg0, mul_nonneg (sq_nonneg C₀) hg0,
          mul_nonneg (sq_nonneg C₀) hnB, mul_nonneg (sq_nonneg C₀) ha1n, mul_nonneg hK0n hnB]

/-- LEAF: Page 485 display 23, from the character expansion of R(η,q,a) before display 16,
Cauchy-Schwarz with the Gauss sum bound τ(χ) ≪ q^(1/2), and the count 22 of bad characters
obtained from the density estimate 21. The paper prints the bad character factor as
q/φ(q)² L^(50B/ε) max_{χ bad} ∫|W(χ,η)|²; here the fixed power of L is L^e with e
depending only on F, the density constants, c, ε and B, and the maximum is any bound X
for the bad character integrals. The final term L⁴/(qQ) of 23 is already absorbed into
N L^(-B), as the paper does when passing to 24.
Class MEDIUM. CONDITIONAL ON display 21 through hDensity. -/
theorem leaf_character_expansion (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d) (hDensity : DensityInput C d)
    (c : ℝ) (hc : 0 < c) (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ e C' N₀ : ℝ, 0 ≤ e ∧ 0 < C' ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ fareyOrder F N H B →
      ∀ a : ℤ, Nat.Coprime a.natAbs q →
      ∀ X : ℝ, 0 ≤ X →
      (∀ χ : DirichletCharacter ℂ q, ¬ goodCharacter B ε N χ →
        (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
          (1 / ((q : ℝ) * fareyOrder F N H B)), ‖twistedRemainder ⌊c * N⌋₊ χ η‖ ^ 2) ≤ X) →
      (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
        (1 / ((q : ℝ) * fareyOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q a η‖ ^ 2) ≤
        C' * ((q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ e * X +
          goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) + N * Real.log N ^ (-B)) := by
  exact character_expansion_bound F hF C d hC hd hDensity c hc ε B hε hB

/-- The good character energy is nonnegative. -/
theorem goodEnergy_nonneg (B ε N : ℝ) (M q : ℕ) [NeZero q] (Q : ℝ) (hQ : 0 < Q) :
    0 ≤ goodEnergy B ε N M q Q := by
  unfold goodEnergy
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro χ _
  split_ifs
  · apply intervalIntegral.integral_nonneg
    · have : 0 < 1 / ((q : ℝ) * Q) := by positivity
      linarith
    · intro η _; positivity
  · exact le_refl 0

/-- A bad character integral over |η| ≤ 1/(qQ) is at most the full period integral. -/
theorem arc_le_full_period (M q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (r : ℝ)
    (hr : 0 < r) (hr2 : r ≤ 1 / 2) :
    (∫ η in (-r)..r, ‖twistedRemainder M χ η‖ ^ 2) ≤
      ∫ η in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), ‖twistedRemainder M χ η‖ ^ 2 := by
  have hcont : Continuous (fun η => ‖twistedRemainder M χ η‖ ^ 2) :=
    ((continuous_twistedRemainder M χ).norm).pow 2
  apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hr2
  · exact Filter.Eventually.of_forall (fun η => by positivity)
  · exact hcont.intervalIntegrable _ _

/-- Page 485 display 24, the exact statement of Char1122.leaf_bad_character_removal,
proved from the two LEAFs above, the full period bound character_full_period_scaled and
bad_character_totient_factor. The choice P = e + B + 4 plays the role of ε' = ε/(200B).
CONDITIONAL ON display 21 and the LEAFs leaf_bad_modulus_large and
leaf_character_expansion. -/
theorem bad_character_removal_of_split (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d) (hDensity : DensityInput C d)
    (c : ℝ) (hc : 0 < c) (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C' N₀ : ℝ, 0 < C' ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ fareyOrder F N H B →
      ∀ a : ℤ, Nat.Coprime a.natAbs q →
      (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
        (1 / ((q : ℝ) * fareyOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q a η‖ ^ 2) ≤
        C' * (goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) +
          N * Real.log N ^ (-B)) := by
  obtain ⟨e, C1, N1, he, hC1, hN1, h23⟩ :=
    leaf_character_expansion F hF C d hC hd hDensity c hc ε B hε hB
  obtain ⟨CP, NP, hCP, hNP, hfull⟩ := character_full_period_scaled c hc
  obtain ⟨c', N2, hc', hN2, h20⟩ := leaf_bad_modulus_large B ε hB hε (e + B + 4) (by positivity)
  obtain ⟨NA, hNA, harc⟩ := arc_parameters F hF ε B hε hB
  let K := 16 * CP / c' + 1
  refine ⟨C1 * K, max (max N1 NP) (max N2 (max NA (Real.exp 1))), by positivity,
    hN1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu q _ hqQ a hcop
  have hN1' : N1 ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNP' : NP ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN2' : N2 ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNA' : NA ≤ N :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  have hNE : Real.exp 1 ≤ N :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hNE
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hNE
  have hL0 : 0 < Real.log N := by linarith
  set Q := fareyOrder F N H B with hQdef
  have hQ2 : 2 ≤ Q := (harc N H hNA' hH).2
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hr : 0 < 1 / ((q : ℝ) * Q) := by positivity
  have hr2 : 1 / ((q : ℝ) * Q) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  set gE := goodEnergy B ε N ⌊c * N⌋₊ q Q with hgE
  have hg0 : 0 ≤ gE := goodEnergy_nonneg B ε N _ q Q (by linarith)
  have hP0 : 0 ≤ N * Real.log N ^ (-B) := by positivity
  have hK1 : 1 ≤ K := by dsimp [K]; have : 0 ≤ 16 * CP / c' := by positivity
                         linarith
  by_cases hbad : ∃ χ : DirichletCharacter ℂ q, ¬ goodCharacter B ε N χ
  · obtain ⟨χ₀, hχ₀⟩ := hbad
    have hqbig : c' * Real.log N ^ (e + B + 4) ≤ q := h20 N hN2' q χ₀ hχ₀
    let Xb := CP * N * Real.log N
    have hX : 0 ≤ Xb := by positivity
    have hbound : ∀ χ : DirichletCharacter ℂ q, ¬ goodCharacter B ε N χ →
        (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)),
          ‖twistedRemainder ⌊c * N⌋₊ χ η‖ ^ 2) ≤ Xb := by
      intro χ _
      refine (arc_le_full_period _ q χ _ hr hr2).trans ?_
      have hf := hfull N hNP' q χ (if χ = 1 then 1 else 0) (by split_ifs <;> simp)
      have heq : (fun η => ‖twistedRemainder ⌊c * N⌋₊ χ η‖ ^ 2) =
          (fun η => ‖(∑ n ∈ range (⌊c * N⌋₊ + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
            (if χ = 1 then (1 : ℂ) else 0) * Kernel.T 0 (⌊c * N⌋₊ + 1) η‖ ^ 2) := by
        funext η; unfold twistedRemainder; split_ifs <;> simp
      rw [heq]; exact hf
    have hmain := h23 N H hN1' hH hHu q hqQ a hcop Xb hX hbound
    -- the bad character term
    have hlogq : Real.log q ≤ Real.log N := by
      have hHk : H ^ F.natDegree ≤ N := by
        have h0 : 0 ≤ H := le_trans (by positivity) hH
        calc H ^ F.natDegree ≤ (N ^ (1 / (F.natDegree : ℝ))) ^ F.natDegree := by gcongr
          _ = N := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
            have : (F.natDegree : ℝ) ≠ 0 := by
              exact_mod_cast (show F.natDegree ≠ 0 by have := hF.1; omega)
            rw [one_div_mul_cancel this, Real.rpow_one]
      have hQN : Q ≤ N := by
        rw [hQdef]; unfold fareyOrder
        have hy : H ^ F.natDegree * Real.log N ^ (-B / 4) ≤ N := by
          have : Real.log N ^ (-B / 4) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
          have h0 : 0 ≤ H ^ F.natDegree := pow_nonneg (le_trans (by positivity) hH) _
          nlinarith
        have hs : Real.sqrt (H ^ F.natDegree * Real.log N ^ (-B / 4)) ≤ N := by
          rw [Real.sqrt_le_left]
          · nlinarith [hL1, Real.add_one_le_exp 1, hNE]
          · exact hN0.le
        linarith
      exact Real.log_le_log (by linarith) (by linarith)
    have hfac := bad_character_totient_factor q hqpos (Real.log N) hL1 hlogq
    have hpowq : 0 < c' * Real.log N ^ (e + B + 4) := by positivity
    have hbadterm : (q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ e * Xb ≤
        16 * CP / c' * (N * Real.log N ^ (-B)) := by
      have hLe : 0 ≤ Real.log N ^ e := by positivity
      calc (q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ e * Xb
          ≤ 16 * Real.log N ^ 2 / q * Real.log N ^ e * Xb := by gcongr
        _ = 16 * CP * N * (Real.log N ^ (e + 3)) / q := by
            dsimp [Xb]
            rw [Real.rpow_add hL0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            ring
        _ ≤ 16 * CP * N * (Real.log N ^ (e + 3)) / (c' * Real.log N ^ (e + B + 4)) := by
            gcongr
        _ = 16 * CP / c' * (N * Real.log N ^ (-B - 1)) := by
            have h1 : Real.log N ^ (e + B + 4) = Real.log N ^ (e + 3) * Real.log N ^ (B + 1) := by
              rw [← Real.rpow_add hL0]; ring_nf
            have h2 : Real.log N ^ (-B - 1) = (Real.log N ^ (B + 1))⁻¹ := by
              rw [← Real.rpow_neg hL0.le]; ring_nf
            rw [h1, h2]
            have : 0 < Real.log N ^ (e + 3) := by positivity
            have : 0 < Real.log N ^ (B + 1) := by positivity
            field_simp
        _ ≤ 16 * CP / c' * (N * Real.log N ^ (-B)) := by
            gcongr
            linarith
    calc _ ≤ C1 * ((q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ e * Xb + gE +
          N * Real.log N ^ (-B)) := hmain
      _ ≤ C1 * (16 * CP / c' * (N * Real.log N ^ (-B)) + gE + N * Real.log N ^ (-B)) := by
          gcongr
      _ ≤ C1 * K * (gE + N * Real.log N ^ (-B)) := by
          dsimp [K]
          have h16 : 0 ≤ 16 * CP / c' := by positivity
          have := mul_nonneg h16 hg0
          nlinarith
  · push_neg at hbad
    have hbound : ∀ χ : DirichletCharacter ℂ q, ¬ goodCharacter B ε N χ →
        (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)),
          ‖twistedRemainder ⌊c * N⌋₊ χ η‖ ^ 2) ≤ 0 := by
      intro χ hχ; exact absurd (hbad χ) hχ
    have hmain := h23 N H hN1' hH hHu q hqQ a hcop 0 le_rfl hbound
    calc _ ≤ C1 * ((q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ e * 0 + gE +
          N * Real.log N ^ (-B)) := hmain
      _ = C1 * 1 * (gE + N * Real.log N ^ (-B)) := by ring
      _ ≤ C1 * K * (gE + N * Real.log N ^ (-B)) := by gcongr

/-- Pages 484 and 485 displays 16 through 25, the same statement as
Char1122.leaf_character_of_split, with display 24 from bad_character_removal_of_split. The exact statement of
Decomp88.leaf_character, CONDITIONAL ON Decomp582a.leaf_zero_density and on the display 25 input h25,
which is Char1122.leaf_good_character_mean with its B replaced by the B at least B₀ form: main states
that leaf for a fixed B, and the B at least B₀ form of display 25 is Good1122.leaf_good_short_variance.
The assembly itself has no sorry. -/
theorem leaf_character_of_split2 (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c)
    (h25 : ∀ ε B : ℝ, 0 < ε → 0 < B →
      ∃ C' N₀ : ℝ, 0 < C' ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
        N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
        H ≤ N ^ (1 / (F.natDegree : ℝ)) →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ fareyOrder F N H B →
          goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) ≤ C' * N * Real.log N ^ (-B)) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ ε B : ℝ, 0 < ε → B₀ ≤ B →
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ fareyOrder F N H B →
      ∀ a : ℤ, Nat.Coprime a.natAbs q →
      (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
        (1 / ((q : ℝ) * fareyOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q a η‖ ^ 2) ≤ C * N * Real.log N ^ (-B) := by
  obtain ⟨CD, d, hCD, hd, hDensity⟩ := leaf_zero_density
  refine ⟨1, one_pos, ?_⟩
  intro ε B hε hBB
  have hB : 0 < B := one_pos.trans_le hBB
  obtain ⟨C1, N1, hC1, hN1, h24⟩ :=
    bad_character_removal_of_split F hF CD d hCD hd hDensity c hc ε B hε hB
  obtain ⟨C2, N2, hC2, hN2, h25b⟩ := h25 ε B hε hB
  refine ⟨C1 * (C2 + 1), max N1 N2, by positivity, hN1.trans (le_max_left _ _), ?_⟩
  intro N H hN hH hHu q hq hqQ a hcop
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb := h24 N H ((le_max_left _ _).trans hN) hH hHu q hqQ a hcop
  have hg := h25b N H ((le_max_right _ _).trans hN) hH hHu q hqQ
  have hN0 : 0 < N := by linarith [hN1.trans ((le_max_left N1 N2).trans hN)]
  have hP : 0 ≤ N * Real.log N ^ (-B) := by
    have : 0 < Real.log N := Real.log_pos (by linarith [hN1.trans ((le_max_left N1 N2).trans hN)])
    positivity
  calc _ ≤ C1 * (goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) +
          N * Real.log N ^ (-B)) := hb
    _ ≤ C1 * (C2 * N * Real.log N ^ (-B) + N * Real.log N ^ (-B)) := by gcongr
    _ = C1 * (C2 + 1) * N * Real.log N ^ (-B) := by ring

end
end LeanLab.Perelli1996.Bad1122
