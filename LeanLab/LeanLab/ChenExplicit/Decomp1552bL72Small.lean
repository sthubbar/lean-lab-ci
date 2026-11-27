/-
AI wrote the Lean code. Claude, session S149, burst-20261122, unit s1552b.
Yamada arXiv 1511.03409v2, Section 7, Lemma 7.2 proof, eqs 100 to 102 and the small
conductor sum before eq 103, printed pages 23 and 24.
Split of the LEAF `Split1552bL72.small_sector_of_prime_sum`.
* `char_bound`, PROVED: one character of small conductor, via its primitive character,
  losing the primes dividing the modulus, eqs 100 and 101.
* `sector_regroup`, PROVED from the LEAF `recip_totient_sum_le`: grouping the moduli by
  conductor and the reciprocal totient sum over multiples of a conductor.
* `sector_arith`, PROVED: the final numerical comparison.
* `recip_totient_sum_le`, LEAF: `Σ_{m < D} 1/φ(m) ≤ 3(log D + 1)`.
`small_sector_of_leaves` has exactly the statement of `small_sector_of_prime_sum`.
It is CONDITIONAL ON the one LEAF `recip_totient_sum_le`. Chen's theorem is known; binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.Decomp324a
import LeanLab.ChenExplicit.Decomp1552b

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.ChenExplicit.Small1552b
open D1552 Decomp324

/-- Yamada page 23 eqs 100 and 101: a nonprincipal character of modulus `d` whose conductor
is small has its product sum bounded by `X` times the primitive prime sum bound `B` plus the
number of primes dividing `d`. -/
theorem char_bound (q₁ : ℕ) (L B : ℝ) (c : ℕ → ℝ) (X Y Z : ℝ)
    (hP : ∀ (r : ℕ) [NeZero r] (ψ : DirichletCharacter ℂ r), ψ.IsPrimitive → ψ ≠ 1 →
      (r : ℝ) < L → ¬ q₁ ∣ r → ‖∑ p ∈ primesIco Z Y, ψ (p : ZMod r)‖ ≤ B)
    (hc : ∀ n, |c n| ≤ 1) (hX : 0 ≤ X)
    (d : ℕ) [NeZero d] (hq : ¬ q₁ ∣ d) (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (hL : (χ.conductor : ℝ) < L) :
    ‖productCharSum χ c X Y Z‖ ≤ X * (B + d.primeFactors.card) := by
  rw [productCharSum_factor, norm_mul]
  have h1 : ‖∑ n ∈ Ico 1 ⌈X⌉₊, (c n : ℂ) * χ (n : ZMod d)‖ ≤ X := by
    calc
      _ ≤ ∑ n ∈ Ico 1 ⌈X⌉₊, (1 : ℝ) := by
        apply norm_sum_le_of_le
        intro n hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_one₀ (hc n) (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
      _ = ((⌈X⌉₊ - 1 : ℕ) : ℝ) := by simp
      _ ≤ X := by
        have hlt := Nat.ceil_lt_add_one hX
        rcases Nat.eq_zero_or_pos ⌈X⌉₊ with h0 | hpos
        · rw [h0]; simpa using hX
        · rw [Nat.cast_sub hpos]; push_cast; linarith
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ1 : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h, map_one]
  have hqr : ¬ q₁ ∣ χ.conductor := fun h => hq (h.trans χ.conductor_dvd_level)
  have hB := hP χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hψ1 hL hqr
  have hsum : ∑ p ∈ primesIco Z Y, χ (p : ZMod d) =
      ∑ p ∈ (primesIco Z Y).filter (fun p => ¬ p ∣ d),
        χ.primitiveCharacter (p : ZMod χ.conductor) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    have hpp : p.Prime := (mem_filter.mp hp).2.1
    by_cases hpd : p ∣ d
    · rw [if_neg (not_not.mpr hpd)]
      apply MulChar.map_nonunit
      intro hu
      have hcop := (ZMod.isUnit_iff_coprime p d).mp hu
      exact (Nat.Prime.coprime_iff_not_dvd hpp).mp hcop hpd
    · rw [if_pos hpd]
      have hcop : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpd
      have he := χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hcop)
      push_cast at he
      exact he.symm
  have hrem := prime_sum_remove_divisors χ.primitiveCharacter d (NeZero.ne d) (primesIco Z Y)
    (fun p hp => (mem_filter.mp hp).2.1)
  have h2 : ‖∑ p ∈ primesIco Z Y, χ (p : ZMod d)‖ ≤ B + d.primeFactors.card := by
    rw [hsum]
    calc
      _ ≤ ‖(∑ p ∈ (primesIco Z Y).filter (fun p => ¬ p ∣ d),
            χ.primitiveCharacter (p : ZMod χ.conductor)) -
          ∑ p ∈ primesIco Z Y, χ.primitiveCharacter (p : ZMod χ.conductor)‖ +
          ‖∑ p ∈ primesIco Z Y, χ.primitiveCharacter (p : ZMod χ.conductor)‖ := by
        refine le_of_eq_of_le ?_ (norm_add_le _ _)
        rw [sub_add_cancel]
      _ ≤ _ := by linarith
  exact mul_le_mul h1 h2 (norm_nonneg _) hX

/-- Yamada page 23, the bound `ω(d) ≤ log d / log 2` used after eq 101. -/
theorem omega_le_log (d : ℕ) (hd : d ≠ 0) :
    (d.primeFactors.card : ℝ) ≤ log d / log 2 := by
  have h2 : (2 : ℕ) ^ d.primeFactors.card ≤ d := by
    calc (2 : ℕ) ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ d.primeFactors, p :=
          prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) (Nat.prod_primeFactors_dvd d)
  have hr : ((2 : ℝ) ^ d.primeFactors.card) ≤ d := by exact_mod_cast h2
  rw [le_div_iff₀ (log_pos (by norm_num))]
  have := log_le_log (by positivity) hr
  rwa [log_pow] at this

/-- LEAF: Yamada 2015, Lemma 7.2 proof, the reciprocal totient sum before eq 103, page 24:
`Σ_{m < D} 1/φ(m) ≤ 3(log D + 1)` for `D ≥ 1`. Route: `m/φ(m) = Σ_{k ∣ m} μ²(k)/φ(k)`, swap,
harmonic bound, and `Σ_k μ²(k)/(k φ(k)) = ∏_p (1 + 1/(p(p-1))) < 1.95`. Numerically the margin
is at least 2 for all integer cutoffs below 2·10⁶. Class MEDIUM. -/
theorem recip_totient_sum_le (D : ℝ) (hD : 1 ≤ D) :
    ∑ m ∈ Ico 1 ⌈D⌉₊, (1 / (m.totient : ℝ)) ≤ 3 * (log D + 1) := by
  by_cases hD1 : D = 1
  · subst D
    simp
  have hDpos : 1 < D := lt_of_le_of_ne hD (Ne.symm hD1)
  have hceil1 : 1 ≤ ⌈D⌉₊ := by
    have hceilpos : 0 < ⌈D⌉₊ := Nat.ceil_pos.mpr (by linarith)
    omega
  have hIco : Ico 1 ⌈D⌉₊ = Icc 1 (⌈D⌉₊ - 1) := by
    ext m
    simp only [mem_Ico, mem_Icc]
    omega
  rw [hIco]
  have hbound := D1552.sum_inv_totient_le_two_log (⌈D⌉₊ - 1) (by omega)
  have hlt : ((⌈D⌉₊ - 1 : ℕ) : ℝ) < D := by
    have hceil := Nat.ceil_lt_add_one (by exact_mod_cast hD)
    push_cast at hceil
    omega
  have hlog : log ((⌈D⌉₊ - 1 : ℕ) : ℝ) ≤ log D := log_le_log (by positivity) hlt.le
  have hnonneg : 0 ≤ 1 + log D := by
    have hlogD := log_nonneg hD
    linarith
  calc
    _ ≤ 2 * (1 + log ((⌈D⌉₊ - 1 : ℕ) : ℝ)) := hbound
    _ ≤ 2 * (1 + log D) := by
      gcongr
      exact hlog
    _ ≤ 3 * (log D + 1) := by
      have hlogD := log_nonneg hD
      nlinarith

/-- Yamada page 24, before eq 103: `Σ_{d < D, r ∣ d} 1/φ(d) ≤ 3(log D + 1)/φ(r)`, from
`φ(r)φ(m) ≤ φ(rm)` and `recip_totient_sum_le`. -/
theorem recip_totient_multiples (D : ℝ) (hD : 1 ≤ D) (r : ℕ) (hr : r ≠ 0) :
    ∑ d ∈ (range ⌈D⌉₊).filter (fun d => 0 < d ∧ r ∣ d), (1 / (d.totient : ℝ)) ≤
      3 * (log D + 1) / r.totient := by
  have hφr : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr)
  set F := (range ⌈D⌉₊).filter (fun d => 0 < d ∧ r ∣ d) with hF
  calc _ ≤ ∑ d ∈ F, (1 / (r.totient : ℝ)) * (1 / ((d / r).totient : ℝ)) := by
        apply sum_le_sum
        intro d hd
        obtain ⟨-, hd0, hrd⟩ := (by simpa [hF] using hd : d < ⌈D⌉₊ ∧ 0 < d ∧ r ∣ d)
        obtain ⟨m, rfl⟩ := hrd
        have hm0 : 0 < m := Nat.pos_of_mul_pos_left hd0
        rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hr)]
        have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
        have hsup : (r.totient : ℝ) * m.totient ≤ (r * m).totient := by
          exact_mod_cast Nat.totient_super_multiplicative r m
        rw [div_mul_div_comm, one_mul]
        exact one_div_le_one_div_of_le (by positivity) hsup
    _ = (1 / (r.totient : ℝ)) * ∑ m ∈ F.image (fun d => d / r), (1 / (m.totient : ℝ)) := by
        rw [mul_sum, sum_image]
        intro a ha b hb hab
        obtain ⟨-, -, hra⟩ := (by simpa [hF] using ha : a < ⌈D⌉₊ ∧ 0 < a ∧ r ∣ a)
        obtain ⟨-, -, hrb⟩ := (by simpa [hF] using hb : b < ⌈D⌉₊ ∧ 0 < b ∧ r ∣ b)
        exact (Nat.div_left_inj hra hrb).mp hab
    _ ≤ (1 / (r.totient : ℝ)) * ∑ m ∈ Ico 1 ⌈D⌉₊, (1 / (m.totient : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg
        · intro m hm
          obtain ⟨d, hd, rfl⟩ := mem_image.mp hm
          obtain ⟨hdD, hd0, hrd⟩ := (by simpa [hF] using hd : d < ⌈D⌉₊ ∧ 0 < d ∧ r ∣ d)
          obtain ⟨m, rfl⟩ := hrd
          have hm0 : 0 < m := Nat.pos_of_mul_pos_left hd0
          rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hr), mem_Ico]
          refine ⟨hm0, lt_of_le_of_lt ?_ hdD⟩
          exact Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hr)
        · intro m _ _; positivity
    _ ≤ (1 / (r.totient : ℝ)) * (3 * (log D + 1)) :=
        mul_le_mul_of_nonneg_left (recip_totient_sum_le D hD) (by positivity)
    _ = _ := by ring

/-- Yamada page 23 eq 100: the nonprincipal characters mod `d` of conductor below `L` number at
most the sum of `φ(r)` over divisors `r ≠ 1` of `d` below `L`. -/
theorem small_char_count (d : ℕ) [NeZero d] (L : ℝ) :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).erase 1,
      if (χ.conductor : ℝ) < L then (1 : ℝ) else 0) ≤
    ∑ r ∈ ((d.divisors).filter (fun r : ℕ => r ≠ 1)).filter (fun r : ℕ => (r : ℝ) < L),
      (r.totient : ℝ) := by
  rw [nonprincipal_sum_by_conductor d (fun χ => if (χ.conductor : ℝ) < L then (1 : ℝ) else 0)]
  conv_rhs => rw [sum_filter]
  apply sum_le_sum
  intro r hr
  have hrd := (Nat.mem_divisors.mp (mem_filter.mp hr).1).1
  have hr0 : r ≠ 0 := fun h => NeZero.ne d (Nat.eq_zero_of_zero_dvd (h ▸ hrd))
  haveI : NeZero r := ⟨hr0⟩
  rw [dite_eq_left hrd]
  have hcond : ∀ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive),
      (if ((DirichletCharacter.changeLevel hrd ψ).conductor : ℝ) < L then (1 : ℝ) else 0) =
        if (r : ℝ) < L then 1 else 0 := by
    intro ψ hψ
    rw [DirichletCharacter.conductor_changeLevel,
      (DirichletCharacter.isPrimitive_def ψ).mp (mem_filter.mp hψ).2]
  rw [sum_congr rfl hcond, sum_const, nsmul_eq_mul]
  have hcard : (((univ : Finset (DirichletCharacter ℂ r)).filter
      (fun ψ => ψ.IsPrimitive)).card : ℝ) ≤ r.totient := by
    have : ((univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive)).card ≤
        r.totient := by
      calc _ ≤ Fintype.card (DirichletCharacter ℂ r) := card_le_univ _
        _ = _ := by
          rw [← Nat.card_eq_fintype_card]
          exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r
    exact_mod_cast this
  split_ifs <;> simp [hcard]

/-- Yamada 2015, Lemma 7.2 proof, eq 100 and the sum over small conductors before eq 103,
pages 23 and 24. Group the nonprincipal characters mod `d` by their conductor `r` with
`2 ≤ r < log¹⁰ Y`, at most `φ(r)` primitive characters mod `r`, use
`Σ_{d < D, r ∣ d} 1/φ(d) ≤ 3(log D + 1)/φ(r)` and `ω(d) ≤ log d / log 2 ≤ log D / log 2`,
where `D = √(XY)/log¹⁰ Y`. PROVED from the LEAF `recip_totient_sum_le`. -/
theorem sector_regroup (q₁ : ℕ) (c : ℕ → ℝ) (X Y Z B : ℝ) (hX : 0 ≤ X) (hB : 0 ≤ B)
    (hD : 1 ≤ √(X * Y) / log Y ^ 10)
    (hχ : ∀ (d : ℕ) [NeZero d], ¬ q₁ ∣ d → ∀ χ : DirichletCharacter ℂ d, χ ≠ 1 →
      (χ.conductor : ℝ) < log Y ^ 10 → ‖productCharSum χ c X Y Z‖ ≤ X * (B + d.primeFactors.card)) :
    sectorMass true q₁ c X Y Z ≤
      3 * X * (B + log (√(X * Y) / log Y ^ 10) / log 2) * log Y ^ 10 *
        (log (√(X * Y) / log Y ^ 10) + 1) := by
  unfold sectorMass
  set L := log Y ^ 10 with hLdef
  set D := √(X * Y) / L with hDdef
  have hL0 : 0 ≤ L := by positivity
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlD : 0 ≤ log D := log_nonneg hD
  have hW : 0 ≤ log D / log 2 := div_nonneg hlD hlog2.le
  set K := X * (B + log D / log 2) with hK
  have hK0 : 0 ≤ K := mul_nonneg hX (by linarith)
  set R := (range ⌈D⌉₊).filter (fun r : ℕ => r ≠ 0 ∧ r ≠ 1 ∧ (r : ℝ) < L) with hR
  have step1 := fun (d : ℕ) (hdS : d ∈ (range ⌈D⌉₊).filter (fun d => 0 < d ∧ ¬ q₁ ∣ d)) =>
    show (if hd : d = 0 then 0 else
      letI : NeZero d := ⟨hd⟩
      (1 / (d.totient : ℝ)) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).erase 1,
          if (decide ((χ.conductor : ℝ) < L) == true) then
            ‖productCharSum χ c X Y Z‖ else 0) ≤
        ∑ r ∈ R, if r ∣ d then K * ((r.totient : ℝ) / d.totient) else 0 by
    obtain ⟨hdr, hd0, hq⟩ := (by simpa using hdS : d < ⌈D⌉₊ ∧ 0 < d ∧ ¬ q₁ ∣ d)
    have hd0' : d ≠ 0 := hd0.ne'
    rw [dif_neg hd0']
    haveI : NeZero d := ⟨hd0'⟩
    have hdD : (d : ℝ) < D := Nat.lt_ceil.mp hdr
    have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd0
    have homega : (d.primeFactors.card : ℝ) ≤ log D / log 2 :=
      (omega_le_log d hd0').trans (div_le_div_of_nonneg_right
        (log_le_log (by exact_mod_cast hd0) hdD.le) hlog2.le)
    calc _ ≤ (1 / (d.totient : ℝ)) * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).erase 1,
            K * (if (χ.conductor : ℝ) < L then (1 : ℝ) else 0) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_le_sum
          intro χ hχm
          by_cases h : (χ.conductor : ℝ) < L
          · simp only [h, decide_true, beq_self_eq_true, if_true, mul_one]
            exact (hχ d hq χ (mem_erase.mp hχm).1 h).trans
              (mul_le_mul_of_nonneg_left (by linarith) hX)
          · simp [h]
      _ = (1 / (d.totient : ℝ)) * (K * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).erase 1,
            (if (χ.conductor : ℝ) < L then (1 : ℝ) else 0)) := by rw [← mul_sum]
      _ ≤ (1 / (d.totient : ℝ)) * (K * ∑ r ∈ ((d.divisors).filter (fun r : ℕ => r ≠ 1)).filter
            (fun r : ℕ => (r : ℝ) < L), (r.totient : ℝ)) := by
          gcongr
          exact small_char_count d L
      _ = ∑ r ∈ ((d.divisors).filter (fun r : ℕ => r ≠ 1)).filter (fun r : ℕ => (r : ℝ) < L),
            K * ((r.totient : ℝ) / d.totient) := by
          rw [mul_sum, mul_sum]
          apply sum_congr rfl
          intro r hr
          ring
      _ ≤ ∑ r ∈ R.filter (fun r => r ∣ d), K * ((r.totient : ℝ) / d.totient) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro r hr
            simp only [mem_filter, Nat.mem_divisors] at hr
            obtain ⟨⟨⟨hrd, -⟩, hr1⟩, hrL⟩ := hr
            have hr0 : r ≠ 0 := fun h => hd0' (Nat.eq_zero_of_zero_dvd (h ▸ hrd))
            have hrle : r ≤ d := Nat.le_of_dvd hd0 hrd
            simp only [hR, mem_filter, mem_range]
            exact ⟨⟨by omega, hr0, hr1, hrL⟩, hrd⟩
          · intro r _ _
            positivity
      _ = _ := by rw [sum_filter]
  refine (sum_le_sum step1).trans ?_
  rw [sum_comm]
  have step2 : ∀ r ∈ R, (∑ d ∈ (range ⌈D⌉₊).filter (fun d => 0 < d ∧ ¬ q₁ ∣ d),
      if r ∣ d then K * ((r.totient : ℝ) / d.totient) else 0) ≤ K * (3 * (log D + 1)) := by
    intro r hr
    have hr0 : r ≠ 0 := (mem_filter.mp hr).2.1
    have hφr : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr0)
    rw [← sum_filter]
    calc _ = K * (r.totient : ℝ) * ∑ d ∈ ((range ⌈D⌉₊).filter (fun d => 0 < d ∧ ¬ q₁ ∣ d)).filter
            (fun d => r ∣ d), (1 / (d.totient : ℝ)) := by
          rw [mul_sum]; apply sum_congr rfl; intro d _; ring
      _ ≤ K * (r.totient : ℝ) * ∑ d ∈ (range ⌈D⌉₊).filter (fun d => 0 < d ∧ r ∣ d),
            (1 / (d.totient : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_le_sum_of_subset_of_nonneg
          · intro d hd
            simp only [mem_filter] at hd ⊢
            exact ⟨hd.1.1, hd.1.2.1, hd.2⟩
          · intro d _ _; positivity
      _ ≤ K * (r.totient : ℝ) * (3 * (log D + 1) / r.totient) :=
          mul_le_mul_of_nonneg_left (recip_totient_multiples D hD r hr0) (by positivity)
      _ = _ := by field_simp
  refine (sum_le_sum step2).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hcard : (R.card : ℝ) ≤ L := by
    have hsub : R ⊆ Ico 2 ⌈L⌉₊ := by
      intro r hr
      simp only [hR, mem_filter, mem_range] at hr
      obtain ⟨-, hr0, hr1, hrL⟩ := hr
      simp only [mem_Ico]
      exact ⟨by omega, Nat.lt_ceil.mpr hrL⟩
    have h1 : R.card ≤ ⌈L⌉₊ - 2 := (card_le_card hsub).trans (by simp)
    have h2 := Nat.ceil_lt_add_one hL0
    rcases Nat.lt_or_ge ⌈L⌉₊ 2 with h | h
    · have : ⌈L⌉₊ - 2 = 0 := by omega
      rw [this] at h1
      have : R.card = 0 := by omega
      rw [this]; simpa using hL0
    · have h3 : ((⌈L⌉₊ - 2 : ℕ) : ℝ) = (⌈L⌉₊ : ℝ) - 2 := by
        rw [Nat.cast_sub h]; norm_num
      have h4 : (R.card : ℝ) ≤ ((⌈L⌉₊ - 2 : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
  have hfac : 0 ≤ K * (3 * (log D + 1)) := by positivity
  calc (R.card : ℝ) * (K * (3 * (log D + 1))) ≤ L * (K * (3 * (log D + 1))) :=
        mul_le_mul_of_nonneg_right hcard hfac
    _ = _ := by rw [hK]; ring

/-- Yamada 2015, Lemma 7.2 proof, the numerical step after eq 102, page 24, with
`log D ≤ 5 log Y` from `XY < 2N` and `Y > N^{1/8}`, and `log Y > e^36 / 8`.
The left side is about `18 e^{-147} XY/log⁵ Y + 180 X log¹² Y`. PROVED. -/
theorem sector_arith (N : ℕ) (hN : exp (exp 36) < N) (X Y : ℝ)
    (hX : log Y ^ 10 < X) (hXY : X * Y < 2 * N) (hY : z8 N < Y) :
    1 ≤ √(X * Y) / log Y ^ 10 ∧ Y ≤ 2 * N ∧
      3 * X * (exp (-147) * Y / log Y ^ 16 + log (√(X * Y) / log Y ^ 10) / log 2) *
        log Y ^ 10 * (log (√(X * Y) / log Y ^ 10) + 1) ≤ exp (-146) * X * Y / log Y ^ 4 := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hlogN : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have hYpos : 0 < Y := (rpow_pos_of_pos hNp _).trans hY
  have ht8 : log N / 8 < log Y := by
    have h := log_lt_log (rpow_pos_of_pos hNp _) hY
    rw [log_rpow hNp] at h
    linarith
  have h18 : (181 : ℝ) ≤ exp 18 := by
    have h := quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 18)
    norm_num at h; linarith
  have h36 : (32761 : ℝ) ≤ exp 36 := by
    have he : exp (36 : ℝ) = exp 18 * exp 18 := by rw [← exp_add]; norm_num
    rw [he]; nlinarith
  set t := log Y with ht_def
  have ht : 4000 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have hYe : Y = exp t := (exp_log hYpos).symm
  clear_value t
  have hsmall : t ≤ exp (t / 32) := by
    have h := quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ t / 32)
    nlinarith
  have ht10 : t ^ 10 ≤ Y := by
    calc t ^ 10 ≤ exp (t / 32) ^ 10 := pow_le_pow_left₀ htpos.le hsmall 10
      _ = exp (10 * (t / 32)) := by rw [← exp_nat_mul]; norm_num
      _ ≤ exp t := exp_le_exp.mpr (by linarith)
      _ = Y := hYe.symm
  have ht10pos : 0 < t ^ 10 := by positivity
  have ht1 : 1 ≤ t ^ 10 := one_le_pow₀ (by linarith)
  have hX1 : 1 ≤ X := by linarith
  have hY2 : Y ≤ 2 * N := by nlinarith
  have hXY1 : t ^ 10 * t ^ 10 ≤ X * Y := by
    have := mul_le_mul hX.le ht10 ht10pos.le (by linarith)
    linarith
  have hXYpos : 0 < X * Y := by positivity
  have hsq : t ^ 10 ≤ √(X * Y) := by
    rw [le_sqrt ht10pos.le hXYpos.le]; nlinarith
  have hD : 1 ≤ √(X * Y) / t ^ 10 := (one_le_div ht10pos).mpr hsq
  refine ⟨hD, hY2, ?_⟩
  set ℓ := log (√(X * Y) / t ^ 10) with hℓ
  have hℓ0 : 0 ≤ ℓ := log_nonneg hD
  have hℓ5 : ℓ ≤ 5 * t := by
    have h1 : √(X * Y) / t ^ 10 ≤ √(X * Y) := div_le_self (sqrt_nonneg _) ht1
    have h2 : ℓ ≤ log (X * Y) / 2 := by
      rw [← log_sqrt hXYpos.le]
      exact log_le_log (by linarith) h1
    have h3 : log (X * Y) ≤ log 2 + log N := by
      rw [← log_mul (by norm_num) hNp.ne']
      exact log_le_log hXYpos hXY.le
    have h4 : log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hlog2 : 1 / 2 < log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2 : ℓ / log 2 ≤ 10 * t := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  set B := exp (-147) * Y / t ^ 16 with hB
  have hBn : 0 ≤ B := by positivity
  have hstep : 3 * X * (B + ℓ / log 2) * t ^ 10 * (ℓ + 1) ≤
      3 * X * (B + 10 * t) * t ^ 10 * (6 * t) := by
    have hA : 0 ≤ 3 * X * (B + ℓ / log 2) * t ^ 10 := by
      have : 0 ≤ ℓ / log 2 := div_nonneg hℓ0 (by linarith)
      positivity
    calc _ ≤ 3 * X * (B + ℓ / log 2) * t ^ 10 * (6 * t) :=
          mul_le_mul_of_nonneg_left (by linarith) hA
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ ht10pos.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
  refine hstep.trans ?_
  -- two pieces
  have he1 : exp (-146 : ℝ) = exp (-147) * exp 1 := by rw [← exp_add]; norm_num
  have he : (2.7 : ℝ) ≤ exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hE : 0 < exp (-147 : ℝ) := exp_pos _
  have ht4 : 0 < t ^ 4 := by positivity
  set E := exp (-147 : ℝ) with hEdef
  have hBt15 : B * t ^ 15 = E * Y / t := by
    rw [hB]; field_simp
  have hEY : 0 ≤ E * Y := by positivity
  have hq1 : 18 * (E * Y / t) ≤ (exp 1 / 2) * (E * Y) := by
    have h18t : 18 / t ≤ exp 1 / 2 := by
      rw [div_le_iff₀ htpos]; nlinarith
    calc 18 * (E * Y / t) = (18 / t) * (E * Y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h18t hEY
  have hq2 : 180 * t ^ 16 ≤ (exp 1 / 2) * (E * Y) := by
    have h6 : (25 : ℝ) ≤ exp 6 := by
      have h := quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)
      norm_num at h; linarith
    have h12 : (360 : ℝ) ≤ exp 12 := by
      have he : exp (12 : ℝ) = exp 6 * exp 6 := by rw [← exp_add]; norm_num
      rw [he]; nlinarith
    have ht16 : t ^ 16 ≤ exp (t / 2) := by
      calc t ^ 16 ≤ exp (t / 32) ^ 16 := pow_le_pow_left₀ htpos.le hsmall 16
        _ = exp (16 * (t / 32)) := by rw [← exp_nat_mul]; norm_num
        _ = exp (t / 2) := by ring_nf
    have hkey : exp 12 * exp (t / 2) ≤ exp 1 * (E * Y) := by
      have h1 : exp 12 * exp (t / 2) = exp (12 + t / 2) := (exp_add _ _).symm
      have h2 : exp 1 * (E * Y) = exp (1 + (-147 + t)) := by
        rw [hEdef, hYe, exp_add, exp_add]
      rw [h1, h2]
      exact exp_le_exp.mpr (by linarith)
    have h0 : 0 ≤ exp (t / 2) := (exp_pos _).le
    have hm : 360 * t ^ 16 ≤ exp 1 * (E * Y) :=
      (mul_le_mul h12 ht16 (by positivity) (by linarith)).trans hkey
    calc 180 * t ^ 16 = (360 * t ^ 16) / 2 := by ring
      _ ≤ (exp 1 * (E * Y)) / 2 := by linarith
      _ = _ := by ring
  rw [he1, le_div_iff₀ ht4]
  calc 3 * X * (B + 10 * t) * t ^ 10 * (6 * t) * t ^ 4 =
        X * (18 * (B * t ^ 15) + 180 * t ^ 16) := by ring
    _ ≤ X * (exp 1 * (E * Y)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [hBt15]; linarith
    _ = _ := by ring

/-- Exact statement of `Split1552bL72.small_sector_of_prime_sum`.
CONDITIONAL ON the LEAF `recip_totient_sum_le`. -/
theorem small_sector_of_leaves (N : ℕ) (hN : exp (exp 36) < N) (q₁ : ℕ)
    (hP : ∀ (Y Z : ℝ), z8 N < Y → Y ≤ 2 * N → z8 N ≤ Z →
        ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → χ ≠ 1 →
          (r : ℝ) < log Y ^ 10 → ¬ q₁ ∣ r →
          ‖∑ p ∈ primesIco Z Y, χ (p : ZMod r)‖ ≤ exp (-147) * Y / log Y ^ 16)
    (c : ℕ → ℝ) (X Y Z : ℝ) (hc : ∀ n, |c n| ≤ 1)
    (hX : log Y ^ 10 < X) (hXupper : X ≤ N / z8 N) (hXY : X * Y < 2 * N)
    (hY : z8 N < Y) (hZ : z8 N ≤ Z) :
    sectorMass true q₁ c X Y Z ≤ exp (-146) * X * Y / log Y ^ 4 := by
  obtain ⟨hD, hY2, harith⟩ := sector_arith N hN X Y hX hXY hY
  have hXp : 0 ≤ X := (by positivity : 0 ≤ log Y ^ 10).trans hX.le
  have hYp : 0 ≤ Y := (rpow_nonneg (Nat.cast_nonneg N) _).trans hY.le
  have hB : 0 ≤ exp (-147) * Y / log Y ^ 16 := by positivity
  refine le_trans (sector_regroup q₁ c X Y Z _ hXp hB hD ?_) harith
  intro d _ hq χ hχ hL
  exact char_bound q₁ (log Y ^ 10) _ c X Y Z (hP Y Z hY hY2 hZ) hc hXp d hq χ hχ hL

end LeanLab.ChenExplicit.Small1552b
