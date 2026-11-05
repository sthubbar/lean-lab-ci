/-
Conjugated incomplete periods and the off diagonal term, page 15.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp292a

namespace LeanLab.KumchevLiu2007.Task292b

open Real Complex Task129b Task292a
open scoped BigOperators

/-- Conjugation acts on `ee t = exp(2 π i t)` by `t ↦ -t`. -/
private lemma conj_ee (t : ℝ) : (starRingEnd ℂ) (U1534.ee t) = U1534.ee (-t) := by
  simp only [U1534.ee]
  rw [← Complex.exp_conj]
  have harg : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * ((-t : ℝ) : ℂ) := by
    rw [map_mul, map_mul, map_mul]
    simp only [map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [harg]

/-- `ee` is unchanged by adding an integer to its argument. -/
private lemma ee_add_int (t : ℝ) (k : ℤ) : U1534.ee (t + (k : ℝ)) = U1534.ee t := by
  simp only [U1534.ee]
  have harg : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (((t + (k : ℝ)) : ℝ) : ℂ) =
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (t : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Conjugating a Gauss sum complements the additive character's frequency. -/
private lemma conj_gaussS {q a : ℕ} (ha : a ≤ q) :
    (starRingEnd ℂ) (U1534.gaussS q a) = U1534.gaussS q (q - a) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp [U1534.gaussS]
  · simp only [U1534.gaussS]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [conj_ee]
    have h1 : ((a * x ^ 2 : ℕ) : ℝ) = (a : ℝ) * (x : ℝ) ^ 2 := by
      push_cast
      ring
    have h2 : (((q - a) * x ^ 2 : ℕ) : ℝ) = (q : ℝ) * (x : ℝ) ^ 2 - (a : ℝ) * (x : ℝ) ^ 2 := by
      rw [Nat.sub_mul, Nat.cast_sub (Nat.mul_le_mul_right _ ha), Nat.cast_mul, Nat.cast_mul]
      push_cast
      ring
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hkey : -(↑(a * x ^ 2) / (q : ℝ)) =
        ↑((q - a) * x ^ 2) / (q : ℝ) + ((-(x ^ 2 : ℤ) : ℤ) : ℝ) := by
      rw [h1, h2]
      push_cast
      field_simp
      ring
    rw [hkey, ee_add_int]

/-- The residue set `{a < q : (a,q) = 1}` is stable under `a ↦ q - a`. -/
private lemma coprime_residues_image {q : ℕ} (hq : 2 ≤ q) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).image (fun a => q - a) =
      (Finset.range q).filter (fun a => Nat.Coprime a q) := by
  have hmem : ∀ a, a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ↔
      a < q ∧ Nat.Coprime a q := by
    intro a
    simp
  have hpos : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), 0 < a := by
    intro a ha
    have ha' := (hmem a).mp ha
    rcases Nat.eq_zero_or_pos a with h0 | h
    · exfalso
      subst h0
      have : q = 1 := by simpa using ha'.2
      omega
    · exact h
  apply Finset.Subset.antisymm
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    refine (hmem _).mpr ⟨Nat.sub_lt (by omega) (hpos a ha), ?_⟩
    exact (Nat.coprime_self_sub_left (le_of_lt ((hmem a).mp ha).1)).mpr ((hmem a).mp ha).2
  · intro b hb
    refine Finset.mem_image.mpr ⟨q - b, ?_, ?_⟩
    · refine (hmem _).mpr ⟨Nat.sub_lt (by omega) (hpos b hb), ?_⟩
      exact (Nat.coprime_self_sub_left (le_of_lt ((hmem b).mp hb).1)).mpr ((hmem b).mp hb).2
    · exact Nat.sub_sub_self (le_of_lt ((hmem b).mp hb).1)

/-- LEAF. Page 13 display 45 and property v, used on page 15 after
 display 51. Pairing a with minus a makes A2 real. This algebraic leaf
contains no estimate and applies to every natural modulus. -/
theorem A2_conj (n q : ℕ) :
    (starRingEnd ℂ) (U1534.A2 n q) = U1534.A2 n q := by
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q <;> simp [U1534.A2, U1534.gaussS, U1534.ee]
  · set A : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q) with hA
    have hmemA : ∀ a, a ∈ A ↔ a < q ∧ Nat.Coprime a q := by
      intro a
      rw [hA]
      simp
    have hposA : ∀ a ∈ A, 0 < a := by
      intro a ha
      have ha' := (hmemA a).mp ha
      rcases Nat.eq_zero_or_pos a with h0 | h
      · exfalso
        subst h0
        have : q = 1 := by simpa using ha'.2
        omega
      · exact h
    have hq0 : (q : ℝ) ≠ 0 := by
      have : 0 < q := by omega
      exact_mod_cast this.ne'
    have himageA : A.image (fun a => q - a) = A := by
      rw [hA]
      exact coprime_residues_image hq
    -- expand `A2` along `A`
    have hA2 : U1534.A2 n q =
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((Nat.totient q : ℂ) ^ 2) *
          ∑ a ∈ A, U1534.gaussS q a * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ))) := by
      simp only [U1534.A2, neg_div]
      rw [← hA]
    -- conjugation of the inner sum
    have hconjS : (starRingEnd ℂ)
        (∑ a ∈ A, U1534.gaussS q a * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ)))) =
        ∑ a ∈ A, U1534.gaussS q (q - a) * U1534.ee ((((a * n : ℕ) : ℝ) / (q : ℝ))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [map_mul, conj_gaussS (le_of_lt ((hmemA a).mp ha).1), conj_ee]
      simp
    -- reindex `a ↦ q - a`
    have hshift : (∑ a ∈ A, U1534.gaussS q (q - a) * U1534.ee ((((a * n : ℕ) : ℝ) / (q : ℝ)))) =
        ∑ b ∈ A, U1534.gaussS q b * U1534.ee (((((q - b) * n : ℕ) : ℝ) / (q : ℝ))) := by
      refine Finset.sum_bij (fun a _ => q - a) ?_ ?_ ?_ ?_
      · intro a ha
        refine (hmemA _).mpr ⟨Nat.sub_lt (by omega) (hposA a ha), ?_⟩
        exact (Nat.coprime_self_sub_left (le_of_lt ((hmemA a).mp ha).1)).mpr ((hmemA a).mp ha).2
      · intro a1 ha1 a2 ha2 heq
        have h1 := congrArg (fun t => q - t) heq
        rwa [Nat.sub_sub_self (le_of_lt ((hmemA a1).mp ha1).1),
          Nat.sub_sub_self (le_of_lt ((hmemA a2).mp ha2).1)] at h1
      · intro b hb
        refine ⟨q - b, (hmemA _).mpr ⟨Nat.sub_lt (by omega) (hposA b hb), ?_⟩,
          Nat.sub_sub_self (le_of_lt ((hmemA b).mp hb).1)⟩
        exact (Nat.coprime_self_sub_left (le_of_lt ((hmemA b).mp hb).1)).mpr ((hmemA b).mp hb).2
      · intro a ha
        rw [Nat.sub_sub_self (le_of_lt ((hmemA a).mp ha).1)]
    -- shift the character back by an integer
    have hback : (∑ b ∈ A, U1534.gaussS q b * U1534.ee (((((q - b) * n : ℕ) : ℝ) / (q : ℝ)))) =
        ∑ b ∈ A, U1534.gaussS q b * U1534.ee (-(((b * n : ℕ) : ℝ) / (q : ℝ))) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbq : b ≤ q := le_of_lt ((hmemA b).mp hb).1
      have hcast : (((q - b) * n : ℕ) : ℝ) = (q : ℝ) * (n : ℝ) - (b : ℝ) * (n : ℝ) := by
        rw [Nat.sub_mul, Nat.cast_sub (Nat.mul_le_mul_right n hbq), Nat.cast_mul, Nat.cast_mul]
      have hkey : ((q : ℝ) * (n : ℝ) - (b : ℝ) * (n : ℝ)) / (q : ℝ) =
          -(((b : ℝ) * (n : ℝ)) / (q : ℝ)) + ((n : ℤ) : ℝ) := by
        field_simp
        push_cast
        ring
      rw [hcast, hkey, ee_add_int, Nat.cast_mul]
    -- conjugation of the real prefactor
    have hc : (starRingEnd ℂ) (((ArithmeticFunction.moebius q : ℤ) : ℂ) /
        ((Nat.totient q : ℂ) ^ 2)) =
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((Nat.totient q : ℂ) ^ 2) := by
      simp
    rw [hA2, map_mul, hc, hconjS, hshift, hback]

/-- Page 15 second display. The conjugated interval estimate follows
from the already proved unconjugated estimate. CONDITIONAL on A2_conj. -/
theorem A2_conjugate_interval_bound {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ ≤
      2 * ∑ n ∈ Finset.range (q * r),
        ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
  simpa only [A2_conj] using A2_interval_bound hq hr hqr a b

/-- Page 15 second display and page 14 display 47. The coefficient
product bound controls the full period absolute sum. CONDITIONAL on
A2_coprime_mul through coefficient_product_bound. -/
theorem complete_period_majorant {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    (∑ n ∈ Finset.range (q * r),
      ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖) ≤
        localMajorant q * localMajorant r := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  calc
    _ ≤ ∑ _n ∈ Finset.range (q * r),
        (localMajorant q / (q : ℝ)) * (localMajorant r / (r : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_conj]
      exact mul_le_mul (coefficient_product_bound n q hq)
        (coefficient_product_bound n r hr) (norm_nonneg _)
        ((norm_nonneg _).trans (coefficient_product_bound n q hq))
    _ = localMajorant q * localMajorant r := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
      field_simp

/-- Pointwise product monotonicity for nonnegative real factors (no `MulLeftMono` for `ℝ`). -/
private lemma prod_le_prod_nonneg {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons ha, Finset.prod_cons ha]
    simp only [Finset.mem_cons, forall_eq_or_imp] at h0 h
    have hfs : 0 ≤ ∏ x ∈ s, f x := Finset.prod_nonneg h0.2
    exact mul_le_mul h.1 (ih h0.2 h.2) hfs (h0.1.trans h.1)

/-- A product of factors at least one is at least one. -/
private lemma one_le_prod_nonneg {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons ha]
    simp only [Finset.mem_cons, forall_eq_or_imp] at h
    have h1 := ih h.2
    nlinarith [h.1, h1]

/-- Extending a product by factors at least one increases it. -/
private lemma prod_le_prod_of_subset_nonneg {ι : Type*} {s t : Finset ι} {f : ι → ℝ}
    (hst : s ⊆ t) (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, i ∉ s → 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical
  have hsplit : ∏ i ∈ t, f i = (∏ i ∈ t \ s, f i) * (∏ i ∈ s, f i) := (Finset.prod_sdiff hst).symm
  have hone : 1 ≤ ∏ i ∈ t \ s, f i :=
    one_le_prod_nonneg (fun i hi => h1 i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2)
  have hpos : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => h0 i (hst hi))
  rw [hsplit]
  nlinarith [hone, hpos]

/-- Small primes divide `q` rarely enough that their local factors cost a constant. -/
private lemma localMajorant_small_part (q : ℕ) :
    ∏ p ∈ q.primeFactors.filter (fun p => p < 30), (1 + 6 / (p : ℝ)) ≤ (7 : ℝ) ^ 10 := by
  have h1 : ∀ p ∈ q.primeFactors.filter (fun p => p < 30), (1 + 6 / (p : ℝ)) ≤ 7 := by
    intro p hp
    have hpp : p ∈ q.primeFactors := (Finset.mem_filter.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have := Nat.prime_of_mem_primeFactors hpp
      have : 2 ≤ p := this.two_le
      exact_mod_cast this
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have h6 : 6 / (p : ℝ) ≤ 6 := by
      rw [div_le_iff₀ hp0]
      nlinarith
    linarith
  have hstep : ∏ p ∈ q.primeFactors.filter (fun p => p < 30), (1 + 6 / (p : ℝ))
      ≤ ∏ p ∈ q.primeFactors.filter (fun p => p < 30), (7 : ℝ) :=
    prod_le_prod_nonneg (fun i hi => by positivity) h1
  calc ∏ p ∈ q.primeFactors.filter (fun p => p < 30), (1 + 6 / (p : ℝ))
      ≤ ∏ p ∈ q.primeFactors.filter (fun p => p < 30), (7 : ℝ) := hstep
    _ = (7 : ℝ) ^ (q.primeFactors.filter (fun p => p < 30)).card := Finset.prod_const _
    _ ≤ (7 : ℝ) ^ 10 := by
        apply pow_le_pow_right₀ (by norm_num)
        have hsub : q.primeFactors.filter (fun p => p < 30) ⊆ (Finset.range 30).filter Nat.Prime := by
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
          exact ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
        have hcard := Finset.card_le_card hsub
        have h30 : ((Finset.range 30).filter Nat.Prime).card = 10 := by decide
        omega

/-- A prime at least `30` is dominated by `p ^ (1/8)`. -/
private lemma one_add_six_div_le_eighth {p : ℕ} (hp : 30 ≤ p) :
    1 + 6 / (p : ℝ) ≤ (p : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp30 : (30 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hle1 : 1 + 6 / (p : ℝ) ≤ 6 / 5 := by
    have h6 : 6 / (p : ℝ) ≤ 1 / 5 := by
      rw [div_le_iff₀ hp0]
      nlinarith
    linarith
  have hbase : ((6 / 5 : ℝ)) ^ 8 ≤ (p : ℝ) := by
    have hval : ((6 / 5 : ℝ)) ^ 8 = 1679616 / 390625 := by norm_num
    rw [hval]
    nlinarith
  have h2 : (6 / 5 : ℝ) ≤ (p : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
    calc (6 / 5 : ℝ) = (((6 / 5 : ℝ)) ^ 8) ^ ((8 : ℕ) : ℝ)⁻¹ :=
          (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
      _ ≤ ((p : ℝ)) ^ ((8 : ℕ) : ℝ)⁻¹ := Real.rpow_le_rpow (by norm_num) hbase (by positivity)
  linarith

/-- Large primes contribute at most `q ^ (1/8)` to the local majorant. -/
private lemma localMajorant_large_part (q : ℕ) (hq : 0 < q) :
    ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (1 + 6 / (p : ℝ)) ≤
      (q : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
  have h1 : ∀ p ∈ q.primeFactors.filter (fun p => ¬ p < 30),
      1 + 6 / (p : ℝ) ≤ (p : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
    intro p hp
    have h30 : 30 ≤ p := by
      have := (Finset.mem_filter.mp hp).2
      omega
    exact one_add_six_div_le_eighth h30
  have hstep : ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (1 + 6 / (p : ℝ))
      ≤ ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (p : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ :=
    prod_le_prod_nonneg (fun i hi => by positivity) h1
  calc ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (1 + 6 / (p : ℝ))
      ≤ ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (p : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := hstep
    _ = (∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (p : ℝ)) ^ ((8 : ℕ) : ℝ)⁻¹ :=
        Real.finsetProd_rpow _ _ (fun p hp => by positivity) _
    _ ≤ (∏ p ∈ q.primeFactors, (p : ℝ)) ^ ((8 : ℕ) : ℝ)⁻¹ := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        apply prod_le_prod_of_subset_nonneg (Finset.filter_subset _ _)
        · intro i hi
          positivity
        · intro i hi _
          have h2 : 2 ≤ i := (Nat.prime_of_mem_primeFactors hi).two_le
          exact_mod_cast (show (1 : ℕ) ≤ i by omega)
    _ ≤ (q : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        have hd := Nat.prod_primeFactors_dvd q
        have hle : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd hq hd
        have hcast : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
          push_cast
          ring
        rw [← hcast]
        exact_mod_cast hle

/-- Page 14 display 47 growth: the local majorant is at most `7^10 q ^ (1/8)`. -/
private lemma localMajorant_le (q : ℕ) (hq : 0 < q) :
    localMajorant q ≤ (7 : ℝ) ^ 10 * (q : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not (s := q.primeFactors) (p := fun p => p < 30)
    (f := fun p => 1 + 6 / (p : ℝ))
  rw [localMajorant, ← hsplit]
  have hsp := localMajorant_small_part q
  have hlp := localMajorant_large_part q hq
  have hsp0 : (0 : ℝ) ≤ ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (1 + 6 / (p : ℝ)) :=
    Finset.prod_nonneg (fun p hp => by positivity)
  have h7 : (0 : ℝ) ≤ (7 : ℝ) ^ 10 := by positivity
  exact mul_le_mul hsp hlp hsp0 h7

/-- LEAF. Page 15 third display, numerical part of the double sum.
The local products have arbitrarily small positive power growth by
page 14 display 47. Summing two such factors up to y to the one third
costs at most y to the three quarters. No A2, interval, or weight occurs. -/
theorem majorant_pair_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ y P : ℝ, 1 ≤ y → 0 < P →
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
          localMajorant q * localMajorant r) ≤ C * y ^ (3 / 4 : ℝ) := by
  refine ⟨4 * (7 : ℝ) ^ 20, by positivity, ?_⟩
  intro y P hy hP
  set Z : ℕ := ⌊y ^ (1 / 3 : ℝ)⌋₊ with hZ
  set S : Finset ℕ := Finset.Ioc ⌊P⌋₊ Z with hS
  have hy1 : (0 : ℝ) < y := by linarith
  have hlM : ∀ q : ℕ, (0 : ℝ) ≤ localMajorant q := by
    intro q
    rw [localMajorant]
    exact Finset.prod_nonneg (fun p _ => by positivity)
  have hy13 : (1 : ℝ) ≤ y ^ (1 / 3 : ℝ) := by
    have h1 : (1 : ℝ) ≤ y := hy
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / 3 : ℝ) := by simp
      _ ≤ y ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  have hZle : (Z : ℝ) ≤ y ^ (1 / 3 : ℝ) := by
    have hfl := Nat.floor_le (show (0 : ℝ) ≤ y ^ (1 / 3 : ℝ) by positivity)
    rwa [← hZ] at hfl
  have hbdd : ∀ q ∈ S, localMajorant q ≤ (7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ) := by
    intro q hq
    have hqmem := (hS ▸ hq : q ∈ Finset.Ioc ⌊P⌋₊ Z)
    have hq0 : 0 < q := by
      have := (Finset.mem_Ioc.mp hqmem).1
      omega
    have hqle : (q : ℝ) ≤ y ^ (1 / 3 : ℝ) := by
      have h2 : (q : ℝ) ≤ (Z : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hqmem).2
      linarith
    calc localMajorant q ≤ (7 : ℝ) ^ 10 * (q : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := localMajorant_le q hq0
      _ ≤ (7 : ℝ) ^ 10 * (y ^ (1 / 3 : ℝ)) ^ ((8 : ℕ) : ℝ)⁻¹ := by
          have hr : (q : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ ≤ (y ^ (1 / 3 : ℝ)) ^ ((8 : ℕ) : ℝ)⁻¹ :=
            Real.rpow_le_rpow (by positivity) hqle (by positivity)
          nlinarith
      _ = (7 : ℝ) ^ 10 * y ^ ((1 / 3 : ℝ) * ((8 : ℕ) : ℝ)⁻¹) := by
          rw [Real.rpow_mul (le_of_lt hy1)]
      _ = (7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ) := by norm_num
  have hsum_le : (∑ q ∈ S, localMajorant q) ≤
      2 * y ^ (1 / 3 : ℝ) * ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ)) := by
    have h1 : (∑ q ∈ S, localMajorant q) ≤ (S.card : ℝ) * ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ)) := by
      have h := Finset.sum_le_card_nsmul S localMajorant ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ)) hbdd
      simpa [nsmul_eq_mul] using h
    have hcard : (S.card : ℝ) ≤ 2 * y ^ (1 / 3 : ℝ) := by
      have hsub : S ⊆ Finset.range (Z + 1) := by
        intro q hq
        have hq' := (hS ▸ hq : q ∈ Finset.Ioc ⌊P⌋₊ Z)
        simp only [Finset.mem_range]
        have := (Finset.mem_Ioc.mp hq').2
        omega
      have hc : S.card ≤ Z + 1 := by
        have := Finset.card_le_card hsub
        simpa using this
      have hc' : (S.card : ℝ) ≤ (Z : ℝ) + 1 := by exact_mod_cast hc
      nlinarith
    have hnn : (0 : ℝ) ≤ (7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ) := by positivity
    nlinarith
  have hdouble : (∑ q ∈ S, ∑ r ∈ S.erase q, localMajorant q * localMajorant r)
      ≤ (∑ q ∈ S, localMajorant q) * (∑ r ∈ S, localMajorant r) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset q S)
      (fun r hr _ => mul_nonneg (hlM q) (hlM r))
  have hyadd : y ^ (1 / 3 : ℝ) * y ^ (1 / 24 : ℝ) = y ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add hy1]
    norm_num
  calc (∑ q ∈ S, ∑ r ∈ S.erase q, localMajorant q * localMajorant r)
      ≤ (∑ q ∈ S, localMajorant q) * (∑ r ∈ S, localMajorant r) := hdouble
    _ ≤ (2 * y ^ (1 / 3 : ℝ) * ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ))) *
          (2 * y ^ (1 / 3 : ℝ) * ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ))) := by
        have hsum0 : (0 : ℝ) ≤ ∑ q ∈ S, localMajorant q :=
          Finset.sum_nonneg (fun q _ => hlM q)
        have hup : (0 : ℝ) ≤ 2 * y ^ (1 / 3 : ℝ) * ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ)) := by positivity
        exact mul_le_mul hsum_le hsum_le hsum0 hup
    _ = (2 * (7 : ℝ) ^ 10 * (y ^ (1 / 3 : ℝ) * y ^ (1 / 24 : ℝ))) *
          (2 * (7 : ℝ) ^ 10 * (y ^ (1 / 3 : ℝ) * y ^ (1 / 24 : ℝ))) := by ring
    _ = (2 * (7 : ℝ) ^ 10 * y ^ (3 / 8 : ℝ)) * (2 * (7 : ℝ) ^ 10 * y ^ (3 / 8 : ℝ)) := by
        rw [hyadd]
    _ = 4 * (7 : ℝ) ^ 20 * (y ^ (3 / 8 : ℝ) * y ^ (3 / 8 : ℝ)) := by ring
    _ = 4 * (7 : ℝ) ^ 20 * y ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add hy1]
        norm_num

/-- Page 15 second display. Weights constant in n have norm at most one.
CONDITIONAL on A2_conj and A2_coprime_mul. -/
theorem weighted_pair_interval {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqr : q ≠ r) (x y Q : ℝ) :
    (∑ n ∈ intervalNumbers x y,
      ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
        (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
      2 * (localMajorant q * localMajorant r) := by
  let u : ℂ := -(smoothWeight q Q : ℂ)
  let v : ℂ := -(smoothWeight r Q : ℂ)
  have hu : ‖u‖ ≤ 1 := by simpa [u] using Task271b.smoothWeight_norm_le_one q Q
  have hv : ‖v‖ ≤ 1 := by simpa [v] using Task271b.smoothWeight_norm_le_one r Q
  have huv : ‖u * (starRingEnd ℂ) v‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    exact mul_le_one₀ hu (norm_nonneg _) hv
  have heq : (∑ n ∈ intervalNumbers x y,
      ((u * U1534.A2 n q) * (starRingEnd ℂ) (v * U1534.A2 n r)).re) =
      ((u * (starRingEnd ℂ) v) * (∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r))).re := by
    rw [← Complex.re_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_mul]
    ring
  change (∑ n ∈ intervalNumbers x y,
      ((u * U1534.A2 n q) * (starRingEnd ℂ) (v * U1534.A2 n r)).re) ≤ _
  rw [heq]
  calc
    _ ≤ ‖(u * (starRingEnd ℂ) v) * (∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r))‖ := Complex.re_le_norm _
    _ ≤ ‖∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) huv
    _ ≤ 2 * ∑ n ∈ Finset.range (q * r),
        ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
      simpa only [intervalNumbers, ← Finset.Ico_succ_succ_eq_Ioc] using
        A2_conjugate_interval_bound hq hr hqr (Order.succ ⌊x⌋₊) (Order.succ ⌊x + y⌋₊)
    _ ≤ _ := mul_le_mul_of_nonneg_left (complete_period_majorant hq hr) (by norm_num)

/-- Page 15 third display. Exact Task271b.off_diagonal_power_bound
statement. CONDITIONAL on multiplicativity, reality and the numerical
prime product sum. There is no sorry in this assembly. -/
theorem off_diagonal_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x y P Q : ℝ,
      0 ≤ x → 1 ≤ y → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
        C * y ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := majorant_pair_sum
  refine ⟨2 * C, by positivity, ?_⟩
  intro x y P Q hx hy hP
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
          2 * (localMajorant q * localMajorant r) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hrn : 0 < r := lt_of_le_of_lt (Nat.zero_le _)
        (Finset.mem_Ioc.mp (Finset.mem_of_mem_erase hr)).1
      exact weighted_pair_interval hqn hrn (Finset.ne_of_mem_erase hr).symm x y Q
    _ ≤ (2 * C) * y ^ (3 / 4 : ℝ) := by
      simp only [← Finset.mul_sum]
      have h := hb y P hy hP
      simp only [← Finset.mul_sum] at h
      nlinarith [h]

end LeanLab.KumchevLiu2007.Task292b
