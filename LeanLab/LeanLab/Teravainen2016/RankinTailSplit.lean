/-
P0076, Section 4, page 15, the Rankin bound for the divisors of P of y above z with
y = z^(1/K), used for the lower bound of G_1 after display 4.3; reference 10 Chapter 7.
Proof of leaf_rankin_tail in G1LowerSplit.lean with no LEAF: a proved Rankin divisor
inequality, a proved squarefree Euler product expansion of the weighted divisor sum,
a proved Mertens ratio bound from the lab's clean mertens1_upper_nat, and a proved assembly.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.G1LowerSplit
import LeanLab.AlmostPrimes.Decomp1528a

open Finset Real
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Page 15, Rankin's trick, PROVED: for s at least 0 and z positive, the sum of h d over the
divisors d of P of y above z is at most z^-s times the sum of h d d^s over all divisors. -/
theorem rankin_divisor_ineq (w : ℕ) (y z s : ℝ) (hs : 0 ≤ s) (hz : 0 < z) :
    ∑ d ∈ (envelopingPrimeProduct w y).divisors.filter (fun d : ℕ => z < (d : ℝ)),
        envelopingH w d ≤
      z ^ (-s) * ∑ d ∈ (envelopingPrimeProduct w y).divisors,
        envelopingH w d * (d : ℝ) ^ s := by
  rw [Finset.mul_sum]
  calc ∑ d ∈ (envelopingPrimeProduct w y).divisors.filter (fun d : ℕ => z < (d : ℝ)),
          envelopingH w d
      ≤ ∑ d ∈ (envelopingPrimeProduct w y).divisors.filter (fun d : ℕ => z < (d : ℝ)),
          z ^ (-s) * (envelopingH w d * (d : ℝ) ^ s) := by
        apply Finset.sum_le_sum
        intro d hd
        have hzd : z < (d : ℝ) := (Finset.mem_filter.mp hd).2
        have h1 : 1 ≤ z ^ (-s) * (d : ℝ) ^ s := by
          rw [Real.rpow_neg hz.le]
          have hzs : 0 < z ^ s := Real.rpow_pos_of_pos hz s
          have hle : z ^ s ≤ (d : ℝ) ^ s := Real.rpow_le_rpow hz.le hzd.le hs
          rw [inv_mul_eq_div, le_div_iff₀ hzs]
          linarith
        have hh := envelopingH_nonneg w d
        nlinarith
    _ ≤ ∑ d ∈ (envelopingPrimeProduct w y).divisors,
          z ^ (-s) * (envelopingH w d * (d : ℝ) ^ s) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro d _ _
        have := envelopingH_nonneg w d
        positivity

/-- Page 15, the expansion of the Euler product of 1 + h p p^s over w < p at most y into
the sum of h d d^s over the divisors d of the squarefree P of y, as for the identity behind
display 4.3 and reference 10 Chapter 7. PROVED from Mathlib's squarefree expansion of a
multiplicative function, since h d d^s is the product over the primes of d on squarefree d. -/
theorem divisor_sum_euler_product :
    ∀ w : ℕ, ∀ y s : ℝ, 0 ≤ s →
      ∑ d ∈ (envelopingPrimeProduct w y).divisors, envelopingH w d * (d : ℝ) ^ s =
        ∏ p ∈ (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y),
          (1 + envelopingH w p * (p : ℝ) ^ s) := by
  intro w y s _
  set S := (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y) with hS
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hP : envelopingPrimeProduct w y = ∏ p ∈ S, p := rfl
  have hPsq : Squarefree (∏ p ∈ S, p) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro a ha b hb hab
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hSp a ha) (hSp b hb)).mpr hab)
    · intro p hp; exact (hSp p hp).squarefree
  set g : ℕ → ℝ := fun p => (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) * (p : ℝ) ^ s
  set F : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors g
  have hF : F.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors g
  have key : ∀ d : ℕ, Squarefree d → envelopingH w d * (d : ℝ) ^ s = F d := by
    intro d hd
    have hd0 : d ≠ 0 := hd.ne_zero
    simp only [F, ArithmeticFunction.prodPrimeFactors_apply hd0, envelopingH, ite_eq_left_of_eq_true _ _ (eq_true hd), g]
    rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (fun i _ => Nat.cast_nonneg i)]
    congr 2
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  have hprime : ∀ p : ℕ, p.Prime → envelopingH w p * (p : ℝ) ^ s = F p := fun p hp =>
    key p hp.squarefree
  rw [hP, Finset.sum_congr rfl (fun d hd => key d (Squarefree.squarefree_of_dvd
      (Nat.dvd_of_mem_divisors hd) hPsq))]
  rw [← hF.prodPrimeFactors_one_add_of_squarefree hPsq, Nat.primeFactors_prod hSp]
  exact Finset.prod_congr rfl (fun p hp => by rw [hprime p (hSp p hp)])

/-- Page 15, h at a prime p is omega p over p - omega p. -/
theorem envelopingH_prime (w p : ℕ) (hp : p.Prime) :
    envelopingH w p = (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) := by
  unfold envelopingH
  rw [ite_eq_left_of_eq_true _ _ (eq_true hp.squarefree), hp.primeFactors, Finset.prod_singleton]

/-- Page 15, the Mertens comparison in Rankin's trick, reference 10 Chapter 7. PROVED.
With s = 1 / log y and y > 1, p^s - 1 is at most 2 s log p for p at most y, h p is at most
4 / p for p > 10, and 1 + h p equals the inverse of 1 - omega p / p, so the ratio of the two
products is at most exp of 8 s times the sum of log p / p over p at most y, which the lab's
clean Mertens first theorem bound mertens1_upper_nat in AlmostPrimes/Decomp1528a makes at
most exp of 8 times 1 + log 4, using log y at least 1 whenever a prime above w lies below y. -/
theorem rankin_mertens_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, wBig ≤ w → ∀ y : ℝ, 1 < y →
      ∏ p ∈ (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y),
          (1 + envelopingH w p * (p : ℝ) ^ (1 / Real.log y)) ≤
        C * ∏ p ∈ (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
  refine ⟨Real.exp (8 * (1 + Real.log 4)), Real.exp_pos _, ?_⟩
  intro w hw y hy
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw10 : (10 : ℝ) ≤ w := hwBig1.trans hw
  set S := (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y) with hS
  set s := 1 / Real.log y with hs
  have hlogy0 : 0 < Real.log y := Real.log_pos hy
  have hs0 : 0 < s := by positivity
  -- per prime facts
  have hfacts : ∀ p ∈ S, 0 ≤ envelopingH w p ∧
      1 + envelopingH w p = (1 - (envelopingOmega w p : ℝ) / p)⁻¹ ∧
      envelopingH w p ≤ 4 * (1 / (p : ℝ)) ∧
      (p : ℝ) ^ s - 1 ≤ 2 * (s * Real.log p) ∧ 1 ≤ Real.log y := by
    intro p hp
    have h := (mem_filter.mp hp).2
    have h10 : (10 : ℝ) < p := lt_of_le_of_lt hw10 (by exact_mod_cast h.2.1)
    have hω2 : envelopingOmega w p ≤ 2 := by unfold envelopingOmega; split_ifs <;> omega
    have hω : (envelopingOmega w p : ℝ) ≤ 2 := by exact_mod_cast hω2
    have hp10 : 10 < p := by exact_mod_cast h10
    have hcast : ((p - envelopingOmega w p : ℕ) : ℝ) = (p : ℝ) - envelopingOmega w p := by
      rw [Nat.cast_sub (by omega)]
    have hden : 0 < (p : ℝ) - envelopingOmega w p := by linarith
    have hω0 : (0 : ℝ) ≤ envelopingOmega w p := Nat.cast_nonneg _
    have hHp := envelopingH_prime w p h.1
    rw [hcast] at hHp
    have hp0 : (0 : ℝ) < p := by linarith
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hlogpy : Real.log p ≤ Real.log y := Real.log_le_log hp0 h.2.2
    have hlogy1 : 1 ≤ Real.log y := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith [h.2.2]
    refine ⟨envelopingH_nonneg w p, ?_, ?_, ?_, hlogy1⟩
    · rw [hHp]
      have : (1 - (envelopingOmega w p : ℝ) / p) = ((p : ℝ) - envelopingOmega w p) / p := by
        field_simp
      rw [this, inv_div]
      field_simp
      ring
    · rw [hHp, div_le_iff₀ hden]
      rw [show 4 * (1 / (p : ℝ)) * ((p : ℝ) - envelopingOmega w p) =
        4 - 4 * envelopingOmega w p / p by field_simp]
      have : (envelopingOmega w p : ℝ) / p ≤ 2 / p := div_le_div_of_nonneg_right hω hp0.le
      have : 2 / (p : ℝ) ≤ 1 / 5 := by rw [div_le_iff₀ hp0]; linarith
      have : 4 * (envelopingOmega w p : ℝ) / p = 4 * ((envelopingOmega w p : ℝ) / p) := by ring
      linarith
    · have hx0 : 0 ≤ s * Real.log p := by positivity
      have hx1 : s * Real.log p ≤ 1 := by
        rw [hs, one_div, inv_mul_le_iff₀ hlogy0]; linarith
      rw [Real.rpow_def_of_pos hp0, mul_comm]
      have := Real.abs_exp_sub_one_sub_id_le (x := s * Real.log p) (by rw [abs_le]; constructor <;> linarith)
      rw [abs_le] at this
      nlinarith
  -- per prime product bound
  have hper : ∀ p ∈ S, 1 + envelopingH w p * (p : ℝ) ^ s ≤
      (1 - (envelopingOmega w p : ℝ) / p)⁻¹ *
        Real.exp (8 * (s * (Real.log p / p))) := by
    intro p hp
    obtain ⟨ha0, ha1, ha4, hts, -⟩ := hfacts p hp
    have h := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h.1.one_lt.le
    have ht1 : 1 ≤ (p : ℝ) ^ s := Real.one_le_rpow hp1 hs0.le
    rw [← ha1]
    set a := envelopingH w p
    set t := (p : ℝ) ^ s
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hq : a * (t - 1) ≤ 8 * (s * (Real.log p / p)) := by
      have hb : a * (t - 1) ≤ (4 * (1 / (p : ℝ))) * (2 * (s * Real.log p)) :=
        mul_le_mul ha4 hts (by linarith) (by positivity)
      calc a * (t - 1) ≤ (4 * (1 / (p : ℝ))) * (2 * (s * Real.log p)) := hb
        _ = 8 * (s * (Real.log p / p)) := by field_simp; ring
    have he := Real.add_one_le_exp (a * (t - 1))
    have : Real.exp (a * (t - 1)) ≤ Real.exp (8 * (s * (Real.log p / p))) := Real.exp_le_exp.mpr hq
    have h1 : 1 + a * t ≤ (1 + a) * (1 + a * (t - 1)) := by
      nlinarith [mul_nonneg (mul_nonneg ha0 ha0) (sub_nonneg.mpr ht1)]
    calc 1 + a * t ≤ (1 + a) * (1 + a * (t - 1)) := h1
      _ ≤ (1 + a) * Real.exp (8 * (s * (Real.log p / p))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hprod := Finset.prod_le_prod₀ (fun p hp => by
      have := (hfacts p hp).1
      have : (0:ℝ) ≤ (p : ℝ) ^ s := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity) hper
  rw [Finset.prod_mul_distrib, ← Real.exp_sum] at hprod
  refine hprod.trans ?_
  rw [mul_comm (Real.exp _)]
  have hE0 : 0 ≤ ∏ p ∈ S, (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
    apply Finset.prod_nonneg; intro p hp
    rw [← (hfacts p hp).2.1]; linarith [(hfacts p hp).1]
  apply mul_le_mul_of_nonneg_left _ hE0
  apply Real.exp_le_exp.mpr
  rcases S.eq_empty_or_nonempty with hSe | ⟨q, hq⟩
  · rw [hSe, Finset.sum_empty]; positivity
  have hlogy1 := (hfacts q hq).2.2.2.2
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  -- Mertens
  have hy1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hM := LeanLab.AlmostPrimes.Decomp1528a.mertens1_upper_nat ⌊y⌋₊ hy1
  have hsub : S ⊆ Nat.primesLE ⌊y⌋₊ := by
    intro p hp
    have h := mem_filter.mp hp
    rw [Nat.primesLE, Nat.mem_primesBelow]
    exact ⟨Finset.mem_range.mp h.1, h.2.1⟩
  have hsum : ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ Nat.primesLE ⌊y⌋₊, Real.log p / p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by
      have : (0:ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
      positivity)
  have hfl : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y :=
    Real.log_le_log (by exact_mod_cast hy1) (Nat.floor_le (by linarith))
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc s * ∑ p ∈ S, Real.log p / p ≤ s * (Real.log y + Real.log 4) :=
        mul_le_mul_of_nonneg_left (by linarith) hs0.le
    _ = 1 + s * Real.log 4 := by rw [hs]; field_simp
    _ ≤ 1 + Real.log 4 := by
        have : s ≤ 1 := by rw [hs, div_le_one hlogy0]; exact hlogy1
        nlinarith

/-- Page 15, the Rankin bound, PROVED from the Rankin divisor inequality and the two lemmas
above, with K = max 1 of log 2C so that e^-K C is at most 1/2. Exactly the statement of
leaf_rankin_tail in G1LowerSplit.lean. -/
theorem rankin_tail_of_leaves :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      ∑ d ∈ (envelopingPrimeProduct w (z ^ (1 / K))).divisors.filter (fun d : ℕ => z < (d : ℝ)),
          envelopingH w d ≤
        (1 / 2) * ∏ p ∈ (range (⌊z ^ (1 / K)⌋₊ + 1)).filter
          (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z ^ (1 / K)),
            (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
  obtain ⟨C, hC, HC⟩ := rankin_mertens_ratio
  refine ⟨max 1 (Real.log (2 * C)), le_max_left _ _, ?_⟩
  set K := max 1 (Real.log (2 * C)) with hKdef
  have hK0 : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
  intro w hw z hz
  rcases hz.lt_or_eq with hz1 | hz1
  · set y := z ^ (1 / K) with hydef
    have hz0 : 0 < z := lt_trans one_pos hz1
    have hlogz : 0 < Real.log z := Real.log_pos hz1
    have hy1 : 1 < y := Real.one_lt_rpow hz1 (by positivity)
    have hlogy : Real.log y = Real.log z * (1 / K) := by rw [hydef, Real.log_rpow hz0]; ring
    have hlogy0 : 0 < Real.log y := Real.log_pos hy1
    set s := 1 / Real.log y with hsdef
    have hs0 : 0 ≤ s := by positivity
    have hR := rankin_divisor_ineq w y z s hs0 hz0
    rw [divisor_sum_euler_product w y s hs0] at hR
    have hM := HC w hw y hy1
    have hzs : z ^ (-s) = Real.exp (-K) := by
      rw [Real.rpow_def_of_pos hz0, hsdef, hlogy]
      congr 1
      field_simp
    have hexp : Real.exp (-K) ≤ 1 / (2 * C) := by
      have : Real.log (2 * C) ≤ K := le_max_right _ _
      calc Real.exp (-K) ≤ Real.exp (-Real.log (2 * C)) := Real.exp_le_exp.mpr (by linarith)
        _ = 1 / (2 * C) := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]; simp
    have hPnn : 0 ≤ ∏ p ∈ (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y),
          (1 + envelopingH w p * (p : ℝ) ^ s) := by
      apply Finset.prod_nonneg
      intro p _
      have := envelopingH_nonneg w p
      positivity
    set A := ∏ p ∈ (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y),
          (1 + envelopingH w p * (p : ℝ) ^ s)
    set E := ∏ p ∈ (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹
    rw [hzs] at hR
    have hCE : 0 ≤ C * E := le_trans hPnn hM
    have h1 : Real.exp (-K) * A ≤ Real.exp (-K) * (C * E) :=
      mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    have h2 : Real.exp (-K) * (C * E) ≤ 1 / (2 * C) * (C * E) :=
      mul_le_mul_of_nonneg_right hexp hCE
    have h3 : 1 / (2 * C) * (C * E) = 1 / 2 * E := by field_simp
    linarith
  · subst hz1
    have hy : (1 : ℝ) ^ (1 / K) = 1 := Real.one_rpow _
    have hempty : (range (⌊(1 : ℝ)⌋₊ + 1)).filter
        (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ 1) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, Nat.floor_one, Finset.notMem_empty,
        iff_false, not_and]
      intro _ hp _ hp1
      have := hp.two_le
      have : (2 : ℝ) ≤ p := by exact_mod_cast this
      linarith
    simp only [envelopingPrimeProduct, hy, hempty, Finset.prod_empty, Nat.divisors_one]
    rw [Finset.filter_singleton]
    norm_num

end LeanLab.Teravainen2016
