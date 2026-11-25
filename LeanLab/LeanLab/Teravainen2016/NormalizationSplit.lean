/-
P0076, Section 4, page 15, the lower bound for G_1 after display 4.3.
Split of the uniform normalization leaf paper_enveloping_normalization_input in
MainInputsRestriction.lean into two cited LEAF pieces, a proved Mertens step and a proved assembly.
The paper chain is G_1 of z at least 10^-10 times the product over w < p < z of
the inverse of 1 - omega p / p, which is at least 10^-20 times log N to the 3/2
times log w to the -3/2. The assembly also uses phi W / W at most 1 / log w.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MainInputsRestriction
import LeanLab.AlmostPrimes.Decomp1528b

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016


/- The proofs below are the in-tree proofs of the two cited LEAFs of G1LowerSplit.lean and of
the Rankin tail, copied here as private helpers because G1LowerSplit.lean imports this file
and importing it back would be a cycle. Their statements are unchanged. -/

/-- For 0 at most x at most 1/2 the inverse of 1 - x is at most exp 2x. -/
private theorem inv_one_sub_le_exp_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have h1 : 0 < 1 - x := by linarith
  rw [inv_le_comm₀ h1 (Real.exp_pos _), ← Real.exp_neg]
  have h2 := Real.add_one_le_exp (2 * x)
  have h3 : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-(2 * x)) := Real.exp_pos _
  nlinarith

/-- Page 15, the Mertens comparison of the Euler products at z^(1/K) and at z.
PROVED: the product over z^(1/K) < p at most z, p > w, of the inverse of 1 - omega p / p is at most
exp of 4 times the sum of 1/p there, since omega p is at most 2 and p > 10, and that sum is at most
log K + 4 by the lab's clean mertens2_block in AlmostPrimes/Decomp1528b. -/
private theorem euler_product_level_change :
    ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ ≤
        C * ∏ p ∈ (range (⌊z ^ (1 / K)⌋₊ + 1)).filter
          (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z ^ (1 / K)),
            (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
  intro K hK
  refine ⟨Real.exp (4 * (Real.log K + 4)), Real.exp_pos _, ?_⟩
  intro w hw z hz
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw10 : (10 : ℝ) ≤ w := hwBig1.trans hw
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  set y := z ^ (1 / K) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hz (by positivity)
  have hyz : y ≤ z := by
    calc y ≤ z ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hz (by rw [div_le_one hK0]; exact hK)
      _ = z := Real.rpow_one z
  set f : ℕ → ℝ := fun p => (1 - (envelopingOmega w p : ℝ) / p)⁻¹ with hf
  set Fz := (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z) with hFz
  set Fy := (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y) with hFy
  set G := Fz.filter (fun p : ℕ => y < (p : ℝ)) with hG
  have hsplit : Fz.filter (fun p : ℕ => ¬ y < (p : ℝ)) = Fy := by
    ext p
    simp only [hFz, hFy, mem_filter, mem_range, not_lt]
    constructor
    · rintro ⟨⟨-, hp, hwp, -⟩, hpy⟩
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpy), hp, hwp, hpy⟩
    · rintro ⟨-, hp, hwp, hpy⟩
      exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor (hpy.trans hyz)), hp, hwp, hpy.trans hyz⟩, hpy⟩
  have hprod : ∏ p ∈ Fz, f p = (∏ p ∈ G, f p) * ∏ p ∈ Fy, f p := by
    rw [← prod_filter_mul_prod_filter_not Fz (fun p : ℕ => y < (p : ℝ)), hsplit]
  -- facts on primes in Fz
  have hx : ∀ p ∈ Fz, 0 ≤ (envelopingOmega w p : ℝ) / p ∧ (envelopingOmega w p : ℝ) / p ≤ 1 / 2 ∧
      (envelopingOmega w p : ℝ) / p ≤ 2 * (1 / (p : ℝ)) := by
    intro p hp
    have h := (mem_filter.mp hp).2
    have h10 : (10 : ℝ) < p := lt_of_le_of_lt hw10 (by exact_mod_cast h.2.1)
    have hω : (envelopingOmega w p : ℝ) ≤ 2 := by
      unfold envelopingOmega; split_ifs <;> norm_num
    refine ⟨by positivity, ?_, ?_⟩
    · rw [div_le_iff₀ (by linarith)]; linarith
    · rw [mul_one_div]; exact div_le_div_of_nonneg_right hω (by linarith)
  have hf0 : ∀ p ∈ Fz, 0 ≤ f p := by
    intro p hp
    have := hx p hp
    simp only [hf]; apply inv_nonneg.mpr; linarith
  have hGexp : ∏ p ∈ G, f p ≤ Real.exp (4 * ∑ p ∈ G, (1 : ℝ) / p) := by
    rw [mul_sum, Real.exp_sum]
    apply prod_le_prod₀ (fun p hp => hf0 p (filter_subset _ _ hp))
    intro p hp
    obtain ⟨h0, h12, h2⟩ := hx p (filter_subset _ _ hp)
    calc f p ≤ Real.exp (2 * ((envelopingOmega w p : ℝ) / p)) := inv_one_sub_le_exp_two_mul h0 h12
      _ ≤ Real.exp (4 * (1 / (p : ℝ))) := Real.exp_le_exp.mpr (by linarith)
  have hFy0 : 0 ≤ ∏ p ∈ Fy, f p := by
    apply prod_nonneg; intro p hp
    rw [← hsplit] at hp
    exact hf0 p (filter_subset _ _ hp)
  -- bound the sum over G by Mertens
  set y' := max y (w : ℝ) with hy'
  have hy'2 : 2 ≤ y' := le_trans (by linarith) (le_max_right y (w : ℝ))
  have hGsum : ∑ p ∈ G, (1 : ℝ) / p ≤ Real.log K + 4 := by
    by_cases hzy : z < y'
    · have hGe : G = ∅ := by
        apply eq_empty_of_forall_notMem
        intro p hp
        have h1 := (mem_filter.mp hp)
        have h2 := (mem_filter.mp h1.1).2
        have hpw : (w : ℝ) < p := by exact_mod_cast h2.2.1
        have : y' < p := max_lt h1.2 hpw
        linarith [h2.2.2]
      rw [hGe, sum_empty]
      have := Real.log_nonneg hK
      linarith
    · push Not at hzy
      have hM := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block hy'2 hzy
      have hsub : G ⊆ (Ioc ⌊y'⌋₊ ⌊z⌋₊).filter Nat.Prime := by
        intro p hp
        have h1 := (mem_filter.mp hp)
        have h2 := (mem_filter.mp h1.1).2
        have hpw : (w : ℝ) < p := by exact_mod_cast h2.2.1
        have hpy' : y' < p := max_lt h1.2 hpw
        simp only [mem_filter, mem_Ioc]
        refine ⟨⟨?_, Nat.le_floor h2.2.2⟩, h2.1⟩
        exact (Nat.floor_lt (by linarith)).mpr hpy'
      have hle := sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => by positivity : ∀ p ∈ (Ioc ⌊y'⌋₊ ⌊z⌋₊).filter Nat.Prime, p ∉ G → (0 : ℝ) ≤ 1 / p)
      have hlogy' : 1 ≤ Real.log y' := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1)
          (by linarith [Real.exp_one_lt_d9, le_max_right y (w : ℝ)])
      have h4 : 4 / Real.log y' ≤ 4 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hz1 : 1 < z := by linarith
      have hlogz : 0 < Real.log z := Real.log_pos hz1
      have hlogy : Real.log y = Real.log z / K := by
        rw [hy, Real.log_rpow (by linarith)]; ring
      have hll : Real.log (Real.log z) - Real.log (Real.log y') ≤ Real.log K := by
        have hyy' : Real.log y ≤ Real.log y' := Real.log_le_log (by linarith) (le_max_left _ _)
        have hpos : 0 < Real.log z / K := div_pos hlogz hK0
        have : Real.log (Real.log z / K) ≤ Real.log (Real.log y') :=
          Real.log_le_log hpos (by rw [← hlogy]; exact hyy')
        rw [Real.log_div hlogz.ne' hK0.ne'] at this
        linarith
      have := (abs_le.mp hM).2
      linarith
  have hfin : ∏ p ∈ G, f p ≤ Real.exp (4 * (Real.log K + 4)) :=
    hGexp.trans (Real.exp_le_exp.mpr (by linarith))
  change ∏ p ∈ Fz, f p ≤ _ * ∏ p ∈ Fy, f p
  rw [hprod]
  exact mul_le_mul_of_nonneg_right hfin hFy0



/-- A product of a finset of primes is squarefree. -/
private theorem squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
  · intro p hp; exact (hs p hp).squarefree

/-- Page 15, statement of leaf_G1_ge_product_sub_tail, PROVED. Since 1 + h p equals the inverse of
1 - omega p / p for w < p, the Euler product at y is the sum of h d over the divisors d of the
squarefree P of y, and the divisors at most z are terms of G_1 of z, whose other terms are
nonnegative. -/
private theorem G1_ge_product_sub_tail_proved :
    ∀ w : ℕ, wBig ≤ w → ∀ y z : ℝ, 1 ≤ y → y ≤ z →
      (∏ p ∈ (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹) -
        ∑ d ∈ (envelopingPrimeProduct w y).divisors.filter (fun d : ℕ => z < (d : ℝ)), envelopingH w d ≤
          envelopingG w 1 z := by
  intro w hw y z hy hyz
  set F := (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y) with hF
  have hFp : ∀ p ∈ F, p.Prime := fun p hp => (mem_filter.mp hp).2.1
  set P := envelopingPrimeProduct w y with hP
  have hPF : P = ∏ p ∈ F, p := rfl
  have hPsq : Squarefree P := hPF ▸ squarefree_prod_primes F hFp
  have hPpf : P.primeFactors = F := by rw [hPF]; exact Nat.primeFactors_prod hFp
  set g : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors
    (fun p => (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ)) with hg
  have hgm : g.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hexp := hgm.prodPrimeFactors_one_add_of_squarefree hPsq
  have hgH : ∀ d ∈ P.divisors, g d = envelopingH w d := by
    intro d hd
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have hdsq : Squarefree d := hPsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    rw [hg, ArithmeticFunction.prodPrimeFactors_apply hd0, envelopingH]
    simp only [hdsq, ↓reduceIte]
  have hgp : ∀ p ∈ F, 1 + g p = (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
    intro p hp
    have hpp := hFp p hp
    have hwp : w < p := (mem_filter.mp hp).2.2.1
    have hwBig1 : (10 : ℝ) ≤ wBig := by
      calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (Real.one_le_rpow (by norm_num) (by positivity))
    have h10 : (10 : ℝ) < p := lt_of_le_of_lt (hwBig1.trans hw) (by exact_mod_cast hwp)
    have hω : envelopingOmega w p ≤ 2 := by
      unfold envelopingOmega; split_ifs <;> norm_num
    have hωp : envelopingOmega w p < p := by
      have : (10 : ℕ) < p := by exact_mod_cast h10
      omega
    rw [hg, ArithmeticFunction.prodPrimeFactors_apply hpp.ne_zero, hpp.primeFactors,
      prod_singleton, Nat.cast_sub hωp.le]
    have hωr : (envelopingOmega w p : ℝ) < p := by exact_mod_cast hωp
    have hp0 : (0 : ℝ) < p := by linarith
    have h1 : (p : ℝ) - envelopingOmega w p ≠ 0 := by linarith
    rw [one_sub_div hp0.ne', inv_div]
    field_simp
    ring
  have hprod : (∏ p ∈ F, (1 - (envelopingOmega w p : ℝ) / p)⁻¹) =
      ∑ d ∈ P.divisors, envelopingH w d := by
    rw [← prod_congr rfl hgp, ← hPpf, hexp]
    exact sum_congr rfl hgH
  rw [hprod, ← sum_filter_add_sum_filter_not P.divisors (fun d : ℕ => z < (d : ℝ)),
    add_sub_cancel_left]
  unfold envelopingG
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hd, hdz⟩ := mem_filter.mp hd
    push Not at hdz
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hd1, Nat.le_floor hdz⟩, ?_⟩
    simpa only [Nat.lcm_one_left] using hdz
  · intro d _ _
    exact envelopingH_nonneg w d


/-- Page 15, Rankin's trick, PROVED: for s at least 0 and z positive, the sum of h d over the
divisors d of P of y above z is at most z^-s times the sum of h d d^s over all divisors. -/
private theorem rankin_divisor_ineq (w : ℕ) (y z s : ℝ) (hs : 0 ≤ s) (hz : 0 < z) :
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
private theorem divisor_sum_euler_product :
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
private theorem envelopingH_prime (w p : ℕ) (hp : p.Prime) :
    envelopingH w p = (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) := by
  unfold envelopingH
  rw [ite_eq_left_of_eq_true _ _ (eq_true hp.squarefree), hp.primeFactors, Finset.prod_singleton]

/-- Page 15, the Mertens comparison in Rankin's trick, reference 10 Chapter 7. PROVED.
With s = 1 / log y and y > 1, p^s - 1 is at most 2 s log p for p at most y, h p is at most
4 / p for p > 10, and 1 + h p equals the inverse of 1 - omega p / p, so the ratio of the two
products is at most exp of 8 s times the sum of log p / p over p at most y, which the lab's
clean Mertens first theorem bound mertens1_upper_nat in AlmostPrimes/Decomp1528a makes at
most exp of 8 times 1 + log 4, using log y at least 1 whenever a prime above w lies below y. -/
private theorem rankin_mertens_ratio :
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
private theorem rankin_tail_of_leaves :
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



/-- LEAF: page 15, first inequality of the display after display 4.3,
G_1 of z is at least 10^-10 times the product over w < p < z of the inverse of 1 - omega p / p.
Class HARD. It is the Selberg sieve lower bound for the truncated sum G_1 of the
dimension 3/2 multiplicative weight h, as in reference 18 Section 4 and reference 10 Chapter 7.
The prime range uses the inclusive endpoint p at most z of envelopingPrimeProduct, see the
endpoint QUESTION in PROGRESS.md; any positive constant is allowed. -/
theorem leaf_G1_ge_euler_product :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      c₀ * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ ≤ envelopingG w 1 z := by
  obtain ⟨K, hK, HT⟩ := rankin_tail_of_leaves
  obtain ⟨C, hC, HC⟩ := euler_product_level_change K hK
  refine ⟨1 / (2 * C), by positivity, ?_⟩
  intro w hw z hz
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hy1 : 1 ≤ z ^ (1 / K) := Real.one_le_rpow hz (by positivity)
  have hyz : z ^ (1 / K) ≤ z := by
    calc z ^ (1 / K) ≤ z ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hz (by rw [div_le_one hK0]; exact hK)
      _ = z := Real.rpow_one z
  have hA := G1_ge_product_sub_tail_proved w hw (z ^ (1 / K)) z hy1 hyz
  have hT := HT w hw z hz
  have hCz := HC w hw z hz
  set Ey := ∏ p ∈ (range (⌊z ^ (1 / K)⌋₊ + 1)).filter
    (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z ^ (1 / K)), (1 - (envelopingOmega w p : ℝ) / p)⁻¹
  set Ez := ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
    (1 - (envelopingOmega w p : ℝ) / p)⁻¹
  have h1 : 1 / (2 * C) * Ez ≤ 1 / (2 * C) * (C * Ey) :=
    mul_le_mul_of_nonneg_left hCz (by positivity)
  have h2 : 1 / (2 * C) * (C * Ey) = (1 / 2) * Ey := by field_simp
  linarith

/-- LEAF: page 15, second inequality of the display after display 4.3,
the product over w < p < z of the inverse of 1 - omega p / p is at least a constant times
log z to the 3/2 times log w to the -3/2, with log N equal to 10 log z.
Class MEDIUM. It is the Mertens estimate for primes in the classes 1 and 3 mod 4, where
omega p is 1 and 2, so the sum of omega p / p over w < p at most z is 3/2 log log z
minus 3/2 log log w up to a bounded error. For z below w the product is empty and the
left side is below one. -/
theorem leaf_euler_product_ge_log_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) ≤
        C * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
  sorry

/-- Display 3.3 and display 3.4, the normalization phi W / W of the weight f
compared with log w, as used on page 15 to match the lower bound of G_1.
PROVED: every prime p at most w divides W = 2^J 3^3 times the primes 5 to w, so
phi W / W is at most the product over p at most w of 1 - 1/p, which is at most 1 / log w
by the lab's elementary Mertens bound mertens_prod_upper in AlmostPrimes/Decomp1528b. -/
theorem totient_ratio_le_inv_log :
    ∀ J w : ℕ, 5 ≤ J → wBig ≤ w →
      (Nat.totient (WW J w).toNat : ℝ) / WW J w ≤ 1 / Real.log w := by
  intro J w hJ hw
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw10 : (10 : ℝ) ≤ w := hwBig1.trans hw
  set n : ℕ := 2 ^ J * 27 * ∏ p ∈ Sw w, p with hn
  have hWn : WW J w = (n : ℤ) := by
    simp only [WW, Wmod, hn]; push_cast; ring
  have hn0 : n ≠ 0 := by
    rw [hn]
    refine mul_ne_zero (by positivity) ?_
    exact prod_ne_zero_iff.mpr fun p hp => (Sw_spec w p hp).1.ne_zero
  rw [hWn, Int.toNat_natCast]
  push_cast
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hφ : (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    exact h
  rw [hφ, mul_div_cancel_left₀ _ hnr.ne']
  have hsub : Nat.primesLE w ⊆ n.primeFactors := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hpw : p ≤ w := Nat.le_of_mem_primesLE hp
    rw [Nat.mem_primeFactors]
    refine ⟨hpp, ?_, hn0⟩
    rw [hn]
    by_cases h2 : p = 2
    · subst h2
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _) _
    by_cases h3 : p = 3
    · subst h3
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (by norm_num) _) _
    have h5 : 5 ≤ p := by
      have := hpp.two_le
      rcases (show p = 4 ∨ 5 ≤ p by omega) with h4 | h4
      · subst h4; exact absurd hpp (by decide)
      · exact h4
    apply Dvd.dvd.mul_left
    apply dvd_prod_of_mem
    simp only [Sw, mem_filter, mem_Icc]
    exact ⟨⟨h5, hpw⟩, hpp⟩
  have hfac : ∀ p ∈ n.primeFactors, 0 ≤ 1 - (p : ℝ)⁻¹ ∧ 1 - (p : ℝ)⁻¹ ≤ 1 := by
    intro p hp
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    constructor
    · rw [sub_nonneg]; exact inv_le_one_of_one_le₀ h1
    · have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
      linarith
  have hle : ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) ≤
      ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹) := by
    rw [← prod_sdiff hsub]
    have h1 : ∏ p ∈ n.primeFactors \ Nat.primesLE w, (1 - (p : ℝ)⁻¹) ≤ 1 :=
      prod_le_one₀ (fun p hp => (hfac p (sdiff_subset hp)).1)
        (fun p hp => (hfac p (sdiff_subset hp)).2)
    have h2 : 0 ≤ ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹) :=
      prod_nonneg fun p hp => (hfac p (hsub hp)).1
    nlinarith
  have hm := LeanLab.AlmostPrimes.Decomp1528b.mertens_prod_upper (x := (w : ℝ)) (by linarith)
  rw [Nat.floor_natCast] at hm
  simp only [one_div] at hm ⊢
  exact hle.trans hm


/-- The uniform normalization comparison, exactly the statement of
paper_enveloping_normalization_input, CONDITIONAL ON the two LEAFs above.
Page 15: log L at most log M = 10 log z, then the two inequalities of the display. -/
theorem paper_enveloping_normalization_input_of_leaves :
    ∃ c : ℝ, 0 < c ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w →
      ∀ L M : ℕ, 1 ≤ L → L ≤ M → M ≤ 2 * L →
        Real.log L ^ ((3 : ℝ) / 2) *
          ((Nat.totient (WW J w).toNat : ℝ) / WW J w) ^ ((3 : ℝ) / 2) ≤
            c * envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c₀, hc₀, HA⟩ := leaf_G1_ge_euler_product
  obtain ⟨CB, hCB, HB⟩ := leaf_euler_product_ge_log_ratio
  refine ⟨(10 : ℝ) ^ ((3 : ℝ) / 2) * CB / c₀, by positivity, ?_⟩
  intro J w hJ hw L M hL hLM hML
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw10 : (10 : ℝ) ≤ w := hwBig1.trans hw
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (hL.trans hLM)
  have hMpos : (0 : ℝ) < M := by linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set z : ℝ := (M : ℝ) ^ ((1 : ℝ) / 10) with hz
  have hz1 : 1 ≤ z := Real.one_le_rpow hM1 (by norm_num)
  have hlogz : Real.log z = Real.log M / 10 := by
    rw [hz, Real.log_rpow hMpos]; ring
  set r : ℝ := (Nat.totient (WW J w).toNat : ℝ) / WW J w with hr
  have hW0 : (0 : ℤ) < WW J w := by
    unfold WW Wmod
    apply mul_pos (by positivity)
    apply prod_pos
    intro p hp
    exact_mod_cast (Sw_spec w p hp).1.pos
  have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hW0.le)
  have hrle : r ≤ 1 / Real.log w := totient_ratio_le_inv_log J w hJ hw
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  have hlogLM : Real.log L ≤ Real.log M :=
    Real.log_le_log hLpos (by exact_mod_cast hLM)
  have hbase : Real.log L * r ≤ 10 * (Real.log z / Real.log w) := by
    calc Real.log L * r ≤ Real.log M * (1 / Real.log w) :=
          mul_le_mul hlogLM hrle hr0 (Real.log_nonneg hM1)
      _ = 10 * (Real.log z / Real.log w) := by rw [hlogz]; field_simp
  have hratio0 : 0 ≤ Real.log z / Real.log w :=
    div_nonneg (Real.log_nonneg hz1) hlogw.le
  have hB := HB w hw z hz1
  have hA := HA w hw z hz1
  calc Real.log L ^ ((3 : ℝ) / 2) * r ^ ((3 : ℝ) / 2)
      = (Real.log L * r) ^ ((3 : ℝ) / 2) := (Real.mul_rpow hlogL0 hr0).symm
    _ ≤ (10 * (Real.log z / Real.log w)) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (mul_nonneg hlogL0 hr0) hbase (by norm_num)
    _ = (10 : ℝ) ^ ((3 : ℝ) / 2) * (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) hratio0
    _ ≤ (10 : ℝ) ^ ((3 : ℝ) / 2) * (CB * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter
          (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z), (1 - (envelopingOmega w p : ℝ) / p)⁻¹) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (10 : ℝ) ^ ((3 : ℝ) / 2) * CB / c₀ * (c₀ * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter
          (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z), (1 - (envelopingOmega w p : ℝ) / p)⁻¹) := by
        field_simp
    _ ≤ (10 : ℝ) ^ ((3 : ℝ) / 2) * CB / c₀ * envelopingG w 1 z :=
        mul_le_mul_of_nonneg_left hA (by positivity)

end LeanLab.Teravainen2016
